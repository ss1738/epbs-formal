# Property Catalog

Every property below is defined in `specs/EPBS.tla` and listed in `specs/EPBS.cfg`. The model tracks EIP-7732. All properties were checked green by TLC on the finite instance (see `RESULTS.md`); this checks them on a small instance, it does not prove them for all sizes (see `MILESTONES.md`).

## Model in one paragraph

One slot runs through `bidding -> proposing -> revealing -> attesting -> final`. Builders post `SignedExecutionPayloadBid`s. The proposer includes one bid; at that point the committed value is deducted from the builder's beacon-chain balance into a pending-payment escrow (EIP-7732's `BuilderPendingPayment`). The included builder then reveals the committed payload, withholds it, or equivocates. A Payload-Timeliness Committee (PTC) votes `payload_present`; a Byzantine minority may lie, but the `PayloadTimelyThreshold` is set so honest members alone decide the outcome. The beacon block is then either canonical or reorged. If canonical, the pending payment is finalized to the proposer (a `BuilderPendingWithdrawal`); if reorged, it is reverted to the builder.

## The three EIP-7732 guarantees

These are the safety guarantees EIP-7732 states for itself, modeled directly.

| ID | Name | Statement | Why it matters |
|---|---|---|---|
| G1 | `INV_G1_ProposerUnconditionalPayment` | A canonical beacon block that included a bid pays the proposer the full committed value, whatever the builder did with the payload. | The proposer is paid for doing its job even if the builder withholds or equivocates. |
| G2 | `INV_G2_BuilderRevealSafety` | An honest, timely reveal on a canonical block, attested present by the PTC, becomes the canonical payload. | Honest builder work is not dropped under an honest PTC majority. |
| G3 | `INV_G3_BuilderWithholdSafety` | If the beacon block is not canonical (withheld or reorged), the builder is not charged and the proposer is not paid. | A builder whose block is reorged out does not lose its bid. |

## Structural safety

| Name | Statement | Why it matters |
|---|---|---|
| `INV_CommitmentBinding` | A canonical payload is always the committed one. | A builder cannot substitute a different payload after commitment. |
| `INV_EquivocationNotCanonical` | An equivocated payload never becomes canonical. | Equivocation cannot force an unexpected block. |
| `INV_Conservation` | Proposer balance plus builder balances plus the pending escrow equals the starting total. | Payment is a pure transfer; nothing is minted or burned. |
| `INV_NoDanglingPayment` | Once the slot is final, the pending escrow is zero. | Every pending payment is either finalized or reverted; none is stuck. |
| `INV_SlashingFaithful` | With slashing off (base EIP-7732) nobody is slashed; when the optional mitigation is on, only a Byzantine equivocator is. | Faithful to the EIP's actual choice, and lets the proposed mitigation be checked. |

## Liveness

| ID | Name | Statement | Why it matters |
|---|---|---|---|
| L1 | `LIVE_Progress` | The slot eventually reaches `final`. | The chain makes progress even under builder or reveal failure. |

## Fidelity note: no equivocation slashing in the base spec

EIP-7732 deliberately has **no penalty for payload equivocation**. Revealing a second, withheld payload splits the view at a cost to the builder (the revealed payload may not be included), and the EIP opted for that simplicity over a slashing rule. This model reflects it: `SlashEquivocation = FALSE` is the base spec. The EIP notes an optional mitigation to add equivocation slashing; setting `SlashEquivocation = TRUE` checks that variant against the same properties. Both pass on the instance.

## Assumptions (stated in the model)

- `ThresholdOK`: `PayloadTimelyThreshold` is above the Byzantine PTC count and at or below the honest PTC count, so a Byzantine minority cannot fake "present" and the honest members can always reach it. This is the honest-majority margin EIP-7732 describes.
- `ByzBuilders` / `ByzAttesters`: the adversary is a fixed subset, chosen before the slot.
- The fork choice and multi-slot history are abstracted to `blockFate` (canonical vs reorged). Milestone 2 refines this.

## Known limitations of the milestone-1 model

- Single slot. Cross-slot reorg scenarios are out of scope until milestone 2.
- The PTC votes in one atomic step rather than as individually timed messages.
- Payment is modeled as integer balances and a single pending escrow, not the full beacon-state `builder_pending_payments` / `builder_pending_withdrawals` lists.
- `blockFate` is chosen nondeterministically rather than derived from a modeled fork-choice rule. Deriving it from a payload-timeliness fork-choice fragment is a milestone-2 target.

These are deliberate abstractions to keep the state space enumerable for a first pass.
