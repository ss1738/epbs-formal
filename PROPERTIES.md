# Property Catalog

Every property below is defined in `specs/EPBS.tla` and listed in `specs/EPBS.cfg`. This file explains what each one means and why it matters for ePBS. All of them were checked green by TLC on the finite instance (see `RESULTS.md`); this checks them on a small instance, it does not prove them for all sizes (see `MILESTONES.md`).

## Model in one paragraph

One slot runs through `bidding -> proposing -> revealing -> attesting -> final`. Builders post bids. The proposer includes one bid, and the bid value is transferred from builder to proposer **at inclusion**, unconditionally. The included builder then reveals the committed payload, withholds it, or equivocates (reveals a different one). A Payload-Timeliness Committee (PTC) votes on whether a valid payload was seen on time; a Byzantine minority of the committee may lie. The vote is tallied, equivocation is slashed, and the canonical payload for the slot is resolved.

## Safety invariants

| ID | Name | Statement | Why it matters |
|---|---|---|---|
| S1 | `INV_PaymentSafety` | If a bid was included, the proposer holds exactly the paid value, and that value is positive. | The proposer's compensation is real and definite once it does its job. |
| S2 | `INV_NoStealFromProposer` | If the builder withheld or equivocated, the proposer still holds the payment. | A griefing builder cannot leave the proposer unpaid. This is the core reason ePBS pays on inclusion, not on reveal. |
| S3 | `INV_CommitmentBinding` | A canonical payload is always the committed one. | A builder cannot substitute a different payload after the proposer commits. |
| S4 | `INV_EquivocationRejected` | An equivocated payload never becomes canonical. | Equivocation cannot be used to force an unexpected block. |
| S5 | `INV_EquivocationSlashed` | A builder that equivocated is slashed by the time the slot is final. | Misbehavior is penalized, not merely ignored. |
| S6 | `INV_Conservation` | Proposer balance plus the sum of builder balances equals the starting total. | Payment is a pure transfer. No value is minted or burned by the mechanism. |
| S7 | `INV_OnlyByzSlashed` | Only Byzantine builders are ever slashed. | An honest builder following the protocol is never punished. |
| S8 | `INV_NoReorgOnWithhold` | Once a bid is included, the proposer's beacon block stays canonical. | A withholding builder yields an empty payload, but does not reorg the proposer out. |

## Liveness properties

| ID | Name | Statement | Why it matters |
|---|---|---|---|
| L1 | `LIVE_Progress` | The slot eventually reaches `final`. | The chain makes progress even under builder failure. |
| L2 | `LIVE_HonestRevealCanonical` | Whenever the committed payload is revealed on time, it eventually becomes canonical. | Under an honest PTC majority, honest work is not dropped. L2 depends on the `HonestMajority` assumption in the model. |

## Assumptions (stated in the model)

- `HonestMajority`: strictly fewer than half the PTC members are Byzantine.
- `ByzBuilders` / `ByzAttesters`: the adversary is a fixed subset of participants, chosen before the slot.
- The fork-choice rule and multi-slot history are abstracted to `beaconCanonical` and a single-slot `canonical` value. Milestone 2 refines these.

## Known limitations of the milestone-1 model

- Single slot. Cross-slot reorg scenarios (for example, a late payload competing across a slot boundary) are out of scope until milestone 2.
- The PTC votes in one atomic step rather than as individually timed messages.
- Payment is modeled as integer balances, not the full beacon-state accounting.

These are deliberate abstractions to keep the state space enumerable for a first pass. Each is listed as a refinement target in `MILESTONES.md`.
