# Fidelity to EIP-7732

A formal model is only as useful as its faithfulness to the thing it models. This document maps each modeling choice to the corresponding part of [EIP-7732](https://eips.ethereum.org/EIPS/eip-7732), so a reader can check that the model represents the spec rather than a convenient idealization. Where the model abstracts, the abstraction is stated.

## Tracked spec revision

The models were built from **EIP-7732 as published** (eips.ethereum.org/EIPS/eip-7732) and have been cross-checked against the live executable spec. In the `ethereum/consensus-specs` repository, ePBS has been promoted from a feature to a named fork, **Gloas** (`specs/gloas/`), the consensus-layer counterpart of the Glamsterdam upgrade. The cross-check below is against `specs/gloas/` at commit **`8a3df1d7`** (retrieved 2026-07-28): `beacon-chain.md`, `fork-choice.md`, `validator.md`.

The abstractions in these models are faithful to the Gloas spec's structure (see the mapping and deltas below). A full rebase onto a specific pinned Gloas revision, tracking its exact functions and constants, is the natural next milestone; the anchor points that would need re-checking are listed below.

## Mapping to the live Gloas spec

| Model element | Gloas (`specs/gloas/`) counterpart |
|---|---|
| `ProposerInclude`, bid escrow (`pending`) | `process_execution_payload_bid`; `state.builder_pending_payments` |
| Settlement to the proposer on a canonical block | `process_builder_pending_payments`; `state.builder_pending_withdrawals` (settled when attestation weight reaches quorum) |
| PTC vote (`ptcVote`, `PayloadTimelyThreshold`) | `process_payload_attestation`; `payload_timeliness(store, root, timely)` against `PAYLOAD_TIMELY_THRESHOLD = PTC_SIZE // 2 = 256` (PTC_SIZE = 512) |
| Fork-choice reorg (`weightB1` vs `weightReorg`, threshold) | `is_head_weak` (`head_weight < REORG_HEAD_WEIGHT_THRESHOLD`) and `is_parent_strong` (`parent_weight > REORG_PARENT_WEIGHT_THRESHOLD`) in `fork-choice.md` |
| `payloadCanonical = committed` vs `none` | `should_build_on_full`; `PAYLOAD_STATUS_FULL` vs `PAYLOAD_STATUS_EMPTY` |
| Affordability guard (`bal[b] >= v`) | `can_builder_cover_bid` (`builder_balance - min_balance >= bid_amount`) |

## Deltas found against the live spec (stated honestly)

- **PTC threshold is a concrete half-committee value.** Gloas fixes `PAYLOAD_TIMELY_THRESHOLD = PTC_SIZE // 2`. The model's `PayloadTimelyThreshold` is abstract, constrained to sit above the Byzantine count and at or below the honest count; that is faithful to a half-committee threshold exactly under an honest majority.
- **Payment settles by attestation weight, not a boolean.** Gloas settles `builder_pending_payments` when accumulated attestation weight reaches quorum, and a non-canonical block simply never accrues that weight. The other models abstract this to escrow-at-inclusion with settle-on-canonical and revert-on-reorg. This delta is now modelled directly in `specs/EPBSWeightPayment.tla`, which reproduces the weight-accumulation-and-quorum mechanism and shows the same guarantees (a canonical block pays the proposer, a non-canonical block charges no one, a Byzantine minority cannot force a payment, value is conserved) emerging from the weight dynamics rather than assumed. The remaining abstraction there is that each attester contributes unit weight rather than its effective balance.
- **No equivocation slashing is confirmed in the live spec.** Gloas defines no payload-equivocation or builder-equivocation slashing (proposer slashing only clears a pending payment). This validates the model's base choice (`SlashEquivocation = FALSE`) and the argument in `coq/EPBSEquivocation.v`.
- **Fork-choice structure matches.** Gloas gates a withholding reorg on head-weakness and parent-strength weight thresholds, the same accumulated-weight comparison `EPBSForkChoice.tla` and `coq/EPBSForkChoice.v` model; Gloas leaves the exact numeric thresholds to committee fractions inherited from prior forks.

## Roles and data structures

| Model element | EIP-7732 counterpart |
|---|---|
| A builder posting a bid (`SubmitBid`, `bids`) | `SignedExecutionPayloadBid` broadcast by a staked builder. |
| The proposer including a bid (`ProposerInclude`) | The proposer placing the selected `signed_execution_payload_bid` in the `BeaconBlockBody`. |
| Debit at inclusion (`pending`, builder balance reduced) | "When processing the `BeaconBlock`, the committed value is deducted from the builder's beacon chain balance", recorded as a `BuilderPendingPayment`. |
| The builder revealing (`BuilderRevealCommitted`) | The builder broadcasting the `SignedExecutionPayloadEnvelope`. |
| Withhold (`BuilderWithhold`) | The builder not revealing, producing an "empty" slot. |
| Equivocate (`BuilderEquivocate`) | The builder revealing the payload and a withheld message, splitting the view. |
| The PTC and its vote (`ptcVote`, `Attesters`) | The Payload-Timeliness Committee (`get_ptc`) attesting via `PayloadAttestationMessage` with a `payload_present` flag. |
| Present-vote tally against a threshold (`PayloadTimelyThreshold`) | `PAYLOAD_TIMELY_THRESHOLD`; the payload is present when enough of the committee attest so. |
| Finalize to proposer (`bal[proposer] += pending`) | The `BuilderPendingWithdrawal` paid to a proposer-chosen execution-layer address. |
| Queued, asynchronous withdrawal (`owed`, `Drain` in `EPBSChain.tla`) | "the consensus layer does not process any more withdrawals until an execution payload has fulfilled the outstanding ones"; `builder_pending_withdrawals`. |

## Design choices modeled faithfully

- **Payment on inclusion, not on reveal.** The value is deducted from the builder at inclusion and the proposer is paid whether or not the payload is revealed. This is EIP-7732's "proposer unconditional payment" (modeled as G1).
- **No slashing for equivocation.** EIP-7732 states there is "no penalty for PTC nor payload equivocation". The base model sets `SlashEquivocation = FALSE` and `coq/EPBSEquivocation.v` proves the rationale (equivocation is self-punishing). The optional mitigation the EIP mentions is available behind the same constant.
- **Payment reverts if the block is not canonical.** EIP-7732's `process_builder_pending_payments` only settles payments for payloads on the canonical chain; the model reverts the escrow to the builder when `blockFate = reorged` (G3).
- **Honest-majority PTC margin.** `PayloadTimelyThreshold` is constrained above the Byzantine count and at or below the honest count, matching the security margin EIP-7732 describes (for example a 2/3 threshold).

## Abstractions (stated honestly)

- **Fork choice.** `EPBS.tla` chooses `blockFate` nondeterministically; `EPBSForkChoice.tla` refines this to an accumulated-weight comparison (an LMD-GHOST abstraction with the payload-timeliness and proposer boosts). Neither models the full fork-choice rule from the consensus-specs; the abstraction captures the reorg dynamic and its threshold.
- **Single vs multi-slot.** `EPBS.tla` and `EPBSForkChoice.tla` are single-slot; `EPBSChain.tla` runs a bounded chain. Unbounded history is not modeled.
- **PTC timing.** `EPBS.tla` tallies the committee atomically; `EPBSPTC.tla` refines this to per-attester interleaved, timed votes and proves the atomic tally is a sound abstraction (`INV_Correct`).
- **Balances.** Payment is integer balances plus one escrow, not the full beacon-state `builder_pending_payments` / `builder_pending_withdrawals` lists.
- **Blob data availability.** The `blob_data_available` component of a `PayloadAttestationMessage` is out of scope; only payload presence is modeled.

## How to check the mapping

The EIP-7732 terms above (`SignedExecutionPayloadBid`, `BuilderPendingPayment`, `PayloadAttestationMessage`, `PAYLOAD_TIMELY_THRESHOLD`, `process_builder_pending_payments`) appear verbatim in the specification. Each corresponds to a named action or variable in the models, listed in the tables above and defined in `specs/` and `coq/`.
