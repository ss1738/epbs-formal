# Milestones

A solo, self-contained delivery plan. Each milestone is a complete, publishable artifact on its own, so value lands even if later milestones slip. Effort estimates are for one person.

## Milestone 1: model-checked single-slot safety (weeks)

**Deliverable.** The single-slot TLA+ model (`specs/EPBS.tla`) run under TLC on the finite instance in `specs/EPBS.cfg`, with all eight safety invariants and both liveness properties either checked green or with any counterexample documented and the model corrected.

- Run TLC, publish the full output (state count, invariants checked, time).
- For any invariant that fails, publish the counterexample trace and the fix.
- Write up what the model does and does not cover.

**Done when:** a reader can reproduce the TLC result from the repo with one command, and the property catalog in `PROPERTIES.md` is marked checked or corrected.

## Milestone 2: refined model (weeks to months)

**Deliverable.** A refinement that removes the milestone-1 abstractions:

- A real fork-choice fragment (payload-timeliness boost) instead of the single `blockFate` choice. **Done:** `specs/EPBSForkChoice.tla` derives the block's fate from an accumulated-weight fork choice and measures the exact reorg threshold. See `MILESTONE2.md`.
- Multi-slot history beyond two slots. **Done:** `specs/EPBSChain.tla` runs a bounded chain of slots with asynchronous, cross-slot withdrawal processing (EIP-7732's queued `BuilderPendingWithdrawal`), and TLC checks conservation and liveness (every queued withdrawal drains) across the whole chain.
- Rebase onto the live executable spec. **Target identified:** ePBS is the Gloas fork in `ethereum/consensus-specs` (`specs/gloas/`). The models are cross-checked against it and mapped in `FIDELITY.md`; a full rebase (weight-accumulation payment mechanism, exact fork-choice thresholds) is the remaining work.
- Per-attester timed votes rather than one atomic PTC step. **Done:** `specs/EPBSPTC.tla` casts each PTC vote as its own interleaved step with a deadline, Byzantine members that may lie or abstain, and late votes. TLC proves `INV_Correct`: the timed tally always equals the truth, which shows the atomic PTC step in `EPBS.tla` is a sound abstraction.
- An adversary that can choose its Byzantine set adaptively within the honest-majority bound. **Remaining.**

Re-check all properties against the refined model and publish deltas from milestone 1.

## Milestone 3: machine-checked proof of the core (months)

**Deliverable.** A Coq (or equivalent) proof of the properties that a finite TLC run can only check on small instances, not prove in general.

- Payment safety, no-steal, and conservation for any number of builders. **Done:** `coq/EPBSPayment.v` proves conservation (including over an arbitrary number of uninvolved builders), G1, G3, no dangling escrow, and commitment binding, all as axiom-free Coq theorems. See `coq/README.md`.
- A machine-checked proof of the fork-choice reorg threshold for all weights. **Done:** `coq/EPBSForkChoice.v` proves timely-payload safety above the threshold, a reorg below it, and the exact iff characterization, all axiom-free.
- A machine-checked proof of the full multi-slot temporal behavior (liveness across slots, single-slot-finality interactions). **Remaining.**

TLC gives confidence on small instances; a proof gives a guarantee for all sizes. This milestone converts the strongest invariants from checked to proven.

## Milestone 4: report and upstream engagement (weeks)

**Deliverable.** A written report aimed at the ePBS spec authors: the properties, the results, any weaknesses found, and suggested spec clarifications. Shared with the relevant Ethereum research channels for feedback.

## Sequencing note

Milestone 1 is the fundable unit and stands alone. Milestones 2 and 3 are the natural extensions a grant would support. Milestone 4 is where the work feeds back into the protocol, which is the point of the whole exercise.
