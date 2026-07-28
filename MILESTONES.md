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

- Multi-slot history, so cross-slot reorg scenarios can be expressed.
- A real fork-choice fragment (payload-timeliness boost) instead of the single `beaconCanonical` boolean.
- Per-attester timed votes rather than one atomic PTC step.
- An adversary that can choose its Byzantine set adaptively within the honest-majority bound.

Re-check all properties against the refined model and publish deltas from milestone 1.

## Milestone 3: machine-checked proof of the core (months)

**Deliverable.** A Coq (or equivalent) proof of the two properties that a finite TLC run can only check on small instances, not prove in general:

- Payment safety and no-steal, for any number of builders.
- Commitment binding, for any payload space.

TLC gives confidence on small instances; a proof gives a guarantee for all sizes. This milestone converts the strongest invariants from checked to proven.

## Milestone 4: report and upstream engagement (weeks)

**Deliverable.** A written report aimed at the ePBS spec authors: the properties, the results, any weaknesses found, and suggested spec clarifications. Shared with the relevant Ethereum research channels for feedback.

## Sequencing note

Milestone 1 is the fundable unit and stands alone. Milestones 2 and 3 are the natural extensions a grant would support. Milestone 4 is where the work feeds back into the protocol, which is the point of the whole exercise.
