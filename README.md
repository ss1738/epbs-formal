# ePBS Formal Model

A machine-checkable formal model of **Enshrined Proposer-Builder Separation (ePBS)** as specified in **[EIP-7732](https://eips.ethereum.org/EIPS/eip-7732)**, the proposer/builder split that Ethereum's Glamsterdam upgrade brings into the consensus protocol itself.

ePBS replaces out-of-protocol relays (MEV-Boost) with in-protocol rules governing how a proposer commits to a builder's block and how the builder is obligated to reveal it. Getting those rules wrong is a consensus-level risk that cannot be rolled back once shipped. This project models the EIP-7732 mechanism (the `SignedExecutionPayloadBid`, the `BuilderPendingPayment` deducted at inclusion, the PTC `payload_present` vote, and the canonical-versus-reorged settlement) and checks its three stated safety guarantees plus liveness, so problems are found before enshrinement rather than after.

## Status

Milestone 1 is done: the single-slot EIP-7732 model is written and has been checked with TLC.

- `specs/EPBS.tla` is a complete single-slot TLA+ model: bidding, payment deducted from the builder at inclusion, builder reveal / withhold / equivocate, a Payload-Timeliness Committee (PTC) vote with a Byzantine minority and a timeliness threshold, canonical-versus-reorged settlement, and pending-payment finalize-or-revert.
- The three EIP-7732 guarantees (proposer unconditional payment, builder reveal safety, builder withhold safety) plus six structural invariants and a liveness property are defined (see `PROPERTIES.md`).
- **TLC checked all of them green** on the finite instance in `specs/EPBS.cfg` (207 distinct states, search depth 8, no errors). The measured run is in `RESULTS.md`. Both the base spec and the optional equivocation-slashing mitigation pass.

Milestone 2 is under way: `specs/EPBSForkChoice.tla` adds an explicit payload-timeliness fork choice and measures the exact weight threshold at which a timely payload becomes reorg-safe. TLC confirms safety above the threshold and returns the reorg counterexample below it, while the payment guarantees hold on both sides. See `MILESTONE2.md`. `specs/EPBSChain.tla` extends the payment lifecycle across a bounded chain of slots with EIP-7732's asynchronous, queued withdrawals, and TLC confirms conservation and liveness (every withdrawal drains) across the whole chain. `specs/EPBSPTC.tla` refines the committee vote from one atomic step into individual, interleaved, timed attestations with lying or abstaining Byzantine members, and TLC proves the timed tally always equals the truth (so the atomic step is a sound abstraction).

Milestone 3 is well under way, with two standalone Coq (Rocq Prover) developments that lift the strongest results from a finite instance to all sizes:

- `coq/EPBSPayment.v` proves the payment core for **all** bid values, **all** balances, and **any** number of builders: conservation, the G1 and G3 payment guarantees, no dangling escrow, and commitment binding.
- `coq/EPBSForkChoice.v` proves the reorg threshold for **all** non-negative weights: a timely payload is canonical against any adversary above the threshold, is reorged by the worst-case adversary below it, and the exact iff characterization in between.

All are machine-checked theorems with no axioms or admitted goals. See `coq/README.md`.

Honest scope: the finite TLC runs check the temporal behavior and the adversary on small instances; the Coq proofs generalize the payment, binding, and reorg-threshold results to all sizes. Remaining milestone-3 work is a machine-checked proof of the full multi-slot temporal behavior (liveness across slots, single-slot-finality interactions).

## What it models

One slot, as a state machine over these phases:

```
bidding -> proposing -> revealing -> attesting -> final
```

The safety questions it targets:

| Property | Plain-language question |
|---|---|
| Proposer unconditional payment (G1) | Is the proposer paid even if the builder never reveals? |
| Builder reveal safety (G2) | Is an honest, timely payload actually included under an honest PTC? |
| Builder withhold safety (G3) | If the block is reorged out, is the builder spared the charge? |
| Commitment binding | Can a builder swap in a different payload after inclusion? |
| Equivocation not canonical | Can an equivocated payload become the canonical one? |
| Conservation | Is payment a pure transfer, with nothing minted or burned? |
| Liveness | Does the slot always terminate? |

Note on fidelity: EIP-7732 deliberately has **no slashing** for payload equivocation. The model reflects that (slashing off by default), and includes the EIP's optional slashing mitigation behind a constant so both can be checked. See `PROPERTIES.md`.

## Running it

You need Java and the TLA+ tools (`tla2tools.jar`).

```bash
# from the repo root
java -cp tla2tools.jar tlc2.TLC -config specs/EPBS.cfg specs/EPBS.tla
```

Or open `specs/EPBS.tla` in the TLA+ Toolbox and run the model defined by `specs/EPBS.cfg`.

The configured instance is deliberately small (2 builders, 3 attesters, bid values {1, 2}) so the state space is fully enumerable.

## Why this project

Ethereum's public roadmap lists ePBS (Glamsterdam) as a near-term L1 change. The Ethereum Foundation funds open-source research that strengthens the protocol's foundations, and formal verification of consensus changes is squarely in scope. This model is offered as a public good under the MIT license.

## Layout

```
specs/EPBS.tla                    milestone 1: single-slot EIP-7732 model
specs/EPBS.cfg                    its TLC configuration
specs/EPBSForkChoice.tla          milestone 2: fork-choice / reorg-threshold model
specs/EPBSForkChoice.cfg          safe parameters (payload never reorged)
specs/EPBSForkChoice_attack.cfg   unsafe parameters (reorg counterexample)
specs/EPBSChain.tla               multi-slot chain: queued withdrawals + liveness
specs/EPBSChain.cfg               its TLC configuration (3 slots)
specs/EPBSPTC.tla                 per-attester timed PTC votes; tally correctness
specs/EPBSPTC.cfg                 its TLC configuration (3 attesters)
coq/EPBSPayment.v                 milestone 3: Coq proof of the payment core (all sizes)
coq/EPBSForkChoice.v              milestone 3: Coq proof of the reorg threshold (all weights)
coq/README.md                     what the Coq developments prove
RESULTS.md                        the measured milestone-1 TLC run
MILESTONE2.md                     the fork-choice result and reorg threshold
PROPERTIES.md                     the milestone-1 invariant catalog
MILESTONES.md                     the delivery plan
PROPOSAL.md                       the grant / office-hours brief
```

## License

MIT. See `LICENSE`.
