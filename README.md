# ePBS Formal Model

A machine-checkable formal model of **Enshrined Proposer-Builder Separation (ePBS)**, the proposer/builder split that Ethereum's Glamsterdam upgrade brings into the consensus protocol itself.

ePBS replaces out-of-protocol relays (MEV-Boost) with in-protocol rules governing how a proposer commits to a builder's block and how the builder is obligated to reveal it. Getting those rules wrong is a consensus-level risk that cannot be rolled back once shipped. This project states the safety and liveness properties precisely and checks them, so problems are found before enshrinement rather than after.

## Status

Milestone 1 is done: the single-slot model is written and has been checked with TLC.

- `specs/EPBS.tla` is a complete single-slot TLA+ model: bidding, unconditional payment on inclusion, builder reveal / withhold / equivocate, a Payload-Timeliness Committee (PTC) vote with a Byzantine minority, tally, slashing, and canonical-payload resolution.
- Eight safety invariants and two liveness properties are defined (see `PROPERTIES.md`).
- **TLC checked all of them green** on the finite instance in `specs/EPBS.cfg` (159 distinct states, search depth 8, no errors). The measured run is in `RESULTS.md`.

Honest scope: a finite TLC run checks the properties on a small instance under the modeled adversary. It does not prove them for all builder counts or the full multi-slot fork choice. Those are milestones 2 and 3.

## What it models

One slot, as a state machine over these phases:

```
bidding -> proposing -> revealing -> attesting -> final
```

The safety questions it targets:

| Property | Plain-language question |
|---|---|
| Payment safety | Is the proposer paid even if the builder never reveals? |
| Commitment binding | Can a builder swap in a different payload after inclusion? |
| Equivocation slashing | Is a builder that reveals a non-committed payload slashed, and that payload rejected? |
| No reorg on withhold | Does a withholding builder unwind the proposer's beacon block? |
| Conservation | Is payment a pure transfer, with nothing minted or burned? |
| Liveness | Does the slot always terminate, and does an honest timely reveal always become canonical? |

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
specs/EPBS.tla     the model
specs/EPBS.cfg     the TLC configuration (small finite instance)
PROPERTIES.md      the full catalog of invariants and temporal properties
MILESTONES.md      the delivery plan
PROPOSAL.md        the grant / office-hours brief
```

## License

MIT. See `LICENSE`.
