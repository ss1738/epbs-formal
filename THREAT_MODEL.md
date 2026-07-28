# Threat Model and Coverage

This maps the adversarial behaviors EIP-7732 has to worry about to the model that covers each one and the result. It is the completeness argument: every attack the specification discusses is expressed somewhere in this repository and checked.

Everything below is reproduced by `./verify.sh`.

## Adversaries modeled

| Adversary behavior | Where modeled | Result |
|---|---|---|
| Builder withholds the payload after inclusion | `specs/EPBS.tla` (`BuilderWithhold`) | Slot is empty; proposer still paid (G1); no dangling escrow. |
| Builder equivocates (reveals a different payload) | `specs/EPBS.tla` (`BuilderEquivocate`) | Equivocated payload never canonical (`INV_EquivocationNotCanonical`); base spec does not slash. |
| Byzantine PTC minority votes dishonestly | `specs/EPBS.tla`, `specs/EPBSPTC.tla` | Cannot force a false `payload_present`; tally equals the truth (`INV_Correct`). |
| PTC votes arrive interleaved / late | `specs/EPBSPTC.tla` | Honest votes are counted before the deadline; tally still correct. |
| Adversarial slot-2 proposer reorgs a builder's payload | `specs/EPBSForkChoice.tla`, `coq/EPBSForkChoice.v` | Safe above the weight threshold; below it the reorg is exhibited and the threshold is proved exact. |
| Beacon block reorged after inclusion | `specs/EPBS.tla` (`blockFate = reorged`), `coq/EPBSPayment.v` | Builder is refunded, proposer paid nothing (G3), for all values. |
| Withdrawals blocked / queued across slots | `specs/EPBSChain.tla` | Value conserved across the chain; every queued withdrawal eventually drains (liveness). |

## The design decisions EIP-7732 is questioned on

| Question | Where answered | Answer |
|---|---|---|
| Why is a proposer paid before the payload is revealed? | `INV_G1` (TLC), `G1_proposer_paid` (Coq) | Payment on inclusion is what protects the proposer from a griefing builder; proved for all values. |
| Why is there no slashing for equivocation? | `coq/EPBSEquivocation.v` | Equivocation is self-punishing: on a canonical block the equivocator pays the full bid yet gets its payload excluded, a strictly dominated strategy. No slashing is needed to deter it. |
| Is the atomic committee vote a faithful abstraction? | `specs/EPBSPTC.tla` (`INV_Correct`) | Yes: the interleaved, timed, per-attester tally always equals the truth under the honest-majority threshold. |
| What exactly does reorg-resistance require? | `coq/EPBSForkChoice.v` (`reorg_threshold_iff`) | A timely payload is safe iff `HonestWeight + PayloadBoost >= ByzWeight + ProposerBoost`, proved in both directions for all weights. |

## Out of scope (stated honestly)

- An adversary that adapts its Byzantine set during a run (the models fix the Byzantine set at the start; this covers the security-relevant cases but is not the most general adversary).
- Networking-layer attacks (gossip, eclipse) below the consensus abstraction.
- Interactions with upgrades not yet specified (single-slot finality, full danksharding).
- Quantitative economics beyond the ordinal dominance argument for equivocation.

These are noted so the coverage claim is not overstated. The models cover the mechanism EIP-7732 specifies and the adversaries it discusses; they do not claim to cover the entire network stack.
