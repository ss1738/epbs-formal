# Milestone 3: Machine-Checked Core

Two standalone Coq (Rocq Prover) developments lift the strongest properties from "checked on a small TLC instance" to "proved for every size". Each file depends only on the standard library and checks with a plain `coqc`.

## `EPBSPayment.v`: the payment core, for all sizes

Proves the EIP-7732 payment core for **all** bid values, **all** balances, and **any** number of uninvolved builders.

| Theorem | Meaning |
|---|---|
| `lifecycle_conserves` | Inclusion followed by settlement conserves the global total, over any number of uninvolved builders, for any fate, value, and balances. |
| `settle_conserves` | Settlement is a pure transfer: the total is unchanged. |
| `G1_proposer_paid` | A canonical block pays the proposer exactly the committed value (G1), for all values. |
| `G3_withhold_safe` | A reorged block refunds the builder and pays the proposer nothing (G3), for all values. |
| `no_dangling_payment` | The escrow is zero after settlement, for any state and fate. |
| `commitment_binding` | A canonical payload is only ever the committed one. |
| `equivocation_not_canonical` | An equivocated reveal never yields a canonical payload. |
| `withhold_not_canonical` | A withheld reveal never yields a canonical payload. |

## `EPBSForkChoice.v`: the reorg threshold, for all weights

Lifts the fork-choice reorg threshold (which `../specs/EPBSForkChoice.tla` measures on two finite parameter sets) to a theorem true for **all** non-negative weights.

| Theorem | Meaning |
|---|---|
| `timely_payload_safe` | Above the threshold, a timely payload is canonical against any adversary strategy. |
| `reorg_threshold_iff` | The exact characterization: for the worst-case adversary, B1 is canonical iff `HonestWeight + PayloadBoost >= ByzWeight + ProposerBoost`. |
| `reorg_below_threshold` | Below the threshold, the worst-case adversary reorgs the timely payload (the threshold is tight, not just sufficient). |
| `reorg_implies_adversary_heavy` | A reorg of a timely payload forces the adversary to strictly out-weigh the honest committee plus the payload boost. |

## `EPBSEquivocation.v`: why no slashing is needed

Formalizes EIP-7732's rationale for omitting equivocation slashing: equivocation is self-punishing.

| Theorem | Meaning |
|---|---|
| `equivocation_pays_gets_nothing` | On a canonical block an equivocating builder pays the full bid and gets its payload excluded. |
| `equivocation_net_loss` | Its net position is exactly minus the bid: a pure loss. |
| `honest_dominates_equivocation` | When the payload has non-negative value, an honest reveal is at least as good as equivocating. |
| `equivocation_strictly_worse` | With any positive payload value, equivocating is strictly worse than revealing honestly. |

## `EPBSCommittee.v`: PTC tally correctness, for all committee sizes

Lifts the timed-PTC tally correctness (which `../specs/EPBSPTC.tla` checks at 3 and 5 attesters) to a theorem for **all** committee sizes, under the honest-majority threshold `B < T <= H`.

| Theorem | Meaning |
|---|---|
| `tally_correct` | The present-count tally equals the truth for any number of honest and Byzantine attesters and any Byzantine behaviour. |
| `no_false_present` | A present tally implies the payload really was timely. |
| `no_false_absent` | A timely payload is always tallied present. |

## No axioms

None of the theorems in either file uses `Admitted`, `admit`, `Axiom`, or `Parameter`; the only imports are the standard library `ZArith` and the `lia` arithmetic decision procedure, which produces ordinary proof terms. A clean `coqc` exit is therefore a complete proof.

## Relationship to the TLA+ models

The TLA+ models (`../specs/`) check these properties, plus the fork-choice and liveness properties, on small finite instances with TLC. This Coq development lifts the payment and binding properties from "checked on an instance" to "proved for all sizes". The two are complementary: TLC explores the temporal behavior and the adversary; Coq generalizes the arithmetic core.

## Build

```bash
# Requires Coq / the Rocq Prover (tested with Rocq 9.2). Each file is standalone.
coqc EPBSPayment.v
coqc EPBSForkChoice.v
coqc EPBSEquivocation.v
coqc EPBSCommittee.v
```

A clean exit and a generated `.vo` mean every theorem type-checked. Because there are no `Admitted` goals or axioms, that is a complete proof, not a partial one.
