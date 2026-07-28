# Milestone 3: Machine-Checked Payment Core

`EPBSPayment.v` proves the EIP-7732 payment core in Coq (the Rocq Prover) for **all** bid values, **all** balances, and **any** number of uninvolved builders. This is the step the finite TLC runs cannot give: a model check confirms the properties on a small instance, a proof guarantees them for every size.

## What is proved

Every statement below is a Coq theorem checked by `coqc`. None uses `Admitted`, `admit`, `Axiom`, or `Parameter`; the only imports are the standard library `ZArith` and the `lia` arithmetic decision procedure, which produces ordinary proof terms.

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

## Relationship to the TLA+ models

The TLA+ models (`../specs/`) check these properties, plus the fork-choice and liveness properties, on small finite instances with TLC. This Coq development lifts the payment and binding properties from "checked on an instance" to "proved for all sizes". The two are complementary: TLC explores the temporal behavior and the adversary; Coq generalizes the arithmetic core.

## Build

```bash
# Requires Coq / the Rocq Prover (tested with Rocq 9.2).
coqc EPBSPayment.v
```

A clean exit and a generated `EPBSPayment.vo` mean every theorem type-checked. Because there are no `Admitted` goals or axioms, that is a complete proof, not a partial one.
