# Non-Vacuity Self-Tests

A model check that passes tells you nothing if the invariant is vacuously true, or if the model can never reach a state where the property would matter. The natural question a reviewer asks is: **do these checks actually have teeth?**

This repository answers it by construction. It injects known bugs and confirms TLC catches each one with the right invariant. If an invariant were vacuous, the injected bug would slip through; it does not.

## The self-tests

The main model `specs/EPBS.tla` has two fault-injection flags, `FaultStealOnReorg` and `FaultBindingBug`. They are `FALSE` in every real configuration, so the verified model is unchanged there. Each is set `TRUE` in a dedicated config that injects one bug.

| Injected bug (flag) | What it breaks | Config | TLC result |
|---|---|---|---|
| A reorged block pays the proposer instead of refunding the builder (`FaultStealOnReorg`) | Builder withhold safety | `specs/EPBS_fault_steal.cfg` | `INV_G3_BuilderWithholdSafety is violated` |
| A canonical block always marks the payload committed, even when withheld or equivocated (`FaultBindingBug`) | Commitment binding | `specs/EPBS_fault_binding.cfg` | `INV_CommitmentBinding is violated` |

Both violations are measured (see the table above), and the base configuration `specs/EPBS.cfg` still passes with both flags `FALSE`. The fork-choice model provides a third teeth-demonstration: `specs/EPBSForkChoice_attack.cfg` drives the weights below the safety threshold and TLC returns the reorg counterexample for `FC_TimelyPayloadSafe`.

## Why this matters

Together these show the invariants are not vacuously true and the model reaches the states where they bite:

- G3 (builder withhold safety) genuinely constrains where the pending payment can go; flip it and the check fires.
- Commitment binding genuinely constrains which payloads become canonical; flip it and the check fires.
- The reorg-safety property genuinely depends on the weight threshold; cross it and the counterexample appears.

## Reproduce

```bash
# tla2tools.jar from https://github.com/tlaplus/tlaplus/releases
# base passes:
java -cp tla2tools.jar tlc2.TLC -config specs/EPBS.cfg specs/EPBS.tla
# injected bugs are caught (each prints "... is violated"):
java -cp tla2tools.jar tlc2.TLC -config specs/EPBS_fault_steal.cfg   specs/EPBS.tla
java -cp tla2tools.jar tlc2.TLC -config specs/EPBS_fault_binding.cfg specs/EPBS.tla
```

`./verify.sh` runs these as part of the standard check: the base configs must pass, and each fault config must produce its expected violation.
