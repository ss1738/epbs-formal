# TLC Results

Measured result of running the TLC model checker on `specs/EPBS.tla` with the finite instance in `specs/EPBS.cfg`.

## Instance checked

- Builders: `{b1, b2}`, with `b2` Byzantine (may withhold or equivocate).
- Attesters (PTC): `{a1, a2, a3}`, with `a3` Byzantine (may vote dishonestly). Honest majority holds (1 of 3 Byzantine).
- Bid values: `{1, 2}`. Starting builder balance: 100.

## Outcome

All eight safety invariants and both liveness properties held. TLC found no error.

```
TLC2 Version 2.19 of 08 August 2024
Model checking completed. No error has been found.
220 states generated, 159 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 8.
Finished checking temporal properties: no violation.
```

Checked:

- Safety: `TypeOK`, `INV_PaymentSafety`, `INV_NoStealFromProposer`, `INV_CommitmentBinding`, `INV_EquivocationRejected`, `INV_EquivocationSlashed`, `INV_Conservation`, `INV_OnlyByzSlashed`, `INV_NoReorgOnWithhold`.
- Liveness: `LIVE_Progress`, `LIVE_HonestRevealCanonical`.

## What this does and does not establish

- It establishes that no reachable state of the small instance violates the stated properties, including under the modeled adversary (a Byzantine builder that withholds or equivocates, and a lying PTC minority).
- It does **not** prove the properties for all builder counts, all payload spaces, or the full multi-slot fork choice. Those are milestones 2 and 3. A finite TLC run checks; it does not prove for all sizes.

## Reproduce

```bash
# tla2tools.jar from https://github.com/tlaplus/tlaplus/releases
java -cp tla2tools.jar tlc2.TLC -config specs/EPBS.cfg specs/EPBS.tla
```

Environment for this run: TLC 2.19, OpenJDK 23, macOS (Apple Silicon). Run completed in under one second.
