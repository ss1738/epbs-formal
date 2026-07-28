# TLC Results

Measured result of running the TLC model checker on `specs/EPBS.tla` (the EIP-7732 model) with the finite instance in `specs/EPBS.cfg`.

## Instance checked

- Builders: `{b1, b2}`, with `b2` Byzantine (may withhold or equivocate).
- Attesters (PTC): `{a1, a2, a3}`, with `a3` Byzantine (may vote dishonestly).
- `PayloadTimelyThreshold = 2`: an honest 2-of-3 margin. The single Byzantine attester cannot force "present"; the two honest ones can reach it.
- Bid values: `{1, 2}`. Starting builder balance: 100.

## Outcome

All nine safety invariants and the liveness property held. TLC found no error.

```
TLC2 Version 2.19 of 08 August 2024
Model checking completed. No error has been found.
316 states generated, 207 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 8.
```

Checked (see `PROPERTIES.md`):

- The three EIP-7732 guarantees: `INV_G1_ProposerUnconditionalPayment`, `INV_G2_BuilderRevealSafety`, `INV_G3_BuilderWithholdSafety`.
- Structural safety: `TypeOK`, `INV_CommitmentBinding`, `INV_EquivocationNotCanonical`, `INV_Conservation`, `INV_NoDanglingPayment`, `INV_SlashingFaithful`.
- Liveness: `LIVE_Progress`.

## Both configurations pass

- `SlashEquivocation = FALSE` (base EIP-7732, no equivocation slashing): no error, 207 distinct states.
- `SlashEquivocation = TRUE` (the optional slashing mitigation the EIP mentions): no error, 207 distinct states.

The base spec is the faithful model; the mitigation variant is included so the proposed slashing change can be checked against the same properties.

## What this does and does not establish

- It establishes that no reachable state of this instance violates the stated properties, including under the modeled adversary: a Byzantine builder that withholds or equivocates, a lying PTC minority, and a beacon block that may be canonical or reorged.
- It does **not** prove the properties for all builder counts, all payload spaces, or the full multi-slot fork choice. Those are milestones 2 and 3. A finite TLC run checks; it does not prove for all sizes.

## Fidelity note

This model tracks EIP-7732 as written, including the design choice that the base protocol has **no slashing for payload equivocation** (it accepts a split-view cost to the builder). `INV_SlashingFaithful` encodes that. The proposer-unconditional-payment, builder-reveal-safety, and builder-withhold-safety guarantees (G1, G2, G3) are the EIP's own stated guarantees, modeled directly.

## Reproduce

```bash
# tla2tools.jar from https://github.com/tlaplus/tlaplus/releases
java -cp tla2tools.jar tlc2.TLC -config specs/EPBS.cfg specs/EPBS.tla
```

Environment for this run: TLC 2.19, OpenJDK 23, macOS (Apple Silicon). Run completed in under one second.
