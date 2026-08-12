> **RETRACTED (2026-08-11).** The reorg-threshold results below were proved over
> `PayloadBoost`, an additive payload term in fork-choice weight that Gloas does
> not have. `coq/EPBSForkChoice.v` has been DELETED. Reorg resistance is
> currently **UNPROVEN** — see `V2_VERIFICATION_SPEC.md` §1.12. Kept as the
> record of what was claimed; see `D5_PAYLOAD_WEIGHT.md`.

# Milestone 2: Fork-Choice Model and the Reorg Threshold

`specs/EPBSForkChoice.tla` extends the milestone-1 model where its most important abstraction was: milestone 1 chose the beacon block's fate (canonical or reorged) nondeterministically. This model **derives** that fate from an explicit payload-timeliness fork choice, so the reorg attack EIP-7732 warns about can be expressed and its threshold measured.

## What it models

Slot 1 has an honest proposer whose block B1 includes a builder's bid (value escrowed at inclusion). The builder reveals the payload on time or withholds it. Slot 2's proposer is adversarial and may extend B1 or attempt to reorg it by building on B1's parent, taking the proposer boost. Honest attesters back B1 (with the payload-timeliness boost when the payload was timely); Byzantine attesters back the reorg branch.

The fork choice is an LMD-GHOST abstraction by accumulated weight:

```
weight(B1)    = HonestWeight + (payload timely ? PayloadBoost : 0)
weight(reorg) = adversary reorged ? (ByzWeight + ProposerBoost) : 0
B1 canonical  iff weight(B1) >= weight(reorg)      (ties favor B1)
```

## The measured result: an exact reorg threshold

A timely-revealed payload is safe from reorg **exactly when**

```
HonestWeight + PayloadBoost >= ByzWeight + ProposerBoost
```

This is checked two ways, both run with TLC:

| Configuration | Parameters | `FC_TimelyPayloadSafe` | States |
|---|---|---|---|
| `EPBSForkChoice.cfg` (safe) | honest 2 + boost 1 = 3 vs byz 1 + boost 1 = 2 | holds (no error) | 11 |
| `EPBSForkChoice_attack.cfg` (unsafe) | honest 1 + boost 1 = 2 vs byz 2 + boost 1 = 3 | **violated**, reorg trace returned | 9 |

The attack configuration returns a four-state counterexample:

```
State 1: initial (payload undecided)
State 2: RevealPresent   (payload = "present")
State 3: P2Reorg         (p2mode = "reorg")
State 4: Resolve         (head = "orphaned")   <- timely payload reorged
```

This is the reorg attack, reproduced mechanically, at the exact weight boundary below which the payload-timeliness boost is insufficient. It matches EIP-7732's informal claim that reorging a builder's payload requires a heavy adversary (a malicious proposer plus a large attester share).

## The payment guarantees survive a reorg

Under the same attack parameters, with `FC_TimelyPayloadSafe` removed, every other invariant still holds (no error, verified separately):

- `FC_G1_ProposerPaid`: a canonical B1 pays the proposer.
- `FC_G3_WithholdSafe`: an orphaned B1 refunds the builder and pays the proposer nothing.
- `FC_Conservation`, `FC_NoDangling`, `FC_Binding`, `FC_ReorgImpliesAdversaryHeavy`.

So even when the adversary is strong enough to reorg a timely payload, the builder is refunded and value is conserved. The reorg costs liveness (the payload is dropped), not builder funds. That is exactly the separation EIP-7732 intends.

## What this establishes and what it does not

- It establishes the exact weight condition under which a timely payload is reorg-safe, and that the payment guarantees hold on both sides of that condition, on the modeled instance.
- It abstracts LMD-GHOST to a single accumulated-weight comparison over two slots. It does not model per-attester timed messages, more than two slots, or equivocation across slots. Those are milestone-3 refinements.

## Reproduce

```bash
# tla2tools.jar from https://github.com/tlaplus/tlaplus/releases
java -cp tla2tools.jar tlc2.TLC -config specs/EPBSForkChoice.cfg specs/EPBSForkChoice.tla
java -cp tla2tools.jar tlc2.TLC -config specs/EPBSForkChoice_attack.cfg specs/EPBSForkChoice.tla
```
