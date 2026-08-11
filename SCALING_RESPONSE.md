# ePBS formal model — response to the ESP review

Boris Stanic, EF Ecosystem Support Program:

> The main issue is scale. The models are checked at a few hundred to a few thousand
> distinct states, with a handful of builders and attesters. At that size the checks
> confirm that the state machine you wrote is internally coherent rather than
> exercising the adversarial behaviour that makes ePBS a consensus-level risk. With
> fork choice modelled as an LMD-GHOST abstraction over single or bounded slots, the
> multi-slot interactions between fork choice and the payload timeliness committee
> sit outside what the models reach.

Every claim was correct. This records the audit, the rebuild, and — most usefully —
the three times the rebuilt model produced a confident answer that turned out to be
wrong.

**We are not reporting an attack.** We are reporting that the structural criticism was
right, that it is fixed, and that enumerative model checking cannot verify the
resulting model at even minimal bounds. That last point is measured, and it is the
argument for the next milestone.

---

## 1. The diagnosis was structural, not budgetary

Measured state space of the submitted models:

| Model | Config | Distinct states |
|---|---|---|
| `EPBS.tla` | default | 207 |
| `EPBS.tla` | `EPBS_large.cfg` | 4,704 |
| `EPBSPTC.tla` | large | 180 |
| `EPBSChain.tla` | large (6 slots) | 267 |

**4,704 was the maximum anywhere in the repository.**

**Fork choice was a closed-form inequality, not a search.** `EPBSForkChoice.tla:67`
declared `head \in {"none","b1full","b1empty","orphaned"}`. `HonestWeight` and
`ByzWeight` were `CONSTANTS` with zero assignments in the module. The header states
the decision procedure outright: *"B1 stays canonical iff weight(B1) >= weight(reorg)"*.
TLC was confirming arithmetic we had written down.

**The halves were never composed.**

```
$ grep -E "^EXTENDS|INSTANCE" specs/*.tla
EPBSChain.tla:         EXTENDS Naturals
EPBSForkChoice.tla:    EXTENDS Naturals, Integers
EPBSPTC.tla:           EXTENDS Naturals, FiniteSets
EPBS.tla:              EXTENDS Naturals, Integers, FiniteSets, TLC
EPBSWeightPayment.tla: EXTENDS Naturals, FiniteSets
```

No specification extended or instantiated any other. Five disjoint state machines: one
with slots and no fork choice, one with fork choice hardcoded to two slots, one with a
committee and no chain. **The multi-slot × PTC interaction was unreachable at any
`MaxSlot`.** Raising bounds would never have found it.

---

## 2. `specs/EPBSMultiSlot.tla`

One state machine: block tree, vote store, PTC.

- **`Head` is computed** by GHOST descent over `blocks`. Ancestry is carried as state
  (`blockAnc`) rather than by a recursive operator, keeping `Weight()` flat and the
  module Apalache-friendly.
- **Weight is derived** from a per-validator latest-message store, so equivocation and
  vote switching became expressible; previously they could not be written down.
- **The adversary chooses when to act**, replacing static `FaultXxx` booleans:
  `AdvProposeFork`, `AdvEquivocate`, `AdvPTCLie`, `AdvLateReveal`,
  `AdvWithholdBlock`, `AdvWithholdVote`, `AdvRelease`.
- **Withholding is real.** Withheld blocks stay out of `blocks` so the GHOST descent
  cannot see them; withheld votes stay out of `votes` so `Weight()` cannot see them.
  `AdvRelease` publishes both atomically. Without a private message set the ex-ante
  reorg class is inexpressible, not merely unreached.

### Constants, fetched not recalled

| Quantity | Source | Value |
|---|---|---|
| `PAYLOAD_TIMELY_THRESHOLD` | `gloas/fork-choice.md:295` | `PTC_SIZE // 2` = 256, strictly `>` |
| `REORG_HEAD_WEIGHT_THRESHOLD` | `configs/mainnet.yaml:146` | 20 |
| `REORG_PARENT_WEIGHT_THRESHOLD` | `configs/mainnet.yaml` | 160 |
| `PROPOSER_SCORE_BOOST` | `phase0/fork-choice.md:129` | 40 |
| `calculate_committee_fraction` | `phase0/fork-choice.md:290` | `(committee_weight * pct) // 100` |

Our PTC tally had been `>=`. On a committee threshold that is an off-by-one of exactly
the kind that flips a reorg.

### An asymmetry the spec forced

Reading `get_proposer_head` changed the design. `is_head_weak` and `is_parent_strong`
are **not** fork-choice constraints — they are two of eight conjuncts gating an
*honest* proposer's reorg decision. An adversary ignores them. Our plan had been to
encode them as gates on the adversary, which would have forbidden it from attacking.
They now gate `ProposeHonestReorg`; `AdvProposeFork` is deliberately ungated.

---

## 3. Results

| Configuration | Outcome |
|---|---|
| submitted models, max | 4,704 distinct states |
| composed, BFS (5 val, `MaxSlot` 3) | 11,331,872 distinct in 2 min, **depth stalled at 10** |
| composed, simulate (5 val, budget 3) | 76,828,388 states, no violation |
| wide (6 val, 2 Byz, `MaxSlot` 4, budget 8) | 51,913,102 states, no violation |
| withholding (budget 12) | 27,582,993 states, no violation |
| **exhaustive (4 val, `MaxSlot` 2, budget 3)** | **84,316,842 distinct, 67M queued — did not exhaust** |
| **exhaustive (4 val, `MaxSlot` 2, budget 1)** | **55,654,172 distinct, 40.6M queued — did not exhaust** |

### Vacuity probes

`Reorged(b) => P` is trivially true wherever nothing is ever reorged. Each probe is a
deliberately false statement; a **violation** witnesses reachability.

| Probe | Result | States to witness |
|---|---|---|
| adversary acts | REACHABLE | — |
| PTC rules "present" | REACHABLE | — |
| equivocation occurs | REACHABLE | — |
| adversary withholds | REACHABLE | 161 |
| a reorg occurs | REACHABLE | 2,692 |
| reorg of a PTC-timely block | not sampled | 13,942,189 |

The invariants have teeth: every precondition they depend on is reachable, cheaply.

### The finding we are NOT making

An earlier draft of this document claimed the payload boost makes timely blocks
resistant to reorg, on the strength of 14M unsampled traces. **That claim is
withdrawn.** Exhaustive search at `MaxSlot = 2` reached the state in minutes. Random
sampling had simply missed it.

The counterexample it found then turned out to be our own bug (see §4.3). So we can
say neither that timely reorgs are unreachable, nor that we have found one.

---

## 4. Three false positives, and what each was

Documented because they bear on how much any single result is worth.

### 4.1 An unearned proposer boost

The first composed model produced a counterexample in 11 seconds: a PTC-timely block
reorged. `BoostWeight` awarded proposer boost to *any* block proposed in the current
slot — including `AdvProposeFork`'s off-schedule block, which Gloas would never boost.
Restricted to the designated proposal, the violation vanished and 35.7M states ran
clean. We were one step from sending that trace to core researchers.

### 4.2 A truncated harness

A first pass at the vacuity probes reported four of five conditions unreachable,
implying every clean run had been vacuous. The probes were piped through `head -400`;
the closing pipe sent `SIGPIPE` to TLC, killing it before it explored anything. A full
diagnosis — that honest validators never split, that the model needed per-validator
views — was built on that measurement before it was caught. Re-run without truncation,
four of five are reachable.

### 4.3 Slots that passed in silence

The one exhaustive run that terminated found a timely reorg. The trace:

```
votes = (v1 :> 0, v2 :> 0, v3 :> 0, v4 :> 0)   ← no validator ever attested
blockSlot = (1 :> 1, 2 :> 1, 3 :> 1)            slot is now 2
ptcVerdict[3] = "present"    everHead = {0, 3}
```

Block 3 became head on `PayloadBoost + ProposerBoost` with zero attestations. The slot
advanced, both boosts expired, every block fell to weight 0, and the tie-break handed
the head to the lowest block id. Not an attack — a committee that never turned up,
plus an arbitrary tie-break.

Two fixes: `AdvanceSlot` now requires `AllHonestAttested`, and ties break on a
hash-like scramble standing in for root ordering rather than on block id.

**Pattern.** A model bug, an instrument bug, and an unstated assumption. Each produced
a confident, wrong conclusion that survived until something external contradicted it.
Every counterexample this model produces is now checked against `consensus-specs`
before it is believed.

---

## 5. The computational boundary

With both fixes applied, TLC does not exhaust **4 validators, 2 slots, adversary
budget 1** — the smallest configuration that still permits a PTC verdict. 55.7M
distinct states, 40.6M queued, still running.

Breadth-first search also never escaped **depth 10** in any configuration, while the
behaviour of interest lives at depth ~120. Enumerative checking explores breadth; the
multi-slot interactions the review names are deep.

This is the measured result the next milestone rests on. Not "we would like symbolic
checking" but: **enumerative verification of this model is infeasible at minimal
bounds, and here are the numbers.** Apalache does not enumerate; bounded-depth claims
become provable where here they are merely unsampled.

---

## 6. What this does not establish

- **Simulation is sampling.** Absence in 14M traces is not unreachability — proven
  today, the hard way.
- **Five of eight `get_proposer_head` conjuncts are unmodelled** (`head_late`,
  `not_epoch_boundary`, `ffg_competitive`, `finalization_ok`, `proposing_on_time`):
  they need a wall clock and FFG state. Honest reorgs are therefore *more* permissive
  here than in the protocol — conservative for safety, unsound for liveness.
- **Unit weight, not effective balance.** `is_head_weak` sums effective balances.
- **No network delay or per-validator views**, so the balancing attack
  (Neu–Tas–Tse) remains out of reach.
- **4–6 validators, `MaxSlot` ≤ 4.** Mainnet has ~1M validators and a 512-member PTC.
- `AllHonestAttested` is stronger than reality: it forces the honest committee to
  converge on one head before time advances, where real views diverge.

---

## 7. Next

1. **Port to Apalache.** §5 is the justification, with numbers.
2. Per-validator views and network delay, without which balancing attacks cannot be
   expressed.
3. Effective balances rather than unit weight.
4. Re-run the timely-reorg question under symbolic checking, where "unreachable to
   depth k" is a claim that can actually be made.

The submitted models were internally coherent and could not have found anything. This
one reaches four orders of magnitude more states, expresses withholding, derives
weight from votes, and has caught three of our own errors. It has not yet found a
protocol bug — and we would rather say that than manufacture one.
