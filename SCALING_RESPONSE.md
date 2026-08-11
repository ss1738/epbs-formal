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

## 7. Apalache port — attempted, and where it stops

A timeboxed port was executed rather than projected. Apalache 0.61.0, Java 26,
16 GB machine.

**Two obstacles cleared.**

*Name collision.* `Head` resolves to `Sequences!Head`, which TLC tolerated and
Apalache does not:

```
requirement failed: unexpected arity 0 in Sequences!Head applied to
```

Renamed to `ChainHead` throughout. After that, `apalache-mc typecheck` returns
`EXITCODE: OK` — the existing `\* @type:` annotations on all fourteen state
variables were sufficient, with no further annotation work required.

**One obstacle not cleared: per-state SMT cost.**

```
apalache-mc check --config=exh.cfg --length=4 --inv=FC_ReorgImpliesAdversaryHeavy
  State 0: state invariant 0 holds.          (11 s)
  Step 0: picking a transition out of 1
  State 1: Checking 1 state invariants
  Ran out of heap memory (max JVM memory: 4294967296)      after 3 min 14 s
```

Raised to `-Xmx12g`. It then survives, but does not finish: at `--length=4` and
again at **`--length=1`**, checking the invariant at the single successor state
exceeds seven minutes without returning.

The bound is therefore not the constraint — a one-step run behaves the same as a
four-step run. The cost is per state, in the invariant itself.

**Diagnosis.** `ChainHead` is a four-level nested GHOST descent:

```tla
Heaviest(S)  == CHOOSE c \in S : \A d \in S : Weight(c) > Weight(d) \/ ...
Descend(b)   == IF Children(b) = {} THEN b ELSE Heaviest(Children(b))
ChainHead    == Descend(Descend(Descend(Descend(Genesis))))
```

Each `Descend` expands a `CHOOSE` over a set comprehension whose guard calls
`Weight`, which itself is a `Cardinality` over a comprehension across all
validators. Four nested levels of that, and `ChainHead` appears in `Canonical`,
`Reorged`, `IsHeadWeak` and the invariant. The SMT formula for one state is large
enough that Z3 does not return.

**Isolation test.** The diagnosis above was initially inferred from the shape of
the operator. It has since been measured. `EPBSStub.tla` is byte-identical to
`EPBSMultiSlot.tla` except for one line:

```tla
ChainHead == Genesis   \* stubbed, replacing the four-level Descend nest
```

Same config, same bound, same invariant:

| Variant | `--length=1` result |
|---|---|
| `ChainHead` = GHOST descent | no result in 7+ minutes |
| `ChainHead` = `Genesis` | **`Checker reports no error up to computation length 1`, `EXITCODE: OK`, ~10 s** |

So the bottleneck is that operator specifically, and Apalache is otherwise able to
check this model: it verified the invariant at depth 1 in ten seconds. Symbolic
checking is blocked on one operator we wrote for TLC's convenience, not on
Apalache's capability, not on our type structure, and not on the model's size.

This is a modelling problem, not an Apalache limitation. The fix is to stop
recomputing the head and carry it as state — maintain `head` as a variable updated
incrementally when blocks or votes change, and assert GHOST-consistency as a
separate invariant rather than inlining the descent everywhere. That converts a
deeply nested `CHOOSE` into a lookup, and is the next concrete task.

**Net.** Symbolic checking is reachable — the spec type-checks and the initial
state verifies. It is blocked on an encoding choice we made for TLC's benefit
(computed head, cheap to enumerate) that is expensive to solve symbolically. We
would rather record that precisely than claim symbolic results we do not have.

## 8. The refactor, and a genuine symbolic result

`ChainHead` was rewritten from a four-level nested descent to a single `CHOOSE`
over a flat GHOST-consistency predicate — same fixpoint, stated as one bounded
quantification rather than four nested choices:

```tla
IsGhostHead(h) ==
    /\ h \in blocks
    /\ Children(h) = {}
    /\ \A a \in ({Genesis} \union blockAnc[h]) :
         \A c \in Children(a) :
            OnPathTo(c, h) => \A d \in Children(a) : Weight(c) >= Weight(d) ...
```

Measured effect on `apalache-mc check`, same config, same invariant:

| Bound | nested descent | flat predicate |
|---|---|---|
| `--length=1` | no result in 7+ min | **OK in ~20 s** |
| `--length=2` | — | timeout at 540 s |
| `--length=3` | — | reaches Step 2, timeout at 400 s |

**The result: `Checker reports no error up to computation length 1`,
`EXITCODE: OK`.** `FC_ReorgImpliesAdversaryHeavy` is symbolically verified for
all initial states and one transition, at 4 validators with 1 Byzantine.

That is a real verification claim — the first in this repository that is not
sampling — and it is a small one. Depth 1 is one step. The multi-slot behaviour
this whole exercise is about lives near depth 120.

**What the refactor bought:** roughly a 20x reduction in per-state SMT cost, and
the demonstration that symbolic checking of this model is possible at all. What it
did not buy is depth. The cost still grows steeply per step, so the flat predicate
moved the wall rather than removing it.

Honest read: enumerative checking stalls at depth 10 over 84M states; symbolic
checking verifies depth 1 in twenty seconds and stalls by depth 2-3. Neither
currently reaches the region of interest. The next lever is not another encoding
tweak but reducing what must be solved per step — smaller validator sets with
symmetry, or splitting the invariant so each check carries less of the model.

## 9. Next

1. Symmetry reduction on `Validators`, and splitting
   `FC_ReorgImpliesAdversaryHeavy` into cheaper conjuncts, to buy depth.
2. Per-validator views and network delay, without which balancing attacks cannot be
   expressed.
3. Effective balances rather than unit weight.
4. Re-run the timely-reorg question under symbolic checking, where "unreachable to
   depth k" is a claim that can actually be made.

The submitted models were internally coherent and could not have found anything. This
one reaches four orders of magnitude more states, expresses withholding, derives
weight from votes, and has caught three of our own errors. It has not yet found a
protocol bug — and we would rather say that than manufacture one.
