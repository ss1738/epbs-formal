# V2 Verification Spec — inductive invariants and SMT tractability for `EPBSMultiSlotV2`

Engineering specification for the phase after `EPBSNodes.tla`. Every claim is
tagged MEASURED (with the command that produced it), INFERRED, or OPEN.


> ## ⚠ This document mixes implemented code with design sketches
>
> `V2_VERIFICATION_SPEC.md` contains both **measured results from operators that
> exist** and **design skeletons for operators that do not**. Code blocks of the
> second kind are marked `DESIGN ONLY — NOT IMPLEMENTED` directly above them.
>
> As of `f318ce3`, of 15 operators shown in `tla` blocks here:
>
> - **Implemented:** `AncClosure`, `HeadCertified`, `NodeInSubtree`,
>   `ShouldApplyProposerBoost`, `VAC_BoostSuppressed`, `StructuralClosure`
>   (2026-08-13, see §1.16)
> - **Design only:** `IndInv`, `MonotoneHistory`,
>   `StoreCoherence`, `SupportAgrees`, `AdversaryBudget`,
>   `AdvProposerEquivocate`, `VAC_ParentPrevSlot`, `VAC_ParentWeak`,
>   `VAC_TimelyEquivExists`
>
> `specs/` is the authority on what exists. `check_registry.sh` enforces that
> every *implemented* checkable operator is registered in §2; it says nothing
> about the sketches here.

---

## §0 Measured ground truth

All on Mini-3, Apalache 0.61.0, `JVM_ARGS=-Xmx12g`, config
`Validators={v1,v2,v3}, ByzValidators={v3}, ProposerBoost=2, CurrentSlot=3, MaxDepth=4`.

```
apalache-mc check --cinit=ConstInit --init=Init --next=Next --inv=<INV> --length=0 MCEPBSNodes.tla
```

> This table is the **pre-rewrite** baseline that §1.1 compares against.
> `AncestorWalkTerminates` no longer exists in the module — M2 deleted the
> unrolling it guarded, and `AncClosure` + `AncRootsUnique` replace it. Do not
> try to run it against current `EPBSNodes.tla`.

| Check | Result | Wall clock | Touches `ChainHead`? |
|---|---|---|---|
| `typecheck` | OK, all expressions typed | 0.4 s | — |
| `AncestorWalkTerminates` | **HOLDS** | 1.8 s | no |
| `TypeOK` | **HOLDS** | ~2 s | no |
| `S5_ChildAttachesToOneBranch` | **HOLDS** | ~2 s | no |
| `S6_FullImpliesVerified` | **HOLDS** | ~2 s | no |
| `VAC_BoostReachesDescendant` | **VIOLATED** (desired) | 4 s | no |
| `S4_PayloadStatusExclusive` | **`OutOfMemoryError` at `-Xmx12g`** | ~3 s after reaching the checker | **yes** |

MEASURED. The correlation in the right-hand column is the central finding of this
document and drives §1–§3.

**Correction.** An earlier revision of this file, and commit `5bd9054`'s message,
recorded the S4 row as "no result in >10 min" and attributed it to solver time.
That is wrong. From `detailed.log` of the 10:14:38 run:

```
PASS #12: AnalysisPass [OK]        (Skolemization, Expansion)
PASS #13: BoundedChecker
State 0: Checking 1 state invariants
State 0: Checking state invariant 0
java.lang.OutOfMemoryError: Java heap space
```

Every pass up to the checker completed in ~3 s total, and the heap died ~3 s into
constraint construction. **Z3 never received a complete problem.** The failure is
in Apalache's rewriter, translating the invariant into SMT — not in solving it.
The >10 min figure was a separate solo re-run made *after* the `is_ancestor` fix,
i.e. of a different and more expensive expression, and should not have been
attributed to the same run.

This matters for the fix. A solver-time wall argues for better encodings or more
time; a rewriter heap wall argues for **smaller terms**, which is what §2 and §3
deliver. It also rules out "raise the timeout" as an option, and makes "raise the
heap" a temporary measure at best: the term size is the problem.

**Defect found and fixed during this run (finding #10).** `NodeInSubtree` was
written as record equality. The spec's `is_ancestor` is not equality:

```python
if node_ancestor.root != ancestor.root: return False
return (node_ancestor.payload_status == ancestor.payload_status
        or ancestor.payload_status == PAYLOAD_STATUS_PENDING)
```

`get_ancestor` carries the *declared* parent status up the walk and so never
returns `PENDING` for a strict ancestor. Under equality, every `PENDING` target
was unreachable — and `BoostNode` is `(boostRoot, PENDING)`, so **proposer boost
propagated to nothing.** Typecheck was clean; `S5` and `S6` both passed. Only
`VAC_BoostReachesDescendant`, added afterwards, distinguishes the two encodings.

**Rule this establishes, and V2 must obey:** every wildcard, disjunction, or
`or`-clause in a spec predicate gets a dedicated probe asserting the wildcard
branch is *reachable*. A predicate that silently degenerates to its narrow case
passes every safety check ever written about it.

---

## §1 The bottleneck is `CHOOSE`, and it is not what the rewrite was supposed to fix

Invariants that avoid `ChainHead` return in 1–4 s. The one that reaches it
exhausts a 12 GB heap during constraint construction, on a domain of at most 5
blocks and 3 validators.

`ChainHead == IF \E h \in AllNodes : IsHead(h) THEN CHOOSE h \in AllNodes : IsHead(h) ELSE ...`

Cost structure. The blow-up is in **term construction**, MEASURED above; the
following account of why is INFERRED from that shape:

- `CHOOSE` is not a search, it is a *definite description*. Apalache must encode
  a Skolem constant plus the constraint that it satisfies `IsHead`, and — because
  `CHOOSE` is deterministic — that it is the same witness at every occurrence.
- `IsHead(h)` contains `\A n \in AllNodes : ... \A sib \in NodeChildren(n) : ... Precedes(sib, h)`.
- `Precedes` calls `Weight` twice; `Weight` calls `AttScore`; `AttScore` is a
  `Cardinality` over `Validators` each element of which calls `NodeInSubtree`;
  `NodeInSubtree` is four `Step` applications each with two function lookups.

Term size is therefore on the order of
`|AllNodes|² × branching × |Validators| × 4`, and `Canonical` instantiates the
whole thing again inside `S4`'s outer `\A r \in blocks`.

**This is the same bottleneck the v1 Apalache port hit.** Isolating `ChainHead`
by stubbing it to `Genesis` took that model from 7+ min to 10 s. The node-algebra
rewrite did not fix it, which retroactively identifies the cause: the bottleneck
was never the block-id encoding. It is computing a global fork-choice head inside
an invariant.

### §1.1 The `nodeAnc` rewrite: measured, and it did not fix `S4`

M2 (§2) was implemented and re-measured at identical bounds and heap.

| Check | Pre-rewrite | Post-rewrite |
|---|---|---|
| `TypeOK` | HOLDS ~2 s | **HOLDS 3 s** |
| `S5_ChildAttachesToOneBranch` | HOLDS ~2 s | **HOLDS 2 s** |
| `S6_FullImpliesVerified` | HOLDS ~2 s | **HOLDS 2 s** |
| `VAC_BoostReachesDescendant` | VIOLATED 4 s | **VIOLATED 2 s** |
| `AncRootsUnique` | n/a | **HOLDS 2 s** |
| `S4_PayloadStatusExclusive` | OOM at ~6 s | **OOM at 877 s** |

MEASURED. Removing `AncestorAt` bought roughly 150x more time before the heap
filled and **did not change the outcome.** The prediction that smaller terms
would fit in 12 GB was wrong.

**But the isolation is now conclusive.** The concern that
`nodeAnc \in [Ids -> SUBSET AncUniverse]` — a function space of size 1024^5 if
expanded — had merely traded one blow-up for another is refuted: every invariant
that avoids `ChainHead` still completes in 2-3 s *with that encoding active*.
Apalache handles it symbolically. Therefore `CHOOSE` over `IsHead` is the **sole**
cause of the S4 heap exhaustion, established by isolation rather than inferred
from shape.

What the rewrite did buy, all MEASURED: semantics preserved (`S5`, `S6` and the
boost probe unchanged), `AncRootsUnique` holds — so `NodeInSubtree` matching on
root really is equivalent to `get_ancestor` matching on slot, making it a faithful
transcription rather than an approximation — and the depth ceiling is gone, since
nothing unrolls any more.

### §1.2 M3 implemented: `S4` verified, heap wall gone

`CHOOSE` removed; `head` and `headPath` carried as state and constrained by
`HeadCertified` (§3). Same bounds, same heap.

| Check | Pre-M3 | Post-M3 |
|---|---|---|
| `S4_PayloadStatusExclusive` | **OOM at 877 s** | **HOLDS, 49 s** |
| `TypeOK` | HOLDS 3 s | HOLDS 48 s |
| `AncRootsUnique` | HOLDS 2 s | HOLDS 50 s |
| `S5_ChildAttachesToOneBranch` | HOLDS 2 s | HOLDS 46 s |
| `S6_FullImpliesVerified` | HOLDS 2 s | HOLDS 50 s |
| `VAC_BoostReachesDescendant` | VIOLATED 2 s | VIOLATED 53 s |
| `VAC_MultiBlock` | n/a | VIOLATED 50 s |
| `VAC_HeadDeep` | n/a | VIOLATED 52 s |
| `VAC_HeadFull` | n/a | VIOLATED 52 s |

MEASURED. **This is the repository's first successful check of a fork-choice head
property.** M1/M3 were the fix; the diagnosis held.

The cost moved rather than vanished: every check now pays ~46-53 s because
`HeadCertified` sits in `Init` and is therefore part of every state constraint.
Trading 2 s for 50 s on the cheap invariants to convert an OOM into a verdict is
the right trade, but it is a real regression on the others and it will matter
once actions multiply the state constraint per transition.

**The certificate does not over-constrain the domain.** `VAC_MultiBlock`,
`VAC_HeadDeep` and `VAC_HeadFull` all VIOLATE, so trees are non-trivial, the head
leaves genesis, and a FULL node can be head. Without those three, `S4` holding
would be worthless: `HeadCertified` is asserted inside `Init`, so an
unsatisfiable certificate would silently delete trees from the domain and every
invariant would hold over the remainder.

**OPEN: what forces `S4` is not understood.** The obvious hypothesis was that it
restates `HeadCertified`'s at-most-one-child-on-the-path conjunct. Tested by
deleting that conjunct and re-running: `S4` still HOLDS (52 s). So it has content
beyond that constraint, but no account of *what* content, and "holds at these
bounds" is not "holds". Do not cite `S4` as a protocol property until the
mechanism is identified.

### §1.3 Full probe suite, completed

The five original probes had never finished — the loop running them was killed
mid-run at 11:00, after `S6` and before any `VAC_` row, and the post-M3 batch only
covered the four new ones. Completed now, post-M3:

| Probe | Result | Time |
|---|---|---|
| `VAC_FullNodeCanonical` | VIOLATED | 51 s |
| `VAC_EmptyNodeCanonical` | VIOLATED | 52 s |
| `VAC_PrevSlotDecision` | VIOLATED | 52 s |
| `VAC_BoostApplies` | VIOLATED | 50 s |
| `VAC_TiebreakerZero` | VIOLATED | 52 s |

MEASURED. All nine probes now fire. Both payload statuses can be canonical, the
weight-zeroing previous-slot rule is reachable, and the `Tiebreaker = 0` branch —
a FULL node scoring *below* EMPTY because `should_extend_payload` is false — is
reachable rather than dead.

**`VAC_BoostApplies` is the weak one and must not be read as reassurance.**
`boostApplies` is a free boolean in this module, so the probe only shows the
solver can set it TRUE. It says nothing about whether the protocol would. Under
§4.3(e) it must be derived from `ShouldApplyProposerBoost`; until it is, this
module permits boost in states Gloas forbids — the D1 failure mode, still live.

### §1.4 Entry gates implemented: filtered tree + derived boost

Both gates required before `EPBSMultiSlotV2`, now in `EPBSNodes.tla` and measured.

**Finding #11.** `get_node_children`'s else-branch is `for root in blocks` where
`blocks` is `get_filtered_block_tree(store)`'s result, **not** `store.blocks`.
Ranging over every block — which is what the module did — lets `get_head` descend
into branches the protocol has pruned. This sat directly under `HeadCertified`,
i.e. under the one property that had just been verified.

`filter_block_tree` is a recursive DFS, and Apalache rejects recursion. But
viability propagates strictly *upward* from leaves — an internal block is viable
iff any child is — so

> `b` is in the filtered tree **iff** some viable leaf has `b` on its path

which the ancestry already in state expresses with no recursion. Carried as
`filtered`, pinned by `FilteredClosure`, so `NodeChildren` pays a set membership.

**`viableLeaf` is a named abstraction, not a model.** `correct_justified` and
`correct_finalized` need epochs, justification and `get_voting_source`, none of
which exist here. `viableLeaf` is an *unconstrained* subset of block-level
leaves, so the solver ranges over every possible viability assignment and results
hold for all of them. The filtering **structure** is exact; the viability
**predicate** is not modelled, and this variable is where that gap is named
rather than hidden.

**`boostApplies` is now derived**, `= ShouldApplyProposerBoost`, implementing the
§6 four-conjunct gate. `IsHeadWeak` uses an **absolute** threshold constant: the
spec's `calculate_committee_fraction` yields `(3 // 32) * 20 // 100 = 0` at model
scale, making `weight < 0` unsatisfiable and silently disabling every mechanism
gated on it. That is D1, and it made `ProposeHonestReorg` dead code through every
v1 run.

| Probe | Result | Time |
|---|---|---|
| `VAC_FilteredPrunes` | VIOLATED | 52 s |
| `VAC_HeadWeak` | VIOLATED | 53 s |
| `VAC_BoostSuppressed` | VIOLATED | 55 s |
| `VAC_MultiBlock` / `HeadDeep` / `HeadFull` | VIOLATED | 53-57 s |
| `VAC_BoostReachesDescendant` | VIOLATED | 58 s |

| Invariant | Result | Time |
|---|---|---|
| `TypeOK` | HOLDS | 54 s |
| `AncRootsUnique` | HOLDS | 51 s |
| `S4_PayloadStatusExclusive` | HOLDS | 51 s |
| `S5_ChildAttachesToOneBranch` | HOLDS | 50 s |
| `S6_FullImpliesVerified` | HOLDS | 52 s |

MEASURED. Twelve probes now fire and safety survives the filtered tree at no
measurable cost. **`VAC_BoostSuppressed` violating is the notable one**: the
four-conjunct suppression gate — the highest reachability risk in §6, with one
conjunct that was outright unsatisfiable in v1 — is reachable.

### §1.6 `EPBSMultiSlotV2` at length 3

| Invariant | Result | Time |
|---|---|---|
| `AncRootsUnique` | HOLDS | 489 s |
| `S4_PayloadStatusExclusive` | HOLDS | 351 s |
| `S5_ChildAttachesToOneBranch` | HOLDS | 446 s |
| `S6_FullImpliesVerified` | HOLDS | 546 s |

MEASURED, with actions, adversarial equivocation, the filtered block tree and the
derived boost gate all live. `S4` — which could not be *encoded* at 12 GB this
morning — verifies over a running transition system.

Cost curve: 7-30 s at length 1-2, 351-546 s at length 3. Steeply superlinear, so
a length-5 push is likely hours per invariant or an OOM, and should not be
assumed to scale just because M3 removed one wall.

`S4` beating `AncRootsUnique` (351 s vs 489 s) says cost tracks quantifier
structure, not conceptual difficulty: `S4` is a membership test on `headPath`,
`AncRootsUnique` quantifies over `nodeAnc` pairs at every state.

### §1.7 THE GAP THAT MATTERS: no protocol property is stated

`S4`, `S5`, `S6` and `AncRootsUnique` are **encoding-consistency** properties.
They would catch real structural errors — and did, twice — but not one of them is
a statement about ePBS.

The questions the ESP review raised are not failing and not vacuous. They are
**absent**:

- whether a payload-timely block resists reorg,
- how the PTC verdict couples to fork choice,
- whether multi-slot adversarial reorgs are reachable within a budget.

Every available hardening vector — longer traces, a stronger adversary, an
inductive invariant, liveness probes — makes the *existing* properties more
certain. None of them makes the model answer an ePBS question. Hardening first
would repeat D5 exactly: a rigorous, machine-checked, unbounded proof of a
theorem nobody asked about.

**Order of work: state the protocol properties, watch them fail or go vacuous,
fix that, and only then harden.**

### §1.8 Finding #12 — `should_extend_payload`, and what the PTC actually governs

The full spec:

```python
def should_extend_payload(store, root) -> bool:
    assert store.blocks[root].slot + 1 == get_current_slot(store)
    if not is_payload_verified(store, root): return False
    proposer_root = store.proposer_boost_root
    return ((payload_is_timely and payload_data_is_available)
            or proposer_root == Root()
            or store.blocks[proposer_root].parent_root != root
            or is_parent_node_full(store, store.blocks[proposer_root]))
```

Four disjuncts and a precondition. The module had the first two and described the
omission as "conservative". **It is not conservative — the missing disjuncts are
permissive**, and reading all four together gives a protocol fact this repository
had backwards:

> Extension proceeds **unless** the boosted block is a direct child of `r` that
> declared `r` EMPTY. The PTC verdict is decisive only inside that window.
> Everywhere else the payload is extended regardless of what the committee voted.

PTC timeliness does not broadly govern the tiebreak. It governs one configuration.

The dropped `assert` caused a concrete false positive. `Tiebreaker` only calls
`should_extend_payload` under `IsPrevSlotPayloadDecision`, so the module was safe;
but `VAC_P3_TiebreakDecisive` called it *directly*, evaluating it where the assert
would fail (`blockSlot[0] = 0`, `slot = 0`). It produced a 7-second "PTC influences
fork choice" witness whose state had **`ptcTimely = {}`** — an empty committee.
`ShouldExtendPayload` now carries the precondition as a guard so it cannot be read
outside its domain.

`PtcIsDecisiveFor(r)` names the window, and `VAC_P3_WindowReachable` probes it.

**The window needs five steps, so short runs say nothing.** `AdvanceSlot` zeroes
`boostRoot`, so the boosted block must be proposed *after* the slot boundary that
makes `r` previous-slot:

1. `AdvanceSlot` → slot 1
2. `ProposeBlock(r=1, par=0)` → `boostRoot = 1`
3. `RevealPayload(1)`
4. `AdvanceSlot` → slot 2, `boostRoot = 0`
5. `ProposeBlock(2, par=1, EMPTY)` → `boostRoot = 2`

`VAC_P3_WindowReachable` HOLDS at length 2 (47 s) — expected and carrying no
information. Derived from the action preconditions, not observed. Length 5 is the
first run that can answer it, and length 5 is the regime where cost was already
351-546 s at length 3.

### §1.9 First protocol-property results

| Check | len | Result | Time | Reading |
|---|---|---|---|---|
| `VAC_P3_WindowReachable` | 2 | HOLDS | 47 s | no information — window needs 5 steps |
| `VAC_P3_WindowReachable` | 5 | **VIOLATED** | 74 s | **the PTC-decisive window is reachable** |
| `P2_SuppressionRequiresDuplicateProposal` | 3 | HOLDS | 406 s | **VACUOUS** — see below |
| `VAC_P2_SuppressionOccurs` | 3 | HOLDS | — | suppression never reached at depth 3 |
| `P1_HeadMarginExceedsAdversary` | 3 | VIOLATED | 8 s | **DEGENERATE** — see below |

**P3's window is reachable, and the hand-derived path was right.** The five-step
execution predicted in §1.8 is realisable: length 2 could not reach it, length 5
does. So the model is capable of the state, no self-inflicted precondition blocks
it, and P3 is a meaningful question rather than a vacuous one. Had length 5
reported HOLDS, the first suspect would have been this module's own action guards,
not Gloas.

**P2 is vacuous at depth 3.** It is an implication whose antecedent is
`boostRoot # 0 /\ ~boostApplies`. `VAC_P2_SuppressionOccurs` HOLDS at length 3, so
that antecedent is never reached and P2's 406 s green says nothing whatever. The
static module's `VAC_BoostSuppressed` did violate — but existence in the static
domain and reachability under actions are different questions, and only the second
one licenses citing P2. Re-running at lengths 5 and 6.

**P1 is degenerate, not a finding.** `AdversaryCapacity = |ByzValidators| +
ProposerBoost = 1 + 2 = 3`, and total validator weight is also 3, so
`Weight(n) > Weight(sib) + 3` is unsatisfiable as soon as any block has both a
FULL and an EMPTY node. The violating state is `blocks = {0}`,
`payloadVerified = {0}`, `headPath = {(0,FULL),(0,PENDING)}` — genesis with a
verified payload. This is D1's shape for the third time today: a threshold that
degenerates at model scale and produces something shaped like a result. Making P1
meaningful needs
`|Validators| - |ByzValidators| > |ByzValidators| + ProposerBoost`, i.e. 5+
validators at the current boost — a cost increase to be paid deliberately.
**P1 must not be cited at this configuration.**

### §1.10 Finding #14 — abstraction soundness depends on property arity

`viableLeaf` was deliberately left unconstrained (§1.4), on the argument that
quantifying over every viability assignment makes a result hold for all of them.

**That argument is valid for one-state properties and invalid for two-state
ones.** For a single state, free choice is a strengthening. Across a transition
the solver re-picks viability each step — an adversary no protocol grants.

It manufactured a false reorg the first time a two-state property was checked:

```
State1: viableLeaf = {0,1}   filtered = {0,1}
State2: viableLeaf = {0,1}   filtered = {0,1}   head = (1,EMPTY)
State3: viableLeaf = {0}     filtered = {}      head = (0,EMPTY)   <- "reorg"
```

`viableLeaf` shrank between states, emptying the filtered tree and collapsing the
head to genesis. `equivocators = {}` throughout; nothing adversarial occurred.
`P1b_NoBlockReorgUnderBudget` VIOLATED at lengths 3 and 5 purely from this.

Every one-state result in this document is unaffected — free choice only ever
strengthened those. P1b was the repository's first two-state property and it was
exposed immediately.

**Fix**, following the `get_parent_payload_status` precedent: viability derives
from a block's own justified/finalized checkpoints, fixed when the block is
signed, so it is chosen once at `ProposeBlock` and frozen. This
under-approximates reality — viability does shift as checkpoints advance — and
that is stated in the module rather than hidden.

**The general rule, now the third methodology finding of the session:**

> Before reusing an abstraction in a property of different arity, re-derive its
> soundness. Free choice strengthens one-state claims and weakens two-state ones.

Alongside #13 (a restricted `Next` must be able to write every free variable of
the target property) and the probe rule (every probe needs its own check that it
is not satisfied at `Init`).

### §1.11 Reproducibility gap in commit `8d63479`

Every P3 result in §1.9 was measured at **bound 2**, but the tree was restored to
bound 4 before committing. A clean clone therefore runs a different model than
the one measured. `set_bounds.sh` exists so a bound can be named rather than
described — but a results table that does not name its bound is not reproducible,
and §1.9's did not. Bounds are now stated per row.

### §1.12 Finding #15 — unopposed is not dominant

`HeadBlockStrong` was the sibling comparison alone:

```tla
\A sibr \in BlockChildren(blockParent[r]) :
    sibr = r \/ BlockMargin(r) > BlockMargin(sibr) + AdversaryCapacity
```

With no siblings this is `\A x \in {} : P(x)` — **true**. A block that was merely
*first* was classified unassailable with **zero attestations**. A later sibling
then took the head on proposer boost and P1b reported a reorg:

```
State2: blocks={0,3}   head=(3,EMPTY)  prevHeadStrong=TRUE   latestMsg: nobody attested
State3: blocks={0,3,4} head=(4,EMPTY)  blockSlot[3]=blockSlot[4]=1, both parent 0
```

The gate was compromised by the same flaw: `VAC_P1b_PrevHeadStrong` violating at
State 3 was witnessing a *vacuously* strong block, so it passed for the wrong
reason and never protected the property. **Passing a gate is not evidence the
property is sound.**

Fixed by requiring absolute support, `BlockMargin(r) > AdversaryCapacity`. This
is what the 5-validator scale-up was for — at 3 validators honest weight cannot
exceed capacity 3 and the predicate is unsatisfiable, which was the original P1
degeneracy. The config was scaled but the threshold was left out of the
predicate, so the scale-up bought nothing until this fix.

**Fourth instance of one pattern today:**

| | Vacuous universal |
|---|---|
| D1 | `Frac(20) = 0` → `weight < 0` never true |
| P2 | antecedent never reached under actions |
| #13 | `ptcTimely = {}` always → antecedent unsatisfiable |
| #15 | `\A sibr \in {}` → unopposed read as dominant |

> Any universally-quantified predicate needs a witness that its domain is
> non-empty. Any threshold needs a witness that it can both fire and not fire.
> Checked separately, never inferred.

### §1.13 Cost: correctness changes dwarf domain-size changes

MEASURED across the session:

| Change | Kind | Effect |
|---|---|---|
| M3, eliminate `CHOOSE` | structural | S4: OOM → 49 s |
| `nodeAnc` static ancestry | term size | OOM at 6 s → OOM at 877 s (no fix) |
| bound 4 → bound 2 | domain size | **zero** (60 s → 66 s) |
| `HeadBlockStrong` made non-vacuous | correctness | length-3: 223 s → 20+ min |

Every domain-size knob reached for moved cost by nothing. The two changes that
moved it by orders of magnitude were structural (`CHOOSE`) and correctness
(non-vacuous predicate). A non-vacuous predicate forces genuine state-space
exploration and the solver charges for it — that cost is the *point*, not
overhead to be optimised away.

Consequence: P1b at length 7 on full `Next` is not tractable at 5 validators,
bound 4. `NextP1b` (§ in module) drops only `PtcVote`/`DaVote` and **retains
`AdvEquivocate`**, because `AttScore` excludes equivocators — equivocation is the
adversary's weight-SUBTRACTION capability, and removing it leaves an adversary
that can only push its own fork, never degrade an incumbent. A HOLDS obtained
that way would be worse than no result.

If `NextP1b` also fails to return, P1b is reported **unresolved at reachable
depth** — antecedent needs ≥7 steps, search does not complete — which is a
finding about tractability, not a protocol claim.

### §1.14 `NextP1b` at length 7: two silent kills, tractability unresolved

Two independent attempts to check `P1b_NoBlockReorgUnderBudget` at length 7 on
`NextP1b` (5 validators, 1 Byzantine, bound 4, `-Xmx12g`), both terminated by an
unexplained external kill rather than a normal Apalache exit.

| | Run 1 | Run 2 |
|---|---|---|
| Elapsed at death | 4h15m41s | 2h19m18s |
| Where | mid-check, State 5, **second** branch (first branch at State 5 had already held clean) | mid-check, State 5, **first** branch (never reached a `holds`) |
| `caffeinate -i` | no | yes |
| Log signature | cuts off with no exception, no `OutOfMemoryError`, no verdict | identical |
| RSS at death | last polled 4.3–5.6 GB, well under the 12 GB ceiling | last polled ~4.8 GB |

**What this rules out, by direct comparison rather than inference:**

- **A fixed-duration timeout or launchd watchdog.** The two elapsed times differ
  by a factor of 1.8. A fixed policy would kill both runs at the same wall-clock
  age.
- **Idle sleep.** Run 2 ran under `caffeinate -i`, which blocks idle sleep
  specifically, and died anyway. `pmset -g` also showed `sleep 0 (sleep
  prevented by powerd)` system-wide during run 1's death window.
- **JVM-level OOM.** Neither log contains `OutOfMemoryError`; RSS was never
  observed near 12 GB in the minutes before either death.
- **CPU ulimit, a wrapper-imposed timeout, or a kernel-logged kill/jetsam
  event.** All checked directly on Mini-3 and absent.

**What is NOT ruled out, and is the closest thing to a pattern:** both deaths
occurred during State-5 invariant checking, not during a transition search or at
any other depth. That is suggestive — something about the SMT query shape at
this depth may correlate with whatever kills the process — but it is not proof:
the two deaths hit different branches within that depth (run 1's second check,
run 2's first), so "the exact same query kills it" is not established, only
"something in this depth's query family does."

**Remaining candidate, untested:** processes launched via `nohup ... &` over SSH
are not immune to macOS terminating all processes tied to a login/audit session
when that session is judged idle or torn down, even with `disown`. A `launchd`
job would rule this in or out, at a cost of another several hours with no
guaranteed result. Not run — see §1.15.

**Tooling defect found while investigating:** the wrapper's exit-code capture
was wrong.

```bash
echo "elapsed=$(( $(date +%s) - S ))s exitcode=$?"
```

`$(date +%s)` runs as part of constructing this string, and any command that
runs overwrites `$?` before it is read later in the same statement. The printed
`exitcode=0` on run 2 reflects `date`'s exit status, not `apalache-mc`'s, and
must not be read as evidence of a clean exit. Correct form, if this is run
again: capture `$?` into a variable immediately after the command it measures,
before any other command runs.

```bash
apalache-mc check ... ; EC=$?; echo "elapsed=... exitcode=$EC"
```

**Status: P1b remains UNPROVEN.** No violation was found through State 5 on
either attempt — real evidence, though partial. Depths 6 and 7 were never
reached. The cause of both terminations is unidentified. This is recorded as a
tractability finding, not a protocol finding: nothing here says anything about
Gloas, only about the limits of checking this property this way on this
hardware.

### §1.15 What was deliberately not done

- **A third blind `nohup` retry.** Two runs disagreeing on elapsed time already
  ruled out the timeout and idle-sleep hypotheses; a third run under the same
  launch method would add a data point without a controlled variable to learn
  from.
- **A `launchd`-based run testing the session-teardown hypothesis.** Sound as an
  experiment, but several more hours for, at best, a single `NextP1b` result
  under the restricted (`PtcVote`/`DaVote`-dropped) adversary — not a proof of
  the real property. Not run.
- **A "minimal" `IndInv` built around an undefined `SupportDominance`
  conjunct.** Naming an operator is not defining one. A real inductive
  invariant needs each conjunct derived from spec text, typechecked, and
  expected to need its own fixes — §4's skeleton already required exactly that
  kind of correction for `HeadCertified`, and `NextP1b` itself needed two
  independent fixes (`PtcVote`/`DaVote` restoration, the `HeadBlockStrong`
  absolute-threshold fix) before it tested anything real. Writing `IndInv`
  correctly is separate, scoped work, not a same-session pivot.

### §1.16 `StructuralClosure` implemented and tested — first real `IndInv` building block

Following "yes go" back to small steps after the mega-prompt/`SupportSticky`
detour: picked the cheapest untested conjunct of the §4 `IndInv` skeleton and
actually implemented it, rather than sketching another name.

**Implemented** in `specs/EPBSNodes.tla`, next to `AncClosure`, unchanged from
the skeleton in §4.1.

**First test was circular, caught before being reported as a result.** Checked
against `MCEPBSNodes.tla`'s free-choice `Init` (`--length=0`): HOLDS, 101s. But
inspecting `Init` showed four of `StructuralClosure`'s five conjuncts —
`Genesis \in blocks`, `blockSlot[Genesis] = 0`, the parent-in-blocks/slot-order
conjunct, and `AncClosure` itself — are asserted **directly as `Init`
constraints** (`MCEPBSNodes.tla` lines 33–42, 61). Testing them against `Init`
could not fail; it restates the admission rule back at itself. Only the fifth
conjunct (every ancestor chain reaches Genesis) is a non-trivial consequence,
provable by induction on `blockParent`'s strict decrease to its one fixed point.
This HOLDS was not reported as a finding for that reason.

**The real test:** does `StructuralClosure` survive actual transitions.
`MCEPBSMultiSlotV2.tla`, concrete genesis-only `Init`, full `Next` (all seven
actions including `AdvEquivocate`), `--length=3`, 5 validators, bound 4:

```
Checker reports no error up to computation length 3
Total time: 2052.486 sec  (34m12s)
```

**HOLDS.** This is not circular: `Init` here is concrete, so the content of the
check is whether `ProposeBlock`'s parent/slot bookkeeping and `nodeAnc`'s update
actually maintain well-formedness as the tree grows under real actions.

**Scope, stated precisely:** this is bounded verification to length 3, not proof
of the inductive step. It shows `StructuralClosure` survived the traces explored
in that bound; it does not show `StructuralClosure /\ Next => StructuralClosure'`
for every reachable state, which is what would actually be needed as an `IndInv`
conjunct and is the next real test once more conjuncts exist to test alongside
it.

**Registered** in `check_registry.sh`'s explicit allowlist (alongside `TypeOK`,
`AncClosure`, `AncRootsUnique`) and in §2's table. Moved from "design only" to
"implemented" in the header inventory.

**Not yet done:** `MonotoneHistory`, `StoreCoherence`, `SupportAgrees`,
`AdversaryBudget` remain design-only. Each needs the same treatment —
implemented for real, tested against the smallest question first, checked for
circularity before its result is trusted.

### §1.5 What `EPBSNodes.tla` does NOT establish

Stated because a complete green suite invites the opposite conclusion.

1. **Leaf viability is abstracted, not modelled** (§1.4). The filtering structure
   is exact; `correct_justified` / `correct_finalized` are not modelled at all.
2. **`ShouldExtendPayload` under-approximates** — two disjuncts omitted.
3. **`S4`'s forcing mechanism is unknown** (§1.2).
4. **The absolute reorg threshold is a rescaling**, not the protocol's formula.
   Results about `is_head_weak` are about the rescaled model.
5. **There are no actions.** Every result here is about a static domain of trees.
   Nothing about transitions, slots, or adversarial behaviour is verified, because
   nothing about them is modelled. This remains the largest gap.

**Mandate M1 is therefore not a recommendation but a measured necessity.**
`EPBSMultiSlotV2` MUST NOT contain `CHOOSE` in any operator reachable from an
invariant. The head is carried as state and validated locally (§3, M3). M3 is now
the critical path: it is the only remaining candidate fix for `S4`.

---

## §2 The structural insight that makes V2 tractable: node ancestry is immutable

From `get_parent_payload_status`:

```python
parent_block_hash = block.body.signed_execution_payload_bid.message.parent_block_hash
message_block_hash = parent.body.signed_execution_payload_bid.message.block_hash
return PAYLOAD_STATUS_FULL if parent_block_hash == message_block_hash else PAYLOAD_STATUS_EMPTY
```

This is a function of **block body fields fixed at signing time.** It reads no
mutable store state. Therefore:

> The node-path from the justified root to `(b, PENDING)` is determined when `b`
> is created and never changes for the lifetime of `b`.

MEASURED from the spec text above. This is the single most important fact for
tractability, and v1 did not exploit it — it recomputed ancestry inside every
weight evaluation.

**Mandate M2.** Carry ancestry as state, written once at block insertion:

```tla
VARIABLE nodeAnc          \* @type: Int -> Set($node);

\* At AddBlock(b, parent, declaredStatus):
nodeAnc' = [nodeAnc EXCEPT ![b] =
              nodeAnc[parent] \union { [root |-> parent, ps |-> declaredStatus] }]
```

`NodeInSubtree` then becomes a set membership plus the PENDING wildcard, with no
walk and no recursion:

```tla
\* @type: ($node, $node) => Bool;
NodeInSubtree(v, target) ==
    \/ v = target
    \/ /\ target.ps = PENDING
       /\ \E a \in nodeAnc[v.root] : a.root = target.root
    \/ [root |-> target.root, ps |-> target.ps] \in nodeAnc[v.root]
```

This removes `AncestorAt`, `Step`, the four-step unrolling, and
`AncestorWalkTerminates` from the model entirely — along with the depth ceiling
that forced `MaxDepth = 4`. **Scaling past depth 3 was blueprint §2's open
problem; this is its answer.** The obligation that replaces the unrolling proof:

```tla
AncClosure ==
    \A b \in blocks : b # Genesis =>
        nodeAnc[b] = nodeAnc[blockParent[b]]
                     \union { [root |-> blockParent[b], ps |-> parentStatus[b]] }
```

which is a conjunct of `IndInv` (§4), not a separate check.

---

## §3 Head as state with a local certificate

**Mandate M3.** Replace computed `ChainHead` with a variable plus a certificate
that is linear in path length rather than quadratic in `|AllNodes|`.

```tla
VARIABLES head,        \* @type: $node;
          headPath     \* @type: Set($node);  justified root .. head, inclusive

\* Local certificate. No CHOOSE, no global quantifier over AllNodes.
HeadCertified ==
    /\ head \in headPath
    /\ NodeChildren(head) = {}
    /\ \A n \in headPath :
         n = head \/ \E c \in NodeChildren(n) :
                       /\ c \in headPath
                       /\ \A sib \in NodeChildren(n) : sib = c \/ Precedes(sib, c)
```

The inner `\A sib` ranges over `NodeChildren(n)`, which has at most 2 elements for
a PENDING node and at most the block branching factor otherwise — **not** over
`AllNodes`. Quantifier depth drops from 3 to 2 and the outer range from
`|AllNodes|` to `|headPath|`.

Actions that can change the head (`AddBlock`, `AddAttestation`, `RevealPayload`,
`AdvanceSlot`, every adversarial action) must re-establish `HeadCertified`, which
is where the solver work now lives — once per transition, not once per invariant
instantiation.

**Mandate M4 — memoize `AttScore`.** Carry `support \in [Ids -> [{EMPTY,FULL,PENDING} -> Int]]`
updated incrementally in `AddAttestation`, so `Weight` is a lookup. Guard it with

> ⚠ **DESIGN ONLY — NOT IMPLEMENTED.** The operator(s) below do not exist in
> any `.tla` file. Running Apalache against them fails with `Operator ... not
> found`, in about one second. That is a configuration error, not a tractability
> result.

```tla
SupportAgrees ==
    \A n \in AllNodes : support[n.root][n.ps] = AttScoreRef(n)
```

as an `IndInv` conjunct, where `AttScoreRef` is the literal transcription. This
keeps the expensive definition in the model as the *specification* of the cheap
one, so the optimization is checked rather than trusted.

---

## §4 `IndInv` skeleton

Target: `apalache-mc check --init=IndInv --inv=IndInv --length=1`. Success means
the property holds at **unbounded** depth, which is the only route past the depth
ceiling and the answer to the ESP review's multi-slot objection.

> ⚠ **DESIGN ONLY — NOT IMPLEMENTED.** The operator(s) below do not exist in
> any `.tla` file. Running Apalache against them fails with `Operator ... not
> found`, in about one second. That is a configuration error, not a tractability
> result.

```tla
IndInv ==
    /\ TypeOK
    /\ StructuralClosure      \* §4.1
    /\ MonotoneHistory        \* §4.2
    /\ StoreCoherence         \* §4.3
    /\ HeadCertified          \* §3
    /\ SupportAgrees          \* §3, M4
    /\ AdversaryBudget        \* §4.4
    /\ Safety                 \* the property being proved
```

### §4.1 `StructuralClosure` — the tree is a tree

**Implemented 2026-08-13** in `specs/EPBSNodes.tla`, next to `AncClosure`. See
§1.16 for the derivation and the first measured result.

```tla
StructuralClosure ==
    /\ Genesis \in blocks
    /\ blockSlot[Genesis] = 0
    /\ \A b \in blocks : b # Genesis =>
         /\ blockParent[b] \in blocks
         /\ blockSlot[blockParent[b]] < blockSlot[b]
    /\ AncClosure                                    \* §2
    /\ \A b \in blocks : Genesis \in {a.root : a \in nodeAnc[b]} \/ b = Genesis
```

Without the last conjunct, induction can invent a block whose ancestry set omits
the root — a disconnected fragment that no reachable state contains. This is the
single most common CTI source in tree models. INFERRED.

### §4.2 `MonotoneHistory` — the conjuncts that kill time-travel CTIs

Induction has no memory of how a state was reached, so anything that only ever
grows must be *stated* to only ever grow.

> ⚠ **DESIGN ONLY — NOT IMPLEMENTED.** The operator(s) below do not exist in
> any `.tla` file. Running Apalache against them fails with `Operator ... not
> found`, in about one second. That is a configuration error, not a tractability
> result.

```tla
MonotoneHistory ==
    /\ \A v \in Validators : latestMsg[v].slot =< slot
    /\ \A v \in Validators : latestMsg[v].root \in blocks
    /\ payloadVerified \subseteq blocks
    /\ equivocators \subseteq ByzValidators
    /\ \A b \in blocks : blockSlot[b] =< slot
```

The LMD monotonicity of `latestMsg` (§ `update_latest_messages`: a message is
recorded only if `message.slot > store.latest_messages[i].slot`) cannot be stated
on a single state. It is a **two-state** property and belongs in `Next`, with the
one-state shadow `latestMsg[v].slot =< slot` above. Attempting to write it as a
one-state conjunct is the second most common CTI source here. INFERRED.

### §4.3 `StoreCoherence` — the four-variable interaction

This is the section the request asked for specifically. The four variables are
not independent, and every missing relation below is a CTI generator.

> ⚠ **DESIGN ONLY — NOT IMPLEMENTED.** The operator(s) below do not exist in
> any `.tla` file. Running Apalache against them fails with `Operator ... not
> found`, in about one second. That is a configuration error, not a tractability
> result.

```tla
StoreCoherence ==
    \* (a) is_payload_verified(root) == root in store.payloads. A FULL node is a
    \*     candidate ONLY for a verified payload -- get_node_children.
    /\ \A n \in AllNodes : n.ps = FULL => n.root \in payloadVerified

    \* (b) PTC and DA verdicts are only meaningful for blocks that exist, and a
    \*     timely verdict presupposes the payload was delivered at all.
    /\ ptcTimely   \subseteq blocks
    /\ daAvailable \subseteq blocks
    /\ ptcTimely   \subseteq payloadVerified

    \* (c) should_extend_payload reads ptcTimely and daAvailable; without (b) the
    \*     induction can set it TRUE for an unverified root and manufacture a
    \*     FULL-node tiebreak win that no reachable state permits.
    /\ \A b \in blocks : ShouldExtendPayload(b) => b \in payloadVerified

    \* (d) boostRoot is a CURRENT-slot proposal or Root(). Omitting this yields
    \*     the exact D1 false positive from v1: boost applied to an off-schedule
    \*     adversarial block, reported as a protocol finding.
    /\ boostRoot \in blocks \union {0}
    /\ boostRoot # 0 => blockSlot[boostRoot] = slot

    \* (e) boostApplies is DERIVED, never free. See §6.
    /\ boostApplies = ShouldApplyProposerBoost
```

Conjunct (e) is mandatory. If `boostApplies` is left as an unconstrained boolean
— as it is in `EPBSNodes.tla`, deliberately, because that module has no actions —
induction will set it TRUE in states where the protocol sets it FALSE, and every
resulting counterexample is spurious.

**`ptcTimely ⊆ payloadVerified` (b) is OPEN.** It is INFERRED from the fact that a
PTC vote concerns a delivered payload, not read off a spec line. Verify against
`on_payload_attestation_message` and `store.block_timeliness` before relying on
it; if false, the conjunct must be weakened or the CTI it prevents accepted.

### §4.4 `AdversaryBudget`

> ⚠ **DESIGN ONLY — NOT IMPLEMENTED.** The operator(s) below do not exist in
> any `.tla` file. Running Apalache against them fails with `Operator ... not
> found`, in about one second. That is a configuration error, not a tractability
> result.

```tla
AdversaryBudget ==
    /\ Cardinality(equivocators) =< MaxEquivocations
    /\ Cardinality(ByzValidators) * 3 < Cardinality(Validators)   \* < 1/3
```

---

## §5 CTI triage procedure

When `--init=IndInv --inv=IndInv --length=1` reports a violation, the trace is a
**counterexample to induction**, not a bug. Triage in this order:

1. **Is the pre-state reachable?** Check it against `Init` plus the actions. If
   not, `IndInv` is too weak — add the conjunct that excludes it. Do **not**
   weaken the safety property.
2. **Which variable in the pre-state is impossible?** Map it to §4.1–§4.4. The
   four highest-frequency sources, INFERRED: disconnected `nodeAnc`, `latestMsg`
   in the future, `boostApplies` free, `payloadVerified` inconsistent with a FULL
   node.
3. **If the pre-state is reachable, the safety property is false.** Minimize and
   cross-check against the spec text before believing it. Four of the nine
   findings in this repository's audit were false positives that survived until
   someone read the source.

**Every new conjunct added to `IndInv` needs a vacuity probe** asserting the
states it excludes were not the only ones satisfying the property. Strengthening
until `IndInv` is trivially unsatisfiable is a proof of nothing, and it is the
failure mode this whole exercise exists to prevent.

---

## §6 `AdvProposerEquivocate` — the exact gate, and a correction

The request stated the rule as "slot N−1 proposer equivocation suppresses slot N
proposer boost." That is the right mechanism but **drops two necessary
conditions.** `should_apply_proposer_boost` in full:

```python
if store.proposer_boost_root == Root(): return False
block = store.blocks[store.proposer_boost_root]
parent = store.blocks[block.parent_root]; slot = block.slot
if parent.slot + 1 < slot: return True                    # parent NOT from previous slot
if not is_head_weak(store, block.parent_root): return True # parent NOT weak
equivocations = [root for root, b in store.blocks.items()
                 if (store.block_timeliness[root][PTC_TIMELINESS_INDEX]
                     and b.proposer_index == parent.proposer_index
                     and b.slot + 1 == slot
                     and root != block.parent_root)]
return len(equivocations) == 0
```

Boost is suppressed only under a **four-way conjunction**:

1. `boostRoot ≠ Root()`, and
2. `parent.slot + 1 = slot` — the parent *is* from the previous slot, and
3. `is_head_weak(parent_root)` — the parent *is* weak, and
4. there exists a block that is **PTC-timely**, by the **same proposer** as the
   parent, at the **same slot** as the parent, distinct from the parent.

Modelling this as "equivocation ⟹ no boost" gives a strictly stronger adversary
than the protocol, and any attack found under it is a false positive of exactly
the D1 kind. Note also condition 4's timeliness requirement: the adversary must
equivocate *and* have the equivocation seen as timely by the PTC.

> ⚠ **DESIGN ONLY — NOT IMPLEMENTED.** The operator(s) below do not exist in
> any `.tla` file. Running Apalache against them fails with `Operator ... not
> found`, in about one second. That is a configuration error, not a tractability
> result.

```tla
\* @type: () => Bool;
ShouldApplyProposerBoost ==
    IF boostRoot = 0 THEN FALSE
    ELSE LET p == blockParent[boostRoot]
             s == blockSlot[boostRoot]
         IN IF blockSlot[p] + 1 < s      THEN TRUE
            ELSE IF ~IsHeadWeak(p)       THEN TRUE
            ELSE ~\E r \in blocks :
                    /\ r \in ptcTimely
                    /\ proposer[r] = proposer[p]
                    /\ blockSlot[r] + 1 = s
                    /\ r # p

AdvProposerEquivocate(pr, s) ==
    /\ pr \in ByzValidators
    /\ Cardinality(equivocators) < MaxEquivocations
    /\ \E b1, b2 \in blocks :
         /\ b1 # b2
         /\ proposer[b1] = pr /\ proposer[b2] = pr
         /\ blockSlot[b1] = s /\ blockSlot[b2] = s
    /\ equivocators' = equivocators \union {pr}
    /\ UNCHANGED << ... >>
```

**Reachability is the risk, not safety.** Four conjuncts must hold simultaneously,
and condition 3 depends on `is_head_weak`, which in v1 was measured to be
**unsatisfiable at small committee sizes** — `calculate_committee_fraction` with
`REORG_HEAD_WEIGHT_THRESHOLD=20` floors to 0, so `weight < 0` never holds (D1).

**Mandate M5.** Before any property about `AdvProposerEquivocate` is reported,
run a probe per conjunct *and* one for the conjunction:

> ⚠ **DESIGN ONLY — NOT IMPLEMENTED.** The operator(s) below do not exist in
> any `.tla` file. Running Apalache against them fails with `Operator ... not
> found`, in about one second. That is a configuration error, not a tractability
> result.

```tla
VAC_ParentPrevSlot   == \A n \in AllNodes : blockSlot[blockParent[n.root]] + 1 # blockSlot[n.root]
VAC_ParentWeak       == \A b \in blocks : ~IsHeadWeak(b)
VAC_TimelyEquivExists== ~\E r \in blocks : r \in ptcTimely /\ \E p \in blocks : proposer[r] = proposer[p] /\ r # p
VAC_BoostSuppressed  == boostRoot = 0 \/ ShouldApplyProposerBoost
```

All four must report VIOLATED. Any that HOLDS means that branch is unreachable at
the chosen bounds and every conclusion downstream of it is vacuous. `is_head_weak`
requires absolute thresholds at model scale — percentage-of-committee floors to
zero and silently disables the mechanism.

---

## §7 Obligations this document does NOT discharge

Stated explicitly so no reader mistakes a plan for a result.

1. **Whether `IndInv` can be made inductive at all is OPEN.** No inductive
   invariant has ever been established for this model. §4 is a skeleton with
   named obligations, not a proof.
2. **`get_filtered_block_tree` is unmodelled.** `get_head` descends the *filtered*
   tree, which prunes branches whose leaves have incompatible justified/finalized
   checkpoints. Nothing in `EPBSNodes.tla` or this spec models it. Any head result
   is therefore about an unfiltered tree and may differ from the protocol's.
3. **`is_head_weak` needs the equivocator add-back loop**, which needs per-validator
   balances and committee structure. §6 assumes an `IsHeadWeak` that does not yet
   exist.
4. **`ptcTimely ⊆ payloadVerified` (§4.3b) is INFERRED**, not read from spec text.
5. **`ShouldExtendPayload` under-approximates** — it omits two disjuncts requiring
   `blockParent` of `boostRoot`. Conservative for the FULL branch; not faithful.
6. **`coq/EPBSForkChoice.v` DELETED (2026-08-12).** It proved a theorem about `PayloadBoost`, a
   quantity Gloas does not have (D5). It is unaffected by anything in this
   document and remains the strongest *wrong* result in the repository.

---

## §8 Order of work

1. `NodeInSubtree` PENDING-wildcard fix — **DONE**, probe VIOLATED in 4 s.
2. Re-run the full `EPBSNodes.tla` suite against the corrected `is_ancestor`.
   Results in §0 for `S5`/`S6` predate it; they do not depend on it, but that
   must be confirmed rather than assumed.
3. Resolve `S4`'s non-termination by M1+M3. If `S4` returns quickly once
   `CHOOSE` is gone, that confirms the §1 localization.
4. Implement M2 (`nodeAnc` as state), delete `AncestorAt` and the depth ceiling.
5. Build `EPBSMultiSlotV2` on the corrected algebra with actions.
6. Only then attempt `--init=IndInv --inv=IndInv --length=1`.

Nothing in this repository goes to the ESP reviewers until step 6 either succeeds
or its failure is characterized.

---

## §2 Probe and invariant registry

Every checkable operator in the two active specs, what it asserts, and the
outcome that means "working". **A probe whose expected result is unrecorded is
worse than no probe** — a HOLDS looks like success either way. 13 of these were
undocumented until a dead-code sweep found them.

Probes are DELIBERATELY FALSE: for them, VIOLATED is the pass condition and
HOLDS means the branch is unreachable, which invalidates anything that depends
on it.

Run as `apalache-mc check --cinit=ConstInit --init=Init --next=<N> --inv=<name> --length=<L> <harness>`.

### `EPBSNodes.tla` / `MCEPBSNodes.tla` — static algebra, `--next=Next --length=0`

| Operator | Kind | Asserts | Expected | Measured |
|---|---|---|---|---|
| `TypeOK` | invariant | types and domains | HOLDS | HOLDS 82 s |
| `AncClosure` | conjunct | `nodeAnc` matches `get_ancestor` recursion | in `Derived` | — |
| `AncRootsUnique` | invariant | one node per root in an ancestor set | HOLDS | HOLDS 77 s |
| `S4_PayloadStatusExclusive` | invariant | FULL and EMPTY never both canonical | HOLDS | HOLDS 76 s |
| `S5_ChildAttachesToOneBranch` | invariant | a child attaches to one parent branch | HOLDS | HOLDS 77 s |
| `S6_FullImpliesVerified` | invariant | FULL node ⇒ payload verified | HOLDS | HOLDS 77 s |
| `VAC_FullNodeCanonical` | probe | a FULL node can be canonical | VIOLATED | VIOLATED 100 s |
| `VAC_EmptyNodeCanonical` | probe | an EMPTY node can be canonical | VIOLATED | VIOLATED 52 s |
| `VAC_PrevSlotDecision` | probe | the weight-zeroing rule is reachable | VIOLATED | VIOLATED 92 s |
| `VAC_TiebreakerZero` | probe | `Tiebreaker = 0` branch is live | VIOLATED | VIOLATED 128 s |
| `VAC_BoostReachesDescendant` | probe | boost propagates past its own root | VIOLATED | VIOLATED 85 s |
| `VAC_FilteredPrunes` | probe | `filter_block_tree` really prunes | VIOLATED | VIOLATED 81 s |
| `VAC_HeadWeak` | probe | `is_head_weak` can fire (D1 guard) | VIOLATED | VIOLATED 80 s |
| `VAC_BoostSuppressed` | probe | the 4-conjunct suppression gate is reachable | VIOLATED | VIOLATED 102 s |
| `VAC_HeadDeep` | probe | head can leave genesis | VIOLATED | VIOLATED 54 s |
| `VAC_HeadFull` | probe | a FULL node can be head | VIOLATED | VIOLATED 57 s |
| `VAC_MultiBlock` | probe | trees are non-trivial | VIOLATED | VIOLATED 53 s |
| `VAC_BoostApplies` | probe | `boostApplies` can be TRUE | VIOLATED | **weak** — free boolean in this module; says nothing about the protocol |

### `EPBSMultiSlotV2.tla` / `MCEPBSMultiSlotV2.tla` — transitions

| Operator | Kind | Asserts | Expected | Measured |
|---|---|---|---|---|
| `RVAC_SlotAdvanced` | probe | a transition is possible at all | VIOLATED | VIOLATED len 1 |
| `RVAC_PayloadVerified` | probe | `RevealPayload` fires | VIOLATED | VIOLATED len 1, 7 s |
| `RVAC_Equivocated` | probe | `AdvEquivocate` fires | VIOLATED | VIOLATED len 1, 11 s |
| `RVAC_BlockProposed` | probe | `ProposeBlock` fires | VIOLATED | VIOLATED len 2, 15 s |
| `RVAC_Attested` | probe | `Attest` fires | VIOLATED | VIOLATED len 2, 30 s |
| `RVAC_HeadMoved` | probe | the head moves off genesis | VIOLATED | VIOLATED len 3, 3 s |
| `VAC_PtcTimelyNonEmpty` | probe | `ptcTimely` is writable (#13 guard) | VIOLATED | VIOLATED len 3, 16 s |
| `StructuralClosure` | invariant | tree well-formedness + Genesis-reachability | HOLDS | see §1.16 |
| `VAC_DaAvailableNonEmpty` | probe | `daAvailable` is writable (#13 guard) | VIOLATED | VIOLATED len 3, 18 s |
| `VAC_BothPtcAndDa` | probe | one block in both sets | VIOLATED | VIOLATED len 4, 144 s |
| `VAC_P3_WindowReachable` | probe | the PTC-decisive window is entered | VIOLATED | VIOLATED len 5, 56 s |
| `VAC_P3_TiebreakDecisive` | probe | the tiebreak actually decides | VIOLATED | **VIOLATED len 7, 3037 s** |
| `VAC_P3_UntimelyLosesInWindow` | probe | an untimely payload loses the tiebreak | VIOLATED | **not yet run** |
| `P3_TimelyPayloadNotSkippedOnTie` | property | a timely payload is never skipped on tiebreak | HOLDS | **not run against the corrected predicate** |
| `P2_SuppressionRequiresDuplicateProposal` | property | suppression ⇒ a duplicate proposal exists | HOLDS | **VACUOUS** — antecedent unreachable at len 3 |
| `VAC_P2_SuppressionOccurs` | probe | suppression is reachable | VIOLATED | **HOLDS len 3** — this is why P2 is vacuous |
| `VAC_P1b_HeadBlockMoves` | probe | the head's *block* changes | VIOLATED | VIOLATED len 3, 26 s |
| `VAC_P1b_PrevHeadStrong` | probe | a non-genesis head can be strong | VIOLATED | HOLDS len 3, 1673 s — correct, needs len ≥ 7 |
| `P1b_NoBlockReorgUnderBudget` | property | a strong block is not reorged | HOLDS | **UNPROVEN** — antecedent needs ≥7 steps |

### Deleted

| Operator | Why |
|---|---|
| `P1_HeadMarginExceedsAdversary` | Degenerate: compared a `Weight` that is zeroed in the window that matters, false at any validator count |
| `VAC_P1_MarginTight` | Its probe |
| `VAC_P3_UntimelyLoses` | Pre-#12: called `ShouldExtendPayload` without pinning the decisive window |
