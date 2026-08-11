# V2 Verification Spec — inductive invariants and SMT tractability for `EPBSMultiSlotV2`

Engineering specification for the phase after `EPBSNodes.tla`. Every claim is
tagged MEASURED (with the command that produced it), INFERRED, or OPEN.

---

## §0 Measured ground truth

All on Mini-3, Apalache 0.61.0, `JVM_ARGS=-Xmx12g`, config
`Validators={v1,v2,v3}, ByzValidators={v3}, ProposerBoost=2, CurrentSlot=3, MaxDepth=4`.

```
apalache-mc check --cinit=ConstInit --init=Init --next=Next --inv=<INV> --length=0 MCEPBSNodes.tla
```

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

**Mandate M1.** `EPBSMultiSlotV2` MUST NOT contain `CHOOSE` in any operator
reachable from an invariant. The head is carried as state and validated locally.

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
6. **`coq/EPBSForkChoice.v` still proves a theorem about `PayloadBoost`**, a
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
