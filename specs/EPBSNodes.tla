---------------------------- MODULE EPBSNodes ----------------------------
(***************************************************************************)
(* Gloas fork-choice NODE ALGEBRA, in isolation.                            *)
(*                                                                          *)
(* No actions, no adversary, no temporal dynamics. This module exists to get *)
(* the (root, payload_status) algebra right before anything is built on it, *)
(* because v1 was built on a block-id tree and every result it produced was  *)
(* an artifact of that choice.                                              *)
(*                                                                          *)
(* Every operator names the consensus-specs function it transcribes.        *)
(* Sources: specs/gloas/fork-choice.md and specs/phase0/fork-choice.md.     *)
(*                                                                          *)
(* Note on scope: the blueprint's §5 step 1 said "no slots". That was wrong. *)
(* is_previous_slot_payload_decision compares block slot against the CURRENT *)
(* slot, so Weight and Tiebreaker cannot be transcribed without one.        *)
(* CurrentSlot is a CONSTANT here: enough to be faithful, not enough to      *)
(* introduce temporal behaviour.                                            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Validators,
    \* @type: Set(Str);
    ByzValidators,
    \* @type: Int;
    ProposerBoost,
    \* @type: Int;
    CurrentSlot,
    \* @type: Int;
    MaxDepth,         \* bounds the id/slot range only; no walk to bound now
    \* @type: Int;
    \* ABSOLUTE reorg-head threshold. calculate_committee_fraction computes
    \*   (total_active_balance // SLOTS_PER_EPOCH) * REORG_HEAD_WEIGHT_THRESHOLD // 100
    \* which at model scale is (3 // 32) * 20 // 100 = 0, making is_head_weak
    \* (weight < 0) unsatisfiable and silently disabling every mechanism gated on
    \* it. That is D1, and it made ProposeHonestReorg dead code through every v1
    \* run. Rescaled to an absolute count here; VAC_HeadWeak proves it fires.
    ReorgHeadWeightAbs

\* PAYLOAD_STATUS_* , gloas/fork-choice.md table
EMPTY   == 0
FULL    == 1
PENDING == 2

Genesis == 0

(*
  @typeAlias: node = { root: Int, ps: Int };
  @typeAlias: msg = { slot: Int, root: Int, present: Bool };
*)
EPBSNodes_typedefs == TRUE

VARIABLES
    \* @type: Set(Int);
    blocks,
    \* @type: Int -> Int;
    blockSlot,
    \* @type: Int -> Int;
    blockParent,
    \* @type: Int -> Int;      get_parent_payload_status: which parent node this
    parentStatus,              \* block declares it builds upon
    \* @type: Set(Int);        store.payloads / is_payload_verified
    payloadVerified,
    \* @type: Set(Int);        roots whose PTC judged the payload timely
    ptcTimely,
    \* @type: Set(Int);        roots whose data availability vote passed
    daAvailable,
    \* @type: Str -> $msg;     store.latest_messages
    latestMsg,
    \* @type: Set(Str);        store.equivocating_indices
    equivocators,
    \* @type: Int;             store.proposer_boost_root, 0 = Root()
    boostRoot,
    \* @type: Bool;            should_apply_proposer_boost, a Store property
    boostApplies,
    \* @type: Int -> Set($node);
    \* STRICT node-ancestors of any node with this root, nearest-first order
    \* irrelevant (it is a set). Indexed by ROOT, not by node, because
    \* get_ancestor's first step leaves the current root regardless of payload
    \* status -- so all three nodes of one root share an ancestor set.
    \* Written once at block insertion; see AncClosure.
    nodeAnc,
    \* @type: $node;      get_head's result, carried rather than computed
    head,
    \* @type: Set($node); justified root .. head inclusive. See HeadCertified.
    headPath,
    \* @type: Int -> Str;  block proposer, for the equivocation gate
    proposer,
    \* @type: Set(Int);
    \* ABSTRACTION. filter_block_tree calls a leaf viable when correct_justified
    \* and correct_finalized both hold. Those need epochs, justification and
    \* get_voting_source, none of which are modelled. This carries leaf viability
    \* as an UNCONSTRAINED subset of block-level leaves instead, so the solver
    \* ranges over every possible viability assignment and results hold for all
    \* of them. The filtering STRUCTURE is exact; the viability PREDICATE is not
    \* modelled at all, and this variable is where that gap is named.
    viableLeaf,
    \* @type: Set(Int);   get_filtered_block_tree's result. See FilteredClosure.
    filtered

vars == << blocks, blockSlot, blockParent, parentStatus, payloadVerified,
           ptcTimely, daAvailable, latestMsg, equivocators, boostRoot,
           boostApplies, nodeAnc, head, headPath, proposer, viableLeaf,
           filtered >>

ASSUME ValidatorsNonEmpty == Validators # {}
ASSUME ByzSubset          == ByzValidators \subseteq Validators
\* MaxDepth no longer bounds an unrolled walk -- ancestry is state now, so there
\* is no recursion to unroll and no depth ceiling. It bounds only the id/slot
\* range below, and may be raised freely.
ASSUME DepthOK == MaxDepth = 4

\* Apalache requires a LITERAL constant range in [a..b]; it will not accept
\* 0..MaxDepth. ASSUME DepthOK keeps these in sync -- change one without the
\* other and the ASSUME fails at parse time.
Ids   == 0 .. 4
Slots == 0 .. 4

\* Every node that may legitimately appear in an ancestor set. Strict ancestors
\* always carry a DECLARED status, never PENDING -- get_ancestor replaces the
\* status at each step with get_parent_payload_status, which returns FULL or
\* EMPTY only.
AncUniverse == { [root |-> r, ps |-> q] : r \in Ids, q \in {EMPTY, FULL} }

-----------------------------------------------------------------------------
(***************************************************************************)
(* Vote-to-node resolution                                                  *)
(***************************************************************************)

\* get_supported_node, gloas/fork-choice.md:390.
\* Attest in the same slot as the block and you support PENDING; attest later
\* and you support FULL or EMPTY per the flag carried.
\* @type: ($msg) => $node;
SupportedNode(m) ==
    IF blockSlot[m.root] < m.slot
    THEN [root |-> m.root, ps |-> IF m.present THEN FULL ELSE EMPTY]
    ELSE [root |-> m.root, ps |-> PENDING]

(***************************************************************************)
(* Ancestry -- STATE, not a walk.                                           *)
(*                                                                          *)
(* get_parent_payload_status reads only block-body fields fixed at signing:  *)
(*                                                                          *)
(*   parent_block_hash = block.body.signed_execution_payload_bid            *)
(*                            .message.parent_block_hash                    *)
(*   message_block_hash = parent.body.signed_execution_payload_bid          *)
(*                             .message.block_hash                          *)
(*   return FULL if parent_block_hash == message_block_hash else EMPTY      *)
(*                                                                          *)
(* It reads NO mutable store state. So the node-path from the justified root *)
(* to a block is fixed the moment the block is signed and never changes.    *)
(* v1 recomputed it inside every weight evaluation; that is what inlined an  *)
(* ancestor walk four levels deep into IsHead and exhausted a 12GB heap      *)
(* during constraint construction.                                          *)
(***************************************************************************)

\* is_ancestor, gloas. Root must match; payload status must match OR the target
\* is PENDING, which is a wildcard over status. See the finding note below.
\* @type: ($node, $node) => Bool;
NodeMatches(a, target) ==
    /\ a.root = target.root
    /\ (a.ps = target.ps \/ target.ps = PENDING)

\* is_ancestor over the stored ancestor set. Each root appears at most once in
\* nodeAnc, so matching on root is equivalent to get_ancestor's match on slot,
\* without the walk.
\*
\* THE PENDING WILDCARD IS LOAD-BEARING. get_ancestor carries the DECLARED
\* parent status upward and never yields PENDING for a strict ancestor, so
\* writing this as record equality makes every PENDING target unreachable --
\* and BoostNode is (boostRoot, PENDING), so proposer boost would propagate to
\* nothing. That bug typechecked cleanly and passed S5 and S6.
\* VAC_BoostReachesDescendant is the only check that distinguishes them.
\* @type: ($node, $node) => Bool;
NodeInSubtree(v, target) ==
    \/ NodeMatches(v, target)
    \/ \E a \in nodeAnc[v.root] : NodeMatches(a, target)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Weight                                                                   *)
(***************************************************************************)

\* get_attestation_score, phase0:323. Equivocators are EXCLUDED -- that is why
\* is_head_weak adds their balance back in its own loop. Unit weight stands in
\* for effective_balance.
\* @type: ($node) => Int;
AttScore(n) ==
    Cardinality({ v \in Validators :
        /\ v \notin equivocators
        /\ NodeInSubtree(SupportedNode(latestMsg[v]), n) })

\* is_previous_slot_payload_decision, gloas. BOTH conjuncts are required:
\* dropping the slot comparison zeroes the weight of every EMPTY/FULL node.
\* @type: ($node) => Bool;
IsPrevSlotPayloadDecision(n) ==
    /\ blockSlot[n.root] + 1 = CurrentSlot
    /\ n.ps \in {EMPTY, FULL}

\* @type: () => $node;
BoostNode == [root |-> boostRoot, ps |-> PENDING]

\* @type: ($node) => Bool;
BoostInSubtree(n) == boostRoot # 0 /\ NodeInSubtree(BoostNode, n)

\* is_head_weak, gloas. Attestation score on the PENDING node PLUS the
\* equivocator balances added back -- get_attestation_score excludes them, and
\* this loop restores them. Unit balances, so the add-back is a count.
\* Threshold is ABSOLUTE; see ReorgHeadWeightAbs for why the spec's percentage
\* cannot be used at model scale.
\* @type: (Int) => Bool;
IsHeadWeak(r) ==
    AttScore([root |-> r, ps |-> PENDING]) + Cardinality(equivocators)
        < ReorgHeadWeightAbs

\* should_apply_proposer_boost, gloas. Boost is SUPPRESSED only under a
\* four-way conjunction: boostRoot set, AND parent from the previous slot, AND
\* parent weak, AND a PTC-timely same-slot same-proposer equivocation exists.
\* Reading it as "equivocation implies no boost" drops the middle two and yields
\* a strictly stronger adversary than the protocol.
\* @type: () => Bool;
ShouldApplyProposerBoost ==
    IF boostRoot = 0 THEN FALSE
    ELSE LET par == blockParent[boostRoot]
             sl  == blockSlot[boostRoot]
         IN IF blockSlot[par] + 1 < sl THEN TRUE
            ELSE IF ~IsHeadWeak(par)   THEN TRUE
            ELSE ~\E r \in blocks :
                    /\ r \in ptcTimely
                    /\ proposer[r] = proposer[par]
                    /\ blockSlot[r] + 1 = sl
                    /\ r # par

\* get_weight, gloas:521. No payload term exists -- that absence is D5.
\* @type: ($node) => Int;
Weight(n) ==
    IF IsPrevSlotPayloadDecision(n) THEN 0
    ELSE AttScore(n)
         + (IF boostApplies /\ BoostInSubtree(n) THEN ProposerBoost ELSE 0)

\* should_extend_payload, gloas. Omits the two disjuncts that need blockParent
\* of boostRoot; those return TRUE more often, so this under-approximates and
\* is conservative for the FULL branch.
\* @type: (Int) => Bool;
ShouldExtendPayload(r) ==
    /\ r \in payloadVerified
    /\ \/ (r \in ptcTimely /\ r \in daAvailable)
       \/ boostRoot = 0

\* get_payload_status_tiebreaker, gloas. FULL scores 2 ONLY when
\* should_extend_payload holds, otherwise 0 -- below EMPTY's 1.
\* @type: ($node) => Int;
Tiebreaker(n) ==
    IF IsPrevSlotPayloadDecision(n)
    THEN IF n.ps = EMPTY THEN 1
         ELSE IF ShouldExtendPayload(n.root) THEN 2 ELSE 0
    ELSE n.ps

\* get_head's max key: (weight, root, tiebreaker), lexicographic.
\* @type: ($node, $node) => Bool;
Precedes(a, b) ==
    \/ Weight(a) < Weight(b)
    \/ (Weight(a) = Weight(b) /\ a.root < b.root)
    \/ (Weight(a) = Weight(b) /\ a.root = b.root /\ Tiebreaker(a) < Tiebreaker(b))

-----------------------------------------------------------------------------
(***************************************************************************)
(* The alternating tree                                                     *)
(***************************************************************************)

(***************************************************************************)
(* get_filtered_block_tree / filter_block_tree, phase0.                     *)
(*                                                                          *)
(* The spec is a recursive DFS: a block with children is viable iff ANY child *)
(* is viable; a LEAF is viable iff correct_justified and correct_finalized.  *)
(* Viability therefore propagates strictly upward from leaves, which means   *)
(*                                                                          *)
(*   b is in the filtered tree  <=>  some viable leaf has b on its path      *)
(*                                                                          *)
(* and that is expressible with the ancestry already in state -- no          *)
(* recursion, which Apalache rejects anyway. Carried as `filtered` and pinned *)
(* by FilteredClosure, the same pattern as nodeAnc, so NodeChildren pays only *)
(* a set membership.                                                        *)
(***************************************************************************)

\* @type: (Int) => Set(Int);
BlockChildren(r) == { b \in blocks : b # Genesis /\ blockParent[b] = r }

\* @type: (Int) => Bool;
IsBlockLeaf(r) == BlockChildren(r) = {}

\* @type: (Int) => Set(Int);
AncRoots(b) == { a.root : a \in nodeAnc[b] }

FilteredClosure ==
    \A b \in blocks :
        (b \in filtered) <=>
            \E l \in blocks :
                /\ IsBlockLeaf(l)
                /\ l \in viableLeaf
                /\ (l = b \/ b \in AncRoots(l))

\* get_node_children, gloas. A PENDING node yields EMPTY always and FULL only
\* when the payload is verified. An EMPTY/FULL node yields PENDING nodes for
\* child blocks that DECLARED that status as their parent's -- so a child
\* attaches to exactly one of the two, never both.
\* @type: ($node) => Set($node);
NodeChildren(n) ==
    IF n.ps = PENDING
    THEN { [root |-> n.root, ps |-> EMPTY] }
         \union (IF n.root \in payloadVerified
                 THEN { [root |-> n.root, ps |-> FULL] } ELSE {})
    \* `for root in blocks` in the spec iterates get_filtered_block_tree's
    \* result, NOT store.blocks. Ranging over every block instead lets get_head
    \* descend into branches the protocol has pruned. The PENDING branch above
    \* is deliberately unfiltered, matching the spec: its root reached this point
    \* through an already-filtered step.
    ELSE { [root |-> c, ps |-> PENDING] :
             c \in { b \in blocks : /\ b # Genesis
                                    /\ b \in filtered
                                    /\ blockParent[b] = n.root
                                    /\ parentStatus[b] = n.ps } }

\* Only nodes get_node_children can actually produce. A FULL node for an
\* unverified root is NOT reachable and must not appear here.
\* @type: () => Set($node);
AllNodes ==
    { [root |-> b, ps |-> PENDING] : b \in blocks }
    \union { [root |-> b, ps |-> EMPTY] : b \in blocks }
    \union { [root |-> b, ps |-> FULL] : b \in (blocks \intersect payloadVerified) }

(***************************************************************************)
(* The head -- STATE with a local certificate, not a global query.          *)
(*                                                                          *)
(* The previous formulation was                                             *)
(*                                                                          *)
(*   ChainHead == IF \E h \in AllNodes : IsHead(h)                           *)
(*                THEN CHOOSE h \in AllNodes : IsHead(h) ELSE ...            *)
(*                                                                          *)
(* with IsHead quantifying twice over AllNodes and calling Precedes -> Weight*)
(* -> AttScore underneath. MEASURED: that exhausted a 12GB heap during       *)
(* constraint construction, both before the nodeAnc rewrite (~6s) and after  *)
(* it (877s), while every invariant avoiding it returned in 2-3s. CHOOSE was *)
(* isolated as the sole cause.                                              *)
(*                                                                          *)
(* CHOOSE is a definite description, not a search: Apalache must encode a    *)
(* Skolem constant plus the constraint that it satisfies IsHead, and that it *)
(* is the SAME witness at every occurrence -- so the whole IsHead term is    *)
(* reconstructed per occurrence. Carrying the head instead turns that into a *)
(* per-transition obligation quantified over headPath and NodeChildren.     *)
(***************************************************************************)

GenesisNode == [root |-> Genesis, ps |-> PENDING]

\* The unique parent of a node in the alternating tree. A payload node's parent
\* is its own block's PENDING node; a PENDING node's parent is the parent block
\* at its DECLARED status. Local, no walk.
\* @type: ($node) => $node;
NodeParent(n) ==
    IF n.ps = PENDING
    THEN [root |-> blockParent[n.root], ps |-> parentStatus[n.root]]
    ELSE [root |-> n.root, ps |-> PENDING]

\* get_head, as a certificate on (head, headPath) rather than a computation.
\* Every quantifier ranges over headPath or NodeChildren -- never over AllNodes,
\* and never nested over it twice.
\* @type: () => Bool;
HeadCertified ==
    /\ headPath \subseteq AllNodes
    /\ filtered \subseteq blocks
    /\ viableLeaf \subseteq blocks
    /\ proposer \in [Ids -> Validators]
    /\ GenesisNode \in headPath
    /\ head \in headPath
    \* head is a leaf: get_head stops where there are no children
    /\ NodeChildren(head) = {}
    \* connected: every node but the root has its parent on the path
    /\ \A n \in headPath : n = GenesisNode \/ NodeParent(n) \in headPath
    \* a path, not a tree: at most one child of any node lies on it
    /\ \A n \in headPath :
         \A c1, c2 \in NodeChildren(n) :
            (c1 \in headPath /\ c2 \in headPath) => c1 = c2
    \* and each step took the MAXIMUM child, which is what makes it get_head
    \* rather than merely some path
    /\ \A n \in headPath :
         n = head \/ \E c \in NodeChildren(n) :
                       /\ c \in headPath
                       /\ \A sib \in NodeChildren(n) : sib = c \/ Precedes(sib, c)

\* @type: ($node) => Bool;
Canonical(n) == n \in headPath

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                               *)
(***************************************************************************)

TypeOK ==
    /\ blocks \subseteq Ids
    /\ Genesis \in blocks
    /\ parentStatus \in [Ids -> {EMPTY, FULL}]
    /\ payloadVerified \subseteq blocks
    /\ equivocators \subseteq Validators
    /\ boostRoot \in blocks \union {0}
    /\ \A b \in Ids : \A a \in nodeAnc[b] : a.root \in Ids /\ a.ps \in {EMPTY, FULL}
    /\ head \in AllNodes
    /\ headPath \subseteq AllNodes
    /\ filtered \subseteq blocks
    /\ viableLeaf \subseteq blocks
    /\ proposer \in [Ids -> Validators]

\* S4. The two payload nodes of one root are never both canonical. Structural,
\* cheap, and independent of any weight -- the first thing to check because it
\* catches whole classes of encoding error in the alternating tree.
S4_PayloadStatusExclusive ==
    \A r \in blocks :
        ~( Canonical([root |-> r, ps |-> FULL])
           /\ Canonical([root |-> r, ps |-> EMPTY]) )

\* A block declaring FULL cannot be a child of its parent's EMPTY node.
S5_ChildAttachesToOneBranch ==
    \A b \in blocks :
        b # Genesis =>
            LET pE == [root |-> blockParent[b], ps |-> EMPTY]
                pF == [root |-> blockParent[b], ps |-> FULL]
                bn == [root |-> b, ps |-> PENDING]
            IN ~(bn \in NodeChildren(pE) /\ bn \in NodeChildren(pF))

\* A FULL node exists only for a verified payload.
S6_FullImpliesVerified ==
    \A n \in AllNodes : n.ps = FULL => n.root \in payloadVerified

\* The obligation that REPLACES the old AncestorWalkTerminates. nodeAnc is state,
\* so nothing recomputes it -- which means nothing catches it being wrong. This
\* pins it to exactly the recursion get_ancestor would have performed:
\*   ancestors(b) = ancestors(parent) + {(parent, declared status of b)}
\* Unlike the unrolling it replaces, this has no depth ceiling.
AncClosure ==
    /\ nodeAnc[Genesis] = {}
    /\ \A b \in blocks :
         b # Genesis =>
            nodeAnc[b] = nodeAnc[blockParent[b]]
                         \union { [root |-> blockParent[b], ps |-> parentStatus[b]] }

\* Each root appears at most once as an ancestor. This is what makes matching on
\* root equivalent to get_ancestor's matching on slot, and it must hold for
\* NodeInSubtree to be a faithful transcription rather than an approximation.
AncRootsUnique ==
    \A b \in blocks :
        \A a1, a2 \in nodeAnc[b] : a1.root = a2.root => a1 = a2

-----------------------------------------------------------------------------
(***************************************************************************)
(* Vacuity probes. Each is deliberately FALSE; a VIOLATION is the desired    *)
(* outcome, witnessing that the condition is reachable. v1 shipped three      *)
(* properties whose preconditions were unreachable and one mechanism that     *)
(* never fired, so these are mandatory, not optional.                        *)
(***************************************************************************)

VAC_FullNodeCanonical  == \A r \in blocks : ~Canonical([root |-> r, ps |-> FULL])
VAC_EmptyNodeCanonical == \A r \in blocks : ~Canonical([root |-> r, ps |-> EMPTY])
VAC_PrevSlotDecision   == \A n \in AllNodes : ~IsPrevSlotPayloadDecision(n)
VAC_BoostApplies       == ~boostApplies \/ boostRoot = 0
VAC_TiebreakerZero     == \A n \in AllNodes : Tiebreaker(n) # 0

\* REGRESSION PROBE for the is_ancestor PENDING-wildcard defect.
\*
\* Deliberately false: it asserts proposer boost never reaches a node of a
\* DIFFERENT root than boostRoot. Under the correct is_ancestor this is violated
\* immediately, because BoostNode is (boostRoot, PENDING) and a PENDING target
\* matches any status carried up the walk.
\*
\* Under the equality encoding this HOLDS -- boost propagates to nothing, and no
\* other check in this file notices. The typecheck was clean and S5/S6 both
\* passed while fork choice had effectively no proposer boost. This probe is the
\* only thing standing between that bug and a green run, so it must never be
\* dropped from the suite.
\* HEAD-CERTIFICATE REACHABILITY PROBES.
\*
\* HeadCertified is asserted inside Init, so if it is unsatisfiable for some
\* trees those trees silently vanish from the domain and every invariant holds
\* vacuously over what remains. That is the exact failure this repository exists
\* to avoid, so the certificate must be probed as hard as the properties.
\* All three are deliberately false and MUST report VIOLATED.
\* GATE PROBES. Each is deliberately false and MUST report VIOLATED.
VAC_FilteredPrunes == \A b \in blocks : b \in filtered   \* filtering really prunes
VAC_HeadWeak       == \A b \in blocks : ~IsHeadWeak(b)   \* D1: threshold fires
VAC_BoostSuppressed== boostRoot = 0 \/ boostApplies       \* suppression reachable

VAC_HeadDeep      == blockSlot[head.root] = 0        \* head can leave genesis
VAC_HeadFull      == head.ps # FULL                  \* a FULL node can be head
VAC_MultiBlock    == blocks = {Genesis}              \* trees can be non-trivial

\* @type: () => Bool;
VAC_BoostReachesDescendant ==
    \A n \in AllNodes :
        ~( boostRoot # 0 /\ n.root # boostRoot /\ BoostInSubtree(n) )

=============================================================================
