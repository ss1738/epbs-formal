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
    MaxDepth          \* bounds the ancestor walk; see AncestorAt

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
    boostApplies

vars == << blocks, blockSlot, blockParent, parentStatus, payloadVerified,
           ptcTimely, daAvailable, latestMsg, equivocators, boostRoot,
           boostApplies >>

ASSUME ValidatorsNonEmpty == Validators # {}
ASSUME ByzSubset          == ByzValidators \subseteq Validators
\* AncestorAt unrolls exactly four Step applications. Pinning MaxDepth here makes
\* any attempt to deepen the model fail at parse time instead of truncating the
\* ancestor walk in silence.
ASSUME UnrollingCoversDepth == MaxDepth = 4

\* Apalache requires a LITERAL constant range in [a..b]; it will not accept
\* 0..MaxDepth. These are therefore written out. ASSUME UnrollingCoversDepth
\* above is what keeps them in sync with MaxDepth -- change one without the
\* other and the ASSUME fails at parse time.
Ids   == 0 .. 4
Slots == 0 .. 4

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

\* get_ancestor, gloas. The parent reached is (parent_root, parentStatus),
\* NOT (parent_root, PENDING) -- payload status is carried up the walk.
\*
\* The spec form is recursive. Apalache rejects RECURSIVE, so this is an
\* explicit unrolling of FOUR steps -- written out, not parameterised, because
\* TLA+ cannot iterate an operator a constant number of times without recursion.
\*
\* This is sound only while no chain exceeds 4 blocks. That is not a comment,
\* it is an obligation: ASSUME UnrollingCoversDepth below pins MaxDepth = 4, and
\* AncestorWalkTerminates asserts the walk reached a fixpoint rather than
\* silently stopping mid-chain. Raising MaxDepth REQUIRES adding steps here.
\* v1 had exactly this shape with no such check and the walk truncated silently.
\* @type: ($node) => $node;
ParentNode(n) == [root |-> blockParent[n.root], ps |-> parentStatus[n.root]]

\* @type: ($node, Int) => $node;
Step(n, s) == IF blockSlot[n.root] =< s THEN n ELSE ParentNode(n)

\* @type: ($node, Int) => $node;
AncestorAt(n, s) ==
    LET a1 == Step(n,  s)
        a2 == Step(a1, s)
        a3 == Step(a2, s)
        a4 == Step(a3, s)
    IN  a4

\* is_ancestor, gloas. NOT record equality. The spec compares roots, then accepts
\* EITHER a payload-status match OR a PENDING target:
\*
\*   return (node_ancestor.payload_status == ancestor.payload_status
\*           or ancestor.payload_status == PAYLOAD_STATUS_PENDING)
\*
\* That second disjunct is load-bearing. get_ancestor carries the DECLARED parent
\* status up the walk, so it never yields PENDING for a strict ancestor. Writing
\* this as equality therefore makes every PENDING target unreachable -- and
\* BoostNode is (boostRoot, PENDING), so proposer boost would propagate to
\* nothing. A PENDING target is a wildcard over payload status, by design.
\* @type: ($node, $node) => Bool;
NodeInSubtree(vNode, target) ==
    LET a == AncestorAt(vNode, blockSlot[target.root]) IN
    /\ a.root = target.root
    /\ (a.ps = target.ps \/ target.ps = PENDING)

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
    ELSE { [root |-> c, ps |-> PENDING] :
             c \in { b \in blocks : /\ b # Genesis
                                    /\ blockParent[b] = n.root
                                    /\ parentStatus[b] = n.ps } }

\* Only nodes get_node_children can actually produce. A FULL node for an
\* unverified root is NOT reachable and must not appear here.
\* @type: () => Set($node);
AllNodes ==
    { [root |-> b, ps |-> PENDING] : b \in blocks }
    \union { [root |-> b, ps |-> EMPTY] : b \in blocks }
    \union { [root |-> b, ps |-> FULL] : b \in (blocks \intersect payloadVerified) }

\* get_head: descend from the justified root taking the max child each step.
\* Computed here; §2.2 of the blueprint carries it as state once actions exist.
\* @type: ($node) => Bool;
IsHead(h) ==
    /\ h \in AllNodes
    /\ NodeChildren(h) = {}
    /\ \A n \in AllNodes :
         (n # h /\ NodeInSubtree(h, n)) =>
            \A sib \in NodeChildren(n) :
               NodeInSubtree(h, sib) \/ Precedes(sib, h)

\* @type: () => $node;
ChainHead ==
    IF \E h \in AllNodes : IsHead(h)
    THEN CHOOSE h \in AllNodes : IsHead(h)
    ELSE [root |-> Genesis, ps |-> PENDING]

\* @type: ($node) => Bool;
Canonical(n) == n = ChainHead \/ NodeInSubtree(ChainHead, n)

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

\* The four-step unrolling in AncestorAt actually reached a fixpoint. If a chain
\* is longer than the unrolling, AncestorAt returns a MID-CHAIN node and every
\* NodeInSubtree answer built on it is quietly wrong -- no error, just false
\* results, which is the failure mode that produced v1's phantom conclusions.
\* This must be checked alongside every other invariant, never on its own.
AncestorWalkTerminates ==
    \A n \in AllNodes :
        \A s \in Slots :
            Step(AncestorAt(n, s), s) = AncestorAt(n, s)

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
VAC_BoostReachesDescendant ==
    \A n \in AllNodes :
        ~( boostRoot # 0 /\ n.root # boostRoot /\ BoostInSubtree(n) )

=============================================================================
