------------------------- MODULE EPBSMultiSlotV2 -------------------------
(***************************************************************************)
(* Gloas ePBS state machine, built on the verified node algebra.            *)
(*                                                                          *)
(* EPBSNodes.tla supplies the algebra: (root, payload_status) nodes, static  *)
(* ancestry, the filtered block tree, the head certificate, and the derived  *)
(* proposer-boost gate. This module supplies only what that lacks -- TIME    *)
(* and ACTIONS.                                                             *)
(*                                                                          *)
(* Design consequence of the M1/M3 measurements: filtered, head, headPath    *)
(* and boostApplies are all CONSTRAINT-DETERMINED, never computed. Every     *)
(* action re-establishes them through a single Derived' conjunct. No action  *)
(* recomputes a head, and CHOOSE appears nowhere -- that is what took S4     *)
(* from an OutOfMemoryError to a verdict.                                    *)
(***************************************************************************)
EXTENDS EPBSNodes

CONSTANTS
    \* @type: Int;
    MaxEquivocations

VARIABLES
    \* @type: $node;
    \* Head as of the PREVIOUS state. One step of carried history turns the
    \* two-state reorg property into a cheap state invariant, avoiding
    \* --temporal's liveness-to-safety reduction.
    prevHead,
    \* @type: Bool;
    \* Whether, IN THE PREVIOUS STATE, the head's block out-attested every
    \* sibling block by more than the adversary could summon.
    prevHeadStrong,
    \* @type: Int -> Str;
    \* Designated proposer per slot, fixed at Init. Without this, an adversary's
    \* off-schedule block can take proposer boost -- v1's first false positive,
    \* which produced a counterexample in 11 s that nearly got reported as a
    \* protocol finding.
    schedule

varsV2 == << blocks, blockSlot, blockParent, parentStatus, payloadVerified,
             ptcTimely, daAvailable, latestMsg, equivocators, boostRoot,
             boostApplies, nodeAnc, head, headPath, proposer, viableLeaf,
             filtered, slot, schedule, prevHead, prevHeadStrong >>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Derived state.                                                          *)
(*                                                                          *)
(* ORDERING IS LOAD-BEARING. Apalache's assignment finder is a left-to-right *)
(* pass: a primed variable must be ASSIGNED before it is USED. AllNodes'     *)
(* reads payloadVerified', so every `head' \in AllNodes'` must come after the *)
(* UNCHANGED that assigns it. Writing the actions in the natural order --    *)
(* changes, derived choices, UNCHANGED -- fails with "payloadVerified' is    *)
(* used before it is assigned"; UNCHANGED goes first.                                                           *)
(*                                                                          *)
(* These four are functions of the rest, but are carried as variables and    *)
(* pinned by constraints rather than computed -- computing them is precisely  *)
(* what exhausted a 12 GB heap. Every action ends with Derived'.             *)
(***************************************************************************)

Derived ==
    /\ AncClosure                                 \* ancestry matches get_ancestor
    /\ FilteredClosure                            \* filtered = get_filtered_block_tree
    /\ HeadCertified                              \* head/headPath = get_head
    /\ boostApplies = ShouldApplyProposerBoost    \* the four-conjunct gate

AdversaryCapacity == Cardinality(ByzValidators) + ProposerBoost

\* IndInv candidate conjunct (V2_VERIFICATION_SPEC.md §4.4), implemented from its
\* design-only skeleton. Two conjuncts of different character, deliberately kept
\* together because both are needed for the adversary-budget reasoning even
\* though only one is a live test:
\*
\*   1. Cardinality(equivocators) =< MaxEquivocations -- protected by
\*      AdvEquivocate's guard (Cardinality(equivocators) < MaxEquivocations,
\*      strict, before the union) and by no other action touching equivocators.
\*      This IS a real claim about the transition relation.
\*
\*   2. Cardinality(ByzValidators) * 3 < Cardinality(Validators) -- entirely
\*      about CONSTANTS, never primed by any action. Decided once at ConstInit,
\*      true or false for the whole run. Testing whether Next preserves it is
\*      the same circularity StructuralClosure's first four conjuncts had
\*      against Init: it cannot fail because nothing can change it. Included
\*      for what it's used for (bounding the adversary in IndInv), not as a
\*      transition-system claim.
AdversaryBudget ==
    /\ Cardinality(equivocators) =< MaxEquivocations
    /\ Cardinality(ByzValidators) * 3 < Cardinality(Validators)   \* < 1/3

\* Block-level attestation margin. Uses AttScore on the PENDING node, NOT
\* Weight, for two reasons. First, Weight is zeroed by
\* is_previous_slot_payload_decision exactly in the window where the payload
\* decision happens -- today's P3 witness showed both branches at zero -- so any
\* margin test built on Weight is false there at ANY validator count. Second,
\* the spec's own is_head_weak and is_parent_strong both measure
\* get_attestation_score on a PENDING node, so this matches how Gloas asks the
\* same question.
\* @type: (Int) => Int;
BlockMargin(r) == AttScore([root |-> r, ps |-> PENDING])

\* Is the current head's BLOCK dominant enough that the adversary cannot flip it?
\* @type: () => Bool;
\* FINDING #15. An earlier version was the sibling clause ALONE. That is
\* vacuously true when the block has no siblings yet, so a block that was merely
\* FIRST got classified unassailable -- with zero attestations. A later sibling
\* then took the head on proposer boost and P1b reported a reorg. Being
\* unopposed is not being dominant.
\*
\* The absolute clause is what makes the predicate mean anything: the block must
\* hold more attestation weight than the adversary can summon, so no adversarial
\* action can flip it. This is why 5 validators were needed -- at 3, honest
\* weight cannot exceed AdversaryCapacity = 3 and the predicate is unsatisfiable
\* (that was the P1 degeneracy). At 5 validators with one Byzantine, 4 honest
\* attestations clear a capacity of 3.
\*
\* The `r = Genesis` disjunct is still trivially true at Init, which is why
\* VAC_P1b_PrevHeadStrong must require prevHead.root # Genesis.
HeadBlockStrong ==
    LET r == head.root IN
    \/ r = Genesis
    \/ /\ BlockMargin(r) > AdversaryCapacity
       /\ \A sibr \in BlockChildren(blockParent[r]) :
            sibr = r \/ BlockMargin(r) > BlockMargin(sibr) + AdversaryCapacity

\* Appended to every action. HeadBlockStrong is evaluated UNPRIMED, so it records
\* the pre-state's verdict -- which is what the reorg property must condition on.
RecordHistory ==
    /\ prevHead' = head
    /\ prevHeadStrong' = HeadBlockStrong

-----------------------------------------------------------------------------
(***************************************************************************)
(* Init: genesis only.                                                      *)
(***************************************************************************)

Init ==
    /\ blocks = {Genesis}
    /\ blockSlot = [i \in Ids |-> 0]
    /\ blockParent = [i \in Ids |-> Genesis]
    /\ parentStatus = [i \in Ids |-> EMPTY]
    /\ nodeAnc = [i \in Ids |-> {}]
    /\ payloadVerified = {}
    /\ ptcTimely = {}
    /\ daAvailable = {}
    /\ equivocators = {}
    /\ boostRoot = 0
    /\ slot = 0
    /\ proposer \in [Ids -> Validators]
    /\ schedule \in [Slots -> Validators]
    /\ proposer[Genesis] = schedule[0]
    /\ latestMsg = [v \in Validators |->
                      [slot |-> 0, root |-> Genesis, present |-> FALSE]]
    /\ viableLeaf \in SUBSET {Genesis}
    /\ filtered \in SUBSET Ids
    /\ head \in AllNodes
    /\ headPath \in SUBSET AllNodes
    /\ boostApplies \in BOOLEAN
    /\ prevHead = head
    \* NOT free. Left as `\in BOOLEAN` the solver picks TRUE and every probe on
    \* it violates at State 0 without a transition establishing anything.
    /\ prevHeadStrong = HeadBlockStrong
    /\ Derived

-----------------------------------------------------------------------------
(***************************************************************************)
(* Honest actions                                                           *)
(***************************************************************************)

\* on_block. The proposer must be the scheduled one for this slot; parentStatus
\* is DECLARED here and immutable thereafter, which is what makes nodeAnc static.
\* A block may declare FULL only if the parent's payload was actually verified,
\* since otherwise the parent's FULL node does not exist as a candidate.
ProposeBlock(b, par, ps) ==
    /\ b \in Ids /\ b \notin blocks /\ b # Genesis
    /\ par \in blocks
    /\ blockSlot[par] < slot
    /\ ps \in {EMPTY, FULL}
    /\ (ps = FULL => par \in payloadVerified)
    /\ blocks'       = blocks \union {b}
    /\ blockSlot'    = [blockSlot    EXCEPT ![b] = slot]
    /\ blockParent'  = [blockParent  EXCEPT ![b] = par]
    /\ parentStatus' = [parentStatus EXCEPT ![b] = ps]
    /\ proposer'     = [proposer     EXCEPT ![b] = schedule[slot]]
    /\ nodeAnc'      = [nodeAnc EXCEPT ![b] =
                          nodeAnc[par] \union { [root |-> par, ps |-> ps] }]
    /\ boostRoot'    = b
    /\ UNCHANGED << payloadVerified, ptcTimely, daAvailable, latestMsg,
                    equivocators, slot, schedule >>
    \* Viability is decided ONCE, here, and frozen -- see the note on
    \* viableLeaf. Every other action carries it unchanged.
    /\ viableLeaf' \in { viableLeaf, viableLeaf \union {b} }
    /\ filtered'   \in SUBSET Ids
    /\ head' \in AllNodes'
    /\ headPath' \in SUBSET AllNodes'
    /\ boostApplies' \in BOOLEAN
    /\ RecordHistory
    /\ Derived'

\* on_execution_payload_envelope: the payload is delivered and verified, so the
\* FULL node becomes a candidate.
RevealPayload(b) ==
    /\ b \in blocks /\ b \notin payloadVerified
    /\ payloadVerified' = payloadVerified \union {b}
    /\ UNCHANGED << blocks, blockSlot, blockParent, parentStatus, nodeAnc,
                    ptcTimely, daAvailable, latestMsg, equivocators, boostRoot,
                    slot, proposer, schedule >>
    /\ viableLeaf' = viableLeaf
    /\ filtered'   \in SUBSET Ids
    /\ head' \in AllNodes'
    /\ headPath' \in SUBSET AllNodes'
    /\ boostApplies' \in BOOLEAN
    /\ RecordHistory
    /\ Derived'

\* on_payload_attestation_message, PTC_TIMELINESS_INDEX. Only meaningful for a
\* delivered payload -- §4.3(b).
PtcVote(b) ==
    /\ b \in payloadVerified /\ b \notin ptcTimely
    /\ ptcTimely' = ptcTimely \union {b}
    /\ UNCHANGED << blocks, blockSlot, blockParent, parentStatus, nodeAnc,
                    payloadVerified, daAvailable, latestMsg, equivocators,
                    boostRoot, slot, proposer, schedule >>
    /\ viableLeaf' = viableLeaf
    /\ filtered'   \in SUBSET Ids
    /\ head' \in AllNodes'
    /\ headPath' \in SUBSET AllNodes'
    /\ boostApplies' \in BOOLEAN
    /\ RecordHistory
    /\ Derived'

DaVote(b) ==
    /\ b \in payloadVerified /\ b \notin daAvailable
    /\ daAvailable' = daAvailable \union {b}
    /\ UNCHANGED << blocks, blockSlot, blockParent, parentStatus, nodeAnc,
                    payloadVerified, ptcTimely, latestMsg, equivocators,
                    boostRoot, slot, proposer, schedule >>
    /\ viableLeaf' = viableLeaf
    /\ filtered'   \in SUBSET Ids
    /\ head' \in AllNodes'
    /\ headPath' \in SUBSET AllNodes'
    /\ boostApplies' \in BOOLEAN
    /\ RecordHistory
    /\ Derived'

\* update_latest_messages. The strict slot increase is the LMD monotonicity rule
\* and CANNOT be stated as a one-state invariant -- §4.2. It lives here.
Attest(v, b, present) ==
    /\ v \in Validators
    /\ b \in blocks
    /\ slot > latestMsg[v].slot
    /\ present \in BOOLEAN
    /\ (present => b \in payloadVerified)
    /\ latestMsg' = [latestMsg EXCEPT ![v] =
                       [slot |-> slot, root |-> b, present |-> present]]
    /\ UNCHANGED << blocks, blockSlot, blockParent, parentStatus, nodeAnc,
                    payloadVerified, ptcTimely, daAvailable, equivocators,
                    boostRoot, slot, proposer, schedule >>
    /\ viableLeaf' = viableLeaf
    /\ filtered'   \in SUBSET Ids
    /\ head' \in AllNodes'
    /\ headPath' \in SUBSET AllNodes'
    /\ boostApplies' \in BOOLEAN
    /\ RecordHistory
    /\ Derived'

\* Proposer boost expires at the slot boundary.
AdvanceSlot ==
    /\ slot + 1 \in Slots
    /\ slot' = slot + 1
    /\ boostRoot' = 0
    /\ UNCHANGED << blocks, blockSlot, blockParent, parentStatus, nodeAnc,
                    payloadVerified, ptcTimely, daAvailable, latestMsg,
                    equivocators, proposer, schedule >>
    /\ viableLeaf' = viableLeaf
    /\ filtered'   \in SUBSET Ids
    /\ head' \in AllNodes'
    /\ headPath' \in SUBSET AllNodes'
    /\ boostApplies' \in BOOLEAN
    /\ RecordHistory
    /\ Derived'

-----------------------------------------------------------------------------
(***************************************************************************)
(* Adversarial actions                                                      *)
(***************************************************************************)

\* A Byzantine validator equivocates. get_attestation_score EXCLUDES equivocators
\* (phase0:323), which is why is_head_weak adds their balance back separately.
\* Whether this suppresses the next slot's boost depends on the four-conjunct
\* gate in ShouldApplyProposerBoost, not on equivocation alone.
AdvEquivocate(v) ==
    /\ v \in ByzValidators
    /\ v \notin equivocators
    /\ Cardinality(equivocators) < MaxEquivocations
    /\ equivocators' = equivocators \union {v}
    /\ UNCHANGED << blocks, blockSlot, blockParent, parentStatus, nodeAnc,
                    payloadVerified, ptcTimely, daAvailable, latestMsg,
                    boostRoot, slot, proposer, schedule >>
    /\ viableLeaf' = viableLeaf
    /\ filtered'   \in SUBSET Ids
    /\ head' \in AllNodes'
    /\ headPath' \in SUBSET AllNodes'
    /\ boostApplies' \in BOOLEAN
    /\ RecordHistory
    /\ Derived'

-----------------------------------------------------------------------------

Next ==
    \/ \E b, par \in Ids : \E ps \in {EMPTY, FULL} : ProposeBlock(b, par, ps)
    \/ \E b \in Ids : RevealPayload(b)
    \/ \E b \in Ids : PtcVote(b)
    \/ \E b \in Ids : DaVote(b)
    \/ \E v \in Validators : \E b \in Ids : \E pr \in BOOLEAN : Attest(v, b, pr)
    \/ AdvanceSlot
    \/ \E v \in Validators : AdvEquivocate(v)

Spec == Init /\ [][Next]_varsV2

\* RESTRICTED Next FOR P1b. Derived by the finding-#13 rule -- enumerate the
\* property's free variables and keep an action that writes each -- rather than
\* by intuition, which is how PtcVote/DaVote got dropped from a property that
\* needed them.
\*
\*   prevHead, prevHeadStrong  <- RecordHistory  (every action)
\*   head, headPath            <- Derived'       (every action)
\*   nodeAnc, blocks, blockParent <- ProposeBlock
\*   latestMsg                 <- Attest
\*   equivocators              <- AdvEquivocate
\*   slot                      <- AdvanceSlot
\*
\* AdvEquivocate is RETAINED and that is the point. AttScore excludes
\* equivocators, so equivocating deletes a validator's vote from whichever block
\* it supported -- the adversary's weight-SUBTRACTION capability. Dropping it
\* would leave an adversary that can only push its own fork with proposer boost
\* and never degrade an incumbent's margin, which is not reorg resistance in any
\* meaningful sense. A HOLDS obtained that way would be worse than no result.
\*
\* RevealPayload is also retained despite payloadVerified being unreachable from
\* P1b: dropping it forbids any block declaring FULL parent status, removing a
\* whole class of tree shape from the search.
\*
\* Only PtcVote and DaVote are dropped. Neither writes any free variable of P1b.
NextP1b ==
    \/ \E b, par \in Ids : \E ps \in {EMPTY, FULL} : ProposeBlock(b, par, ps)
    \/ \E b \in Ids : RevealPayload(b)
    \/ \E v \in Validators : \E b \in Ids : \E pr \in BOOLEAN : Attest(v, b, pr)
    \/ AdvanceSlot
    \/ \E v \in Validators : AdvEquivocate(v)

\* WITNESS-HUNTING SUB-MODEL. Six of the seven actions; only AdvEquivocate is
\* dropped, since no P3 property mentions `equivocators`.
\*
\* AN EARLIER VERSION ALSO DROPPED PtcVote AND DaVote. That was wrong and it was
\* wrong SILENTLY. VAC_P3_TiebreakDecisive requires b \in ptcTimely /\ b \in
\* daAvailable; with those two actions removed, nothing can ever add to those
\* sets, so the antecedent was unsatisfiable and the invariant held VACUOUSLY at
\* every length. Runs at lengths 5, 7 and 9 were foregone conclusions.
\*
\* The sanity check missed it: VAC_P3_WindowReachable calls PtcIsDecisiveFor,
\* which does not reference ptcTimely, so it validated ONE precondition and said
\* nothing about the others.
\*
\* RULE. Before restricting Next, take the target property's free variables and
\* confirm that some retained action can write EACH of them. A sub-model that
\* cannot reach a property's antecedent does not test that property.
\*
\* SOUND FOR VIOLATIONS ONLY. Every disjunct here is a real action of Next, so
\* any trace found is a genuine execution of the full model. A HOLDS under this
\* Next is STRICTLY WEAKER than a HOLDS under Next and must never be reported as
\* one -- it only says no witness exists among executions using these four
\* actions.
NextWitness ==
    \/ \E b, par \in Ids : \E ps \in {EMPTY, FULL} : ProposeBlock(b, par, ps)
    \/ \E b \in Ids : RevealPayload(b)
    \/ \E b \in Ids : PtcVote(b)
    \/ \E b \in Ids : DaVote(b)
    \/ \E v \in Validators : \E b \in Ids : \E pr \in BOOLEAN : Attest(v, b, pr)
    \/ AdvanceSlot

-----------------------------------------------------------------------------
(***************************************************************************)
(* Reachability probes. Each is deliberately FALSE; VIOLATED is the desired  *)
(* outcome. With actions present these check that the TRANSITION SYSTEM can   *)
(* reach the interesting states, which is a strictly different question from  *)
(* the static probes in EPBSNodes -- those only showed such states exist.     *)
(***************************************************************************)

-----------------------------------------------------------------------------
(***************************************************************************)
(* PROTOCOL PROPERTIES.                                                     *)
(*                                                                          *)
(* Everything above this line checks that the ENCODING is consistent. These  *)
(* are the first statements in this repository about ePBS itself.           *)
(*                                                                          *)
(* Each comes with a decisiveness probe. A property can hold because the     *)
(* protocol enforces it, or because its precondition is unreachable -- and   *)
(* those look identical from a green result. The probes tell them apart, and *)
(* for P3 a vacuous outcome IS the ESP reviewer's criticism confirmed.       *)
(***************************************************************************)

\* Everything an adversary can add to one node's weight at these bounds: every
\* Byzantine validator's attestation, plus the proposer boost if it controls the
\* current proposal.
(*-------------------------------------------------------------------------*)
(* P1 (DELETED). An earlier margin property, Weight(n) > Weight(sib) +        *)
(* AdversaryCapacity, together with its probe VAC_P1_MarginTight.            *)
(*                                                                          *)
(* Removed because it was degenerate, not merely superseded: AdversaryCapacity*)
(* equalled total validator weight at 3 validators, so the inequality was     *)
(* unsatisfiable, AND the Weight it compared is zeroed by                    *)
(* is_previous_slot_payload_decision in exactly the window that matters --    *)
(* false at ANY validator count. P1b below replaces it, measuring with        *)
(* AttScore on PENDING nodes, which is what is_head_weak and is_parent_strong *)
(* do. The finding is recorded in V2_VERIFICATION_SPEC.md 1.9.               *)
(*-------------------------------------------------------------------------*)

(*-------------------------------------------------------------------------*)
(* P1b. THE GENUINE REORG PROPERTY (two-state, via carried history).        *)
(*                                                                          *)
(* If the head's block was dominant last state -- out-attesting every sibling *)
(* by more than the adversary can summon -- then this state's head is still  *)
(* on that block or a descendant of it. That is what reorg resistance means. *)
(*                                                                          *)
(* Deliberately BLOCK-level. A head moving between (r,EMPTY) and (r,FULL) is *)
(* the payload decision resolving, not a reorg, and P3 showed that movement  *)
(* is governed by the tiebreaker with both weights at zero.                  *)
(*-------------------------------------------------------------------------*)
P1b_NoBlockReorgUnderBudget ==
    prevHeadStrong =>
        \/ head.root = prevHead.root
        \/ prevHead.root \in AncRoots(head.root)

\* MANDATORY companion. P1b is an implication; if prevHeadStrong is never true it
\* holds vacuously and says nothing. P2 already failed exactly this way.
\*
\* The NON-TRIVIAL form. `~prevHeadStrong` alone violates at State 0, because
\* HeadBlockStrong's first disjunct is `r = Genesis` -- so it is TRUE at the
\* initial state for free and the probe proves nothing. What has to be reachable
\* is a strong head that is NOT genesis.
VAC_P1b_PrevHeadStrong == ~(prevHeadStrong /\ prevHead.root # Genesis)

\* And: can the head's block ever actually change? If not, P1b is trivial.
VAC_P1b_HeadBlockMoves == head.root = prevHead.root

(*-------------------------------------------------------------------------*)
(* P2. Proposer-boost suppression is strictly bound to a duplicate proposal. *)
(*                                                                          *)
(* should_apply_proposer_boost returns False only via the equivocations list, *)
(* which requires a PTC-timely block by the SAME proposer at the SAME slot as *)
(* the parent. So boost must never be suppressed in an execution where no     *)
(* proposer ever produced two blocks in one slot. A violation means the       *)
(* four-conjunct gate can fire without an actual equivocation -- a strictly   *)
(* stronger adversary than the protocol grants, i.e. the D1 failure mode.     *)
(*-------------------------------------------------------------------------*)
P2_SuppressionRequiresDuplicateProposal ==
    (boostRoot # 0 /\ ~boostApplies)
    => \E r1, r2 \in blocks :
         /\ r1 # r2
         /\ proposer[r1] = proposer[r2]
         /\ blockSlot[r1] = blockSlot[r2]

(*-------------------------------------------------------------------------*)
(* P3. PTC timeliness influences head selection.                            *)
(*                                                                          *)
(* THE DIRECT ANSWER TO THE ESP REVIEW's "multi-slot x PTC interactions are   *)
(* unreachable". The coupling is not additive weight -- that was D5. It runs  *)
(* through get_payload_status_tiebreaker: FULL scores 2 when                  *)
(* should_extend_payload holds and 0 otherwise, against EMPTY's 1. So a       *)
(* timely payload wins ties and an untimely one loses them.                   *)
(*                                                                          *)
(* P3 states that a timely payload is never skipped on the tiebreak: if the   *)
(* EMPTY node of a timely block is canonical, it got there on WEIGHT, never   *)
(* by out-ranking FULL.                                                      *)
(*-------------------------------------------------------------------------*)
\* Is boost suppression reachable in the TRANSITION SYSTEM at all? P2 is an
\* implication whose antecedent is (boostRoot # 0 /\ ~boostApplies); if that is
\* never reached, P2 holds trivially and says nothing. The static module's
\* VAC_BoostSuppressed violated, but reachability under actions is a different
\* question and must be asked separately.
VAC_P2_SuppressionOccurs == ~(boostRoot # 0 /\ ~boostApplies)

P3_TimelyPayloadNotSkippedOnTie ==
    \A b \in blocks :
        ( /\ b \in ptcTimely /\ b \in daAvailable
          /\ ShouldExtendPayload(b)
          /\ [root |-> b, ps |-> EMPTY] \in headPath )
        => Weight([root |-> b, ps |-> EMPTY]) > Weight([root |-> b, ps |-> FULL])

\* THE PROBE THAT MATTERS. Deliberately false: it asserts the payload tiebreak
\* is never DECISIVE -- never the thing that picks FULL over an equally-weighted
\* EMPTY. VIOLATED means the PTC verdict genuinely reaches fork choice in this
\* model. HOLDS means the coupling is unreachable at these bounds, which is
\* precisely the reviewer's objection, confirmed rather than answered.
VAC_P3_TiebreakDecisive ==
    \A b \in blocks :
        ~( /\ PtcIsDecisiveFor(b)
           /\ b \in ptcTimely
           /\ b \in daAvailable
           /\ [root |-> b, ps |-> FULL] \in headPath
           /\ Weight([root |-> b, ps |-> FULL])
                = Weight([root |-> b, ps |-> EMPTY]) )

\* Can the decisive window be entered at all? If this HOLDS, the three permissive
\* disjuncts of should_extend_payload always cover the case and the PTC verdict
\* never decides anything -- which would be the ESP objection confirmed at a
\* deeper level than "unreachable state space".
VAC_P3_WindowReachable == \A b \in blocks : ~PtcIsDecisiveFor(b)

\* ANTECEDENT-WRITABILITY PROBES. One per set the P3 properties read. These are
\* what should have been run before any restricted Next was trusted -- each is
\* deliberately false and a HOLDS means no retained action can populate that set.
VAC_PtcTimelyNonEmpty  == ptcTimely = {}
VAC_DaAvailableNonEmpty == daAvailable = {}
VAC_BothPtcAndDa       == \A b \in blocks : ~(b \in ptcTimely /\ b \in daAvailable)

\* Within the window, does an UNTIMELY payload actually lose? Tiebreaker 0 < 1.
VAC_P3_UntimelyLosesInWindow ==
    \A b \in blocks :
        ~( /\ PtcIsDecisiveFor(b)
           /\ ~(b \in ptcTimely /\ b \in daAvailable)
           /\ [root |-> b, ps |-> EMPTY] \in headPath
           /\ Weight([root |-> b, ps |-> EMPTY])
                = Weight([root |-> b, ps |-> FULL]) )

\* Companion: can an UNTIMELY payload lose a tie it would otherwise win? This is
\* the same mechanism read from the other side (Tiebreaker = 0 < EMPTY's 1).
-----------------------------------------------------------------------------

RVAC_BlockProposed  == blocks = {Genesis}
RVAC_SlotAdvanced   == slot = 0
RVAC_PayloadVerified== payloadVerified = {}
RVAC_Attested       == \A v \in Validators : latestMsg[v].slot = 0
RVAC_Equivocated    == equivocators = {}
RVAC_HeadMoved      == head = [root |-> Genesis, ps |-> PENDING]

=============================================================================
