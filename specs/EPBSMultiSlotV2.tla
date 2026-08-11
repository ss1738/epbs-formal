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

VARIABLE
    \* @type: Int -> Str;
    \* Designated proposer per slot, fixed at Init. Without this, an adversary's
    \* off-schedule block can take proposer boost -- v1's first false positive,
    \* which produced a counterexample in 11 s that nearly got reported as a
    \* protocol finding.
    schedule

varsV2 == << blocks, blockSlot, blockParent, parentStatus, payloadVerified,
             ptcTimely, daAvailable, latestMsg, equivocators, boostRoot,
             boostApplies, nodeAnc, head, headPath, proposer, viableLeaf,
             filtered, slot, schedule >>

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
    /\ viableLeaf' \in SUBSET blocks'
    /\ filtered'   \in SUBSET Ids
    /\ head' \in AllNodes'
    /\ headPath' \in SUBSET AllNodes'
    /\ boostApplies' \in BOOLEAN
    /\ Derived'

\* on_execution_payload_envelope: the payload is delivered and verified, so the
\* FULL node becomes a candidate.
RevealPayload(b) ==
    /\ b \in blocks /\ b \notin payloadVerified
    /\ payloadVerified' = payloadVerified \union {b}
    /\ UNCHANGED << blocks, blockSlot, blockParent, parentStatus, nodeAnc,
                    ptcTimely, daAvailable, latestMsg, equivocators, boostRoot,
                    slot, proposer, schedule >>
    /\ viableLeaf' \in SUBSET blocks
    /\ filtered'   \in SUBSET Ids
    /\ head' \in AllNodes'
    /\ headPath' \in SUBSET AllNodes'
    /\ boostApplies' \in BOOLEAN
    /\ Derived'

\* on_payload_attestation_message, PTC_TIMELINESS_INDEX. Only meaningful for a
\* delivered payload -- §4.3(b).
PtcVote(b) ==
    /\ b \in payloadVerified /\ b \notin ptcTimely
    /\ ptcTimely' = ptcTimely \union {b}
    /\ UNCHANGED << blocks, blockSlot, blockParent, parentStatus, nodeAnc,
                    payloadVerified, daAvailable, latestMsg, equivocators,
                    boostRoot, slot, proposer, schedule >>
    /\ viableLeaf' \in SUBSET blocks
    /\ filtered'   \in SUBSET Ids
    /\ head' \in AllNodes'
    /\ headPath' \in SUBSET AllNodes'
    /\ boostApplies' \in BOOLEAN
    /\ Derived'

DaVote(b) ==
    /\ b \in payloadVerified /\ b \notin daAvailable
    /\ daAvailable' = daAvailable \union {b}
    /\ UNCHANGED << blocks, blockSlot, blockParent, parentStatus, nodeAnc,
                    payloadVerified, ptcTimely, latestMsg, equivocators,
                    boostRoot, slot, proposer, schedule >>
    /\ viableLeaf' \in SUBSET blocks
    /\ filtered'   \in SUBSET Ids
    /\ head' \in AllNodes'
    /\ headPath' \in SUBSET AllNodes'
    /\ boostApplies' \in BOOLEAN
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
    /\ viableLeaf' \in SUBSET blocks
    /\ filtered'   \in SUBSET Ids
    /\ head' \in AllNodes'
    /\ headPath' \in SUBSET AllNodes'
    /\ boostApplies' \in BOOLEAN
    /\ Derived'

\* Proposer boost expires at the slot boundary.
AdvanceSlot ==
    /\ slot + 1 \in Slots
    /\ slot' = slot + 1
    /\ boostRoot' = 0
    /\ UNCHANGED << blocks, blockSlot, blockParent, parentStatus, nodeAnc,
                    payloadVerified, ptcTimely, daAvailable, latestMsg,
                    equivocators, proposer, schedule >>
    /\ viableLeaf' \in SUBSET blocks
    /\ filtered'   \in SUBSET Ids
    /\ head' \in AllNodes'
    /\ headPath' \in SUBSET AllNodes'
    /\ boostApplies' \in BOOLEAN
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
    /\ viableLeaf' \in SUBSET blocks
    /\ filtered'   \in SUBSET Ids
    /\ head' \in AllNodes'
    /\ headPath' \in SUBSET AllNodes'
    /\ boostApplies' \in BOOLEAN
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

-----------------------------------------------------------------------------
(***************************************************************************)
(* Reachability probes. Each is deliberately FALSE; VIOLATED is the desired  *)
(* outcome. With actions present these check that the TRANSITION SYSTEM can   *)
(* reach the interesting states, which is a strictly different question from  *)
(* the static probes in EPBSNodes -- those only showed such states exist.     *)
(***************************************************************************)

RVAC_BlockProposed  == blocks = {Genesis}
RVAC_SlotAdvanced   == slot = 0
RVAC_PayloadVerified== payloadVerified = {}
RVAC_Attested       == \A v \in Validators : latestMsg[v].slot = 0
RVAC_Equivocated    == equivocators = {}
RVAC_HeadMoved      == head = [root |-> Genesis, ps |-> PENDING]

=============================================================================
