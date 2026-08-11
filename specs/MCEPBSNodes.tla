--------------------------- MODULE MCEPBSNodes ---------------------------
(***************************************************************************)
(* Harness for the node algebra.                                            *)
(*                                                                          *)
(* There are no actions. Init admits EVERY well-formed block tree within the *)
(* bounds and Next stutters, so `--length=0` asks Apalache to check the      *)
(* invariants against all of them simultaneously via SMT. For a pure algebra *)
(* this is strictly stronger than enumerating a reachable state space: there *)
(* is no reachability question to get wrong, which is precisely how v1's     *)
(* conclusions became artifacts of an unreachable precondition.             *)
(*                                                                          *)
(* Run:                                                                     *)
(*   apalache-mc check --cinit=ConstInit --init=Init --next=Next \           *)
(*                    --inv=<INV> --length=0 MCEPBSNodes.tla                *)
(***************************************************************************)
EXTENDS EPBSNodes

ConstInit ==
    /\ Validators    = {"v1", "v2", "v3"}
    /\ ByzValidators = {"v3"}
    /\ ProposerBoost = 2
    /\ MaxDepth      = 4
    /\ ReorgHeadWeightAbs = 2

\* Every well-formed tree. Two restrictions are MODELLING choices, not protocol
\* facts, and are named as such:
\*   (a) blockParent[b] < b  -- canonical form, cuts id-permutation symmetry
\*   (b) strictly increasing slots along a chain -- a block cannot share its
\*       parent's slot. True in practice; here it also bounds chain length by
\*       MaxDepth, which is what makes the four-step unrolling sound.
Init ==
    /\ blocks \in SUBSET Ids
    /\ Genesis \in blocks
    /\ blockSlot \in [Ids -> Slots]
    /\ blockSlot[Genesis] = 0
    /\ blockParent \in [Ids -> Ids]
    /\ blockParent[Genesis] = Genesis
    /\ \A b \in blocks :
         b # Genesis =>
            /\ blockParent[b] \in blocks
            /\ blockParent[b] < b
            /\ blockSlot[blockParent[b]] < blockSlot[b]
    /\ parentStatus \in [Ids -> {EMPTY, FULL}]
    /\ payloadVerified \in SUBSET Ids
    /\ payloadVerified \subseteq blocks
    /\ ptcTimely \in SUBSET Ids
    /\ ptcTimely \subseteq blocks
    /\ daAvailable \in SUBSET Ids
    /\ daAvailable \subseteq blocks
    /\ equivocators \in SUBSET Validators
    /\ equivocators \subseteq ByzValidators
    /\ boostRoot \in Ids
    /\ (boostRoot # 0 => boostRoot \in blocks)
    /\ latestMsg \in [Validators -> [slot: Slots, root: Ids, present: BOOLEAN]]
    /\ \A v \in Validators : latestMsg[v].root \in blocks
    \* Ancestry is admitted DECLARATIVELY, not constructed. nodeAnc ranges over
    \* every candidate assignment and AncClosure pins it to exactly the recursion
    \* get_ancestor would have performed. This is the whole point of the rewrite:
    \* the solver constrains ancestry once here instead of the rewriter inlining
    \* a four-step walk into every weight evaluation inside IsHead.
    /\ nodeAnc \in [Ids -> SUBSET AncUniverse]
    /\ AncClosure
    /\ \A b \in Ids \ blocks : nodeAnc[b] = {}
    \* The head is admitted freely and constrained by its certificate -- the M3
    \* substitution. No CHOOSE anywhere in the reachable term graph.
    /\ slot \in Slots
    /\ \A b \in blocks : blockSlot[b] =< slot
    /\ proposer \in [Ids -> Validators]
    /\ viableLeaf \in SUBSET Ids
    /\ viableLeaf \subseteq blocks
    /\ filtered \in SUBSET Ids
    /\ filtered \subseteq blocks
    /\ FilteredClosure
    \* boostApplies is DERIVED, not free. Leaving it free lets induction grant
    \* boost in states Gloas forbids -- the D1 false positive.
    /\ boostApplies = ShouldApplyProposerBoost
    /\ head \in AllNodes
    /\ headPath \in SUBSET AllNodes
    /\ HeadCertified

Next == UNCHANGED vars

===========================================================================
