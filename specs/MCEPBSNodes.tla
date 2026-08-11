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
    /\ CurrentSlot   = 3
    /\ MaxDepth      = 4

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
    /\ boostApplies \in BOOLEAN
    /\ latestMsg \in [Validators -> [slot: Slots, root: Ids, present: BOOLEAN]]
    /\ \A v \in Validators : latestMsg[v].root \in blocks

Next == UNCHANGED vars

===========================================================================
