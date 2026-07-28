------------------------------- MODULE EPBSChain ----------------------------
(***************************************************************************)
(* A multi-slot model of the EIP-7732 payment lifecycle across a chain of  *)
(* slots. Milestones 1 and 2 studied a single slot and a single slot         *)
(* boundary. This model runs a bounded sequence of slots and checks the      *)
(* cross-slot behavior EIP-7732 actually has:                               *)
(*                                                                         *)
(*   * At inclusion the committed value is debited from the builder into a  *)
(*     pending-payment escrow.                                              *)
(*   * The proposer is paid via a BuilderPendingWithdrawal, which is        *)
(*     processed ASYNCHRONOUSLY, possibly in a later slot. EIP-7732 notes    *)
(*     that outstanding withdrawals queue up and drain over time.           *)
(*                                                                         *)
(* Each slot resolves to one of four outcomes:                             *)
(*   full     - block canonical, payload revealed  -> proposer owed the bid *)
(*   empty    - block canonical, payload withheld   -> proposer owed the bid *)
(*              (proposer unconditional payment: paid in both full and empty)*)
(*   reorged  - block not canonical                 -> builder not charged   *)
(*   skipped  - no builder included                 -> no payment            *)
(*                                                                         *)
(* Properties checked with TLC:                                            *)
(*   * Conservation of value across the whole chain, including the queued    *)
(*     escrow (INV_Conservation).                                           *)
(*   * Balances never go negative (INV_NonNeg); a builder is only charged    *)
(*     when it can afford the bid.                                          *)
(*   * Liveness: the chain reaches its final slot, and every queued          *)
(*     withdrawal is eventually processed (LIVE_Drained).                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    NumSlots,   \* number of slots in the run
    StartBal,   \* builder's starting balance
    Value       \* bid value committed per included slot

ASSUME NumSlotsOK == NumSlots \in Nat /\ NumSlots > 0
ASSUME BalOK      == StartBal \in Nat /\ Value \in Nat /\ Value > 0

VARIABLES
    slot,         \* current slot index, 1..NumSlots+1 (NumSlots+1 = all proposed)
    proposerBal,  \* proposer balance (credited when a withdrawal is processed)
    builderBal,   \* builder balance (debited at inclusion)
    owed,         \* queued BuilderPendingWithdrawal value not yet paid out
    lastOutcome   \* the most recent slot outcome (for readability)

vars == <<slot, proposerBal, builderBal, owed, lastOutcome>>

Done_slot == NumSlots + 1

TypeOK ==
    /\ slot \in 1..(NumSlots + 1)
    /\ proposerBal \in Nat
    /\ builderBal \in Nat
    /\ owed \in Nat
    /\ lastOutcome \in {"none","full","empty","reorged","skipped"}

Init ==
    /\ slot = 1
    /\ proposerBal = 0
    /\ builderBal = StartBal
    /\ owed = 0
    /\ lastOutcome = "none"

(* Canonical block with a revealed payload: builder charged, proposer owed. *)
SlotFull ==
    /\ slot =< NumSlots
    /\ builderBal >= Value
    /\ builderBal' = builderBal - Value
    /\ owed' = owed + Value
    /\ slot' = slot + 1
    /\ lastOutcome' = "full"
    /\ UNCHANGED proposerBal

(* Canonical block, payload withheld: proposer still owed (unconditional pay). *)
SlotEmpty ==
    /\ slot =< NumSlots
    /\ builderBal >= Value
    /\ builderBal' = builderBal - Value
    /\ owed' = owed + Value
    /\ slot' = slot + 1
    /\ lastOutcome' = "empty"
    /\ UNCHANGED proposerBal

(* Block not canonical: builder not charged. *)
SlotReorged ==
    /\ slot =< NumSlots
    /\ slot' = slot + 1
    /\ lastOutcome' = "reorged"
    /\ UNCHANGED <<proposerBal, builderBal, owed>>

(* No builder included. *)
SlotSkipped ==
    /\ slot =< NumSlots
    /\ slot' = slot + 1
    /\ lastOutcome' = "skipped"
    /\ UNCHANGED <<proposerBal, builderBal, owed>>

(* Process one queued withdrawal (asynchronous, may be a later slot). *)
Drain ==
    /\ owed >= Value
    /\ owed' = owed - Value
    /\ proposerBal' = proposerBal + Value
    /\ UNCHANGED <<slot, builderBal, lastOutcome>>

(* Terminal: all slots proposed and all withdrawals processed. *)
Finished == slot = Done_slot /\ owed = 0 /\ UNCHANGED vars

Next ==
    \/ SlotFull \/ SlotEmpty \/ SlotReorged \/ SlotSkipped
    \/ Drain
    \/ Finished

Fairness ==
    /\ WF_vars(SlotFull \/ SlotEmpty \/ SlotReorged \/ SlotSkipped)
    /\ WF_vars(Drain)

Spec == Init /\ [][Next]_vars /\ Fairness

-------------------------------------------------------------------------------
(* SAFETY *)

\* Value is conserved across the chain, including the queued escrow.
INV_Conservation ==
    proposerBal + builderBal + owed = StartBal

\* No balance or queue ever goes negative.
INV_NonNeg ==
    /\ builderBal >= 0
    /\ proposerBal >= 0
    /\ owed >= 0

\* The proposer is never paid more in total than the builder was charged.
INV_NoOverpay ==
    proposerBal + owed = StartBal - builderBal

-------------------------------------------------------------------------------
(* LIVENESS *)

\* The chain reaches its final slot.
LIVE_Progress == <>(slot = Done_slot)

\* Every queued withdrawal is eventually processed and the chain finishes.
LIVE_Drained == <>(slot = Done_slot /\ owed = 0)

=============================================================================
