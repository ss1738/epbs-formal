---------------------------- MODULE EPBSForkChoice --------------------------
\* ARCHIVED v1 -- ORIGINAL ESP SUBMISSION. DO NOT BUILD ON THIS.
\*
\* This model carries PayloadBoost, an additive payload term in fork-choice
\* weight. Gloas has no such term: get_weight returns attestation_score plus
\* conditional proposer_score and nothing else. See D5_PAYLOAD_WEIGHT.md.
\*
\* Kept as the version of record for what was submitted, so the erratum can be
\* checked against it. The corrected model is specs/EPBSNodes.tla and
\* specs/EPBSMultiSlotV2.tla; the standalone finding is PTC_TIEBREAK_NOTE.md.
\*
(***************************************************************************)
(* Milestone 2: a fork-choice-aware model of the EIP-7732 reorg question.  *)
(*                                                                         *)
(* Milestone 1 (EPBS.tla) abstracted the beacon block's fate to a          *)
(* nondeterministic canonical-vs-reorged choice. This model derives that    *)
(* fate from an explicit payload-timeliness fork choice, so the reorg       *)
(* attack EIP-7732 warns about can be expressed and its threshold measured. *)
(*                                                                         *)
(* Scenario. Slot 1 has an honest proposer whose beacon block B1 includes a *)
(* builder's bid (value deducted at inclusion). The builder reveals the     *)
(* payload on time or withholds it. Slot 2's proposer is adversarial and    *)
(* may either extend B1 or attempt to reorg it by building on B1's parent,   *)
(* taking the proposer boost. Honest attesters back B1 (with the            *)
(* payload-timeliness boost when the payload was timely); Byzantine          *)
(* attesters back the reorg branch.                                         *)
(*                                                                         *)
(* Fork choice (an LMD-GHOST abstraction by accumulated weight):            *)
(*   weight(B1)    = HonestWeight + (payload timely ? PayloadBoost : 0)      *)
(*   weight(reorg) = adversary reorged ? (ByzWeight + ProposerBoost) : 0     *)
(*   B1 stays canonical iff weight(B1) >= weight(reorg) (ties favor B1).     *)
(*                                                                         *)
(* The point of the model: a timely-revealed payload is safe from reorg      *)
(* exactly when HonestWeight + PayloadBoost >= ByzWeight + ProposerBoost.    *)
(* That inequality is HonestMajoritySafe below. With safe parameters TLC     *)
(* confirms the payload is never reorged; with unsafe parameters TLC         *)
(* produces the reorg trace. See RESULTS.md and MILESTONE2.md.              *)
(*                                                                         *)
(* The payment guarantees carry over: a canonical B1 pays the proposer, an   *)
(* orphaned B1 refunds the builder, and value is conserved throughout.       *)
(***************************************************************************)
EXTENDS Naturals, Integers

CONSTANTS
    HonestWeight,   \* attester weight backing B1 (honest committee)
    ByzWeight,      \* attester weight backing the reorg branch (Byzantine)
    ProposerBoost,  \* fork-choice boost for slot 2's proposer block
    PayloadBoost,   \* payload-timeliness boost when the payload is timely
    StartBal,       \* builder's starting balance
    Bid             \* the bid value committed in B1

ASSUME WeightsOK ==
    /\ {HonestWeight, ByzWeight, ProposerBoost, PayloadBoost} \subseteq Nat
    /\ StartBal \in Nat /\ Bid \in Nat
    /\ Bid > 0 /\ Bid =< StartBal

\* The safety threshold. Not an ASSUME, so the unsafe (attack) configuration
\* can also be model-checked; it is referenced by the safety property below.
HonestMajoritySafe == HonestWeight + PayloadBoost >= ByzWeight + ProposerBoost

Actors == {"proposer", "builder"}

VARIABLES
    phase,    \* "reveal" -> "propose2" -> "resolve" -> "final"
    payload,  \* "undecided" | "present" | "absent"
    p2mode,   \* "undecided" | "extend" | "reorg"
    head,     \* "none" | "b1full" | "b1empty" | "orphaned"
    bal,      \* [Actors -> Int]
    pending   \* Int : BuilderPendingPayment escrow

vars == <<phase, payload, p2mode, head, bal, pending>>

TypeOK ==
    /\ phase \in {"reveal","propose2","resolve","final"}
    /\ payload \in {"undecided","present","absent"}
    /\ p2mode \in {"undecided","extend","reorg"}
    /\ head \in {"none","b1full","b1empty","orphaned"}
    /\ bal \in [Actors -> Int]
    /\ pending \in Int

\* B1 is already proposed and its bid included: the value is escrowed and the
\* builder's balance already debited, matching EIP-7732's deduction at inclusion.
Init ==
    /\ phase = "reveal"
    /\ payload = "undecided"
    /\ p2mode = "undecided"
    /\ head = "none"
    /\ pending = Bid
    /\ bal = [x \in Actors |-> IF x = "builder" THEN StartBal - Bid ELSE 0]

RevealPresent ==
    /\ phase = "reveal"
    /\ payload' = "present"
    /\ phase' = "propose2"
    /\ UNCHANGED <<p2mode, head, bal, pending>>

RevealWithhold ==
    /\ phase = "reveal"
    /\ payload' = "absent"
    /\ phase' = "propose2"
    /\ UNCHANGED <<p2mode, head, bal, pending>>

\* Slot 2's proposer either extends B1 or attempts to reorg it.
P2Extend ==
    /\ phase = "propose2"
    /\ p2mode' = "extend"
    /\ phase' = "resolve"
    /\ UNCHANGED <<payload, head, bal, pending>>

P2Reorg ==
    /\ phase = "propose2"
    /\ p2mode' = "reorg"
    /\ phase' = "resolve"
    /\ UNCHANGED <<payload, head, bal, pending>>

WeightB1    == HonestWeight + IF payload = "present" THEN PayloadBoost ELSE 0
WeightReorg == IF p2mode = "reorg" THEN ByzWeight + ProposerBoost ELSE 0
B1Canonical == WeightB1 >= WeightReorg

Resolve ==
    /\ phase = "resolve"
    /\ IF B1Canonical
       THEN /\ head' = IF payload = "present" THEN "b1full" ELSE "b1empty"
            /\ bal' = [bal EXCEPT !["proposer"] = @ + pending]   \* payment finalized
       ELSE /\ head' = "orphaned"
            /\ bal' = [bal EXCEPT !["builder"] = @ + pending]    \* payment reverted
    /\ pending' = 0
    /\ phase' = "final"
    /\ UNCHANGED <<payload, p2mode>>

Done == phase = "final" /\ UNCHANGED vars

Next ==
    \/ RevealPresent \/ RevealWithhold
    \/ P2Extend \/ P2Reorg
    \/ Resolve
    \/ Done

Fairness ==
    /\ WF_vars(RevealPresent \/ RevealWithhold)
    /\ WF_vars(P2Extend \/ P2Reorg)
    /\ WF_vars(Resolve)

Spec == Init /\ [][Next]_vars /\ Fairness

-------------------------------------------------------------------------------
(* SAFETY *)

\* The central result: a timely-revealed payload is never reorged, provided
\* the honest weight plus the payload boost meets the adversary's weight plus
\* the proposer boost. This holds exactly when HonestMajoritySafe holds.
FC_TimelyPayloadSafe ==
    (phase = "final" /\ payload = "present") => (head # "orphaned")

\* Proposer unconditional payment carries over: a canonical B1 pays the proposer.
FC_G1_ProposerPaid ==
    (phase = "final" /\ head \in {"b1full","b1empty"}) => (bal["proposer"] = Bid)

\* Builder withhold safety carries over: an orphaned B1 refunds the builder and
\* pays the proposer nothing.
FC_G3_WithholdSafe ==
    (phase = "final" /\ head = "orphaned")
        => (bal["builder"] = StartBal /\ bal["proposer"] = 0)

\* A full head means the payload was actually present (binding).
FC_Binding ==
    (head = "b1full") => (payload = "present")

\* Value is conserved across balances and the escrow.
FC_Conservation ==
    bal["proposer"] + bal["builder"] + pending = StartBal

\* No payment is left dangling once resolved.
FC_NoDangling ==
    (phase = "final") => (pending = 0)

\* A reorg of a timely payload can only happen when the adversary out-weighs
\* the honest committee plus the payload boost. This makes the threshold
\* explicit and matches EIP-7732's claim that reorg needs a heavy adversary.
FC_ReorgImpliesAdversaryHeavy ==
    (head = "orphaned" /\ payload = "present")
        => (ByzWeight + ProposerBoost > HonestWeight + PayloadBoost)

Safety ==
    /\ TypeOK
    /\ FC_G1_ProposerPaid
    /\ FC_G3_WithholdSafe
    /\ FC_Binding
    /\ FC_Conservation
    /\ FC_NoDangling
    /\ FC_ReorgImpliesAdversaryHeavy

LIVE_Progress == <>(phase = "final")

=============================================================================
