-------------------------------- MODULE EPBSPTC -----------------------------
(***************************************************************************)
(* A refined model of the EIP-7732 Payload-Timeliness Committee (PTC).     *)
(*                                                                         *)
(* The milestone-1 model (EPBS.tla) has the whole committee vote in one     *)
(* atomic step. Real PTC attestations arrive as individual PayloadAttestation *)
(* messages, interleaved, before an attestation deadline. Byzantine members  *)
(* may vote either way or abstain, and their messages may be late.          *)
(*                                                                         *)
(* This model casts each attester's vote as its own step:                  *)
(*   * Honest attesters are prompt and vote the truth: "present" iff the    *)
(*     committed payload was revealed on time. The deadline waits for them  *)
(*     (an honest attester's vote is not late).                            *)
(*   * Byzantine attesters may vote "present" or "absent", or never vote.   *)
(*   * At the deadline the tally counts the "present" votes received; the    *)
(*     payload is deemed present iff at least PayloadTimelyThreshold did.    *)
(*                                                                         *)
(* The threshold is set so a Byzantine minority alone cannot force          *)
(* "present" and the honest members alone can reach it (the EIP-7732        *)
(* honest-majority margin). Under that assumption the key result is         *)
(* INV_Correct: the interleaved, timed tally always equals the truth. That  *)
(* is exactly what justifies the atomic PTCVote step in EPBS.tla: this model *)
(* shows the atomic step is a SOUND abstraction of the real per-attester,    *)
(* timed process.                                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Attesters,              \* PTC members for the slot
    ByzAttesters,           \* subset that may vote dishonestly or abstain
    PayloadTimelyThreshold  \* "present" votes needed (PAYLOAD_TIMELY_THRESHOLD)

ASSUME ByzOK == ByzAttesters \subseteq Attesters

HonestAttesters == Attesters \ ByzAttesters

\* Byzantine members cannot force "present", honest members can reach it.
ASSUME ThresholdOK ==
    /\ PayloadTimelyThreshold \in Nat
    /\ PayloadTimelyThreshold > Cardinality(ByzAttesters)
    /\ PayloadTimelyThreshold =< Cardinality(HonestAttesters)

VARIABLES
    phase,          \* "voting" -> "closed" -> "final"
    payloadTimely,  \* BOOLEAN : was the committed payload revealed on time
    votes,          \* [Attesters -> {"none","present","absent"}]
    result          \* "undecided" | "present" | "absent"

vars == <<phase, payloadTimely, votes, result>>

TypeOK ==
    /\ phase \in {"voting","closed","final"}
    /\ payloadTimely \in BOOLEAN
    /\ votes \in [Attesters -> {"none","present","absent"}]
    /\ result \in {"undecided","present","absent"}

\* Two initial states, one per truth value of payloadTimely, both explored.
Init ==
    /\ phase = "voting"
    /\ payloadTimely \in BOOLEAN
    /\ votes = [a \in Attesters |-> "none"]
    /\ result = "undecided"

\* An honest attester votes the truth.
HonestVote(a) ==
    /\ phase = "voting"
    /\ a \in HonestAttesters
    /\ votes[a] = "none"
    /\ votes' = [votes EXCEPT ![a] = IF payloadTimely THEN "present" ELSE "absent"]
    /\ UNCHANGED <<phase, payloadTimely, result>>

\* A Byzantine attester votes either way.
ByzVote(a, v) ==
    /\ phase = "voting"
    /\ a \in ByzAttesters
    /\ votes[a] = "none"
    /\ v \in {"present","absent"}
    /\ votes' = [votes EXCEPT ![a] = v]
    /\ UNCHANGED <<phase, payloadTimely, result>>

AllHonestVoted == \A a \in HonestAttesters : votes[a] # "none"

\* The deadline. Honest attesters are prompt, so it waits for their votes;
\* Byzantine attesters may or may not have voted by now.
Deadline ==
    /\ phase = "voting"
    /\ AllHonestVoted
    /\ phase' = "closed"
    /\ UNCHANGED <<payloadTimely, votes, result>>

PresentCount == Cardinality({a \in Attesters : votes[a] = "present"})

Tally ==
    /\ phase = "closed"
    /\ result' = IF PresentCount >= PayloadTimelyThreshold THEN "present" ELSE "absent"
    /\ phase' = "final"
    /\ UNCHANGED <<payloadTimely, votes>>

Done == phase = "final" /\ UNCHANGED vars

Next ==
    \/ \E a \in Attesters : HonestVote(a)
    \/ \E a \in Attesters, v \in {"present","absent"} : ByzVote(a, v)
    \/ Deadline
    \/ Tally
    \/ Done

Fairness ==
    /\ WF_vars(\E a \in Attesters : HonestVote(a))
    /\ WF_vars(Deadline)
    /\ WF_vars(Tally)

Spec == Init /\ [][Next]_vars /\ Fairness

-------------------------------------------------------------------------------
(* SAFETY *)

\* No false present: a "present" tally implies the payload really was timely.
INV_NoFalsePresent ==
    (result = "present") => payloadTimely

\* No false absent: a timely payload is never tallied absent once decided.
INV_NoFalseAbsent ==
    (phase = "final" /\ payloadTimely) => (result = "present")

\* The strong result: the interleaved, timed tally always equals the truth.
\* This is what makes EPBS.tla's atomic PTC step a sound abstraction.
INV_Correct ==
    (phase = "final")
        => (result = IF payloadTimely THEN "present" ELSE "absent")

-------------------------------------------------------------------------------
(* LIVENESS *)

\* The committee always reaches a decision.
LIVE_Decided == <>(phase = "final")

=============================================================================
