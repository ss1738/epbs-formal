--------------------------- MODULE EPBSWeightPayment ------------------------
(***************************************************************************)
(* A faithful model of the Gloas (ePBS) builder-payment settlement by       *)
(* attestation weight, closing the main abstraction delta noted in          *)
(* FIDELITY.md.                                                            *)
(*                                                                         *)
(* The other models abstract the builder payment to "canonical pays the     *)
(* proposer". The live Gloas spec is more subtle: at inclusion a            *)
(* BuilderPendingPayment is recorded but NOT immediately debited; validators *)
(* accumulate weight toward it via same-slot attestations; and              *)
(* process_builder_pending_payments settles it to the proposer only if the   *)
(* accumulated weight reaches a quorum. A non-canonical block never accrues  *)
(* that weight, so its payment never settles and the builder is not charged. *)
(*                                                                         *)
(* This model reproduces that mechanism directly (attesters accumulate       *)
(* weight; settlement is gated on a quorum) and shows the same guarantees    *)
(* the boolean model assumes now EMERGE from the weight dynamics:            *)
(*   - a canonical block pays the proposer (weight reaches quorum);          *)
(*   - a non-canonical block charges no one (weight stays below quorum);     *)
(*   - a Byzantine minority alone can never force a payment;                 *)
(*   - value is conserved.                                                  *)
(*                                                                         *)
(* Abstraction kept: each attester contributes unit weight rather than its   *)
(* effective balance; the quorum is expressed in attester units. This        *)
(* preserves the quorum structure while keeping the state space finite.      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Attesters,     \* validators who may attest weight toward the payment
    ByzAttesters,  \* subset that may attest even for a non-canonical block, or abstain
    Quorum,        \* attestation weight needed to settle (process_builder_pending_payments)
    StartBal,      \* builder's starting balance
    Value          \* the bid value owed to the proposer

ASSUME ByzOK == ByzAttesters \subseteq Attesters
ASSUME BalOK == StartBal \in Nat /\ Value \in Nat /\ Value > 0 /\ Value =< StartBal

HonestAttesters == Attesters \ ByzAttesters

\* Honest-majority quorum: a Byzantine minority alone cannot reach it, and the
\* honest attesters alone can. Mirrors the PTC threshold margin.
ASSUME QuorumOK ==
    /\ Quorum \in Nat
    /\ Quorum > Cardinality(ByzAttesters)
    /\ Quorum =< Cardinality(HonestAttesters)

Parties == {"proposer", "builder"}

VARIABLES
    phase,          \* "voting" -> "settled"
    blockCanonical, \* BOOLEAN : is the block that included the bid on the canonical chain
    attested,       \* [Attesters -> BOOLEAN] : who has attested weight so far
    bal             \* [Parties -> Int]

vars == <<phase, blockCanonical, attested, bal>>

Weight == Cardinality({a \in Attesters : attested[a]})

TypeOK ==
    /\ phase \in {"voting","settled"}
    /\ blockCanonical \in BOOLEAN
    /\ attested \in [Attesters -> BOOLEAN]
    /\ bal \in [Parties -> Nat]

\* Two initial states, one per canonicality. The value is not debited yet.
Init ==
    /\ phase = "voting"
    /\ blockCanonical \in BOOLEAN
    /\ attested = [a \in Attesters |-> FALSE]
    /\ bal = [x \in Parties |-> IF x = "builder" THEN StartBal ELSE 0]

\* An honest validator attests weight only for a block it sees as canonical.
HonestAttest(a) ==
    /\ phase = "voting"
    /\ a \in HonestAttesters
    /\ blockCanonical
    /\ ~attested[a]
    /\ attested' = [attested EXCEPT ![a] = TRUE]
    /\ UNCHANGED <<phase, blockCanonical, bal>>

\* A Byzantine validator may attest regardless (or never).
ByzAttest(a) ==
    /\ phase = "voting"
    /\ a \in ByzAttesters
    /\ ~attested[a]
    /\ attested' = [attested EXCEPT ![a] = TRUE]
    /\ UNCHANGED <<phase, blockCanonical, bal>>

\* Settlement (process_builder_pending_payments): honest validators are prompt,
\* so on a canonical block the deadline waits for their weight. If the weight
\* reached quorum the builder is debited and the proposer credited; otherwise
\* the pending payment lapses and no one is charged.
Settle ==
    /\ phase = "voting"
    /\ (blockCanonical => \A a \in HonestAttesters : attested[a])
    /\ IF Weight >= Quorum
       THEN bal' = [bal EXCEPT !["proposer"] = @ + Value, !["builder"] = @ - Value]
       ELSE bal' = bal
    /\ phase' = "settled"
    /\ UNCHANGED <<blockCanonical, attested>>

Done == phase = "settled" /\ UNCHANGED vars

Next ==
    \/ \E a \in Attesters : HonestAttest(a)
    \/ \E a \in Attesters : ByzAttest(a)
    \/ Settle
    \/ Done

Fairness ==
    /\ WF_vars(\E a \in Attesters : HonestAttest(a))
    /\ WF_vars(Settle)

Spec == Init /\ [][Next]_vars /\ Fairness

-------------------------------------------------------------------------------
(* SAFETY *)

\* A Byzantine minority alone can never accumulate quorum on a non-canonical
\* block, so no payment can be forced.
INV_NoForcedPay ==
    (~blockCanonical) => (Weight < Quorum)

\* A canonical block pays the proposer exactly the bid value.
INV_CanonicalPays ==
    (phase = "settled" /\ blockCanonical) => (bal["proposer"] = Value)

\* A non-canonical block charges no one: the builder keeps its balance and the
\* proposer is paid nothing. This is builder withhold safety, emerging from the
\* weight mechanism rather than assumed.
INV_NonCanonicalRefunds ==
    (phase = "settled" /\ ~blockCanonical)
        => (bal["builder"] = StartBal /\ bal["proposer"] = 0)

\* Value is conserved.
INV_Conservation ==
    bal["proposer"] + bal["builder"] = StartBal

-------------------------------------------------------------------------------
(* LIVENESS *)

\* The pending payment is always resolved.
LIVE_Settled == <>(phase = "settled")

=============================================================================
