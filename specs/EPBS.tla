-------------------------------- MODULE EPBS --------------------------------
(***************************************************************************)
(* A formal model of one slot of Enshrined Proposer-Builder Separation     *)
(* (ePBS) as specified in EIP-7732, for Ethereum's Glamsterdam upgrade.    *)
(*                                                                         *)
(* This model tracks the actual mechanism in EIP-7732:                     *)
(*                                                                         *)
(*   * The proposer includes a builder's SignedExecutionPayloadBid in the  *)
(*     BeaconBlockBody. At block processing the committed value is deducted *)
(*     from the builder's beacon-chain balance as a BuilderPendingPayment.  *)
(*   * The builder later reveals a SignedExecutionPayloadEnvelope, or       *)
(*     withholds it, or equivocates (reveals a different payload).          *)
(*   * A Payload-Timeliness Committee (PTC) attests payload_present. The     *)
(*     payload is deemed present iff at least PayloadTimelyThreshold members *)
(*     attest present.                                                       *)
(*   * If the beacon block is canonical, the pending payment is finalized to *)
(*     the proposer (a BuilderPendingWithdrawal). If the beacon block is not *)
(*     canonical (withheld or reorged), the pending payment is reverted and  *)
(*     the builder is not charged.                                          *)
(*                                                                         *)
(* The three safety guarantees EIP-7732 states for itself are modeled       *)
(* directly:                                                                *)
(*   G1 Proposer unconditional payment - a canonical beacon block pays the  *)
(*      proposer even if the builder withholds or equivocates the payload.   *)
(*   G2 Builder reveal safety - an honest, timely reveal on a canonical      *)
(*      block, attested by an honest PTC, becomes the canonical payload.     *)
(*   G3 Builder withhold safety - if the beacon block is not canonical, the  *)
(*      builder is not charged.                                             *)
(*                                                                         *)
(* IMPORTANT FIDELITY NOTE: EIP-7732 deliberately has NO slashing for       *)
(* payload equivocation (it accepts a split-view cost to the builder for    *)
(* implementation simplicity). This model reflects that: slashing is off by  *)
(* default. The EIP mentions an OPTIONAL mitigation to add equivocation      *)
(* slashing; that variant is available via the SlashEquivocation constant so *)
(* both the base spec and the proposed mitigation can be checked.           *)
(*                                                                         *)
(* Scope: single slot. The fork choice and multi-slot history are abstracted *)
(* to blockFate (canonical vs reorged). Milestone 2 refines these.          *)
(*                                                                         *)
(* STATUS: milestone 1, model-checked with TLC. See RESULTS.md.             *)
(***************************************************************************)
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS
    Builders,               \* set of staked builder identities
    ByzBuilders,            \* subset that may withhold or equivocate
    Attesters,              \* PTC members for this slot (get_ptc)
    ByzAttesters,           \* subset that may attest dishonestly
    Values,                 \* possible bid values (positive naturals)
    StartBal,               \* starting beacon-chain balance of each builder
    PayloadTimelyThreshold, \* PTC "present" votes needed (PAYLOAD_TIMELY_THRESHOLD)
    SlashEquivocation       \* FALSE = base EIP-7732; TRUE = optional slashing mitigation

CONSTANTS NONE

ASSUME ByzBuildersOK  == ByzBuilders  \subseteq Builders
ASSUME ByzAttestersOK == ByzAttesters \subseteq Attesters
ASSUME ValuesPositive == \A v \in Values : v > 0
ASSUME StartBalOK     == StartBal \in Nat /\ StartBal > 0
ASSUME SlashFlagOK    == SlashEquivocation \in BOOLEAN

\* Threshold is set so that a Byzantine PTC minority alone cannot force
\* "present" (threshold > Byzantine count), and the honest members alone can
\* reach it (threshold =< honest count). This is the honest-majority security
\* margin EIP-7732 describes (e.g. a 2/3 PAYLOAD_TIMELY_THRESHOLD).
ASSUME ThresholdOK ==
    /\ PayloadTimelyThreshold \in Nat
    /\ PayloadTimelyThreshold > Cardinality(ByzAttesters)
    /\ PayloadTimelyThreshold =< Cardinality(Attesters) - Cardinality(ByzAttesters)

Accounts == {"proposer"} \cup Builders
AllNull  == [a \in Attesters |-> "null"]

VARIABLES
    phase,            \* "bidding" -> "proposing" -> "revealing" -> "attesting" -> "final"
    bids,             \* [Builders -> Values \cup {NONE}]
    included,         \* Builders \cup {NONE} : builder committed in the beacon block
    committedValue,   \* Int : the bid value committed to (0 before inclusion)
    pending,          \* Int : BuilderPendingPayment held in escrow (0 when settled)
    reveal,           \* "none" | "committed" | "equivocated"
    ptcVote,          \* [Attesters -> {"present","absent","null"}]
    ptcResult,        \* "present" | "absent" | "null"
    bal,              \* [Accounts -> Int] : beacon-chain balances
    payloadCanonical, \* "none" | "committed" : the canonical execution payload
    blockFate,        \* "pending" | "canonical" | "reorged" : fate of the beacon block
    slashed           \* subset of Builders (empty unless SlashEquivocation)

vars == <<phase, bids, included, committedValue, pending, reveal, ptcVote,
          ptcResult, bal, payloadCanonical, blockFate, slashed>>

-------------------------------------------------------------------------------
RECURSIVE SumBal(_)
SumBal(S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE e \in S : TRUE IN bal[x] + SumBal(S \ {x})

InitialTotal == Cardinality(Builders) * StartBal

-------------------------------------------------------------------------------
TypeOK ==
    /\ phase \in {"bidding","proposing","revealing","attesting","final"}
    /\ bids \in [Builders -> Values \cup {NONE}]
    /\ included \in Builders \cup {NONE}
    /\ committedValue \in Int
    /\ pending \in Int
    /\ reveal \in {"none","committed","equivocated"}
    /\ ptcVote \in [Attesters -> {"present","absent","null"}]
    /\ ptcResult \in {"present","absent","null"}
    /\ bal \in [Accounts -> Int]
    /\ payloadCanonical \in {"none","committed"}
    /\ blockFate \in {"pending","canonical","reorged"}
    /\ slashed \subseteq Builders

Init ==
    /\ phase = "bidding"
    /\ bids = [b \in Builders |-> NONE]
    /\ included = NONE
    /\ committedValue = 0
    /\ pending = 0
    /\ reveal = "none"
    /\ ptcVote = AllNull
    /\ ptcResult = "null"
    /\ bal = [x \in Accounts |-> IF x = "proposer" THEN 0 ELSE StartBal]
    /\ payloadCanonical = "none"
    /\ blockFate = "pending"
    /\ slashed = {}

-------------------------------------------------------------------------------
SubmitBid(b, v) ==
    /\ phase = "bidding"
    /\ bids[b] = NONE
    /\ v \in Values
    /\ bal[b] >= v
    /\ bids' = [bids EXCEPT ![b] = v]
    /\ UNCHANGED <<phase, included, committedValue, pending, reveal, ptcVote,
                   ptcResult, bal, payloadCanonical, blockFate, slashed>>

CloseBidding ==
    /\ phase = "bidding"
    /\ phase' = "proposing"
    /\ UNCHANGED <<bids, included, committedValue, pending, reveal, ptcVote,
                   ptcResult, bal, payloadCanonical, blockFate, slashed>>

(* Proposer includes a bid. The committed value is deducted from the        *)
(* builder's balance NOW (BuilderPendingPayment), before any reveal.        *)
ProposerInclude(b) ==
    /\ phase = "proposing"
    /\ included = NONE
    /\ bids[b] # NONE
    /\ included' = b
    /\ committedValue' = bids[b]
    /\ pending' = bids[b]
    /\ bal' = [bal EXCEPT ![b] = @ - bids[b]]
    /\ phase' = "revealing"
    /\ UNCHANGED <<bids, reveal, ptcVote, ptcResult, payloadCanonical,
                   blockFate, slashed>>

(* Proposer proposes an empty beacon block (no builder, no payment). *)
ProposerSkip ==
    /\ phase = "proposing"
    /\ included = NONE
    /\ blockFate' = "canonical"
    /\ payloadCanonical' = "none"
    /\ phase' = "final"
    /\ UNCHANGED <<bids, included, committedValue, pending, reveal, ptcVote,
                   ptcResult, bal, slashed>>

BuilderRevealCommitted ==
    /\ phase = "revealing"
    /\ included # NONE
    /\ reveal' = "committed"
    /\ phase' = "attesting"
    /\ UNCHANGED <<bids, included, committedValue, pending, ptcVote, ptcResult,
                   bal, payloadCanonical, blockFate, slashed>>

BuilderWithhold ==
    /\ phase = "revealing"
    /\ included \in ByzBuilders
    /\ reveal' = "none"
    /\ phase' = "attesting"
    /\ UNCHANGED <<bids, included, committedValue, pending, ptcVote, ptcResult,
                   bal, payloadCanonical, blockFate, slashed>>

BuilderEquivocate ==
    /\ phase = "revealing"
    /\ included \in ByzBuilders
    /\ reveal' = "equivocated"
    /\ phase' = "attesting"
    /\ UNCHANGED <<bids, included, committedValue, pending, ptcVote, ptcResult,
                   bal, payloadCanonical, blockFate, slashed>>

(* PTC votes atomically. Honest members vote present iff the committed       *)
(* payload was revealed; Byzantine members vote arbitrarily.                 *)
PTCVote ==
    /\ phase = "attesting"
    /\ ptcVote = AllNull
    /\ \E byz \in [ByzAttesters -> {"present","absent"}] :
         ptcVote' = [a \in Attesters |->
                        IF a \in ByzAttesters THEN byz[a]
                        ELSE IF reveal = "committed" THEN "present" ELSE "absent"]
    /\ UNCHANGED <<phase, bids, included, committedValue, pending, reveal,
                   ptcResult, bal, payloadCanonical, blockFate, slashed>>

Present == Cardinality({a \in Attesters : ptcVote[a] = "present"})

(* Tally the PTC, decide the beacon block's fate (canonical or reorged),     *)
(* settle the pending payment accordingly, and resolve the canonical payload.*)
Finalize ==
    /\ phase = "attesting"
    /\ ptcVote # AllNull
    /\ LET result == IF Present >= PayloadTimelyThreshold THEN "present" ELSE "absent"
       IN /\ ptcResult' = result
          /\ \E fate \in {"canonical","reorged"} :
               /\ blockFate' = fate
               /\ IF fate = "canonical"
                  THEN /\ bal' = [bal EXCEPT !["proposer"] = @ + pending]
                       /\ payloadCanonical' =
                            IF reveal = "committed" /\ result = "present"
                            THEN "committed" ELSE "none"
                  ELSE /\ bal' = [bal EXCEPT ![included] = @ + pending]
                       /\ payloadCanonical' = "none"
    /\ pending' = 0
    /\ slashed' = IF SlashEquivocation /\ reveal = "equivocated"
                  THEN {included} ELSE slashed
    /\ phase' = "final"
    /\ UNCHANGED <<bids, included, committedValue, reveal, ptcVote>>

Done == phase = "final" /\ UNCHANGED vars

Next ==
    \/ \E b \in Builders, v \in Values : SubmitBid(b, v)
    \/ CloseBidding
    \/ \E b \in Builders : ProposerInclude(b)
    \/ ProposerSkip
    \/ BuilderRevealCommitted
    \/ BuilderWithhold
    \/ BuilderEquivocate
    \/ PTCVote
    \/ Finalize
    \/ Done

Fairness ==
    /\ WF_vars(CloseBidding)
    /\ WF_vars((\E b \in Builders : ProposerInclude(b)) \/ ProposerSkip)
    /\ WF_vars(BuilderRevealCommitted \/ BuilderWithhold \/ BuilderEquivocate)
    /\ WF_vars(PTCVote)
    /\ WF_vars(Finalize)

Spec == Init /\ [][Next]_vars /\ Fairness

-------------------------------------------------------------------------------
(* SAFETY. The three EIP-7732 guarantees plus structural hygiene. *)

\* G1. Proposer unconditional payment: a canonical beacon block that included
\*     a bid pays the proposer the full committed value, whatever the builder
\*     did with the payload.
INV_G1_ProposerUnconditionalPayment ==
    (phase = "final" /\ included # NONE /\ blockFate = "canonical")
        => (bal["proposer"] = committedValue /\ committedValue > 0)

\* G2. Builder reveal safety: an honest, timely reveal on a canonical block,
\*     attested present by the PTC, is the canonical payload.
INV_G2_BuilderRevealSafety ==
    (blockFate = "canonical" /\ reveal = "committed" /\ ptcResult = "present")
        => (payloadCanonical = "committed")

\* G3. Builder withhold safety: if the beacon block is not canonical, the
\*     builder is not charged and the proposer is not paid.
INV_G3_BuilderWithholdSafety ==
    (phase = "final" /\ included # NONE /\ blockFate = "reorged")
        => (bal[included] = StartBal /\ bal["proposer"] = 0)

\* Commitment binding: the canonical payload is only ever the committed one.
INV_CommitmentBinding ==
    (payloadCanonical = "committed") => (reveal = "committed")

\* An equivocated payload never becomes canonical.
INV_EquivocationNotCanonical ==
    (reveal = "equivocated") => (payloadCanonical # "committed")

\* Value is conserved across balances and the pending-payment escrow.
INV_Conservation ==
    bal["proposer"] + SumBal(Builders) + pending = InitialTotal

\* No payment is left dangling once the slot is final.
INV_NoDanglingPayment ==
    (phase = "final") => (pending = 0)

\* Base EIP-7732 has no equivocation slashing. Slashing appears only when the
\* optional mitigation is enabled, and then only for a Byzantine equivocator.
INV_SlashingFaithful ==
    /\ (~SlashEquivocation => slashed = {})
    /\ slashed \subseteq ByzBuilders

Safety ==
    /\ TypeOK
    /\ INV_G1_ProposerUnconditionalPayment
    /\ INV_G2_BuilderRevealSafety
    /\ INV_G3_BuilderWithholdSafety
    /\ INV_CommitmentBinding
    /\ INV_EquivocationNotCanonical
    /\ INV_Conservation
    /\ INV_NoDanglingPayment
    /\ INV_SlashingFaithful

-------------------------------------------------------------------------------
(* LIVENESS. *)

\* Every slot terminates.
LIVE_Progress == <>(phase = "final")

=============================================================================
