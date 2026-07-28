-------------------------------- MODULE EPBS --------------------------------
(***************************************************************************)
(* A formal model of one slot of Enshrined Proposer-Builder Separation     *)
(* (ePBS) for Ethereum's Glamsterdam upgrade.                              *)
(*                                                                         *)
(* ePBS moves proposer/builder separation from out-of-protocol relays      *)
(* (MEV-Boost) into the consensus protocol itself. The central safety      *)
(* question is: can the split of duties between a proposer and a builder   *)
(* be griefed?  Concretely:                                                *)
(*                                                                         *)
(*   * Payment safety      - a proposer that includes a builder's bid is   *)
(*                           paid unconditionally, even if the builder     *)
(*                           later withholds or equivocates the payload.   *)
(*   * Commitment binding  - the payload that becomes canonical is always  *)
(*                           the one the proposer committed to; a builder   *)
(*                           cannot substitute a different payload after    *)
(*                           inclusion.                                     *)
(*   * Equivocation slashing - a builder that reveals a payload other than  *)
(*                           the committed one is slashed, and that payload *)
(*                           never becomes canonical.                       *)
(*   * No reorg on withhold - a withholding builder yields an empty slot,   *)
(*                           but does NOT unwind the proposer's beacon      *)
(*                           block.                                         *)
(*   * Liveness            - the slot always terminates, and an honest      *)
(*                           builder's timely payload always becomes        *)
(*                           canonical under an honest Payload-Timeliness   *)
(*                           Committee (PTC) majority.                      *)
(*                                                                         *)
(* This is the milestone-1 model. It abstracts the fork-choice rule and    *)
(* the beacon-chain state to a single boolean (beaconCanonical) and models  *)
(* payment with integer balances. Milestone 2 refines the PTC vote and     *)
(* the multi-slot fork choice. See PROPERTIES.md for the property catalog.  *)
(*                                                                         *)
(* STATUS: scaffold. Not yet model-checked. Running it under TLC is the     *)
(* first funded deliverable (see MILESTONES.md).                            *)
(***************************************************************************)
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS
    Builders,        \* set of builder identities
    Attesters,       \* set of PTC (Payload-Timeliness Committee) members
    ByzAttesters,    \* subset of Attesters that may vote dishonestly
    ByzBuilders,     \* subset of Builders that may withhold or equivocate
    Values,          \* set of possible bid values (positive naturals)
    StartBal         \* starting balance held by each builder

\* Sentinels (overridden to model values in EPBS.cfg).
CONSTANTS NONE

ASSUME ByzAttestersOK == ByzAttesters \subseteq Attesters
ASSUME ByzBuildersOK  == ByzBuilders  \subseteq Builders
\* Honest PTC majority: strictly fewer than half the attesters are Byzantine.
ASSUME HonestMajority == 2 * Cardinality(ByzAttesters) < Cardinality(Attesters)
ASSUME ValuesPositive == \A v \in Values : v > 0
ASSUME StartBalOK      == StartBal \in Nat /\ StartBal > 0

Accounts == {"proposer"} \cup Builders

VARIABLES
    phase,           \* "bidding" -> "proposing" -> "revealing" -> "attesting" -> "final"
    bids,            \* [Builders -> Values \cup {NONE}] : each builder's posted bid
    included,        \* Builders \cup {NONE} : the bid the proposer committed to
    paidValue,       \* Int : value transferred at inclusion (0 before inclusion)
    reveal,          \* "none" | "committed" | "equivocated" : what the included builder did
    ptcVote,         \* [Attesters -> {"present","absent","null"}]
    ptcResult,       \* "present" | "absent" | "null" : PTC tally
    bal,             \* [Accounts -> Int] : balances
    canonical,       \* "null" | "committed" | "EMPTY" : canonical payload for this slot
    slashed,         \* subset of Builders : slashed for equivocation
    beaconCanonical  \* BOOLEAN : proposer's beacon block is canonical

vars == <<phase, bids, included, paidValue, reveal, ptcVote, ptcResult,
          bal, canonical, slashed, beaconCanonical>>

Honest(b)  == b \notin ByzBuilders

-------------------------------------------------------------------------------
(* Balance bookkeeping *)
RECURSIVE SumBal(_)
SumBal(S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE e \in S : TRUE IN bal[x] + SumBal(S \ {x})

InitialTotal == Cardinality(Builders) * StartBal

-------------------------------------------------------------------------------
TypeOK ==
    /\ phase \in {"bidding","proposing","revealing","attesting","final"}
    /\ bids \in [Builders -> Values \cup {NONE}]
    /\ included \in Builders \cup {NONE}
    /\ paidValue \in Int
    /\ reveal \in {"none","committed","equivocated"}
    /\ ptcVote \in [Attesters -> {"present","absent","null"}]
    /\ ptcResult \in {"present","absent","null"}
    /\ bal \in [Accounts -> Int]
    /\ canonical \in {"null","committed","EMPTY"}
    /\ slashed \subseteq Builders
    /\ beaconCanonical \in BOOLEAN

Init ==
    /\ phase = "bidding"
    /\ bids = [b \in Builders |-> NONE]
    /\ included = NONE
    /\ paidValue = 0
    /\ reveal = "none"
    /\ ptcVote = [a \in Attesters |-> "null"]
    /\ ptcResult = "null"
    /\ bal = [x \in Accounts |-> IF x = "proposer" THEN 0 ELSE StartBal]
    /\ canonical = "null"
    /\ slashed = {}
    /\ beaconCanonical = FALSE

-------------------------------------------------------------------------------
(* A builder posts a bid it can afford. *)
SubmitBid(b, v) ==
    /\ phase = "bidding"
    /\ bids[b] = NONE
    /\ v \in Values
    /\ bal[b] >= v
    /\ bids' = [bids EXCEPT ![b] = v]
    /\ UNCHANGED <<phase, included, paidValue, reveal, ptcVote, ptcResult,
                   bal, canonical, slashed, beaconCanonical>>

CloseBidding ==
    /\ phase = "bidding"
    /\ phase' = "proposing"
    /\ UNCHANGED <<bids, included, paidValue, reveal, ptcVote, ptcResult,
                   bal, canonical, slashed, beaconCanonical>>

(* The proposer includes a builder's bid. Payment is UNCONDITIONAL and       *)
(* happens now, at inclusion, not at reveal. This is the ePBS invariant that  *)
(* protects the proposer from a griefing builder.                            *)
ProposerInclude(b) ==
    /\ phase = "proposing"
    /\ included = NONE
    /\ bids[b] # NONE
    /\ included' = b
    /\ paidValue' = bids[b]
    /\ bal' = [bal EXCEPT !["proposer"] = @ + bids[b], ![b] = @ - bids[b]]
    /\ beaconCanonical' = TRUE
    /\ phase' = "revealing"
    /\ UNCHANGED <<bids, reveal, ptcVote, ptcResult, canonical, slashed>>

(* The proposer may instead propose an empty slot (no bid worth including). *)
ProposerSkip ==
    /\ phase = "proposing"
    /\ included = NONE
    /\ canonical' = "EMPTY"
    /\ beaconCanonical' = TRUE
    /\ phase' = "final"
    /\ UNCHANGED <<bids, included, paidValue, reveal, ptcVote, ptcResult,
                   bal, slashed>>

(* Reveal actions for the included builder. *)
BuilderRevealCommitted ==
    /\ phase = "revealing"
    /\ included # NONE
    /\ reveal' = "committed"
    /\ phase' = "attesting"
    /\ UNCHANGED <<bids, included, paidValue, ptcVote, ptcResult,
                   bal, canonical, slashed, beaconCanonical>>

BuilderWithhold ==
    /\ phase = "revealing"
    /\ included # NONE
    /\ included \in ByzBuilders          \* only a Byzantine builder withholds
    /\ reveal' = "none"
    /\ phase' = "attesting"
    /\ UNCHANGED <<bids, included, paidValue, ptcVote, ptcResult,
                   bal, canonical, slashed, beaconCanonical>>

BuilderEquivocate ==
    /\ phase = "revealing"
    /\ included # NONE
    /\ included \in ByzBuilders          \* only a Byzantine builder equivocates
    /\ reveal' = "equivocated"
    /\ phase' = "attesting"
    /\ UNCHANGED <<bids, included, paidValue, ptcVote, ptcResult,
                   bal, canonical, slashed, beaconCanonical>>

(* The PTC votes. An honest attester votes the truth: "present" iff the     *)
(* committed payload was revealed on time. A Byzantine attester may vote     *)
(* either way. All attesters vote in one atomic step for tractability.       *)
TruthVote == IF reveal = "committed" THEN "present" ELSE "absent"

PTCVote ==
    /\ phase = "attesting"
    /\ ptcVote = [a \in Attesters |-> "null"]
    /\ \E byzChoice \in [ByzAttesters -> {"present","absent"}] :
         ptcVote' = [a \in Attesters |->
                        IF a \in ByzAttesters THEN byzChoice[a] ELSE TruthVote]
    /\ UNCHANGED <<phase, bids, included, paidValue, reveal, ptcResult,
                   bal, canonical, slashed, beaconCanonical>>

Present == Cardinality({a \in Attesters : ptcVote[a] = "present"})
Absent  == Cardinality({a \in Attesters : ptcVote[a] = "absent"})

(* Tally the vote, resolve the canonical payload, and slash equivocation.   *)
Finalize ==
    /\ phase = "attesting"
    /\ ptcVote # [a \in Attesters |-> "null"]
    /\ ptcResult' = IF Present > Absent THEN "present" ELSE "absent"
    /\ slashed' = IF reveal = "equivocated" THEN slashed \cup {included} ELSE slashed
    /\ canonical' =
         CASE reveal = "equivocated"          -> "EMPTY"
           [] (ptcResult' = "present")        -> "committed"
           [] OTHER                           -> "EMPTY"
    /\ phase' = "final"
    /\ UNCHANGED <<bids, included, paidValue, reveal, ptcVote,
                   bal, beaconCanonical>>

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
    /\ WF_vars(\E b \in Builders : ProposerInclude(b) \/ ProposerSkip)
    /\ WF_vars(BuilderRevealCommitted \/ BuilderWithhold \/ BuilderEquivocate)
    /\ WF_vars(PTCVote)
    /\ WF_vars(Finalize)

Spec == Init /\ [][Next]_vars /\ Fairness

-------------------------------------------------------------------------------
(* SAFETY INVARIANTS (state predicates; see PROPERTIES.md).                 *)

\* S1. A proposer that included a bid holds exactly the bid value paid.
INV_PaymentSafety ==
    (included # NONE) => (bal["proposer"] = paidValue /\ paidValue > 0)

\* S2. The proposer keeps the payment even if the builder misbehaves.
INV_NoStealFromProposer ==
    (included # NONE /\ reveal \in {"none","equivocated"})
        => (bal["proposer"] = paidValue)

\* S3. A canonical payload is always the committed one, never a substitute.
INV_CommitmentBinding ==
    (canonical = "committed") => (reveal = "committed")

\* S4. An equivocated payload never becomes canonical.
INV_EquivocationRejected ==
    (reveal = "equivocated") => (canonical # "committed")

\* S5. Equivocation is slashed by the time the slot is final.
INV_EquivocationSlashed ==
    (phase = "final" /\ reveal = "equivocated") => (included \in slashed)

\* S6. Value is conserved: payment is a transfer, nothing is minted or burned.
INV_Conservation ==
    bal["proposer"] + SumBal(Builders) = InitialTotal

\* S7. No honest party is ever slashed (only Byzantine builders can be).
INV_OnlyByzSlashed ==
    slashed \subseteq ByzBuilders

\* S8. Once a bid is included, the beacon block stays canonical regardless of
\*     what the builder does (no reorg of the proposer's block on withhold).
INV_NoReorgOnWithhold ==
    (included # NONE) => beaconCanonical

Safety ==
    /\ TypeOK
    /\ INV_PaymentSafety
    /\ INV_NoStealFromProposer
    /\ INV_CommitmentBinding
    /\ INV_EquivocationRejected
    /\ INV_EquivocationSlashed
    /\ INV_Conservation
    /\ INV_OnlyByzSlashed
    /\ INV_NoReorgOnWithhold

-------------------------------------------------------------------------------
(* LIVENESS (temporal properties). *)

\* L1. Every slot terminates.
LIVE_Progress == <>(phase = "final")

\* L2. An honest builder's timely reveal becomes canonical (honest PTC
\*     majority guarantees the tally reflects the truth).
LIVE_HonestRevealCanonical ==
    [](reveal = "committed" => <>(canonical = "committed"))

=============================================================================
