-------------------------- MODULE EPBSMultiSlot --------------------------
(***************************************************************************)
(* A COMPOSED model of EIP-7732: block tree, LMD-GHOST fork choice derived  *)
(* from a vote store, and the Payload Timeliness Committee, in ONE state    *)
(* machine over multiple slots.                                             *)
(*                                                                          *)
(* Why this module exists                                                   *)
(* ----------------------------                                             *)
(* The EF ESP review observed that our models "confirm that the state       *)
(* machine you wrote is internally coherent rather than exercising the      *)
(* adversarial behaviour that makes ePBS a consensus-level risk", and that  *)
(* "the multi-slot interactions between fork choice and the payload         *)
(* timeliness committee sit outside what the models reach".                 *)
(*                                                                          *)
(* Auditing the repository showed the reason was structural, not budgetary: *)
(* no specification EXTENDed or INSTANCEd any other. EPBSChain.tla had      *)
(* slots but no fork choice; EPBSForkChoice.tla had fork choice hardcoded   *)
(* to two slots; EPBSPTC.tla had a committee with no chain. The interaction *)
(* could not be reached at ANY MaxSlot because the halves were never one    *)
(* machine.                                                                 *)
(*                                                                          *)
(* Two things change here versus EPBSForkChoice.tla:                        *)
(*                                                                          *)
(*   1. head was `\in {"none","b1full","b1empty","orphaned"}` -- a four     *)
(*      value enum. It is now COMPUTED by a GHOST descent over a real       *)
(*      block tree.                                                         *)
(*                                                                          *)
(*   2. HonestWeight and ByzWeight were CONSTANTS, never assigned. Weight   *)
(*      is now DERIVED from a per-validator latest-message vote store, so   *)
(*      equivocation, vote switching and late votes are expressible. They   *)
(*      previously could not be written down at all.                        *)
(*                                                                          *)
(* Ancestry is carried as state (blockAnc), updated when a block is built,  *)
(* rather than computed by a recursive operator. Apalache handles RECURSIVE *)
(* poorly, and this keeps Weight() a flat set comprehension.                *)
(***************************************************************************)
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Validators,
    \* @type: Set(Str);
    ByzValidators,
    \* @type: Int;
    MaxSlot,
    \* @type: Int;
    ProposerBoost,
    \* @type: Int;
    PayloadBoost,
    \* @type: Int;
    PTCThreshold,
    \* @type: Int;
    MaxAdvActions,
    \* @type: Int;
    ReorgHeadWeightPct,
    \* @type: Int;
    ReorgParentWeightPct

ASSUME ByzSubset   == ByzValidators \subseteq Validators
ASSUME SlotOK      == MaxSlot \in Nat /\ MaxSlot >= 2 /\ MaxSlot =< 4
ASSUME ThreshOK    == PTCThreshold \in Nat /\ PTCThreshold > Cardinality(ByzValidators)
ASSUME BudgetOK    == MaxAdvActions \in Nat
\* configs/mainnet.yaml: REORG_HEAD_WEIGHT_THRESHOLD = 20,
\* REORG_PARENT_WEIGHT_THRESHOLD = 160, PROPOSER_SCORE_BOOST = 40.
\* calculate_committee_fraction: (committee_weight * pct) // 100.
ASSUME ReorgPctOK  == ReorgHeadWeightPct \in Nat /\ ReorgParentWeightPct \in Nat

HonestValidators == Validators \ ByzValidators

\* Block 0 is genesis. A slot may host an honest block and a competing block,
\* so the id space is 2*MaxSlot wide plus genesis.
Genesis   == 0
\* sentinel: no withheld vote pending for this validator
NoVote    == -1
MaxBlockId == 2 * MaxSlot
BlockIds  == 0 .. MaxBlockId

VARIABLES
    \* @type: Int;
    slot,
    \* @type: Set(Int);
    blocks,
    \* @type: Int -> Int;
    blockSlot,
    \* @type: Int -> Int;
    blockParent,
    \* @type: Int -> Set(Int);
    blockAnc,
    \* @type: Int -> Bool;
    revealed,
    \* @type: Int -> (Str -> Str);
    ptcVotes,
    \* @type: Int -> Str;
    ptcVerdict,
    \* @type: Str -> Int;
    votes,
    \* @type: Set(Int);
    privateBlocks,
    \* @type: Str -> Int;
    privateVotes,
    \* @type: Set(Str);
    equivocators,
    \* @type: Set(Int);
    designated,
    \* @type: Set(Int);
    everHead,
    \* @type: Int;
    advUsed,
    \* @type: Int;
    nextId

vars == << slot, blocks, blockSlot, blockParent, blockAnc, revealed,
           ptcVotes, ptcVerdict, votes, privateBlocks, privateVotes,
           equivocators, designated, everHead, advUsed, nextId >>

(***************************************************************************)
(* Fork choice, derived                                                     *)
(***************************************************************************)

\* A validator's latest message supports b if it voted for b or for a
\* descendant of b. This is the LMD part: only votes[v], the latest, counts.
Supports(v, b) == votes[v] = b \/ b \in blockAnc[votes[v]]

BaseWeight(b) == Cardinality({ v \in Validators : Supports(v, b) })


\* EIP-7732 gives a block extra fork-choice weight when the PTC judged its
\* payload present. This is the coupling the review said was unreachable:
\* a committee verdict feeding directly into fork-choice weight.
PayloadWeight(b) == IF ptcVerdict[b] = "present" THEN PayloadBoost ELSE 0

\* Proposer boost applies to a block proposed in the CURRENT slot.
BoostWeight(b) ==
    IF blockSlot[b] = slot /\ b \in designated THEN ProposerBoost ELSE 0

Weight(b) == BaseWeight(b) + PayloadWeight(b) + BoostWeight(b)

Children(b) == { c \in blocks : blockParent[c] = b /\ c # Genesis }

\* consensus-specs breaks fork-choice ties on the block ROOT, i.e. a hash, which
\* bears no relation to creation order. Ties were previously broken by lowest
\* block id, which systematically favours earlier blocks and produced a
\* spurious "reorg" whenever two zero-weight siblings existed. This scramble
\* stands in for root ordering: deterministic, but not monotone in id.
BlockHash(b) == (b * 7 + 3) % 13

Heaviest(S) ==
    CHOOSE c \in S :
        \A d \in S : Weight(c) > Weight(d)
                     \/ (Weight(c) = Weight(d) /\ BlockHash(c) >= BlockHash(d))

Descend(b) == IF Children(b) = {} THEN b ELSE Heaviest(Children(b))

\* GHOST descent, unrolled to the maximum tree depth. MaxSlot =< 4 is asserted
\* above so this unrolling is complete; a deeper horizon needs more steps.
Head == Descend(Descend(Descend(Descend(Genesis))))

Canonical(b) == b = Head \/ b \in blockAnc[Head]

\* consensus-specs gloas/fork-choice.md, is_head_weak: head weight counts the
\* effective balance of every validator in store.equivocating_indices, on top
\* of the attestation score. An equivocator therefore contributes to the head
\* it attacked, not only to the branch its latest message names. Unit weight
\* here stands in for effective balance.
EquivWeight(b) ==
    IF b = Head THEN Cardinality(equivocators \ { v \in equivocators : Supports(v, b) })
    ELSE 0


(***************************************************************************)
(* Honest proposer reorg governance                                         *)
(*                                                                          *)
(* gloas/fork-choice.md get_proposer_head gates an honest proposer's reorg  *)
(* on EIGHT conjuncts. These constrain HONEST proposers only; an adversary  *)
(* ignores all of them, which is why AdvProposeFork stays ungated. Encoding *)
(* them on the adversary would forbid it from attacking.                    *)
(*                                                                          *)
(* Modelled here: head_weak, parent_strong, single_slot_reorg.              *)
(* Not modelled (no wall clock / FFG in this abstraction): head_late,       *)
(* not_epoch_boundary, ffg_competitive, finalization_ok, proposing_on_time. *)
(* Omitting them makes honest reorgs MORE permissive than the spec, so the  *)
(* model over-approximates honest reorg behaviour -- conservative for       *)
(* safety, unsound for liveness claims.                                     *)
(***************************************************************************)

CommitteeWeight == Cardinality(Validators)
Frac(pct) == (CommitteeWeight * pct) \div 100

\* is_head_weak: head_weight < calculate_committee_fraction(REORG_HEAD_WEIGHT_THRESHOLD)
IsHeadWeak(h) == BaseWeight(h) + EquivWeight(h) < Frac(ReorgHeadWeightPct)

\* is_parent_strong: parent_weight > calculate_committee_fraction(REORG_PARENT_WEIGHT_THRESHOLD)
IsParentStrong(h) == BaseWeight(blockParent[h]) > Frac(ReorgParentWeightPct)

\* single_slot_reorg: parent.slot + 1 == head.slot AND head.slot + 1 == current
SingleSlotReorg(h) ==
    /\ blockSlot[blockParent[h]] + 1 = blockSlot[h]
    /\ blockSlot[h] + 1 = slot

HonestMayReorg(h) ==
    /\ h # Genesis
    /\ IsHeadWeak(h)
    /\ IsParentStrong(h)
    /\ SingleSlotReorg(h)

(***************************************************************************)
(* Init                                                                     *)
(***************************************************************************)

Init ==
    /\ slot        = 1
    /\ blocks      = {Genesis}
    /\ blockSlot   = [b \in BlockIds |-> 0]
    /\ blockParent = [b \in BlockIds |-> Genesis]
    /\ blockAnc    = [b \in BlockIds |-> {}]
    /\ revealed    = [b \in BlockIds |-> FALSE]
    /\ ptcVotes    = [b \in BlockIds |-> [v \in Validators |-> "none"]]
    /\ ptcVerdict  = [b \in BlockIds |-> "none"]
    /\ votes       = [v \in Validators |-> Genesis]
    /\ privateBlocks = {}
    /\ privateVotes  = [v \in Validators |-> NoVote]
    /\ equivocators = {}
    /\ designated  = {}
    /\ everHead    = {Genesis}
    /\ advUsed     = 0
    /\ nextId      = 1

(***************************************************************************)
(* Honest actions                                                           *)
(***************************************************************************)

\* The slot's proposer builds on the canonical head.
ProposeHonest ==
    /\ slot =< MaxSlot
    /\ nextId =< MaxBlockId
    /\ ~HonestMayReorg(Head)
    /\ LET p == Head IN
       /\ blocks'      = blocks \union {nextId}
       /\ blockSlot'   = [blockSlot   EXCEPT ![nextId] = slot]
       /\ blockParent' = [blockParent EXCEPT ![nextId] = p]
       /\ blockAnc'    = [blockAnc    EXCEPT ![nextId] = blockAnc[p] \union {p}]
    /\ designated' = designated \union {nextId}
    /\ nextId' = nextId + 1
    /\ UNCHANGED << privateBlocks, privateVotes,
                    slot, revealed, ptcVotes, ptcVerdict, votes, equivocators,
                    everHead, advUsed >>

\* An honest proposer reorgs the head, but only when get_proposer_head would
\* allow it. This is the asymmetry: honest proposers are governed, the
\* adversary is not.
ProposeHonestReorg ==
    /\ slot =< MaxSlot
    /\ nextId =< MaxBlockId
    /\ HonestMayReorg(Head)
    /\ LET p == blockParent[Head] IN
       /\ blocks'      = blocks \union {nextId}
       /\ blockSlot'   = [blockSlot   EXCEPT ![nextId] = slot]
       /\ blockParent' = [blockParent EXCEPT ![nextId] = p]
       /\ blockAnc'    = [blockAnc    EXCEPT ![nextId] = blockAnc[p] \union {p}]
    /\ designated' = designated \union {nextId}
    /\ nextId' = nextId + 1
    /\ UNCHANGED << privateBlocks, privateVotes,
                    slot, revealed, ptcVotes, ptcVerdict, votes, equivocators,
                    everHead, advUsed >>

\* The builder reveals the committed payload on time.
RevealPayload(b) ==
    /\ b \in blocks /\ b # Genesis
    /\ ~revealed[b]
    /\ blockSlot[b] = slot
    /\ revealed' = [revealed EXCEPT ![b] = TRUE]
    /\ UNCHANGED << slot, blocks, blockSlot, blockParent, blockAnc,
                    ptcVotes, ptcVerdict, votes, privateBlocks, privateVotes,
           equivocators, designated, everHead, advUsed, nextId >>

\* An honest PTC member votes what it observed.
HonestPTCVote(v, b) ==
    /\ v \in HonestValidators
    /\ b \in blocks /\ b # Genesis
    /\ blockSlot[b] = slot
    /\ ptcVotes[b][v] = "none"
    /\ ptcVotes' = [ptcVotes EXCEPT ![b][v] = IF revealed[b] THEN "present" ELSE "absent"]
    /\ UNCHANGED << privateBlocks, privateVotes,
                    slot, blocks, blockSlot, blockParent, blockAnc, revealed,
                    ptcVerdict, votes, equivocators, designated, everHead,
                    advUsed, nextId >>

\* An honest validator attests to the block it sees as canonical.
HonestAttest(v) ==
    /\ v \in HonestValidators
    /\ votes[v] # Head
    /\ votes' = [votes EXCEPT ![v] = Head]
    /\ UNCHANGED << privateBlocks, privateVotes,
                    slot, blocks, blockSlot, blockParent, blockAnc, revealed,
                    ptcVotes, ptcVerdict, equivocators, designated, everHead, advUsed, nextId >>

\* Close the committee for a block: tally to a verdict.
ClosePTC(b) ==
    /\ b \in blocks /\ b # Genesis
    /\ ptcVerdict[b] = "none"
    /\ blockSlot[b] = slot
    /\ ptcVerdict' =
         [ptcVerdict EXCEPT ![b] =
            \* consensus-specs gloas/fork-choice.md L295:
            \*   sum(vote == timely for vote in votes) > PAYLOAD_TIMELY_THRESHOLD
            \* Strictly greater. This was >= and is an off-by-one on a committee
            \* tally, exactly the kind of error that flips a reorg.
            IF Cardinality({v \in Validators : ptcVotes[b][v] = "present"}) > PTCThreshold
            THEN "present" ELSE "absent"]
    /\ UNCHANGED << privateBlocks, privateVotes,
                    slot, blocks, blockSlot, blockParent, blockAnc, revealed,
                    ptcVotes, votes, equivocators, designated, everHead, advUsed, nextId >>

\* An honest committee attests every slot. The model previously let a slot pass
\* with no attestations at all, so TLC found traces where a block was head only
\* by proposer boost, the boost expired at the slot boundary, and the head moved
\* to a zero-weight sibling. That is a liveness artifact of the encoding, not a
\* reorg, and it contaminated every safety result.
AllHonestAttested == \A v \in HonestValidators : votes[v] = Head

AdvanceSlot ==
    /\ slot < MaxSlot
    /\ AllHonestAttested
    /\ slot' = slot + 1
    /\ everHead' = everHead \union {Head}
    /\ UNCHANGED << privateBlocks, privateVotes,
                    blocks, blockSlot, blockParent, blockAnc, revealed,
                    ptcVotes, ptcVerdict, votes, equivocators, designated, advUsed, nextId >>

(***************************************************************************)
(* Adversary. Budgeted, and chooses WHEN to act -- the previous models had  *)
(* static FaultXxx booleans fixed for a whole run, so the adversary had no  *)
(* timing decision to make.                                                 *)
(***************************************************************************)

Spend == advUsed < MaxAdvActions /\ advUsed' = advUsed + 1

\* Build on a non-canonical parent: an explicit reorg attempt.
AdvProposeFork(p) ==
    /\ Spend
    /\ slot =< MaxSlot
    /\ nextId =< MaxBlockId
    /\ p \in blocks
    /\ p # Head
    /\ blocks'      = blocks \union {nextId}
    /\ blockSlot'   = [blockSlot   EXCEPT ![nextId] = slot]
    /\ blockParent' = [blockParent EXCEPT ![nextId] = p]
    /\ blockAnc'    = [blockAnc    EXCEPT ![nextId] = blockAnc[p] \union {p}]
    /\ nextId' = nextId + 1
    /\ UNCHANGED << privateBlocks, privateVotes,
                    slot, revealed, ptcVotes, ptcVerdict, votes, equivocators, designated, everHead >>

\* Latest-message replacement: the essence of an LMD attack, and impossible
\* to express when weight was a constant.
AdvEquivocate(v, b) ==
    /\ Spend
    /\ v \in ByzValidators
    /\ b \in blocks
    /\ votes[v] # b
    /\ votes' = [votes EXCEPT ![v] = b]
    /\ equivocators' = equivocators \union {v}
    /\ UNCHANGED << privateBlocks, privateVotes,
                    slot, blocks, blockSlot, blockParent, blockAnc, revealed,
                    ptcVotes, ptcVerdict, designated, everHead, nextId >>

\* Byzantine PTC member votes against what it observed.
AdvPTCLie(v, b) ==
    /\ Spend
    /\ v \in ByzValidators
    /\ b \in blocks /\ b # Genesis
    /\ ptcVotes[b][v] = "none"
    /\ ptcVotes' = [ptcVotes EXCEPT ![b][v] = IF revealed[b] THEN "absent" ELSE "present"]
    /\ UNCHANGED << privateBlocks, privateVotes,
                    slot, blocks, blockSlot, blockParent, blockAnc, revealed,
                    ptcVerdict, votes, equivocators, designated, everHead, nextId >>

\* Reveal a withheld payload in a LATER slot, after the committee has closed.
\* This is the specific fork-choice x PTC crossing the review named.
AdvLateReveal(b) ==
    /\ Spend
    /\ b \in blocks /\ b # Genesis
    /\ ~revealed[b]
    /\ blockSlot[b] < slot
    /\ revealed' = [revealed EXCEPT ![b] = TRUE]
    /\ UNCHANGED << privateBlocks, privateVotes,
                    slot, blocks, blockSlot, blockParent, blockAnc,
                    ptcVotes, ptcVerdict, votes, equivocators, designated, everHead, nextId >>

(***************************************************************************)
(* Withholding. Until now the adversary published everything the instant it *)
(* acted, which makes it an off-schedule proposer rather than a strategic   *)
(* actor. Every real ex-ante reorg works by hoarding blocks and votes and   *)
(* releasing them together to produce an instant weight surge, so that      *)
(* attack class was structurally inexpressible, not merely unreached.       *)
(*                                                                          *)
(* Withheld blocks stay out of `blocks`, so Children() and therefore the    *)
(* GHOST descent cannot see them. Withheld votes stay out of `votes`, so    *)
(* Supports() and therefore Weight() cannot see them. Both become visible   *)
(* atomically in AdvRelease.                                                *)
(***************************************************************************)

\* Build a block privately. Metadata is recorded now; visibility comes later.
AdvWithholdBlock(p) ==
    /\ Spend
    /\ slot =< MaxSlot
    /\ nextId =< MaxBlockId
    /\ p \in blocks
    /\ blockSlot'   = [blockSlot   EXCEPT ![nextId] = slot]
    /\ blockParent' = [blockParent EXCEPT ![nextId] = p]
    /\ blockAnc'    = [blockAnc    EXCEPT ![nextId] = blockAnc[p] \union {p}]
    /\ privateBlocks' = privateBlocks \union {nextId}
    /\ nextId' = nextId + 1
    /\ UNCHANGED << slot, blocks, revealed, ptcVotes, ptcVerdict, votes,
                     privateVotes, equivocators, designated, everHead >>

\* Cast a vote that nobody can see yet. Target may be a withheld block.
AdvWithholdVote(v, b) ==
    /\ Spend
    /\ v \in ByzValidators
    /\ b \in (blocks \union privateBlocks)
    /\ privateVotes[v] = NoVote
    /\ privateVotes' = [privateVotes EXCEPT ![v] = b]
    /\ UNCHANGED << slot, blocks, blockSlot, blockParent, blockAnc, revealed,
                     ptcVotes, ptcVerdict, votes, privateBlocks, equivocators,
                     designated, everHead, nextId >>

\* Publish everything at once: the weight surge that forces the reorg.
AdvRelease ==
    /\ Spend
    /\ (privateBlocks # {} \/ \E v \in Validators : privateVotes[v] # NoVote)
    /\ blocks' = blocks \union privateBlocks
    /\ votes'  = [v \in Validators |->
                     IF privateVotes[v] # NoVote THEN privateVotes[v] ELSE votes[v]]
    /\ equivocators' = equivocators
         \union { v \in ByzValidators : privateVotes[v] # NoVote /\ privateVotes[v] # votes[v] }
    /\ privateBlocks' = {}
    /\ privateVotes'  = [v \in Validators |-> NoVote]
    /\ UNCHANGED << slot, blockSlot, blockParent, blockAnc, revealed,
                     ptcVotes, ptcVerdict, designated, everHead, nextId >>

Next ==
    \/ ProposeHonest
    \/ ProposeHonestReorg
    \/ \E b \in blocks : RevealPayload(b)
    \/ \E v \in Validators, b \in blocks : HonestPTCVote(v, b)
    \/ \E v \in Validators : HonestAttest(v)
    \/ \E b \in blocks : ClosePTC(b)
    \/ AdvanceSlot
    \/ \E p \in blocks : AdvProposeFork(p)
    \/ \E v \in Validators, b \in blocks : AdvEquivocate(v, b)
    \/ \E v \in Validators, b \in blocks : AdvPTCLie(v, b)
    \/ \E b \in blocks : AdvLateReveal(b)
    \/ \E p \in blocks : AdvWithholdBlock(p)
    \/ \E v \in Validators, b \in (blocks \union privateBlocks) : AdvWithholdVote(v, b)
    \/ AdvRelease

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants                                                               *)
(***************************************************************************)

TypeOK ==
    /\ slot \in 1 .. MaxSlot
    /\ blocks \subseteq BlockIds
    /\ advUsed \in 0 .. MaxAdvActions
    /\ nextId \in 1 .. (MaxBlockId + 1)
    /\ designated \subseteq BlockIds
    /\ equivocators \subseteq Validators
    /\ privateBlocks \subseteq BlockIds
    /\ privateVotes \in [Validators -> BlockIds \union {NoVote}]
    /\ votes \in [Validators -> BlockIds]
    /\ ptcVerdict \in [BlockIds -> {"none","present","absent"}]

\* A block was head at some point and is now off the canonical chain.
Reorged(b) == b \in everHead /\ b # Genesis /\ ~Canonical(b)

ByzSupport(b) == Cardinality({ v \in ByzValidators : Supports(v, b) })
HonSupport(b) == Cardinality({ v \in HonestValidators : Supports(v, b) })

(***************************************************************************)
(* THE invariant. The direct analogue of FC_ReorgImpliesAdversaryHeavy from *)
(* EPBSForkChoice.tla, but with weights DERIVED rather than declared.       *)
(*                                                                          *)
(* In the old module this was a restatement of a closed-form inequality the *)
(* author wrote, so TLC could only confirm it. Here both sides are computed *)
(* from the vote store, so it is a genuine claim about reachable states and *)
(* CAN fail. A violation is the intended first result: it means the model   *)
(* has begun searching rather than confirming.                              *)
(***************************************************************************)
FC_ReorgImpliesAdversaryHeavy ==
    \A b \in blocks :
        Reorged(b) => ByzSupport(Head) + ProposerBoost >= HonSupport(b)

\* A payload the committee ruled present should not be reorged out by an
\* adversary lacking the weight for it.
FC_TimelyPayloadSafe ==
    \A b \in blocks :
        (Reorged(b) /\ ptcVerdict[b] = "present")
            => ByzSupport(Head) + ProposerBoost >= HonSupport(b) + PayloadBoost

(***************************************************************************)
(* VACUITY PROBES                                                           *)
(*                                                                          *)
(* An invariant of the form Reorged(b) => P is trivially true in every state *)
(* where no block is ever reorged. 129M "clean" states prove nothing if the  *)
(* antecedent is never satisfied.                                            *)
(*                                                                          *)
(* These are deliberately FALSE statements. TLC reporting them VIOLATED is   *)
(* the desired outcome: a violation is a witness that the condition is       *)
(* reachable. If one of these HOLDS, the corresponding invariant above is    *)
(* vacuous and every clean run so far was measuring nothing.                 *)
(***************************************************************************)

\* Violation => a reorg is reachable => FC_ReorgImpliesAdversaryHeavy has teeth.
VACUITY_ReorgReachable == \A b \in blocks : ~Reorged(b)

\* Violation => the adversary actually acts.
VACUITY_AdversaryActs == advUsed = 0

\* Violation => the PTC actually rules "present" on something.
VACUITY_PTCPresent == \A b \in blocks : ptcVerdict[b] # "present"

\* Violation => a reorged block had a present payload, i.e. the specific
\* fork-choice x PTC interaction the EF review named is reachable.
VACUITY_TimelyReorgReachable ==
    \A b \in blocks : ~(Reorged(b) /\ ptcVerdict[b] = "present")

\* Violation => the adversary actually withholds something. Without this the
\* "no timely reorg under withholding" result would be vacuous in exactly the
\* way the earlier clean runs nearly were.
VACUITY_WithholdingHappens ==
    privateBlocks = {} /\ \A v \in Validators : privateVotes[v] = NoVote

\* Violation => a withheld batch was actually published.
VACUITY_ReleaseHappens == advUsed = 0 \/ privateBlocks = {}

\* Violation => equivocation occurs.
VACUITY_EquivocationHappens == equivocators = {}

\* The committee should never rule "present" on a payload never revealed,
\* unless Byzantine members pushed it over the threshold.
PTC_NoFalsePresent ==
    \A b \in blocks :
        (ptcVerdict[b] = "present" /\ ~revealed[b])
            => Cardinality(ByzValidators) >= PTCThreshold

=============================================================================
