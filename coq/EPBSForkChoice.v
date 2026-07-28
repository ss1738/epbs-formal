(** * A machine-checked proof of the ePBS reorg threshold, for all weights.

    [../specs/EPBSForkChoice.tla] measures the reorg threshold on two finite
    parameter sets: a safe one where a timely payload is never reorged, and an
    unsafe one where TLC returns a reorg counterexample. This development lifts
    that result to a theorem true for ALL non-negative weights.

    The fork choice is the accumulated-weight comparison from the TLA+ model:

      weight(B1)    = HonestWeight + (payload timely ? PayloadBoost : 0)
      weight(reorg) = adversary reorged ? (ByzWeight + ProposerBoost) : 0
      B1 canonical  iff weight(reorg) <= weight(B1)     (ties favor B1)

    Main results, all checked by [coqc] with no axioms or admitted goals:

      - [timely_payload_safe]     : above the threshold, a timely payload is
                                    canonical against ANY adversary strategy.
      - [reorg_below_threshold]   : below the threshold, the worst-case
                                    adversary reorgs the timely payload.
      - [reorg_threshold_iff]     : the exact characterization. For the
                                    worst-case adversary, B1 is canonical iff
                                    HonestWeight + PayloadBoost >= ByzWeight +
                                    ProposerBoost.

    The payment guarantees on both sides of the threshold (a canonical block
    pays the proposer, an orphaned block refunds the builder, value is
    conserved) are proved for all sizes in [EPBSPayment.v]; a reorg costs the
    payload's liveness, not the builder's funds. This file is standalone and
    depends only on the standard library. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Section ForkChoice.

  (** Fork-choice weights. All non-negative. *)
  Variables HonestWeight ByzWeight ProposerBoost PayloadBoost : Z.
  Hypothesis Hhw  : 0 <= HonestWeight.
  Hypothesis Hbw  : 0 <= ByzWeight.
  Hypothesis Hprb : 0 <= ProposerBoost.
  Hypothesis Hpb  : 0 <= PayloadBoost.

  Definition weightB1 (present : bool) : Z :=
    HonestWeight + (if present then PayloadBoost else 0).

  Definition weightReorg (reorg : bool) : Z :=
    if reorg then ByzWeight + ProposerBoost else 0.

  (** B1 stays canonical iff the reorg branch does not out-weight it. *)
  Definition b1_canonical (present reorg : bool) : bool :=
    Z.leb (weightReorg reorg) (weightB1 present).

  (** The safety threshold. *)
  Definition HonestMajoritySafe : Prop :=
    HonestWeight + PayloadBoost >= ByzWeight + ProposerBoost.

  (** Above the threshold, a timely payload is canonical no matter what slot 2's
      proposer does. *)
  Theorem timely_payload_safe :
    HonestMajoritySafe -> forall reorg, b1_canonical true reorg = true.
  Proof.
    unfold HonestMajoritySafe, b1_canonical, weightB1, weightReorg.
    intros H reorg. apply Z.leb_le. destruct reorg; lia.
  Qed.

  (** The exact threshold, for the worst-case adversary (reorg attempted
      against a timely payload). *)
  Theorem reorg_threshold_iff :
    b1_canonical true true = true <-> HonestMajoritySafe.
  Proof.
    unfold b1_canonical, weightB1, weightReorg, HonestMajoritySafe.
    rewrite Z.leb_le. split; intro; lia.
  Qed.

  (** Below the threshold, the worst-case adversary reorgs the timely payload.
      This shows the threshold is tight, not merely sufficient. *)
  Theorem reorg_below_threshold :
    ~ HonestMajoritySafe -> b1_canonical true true = false.
  Proof.
    unfold HonestMajoritySafe, b1_canonical, weightB1, weightReorg.
    intro H. apply Z.leb_gt. lia.
  Qed.

  (** Corollary: an adversary that reorgs a timely payload must strictly
      out-weigh the honest committee plus the payload boost. This is the
      formal counterpart of EIP-7732's claim that reorging a builder's payload
      requires a heavy adversary. *)
  Corollary reorg_implies_adversary_heavy :
    b1_canonical true true = false ->
    ByzWeight + ProposerBoost > HonestWeight + PayloadBoost.
  Proof.
    unfold b1_canonical, weightB1, weightReorg.
    intro H. apply Z.leb_gt in H. lia.
  Qed.

End ForkChoice.
