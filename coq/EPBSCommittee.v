(** * PTC tally correctness, for all committee sizes.

    specs/EPBSPTC.tla checks that the Payload-Timeliness Committee tally always
    equals the truth (INV_Correct) at finite instances (3 and 5 attesters). This
    development lifts that to a theorem for ALL committee sizes.

    Setup, matching the model's ThresholdOK assumption:
      - [H] honest attesters, all voting the truth: "present" iff the payload
        was timely, so the honest present-count is [H] when timely and 0 otherwise;
      - [B] Byzantine attesters voting arbitrarily, contributing between 0 and [B]
        present votes;
      - threshold [T] with [B < T <= H]: a Byzantine minority alone cannot reach
        the threshold, and the honest members alone can.

    The payload is deemed present iff the present-count reaches [T]. We prove the
    tally equals the truth for every [H], [B], [T] satisfying the assumption and
    every Byzantine behaviour. Checked by coqc, no axioms. *)

(* Plain [Require Import] for portability across Coq 8.x and the Rocq Prover. *)
Require Import Arith.
Require Import Lia.

Section Committee.

  Variables H B T : nat.
  Hypothesis Byz_below_T : B < T.        (* Byzantine minority cannot force present *)
  Hypothesis T_below_H   : T <= H.        (* honest majority can reach the threshold *)

  (* Present-count and the tally, given the truth and the Byzantine present votes. *)
  Definition present_count (timely : bool) (byz_present : nat) : nat :=
    (if timely then H else 0) + byz_present.

  Definition tally (timely : bool) (byz_present : nat) : bool :=
    T <=? present_count timely byz_present.

  (** The tally always equals the truth, for any Byzantine present-vote count
      within its budget [B]. *)
  Theorem tally_correct : forall timely byz_present,
    byz_present <= B ->
    tally timely byz_present = timely.
  Proof.
    intros timely byz_present Hbp.
    unfold tally, present_count.
    destruct timely.
    - rewrite Nat.leb_le. lia.
    - rewrite Nat.leb_gt. lia.
  Qed.

  (** No false present: a present tally implies the payload really was timely. *)
  Corollary no_false_present : forall timely byz_present,
    byz_present <= B ->
    tally timely byz_present = true -> timely = true.
  Proof.
    intros timely byz_present Hbp Ht.
    rewrite (tally_correct timely byz_present Hbp) in Ht. exact Ht.
  Qed.

  (** No false absent: a timely payload is always tallied present. *)
  Corollary no_false_absent : forall byz_present,
    byz_present <= B ->
    tally true byz_present = true.
  Proof.
    intros byz_present Hbp.
    rewrite (tally_correct true byz_present Hbp). reflexivity.
  Qed.

End Committee.
