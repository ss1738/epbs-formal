(** * Gloas weight-quorum payment, for all committee sizes.

    specs/EPBSWeightPayment.tla checks the Gloas builder-payment settlement (a
    payment settles only when accumulated attestation weight reaches a quorum)
    at finite instances. This development lifts its guarantees to a theorem for
    ALL committee sizes, under the honest-majority quorum B < Q <= H.

    Setup, matching the model:
      - [H] honest attesters, who attest weight iff the block is canonical;
      - [B] Byzantine attesters, contributing between 0 and [B] weight;
      - quorum [Q] with [B < Q <= H]: a Byzantine minority alone cannot reach it,
        and the honest attesters alone can.

    The payment settles to the proposer iff the weight reaches the quorum. We
    prove the G1/G3-style guarantees the finite model checks now hold for every
    committee size and every Byzantine behaviour. Checked by coqc, no axioms. *)

Require Import Arith.
Require Import ZArith.
Require Import Lia.

Section WeightPayment.

  Variables H B Q : nat.
  Hypothesis Byz_below_Q : B < Q.        (* Byzantine minority cannot reach quorum *)
  Hypothesis Q_below_H   : Q <= H.        (* honest attesters alone can reach it *)

  Variables StartBal Value : Z.
  Hypothesis Value_pos   : (0 < Value)%Z.
  Hypothesis Value_fits  : (Value <= StartBal)%Z.

  (* Attestation weight and whether the payment settles. *)
  Definition weight (canonical : bool) (byz : nat) : nat :=
    (if canonical then H else 0) + byz.

  Definition paid (canonical : bool) (byz : nat) : bool :=
    Nat.leb Q (weight canonical byz).

  (** The payment settles exactly when the block is canonical: honest weight
      reaches the quorum, a Byzantine minority alone cannot. *)
  Lemma paid_iff_canonical : forall canonical byz,
    (byz <= B)%nat -> paid canonical byz = canonical.
  Proof.
    intros canonical byz Hb. unfold paid, weight.
    destruct canonical.
    - apply Nat.leb_le. lia.
    - apply Nat.leb_gt. lia.
  Qed.

  (* Balances after settlement. *)
  Definition proposer_bal (canonical : bool) (byz : nat) : Z :=
    if paid canonical byz then Value else 0%Z.
  Definition builder_bal (canonical : bool) (byz : nat) : Z :=
    if paid canonical byz then (StartBal - Value)%Z else StartBal.

  (** A Byzantine minority alone can never force a payment on a non-canonical
      block. *)
  Theorem no_forced_pay : forall byz,
    (byz <= B)%nat -> paid false byz = false.
  Proof. intros byz Hb. rewrite paid_iff_canonical; [reflexivity | exact Hb]. Qed.

  (** A canonical block pays the proposer exactly the bid value (G1). *)
  Theorem canonical_pays : forall byz,
    (byz <= B)%nat -> proposer_bal true byz = Value.
  Proof.
    intros byz Hb. unfold proposer_bal.
    rewrite paid_iff_canonical; [reflexivity | exact Hb].
  Qed.

  (** A non-canonical block charges no one: builder keeps its balance, proposer
      is paid nothing (G3). *)
  Theorem noncanonical_refunds : forall byz,
    (byz <= B)%nat ->
    proposer_bal false byz = 0%Z /\ builder_bal false byz = StartBal.
  Proof.
    intros byz Hb. unfold proposer_bal, builder_bal.
    rewrite (paid_iff_canonical false byz Hb). simpl. split; reflexivity.
  Qed.

  (** Value is conserved whatever the outcome. *)
  Theorem conservation : forall canonical byz,
    (proposer_bal canonical byz + builder_bal canonical byz)%Z = StartBal.
  Proof.
    intros canonical byz. unfold proposer_bal, builder_bal.
    destruct (paid canonical byz); lia.
  Qed.

End WeightPayment.
