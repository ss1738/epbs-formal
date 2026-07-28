(** * A machine-checked proof of the EIP-7732 payment core.

    The TLA+ models in this repository check the ePBS safety properties on
    small finite instances with TLC. This Coq development proves the payment
    core for ALL bid values, ALL balances, and ANY number of uninvolved
    builders. A finite model check gives confidence on small instances; a
    proof gives a guarantee for every size.

    We model the EIP-7732 payment lifecycle for one included bid:

      - at inclusion, the committed value [v] is debited from the builder's
        balance into a pending escrow (BuilderPendingPayment);
      - at settlement, if the beacon block is canonical the escrow is paid to
        the proposer (BuilderPendingWithdrawal); if it is reorged the escrow is
        refunded to the builder.

    We prove: value conservation (including over an arbitrary number of other
    builders), the two payment guarantees G1 and G3, no dangling escrow, and
    payload commitment binding. Every theorem below is checked by [coqc]. *)

(* Plain [Require Import] for portability across Coq 8.x and the Rocq Prover
   9.x. On 9.x this emits a harmless deprecation warning; it does not affect
   the proofs. *)
Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

(** The choices the protocol and the adversary make. *)
Inductive reveal  := Committed | Withheld | Equivocated.
Inductive fate    := Canonical | Reorged.
Inductive payload := PNone | PCommitted.

(** The part of the beacon state the payment touches. *)
Record state := mkState {
  bprop  : Z;   (* proposer balance *)
  bbuild : Z;   (* the included builder's balance *)
  pend   : Z    (* pending-payment escrow *)
}.

Definition total (s : state) : Z := bprop s + bbuild s + pend s.

(** Inclusion: debit the builder by [v], escrow [v]. *)
Definition after_inclusion (bp bb v : Z) : state :=
  mkState bp (bb - v) v.

(** Settlement, decided by the beacon block's fate. *)
Definition settle (s : state) (f : fate) : state :=
  match f with
  | Canonical => mkState (bprop s + pend s) (bbuild s) 0
  | Reorged   => mkState (bprop s) (bbuild s + pend s) 0
  end.

(** The canonical payload: committed only on a canonical block with a
    committed, timely reveal. *)
Definition resolve_payload (f : fate) (r : reveal) (present : bool) : payload :=
  match f, r, present with
  | Canonical, Committed, true => PCommitted
  | _, _, _ => PNone
  end.

(* ---------------------------------------------------------------------- *)
(** ** Conservation *)

Lemma settle_conserves : forall s f, total (settle s f) = total s.
Proof. intros s f; destruct f; unfold total, settle; simpl; lia. Qed.

Lemma inclusion_total : forall bp bb v,
  total (after_inclusion bp bb v) = bp + bb.
Proof. intros; unfold total, after_inclusion; simpl; lia. Qed.

(** Conservation over the whole system, including [others] = the summed
    balances of any number of uninvolved builders, who are untouched. This is
    the "any number of builders" generalization the finite TLC run cannot give. *)
Definition gtotal (others : Z) (s : state) : Z := others + total s.

Lemma settle_conserves_global : forall others s f,
  gtotal others (settle s f) = gtotal others s.
Proof. intros; unfold gtotal; rewrite settle_conserves; reflexivity. Qed.

(** The full lifecycle (inclusion then settlement) conserves the global total,
    for any fate, any value, any balances, and any number of other builders. *)
Theorem lifecycle_conserves : forall others bp bb v f,
  gtotal others (settle (after_inclusion bp bb v) f) = others + bp + bb.
Proof.
  intros others bp bb v f.
  rewrite settle_conserves_global.
  unfold gtotal; rewrite inclusion_total; lia.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** The payment guarantees, for all values *)

(** G1: proposer unconditional payment. A canonical block pays the proposer
    exactly the committed value (proposer starting from 0), whatever the
    builder did with the payload. *)
Theorem G1_proposer_paid : forall bb v,
  bprop (settle (after_inclusion 0 bb v) Canonical) = v.
Proof. intros; simpl; lia. Qed.

(** G3: builder withhold safety. A reorged block refunds the builder to its
    starting balance and pays the proposer nothing. *)
Theorem G3_withhold_safe : forall bb v,
  bprop  (settle (after_inclusion 0 bb v) Reorged) = 0
  /\ bbuild (settle (after_inclusion 0 bb v) Reorged) = bb.
Proof. intros; simpl; split; lia. Qed.

(** No escrow is left dangling after settlement, for any state and fate. *)
Theorem no_dangling_payment : forall s f, pend (settle s f) = 0.
Proof. intros s f; destruct f; simpl; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Commitment binding *)

(** The canonical payload is only ever the committed one. *)
Theorem commitment_binding : forall f r present,
  resolve_payload f r present = PCommitted -> r = Committed.
Proof.
  intros f r present H; destruct f, r, present; simpl in H;
    try discriminate; reflexivity.
Qed.

(** An equivocated reveal never yields a canonical payload, for any fate. *)
Theorem equivocation_not_canonical : forall f present,
  resolve_payload f Equivocated present <> PCommitted.
Proof. intros f present; destruct f, present; simpl; discriminate. Qed.

(** A withheld reveal never yields a canonical payload either. *)
Theorem withhold_not_canonical : forall f present,
  resolve_payload f Withheld present <> PCommitted.
Proof. intros f present; destruct f, present; simpl; discriminate. Qed.
