(** * Chain conservation, for all chain lengths.

    specs/EPBSChain.tla checks that value is conserved across a bounded chain of
    slots with queued, asynchronously-draining withdrawals (INV_Conservation),
    at a finite length. This development lifts conservation to a theorem for ANY
    sequence of slot outcomes and drains, of any length.

    The chain is a list of events. Each slot resolves to a full or empty block
    (the builder is debited by the bid and the value is escrowed), a reorged or
    skipped block (no change), or a withdrawal drain (the escrow is moved to the
    proposer). We prove the total across the proposer balance, the builder
    balance, and the escrow is invariant under every event, hence across the
    whole chain. Checked by coqc, no axioms. *)

Require Import ZArith.
Require Import Lia.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

Record cstate := mkC { prop : Z; build : Z; owed : Z }.

Definition ctotal (s : cstate) : Z := prop s + build s + owed s.

Inductive event :=
  | EFull  (v : Z)   (* canonical block, payload revealed: debit builder, escrow *)
  | EEmpty (v : Z)   (* canonical block, payload withheld: debit builder, escrow *)
  | EReorged         (* block not canonical: no change *)
  | ESkipped         (* no builder included: no change *)
  | EDrain (v : Z).  (* process a queued withdrawal: escrow to proposer *)

Definition cstep (s : cstate) (e : event) : cstate :=
  match e with
  | EFull v  => mkC (prop s) (build s - v) (owed s + v)
  | EEmpty v => mkC (prop s) (build s - v) (owed s + v)
  | EReorged => s
  | ESkipped => s
  | EDrain v => mkC (prop s + v) (build s) (owed s - v)
  end.

(** Every event conserves the total. *)
Lemma cstep_conserves : forall s e, ctotal (cstep s e) = ctotal s.
Proof. intros s e; destruct e; unfold ctotal, cstep; simpl; lia. Qed.

(** Therefore the whole chain conserves the total, for any events and length. *)
Theorem run_conserves : forall (es : list event) (s : cstate),
  ctotal (fold_left cstep es s) = ctotal s.
Proof.
  induction es as [| e es' IH]; intros s; simpl.
  - reflexivity.
  - rewrite IH. apply cstep_conserves.
Qed.

(** When every queued withdrawal has drained (escrow is zero), the proposer and
    builder balances account for exactly the starting total: nothing was minted
    or lost along the way. This is the all-lengths counterpart of the model's
    drained-liveness settlement. *)
Corollary drained_settles : forall (es : list event) (s : cstate),
  owed (fold_left cstep es s) = 0 ->
  prop (fold_left cstep es s) + build (fold_left cstep es s) = ctotal s.
Proof.
  intros es s Hd.
  pose proof (run_conserves es s) as Hc.
  unfold ctotal in *. lia.
Qed.
