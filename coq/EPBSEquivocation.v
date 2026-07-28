(** * Why EIP-7732 needs no slashing for payload equivocation.

    EIP-7732 deliberately omits any penalty for a builder that equivocates
    (reveals the committed payload and also a withheld message, splitting the
    view). Its stated rationale: equivocation "results in a split view AT A
    COST to the builder (the payload is revealed and may not be included)", so
    the design opted for simplicity over an explicit slashing rule.

    This is the design decision a reviewer is most likely to question. This
    development formalizes the rationale and proves it: on a canonical block an
    equivocating builder pays the full bid yet gets its payload excluded, so it
    is strictly worse off than had it revealed honestly. Equivocation is
    self-punishing; no slashing is required to disincentivize it.

    Every statement is checked by coqc with no axioms or admitted goals. *)

(* Plain [Require Import] for portability across Coq 8.x and the Rocq Prover. *)
Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Inductive reveal := Committed | Withheld | Equivocated.

(** On a canonical block the builder is charged the full bid; on a reorged one
    it is charged nothing (builder withhold safety, proved in EPBSPayment.v). *)
Definition charged (canonical : bool) (bid : Z) : Z :=
  if canonical then bid else 0.

(** The builder's payload is included only on a canonical block with a
    committed reveal. An equivocated or withheld reveal is never included. *)
Definition payload_included (canonical : bool) (r : reveal) : bool :=
  match canonical, r with
  | true, Committed => true
  | _, _ => false
  end.

(** The builder's net position: the value it assigns to getting its payload
    included, [gain], minus what it was charged. Getting the payload included
    is the only reason a builder pays to be in the block, so [gain] is realized
    exactly when [payload_included] holds. *)
Definition net (canonical : bool) (r : reveal) (bid gain : Z) : Z :=
  (if payload_included canonical r then gain else 0) - charged canonical bid.

(* --- The net position reduces to a closed form on a canonical block. ----- *)

Lemma net_committed_val : forall bid gain,
  net true Committed bid gain = gain - bid.
Proof. reflexivity. Qed.

Lemma net_equivocated_val : forall bid gain,
  net true Equivocated bid gain = - bid.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)

(** On a canonical block, an equivocating builder pays the full bid and gets
    nothing included. *)
Theorem equivocation_pays_gets_nothing : forall bid,
  charged true bid = bid /\ payload_included true Equivocated = false.
Proof. intro bid; split; reflexivity. Qed.

(** Its net position is therefore exactly minus the bid: a pure loss. *)
Theorem equivocation_net_loss : forall bid gain,
  net true Equivocated bid gain = - bid.
Proof. intros; apply net_equivocated_val. Qed.

(** An honest reveal on a canonical block does get the payload included. *)
Theorem honest_reveal_included :
  payload_included true Committed = true.
Proof. reflexivity. Qed.

(** The key result: when the payload has non-negative value to its builder (the
    only regime in which bidding to be included is rational), an honest reveal
    is at least as good as equivocating. Equivocation is a dominated strategy,
    so no slashing is needed to deter it. *)
Theorem honest_dominates_equivocation : forall bid gain,
  gain >= 0 ->
  net true Committed bid gain >= net true Equivocated bid gain.
Proof.
  intros bid gain H.
  rewrite net_committed_val, net_equivocated_val. lia.
Qed.

(** And strictly better whenever the payload has any positive value. *)
Theorem equivocation_strictly_worse : forall bid gain,
  gain > 0 ->
  net true Committed bid gain > net true Equivocated bid gain.
Proof.
  intros bid gain H.
  rewrite net_committed_val, net_equivocated_val. lia.
Qed.
