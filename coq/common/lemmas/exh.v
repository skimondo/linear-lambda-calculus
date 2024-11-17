(* =================================================== *)
(* Properties of exhaustedness *)
(* =================================================== *)

Require Import Coq.Program.Equality.
Require Import Coq.Arith.PeanoNat.

Require Import common.defs.obj.
Require Import common.defs.ctx.
Require Import common.defs.tp.
Require Import common.defs.lin_aff.

(* --------------------------------------------------- *)
(* Pruning lemmas *)
(* --------------------------------------------------- *)

(* "Prune" LF context to remove dependencies *)

(* Prune exh lemma *)
Lemma prune_exh :
  forall {N : nat} (delta : lctx N) (x : obj) (A : tp) (alpha : mult),
    exh (cons N delta x A alpha) ->
    exh delta.
Proof.
  intros N delta x A alpha H.
  dependent destruction H.
  exact H.
Qed.

Lemma exh_lookup :
  forall {N : nat} (delta delta' : lctx N) (n : nat)
         (X Y : obj) (A B : tp) (alpha beta : mult),
    exh delta ->
    upd delta n X Y A B alpha beta delta' ->
    unr alpha.
Proof.
  intros N delta delta' n X Y A B alpha beta H_exh H_upd.
  induction H_upd.
  - (* Case upd_t *)
    dependent destruction H_exh.
    assumption.
  - (* Case upd_n *)
    dependent destruction H_exh.
    apply IHH_upd; assumption.
Qed.

(* Changing type of an element of an exhausted context preserves exhaustedness *)
(* (1) If exh(Δ) and unr(β), then exh(Δ[x :α A ↦ₙ y :β B])  *)
(* (2) If exh(Δ), then exh(Δ[x :α A ↦ₙ y :α B]) [corollary of (1) and exh_lookup] *)

Lemma exh_changetp :
  forall {N : nat} (delta delta' : lctx N) (n : nat)
         (X Y : obj) (A B : tp) (alpha beta : mult),
    exh delta ->
    unr beta ->
    upd delta n X Y A B alpha beta delta' ->
    exh delta'.
Proof.
  intros N delta delta' n X Y A B alpha beta H_exh H_unr H_upd.
  generalize dependent delta'.
  generalize dependent n.
  induction H_exh as [| N delta0 x A0 alpha0 sub_exh IH alpha_unr].
  - (* Base case: exh_n *)
    intros n delta' H_upd.
    inversion H_upd.
  - (* Inductive case: exh_c *)
    intros n delta' H_upd.
    inversion H_upd; subst.
    + (* Subcase: upd_t *)
      apply exh_c.
      * dependent destruction H. (* Align delta and delta0 *)
        exact sub_exh.
      * exact H_unr.
    + (* Subcase: upd_n *)
      dependent destruction H.  (* Align delta and delta0 *)
      dependent destruction H12. (* Align delta' with the updated context *)
      apply exh_c.
      * apply IH with (n := n) (delta' := delta'0); assumption.
      * exact alpha_unr.
Qed.

Lemma exh_changetp_cor :
  forall {N : nat} (delta delta' : lctx N) (n : nat)
         (X Y : obj) (A B : tp) (alpha : mult),
    exh delta ->
    upd delta n X Y A B alpha alpha delta' ->
    exh delta'.
Proof.
  intros N delta delta' n X Y A B alpha H_exh H_upd.
  (* Derive unr alpha using exh_lookup *)
  assert (unr alpha) as H_unr.
  {
    (* Pass explicit arguments *)
    apply (exh_lookup delta delta' n X Y A B alpha alpha H_exh H_upd).
  }
  (* Apply exh_changetp with the derived unr alpha *)
  apply (exh_changetp delta delta' n X Y A B alpha alpha H_exh H_unr H_upd).
Qed.
