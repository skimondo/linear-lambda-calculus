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
Admitted.


Lemma exh_changetp_cor :
  forall {N : nat} (delta delta' : lctx N) (n : nat)
         (X Y : obj) (A B : tp) (alpha : mult),
    exh delta ->
    upd delta n X Y A B alpha alpha delta' ->
    exh delta'.
Admitted.
