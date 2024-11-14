(* =================================================== *)
(* Properties of Wf predicate *)
(* =================================================== *)

Require Import common.ctx.
Require Import common.obj.
Require Import common.tp.
Require Import Coq.Arith.PeanoNat.
Require Import common.mult.lin_aff.

(* Proving properties about well-formedness requires a series of auxilliary technical lemmas about *)
(* context membership like the following. *)

(* Adjusting Arguments *)
Arguments lookup_n X {N} delta.
Arguments lookn {N} A alpha delta delta' X n _.
Arguments upd_t {N} delta X X' A A' alpha alpha'.
Arguments upd_n {N} delta delta' n X X' Y A A' B alpha alpha' beta _.

(* Auxiliary lemma: refl_top *)
Lemma refl_top {N : nat} (delta : lctx N) (X : obj) (A : tp) (alpha : mult) :
  upd (cons N delta X A alpha) (S N) X X A A alpha alpha (cons N delta X A alpha).
Proof.
  apply upd_t.
Qed.

(* Main lemma: look_top *)
Lemma look_top {N : nat} (delta : lctx N) (X : obj) (A : tp) (alpha : mult) :
  lookup_n X (cons N delta X A alpha).
Proof.
  apply lookn with (A := A) (alpha := alpha) (delta' := cons N delta X A alpha) (n := S N).
  - apply refl_top.
Qed.

(* --------------------------------------------------- *)
(* Main properties of context well-formedness *)
(* --------------------------------------------------- *)

(* If Wf [Ψ ⊢ Δ] and x ∈ Δ, then x is a parameter variable from Ψ *)


