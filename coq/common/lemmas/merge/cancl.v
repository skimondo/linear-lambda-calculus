(* =================================================== *)
(* Algebraic properties that depend on *)
(* resource algebra operation being cancellative *)
(* =================================================== *)

Require Import common.ctx.
Require Import common.obj2.

(* Cancellativity: If Δ₁ ⋈ Δ₂ = Δ₁ ⋈ Δ₂', then Δ₂ = Δ₂' *)
Lemma merge_cancl_lemma :
  forall (psi : ctx) (N : nat) (delta delta1 delta2 delta2' : lctx N),
    merge delta1 delta2 delta ->
    merge delta1 delta2' delta ->
    cx_eq delta2 delta2'.
Proof.
Admitted.
