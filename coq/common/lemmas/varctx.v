(* =================================================== *)
(* Properties of VarCtx predicate *)
(* =================================================== *)

Require Import common.ctx.
Require Import common.obj.
Require Import common.tp.
Require Import Coq.Arith.PeanoNat.
Require Import common.mult.lin_aff.

(* If VarCtx [Ψ ⊢ Δ] and x ∈ Δ, then x is a parameter variable from Ψ *)
Lemma varctx_isvar :
  forall {N : nat} (psi : ctx) (delta delta' : lctx N) (n : nat)
         (X X' : obj) (A A' : tp) (alpha alpha' : mult),
    VarCtx psi delta ->
    upd delta n X X' A A' alpha alpha' delta' ->
    IsVar psi X.
Admitted.

(* Extend VarCtx judgment with new variable of type obj *)
Lemma varctx_ext :
  forall {N : nat} (psi : ctx) (delta : lctx N) (x : obj),
    VarCtx psi delta ->
    VarCtx (extend x psi) delta.
Admitted.

(* Extending a context with a fresh variable preserves VarCtx predicate *)
Lemma varctx_extcons :
  forall {N : nat} (psi : ctx) (delta : lctx N) (x : obj) (A : tp) (alpha : mult),
    VarCtx psi delta ->
    VarCtx (extend x psi) (cons N delta x A alpha).
Admitted.

(* If VarCtx [Ψ ⊢ Δ] and Δ₁ ⋈ Δ₂ = Δ, then VarCtx [Ψ ⊢ Δ₁] *)
Lemma varctx_merge :
  forall {N : nat} (psi : ctx) (delta delta1 delta2 : lctx N),
    VarCtx psi delta ->
    merge delta1 delta2 delta ->
    VarCtx psi delta1.
Admitted.

(* If VarCtx [Ψ ⊢ Δ] and Δ₁ ⋈ Δ₂ = Δ, then VarCtx [Ψ ⊢ Δ₂] *)
Lemma varctx_merge_r :
  forall {N : nat} (psi : ctx) (delta delta1 delta2 : lctx N),
    VarCtx psi delta ->
    merge delta1 delta2 delta ->
    VarCtx psi delta2.
Admitted.