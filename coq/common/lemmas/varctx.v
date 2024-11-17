(* =================================================== *)
(* Properties of VarCtx predicate *)
(* =================================================== *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Equality.

Require Import common.defs.ctx.
Require Import common.defs.obj.
Require Import common.defs.tp.
Require Import common.defs.lin_aff.

(* If VarCtx [Ψ ⊢ Δ] and x ∈ Δ, then x is a parameter variable from Ψ *)

Lemma varctx_isvar :
  forall {N : nat} (psi : ctx) (delta delta' : lctx N) (X X' : obj) (A A' : tp) (alpha alpha' : mult) (n : nat),
    VarCtx psi delta ->
    upd delta n X X' A A' alpha alpha' delta' ->
    IsVar psi X.
Proof.
  intros N psi delta delta' X X' A A' alpha alpha' n H_varctx H_upd.
  generalize dependent psi.
  induction H_upd as [
      (* Case: upd_t *)
      N delta X X' A A' alpha alpha' |
      (* Case: upd_n *)
      N delta delta' n X X' Y A A' B alpha alpha' beta H_upd IH].
  - (* Case: upd_t *)
    intros psi H_varctx.
    inversion H_varctx as [| N' psi' delta' Y' B' beta' H_varctx_sub H_unique]; subst.
    (* X is at the top of the context, and the parent context is `psi` *)
    apply IsVar_intro.
  - (* Case: upd_n *)
    intros psi H_varctx.
    (* Decompose the VarCtx for (cons N delta Y B beta) *)
    inversion H_varctx as [| N' psi' delta_sub Y' B' beta' H_varctx_sub H_unique]; subst.
    (* Apply the IH to the sub-context delta *)
    apply IH.
    Abort.
    (* exact H_varctx_sub.
Qed. *)

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