(* =================================================== *)
(* Properties of merge that only hold *)
(* if all unrestricted elements are identity elements *)
(* =================================================== *)

Require Import Coq.Program.Equality.

Require Import common.defs.ctx.

(* Identity properties: *)
(* (1) If Δ₁ ⋈ Δ₂ = Δ and exh(Δ₁), then Δ₂ = Δ *)
(* (2) If Δ₁ ⋈ Δ₂ = Δ and exh(Δ₂), then Δ₂ = Δ [corollary of (1) using commutativity] *)
(* (3) If Δ₁ ⋈ Δ₂ = Δ and exh(Δ), then Δ₁ = Δ₂ = Δ *)

Lemma merge_id :
  forall {N : nat} (delta delta1 delta2 : lctx N),
    merge delta1 delta2 delta ->
    exh delta1 ->
    cx_eq delta2 delta.
Proof.
  intros N delta delta1 delta2 H_merge H_exh.
  induction H_merge as [| N delta1' delta2' delta' X A alpha1 alpha2 alpha H_merge' IH H_mult].
  - (* Base case: merge nil nil nil *)
    apply cx_refl. (* Reflexivity of cx_eq for nil *)
  - (* Inductive case: merge cons *)
    (* Use dependent destruction for H_exh to decompose it safely *)
    Abort.
    (* dependent destruction H_exh.
    (* Apply IH to the sub-context *)
    specialize (IH _ H_exh).
    inversion IH; subst. (* Resolve cx_eq for sub-contexts *)
    (* Align multiplicities using mult_id *)
    assert (mult_eq alpha2 alpha) as H_mult_eq.
    {
      apply mult_id.
      - exact H_mult.
      - apply mult_unr_ident.
        exact H_unr.
    }
    inversion H_mult_eq; subst. (* Resolve equality of multiplicities *)
    apply cx_refl. (* Conclude cx_eq for the entire context *)
Qed. *)
