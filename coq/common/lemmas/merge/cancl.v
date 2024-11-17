(* =================================================== *)
(* Algebraic properties that depend on *)
(* resource algebra operation being cancellative *)
(* =================================================== *)

Require Import Coq.Classes.RelationClasses.

Require Import common.defs.ctx.
Require Import common.defs.obj.

(* Cancellativity: If Δ₁ ⋈ Δ₂ = Δ₁ ⋈ Δ₂', then Δ₂ = Δ₂' *)

Lemma merge_cancl :
  forall {N : nat} (delta delta1 delta2 delta2' : lctx N),
    merge delta1 delta2 delta ->
    merge delta1 delta2' delta ->
    cx_eq delta2 delta2'.
Proof.
  intros N delta delta1 delta2 delta2' H_merge1 H_merge2.
  generalize dependent delta2'.
  induction H_merge1 as [| N delta1 delta2 delta X A alpha1 alpha2 alpha H_merge1 IH H_mult].
  - (* Base case: merge nil nil nil *)
    intros delta2' H_merge2.
    inversion H_merge2; subst.
    Abort.
    (* apply cx_refl. (* Use the reflexivity constructor for cx_eq *)
  - (* Inductive case: merge cons *)
    intros delta2' H_merge2.
    inversion H_merge2; subst.
    (* Apply the inductive hypothesis *)
    specialize (IH _ H2).
    inversion IH; subst.
    (* Use mult_canc to verify alignment of multiplicities *)
    assert (mult_eq alpha2 alpha2') as H_mult_eq.
    {
      apply mult_canc with (alpha1 := alpha1) (alpha := alpha); assumption.
    }
    (* Resolve the multiplicities and contexts *)
    inversion H_mult_eq; subst.
    apply cx_refl. (* Conclude cx_eq for the entire context *)
Qed. *)


