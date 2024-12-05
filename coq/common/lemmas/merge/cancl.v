(* =================================================== *)
(* Algebraic properties that depend on *)
(* resource algebra operation being cancellative *)
(* =================================================== *)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.

Require Import common.defs.ctx.
Require Import common.defs.obj.

(* Cancellativity: If Δ₁ ⋈ Δ₂ = Δ₁ ⋈ Δ₂', then Δ₂ = Δ₂' *)



Lemma cx_eq_cons_refl :
  forall {N : nat} (delta : lctx N) (obj : obj) (tp : tp.tp) (alpha : lin_aff.mult),
    cx_eq delta delta ->
    cx_eq (cons N delta obj tp alpha) (cons N delta obj tp alpha).
Proof.
  intros N delta obj tp alpha H_cx_eq.
  inversion H_cx_eq; subst.
  constructor.
Qed.



Lemma merge_cancl :
  forall {N : nat} (psi : ctx) (delta delta1 delta2 delta2' : lctx N),
    merge delta1 delta2 delta ->
    merge delta1 delta2' delta ->
    cx_eq delta2 delta2'.
Proof.
  intros N psi delta delta1 delta2 delta2' H_merge1 H_merge2.
  generalize dependent delta2'.
  induction H_merge1 as [| N delta1 delta2 delta obj tp alpha1 alpha2 alpha H_merge1 IH_merge H_mult].
  - (* Base case *)
    intros delta2' H_merge2.
    dependent destruction H_merge2.
    apply cx_refl.
  - (* Inductive case *)
    intros delta2' H_merge2.
    dependent destruction H_merge2.
    (* Use IH_merge to prove subcontext equality *)
    specialize (IH_merge delta3 H_merge2).
    inversion IH_merge; subst.
    (* apply cx_eq_cons_refl. *)
    Abort.

(* Qed. *)



Lemma merge_cancl :
  forall {N : nat} (psi : ctx) (delta delta1 delta2 delta2' : lctx N),
    merge delta1 delta2 delta ->
    merge delta1 delta2' delta ->
    cx_eq delta2 delta2'.
Proof.
  intros N psi delta delta1 delta2 delta2' H_merge1 H_merge2.
  generalize dependent delta2'.
  induction H_merge1 as [| N delta1 delta2 delta obj tp alpha1 alpha2 alpha H_merge1 IH_merge H_mult].
  - (* Base case *)
    intros delta2' H_merge2.
    dependent destruction H_merge2.
    apply cx_refl.
  - (* Inductive case *)
    intros delta2' H_merge2.
    dependent destruction H_merge2.
    (* Use IH_merge to prove subcontext equality *)
    specialize (IH_merge delta3 H_merge2).
    inversion IH_merge; subst.
    (* Use mult_op_cancellation to align multiplicities *)
    assert (alpha3 = tp) as H_alpha_eq.
    Abort.
(* Qed. *)

    (* Prove multiplicities align *)
    (* assert (alpha2 = alpha3). *)

    (* Conclude cx_eq for the extended contexts *)
    (* constructor. *)






Lemma merge_cancl' :
  forall {N : nat} (delta delta1 delta2 delta2' : lctx N),
    merge delta1 delta2 delta ->
    merge delta1 delta2' delta ->
    cx_eq delta2 delta2'.
Proof.
  intros N delta delta1 delta2 delta2' H_merge1 H_merge2.
  (* The goal depends on delta2'. so we treated as a universally quantified var *)
  generalize dependent delta2'. (* Generalize delta2' for induction *)
  induction H_merge1 as [| N delta1 delta2 delta X A alpha1 alpha2 alpha H_merge1 IH H_mult1].
  - (* Base Case: merge nil nil nil *)
    intros delta2' H_merge2.
    dependent destruction H_merge2. (* Ensure delta2' = nil *)
    apply cx_refl. (* Reflexivity of cx_eq for nil *)
  - (* Inductive Case: merge cons *)
    intros delta2' H_merge2.
    dependent destruction H_merge2. (* Decompose merge for delta2' *)
    (* Apply IH to the sub-contexts delta2 and delta3 *)
    specialize (IH _ H_merge2).
    Admitted.
(* Qed. *)
