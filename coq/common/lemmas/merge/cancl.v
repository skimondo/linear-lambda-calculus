(* =================================================== *)
(* Algebraic properties that depend on *)
(* resource algebra operation being cancellative *)
(* =================================================== *)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.

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
