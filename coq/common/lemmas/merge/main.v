(* =================================================== *)
(* Properties of context merge *)
(* =================================================== *)

Require Import common.obj2.
Require Import common.ctx.
Require Import common.tp.
Require Import common.obj.
Require Import common.mult.lin_aff.

(* Basic properties of judgment *)

(* "Prune" LF context to remove dependencies: *)
(* (1) Obtain from [Ψ,x:obj ⊢ merge Δ₁ Δ₂ Δ[..]] that neither Δ₁ nor Δ₂ depend on x *)
(* (2) Obtain from [Ψ,x:obj ⊢ merge Δ₁[..] Δ₂ Δ] that neither Δ₂ nor Δ depend on x *)

Inductive PruneMerge : ctx -> forall {N : nat}, lctx N -> lctx N -> lctx N -> Prop :=
| Prune_Merge_n : forall Psi, PruneMerge Psi nil nil nil
| Prune_Merge_c : forall Psi {N : nat} (delta1 delta2 delta : lctx N) (X : obj) (A : tp) 
                    (alpha1 alpha2 alpha : mult),
    PruneMerge Psi delta1 delta2 delta ->
    mult_op alpha1 alpha2 alpha ->
    PruneMerge Psi (cons N delta1 X A alpha1) (cons N delta2 X A alpha2) (cons N delta X A alpha).

(* PruneMerge lemma, structured with induction over merge *)
Lemma prune_merge :
  forall (Psi : ctx) {N : nat} (Delta : lctx N) (Delta1 Delta2 : lctx N),
    merge Delta1 Delta2 Delta -> 
    PruneMerge Psi Delta1 Delta2 Delta.
Proof.
  intros Psi N Delta Delta1 Delta2 Hmerge.
  induction Hmerge.
  - (* Base case: mg_n *)
    apply Prune_Merge_n.
  - (* Recursive case: mg_c *)
    apply Prune_Merge_c.
    + apply IHHmerge. (* Apply the induction hypothesis *)
    + assumption. (* Apply mult_op condition directly *)
Qed.

Lemma prune_merge_l :
  forall (Psi : ctx) {N : nat} (Delta : lctx N) (Delta1 Delta2 : lctx N),
    merge Delta1 Delta2 Delta ->
    PruneMerge Psi Delta1 Delta2 Delta.
Proof.
  intros Psi N Delta Delta1 Delta2 Hmerge.
  induction Hmerge.
  - (* Base case: mg_n *)
    apply Prune_Merge_n.
  - (* Recursive case: mg_c *)
    apply Prune_Merge_c.
    + apply IHHmerge. (* Use the induction hypothesis for Delta1 and Delta2 *)
    + assumption. (* Apply the mult_op property directly *)
Qed.

(* --------------------------------------------------- *)
(* Algebraic properties *)
(* --------------------------------------------------- *)

(* Functionality: If Δ₁ ⋈ Δ₂ = Δ and Δ₁ ⋈ Δ₂ = Δ', then Δ = Δ' *)
