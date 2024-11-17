(* =================================================== *)
(* Further properties of objects *)
(* (assuming the type obj is uninhabited) *)
(* =================================================== *)

Require Import Coq.Logic.Classical_Prop.

Require Import common.defs.obj.
Require Import common.defs.ctx.

(* For any objects M and N, either M = N or M ≠ N *)

Lemma comp_obj :
  forall (psi : ctx) (M N : obj),
    CompareObjs psi M N.
Proof.
  intros psi M N.
  (* Define two cases: M = N or M <> N *)
  destruct (classic (M = N)) as [H_eq | H_neq].
  - (* Case: M = N *)
    apply Ct_Eq.
    exact H_eq.
  - (* Case: M <> N *)
    apply Ct_Neq.
    exact H_neq.
Qed.

(* If X is an object under the ambient context Ψ,y:obj and X ≠ y, then X is a parameter variable in Ψ *)

Lemma prune_obj :
  forall (psi : ctx) (x p : obj),
    obj_eq p x -> False -> PruneObj (extend x psi) (fun _ => p).
Proof.
  intros psi x p H_eq H_false.
  (* Case analysis on the equality proof *)
  inversion H_eq; subst.
  exfalso. (* Use the false hypothesis to derive a contradiction *)
  exact H_false.
Qed.
