(* =================================================== *)
(* Object-related definitions *)
(* (independent of how obj is defined) *)
(* =================================================== *)

Require Import common.obj.

(* Ambient/implicit context schema *)

(* In Coq, we cannot directly translate `schema ctx = obj;`
   Instead, we define ctx as an inductive type that can extend with obj elements. *)

Inductive ctx : Type :=
| empty : ctx
| extend : obj -> ctx -> ctx.

(* Object inequality *)

Inductive obj_eq : obj -> obj -> Type :=
| obj_refl : forall X : obj, obj_eq X X.

(* IsVar [Ψ ⊢ X]: X is a parameter variable under the LF context Ψ *)

Inductive IsVar : ctx -> obj -> Prop :=
| IsVar_intro : forall (Ψ : ctx) (p : obj), IsVar (extend p Ψ) p.

(* Definition for 'pruning' LF context to remove dependencies *)

Inductive PruneObj : ctx -> (obj -> obj) -> Prop :=
| Prune_Obj : forall (Ψ : ctx) (M : obj -> obj),
    PruneObj Ψ M.

(* CompareObjs: compares two objects to indicate if they are equal or unequal *)

Inductive CompareObjs (Ψ : ctx) (M N : obj) : Prop :=
| Ct_Eq : M = N -> CompareObjs Ψ M N
| Ct_Neq : M <> N -> CompareObjs Ψ M N.

(* 
Record ctx := {
element : obj
}. *)

(* Inductive CompareObjs : ctx -> obj -> obj -> Type :=
| Ct_Eq : forall (Ψ : ctx) (M : obj), CompareObjs Ψ M M
| Ct_Neq : forall (Ψ : ctx) (M N : obj),
    (obj_eq M N -> False) -> CompareObjs Ψ M N. *)