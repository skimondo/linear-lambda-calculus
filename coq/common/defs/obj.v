(* =================================================== *)
(* Object-related definitions *)
(* (independent of how obj is defined) *)
(* =================================================== *)

Parameter obj : Type.

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
| IsVar_intro : forall (psi : ctx) (p : obj), IsVar (extend p psi) p.

(* Definition for 'pruning' LF context to remove dependencies *)

Inductive PruneObj : ctx -> (obj -> obj) -> Prop :=
| Prune_Obj : forall (psi : ctx) (M : obj -> obj),
    PruneObj psi M.

(* CompareObjs: compares two objects to indicate if they are equal or unequal *)
(* Inductive type to encode the property that for any objects M and N, either M = N or M ≠ N *)
(* (see, e.g., the lemma comp_obj in common/lemmas/obj2.bel) *)

Inductive CompareObjs (psi : ctx) (M N : obj) : Prop :=
| Ct_Eq : M = N -> CompareObjs psi M N
| Ct_Neq : M <> N -> CompareObjs psi M N.

(* InCtx: Determines if an object is in a given context *)
Inductive InCtx : ctx -> obj -> Prop :=
| InCtx_top : forall (psi : ctx) (x : obj), InCtx (extend x psi) x
| InCtx_pop : forall (psi : ctx) (x y : obj), InCtx psi x -> InCtx (extend y psi) x.
