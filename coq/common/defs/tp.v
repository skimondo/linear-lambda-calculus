(* =================================================== *)
(* General definition of types *)
(* =================================================== *)

(* Unset Automatic Proposition Inductives. *)

Parameter tp : Type.

(* Type equality *)

Inductive eq_tp : tp -> tp -> Type :=
| refl : forall A : tp, eq_tp A A.
