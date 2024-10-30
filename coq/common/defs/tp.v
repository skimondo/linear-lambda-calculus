(* =================================================== *)
(* General definition of types *)
(* =================================================== *)

Unset Automatic Proposition Inductives.

Inductive tp : Type := .

(* Not necessary here, but to prevent undefined behavior *)
Set Automatic Proposition Inductives.

(* Type equality *)

Inductive eq_tp : tp -> tp -> Type :=
| refl : forall A : tp, eq_tp A A.
