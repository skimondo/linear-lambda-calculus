(* =================================================== *)
(* Multiplicities (graded systems) *)
(* =================================================== *)

Require Import common.nat_alt.

Inductive mult : Type :=
| num : nat_alt -> mult. (* available to be used exactly n times *)

(* α₁ • α₂ = α *)

Inductive mult_op : mult -> mult -> mult -> Prop :=
| mult_op_plus : forall (n m k : nat_alt), plus_alt n m k -> mult_op (num n) (num m) (num k).

(* α is unrestricted *)

Inductive unr : mult -> Prop :=
| unr_zero : unr (num zero). (* Zero multiplicity represents unrestricted usage *)

(* α is an identity element w.r.t. • *)

Inductive ident : mult -> Prop :=
| ident_zero : ident (num zero).

(* α = α *)

Inductive mult_eq : mult -> mult -> Prop :=
| mult_refl : forall alpha : mult, mult_eq alpha alpha.
