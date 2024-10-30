(* =================================================== *)
(* Multiplicities (strict systems) *)
(* =================================================== *)

Inductive mult : Type :=
| one : mult (* muste be used at least once *)
| omega : mult. (* available unrestrictedly *)

(* α₁ • α₂ = α *)

Inductive mult_op : mult -> mult -> mult -> Prop :=
| mult_op_one_omega : mult_op one omega one
| mult_op_omega_one : mult_op omega one one
| mult_op_omega_omega : mult_op omega omega omega.

(* α is unrestricted *)

Inductive unr : mult -> Prop :=
| unr_omega : unr omega.

(* α is an identity element w.r.t. • *)

Inductive ident : mult -> Prop :=
| ident_omega : ident omega.

(* α = α *)

Inductive mult_eq : mult -> mult -> Prop :=
| mult_refl : forall alpha : mult, mult_eq alpha alpha.
