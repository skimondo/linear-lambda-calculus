(* =================================================== *)
(* Multiplicities *)
(* (linear / affine systems with exponentials) *)
(* =================================================== *)

Inductive mult : Type :=
| zero : mult (* used *)
| one : mult (* available linearly *)
| omega : mult. (* available unrestrictedly *)

(* α₁ • α₂ = α *)

Inductive mult_op : mult -> mult -> mult -> Prop :=
| mult_op_zero_one : forall alpha : mult, mult_op zero alpha alpha
| mult_op_zero_two : forall alpha : mult, mult_op alpha zero alpha
| mult_op_one_one : mult_op one one omega
| mult_op_omega_one : forall alpha : mult, mult_op omega alpha omega
| mult_op_omega_two : forall alpha : mult, mult_op alpha omega omega.

(* α is unrestricted or used*)

Inductive unr : mult -> Prop :=
| unr_zero : unr zero
| unr_omega : unr omega.

(* α is an identity element w.r.t. • *)

Inductive ident : mult -> Prop :=
| ident_zero : ident zero.

(* α = α *)

Inductive mult_eq : mult -> mult -> Prop :=
| mult_refl : forall alpha : mult, mult_eq alpha alpha.



