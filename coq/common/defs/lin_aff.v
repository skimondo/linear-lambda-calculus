(* =================================================== *)
(* Multiplicities (linear / affine systems) *)
(* =================================================== *)

Inductive mult : Type :=
| zero : mult (* used *)
| one : mult. (* available once *)

(* α₁ • α₂ = α *)

Inductive mult_op : mult -> mult -> mult -> Prop :=
  | mult_op_us : mult_op zero zero zero
  | mult_op_a1 : mult_op one zero one
  | mult_op_a2 : mult_op zero one one.

(* α is unavilable/consumed *)

Inductive unr : mult -> Prop :=
| unr_zero : unr zero.

(* α is an identity element w.r.t. • *)

Inductive ident : mult -> Prop :=
| ident_zero : ident zero.

(* α = α *)

Inductive mult_eq : mult -> mult -> Prop :=
| mult_refl : forall alpha : mult, mult_eq alpha alpha.
