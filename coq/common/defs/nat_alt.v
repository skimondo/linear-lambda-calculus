(* =================================================== *)
(* Natual numbers *)
(* =================================================== *)

Inductive nat_alt : Type :=
| zero_nat : nat_alt
| suc : nat_alt -> nat_alt.

(* n = n *)

Inductive nat_alt_eq : nat_alt -> nat_alt -> Type :=
| nat_alt_ref : forall n : nat_alt, nat_alt_eq n n.

(* n < m *)

Inductive lt_alt : nat_alt -> nat_alt -> Type :=
| lt_z : forall m : nat_alt, lt_alt zero_nat (suc m)
| lt_s : forall n m : nat_alt, lt_alt n m -> lt_alt (suc n) (suc m).  

(* n ≤ m *)

Inductive leq_alt : nat_alt -> nat_alt -> Type :=
| leq_id : forall n : nat_alt, leq_alt n n
| leq_lt : forall n m : nat_alt, lt_alt n m -> leq_alt n m.

(* n ≠ m *)

Inductive neq_alt : nat_alt -> nat_alt -> Type :=
| neq_1 : forall n m : nat_alt, lt_alt n m -> neq_alt n m
| neq_2 : forall n m : nat_alt, lt_alt m n -> neq_alt n m.


(* n + m = k *)

Inductive plus_alt : nat_alt -> nat_alt -> nat_alt -> Type :=
| pl_z : forall n : nat_alt, plus_alt zero_nat n n
| pl_s : forall n m k : nat_alt, plus_alt n m k -> plus_alt (suc n) m (suc k).


(* n = n' + 1 for some n' *)

Inductive is_suc : nat_alt -> Type :=
| is_suc_cons : forall n : nat_alt, is_suc (suc n).
