(* =================================================== *)
(* Properties of natural number inequalities *)
(* =================================================== *)

Require Import common.nat_alt.

(* n < n + 1 for any n *)

Fixpoint lt_suc (n : nat_alt) : lt_alt n (suc n) :=
  match n with
  | zero_nat => lt_z zero_nat       (* Base case: zero < suc zero *)
  | suc n' => lt_s n' (suc n') (lt_suc n') (* Recursive case: n < suc n *)
  end.  

Theorem lt_suc_2 :
forall n : nat_alt, lt_alt n (suc n).
    
Proof.
 Admitted.