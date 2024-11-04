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

(* Natural numbers are discrete, i.e., it is never the case that m < n < (m + 1) *)

(* Fixpoint nats_discrete {m n : nat_alt} (l1 : lt_alt m n) (l2 : lt_alt n (suc m)) : False :=
  match l1, l2 with
  | lt_z _, lt_s _ _ LT2 => match LT2 with end (* Contradiction: LT2 cannot match as `lt_s` in this case *)
  | lt_s _ _ LT1, lt_s _ _ LT2 => nats_discrete LT1 LT2 (* Recursive case *)
  end. *)


(* n < m -> n < m + 1 *)