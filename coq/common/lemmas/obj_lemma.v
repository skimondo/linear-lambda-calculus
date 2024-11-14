(* =================================================== *)
(* General properties of objects *)
(* =================================================== *)

Require Import common.obj.
Require Import common.obj2.

(* TODO TO BE VERIFIED *)

(* Weaken object inequality judgment *)
Lemma neq_weak_v :
  forall (Psi : ctx) (M N : obj),
    (obj_eq M N -> False) -> (forall x : obj, obj_eq M N -> False).
Proof.
  intros Psi M N neq_proof x eq_proof.
  (* Since `obj_eq M N -> False`, any instance of `obj_eq M N` leads to contradiction *)
  apply neq_proof in eq_proof. (* Apply the `neq_proof` to derive contradiction *)
  contradiction.
Qed.

(* Object inequality is commutative *)
Lemma neq_comm_v :
  forall (Psi : ctx) (M N : obj),
    (obj_eq M N -> False) -> (obj_eq N M -> False).
Proof.
  intros Psi M N neq_proof eq_proof.
  (* Use symmetry if `obj_eq` is symmetric *)
  assert (sym_eq : obj_eq M N).
  { inversion eq_proof; subst. apply obj_refl. } (* Use `obj_refl` to show `obj_eq M N` *)
  apply neq_proof in sym_eq. (* Now we can apply `neq_proof` to get a contradiction *)
  contradiction.
Qed.
