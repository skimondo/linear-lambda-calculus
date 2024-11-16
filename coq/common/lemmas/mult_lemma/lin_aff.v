(* =================================================== *)
(* Algebraic properties of multiplicities *)
(* (linear / affine systems) *)
(* =================================================== *)

(* Remark: • is not total since 𝟙 • 𝟙 is undefined *)

Require Import common.mult.lin_aff.

(* Functionality: If α₁ ∙ α₂ = α and α₁ ∙ α₂ = α', then α = α' *)

Lemma mult_func :
  forall (alpha1 alpha2 alpha alpha' : mult),
    mult_op alpha1 alpha2 alpha ->
    mult_op alpha1 alpha2 alpha' ->
    mult_eq alpha alpha'.
Proof.
  intros alpha1 alpha2 alpha alpha' Hmult1 Hmult2.
  (* Case analysis on Hmult1 to match possible forms of mult_op *)
  destruct Hmult1;
  inversion Hmult2; subst;
  apply mult_refl.
Qed.



(* Identity:  *)
(* (1) If α₁ ∙ α₂ = α and α₁ is an identity element, then α₂ = α *)
(* (2) For any α, obtain an identity element β such that β • α = α *)

Lemma mult_id :
  forall {alpha1 alpha2 alpha : mult},
    mult_op alpha1 alpha2 alpha ->
    ident alpha1 ->
    mult_eq alpha2 alpha.
Proof.
  Admitted.