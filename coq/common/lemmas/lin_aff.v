(* =================================================== *)
(* Algebraic properties of multiplicities *)
(* (linear / affine systems) *)
(* =================================================== *)

(* Remark: • is not total since 𝟙 • 𝟙 is undefined *)

Require Import common.defs.lin_aff.

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
  intros alpha1 alpha2 alpha Hmult Hident.
  (* Case analysis on the identity property *)
  inversion Hident; subst; clear Hident.
  - (* Case: ident/0 (zero element) *)
    (* Analyze the multiplication operation *)
    inversion Hmult; subst; clear Hmult.
    + (* Case: mult_op/zero *)
      apply mult_refl.
    + (* Case: mult_op/unit *)
      apply mult_refl.
Qed.

Inductive get_u_mult : mult -> Prop :=
| get_u_mult_intro :
    forall (beta alpha : mult),
      ident beta -> mult_op beta alpha alpha -> get_u_mult alpha.

Lemma mult_get_id :
  forall (alpha : mult),
    (exists beta, ident beta /\ mult_op beta alpha alpha) -> get_u_mult alpha.
Proof.
  intros alpha [beta [Hident Hmult]].
  destruct alpha.
  - (* Case: zero *)
    (* Use mult_op to show beta = zero *)
    inversion Hmult; subst.
    apply get_u_mult_intro with (beta := zero).
    + constructor. (* ident zero *)
    + exact Hmult.
  - (* Case: one *)
    (* Use mult_op to show beta = zero *)
    inversion Hmult; subst.
    apply get_u_mult_intro with (beta := zero).
    + constructor. (* ident zero *)
    + exact Hmult.
Qed.

(* Zero-sum-freedom: If α₁ ∙ α₂ = α and α is an identity element, then α₁ = α *)

Lemma mult_zsfree :
  forall (alpha1 alpha2 alpha : mult),
    mult_op alpha1 alpha2 alpha ->
    ident alpha ->
    mult_eq alpha1 alpha.
Proof.
  intros alpha1 alpha2 alpha Hmult Hident.
  (* Case analysis on the identity property *)
  inversion Hident; subst; clear Hident.
  - (* Case: ident/0 (zero element) *)
    (* Case analysis on mult_op *)
    inversion Hmult; subst; clear Hmult.
    + (* Case: •/us (zero with unrestricted) *)
      apply mult_refl.
Qed.

(* Commutativity: If α₁ ∙ α₂ = α, then α₂ ∙ α₁ = α *)

Lemma mult_comm :
  forall (alpha1 alpha2 alpha : mult),
    mult_op alpha1 alpha2 alpha ->
    mult_op alpha2 alpha1 alpha.
Proof.
  intros alpha1 alpha2 alpha Hmult.
  (* Case analysis on mult_op *)
  destruct Hmult.
  - (* Case: mult_op_us (zero • zero = zero) *)
    apply mult_op_us.
  - (* Case: mult_op_a1 (one • zero = one) *)
    apply mult_op_a2.
  - (* Case: mult_op_a2 (zero • one = one) *)
    apply mult_op_a1.
Qed.

(* Associativity: If (α₁ • α₂) • α₃ = α, then α₁ • (α₂ • α₃) = α *)

Inductive assoc : mult -> mult -> mult -> mult -> mult -> mult -> Prop :=
| assoc_intro :
    forall (alpha1 alpha2 alpha3 alpha12 alpha23 alpha : mult),
      mult_op alpha2 alpha3 alpha23 ->  (* α₂ • α₃ = α₂₃ *)
      mult_op alpha1 alpha23 alpha ->  (* α₁ • α₂₃ = α *)
      mult_op alpha1 alpha2 alpha12 -> (* α₁ • α₂ = α₁₂ *)
      mult_op alpha12 alpha3 alpha ->  (* α₁₂ • α₃ = α *)
      assoc alpha1 alpha2 alpha3 alpha12 alpha23 alpha.

Lemma mult_assoc :
  forall (alpha1 alpha2 alpha3 alpha12 alpha23 alpha : mult),
    mult_op alpha1 alpha2 alpha12 ->
    mult_op alpha12 alpha3 alpha ->
    mult_op alpha2 alpha3 alpha23 ->
    mult_op alpha1 alpha23 alpha ->
    assoc alpha1 alpha2 alpha3 alpha12 alpha23 alpha.
Proof.
  intros alpha1 alpha2 alpha3 alpha12 alpha23 alpha H12 H123 H23 H123_2.
  (* Use assoc_intro to construct the result *)
  apply assoc_intro; assumption.
Qed.

(* Cancellativity: If α₁ ∙ α₂ = α and α₁ ∙ α₂' = α, then α₂ = α₂' *)

Lemma mult_canc :
  forall (alpha1 alpha2 alpha2' alpha : mult),
    mult_op alpha1 alpha2 alpha ->
    mult_op alpha1 alpha2' alpha ->
    mult_eq alpha2 alpha2'.
Proof.
  intros alpha1 alpha2 alpha2' alpha H1 H2.
  (* Case analysis on the first mult_op *)
  destruct H1;
  (* Match the second mult_op with the first *)
  inversion H2; subst;
  (* Apply reflexivity for equality of alpha2 and alpha2' *)
  apply mult_refl.
Qed.

(* Corollaries *)

Lemma mult_id_cor :
  forall (alpha2 alpha : mult),
    mult_op zero alpha2 alpha ->
    mult_eq alpha2 alpha.
Proof.
  intros alpha2 alpha Hmult.
  (* Explicitly provide the necessary proof to mult_id *)
  apply (mult_id Hmult).
  (* Provide proof of ident zero *)
  constructor. (* ident_zero *)
Qed.

Lemma mult_zsfree_cor :
  forall (alpha1 alpha2 : mult),
    mult_op alpha1 alpha2 zero ->
    mult_eq alpha1 zero.
Proof.
  intros alpha1 alpha2 Hmult.
  (* Apply the mult_zsfree lemma with ident zero *)
  apply (mult_zsfree alpha1 alpha2 zero Hmult).
  constructor. (* ident zero *)
Qed.

Lemma mult_get_id_cor :
  forall (alpha : mult),
    mult_op zero alpha alpha.
Proof.
  intros alpha.
  destruct alpha.
  - (* Case: alpha = zero *)
    constructor. (* mult_op zero zero zero *)
  - (* Case: alpha = one *)
    constructor. (* mult_op zero one one *)
Qed.

(* --------------------------------------------------- *)
(* Properties of unrestricted elements *)
(* --------------------------------------------------- *)

(* Technical lemmas about unrestricted elements (used to prove context lemmas) *)

Lemma mult_unr_id :
  forall (alpha : mult),
    unr alpha ->
    mult_op alpha alpha alpha.
Proof.
  intros alpha H_unr.
  (* Case analysis on the proof of unr alpha *)
  inversion H_unr; subst.
  - (* Case: unr_zero *)
    constructor. (* mult_op_us: zero • zero = zero *)
Qed.

Lemma mult_ident_unr :
  forall (alpha : mult),
    ident alpha ->
    unr alpha.
Proof.
  intros alpha H_ident.
  (* Case analysis on the proof of ident alpha *)
  inversion H_ident; subst.
  - (* Case: ident_zero *)
    constructor. (* unr_zero *)
Qed.

Lemma mult_unr_ident :
  forall (alpha : mult),
    unr alpha ->
    ident alpha.
Proof.
  intros alpha H_unr.
  (* Case analysis on the proof of unr alpha *)
  inversion H_unr; subst.
  - (* Case: unr_zero *)
    constructor. (* ident_zero *)
Qed.
