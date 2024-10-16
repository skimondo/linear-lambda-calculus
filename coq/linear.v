
Require Import List.
Import ListNotations.

Lemma A_proves_A : forall A : Prop, A -> A.
Proof.
    intros A hyp.
    exact hyp.
Qed.

Lemma cut : forall (A  B : Prop), (A -> B) -> A -> B.
Proof.
(* H1 is Delta2,A proves B *)
(* H2 is Delta1 proves A *)
    intros A B H1 H2.
    apply H1.
    exact H2.
Qed.

(* From the ressources PSI and the availability of A, you can derive B *)
(* With the ressources of Delta, you can Derive A /multimap B *)

(* AVAILABLE TRANSFORMATIONS/PROPOSITION  *)
Inductive lprop : Set :=
(* A is atomic prop *)
  | A : lprop
  | B : lprop
  | C : lprop
  | Lollipop : lprop -> lprop -> lprop.

(* RESSOURCES *)
Definition ressource := list lprop.

(* how assumptions are consumed *)
Inductive entails : ressource -> lprop -> Prop :=
(* if A is present in Gamma, then you can derive A *)
  | Entails_A : forall (Gamma : ressource), In A Gamma -> entails Gamma A
  | Entails_B : forall (Gamma : ressource), In B Gamma -> entails Gamma B
  | Entails_C : forall (Gamma : ressource), In C Gamma -> entails Gamma C
  (* If P ⊸ Q and you can derive Q from P, then P ⊸ Q holds *)
  | Entails_Lollipop : forall (Gamma : ressource) (P Q : lprop),
      entails (P :: Gamma) Q -> entails Gamma (Lollipop P Q)
  | Entails_Lollipop_Elim : forall (Delta1 Delta2 : ressource) (P Q C : lprop),
      entails Delta1 P -> 
      entails (Q :: Delta2) C -> 
      entails (Lollipop P Q :: Delta1 ++ Delta2) C.

(* The linear implication rule *)
(* I am assuimg same ressource *)
Theorem linear_implication_rule :
  forall (Psi : ressource), 
  entails (A :: Psi) B -> 
  entails Psi (Lollipop A B).
Proof.
  intros Psi H.
  apply Entails_Lollipop.
  exact H.
Qed.

(* Elimination *)
Theorem lollipop_elimination :
  forall (Delta1 Delta2 : ressource) (P Q C : lprop),
  entails Delta1 P ->
  entails (Q :: Delta2) C ->
  entails (Lollipop P Q :: Delta1 ++ Delta2) C.
Proof.
  intros Delta1 Delta2 P Q C H1 H2.
  (* Apply the linear implication elimination rule *)
  apply Entails_Lollipop_Elim.
  - exact H1.
  - exact H2.
Qed.


