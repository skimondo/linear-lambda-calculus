(* =================================================== *)
(* Explicit contexts *)
(* =================================================== *)

Require Import common.obj.
Require Import common.tp.
Require Import common.nat_alt.
(* Require Import common.mult.expon. *)
(* Require Import common.mult.graded. *)
(* Require Import common.mult.intuit. *)
Require Import common.mult.lin_aff.
(* Require Import common.mult.strict. *)

(* --------------------------------------------------- *)
(* Length-indexed typing contexts *)
(* --------------------------------------------------- *)

Inductive lctx : nat_alt -> Type :=
| nil : lctx zero_nat
| cons : forall (N : nat_alt), lctx N -> obj -> tp -> mult -> lctx (suc N).

(* Typing context equality *)

(* curly braces *)
(* https://coq.inria.fr/doc/v8.12/refman/language/extensions/implicit-arguments.html *)

Inductive cx_eq {N : nat_alt} : lctx N -> lctx N -> Type :=
| cx_refl : forall delta : lctx N, cx_eq delta delta.

(* --------------------------------------------------- *)
(* Main operations on typing contexts *)
(* --------------------------------------------------- *)

(* Splitting / merging typing contexts: Δ₁ ⋈ Δ₂ = Δ *)

(* Define N of type nat_alt *)
(* https://coq.inria.fr/distrib/current/refman/language/gallina-extensions.html#implicit-generalization *)


(* Inductive merge {N : nat_alt} : lctx N -> lctx N -> lctx N -> Type :=
| mg_n : merge nil nil nil
| mg_c : forall (delta1 delta2 delta : lctx N) (alpha1 alpha2 alpha : mult) (X : obj) (A : tp),
    merge delta1 delta2 delta -> mult_op alpha1 alpha2 alpha -> merge (cons delta1 X A alpha1) (cons delta2 X A alpha2) (cons delta X A alpha). *)

(* --------------------------------------------------- *)
(* Context pruning *)
(* --------------------------------------------------- *)

