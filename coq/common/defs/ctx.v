(* =================================================== *)
(* Explicit contexts *)
(* =================================================== *)

Require Import common.obj.
Require Import common.tp.
Require Import Coq.Arith.PeanoNat.
Require Import common.mult.lin_aff.

(* --------------------------------------------------- *)
(* Length-indexed typing contexts *)
(* --------------------------------------------------- *)

Inductive lctx : nat -> Type :=
| nil : lctx 0
| cons : forall (N : nat), lctx N -> obj -> tp -> mult -> lctx (S N).

(* Typing context equality *)

(* curly braces *)
(* https://coq.inria.fr/doc/v8.12/refman/language/extensions/implicit-arguments.html *)

Inductive cx_eq {N : nat} : lctx N -> lctx N -> Type :=
| cx_refl : forall delta : lctx N, cx_eq delta delta.

(* --------------------------------------------------- *)
(* Main operations on typing contexts *)
(* --------------------------------------------------- *)

(* Splitting / merging typing contexts: Δ₁ ⋈ Δ₂ = Δ *)

(* https://coq.inria.fr/distrib/current/refman/language/gallina-extensions.html#implicit-generalization *)

Inductive merge : forall {N : nat}, lctx N -> lctx N -> lctx N -> Type :=
| mg_n : merge nil nil nil
| mg_c : forall {N} (delta1 delta2 delta : lctx N) (alpha1 alpha2 alpha : mult) (X : obj) (A : tp),
    merge delta1 delta2 delta
    -> mult_op alpha1 alpha2 alpha
    -> merge (cons N delta1 X A alpha1) (cons N delta2 X A alpha2) (cons N delta X A alpha).

(* --------------------------------------------------- *)
(* Context pruning *)
(* --------------------------------------------------- *)


