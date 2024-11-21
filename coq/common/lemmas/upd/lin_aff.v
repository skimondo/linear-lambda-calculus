(* =================================================== *)
(* Corollaries of look-up properties *)
(* (linear / affine systems) *)
(* =================================================== *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Import common.defs.ctx.
Require Import common.defs.obj.
Require Import common.defs.tp.
Require Import common.defs.lin_aff.

(* Lookup-inequality properties: *)
(* (1) If (x :¹ A) ∈ₙ Δ and (y :⁰ B) ∈ₘ Δ, then n ≠ m *)
(* (2) If (x :⁰ A) ∈ₙ Δ and (y :¹ B) ∈ₘ Δ, then n ≠ m [corollary of (1) using commutativity of ≠] *)

Lemma lookup_lab_neq :
  forall {N : nat} {psi : ctx} {delta delta' delta'' : lctx N} {n m : nat}
         {X X' Y Y' : obj} {A A' B B' : tp} {alpha' beta' : mult},
    upd delta n X X' A A' one alpha' delta' ->
    upd delta m Y Y' B B' zero beta' delta'' ->
    n <> m.
Admitted.

