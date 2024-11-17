(* =================================================== *)
(* Explicit contexts *)
(* =================================================== *)

Require Import Coq.Arith.PeanoNat.

Require Import common.defs.obj.
Require Import common.defs.tp.
Require Import common.defs.lin_aff.

(* --------------------------------------------------- *)
(* Length-indexed typing contexts *)
(* --------------------------------------------------- *)

Inductive lctx : nat -> Type :=
| nil : lctx 0
| cons : forall (N : nat), lctx N -> obj -> tp -> mult -> lctx (S N).

(* Typing context equality *)

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

(* Δ[x :α A ↦ₙ y :β B] = Δ' *)
(* i.e., x appears in Δ at position n with type A and multiplicity α, and *)
(* Δ' is the result of changing that entry to y :β B *)

Inductive upd : forall {N : nat}, lctx N -> nat -> obj -> obj -> tp -> tp -> mult -> mult -> lctx N -> Type :=
| upd_t : forall {N : nat} (delta : lctx N) (X X' : obj) (A A' : tp) (alpha alpha' : mult),
    upd (cons N delta X A alpha) (S N) X X' A A' alpha alpha' (cons N delta X' A' alpha')
| upd_n : forall {N : nat} (delta delta' : lctx N) (n : nat) (X X' Y : obj) (A A' B : tp) (alpha alpha' beta : mult),
    upd delta n X X' A A' alpha alpha' delta' ->
    upd (cons N delta Y B beta) n X X' A A' alpha alpha' (cons N delta' Y B beta).

(* Only unrestricted assumptions appear in Δ, *)
(* parametric to the predicate "unr α"; in the case of linear type systems, *)
(* "unr α" holds when α = 𝟘 (unavailable). *)

Inductive exh : forall {N : nat}, lctx N -> Prop :=
| exh_n : exh nil
| exh_c : forall {N : nat} (delta : lctx N) (x : obj) (A : tp) (alpha : mult),
    exh delta -> unr alpha -> exh (cons N delta x A alpha).

(* Δ ≈ Δ', Δ = Δ' up to varying multiplicities *)
(* (corresponds to 0Δ = 0Δ' for linear systems) *)

Inductive same_elts : forall {N : nat}, lctx N -> lctx N -> Type :=
| se_n : same_elts nil nil
| se_c : forall {N : nat} (delta delta' : lctx N) (X : obj) (A : tp) (alpha alpha' : mult),
    same_elts delta delta' -> same_elts (cons N delta X A alpha) (cons N delta' X A alpha').

(* --------------------------------------------------- *)
(* Shorthand for other properties *)
(* --------------------------------------------------- *)

(* Δ[(n, x) ↔ (m, y)] = Δ', i.e., permute two distinct elements of a typing context *)

(* Exchanging two distinct elements in a typing context *)
Inductive exch : forall {N : nat}, lctx N -> nat -> obj -> nat -> obj -> lctx N -> Type :=
| exch_u : forall {N : nat} (delta delta' delta'' : lctx N) (n m : nat) (x y : obj) (a b : tp) (alpha beta : mult),
    n <> m ->                        (* Ensure n and m are distinct *)
    upd delta n x y a b alpha beta delta'' ->    (* Update at position n *)
    upd delta'' m y x b a beta alpha delta' ->   (* Update at position m *)
    exch delta n x m y delta'.                   (* Resulting context after exchange *)


(* Look up name, type, and multiplicity *)

Inductive lookup : obj -> tp -> mult -> forall {N : nat}, lctx N -> Prop :=
| look : forall {N : nat} (delta delta' : lctx N) (X : obj) (A : tp) (alpha : mult) (n : nat),
    upd delta n X X A A alpha alpha delta' -> lookup X A alpha delta.


(* Look up name *)

(* Inductive lookup_n : obj -> forall {N : nat}, lctx N -> Prop :=
| lookn : forall {N : nat} (delta delta' : lctx N) (X : obj) (A : tp) (alpha : mult) (n : nat),
    upd delta n X X A A alpha alpha delta' -> lookup_n X delta. *)

Inductive lookup_n : obj -> forall {N : nat}, lctx N -> Prop :=
| lookn : forall {N : nat} (A : tp) (alpha : mult) (delta delta' : lctx N) (X : obj) (n : nat),
    upd delta n X X A A alpha alpha delta' -> lookup_n X delta.

(* Look up index and name *)

Inductive lookup_in : nat -> obj -> forall {N : nat}, lctx N -> Prop :=
| lookin : forall {N : nat} (delta delta' : lctx N) (n : nat) (X Y : obj) (A B : tp) (alpha beta : mult),
    upd delta n X Y A B alpha beta delta' -> lookup_in n X delta.

(* Look up index, name, and type *)

Inductive lookup_int : nat -> obj -> tp -> forall {N : nat}, lctx N -> Prop :=
| lookint : forall {N : nat} (delta delta' : lctx N) (n : nat) (X Y : obj) (A B : tp) (alpha beta : mult),
    upd delta n X Y A B alpha beta delta' -> lookup_int n X A delta.

(* Look up index, name, type, and multiplicity *)

Inductive lookup_intm : nat -> obj -> tp -> mult -> forall {N : nat}, lctx N -> Prop :=
| lookintm : forall {N : nat} (delta delta' : lctx N) (n : nat) (X Y : obj) (A B : tp) (alpha beta : mult),
    upd delta n X Y A B alpha beta delta' -> lookup_intm n X A alpha delta.

(* --------------------------------------------------- *)
(* Well-formedness conditions *)
(* --------------------------------------------------- *)

(* Context contains no duplicate names and only elements of the LF context *)

Inductive Wf : forall {N : nat}, lctx N -> Prop :=
| Wf_nil : Wf nil
| Wf_cons : forall {N : nat} (delta : lctx N) (x : obj) (A : tp) (alpha : mult),
    Wf delta ->
    (forall n : nat, ~ lookup_n x delta) ->  (* Ensure x does not already exist in delta *)
    Wf (cons N delta x A alpha).

(* TODO Ask if missing anuthing *)
(* Context contains only variables from the LF context *)

(* Inductive VarCtx : forall {N : nat}, lctx N -> Prop :=
| VCtx_nil : VarCtx nil
| VCtx_cons : forall {N : nat} (delta : lctx N) (p : obj) (A : tp) (alpha : mult),
    VarCtx delta ->
    VarCtx (cons N delta p A alpha). *)

Inductive VarCtx : ctx -> forall {N : nat}, lctx N -> Prop :=
| VCtx_nil : VarCtx empty nil
| VCtx_cons : forall {N : nat} (psi : ctx) (delta : lctx N) (x : obj) (A : tp) (alpha : mult),
    VarCtx psi delta ->
    VarCtx (extend x psi) (cons N delta x A alpha).
