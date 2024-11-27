(* =================================================== *)
(* Properties of context update *)
(* =================================================== *)

(* --------------------------------------------------- *)
(* Pruning lemmas *)
(* --------------------------------------------------- *)

Require Import Coq.Arith.PeanoNat.

Require Import common.defs.obj.
Require Import common.defs.ctx.
Require Import common.defs.tp.
Require Import common.defs.lin_aff.

(* "Prune" LF context to remove dependencies: *)
(* Obtain from [Ψ,x:obj ⊢ upd Δ[..] n[] X X A₁[] A₂[] α₁[] α₂[] Δ'] that neither X nor Δ' depend on x *)

Inductive PruneUpd 
  {N : nat} (Ψ : ctx) (Δ Δ' : lctx N) 
  (n : nat) (X X' : obj) (A A' : tp) (α α' : mult) 
  (U : upd Δ n X X' A A' α α' Δ') : Type :=
| Prune_Upd : upd Δ n X X' A A' α α' Δ' -> PruneUpd Ψ Δ Δ' n X X' A A' α α' U.

Lemma prune_upd :
  forall {N : nat} {Ψ : ctx} {Δ Δ' : lctx N}
         (n : nat) {X X' : obj} {A A' : tp} {α α' : mult}
         (U : upd Δ n X X' A A' α α' Δ'),
    PruneUpd Ψ Δ Δ' n X X' A A' α α' U.
Proof.
  intros N Ψ Δ Δ' n X X' A A' α α' U.
  induction U.
  - (* Case: upd/t *)
    apply Prune_Upd.
    apply upd_t.
  - (* Case: upd/n *)
    (* Apply the PruneUpd constructor for the recursive case *)
    apply Prune_Upd.
    (* Use the `upd_n` constructor to build the `upd` term *)
    apply upd_n.
    (* Use the induction hypothesis *)
    apply IHU.
Qed.


(* --------------------------------------------------- *)
(* Basic properties *)
(* --------------------------------------------------- *)

(* Obtain the identity update judgment on the top-most element of a given context *)

Lemma upd_top :
  forall {N : nat} {Ψ : ctx} {Δ : lctx N} {X X' : obj} {A A' : tp} {α α' : mult},
    upd (cons N Δ X A α) (S N) X X' A A' α α' (cons N Δ X' A' α').
Proof.
  intros N Ψ Δ X X' A A' α α'.
  apply upd_t.
Qed.

Lemma refl_top :
  forall {N : nat} {Ψ : ctx} {Δ : lctx N} {X : obj} {A : tp} {α : mult},
    upd (cons N Δ X A α) (S N) X X A A α α (cons N Δ X A α).
Proof.
  intros N Ψ Δ X A α.
  apply upd_t.
Qed.

(* If (x :α A) ∈ₙ Δ, obtain the result of changing the entry to (y :β B) *)

Inductive get_upd : forall {N : nat}, lctx N -> nat -> obj -> obj -> tp -> tp -> mult -> mult -> Type :=
| get_upd_intro :
    forall {N : nat} (Δ : lctx N) (n : nat) (X X' : obj) (A A' : tp) (α α' : mult) (Δ' : lctx N),
      upd Δ n X X' A A' α α' Δ' -> get_upd Δ n X X' A A' α α'.

Lemma lookup_getupd :
  forall {N : nat} {Ψ : ctx} {Δ Δ' : lctx N}
         (n : nat) {X X' : obj} {A A' : tp} {α α' : mult},
         upd Δ n X X' A A' α α' Δ' ->
         forall {Y : obj} {B : tp} {β : mult},
           get_upd Δ n X Y A B α β.
Proof.
  intros N Ψ Δ Δ' n X X' A A' α α' H_upd Y B β.
Admitted.

(* --------------------------------------------------- *)
(* Context size *)
(* --------------------------------------------------- *)

(* If n ∈ Δ then 0 < n < |Δ| + 1 *)

(* Define is_suc to represent successor property *)
Inductive is_suc : nat -> Prop :=
| is_suc_intro : forall n : nat, is_suc (S n).

Lemma is_suc_pred :
  forall n : nat,
    is_suc n ->
    n = S (Init.Nat.pred n).
Proof.
  intros n H.
  inversion H; subst. (* Break down the structure of `is_suc` *)
  reflexivity. (* Apply reflexivity since `n = S (pred n)` holds *)
Qed.

Lemma lookup_is_suc :
  forall {N : nat} {Ψ : ctx} {Δ Δ' : lctx N}
         (n : nat) {X X' : obj} {A A' : tp} {α α' : mult},
         upd Δ n X X' A A' α α' Δ' ->
         is_suc n.
Proof.
  intros N Ψ Δ Δ' n X X' A A' α α' H_upd.
  induction H_upd as [ | N Δ Δ' Δ'' n X X' Y A A' B α α' β H_inner].
  - (* Base case: upd/t *)
    apply is_suc_intro. (* Use the `is_suc_intro` constructor *)
  - (* Recursive case: upd/n *)
    exact H_inner. (* Directly use the hypothesis for `n` *)
Qed.
