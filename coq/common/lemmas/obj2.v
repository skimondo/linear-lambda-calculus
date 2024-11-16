(* =================================================== *)
(* Further properties of objects *)
(* (assuming the type obj is uninhabited) *)
(* =================================================== *)

Require Import common.defs.obj.
Require Import common.defs.ctx.

(* For any objects M and N, either M = N or M ≠ N *)

Lemma comp_obj :
  forall (M N : obj) (psi : ctx),
    InCtx psi M ->
    InCtx psi N ->
    CompareObjs psi M N.
Admitted.

Lemma prune_obj :
  forall (psi : ctx) (x p : obj),
    obj_eq p x -> False -> PruneObj (extend x psi) (fun _ => p).
Admitted.
