(* =================================================== *)
(* mult_interface.v *)
(* =================================================== *)

Require Import common.nat_alt.

Module Type MultType.
  Parameter nat_alt : Type.
  Parameter mult : Type.
  Parameter zero : mult.
  Parameter one : mult.
  Parameter omega : mult.

Parameter mult_op : mult -> mult -> mult -> Prop.
Parameter unr : mult -> Prop.
Parameter ident : mult -> Prop.
Parameter mult_eq : mult -> mult -> Prop.

End MultType.
