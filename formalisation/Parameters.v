(** Our semantics of MuJS is parameterised over the following unspecified sets and operations. **)

Require Export String.

(** set of primitive values **)
Parameter primval : Type.

(** a designated primitive value **)
Parameter undefined : primval.

(** set of primitive binary operators **)
Parameter primop : Type.

(** conversion from primitive values to Booleans **)
Parameter prim_truthy : primval -> Prop.

(** conversion from primitive values to strings **)
Parameter tostring : primval -> string.

(** semantics of primitive operators **)
Parameter primop_eval : primval -> primop -> primval -> option primval.
