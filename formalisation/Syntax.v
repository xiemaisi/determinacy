(** Syntax of MuJS **)
Require Export Common Parameters.

Inductive literal :=
  | LPV :> primval -> literal
  | LFun : forall (parm:name)
                  (locals:list name)
                  (body:stmt)
                  (ret:name), literal
  | LRec : literal
with stmt :=
  | SLoadLit : name -> literal -> stmt
  | SVarCopy : name -> name -> stmt
  | SPropRead : name -> name -> name -> stmt
  | SPropWrite : name -> name -> name -> stmt
  | SPrimOp : name -> name -> primop -> name -> stmt
  | SFunCall : name -> name -> name -> stmt
  | SIf : name -> stmt -> stmt
  | SWhile : label -> name -> stmt -> stmt
  | SSkip : stmt
  | SSeq : stmt -> stmt -> stmt.

Scheme literal_stmt_ind := Induction for literal Sort Prop
  with stmt_literal_ind := Induction for stmt Sort Prop.
