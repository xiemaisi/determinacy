(** Concrete values, records, environments, heaps and events. **)
Set Implicit Parameters.

Require Import Eq Common FinMap Syntax.

Inductive value :=
  | VPrim :> primval -> value
  | VAddr :> address -> value
  | VClos : forall (parm:name)
                   (vars:list name)
                   (body:stmt)
                   (ret:name)
                   (ρ:env name value), value.

(* the default induction principle for values is useless; define a better one *)
Section BetterValueInd.
  Variable P : value -> Type.
  Variable H1: forall (pv:primval), P pv.
  Variable H2: forall (a:address), P a.
  Variable H3: forall x ys b z ρ, (forall x v, lookup ρ x = Some v -> P v) -> P (VClos x ys b z ρ).

  (* introduce views to make proof go through *)
  Inductive is_a_value : value -> Type :=
    | VPrimIsValue : forall (pv:primval), is_a_value pv
    | VAddrIsValue : forall (a:address), is_a_value a
    | VClosIsValue : forall x ys b z ρ, is_an_env ρ -> is_a_value (VClos x ys b z ρ)
  with is_an_env : env name value -> Type :=
    | NilIsEnv : is_an_env nil
    | ConsIsEnv : forall x v ρ, is_a_value v -> is_an_env ρ -> is_an_env ((x,v)::ρ).

  Scheme is_a_value_env_rect := Induction for is_a_value Sort Type
    with is_an_env_value_rect := Induction for is_an_env Sort Type.

  Definition is_value_env_mutrect (P: forall v, is_a_value v -> Type)
                                  (Q: forall e, is_an_env e -> Type)
                                  (H1: forall (pv:primval), P pv (VPrimIsValue pv))
                                  (H2: forall (a:address), P a (VAddrIsValue a))
                                  (H3 : forall x ys b z ρ (H : is_an_env ρ),
                                    Q ρ H -> P (VClos x ys b z ρ) (VClosIsValue x ys b z ρ H))
                                  (H4 : Q nil NilIsEnv)
                                  (H5 : forall x v ρ (H : is_a_value v),
                                    P v H -> forall H' : is_an_env ρ, Q ρ H' -> Q ((x, v) :: ρ) (ConsIsEnv x v ρ H H')) :=
     (is_a_value_env_rect P Q H1 H2 H3 H4 H5,
      is_an_env_value_rect P Q H1 H2 H3 H4 H5).

  (* prove soundness of view *)
  Lemma every_value_is_a_value : forall v, is_a_value v.
  Proof.
    fix 1; destruct v.
      constructor.
      
      constructor.

      constructor.
      induction ρ.
        constructor.

        destruct a as (x,v).
        constructor.
          apply every_value_is_a_value.

          apply IHρ.
  Qed.

  Lemma better_value_ind : forall v, P v.
  Proof.
    assert (K : (forall v (H:is_a_value v), (fun _ => P v) H) *
                (forall ρ (H:is_an_env ρ),  (fun _ => forall x v, lookup ρ x = Some v -> P v) H)).
    apply (is_value_env_mutrect (fun v _ => P v) (fun ρ _ => forall x v, lookup ρ x = Some v -> P v)).
      apply H1.

      apply H2.

      intros.
      apply H3; auto.

      inversion 1.

      intros x v ρ _ K1 _ K2 x' v'.
      inversion 1; subst.
      destruct (x' == x); subst.
        inversion H4; subst.
        trivial.

        eauto.

    destruct K as (K1&K2).
    auto using every_value_is_a_value.
  Qed.
End BetterValueInd.

(** extending definition of truthiness to all values **)
Inductive truthy : value -> Prop :=
  | PrimTruthy : forall pv, prim_truthy pv -> truthy pv
  | AddrTruthy : forall (a:address), truthy a
  | ClosTruthy : forall x ys b z ρ, truthy (VClos x ys b z ρ).

(** records **)
Definition record := env name value.

(** records can be interpreted as total functions **)
Definition record_lookup (r:record) (x:name) :=
  match lookup r x with
  | Some v => v
  | None => undefined
  end.

(** heaps **)
Definition heap := address -> option record.

(** events **)
Inductive event :=
  | EVarWrite : name -> value -> event
  | EPropWrite : address -> name -> value -> event
  | ECond : value -> event -> event
  | ECall : value -> env name value -> event -> event
  | ESkip : event
  | ESeq : event -> event -> event.

