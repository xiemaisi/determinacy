(** Data types of instrumented values, records, environments, heaps and events **)
Set Implicit Arguments.

Require Import Eq Common FinMap Syntax Parameters.

(** determinacy flags **)
Inductive det := Det | Indet.

(** instrumented values **)
Inductive dvalue :=
  | DVPrim : primval -> det -> dvalue
  | DVAddr : address -> det -> dvalue
  | DVClos : forall (p:name)
                    (vars:list name)
                    (body:stmt)
                    (ret:name)
                    (ρ:env name dvalue), det -> dvalue.

(** as for concrete values, we need a better induction principle **)
Section BetterDValueInd.
  Variable P : dvalue -> Type.
  Variable H1: forall (pv:primval) d, P (DVPrim pv d).
  Variable H2: forall (a:address) d, P (DVAddr a d).
  Variable H3: forall x ys b z ρ d, (forall x v, lookup ρ x = Some v -> P v) -> P (DVClos x ys b z ρ d).

  (* introduce views to make proof go through *)
  Inductive is_a_dvalue : dvalue -> Type :=
    | DVPrimIsValue : forall (pv:primval) d, is_a_dvalue (DVPrim pv d)
    | DVAddrIsValue : forall (a:address) d, is_a_dvalue (DVAddr a d)
    | DVClosIsValue : forall x ys b z ρ d, is_a_denv ρ -> is_a_dvalue (DVClos x ys b z ρ d)
  with is_a_denv : env name dvalue -> Type :=
    | NilIsDEnv : is_a_denv nil
    | ConsIsDEnv : forall x v ρ, is_a_dvalue v -> is_a_denv ρ -> is_a_denv ((x,v)::ρ).

  Scheme is_a_dvalue_env_rect := Induction for is_a_dvalue Sort Type
    with is_a_denv_value_rect := Induction for is_a_denv Sort Type.

  Definition is_dvalue_env_mutrect (P: forall v, is_a_dvalue v -> Type)
                                   (Q: forall e, is_a_denv e -> Type)
                                   (H1: forall (pv:primval) d, P (DVPrim pv d) (DVPrimIsValue pv d))
                                   (H2: forall (a:address) d, P (DVAddr a d) (DVAddrIsValue a d))
                                   (H3 : forall x ys b z ρ d (H : is_a_denv ρ),
                                     Q ρ H -> P (DVClos x ys b z ρ d) (DVClosIsValue x ys b z d H))
                                   (H4 : Q nil NilIsDEnv)
                                   (H5 : forall x v ρ (H : is_a_dvalue v),
                                     P v H -> forall H' : is_a_denv ρ, Q ρ H' -> Q ((x, v) :: ρ) (ConsIsDEnv x H H')) :=
     (is_a_dvalue_env_rect P Q H1 H2 H3 H4 H5,
      is_a_denv_value_rect P Q H1 H2 H3 H4 H5).

  (* prove soundness of view *)
  Lemma every_dvalue_is_a_dvalue : forall v, is_a_dvalue v.
  Proof.
    fix 1; destruct v.
      constructor.
      
      constructor.

      constructor.
      induction ρ.
        constructor.

        destruct a as (x,v).
        constructor.
          apply every_dvalue_is_a_dvalue.

          apply IHρ.
  Qed.

  Lemma better_dvalue_ind : forall v, P v.
  Proof.
    assert (K : (forall v (H:is_a_dvalue v), (fun _ => P v) H) *
                (forall ρ (H:is_a_denv ρ),  (fun _ => forall x v, lookup ρ x = Some v -> P v) H)).
    apply (is_dvalue_env_mutrect (fun v _ => P v) (fun ρ _ => forall x v, lookup ρ x = Some v -> P v)).
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
    auto using every_dvalue_is_a_dvalue.
  Qed.
End BetterDValueInd.

(** instrumented records **)
Record drecord := DRecord {
  bindings :> env name dvalue;
  complete : det (** Det means closed, Indet means open **)
}.

(** instrumented heaps **)
Definition dheap := address -> option drecord.

(** instrumented trace events **)
Inductive devent :=
  | DEVarWrite : name -> dvalue -> devent
  | DEPropWrite : address -> det -> name -> det -> dvalue -> devent
  | DECond : dvalue -> devent -> devent
  | DECall : dvalue -> env name dvalue -> devent -> det -> devent
  | DESkip : devent
  | DESeq : devent -> devent -> devent.

(** record lookup **)
Definition drecord_lookup (dr:drecord) (x:name) :=
  match lookup dr x with
  | Some dv => dv
  | None => DVPrim undefined dr.(complete)
  end.

(** record update **)
Definition drecord_update (dr:drecord) (p:name) (dv:dvalue) :=
  DRecord (update dr.(bindings) p dv) dr.(complete).

(** extracting the determinacy flag from an instrumented value **)
Definition get_det dv :=
  match dv with
  | DVPrim _ d => d
  | DVAddr _ d => d
  | DVClos _ _ _ _ _ d => d
  end.

(* some simple results *)
Lemma drecord_update_lookup_same : forall dr p dv, drecord_lookup (drecord_update dr p dv) p = dv.
Proof.
  intros (b, c) p dv.
  unfold drecord_update.
  unfold drecord_lookup.
  unfold bindings.
  rewrite update_lookup_same.
  trivial.
Qed.

Lemma drecord_update_lookup_different : forall dr p p' dv, p <> p' -> 
  drecord_lookup (drecord_update dr p dv) p' = drecord_lookup dr p'.
Proof.
  intros (b, c) p p' dv K.
  unfold drecord_update.
  unfold drecord_lookup.
  unfold bindings.
  rewrite update_lookup_different; auto.
Qed.


