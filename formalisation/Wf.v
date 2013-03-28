(** well-formedness relations ensuring that there are no dangling references **)
Set Implicit Arguments.

Require Import Eq Common FinMap Parameters Values.

Section Wellformedness.
  Variable h : heap.

  Inductive wf_v : value -> Prop :=
    | WfPrim : forall (pv:primval), wf_v pv
    | WfAddr : forall a r, h a = Some r -> wf_v a
    | WfClos : forall x ys b z ρ, wf_env ρ -> wf_v (VClos x ys b z ρ)
  with wf_env : env name value -> Prop :=
    | WfEnv : forall (ρ:env name value), (forall x v, lookup ρ x = Some v -> wf_v v) -> wf_env ρ.

  Inductive wf_h :=
    | WfHeap : (forall a r, h a = Some r -> wf_env r) -> wf_h.

  (* auxiliary predicate expressing that both heap and environment are well-defined *)
  Inductive wf : env name value -> Prop :=
    | Wf : forall ρ, wf_h -> wf_env ρ -> wf ρ.

  Inductive wf_evt : event -> Prop :=
    | WfVarWrite : forall x v, wf_v v -> wf_evt (EVarWrite x v)
    | WfPropWrite : forall (a:address) p v, wf_v a -> wf_v v -> wf_evt (EPropWrite a p v)
    | WfCond : forall v e, wf_v v -> wf_evt e -> wf_evt (ECond v e)
    | WfCall : forall v ρ e, wf_v v -> wf_env ρ -> wf_evt e -> wf_evt (ECall v ρ e)
    | WfSkip : wf_evt ESkip
    | WfSeq : forall e₁ e₂, wf_evt e₁ -> wf_evt e₂ -> wf_evt (ESeq e₁ e₂).

  Lemma wf_empty_env : wf_env nil.
  Proof.
    constructor.
    inversion 1.
  Qed.

  Lemma wf_env_update : forall ρ x v, wf_env ρ -> wf_v v -> wf_env (update ρ x v).
  Proof.
    destruct 1.
    constructor.
    intros x' v'.
    simpl.
    destruct (x' == x); eauto.
    congruence.
  Qed.
End Wellformedness.
Hint Constructors wf_v wf_evt.
Hint Resolve wf_env_update wf_empty_env.

(* some basic results: well-formedness is preserved when the heap grows *)
Lemma wf_v_heap_update : forall (h h':heap) v, wf_v h v -> dom h ⊆ dom h' -> wf_v h' v.
Proof.
  induction v using better_value_ind; auto.
    intros K1 K2.
    assert (a ∈ dom h).
      inversion K1; subst.
      solve [eauto using dom].
    generalize (K2 a H).
    inversion 1; subst.
    solve [eauto].

    constructor.
    constructor.
    inversion H0; subst.
    inversion H3; subst.
    eauto.
Qed.
  
Lemma wf_env_heap_update : forall h h' ρ, wf_env h ρ -> dom h ⊆ dom h' -> wf_env h' ρ.
Proof.
  destruct 1.
  constructor.
  intros.
  eapply wf_v_heap_update; eauto.
Qed.

Lemma wf_evt_heap_update : forall h h' e, wf_evt h e -> dom h ⊆ dom h' -> wf_evt h' e.
Proof.
  induction 1; eauto using wf_v_heap_update, wf_env_heap_update.
Qed.

(** extending the heap with a well-formed record yields a well-formed heap **)
Lemma wf_h_update : forall h a r, wf_h h -> wf_env h r -> wf_h (fupdate h a (Some r)).
Proof.
  constructor.
  intros a' r'.
  unfold fupdate.
  destruct (a' == a); subst.
    inversion 1; subst.
    apply wf_env_heap_update with (h:=h); auto.
    solve [apply dom_fupdate_subset].
    
    intro K.
    destruct H.
    apply wf_env_heap_update with (h:=h).
      solve [eauto].

      solve [apply dom_fupdate_subset].
Qed.

(** looking up a variable in a well-formed record gives a well-formed value **)
Lemma wf_record_lookup : forall h (r:record), wf_env h r -> forall x v, record_lookup r x = v -> wf_v h v.
Proof.
  destruct 1.
  intros x v.
  unfold record_lookup.
  remember (lookup ρ x) as ρx.
  destruct ρx; intro; subst; eauto.
Qed.
Hint Resolve wf_record_lookup.
