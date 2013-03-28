(** Modelling relationship between instrumented and concrete values **)
Set Implicit Arguments.

Require Import Common Eq FinMap InstrumentedValues Parameters Values Wf.

(** helper functions to strip off determinacy annotations **)
Fixpoint strip_v dv :=
  match dv with
  | DVPrim pv _ => VPrim pv
  | DVAddr a _ => VAddr a
  | DVClos x ys b z dρ _ => VClos x ys b z (map (fun (b:name*dvalue) => let (x, dv) := b in (x, strip_v dv)) dρ)
  end.

Definition strip_env (dρ:env name dvalue) : env name value :=
  map (fun (b:name*dvalue) => let (x, dv) := b in (x, strip_v dv)) dρ.

Definition strip_r (dr:drecord) : record := strip_env dr.(bindings).

Definition strip_h (dh:dheap) : heap := fun a => option_map strip_r (dh a).

Fixpoint strip_evt (de:devent) : event :=
  match de with
  | DEVarWrite x dv => EVarWrite x (strip_v dv)
  | DEPropWrite a _ p _ dv => EPropWrite a p (strip_v dv)
  | DECond dv de => ECond (strip_v dv) (strip_evt de)
  | DECall dv dρ de _ => ECall (strip_v dv) (strip_env dρ) (strip_evt de)
  | DESkip => ESkip
  | DESeq de₁ de₂ => ESeq (strip_evt de₁) (strip_evt de₂)
  end.

(* modelling *)
Section Modelling.
  Variable μ : address -> address.

  Inductive models_v : dvalue -> value -> Prop :=
  | MVPrimIndet : forall pv v, models_v (DVPrim pv Indet) v
  | MVAddrIndet : forall a v, models_v (DVAddr a Indet) v
  | MVClosIndet : forall x ys b z dρ v, models_v (DVClos x ys b z dρ Indet) v
  | MVPrimDet : forall pv, models_v (DVPrim pv Det) pv
  | MVAddrDet : forall a, models_v (DVAddr (μ a) Det) a
  | MVClosDet : forall x ys b z ρ dρ, models_env dρ ρ -> models_v (DVClos x ys b z dρ Det) (VClos x ys b z ρ)
  with models_env : env name dvalue -> env name value -> Prop :=
  | MEnv : forall dρ ρ, (forall x v, lookup ρ x = Some v -> exists dv, lookup dρ x = Some dv /\ models_v dv v) -> 
    models_env dρ ρ.

  Inductive models_r : drecord -> record -> Prop :=
  | MRecord : forall (dr:drecord) (r:record), (forall x, models_v (drecord_lookup dr x) (record_lookup r x)) -> models_r dr r.

  Inductive models_h : dheap -> heap -> Prop :=
  | MHeap : forall (dh:dheap) (h:heap), (forall a r, h a = Some r -> exists dr, dh (μ a) = Some dr /\ models_r dr r) -> models_h dh h.

  Inductive models_evt : devent -> event -> Prop :=
  | MEVarWrite : forall x dv v, models_v dv v -> models_evt (DEVarWrite x dv) (EVarWrite x v)
  | MEPropWrite : forall (a a':address) d₁ (pv pv':primval) d₂ dv v, models_v (DVAddr a d₁) a' -> models_v (DVPrim pv d₂) pv' -> models_v dv v -> models_evt (DEPropWrite a d₁ (tostring pv) d₂ dv) (EPropWrite a' (tostring pv') v)
  | MECall₁ : forall dv v dρ ρ de e, models_v dv v -> models_evt (DECall dv dρ de Indet) (ECall v ρ e)
  | MECall₂ : forall dv v dρ ρ de e, models_v dv v -> models_env dρ ρ -> models_evt de e -> models_evt (DECall dv dρ de Det) (ECall v ρ e)
  | MECond₁ : forall dv de v e, models_v dv v -> models_evt de e -> models_evt (DECond dv de) (ECond v e)
  | MECond₂ : forall dv de v e, get_det dv = Indet -> models_evt (DECond dv de) (ECond v e)
  | MESkip : models_evt DESkip ESkip
  | MESeq : forall de₁ de₂ e₁ e₂, models_evt de₁ e₁ -> models_evt de₂ e₂ -> models_evt (DESeq de₁ de₂) (ESeq e₁ e₂).

  (** results on how to extend environments, records and heaps while keeping the modelling relation intact **)

  (** Lemma 5 **)
  Lemma models_env_ext : forall dρ ρ x dv v, models_env dρ ρ -> models_v dv v -> models_env (update dρ x dv) (update ρ x v).
  Proof.
    intros dρ ρ x dv v K1 K2.
    destruct K1.
    constructor.
    intros x' v' K3.
    simpl in *.
    destruct (x' == x).
      inversion K3; subst.
      solve [eauto].

      solve [auto].
  Qed.

  Lemma models_r_ext : forall dr r x dv v, models_r dr r -> models_v dv v -> models_r (drecord_update dr x dv) (update r x v).
  Proof.
    destruct 1.
    intro K.
    constructor.
    intro x'.
    unfold drecord_update; unfold drecord_lookup in *; unfold record_lookup in *; simpl.
    destruct (x' == x); auto.
  Qed.

  (** Lemma 6 **)
  Lemma models_h_ext : forall dh h a dr r, models_h dh h -> models_r dr r -> injective μ (dom h ∪ Just a) ->
    models_h (fupdate dh (μ a) (Some dr)) (fupdate h a (Some r)).
  Proof.
    destruct 1.
    constructor.
    intros a' r'.
    unfold fupdate.
    destruct (a' == a); subst.
      inversion 1; subst.
      erewrite if_eq; solve [eauto].

      intro K1.
      assert (μ a' <> μ a).
        contradict n.
        apply H1; auto.
          left; solve [eauto using dom].

          right; unfold Just; solve [auto].
      rewrite if_neq; eauto.
  Qed.

  (** looking up preserves modelling **)
  Lemma models_env_lookup : forall dρ ρ x dv v, models_env dρ ρ -> lookup dρ x = Some dv -> lookup ρ x = Some v -> models_v dv v.
  Proof.
    destruct 1; intros.
    edestruct H as (?&?&?); eauto.
    congruence.
  Qed.

  Lemma models_heap_lookup : forall dh h a dr r, models_h dh h -> dh (μ a) = Some dr -> h a = Some r -> models_r dr r.
  Proof.
    destruct 1; intros.
    edestruct H as (?&?&?); eauto.
    congruence.
  Qed.
End Modelling.
Hint Constructors models_v models_evt.
Hint Resolve models_env_ext models_env_lookup models_heap_lookup.

(** extending a heap with a fresh record doesn't impact modelling **)
Lemma update_h_fresh : forall μ dh h a,
  models_h μ dh h -> ~a ∈ dom dh -> models_h μ (fupdate dh a (Some (DRecord nil Det))) h.
Proof.
  constructor.
  intros a' r' K.
  unfold fupdate.
  inversion H; subst.
  edestruct H1 as (?&?&?); eauto.
  destruct (μ a' == a); subst; eauto.
  contradict H0; eauto using dom.
Qed.

(* Lemma 2: when mu is extended, the modelling relations still hold as long as the involved elements
   are well-formed *)
Section MuAgreement.
  Variable μ μ' : address -> address.
  Variable h : heap.
  Hypothesis HAgree : agree μ μ' (dom h).

  Lemma mu_agreement_v : forall dv v, models_v μ dv v -> wf_v h v -> models_v μ' dv v.
  Proof.
    intros dv v.
    revert dv.
    induction v using better_value_ind.
      inversion 1; subst; solve [eauto].

      inversion 1; subst; eauto.
      inversion 1; subst.
      rewrite HAgree; solve [eauto using dom].

      inversion 1; subst; eauto.
      constructor.
      constructor.
      intros.
      destruct H3.
      edestruct H3 as (dv&?&?); eauto.
      exists dv.
      constructor; auto.
      eapply H; eauto.
      inversion H1; subst.
      destruct H7.
      eauto.
  Qed.

  Lemma mu_agreement_e : forall dρ ρ, models_env μ dρ ρ -> wf_env h ρ -> models_env μ' dρ ρ.
  Proof.
    destruct 1.
    destruct 1.
    constructor.
    intros.
    edestruct H as (dv&?&?); eauto.
    exists dv.
    constructor; auto.
    apply mu_agreement_v; eauto.
  Qed.

  Lemma mu_agreement_r : forall dr r, models_r μ dr r -> wf_env h r -> models_r μ' dr r.
  Proof.
    destruct 1.
    destruct 1.
    constructor.
    intro x.
    apply mu_agreement_v; auto.
    remember (lookup ρ x) as rx.
    unfold record_lookup.
    destruct rx.
      rewrite <- Heqrx.
      solve [eauto].

      rewrite <- Heqrx.
      constructor.
  Qed.

  Lemma mu_agreement_evt : forall de e, models_evt μ de e -> wf_evt h e -> models_evt μ' de e.
  Proof.
    induction 1; solve [inversion 1; subst; auto using mu_agreement_v, mu_agreement_e].
  Qed.
End MuAgreement.

Lemma mu_agreement_h : forall h μ μ', agree μ μ' (dom h) -> forall dh, models_h μ dh h -> wf_h h -> models_h μ' dh h.
Proof.
  destruct 2.
  destruct 1.
  constructor.
  intros a r K1.
  destruct (H0 _ _ K1) as (dr&K2&K3).
  assert (K4 : a ∈ dom h) by eauto using dom.
  rewrite (H _ K4) in K2.
  exists dr.
  constructor; auto.
  eauto using mu_agreement_r.
Qed.

(* truthiness of determinate values *)
Lemma truthy_strip : forall μ dv v, models_v μ dv v -> get_det dv = Det -> (truthy (strip_v dv) <-> truthy v).
Proof.
  destruct 1; simpl; inversion 1; intuition (constructor).
Qed.
