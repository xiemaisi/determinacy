(** This module defines a preorder ≼ expressing that its left operand is ``more determinate''
    than its right one. **)
Set Implicit Arguments.

Require Import Common Eq FinMap InstrumentedValues Modelling.

(** the basic definition for instrumented values; the others are homomorphic extensions **)
Definition det_leq (d₁ d₂:det) := d₁ = d₂ \/ d₂ = Indet.

Instance DetPO : PreOrder det := {
  leq:= det_leq
}.
Proof.
  firstorder (congruence).
  firstorder (congruence).
Defined.

Definition dval_leq (dv₁ dv₂:dvalue) := dv₁ = dv₂ \/ get_det dv₂ = Indet.

Instance DValPO : PreOrder dvalue := {
  leq := dval_leq
}.
Proof.
  firstorder.
  
  intros dv₁ dv₂ dv₃.
  destruct 1; subst.
    destruct 1; subst; firstorder.

    destruct 1; subst; firstorder.
Defined.

Definition denv_leq (ρ₁ ρ₂:env name dvalue) : Prop :=
  forall x dv₁, lookup ρ₁ x = Some dv₁ -> exists dv₂, lookup ρ₂ x = Some dv₂ /\ dv₁ ≼ dv₂.

Instance DEnvPO : PreOrder (env name dvalue) := {
  leq := denv_leq
}.
Proof.
  intros ρ x dv K.
  exists dv.
  constructor; auto.
  apply leq_refl.

  intros ρ₁ ρ₂ ρ₃ K₁ K₂ x dv₁ K₃.
  edestruct K₁ as (dv₂&?&?); eauto.
  edestruct K₂ as (dv₃&?&?); eauto.
  exists dv₃.
  constructor; auto.
  eapply leq_trans; eauto.
Defined.

Definition drecord_leq (dr₁ dr₂: drecord) : Prop :=
  forall x, drecord_lookup dr₁ x ≼ drecord_lookup dr₂ x.

Instance DRecordPO : PreOrder drecord := {
  leq := drecord_leq
}.
Proof.
  intros a p.
  apply leq_refl.

  intros dr₁ dr₂ dr₃ K₁ K₂ a.
  eapply leq_trans; eauto.
Defined.
    
Definition dheap_leq (h₁ h₂:dheap) : Prop :=
  forall x dr₁, h₁ x = Some dr₁ -> exists dr₂, h₂ x = Some dr₂ /\ dr₁ ≼ dr₂.

Instance DHeapPO : PreOrder dheap := {
  leq := dheap_leq
}.
Proof.
  intros dh x dr₁ K₁.
  exists dr₁.
  constructor; auto.
  apply leq_refl.

  intros dh₁ dh₂ dh₃ K₁ K₂ x dr₁ K₃.
  edestruct K₁ as (dr₂&?&?); eauto.
  edestruct K₂ as (dr₃&?&?); eauto.
  exists dr₃.
  constructor; auto.
  eapply leq_trans; eauto.
Defined.

(* Show that ⊧ is monotonic wrt ≼ in its first argument. *)
Lemma models_v_mon : forall dv₁ μ v, models_v μ dv₁ v -> forall dv₂, dv₁ ≼ dv₂ ->  models_v μ dv₂ v.
Proof.
  destruct 2; subst; auto.
  destruct dv₂; simpl in H0; rewrite H0; constructor.
Qed.     

Lemma models_env_mon : forall μ dρ₁ dρ₂ ρ, models_env μ dρ₁ ρ -> dρ₁ ≼ dρ₂ -> models_env μ dρ₂ ρ.
Proof.
  destruct 1.
  constructor.
  intros x v K₁.
  edestruct H as (dv&?&?); eauto.
  edestruct H0 as (dv'&?&?); eauto.
  exists dv'.
  constructor; auto.
  eauto using models_v_mon.
Qed.

Lemma models_rec_mon : forall μ dr₁ dr₂ r, models_r μ dr₁ r -> dr₁ ≼ dr₂ -> models_r μ dr₂ r.
Proof.
  destruct 1.
  constructor.
  intro x.
  unfold leq in H0; simpl in H0.
  unfold drecord_leq in H0.
  eauto using models_v_mon.
Qed.

Lemma models_h_mon : forall μ dh₁ dh₂ h, models_h μ dh₁ h -> dh₁ ≼ dh₂ -> models_h μ dh₂ h.
Proof.
  destruct 1.
  constructor.
  intros a r K.
  edestruct H as (dr&?&?); eauto.
  edestruct H0 as (dr'&?&?); eauto.
  eauto using models_rec_mon.
Qed.
