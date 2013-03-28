(** Definition of the clobbering operators \hat{\rho}[V:=\hat{\rho}^d] and \hat{h}[A:=\hat{h}^d]. 
    This is the case where some names/properties are possibly marked indeterminate, but their values 
    stay the same. See Reverting.v for the case where their values are reset as well. **)
Set Implicit Arguments.

Require Import Common Eq Parameters Discharging FinMap InstrumentedValues Modelling DeterminacyOrder Substruct.

(** clobbering operator for environments **)
Fixpoint clobber_names xs (dρ: env name dvalue) :=
  match xs with
  | nil => dρ
  | x::xs => update (clobber_names xs dρ) x (match lookup dρ x with
                                             | Some dv => discharge dv Indet
                                             | _ => DVPrim undefined Indet
                                             end)
  end.

Definition discharge_names dρ xs d :=
  match d with
  | Det => dρ
  | Indet => clobber_names xs dρ
  end.

(** clobbering operator for records **)
Definition clobber_prop p dr :=
  match lookup dr.(bindings) p with
  | Some dv => drecord_update dr p (discharge dv Indet)
  | None => dr
  end.

(** the clobbering operator for heaps takes an instrumented event rather than a set
    of address-property name pairs as in the paper; this is more convenient to do in Coq **)
Fixpoint clobber_evt_h de (dh:dheap) : dheap :=
  match de with
  | DEPropWrite a _ p _ dv => (fun a' => if a' == a then
                                           option_map (clobber_prop p) (dh a)
                                         else
                                           dh a')
  | DECond _ de => clobber_evt_h de dh
  | DECall _ _ de _ => clobber_evt_h de dh
  | DESeq de₁ de₂ => clobber_evt_h de₁ (clobber_evt_h de₂ dh)
  | _ => dh
  end.

Definition discharge_evt_h dh de d :=
  match d with
  | Det => dh
  | Indet => clobber_evt_h de dh
  end.

(** auxiliary results **)
Lemma dom_clobber_evt_h : forall de dh, dom dh ≡ dom (clobber_evt_h de dh).
Proof.
  induction de; simpl; auto using coext_refl.
    constructor.
      destruct 1.
      destruct (a0 == a); subst.
        rewrite H.
        apply Dom with (b := clobber_prop n b).
        erewrite if_eq; eauto.

        apply Dom with (b := b).
        erewrite if_neq; eauto.

      inversion 1; subst.
      destruct (a0 == a); subst; eauto using Dom.
      remember (dh a) as dha.
      destruct dha; eauto using Dom.
      inversion H0.

    constructor; intro H.
      edestruct IHde2; edestruct IHde1; eauto.

      edestruct IHde2; edestruct IHde1; eauto.
Qed.

Lemma dom_discharge_evt_h : forall de dh d, dom dh ≡ dom (discharge_evt_h dh de d).
Proof.
  destruct d; simpl; auto using coext_refl, dom_clobber_evt_h.
Qed.

Lemma clobber_names_app : forall xs ys dρ,
  clobber_names (xs ++ ys) dρ = clobber_names xs (clobber_names ys dρ).
Proof.
  induction xs; simpl clobber_names; auto.
  intros ys dρ.
  rewrite IHxs.
  f_equal.
  clear.
  induction ys; simpl; auto.
  destruct (a == a0); subst; auto.
  destruct (lookup dρ a0); auto.
  destruct d; auto.
Qed.

Lemma substruct_clobber_update : forall dr p dv,
  substruct_r dr (clobber_prop p (drecord_update dr p dv)).
Proof.
  intros dr p dv q dv' K.
  unfold drecord_update.
  unfold clobber_prop.
  simpl bindings.
  erewrite if_eq; eauto.
  destruct (q == p); subst; simpl.
    erewrite if_eq; eauto.

    erewrite if_neq; eauto.
    erewrite if_neq; eauto.
Qed.

(** looking up names in clobbered environments **)
Lemma clobber_names_lookup_clobbered : forall xs x dρ, In x xs ->
  lookup (clobber_names xs dρ) x = Some (discharge (match lookup dρ x with Some dv => dv | _ => DVPrim undefined Det end) Indet).
Proof.
  induction xs.
    solve [inversion 1].

    intros x dρ.
    destruct (a == x); subst.
      simpl; intros _.
      erewrite if_eq; eauto.
      destruct (lookup dρ x); eauto.

      inversion 1; subst.
        solve [intuition].

        simpl.
        erewrite if_neq; eauto.
Qed.

Lemma clobber_names_lookup_not_clobbered : forall xs x dρ, ~In x xs -> lookup (clobber_names xs dρ) x = lookup dρ x.
Proof.
  induction xs; simpl; auto.
  intros x dρ K.
  destruct (lookup dρ a); simpl; erewrite if_neq; eauto.
Qed.

(** compatibility with modelling **)
Lemma models_env_clobber_names_monotonic : forall xs μ dρ ρ, models_env μ (clobber_names xs dρ) ρ ->
  forall xs', incl xs xs' -> models_env μ (clobber_names xs' dρ) ρ.
Proof.
  constructor.
  intros x v K.
  inversion H; subst.
  edestruct H1 as (dv&?&?); eauto; clear H1.
  destruct (In_dec x xs').
    erewrite clobber_names_lookup_clobbered; eauto using models_v_clobber.

    destruct (In_dec x xs).
      contradict n; auto.

      erewrite clobber_names_lookup_not_clobbered; eauto.
      erewrite clobber_names_lookup_not_clobbered in H2; eauto.
Qed.    

Lemma models_env_clobber_names : forall xs μ dρ ρ, models_env μ dρ ρ -> models_env μ (clobber_names xs dρ) ρ.
Proof.
  intros.
  apply models_env_clobber_names_monotonic with (xs:=nil); simpl; auto.
  intro K.
  inversion 1.
Qed.

Lemma models_env_discharge_names : forall μ dρ ρ xs d, models_env μ dρ ρ -> models_env μ (discharge_names dρ xs d) ρ.
Proof.
  destruct d; simpl; auto using models_env_clobber_names.
Qed.

Lemma models_r_clobber_evt : forall μ p dr r, models_r μ dr r -> models_r μ (clobber_prop p dr) r.
Proof.
  constructor.
  intro x; unfold clobber_prop; simpl.
  destruct H.
  remember (lookup dr p) as drp.
  destruct drp; auto.
  destruct (x == p); subst.
    rewrite drecord_update_lookup_same.
    apply models_v_clobber.

    rewrite drecord_update_lookup_different; auto.
Qed.
        
Lemma models_h_clobber_evt : forall de μ dh h, models_h μ dh h -> models_h μ (clobber_evt_h de dh) h.
Proof.
  induction de; simpl; auto.
  constructor.
  intros a' r K1.
  destruct (μ a' == a).
    destruct H.
    edestruct H as (dr&?&?); eauto.
    rewrite <- e.
    rewrite H0; simpl.
    exists (clobber_prop n dr).
    constructor; auto.
    apply models_r_clobber_evt; solve [auto].

    destruct H; solve [auto].
Qed.

Lemma models_h_discharge_evt : forall μ dh de d h, models_h μ dh h -> models_h μ (discharge_evt_h dh de d) h.
Proof.
  destruct d; simpl; auto using models_h_clobber_evt.
Qed.

(** relationship with the ≼ operator **)
(** Lemma 7 **)
Lemma denv_leq_clobber_names : forall xs dρ, dρ ≼ clobber_names xs dρ.
Proof.
  induction xs; simpl clobber_names; intro dρ.
    apply leq_refl.
  
    intros y dv K.
    unfold update. simpl lookup.
    destruct (y == a); subst.
      rewrite K.
      exists (discharge dv Indet).
      constructor; auto.
      destruct dv; right; auto.

      edestruct IHxs; eauto.
Qed.

Lemma denv_leq_discharge_names : forall dρ xs d, dρ ≼ discharge_names dρ xs d.
Proof.
  destruct d; simpl discharge_names.
    apply leq_refl.

    apply denv_leq_clobber_names.
Qed.

Lemma leq_clobber_names_update : forall dρ x dv,
  dρ ≼ clobber_names (x::nil) (update dρ x dv).
Proof.
  intros dρ x dv x' dv' K.
  simpl.
  destruct (x' == x); subst.
    erewrite if_eq; eauto.
    exists (discharge dv Indet).
    constructor; auto.
    destruct dv; simpl; firstorder.

    rewrite K.
    exists dv'.
    constructor; auto.
    firstorder.
Qed.

Lemma denv_leq_clobber_prop : forall p dr, dr ≼ clobber_prop p dr.
Proof.
  intros.
  unfold clobber_prop.
  intro p'.
  destruct (p' == p); subst.
    unfold drecord_lookup.
    remember (lookup dr.(bindings) p) as drp; destruct drp.
      unfold drecord_update.
      simpl bindings.
      rewrite update_lookup_same.
      destruct d; right; auto.

      rewrite <- Heqdrp.
      apply (@leq_refl dvalue).

    remember (lookup dr.(bindings) p) as drp; destruct drp; auto using (@leq_refl dvalue).
    rewrite drecord_update_lookup_different; auto using (@leq_refl dvalue).
Qed.      

(** Lemma 7 **)
Lemma denv_leq_clobber_evt : forall de dh, dh ≼ clobber_evt_h de dh.
Proof. 
  induction de; simpl clobber_evt_h; auto using (@leq_refl dheap).
    intros dh a' dr K.
    destruct (a' == a); subst.
      rewrite K.
      exists (clobber_prop n dr).
      constructor; auto using denv_leq_clobber_prop.

      exists dr; auto using (@leq_refl drecord).

    eauto using (@leq_trans dheap).
Qed.

(* clobbering is monotonic wrt ≼ *)
Lemma clobber_names_mon : forall xs dρ dρ', dρ ≼ dρ' -> clobber_names xs dρ ≼ clobber_names xs dρ'.
Proof.
  induction xs; simpl clobber_names; auto.
  intros dρ dρ' K.
  remember (lookup dρ a) as dρa.
  destruct dρa.
    edestruct K as (dv'&?&?); eauto.
    rewrite H.
    intros y dv''.
    destruct (y == a); subst.
      rewrite ! update_lookup_same.
      inversion 1; subst.
      exists (discharge dv' Indet).
      constructor; auto.
      destruct dv'; simpl; right; auto.

      rewrite ! update_lookup_different; auto.
      intro K'.
      edestruct IHxs; eauto.

    intros y dv''.
    destruct (y == a); subst.
      rewrite ! update_lookup_same.
      inversion 1; subst.
      destruct (lookup dρ' a).
        exists (discharge d Indet).
        constructor; auto.
        destruct d; simpl; right; auto.

        exists (DVPrim undefined Indet).
        constructor; firstorder.
          
      rewrite ! update_lookup_different; auto.
      intro K'.
      edestruct IHxs; eauto.
Qed.

Lemma drecord_update_leq : forall dr p dv dr' dv',
  dr ≼ dr' -> dv ≼ dv' -> drecord_update dr p dv ≼ drecord_update dr' p dv'.
Proof.
  intros dr p dv dr' dv' K₁ K₂ p'.
  destruct (p' == p); subst.
    rewrite ! drecord_update_lookup_same; auto.

    rewrite ! drecord_update_lookup_different; auto.
Qed.

(** relationship with substructure **)
Lemma clobber_prop_preserves_substruct : forall p dr dr',
  substruct_r dr dr' -> substruct_r (clobber_prop p dr) (clobber_prop p dr').
Proof.
  intros.
  unfold clobber_prop.
  remember (lookup dr.(bindings) p) as drp; destruct drp.
    rename d into dv.
    edestruct H as (dv'&?); eauto.
    rewrite H0.
    apply substruct_r_update; auto.

    destruct (lookup dr'.(bindings) p); auto.
    apply substruct_r_update_r; auto.
Qed.

Lemma clobber_evt_preserves_substruct : forall de dh dh', 
  substruct_h dh dh' -> substruct_h (clobber_evt_h de dh) (clobber_evt_h de dh').
Proof.
  induction de; simpl clobber_evt_h; eauto.
  intros dh dh' K a' dr'.
  destruct (a' == a); subst.
    remember (dh a) as dha; destruct dha; simpl; inversion 1; subst.
    edestruct K as (dr'&?&?); eauto.
    rewrite H0; simpl option_map.
    exists (clobber_prop n dr').
    constructor; auto.
    apply clobber_prop_preserves_substruct; auto.

    eauto.
Qed.

Lemma clobber_prop_mon : forall p dr dr', 
  substruct_r dr dr' -> dr ≼ dr' -> clobber_prop p dr ≼ clobber_prop p dr'.
Proof.
  intros.
  unfold clobber_prop.
  remember (lookup dr.(bindings) p) as drp; destruct drp.
    edestruct H as (dv'&?); eauto.
    rewrite H1.
    apply drecord_update_leq; auto using (@leq_refl drecord).
    destruct dv'; right; auto.

    remember (lookup dr'.(bindings) p) as dr'p; destruct dr'p; auto.
    intros p'.
    destruct (p' == p); subst.
      unfold drecord_lookup.
      rewrite <- Heqdrp.
      unfold drecord_update at 1.
      simpl bindings.
      rewrite update_lookup_same.
      destruct d; right; auto.

      rewrite drecord_update_lookup_different; auto.
Qed.

Lemma clobber_evt_h_mon : forall de dh dh', 
  substruct_h dh dh' -> dh ≼ dh' -> clobber_evt_h de dh ≼ clobber_evt_h de dh'.
Proof.
  induction de; simpl clobber_evt_h; auto.
    intros dh dh' K₁ K₂ a' dr'.
    destruct (a' == a); subst.
      remember (dh a) as dha; destruct dha; inversion 1; subst.
      edestruct K₂ as (dr'&?&?); eauto.
      rewrite H0.
      simpl option_map.
      exists (clobber_prop n dr').
      constructor; auto.
      apply clobber_prop_mon; auto.
      edestruct K₁ as (dr''&?&?); eauto.
      rewrite H0 in H2; inversion H2; subst.
      auto.

      intro K'.
      edestruct K₁ as (dr''&?&?); eauto.

    intros.
    eapply IHde1.
      apply clobber_evt_preserves_substruct; auto.

      eapply IHde2; auto.
Qed.

Lemma total_clobber_substruct : forall p dr, substruct_r (clobber_prop p dr) (DRecord (discharge_env dr.(bindings) Indet) Indet).
Proof.
  intros p dr x dv.
  unfold clobber_prop.
  simpl bindings.
  rewrite discharge_env_lookup.
  destruct (x == p); subst.
    remember (lookup dr.(bindings) p) as drp; destruct drp; simpl.
      erewrite if_eq; eauto.

      congruence.

    destruct (lookup dr.(bindings) p); simpl.
      rewrite if_neq; auto.
      intro K.
      rewrite K; simpl; eauto.

      intro K.
      rewrite K; simpl; eauto.
Qed.
    
Lemma total_clobber : forall p dr, clobber_prop p dr ≼ DRecord (discharge_env dr.(bindings) Indet) Indet.
Proof.
  intros p dr p'.
  unfold drecord_lookup.
  unfold clobber_prop.
  simpl bindings.
  rewrite discharge_env_lookup.
  destruct (p' == p); subst.
    destruct (lookup dr.(bindings) p).
      simpl lookup. simpl option_map.
      erewrite if_eq; eauto using (@leq_refl dvalue).

      simpl option_map. simpl complete.
      right; auto.

    destruct (lookup dr.(bindings) p).
      simpl lookup.
      rewrite if_neq; auto.
      destruct (lookup dr.(bindings) p').
        right; simpl; destruct d0; auto.
        
        right; auto.

      destruct (lookup dr.(bindings) p').
        right; simpl; destruct d; auto.

        right; auto.
Qed.

Lemma leq_clobber_update : forall dr p dv,
  dr ≼ clobber_prop p (drecord_update dr p dv).
Proof.
  intros dr p dv q.
  unfold drecord_update.
  unfold clobber_prop.
  simpl bindings.
  rewrite update_lookup_same.
  destruct (q == p); subst.
    rewrite drecord_update_lookup_same.
    destruct dv; right; auto.

    rewrite drecord_update_lookup_different; auto.
    unfold drecord_lookup.
    simpl bindings.
    simpl complete.
    rewrite update_lookup_different; auto using (@leq_refl dvalue).
Qed.

