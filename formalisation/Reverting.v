(** Definition of the reverting operators \hat{\rho}'[V:=\hat{\rho}^?] and \hat{h}'[A:=\hat{h}^?]. 
    This is the case where some names/properties are marked indeterminate, and their values are reset.
    See Clobbering.v for the case where their values are not reset. **)

Set Implicit Arguments.

Require Import Common Eq Parameters Discharging FinMap InstrumentedValues Modelling DeterminacyOrder Clobbering Substruct.

Fixpoint revert_names xs (dρ dρ': env name dvalue) :=
  match xs with
  | nil => dρ
  | x::xs => update (revert_names xs dρ dρ') x (match lookup dρ' x with
                                                | Some dv => discharge dv Indet
                                                | _ => DVPrim undefined Indet
                                                end)
  end.

Definition revert_prop p dr dr' :=
  match lookup dr.(bindings) p with
  | Some dv =>
    match lookup dr'.(bindings) p with
    | Some dv' => drecord_update dr p (discharge dv' Indet)
    | None => DRecord (update dr.(bindings) p (DVPrim undefined Indet)) Indet (* if the property didn't exist in the previous record, remove it and make the record indeterminate *)
    end
  | _ => dr
  end.

Fixpoint revert_evt_h de (dh dh':dheap) : dheap :=
  match de with
  | DEPropWrite a _ p _ dv => (fun a' => if a' == a then
                                           (match dh a with
                                            | Some dr =>
                                              (match dh' a with
                                               | Some dr' => Some (revert_prop p dr dr')
                                               | None => Some (DRecord (discharge_env dr.(bindings) Indet) Indet)
                                               end)
                                            | None => None
                                            end)
                                         else
                                           dh a')
  | DECond _ de => revert_evt_h de dh dh'
  | DECall _ _ de _ => revert_evt_h de dh dh'
  | DESeq de₁ de₂ => revert_evt_h de₁ (revert_evt_h de₂ dh dh') dh'
  | _ => dh
  end.

(** simple results **)
Lemma dom_revert_evt_h₁ : forall de dh dh', dom dh ≡ dom (revert_evt_h de dh dh').
Proof.
  induction de; simpl; eauto using coext_refl.
    intros dh dh' a'.
    constructor.
      destruct 1.
      destruct (a0 == a); subst.
        rewrite H.
        destruct (dh' a); eauto using dom, if_eq.

        exists b.
        rewrite if_neq; auto.

      inversion 1; subst.
      destruct (a' == a); subst; eauto using dom.
      remember (dh a) as dha; destruct dha.
        exists d2; eauto using dom.

        inversion H0.

    constructor; intros.
      apply IHde1.
      apply IHde2; auto.

      eapply IHde2.
      eapply IHde1; eauto.
Qed.

Lemma dom_revert_evt_h₂ : forall de dh dh', dom dh ⊆ dom dh' -> dom dh ⊆ dom (revert_evt_h de dh' dh).
Proof.
  induction de; simpl; auto using subset_refl.
  intros dh dh' K₁ a' K₂.
  specialize (K₁ a' K₂).
  destruct K₁.
  destruct K₂.
  destruct (a0 == a); subst.
    rewrite H; simpl.
    rewrite H0; simpl.
    exists (revert_prop n b b0).
    erewrite if_eq; eauto.

    exists b.
    erewrite if_neq; eauto.
Qed.

(** relationship with clobbering **)
Lemma clobber_names_leq_revert_names : forall xs dρ dρ', clobber_names xs dρ' ≼ revert_names xs dρ' dρ.
Proof.
  induction xs; simpl clobber_names; simpl revert_names; auto using (@leq_refl (env name dvalue)).
  intros dρ dρ' x dv.
  destruct (a == x); subst.
    rewrite ! update_lookup_same.
    remember (lookup dρ' x) as dρ'x.
    destruct dρ'x.
      inversion 1; subst.
      remember (lookup dρ x) as dρx.
      destruct dρx.
        exists (discharge d0 Indet).
        constructor; auto.
        destruct d0; right; auto.

        exists (DVPrim undefined Indet).
        constructor; auto.
        right; auto.

      inversion 1; subst.
      destruct (lookup dρ x).
        exists (discharge d Indet).
        constructor; auto.
        destruct d; right; auto.

        exists (DVPrim undefined Indet).
        constructor; auto.
        right; auto.

    rewrite ! update_lookup_different; auto.
    intro K.
    edestruct IHxs; eauto.
Qed.

Lemma clobber_prop_leq_revert_prop : forall p dr dr',
  clobber_prop p dr ≼ revert_prop p dr dr'.
Proof.
  intros.
  unfold clobber_prop.
  unfold revert_prop.
  destruct (lookup dr.(bindings) p); auto using (@leq_refl drecord).
  destruct (lookup dr'.(bindings) p).
    intros p'.
    destruct (p' == p); subst.
      rewrite ! drecord_update_lookup_same.
      destruct d0; right; auto.

      rewrite ! drecord_update_lookup_different; auto using (@leq_refl dvalue).

    intros p'.
    unfold drecord_lookup.
    simpl bindings.
    destruct (p' == p); subst.
      rewrite ! update_lookup_same.
      right; auto.

      rewrite ! update_lookup_different; auto.
      destruct (lookup dr.(bindings) p'); auto using (@leq_refl dvalue).
      right; auto.
Qed.

Lemma clobber_prop_substruct_revert_prop : forall p dr dr',
  substruct_r (clobber_prop p dr) (revert_prop p dr dr').
Proof.
  intros p dr dr' p' dv'.
  unfold clobber_prop; unfold revert_prop.
  destruct (lookup dr.(bindings) p); simpl; eauto.
  destruct (p' == p); subst.
    inversion 1; subst.
    destruct (lookup dr'.(bindings) p); simpl; erewrite if_eq; eauto.

    destruct (lookup dr'.(bindings) p); simpl; rewrite if_neq; eauto.
Qed.

Lemma substruct_revert_substruct_r : forall p dr dr' dr'',
  substruct_r dr dr' -> substruct_r (revert_prop p dr dr'') (revert_prop p dr' dr'').
Proof.
  intros p dr dr' dr'' K q dv.
  unfold revert_prop.
  remember (lookup dr.(bindings) p) as drp; destruct drp; subst.
    edestruct K as (dv'&K'); eauto.
    rewrite K'.
    destruct (lookup dr''.(bindings) p).
      destruct (q == p); subst; simpl.
        erewrite ! if_eq; eauto.

        erewrite ! if_neq; eauto.

      simpl bindings.
      destruct (q == p); subst; simpl.
        erewrite ! if_eq; eauto.

        erewrite ! if_neq; eauto.

    intro K'.
    assert (p <> q) by congruence.
    edestruct K as (dv'&K''); eauto.
    remember (lookup dr'.(bindings) p) as dr'p; destruct dr'p; eauto.
    destruct (lookup dr''.(bindings) p); simpl.
      rewrite if_neq; eauto.

      rewrite if_neq; eauto.
Qed.

Lemma substruct_revert_substruct_h : forall de dh dh' dh'',
  substruct_h dh dh' -> substruct_h (revert_evt_h de dh dh'') (revert_evt_h de dh' dh'').
Proof.
  induction de; simpl revert_evt_h; auto.
  intros dh dh' dh'' K₁ a' dr'.
  destruct (a' == a); subst.
    remember (dh a) as dha; destruct dha; simpl.
      edestruct K₁ as (dr''&K₂&K₃); eauto.
      rewrite K₂.
      destruct (dh'' a); inversion 1; subst.
        exists (revert_prop n dr'' d3).
        constructor; auto.
        apply substruct_revert_substruct_r; auto.

        exists (DRecord (discharge_env dr'' Indet) Indet).
        constructor; auto.
        intros p dv.
        simpl bindings.
        rewrite ! discharge_env_lookup.
        remember (lookup d2.(bindings) p) as d2p; destruct d2p; simpl; inversion 1; subst.
        edestruct K₃ as (dv'&K₄); eauto.
        rewrite K₄; simpl; eauto.

      inversion 1.

    eauto using substruct_r_refl.
Qed.

Lemma clobber_evt_substruct_revert_evt : forall de dh dh',
  substruct_h (clobber_evt_h de dh') (revert_evt_h de dh' dh).
Proof.
  induction de; try (solve [simpl clobber_evt_h; simpl revert_evt_h; auto using (@leq_refl dheap), substruct_h_refl]).
    simpl.
    intros dh dh' a' dr'.
    destruct (a' == a); subst.
      destruct (dh' a); inversion 1; subst.
      destruct (dh a).
        exists (revert_prop n d2 d3).
        constructor; auto.
        apply clobber_prop_substruct_revert_prop.

        exists (DRecord (discharge_env d2.(bindings) Indet) Indet).
        constructor; auto.
        apply total_clobber_substruct.

      eauto using substruct_r_refl.

    intros.
    simpl.
    apply substruct_h_trans with (dh₂ := revert_evt_h de1 (clobber_evt_h de2 dh') dh).
      apply IHde1.
    
      apply substruct_revert_substruct_h; auto.
Qed.

Lemma clobber_evt_leq_revert_evt : forall de dh dh', 
  clobber_evt_h de dh' ≼ revert_evt_h de dh' dh.
Proof.
  induction de; simpl clobber_evt_h; simpl revert_evt_h; auto using (@leq_refl dheap).
    intros dh dh' a' dr.
    destruct (a' == a); subst.
      remember (dh' a) as dh'a; destruct dh'a; symmetry in Heqdh'a; inversion 1; subst.
      remember (dh a) as dha; destruct dha; symmetry in Heqdha.
        exists (revert_prop n d2 d3).
        constructor; auto.
        apply clobber_prop_leq_revert_prop.

        exists (DRecord (discharge_env d2.(bindings) Indet) Indet).
        constructor; auto.
        apply total_clobber.

      eauto using (@leq_refl drecord).

    intros.
    eapply leq_trans with (b := clobber_evt_h de1 (revert_evt_h de2 dh' dh)).
      apply clobber_evt_h_mon; auto.
      apply clobber_evt_substruct_revert_evt.

      apply IHde1.
Qed.
