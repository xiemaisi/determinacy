(* The Soundness Theorem *)
Set Implicit Arguments.

Require Import Common Eq FinMap Parameters Values InstrumentedValues ConcreteSemantics InstrumentedSemantics Wf Modelling Discharging Clobbering Reverting DeterminacyOrder Domains Substruct.

(** clobbering all names in the syntactic vd accounts for all possible changes to the local environment **)
Lemma leq_clobber_all_names : forall de dh dρ s n dh' dρ', (〈dh, dρ, s〉 ↓^(n) 〈dh', dρ', de〉) -> 
  dρ ≼ (clobber_names (vd (strip_evt de)) dρ').
Proof.
  induction 1; simpl strip_evt; simpl vd; (solve [auto using leq_clobber_names_update] || 
                                           solve [simpl clobber_names; apply leq_refl] || 
                                           idtac).
   eapply leq_trans; eauto.
   apply clobber_names_mon.
   apply denv_leq_discharge_names.

   apply leq_trans with (b := clobber_names (vd (strip_evt de)) dρ); auto using denv_leq_clobber_names.

   simpl clobber_names.
   apply clobber_names_mon; auto.

   simpl clobber_names.
   eapply leq_trans; eauto using clobber_names_leq_revert_names.
 
   simpl clobber_names.
   apply denv_leq_clobber_names.

   rewrite clobber_names_app.
   eapply leq_trans; eauto.
   apply clobber_names_mon.
   auto.
Qed.

(** some technical lemmas on substructure **)
Lemma substruct_clobber_r : forall p dr, substruct_r dr (clobber_prop p dr).
Proof.
  intros p dr q dv K.
  unfold clobber_prop.
  destruct (lookup dr.(bindings) p); eauto.
  destruct (q == p); subst; simpl.
    erewrite if_eq; eauto.

    erewrite if_neq; eauto.
Qed.

Lemma substruct_discharge_r : forall dr d, substruct_r dr (discharge_r dr d).
Proof.
  destruct d.
    rewrite discharge_det_r.
    apply substruct_r_refl.

    intros p dv K.
    simpl.
    rewrite discharge_env_lookup.
    rewrite K; simpl; eauto.
Qed.

Lemma substruct_discharge_h : forall dh d, substruct_h dh (discharge_h dh d).
Proof.
  destruct d; simpl; auto using substruct_h_refl.
  intros a dr K.
  rewrite K.
  exists (discharge_r dr Indet).
  constructor; auto.
  apply substruct_discharge_r.
Qed.

Lemma substruct_clobber_evt : forall de dh, substruct_h dh (clobber_evt_h de dh).
  induction de; simpl clobber_evt_h; auto using substruct_h_refl.
    intros dh a' dr' K.
    destruct (a' == a); subst.
      rewrite K; simpl.
      exists (clobber_prop n dr').
      constructor; auto using substruct_clobber_r.

      eauto using substruct_r_refl.

    intro dh.
    eauto using substruct_h_trans.
Qed.

Lemma substruct_discharge_evt : forall de dh d, substruct_h dh (discharge_evt_h dh de d).
Proof.
  destruct d; simpl; auto using substruct_h_refl, substruct_clobber_evt.
Qed.

Lemma substruct_clobber_substruct_r: forall p dr dr' dr'',
  substruct_r dr (clobber_prop p dr') -> substruct_r dr' dr'' -> substruct_r dr (clobber_prop p dr'').
Proof.
  unfold clobber_prop.
  intros p dr dr' dr'' K₁ K₂ p' dv K₃.
  edestruct K₁ as (dv'&?); eauto.
  remember (lookup dr'.(bindings) p) as dr'p; destruct dr'p.
    edestruct K₂ as (dv''&?); eauto.
    rewrite H0.
    destruct (p' == p); subst; simpl in *.
      erewrite ! if_eq in *; eauto.

      rewrite ! if_neq in *; auto.
      edestruct K₂ as (dv'''&?); eauto.

    edestruct K₂ as (dv''&?); eauto.
    remember (lookup dr''.(bindings) p) as dr''p; destruct dr''p; eauto.
    destruct (p' == p); subst; simpl.
      erewrite ! if_eq; eauto.

      erewrite ! if_neq; eauto.
Qed.      

Lemma substruct_clobber_substruct_h : forall de dh dh' dh'',
  substruct_h dh (clobber_evt_h de dh') -> substruct_h dh' dh'' -> substruct_h dh (clobber_evt_h de dh'').
Proof.
  induction de; simpl clobber_evt_h; eauto using substruct_h_trans.
    intros dh dh' dh'' K₁ K₂ a' dr' K₃.
    destruct (a' == a); subst.
      edestruct K₁ as (dr''&?&?); eauto.
      erewrite if_eq in H; eauto.
      remember (dh' a) as dh'a; destruct dh'a; inversion H; subst.
      edestruct K₂ as (dh'''&?&?); eauto.
      rewrite H1; subst; simpl.
      exists (clobber_prop n dh''').
      constructor; auto.
      eapply substruct_clobber_substruct_r; eauto.

      edestruct K₁ as (dr''&?&?); eauto.
      rewrite if_neq in H; auto.
      edestruct K₂ as (dh'''&?&?); eauto.
      exists dh'''.
      constructor; eauto using substruct_r_trans.

    intros.
    eapply IHde1; eauto.
    apply clobber_evt_preserves_substruct.
    auto.
Qed.

Lemma substruct_substruct_clobber_h : forall de dh dh',
  substruct_h dh dh' -> substruct_h dh (clobber_evt_h de dh').
Proof.
  induction de; simpl substruct_h; auto.
  intros dh dh' K a' dr' K'.
  destruct (a' == a); subst.
    edestruct K as (dr''&?&?); eauto.
    rewrite H; simpl.
    exists (clobber_prop n dr'').
    constructor; auto.
    eapply substruct_clobber_substruct_r; eauto.
    apply substruct_clobber_r.

    eauto.
Qed.

(** if the heap resulting from an evaluation is clobbered, its structure is an extension of the initial one **)
Lemma substruct_red : forall de dh dρ s n dh' dρ', (〈dh, dρ, s〉 ↓^(n) 〈dh', dρ', de〉) ->
  substruct_h dh (clobber_evt_h de dh').
Proof.
  induction 1; simpl clobber_evt_h; auto using substruct_h_refl.
    intros a' dr' K.
    unfold fupdate.
    destruct (a' == a); subst.
      contradict H; eauto using dom.

      eauto using substruct_r_refl.

    intros a' dr' K.
    destruct (a' == a); subst.
      rewrite K in H1; inversion H1; subst.
      destruct d₁; simpl discharge_h.
        unfold fupdate.
        erewrite if_eq; eauto.
        exists (clobber_prop (tostring pv) (discharge_r (drecord_update dr (tostring pv) dv) d₂)).
        constructor; auto.
        destruct d₂.
          rewrite discharge_det_r.
          apply substruct_clobber_update.

          remember (tostring pv) as p.
          clear.
          intros q dv' K.
          unfold clobber_prop.
          unfold discharge_r at 1.
          simpl bindings.
          erewrite if_eq; eauto.
          destruct (q == p); subst; simpl.
            erewrite ! if_eq; eauto.

            erewrite ! if_neq; eauto.
            rewrite discharge_env_lookup.
            rewrite K; simpl; eauto.

        unfold fupdate.
        erewrite if_eq; eauto.
        simpl option_map.
        exists (clobber_prop (tostring pv) (discharge_r (discharge_r (drecord_update dr (tostring pv) dv) d₂) Indet)).
        constructor; auto.
        remember (tostring pv) as p; clear.
        intros q dv' K.
        unfold clobber_prop.
        unfold discharge_r at 2.
        simpl bindings.
        erewrite if_eq; eauto.
        destruct (q == p); subst; simpl.
          erewrite ! if_eq; eauto.

          erewrite ! if_neq; eauto.
          rewrite discharge_env_lookup.
          rewrite discharge_env_lookup.
          rewrite K; simpl; eauto.

      destruct d₁; simpl discharge_h.
        unfold fupdate.
        rewrite if_neq; eauto using substruct_r_refl.
        
        unfold fupdate.
        rewrite if_neq; auto.
        rewrite K.
        exists (discharge_r dr' Indet).
        constructor; auto.
        apply substruct_discharge_r.

      eapply substruct_clobber_substruct_h; eauto.
      apply substruct_discharge_h.

      destruct (get_det dv); simpl discharge_evt_h; auto.
      apply substruct_substruct_clobber_h; auto.

      eapply substruct_clobber_substruct_h; eauto.
      apply substruct_h_trans with (dh₂ := clobber_evt_h de dh').
        apply substruct_substruct_clobber_h.
        apply substruct_h_refl.

        apply clobber_evt_substruct_revert_evt.

      intros a dr K.
      rewrite K.
      exists (discharge_r dr Indet).
      constructor; auto.
      apply substruct_discharge_r.

      eapply substruct_clobber_substruct_h; eauto.
Qed.

(** if the heap resulting from an evaluation is clobbered, it will be less determinate than the initial one **)
Lemma leq_clobber_evt : forall de dh dρ s n dh' dρ', (〈dh, dρ, s〉 ↓^(n) 〈dh', dρ', de〉) ->
  dh ≼ (clobber_evt_h de dh').
Proof.
  induction 1; simpl clobber_evt_h; auto using (@leq_refl dheap).
    intros a' dr' K.
    destruct (a' == a); subst.
      contradict H.
      eauto using dom.

      unfold fupdate.
      erewrite if_neq; eauto.
      exists dr'.
      constructor; auto using (@leq_refl drecord).
      
    intros a' dr' K.
    destruct (a' == a); subst.
      destruct d₁; simpl discharge_h.
        unfold fupdate.
        erewrite if_eq; eauto.
        exists (clobber_prop (tostring pv) (discharge_r (drecord_update dr (tostring pv) dv) d₂)).
        constructor; auto.
        rewrite K in H1; inversion H1; subst.
        destruct d₂.
          rewrite discharge_det_r.
          apply leq_clobber_update.

          remember (tostring pv) as p.
          clear.
          intro q.
          unfold clobber_prop.
          unfold discharge_r at 1.
          simpl bindings.
          simpl lookup.
          erewrite if_eq; eauto.
          destruct (q == p); subst.
            rewrite drecord_update_lookup_same.
            destruct (discharge dv Indet); right; auto.

            rewrite drecord_update_lookup_different; auto.
            unfold drecord_lookup at 2.
            unfold discharge_r.
            simpl bindings.
            simpl lookup.
            rewrite if_neq; auto.
            rewrite discharge_env_lookup.
            unfold drecord_lookup.
            destruct (lookup dr.(bindings) q); simpl.
              destruct d; right; auto.

              right; auto.

        unfold fupdate.
        erewrite if_eq; eauto.
        simpl option_map.
        exists (clobber_prop (tostring pv) (discharge_r (discharge_r (drecord_update dr (tostring pv) dv) d₂) Indet)).
        constructor; auto.
        remember (tostring pv) as p; clear.
        intro q.
        unfold clobber_prop.
        unfold discharge_r at 2.
        simpl bindings.
        simpl lookup.
        erewrite if_eq; eauto.
        destruct (q == p); subst.
          rewrite drecord_update_lookup_same.
          destruct (discharge (discharge dv d₂) Indet); right; auto.

          rewrite drecord_update_lookup_different; auto.
          unfold drecord_lookup at 2.
          unfold discharge_r.
          simpl bindings.
          simpl lookup.
          rewrite if_neq; auto.
          rewrite discharge_env_lookup.
          rewrite discharge_env_lookup.
          destruct (lookup dr.(bindings) q); simpl.
            destruct (discharge d d₂); right; auto.

            right; auto.

      destruct d₁; simpl discharge_h.
        unfold fupdate.
        rewrite if_neq; eauto using (@leq_refl drecord).
        
        unfold fupdate.
        rewrite if_neq; auto.
        rewrite K.
        exists (discharge_r dr' Indet).
        constructor; auto.
        apply drecord_leq_discharge_Indet.

    eapply leq_trans; eauto.
    apply clobber_evt_h_mon.
      apply substruct_discharge_h.

      apply dheap_leq_discharge.

    eapply leq_trans; eauto.
    apply clobber_evt_h_mon.
      apply substruct_discharge_evt.

      destruct (get_det dv); simpl discharge_evt_h; auto using (@leq_refl dheap).
      apply denv_leq_clobber_evt.

    apply leq_trans with (b := revert_evt_h de dh' dh).
      eapply leq_trans; eauto.
      apply clobber_evt_leq_revert_evt.

      apply denv_leq_clobber_evt.

    intros a' dr' K.
    rewrite K.
    exists (discharge_r dr' Indet).
    constructor; auto.
    apply drecord_leq_discharge_Indet.

    eapply leq_trans; eauto.
    apply clobber_evt_h_mon; auto.
    eapply substruct_red; eauto.
Qed.

(** Finally! **)    
Theorem soundness : forall dh dρ s dh' dρ' de n,
  〈dh, dρ, s〉 ↓^(n) 〈dh', dρ', de〉 ->
  forall μ h ρ, models_h μ dh h -> models_env μ dρ ρ ->
    forall h' ρ' e, 〈h, ρ, s〉 ↓ 〈h', ρ', e〉 -> wf h ρ -> injective μ (dom h) ->
      exists μ', agree μ μ' (dom h) /\ injective μ' (dom h') /\
                 models_h μ' dh' h' /\ models_env μ' dρ' ρ' /\ models_evt μ' de e.
Proof.
  induction 1; intros.
    inversion H1; subst.
    exists μ; solve [eauto 10].

    inversion H1; subst.
    subst dv. subst v.
    exists μ; solve [auto 8].
    
    inversion H2; subst.
    rename a0 into a'.
    exists (fupdate μ a' a).
    constructor.
      intros a'' K1.
      unfold fupdate.
      destruct (a'' == a'); subst; solve [intuition].

      constructor.
        apply injective_coext with (dom h ∪ Just a').
          apply injective_add_one; auto.
          intros a'' K.
          contradict H.
          destruct H0.
          destruct K.
          edestruct H0 as (?&?&?); eauto.
          rewrite H in H6.
          solve [eauto using dom].

          solve [auto using coext_symm].

        constructor.
          constructor.
          intros a'' r.
          unfold fupdate.
          destruct (a'' == a'); subst.
            erewrite if_eq; eauto.
            inversion 1; subst.
            exists (DRecord nil Det).
            constructor; auto.
            constructor.
            unfold drecord_lookup.
            unfold record_lookup.
            simpl.
            solve [constructor].

            intro K.
            destruct (μ a'' == a).
              destruct H0.
              edestruct H0 as (?&?&?); eauto.
              contradict H.
              rewrite e in H5.
              solve [eauto using dom].

              destruct H0.
              edestruct H0 as (?&?&?); eauto.
              exists x0.
              constructor; auto.
              assert (K': wf_env h r).
                destruct H3.
                destruct H3.
                solve [eauto].
              assert (K'':agree μ (fupdate μ a' a) (dom h)) by auto using agree_fupdate.
              eapply mu_agreement_r; solve [eauto].

          constructor.
            apply models_env_ext.
              destruct H3.
              assert (K': agree μ (fupdate μ a' a) (dom h)) by auto using agree_fupdate.
              eapply mu_agreement_e; solve [eauto].
  
              assert (K : (fupdate μ a' a) a' = a).
                unfold fupdate.
                erewrite if_eq; solve [eauto].
              rewrite <- K at 2.
              solve [constructor].

            constructor.
            assert (K : (fupdate μ a' a) a' = a).
              unfold fupdate.
              erewrite if_eq; solve [eauto].
            rewrite <- K at 2.
            solve [constructor].

    inversion H2; subst.
    exists μ; solve [eauto 10].

    inversion H5.
    assert (K₁ : models_v μ (DVAddr a d₁) a0) by eauto using models_env.
    assert (K₂ : models_v μ (DVPrim pv d₂) pv0) by eauto using models_env.
    assert (K₃ : models_v μ dv' v).
      subst dv'; subst.
      destruct d₂.
        rewrite discharge_det_v.
        destruct d₁.
          rewrite discharge_det_v.
          inversion K₁; subst.
          assert (K₄ : models_r μ dr r) by eauto using models_h.
          inversion K₂; subst.
          inversion K₄; subst.
          solve [auto].

          solve [auto using models_v_clobber].

        solve [auto using models_v_clobber].
    subst dv'; subst.
    exists μ.
    constructor; solve [auto].

    inversion H5; subst.
    assert (K₁ : models_v μ (DVAddr a d₁) a0) by eauto using models_env.
    assert (K₂ : models_v μ (DVPrim pv d₂) pv0) by eauto using models_env.
    assert (K₃ : models_v μ dv v) by eauto using models_env.
    exists μ.
    constructor; auto.
    constructor.
      apply injective_coext with (X:=dom h); auto.
      apply coext_trans with (Y:=dom h ∪ Just a0).
        intro a'.
        constructor; firstorder.
        inversion H8; subst.
        solve [eauto using dom].
      auto using coext_symm.

      destruct d₁.
        unfold discharge_h; simpl.
        inversion K₁; subst.
        constructor.
          apply models_h_ext; auto.
            destruct d₂.
              rewrite discharge_det_r.
              inversion K₂; subst.
              apply models_r_ext; auto.
              destruct H3.
              edestruct H3 as (?&?&?); eauto.
              congruence.

              solve [apply models_r_clobber].

            apply injective_coext with (X:=dom h); auto.
            intro a'.
            constructor; firstorder.
            inversion H8; subst.
            solve [eauto using dom].

          constructor; solve [auto].

        constructor.
          solve [apply models_h_clobber].

          constructor; solve [auto].

    inversion H4; subst.
    assert (K₁ : models_v μ (DVPrim v₁ d₁) v₁0) by eauto using models_env.
    assert (K₂ : models_v μ (DVPrim v₂ d₂) v₂0) by eauto using models_env.
    assert (K₃ : models_v μ dv v₃0).
      subst dv.
      destruct d₂.
        rewrite discharge_det_v.
        inversion K₂; subst.
        destruct d₁.
          inversion K₁; subst.
          assert (K₄ : v₃ = v₃0) by congruence.
          subst.
          solve [constructor].

          solve [constructor].

        solve [apply models_v_clobber].
    exists μ; solve [auto 8].

    inversion H5; subst.
    assert (K₁: models_v μ (DVClos p ys b z dρ' d) (VClos p0 ys0 b0 z0 ρ'0)) by eauto using models_env.
    assert (K₂: models_v μ dv v) by eauto using models_env.
    destruct d.
      inversion K₁; subst.
      assert (K₃: models_env μ (updates (update dρ' p0 dv) ys0 (DVPrim undefined Det))
                               (updates (update ρ'0 p0 v) ys0 undefined)).
        generalize H9 K₂.
        clear.
        induction ys0; simpl; solve [auto].
      destruct H6.
      destruct H8.
      assert (K₄: wf_env h ρ'0).
        set (K := H8 _ _ H11).
        inversion K; subst; solve [auto].
      assert (K₅: wf_v h v) by eauto.
      assert (K₆: wf h (updates (update ρ'0 p0 v) ys0 undefined)).
        constructor; auto.
        generalize K₄ K₅.
        clear.
        induction ys0; simpl; solve [auto].
      destruct (IHdred _ _ _ H3 K₃ _ _ _ H18 K₆ H7) as (μ'&?&?&?&?&?).
      assert (K₇: models_v μ' dv' v').
        destruct H15.
        destruct (H15 _ _ H19) as (?&?&?).
        rewrite H2 in H17.
        inversion H17; subst; solve [auto].
      exists μ'.
      constructor; auto.
      constructor; auto.
      unfold discharge_h; simpl.
      constructor; auto.
      rewrite discharge_det_v.
      constructor; auto.
        apply models_env_ext; solve [eauto using mu_agreement_e, wf_env].

        constructor; solve [eauto using mu_agreement_v, mu_agreement_e].

      set (K := @injective_extension μ (dom h) (dom h')).
      destruct K as (μ'&?&?); eauto using red_dom_expand.
      exists μ'.
      constructor; auto.
      constructor; auto.
      constructor; auto using models_h_clobber.
      destruct H6.
      assert (wf_v h v).
        destruct H10; solve [eauto].
      constructor.
            solve [eauto using models_env_ext, mu_agreement_e, wf_env, models_v_clobber].

            constructor; solve [eauto using mu_agreement_v, models_v_clobber].

    inversion H4; subst.
      destruct (IHdred μ h ρ H2 H3 h' ρ' e0 H16 H5 H6) as (μ'&?&?&?&?&?).
      exists μ'.
      constructor; auto.
      constructor; auto.
      constructor; auto using models_h_discharge_evt.
      constructor; auto using models_env_discharge_names.
      assert (models_v μ' dv v).
        apply mu_agreement_v with (μ:=μ) (h:=h); eauto using models_env_lookup.
        destruct H5.
        destruct H14.
        solve [eauto].
      constructor; solve [auto].

      assert (models_v μ dv v).
        eapply models_env_lookup; solve [eauto].
      assert (K: get_det dv = Indet).
        remember (get_det dv) as get_det_dv.
        destruct get_det_dv; auto.
        symmetry in Heqget_det_dv.
        contradict H15.
        eapply truthy_strip; solve [eauto].
      rewrite K.
      exists μ; simpl.
      constructor; auto.
      constructor; auto.
      constructor.
        eapply models_h_mon; eauto using leq_clobber_evt.
        
        constructor; auto.
        eapply models_env_mon; eauto using leq_clobber_all_names.

    inversion H4; subst.
      exfalso.
      contradict H0.
      assert (K: models_v μ dv v) by eauto using models_env_lookup.
      eapply truthy_strip; solve [eauto].

      assert (K: models_v μ dv v) by eauto using models_env_lookup.
      solve [eauto 8].

    inversion H6; subst.
      destruct (IHdred μ h ρ H4 H5 h' ρ' e0 H18 H7 H8) as (μ'&?&?&?&?&?).
      exists μ'; simpl.
      constructor; auto.
      constructor; auto.
      constructor.
        eapply models_h_mon; eauto.
        eapply leq_trans; eauto using clobber_evt_leq_revert_evt, denv_leq_clobber_evt.

        constructor; eauto.
        eapply models_env_mon; eauto.
        eapply leq_trans; eauto using clobber_names_leq_revert_names, denv_leq_clobber_names.

      exists μ.
      constructor; auto.
      constructor; auto.
      constructor.
        eapply models_h_mon; eauto.
        apply leq_trans with (b := clobber_evt_h de dh').
          eapply leq_clobber_evt; eauto.

          apply clobber_evt_leq_revert_evt.

        constructor; auto.
        eapply models_env_mon; eauto.
        eapply leq_trans; eauto using clobber_names_leq_revert_names, leq_clobber_all_names.

    inversion H5; subst.
      set (K₁ := @injective_extension μ (dom h) (dom h')).
      destruct K₁ as (μ'&?&?); eauto using red_dom_expand. 
      assert (K₂ : models_v μ dv v) by eauto using models_env.
      assert (K₃ : wf_env h ρ) by (destruct H6; auto).
      assert (K₄ : wf_v h v) by (destruct K₃; eauto).
      assert (K₅ : models_v μ' dv v) by eauto using mu_agreement_v.
      exists μ'.
      constructor; auto.
      constructor; auto.
      constructor; auto using models_h_clobber.
      constructor; auto.
      constructor.
      intros x' v' K₆. 
      destruct (In_dec x' (syntactic_vd s)).
        rewrite clobber_names_lookup_clobbered; eauto using models_v_clobber.

        rewrite clobber_names_lookup_not_clobbered; eauto.
        rewrite (vd_correct H17) in K₆.
          assert (K₇ : models_env μ' dρ ρ).
            eapply mu_agreement_e; eauto.
          destruct K₇.
          eauto.

          contradict n0.
          eapply syntactic_vd_correct; eauto.

      assert (K : models_v μ dv v) by eauto using models_env.
      exists μ.
      constructor; auto.
      constructor; auto.
      constructor; auto using models_h_clobber.
      constructor; solve [auto using models_env_clobber_names].
      
    inversion H1; subst.
    solve [eauto 8].

    inversion H3; subst.
    edestruct IHdred1 as (μ'&?&?&?&?&?); eauto; clear IHdred1.
    edestruct IHdred2 as (μ''&?&?&?&?&?); eauto; clear IHdred2.
      destruct (wf_pres H10); solve [auto].
    exists μ''.
    constructor.
      apply agree_trans with (g:=μ'); auto.
      apply agree_subset with (X':=dom h'0); auto.
      solve [eapply red_dom_expand; eauto].

      constructor; auto.
      constructor; auto.
      constructor; auto.
      constructor; auto.
      assert (K: wf_evt h'0 e₁0).
        destruct (wf_pres H10); solve [auto].
      solve [eapply mu_agreement_evt; eauto].
Qed.
