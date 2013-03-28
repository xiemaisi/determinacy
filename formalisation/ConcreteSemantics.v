(** Concrete semantics of MuJS **)
Set Implicit Arguments.

Require Import Common Eq FinMap Syntax Values Wf.

Reserved Notation "〈 h , ρ , s 〉 ↓ 〈 h' , ρ' , e 〉" (at level 200, no associativity).

Inductive red : heap -> env name value -> stmt -> heap -> env name value -> event -> Prop :=
| LdLit : forall h ρ x (pv:primval),
             〈h, ρ, SLoadLit x pv〉 ↓ 
              〈h, update ρ x pv, EVarWrite x pv〉
| LdClos : forall h ρ x y ls s z,
           let v := VClos y ls s z ρ in
             〈h, ρ, SLoadLit x (LFun y ls s z)〉 ↓ 〈h, update ρ x v, EVarWrite x v〉
| LdRec : forall h ρ x a, a ∉ (dom h) ->
             〈h, ρ, SLoadLit x LRec〉 ↓
              〈fupdate h a (Some nil), update ρ x a, EVarWrite x a〉
| Assign : forall h ρ x y v, lookup ρ y = Some v ->
             〈h, ρ, SVarCopy x y〉 ↓
              〈h, update ρ x v, EVarWrite x v〉
| Ld : forall (h:heap) ρ x y z a pv r v,
            lookup ρ y = Some (VAddr a) -> lookup ρ z = Some (VPrim pv) -> h a = Some r -> 
            record_lookup r (tostring pv) = v ->
             〈h, ρ, SPropRead x y z〉 ↓
              〈h, update ρ x v, EVarWrite x v〉
| Sto : forall (h:heap) ρ x y z a pv r v,
            lookup ρ x = Some (VAddr a) -> lookup ρ y = Some (VPrim pv) -> h a = Some r -> lookup ρ z = Some v ->
             〈h, ρ, SPropWrite x y z〉 ↓
              〈fupdate h a (Some (update r (tostring pv) v)), ρ, EPropWrite a (tostring pv) v〉
| PrimOp : forall h (ρ:env name value) x y o z (v₁ v₂ v₃:primval),
            lookup ρ y = Some (VPrim v₁) -> lookup ρ z = Some (VPrim v₂) -> primop_eval v₁ o v₂ = Some v₃ ->
             〈h, ρ, SPrimOp x y o z〉 ↓ 〈h, update ρ x v₃, EVarWrite x v₃〉
| Call : forall h ρ x f (y:name) p ys b z ρ' v h' ρ'' v' e,
            lookup ρ f = Some (VClos p ys b z ρ') -> lookup ρ y = Some v ->
            (〈h, updates (update ρ' p v) ys undefined, b〉 ↓ 〈h', ρ'', e〉) -> lookup ρ'' z = Some v' ->
             〈h, ρ, SFunCall x f y〉 ↓
              〈h', update ρ x v', ESeq (ECall v ρ' e) (EVarWrite x v')〉
| IfTrue : forall h ρ x s v h' ρ' e,
            lookup ρ x = Some v -> truthy v -> (〈h, ρ, s〉 ↓ 〈h', ρ', e〉) ->
             〈h, ρ, SIf x s〉 ↓ 〈h', ρ', ECond v e〉
| IfFalse : forall h ρ x s v,
            lookup ρ x = Some v -> ~truthy v ->
             〈h, ρ, SIf x s〉 ↓ 〈h, ρ, ECond v ESkip〉
| Skip : forall h ρ,
             〈h, ρ, SSkip〉 ↓
              〈h, ρ, ESkip〉
| Seq : forall h ρ s₁ s₂ h' ρ' h'' ρ'' e₁ e₂,
             (〈h, ρ, s₁〉 ↓ 〈h', ρ', e₁〉) ->
             (〈h', ρ', s₂〉 ↓ 〈h'', ρ'', e₂〉) ->
              (〈h, ρ, SSeq s₁ s₂〉 ↓ 〈h'', ρ'', ESeq e₁ e₂〉)

where "〈 h , ρ , s 〉 ↓ 〈 h' , ρ' , e 〉" := (red h ρ s h' ρ' e).

(** the DOM expands during evaluation **)
Lemma red_dom_expand : forall h ρ s h' ρ' e, 〈h, ρ, s〉 ↓ 〈h', ρ', e〉 ->
  dom h ⊆ dom h'.
Proof.
  induction 1; eauto.
Qed.

(** Lemma 1: evaluation preserves well-formedness **)
Lemma wf_pres : forall h ρ s h' ρ' e, 〈h, ρ, s〉 ↓ 〈h', ρ', e〉 ->
  wf h ρ -> wf h' ρ' /\ wf_evt h' e.
Proof.
  induction 1; destruct 1.
    solve [auto using wf].
    
    subst v.
    solve [auto using wf].

    constructor.
      constructor.
        apply wf_h_update; solve [auto].

        apply wf_env_update.
          apply wf_env_heap_update with (h:=h); solve [auto].

          apply WfAddr with (r:=nil).
          unfold fupdate.
          eapply if_eq; solve [eauto].

      constructor.
      apply WfAddr with (r:=nil).
      unfold fupdate.
      eapply if_eq; solve [eauto].

    assert (K: wf_v h v).
      destruct H1; solve [eauto].
    constructor; auto.
    constructor; solve [auto].

    assert (K: wf_v h v).
      destruct H3.
      generalize (w _ _ H1).
      destruct 1; solve [eauto].
    solve [auto using wf].

    assert (K: wf_v h v).
      destruct H4; solve [eauto].
    constructor.
      constructor.
        destruct H3.
        constructor.
        intros a' r' K'.
        apply wf_env_heap_update with (h:=h); eauto.
        unfold fupdate in K'.
        destruct (a' == a); subst; eauto.
        inversion K'; subst; solve [eauto].

        apply wf_env_heap_update with (h:=h); solve [eauto].

      apply wf_evt_heap_update with (h:=h); solve [eauto].

    solve [auto using wf].

    assert (K₁: wf_v h v).
      destruct H4; solve [eauto].
    assert (K₂: wf_env h ρ').
      destruct H4.
      set (K := H4 f _ H).
      inversion K; subst.
      solve [auto].
    assert (K₃: wf_v h' v).
      apply wf_v_heap_update with (h:=h); solve [eauto using red_dom_expand].
    assert (K₄: wf_env h' ρ').
      apply wf_env_heap_update with (h:=h); solve [eauto using red_dom_expand].
    destruct IHred.
      constructor; auto.
      clear H H0 H1 H2 H3 H4.
      induction ys; simpl; solve [auto using wf_env_update].
    destruct H5.
    assert (K₅: wf_v h' v').
      destruct H7; solve [eauto].
    assert (K₆: wf_env h' ρ).
      apply wf_env_heap_update with (h:=h); solve [eauto using red_dom_expand].
    solve [auto using wf].

    destruct IHred; auto using wf.
    destruct H3.
    solve [eauto 8 using wf_v_heap_update, red_dom_expand].

    constructor; auto using wf.
    destruct H2; solve [eauto].

    solve [auto using wf].

    intros.
    edestruct IHred1 as (?,?); eauto using wf.
    edestruct IHred2 as (?,?); eauto using wf.
    constructor; auto.
    constructor; auto.
    apply wf_evt_heap_update with (h:=h'); eauto using red_dom_expand.
Qed. 
