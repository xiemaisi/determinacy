(** variable and property domains **)
Set Implicit Arguments.

Require Import Common Eq Syntax FinMap Values ConcreteSemantics.

(** all variables written by an event **)
Fixpoint vd (e:event) : list name :=
  match e with
  | EVarWrite x _ => x::nil
  | ECond _ e => vd e
  | ESeq e₁ e₂ => (vd e₁) ++ (vd e₂)
  | _ => nil
  end.

(** all variables possibly written by a piece of code **)
Fixpoint syntactic_vd (s:stmt) : list name :=
  match s with
  | SLoadLit x _
  | SVarCopy x _
  | SPropRead x _ _
  | SPrimOp x _ _ _
  | SFunCall x _ _ => x::nil
  | SIf _ s
  | SWhile _ _ s => syntactic_vd s
  | SSeq s₁ s₂ => (syntactic_vd s₁) ++ (syntactic_vd s₂)
  | SPropWrite _ _ _ 
  | SSkip => nil
  end.

(** all properties written by an event **)
Inductive pd : event -> address * name -> Prop :=
  | PDPropWrite : forall a p v, pd (EPropWrite a p v) (a, p)
  | PDCond : forall v e a p, pd e (a, p) -> pd (ECond v e) (a, p)
  | PDCall : forall vs ρ e a p, pd e (a, p) -> pd (ECall vs ρ e) (a, p)
  | PDSeq₁ : forall e₁ e₂ a p, pd e₁ (a, p) -> pd (ESeq e₁ e₂) (a, p)
  | PDSeq₂ : forall e₁ e₂ a p, pd e₂ (a, p) -> pd (ESeq e₁ e₂) (a, p).

(** Lemma 3: correctness of vd **)
Lemma vd_correct : forall h ρ s h' ρ' e,
  〈h, ρ, s〉 ↓ 〈h', ρ', e〉 -> 
  forall x, ~In x (vd e) -> lookup ρ' x = lookup ρ x.
Proof.
  induction 1; intros; try (solve [trivial]).
    apply update_lookup_different.
    contradict H.
    simpl; auto.

    apply update_lookup_different.
    contradict H.
    simpl; auto.

    apply update_lookup_different.
    contradict H0.
    simpl; auto.

    apply update_lookup_different.
    contradict H0.
    simpl; auto.

    apply update_lookup_different.
    contradict H3.
    simpl; auto.

    apply update_lookup_different.
    contradict H2.
    simpl; auto.

    apply update_lookup_different.
    contradict H3.
    simpl; auto.

    apply IHred.
    contradict H2.
    simpl; auto.

    rewrite IHred2.
      apply IHred1.
      contradict H1.
      simpl; auto with datatypes.

      contradict H1.
      simpl; auto with datatypes.
Qed.

(** Lemma 4: syntactic vd over-approximates vd **)
Lemma syntactic_vd_correct : forall h ρ s h' ρ' e,
  〈h, ρ, s〉 ↓ 〈h', ρ', e〉 -> forall x, In x (vd e) -> In x (syntactic_vd s).
Proof.
  induction 1; subst; simpl; auto with datatypes.
    inversion 1.

    intros x K.
    edestruct in_app_or; eauto with datatypes.
Qed.

(** Lemma 3: correctness of pd **)
Lemma pd_correct : forall h ρ s h' ρ' e,
  〈h, ρ, s〉 ↓ 〈h', ρ', e〉 -> 
  forall a p, (a, p) ∉ (pd e) -> bind (fun r => lookup r p) (h' a) = bind (fun r => lookup r p) (h a).
Proof.
  induction 1; intros; try (solve [trivial]).
    unfold fupdate; simpl.
    destruct (a0 == a); subst; simpl; auto.
    remember (h a) as ha.
    destruct ha; auto.
    contradict H.
    solve [eauto using dom].

    unfold fupdate.
    destruct (a0 == a); subst; simpl; auto.
    destruct (p == tostring pv); subst.
      contradict H3.
      solve [constructor].

      rewrite H1.
      solve [trivial].

    apply IHred.
    contradict H3.
    solve [auto using pd].

    apply IHred.
    contradict H2.
    solve [auto using pd].

    rewrite IHred2.
      apply IHred1.
      contradict H1.
      solve [auto using pd].

      contradict H1.
      solve [auto using pd].
Qed.

(** decidability of pd **)
Lemma pd_dec : forall e ap, {ap ∈ pd e} + {~ap ∈ pd e}.
Proof.
  induction e.
    right; intro K.
    solve [inversion K].

    intros (a', p').
    destruct (a' == a); subst.
      destruct (p' == n); subst.
        solve [eauto using pd].

        right; intro K.
        inversion K; congruence.

      right; intro K.
      inversion K; congruence.

    intros (a, p).
    destruct (IHe (a, p)).
      eauto using pd.

      right; contradict n.
      inversion n; subst; trivial.


    intros (a, p).
    destruct (IHe (a, p)).
      eauto using pd.

      right; contradict n.
      inversion n; subst; trivial.

    right; intro K.
    inversion K.

    intros (a, p).
    destruct (IHe1 (a, p)).
      eauto using pd.

      destruct (IHe2 (a, p)).
        eauto using pd.

        right; intro K.
        inversion K; subst; auto.
Qed.


