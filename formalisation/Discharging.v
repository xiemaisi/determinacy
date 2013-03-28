(** Functions for discharging determinacy annotations on values **)
Set Implicit Arguments.

Require Import Common Eq FinMap InstrumentedValues Modelling DeterminacyOrder.

(** join operator on determinacy flags **)
Definition dmax d d' :=
  match d with
    | Indet => Indet
    | Det => d'
  end.

(** this operation is written dv^d in the paper **)
Definition discharge dv d :=
  match dv with
    | DVPrim pv d' => DVPrim pv (dmax d d')
    | DVAddr a d' => DVAddr a (dmax d d')
    | DVClos x ys b z ρ d' => DVClos x ys b z ρ (dmax d d')
  end.

(** homomorphic extensions to environments, records and heaps **)
Definition discharge_env (dρ:env name dvalue) d : env name dvalue :=
  map (fun (b:name*dvalue) => let (x, dv) := b in (x, discharge dv d)) dρ.

Definition discharge_r (dr:drecord) d := 
  DRecord (discharge_env dr.(bindings) d) (dmax d dr.(complete)).

Definition discharge_h (dh:dheap) d : dheap :=
  match d with
    | Det => dh
    | Indet => fun (a:address) => match dh a with 
                                  | Some dr => Some (discharge_r dr d) 
                                  | None => Some (DRecord nil Indet) end 
  end.

(** some simple results **)
Lemma discharge_env_lookup : forall e d x, lookup (discharge_env e d) x = option_map (fun v => discharge v d) (lookup e x).
Proof.
  induction e; simpl; auto.
  destruct a as (x,dv).
  intros d x'.
  destruct (x' == x); simpl; subst; auto.
Qed.

Lemma dom_discharge_h : forall dh d, dom dh ⊆ dom (discharge_h dh d).
Proof.
  destruct d; simpl; auto using coext_refl.
  intros a K.
  destruct K.
  apply Dom with (b:=discharge_r b Indet).
  rewrite H.
  trivial.
Qed.

Lemma discharge_det_v : forall dv, discharge dv Det = dv.
Proof.
  destruct dv; trivial.
Qed.

Lemma discharge_det_env : forall dρ, discharge_env dρ Det = dρ.
Proof.
  induction dρ; simpl; auto.
  destruct a as (x,dv).
  rewrite discharge_det_v.
  rewrite IHdρ.
  trivial.
Qed.

Lemma discharge_det_r : forall dr, discharge_r dr Det = dr.
Proof.
  destruct dr; unfold discharge_r; simpl.
  rewrite discharge_det_env.
  trivial.
Qed.

(** discharging an element makes it model any concrete counterpart **)
Lemma models_v_clobber: forall μ dv v, models_v μ (discharge dv Indet) v.
Proof.
  destruct dv; simpl; auto using models_v.
Qed.

Lemma models_r_clobber : forall μ dr r, models_r μ (discharge_r dr Indet) r.
Proof.
  intros.
  constructor.
  intro x.
  unfold discharge_r.
  unfold drecord_lookup.
  simpl.
  rewrite discharge_env_lookup.
  destruct (lookup dr x); simpl.
    apply models_v_clobber.

    constructor.
Qed.

Lemma models_h_clobber : forall μ dh h, models_h μ (discharge_h dh Indet) h.
Proof.
  constructor.
  intros a r K.
  simpl.
  destruct (dh (μ a)).
    solve [eauto using models_r_clobber].

    exists (DRecord nil Indet).
    constructor; auto.
    constructor.
    intro x; unfold drecord_lookup; simpl.
    constructor.
Qed.

(** relationship between discharging and the ≼ relation **)
Lemma dvalue_leq_discharge : forall dv d, dv ≼ discharge dv d.
Proof.
  destruct dv; destruct d0; simpl discharge; firstorder.
Qed.

Lemma denv_leq_discharge : forall dρ d, dρ ≼ discharge_env dρ d.
Proof.
  induction dρ; simpl discharge_env; auto using (@leq_refl (env name dvalue)).
  destruct a as (x, dv).
  intros d y.
  simpl lookup.
  destruct (y == x); subst.
    inversion 1; subst.
    eauto using dvalue_leq_discharge.

    inversion 1; subst.
    edestruct IHdρ; eauto.
Qed.

Lemma drecord_leq_discharge : forall dr d, dr ≼ discharge_r dr d.
Proof.
  destruct dr as (bindings, complete).
  intros d x.
  unfold discharge_r.
  unfold drecord_lookup; simpl.
  remember (lookup bindings x) as bx; destruct bx.
    edestruct (denv_leq_discharge bindings d x) as (dv&?&?); eauto.
    rewrite H.
    exact H0.

    rewrite discharge_env_lookup.
    rewrite <- Heqbx.
    simpl.
    destruct d; simpl; firstorder.
Qed.

Lemma drecord_leq_discharge_Indet : forall dr dr', dr ≼ discharge_r dr' Indet.
Proof.
  intros (b, c) (b', c') a.
  unfold drecord_lookup.
  simpl bindings.
  rewrite discharge_env_lookup.
  destruct (lookup b' a); simpl.
    destruct d; right; auto.

    right; auto.
Qed.

Lemma dheap_leq_discharge : forall dh d, dh ≼ (discharge_h dh d).
Proof.
  destruct d; simpl discharge_h; auto using (@leq_refl dheap).
  intros a dr K.
  rewrite K.
  eauto using drecord_leq_discharge.
Qed.

