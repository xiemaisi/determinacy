(** The substructure relations. A record r is a substructure of another record r' if r' has all
    the properties of r. A heap h is a substructure of another heap h' if, for every record
    at address a in h, h' has a record r' at the same address such that r is a substructure of r'. **)
Set Implicit Arguments.

Require Import Common Eq FinMap InstrumentedValues.

Definition substruct_r (dr dr':drecord) :=
  forall p dv, lookup dr.(bindings) p = Some dv -> exists dv', lookup dr'.(bindings) p = Some dv'.

Definition substruct_h (dh dh':dheap) :=
  forall a dr, dh a = Some dr -> exists dr', dh' a = Some dr' /\ substruct_r dr dr'.

(** substructure is a preorder **)
Lemma substruct_r_refl : forall dr, substruct_r dr dr.
Proof.
  unfold substruct_r; eauto.
Qed.

Lemma substruct_r_trans : forall dr₁ dr₂ dr₃, substruct_r dr₁ dr₂ -> substruct_r dr₂ dr₃ -> substruct_r dr₁ dr₃.
Proof.
  intros dr₁ dr₂ dr₃ K₁ K₂ a dr K₃.
  edestruct K₁ as (dr'&?); eauto.
Qed.

Lemma substruct_h_refl : forall dh, substruct_h dh dh.
Proof.
  unfold substruct_h; eauto using substruct_r_refl.
Qed.

Lemma substruct_h_trans : forall dh₁ dh₂ dh₃, substruct_h dh₁ dh₂ -> substruct_h dh₂ dh₃ -> substruct_h dh₁ dh₃.
Proof.
  intros dh₁ dh₂ dh₃ K₁ K₂ p dv K₃.
  edestruct K₁ as (dr'&?&?); eauto.
  edestruct K₂ as (dr''&?&?); eauto using substruct_r_trans.
Qed.

(** compatibility with record update **)
Lemma substruct_r_update : forall dr dr' p dv dv',
  substruct_r dr dr' -> substruct_r (drecord_update dr p dv) (drecord_update dr' p dv').
Proof.
  intros dr dr' p dv dv' K₁ p'' dv''.
  destruct (p'' == p); subst; unfold drecord_update; simpl.
    erewrite ! if_eq; eauto.

    erewrite ! if_neq; eauto.
Qed.
    
Lemma substruct_r_update_r : forall dr dr' p dv,
  substruct_r dr dr' -> substruct_r dr (drecord_update dr' p dv).
Proof.
  intros dr dr' p dv K₁ p' dv'.
  destruct (p' == p); subst; unfold drecord_update; simpl.
    erewrite ! if_eq; eauto.

    erewrite ! if_neq; eauto.
Qed.
    
