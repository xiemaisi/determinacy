(* Generally useful definitions and lemmas. *)
Set Implicit Arguments.

Require Export String List.
Require Import Eq.

Definition label := nat.
Definition address := nat.
Definition name := string.

Notation "[ x ]" := (cons x nil).

Definition option_map A B (f:A->B) (o:option A) :=
  match o with
  | Some a => Some (f a)
  | None => None
  end.

Definition subset A (P Q:A->Prop) := forall a, P a -> Q a.

Notation "P ⊆ Q" := (subset P Q) (at level 70).
Notation "x ∈ P" := (P x) (at level 60, only parsing).
Notation "x ∉ P" := (~P x) (at level 60, only parsing).

Class PreOrder A := {
  leq: A -> A -> Prop;
  leq_refl: forall a, leq a a;
  leq_trans: forall a b c, leq a b -> leq b c -> leq a c
}.
Notation "a ≼ b" := (leq a b) (at level 70).

Lemma subset_refl : forall A (P:A->Prop), P ⊆ P.
Proof. firstorder. Qed.

Lemma subset_trans : forall A (P Q R:A->Prop), P ⊆ Q -> Q ⊆ R -> P ⊆ R.
Proof. firstorder. Qed.

Hint Resolve subset_refl subset_trans.

Definition union A (X Y:A->Prop) : A -> Prop :=
  fun z => z ∈ X \/ z ∈ Y.
Notation "X ∪ Y" := (union X Y) (at level 60).

Lemma subset_union_r : forall A (P Q R:A->Prop), P ⊆ R -> P ⊆ Q ∪ R.
Proof.
  firstorder.
Qed.

Lemma subset_union_l : forall A (P Q R:A->Prop), P ⊆ Q -> P ⊆ Q ∪ R.
Proof.
  firstorder.
Qed.

Definition coextensive A (X Y:A->Prop) :=
  forall a, a ∈ X <-> a ∈ Y.
Notation "X ≡ Y" := (coextensive X Y) (at level 70).

Definition Just A (a:A) : A -> Prop := fun a' => a' = a.

Lemma coext_refl : forall A (X:A->Prop), X ≡ X.
Proof.
  firstorder.
Qed.

Lemma coext_symm : forall A (X Y:A->Prop), X ≡ Y -> Y ≡ X.
Proof.
  firstorder.
Qed.

Lemma coext_trans : forall A (X Y Z:A->Prop), X ≡ Y -> Y ≡ Z -> X ≡ Z.
Proof.
  firstorder.
Qed.

Lemma subset_coext : forall A (X Y Z:A->Prop), X ⊆ Y -> Y ≡ Z -> X ⊆ Z.
Proof.
  firstorder.
Qed.

Definition fupdate A `{Eq A} B (h:A->B) (a:A) (b:B) : A->B :=
  fun (a':A) => if a' == a then b else h a'.

Inductive dom A B (f:A->option B) : A -> Prop :=
| Dom : forall a b, f a = Some b -> dom f a.

Lemma fupdate_dom : forall A `{Eq A} B (f:A->option B) a b, dom (fupdate f a (Some b)) ≡ dom f ∪ Just a.
Proof.
  intros A K1 B f a b a'.
  unfold fupdate.
  constructor.
    inversion 1; subst.
    destruct (a' == a); subst.
      inversion H0; subst.
      right; unfold Just; solve [auto].

      left; solve [eauto using dom].

    destruct (a' == a); subst.
      intros _.
      apply Dom with (b:=b).
      erewrite if_eq; solve [eauto].

      inversion 1; subst.
        destruct H0.
        apply Dom with (b:=b0).
        rewrite if_neq; solve [eauto].

        tauto.
Qed.
Hint Resolve fupdate_dom.

Lemma coext_subset : forall A (X Y:A->Prop), X ≡ Y -> X ⊆ Y.
Proof.
  firstorder.
Qed.
Hint Resolve coext_subset.

Definition injective A B (f:A->B) (X:A->Prop) :=
  forall x x', x ∈ X -> x' ∈ X -> f x = f x' -> x = x'.

Lemma injective_add_one : forall A `{Eq A} B (f:A->B) (X:A->Prop) a b, (forall a', a' ∈ X -> f a' <> b) ->
  injective f X -> injective (fupdate f a b) (X ∪ Just a).
Proof.
  intros A K1 B f X a b K2 K3 x x'.
  unfold fupdate.
  destruct (x == a); subst.
    destruct (x' == a); subst; auto.
    inversion 2; subst.
      intro K4.
      exfalso.
      eapply K2; solve [eauto].

      inversion H1; subst.
      solve [trivial].

    inversion 1; subst.
      destruct (x' == a); subst; auto.
        intros _ K4.
        exfalso.
        eapply K2; solve [eauto].

        inversion 1; subst; eauto.
        tauto.

      inversion H0; subst.
      tauto.
Qed.

Lemma injective_coext : forall A B (f:A->B) (X Y:A->Prop), injective f X -> X ≡ Y -> injective f Y.
Proof.
  firstorder.
Qed.

Lemma dom_fupdate_subset : forall A `{Eq A} B (h:A->option B) a (b:B), dom h ⊆ dom (fupdate h a (Some b)).
Proof.
  intros.
  apply subset_coext with (Y := dom h ∪ Just a).
    firstorder.

    eauto using fupdate_dom, coext_symm.
Qed.
Hint Resolve dom_fupdate_subset.

Definition bind A B (f:A->option B) (o:option A) :=
  match o with
  | None => None
  | Some a => f a
  end.
Implicit Arguments bind [A B].

Definition agree A B (f g:A->B) (X:A->Prop) := forall x, x ∈ X -> f x = g x.

Lemma agree_self : forall A B (f:A->B) (X:A->Prop), agree f f X.
Proof.
  intros A B f X x K1.
  trivial.
Qed.
Hint Resolve agree_self.

Lemma agree_trans : forall A B (f g h:A->B) (X:A->Prop), agree f g X -> agree g h X -> agree f h X.
Proof.
  intros A B f g h X K1 K2 x K3.
  rewrite K1; auto.
Qed.

Lemma agree_subset : forall A B (f g:A->B) (X X':A->Prop), X ⊆ X' -> agree f g X' -> agree f g X.
Proof.
  firstorder.
Qed.

Lemma agree_fupdate : forall A `{Eq A} B (μ:A->B) a b X, a ∉ X -> agree μ (fupdate μ a b) X.
Proof.
  intros.
  intros a' K.
  unfold fupdate.
  destruct (a' == a); subst; intuition.
Qed.

(* not proved explicitly; would likely require classical logic, and isn't particularly interesting *)
Lemma injective_extension : forall (μ:address->address) (X Y:address->Prop), injective μ X -> X ⊆ Y ->
  exists μ', agree μ μ' X /\ injective μ' Y.
Proof. Admitted.
