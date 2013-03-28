(* Haskell-like Eq typeclass *)
Set Implicit Arguments.

Require Import List String.

Class Eq A := {
  cmp : forall (a a':A), {a=a'}+{a<>a'}
}.
Notation "a == a'" := (cmp a a') (at level 70).

Instance nat_eq : Eq nat.
Proof.
  constructor.
  decide equality.
Qed.

Instance string_eq : Eq string.
Proof.
  constructor.
  apply string_dec.
Qed.

Section EqFacts.
  Variable A B : Type.
  Context `{Eq A}.

  Lemma if_eq : forall a a' (b b':B), a = a' -> (if a == a then b else b') = b.
  Proof.
    intros.
    destruct (a == a); congruence.
  Qed.

  Lemma if_neq : forall a a' (b b':B), a <> a' -> (if a == a' then b else b') = b'.
  Proof.
    intros.
    destruct (a == a'); congruence.
  Qed.

  Lemma neq_symm : forall (b b':B), b <> b' -> b' <> b.
  Proof.
    congruence.
  Qed.

  Lemma In_dec : forall (x:A) xs, {In x xs} + {~In x xs}.
  Proof.
    induction xs.
      right; auto.
    
      destruct (a == x); subst.
        left; simpl; auto.

        destruct IHxs.
          left; simpl; auto.

          right; red; inversion 1; auto.
  Qed.
End EqFacts.
Hint Resolve neq_symm.
