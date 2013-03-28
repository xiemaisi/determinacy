(* An implementation of finite maps as association lists. *)
Set Implicit Arguments.

Require Import Common Eq.
Require Import List.

Section FinMap.
  Variable A : Type.
  Context `{Eq A}.

  Section Defns.
    Variable B : Type.

    Definition env := list (A*B).

    Fixpoint lookup (e:env) (a:A) : option B :=
      match e with
        | nil => None
        | (a',b)::e' => if a == a' then Some b else lookup e' a
      end.
    Functional Scheme lookup_ind := Induction for lookup Sort Prop.
    Coercion lookup : env >-> Funclass.

    Inductive Lookup : env -> A -> B -> Prop :=
    | LookupCar : forall a b e, Lookup ((a,b)::e) a b
    | LookupCdr : forall a b a' b' e, a <> a' -> Lookup e a b -> Lookup ((a',b')::e) a b.

    Lemma lookup_Lookup : forall e a b, lookup e a = Some b -> Lookup e a b.
    Proof.
      intros.
      functional induction (lookup e a).
        discriminate H0.

        inversion H0; subst.
        constructor.

        eauto using Lookup.
    Qed.

    Lemma Lookup_lookup : forall e a b, Lookup e a b -> lookup e a = Some b.
    Proof.
      induction 1; simpl.
        erewrite if_eq; eauto.

        erewrite if_neq; eauto.
    Qed.

    Inductive mdom (e:env) : A -> Prop :=
    | MDom : forall a b, lookup e a = Some b -> mdom e a.
    
    Definition update (e:env) (a:A) (b:B) : env := (a,b)::e.

    Fixpoint updates (e:env) (l:list A) (deflt:B) :=
    match l with
    | nil => e
    | x::xs => update (updates e xs deflt) x deflt
    end.

    Definition agree_on (P:A->Prop) (e e':env) := forall a, a ∈ P -> e a = e' a.

    Lemma update_lookup_same : forall e a b, (update e a b) a = Some b.
    Proof.
      intros; unfold update; unfold lookup.
      erewrite if_eq; eauto.
    Qed.
    
    Lemma update_lookup_different : forall e a b a', a <> a' ->  lookup (update e a b) a' = lookup e a'.
    Proof.
      intros; unfold update; unfold lookup.
      erewrite if_neq; eauto.
    Qed.

(*    Lemma update_dom : forall e a b, dom e ⊆ dom (update e a b).
    Proof.
      intros e a b a'; unfold dom; simpl.
      destruct (a' == a); subst; eauto.
    Qed.*)

    Hint Unfold agree_on.
    Lemma agree_on_refl : forall P e, agree_on P e e.
    Proof. auto. Qed.

    Lemma agree_on_update : forall P e e', agree_on P e e' -> forall a b, a ∉ P -> agree_on P e (update e' a b).
    Proof.
      intros P e e' K1 a b K2 a' K3.
      simpl.
      destruct (a' == a); subst; intuition.
    Qed.
  End Defns.

  Section val_map.
    Variables B B' : Type.
    Variable f : B -> B'.

    Definition val_map : env B -> env B' :=
      map (fun e => (fst e, f (snd e))).

    Lemma lookup_val_map : forall e a, lookup (val_map e) a = option_map f (lookup e a).
    Proof.
      induction e; simpl; auto.
      destruct a as (a, b); simpl.
      intro a'.
      destruct (a' == a); simpl; auto.
    Qed.

(*    Lemma dom_val_map : forall e, dom (val_map e) ⊆ dom e /\ dom e ⊆ dom (val_map e).
    Proof.
      unfold dom.
      constructor.
        intros a (b,K).
        rewrite lookup_val_map in K.
        destruct (lookup e a); inversion K; eauto.

        intros a (b,K).
        rewrite lookup_val_map.
        destruct (lookup e a); simpl; inversion K; eauto.
    Qed.        *)
  End val_map.

  Lemma val_map_id : forall B (f:B->B), (forall b, f b = b) -> forall e, val_map f e = e.
  Proof.
    induction e; simpl; auto.
    destruct a as (a,b); simpl.
    congruence.
  Qed.
End FinMap.
Hint Resolve update_lookup_same update_lookup_different (*update_dom*).
Hint Resolve agree_on_refl agree_on_update.
