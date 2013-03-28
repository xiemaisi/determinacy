(** instrumented semantics **)
Set Implicit Arguments.

Require Import Common Eq FinMap Syntax Values Parameters InstrumentedValues Discharging Clobbering Reverting Domains Modelling.

Parameter k : nat.

Reserved Notation "〈 h , ρ , s 〉 ↓^ n 〈 h' , ρ' , e 〉" (at level 200, n at level 10, no associativity).

Inductive dred : dheap -> env name dvalue -> stmt -> nat -> dheap -> env name dvalue -> devent -> Prop :=
| DLdLit : forall dh dρ x (pv:primval) n,
             〈dh, dρ, SLoadLit x pv〉 ↓^(n) 
              〈dh, update dρ x (DVPrim pv Det), DEVarWrite x (DVPrim pv Det)〉
| DLdClos : forall dh dρ x xs ys s z n,
           let dv := DVClos xs ys s z dρ Det in
             〈dh, dρ, SLoadLit x (LFun xs ys s z)〉 ↓^(n)
              〈dh, update dρ x dv, DEVarWrite x dv〉
| DLdRec : forall dh dρ x a n, a ∉ (dom dh) ->
             〈dh, dρ, SLoadLit x LRec〉 ↓^(n)
              〈fupdate dh a (Some (DRecord nil Det)), update dρ x (DVAddr a Det), DEVarWrite x (DVAddr a Det)〉
| DAssign : forall dh dρ x y dv n, lookup dρ y = Some dv ->
             〈dh, dρ, SVarCopy x y〉 ↓^(n)
              〈dh, update dρ x dv, DEVarWrite x dv〉
| DLd : forall (dh:dheap) dρ x y z a d₁ pv d₂ dr dv n,
        let dv' := discharge (discharge dv d₁) d₂ in
           lookup dρ y = Some (DVAddr a d₁) -> lookup dρ z = Some (DVPrim pv d₂) -> dh a = Some dr -> 
           drecord_lookup dr (tostring pv) = dv ->
             〈dh, dρ, SPropRead x y z〉 ↓^(n)
              〈dh, update dρ x dv', DEVarWrite x dv'〉
| DSto : forall (dh:dheap) dρ x y z a d₁ pv d₂ dr dv n,
            lookup dρ x = Some (DVAddr a d₁) -> lookup dρ y = Some (DVPrim pv d₂) -> dh a = Some dr -> 
            lookup dρ z = Some dv ->
             〈dh, dρ, SPropWrite x y z〉 ↓^(n)
              〈discharge_h (fupdate dh a (Some (discharge_r (drecord_update dr (tostring pv) dv) d₂))) d₁, 
               dρ, 
               DEPropWrite a d₁ (tostring pv) d₂ dv〉
| DPrimOp : forall dh (dρ:env name dvalue) x y o z (v₁ v₂ v₃:primval) d₁ d₂ n,
            let dv := (discharge (DVPrim v₃ d₁) d₂) in
             lookup dρ y = Some (DVPrim v₁ d₁) -> lookup dρ z = Some (DVPrim v₂ d₂) -> primop_eval v₁ o v₂ = Some v₃ ->
             〈dh, dρ, SPrimOp x y o z〉 ↓^(n)
              〈dh, update dρ x dv, DEVarWrite x dv〉
| DCall : forall dh dρ x f y p ys b z dρ' dv dh' dρ'' dv' de d n,
            lookup dρ f = Some (DVClos p ys b z dρ' d) -> lookup dρ y = Some dv ->
            (〈dh, updates (update dρ' p dv) ys (DVPrim undefined Det), b〉 ↓^(n) 〈dh', dρ'', de〉) -> lookup dρ'' z = Some dv' ->
             〈dh, dρ, SFunCall x f y〉 ↓^(n)
              〈discharge_h dh' d, update dρ x (discharge dv' d), DESeq (DECall dv dρ' de d) (DEVarWrite x (discharge dv' d))〉
| DIfTrue : forall dh dh' dρ dρ' x s dv de n,
             lookup dρ x = Some dv -> truthy (strip_v dv) ->
             (〈dh, dρ, s〉 ↓^(n) 〈dh', dρ', de〉) ->
              〈dh, dρ, SIf x s〉 ↓^(n) 〈discharge_evt_h dh' de (get_det dv), discharge_names dρ' (vd (strip_evt de)) (get_det dv), DECond dv de〉
| DIfFalseDet : forall dh dρ x s dv n,
             lookup dρ x = Some dv -> ~truthy (strip_v dv) -> get_det dv = Det ->
              〈dh, dρ, SIf x s〉 ↓^(n) 〈dh, dρ, DECond dv DESkip〉
| DDCntr : forall dh dh' dρ dρ' x s dv de n,
             lookup dρ x = Some dv -> ~truthy (strip_v dv) -> get_det dv = Indet -> n < k ->
             (〈dh, dρ, s〉 ↓^(n) 〈dh', dρ', de〉) ->
              〈dh, dρ, SIf x s〉 ↓^(n) 〈revert_evt_h de dh' dh, revert_names (vd (strip_evt de)) dρ' dρ, DECond dv de〉
| DCntrAbort : forall dh dρ x s dv n,
             lookup dρ x = Some dv -> ~truthy (strip_v dv) -> get_det dv = Indet -> n >= k ->
              〈dh, dρ, SIf x s〉 ↓^(n) 〈discharge_h dh Indet, clobber_names (syntactic_vd s) dρ, DECond dv DESkip〉
| DSkip : forall dh dρ n,
             〈dh, dρ, SSkip〉 ↓^(n)
              〈dh, dρ, DESkip〉
| DSeq : forall dh dρ s₁ s₂ dh' dρ' dh'' dρ'' e₁ e₂ n,
             (〈dh, dρ, s₁〉 ↓^(n) 〈dh', dρ', e₁〉) ->
             (〈dh', dρ', s₂〉 ↓^(n) 〈dh'', dρ'', e₂〉) ->
              (〈dh, dρ, SSeq s₁ s₂〉 ↓^(n) 〈dh'', dρ'', DESeq e₁ e₂〉)

where "〈 dh , dρ , s 〉 ↓^ n 〈 h' , dρ' , e 〉" := (dred dh dρ s n h' dρ' e).

Lemma dred_dom_expand : forall dh dρ s dh' dρ' de n, 〈dh, dρ, s〉 ↓^(n) 〈dh', dρ', de〉 ->
  dom dh ⊆ dom dh'.
Proof.
  induction 1; eauto using dom_discharge_h, dom_discharge_evt_h, dom_clobber_evt_h, dom_revert_evt_h₂.
Qed.

