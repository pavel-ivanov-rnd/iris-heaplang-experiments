From iris.proofmode Require Import tactics.
From iris.base_logic Require Import namespaces.
From iris_examples.iris_logrel.F_mu_ref_conc Require Import examples.lock.
Import uPred.

Definition CG_StackType τ :=
  TRec (TSum TUnit (TProd τ.[ren (+1)] (TVar 0))).

(* Coarse-grained push *)
Definition CG_push (st : expr) : expr :=
  Rec (Store
         (st.[ren (+2)]) (Fold (InjR (Pair (Var 1) (Load st.[ren (+ 2)]))))).

Definition CG_locked_push (st l : expr) := with_lock (CG_push st) l.
Definition CG_locked_pushV (st l : expr) : val := with_lockV (CG_push st) l.

Definition CG_pop (st : expr) : expr :=
  Rec (Case (Unfold (Load st.[ren (+ 2)]))
            (InjL Unit)
            (
              App (Rec (InjR (Fst (Var 2))))
                  (Store st.[ren (+ 3)] (Snd (Var 0)))
            )
      ).

Definition CG_locked_pop (st l : expr) := with_lock (CG_pop st) l.
Definition CG_locked_popV (st l : expr) : val := with_lockV (CG_pop st) l.

Definition CG_snap (st l : expr) :=  with_lock (Rec (Load st.[ren (+2)])) l.
Definition CG_snapV (st l : expr) : val := with_lockV (Rec (Load st.[ren (+2)])) l.

Definition CG_iter (f : expr) : expr :=
  Rec (Case (Unfold (Var 1))
            Unit
            (
              App (Rec (App (Var 3) (Snd (Var 2))))
                  (App f.[ren (+3)] (Fst (Var 0)))
            )
      ).

Definition CG_iterV (f : expr) : val :=
  RecV (Case (Unfold (Var 1))
            Unit
            (
              App (Rec (App (Var 3) (Snd (Var 2))))
                  (App f.[ren (+3)] (Fst (Var 0)))
            )
      ).

Definition CG_snap_iter (st l : expr) : expr :=
  Rec (App (CG_iter (Var 1)) (App (CG_snap st.[ren (+2)] l.[ren (+2)]) Unit)).
Definition CG_stack_body (st l : expr) : expr :=
  Pair (Pair (CG_locked_push st l) (CG_locked_pop st l))
       (CG_snap_iter st l).

Definition CG_stack : expr :=
  TLam (App (Rec (App (Rec (CG_stack_body (Var 1) (Var 3)))
                (Alloc (Fold (InjL Unit))))) newlock).

Section CG_Stack.
  Context `{heapIG Σ, cfgSG Σ}.

  Lemma CG_push_type st Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ (CG_push st) (TArrow τ TUnit).
  Proof.
    intros H1. repeat econstructor.
    eapply (context_weakening [_; _]); eauto.
    repeat constructor; asimpl; trivial.
    eapply (context_weakening [_; _]); eauto.
  Qed.

  Lemma CG_push_closed (st : expr) :
    (∀ f, st.[f] = st) → ∀ f, (CG_push st).[f] = CG_push st.
  Proof. intros Hst f. unfold CG_push. asimpl. rewrite ?Hst; trivial. Qed.

  Lemma CG_push_subst (st : expr) f : (CG_push st).[f] = CG_push st.[f].
  Proof. unfold CG_push; asimpl; trivial. Qed.

  Lemma steps_CG_push E ρ j K st v w :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ st ↦ₛ v ∗ j ⤇ fill K (App (CG_push (Loc st)) (of_val w))
    ⊢ |={E}=> j ⤇ fill K Unit ∗ st ↦ₛ FoldV (InjRV (PairV w v)).
  Proof.
    intros HNE. iIntros "[#Hspec [Hx Hj]]". unfold CG_push.
    iMod (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iMod (step_load _ _ j (PairRCtx _ :: InjRCtx :: FoldCtx :: StoreRCtx (LocV _) :: K)
                    _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    simpl. iFrame "Hspec Hj"; trivial. simpl.
    iMod (step_store _ _ j K _ _ _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    { by iFrame. }
    iModIntro. by iFrame.
    Unshelve.
    all: try match goal with |- to_val _ = _ => auto using to_of_val end.
    simpl; by rewrite ?to_of_val.
  Qed.

  Global Opaque CG_push.

  Lemma CG_locked_push_to_val st l :
    to_val (CG_locked_push st l) = Some (CG_locked_pushV st l).
  Proof. trivial. Qed.

  Lemma CG_locked_push_of_val st l :
    of_val (CG_locked_pushV st l) = CG_locked_push st l.
  Proof. trivial. Qed.

  Global Opaque CG_locked_pushV.

  Lemma CG_locked_push_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_locked_push st l) (TArrow τ TUnit).
  Proof.
    intros H1 H2. repeat econstructor.
    eapply with_lock_type; auto using CG_push_type.
  Qed.

  Lemma CG_locked_push_closed (st l : expr) :
    (∀ f, st.[f] = st) → (∀ f, l.[f] = l) →
    ∀ f, (CG_locked_push st l).[f] = CG_locked_push st l.
  Proof.
    intros H1 H2 f. asimpl. unfold CG_locked_push.
    rewrite with_lock_closed; trivial. apply CG_push_closed; trivial.
  Qed.

  Lemma CG_locked_push_subst (st l : expr) f :
    (CG_locked_push st l).[f] = CG_locked_push st.[f] l.[f].
  Proof. by rewrite with_lock_subst CG_push_subst. Qed.

  Lemma steps_CG_locked_push E ρ j K st w v l :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ st ↦ₛ v ∗ l ↦ₛ (#♭v false)
      ∗ j ⤇ fill K (App (CG_locked_push (Loc st) (Loc l)) (of_val w))
    ⊢ |={E}=> j ⤇ fill K Unit ∗ st ↦ₛ FoldV (InjRV (PairV w v)) ∗ l ↦ₛ (#♭v false).
  Proof.
    intros HNE. iIntros "[#Hspec [Hx [Hl Hj]]]". unfold CG_locked_push.
    iMod (steps_with_lock
            _ _ j K _ _ _ _ UnitV _ _ _ with "[Hj Hx Hl]") as "Hj"; last done.
    - iIntros (K') "[#Hspec [Hx Hj]]".
      iApply steps_CG_push; first done. iFrame. iSplitR; trivial.
    - iFrame "Hspec Hj Hx"; trivial.
      Unshelve. all: trivial.
  Qed.

  Global Opaque CG_locked_push.

  (* Coarse-grained pop *)
  Lemma CG_pop_type st Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ (CG_pop st) (TArrow TUnit (TSum TUnit τ)).
  Proof.
    intros H1.
    econstructor.
    eapply (Case_typed _ _ _ _ TUnit);
      [| repeat constructor
       | repeat econstructor; eapply (context_weakening [_; _; _]); eauto].
    replace (TSum TUnit (TProd τ (CG_StackType τ))) with
    ((TSum TUnit (TProd τ.[ren (+1)] (TVar 0))).[(CG_StackType τ)/])
      by (by asimpl).
    repeat econstructor.
    eapply (context_weakening [_; _]); eauto.
  Qed.

  Lemma CG_pop_closed (st : expr) :
    (∀ f, st.[f] = st) → ∀ f, (CG_pop st).[f] = CG_pop st.
  Proof. intros Hst f. unfold CG_pop. asimpl. rewrite ?Hst; trivial. Qed.

  Lemma CG_pop_subst (st : expr) f : (CG_pop st).[f] = CG_pop st.[f].
  Proof. unfold CG_pop; asimpl; trivial. Qed.

  Lemma steps_CG_pop_suc E ρ j K st v w :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ st ↦ₛ FoldV (InjRV (PairV w v)) ∗
               j ⤇ fill K (App (CG_pop (Loc st)) Unit)
      ⊢ |={E}=> j ⤇ fill K (InjR (of_val w)) ∗ st ↦ₛ v.
  Proof.
    intros HNE. iIntros "[#Hspec [Hx Hj]]". unfold CG_pop.
    iMod (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iMod (step_load _ _ j (UnfoldCtx :: CaseCtx _ _ :: K)
                    _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iMod (step_Fold  _ _ j (CaseCtx _ _ :: K)
                    _ _ _ _ with "[Hj]") as "Hj"; eauto.
    simpl.
    iMod (step_case_inr _ _ j K _ _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iMod (step_snd _ _ j (StoreRCtx (LocV _) :: AppRCtx (RecV _) :: K) _ _ _ _
                   _ _ with "[Hj]") as "Hj"; eauto.
    simpl.
    iMod (step_store _ _ j (AppRCtx (RecV _) :: K) _ _ _ _ _ _
          with "[Hj Hx]") as "[Hj Hx]"; eauto.
    rewrite ?fill_app. simpl.
    iFrame "Hspec Hj"; trivial.
    rewrite ?fill_app. simpl.
    iMod (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iMod (step_fst _ _ j (InjRCtx :: K) _ _ _ _ _ _
          with "[Hj]") as "Hj"; eauto.
    simpl.
    iModIntro. iFrame "Hj Hx"; trivial.
    Unshelve.
    all: try match goal with |- to_val _ = _ => simpl; by rewrite ?to_of_val end.
    all: trivial.
  Qed.

  Lemma steps_CG_pop_fail E ρ j K st :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ st ↦ₛ FoldV (InjLV UnitV) ∗
               j ⤇ fill K (App (CG_pop (Loc st)) Unit)
      ⊢ |={E}=> j ⤇ fill K (InjL Unit) ∗ st ↦ₛ FoldV (InjLV UnitV).
  Proof.
    iIntros (HNE) "[#Hspec [Hx Hj]]". unfold CG_pop.
    iMod (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iMod (step_load _ _ j (UnfoldCtx :: CaseCtx _ _ :: K)
                    _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    simpl. iFrame "Hspec Hj"; trivial. simpl.
    iMod (step_Fold _ _ j (CaseCtx _ _ :: K)
                    _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iMod (step_case_inl _ _ j K _ _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iModIntro. iFrame "Hj Hx"; trivial.
    Unshelve.
    all: try match goal with |- to_val _ = _ => simpl; by rewrite ?to_of_val end.
    all: trivial.
  Qed.

  Global Opaque CG_pop.

  Lemma CG_locked_pop_to_val st l :
    to_val (CG_locked_pop st l) = Some (CG_locked_popV st l).
  Proof. trivial. Qed.

  Lemma CG_locked_pop_of_val st l :
    of_val (CG_locked_popV st l) = CG_locked_pop st l.
  Proof. trivial. Qed.

  Global Opaque CG_locked_popV.

  Lemma CG_locked_pop_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_locked_pop st l) (TArrow TUnit (TSum TUnit τ)).
  Proof.
    intros H1 H2. repeat econstructor.
    eapply with_lock_type; auto using CG_pop_type.
  Qed.

  Lemma CG_locked_pop_closed (st l : expr) :
    (∀ f, st.[f] = st) → (∀ f, l.[f] = l) →
    ∀ f, (CG_locked_pop st l).[f] = CG_locked_pop st l.
  Proof.
    intros H1 H2 f. asimpl. unfold CG_locked_pop.
    rewrite with_lock_closed; trivial. apply CG_pop_closed; trivial.
  Qed.

  Lemma CG_locked_pop_subst (st l : expr) f :
  (CG_locked_pop st l).[f] = CG_locked_pop st.[f] l.[f].
  Proof. by rewrite with_lock_subst CG_pop_subst. Qed.

  Lemma steps_CG_locked_pop_suc E ρ j K st v w l :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ st ↦ₛ FoldV (InjRV (PairV w v)) ∗ l ↦ₛ (#♭v false)
               ∗ j ⤇ fill K (App (CG_locked_pop (Loc st) (Loc l)) Unit)
      ⊢ |={E}=> j ⤇ fill K (InjR (of_val w)) ∗ st ↦ₛ v ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE) "[#Hspec [Hx [Hl Hj]]]". unfold CG_locked_pop.
    iMod (steps_with_lock _ _ j K _ _ _ _ (InjRV w) UnitV _ _
          with "[Hj Hx Hl]") as "Hj"; last done.
    - iIntros (K') "[#Hspec [Hx Hj]]".
      iApply steps_CG_pop_suc; first done. iFrame. by iSplitR.
    - iFrame "Hspec Hj Hx"; trivial.
      Unshelve. all: trivial.
  Qed.

  Lemma steps_CG_locked_pop_fail E ρ j K st l :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ st ↦ₛ FoldV (InjLV UnitV) ∗ l ↦ₛ (#♭v false)
               ∗ j ⤇ fill K (App (CG_locked_pop (Loc st) (Loc l)) Unit)
      ⊢ |={E}=> j ⤇ fill K (InjL Unit) ∗ st ↦ₛ FoldV (InjLV UnitV) ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE) "[#Hspec [Hx [Hl Hj]]]". unfold CG_locked_pop.
    iMod (steps_with_lock _ _ j K _ _ _ _ (InjLV UnitV) UnitV _ _
          with "[Hj Hx Hl]") as "Hj"; last done.
    - iIntros (K') "[#Hspec [Hx Hj]] /=".
      iApply steps_CG_pop_fail; first done. iFrame. by iSplitR.
    - iFrame "Hspec Hj Hx"; trivial.
      Unshelve. all: trivial.
  Qed.

  Global Opaque CG_locked_pop.

  Lemma CG_snap_to_val st l : to_val (CG_snap st l) = Some (CG_snapV st l).
  Proof. trivial. Qed.

  Lemma CG_snap_of_val st l : of_val (CG_snapV st l) = CG_snap st l.
  Proof. trivial. Qed.

  Global Opaque CG_snapV.

  Lemma CG_snap_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_snap st l) (TArrow TUnit (CG_StackType τ)).
  Proof.
    intros H1 H2. repeat econstructor.
    eapply with_lock_type; trivial. do 2 constructor.
    eapply (context_weakening [_; _]); eauto.
  Qed.

  Lemma CG_snap_closed (st l : expr) :
    (∀ f, st.[f] = st) → (∀ f, l.[f] = l) →
    ∀ f, (CG_snap st l).[f] = CG_snap st l.
  Proof.
    intros H1 H2 f. asimpl. unfold CG_snap.
    rewrite with_lock_closed; trivial.
    intros f'. by asimpl; rewrite ?H1.
  Qed.

  Lemma CG_snap_subst (st l : expr) f :
    (CG_snap st l).[f] = CG_snap st.[f] l.[f].
  Proof. unfold CG_snap; rewrite ?with_lock_subst. by asimpl. Qed.

  Lemma steps_CG_snap E ρ j K st v l :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ st ↦ₛ v ∗ l ↦ₛ (#♭v false)
               ∗ j ⤇ fill K (App (CG_snap (Loc st) (Loc l)) Unit)
      ⊢ |={E}=> j ⤇ (fill K (of_val v)) ∗ st ↦ₛ v ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE) "[#Hspec [Hx [Hl Hj]]]". unfold CG_snap.
    iMod (steps_with_lock _ _ j K _ _ (st ↦ₛ v) _ v UnitV _ _
          with "[Hj Hx Hl]") as "Hj"; last done; [|iFrame; iFrame "#"].
    iIntros (K') "[#Hspec [Hx Hj]]".
    iMod (step_rec _ _ j K' _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iMod (step_load _ _ j K' _ _ _ _
          with "[Hj Hx]") as "[Hj Hx]"; eauto.
    - iFrame "#"; iFrame.
    - iModIntro. by iFrame "Hj Hx".
      Unshelve.
      all: try match goal with |- to_val _ = _ => simpl; by rewrite ?to_of_val end.
      all: trivial.
  Qed.

  Global Opaque CG_snap.

  (* Coarse-grained iter *)
  Lemma CG_iter_folding (f : expr) :
    CG_iter f =
    Rec (Case (Unfold (Var 1))
              Unit
              (
                App (Rec (App (Var 3) (Snd (Var 2))))
                    (App f.[ren (+3)] (Fst (Var 0)))
              )
        ).
  Proof. trivial. Qed.

  Lemma CG_iter_type f Γ τ :
    typed Γ f (TArrow τ TUnit) →
    typed Γ (CG_iter f) (TArrow (CG_StackType τ) TUnit).
  Proof.
    intros H1.
    econstructor.
    eapply (Case_typed _ _ _ _ TUnit);
      [| repeat constructor
       | repeat econstructor; eapply (context_weakening [_; _; _]); eauto].
    replace (TSum TUnit (TProd τ (CG_StackType τ))) with
    ((TSum TUnit (TProd τ.[ren (+1)] (TVar 0))).[(CG_StackType τ)/])
      by (by asimpl).
    repeat econstructor.
  Qed.

  Lemma CG_iter_to_val f : to_val (CG_iter f) = Some (CG_iterV f).
  Proof. trivial. Qed.

  Lemma CG_iter_of_val f : of_val (CG_iterV f) = CG_iter f.
  Proof. trivial. Qed.

  Global Opaque CG_iterV.

  Lemma CG_iter_closed (f : expr) :
    (∀ g, f.[g] = f) → ∀ g, (CG_iter f).[g] = CG_iter f.
  Proof. intros Hf g. unfold CG_iter. asimpl. rewrite ?Hf; trivial. Qed.

  Lemma CG_iter_subst (f : expr) g : (CG_iter f).[g] = CG_iter f.[g].
  Proof. unfold CG_iter; asimpl; trivial. Qed.

  Lemma steps_CG_iter E ρ j K f v w :
    nclose specN ⊆ E →
    spec_ctx ρ
             ∗ j ⤇ fill K (App (CG_iter (of_val f))
                               (Fold (InjR (Pair (of_val w) (of_val v)))))
      ⊢ |={E}=>
    j ⤇ fill K
          (App
             (Rec
                (App ((CG_iter (of_val f)).[ren (+2)])
                     (Snd (Pair ((of_val w).[ren (+2)]) (of_val v).[ren (+2)]))))
             (App (of_val f) (of_val w))).
  Proof.
    iIntros (HNE) "[#Hspec Hj]". unfold CG_iter.
    iMod (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    rewrite -CG_iter_folding. Opaque CG_iter. asimpl.
    iMod (step_Fold _ _ j (CaseCtx _ _ :: K)
                    _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iMod (step_case_inr _ _ j K _ _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iMod (step_fst _ _ j (AppRCtx f :: AppRCtx (RecV _) :: K) _ _ _ _
                   _ _ with "[Hj]") as "Hj"; eauto.
    Unshelve.
    all: try match goal with |- to_val _ = _ => simpl; by rewrite ?to_of_val end.
  Qed.

  Transparent CG_iter.

  Lemma steps_CG_iter_end E ρ j K f :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K (App (CG_iter (of_val f)) (Fold (InjL Unit)))
      ⊢ |={E}=> j ⤇ fill K Unit.
  Proof.
    iIntros (HNE) "[#Hspec Hj]". unfold CG_iter.
    iMod (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    rewrite -CG_iter_folding. Opaque CG_iter. asimpl.
    iMod (step_Fold _ _ j (CaseCtx _ _ :: K)
                    _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iMod (step_case_inl _ _ j K _ _ _ _ _ with "[Hj]") as "Hj"; eauto.
    Unshelve.
    all: try match goal with |- to_val _ = _ => simpl; by rewrite ?to_of_val end.
  Qed.

  Global Opaque CG_iter.

  Lemma CG_snap_iter_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_snap_iter st l) (TArrow (TArrow τ TUnit) TUnit).
  Proof.
    intros H1 H2; repeat econstructor.
    - eapply CG_iter_type; by constructor.
    - eapply CG_snap_type; by eapply (context_weakening [_;_]).
  Qed.

  Lemma CG_snap_iter_closed (st l : expr) :
    (∀ f, st.[f] = st) → (∀ f, l.[f] = l) →
    ∀ f, (CG_snap_iter st l).[f] = CG_snap_iter st l.
  Proof.
    intros H1 H2 f. unfold CG_snap_iter. asimpl. rewrite H1 H2.
    rewrite CG_snap_closed; auto.
  Qed.

  Lemma CG_snap_iter_subst (st l : expr) g :
    (CG_snap_iter st l).[g] = CG_snap_iter st.[g] l.[g].
  Proof.
    unfold CG_snap_iter; asimpl.
    rewrite CG_snap_subst CG_iter_subst. by asimpl.
  Qed.

  Lemma CG_stack_body_type st l Γ τ :
    typed Γ st (Tref (CG_StackType τ)) →
    typed Γ l LockType →
    typed Γ (CG_stack_body st l)
          (TProd
             (TProd (TArrow τ TUnit) (TArrow TUnit (TSum TUnit τ)))
             (TArrow (TArrow τ TUnit) TUnit)
          ).
  Proof.
    intros H1 H2.
    repeat (econstructor; eauto using CG_locked_push_type,
                          CG_locked_pop_type, CG_snap_iter_type).
  Qed.

  Opaque CG_snap_iter.

  Lemma CG_stack_body_closed (st l : expr) :
    (∀ f, st.[f] = st) → (∀ f, l.[f] = l) →
    ∀ f, (CG_stack_body st l).[f] = CG_stack_body st l.
  Proof.
    intros H1 H2 f. unfold CG_stack_body. asimpl.
    rewrite CG_locked_push_closed; trivial.
    rewrite CG_locked_pop_closed; trivial.
    by rewrite CG_snap_iter_closed.
  Qed.

  Lemma CG_stack_type Γ :
    typed Γ CG_stack
          (TForall
             (TProd
                (TProd
                   (TArrow (TVar 0) TUnit)
                   (TArrow TUnit (TSum TUnit (TVar 0)))
                )
                (TArrow (TArrow (TVar 0) TUnit) TUnit)
          )).
  Proof.
    repeat econstructor.
    - eapply CG_locked_push_type; constructor; simpl; eauto.
    - eapply CG_locked_pop_type; constructor; simpl; eauto.
    - eapply CG_snap_iter_type; constructor; by simpl.
    - asimpl. repeat constructor.
    - eapply newlock_type.
  Qed.

  Lemma CG_stack_closed f : CG_stack.[f] = CG_stack.
  Proof.
    unfold CG_stack.
    asimpl; rewrite ?CG_locked_push_subst ?CG_locked_pop_subst.
    asimpl. rewrite ?CG_snap_iter_subst. by asimpl.
  Qed.
End CG_Stack.
