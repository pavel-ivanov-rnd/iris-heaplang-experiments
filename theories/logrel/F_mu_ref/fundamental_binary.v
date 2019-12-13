From iris_examples.logrel.F_mu_ref Require Export logrel_binary.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From iris_examples.logrel.F_mu_ref Require Import rules_binary.

Section bin_log_def.
  Context `{heapG Σ,cfgSG Σ}.
  Notation D := (prodO valO valO -n> iProp Σ).

  Definition bin_log_related (Γ : list type) (e e' : expr) (τ : type) :=
    ∀ Δ vvs (ρ : cfg F_mu_ref_lang), env_Persistent Δ →
    spec_inv ρ ∗ ⟦ Γ ⟧* Δ vvs ⊢
    ⟦ τ ⟧ₑ Δ (e.[env_subst (vvs.*1)], e'.[env_subst (vvs.*2)]).
End bin_log_def.

Notation "Γ ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related Γ e e' τ) (at level 74, e, e', τ at next level).

Section fundamental.
  Context `{heapG Σ,cfgSG Σ}.
  Notation D := (prodO valO valO -n> iPropO Σ).
  Implicit Types e : expr.
  Implicit Types Δ : listO D.
  Local Hint Resolve to_of_val : core.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) ident(w)
        constr(Hv) uconstr(Hp) :=
    iApply (wp_bind (fill [ctx]));
    iApply (wp_wand with "[-]");
      [iApply Hp; iFrame "#"; trivial|];
    iIntros (v); iDestruct 1 as (w) Hv.

  (* Put all quantifiers at the outer level *)
  Lemma bin_log_related_alt {Γ e e' τ} : Γ ⊨ e ≤log≤ e' : τ → ∀ Δ vvs ρ K,
    env_Persistent Δ →
    spec_inv ρ ∗ ⟦ Γ ⟧* Δ vvs ∗ ⤇ fill K (e'.[env_subst (vvs.*2)])
    ⊢ WP e.[env_subst (vvs.*1)] {{ v, ∃ v',
        ⤇ fill K (of_val v') ∗ interp τ Δ (v, v') }}.
  Proof.
    iIntros (Hlog Δ vvs K ρ ?) "[#Hρ [HΓ Hj]]". asimpl.
    iApply (Hlog with "[HΓ]"); iFrame. eauto.
  Qed.

  Notation "'` H" := (bin_log_related_alt H) (at level 8).

  Lemma bin_log_related_var Γ x τ :
    Γ !! x = Some τ → Γ ⊨ Var x ≤log≤ Var x : τ.
  Proof.
    iIntros (? Δ vvs ρ ?) "[#Hρ #HΓ]". iIntros (K) "Hj /=".
    iDestruct (interp_env_Some_l with "HΓ") as ([v v']) "[Heq Hv]"; first done.
    iDestruct "Heq" as %Heq.
    erewrite !env_subst_lookup; rewrite ?list_lookup_fmap ?Heq; eauto.
    iApply wp_value; auto.
  Qed.

  Lemma bin_log_related_unit Γ : Γ ⊨ Unit ≤log≤ Unit : TUnit.
  Proof.
    iIntros (Δ vvs ρ ?) "#[Hρ HΓ]". iIntros (K) "Hj /=".
    iApply wp_value. iExists UnitV; eauto.
  Qed.

  Lemma bin_log_related_pair Γ e1 e2 e1' e2' τ1 τ2
      (IHHtyped1 : Γ ⊨ e1 ≤log≤ e1' : τ1)
      (IHHtyped2 : Γ ⊨ e2 ≤log≤ e2' : τ2) :
    Γ ⊨ Pair e1 e2 ≤log≤ Pair e1' e2' : TProd τ1 τ2.
  Proof.
    iIntros (Δ vvs ρ ?) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (PairLCtx e2.[env_subst _]) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ _ ((PairLCtx e2'.[env_subst _]) :: K)).
    smart_wp_bind (PairRCtx v) w w' "[Hw #Hiw]"
      ('`IHHtyped2 _ _ _ ((PairRCtx v') :: K)).
    iApply wp_value.
    iExists (PairV v' w'); iFrame "Hw".
    iExists (v, v'), (w, w'); simpl; repeat iSplit; trivial.
  Qed.

  Lemma bin_log_related_fst Γ e e' τ1 τ2
      (IHHtyped : Γ ⊨ e ≤log≤ e' : TProd τ1 τ2) :
    Γ ⊨ Fst e ≤log≤ Fst e' : τ1.
  Proof.
    iIntros (Δ vvs ρ ?) "[#Hρ #HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (FstCtx) v v' "[Hv #Hiv]" ('`IHHtyped _ _ _ (FstCtx :: K)); cbn.
    iDestruct "Hiv" as ([w1 w1'] [w2 w2']) "#[% [Hw1 Hw2]]"; simplify_eq.
    iMod (step_fst _ _ K (of_val w1') (of_val w2') with "[-]") as "Hw"; eauto.
    iApply wp_pure_step_later; auto. iApply wp_value; auto.
  Qed.

  Lemma bin_log_related_snd Γ e e' τ1 τ2
      (IHHtyped : Γ ⊨ e ≤log≤ e' : TProd τ1 τ2) :
    Γ ⊨ Snd e ≤log≤ Snd e' : τ2.
  Proof.
    iIntros (Δ vvs ρ ?) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (SndCtx) v v' "[Hv #Hiv]" ('`IHHtyped _ _ _ (SndCtx :: K)); cbn.
    iDestruct "Hiv" as ([w1 w1'] [w2 w2']) "#[% [Hw1 Hw2]]"; simplify_eq.
    iMod (step_snd _ _ K (of_val w1') (of_val w2') with "[-]") as "Hw"; eauto.
    iApply wp_pure_step_later; auto. iApply wp_value; auto.
  Qed.

  Lemma bin_log_related_injl Γ e e' τ1 τ2
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τ1) :
    Γ ⊨ InjL e ≤log≤ InjL e' : (TSum τ1 τ2).
  Proof.
    iIntros (Δ vvs ρ ?) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (InjLCtx) v v' "[Hv #Hiv]"
      ('`IHHtyped _ _ _ (InjLCtx :: K)); cbn.
    iApply wp_value. repeat rewrite /= to_of_val. eauto.
    iExists (InjLV v'); iFrame "Hv".
    iLeft; iExists (_,_); eauto 10.
  Qed.

  Lemma bin_log_related_injr Γ e e' τ1 τ2
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τ2) :
    Γ ⊨ InjR e ≤log≤ InjR e' : TSum τ1 τ2.
  Proof.
    iIntros (Δ vvs ρ ?) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (InjRCtx) v v' "[Hv #Hiv]"
      ('`IHHtyped _ _ _ (InjRCtx :: K)); cbn.
    iApply wp_value. repeat rewrite /= to_of_val. eauto.
    iExists (InjRV v'); iFrame "Hv".
    iRight; iExists (_,_); eauto 10.
  Qed.

  Lemma bin_log_related_case Γ e0 e1 e2 e0' e1' e2' τ1 τ2 τ3
      (Hclosed2 : ∀ f, e1.[upn (S (length Γ)) f] = e1)
      (Hclosed3 : ∀ f, e2.[upn (S (length Γ)) f] = e2)
      (Hclosed2' : ∀ f, e1'.[upn (S (length Γ)) f] = e1')
      (Hclosed3' : ∀ f, e2'.[upn (S (length Γ)) f] = e2')
      (IHHtyped1 : Γ ⊨ e0 ≤log≤ e0' : TSum τ1 τ2)
      (IHHtyped2 : τ1 :: Γ ⊨ e1 ≤log≤ e1' : τ3)
      (IHHtyped3 : τ2 :: Γ ⊨ e2 ≤log≤ e2' : τ3) :
    Γ ⊨ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' : τ3.
  Proof.
    iIntros (Δ vvs ρ ?) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    iDestruct (interp_env_length with "HΓ") as %?.
    smart_wp_bind (CaseCtx _ _) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ _ ((CaseCtx _ _) :: K)); cbn.
    iDestruct "Hiv" as "[Hiv|Hiv]".
    - iDestruct "Hiv" as ([w w']) "[% Hw]"; simplify_eq.
      iMod (step_case_inl _ _ K (of_val w') with "[-]") as "Hz"; eauto.
      simpl.
      iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
      asimpl. iApply ('`IHHtyped2 _ ((w,w') :: vvs)); repeat iSplit; eauto.
      iApply interp_env_cons; auto.
    - iDestruct "Hiv" as ([w w']) "[% Hw]"; simplify_eq.
      iMod (step_case_inr _ _ K (of_val w') with "[-]") as "Hz"; eauto.
      simpl.
      iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
      asimpl. iApply ('`IHHtyped3 _ ((w,w') :: vvs)); repeat iSplit; eauto.
      iApply interp_env_cons; auto.
  Qed.

  Lemma bin_log_related_lam Γ (e e' : expr) τ1 τ2
      (Hclosed : ∀ f, e.[upn (S (length Γ)) f] = e)
      (Hclosed' : ∀ f, e'.[upn (S (length Γ)) f] = e')
      (IHHtyped : τ1 :: Γ ⊨ e ≤log≤ e' : τ2) :
    Γ ⊨ Lam e ≤log≤ Lam e' : TArrow τ1 τ2.
  Proof.
    iIntros (Δ vvs ρ ?) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    iApply wp_value. iExists (LamV _). iIntros "{$Hj} !#".
    iIntros ([v v']) "#Hiv". iIntros (K') "Hj".
    iDestruct (interp_env_length with "HΓ") as %?.
    iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
    iMod (step_lam _ _ K' _ (of_val v') with "[-]") as "Hz"; eauto.
    asimpl. iApply ('`IHHtyped _ ((v,v') :: vvs)); repeat iSplit; eauto.
    iApply interp_env_cons; iSplit; auto.
  Qed.

  Lemma bin_log_related_app Γ e1 e2 e1' e2' τ1 τ2
      (IHHtyped1 : Γ ⊨ e1 ≤log≤ e1' : TArrow τ1 τ2)
      (IHHtyped2 : Γ ⊨ e2 ≤log≤ e2' : τ1) :
    Γ ⊨ App e1 e2 ≤log≤ App e1' e2' :  τ2.
  Proof.
    iIntros (Δ vvs ρ ?) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (AppLCtx (e2.[env_subst (vvs.*1)])) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ _ (((AppLCtx (e2'.[env_subst (vvs.*2)]))) :: K)); cbn.
    smart_wp_bind (AppRCtx v) w w' "[Hw #Hiw]"
                  ('`IHHtyped2 _ _ _ ((AppRCtx v') :: K)); cbn.
    iApply ("Hiv" $! (w, w') with "Hiw"); simpl; eauto.
  Qed.

  Lemma bin_log_related_tlam Γ e e' τ
      (IHHtyped : (subst (ren (+1)) <$> Γ) ⊨ e ≤log≤ e' : τ) :
    Γ ⊨ TLam e ≤log≤ TLam e' : TForall τ.
  Proof.
    iIntros (Δ vvs ρ ?) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    iApply wp_value. iExists (TLamV _).
    iIntros "{$Hj} /= !#"; iIntros (τi ? K') "Hv /=".
    iApply wp_pure_step_later; auto; iNext.
    iMod (step_tlam _ _ K' (e'.[env_subst (vvs.*2)]) with "[-]") as "Hz"; eauto.
    iApply '`IHHtyped; repeat iSplit; eauto. by iApply interp_env_ren.
  Qed.

  Lemma bin_log_related_tapp Γ e e' τ τ'
      (IHHtyped : Γ ⊨ e ≤log≤ e' : TForall τ) :
    Γ ⊨ TApp e ≤log≤ TApp e' : τ.[τ'/].
  Proof.
    iIntros (Δ vvs ρ ?) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (TAppCtx) v v' "[Hj #Hv]"
      ('`IHHtyped _ _ _ (TAppCtx :: K)).
    iApply wp_wand_r; iSplitL.
    { iSpecialize ("Hv" $! (interp τ' Δ) with "[#]"); [iPureIntro; apply _|].
      iApply "Hv"; eauto. }
    iIntros (w). iDestruct 1 as (w') "Hw".
    iExists _; rewrite -interp_subst; eauto.
  Qed.

  Lemma bin_log_related_fold Γ e e' τ
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τ.[(TRec τ)/]) :
    Γ ⊨ Fold e ≤log≤ Fold e' : TRec τ.
  Proof.
    iIntros (Δ vvs ρ ?) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    iApply (wp_bind (fill [FoldCtx])); iApply wp_wand_l; iSplitR;
        [|iApply ('`IHHtyped _ _ _ (FoldCtx :: K));
          rewrite ?fill_app; simpl; repeat iSplitR; trivial].
    iIntros (v); iDestruct 1 as (w) "[Hv #Hiv]".
    iApply wp_value. repeat rewrite /= to_of_val; eauto.
    iExists (FoldV w); iFrame "Hv".
    rewrite fixpoint_interp_rec1_eq /= -interp_subst.
    iAlways; iExists (_, _); eauto.
  Qed.

  Lemma bin_log_related_unfold Γ e e' τ
      (IHHtyped : Γ ⊨ e ≤log≤ e' : TRec τ) :
    Γ ⊨ Unfold e ≤log≤ Unfold e' : τ.[(TRec τ)/].
  Proof.
    iIntros (Δ vvs ρ ?) "#[Hρ HΓ]"; iIntros (K) "Hj /=".
    iApply (wp_bind (fill [UnfoldCtx])); iApply wp_wand_l; iSplitR;
        [|iApply ('`IHHtyped _ _ _ (UnfoldCtx :: K));
          rewrite ?fill_app; simpl; repeat iSplitR; trivial].
    iIntros (v). iDestruct 1 as (v') "[Hw #Hiw]".
    rewrite /= fixpoint_interp_rec1_eq /=.
    change (fixpoint _) with (interp (TRec τ) Δ).
    iDestruct "Hiw" as ([w w']) "#[% Hiz]"; simplify_eq/=.
    iMod (step_Fold _ _ K (of_val w') with "[-]") as "Hz"; eauto.
    iApply wp_pure_step_later; cbn; auto.
    iNext. iApply wp_value; auto. iExists _; iFrame "Hz".
      by rewrite -interp_subst.
  Qed.

  Lemma bin_log_related_alloc Γ e e' τ
      (IHHtyped : Γ ⊨ e ≤log≤ e' : τ) :
    Γ ⊨ Alloc e ≤log≤ Alloc e' : Tref τ.
  Proof.
    iIntros (Δ vvs ρ ?) "#[Hρ HΓ]". iIntros (K) "Hj /=".
    smart_wp_bind (AllocCtx) v v' "[Hv #Hiv]" ('`IHHtyped _ _ _ (AllocCtx :: K)).
    iMod (step_alloc _ _ K (of_val v') v' with "[Hv]") as (l') "[Hj Hl']"; eauto.
    iApply wp_fupd. iApply wp_alloc; auto.
    iIntros "!>"; iIntros (l) "Hl".
    iMod (inv_alloc (logN .@ (l,l')) _ (∃ w : val * val,
      l ↦ w.1 ∗ l' ↦ₛ w.2 ∗ interp τ Δ w)%I with "[Hl Hl']") as "HN"; eauto.
    { iNext; iExists (v, v'); by iFrame. }
    iModIntro; iExists (LocV l'). iFrame "Hj". iExists (l, l'). eauto.
  Qed.

  Lemma bin_log_related_load Γ e e' τ
      (IHHtyped : Γ ⊨ e ≤log≤ e' : (Tref τ)) :
    Γ ⊨ Load e ≤log≤ Load e' : τ.
  Proof.
    iIntros (Δ vvs ρ ?) "#[? HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (LoadCtx) v v' "[Hv #Hiv]" ('`IHHtyped _ _ _ (LoadCtx :: K)).
    simpl. iDestruct "Hiv" as ([l l']) "[% Hinv]"; simplify_eq.
    iInv (logN .@ (l,l')) as  ([w w']) "[Hw1 [Hw2 #Hw]]" "Hclose"; simpl.
    iMod "Hw2".
    iMod (step_load _ _ K l' 1 w' with "[Hv Hw2]") as "[Hv Hw2]";
      [solve_ndisj|by iFrame|].
    iApply (wp_load _ _ 1 with "[Hw1]"); eauto.
    iNext. iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]").
    { iNext. iExists (w,w'); by iFrame. }
    iModIntro. iExists w'; by iFrame.
  Qed.

  Lemma bin_log_related_store Γ e1 e2 e1' e2' τ
      (IHHtyped1 : Γ ⊨ e1 ≤log≤ e1' : (Tref τ))
      (IHHtyped2 : Γ ⊨ e2 ≤log≤ e2' : τ) :
    Γ ⊨ Store e1 e2 ≤log≤ Store e1' e2' : TUnit.
  Proof.
    iIntros (Δ vvs ρ ?) "#[? HΓ]"; iIntros (K) "Hj /=".
    smart_wp_bind (StoreLCtx _) v v' "[Hv #Hiv]"
      ('`IHHtyped1 _ _ _ ((StoreLCtx _) :: K)).
    smart_wp_bind (StoreRCtx _) w w' "[Hw #Hiw]"
      ('`IHHtyped2 _ _ _ ((StoreRCtx _) :: K)).
    simpl. iDestruct "Hiv" as ([l l']) "[% Hinv]"; simplify_eq/=.
    iInv (logN .@ (l,l')) as ([v v']) "[>Hv1 [>Hv2 #Hv]]" "Hclose".
    iMod (step_store _ _ K l' v' (of_val w') w' with "[Hw Hv2]")
      as "[Hw Hv2]"; [solve_ndisj|by iFrame|].
    iApply (wp_store with "[Hv1]"); eauto using to_of_val.
    iNext. iIntros "Hv1". iMod ("Hclose" with "[Hv1 Hv2]").
    { iNext; iExists (w, w'); by iFrame. }
    iExists UnitV; iFrame; auto.
  Qed.

  Theorem binary_fundamental Γ e τ :
    Γ ⊢ₜ e : τ → Γ ⊨ e ≤log≤ e : τ.
  Proof.
    induction 1.
    - by apply bin_log_related_var.
    - by apply bin_log_related_unit.
    - apply bin_log_related_pair; eauto.
    - eapply bin_log_related_fst; eauto.
    - eapply bin_log_related_snd; eauto.
    - eapply bin_log_related_injl; eauto.
    - eapply bin_log_related_injr; eauto.
    - eapply bin_log_related_case; eauto;
        match goal with H : _ |- _ => eapply (typed_n_closed _ _ _ H) end.
    - eapply bin_log_related_lam; eauto;
        match goal with H : _ |- _ => eapply (typed_n_closed _ _ _ H) end.
    - eapply bin_log_related_app; eauto.
    - eapply bin_log_related_tlam; eauto with typeclass_instances.
    - eapply bin_log_related_tapp; eauto.
    - eapply bin_log_related_fold; eauto.
    - eapply bin_log_related_unfold; eauto.
    - eapply bin_log_related_alloc; eauto.
    - eapply bin_log_related_load; eauto.
    - eapply bin_log_related_store; eauto.
  Qed.
End fundamental.
