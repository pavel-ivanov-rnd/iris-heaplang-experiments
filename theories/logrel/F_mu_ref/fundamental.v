From iris_examples.logrel.F_mu_ref Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import lifting.
From iris_examples.logrel.F_mu_ref Require Import rules.

Definition log_typed `{heapG Σ} (Γ : list type) (e : expr) (τ : type) := ∀ Δ vs,
  env_Persistent Δ →
  ⟦ Γ ⟧* Δ vs ⊢ ⟦ τ ⟧ₑ Δ e.[env_subst vs].
Notation "Γ ⊨ e : τ" := (log_typed Γ e τ) (at level 74, e, τ at next level).

Section fundamental.
  Context `{heapG Σ}.
  Notation D := (valO -n> iProp Σ).

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
    iApply (wp_bind (fill [ctx]));
    iApply (wp_wand with "[-]"); [iApply Hp; trivial|]; cbn;
    iIntros (v) Hv; cbn.

  Theorem fundamental Γ e τ : Γ ⊢ₜ e : τ → Γ ⊨ e : τ.
  Proof.
    induction 1; iIntros (Δ vs HΔ) "#HΓ /=".
    - (* var *)
      iDestruct (interp_env_Some_l with "HΓ") as (v) "[% ?]"; first done.
      erewrite env_subst_lookup; eauto. by iApply wp_value.
    - (* unit *) by iApply wp_value.
    - (* pair *)
      smart_wp_bind (PairLCtx e2.[env_subst vs]) v "#Hv" IHtyped1.
      smart_wp_bind (PairRCtx v) v' "# Hv'" IHtyped2.
      iApply wp_value. eauto 10.
   - (* fst *)
      smart_wp_bind (FstCtx) v "# Hv" IHtyped; cbn.
      iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
      iApply wp_pure_step_later; auto. by iApply wp_value.
    - (* snd *)
      smart_wp_bind (SndCtx) v "# Hv" IHtyped; cbn.
      iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
      iApply wp_pure_step_later; auto; by iApply wp_value.
    - (* injl *)
      smart_wp_bind (InjLCtx) v "# Hv" IHtyped; cbn.
      iApply wp_value; eauto.
    - (* injr *)
      smart_wp_bind (InjRCtx) v "# Hv" IHtyped; cbn.
      iApply wp_value; eauto.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) v "#Hv" IHtyped1; cbn.
      iDestruct (interp_env_length with "HΓ") as %?.
      iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as (w) "[% Hw]"; simplify_eq/=.
      + iApply wp_pure_step_later; auto 1 using to_of_val; asimpl. iNext.
        iApply (IHtyped2 Δ (w :: vs)). iApply interp_env_cons; auto.
      + iApply wp_pure_step_later; auto 1 using to_of_val; asimpl. iNext.
        iApply (IHtyped3 Δ (w :: vs)). iApply interp_env_cons; auto.
    - (* lam *)
      iApply wp_value. simpl. iAlways. iIntros (w) "#Hw".
      iDestruct (interp_env_length with "HΓ") as %?.
      iApply wp_pure_step_later; auto 1 using to_of_val. iNext.
      asimpl.
      iApply (IHtyped Δ (w :: vs)). iApply interp_env_cons; auto.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "#Hv" IHtyped1.
      smart_wp_bind (AppRCtx v) w "#Hw" IHtyped2.
      iApply wp_mono; [|iApply "Hv"]; auto.
    - (* TLam *)
      iApply wp_value.
      iAlways; iIntros (τi) "%". iApply wp_pure_step_later; auto; iNext.
      iApply IHtyped. by iApply interp_env_ren.
    - (* TApp *)
      smart_wp_bind TAppCtx v "#Hv" IHtyped; cbn.
      iApply wp_wand_r; iSplitL; [iApply ("Hv" $! (interp  τ' Δ)); iPureIntro; apply _|].
      iIntros (w) "?". by rewrite interp_subst.
    - (* Fold *)
      smart_wp_bind FoldCtx v "#Hv" IHtyped; cbn.
      iApply wp_value. rewrite /= -interp_subst fixpoint_interp_rec1_eq /=.
      iAlways; eauto.
    - (* Unfold *)
      iApply (wp_bind (fill [UnfoldCtx]));
        iApply wp_wand_l; iSplitL; [|iApply IHtyped; auto].
      iIntros (v) "#Hv". rewrite /= fixpoint_interp_rec1_eq.
      change (fixpoint _) with (interp  (TRec τ) Δ); simpl.
      iDestruct "Hv" as (w) "#[% Hw]"; subst.
      iApply wp_pure_step_later; cbn; auto using to_of_val.
      iNext. iApply wp_value. by rewrite -interp_subst.
    - (* Alloc *)
      smart_wp_bind AllocCtx v "#Hv" IHtyped; cbn. iClear "HΓ". iApply wp_fupd.
      iApply wp_alloc; auto 1 using to_of_val.
      iNext; iIntros (l) "Hl".
      iMod (inv_alloc _ with "[Hl]") as "HN";
        [| iModIntro; iExists _; iSplit; trivial]; eauto.
    - (* Load *)
      smart_wp_bind LoadCtx v "#Hv" IHtyped; cbn. iClear "HΓ".
      iDestruct "Hv" as (l) "[% #Hv]"; subst.
      iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
      iApply (wp_load with "Hw1 [Hclose]").
      iNext.
      iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
    - (* Store *)
      smart_wp_bind (StoreLCtx _) v "#Hv" IHtyped1; cbn.
      smart_wp_bind (StoreRCtx _) w "#Hw" IHtyped2; cbn. iClear "HΓ".
      iDestruct "Hv" as (l) "[% #Hv]"; subst.
      iInv (logN .@ l) as (z) "[Hz1 #Hz2]" "Hclose".
      iApply (wp_store with "Hz1 [Hclose]"); eauto using to_of_val. iNext.
      iIntros "Hz1". iMod ("Hclose" with "[Hz1 Hz2]"); eauto.
  Qed.
End fundamental.
