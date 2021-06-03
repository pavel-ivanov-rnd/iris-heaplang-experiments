From iris.proofmode Require Import tactics.
From iris_examples.logrel.stlc Require Import rules.
From iris.program_logic Require Import lifting.
From iris_examples.logrel.stlc Require Export logrel.

Definition log_typed `{irisGS stlc_lang Σ}
           (Γ : list type) (e : expr) (τ : type) : iProp Σ :=
  □∀ vs, ⟦ Γ ⟧* vs -∗ ⟦ τ ⟧ₑ e.[env_subst vs].
Notation "Γ ⊨ e : τ" := (log_typed Γ e τ) (at level 74, e, τ at next level).

Section typed_interp.
  Context `{irisGS stlc_lang Σ}.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) constr(Hp) :=
    iApply (wp_bind (fill [ctx]));
    iApply (wp_wand with "[-]"); [iApply Hp; trivial|]; cbn;
    iIntros (v) Hv.

  Theorem fundamental Γ e τ : Γ ⊢ₜ e : τ → ⊢ Γ ⊨ e : τ.
  Proof.
    intros Htyped.
    induction Htyped; iIntros (vs) "!# #Hctx /=".
    - (* var *)
      iDestruct (interp_env_Some_l with "[]") as (v) "[#H1 #H2]"; eauto;
        iDestruct "H1" as %Heq. erewrite env_subst_lookup; eauto.
      by iApply wp_value.
    - (* unit *) by iApply wp_value.
    - (* pair *)
      smart_wp_bind (PairLCtx e2.[env_subst vs]) v "# Hv" IHHtyped1.
      smart_wp_bind (PairRCtx v) v' "# Hv'" IHHtyped2.
      iApply wp_value; eauto 10.
    - (* fst *)
      smart_wp_bind (FstCtx) v "# Hv" IHHtyped; cbn.
      iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
      iApply wp_pure_step_later; auto. by iApply wp_value.
    - (* snd *)
      smart_wp_bind (SndCtx) v "# Hv" IHHtyped; cbn.
      iDestruct "Hv" as (w1 w2) "#[% [H2 H3]]"; subst.
      iApply wp_pure_step_later; auto. by iApply wp_value.
    - (* injl *)
      smart_wp_bind (InjLCtx) v "# Hv" IHHtyped. by iApply wp_value; eauto.
    - (* injr *)
      smart_wp_bind (InjRCtx) v "# Hv" IHHtyped. by iApply wp_value; eauto.
    - (* case *)
      iDestruct (interp_env_length with "[]") as %Hlen; auto.
      smart_wp_bind (CaseCtx _ _) v "# Hv" IHHtyped1; cbn.
      iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as (w) "[% Hw]"; subst.
      + simpl. iApply wp_pure_step_later; auto. asimpl.
        iApply (IHHtyped2 $! (w::vs)).
        iNext. iApply interp_env_cons; by iSplit.
      + simpl. iApply wp_pure_step_later; auto. asimpl.
        iApply (IHHtyped3 $! (w::vs)).
        iNext. iApply interp_env_cons; by iSplit.
    - (* lam *)
      iDestruct (interp_env_length with "[]") as %Hlen; auto.
      iApply wp_value. simpl. iModIntro; iIntros (w) "#Hw".
      iApply wp_pure_step_later; auto.
      asimpl.
      iNext; iApply (IHHtyped $! (w :: vs)). iApply interp_env_cons; by iSplit.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) v "#Hv" IHHtyped1.
      smart_wp_bind (AppRCtx v) w "#Hw" IHHtyped2.
      iApply "Hv"; auto.
  Qed.
End typed_interp.
