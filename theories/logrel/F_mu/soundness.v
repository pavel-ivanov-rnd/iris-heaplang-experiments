From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.
From iris_examples.logrel.F_mu Require Export fundamental.

Theorem soundness Σ `{invPreG Σ} e τ e' thp σ σ' :
  (∀ `{irisG F_mu_lang Σ}, [] ⊨ e : τ) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp → not_stuck e' σ'.
Proof.
  intros Hlog ??.
  cut (adequate NotStuck e σ (λ _ _, True));
    first by intros [_ Hsafe]; eapply Hsafe; eauto.
  eapply (wp_adequacy Σ); eauto.
  iIntros (Hinv ?). iModIntro. iExists (λ _ _, True%I), (λ _, True%I). iSplit=> //.
  replace e with e.[env_subst[]] by by asimpl.
  set (HΣ := IrisG _ _ Hinv (λ _ _ _, True)%I (λ _, True)%I).
  iApply (wp_wand with "[]"). iApply Hlog; eauto. by iApply interp_env_nil. auto.
Qed.

Corollary type_soundness e τ e' thp σ σ' :
  [] ⊢ₜ e : τ →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp → not_stuck e' σ'.
Proof.
  intros ??. set (Σ := invΣ).
  eapply (soundness Σ); eauto using fundamental.
Qed.
