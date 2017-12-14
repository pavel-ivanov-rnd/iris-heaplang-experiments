From iris_examples.logrel.F_mu Require Export fundamental.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.

Theorem soundness Σ `{invPreG Σ} e τ e' thp σ σ' :
  (∀ `{irisG F_mu_lang Σ}, [] ⊨ e : τ) →
  rtc step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog ??. cut (adequate NotStuck e σ (λ _, True)); first (intros [_ ?]; eauto).
  eapply (wp_adequacy Σ); eauto.
  iIntros (Hinv). iModIntro. iExists (λ _, True%I). iSplit=> //.
  rewrite -(empty_env_subst e).
  set (HΣ := IrisG _ _ Hinv (λ _, True)%I).
  iApply (wp_wand with "[]"). iApply Hlog; eauto. by iApply interp_env_nil. auto.
Qed.

Corollary type_soundness e τ e' thp σ σ' :
  [] ⊢ₜ e : τ →
  rtc step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros ??. set (Σ := invΣ).
  eapply (soundness Σ); eauto using fundamental.
Qed.
