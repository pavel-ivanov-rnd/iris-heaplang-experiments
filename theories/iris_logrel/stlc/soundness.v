From iris_examples.iris_logrel.stlc Require Export fundamental.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.

Lemma wp_soundness `{irisG stlc_lang Σ} e τ : [] ⊢ₜ e : τ → (WP e {{ ⟦ τ ⟧ }})%I.
Proof.
  iIntros (?). rewrite -(empty_env_subst e).
  iApply fundamental; eauto. iApply interp_env_nil.
Qed.

Theorem soundness e τ e' thp :
  [] ⊢ₜ e : τ → rtc step ([e], ()) (thp, ()) → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' ().
Proof.
  set (Σ := invΣ). intros.
  cut (adequate NotStuck e () (λ _, True)); first (intros [_ Hsafe]; eauto).
  eapply (wp_adequacy Σ _). iIntros (Hinv).
  iModIntro. iExists (λ _, True%I). iSplit=>//.
  set (HΣ := IrisG _ _ Hinv (λ _, True)%I).
  iApply (wp_wand with "[]"). by iApply wp_soundness. eauto.
Qed.

