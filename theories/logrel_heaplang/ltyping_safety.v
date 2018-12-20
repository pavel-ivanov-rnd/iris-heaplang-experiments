From iris_examples.logrel_heaplang Require Export ltyping.
From iris.heap_lang Require Import adequacy.
From iris.heap_lang Require Import proofmode.

Lemma ltyped_safety `{heapPreG Σ} e σ es σ' e' :
  (∀ `{heapG Σ}, ∃ A, ∅ ⊨ e : A) →
  rtc erased_step ([e], σ) (es, σ') → e' ∈ es →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hty. apply (heap_adequacy Σ NotStuck e σ (λ _, True))=> // ?.
  destruct (Hty _) as [A He]. iStartProof. iDestruct (He $! ∅) as "#He".
  iSpecialize ("He" with "[]").
  { iSplit.
    - iPureIntro=> x. rewrite !lookup_empty -!not_eq_None_Some. by naive_solver.
    - by rewrite map_zip_with_empty. }
  rewrite subst_map_empty. iApply (wp_wand with "He"); auto.
Qed.
