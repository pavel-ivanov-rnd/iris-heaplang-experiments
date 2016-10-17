From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.

Section sync.
  Context `{!heapG Σ} (N : namespace).

  Definition synced R (f' f: val) :=
    (□ ∀ P Q (x: val), ({{ R ★ P x }} f x {{ v, R ★ Q x v }}) →
                       ({{ P x }} f' x {{ v, Q x v }}))%I.

  Definition is_syncer (R: iProp Σ) (s: val) :=
    (□ ∀ (f : val), WP s f {{ f', synced R f' f }})%I.

  Definition mk_syncer_spec (mk_syncer: val) :=
    ∀ (R: iProp Σ) (Φ: val -> iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ R ★ (∀ s, is_syncer R s -★ Φ s) ⊢ WP mk_syncer #() {{ Φ }}.
End sync.
