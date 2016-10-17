From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import dec_agree frac.
From iris_atomic Require Import sync atomic_sync.
Import uPred.

Section atomic_pair.
  Context `{!heapG Σ, !lockG Σ, !syncG Σ,
            !inG Σ (prodR fracR (dec_agreeR (val * val)))} (N : namespace).
  
  Definition pcas_seq : val :=
    λ: "ls" "ab",
       if: !(Fst "ls") = Fst "ab"
         then if: !(Snd "ls") = Fst "ab"
                then Fst "ls" <- Snd "ab";; Snd "ls" <- Snd "ab";; #true
                else #false
         else #false.

  Local Opaque pcas_seq.

  Definition α (x: val) : iProp Σ := (∃ a b: val, x = (a, b)%V)%I.
  
  Definition ϕ (ls: val) (xs: val) : iProp Σ :=
    (∃ (l1 l2: loc) (x1 x2: val),
       ls = (#l1, #l2)%V ★ xs = (x1, x2)%V ★ l1 ↦ x1 ★ l2 ↦ x2)%I.

  Definition β (ab: val) (xs xs': val) (v: val) : iProp Σ :=
    (■ ∃ a b x1 x2 x1' x2': val,
         ab = (a, b)%V ∧ xs = (x1, x2)%V ∧ xs' = (x1', x2')%V ∧
         ((v = #true  ∧ x1 = a ∧ x2 = a ∧ x1' = b ∧ x2' = b) ∨
          (v = #false ∧ (x1 ≠ a ∨ x2 ≠ a) ∧ xs = xs')))%I.

  Local Opaque β.
  
  Lemma pcas_seq_spec: seq_spec N pcas_seq ϕ α β ⊤.
  Proof.
    iIntros (_ l) "!# _". wp_seq. iVsIntro. iPureIntro.
    iIntros (x Φ g HN) "(#Hh & Hg & #Hα & HΦ)".
    iDestruct "Hg" as (l1 l2 x1 x2) "(% & % & Hl1 & Hl2)".
    iDestruct "Hα" as (a b) "%".
    subst. simpl. wp_let. wp_proj. wp_load. wp_proj.
    wp_op=>[?|Hx1na].
    - subst.
      wp_if. wp_proj. wp_load. wp_proj.
      wp_op=>[?|Hx2na]. subst.
      + wp_if. wp_proj. wp_proj. wp_store. wp_proj. wp_proj. wp_store.
        iDestruct ("HΦ" $! #true (b, b)%V) as "HΦ".
        iApply ("HΦ" with "[Hl1 Hl2]").
        { iExists l1, l2, b, b. iFrame. eauto. }
        rewrite /β. iPureIntro.
        exists a, b, a, a, b, b.
        repeat (split; first done). left. eauto.
      + wp_if.
        iDestruct ("HΦ" $! #false (a, x2)%V) as "H".
        iApply ("H" with "[Hl1 Hl2]").
        { iExists l1, l2, a, x2. iFrame. eauto. }
        rewrite /β. iPureIntro.
        exists a, b, a, x2, a, x2. repeat (split; first done). right. eauto.
    - subst. wp_if.
      iDestruct ("HΦ" $! #false (x1, x2)%V) as "H".
      iApply ("H" with "[Hl1 Hl2]").
      { iExists l1, l2, x1, x2. iFrame. eauto. }
      rewrite /β. iPureIntro.
      exists a, b, x1, x2, x1, x2.
      repeat (split; first done). right. eauto.
  Qed.

  Lemma pcas_atomic_spec (mk_syncer: val) (l1 l2: loc) (x1 x2: val) :
    heapN ⊥ N → mk_syncer_spec N mk_syncer →
    heap_ctx ★ l1 ↦ x1 ★ l2 ↦ x2
    ⊢ WP sync mk_syncer pcas_seq (LitV l1, LitV l2)%V {{ f, ∃ γ, gHalf γ (x1, x2)%V ★ ∀ x, □ atomic_triple' α β ⊤ ⊤ f x γ  }}.
  Proof.
    iIntros (HN Hmk_syncer) "(#Hh & Hl1 & Hl2)".
    iDestruct (atomic_spec with "[Hl1 Hl2]") as "Hspec"=>//.
    - apply pcas_seq_spec.
    - iFrame "Hh". iExists l1, l2, x1, x2. iFrame. eauto.
  Qed.
End atomic_pair.

