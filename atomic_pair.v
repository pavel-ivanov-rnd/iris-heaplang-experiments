From iris.program_logic Require Export weakestpre hoare.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.tests Require Import atomic.
From iris.algebra Require Import dec_agree frac.
From iris.program_logic Require Import auth.
From flatcomb Require Import sync.
Import uPred.

Section atomic_pair.
  Context `{!heapG Σ, !lockG Σ, !syncG Σ} (N : namespace).
  
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
    rewrite /seq_spec.
    intros Φ l.
    iIntros "!# _". wp_seq. iVsIntro. iPureIntro. clear Φ.
    iIntros (x Φ g HN) "(#Hh & Hg & #Hα & HΦ)".
    rewrite /ϕ /α.
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
        rewrite /β.
        iPureIntro. exists a, b, a, a, b, b. repeat (split; first done). left. eauto.
      + wp_if.
        iDestruct ("HΦ" $! #false (a, x2)%V) as "H".
        iApply ("H" with "[Hl1 Hl2]").
        { iExists l1, l2, a, x2. iFrame. eauto. }
        rewrite /β.
        iPureIntro. exists a, b, a, x2, a, x2. repeat (split; first done). right. eauto.
    - subst.
      wp_if.
      iDestruct ("HΦ" $! #false (x1, x2)%V) as "H".
      iApply ("H" with "[Hl1 Hl2]").
      { iExists l1, l2, x1, x2. iFrame. eauto. }
      rewrite /β.
      iPureIntro. exists a, b, x1, x2, x1, x2. repeat (split; first done). right. eauto.
  Qed.

  Lemma pcas_atomic_spec:
    heapN ⊥ N → heap_ctx ⊢ WP sync (λ: <>, (ref #0, ref #0))%V pcas_seq {{ f, ∃ γ, gFrag γ (#0, #0) ★ ∀ x, □ atomic_triple' α β ⊤ ⊤ f x γ  }}.
  Proof.
    iIntros (HN) "#Hh".
    iDestruct (atomic_spec with "[]") as "Hspec"=>//.
    - apply pcas_seq_spec.
    - rewrite /cons_spec.
      iIntros (Φ _) "[#Hh HΦ]".
      wp_seq.
      wp_alloc l1 as "Hl1".
      wp_alloc l2 as "Hl2".
      iVs (own_alloc (gFullR (#0, #0) ⋅ gFragR (#0, #0))) as (γ) "[HgFull HgFrag]".
      { rewrite /gFragR /gFullR. split; first by simpl. simpl. by rewrite dec_agree_idemp. }
      rewrite /ϕ.
      iSpecialize ("HΦ" $! (#l1, #l2)%V γ).
      rewrite /gFull /gFrag.
      iVsIntro.
      iAssert ((∃ (l0 l3 : loc) (x1 x2 : val),
            (#l1, #l2)%V = (#l0, #l3)%V
            ★ (#0, #0)%V = (x1, x2)%V ★ l0 ↦ x1 ★ l3 ↦ x2))%I with "[Hl1 Hl2]" as "H'".
      { iExists l1, l2, #0, #0. iFrame. eauto. }
      iApply ("HΦ" with "H' HgFull HgFrag").
   Qed.
End atomic_pair.
