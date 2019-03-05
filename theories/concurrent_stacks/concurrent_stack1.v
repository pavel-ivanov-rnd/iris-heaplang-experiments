From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import notation proofmode.
From iris_examples.concurrent_stacks Require Import specs.
Set Default Proof Using "Type".

Definition new_stack : val := λ: "_", ref NONEV.
Definition push : val :=
  rec: "push" "s" "v" :=
    let: "tail" := ! "s" in
    let: "new" := SOME (ref ("v", "tail")) in
    if: CAS "s" "tail" "new" then #() else "push" "s" "v".
Definition pop : val :=
  rec: "pop" "s" :=
    match: !"s" with
      NONE => NONEV
    | SOME "l" =>
      let: "pair" := !"l" in
      if: CAS "s" (SOME "l") (Snd "pair")
      then SOME (Fst "pair")
      else "pop" "s"
    end.

Section stacks.
  Context `{!heapG Σ} (N : namespace).
  Implicit Types l : loc.

  Local Notation "l ↦{-} v" := (∃ q, l ↦{q} v)%I
    (at level 20, format "l  ↦{-}  v") : bi_scope.

  Lemma partial_mapsto_duplicable l v :
    l ↦{-} v -∗ l ↦{-} v ∗ l ↦{-} v.
  Proof.
    iIntros "H"; iDestruct "H" as (?) "[Hl Hl']"; iSplitL "Hl"; eauto.
  Qed.

  Definition is_list_pre (P : val → iProp Σ) (F : val -c> iProp Σ) :
     val -c> iProp Σ := λ v,
    (v ≡ NONEV ∨ ∃ (l : loc) (h t : val), ⌜v ≡ SOMEV #l⌝ ∗ l ↦{-} (h, t)%V ∗ P h ∗ ▷ F t)%I.

  Local Instance is_list_contr (P : val → iProp Σ) : Contractive (is_list_pre P).
  Proof.
    rewrite /is_list_pre => n f f' Hf v.
    repeat (f_contractive || f_equiv).
    apply Hf.
  Qed.

  Definition is_list_def (P : val -> iProp Σ) := fixpoint (is_list_pre P).
  Definition is_list_aux P : seal (@is_list_def P). by eexists. Qed.
  Definition is_list P := unseal (is_list_aux P).
  Definition is_list_eq P : @is_list P = @is_list_def P := seal_eq (is_list_aux P).

  Lemma is_list_unfold (P : val → iProp Σ) v :
    is_list P v ⊣⊢ is_list_pre P (is_list P) v.
  Proof.
    rewrite is_list_eq. apply (fixpoint_unfold (is_list_pre P)).
  Qed.

  (* TODO: shouldn't have to explicitly return is_list *)
  Lemma is_list_unboxed (P : val → iProp Σ) v :
      is_list P v -∗ ⌜val_is_unboxed v⌝ ∗ is_list P v.
  Proof.
    iIntros "Hstack"; iSplit; last done;
    iDestruct (is_list_unfold with "Hstack") as "[->|Hstack]";
    last iDestruct "Hstack" as (l h t) "(-> & _)"; done.
  Qed.

  Lemma is_list_disj (P : val → iProp Σ) v :
    is_list P v -∗ is_list P v ∗ (⌜v ≡ NONEV⌝ ∨ ∃ (l : loc) h t, ⌜v ≡ SOMEV #l%V⌝ ∗ l ↦{-} (h, t)%V).
  Proof.
    iIntros "Hstack".
    iDestruct (is_list_unfold with "Hstack") as "[%|Hstack]"; simplify_eq.
    - rewrite is_list_unfold; iSplitR; [iLeft|]; eauto.
    - iDestruct "Hstack" as (l h t) "(% & Hl & Hlist)".
      iDestruct (partial_mapsto_duplicable with "Hl") as "[Hl1 Hl2]"; simplify_eq.
      rewrite (is_list_unfold _ (InjRV _)); iSplitR "Hl2"; iRight; iExists _, _, _; by iFrame.
  Qed.

  Definition stack_inv P v :=
    (∃ l v', ⌜v = #l⌝ ∗ l ↦ v' ∗ is_list P v')%I.

  Definition is_stack (P : val → iProp Σ) v :=
    inv N (stack_inv P v).

  Theorem new_stack_spec P :
    {{{ True }}} new_stack #() {{{ s, RET s; is_stack P s }}}.
  Proof.
    iIntros (ϕ) "_ Hpost".
    iApply wp_fupd.
    wp_lam.
    wp_alloc ℓ as "Hl".
    iMod (inv_alloc N ⊤ (stack_inv P #ℓ) with "[Hl]") as "Hinv".
    { iNext; iExists ℓ, NONEV; iFrame;
      by iSplit; last (iApply is_list_unfold; iLeft). }
    by iApply "Hpost".
  Qed.

  Theorem push_spec P s v :
    {{{ is_stack P s ∗ P v }}} push s v {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "[#Hstack HP] HΦ".
    iLöb as "IH".
    wp_lam. wp_let. wp_bind (Load _).
    iInv N as (ℓ v') "(>% & Hl & Hlist)" "Hclose"; subst.
    wp_load.
    iMod ("Hclose" with "[Hl Hlist]") as "_".
    { iNext; iExists _, _; by iFrame. }
    iModIntro. wp_let. wp_alloc ℓ' as "Hl'". wp_pures. wp_bind (CAS _ _ _).
    iInv N as (ℓ'' v'') "(>% & >Hl & Hlist)" "Hclose"; simplify_eq.
    destruct (decide (v' = v'')) as [ -> |].
    - iDestruct (is_list_unboxed with "Hlist") as "[>% Hlist]".
      wp_cas_suc.
      iMod ("Hclose" with "[HP Hl Hl' Hlist]") as "_".
      { iNext; iExists _, (InjRV #ℓ'); iFrame; iSplit; first done;
        rewrite (is_list_unfold _ (InjRV _)). iRight; iExists _, _, _; iFrame; eauto. }
      iModIntro.
      wp_if.
      by iApply "HΦ".
    - iDestruct (is_list_unboxed with "Hlist") as "[>% Hlist]".
      wp_cas_fail.
      iMod ("Hclose" with "[Hl Hlist]") as "_".
      { iNext; iExists _, _; by iFrame. }
      iModIntro.
      wp_if.
      iApply ("IH" with "HP HΦ").
  Qed.

  Theorem pop_spec P s :
    {{{ is_stack P s }}} pop s {{{ ov, RET ov; ⌜ov = NONEV⌝ ∨ ∃ v, ⌜ov = SOMEV v⌝ ∗ P v }}}.
  Proof.
    iIntros (Φ) "#Hstack HΦ".
    iLöb as "IH".
    wp_lam. wp_bind (Load _).
    iInv N as (ℓ v') "(>% & Hl & Hlist)" "Hclose"; subst.
    wp_load.
    iDestruct (is_list_disj with "Hlist") as "[Hlist Hdisj]".
    iMod ("Hclose" with "[Hl Hlist]") as "_".
    { iNext; iExists _, _; by iFrame. }
    iModIntro.
    iDestruct "Hdisj" as "[-> | Heq]".
    - wp_match.
      iApply "HΦ"; by iLeft.
    - iDestruct "Heq" as (l h t) "[-> Hl]".
      wp_match. wp_bind (Load _).
      iInv N as (ℓ' v') "(>% & Hl' & Hlist)" "Hclose". simplify_eq.
      iDestruct "Hl" as (q) "Hl".
      wp_load.
      iMod ("Hclose" with "[Hl' Hlist]") as "_".
      { iNext; iExists _, _; by iFrame. }
      iModIntro.
      wp_pures. wp_bind (CAS _ _ _).
      iInv N as (ℓ'' v'') "(>% & Hl' & Hlist)" "Hclose". simplify_eq.
      destruct (decide (v'' = InjRV #l)) as [-> |].
      * rewrite is_list_unfold.
        iDestruct "Hlist" as "[>% | H]"; first done.
        iDestruct "H" as (ℓ''' h' t') "(>% & Hl'' & HP & Hlist)"; simplify_eq.
        iDestruct "Hl''" as (q') "Hl''".
        wp_cas_suc.
        iDestruct (mapsto_agree with "Hl'' Hl") as "%"; simplify_eq.
        iMod ("Hclose" with "[Hl' Hlist]") as "_".
        { iNext; iExists ℓ'', _; by iFrame. }
        iModIntro.
        wp_pures.
        iApply ("HΦ" with "[HP]"); iRight; iExists h; by iFrame.
      * wp_cas_fail.
        iMod ("Hclose" with "[Hl' Hlist]") as "_".
        { iNext; iExists ℓ'', _; by iFrame. }
        iModIntro.
        wp_if.
        iApply ("IH" with "HΦ").
  Qed.
End stacks.

Program Definition spec {Σ} N `{heapG Σ} : concurrent_bag Σ :=
  {| is_bag := is_stack N; new_bag := new_stack; bag_push := push; bag_pop := pop |} .
Solve Obligations of spec with eauto using pop_spec, push_spec, new_stack_spec.
