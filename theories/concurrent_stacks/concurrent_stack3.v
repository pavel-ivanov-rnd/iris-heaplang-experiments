From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang proofmode notation.
Set Default Proof Using "Type".

Definition mk_stack : val := λ: "_", ref NONEV.
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

Section stack_works.
  Context `{!heapG Σ} (N : namespace).
  Implicit Types l : loc.

  Local Notation "l ↦{-} v" := (∃ q, l ↦{q} v)%I
    (at level 20, format "l  ↦{-}  v") : bi_scope.

  Lemma partial_mapsto_duplicable l v :
    l ↦{-} v -∗ l ↦{-} v ∗ l ↦{-} v.
  Proof.
    iIntros "H"; iDestruct "H" as (?) "[Hl Hl']"; iSplitL "Hl"; eauto.
  Qed.

  Lemma partial_mapsto_agree l v1 v2 :
    l ↦{-} v1 -∗ l ↦{-} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H1" as (?) "H1".
    iDestruct "H2" as (?) "H2".
    iApply (mapsto_agree with "H1 H2").
  Qed.

  Fixpoint is_list xs v : iProp Σ :=
    (match xs with
     | [] => ⌜v = NONEV⌝
     | x :: xs => ∃ l (t : val), ⌜v = SOMEV #l%V⌝ ∗ l ↦{-} (x, t)%V ∗ is_list xs t
     end)%I.

  Lemma is_list_disj xs v :
    is_list xs v -∗ is_list xs v ∗ (⌜v = NONEV⌝ ∨ ∃ l (h t : val), ⌜v = SOMEV #l⌝ ∗ l ↦{-} (h, t)%V).
  Proof.
    destruct xs; auto.
    iIntros "H"; iDestruct "H" as (l t) "(-> & Hl & Hstack)".
    iDestruct (partial_mapsto_duplicable with "Hl") as "[Hl1 Hl2]".
    iSplitR "Hl2"; first by (iExists _, _; iFrame). iRight; auto.
  Qed.

  Lemma is_list_unboxed xs v :
      is_list xs v -∗ ⌜val_is_unboxed v⌝ ∗ is_list xs v.
  Proof.
    iIntros "Hlist"; iDestruct (is_list_disj with "Hlist") as "[$ Heq]".
    iDestruct "Heq" as "[-> | H]"; first done; by iDestruct "H" as (? ? ?) "[-> ?]".
  Qed.

  Lemma is_list_empty xs :
    is_list xs (InjLV #()) -∗ ⌜xs = []⌝.
  Proof.
    destruct xs; iIntros "Hstack"; auto.
    iDestruct "Hstack" as (? ?) "(% & H)"; discriminate.
  Qed.

  Lemma is_list_cons xs l h t :
    l ↦{-} (h, t)%V -∗
    is_list xs (InjRV #l) -∗
    ∃ ys, ⌜xs = h :: ys⌝.
  Proof.
    destruct xs; first by iIntros "? %".
    iIntros "Hl Hstack"; iDestruct "Hstack" as (l' t') "(% & Hl' & Hrest)"; simplify_eq.
    iDestruct (partial_mapsto_agree with "Hl Hl'") as "%"; simplify_eq; iExists _; auto.
  Qed.

  Definition stack_inv P l :=
    (∃ v xs, l ↦ v ∗ is_list xs v ∗ P xs)%I.

  Definition is_stack P v :=
    (∃ l, ⌜v = #l⌝ ∗ inv N (stack_inv P l))%I.

  Theorem mk_stack_works P :
    {{{ P [] }}} mk_stack #() {{{ v, RET v; is_stack P v }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    rewrite -wp_fupd.
    wp_lam. wp_alloc l as "Hl".
    iMod (inv_alloc N _ (stack_inv P l) with "[Hl HP]") as "#Hinv".
    { by iNext; iExists _, []; iFrame. }
    iModIntro; iApply "HΦ"; iExists _; auto.
  Qed.

  Theorem push_works P s v Ψ :
    {{{ is_stack P s ∗ ∀ xs, P xs ={⊤ ∖ ↑ N}=∗ P (v :: xs) ∗ Ψ #()}}}
      push s v
    {{{ RET #(); Ψ #() }}}.
  Proof.
    iIntros (Φ) "[Hstack Hupd] HΦ". iDestruct "Hstack" as (l) "[-> #Hinv]".
    iLöb as "IH".
    wp_lam. wp_pures. wp_bind (Load _).
    iInv N as (list xs) "(Hl & Hlist & HP)" "Hclose".
    wp_load.
    iMod ("Hclose" with "[Hl Hlist HP]") as "_".
    { iNext; iExists _, _; iFrame. }
    clear xs.
    iModIntro.
    wp_let. wp_alloc l' as "Hl'". wp_pures. wp_bind (CAS _ _ _).
    iInv N as (list' xs) "(Hl & Hlist & HP)" "Hclose".
    iDestruct (is_list_unboxed with "Hlist") as "[>% Hlist]".
    destruct (decide (list = list')) as [ -> |].
    - wp_cas_suc.
      iMod ("Hupd" with "HP") as "[HP HΨ]".
      iMod ("Hclose" with "[Hl Hl' HP Hlist]") as "_".
      { iNext; iExists (SOMEV _), (v :: xs); iFrame; iExists _, _; iFrame; auto. }
      iModIntro.
      wp_if.
      by iApply ("HΦ" with "HΨ").
    - wp_cas_fail.
      iMod ("Hclose" with "[Hl HP Hlist]").
      { iExists _, _; iFrame. }
      iModIntro.
      wp_if.
      iApply ("IH" with "Hupd HΦ").
  Qed.

  Theorem pop_works P s Ψ :
    {{{ is_stack P s ∗
        (∀ v xs, P (v :: xs) ={⊤ ∖ ↑ N}=∗ P xs ∗ Ψ (SOMEV v)) ∗
        (P [] ={⊤ ∖ ↑ N}=∗ P [] ∗ Ψ NONEV) }}}
      pop s
    {{{ v, RET v; Ψ v }}}.
  Proof.
    iIntros (Φ) "(Hstack & Hupdcons & Hupdnil) HΦ".
    iDestruct "Hstack" as (l) "[-> #Hinv]".
    iLöb as "IH".
    wp_lam. wp_bind (Load _).
    iInv N as (v xs) "(Hl & Hlist & HP)" "Hclose".
    wp_load.
    iDestruct (is_list_disj with "Hlist") as "[Hlist H]".
    iDestruct "H" as "[-> | HSome]".
    - iDestruct (is_list_empty with "Hlist") as %->.
      iMod ("Hupdnil" with "HP") as "[HP HΨ]".
      iMod ("Hclose" with "[Hlist Hl HP]") as "_".
      { iNext; iExists _, _; iFrame. }
      iModIntro.
      wp_match.
      iApply ("HΦ" with "HΨ").
    - iDestruct "HSome" as (l' h t) "[-> Hl']".
      iMod ("Hclose" with "[Hlist Hl HP]") as "_".
      { iNext; iExists _, _; iFrame. }
      iModIntro.
      wp_match. wp_bind (Load _).
      iInv N as (v xs') "(Hl & Hlist & HP)" "Hclose".
      iDestruct "Hl'" as (q) "Hl'".
      wp_load.
      iMod ("Hclose" with "[Hlist Hl HP]") as "_".
      { iNext; iExists _, _; iFrame. }
      iModIntro.
      wp_let. wp_proj. wp_bind (CAS _ _ _). wp_pures.
      iInv N as (v' xs'') "(Hl & Hlist & HP)" "Hclose".
      destruct (decide (v' = (SOMEV #l'))) as [ -> |].
      * wp_cas_suc.
        iDestruct (is_list_cons with "[Hl'] Hlist") as (ys) "%"; first by iExists _.
        simplify_eq.
        iMod ("Hupdcons" with "HP") as "[HP HΨ]".
        iDestruct "Hlist" as (l'' t') "(% & Hl'' & Hlist)"; simplify_eq.
        iDestruct "Hl''" as (q') "Hl''".
        iDestruct (mapsto_agree with "Hl' Hl''") as "%"; simplify_eq.
        iMod ("Hclose" with "[Hlist Hl HP]") as "_".
        { iNext; iExists _, _; iFrame. }
        iModIntro.
        wp_pures.
        iApply ("HΦ" with "HΨ").
      * wp_cas_fail.
        iMod ("Hclose" with "[Hlist Hl HP]") as "_".
        { iNext; iExists _, _; iFrame. }
        iModIntro.
        wp_if.
        iApply ("IH" with "Hupdcons Hupdnil HΦ").
  Qed.
End stack_works.
