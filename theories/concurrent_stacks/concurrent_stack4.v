From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang proofmode notation.
From iris.algebra Require Import excl.

Definition mk_offer : val :=
  λ: "v", ("v", ref #0).
Definition revoke_offer : val :=
  λ: "v", if: CAS (Snd "v") #0 #2 then SOME (Fst "v") else NONE.
Definition take_offer : val :=
  λ: "v", if: CAS (Snd "v") #0 #1 then SOME (Fst "v") else NONE.

Definition mk_mailbox : val := λ: "_", ref NONEV.
Definition put : val :=
  λ: "r" "v",
    let: "off" := mk_offer "v" in
    "r" <- SOME "off";;
    revoke_offer "off".
Definition get : val :=
  λ: "r",
    let: "offopt" := !"r" in
    match: "offopt" with
      NONE => NONE
    | SOME "x" => take_offer "x"
    end.

Definition mk_stack : val := λ: "_", (mk_mailbox #(), ref NONEV).
Definition push : val :=
  rec: "push" "p" "v" :=
    let: "mailbox" := Fst "p" in
    let: "s" := Snd "p" in
    match: put "mailbox" "v" with
      NONE => #()
    | SOME "v'" =>
      let: "tail" := ! "s" in
      let: "new" := SOME (ref ("v'", "tail")) in
      if: CAS "s" "tail" "new" then #() else "push" "p" "v'"
    end.
Definition pop : val :=
  rec: "pop" "p" :=
    let: "mailbox" := Fst "p" in
    let: "s" := Snd "p" in
    match: get "mailbox" with
      NONE =>
      match: !"s" with
        NONE => NONEV
      | SOME "l" =>
        let: "pair" := !"l" in
        if: CAS "s" (SOME "l") (Snd "pair")
        then SOME (Fst "pair")
        else "pop" "p"
      end
    | SOME "x" => SOME "x"
    end.

Definition channelR := exclR unitR.
Class channelG Σ := {channel_inG :> inG Σ channelR}.

Section proofs.
  Context `{!heapG Σ, !channelG Σ} (N : namespace).

  Implicit Types l : loc.

  Definition Nside_channel := N .@ "side_channel".
  Definition Nstack := N .@ "stack".
  Definition Nmailbox := N .@ "mailbox".

  Definition inner_mask : coPset := ⊤ ∖ ↑Nside_channel ∖ ↑Nstack.

  Lemma inner_mask_includes :
     ⊤ ∖ ↑ N ⊆ inner_mask.
  Proof. solve_ndisj. Qed.

  Definition revoke_tok γ := own γ (Excl ()).
  Definition can_push P Q v : iProp Σ :=
    (∀ (xs : list val), P xs ={inner_mask}=∗ P (v :: xs) ∗ Q #())%I.
  Definition access_inv (P : list val → iProp Σ) : iProp Σ :=
    (|={⊤ ∖ ↑Nside_channel, inner_mask}=> ∃ vs, (▷ P vs) ∗
      ((▷ P vs) ={inner_mask, ⊤ ∖ ↑Nside_channel}=∗ True))%I.

  Definition stages γ P Q l (v : val) :=
    ((l ↦ #0 ∗ can_push P Q v)  ∨
     (l ↦ #1 ∗ Q #()) ∨
     (l ↦ #1 ∗ revoke_tok γ) ∨
     (l ↦ #2 ∗ revoke_tok γ))%I.

  Definition is_offer γ P Q (v : val) : iProp Σ :=
    (∃ v' l, ⌜v = (v', #l)%V⌝ ∗ inv Nside_channel (stages γ P Q l v'))%I.

  Lemma mk_offer_works P Q v :
    {{{ can_push P Q v }}}
      mk_offer v
    {{{ o γ, RET o; is_offer γ P Q o ∗ revoke_tok γ }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    rewrite -wp_fupd.
    wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc Nside_channel _ (stages γ P Q l v) with "[Hl HP]") as "#Hinv".
    { iNext; iLeft; iFrame. }
    wp_pures; iModIntro; iApply "HΦ"; iFrame; iExists _, _; auto.
  Qed.

  Lemma revoke_works γ P Q v :
    {{{ is_offer γ P Q v ∗ revoke_tok γ }}}
      revoke_offer v
    {{{ v', RET v'; (∃ v'' : val, ⌜v' = InjRV v''⌝ ∗ can_push P Q v'') ∨ (⌜v' = InjLV #()⌝ ∗ (Q #())) }}}.
  Proof.
    iIntros (Φ) "[Hinv Hγ] HΦ". iDestruct "Hinv" as (v' l) "[-> #Hinv]".
    wp_lam. wp_pures. wp_bind (CAS _ _ _).
    iInv Nside_channel as "Hstages" "Hclose".
    iDestruct "Hstages" as "[[Hl HP] | [[Hl HQ] | [[Hl H] | [Hl H]]]]".
    - wp_cas_suc.
      iMod ("Hclose" with "[Hl Hγ]") as "_".
      { iNext; iRight; iRight; iFrame. }
      iModIntro.
      wp_pures.
      by iApply "HΦ"; iLeft; iExists _; iFrame.
    - wp_cas_fail.
      iMod ("Hclose" with "[Hl Hγ]") as "_".
      { iNext; iRight; iRight; iLeft; iFrame. }
      iModIntro.
      wp_pures.
      iApply ("HΦ" with "[HQ]"); iRight; auto.
    - wp_cas_fail.
      iDestruct (own_valid_2 with "H Hγ") as %[].
    - wp_cas_fail.
      iDestruct (own_valid_2 with "H Hγ") as %[].
  Qed.

  Lemma take_works γ P Q o Ψ :
    let do_pop : iProp Σ :=
        (∀ v xs, P (v :: xs) ={inner_mask}=∗ P xs ∗ Ψ (SOMEV v))%I in
    {{{ is_offer γ P Q o ∗ access_inv P ∗ do_pop }}}
      take_offer o
    {{{ v', RET v';
        (∃ v'' : val, ⌜v' = InjRV v''⌝ ∗ Ψ v') ∨ (⌜v' = InjLV #()⌝ ∗ do_pop) }}}.
  Proof.
    simpl; iIntros (Φ) "[H [Hopener Hupd]] HΦ"; iDestruct "H" as (v l) "[-> #Hinv]".
    wp_lam. wp_proj. wp_bind (CAS _ _ _).
    iInv Nside_channel as "Hstages" "Hclose".
    iDestruct "Hstages" as "[[Hl Hpush] | [[Hl HQ] | [[Hl Hγ] | [Hl Hγ]]]]".
    - iMod "Hopener" as (xs) "[HP Hcloser]".
      wp_cas_suc.
      iMod ("Hpush" with "HP") as "[HP HQ]".
      iMod ("Hupd" with "HP") as "[HP HΨ]".
      iMod ("Hcloser" with "HP") as "_".
      iMod ("Hclose" with "[Hl HQ]") as "_".
      { iRight; iLeft; iFrame. }
      iApply fupd_intro_mask; first done.
      wp_pures.
      iApply "HΦ"; iLeft; auto.
    - wp_cas_fail.
      iMod ("Hclose" with "[Hl HQ]") as "_".
      { iRight; iLeft; iFrame. }
      iModIntro.
      wp_pures.
      iApply "HΦ"; auto.
    - wp_cas_fail.
      iMod ("Hclose" with "[Hl Hγ]").
      { iRight; iRight; iFrame. }
      iModIntro.
      wp_pures.
      iApply "HΦ"; auto.
    - wp_cas_fail.
      iMod ("Hclose" with "[Hl Hγ]").
      { iRight; iRight; iFrame. }
      iModIntro.
      wp_pures.
      iApply "HΦ"; auto.
  Qed.

  Definition mailbox_inv P l : iProp Σ :=
    (l ↦ NONEV ∨ (∃ v' γ Q, l ↦ SOMEV v' ∗ is_offer γ P Q v'))%I.

  Definition is_mailbox P v : iProp Σ :=
    (∃ l, ⌜v = #l⌝ ∗ inv Nmailbox (mailbox_inv P l))%I.

  Lemma mk_mailbox_works P :
    {{{ True }}} mk_mailbox #() {{{ v, RET v; is_mailbox P v }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite -wp_fupd. wp_lam. wp_alloc l as "Hl".
    iMod (inv_alloc Nmailbox _ (mailbox_inv P l) with "[Hl]") as "#Hinv".
    { iNext; by iLeft. }
    iModIntro.
    iApply "HΦ"; iExists _; auto.
  Qed.

  Lemma get_works P Ψ mailbox :
    let do_pop : iProp Σ :=
        (∀ v xs, P (v :: xs) ={inner_mask}=∗ P xs ∗ Ψ (SOMEV v))%I in
    {{{ is_mailbox P mailbox ∗ access_inv P ∗ do_pop }}}
      get mailbox
    {{{ ov, RET ov; (∃ v, ⌜ov = SOMEV v⌝ ∗ Ψ ov) ∨ (⌜ov = NONEV⌝ ∗ do_pop) }}}.
  Proof.
    simpl; iIntros (Φ) "[Hmail [Hopener Hpush]] HΦ". iDestruct "Hmail" as (l) "[-> #Hmail]".
    wp_lam. wp_bind (Load _).
    iInv Nmailbox as "[Hnone | Hsome]" "Hclose".
    - wp_load.
      iMod ("Hclose" with "[Hnone]") as "_".
      { by iLeft. }
      iModIntro.
      wp_pures.
      iApply "HΦ"; iRight; by iFrame.
    - iDestruct "Hsome" as (v' γ Q) "[Hl #Hoffer]".
      wp_load.
      iMod ("Hclose" with "[Hl Hoffer]") as "_".
      { iNext; iRight; iExists _, _, _; by iFrame. }
      iModIntro.
      wp_let. wp_match. wp_apply (take_works with "[Hpush Hopener]"); by iFrame.
  Qed.

  Lemma put_works P Q mailbox v :
    {{{ is_mailbox P mailbox ∗ can_push P Q v }}}
      put mailbox v
    {{{ o, RET o; (∃ v', ⌜o = SOMEV v'⌝ ∗ can_push P Q v') ∨ (⌜o = NONEV⌝ ∗ Q #()) }}}.
  Proof.
    iIntros (Φ) "[Hmail Hpush] HΦ". iDestruct "Hmail" as (l) "[-> #Hmail]".
    wp_lam. wp_let. wp_apply (mk_offer_works with "Hpush").
    iIntros (o γ) "[#Hoffer Hrev]".
    wp_let. wp_bind (Store _ _). wp_pures.
    iInv Nmailbox as "[Hnone | Hsome]" "Hclose".
    - wp_store.
      iMod ("Hclose" with "[Hnone]") as "_".
      { iNext; iRight; iExists _, _, _; by iFrame. }
      iModIntro.
      wp_pures.
      wp_apply (revoke_works with "[Hrev]"); first auto.
      iIntros (v') "H"; iApply "HΦ"; auto.
    - iDestruct "Hsome" as (? ? ?) "[Hl _]". wp_store.
      iMod ("Hclose" with "[Hl]") as "_".
      { iNext; iRight; iExists _, _, _; by iFrame. }
      iModIntro.
      wp_pures.
      wp_apply (revoke_works with "[Hrev]"); first auto.
      iIntros (v') "H"; iApply "HΦ"; auto.
  Qed.

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
    (∃ mailbox l, ⌜v = (mailbox, #l)%V⌝ ∗ is_mailbox P mailbox ∗ inv Nstack (stack_inv P l))%I.

  Theorem mk_stack_works (P : list val → iProp Σ) :
    {{{ P [] }}} mk_stack #() {{{ v, RET v; is_stack P v }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    rewrite -wp_fupd.
    wp_lam.
    wp_alloc l as "Hl".
    wp_apply mk_mailbox_works ; first done. iIntros (v) "#Hmailbox".
    iMod (inv_alloc Nstack _ (stack_inv P l) with "[Hl HP]") as "#Hinv".
    { by iNext; iExists _, []; iFrame. }
    wp_pures. iModIntro; iApply "HΦ"; iExists _; auto.
  Qed.

  Theorem push_works P s v Ψ :
    {{{ is_stack P s ∗ ∀ xs, P xs ={inner_mask}=∗ P (v :: xs) ∗ Ψ #()}}}
      push s v
    {{{ RET #(); Ψ #() }}}.
  Proof.
    iIntros (Φ) "[Hstack Hupd] HΦ". iDestruct "Hstack" as (mailbox l) "(-> & #Hmailbox & #Hinv)".
    iLöb as "IH" forall (v).
    wp_lam. wp_pures.
    wp_apply (put_works with "[Hupd]"); first auto. iIntros (o) "H".
    iDestruct "H" as "[Hsome | [-> HΨ]]".
    - iDestruct "Hsome" as (v') "[-> Hupd]".
      wp_match.
      wp_bind (Load _).
      iInv Nstack as (list xs) "(Hl & Hlist & HP)" "Hclose".
      wp_load.
      iMod ("Hclose" with "[Hl Hlist HP]") as "_".
      { iNext; iExists _, _; iFrame. }
      clear xs.
      iModIntro.
      wp_let. wp_alloc l' as "Hl'". wp_pures. wp_bind (CAS _ _ _).
      iInv Nstack as (list' xs) "(Hl & Hlist & HP)" "Hclose".
      iDestruct (is_list_unboxed with "Hlist") as "[>% Hlist]".
      destruct (decide (list = list')) as [ -> |].
      * wp_cas_suc.
        iMod (fupd_intro_mask' (⊤ ∖ ↑Nstack) inner_mask) as "Hupd'"; first solve_ndisj.
        iMod ("Hupd" with "HP") as "[HP HΨ]".
        iMod "Hupd'" as "_".
        iMod ("Hclose" with "[Hl Hl' HP Hlist]") as "_".
        { iNext; iExists (SOMEV _), (v' :: xs); iFrame; iExists _, _; iFrame; auto. }
        iModIntro.
        wp_if.
        by iApply ("HΦ" with "HΨ").
      * wp_cas_fail.
        iMod ("Hclose" with "[Hl HP Hlist]").
        { iExists _, _; iFrame. }
        iModIntro.
        wp_if.
        iApply ("IH" with "Hupd HΦ").
    - wp_match. iApply ("HΦ" with "HΨ").
  Qed.

  Theorem pop_works P s Ψ :
    {{{ is_stack P s ∗
        (∀ v xs, P (v :: xs) ={inner_mask}=∗ P xs ∗ Ψ (SOMEV v)) ∗
        (P [] ={inner_mask}=∗ P [] ∗ Ψ NONEV) }}}
      pop s
    {{{ v, RET v; Ψ v }}}.
  Proof.
    iIntros (Φ) "(Hstack & Hupdcons & Hupdnil) HΦ".
    iDestruct "Hstack" as (mailbox l) "(-> & #Hmailbox & #Hinv)".
    iLöb as "IH".
    wp_lam. wp_proj. wp_let. wp_proj. wp_let.
    wp_apply (get_works _ (λ v, Ψ v) with "[Hupdcons]").
    { iSplitR; first done.
      iFrame.
      iInv Nstack as (v xs) "(Hl & Hlist & HP)" "Hclose".
      iModIntro.
      iExists xs; iSplitL "HP"; first auto.
      iIntros "HP".
      iMod ("Hclose" with "[HP Hl Hlist]") as "_".
      { iNext; iExists _, _; iFrame. }
      auto. }
    iIntros (ov) "[Hsome | [-> Hupdcons]]".
    - iDestruct "Hsome" as (v) "[-> HΨ]".
      wp_pures.
      iApply ("HΦ" with "HΨ").
    - wp_match. wp_bind (Load _).
      iInv Nstack as (v xs) "(Hl & Hlist & HP)" "Hclose".
      wp_load.
      iDestruct (is_list_disj with "Hlist") as "[Hlist H]".
      iDestruct "H" as "[-> | HSome]".
      * iDestruct (is_list_empty with "Hlist") as %->.
        iMod (fupd_intro_mask' (⊤ ∖ ↑Nstack) inner_mask) as "Hupd'"; first solve_ndisj.
        iMod ("Hupdnil" with "HP") as "[HP HΨ]".
        iMod "Hupd'" as "_".
        iMod ("Hclose" with "[Hlist Hl HP]") as "_".
        { iNext; iExists _, _; iFrame. }
        iModIntro.
        wp_match.
        iApply ("HΦ" with "HΨ").
      * iDestruct "HSome" as (l' h t) "[-> Hl']".
        iMod ("Hclose" with "[Hlist Hl HP]") as "_".
        { iNext; iExists _, _; iFrame. }
        iModIntro.
        wp_match. wp_bind (Load _).
        iInv Nstack as (v xs') "(Hl & Hlist & HP)" "Hclose".
        iDestruct "Hl'" as (q) "Hl'".
        wp_load.
        iMod ("Hclose" with "[Hlist Hl HP]") as "_".
        { iNext; iExists _, _; iFrame. }
        iModIntro.
        wp_pures. wp_bind (CAS _ _ _).
        iInv Nstack as (v' xs'') "(Hl & Hlist & HP)" "Hclose".
        destruct (decide (v' = (SOMEV #l'))) as [ -> |].
        + wp_cas_suc.
          iDestruct (is_list_cons with "[Hl'] Hlist") as (ys) "%"; first by iExists _.
          simplify_eq.
          iMod (fupd_intro_mask' (⊤ ∖ ↑Nstack) inner_mask) as "Hupd'"; first solve_ndisj.
          iMod ("Hupdcons" with "HP") as "[HP HΨ]".
          iMod "Hupd'" as "_".
          iDestruct "Hlist" as (l'' t') "(% & Hl'' & Hlist)"; simplify_eq.
          iDestruct "Hl''" as (q') "Hl''".
          iDestruct (mapsto_agree with "Hl' Hl''") as "%"; simplify_eq.
          iMod ("Hclose" with "[Hlist Hl HP]") as "_".
          { iNext; iExists _, _; iFrame. }
          iModIntro.
          wp_pures.
          iApply ("HΦ" with "HΨ").
        + wp_cas_fail.
          iMod ("Hclose" with "[Hlist Hl HP]") as "_".
          { iNext; iExists _, _; iFrame. }
          iModIntro.
          wp_pures.
          iApply ("IH" with "Hupdcons Hupdnil HΦ").
  Qed.
End proofs.
