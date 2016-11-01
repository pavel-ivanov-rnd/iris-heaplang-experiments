(* Flat Combiner *)

From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import auth frac agree excl dec_agree gset gmap.
From iris.base_logic Require Import big_op saved_prop.
From iris_atomic Require Import misc peritem sync evmap.

Definition doOp : val :=
  λ: "p",
     match: !"p" with
       InjL "req" => "p" <- InjR ((Fst "req") (Snd "req"))
     | InjR "_" => #()
     end.

Definition try_srv : val :=
  λ: "lk" "s",
    if: try_acquire "lk"
      then let: "hd" := !"s" in
           iter "hd" doOp;;
           release "lk"
      else #().

Definition loop: val :=
  rec: "loop" "p" "s" "lk" :=
    match: !"p" with
    InjL "_" =>
        try_srv "lk" "s";;
        "loop" "p" "s" "lk"
    | InjR "r" => "r"
    end.

Definition install : val :=
  λ: "f" "x" "s",
     let: "p" := ref (InjL ("f", "x")) in
     push "s" "p";;
     "p".

Definition mk_flat : val :=
  λ: <>,
   let: "lk" := newlock #() in
   let: "s" := new_stack #() in
   λ: "f" "x",
      let: "p" := install "f" "x" "s" in
      let: "r" := loop "p" "s" "lk" in
      "r".

Global Opaque doOp try_srv install loop mk_flat.

Definition reqR := prodR fracR (dec_agreeR val). (* request x should be kept same *)
Definition toks : Type := gname * gname * gname * gname * gname. (* a bunch of tokens to do state transition *)
Definition tokmR : ucmraT := evmapR loc toks unitR. (* tie each slot to tokens *)
Class flatG Σ := FlatG {
  req_G :> inG Σ reqR;
  tok_G :> inG Σ (authR tokmR);
  sp_G  :> savedPropG Σ (cofe_funCF val idCF)
}.

Definition flatΣ : gFunctors :=
  #[ GFunctor (constRF reqR);
     GFunctor (constRF (authR tokmR));
     savedPropΣ (cofe_funCF val idCF)
   ].

Instance subG_flatΣ {Σ} : subG flatΣ Σ → flatG Σ.
Proof. intros [?%subG_inG [?%subG_inG [? _]%subG_inv]%subG_inv]%subG_inv. split; apply _. Qed.

Section proof.
  Context `{!heapG Σ, !lockG Σ, !evidenceG loc val unitR Σ, !flatG Σ} (N : namespace).

  Definition init_s (ts: toks) :=
    let '(_, γ1, γ3, _, _) := ts in (own γ1 (Excl ()) ★ own γ3 (Excl ()))%I.

  Definition installed_s R (ts: toks) (f x: val) :=
    let '(γx, γ1, _, γ4, γq) := ts in
    (∃ (P: val → iProp Σ) Q,
       own γx ((1/2)%Qp, DecAgree x) ★ P x ★ ({{ R ★ P x }} f x {{ v, R ★ Q x v }}) ★
       saved_prop_own γq (Q x) ★ own γ1 (Excl ()) ★ own γ4 (Excl ()))%I.

  Definition received_s (ts: toks) (x: val) γr :=
    let '(γx, _, _, γ4, _) := ts in
    (own γx ((1/2/2)%Qp, DecAgree x) ★ own γr (Excl ()) ★ own γ4 (Excl ()))%I.

  Definition finished_s (ts: toks) (x y: val) :=
    let '(γx, γ1, _, γ4, γq) := ts in
    (∃ Q: val → val → iProp Σ,
       own γx ((1/2)%Qp, DecAgree x) ★ saved_prop_own γq (Q x) ★
       Q x y ★ own γ1 (Excl ()) ★ own γ4 (Excl ()))%I.

  Definition evm := ev loc toks.
  
  (* p slot invariant *)
  Definition p_inv R (γm γr: gname) (v: val) :=
    (∃ (ts: toks) (p : loc),
       v = #p ★ evm γm p ts ★
       ((* INIT *)
        (∃ y: val, p ↦{1/2} InjRV y ★ init_s ts)∨
        (* INSTALLED *)
        (∃ f x: val, p ↦{1/2} InjLV (f, x) ★ installed_s R ts f x) ∨
        (* RECEIVED *)
        (∃ f x: val, p ↦{1/2} InjLV (f, x) ★ received_s ts x γr) ∨
        (* FINISHED *)
        (∃ x y: val, p ↦{1/2} InjRV y ★ finished_s ts x y)))%I.

  Definition srv_stack_inv R γs γm γr s := (∃ xs, is_stack' (p_inv R γm γr) γs xs s)%I.

  Definition srv_tokm_inv γm := (∃ m : tokmR, own γm (● m) ★ [★ map] p ↦ _ ∈ m, ∃ v, p ↦{1/2} v)%I.

  Lemma install_push_spec R
        (p: loc) (γs γm γr: gname) (ts: toks)
        (s: loc) (f x: val) (Φ: val → iProp Σ) :
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_stack_inv R γs γm γr s ★ srv_tokm_inv γm) ★
    evm γm p ts ★ installed_s R ts f x ★
    p ↦{1/2} InjLV (f, x) ★ ((∃ hd, evs γs hd #p) -★ Φ #())
    ⊢ WP push #s #p {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & Hpm & Hs & Hp & HΦ)".
    rewrite /srv_stack_inv.
    iDestruct (push_spec N (p_inv R γm γr) (fun v => (∃ hd, evs γs hd #p) ★ v = #())%I
               with "[-HΦ]") as "Hpush"=>//.
    - iFrame "Hh". iSplitL "Hp Hs Hpm"; last eauto.
      iExists ts. iExists p. iSplit=>//. iFrame "Hpm".
      iRight. iLeft. iExists f, x. iFrame.
    - iApply wp_wand_r.
      iSplitL "Hpush"; first done.
      iIntros (?) "[? %]". subst.
      by iApply "HΦ".
  Qed.

  Definition installed_recp (ts: toks) (x: val) (Q: val → val → iProp Σ) :=
    let '(γx, _, γ3, _, γq) := ts in
    (own γ3 (Excl ()) ★ own γx ((1/2)%Qp, DecAgree x) ★ saved_prop_own γq (Q x))%I.

  Lemma install_spec
        R P Q
        (f x: val) (γs γm γr: gname) (s: loc)
        (Φ: val → iProp Σ):
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_stack_inv R γs γm γr s ★ srv_tokm_inv γm) ★
    P x ★ ({{ R ★ P x }} f x {{ v, R ★ Q x v }}) ★
    (∀ (p: loc) (ts: toks), installed_recp ts x Q -★ evm γm p ts -★(∃ hd, evs γs hd #p) -★ Φ #p)
    ⊢ WP install f x #s {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & Hpx & Hf & HΦ)".
    wp_seq. wp_let. wp_let. wp_alloc p as "Hl".
    iApply fupd_wp.
    iMod (own_alloc (Excl ())) as (γ1) "Ho1"; first done.
    iMod (own_alloc (Excl ())) as (γ3) "Ho3"; first done.
    iMod (own_alloc (Excl ())) as (γ4) "Ho4"; first done.
    iMod (own_alloc (1%Qp, DecAgree x)) as (γx) "Hx"; first done.
    iMod (saved_prop_alloc (F:=(cofe_funCF val idCF)) (Q x)%I) as (γq) "#?".
    iInv N as "[Hrs >Hm]" "Hclose".
    iDestruct "Hm" as (m) "[Hm HRm]".
    destruct (m !! p) eqn:Heqn.
    - (* old name *)
      iDestruct (big_sepM_delete (fun p _ => ∃ v : val, p ↦{1 / 2} v)%I m with "HRm") as "[Hp HRm]"=>//.
      iDestruct "Hp" as (?) "Hp". iExFalso. iApply bogus_heap; last by iFrame "Hh Hl Hp". auto.
    - (* fresh name *)
      iDestruct (evmap_alloc _ _ _ m p (γx, γ1, γ3, γ4, γq) with "[Hm]") as ">[Hm1 #Hm2]"=>//.
      iDestruct "Hl" as "[Hl1 Hl2]".
      iMod ("Hclose" with "[HRm Hm1 Hl1 Hrs]").
      + iNext. iFrame. iExists (<[p := (∅, DecAgree (γx, γ1, γ3, γ4, γq))]> m). iFrame.
        iDestruct (big_sepM_insert _ m with "[-]") as "H"=>//.
        iSplitL "Hl1"; last by iAssumption. eauto.
      + iDestruct (own_update with "Hx") as ">[Hx1 Hx2]"; first by apply pair_l_frac_op_1'.
        iModIntro. wp_let. wp_bind ((push _) _).
        iApply install_push_spec=>//.
        iFrame "#". rewrite /evm /installed_s. iFrame.
        iSplitL "Hpx Hf".
        { iExists P, Q. by iFrame. }
        iIntros "Hhd". wp_seq. iModIntro.
        iSpecialize ("HΦ" $! p (γx, γ1, γ3, γ4, γq) with "[-Hhd]")=>//.
        { rewrite /installed_recp. iFrame. iFrame "#". }
        by iApply ("HΦ" with "[]").
  Qed.

  Lemma loop_iter_doOp_spec R (s hd: loc) (γs γm γr: gname) xs Φ:
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_stack_inv R γs γm γr s ★ srv_tokm_inv γm) ★ own γr (Excl ()) ★ R ★
    is_list' γs hd xs ★ (own γr (Excl ()) -★ R -★ Φ #())
    ⊢ WP iter #hd doOp {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hf & #? & Ho2 & HR & Hlist' & HΦ)".
    iApply (iter_spec N (p_inv R γm γr) Φ
                      (* (fun v => v = #() ★ own γr (Excl ()) ★ R)%I *)
                      γs s (own γr (Excl ()) ★ R)%I (srv_tokm_inv γm) xs hd doOp doOp
            with "[-]")=>//.
    - rewrite /f_spec.
      iIntros (Φ' x _) "(#Hh & #? & Hev & [Hor HR] & HΦ')".
      iDestruct "Hev" as (xhd) "#Hev".
      wp_rec.  wp_bind (! _)%E. iInv N as "[Hs >Hm]" "Hclose".
      iDestruct "Hs" as (gxs ghd) "[>Hghd [>Hgxs HRs]]". (* global xs, hd *)
      iDestruct "HRs" as (m) "[>Hom HRs]".
      (* acccess *)
      iDestruct (ev_map_witness _ _ _ m with "[Hev Hom]") as %H'; first by iFrame.
      iDestruct (big_sepM_delete_later (perR _) m with "HRs") as "[Hp HRm]"=>//.
      iDestruct "Hp" as (v') "[>% [Hpinv' >Hahd]]". inversion H. subst.
      iDestruct "Hpinv'" as (ts p'') "[>% [>#Hevm [Hp | [Hp | [Hp | Hp]]]]]"; subst.
      + iDestruct "Hp" as (y) "(>Hp & Hs)".
        wp_load. iMod ("Hclose" with "[-Hor HR Hev HΦ']").
        { iNext. iFrame. iExists gxs, ghd.
          iFrame "Hghd Hgxs". iExists m.
          iFrame "Hom". iDestruct (big_sepM_delete _ m with "[-]") as "?"=>//.
          iFrame. iExists #p''. iSplitR; first done. iExists ts, p''.
          iSplitR; first done. iFrame "#". iLeft. iExists y. iFrame. }
        iModIntro. wp_match. iModIntro. iApply ("HΦ'" with "[Hor HR]"). iFrame.
      + iDestruct "Hp" as (f' x') "(Hp & Hs)".
        wp_load. destruct ts as [[[[γx γ1] γ3] γ4] γq].
        iDestruct "Hs" as (P Q) "(Hx & Hpx & Hf' & HoQ & Ho1 & Ho4)".
        iAssert (|==> own γx (((1/2/2)%Qp, DecAgree x') ⋅
                               ((1/2/2)%Qp, DecAgree x')))%I with "[Hx]" as ">[Hx1 Hx2]".
        { iDestruct (own_update with "Hx") as "?"; last by iAssumption.
          rewrite -{1}(Qp_div_2 (1/2)%Qp).
          by apply pair_l_frac_op'. }
        iMod ("Hclose" with "[-Hf' Ho1 Hx2 HR HoQ HΦ' Hpx]").
        { iNext. iFrame. iExists gxs, ghd.
          iFrame "Hghd Hgxs". iExists m.
          iFrame "Hom". iDestruct (big_sepM_delete _ m with "[-]") as "?"=>//.
          simpl. iFrame. iExists #p''. iSplitR; auto. rewrite /allocated.
          iExists (γx, γ1, γ3, γ4, γq), p''. iSplitR; auto.
          iFrame "#". iRight. iRight. iLeft. iExists f', x'. iFrame. }
        iModIntro. wp_match.
        wp_proj. wp_proj.
        wp_bind (f' _). iApply wp_wand_r. iSplitL "Hpx Hf' HR".
        { iApply "Hf'". iFrame. }
        iIntros (v) "[HR HQ]".
        wp_value. iModIntro. iInv N as "[Hs >Hm]" "Hclose".
        iDestruct "Hs" as (xs'' hd''') "[>Hhd [>Hxs HRs]]".
        iDestruct "HRs" as (m') "[>Hom HRs]".
        iDestruct (ev_map_witness _ _ _ m' with "[Hevm Hom]") as %?; first by iFrame.
        iDestruct (big_sepM_delete_later (perR _) m' with "HRs") as "[Hp HRm]"=>//.
        iDestruct "Hp" as (v'') "[>% [Hpinv' >Hhd'']]". inversion H1. subst.
        iDestruct "Hpinv'" as ([[[[γx' γ1'] γ3'] γ4'] γq'] p'''') "[>% [>#Hevm2 Hps]]".
        inversion H2. subst.
        destruct (decide (γ1 = γ1' ∧ γx = γx' ∧ γ3 = γ3' ∧ γ4 = γ4' ∧ γq = γq'))
          as [[? [? [? [? ?]]]]|Hneq]; subst.
        {
          iDestruct "Hps" as "[Hp | [Hp | [Hp | Hp]]]".
          * iDestruct "Hp" as (?) "(_ & >Ho1' & _)".
            iApply excl_falso. iFrame.
          * iDestruct "Hp" as (? ?) "[>? Hs]". iDestruct "Hs" as (? ?) "(_ & _ & _ & _ & >Ho1' & _)".
            iApply excl_falso. iFrame.
          * iDestruct "Hp" as (? x5) ">(Hp & Hx & Hor & Ho4)".
            iDestruct "Hm" as (m2) "[Hom2 HRp]".
            iDestruct (ev_map_witness _ _ _ m2 with "[Hevm Hom2]") as %?; first by iFrame.
            iDestruct (big_sepM_delete _ m2 with "HRp") as "[HRk HRp]"=>//.
            iDestruct "HRk" as (?) "HRk".
            iDestruct (heap_mapsto_op_1 with "[HRk Hp]") as "[% Hp]"; first by iFrame.
            rewrite Qp_div_2. wp_store.
            (* now close the invariant *)
            iDestruct (m_frag_agree' with "[Hx Hx2]") as "[Hx %]"; first iFrame.
            subst. rewrite Qp_div_2. iMod ("Hclose" with "[-HR Hor HΦ']").
            { iNext. iDestruct "Hp" as "[Hp1 Hp2]".
              iAssert (srv_tokm_inv γm) with "[Hp1 HRp Hom2]" as "HRp".
              { iExists m2. iFrame. iApply (big_sepM_delete _ m2)=>//.
                iFrame. eauto. }
              iFrame. iExists xs''. iFrame. iExists hd'''. iFrame.
              iExists m'. iFrame.
              iDestruct (big_sepM_delete _ m' with "[-]") as "?"=>//.
              { simpl. iFrame. iExists #p''''.
                iSplitR; first auto. iExists (γx', γ1', γ3', γ4', γq'), p''''.
                iSplitR; first auto. iFrame "Hevm". iRight. iRight.
                iRight. iExists x5, v. iFrame.
                iExists Q. iFrame. 
              }
            }
            iApply "HΦ'". iFrame.
          * iDestruct "Hp" as (? ?) "[? Hs]". iDestruct "Hs" as (?) "(_ & _ & _ & >Ho1' & _)".
            iApply excl_falso. iFrame.
        }
        { iDestruct (evmap_frag_agree_split with "[]") as "%"; first iFrame "Hevm Hevm2".
          inversion H3. subst. by contradiction Hneq. }
      + destruct ts as [[[[γx γ1] γ3] γ4] γq]. iDestruct "Hp" as (? x) "(_ & _ & >Ho2' & _)".
        iApply excl_falso. iFrame.
      + destruct ts as [[[[γx γ1] γ3] γ4] γq]. iDestruct "Hp" as (x' y) "[Hp Hs]".
        iDestruct "Hs" as (Q) "(>Hx & HoQ & HQxy & >Ho1 & >Ho4)".
        wp_load. iMod ("Hclose" with "[-HΦ' HR Hor]").
        { iNext. iFrame. iExists gxs, ghd.
          iFrame "Hghd Hgxs". iExists m.
          iFrame "Hom". iDestruct (big_sepM_delete _ m with "[-]") as "?"=>//.
          iFrame. iExists #p''. iSplitR; first auto. iExists (γx, γ1, γ3, γ4, γq), p''.
          iSplitR; auto. iFrame "#". iRight. iRight. iRight. iExists x', y. iFrame.
          iExists Q. iFrame. }
        iModIntro. wp_match.
        iApply "HΦ'". iFrame.
    - apply to_of_val.
    - iFrame "#". iFrame. iIntros "[Hor HR]".
      iApply ("HΦ" with "Hor HR").
  Qed.

  Definition own_γ3 (ts: toks) := let '(_, _, γ3, _, _) := ts in own γ3 (Excl ()).
  Definition finished_recp (ts: toks) (x y: val) :=
    let '(γx, _, _, _, γq) := ts in
    (∃ Q, own γx ((1 / 2)%Qp, DecAgree x) ★ saved_prop_own γq (Q x) ★ Q x y)%I.

  Lemma try_srv_spec R (s: loc) (lk: val) (γs γr γm γlk: gname) Φ :
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_stack_inv R γs γm γr s ★ srv_tokm_inv γm) ★
    is_lock N γlk lk (own γr (Excl ()) ★ R) ★ Φ #()
    ⊢ WP try_srv lk #s {{ Φ }}.
  Proof.
    iIntros (?) "(#? & #? & #? & HΦ)".
    wp_seq. wp_let.
    wp_bind (try_acquire _). iApply try_acquire_spec.
    iFrame "#". iSplit; last by wp_if.
    (* acquired the lock *)
    iIntros "Hlocked [Ho2 HR]".
    wp_if. wp_bind (! _)%E.
    iInv N as "[H >Hm]" "Hclose".
    iDestruct "H" as (xs' hd') "[>Hs [>Hxs HRs]]".
    wp_load. iDestruct (dup_is_list' with "[Hxs]") as ">[Hxs1 Hxs2]"; first by iFrame.
    iMod ("Hclose" with "[Hs Hxs1 HRs Hm]").
    { iNext. iFrame. iExists xs', hd'. by iFrame. }
    iModIntro. wp_let.
    wp_bind (iter _ _).
    iApply wp_wand_r. iSplitL "HR Ho2 Hxs2".
    { iApply (loop_iter_doOp_spec R _ _ _ _ _ _ (fun v => own γr (Excl ()) ★ R ★ v = #()))%I=>//.      
      iFrame "#". iFrame. iIntros "? ?". by iFrame. }
    iIntros (f') "[Ho [HR %]]". subst.
    wp_let. iApply release_spec. iFrame "#".
    iFrame. iNext. iIntros. done.
  Qed.

  Lemma loop_spec R (p s: loc) (lk: val)
        (γs γr γm γlk: gname) (ts: toks) Φ:
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_stack_inv R γs γm γr s ★ srv_tokm_inv γm) ★
    is_lock N γlk lk (own γr (Excl ()) ★ R) ★
    own_γ3 ts ★ evm γm p ts ★
    (∃ hd, evs γs hd #p) ★ (∀ x y, finished_recp ts x y -★ Φ y)
    ⊢ WP loop #p #s lk {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & #? & Ho3 & #Hev & Hhd & HΦ)".
    iLöb as "IH". wp_rec. repeat wp_let.
    wp_bind (! _)%E. iInv N as "[Hinv >?]" "Hclose".
    iDestruct "Hinv" as (xs hd) "[>Hs [>Hxs HRs]]".
    iDestruct "HRs" as (m) "[>Hom HRs]".
    iDestruct "Hhd" as (hdp) "Hhd".
    destruct (m !! hdp) eqn:Heqn.
    - iDestruct (big_sepM_delete_later _ m with "HRs") as "[Hp Hrs]"=>//.
      iDestruct "Hp" as (?) "[>% [Hpr ?]]"; subst.
      iDestruct "Hpr" as (ts' p') "(>% & >Hp' & Hp)".
      subst. iDestruct (ev_map_witness _ _ _ m with "[Hom Hhd]") as %H=>//; first iFrame.
      rewrite Heqn in H. inversion H. subst.
      iDestruct (evmap_frag_agree_split with "[Hp']") as "%"; first iFrame "Hev Hp'". subst.
      destruct ts' as [[[[γx γ1] γ3] γ4] γq].
      iDestruct "Hp" as "[Hp | [Hp | [ Hp | Hp]]]".
      + iDestruct "Hp" as (?) "(_ & _ & >Ho3')".
        iApply excl_falso. iFrame.
      + iDestruct "Hp" as (f x) "(>Hp & Hs')".
        wp_load. iMod ("Hclose" with "[-Ho3 HΦ Hhd]").
        { iNext. iFrame. iExists xs, hd. iFrame. iExists m. iFrame.
          iDestruct (big_sepM_delete _ m with "[-]") as "?"=>//.
          iFrame. iExists #p. iSplitR; first auto. iExists (γx, γ1, γ3, γ4, γq), p.
          iSplitR; first auto. iFrame.
          iRight. iLeft. iExists f, x. iFrame. }
        iModIntro. wp_match.
        wp_bind (try_srv _ _). iApply try_srv_spec=>//.
        iFrame "#". wp_seq.
        iAssert (∃ hd, evs γs hd #p)%I with "[Hhd]" as "Hhd"; eauto.
        by iApply ("IH" with "Ho3 Hhd").
      + iDestruct "Hp" as (f x) "(Hp & Hx & Ho2 & Ho4)".
        wp_load.
        iMod ("Hclose" with "[-Ho3 HΦ Hhd]").
        { iNext. iFrame. iExists xs, hd. iFrame. iExists m. iFrame.
          iDestruct (big_sepM_delete _ m with "[-]") as "?"=>//.
          iFrame. iExists #p. iSplitR; auto. iExists (γx, γ1, γ3, γ4, γq), p.
          iSplitR; first auto. iFrame.
          iRight. iRight. iLeft. iExists f, x. iFrame. }
        iModIntro. wp_match.
        wp_bind (try_srv _ _). iApply try_srv_spec=>//.
        iFrame "#". wp_seq.
        iAssert (∃ hd, evs γs hd #p)%I with "[Hhd]" as "Hhd"; eauto.
        by iApply ("IH" with "Ho3 Hhd").
       + iDestruct "Hp" as (x y) "[>Hp Hs']". iDestruct "Hs'" as (Q) "(>Hx & HoQ & HQ & >Ho1 & >Ho4)".
          wp_load. iMod ("Hclose" with "[-Ho4 HΦ Hx HoQ HQ]").
          { iNext. iFrame. iExists xs, hd. iFrame. iExists m. iFrame.
            iDestruct (big_sepM_delete _ m with "[-]") as "?"=>//.
            iFrame. iExists #p. iSplitR; auto. iExists (γx, γ1, γ3, γ4, γq), p.
            iSplitR; first auto. iFrame.
            iLeft. iExists y. iFrame. }
          iModIntro. wp_match. iApply ("HΦ" with "[-]"). iFrame.
          iExists Q. iFrame.
    - iExFalso. iApply (map_agree_none' _ _ _ m)=>//. iFrame "Hom".
      rewrite /ev. eauto.
  Qed.

  Lemma mk_flat_spec: mk_syncer_spec N mk_flat.
  Proof.
    iIntros (R Φ HN) "(#Hh & HR & HΦ)".
    iMod (own_alloc (Excl ())) as (γr) "Ho2"; first done.
    iMod (own_alloc (● (∅: tokmR) ⋅ ◯ ∅)) as (γm) "[Hm _]"; first by rewrite -auth_both_op.
    iAssert (srv_tokm_inv γm) with "[Hm]" as "Hm"; first eauto.
    { iExists ∅. iFrame. by rewrite big_sepM_empty. }
    wp_seq. wp_bind (newlock _).
    iApply (newlock_spec _ (own γr (Excl ()) ★ R))%I=>//.
    iFrame "Hh Ho2 HR". iNext. iIntros (lk γlk) "#Hlk".
    wp_let. wp_bind (new_stack _).
    iApply (new_stack_spec' _ (p_inv _ γm γr))=>//.
    iFrame "Hh Hm". iIntros (γ s) "#Hss".
    wp_let. iModIntro. iApply "HΦ". rewrite /synced.
    iAlways.
    iIntros (f). wp_let. iModIntro. iAlways.
    iIntros (P Q x) "#Hf".
    iIntros "!# Hp". wp_let.
    wp_bind (install _ _ _).
    iApply (install_spec R P Q)=>//.
    iFrame "#". iFrame "Hp". iSplitR; first iApply "Hf".
    iIntros (p [[[[γx γ1] γ3] γ4] γq]) "(Ho3 & Hx & HoQ) Hev Hhd".
    wp_let. wp_bind (loop _ _ _).
    iApply loop_spec=>//.
    iFrame "#". iFrame.
    iIntros (? ?) "Hs".
    iDestruct "Hs" as (Q') "(Hx' & HoQ' & HQ')".
    destruct (decide (x = a)) as [->|Hneq].
    - iDestruct (saved_prop_agree with "[HoQ HoQ']") as "Heq"; first by iFrame.
      wp_let. iDestruct (uPred.cofe_funC_equivI with "Heq") as "Heq".
      iSpecialize ("Heq" $! a0). by iRewrite "Heq" in "HQ'".
    - iExFalso. iCombine "Hx" "Hx'" as "Hx".
      iDestruct (own_valid with "Hx") as %[_ H1].
      rewrite pair_op //= dec_agree_ne in H1=>//.
  Qed.

End proof.
