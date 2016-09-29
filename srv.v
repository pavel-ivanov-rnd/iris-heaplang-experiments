From iris.program_logic Require Export auth weakestpre.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import upred frac agree excl dec_agree upred_big_op gset gmap.
From iris.tests Require Import misc atomic treiber_stack.

Definition doOp (f: val) : val :=
  λ: "p",
     match: !"p" with
       InjL "x" => "p" <- InjR (f "x")
     | InjR "_" => #()
     end.

Definition loop (f: val): val :=
  rec: "loop" "p" "s" "lk" :=
    match: !"p" with
      InjL "_" =>
        if: try_acquire "lk"
          then iter (!"s") (doOp f);;
               release "lk";;
               "loop" "p" "s" "lk"
          else "loop" "p" "s" "lk"
    | InjR "r" => "r"
    end.

Definition install : val :=
  λ: "x" "s",
     let: "p" := ref (InjL "x") in
     push "s" "p";;
     "p".

Definition flat (f: val) : val :=
  λ: <>,
   let: "lk" := newlock #() in
   let: "s" := new_stack #() in
   λ: "x",
      let: "p" := install "x" "s" in
      loop f "p" "s" "lk".

Global Opaque doOp install loop flat.

Definition srvR := prodR fracR (dec_agreeR val).
Definition toks : Type := gname * gname * gname * gname.
Definition tokmR := evmapR loc toks.
Definition srvmR := evmapR loc val.
Class srvG Σ := SrvG {
  srv_G :> inG Σ srvR;
  tok_G :> inG Σ (authR tokmR);
}.

Definition srvΣ : gFunctors :=
  #[ GFunctor (constRF srvR);
     GFunctor (constRF (authR tokmR))
   ].

Instance subG_srvΣ {Σ} : subG srvΣ Σ → srvG Σ.
Proof. intros [?%subG_inG [?%subG_inG _]%subG_inv]%subG_inv. split; apply _. Qed.

Section proof.
  Context `{!heapG Σ, !lockG Σ, !evidenceG loc val Σ, !srvG Σ} (N : namespace).
  Context (Q: val → val → Prop).
  
  (* p slot invariant *)
  Definition p_inv (γm γ2: gname) (v: val) :=
    (∃ (γx γ1 γ3 γ4: gname) (p : loc) (q: Qp),
       v = #p ★ own γm (◯ ({[ p := (q, DecAgree (γx, γ1, γ3, γ4)) ]} : tokmR)) ★
       ((* INIT *)
        (∃ y: val, p ↦{1/2} InjRV y ★ own γ1 (Excl ()) ★ own γ3 (Excl ()))∨
        (* INSTALLED *)
        (∃ x: val, p ↦{1/2} InjLV x ★ own γx ((1/2)%Qp, DecAgree x) ★ own γ1 (Excl ()) ★ own γ4 (Excl ())) ∨
        (* RECEIVED *)
        (∃ x: val, p ↦{1/2} InjLV x ★ own γx ((1/2/2)%Qp, DecAgree x) ★ own γ2 (Excl ()) ★ own γ4 (Excl ())) ∨
        (* FINISHED *)
        (∃ x y: val, p ↦{1/2} InjRV y ★ own γx ((1/2)%Qp, DecAgree x) ★ ■ Q x y ★ own γ1 (Excl ()) ★ own γ4 (Excl ()))))%I.

  Definition srv_stack_inv (γs γm γ2: gname) (s: loc) := (∃ xs, is_stack' (p_inv γm γ2) γs xs s)%I.

  Definition srv_tokm_inv γm := (∃ m : tokmR, own γm (● m) ★ [★ map] p ↦ _ ∈ m, ∃ v, p ↦{1/2} v)%I.

  Lemma install_push_spec
        (Φ: val → iProp Σ)
        (p: loc) (γs γm γx γ1 γ2 γ3 γ4: gname)
        (s: loc) (x: val) :
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_stack_inv γs γm γ2 s ★ srv_tokm_inv γm) ★ own γx ((1/2)%Qp, DecAgree x) ★
    own γm (◯ ({[ p := ((1 / 2)%Qp, DecAgree (γx, γ1, γ3, γ4)) ]})) ★
    p ↦{1/2} InjLV x ★ own γ1 (Excl ()) ★ own γ4 (Excl ()) ★ ((∃ hd, ev γs hd #p) -★ Φ #())
    ⊢ WP push #s #p {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & Hx & Hpm & Hp & Ho1 & Ho2 & HΦ)".
    rewrite /srv_stack_inv.
    iDestruct (push_spec N (p_inv γm γ2) (fun v => (∃ hd, ev γs hd #p) ★ v = #())%I
               with "[-HΦ]") as "Hpush"=>//.
    - iFrame "Hh". iSplitL "Hx Hp Hpm Ho1 Ho2"; last eauto.
      iExists γx, γ1, γ3, γ4. iExists p, (1/2)%Qp. iSplit=>//. iFrame "Hpm".
      iRight. iLeft.
      iExists x. iFrame.
    - iApply wp_wand_r.
      iSplitL "Hpush"; first done.
      iIntros (?) "[? %]". subst.
      by iApply "HΦ".
  Qed.

  Lemma install_spec
        (Φ: val → iProp Σ)
        (x: val) (γs γm γ2: gname) (s: loc):
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_stack_inv γs γm γ2 s ★ srv_tokm_inv γm) ★
    (∀ (p: loc) (γx γ1 γ3 γ4: gname),
       own γ3 (Excl ()) -★ own γm (◯ {[ p := ((1 / 2)%Qp, DecAgree (γx, γ1, γ3, γ4)) ]}) -★
       own γx ((1/2)%Qp, DecAgree x) -★ (∃ hd, ev γs hd #p) -★ Φ #p)
    ⊢ WP install x #s {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & HΦ)".
    wp_seq. wp_let. wp_alloc p as "Hl".
    iApply pvs_wp.
    iVs (own_alloc (Excl ())) as (γ1) "Ho1"; first done.
    iVs (own_alloc (Excl ())) as (γ3) "Ho3"; first done.
    iVs (own_alloc (Excl ())) as (γ4) "Ho4"; first done.
    iVs (own_alloc (1%Qp, DecAgree x)) as (γx) "Hx"; first done.
    iInv N as ">[Hrs Hm]" "Hclose".
    iDestruct "Hm" as (m) "[Hm HRm]".
    destruct (m !! p) eqn:Heqn.
    - (* old name *)
      iDestruct (big_sepM_delete (fun p _ => ∃ v : val, p ↦{1 / 2} v)%I m with "HRm") as "[Hp HRm]"=>//.
      iDestruct "Hp" as (?) "Hp". iExFalso. iApply bogus_heap; last by iFrame "Hh Hl Hp". auto.
    - (* fresh name *)
      iAssert (|=r=> own γm (● ({[p := (1%Qp, DecAgree (γx, γ1, γ3, γ4))]} ⋅ m) ⋅
                             ◯ {[p := (1%Qp, DecAgree (γx, γ1, γ3, γ4))]}))%I with "[Hm]" as "==>[Hm1 Hm2]".
      { iDestruct (own_update with "Hm") as "?"; last by iAssumption.
        apply auth_update_no_frag. apply alloc_unit_singleton_local_update=>//. }
      iDestruct "Hl" as "[Hl1 Hl2]".
      iVs ("Hclose" with "[HRm Hm1 Hl1 Hrs]").
      + iNext. iFrame. iExists ({[p := (1%Qp, DecAgree (γx, γ1, γ3, γ4))]} ⋅ m).
        iFrame.
        replace ({[p := (1%Qp, DecAgree (γx, γ1, γ3, γ4))]} ⋅ m) with
                (<[p := (1%Qp, DecAgree (γx, γ1, γ3, γ4))]> m); last by apply insert_singleton_op.
        iDestruct (big_sepM_insert _ m with "[-]") as "H"=>//.
        iSplitL "Hl1"; last by iAssumption. simpl. auto.
      + iAssert (|=r=>own γm (◯ {[p := ((1/2)%Qp, DecAgree (γx, γ1, γ3, γ4))]} ⋅
                              ◯ {[p := ((1/2)%Qp, DecAgree (γx, γ1, γ3, γ4))]}))%I
        with "[Hm2]" as "==>[Hfrag1 Hfrag2]".
        { iDestruct (own_update with "Hm2") as "?"; last by iAssumption.
          rewrite <- auth_frag_op.
          by rewrite op_singleton pair_op dec_agree_idemp frac_op' Qp_div_2. }
        iDestruct (own_update with "Hx") as "==>[Hx1 Hx2]"; first by apply pair_l_frac_op_1'.
        iVsIntro. wp_let. wp_bind ((push _) _).
        iApply install_push_spec=>//.
        iFrame "#". iFrame "Hx1 Hfrag1 Hl2 Ho1 Ho4".
        iIntros "Hev". wp_seq. iVsIntro.
        iSpecialize ("HΦ" $! p γx γ1 γ3 γ4 with "[-Hx2 Hfrag2 Hev]")=>//.
        by iApply ("HΦ" with "Hfrag2 Hx2").
  Qed.

  Lemma access (γ γm γ2: gname) x xs m :
    ∀ hd: loc,
    heapN ⊥ N → x ∈ xs  →
    heap_ctx ★ ([★ map] hd↦v ∈ m, perR (p_inv γm γ2) hd v) ★ own γ (● m) ★
    is_list' γ hd xs
    ⊢ ∃ hd' v', ([★ map] hd↦v ∈ delete hd' m, perR (p_inv γm γ2) hd v) ★
                perR' (p_inv γm γ2) hd' v' x ★ m !! hd' = Some v' ★ own γ (● m).
  Proof.
    induction xs as [|x' xs' IHxs'].
    - iIntros (? _ Habsurd). inversion Habsurd.
    - destruct (decide (x = x')) as [->|Hneq].
      + iIntros (hd HN _) "(#Hh & HR & Hom & Hxs)".
        simpl. iDestruct "Hxs" as (hd' q) "[Hhd [Hev Hxs']]".
        rewrite /ev. destruct (m !! hd) eqn:Heqn.
        * iDestruct (big_sepM_delete (perR (p_inv γm γ2)) m with "HR") as "[Hp HRm]"=>//.
          iDestruct "Hp" as (v') "[% [? ?]]".
          subst.
          destruct (decide (x' = v')) as [->|Hneq].
          { iFrame. iExists hd. iFrame. iExists (1%Qp, DecAgree v'). iSplitL; auto. }
          { iExFalso.
            iDestruct "Hev" as (?) "Hev".  iCombine "Hom" "Hev" as "Hauth".
            iDestruct (own_valid γ (● m ⋅ ◯ {[hd := (_, DecAgree x')]}) with "[Hauth]") as %Hvalid=>//.
            iPureIntro. apply auth_valid_discrete_2 in Hvalid as [[af Compose%leibniz_equiv_iff] Valid].
            apply Hneq. eapply (map_agree_eq _ _ m)=>//. }
        * iExFalso.
          iDestruct "Hev" as (?) "Hev".  iCombine "Hom" "Hev" as "Hauth".
          iDestruct (own_valid γ (● m ⋅ ◯ {[hd := (_, DecAgree x')]}) with "[Hauth]") as %Hvalid=>//.
          iPureIntro. apply auth_valid_discrete_2 in Hvalid as [[af Compose%leibniz_equiv_iff] Valid].
          eapply (map_agree_none _ _ m)=>//.
      + iIntros (hd HN ?).
        assert (x ∈ xs').
        { set_solver. }
        iIntros "(#Hh & HRs & Hom & Hxs')".
        simpl. iDestruct "Hxs'" as (hd' q) "[Hhd [Hev Hxs']]".
        iDestruct (IHxs' hd' with "[HRs Hxs' Hom]") as "?"=>//.
        iFrame "#". iFrame.
  Qed.

  Lemma loop_iter_list_spec Φ (f: val) (s hd: loc) (γs γm γ2: gname) xs:
    heapN ⊥ N → (∀ x:val, True ⊢ WP f x {{ v, ■ Q x v }}) →
    heap_ctx ★ inv N (srv_stack_inv γs γm γ2 s ★ srv_tokm_inv γm) ★ own γ2 (Excl ()) ★
    is_list' γs hd xs ★ (own γ2 (Excl ()) -★ Φ #())
    ⊢ WP iter #hd (doOp f) {{ Φ }}.
  Proof.
    iIntros (HN Hf) "(#? & #? & Ho2 & Hlist' & HΦ)".
    iApply pvs_wp.
    iDestruct (dup_is_list' with "[Hlist']") as "==>[Hl1 Hl2]"; first by iFrame.
    iDestruct (dup_is_list' with "[Hl2]") as "==>[Hl2 Hl3]"; first by iFrame.
    iVsIntro.
    iDestruct (iter_spec _ (p_inv γm γ2) (fun v => v = #() ★ own γ2 (Excl ()))%I γs s (is_list' γs hd xs ★ own γ2 (Excl ()))%I (srv_tokm_inv γm) xs hd (doOp f) (doOp f)
              with "[-Hl1 HΦ]") as "Hiter"=>//.
    - rewrite /f_spec. 
      iIntros (Φ' p _ Hin) "(#Hh & #? & (Hls & Ho2) & HΦ')".
      wp_let. wp_bind (! _)%E. iInv N as ">[Hs Hm]" "Hclose".
      iDestruct "Hs" as (xs' hd') "[Hhd [Hxs HRs]]".
      iDestruct (dup_is_list' with "[Hls]") as "==>[Hls1 Hls2]"; first by iFrame.
      iDestruct "HRs" as (m) "[Hom HRs]".
      iDestruct (access with "[Hom HRs Hls1]") as (hd'' [q x]) "[Hrest [Hhd'' [% Hom]]]"=>//; first by iFrame.
      iDestruct "Hhd''" as "(% & H & Hphd)". inversion H0. subst.
      iDestruct "H" as (γx γ1 γ3 γ4 p'' q'') "[% [Hop [Hp | [Hp | [Hp | Hp]]]]]"; subst.
      + iDestruct "Hp" as (x') "(Hp & Ho1 & Ho3)".
        wp_load. iVs ("Hclose" with "[-HΦ' Ho2 Hls2]").
        { iNext. iFrame. iExists xs', hd'.
          iFrame "Hhd Hxs". iExists m.
          iFrame "Hom". iDestruct (big_sepM_delete _ m with "[Hrest Hphd Hop Hp Ho1 Ho3]") as "?"=>//.
          iFrame. iExists #p''. iSplitR; first auto. iExists γx, γ1, γ3, γ4, p'', q''.
          iSplitR; auto. iFrame. iLeft. iExists x'. iFrame. }
        iVsIntro. wp_match. iApply "HΦ'". iFrame.
      + iDestruct "Hp" as (x') "(Hp & Hx & Ho1 & Ho4)".
        wp_load.
        iAssert (|=r=> own γm (◯ {[p'' := ((q''/2)%Qp, DecAgree (γx, γ1, γ3, γ4))]} ⋅
                               ◯ {[p'' := ((q''/2)%Qp, DecAgree (γx, γ1, γ3, γ4))]}))%I
                with "[Hop]" as "==>[Hop1 Hop2]".
        { iDestruct (own_update with "Hop") as "?"; last by iAssumption.
          rewrite <-auth_frag_op.
          by rewrite op_singleton pair_op dec_agree_idemp frac_op' Qp_div_2.
        }
        iAssert (|=r=> own γx (((1 / 2 / 2)%Qp, DecAgree x') ⋅ ((1 / 2/ 2)%Qp, DecAgree x')))%I with "[Hx]" as "==>[Hx1 Hx2]".
        { iDestruct (own_update with "Hx") as "?"; last by iAssumption.
          rewrite -{1}(Qp_div_2 (1/2)%Qp).
          by apply pair_l_frac_op'. }
        iVs ("Hclose" with "[-Hls2 Ho1 Hx2 Hop2 HΦ']").
        { iNext. iFrame. iExists xs', hd'.
          iFrame "Hhd Hxs". iExists m.
          iFrame "Hom". iDestruct (big_sepM_delete _ m with "[-]") as "?"=>//.
          simpl. iFrame. iExists #p''.  iSplitR; auto. rewrite /allocated.
          iExists γx, γ1, γ3, γ4, p'', (q''/2)%Qp. iSplitR; auto.
          iFrame. iRight. iRight. iLeft. iExists x'. iFrame. }
        iVsIntro. wp_match.
        wp_bind (f _). iApply wp_wand_r. iSplitR; first iApply Hf.
        iIntros (v) "%".
        wp_value. iVsIntro. iInv N as ">[Hs Hm]" "Hclose".
        iDestruct "Hs" as (xs'' hd''') "[Hhd [Hxs HRs]]".
        iDestruct "HRs" as (m') "[Hom HRs]".
        iDestruct (dup_is_list' with "[Hls2]") as "==>[Hls2 Hls3]"; first by iFrame.
        iDestruct (access with "[Hom HRs Hls2]") as (hd'''' [q x]) "[Hrest [Hhd'' [% Hom]]]"=>//; first by iFrame.
        iDestruct "Hhd''" as "(% & H & Hphd)". inversion H3. subst.
        iDestruct "H" as (γx' γ1' γ3' γ4' p'''' q'''') "[% [Hop Hps]]".
        inversion H4.
        destruct (decide (γ1 = γ1' ∧ γx = γx' ∧ γ3 = γ3' ∧ γ4 = γ4')) as [[? [? [? ?]]]|Hneq].
        { 
          subst.
          iDestruct "Hps" as "[Hp | [Hp | [Hp | Hp]]]".
          * iDestruct "Hp" as (x5) "(Hp & Ho1' & Ho3)". iExFalso.
            iCombine "Ho1" "Ho1'" as "Ho1".
            by iDestruct (own_valid with "Ho1") as "%".
          * iDestruct "Hp" as (x5) "(Hp & Hx & Ho1' & Ho3)".
            iExFalso. iCombine "Ho1" "Ho1'" as "Ho1".
            by iDestruct (own_valid with "Ho1") as "%".
          * iDestruct "Hp" as (x5) "(Hp & Hx & Ho2 & Ho4)".
            iDestruct "Hm" as (m2) "[Hom2 HRm]".
            destruct (m2 !! p'''') eqn:Heqn.
            { 
              iDestruct (big_sepM_delete _ m2 with "HRm") as "[HRk HRm]"=>//.
              iDestruct "HRk" as (?) "HRk".
              iDestruct (heap_mapsto_op_1 with "[HRk Hp]") as "[% Hp]"; first by iFrame.
              rewrite Qp_div_2. wp_store.
              (* now close the invariant *)
              iDestruct (m_frag_agree with "[Hx Hx2]") as "==>[Hx %]"; first iFrame.
              subst. rewrite Qp_div_2. iVs ("Hclose" with "[-HΦ' Ho2 Hls3]").
              { iNext. iDestruct "Hp" as "[Hp1 Hp2]".
                iAssert (srv_tokm_inv γm) with "[Hp1 HRm Hom2]" as "HRm".
                { iExists m2. iFrame. iApply (big_sepM_delete _ m2)=>//.
                  iFrame. eauto. }
                iFrame. iExists xs''. iFrame. iExists hd'''. iFrame.
                iExists m'. iFrame.
                iDestruct (big_sepM_delete _ m' with "[-]") as "?"=>//.
                { simpl. iFrame. iExists #p''''.
                  iSplitR; first auto. iExists γx', γ1', γ3', γ4'.
                  rewrite /p_inv. iExists p'''', q''''.
                  iSplitR; first auto. iFrame. iRight. iRight.
                  iRight. iExists x5, v. by iFrame. }
              }
              iApply "HΦ'". iFrame.
            }
            { iExFalso.
              iCombine "Hom2" "Hop2" as "Hauth".
              iDestruct (own_valid γm (● m2
                ⋅ ◯ {[p''''
                    := ((q'' / 2)%Qp, DecAgree (γx', γ1', γ3', γ4'))]}) with "[Hauth]") as %Hvalid=>//.
              iPureIntro.
              apply auth_valid_discrete_2 in Hvalid as [[af Compose%leibniz_equiv_iff] Valid].
              eapply (map_agree_none _ _ m2)=>//.
            }
          * iDestruct "Hp" as (? ?) "(_ & _ & _ & Ho1' & _)".
            iExFalso. iCombine "Ho1" "Ho1'" as "Ho1".
            by iDestruct (own_valid with "Ho1") as "%". }
        { iDestruct (evmap_frag_agree with "[Hop Hop2]") as "==>[Hop %]"; first iFrame.
          inversion H5. subst. exfalso. apply Hneq. auto. }
      + iDestruct "Hp" as (y) "(Hp & Hx & Ho2' & Ho4)".
        iExFalso. iCombine "Ho2" "Ho2'" as "Ho2".
        by iDestruct (own_valid with "Ho2") as "%".
      + iDestruct "Hp" as (x' y) "(Hp & Ho1 & Ho4)".
        wp_load. iVs ("Hclose" with "[-HΦ' Ho2 Hls2]").
        { iNext. iFrame. iExists xs', hd'.
          iFrame "Hhd Hxs". iExists m.
          iFrame "Hom". iDestruct (big_sepM_delete _ m with "[Hop Hphd Hrest Hp Ho1 Ho4]") as "?"=>//.
          iFrame. iExists #p''. iSplitR; first auto. iExists γx, γ1, γ3, γ4, p'', q''.
          iSplitR; auto. iFrame. iRight. iRight. iRight. iExists x', y. iFrame. }
        iVsIntro. wp_match. iApply "HΦ'". iFrame.
    - apply to_of_val.
    - rewrite /srv_stack_inv. iFrame "#". iFrame. iIntros "[_ Ho2]". eauto.
    - iApply wp_wand_r. iSplitL "Hiter"; first done.
      iIntros (?) "[% Ho2]". subst. by iApply "HΦ".
  Qed.

  Lemma in_m γs (m: srvmR) k q q' (a b: val):
    m !! k = Some (q, DecAgree b) →
    own γs (● m) ★ own γs (◯ {[ k := (q', DecAgree a)]})
    ⊢ own γs (● m) ★ own γs (◯ {[ k := (q', DecAgree a)]}) ★ a = b.
  Proof.
    iIntros (H) "[HFull HFrag]".
    destruct (decide (a = b)) as [->|Hneq].
    - by iFrame.
    - iCombine "HFull" "HFrag" as "Hauth".
      iDestruct (own_valid γs (● m ⋅ ◯ {[k := (q', DecAgree a)]}) with "[Hauth]") as %Hvalid=>//.
      exfalso. apply auth_valid_discrete_2 in Hvalid as [[af Compose%leibniz_equiv_iff] Valid].
      apply Hneq. eapply (map_agree_eq _ _ m); done.
  Qed.

  Lemma loop_spec Φ (p s: loc) (lk: val) (f: val)
        (γs γ2 γm γlk: gname) (γx γ1 γ3 γ4: gname):
    heapN ⊥ N → (∀ x:val, True ⊢ WP f x {{ v, ■ Q x v }}) →
    heap_ctx ★ inv N (srv_stack_inv γs γm γ2 s ★ srv_tokm_inv γm) ★ is_lock N γlk lk (own γ2 (Excl ())) ★
    own γ3 (Excl ()) ★ (∃ q: Qp, own γm (◯ {[ p := (q, DecAgree (γx, γ1, γ3, γ4)) ]})) ★
    (∃ hd, ev γs hd #p) ★ (∀ x y,  own γx ((1 / 2)%Qp, DecAgree x) -★ ■ Q x y -★ Φ y)
    ⊢ WP loop f #p #s lk {{ Φ }}.
  Proof.
    iIntros (HN Hf) "(#Hh & #? & #? & Ho3 & Hγs & Hev & HΦ)".
    iLöb as "IH". wp_rec. repeat wp_let.
    iDestruct "Hγs" as (q) "Hγs".
    wp_bind (! _)%E. iInv N as ">[Hinv ?]" "Hclose". 
    iDestruct "Hinv" as (xs hd) "[Hs [Hxs HRs]]".
    iDestruct "HRs" as (m) "[Hom HRs]".
    iDestruct "Hev" as (hdp ?) "Hev".
    rewrite /ev. destruct (m !! hdp) eqn:Heqn.
    - iDestruct (big_sepM_delete _ m with "HRs") as "[Hp Hrs]"=>//.
      iDestruct "Hp" as (?) "[% [Hpr ?]]"; subst.
      iDestruct "Hpr" as (γx' γ1' γ3' γ4' p' q') "(% & Hp' & Hp)".
      subst. iDestruct (in_m γs with "[Hom Hev]") as "(Hom & Hev & %)"=>//; first iFrame; eauto.
      inversion H0. subst.
      iDestruct (evmap_frag_agree_split with "[Hγs Hp']") as "==>[Hγs2 [Hγs %]]"; first iFrame.
      inversion H1. subst.
      iDestruct "Hp" as "[Hp | [Hp | [ Hp | Hp]]]".
      + iDestruct "Hp" as (?) "(_ & _ & Ho3')".
        iExFalso. iCombine "Ho3" "Ho3'" as "Ho3".
        by iDestruct (own_valid with "Ho3") as "%".
      + iDestruct "Hp" as (x) "(Hp & Hx & Ho1 & Ho4)".
        wp_load.
        iVs ("Hclose" with "[-Hγs2 Ho3 HΦ Hev]"). (* Hev here should be a duplicated one *)
        { iNext. iFrame. iExists xs, hd. iFrame. iExists m. iFrame.
          iDestruct (big_sepM_delete _ m with "[-]") as "?"=>//.
          iFrame. iExists #p'. iSplitR; first auto. iExists γx, γ1, γ3, γ4, p', q.
          iSplitR; first auto. iFrame.
          iRight. iLeft. iExists x.
          iFrame. } 
        iVsIntro. wp_match.
        (* now, just reason like a server *)
        wp_bind (try_acquire _). iApply try_acquire_spec.
        iFrame "#". iSplit.
        { (* acquired the lock *)
          iIntros "Hlocked Ho2".
          wp_if. wp_bind ((iter _) _). wp_bind (! _)%E.
          iInv N as ">[H Hm]" "Hclose".
          iDestruct "H" as (xs' hd') "[Hs [Hxs HRs]]".
          wp_load. iDestruct (dup_is_list' with "[Hxs]") as "==>[Hxs1 Hxs2]"; first by iFrame.
          iVs ("Hclose" with "[Hs Hxs1 HRs Hm]").
          { iNext. iFrame. iExists xs', hd'. by iFrame. }
          iVsIntro. iApply loop_iter_list_spec=>//.
          iFrame "#". iFrame. iIntros "Ho2".
          wp_seq. wp_bind (release _). iApply release_spec.
          iFrame "~ Hlocked Ho2". wp_seq.
          iAssert ((∃ q0 : Qp, own γm (◯ {[p' := (q0, DecAgree (γx, γ1, γ3, γ4))]})))%I
                  with "[Hγs2]" as "Hγs"; eauto.
          iAssert (∃ (hd0 : loc) (q0 : Qp), own γs (◯ {[hd0 := (q0, DecAgree #p')]}))%I
                  with "[Hev]" as "Hev"; eauto.
          by iApply ("IH" with "Ho3 Hγs Hev"). }
        {  wp_if.
           iAssert (∃ q0 : Qp, own γm (◯ {[p' := (q0, DecAgree (γx, γ1, γ3, γ4))]}))%I
                    with "[Hγs2]" as "Hp'"; eauto.
           iAssert (∃ (hd0 : loc) (q0 : Qp), own γs (◯ {[hd0 := (q0, DecAgree #p')]}))%I
                   with "[Hev]" as "Hev"; eauto.
            iApply ("IH" with "Ho3 Hp' Hev")=>//. }
      + iDestruct "Hp" as (x) "(Hp & Hx & Ho2 & Ho4)".
        wp_load.
        iVs ("Hclose" with "[-Hγs Ho3 HΦ Hev]").
        { iNext. iFrame. iExists xs, hd. iFrame. iExists m. iFrame.
          iDestruct (big_sepM_delete _ m with "[-]") as "?"=>//.
          iFrame. iExists #p'. iSplitR; auto. iExists γx, γ1, γ3, γ4, p', q'.
          iSplitR; first auto. iFrame. iFrame.
          iRight. iRight. iLeft. iExists x. iFrame.
        }
        iVsIntro. wp_match.
        (* now, just reason like a server *)
        wp_bind (try_acquire _). iApply try_acquire_spec.
        iFrame "#". iSplit.
        { (* acquired the lock *)
          iIntros "Hlocked Ho2".
          wp_if. wp_bind ((iter _) _). wp_bind (! _)%E.
          iInv N as ">[H Hm]" "Hclose".
          iDestruct "H" as (xs' hd') "[Hs [Hxs HRs]]".
          wp_load. iDestruct (dup_is_list' with "[Hxs]") as "==>[Hxs1 Hxs2]"; first by iFrame.
          iVs ("Hclose" with "[Hs Hxs1 HRs Hm]").
          { iNext. iFrame. iExists xs', hd'. by iFrame. }
          iVsIntro. iApply loop_iter_list_spec=>//.
          iFrame "#". iFrame. iIntros "Ho2".
          wp_seq. wp_bind (release _). iApply release_spec.
          iFrame "~ Hlocked Ho2". wp_seq.
          iAssert ((∃ q0 : Qp,
                      own γm (◯ {[p' := (q0, DecAgree (γx, γ1, γ3, γ4))]})))%I with "[Hγs]" as "Hγs".
          { eauto. }
          iAssert (∃ (hd0 : loc) (q0 : Qp), own γs (◯ {[hd0 := (q0, DecAgree #p')]}))%I with "[Hev]" as "Hev".
          { eauto. }
            by iApply ("IH" with "Ho3 Hγs Hev"). }
        {  wp_if.
           iAssert ((∃ q0 : Qp,
                       own γm (◯ {[p' := (q0, DecAgree (γx, γ1, γ3, γ4))]})))%I with "[Hγs]" as "Hp'".
           { eauto. }
           iAssert (∃ (hd0 : loc) (q0 : Qp), own γs (◯ {[hd0 := (q0, DecAgree #p')]}))%I with "[Hev]" as "Hev".
          { eauto. }
            iApply ("IH" with "Ho3 Hp' Hev")=>//. }
      + iDestruct "Hp" as (x y) "(Hp & Hx & % & Ho1 & Ho4)".
          wp_load. 
          iVs ("Hclose" with "[-Hγs Ho4 HΦ Hx]").
          { iNext. iFrame. iExists xs, hd. iFrame. iExists m. iFrame.
            iDestruct (big_sepM_delete _ m with "[-]") as "?"=>//.
            iFrame. iExists #p'. iSplitR; auto. iExists γx, γ1, γ3, γ4, p', q'.
            iSplitR; first auto. iFrame. iFrame.
            iLeft. iExists y. iFrame. }            
          iVsIntro. wp_match. iApply ("HΦ" with "[-]").
          iFrame. done.
    - iExFalso.
      iCombine "Hom" "Hev" as "Hauth".
      iDestruct (own_valid γs (● m ⋅ ◯ {[hdp := (H, DecAgree #p)]}) with "[Hauth]") as %Hvalid=>//.
      iPureIntro.
      apply auth_valid_discrete_2 in Hvalid as [[af Compose%leibniz_equiv_iff] Valid].
      eapply (map_agree_none _ _ m)=>//.
  Qed.

  Lemma flat_spec (f: val):
    heapN ⊥ N → (∀ x:val, True ⊢ WP f x {{ v, ■ Q x v }}) →
    heap_ctx ⊢ WP flat f #() {{ f', □ (∀ x: val, WP f' x {{ v, ■ Q x v }}) }}.
  Proof.
    iIntros (HN Hf) "#Hh".
    iVs (own_alloc (Excl ())) as (γ2) "Ho2"; first done.
    iVs (own_alloc (● (∅: tokmR) ⋅ ◯ ∅)) as (γm) "[Hm _]"; first by rewrite -auth_both_op.
    iAssert (srv_tokm_inv γm) with "[Hm]" as "Hm"; first eauto.
    { iExists ∅. iFrame. by rewrite big_sepM_empty. }
    wp_seq. wp_bind (newlock _).
    iApply newlock_spec=>//.
    iFrame "Hh Ho2". iIntros (lk γlk) "#Hlk".
    wp_let. wp_bind (new_stack _).
    iApply (new_stack_spec' _ (p_inv γm γ2))=>//.
    iFrame "Hh Hm". iIntros (γ s) "#Hss".
    wp_let. iVsIntro. iAlways.
    iIntros (x). wp_let.
    wp_bind ((install _) _).
    iApply install_spec=>//.
    iFrame "Hh Hss". iIntros (p γx γ1 γ3 γ4) "Hp3 Hpx Hx Hev".
    wp_let. iApply loop_spec=>//.
    iFrame "Hh Hss Hlk". iFrame.
    iSplitL "Hpx"; first eauto.
    iIntros (? ?) "Hox %".
    destruct (decide (x = a)) as [->|Hneq]; first done.
    { iExFalso. iCombine "Hx" "Hox" as "Hx".
      iDestruct (own_valid with "Hx") as "%".
      rewrite pair_op in H0. destruct H0 as [_ ?]. simpl in H0.
      rewrite dec_agree_ne in H0=>//. }
  Qed.
End proof.
