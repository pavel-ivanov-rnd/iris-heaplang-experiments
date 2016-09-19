From iris.program_logic Require Export auth weakestpre.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import frac excl dec_agree upred_big_op gset gmap.
From iris.tests Require Import atomic treiber_stack.
From flatcomb Require Import misc.

Definition doOp : val :=
  λ: "f" "p",
     match: !"p" with
       InjL "x" => "p" <- InjR ("f" "x")
     | InjR "_" => #()
     end.

Definition loop : val :=
  rec: "loop" "p" "f" "s" "lk" :=
    match: !"p" with
      InjL "_" =>
        if: CAS "lk" #false #true
          then iter (doOp "f") "s"
          else "loop" "p" "f" "s" "lk"
    | InjR "r" => "r"
    end.

(* Naive implementation *)
Definition install : val :=
  λ: "x" "s",
     let: "p" := ref (InjL "x") in
     push "s" "p";;
     "p".

Definition flat : val :=
  λ: "f",
     let: "lk" := ref (#false) in
     let: "s" := new_stack #() in
     λ: "x",
        let: "p" := install "x" "s" in
        loop "p" "f" "s" "lk".

Global Opaque doOp install loop flat.

Definition hdset := gset loc.
Definition gnmap := gmap loc (dec_agree (gname * gname * gname * gname * gname)).

Definition srvR := prodR fracR (dec_agreeR val).
Definition hdsetR := gset_disjUR loc.
Definition gnmapR := gmapUR loc (dec_agreeR (gname * gname * gname * gname * gname)).

Class srvG Σ :=
  SrvG {
      srv_tokG :> inG Σ srvR;
      hd_G :> inG Σ (authR hdsetR);
      gn_G :> inG Σ (authR gnmapR)
    }.

Definition srvΣ : gFunctors :=
  #[ GFunctor (constRF srvR);
     GFunctor (constRF (authR hdsetR));
     GFunctor (constRF (authR gnmapR))
   ].

Instance subG_srvΣ {Σ} : subG srvΣ Σ → srvG Σ.
Proof. intros [?%subG_inG [?subG_inG [?subG_inG _]%subG_inv]%subG_inv]%subG_inv. split; apply _. Qed.

Section proof.
  Context `{!heapG Σ, !lockG Σ, !srvG Σ} (N : namespace).

  Definition p_inv
             (γx γ1 γ2 γ3 γ4: gname) (p: loc)
             (Q: val → val → Prop): iProp Σ :=
    ((∃ (y: val), p ↦ InjRV y ★ own γ1 (Excl ()) ★ own γ3 (Excl ())) ∨
     (∃ (x: val), p ↦ InjLV x ★ own γx ((1/2)%Qp, DecAgree x) ★ own γ1 (Excl ()) ★ own γ4 (Excl ())) ∨
     (∃ (x: val), p ↦ InjLV x ★ own γx ((1/4)%Qp, DecAgree x) ★ own γ2 (Excl ()) ★ own γ4 (Excl ())) ∨
     (∃ (x y: val), p ↦ InjRV y ★ own γx ((1/2)%Qp, DecAgree x) ★ ■ Q x y ★ own γ1 (Excl ()) ★ own γ4 (Excl ())))%I.

  Definition p_inv' (γs: dec_agree (gname * gname * gname * gname * gname)) p Q :=
    match γs with
      | DecAgreeBot => False%I
      | DecAgree (γx, γ1, γ2, γ3, γ4) => p_inv γx γ1 γ2 γ3 γ4 p Q
    end.

  Definition srv_inv (γhd γgn: gname) (s: loc) (Q: val → val → Prop) : iProp Σ :=
    (∃ (hds: hdset) (gnm: gnmap),
       own γhd (● GSet hds) ★ own γgn (● gnm) ★
       (∃ xs: list loc, is_stack s (map (fun x => # (LitLoc x)) xs) ★
                        [★ list] k ↦ x ∈ xs, ■ (x ∈ dom (gset loc) gnm)) ★
       ([★ set] hd ∈ hds, ∃ xs, is_list hd (map (fun x => # (LitLoc x)) xs) ★
                                [★ list] k ↦ x ∈ xs, ■ (x ∈ dom (gset loc) gnm)) ★
       ([★ map] p ↦ γs ∈ gnm, p_inv' γs p Q)
    )%I.

  Instance p_inv_timeless γx γ1 γ2 γ3 γ4 p Q: TimelessP (p_inv γx γ1 γ2 γ3 γ4 p Q).  
  Proof. apply _. Qed.

  Instance p_inv'_timeless γs p Q: TimelessP (p_inv' γs p Q).
  Proof.
    rewrite /p_inv'. destruct γs as [γs|].
    - repeat (destruct γs as [γs ?]). apply _.
    - apply _.
  Qed.

  Instance srv_inv_timeless γhd γgn s Q: TimelessP (srv_inv γhd γgn s Q).
  Proof. apply _. Qed.

  Lemma push_spec
        (Φ: val → iProp Σ) (Q: val → val → Prop)
        (p: loc) (γx γ1 γ2 γ3 γ4: gname)
        (γhd γgn: gname) (s: loc) (x: val) :
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_inv γhd γgn s Q) ★ own γx ((1/2)%Qp, DecAgree x) ★
    p ↦ InjLV x ★ own γ1 (Excl ()) ★ own γ4 (Excl ()) ★ (True -★ Φ #())
    ⊢ WP push #s #p {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #Hsrv & Hp & Hx & Ho1 & Ho4 & HΦ)".    
    iDestruct (push_atomic_spec N s #p with "Hh") as "Hpush"=>//.
    rewrite /push_triple /atomic_triple.
    iSpecialize ("Hpush" $! (p ↦ InjLV x ★ own γ1 (Excl ()) ★ own γ4 (Excl ()) ★
                             own γx ((1/2)%Qp, DecAgree x))%I
                            (fun _ ret => ret = #())%I with "[]").
    - iIntros "!#". iIntros "(Hp & Hx & Ho1 & Ho4)".
      (* open the invariant *)
      iInv N as (hds gnm) ">(Hohd & Hogn & Hxs & Hhd & Hps)" "Hclose".
      iDestruct "Hxs" as (xs) "(Hs & Hgn)".
      (* mask magic *)
      iApply pvs_intro'.
      { apply ndisj_subseteq_difference; auto. }
      iIntros "Hvs".
      iExists (map (λ x : loc, #x) xs).
      iFrame "Hs". iSplit.
      + (* provide a way to rollback *)
        iIntros "Hl'".
        iVs "Hvs". iVs ("Hclose" with "[-Hp Hx Ho1 Ho4]"); last by iFrame.
        iNext. rewrite /srv_inv. iExists hds, gnm.
        iFrame. iExists xs. by iFrame.
      + (* provide a way to commit *)
        iIntros (?) "[% Hs]". subst.
        iVs "Hvs". iVs ("Hclose" with "[-]"); last done.
        iNext. rewrite /srv_inv. iExists hds, (gnm ∪ {[ p := DecAgree (γx, γ1, γ2, γ3, γ4) ]}).
        iFrame.
        iClear "Hogn".
        iAssert (own γgn (● (gnm ∪ {[p := DecAgree (γx, γ1, γ2, γ3, γ4)]})) ★
                 own γgn (◯ {[ p := DecAgree (γx, γ1, γ2, γ3, γ4) ]}))%I as "[Hogn' Hfrag]".
        { admit. }
        iFrame. iSplitL "Hs Hgn".
        { iExists (p::xs).
          iFrame. admit. }
        iSplitL "Hhd".
        { admit. }
        iAssert (p_inv' (DecAgree (γx, γ1, γ2, γ3, γ4)) p Q)  with "[Hp Hx Ho1 Ho4]" as "Hinvp".
        { rewrite /p_inv' /p_inv. iRight. iLeft. iExists x. by iFrame. }
        admit.
    - iApply wp_wand_r. iSplitR "HΦ".
      + iApply "Hpush". by iFrame.
      + iIntros (?) "H". iDestruct "H" as (?) "%". subst. by iApply "HΦ".
  Admitted.

  Lemma install_spec
        (Φ: val → iProp Σ) (Q: val → val → Prop)
        (x: val) (γhd γgn: gname) (s: loc):
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_inv γhd γgn s Q) ★
    (∀ (p: loc) (γx γ1 γ2 γ3 γ4: gname),
       own γ2 (Excl ()) -★ own γ3 (Excl ()) -★ own γgn (◯ {[ p := DecAgree (γx, γ1, γ2, γ3, γ4) ]}) -★
       own γx ((1/2)%Qp, DecAgree x) -★ Φ #p)
    ⊢ WP install x #s {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #Hsrv & HΦ)".
    wp_seq. wp_let. wp_alloc p as "Hl".
    iVs (own_alloc (Excl ())) as (γ1) "Ho1"; first done.
    iVs (own_alloc (Excl ())) as (γ2) "Ho2"; first done.
    iVs (own_alloc (Excl ())) as (γ3) "Ho3"; first done.
    iVs (own_alloc (Excl ())) as (γ4) "Ho4"; first done.
    iVs (own_alloc (1%Qp, DecAgree x)) as (γx) "Hx"; first done.
    iDestruct (own_update with "Hx") as "==>[Hx1 Hx2]".
    { by apply pair_l_frac_op_1'. }
    wp_let. wp_bind ((push _) _).
    iApply push_spec=>//.
    iFrame "Hh Hsrv Hx1 Hl Ho1 Ho4".
    iIntros "_". wp_seq. iVsIntro.
    iSpecialize ("HΦ" $! p γx γ1 γ2 γ3 γ4).
    iAssert (own γgn (◯ {[p := DecAgree (γx, γ1, γ2, γ3, γ4)]})) as "Hfrag".
    { admit. }
    iApply ("HΦ" with "Ho2 Ho3 Hfrag Hx2").
  Admitted.
    
  Lemma mk_srv_spec (f: val) Q:
    heapN ⊥ N →
    heap_ctx ★ □ (∀ x:val, WP f x {{ v, ■ Q x v }})
    ⊢ WP mk_srv f {{ f', □ (∀ x:val, WP f' x {{ v, ■ Q x v }})}}.
  Proof.
    iIntros (HN) "[#Hh #Hf]".
    wp_let. wp_alloc p as "Hp".
    iVs (own_alloc (Excl ())) as (γ1) "Ho1"; first done.
    iVs (own_alloc (Excl ())) as (γ2) "Ho2"; first done.
    iVs (own_alloc (Excl ())) as (γ3) "Ho3"; first done.
    iVs (own_alloc (Excl ())) as (γ4) "Ho4"; first done.
    iVs (own_alloc (1%Qp, DecAgree #0)) as (γx) "Hx"; first done.
    iVs (inv_alloc N _ (srv_inv γx γ1 γ2 γ3 γ4 p Q) with "[Hp Ho1 Ho3]") as "#?".
    { iNext. rewrite /srv_inv. iLeft. iExists #0. by iFrame. }
    wp_let. wp_bind (newlock _).
    iApply newlock_spec=>//. iFrame "Hh".
    iAssert (∃ x, own γx (1%Qp, DecAgree x) ★ own γ4 (Excl ()))%I with "[Ho4 Hx]" as "Hinv".
    { iExists #0. by iFrame. }
    iFrame "Hinv". iIntros (lk γlk) "#Hlk".
    wp_let. wp_apply wp_fork.
    iSplitR "Ho2".
    - (* client closure *)
      iVsIntro. wp_seq. iVsIntro.
      iAlways. iIntros (x).
      wp_let. wp_bind (acquire _). iApply acquire_spec.
      iFrame "Hlk". iIntros "Hlked Ho".
      iDestruct "Ho" as (x') "[Hx Ho4]".
      wp_seq. wp_bind (_ <- _)%E.
      iInv N as ">Hinv" "Hclose".
      iDestruct "Hinv" as "[Hinv|[Hinv|[Hinv|Hinv]]]".
      + iDestruct "Hinv" as (?) "(Hp & Ho1 & Ho3)".
        wp_store. iAssert (|=r=> own γx (1%Qp, DecAgree x))%I with "[Hx]" as "==>Hx".
        { iDestruct (own_update with "Hx") as "Hx"; last by iAssumption.
          apply cmra_update_exclusive. done. }
        iAssert (|=r=> own γx (((1/2)%Qp, DecAgree x) ⋅ ((1/2)%Qp, DecAgree x)))%I with "[Hx]" as "==>[Hx1 Hx2]".
        { iDestruct (own_update with "Hx") as "Hx"; last by iAssumption.
          by apply pair_l_frac_op_1'. }
        iVs ("Hclose" with "[Hp Hx1 Ho1 Ho4]").
        { iNext. iRight. iLeft. iExists x. by iFrame. }
        iVsIntro. wp_seq.
        wp_bind (wait _).
        iApply (wait_spec with "[Hx2 Ho3 Hlked]"); first by done.
        iFrame "Hh". iFrame "#". iFrame.
        iIntros (y) "Ho4 Hx %".
        wp_let. wp_bind (release _).
        iApply release_spec. iFrame "Hlk Hlked".
        iSplitL.
        * iExists x. by iFrame.
        * wp_seq. done.
      + admit.
      + admit.
      + admit.
    - (* server side *)
      iLöb as "IH".
      wp_rec. wp_let. wp_bind (! _)%E.
      iInv N as ">[Hinv|[Hinv|[Hinv|Hinv]]]" "Hclose".
      + admit.
      + iDestruct "Hinv" as (x) "(Hp & Hx & Ho1 & Ho4)".
        iAssert (|=r=> own γx (((1 / 4)%Qp, DecAgree x) ⋅ ((1 / 4)%Qp, DecAgree x)))%I with "[Hx]" as "==>[Hx1 Hx2]".
        { iDestruct (own_update with "Hx") as "Hx"; last by iAssumption.
          replace ((1 / 2)%Qp) with (1/4 + 1/4)%Qp; last by apply Qp_div_S.
          by apply pair_l_frac_op'. }
        wp_load.
        iVs ("Hclose" with "[Hp Hx1 Ho2 Ho4]").
        { iNext. iRight. iRight. iLeft. iExists x. by iFrame. }
        iVsIntro. wp_match.
        wp_bind (f x).
        iApply wp_wand_r. iSplitR; first by iApply "Hf".
        iIntros (y) "%".
        wp_value. iVsIntro. wp_bind (_ <- _)%E.
        iInv N as ">[Hinv|[Hinv|[Hinv|Hinv]]]" "Hclose".
        * admit.
        * admit.
        * iDestruct "Hinv" as (x') "(Hp & Hx' & Ho2 & Ho4)".
          destruct (decide (x = x')) as [->|Hneq]; last by admit.
          wp_store. iCombine "Hx2" "Hx'" as "Hx".
          iDestruct (own_update with "Hx") as "==>Hx"; first by apply pair_l_frac_op.
          rewrite Qp_div_S.
          iVs ("Hclose" with "[Hp Hx Ho1 Ho4]").
          { iNext. rewrite /srv_inv. iRight. iRight. iRight.
            iExists x', y. by iFrame. }
          iVsIntro. wp_seq. iApply ("IH" with "Ho2").
        * admit.
      + admit.
      + admit.
  Admitted.
