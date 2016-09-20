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
Definition gnmap := gmap loc (dec_agree (gname * gname * gname * gname)).

Definition srvR := prodR fracR (dec_agreeR val).
Definition hdsetR := gset_disjUR loc.
Definition gnmapR := gmapUR loc (dec_agreeR (gname * gname * gname * gname)).

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

  Definition p_inv' γ2 (γs: dec_agree (gname * gname * gname * gname)) p Q :=
    match γs with
      | DecAgreeBot => False%I
      | DecAgree (γx, γ1, γ3, γ4) => p_inv γx γ1 γ2 γ3 γ4 p Q
    end.

  Definition srv_inv (γhd γgn γ2: gname) (s: loc) (Q: val → val → Prop) : iProp Σ :=
    (∃ (hds: hdset) (gnm: gnmap),
       own γhd (● GSet hds) ★ own γgn (● gnm) ★
       (∃ xs: list loc, is_stack s (map (fun x => # (LitLoc x)) xs) ★
                        [★ list] k ↦ x ∈ xs, ■ (x ∈ dom (gset loc) gnm)) ★
       ([★ set] hd ∈ hds, ∃ xs, is_list hd (map (fun x => # (LitLoc x)) xs) ★
                                [★ list] k ↦ x ∈ xs, ■ (x ∈ dom (gset loc) gnm)) ★
       ([★ map] p ↦ γs ∈ gnm, p_inv' γ2 γs p Q)
    )%I.

  Instance p_inv_timeless γx γ1 γ2 γ3 γ4 p Q: TimelessP (p_inv γx γ1 γ2 γ3 γ4 p Q).
  Proof. apply _. Qed.

  Instance p_inv'_timeless γ2 γs p Q: TimelessP (p_inv' γ2 γs p Q).
  Proof.
    rewrite /p_inv'. destruct γs as [γs|].
    - repeat (destruct γs as [γs ?]). apply _.
    - apply _.
  Qed.

  Instance srv_inv_timeless γhd γgn γ2 s Q: TimelessP (srv_inv γhd γgn γ2 s Q).
  Proof. apply _. Qed.

  (* Lemma push_spec *)
  (*       (Φ: val → iProp Σ) (Q: val → val → Prop) *)
  (*       (p: loc) (γx γ1 γ2 γ3 γ4: gname) *)
  (*       (γhd γgn: gname) (s: loc) (x: val) : *)
  (*   heapN ⊥ N → *)
  (*   heap_ctx ★ inv N (srv_inv γhd γgn s Q) ★ own γx ((1/2)%Qp, DecAgree x) ★ *)
  (*   p ↦ InjLV x ★ own γ1 (Excl ()) ★ own γ4 (Excl ()) ★ (True -★ Φ #()) *)
  (*   ⊢ WP push #s #p {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (HN) "(#Hh & #Hsrv & Hp & Hx & Ho1 & Ho4 & HΦ)".     *)
  (*   iDestruct (push_atomic_spec N s #p with "Hh") as "Hpush"=>//. *)
  (*   rewrite /push_triple /atomic_triple. *)
  (*   iSpecialize ("Hpush" $! (p ↦ InjLV x ★ own γ1 (Excl ()) ★ own γ4 (Excl ()) ★ *)
  (*                            own γx ((1/2)%Qp, DecAgree x))%I *)
  (*                           (fun _ ret => ret = #())%I with "[]"). *)
  (*   - iIntros "!#". iIntros "(Hp & Hx & Ho1 & Ho4)". *)
  (*     (* open the invariant *) *)
  (*     iInv N as (hds gnm) ">(Hohd & Hogn & Hxs & Hhd & Hps)" "Hclose". *)
  (*     iDestruct "Hxs" as (xs) "(Hs & Hgn)". *)
  (*     (* mask magic *) *)
  (*     iApply pvs_intro'. *)
  (*     { apply ndisj_subseteq_difference; auto. } *)
  (*     iIntros "Hvs". *)
  (*     iExists (map (λ x : loc, #x) xs). *)
  (*     iFrame "Hs". iSplit. *)
  (*     + (* provide a way to rollback *) *)
  (*       iIntros "Hl'". *)
  (*       iVs "Hvs". iVs ("Hclose" with "[-Hp Hx Ho1 Ho4]"); last by iFrame. *)
  (*       iNext. rewrite /srv_inv. iExists hds, gnm. *)
  (*       iFrame. iExists xs. by iFrame. *)
  (*     + (* provide a way to commit *) *)
  (*       iIntros (?) "[% Hs]". subst. *)
  (*       iVs "Hvs". iVs ("Hclose" with "[-]"); last done. *)
  (*       iNext. rewrite /srv_inv. iExists hds, (gnm ∪ {[ p := DecAgree (γx, γ1, γ2, γ3, γ4) ]}). *)
  (*       iFrame. *)
  (*       iClear "Hogn". *)
  (*       iAssert (own γgn (● (gnm ∪ {[p := DecAgree (γx, γ1, γ2, γ3, γ4)]})) ★ *)
  (*                own γgn (◯ {[ p := DecAgree (γx, γ1, γ2, γ3, γ4) ]}))%I as "[Hogn' Hfrag]". *)
  (*       { admit. } *)
  (*       iFrame. iSplitL "Hs Hgn". *)
  (*       { iExists (p::xs). *)
  (*         iFrame. admit. } *)
  (*       iSplitL "Hhd". *)
  (*       { admit. } *)
  (*       iAssert (p_inv' (DecAgree (γx, γ1, γ2, γ3, γ4)) p Q)  with "[Hp Hx Ho1 Ho4]" as "Hinvp". *)
  (*       { rewrite /p_inv' /p_inv. iRight. iLeft. iExists x. by iFrame. } *)
  (*       admit. *)
  (*   - iApply wp_wand_r. iSplitR "HΦ". *)
  (*     + iApply "Hpush". by iFrame. *)
  (*     + iIntros (?) "H". iDestruct "H" as (?) "%". subst. by iApply "HΦ". *)
  (* Admitted. *)

  (* Lemma install_spec *)
  (*       (Φ: val → iProp Σ) (Q: val → val → Prop) *)
  (*       (x: val) (γhd γgn: gname) (s: loc): *)
  (*   heapN ⊥ N → *)
  (*   heap_ctx ★ inv N (srv_inv γhd γgn s Q) ★ *)
  (*   (∀ (p: loc) (γx γ1 γ2 γ3 γ4: gname), *)
  (*      own γ2 (Excl ()) -★ own γ3 (Excl ()) -★ own γgn (◯ {[ p := DecAgree (γx, γ1, γ2, γ3, γ4) ]}) -★ *)
  (*      own γx ((1/2)%Qp, DecAgree x) -★ Φ #p) *)
  (*   ⊢ WP install x #s {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (HN) "(#Hh & #Hsrv & HΦ)". *)
  (*   wp_seq. wp_let. wp_alloc p as "Hl". *)
  (*   iVs (own_alloc (Excl ())) as (γ1) "Ho1"; first done. *)
  (*   iVs (own_alloc (Excl ())) as (γ2) "Ho2"; first done. *)
  (*   iVs (own_alloc (Excl ())) as (γ3) "Ho3"; first done. *)
  (*   iVs (own_alloc (Excl ())) as (γ4) "Ho4"; first done. *)
  (*   iVs (own_alloc (1%Qp, DecAgree x)) as (γx) "Hx"; first done. *)
  (*   iDestruct (own_update with "Hx") as "==>[Hx1 Hx2]". *)
  (*   { by apply pair_l_frac_op_1'. } *)
  (*   wp_let. wp_bind ((push _) _). *)
  (*   iApply push_spec=>//. *)
  (*   iFrame "Hh Hsrv Hx1 Hl Ho1 Ho4". *)
  (*   iIntros "_". wp_seq. iVsIntro. *)
  (*   iSpecialize ("HΦ" $! p γx γ1 γ2 γ3 γ4). *)
  (*   iAssert (own γgn (◯ {[p := DecAgree (γx, γ1, γ2, γ3, γ4)]})) as "Hfrag". *)
  (*   { admit. } *)
  (*   iApply ("HΦ" with "Ho2 Ho3 Hfrag Hx2"). *)
  (* Admitted. *)

  (* Definition pinv_sub RI γx γ1 γ2 γ3 γ4 p Q := (RI ⊣⊢ ∃ Rf, Rf ★ p_inv γx γ1 γ2 γ3 γ4 p Q)%I. *)

  (* Lemma doOp_spec Φ (f: val) (RI: iProp Σ) γx γ1 γ2 γ3 γ4 p Q `{TimelessP _ RI}: *)
  (*   heapN ⊥ N → pinv_sub RI γx γ1 γ2 γ3 γ4 p Q → *)
  (*   heap_ctx ★ inv N RI ★ own γ2 (Excl ()) ★ *)
  (*   □ (∀ x:val, WP f x {{ v, ■ Q x v }})%I ★ (own γ2 (Excl ()) -★ Φ #()) *)
  (*   ⊢ WP doOp f #p {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (HN Hsub) "(#Hh & #HRI & Ho2 & #Hf & HΦ)". *)
  (*   wp_seq. wp_let. wp_bind (! _)%E. *)
  (*   iInv N as ">H" "Hclose". *)
  (*   iDestruct (Hsub with "H") as (Rf) "[HRf [Hp | [Hp | [Hp | Hp]]]]". *)
  (*   - iDestruct "Hp" as (y) "(Hp & Ho1 & Ho3)". *)
  (*     wp_load. iVs ("Hclose" with "[HRf Hp Ho1 Ho3]"). *)
  (*     { iNext. iApply Hsub. iExists Rf. iFrame "HRf". *)
  (*       iLeft. iExists y. by iFrame. } *)
  (*     iVsIntro. wp_match. by iApply "HΦ". *)
  (*   - iDestruct "Hp" as (x) "(Hp & Hx & Ho1 & Ho4)". *)
  (*     wp_load. *)
  (*     iAssert (|=r=> own γx (((1 / 4)%Qp, DecAgree x) ⋅ ((1 / 4)%Qp, DecAgree x)))%I with "[Hx]" as "==>[Hx1 Hx2]". *)
  (*     { iDestruct (own_update with "Hx") as "Hx"; last by iAssumption. *)
  (*       replace ((1 / 2)%Qp) with (1/4 + 1/4)%Qp; last by apply Qp_div_S. *)
  (*       by apply pair_l_frac_op'. } *)
  (*     iVs ("Hclose" with "[HRf Hp Hx1 Ho2 Ho4]"). *)
  (*     { iNext. iApply Hsub. iExists Rf. iFrame "HRf". *)
  (*       iRight. iRight. iLeft. iExists x. by iFrame. } *)
  (*     iVsIntro. wp_match. *)
  (*     wp_bind (f _). iApply wp_wand_r. *)
  (*     iSplitR; first by iApply "Hf". *)
  (*     iIntros (y) "%". *)
  (*     iInv N as ">H" "Hclose". *)
  (*     iDestruct (Hsub with "H") as (Rf') "[HRf [Hp | [Hp | [Hp | Hp]]]]". *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + iDestruct "Hp" as (x') "(Hp & Hx & Ho2 & Ho4)". *)
  (*       destruct (decide (x = x')) as [->|Hneq]; last by admit. *)
  (*       iCombine "Hx2" "Hx" as "Hx". *)
  (*       iDestruct (own_update with "Hx") as "==>Hx"; first by apply pair_l_frac_op. *)
  (*       rewrite Qp_div_S. *)
  (*       wp_store. iVs ("Hclose" with "[HRf Hp Hx Ho1 Ho4]"). *)
  (*       { iNext. iApply Hsub. iExists Rf'. iFrame "HRf". *)
  (*         iRight. iRight. iRight. iExists x', y. *)
  (*         by iFrame. } *)
  (*       iVsIntro. by iApply "HΦ". *)
  (*     + admit. *)
  (*   - admit. *)
  (*   - admit. *)
  (* Admitted. *)

  Lemma loop_iter_list_spec Φ (f: val) (s hd: loc) Q (γhd γgn γ2: gname) xs:
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_inv γhd γgn γ2 s Q) ★ □ (∀ x:val, WP f x {{ v, ■ Q x v }})%I ★ own γ2 (Excl ()) ★
    is_list hd xs ★ own γhd (◯ GSet {[ hd ]}) ★ (own γ2 (Excl ()) -★ Φ #())
    ⊢ WP doOp f {{ f', WP iter' #hd f' {{ Φ  }} }}.
  Proof.
    iIntros (HN) "(#Hh & #? & #Hf & Hxs & Hhd & Ho2 & HΦ)".
    rewrite /doOp. wp_let.
    iLöb as "IH".
    wp_rec. wp_let. wp_bind (! _)%E.
    destruct xs as [|x xs'].
    - simpl. iDestruct "Hhd" as (q) "Hhd".
      wp_load. wp_match. by iApply "HΦ".
    - simpl. iDestruct "Hhd" as (hd' q) "[[Hhd1 Hhd2] Hhd']".
      wp_load. wp_match. wp_proj. wp_let.
      wp_bind (! _)%E.
      iInv N as (hds gnm) ">(Hohd & Hogn & Hxse & Hhds & Hps)" "Hclose".
      iAssert (∃ (p: loc) γs, x = #p ★ p_inv' γ2 γs p Q)%I as "Hx".
      { admit. }
      iDestruct "Hx" as (p γs) "[% Hp]". subst.
      rewrite /p_inv'. destruct γs as [[[[γx γ1] γ3] γ4]|].
      iDestruct "Hp" as "[Hp | [Hp | [ Hp | Hp]]]"=>//.
      + admit.
      + iDestruct "Hp" as (x) "(Hp & Hx & Ho1 & Ho4)".
        iAssert (|=r=> own γx (((1 / 4)%Qp, DecAgree x) ⋅ ((1 / 4)%Qp, DecAgree x)))%I with "[Hx]" as "==>[Hx1 Hx2]".
        { iDestruct (own_update with "Hx") as "Hx"; last by iAssumption.
          replace ((1 / 2)%Qp) with (1/4 + 1/4)%Qp; last by apply Qp_div_S.
          by apply pair_l_frac_op'. }
        wp_load. iVs ("Hclose" with "[-Ho1 Hx2 Hhd2 HΦ]").
        { iNext. iExists hds, gnm. by iFrame. }
        iVsIntro. wp_match.
        wp_bind (f _). iApply wp_wand_r. iSplitR; first by iApply "Hf".
        iIntros (y) "Q". 
        iInv N as (hds' gnm') ">(Hohd & Hogn & Hxse & Hhds & Hps)" "Hclose".
        iAssert (p_inv' γ2 (DecAgree (γx, γ1, γ3, γ4)) p Q)%I as "Hp".
        { admit. }
        rewrite /p_inv'.
        iDestruct "Hp" as "[Hp | [Hp | [ Hp | Hp]]]".
        * admit.
        * admit.
        * iDestruct "Hp" as (x') "(Hp & Hx' & Ho2 & Ho4)".
          destruct (decide (x = x')) as [->|Hneq]; last by admit.
          iCombine "Hx2" "Hx'" as "Hx".
          iDestruct (own_update with "Hx") as "==>Hx"; first by apply pair_l_frac_op.
          rewrite Qp_div_S.
          wp_store. iVs ("Hclose" with "[-Ho2 HΦ Hhd2]").
          { iNext. iExists hds', gnm'. by iFrame. }
          iVsIntro. wp_seq. wp_proj. rewrite /doOp.
          iAssert (is_list hd' xs') as "Hl".
          { admit. }
          iAssert (∃ (hd'0 : loc) (q0 : Qp),
                     hd ↦{q0} SOMEV (#p, #hd'0) ★ is_list hd'0 xs')%I with "[Hhd2 Hl]" as "He".
          { iExists hd', (q / 2)%Qp. by iFrame. }
          iAssert (own γhd (◯ GSet {[hd]})) as "Hfrag".
          { admit. }
          iSpecialize ("IH" with "Ho2 He Hfrag HΦ").
          admit.
        * admit.
      + admit.
      + admit.
      + by iExFalso.
  Admitted.

  Lemma loop_iter_spec Φ (f: val) (s: loc) Q (γhd γgn γ2: gname):
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_inv γhd γgn γ2 s Q) ★ □ (∀ x:val, WP f x {{ v, ■ Q x v }})%I ★
    own γ2 (Excl ()) ★ (own γ2 (Excl ()) -★ Φ #())
    ⊢ WP iter (doOp f) #s {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & #? & ? & ?)".
    iAssert (∃ (hd: loc) xs, is_list hd xs ★ own γhd (◯ GSet {[ hd ]}) ★ s ↦ #hd)%I as "H".
    { admit. }
    iDestruct "H" as (hd xs) "(? & ? & ?)".
    wp_bind (doOp _).
    iApply wp_wand_r.
    iSplitR "~5".
    - iApply loop_iter_list_spec=>//.
      iFrame "Hh". iFrame. by iFrame "#".
    - iIntros (v) "Hf'".
      wp_let. wp_let. wp_load.
        by iClear "~5".
  Admitted.

  Lemma loop_spec Φ (p s lk: loc) (f: val) Q (γhd γgn γ2 γlk: gname) γs:
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_inv γhd γgn γ2 s Q) ★ inv N (lock_inv γlk lk (own γ2 (Excl ()))) ★
    own γgn (◯ {[ p := γs ]})  ★ □ (∀ x:val, WP f x {{ v, ■ Q x v }})%I ★ (∀ x y, ■ Q x y → Φ y) (* there should be some constraints on x *)
    ⊢ WP loop #p f #s #lk {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & #? & #? & #? & HΦ)".
    iLöb as "IH".
    wp_rec. repeat wp_let.
    (* we should be able to know p is something by open the invariant and using the fragment *)
    (* but for now we will move fast *)
    iAssert (p_inv' γ2 γs p Q) as "Hp".
    { admit. }
    rewrite /p_inv'. destruct γs as [[[[γx γ1] γ3] γ4]|]; last by iExFalso.
    iDestruct "Hp" as "[Hp | [Hp | [ Hp | Hp]]]".
    - (* I should be able to refuse this case *) admit.
    - admit.
    - admit.
    - iDestruct "Hp" as (x y) "(Hp & Hx & % & Ho1 & Ho4)".
      (* there should be some token exchange *)
      wp_load. wp_match.
      by iApply "HΦ".
  Admitted.

  Lemma flat_spec (f: val) Q:
    heapN ⊥ N →
    heap_ctx ★ □ (∀ x:val, WP f x {{ v, ■ Q x v }})%I
    ⊢ WP flat f {{ f', True%I }}.
  Proof.
    iIntros (HN) "(#Hh & #?)".
    wp_seq. wp_alloc lk as "Hl".
    iVs (own_alloc (Excl ())) as (γ2) "Ho2"; first done.
    iVs (own_alloc (Excl ())) as (γlk) "Hγlk"; first done.
    iVs (inv_alloc N _ (lock_inv γlk lk (own γ2 (Excl ()))) with "[-]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    wp_let. wp_bind (new_stack _).
    iApply new_stack_spec=>//.
    iFrame "Hh". iIntros (s) "Hs".
    wp_let.
    done.
  Qed.
  