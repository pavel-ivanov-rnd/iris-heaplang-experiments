From iris.program_logic Require Export auth weakestpre.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import frac excl dec_agree upred_big_op gset gmap.
From iris.tests Require Import treiber_stack.
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

  Instance stack_inv_timeless γx γ1 γ2 γ3 γ4 p Q: TimelessP (srv_inv γx γ1 γ2 γ3 γ4 p Q).
  Proof. apply _. Qed.

  Lemma install_spec (Φ: val → iProp Σ) (Q: val → val → Prop) x γ3 γ4 γx p s:
    heapN ⊥ N →
    heap_ctx ★ inv N (stack_inv s Q) ★
    own γx ((1/2)%Qp, DecAgree x) ★ own γ3 (Excl ()) ★
    (∀ y, own γ4 (Excl ()) -★ own γx (1%Qp, DecAgree x) -★ ■ Q x y-★ Φ y)
    ⊢ WP install #p #s {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #Hsrv & Hx & Ho3 & HΦ)".
    iLöb as "IH".
    wp_rec. wp_bind (! #p)%E.
    iInv N as ">[Hinv|[Hinv|[Hinv|Hinv]]]" "Hclose".
    - iExFalso. iDestruct "Hinv" as (?) "[_ [_ Ho3']]".
      iCombine "Ho3" "Ho3'" as "Ho3".
      by iDestruct (own_valid with "Ho3") as "%".
    - admit.
    - admit.
    - iDestruct "Hinv" as (x' y') "(Hp & Hx' & % & Ho1 & Ho4)".
      destruct (decide (x = x')) as [->|Hneq].
      + wp_load. iVs ("Hclose" with "[Hp Ho1 Ho3]").
        { iNext. rewrite /srv_inv. iLeft. iExists y'. by iFrame. }
        iVsIntro. wp_match.
        iCombine "Hx" "Hx'" as "Hx".
        iDestruct (own_update with "Hx") as "==>Hx"; first by apply pair_l_frac_op.
        rewrite Qp_div_2.
        iApply ("HΦ" with "Ho4 Hx"). done.
      + admit.
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
