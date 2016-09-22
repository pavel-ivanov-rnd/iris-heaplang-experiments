From iris.program_logic Require Export auth weakestpre.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import upred frac excl dec_agree upred_big_op gset gmap.
From iris.tests Require Import atomic treiber_stack.
From flatcomb Require Import misc.

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
        if: CAS "lk" #false #true
          then iter (doOp f) "s"
          else "loop" "p" "s" "lk"
    | InjR "r" => "r"
    end.

(* Naive implementation *)
Definition install : val :=
  λ: "x" "s",
     let: "p" := ref (InjL "x") in
     push "s" "p";;
     "p".

Definition flat (f: val) : val :=
  λ: "f",
     let: "lk" := ref (#false) in
     let: "s" := new_stack #() in
     λ: "x",
        let: "p" := install "x" "s" in
        loop f "p" "s" "lk".

Global Opaque doOp install loop flat.

Definition srvR := prodR fracR (dec_agreeR val).
Definition tokR := evmapR loc (gname * gname * gname * gname).
Class srvG Σ := SrvG {
  srv_G :> inG Σ srvR;
  tok_G :> inG Σ (authR tokR);
}.

Definition srvΣ : gFunctors :=
  #[ GFunctor (constRF srvR);
     GFunctor (constRF (authR tokR))
   ].

Instance subG_srvΣ {Σ} : subG srvΣ Σ → srvG Σ.
Proof. intros [?%subG_inG [?%subG_inG _]%subG_inv]%subG_inv. split; apply _. Qed.

Section proof.
  Context `{!heapG Σ, !lockG Σ, !evidenceG loc val Σ, !srvG Σ} (N : namespace).

  Definition p_inv
             (γm γx γ1 γ2 γ3 γ4: gname)
             (Q: val → val → Prop)
             (v: val): iProp Σ :=
    (∃ (p : loc) (q: Qp), v = #p ★ own γm (◯ ({[ p := (q, DecAgree (γx, γ1, γ3, γ4)) ]} : tokR)) ★
     ((∃ (y: val), p ↦ InjRV y ★ own γ1 (Excl ()) ★ own γ3 (Excl ())) ∨
      (∃ (x: val), p ↦ InjLV x ★ own γx ((1/2)%Qp, DecAgree x) ★ own γ1 (Excl ()) ★ own γ4 (Excl ())) ∨
      (∃ (x: val), p ↦ InjLV x ★ own γx ((1/4)%Qp, DecAgree x) ★ own γ2 (Excl ()) ★ own γ4 (Excl ())) ∨
      (∃ (x y: val), p ↦ InjRV y ★ own γx ((1/2)%Qp, DecAgree x) ★ ■ Q x y ★ own γ1 (Excl ()) ★ own γ4 (Excl ()))))%I.

  Definition p_inv_R γm γ2 Q v : iProp Σ :=
    (∃ γx γ1 γ3 γ4: gname, p_inv γm γx γ1 γ2 γ3 γ4 Q v)%I.

  Definition srv_stack_inv (γ γm γ2: gname) (s: loc) (Q: val → val → Prop) : iProp Σ :=
    (∃ xs, is_stack' (p_inv_R γm γ2 Q) xs s γ)%I.

  Definition srv_m_inv γm := (∃ m, own γm (● m))%I.

  Lemma install_push_spec
        (Φ: val → iProp Σ) (Q: val → val → Prop)
        (p: loc) (γ γm γx γ1 γ2 γ3 γ4: gname)
        (s: loc) (x: val) :
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_stack_inv γ γm γ2 s Q) ★ own γx ((1/2)%Qp, DecAgree x) ★
    own γm (◯ ({[ p := ((1 / 2)%Qp, DecAgree (γx, γ1, γ3, γ4)) ]})) ★
    p ↦ InjLV x ★ own γ1 (Excl ()) ★ own γ4 (Excl ()) ★ (True -★ Φ #())
    ⊢ WP push #s #p {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & Hx & Hpm & Hp & Ho1 & Ho2 & HΦ)".
    rewrite /srv_stack_inv.
    iDestruct (push_spec N (p_inv_R γm γ2 Q) with "[-HΦ]") as "Hpush"=>//.
    - iFrame "Hh". iSplitL "Hx Hp Hpm Ho1 Ho2"; last eauto.
      iExists γx, γ1, γ3, γ4. iExists p, (1/2)%Qp. iSplit=>//. iFrame "Hpm".
      iRight. iLeft.
      iExists x. iFrame.
    - iApply wp_wand_r.
      iSplitL "Hpush"; first done.
      iIntros (?). iIntros "%".
      inversion H. by iApply "HΦ".
  Qed.

  Lemma install_spec
        (Φ: val → iProp Σ) (Q: val → val → Prop)
        (x: val) (γ2 γm γ: gname) (s: loc):
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_stack_inv γ γm γ2 s Q) ★ inv N (srv_m_inv γm) ★ 
    (∀ (p: loc) (γx γ1 γ2 γ3 γ4: gname),
       own γ3 (Excl ()) -★ own γm (◯ {[ p := ((1 / 2)%Qp, DecAgree (γx, γ1, γ3, γ4)) ]}) -★
       own γx ((1/2)%Qp, DecAgree x) -★ Φ #p)
    ⊢ WP install x #s {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & #? & HΦ)".
    wp_seq. wp_let. wp_alloc p as "Hl".
    iVs (own_alloc (Excl ())) as (γ1) "Ho1"; first done.
    iVs (own_alloc (Excl ())) as (γ3) "Ho3"; first done.
    iVs (own_alloc (Excl ())) as (γ4) "Ho4"; first done.
    iVs (own_alloc (1%Qp, DecAgree x)) as (γx) "Hx"; first done.
    iDestruct (own_update with "Hx") as "==>[Hx1 Hx2]"; first by apply pair_l_frac_op_1'.
    wp_let. wp_bind ((push _) _).
    iApply install_push_spec=>//.
    iFrame "#".
    iAssert (own γm (◯ {[p := ((1/2)%Qp, DecAgree (γx, γ1, γ3, γ4))]} ⋅
                     ◯ {[p := ((1/2)%Qp, DecAgree (γx, γ1, γ3, γ4))]})) as "[Hfrag1 Hfrag2]".
    { admit. }
    iFrame "Hx1 Hfrag1 Hl Ho1 Ho4". iIntros "_". wp_seq. iVsIntro.
    iSpecialize ("HΦ" $! p γx γ1 γ2 γ3 γ4 with "[-Hx2 Hfrag2]")=>//.
    iApply ("HΦ" with "Hfrag2 Hx2").
  Admitted.

  Lemma loop_iter_list_spec Φ (f: val) (s hd: loc) Q (γ γm γ2: gname) xs:
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_stack_inv γ γm γ2 s Q) ★ □ (∀ x:val, WP f x {{ v, ■ Q x v }})%I ★ own γ2 (Excl ()) ★
    is_list' γ hd xs ★ (own γ2 (Excl ()) -★ Φ #())
    ⊢ WP iter' #hd (doOp f) {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & #Hf & Ho2 & Hlist' & HΦ)".
    rewrite /doOp.
    iApply pvs_wp.
    iDestruct (dup_is_list' with "[Hlist']") as "==>[Hl1 Hl2]"; first by iFrame.
    iDestruct (dup_is_list' with "[Hl2]") as "==>[Hl2 Hl3]"; first by iFrame.
    iDestruct (iter'_spec _ (p_inv_R γm γ2 Q) _ γ s (is_list' γ hd xs ★ own γ2 (Excl ()))%I xs hd (λ: "p",
      match: ! "p" with InjL "x" => "p" <- SOME (f "x") | InjR "_" => #() end)%V (λ: "p",
      match: ! "p" with InjL "x" => "p" <- SOME (f "x") | InjR "_" => #() end) with "[-Hl1]") as "Hiter'"=>//.
    - rewrite /f_spec.
      iIntros (Φ' x _ Hin) "(#Hh & #? & (Hls & Ho2) & HΦ')".
      wp_let. wp_bind (! _)%E. iInv N as (xs') ">Hs" "Hclose".
      iDestruct "Hs" as (hd') "[Hhd [Hxs HRs]]".
      (* now I know x conforms to p_inv_R *)
      admit.
    - apply to_of_val.
    - iFrame "#". iFrame "Hl2 Hl3 Ho2".
      iIntros "[_ H]". by iApply "HΦ".
    - done.
  Admitted.

  Lemma loop_iter_spec Φ (f: val) (s: loc) Q (γhd γgn γ2: gname):
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_inv γhd γgn γ2 s Q) ★ □ (∀ x:val, WP f x {{ v, ■ Q x v }})%I ★
    own γ2 (Excl ()) ★ (own γ2 (Excl ()) -★ Φ #())
    ⊢ WP iter (doOp f) #s {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #? & #? & ? & ?)".
    iAssert (∃ (hd: loc) xs, is_list hd xs ★ own γhd (◯ {[ hd ]}) ★ s ↦ #hd)%I as "H".
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
    heap_ctx ★ □ (∀ x: val, WP f x {{ v, ■ Q x v }})%I
    ⊢ WP flat f {{ f', □ (∀ x: val, WP f' x {{ v, ■ Q x v }}) }}.
  Proof.
    iIntros (HN) "(#Hh & #?)".
    wp_seq. wp_alloc lk as "Hl".
    iVs (own_alloc (Excl ())) as (γ2) "Ho2"; first done.
    iVs (own_alloc (Excl ())) as (γlk) "Hγlk"; first done.
    iVs (own_alloc (● (∅: hdsetR) ⋅ ◯ ∅)) as (γhd) "[Hgs Hgs']"; first admit.
    iVs (own_alloc (● ∅ ⋅ ◯ ∅)) as (γgn) "[Hgs Hgs']"; first admit.
    iVs (own_alloc ()) as (γlk) "Hγlk"; first done.
    iVs (inv_alloc N _ (lock_inv γlk lk (own γ2 (Excl ()))) with "[-]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    wp_let. wp_bind (new_stack _).
    iApply new_stack_spec=>//.
    iFrame "Hh". iIntros (s) "Hs".
    iVs (inv_alloc N _ (srv_inv γhd γgn γ2 s Q) with "") as "#?".
    wp_let.
    iVsIntro. iPureIntro
  Qed.
End proof.
