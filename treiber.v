From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import auth upred gmap dec_agree upred_big_op.
From iris_atomic Require Import atomic misc.

Definition new_stack: val := λ: <>, ref (ref NONE).

Definition push: val :=
  rec: "push" "s" "x" :=
      let: "hd" := !"s" in
      let: "s'" := ref SOME ("x", "hd") in
      if: CAS "s" "hd" "s'"
        then #()
        else "push" "s" "x".

Definition pop: val :=
  rec: "pop" "s" :=
      let: "hd" := !"s" in
      match: !"hd" with
        SOME "cell" =>
        if: CAS "s" "hd" (Snd "cell")
          then SOME (Fst "cell")
          else "pop" "s"
      | NONE => NONE
      end.

Definition iter: val :=
  rec: "iter" "hd" "f" :=
      match: !"hd" with
        NONE => #()
      | SOME "cell" => "f" (Fst "cell") ;; "iter" (Snd "cell") "f"
      end.

Global Opaque new_stack push pop iter.

Section proof.
  Context `{!heapG Σ} (N: namespace).

  Fixpoint is_list (hd: loc) (xs: list val) : iProp Σ :=
    match xs with
    | [] => (∃ q, hd ↦{ q } NONEV)%I
    | x :: xs => (∃ (hd': loc) q, hd ↦{ q } SOMEV (x, #hd') ★ is_list hd' xs)%I
    end.

  Lemma dup_is_list : ∀ xs hd,
    heap_ctx ★ is_list hd xs ⊢ is_list hd xs ★ is_list hd xs.
  Proof.
    induction xs as [|y xs' IHxs'].
    - iIntros (hd) "(#? & Hs)".
      simpl. iDestruct "Hs" as (q) "[Hhd Hhd']". iSplitL "Hhd"; eauto.
    - iIntros (hd) "(#? & Hs)". simpl.
      iDestruct "Hs" as (hd' q) "([Hhd Hhd'] & Hs')".
      iDestruct (IHxs' with "[Hs']") as "[Hs1 Hs2]"; first by iFrame.
      iSplitL "Hhd Hs1"; iExists hd', (q / 2)%Qp; by iFrame.
  Qed.

  Lemma uniq_is_list:
    ∀ xs ys hd, heap_ctx ★ is_list hd xs ★ is_list hd ys ⊢ xs = ys.
  Proof.
    induction xs as [|x xs' IHxs'].
    - induction ys as [|y ys' IHys'].
      + auto.
      + iIntros (hd) "(#? & Hxs & Hys)".
        simpl. iDestruct "Hys" as (hd' ?) "(Hhd & Hys')".
        iExFalso. iDestruct "Hxs" as (?) "Hhd'".
        iDestruct (heap_mapsto_op_1 with "[Hhd Hhd']") as "[% _]".
        { iSplitL "Hhd"; done. }
        done.
    - induction ys as [|y ys' IHys'].
      + iIntros (hd) "(#? & Hxs & Hys)".
        simpl.
        iExFalso. iDestruct "Hxs" as (? ?) "(Hhd & _)".
        iDestruct "Hys" as (?) "Hhd'".
        iDestruct (heap_mapsto_op_1 with "[Hhd Hhd']") as "[% _]".
        { iSplitL "Hhd"; done. }
        done.
      + iIntros (hd) "(#? & Hxs & Hys)".
        simpl. iDestruct "Hxs" as (? ?) "(Hhd & Hxs')".
        iDestruct "Hys" as (? ?) "(Hhd' & Hys')".
        iDestruct (heap_mapsto_op_1 with "[Hhd Hhd']") as "[% _]".
        { iSplitL "Hhd"; done. }
        inversion H3. (* FIXME: name *)
        subst. iDestruct (IHxs' with "[Hxs' Hys']") as "%"; first by iFrame.
        by subst.
  Qed.

  Definition is_stack (s: loc) xs: iProp Σ := (∃ hd: loc, s ↦ #hd ★ is_list hd xs)%I.

  Global Instance is_list_timeless xs hd: TimelessP (is_list hd xs).
  Proof. generalize hd. induction xs; apply _. Qed.

  Global Instance is_stack_timeless xs hd: TimelessP (is_stack hd xs).
  Proof. generalize hd. induction xs; apply _. Qed.

  Lemma new_stack_spec:
    ∀ (Φ: val → iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ (∀ s, is_stack s [] -★ Φ #s) ⊢ WP new_stack #() {{ Φ }}.
  Proof.
    iIntros (Φ HN) "[#Hh HΦ]". wp_seq.
    wp_bind (ref NONE)%E. wp_alloc l as "Hl".
    wp_alloc l' as "Hl'".
    iApply "HΦ". rewrite /is_stack. iExists l.
    iFrame. by iExists 1%Qp.
  Qed.

  Definition push_triple (s: loc) (x: val) :=
    atomic_triple (fun xs_hd: list val * loc =>
                     let '(xs, hd) := xs_hd in s ↦ #hd ★ is_list hd xs)%I
                  (fun xs_hd ret =>
                     let '(xs, hd) := xs_hd in 
                     ∃ hd': loc,
                       ret = #() ★ s ↦ #hd' ★ hd' ↦ SOMEV (x, #hd) ★ is_list hd xs)%I
                  (nclose heapN)
                  ⊤
                  (push #s x).
  
  Lemma push_atomic_spec (s: loc) (x: val) :
    heapN ⊥ N → heap_ctx ⊢ push_triple s x.
  Proof.
    iIntros (HN) "#?". rewrite /push_triple /atomic_triple.
    iIntros (P Q) "#Hvs".
    iLöb as "IH". iIntros "!# HP". wp_rec.
    wp_let. wp_bind (! _)%E.
    iVs ("Hvs" with "HP") as ([xs hd]) "[[Hs Hhd] [Hvs' _]]".
    wp_load. iVs ("Hvs'" with "[Hs Hhd]") as "HP"; first by iFrame.
    iVsIntro. wp_let. wp_alloc l as "Hl". wp_let.
    wp_bind (CAS _ _ _)%E.
    iVs ("Hvs" with "HP") as ([xs' hd']) "[[Hs Hhd'] Hvs']".
    destruct (decide (hd = hd')) as [->|Hneq].
    * wp_cas_suc. iDestruct "Hvs'" as "[_ Hvs']".
      iVs ("Hvs'" $! #() with "[-]") as "HQ".
      { iExists l. iSplitR; first done. by iFrame. }
      iVsIntro. wp_if. iVsIntro. eauto.
    * wp_cas_fail.
      iDestruct "Hvs'" as "[Hvs' _]".
      iVs ("Hvs'" with "[-]") as "HP"; first by iFrame.
      iVsIntro. wp_if. by iApply "IH".
  Qed.

  Definition pop_triple (s: loc) :=
    atomic_triple (fun xs_hd: list val * loc =>
                     let '(xs, hd) := xs_hd in s ↦ #hd ★ is_list hd xs)%I
                  (fun xs_hd ret =>
                     let '(xs, hd) := xs_hd in
                     (ret = NONEV ★ xs = [] ★ s ↦ #hd ★ is_list hd []) ∨
                     (∃ x q (hd': loc) xs', hd ↦{q} SOMEV (x, #hd') ★ ret = SOMEV x ★
                                            xs = x :: xs' ★ s ↦ #hd' ★ is_list hd' xs'))%I
                  (nclose heapN)
                  ⊤
                  (pop #s).

  Lemma pop_atomic_spec (s: loc):
    heapN ⊥ N → heap_ctx ⊢ pop_triple s.
  Proof.
    iIntros (HN) "#?".
    rewrite /pop_triple /atomic_triple.
    iIntros (P Q) "#Hvs".
    iLöb as "IH". iIntros "!# HP". wp_rec.
    wp_bind (! _)%E.
    iVs ("Hvs" with "HP") as ([xs hd]) "[[Hs Hhd] Hvs']".
    destruct xs as [|y' xs'].
    - simpl. wp_load. iDestruct "Hvs'" as "[_ Hvs']".
      iDestruct "Hhd" as (q) "[Hhd Hhd']".
      iVs ("Hvs'" $! NONEV with "[-Hhd]") as "HQ".
      { iLeft. iSplit=>//. iSplit=>//. iFrame. eauto. }
      iVsIntro. wp_let. wp_load. wp_match.
      iVsIntro. eauto.
    - simpl. iDestruct "Hhd" as (hd' q) "([[Hhd1 Hhd2] Hhd'] & Hxs')".
      iDestruct (dup_is_list with "[Hxs']") as "[Hxs1 Hxs2]"; first by iFrame.
      wp_load. iDestruct "Hvs'" as "[Hvs' _]".
      iVs ("Hvs'" with "[-Hhd1 Hhd2 Hxs1]") as "HP".
      { iFrame. iExists hd', (q / 2)%Qp. by iFrame. }
      iVsIntro. wp_let. wp_load. wp_match. wp_proj.
      wp_bind (CAS _ _ _). iVs ("Hvs" with "HP") as ([xs hd'']) "[[Hs Hhd''] Hvs']".
      destruct (decide (hd = hd'')) as [->|Hneq].
      + wp_cas_suc. iDestruct "Hvs'" as "[_ Hvs']".
        iVs ("Hvs'" $! (SOMEV y') with "[-]") as "HQ".
        { iRight. iExists y', (q / 2 / 2)%Qp, hd', xs'.
          destruct xs as [|x' xs''].
          - simpl. iDestruct "Hhd''" as (?) "H".
            iExFalso. iDestruct (heap_mapsto_op_1 with "[Hhd1 H]") as "[% _]".
            { iSplitL "Hhd1"; done. }
            done.
          - simpl. iDestruct "Hhd''" as (hd''' ?) "(Hhd'' & Hxs'')".
            iDestruct (heap_mapsto_op_1 with "[Hhd1 Hhd'']") as "[% _]".
            { iSplitL "Hhd1"; done. }
            inversion H0. (* FIXME: bad naming *) subst.
            iDestruct (uniq_is_list with "[Hxs1 Hxs'']") as "%"; first by iFrame. subst.
            repeat (iSplitR "Hxs1 Hs"; first done).
            iFrame. }
        iVsIntro. wp_if. wp_proj. eauto.
      + wp_cas_fail. iDestruct "Hvs'" as "[Hvs' _]".
        iVs ("Hvs'" with "[-]") as "HP"; first by iFrame.
        iVsIntro. wp_if. by iApply "IH".
  Qed.

End proof.



Section defs.
  Context `{heapG Σ, !evidenceG loc val Σ} (N: namespace).
  Context (R: val → iProp Σ) (γ: gname) `{∀ x, TimelessP (R x)}.

  Definition allocated hd := (∃ q v, hd ↦{q} v)%I.

  Definition evs := ev loc val γ.

  Fixpoint is_list' (hd: loc) (xs: list val) : iProp Σ :=
    match xs with
    | [] => (∃ q, hd ↦{ q } NONEV)%I
    | x :: xs => (∃ (hd': loc) q, hd ↦{q} SOMEV (x, #hd') ★ evs hd x ★ is_list' hd' xs)%I
    end.

  Lemma in_list' x xs:
    ∀ hd, x ∈ xs →
          is_list' hd xs
          ⊢ ∃ (hd' hd'': loc) q, hd' ↦{q} SOMEV (x, #hd'') ★ evs hd' x.
  Proof.
    induction xs as [|x' xs' IHxs'].
    - intros ? Hin. inversion Hin.
    - intros hd Hin. destruct (decide (x = x')) as [->|Hneq].
      + iIntros "Hls". simpl.
        iDestruct "Hls" as (hd' q) "(? & ? & ?)".
        iExists hd, hd', q. iFrame.
      + assert (x ∈ xs') as Hin'; first set_solver.
        iIntros "Hls". simpl.
        iDestruct "Hls" as (hd' q) "(? & ? & ?)".
        iApply IHxs'=>//.
  Qed.

  Definition perR' hd v v' := (v = (1%Qp, DecAgree v') ★ R v' ★ allocated hd)%I.
  Definition perR  hd v := (∃ v', perR' hd v v')%I.
  
  Definition allR := (∃ m, own γ (● m) ★ [★ map] hd ↦ v ∈ m, perR hd v)%I.

  Definition is_stack' xs s := (∃ hd: loc, s ↦ #hd ★ is_list' hd xs ★ allR)%I.

  Global Instance is_list'_timeless hd xs: TimelessP (is_list' hd xs).
  Proof. generalize hd. induction xs; apply _. Qed.

  Global Instance is_stack'_timeless xs s: TimelessP (is_stack' xs s).
  Proof. apply _. Qed.

  Lemma dup_is_list': ∀ xs hd,
    heap_ctx ★ is_list' hd xs ⊢ |=r=> is_list' hd xs ★ is_list' hd xs.
  Proof.
    induction xs as [|y xs' IHxs'].
    - iIntros (hd) "(#? & Hs)".
      simpl. iDestruct "Hs" as (q) "[Hhd Hhd']". iSplitL "Hhd"; eauto.
    - iIntros (hd) "(#? & Hs)". simpl.
      iDestruct "Hs" as (hd' q) "([Hhd Hhd'] & Hev & Hs')".
      iDestruct (IHxs' with "[Hs']") as "==>[Hs1 Hs2]"; first by iFrame.
      iDestruct (dup_ev with "Hev") as "==>[Hev1 Hev2]".
      iVsIntro. iSplitL "Hhd Hs1 Hev1"; iExists hd', (q / 2)%Qp; by iFrame.
  Qed.

  Lemma extract_is_list: ∀ xs hd,
    heap_ctx ★ is_list' hd xs ⊢ |=r=> is_list' hd xs ★ is_list hd xs.
  Proof.
    induction xs as [|y xs' IHxs'].
    - iIntros (hd) "(#? & Hs)".
      simpl. iDestruct "Hs" as (q) "[Hhd Hhd']". iSplitL "Hhd"; eauto.
    - iIntros (hd) "(#? & Hs)". simpl.
      iDestruct "Hs" as (hd' q) "([Hhd Hhd'] & Hev & Hs')".
      iDestruct (IHxs' with "[Hs']") as "==>[Hs1 Hs2]"; first by iFrame.
      iVsIntro. iSplitL "Hhd Hs1 Hev"; iExists hd', (q / 2)%Qp; by iFrame.
  Qed.

  Definition f_spec (xs: list val) (s: loc) (f: val) (Rf RI: iProp Σ) := (* Rf, RI is some frame *)
    ∀ Φ (x: val),
      heapN ⊥ N → x ∈ xs →
      heap_ctx ★ inv N ((∃ xs, is_stack' xs s) ★ RI) ★  Rf ★ (Rf -★ Φ #())
      ⊢ WP f x {{ Φ }}.
End defs.

Section proofs.
  Context `{heapG Σ, !evidenceG loc val Σ} (N: namespace).
  Context (R: val → iProp Σ).

Lemma new_stack_spec' Φ RI:
    heapN ⊥ N →
    heap_ctx ★ RI ★ (∀ γ s : loc, inv N ((∃ xs, is_stack' R γ xs s) ★ RI) -★ Φ #s)
    ⊢ WP new_stack #() {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & HR & HΦ)".
    iVs (own_alloc (● (∅: evmapR loc val) ⋅ ◯ ∅)) as (γ) "[Hm Hm']".
    { apply auth_valid_discrete_2. done. }
    wp_seq. wp_bind (ref NONE)%E. wp_alloc l as "Hl".
    wp_alloc s as "Hs".
    iAssert ((∃ xs : list val, is_stack' R γ xs s) ★ RI)%I with "[-HΦ Hm']" as "Hinv".
    { iFrame. iExists [], l. iFrame. simpl. iSplitL "Hl".
      - eauto.
      - iExists ∅. iFrame. by iApply (big_sepM_empty (fun hd v => perR R hd v)). }
    iVs (inv_alloc N _ ((∃ xs : list val, is_stack' R γ xs s) ★ RI)%I with "[-HΦ Hm']") as "#?"; first eauto.
    by iApply "HΦ".
  Qed.
    
  Lemma iter_spec Φ γ s (Rf RI: iProp Σ):
    ∀ xs hd (f: expr) (f': val),
      heapN ⊥ N → f_spec N R γ xs s f' Rf RI → to_val f = Some f' →
      heap_ctx ★ inv N ((∃ xs, is_stack' R γ xs s) ★ RI) ★
      is_list' γ hd xs ★ Rf ★ (Rf -★ Φ #())
      ⊢ WP (iter #hd) f {{ v, Φ v }}.
  Proof.
    induction xs as [|x xs' IHxs'].
    - simpl. iIntros (hd f f' HN ? ?) "(#Hh & #? & Hxs1 & HRf & HΦ)".
      iDestruct "Hxs1" as (q) "Hhd".
      wp_rec. wp_value. iVsIntro. wp_let. wp_load. wp_match. by iApply "HΦ".
    - simpl. iIntros (hd f f' HN Hf ?) "(#Hh & #? & Hxs1 & HRf & HΦ)".
      iDestruct "Hxs1" as (hd2 q) "(Hhd & Hev & Hhd2)".
      wp_rec. wp_value. iVsIntro. wp_let. wp_load. wp_match. wp_proj.
      wp_bind (f' _). iApply Hf=>//; first set_solver. iFrame "#". iFrame. iIntros "HRf".
      wp_seq. wp_proj. iApply (IHxs' with "[-]")=>//.
      + rewrite /f_spec. iIntros (? ? ? ?) "(#? & #? & ? & ?)".
        iApply Hf=>//.
        * set_solver.
        * iFrame "#". by iFrame.
      + apply to_of_val.
      + iFrame "#". by iFrame.
  Qed.
  
  Lemma push_spec Φ γ (s: loc) (x: val) RI:
    heapN ⊥ N →
    heap_ctx ★ R x ★ inv N ((∃ xs, is_stack' R γ xs s) ★ RI) ★ ((∃ hd, evs γ hd x) -★ Φ #())
    ⊢ WP push #s x {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & HRx & #? & HΦ)".
    iDestruct (push_atomic_spec N s x with "Hh") as "Hpush"=>//.
    rewrite /push_triple /atomic_triple.
    iSpecialize ("Hpush" $! (R x) (fun _ ret => (∃ hd, evs γ hd x) ★ ret = #())%I with "[]").
    - iIntros "!# Rx".
      (* open the invariant *)
      iInv N as "[IH1 ?]" "Hclose".
      iDestruct "IH1" as (xs hd) "[>Hs [>Hxs HR]]".
      iDestruct (extract_is_list with "[Hxs]") as "==>[Hxs Hxs']"; first by iFrame.
      iDestruct (dup_is_list with "[Hxs']") as "[Hxs'1 Hxs'2]"; first by iFrame.
      (* mask magic *)
      iApply pvs_intro'.
      { apply ndisj_subseteq_difference; auto. }
      iIntros "Hvs".
      iExists (xs, hd).
      iFrame "Hs Hxs'1".
      iSplit.
      + (* provide a way to rollback *)
        iIntros "[Hs Hl']".
        iVs "Hvs". iVs ("Hclose" with "[-Rx]"); last done.
        { iNext. iFrame. iExists xs. iExists hd. by iFrame. }
      + (* provide a way to commit *)
        iIntros (v) "Hs".
        iDestruct "Hs" as (hd') "[% [Hs [[Hhd'1 Hhd'2] Hxs']]]". subst.
        iVs "Hvs".
        iDestruct "HR" as (m) "[>Hom HRm]".
        destruct (m !! hd') eqn:Heqn.
        * iDestruct (big_sepM_delete_later (perR R) m with "HRm") as "[Hx ?]"=>//.
          iDestruct "Hx" as (?) "(_ & _ & >Hhd'')".
          iDestruct (heap_mapsto_op_1 with "[Hhd'1 Hhd'2]") as "[_ Hhd]"; first iFrame.
          rewrite Qp_div_2.
          iDestruct "Hhd''" as (q v) "Hhd''". iExFalso.
          iApply (bogus_heap hd' 1%Qp q); first apply Qp_not_plus_q_ge_1.
          iFrame "#". iFrame.
        * iAssert (evs γ hd' x ★ ▷ (allR R γ))%I
                  with "==>[Rx Hom HRm Hhd'1]" as "[Hox ?]".
          {
            iDestruct (evmap_alloc _ _ _ m with "[Hom]") as "==>[Hom Hox]"=>//.
            iDestruct (dup_ev with "[Hox]") as "==>[Hox1 Hox2]".
            { rewrite /ev. eauto. }
            iFrame.
            iDestruct (big_sepM_insert_later (perR R) m) as "H"=>//.
            iExists (<[hd' := (1%Qp, DecAgree x)]> m).
            iFrame. iApply "H". iFrame. iExists x.
            iFrame. rewrite /allocated. iSplitR "Hhd'1"; auto.
          }
          iDestruct (dup_ev with "[Hox]") as "==>[Hox1 Hox2]"=>//.
          iVs ("Hclose" with "[-Hox2]").
          { iNext. iFrame. iExists (x::xs).
            iExists hd'. iFrame.
            iExists hd, (1/2)%Qp. iFrame.
          }
        iVsIntro. iSplitL; last auto. by iExists hd'.
    - iApply wp_wand_r. iSplitL "HRx Hpush".
      + by iApply "Hpush".
      + iIntros (?) "H". iDestruct "H" as (_) "[? %]". subst.
        by iApply "HΦ".
  Qed.

  (* some helpers *)
  Lemma access (γ: gname) (x: val) (xs: list val) m:
    ∀ hd: loc,
    x ∈ xs  →
    ▷ ([★ map] hd↦v ∈ m, perR R hd v) ★ own γ (● m) ★
    is_list' γ hd xs
    ⊢ ∃ hd' q, ▷ ([★ map] hd↦v ∈ delete hd' m, perR R hd v) ★
               ▷ perR R hd' (q, DecAgree x) ★ m !! hd' = Some (q, DecAgree x) ★ own γ (● m).
  Proof.
    induction xs as [|x' xs' IHxs'].
    - iIntros (? Habsurd). inversion Habsurd.
    - destruct (decide (x = x')) as [->|Hneq].
      + iIntros (hd _) "(HR & Hom & Hxs)".
        simpl. iDestruct "Hxs" as (hd' q) "[Hhd [Hev Hxs']]".
        rewrite /ev. destruct (m !! hd) as [[q' [x|]]|] eqn:Heqn.
        * iDestruct (big_sepM_delete_later (perR R) m with "HR") as "[Hp HRm]"=>//.
          iDestruct (map_agree_eq' _ _ _ m with "[Hom Hev]") as "(Hom & Hev & %)"=>//; first iFrame.
          subst. iExists hd, q'. inversion H0. subst. by iFrame.
        * iDestruct (big_sepM_delete_later (perR R) m with "HR") as "[Hp HRm]"=>//.
          iDestruct (map_agree_eq' _ _ _ m with "[Hom Hev]") as "(Hom & Hev & %)"=>//; first iFrame.
        * iExFalso. iApply (map_agree_none' _ _ _ m)=>//. iFrame.
      + iIntros (hd ?).
        assert (x ∈ xs'); first set_solver.
        iIntros "(HRs & Hom & Hxs')".
        simpl. iDestruct "Hxs'" as (hd' q) "[Hhd [Hev Hxs']]".
        iDestruct (IHxs' hd' with "[HRs Hxs' Hom]") as "?"=>//.
        iFrame.
  Qed.

End proofs.

