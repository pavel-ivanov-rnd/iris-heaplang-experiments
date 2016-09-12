From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import upred upred_big_op.
From iris.tests Require Import atomic.

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
        SOME "pair" =>
        if: CAS "s" "hd" (Snd "pair")
          then SOME (Fst "pair")
          else "pop" "s"
      | NONE => NONE
      end.

Section proof.
  Context `{!heapG Σ} (N: namespace) (R: val → iProp Σ).

  Fixpoint is_stack' (hd: loc) (xs: list val) : iProp Σ :=
    match xs with
    | [] => (∃ q, hd ↦{ q } NONEV)%I
    | x :: xs => (∃ (hd': loc) q, hd ↦{ q } SOMEV (x, #hd') ★ □ R x ★ is_stack' hd' xs)%I
    end.

  (* how can we prove that it is persistent? *)
  Lemma dup_is_stack': ∀ xs hd,
    heap_ctx ★ is_stack' hd xs ⊢ is_stack' hd xs ★ is_stack' hd xs.
  Proof.
    induction xs as [|y xs' IHxs'].
    - iIntros (hd) "(#? & Hs)".
      simpl. iDestruct "Hs" as (q) "[Hhd Hhd']". iSplitL "Hhd"; eauto.
    - iIntros (hd) "(#? & Hs)". simpl.
      iDestruct "Hs" as (hd' q) "([Hhd Hhd'] & #HR & Hs')".
      iDestruct (IHxs' with "[Hs']") as "[Hs1 Hs2]"; first by iFrame.
      iSplitL "Hhd Hs1"; iExists hd', (q / 2)%Qp; by iFrame.
  Qed.

  Lemma uniq_is_stack':
    ∀ xs ys hd, heap_ctx ★ is_stack' hd xs ★ is_stack' hd ys ⊢ xs = ys.
  Proof.
    induction xs as [|x xs' IHxs'].
    - induction ys as [|y ys' IHys'].
      + auto.
      + iIntros (hd) "(#? & Hxs & Hys)".
        simpl. iDestruct "Hys" as (hd' ?) "(Hhd & #Hy & Hys')".
        iExFalso. iDestruct "Hxs" as (?) "Hhd'".
        iDestruct (heap_mapsto_op_1 with "[Hhd Hhd']") as "[% _]".
        { iSplitL "Hhd"; done. }
        done.
    - induction ys as [|y ys' IHys'].
      + iIntros (hd) "(#? & Hxs & Hys)".
        simpl.
        iExFalso. iDestruct "Hxs" as (? ?) "(Hhd & _ & _)".
        iDestruct "Hys" as (?) "Hhd'".
        iDestruct (heap_mapsto_op_1 with "[Hhd Hhd']") as "[% _]".
        { iSplitL "Hhd"; done. }
        done.
      + iIntros (hd) "(#? & Hxs & Hys)".
        simpl. iDestruct "Hxs" as (? ?) "(Hhd & _ & Hxs')".
        iDestruct "Hys" as (? ?) "(Hhd' & _ & Hys')".
        iDestruct (heap_mapsto_op_1 with "[Hhd Hhd']") as "[% _]".
        { iSplitL "Hhd"; done. }
        inversion H3. (* FIXME: name *)
        subst. iDestruct (IHxs' with "[Hxs' Hys']") as "%"; first by iFrame.
        by subst.
  Qed.
  
  Definition is_stack (s: loc) xs: iProp Σ := (∃ hd: loc, s ↦ #hd ★ is_stack' hd xs)%I.

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
    atomic_triple (fun xs => □ R x ★ is_stack s xs)%I
                  (fun xs _ => is_stack s (x :: xs))
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
    iVs ("Hvs" with "HP") as (xs) "[[Hx Hxs] [Hvs' _]]".
    simpl. iDestruct "Hxs" as (hd) "[Hs Hhd]".
    wp_load. iVs ("Hvs'" with "[Hx Hs Hhd]") as "HP".
    { rewrite /is_stack. iFrame. iExists hd. by iFrame. }
    iVsIntro. wp_let. wp_alloc l as "Hl". wp_let.
    wp_bind (CAS _ _ _)%E.
    iVs ("Hvs" with "HP") as (xs') "[[Hx Hxs] Hvs']".
    simpl. iDestruct "Hxs" as (hd') "[Hs Hhd']".
    destruct (decide (hd = hd')) as [->|Hneq].
    * wp_cas_suc. iDestruct "Hvs'" as "[_ Hvs']".
      iVs ("Hvs'" $! #() with "[-]") as "HQ".
      {  iExists l. iFrame. iExists hd', 1%Qp. by iFrame. }
      iVsIntro. wp_if. iVsIntro. eauto.
    * wp_cas_fail.
      iDestruct "Hvs'" as "[Hvs' _]".
      iVs ("Hvs'" with "[-]") as "HP".
      {  iFrame. iExists hd'. by iFrame. }
      iVsIntro. wp_if. by iApply "IH".
  Qed.

  Definition pop_triple (s: loc) :=
    atomic_triple (fun xs => is_stack s xs)%I
                  (fun xs ret => (ret = NONEV ★ xs = [] ★ is_stack s []) ∨
                                 (∃ x xs', ret = SOMEV x ★ □ R x ★ xs = x :: xs' ★ is_stack s xs'))%I
                  (nclose heapN)
                  ⊤
                  (pop #s).
  
  Lemma pop_atomic_spec (s: loc) (x: val) :
    heapN ⊥ N → heap_ctx ⊢ pop_triple s.
  Proof.
    iIntros (HN) "#?".
    rewrite /pop_triple /atomic_triple.
    iIntros (P Q) "#Hvs".
    iLöb as "IH". iIntros "!# HP". wp_rec.
    wp_bind (! _)%E.
    iVs ("Hvs" with "HP") as (xs) "[Hxs Hvs']".
    destruct xs as [|y' xs'].
    - simpl. iDestruct "Hxs" as (hd) "[Hs Hhd]".
      wp_load. iDestruct "Hvs'" as "[_ Hvs']".
      iDestruct "Hhd" as (q) "[Hhd Hhd']".
      iVs ("Hvs'" $! NONEV with "[-Hhd]") as "HQ".
      { iLeft. iSplit=>//. iSplit=>//.
        iExists hd. iFrame. rewrite /is_stack'. eauto. }
      iVsIntro. wp_let. wp_load. wp_match.
      iVsIntro. by iExists [].
    - simpl. iDestruct "Hxs" as (hd) "[Hs Hhd]".
      simpl. iDestruct "Hhd" as (hd' q) "([Hhd Hhd'] & #Hy' & Hxs')".
      iDestruct (dup_is_stack' with "[Hxs']") as "[Hxs1 Hxs2]"; first by iFrame.
      wp_load. iDestruct "Hvs'" as "[Hvs' _]".
      iVs ("Hvs'" with "[-Hhd Hxs1]") as "HP".
      { iExists hd. iFrame. iExists hd', (q / 2)%Qp. by iFrame. }
      iVsIntro. wp_let. wp_load. wp_match. wp_proj.
      wp_bind (CAS _ _ _). iVs ("Hvs" with "HP") as (xs) "[Hxs Hvs']".
      iDestruct "Hxs" as (hd'') "[Hs Hhd'']".
      destruct (decide (hd = hd'')) as [->|Hneq].
      + wp_cas_suc. iDestruct "Hvs'" as "[_ Hvs']".
        iVs ("Hvs'" $! (SOMEV y') with "[-]") as "HQ".
        { iRight. rewrite /is_stack. iExists y', xs'.
          destruct xs as [|x' xs''].
          - simpl. iDestruct "Hhd''" as (?) "H".
            iExFalso. iDestruct (heap_mapsto_op_1 with "[Hhd H]") as "[% _]".
            { iSplitL "Hhd"; done. }
            done.
          - simpl. iDestruct "Hhd''" as (hd''' ?) "(Hhd'' & _ & Hxs'')".
            iDestruct (heap_mapsto_op_1 with "[Hhd Hhd'']") as "[% _]".
            { iSplitL "Hhd"; done. }
            inversion H0. (* FIXME: bad naming *) subst.
            iDestruct (uniq_is_stack' with "[Hxs1 Hxs'']") as "%"; first by iFrame. subst.
            repeat (iSplitR "Hxs1 Hs"; first done).
            iExists hd'''. by iFrame.
        }
        iVsIntro. wp_if. wp_proj. eauto.
      + wp_cas_fail. iDestruct "Hvs'" as "[Hvs' _]".
        iVs ("Hvs'" with "[-]") as "HP".
        { iExists hd''. by iFrame. }
        iVsIntro. wp_if. by iApply "IH".
  Qed.
      
End proof.
