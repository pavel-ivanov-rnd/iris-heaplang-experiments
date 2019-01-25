From stdpp Require Import namespaces.
From iris.program_logic Require Export weakestpre atomic.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import frac auth gmap csum.

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

Section proof.
  Context `{!heapG Σ} (N: namespace).

  Fixpoint is_list (hd: loc) (xs: list val) : iProp Σ :=
    match xs with
    | [] => (∃ q, hd ↦{ q } NONEV)%I
    | x :: xs => (∃ (hd': loc) q, hd ↦{ q } SOMEV (x, #hd') ∗ is_list hd' xs)%I
    end.

  Lemma dup_is_list : ∀ xs hd,
    is_list hd xs ⊢ is_list hd xs ∗ is_list hd xs.
  Proof.
    induction xs as [|y xs' IHxs'].
    - iIntros (hd) "Hs".
      simpl. iDestruct "Hs" as (q) "[Hhd Hhd']". iSplitL "Hhd"; eauto.
    - iIntros (hd) "Hs". simpl.
      iDestruct "Hs" as (hd' q) "([Hhd Hhd'] & Hs')".
      iDestruct (IHxs' with "[Hs']") as "[Hs1 Hs2]"; first by iFrame.
      iSplitL "Hhd Hs1"; iExists hd', (q / 2)%Qp; by iFrame.
  Qed.

  Lemma uniq_is_list:
    ∀ xs ys hd, is_list hd xs ∗ is_list hd ys ⊢ ⌜xs = ys⌝.
  Proof.
    induction xs as [|x xs' IHxs'].
    - induction ys as [|y ys' IHys'].
      + auto.
      + iIntros (hd) "(Hxs & Hys)".
        simpl. iDestruct "Hys" as (hd' ?) "(Hhd & Hys')".
        iExFalso. iDestruct "Hxs" as (?) "Hhd'".
        (* FIXME: If I dont use the @ here and below through this file, it loops. *)
        by iDestruct (@mapsto_agree with "[$Hhd] [$Hhd']") as %?.
    - induction ys as [|y ys' IHys'].
      + iIntros (hd) "(Hxs & Hys)".
        simpl.
        iExFalso. iDestruct "Hxs" as (? ?) "(Hhd & _)".
        iDestruct "Hys" as (?) "Hhd'".
        by iDestruct (@mapsto_agree with "[$Hhd] [$Hhd']") as %?.
      + iIntros (hd) "(Hxs & Hys)".
        simpl. iDestruct "Hxs" as (? ?) "(Hhd & Hxs')".
        iDestruct "Hys" as (? ?) "(Hhd' & Hys')".
        iDestruct (@mapsto_agree with "[$Hhd] [$Hhd']") as %[= Heq].
        subst. iDestruct (IHxs' with "[Hxs' Hys']") as "%"; first by iFrame.
        by subst.
  Qed.

  Definition is_stack (s: loc) xs: iProp Σ := (∃ hd: loc, s ↦ #hd ∗ is_list hd xs)%I.

  Global Instance is_list_timeless xs hd: Timeless (is_list hd xs).
  Proof. generalize hd. induction xs; apply _. Qed.

  Global Instance is_stack_timeless xs hd: Timeless (is_stack hd xs).
  Proof. generalize hd. induction xs; apply _. Qed.

  Lemma new_stack_spec:
    ∀ (Φ: val → iProp Σ),
      (∀ s, is_stack s [] -∗ Φ #s) ⊢ WP new_stack #() {{ Φ }}.
  Proof.
    iIntros (Φ) "HΦ". wp_lam.
    wp_bind (ref NONE)%E. wp_alloc l as "Hl".
    wp_alloc l' as "Hl'".
    iApply "HΦ". rewrite /is_stack. iExists l.
    iFrame. by iExists 1%Qp.
  Qed.

  Definition push_triple (s: loc) (x: val) :=
    <<< ∀ (xs : list val) (hd : loc), s ↦ #hd ∗ is_list hd xs >>>
      push #s x @ ⊤
    <<< ∃ hd' : loc, s ↦ #hd' ∗ hd' ↦ SOMEV (x, #hd) ∗ is_list hd xs, RET #() >>>.
  
  Lemma push_atomic_spec (s: loc) (x: val) :
    push_triple s x.
  Proof.
    rewrite /push_triple. iApply wp_atomic_intro.
    iIntros (Φ) "HP". iLöb as "IH". wp_rec.
    wp_let. wp_bind (! _)%E.
    iMod "HP" as (xs hd) "[[Hs Hhd] [Hvs' _]]".
    wp_load. iMod ("Hvs'" with "[Hs Hhd]") as "HP"; first by iFrame.
    iModIntro. wp_let. wp_alloc l as "Hl". wp_let.
    wp_bind (CAS _ _ _)%E.
    iMod "HP" as (xs' hd') "[[Hs Hhd'] Hvs']".
    destruct (decide (hd = hd')) as [->|Hneq].
    * wp_cas_suc. iDestruct "Hvs'" as "[_ Hvs']".
      iMod ("Hvs'" with "[-]") as "HQ".
      { by iFrame. }
      iModIntro. wp_if. eauto.
    * wp_cas_fail.
      iDestruct "Hvs'" as "[Hvs' _]".
      iMod ("Hvs'" with "[-]") as "HP"; first by iFrame.
      iModIntro. wp_if. by iApply "IH".
  Qed.

  Definition pop_triple (s: loc) :=
    <<< ∀ (xs : list val) (hd : loc), s ↦ #hd ∗ is_list hd xs >>>
      pop #s @ ⊤
    <<< match xs with [] => s ↦ #hd ∗ is_list hd []
                | x::xs' => ∃ q (hd': loc), hd ↦{q} SOMEV (x, #hd') ∗ s ↦ #hd' ∗ is_list hd' xs' end,
    RET match xs with [] => NONEV | x :: _ => SOMEV x end >>>.

  Lemma pop_atomic_spec (s: loc):
    pop_triple s.
  Proof.
    rewrite /pop_triple. iApply wp_atomic_intro.
    iIntros (Φ) "HP". iLöb as "IH". wp_rec.
    wp_bind (! _)%E.
    iMod "HP" as (xs hd) "[[Hs Hhd] Hvs']".
    destruct xs as [|y' xs'].
    - simpl. wp_load. iDestruct "Hvs'" as "[_ Hvs']".
      iDestruct "Hhd" as (q) "[Hhd Hhd']".
      iMod ("Hvs'" with "[-Hhd]") as "HQ".
      { iFrame. eauto. }
      iModIntro. wp_let. wp_load. wp_pures.
      eauto.
    - simpl. iDestruct "Hhd" as (hd' q) "([[Hhd1 Hhd2] Hhd'] & Hxs')".
      iDestruct (dup_is_list with "[Hxs']") as "[Hxs1 Hxs2]"; first by iFrame.
      wp_load. iDestruct "Hvs'" as "[Hvs' _]".
      iMod ("Hvs'" with "[-Hhd1 Hhd2 Hxs1]") as "HP".
      { iFrame. iExists hd', (q / 2)%Qp. by iFrame. }
      iModIntro. wp_let. wp_load. wp_match. wp_proj.
      wp_bind (CAS _ _ _).
      iMod "HP" as (xs hd'') "[[Hs Hhd''] Hvs']".
      destruct (decide (hd = hd'')) as [->|Hneq].
      + wp_cas_suc. iDestruct "Hvs'" as "[_ Hvs']".
        destruct xs as [|x' xs''].
        { simpl. iDestruct "Hhd''" as (?) "H".
          iExFalso. by iDestruct (@mapsto_agree with "[$Hhd1] [$H]") as %?. }
        simpl. iDestruct "Hhd''" as (hd''' ?) "(Hhd'' & Hxs'')".
        iDestruct (@mapsto_agree with "[$Hhd1] [$Hhd'']") as %[=]. subst.
        iMod ("Hvs'" with "[-]") as "HQ".
        { iExists (q / 2 / 2)%Qp, _.
          iDestruct (uniq_is_list with "[Hxs1 Hxs'']") as "%"; first by iFrame. subst.
          repeat (iSplitR "Hxs1 Hs"; first done).
          iFrame. }
        iModIntro. wp_if. wp_pures. eauto.
      + wp_cas_fail. iDestruct "Hvs'" as "[Hvs' _]".
        iMod ("Hvs'" with "[-]") as "HP"; first by iFrame.
        iModIntro. wp_if. by iApply "IH".
  Qed.
End proof.
