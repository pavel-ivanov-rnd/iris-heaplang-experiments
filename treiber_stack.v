From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import upred upred_big_op.
From iris.tests Require Import atomic.

Definition new_stack: val := λ: <>, ref NONE.

Definition push: val :=
  rec: "push" "s" "x" :=
      let: "hd" := !"s" in
      let: "s'" := SOME ("x", ref "hd") in
      if: CAS "s" "hd" "s'"
        then #()
        else "push" "s" "x".

Definition pop: val :=
  rec: "pop" "s" :=
      let: "hd" := !"s" in
      match: "hd" with
        SOME "pair" =>
        if: CAS "s" "hd" (Snd "pair")
          then SOME (Fst "pair")
          else "pop" "s"
      | NONE => NONE
      end.

Section proof.
  Context `{!heapG Σ} (N: namespace) (R: val → iProp Σ) `{∀ v, TimelessP (R v)}.

  Fixpoint is_stack (s: loc) (xs: list val) : iProp Σ :=
    match xs with
    | [] => (s ↦ NONEV)%I
    | x :: xs => (∃ s': loc, s ↦ SOMEV (x, #s') ★ R x ★ is_stack s' xs)%I
    end.

  Definition is_some_stack (s: loc) : iProp Σ := (∃ xs: list val, is_stack s xs)%I.

  Definition stack_inv s : iProp Σ := inv N (is_some_stack s).

  Instance stack_inv_persistent s: PersistentP (stack_inv s).
  Proof. apply _. Qed.

  Instance is_stack_timeless: ∀ xs s, TimelessP (is_stack s xs).
  Proof.
    induction xs as [|? xs'].
    - apply _.
    - simpl. intros s.
      apply uPred.exist_timeless.
      intros s'. specialize IHxs' with s'.
      apply _.
  Qed.

  Instance is_some_stack_timeless: ∀ s, TimelessP (is_some_stack s).
  Proof.
    intros s. rewrite /is_some_stack. apply uPred.exist_timeless. intros ?. apply is_stack_timeless.
  Qed.

  Lemma new_stack_spec:
    ∀ (Φ: val → iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ (∀ s, is_stack s [] -★ Φ #s) ⊢ WP new_stack #() {{ Φ }}.
  Proof. iIntros (Φ HN) "[#Hh HΦ]". wp_seq. wp_alloc l as "Hl". by iApply "HΦ". Qed.

  Definition push_triple (s: loc) (x: val) :=
    atomic_triple (fun xs => R x ★ is_stack s xs)%I
                  (fun xs _ => is_stack s (x :: xs))
                  (nclose heapN)
                  ⊤
                  (push #s x).
  
  Lemma push_atomic_spec (s: loc) (x: val) :
    heapN ⊥ N → heap_ctx ⊢ push_triple s x.
  Proof.
    iIntros (HN) "#?".
    rewrite /push_triple /atomic_triple.
    iIntros (P Q) "#Hvs".
    iLöb as "IH". iIntros "!# HP". wp_rec.
    wp_let. wp_bind (! _)%E.
    iVs ("Hvs" with "HP") as (xs) "[[Hx Hxs] [Hvs' _]]".
    destruct xs as [|y xs'].
    - simpl. wp_load. iVs ("Hvs'" with "[Hx Hxs]") as "HP"; first by iFrame.
      iVsIntro. wp_let. wp_alloc l as "Hl". wp_let.
      wp_bind (CAS _ _ _)%E.
      iVs ("Hvs" with "HP") as (xs) "[[Hx Hxs] Hvs']".
      destruct xs as [|y xs'].
      + simpl. wp_cas_suc.
        iDestruct "Hvs'" as "[_ Hvs']".
        iVs ("Hvs'" $! #() with "[Hl Hx Hxs]") as "HQ".
        {  iExists l. by iFrame. }
        iVsIntro. wp_if. iVsIntro. eauto.
      + simpl. iDestruct "Hxs" as (s') "(Hs & Hy & Hs')".
        wp_cas_fail.
        iDestruct "Hvs'" as "[Hvs' _]".
        iVs ("Hvs'" with "[Hx Hs Hy Hs']").
        { iFrame. iExists s'. by iFrame. }
        iVsIntro. wp_if. by iApply "IH".
    - simpl.
      iDestruct "Hxs" as (s') "(Hs & Hy & Hs')".
      wp_load. iVs ("Hvs'" with "[Hx Hs Hy Hs']") as "HP".
      { iFrame. iExists s'. by iFrame. }
      iVsIntro. wp_let. wp_alloc l as "Hl".
      wp_let. wp_bind (CAS _ _ _)%E.
      iVs ("Hvs" with "HP") as (xs) "[[Hx Hxs] Hvs']".
      destruct xs as [|y' xs''].
      + simpl. wp_cas_fail.
        iDestruct "Hvs'" as "[Hvs' _]".
        iVs ("Hvs'" with "[Hx Hxs]"); first by iFrame.
        iVsIntro. wp_if. by iApply "IH".
      + simpl. iDestruct "Hxs" as (s'') "(Hs & Hy' & Hs'')".
        destruct (decide (s' = s'' ∧ y = y')) as [[]|Hneq].
        * subst. wp_cas_suc.
          iDestruct "Hvs'" as "[_ Hvs']".
          iVs ("Hvs'" $! #() with "[Hs Hx Hl Hy' Hs'']") as "HQ".
          { iExists l. iFrame. iExists s''. by iFrame. }
          iVsIntro. wp_if. iVsIntro. eauto.
        * wp_cas_fail.
          { intros Heq. apply Hneq. by inversion Heq. }
          iDestruct "Hvs'" as "[Hvs' _]".
          iVs ("Hvs'" with "[Hx Hs Hy' Hs'']").
          { iFrame. iExists s''. by iFrame. }
          iVsIntro. wp_if. by iApply "IH".
  Qed.
  
    
End proof.

