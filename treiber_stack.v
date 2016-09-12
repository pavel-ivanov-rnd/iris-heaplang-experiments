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
  Context `{!heapG Σ} (N: namespace) (R: val → iProp Σ) `{∀ v, TimelessP (R v)}.

  Fixpoint is_stack' (hd: loc) (xs: list val) : iProp Σ :=
    match xs with
    | [] => (∃ q, hd ↦{ q } NONEV)%I
    | x :: xs => (∃ (hd': loc) q, hd ↦{ q } SOMEV (x, #hd') ★ □ R x ★ is_stack' hd' xs)%I
    end.

  Definition is_stack (s: loc) xs: iProp Σ := (∃ hd: loc, s ↦ #hd ★ is_stack' hd xs)%I.

  Definition is_some_stack (s: loc): iProp Σ := (∃ xs, is_stack s xs)%I.

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
                  (fun xs ret => ret = NONEV ∨ (∃ x, ret = SOMEV x ★ □ R x))%I (* FIXME: we can give a stronger one *)
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
      iVs ("Hvs'" $! NONEV with "[]") as "HQ"; first by iLeft.
      iVsIntro. wp_let. iDestruct "Hhd" as (q) "Hhd".
      wp_load. wp_match.
      iVsIntro. by iExists [].
    - simpl. iDestruct "Hxs" as (hd) "[Hs Hhd]".
      simpl. iDestruct "Hhd" as (hd' q) "([Hhd Hhd'] & #Hy' & Hxs')".
      wp_load. iDestruct "Hvs'" as "[Hvs' _]".
      iVs ("Hvs'" with "[-Hhd]") as "HP".
      { iExists hd. iFrame. iExists hd', (q / 2)%Qp. by iFrame. }
      iVsIntro. wp_let. wp_load. wp_match. wp_proj.
      wp_bind (CAS _ _ _). iVs ("Hvs" with "HP") as (xs) "[Hxs Hvs']".
      iDestruct "Hxs" as (hd'') "[Hs Hhd'']".
      destruct (decide (hd = hd'')) as [->|Hneq].
      + wp_cas_suc. iDestruct "Hvs'" as "[_ Hvs']".
        iVs ("Hvs'" $! (SOMEV y') with "[]") as "HQ".
        { iRight. eauto. }
        iVsIntro. wp_if. wp_proj. eauto.
      + wp_cas_fail. iDestruct "Hvs'" as "[Hvs' _]".
        iVs ("Hvs'" with "[-]") as "HP".
        { iExists hd''. by iFrame. }
        iVsIntro. wp_if. by iApply "IH".
  Qed.
      
End proof.

