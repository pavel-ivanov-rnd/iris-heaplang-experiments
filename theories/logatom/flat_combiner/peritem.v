From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac auth gmap csum.
From iris.base_logic.lib Require Import invariants.
From iris_examples.logatom Require Export treiber.

(** The flat combiner uses a bag, this is where we prove the spec for that.
    We re-use the code but not the spec of the treiber stack. *)

Section defs.
  Context `{heapG Σ} (N: namespace).
  Context (R: val → iProp Σ) `{∀ x, TimelessP (R x)}.

  Fixpoint is_list_R (hd: loc) (xs: list val) : iProp Σ :=
    match xs with
    | [] => (∃ q, hd ↦{ q } NONEV)%I
    | x :: xs => (∃ (hd': loc) q, hd ↦{q} SOMEV (x, #hd') ∗ inv N (R x) ∗ is_list_R hd' xs)%I
    end.

  Definition is_bag_R xs s := (∃ hd: loc, s ↦ #hd ∗ is_list_R hd xs)%I.

  Lemma dup_is_list_R : ∀ xs hd,
    is_list_R hd xs ⊢ |==> is_list_R hd xs ∗ is_list_R hd xs.
  Proof.
    induction xs as [|y xs' IHxs'].
    - iIntros (hd) "Hs".
      simpl. iDestruct "Hs" as (q) "[Hhd Hhd']". iSplitL "Hhd"; eauto.
    - iIntros (hd) "Hs". simpl.
      iDestruct "Hs" as (hd' q) "([Hhd Hhd'] & #Hinv & Hs')".
      iDestruct (IHxs' with "[Hs']") as ">[Hs1 Hs2]"; first by iFrame.
      iModIntro. iSplitL "Hhd Hs1"; iExists hd', (q / 2)%Qp; by iFrame.
  Qed.

  Definition f_spec (R: iProp Σ) (f: val) (Rf: iProp Σ) x :=
    {{{ inv N R ∗ Rf }}}
      f x
    {{{ RET #(); Rf }}}.

End defs.

Section proofs.
  Context `{heapG Σ} (N: namespace).
  Context (R: val → iProp Σ).

  Definition bag_inv s: iProp Σ := inv N (∃ xs, is_bag_R N R xs s)%I.

  Lemma new_bag_spec:
    {{{ True }}} new_stack #() {{{ s, RET #s; bag_inv s }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_fupd.
    wp_lam. wp_bind (ref NONE)%E. wp_alloc l as "Hl".
    wp_alloc s as "Hs".
    iAssert ((∃ xs, is_bag_R N R xs s))%I with "[-HΦ]" as "Hxs".
    { iFrame. iExists [], l.
      iFrame. simpl. eauto. }
    iMod (inv_alloc N _ (∃ xs : list val, is_bag_R N R xs s)%I with "[-HΦ]") as "#?"; first eauto.
    iApply "HΦ". iFrame "#". done.
  Qed.
  
  Lemma push_spec (s: loc) (x: val):
    {{{ R x ∗ bag_inv s }}} push #s x {{{ RET #() ; inv N (R x) }}}.
  Proof.
    iIntros (Φ) "(HRx & #?) HΦ".
    iLöb as "IH". wp_rec. wp_let.
    wp_bind (! _)%E.
    iInv N as "H1" "Hclose".
    iDestruct "H1" as (xs hd) "[>Hs H1]".
    wp_load. iMod ("Hclose" with "[Hs H1]").
    { iNext. iFrame. iExists xs, hd. iFrame. }
    iModIntro. wp_let. wp_alloc l as "Hl".
    wp_let. wp_bind (CmpXchg _ _ _)%E.
    iInv N as "H1" "Hclose".
    iDestruct "H1" as (xs' hd') "[>Hs H1]".
    destruct (decide (hd = hd')) as [->|Hneq].
    - wp_cmpxchg_suc.
      iMod (inv_alloc N _ (R x) with "[HRx]") as "#HRx"; first eauto.
      iMod ("Hclose" with "[Hs Hl H1]").
      { iNext. iFrame. iExists (x::xs'), l.
        iFrame. simpl. iExists hd', 1%Qp. iFrame.
        by iFrame "#". }
      iModIntro. wp_pures. by iApply "HΦ".
    - wp_cmpxchg_fail.
      iMod ("Hclose" with "[Hs H1]").
      { iNext. iFrame. iExists (xs'), hd'. iFrame. }
      iModIntro. wp_pures. iApply ("IH" with "HRx").
      by iNext.
  Qed.

End proofs.
