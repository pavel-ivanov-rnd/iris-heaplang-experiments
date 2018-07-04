From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang proofmode notation.
From iris.algebra Require Import excl.
Set Default Proof Using "Type".

From iris_examples.concurrent_stacks Require Import spec.

(** Stack 3: No helping, view-shift spec. *)

Definition mk_stack : val :=
  λ: "_",
  let: "r" := ref NONEV in
  (rec: "pop" "n" :=
       (match: !"r" with
          NONE => NONE
        | SOME "hd" =>
          if: CAS "r" (SOME "hd") (Snd !"hd")
          then SOME (Fst !"hd")
          else "pop" "n"
        end),
    rec: "push" "n" :=
        let: "r'" := !"r" in
        let: "r''" := SOME (Alloc ("n", "r'")) in
        if: CAS "r" "r'" "r''"
        then #()
        else "push" "n").

Section stack_works.
  Context `{!heapG Σ}.
  Implicit Types l : loc.

  Fixpoint is_stack xs v : iProp Σ :=
    (match xs with
     | [] => ⌜v = NONEV⌝
     | x :: xs => ∃ q (l : loc) (t : val), ⌜v = SOMEV #l ⌝ ∗ l ↦{q} (x, t) ∗ is_stack xs t
     end)%I.

  Definition stack_inv P v :=
    (∃ l v' xs, ⌜v = #l⌝ ∗ l ↦ v' ∗ is_stack xs v' ∗ P xs)%I.

  Lemma is_stack_disj xs v :
      is_stack xs v -∗ is_stack xs v ∗ (⌜v = NONEV⌝ ∨ ∃ q (l : loc) (h t : val), ⌜v = SOMEV #l⌝ ∗ l ↦{q} (h, t)).
  Proof.
    iIntros "Hstack".
    destruct xs.
    - iSplit; try iLeft; auto.
    - simpl. iDestruct "Hstack" as (q l t) "[-> [[Hl Hl'] Hstack]]".
      iSplitR "Hl"; eauto 10 with iFrame.
  Qed.
  Lemma is_stack_unboxed xs v :
    is_stack xs v -∗ ⌜val_is_unboxed v⌝.
  Proof.
    iIntros "Hstack". iDestruct (is_stack_disj with "Hstack") as "[_ [->|Hdisj]]".
    - done.
    - iDestruct "Hdisj" as (???? ->) "_". done.
  Qed.

  Lemma is_stack_uniq : ∀ xs ys v,
      is_stack xs v ∗ is_stack ys v -∗ ⌜xs = ys⌝.
  Proof.
    induction xs, ys; iIntros (v') "[Hstack1 Hstack2]"; auto.
    - iDestruct "Hstack1" as "%".
      iDestruct "Hstack2" as (???) "[% _]".
      subst.
      discriminate.
    - iDestruct "Hstack2" as "%".
      iDestruct "Hstack1" as (???) "[% _]".
      subst.
      discriminate.
    - simpl. iDestruct "Hstack1" as (q1 l1 t) "[% [Hl1 Hstack1]]".
      iDestruct "Hstack2" as (q2 l2 t') "[% [Hl2 Hstack2]]".
      subst; injection H0; intros; subst; clear H0.
      iDestruct (mapsto_agree with "Hl1 Hl2") as %[= -> ->].
      iDestruct (IHxs with "[Hstack1 Hstack2]") as "%". by iFrame.
      subst; auto.
  Qed.

  Lemma is_stack_empty : ∀ xs,
      is_stack xs NONEV -∗ ⌜xs = []⌝.
  Proof.
    iIntros (xs) "Hstack".
    destruct xs; auto.
    iDestruct "Hstack" as (?? t) "[% rest]".
    discriminate.
  Qed.
  Lemma is_stack_cons : ∀ xs l,
      is_stack xs (SOMEV #l) -∗
               is_stack xs (SOMEV #l) ∗ ∃ q h t ys, ⌜xs = h :: ys⌝ ∗ l ↦{q} (h, t).
  Proof.
    iIntros ([|x xs] l) "Hstack".
    - iDestruct "Hstack" as "%"; discriminate.
    - simpl. iDestruct "Hstack" as (q l' t') "[% [[Hl Hl'] Hstack]]".
      injection H; intros; subst; clear H.
      iSplitR "Hl'"; eauto 10 with iFrame.
  Qed.

  (* Whole-stack invariant (P). However:
     - The resources for the successful and failing pop must be disjoint.
       Instead, there should be a normal conjunction between them.
     Open question: How does this relate to a logically atomic spec? *)
  Theorem stack_works ι P Q Q' Q'' (Φ : val → iProp Σ) :
    ▷ (∀ (f₁ f₂ : val),
        (□((∀ v vs, P (v :: vs) ={⊤∖↑ι}=∗ Q v ∗ P vs) ∧ (* pop *)
            (P [] ={⊤∖↑ι}=∗ Q' ∗ P []) -∗
            WP f₁ #() {{ v, (∃ (v' : val), v ≡ SOMEV v' ∗ Q v') ∨ (v ≡ NONEV ∗ Q')}}))
         -∗ (∀ (v : val), (* push *)
               □ ((∀ vs, P vs ={⊤∖↑ι}=∗ P (v :: vs) ∗ Q'') -∗
                  WP f₂ v {{ v, Q'' }}))
         -∗ Φ (f₁, f₂)%V)%I
    -∗ P []
    -∗ WP mk_stack #()  {{ Φ }}.
  Proof.
    iIntros "HΦ HP".
    rename ι into N.
    wp_let.
    wp_alloc l as "Hl".
    iMod (inv_alloc N _ (stack_inv P #l) with "[Hl HP]") as "#Istack".
    { iNext; iExists l, (InjLV #()), []; iSplit; iFrame; auto. }
    wp_let.
    iApply "HΦ".
    - iIntros "!# Hcont".
      iLöb as "IH".
      wp_rec.
      wp_bind (! _)%E.
      iInv N as "Hstack" "Hclose".
      iDestruct "Hstack" as (l' v' xs) "[>% [Hl' [Hstack HP]]]".
      injection H; intros; subst; clear H.
      wp_load.
      iDestruct (is_stack_disj with "[Hstack]") as "[Hstack H]"; auto.
      iDestruct "H" as "[% | H]".
      * subst.
        iDestruct (is_stack_empty with "Hstack") as "%".
        subst.
        iDestruct "Hcont" as "[_ Hfail]".
        iMod ("Hfail" with "HP") as "[HQ' HP]".
        iMod ("Hclose" with "[Hl' Hstack HP]").
        { iExists l', (InjLV #()), []; iSplit; iFrame; auto. }
        iModIntro.
        wp_match.
        iRight; auto.
      * iDestruct "H" as (q l h t) "[% Hl]".
        subst.
        iMod ("Hclose" with "[Hl' Hstack HP]").
        { iExists l', _, xs; iSplit; iFrame; auto. }
        iModIntro.

        assert (to_val (h, t)%V = Some (h, t)%V) by apply to_of_val.
        assert (is_Some (to_val (h, t)%V)) by (exists (h, t)%V; auto).
        wp_match.
        unfold subst; simpl; fold of_val.

        wp_load.
        wp_proj.
        wp_bind (CAS _ _ _).
        iInv N as "Hstack" "Hclose".
        iDestruct "Hstack" as (l'' v' ys) "[>% [Hl'' [Hstack HP]]]".
        injection H1; intros; subst; clear H1.
        assert (Decision (v' = InjRV #l%V)) as Heq by apply val_eq_dec.
        destruct Heq.
      + subst.
        wp_cas_suc. destruct ys as [|y ys]; simpl.
        { iDestruct "Hstack" as %?. done. }
        iDestruct "Hstack" as (q'' l' t'') "[% [Hl' Hstack]]".
        injection H1; intros; subst; clear H1.
        iDestruct "Hcont" as "[Hsucc _]".
        iDestruct ("Hsucc" with "[HP]") as "> [HQ HP]"; auto.
        iDestruct (mapsto_agree with "Hl Hl'") as %[= -> ->].
        iMod ("Hclose" with "[Hl'' Hl' Hstack HP]").
        { iExists l''. eauto 10 with iFrame. }
        iModIntro.
        wp_if.
        wp_load.
        wp_proj.
        iLeft; iExists _; auto.
      + wp_cas_fail.
        iMod ("Hclose" with "[Hl'' Hstack HP]").
        { iExists l'', v', ys; iSplit; iFrame; auto. }
        iModIntro.
        wp_if.
        iApply ("IH" with "Hcont").
    - iIntros (v) "!# Hpush".
      iLöb as "IH".
      wp_rec.
      wp_bind (! _)%E.
      iInv N as "Hstack" "Hclose".
      iDestruct "Hstack" as (l' v' ys) "[>% [Hl' [Hstack HP]]]".
      injection H; intros; subst; clear H.
      wp_load.
      iMod ("Hclose" with "[Hl' Hstack HP]").
      { iExists l', v', ys; iSplit; iFrame; auto. }
      iModIntro.
      wp_let.
      wp_alloc lp as "Hlp".
      wp_let.
      wp_bind (CAS _ _ _).
      iInv N as "Hstack" "Hclose".
      iDestruct "Hstack" as (l'' v'' xs) "[>% [Hl'' [Hstack HP]]]".
      injection H; intros; subst; clear H.
      iDestruct (is_stack_unboxed with "Hstack") as "#>%".
      assert (Decision (v' = v''%V)) as Heq by apply val_eq_dec.
      destruct Heq.
      + subst. wp_cas_suc.
        iDestruct ("Hpush" with "[HP]") as "> [HP HQ]"; auto.
        iMod ("Hclose" with "[Hl'' Hlp Hstack HP]").
        { iExists l'', _, _. iFrame. simpl. eauto 10 with iFrame. }
        iModIntro.
        wp_if.
        done.
      + wp_cas_fail.
        iMod ("Hclose" with "[Hl'' Hstack HP]").
        { iExists l'', v'', xs; iSplit; iFrame; auto. }
        iModIntro.
        wp_if.
        iApply ("IH" with "Hpush").
  Qed.

  Program Definition is_concurrent_stack : concurrent_stack Σ :=
    {| spec.mk_stack := mk_stack |}.
  Next Obligation.
    iIntros (????? Φ) "HP HΦ". iApply (stack_works with "[HΦ] HP").
    iNext. iIntros (f₁ f₂) "Hpop Hpush". iApply "HΦ". iFrame.
  Qed.
End stack_works.
