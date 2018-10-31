From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.algebra Require Import agree list.
From iris.heap_lang Require Import assert proofmode notation.

From iris_examples.concurrent_stacks Require Import spec.

Set Default Proof Using "Type".

(** Stack 1: No helping, bag spec. *)

Definition mk_stack : val :=
  λ: "_",
  let: "r" := ref NONEV in
  (rec: "pop" "n" :=
     match: !"r" with
       NONE => NONE
     | SOME "hd" =>
       if: CAS "r" (SOME "hd") (Snd !"hd")
       then SOME (Fst !"hd")
       else "pop" "n"
     end,
    rec: "push" "n" :=
       let: "r'" := !"r" in
       let: "r''" := SOME (Alloc ("n", "r'")) in
       if: CAS "r" "r'" "r''"
       then #()
       else "push" "n").

Section stacks.
  Context `{!heapG Σ}.
  Implicit Types l : loc.

  Definition oloc_to_val (h : option loc) : val :=
    match h with
    | None => NONEV
    | Some l => SOMEV #l
    end.
  Local Instance oloc_to_val_inj : Inj (=) (=) oloc_to_val.
  Proof. rewrite /Inj /oloc_to_val=>??. repeat case_match; congruence. Qed.

  Definition is_stack_pre (P : val → iProp Σ) (F : option loc -c> iProp Σ) :
     option loc -c> iProp Σ := λ v,
    (match v with
     | None => True
     | Some l => ∃ q h t, l ↦{q} (h, oloc_to_val t) ∗ P h ∗ ▷ F t
     end)%I.

  Local Instance is_stack_contr (P : val → iProp Σ): Contractive (is_stack_pre P).
  Proof.
    rewrite /is_stack_pre => n f f' Hf v.
    repeat (f_contractive || f_equiv).
    apply Hf.
  Qed.

  Definition is_stack_def (P : val -> iProp Σ) := fixpoint (is_stack_pre P).
  Definition is_stack_aux P : seal (@is_stack_def P). by eexists. Qed.
  Definition is_stack P := unseal (is_stack_aux P).
  Definition is_stack_eq P : @is_stack P = @is_stack_def P := seal_eq (is_stack_aux P).

  Definition stack_inv P l :=
    (∃ ol, l ↦ oloc_to_val ol ∗ is_stack P ol)%I.


  Lemma is_stack_unfold (P : val → iProp Σ) v :
      is_stack P v ⊣⊢ is_stack_pre P (is_stack P) v.
  Proof.
    rewrite is_stack_eq. apply (fixpoint_unfold (is_stack_pre P)).
  Qed.

  Lemma is_stack_copy (P : val → iProp Σ) ol :
      is_stack P ol -∗ is_stack P ol ∗
           (match ol with None => True | Some l => ∃ q h t, l ↦{q} (h, oloc_to_val t) end).
  Proof.
    iIntros "Hstack".
    iDestruct (is_stack_unfold with "Hstack") as "Hstack". destruct ol; last first.
    - iSplitL; try iApply is_stack_unfold; auto.
    - iDestruct "Hstack" as (q h t) "[[Hl1 Hl2] [HP Hrest]]".
      iSplitR "Hl2"; try iApply is_stack_unfold; simpl; eauto 10 with iFrame.
  Qed.

  (* Per-element invariant (i.e., bag spec). *)
  Theorem stack_works P Φ :
    ▷ (∀ (f₁ f₂ : val),
            (□ WP f₁ #() {{ v, (∃ v', v ≡ SOMEV v' ∗ P v')  ∨  v ≡ NONEV }})
         -∗ (∀ (v : val), □ (P v -∗ WP f₂ v {{ v, True }}))
         -∗ Φ (f₁, f₂)%V)%I
    -∗ WP mk_stack #()  {{ Φ }}.
  Proof.
    iIntros "HΦ".
    wp_lam.
    wp_alloc l as "Hl".
    pose proof (nroot .@ "N") as N.
    rewrite -wp_fupd.
    iMod (inv_alloc N _ (stack_inv P l) with "[Hl]") as "#Hisstack".
    { iExists None; iFrame; auto.
      iApply is_stack_unfold. auto. }
    wp_pures.
    iModIntro.
    iApply "HΦ".
    - iIntros "!#".
      iLöb as "IH".
      wp_rec.
      wp_bind (! #l)%E.
      iInv N as "Hstack" "Hclose".
      iDestruct "Hstack" as (v') "[Hl' Hstack]".
      wp_load.
      destruct v' as [l'|]; simpl; last first.
      + iMod ("Hclose" with "[Hl' Hstack]") as "_".
        { rewrite /stack_inv. eauto with iFrame. }
        iModIntro. wp_match. wp_pures. by iRight.
      + iDestruct (is_stack_copy with "Hstack") as "[Hstack Hmy]".
        iDestruct "Hmy" as (q h t) "Hl".
        iMod ("Hclose" with "[Hl' Hstack]") as "_".
        { rewrite /stack_inv. eauto with iFrame. }
        iModIntro. wp_match.
        wp_load. wp_pures.
        wp_bind (CAS _ _ _).
        iInv N as "Hstack" "Hclose".
        iDestruct "Hstack" as (v'') "[Hl'' Hstack]".
        destruct (decide (oloc_to_val v'' = oloc_to_val (Some l'))) as [->%oloc_to_val_inj|Hne].
        * simpl. wp_cas_suc.
          iDestruct (is_stack_unfold with "Hstack") as "Hstack".
          iDestruct "Hstack" as (q' h' t') "[Hl' [HP Hstack]]".
          iDestruct (mapsto_agree with "Hl Hl'") as %[= <- <-%oloc_to_val_inj].
          iMod ("Hclose" with "[Hl'' Hstack]").
          { iExists _. auto with iFrame. }
          iModIntro.
          wp_if.
          wp_load.
          wp_pures.
          eauto.
        * simpl in Hne. wp_cas_fail.
          iMod ("Hclose" with "[Hl'' Hstack]").
          { iExists v''; iFrame; auto. }
          iModIntro.
          wp_if.
          iApply "IH".
    - iIntros (v) "!# HP".
      iLöb as "IH".
      wp_rec.
      wp_bind (! _)%E.
      iInv N as "Hstack" "Hclose".
      iDestruct "Hstack" as (v') "[Hl' Hstack]".
      wp_load.
      iMod ("Hclose" with "[Hl' Hstack]").
      { iExists v'. iFrame. }
      iModIntro.
      wp_let.
      wp_alloc r'' as "Hr''".
      wp_pures. wp_bind (CAS _ _ _).
      iInv N as "Hstack" "Hclose".
      iDestruct "Hstack" as (v'') "[Hl'' Hstack]".
      wp_cas as ->%oloc_to_val_inj|_.
      + destruct v'; by right.
      + iMod ("Hclose" with "[Hl'' Hr'' HP Hstack]").
        iExists (Some r'').
        iFrame; auto.
        iNext.
        iApply is_stack_unfold.
        simpl.
        iExists _, _, v'. iFrame.
        iModIntro.
        wp_if.
        done.
      + iMod ("Hclose" with "[Hl'' Hstack]").
        iExists v''; iFrame; auto.
        iModIntro.
        wp_if.
        iApply "IH".
        done.
  Qed.
End stacks.

Program Definition is_concurrent_bag `{!heapG Σ} : concurrent_bag Σ :=
  {| spec.mk_bag := mk_stack |}.
Next Obligation.
  iIntros (??? P Φ) "_ HΦ". iApply stack_works.
  iNext. iIntros (f₁ f₂) "Hpop Hpush". iApply "HΦ". iFrame.
Qed.
