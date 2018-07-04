(** THIS FILE CURRENTLY DOES NOT COMPILE because it has not been ported to the
stricter CAS requirements yet. *)
From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang proofmode notation.
From iris.algebra Require Import excl.

From iris_examples.concurrent_stacks Require Import spec.

(** Stack 3: Helping, view-shift spec. *)

Definition mk_offer : val :=
  λ: "v", ("v", ref #0).
Definition revoke_offer : val :=
  λ: "v", if: CAS (Snd "v") #0 #2 then SOME (Fst "v") else NONE.
Definition take_offer : val :=
  λ: "v", if: CAS (Snd "v") #0 #1 then SOME (Fst "v") else NONE.

Definition mailbox : val :=
  λ: "_",
  let: "r" := ref NONEV in
  (rec: "put" "v" :=
     let: "off" := mk_offer "v" in
     "r" <- SOME "off";;
     revoke_offer "off",
   rec: "get" "n" :=
     let: "offopt" := !"r" in
     match: "offopt" with
       NONE => NONE
     | SOME "x" => if: CAS (Snd "x") #0 #1 then SOME (Fst "x") else NONE
     end
  ).

Definition mk_stack : val :=
  λ: "_",
  let: "mailbox" := mailbox #() in
  let: "put" := Fst "mailbox" in
  let: "get" := Snd "mailbox" in
  let: "r" := ref NONEV in
  (rec: "pop" "n" :=
     match: "get" #() with
       NONE =>
       (match: !"r" with
          NONE => NONE
        | SOME "hd" =>
          if: CAS "r" (SOME "hd") (Snd "hd")
          then SOME (Fst "hd")
          else "pop" "n"
        end)
     | SOME "x" => SOME "x"
     end,
    rec: "push" "n" :=
      match: "put" "n" with
        NONE => #()
      | SOME "n" =>
        let: "r'" := !"r" in
        let: "r''" := SOME ("n", "r'") in
        if: CAS "r" "r'" "r''"
        then #()
        else "push" "n"
      end).

Definition channelR := exclR unitR.
Class channelG Σ := { channel_inG :> inG Σ channelR }.
Definition channelΣ : gFunctors := #[GFunctor channelR].
Instance subG_channelΣ {Σ} : subG channelΣ Σ → channelG Σ.
Proof. solve_inG. Qed.

Section side_channel.
  Context `{!heapG Σ, !channelG Σ} (N : namespace).

  Implicit Types l : loc.

  Definition stages γ (P : list val → iProp Σ) (Q : iProp Σ) l (v : val):=
    ((l ↦ #0 ∗ (∀ vs, P vs ={⊤ ∖ ↑N}=∗ P (v :: vs) ∗ Q))
     ∨ (l ↦ #1 ∗ Q)
     ∨ (l ↦ #1 ∗ own γ (Excl ()))
     ∨ (l ↦ #2 ∗ own γ (Excl ())))%I.

  Definition is_offer γ (P : list val → iProp Σ) Q (v : val) : iProp Σ :=
    (∃ v' l, ⌜v = (v', #l)%V⌝ ∗ inv (N .@ "offer_inv")(stages γ P Q l v'))%I.

  Definition mailbox_inv (P : list val → iProp Σ) Q (v : val) : iProp Σ :=
    (∃ l, ⌜v = #l⌝ ∗ (l ↦ NONEV ∨ (∃ v' γ, l ↦ SOMEV v' ∗ is_offer γ P Q v')))%I.
End side_channel.
Section stack_works.
  Context `{!heapG Σ}.

  Implicit Types l : loc.

  Fixpoint is_stack xs v : iProp Σ :=
    (match xs with
     | [] => ⌜v = NONEV⌝
     | x :: xs => ∃ (t : val), ⌜v = SOMEV (x, t)%V⌝ ∗ is_stack xs t
     end)%I.

  Definition stack_inv P v :=
    (∃ l v' xs, ⌜v = #l⌝ ∗ l ↦ v' ∗ is_stack xs v' ∗ P xs)%I.

  Lemma is_stack_disj xs v :
      is_stack xs v -∗ is_stack xs v ∗ (⌜v = NONEV⌝ ∨ ∃ (h t : val), ⌜v = SOMEV (h, t)%V⌝).
  Proof.
    iIntros "Hstack".
    destruct xs.
    - iSplit; try iLeft; auto.
    - iSplit; auto; iRight; iDestruct "Hstack" as (t) "[% Hstack]";
      iExists v0, t; auto.
  Qed.

  Lemma is_stack_uniq : ∀ xs ys v,
      is_stack xs v ∗ is_stack ys v -∗ ⌜xs = ys⌝.
  Proof.
    induction xs, ys; iIntros (v') "[Hstack1 Hstack2]"; auto.
    - iDestruct "Hstack1" as "%".
      iDestruct "Hstack2" as (t) "[% Hstack2]".
      subst.
      discriminate.
    - iDestruct "Hstack2" as "%".
      iDestruct "Hstack1" as (t) "[% Hstack1]".
      subst.
      discriminate.
    - iDestruct "Hstack1" as (t) "[% Hstack1]".
      iDestruct "Hstack2" as (t') "[% Hstack2]".
      subst; injection H0; intros; subst.
      iDestruct (IHxs with "[Hstack1 Hstack2]") as "%".
        by iSplitL "Hstack1".
      subst; auto.
  Qed.

  Lemma is_stack_empty : ∀ xs,
      is_stack xs (InjLV #()) -∗ ⌜xs = []⌝.
  Proof.
    iIntros (xs) "Hstack".
    destruct xs; auto.
    iDestruct "Hstack" as (t) "[% rest]".
    discriminate.
  Qed.
  Lemma is_stack_cons : ∀ xs h t,
      is_stack xs (InjRV (h, t)%V) -∗
               is_stack xs (InjRV (h, t)%V) ∗ ∃ ys, ⌜xs = h :: ys⌝.
  Proof.
    destruct xs; iIntros (h t) "Hstack".
    - iDestruct "Hstack" as "%"; discriminate.
    - iSplit; [auto | iExists xs].
      iDestruct "Hstack" as (t') "[% Hstack]".
      injection H; intros; subst; auto.
  Qed.

  (* Whole-stack invariant (P). *)
  Theorem stack_works {channelG0 : channelG Σ} N P Q Q' Q'' (Φ : val → iProp Σ) :
    ▷ (∀ (f₁ f₂ : val),
        (□(((∀ v vs, P (v :: vs) ={⊤ ∖ ↑ N}=∗ Q v ∗ P vs)
            ∧ (P [] ={⊤ ∖ ↑ N}=∗ Q' ∗ P []) -∗
            WP f₁ #() {{ v, (∃ (v' : val), v ≡ SOMEV v' ∗ Q v') ∨ (v ≡ NONEV ∗ Q')}}))
         ∧ (∀ (v : val),
               □ ((∀ vs, P vs ={⊤ ∖ ↑ N}=∗ P (v :: vs) ∗ Q'') -∗ WP f₂ v {{ v, Q'' }})))
         -∗ Φ (f₁, f₂)%V)%I
    -∗ P []
    -∗ WP mk_stack #()  {{ Φ }}.
  Proof.
    iIntros "HΦ HP".
    wp_let.
    wp_let.
    wp_alloc m as "Hm".
    iMod (inv_alloc (N .@ "mailbox_inv") _ (mailbox_inv N P Q'' #m) with "[Hm]") as "#Imailbox".
    iExists m; iSplit; auto.
    wp_let.
    wp_let.
    wp_proj.
    wp_let.
    wp_proj.
    wp_let.
    wp_alloc l as "Hl".
    iMod (inv_alloc (N .@ "stack_inv") _ (stack_inv P #l) with "[Hl HP]") as "#Istack".
    { iNext; iExists l, (InjLV #()), []; iSplit; iFrame; auto. }
    wp_let.
    iApply "HΦ"; iSplit.
    - iIntros "!# Hcont".
      iLöb as "IH".
      wp_rec.
      wp_rec.
      wp_bind (! _)%E.
      iInv (N .@ "mailbox_inv") as "Hmail" "Hclose".
      iDestruct "Hmail" as (m') "[>% H]".
      injection H; intros; subst.
      iDestruct "H" as "[Hm' | H]".
      * wp_load.
        iMod ("Hclose" with "[Hm']").
        { iExists m'; iSplit; auto. }
        iModIntro.
        wp_let.
        wp_match.
        wp_match.
        wp_bind (! _)%E.
        iInv (N .@ "stack_inv") as "Hstack" "Hclose".
        iDestruct "Hstack" as (l' v' xs) "[>% [Hl' [Hstack HP]]]".
        injection H0; intros; subst.
        wp_load.
        iDestruct (is_stack_disj with "[Hstack]") as "[Hstack H]"; auto.
        iDestruct "H" as "[% | H]".
        + subst.
          iDestruct (is_stack_empty with "Hstack") as "%".
          subst.
          iDestruct "Hcont" as "[_ Hfail]".
          iDestruct ("Hfail" with "HP") as "Hfail".
          iDestruct (fupd_mask_mono with "Hfail") as "Hfail";
          last iMod "Hfail" as "[HQ' HP]"; first by solve_ndisj.
          iMod ("Hclose" with "[Hl' Hstack HP]").
          { iExists l', (InjLV #()), []; iSplit; iFrame; auto. }
          iModIntro.
          wp_match.
          iRight; auto.
        + iDestruct "H" as (h t) "%".
          subst.
          iMod ("Hclose" with "[Hl' Hstack HP]").
          { iExists l', (InjRV (h, t)), xs; iSplit; iFrame; auto. }
          iModIntro.

          assert (to_val (h, t)%V = Some (h, t)%V) by apply to_of_val.
          assert (is_Some (to_val (h, t)%V)) by (exists (h, t)%V; auto).
          wp_match.
          unfold subst; simpl; fold of_val.

          wp_proj.
          wp_bind (CAS _ _ _).
          iInv (N .@ "stack_inv") as "Hstack" "Hclose".
          iDestruct "Hstack" as (l'' v' ys) "[>% [Hl'' [Hstack HP]]]".
          injection H3; intros; subst.
          assert (Decision (v' = InjRV (h, t)%V)) as Heq by apply val_eq_dec.
          destruct Heq.
          ++ wp_cas_suc.
             subst.
             iDestruct (is_stack_cons with "Hstack") as "[Hstack H]".
             iDestruct "H" as (ys') "%"; subst.
             iDestruct "Hstack" as (t') "[% Hstack]".
             injection H4; intros; subst.
             iDestruct "Hcont" as "[Hsucc _]".
             iDestruct ("Hsucc" with "HP") as "Hsucc".
             iDestruct (fupd_mask_mono with "Hsucc") as "Hsucc";
               last iMod "Hsucc" as "[HQ HP]"; first by solve_ndisj.
             iMod ("Hclose" with "[Hl'' Hstack HP]").
             { iExists l'', t', ys'; iSplit; iFrame; auto. }
             iModIntro.
             wp_if.
             wp_proj.
             iLeft; iExists h; auto.
          ++ wp_cas_fail.
             iMod ("Hclose" with "[Hl'' Hstack HP]").
             { iExists l'', v', ys; iSplit; iFrame; auto. }
             iModIntro.
             wp_if.
             iApply ("IH" with "Hcont").
      * iDestruct "H" as (v' γ') "[Hm' Hstages]".
        wp_load.
        iDestruct "Hstages" as (v'' l') "[% #Hstages]".
        iMod ("Hclose" with "[Hm' Hstages]").
        { iExists m'. iSplit; auto; iRight.
          iExists v', γ'; iFrame. iExists v'', l'; iSplit; auto. }
        iModIntro.
        wp_let.
        wp_match.
        unfold take_offer.
        subst.
        wp_proj.
        wp_bind (CAS _ _ _).
        iInv (N .@ "offer_inv") as "Hstage" "Hclose".
        iDestruct "Hstage" as "[H | [H | [H | H]]]".
        + iDestruct "H" as "[Hl' Hmove]".
          iInv (N .@ "stack_inv") as "Hstack" "Hclose2".
          wp_cas_suc.
          iDestruct "Hstack" as (l'' v' xs) "[% [Hl'' [Hstack HP]]]".
          iDestruct ("Hmove" with "HP") as "Hmove".
          iDestruct (fupd_mask_mono with "Hmove") as "Hmove";
            last iMod "Hmove" as "[HP HQ'']"; first solve_ndisj.
          iDestruct "Hcont" as "[Hsucc _]".
          iDestruct ("Hsucc" with "HP") as "Hsucc".
          iDestruct (fupd_mask_mono with "Hsucc") as "Hsucc";
            last (iMod "Hsucc" as "[HQ HP]"); first solve_ndisj.
          iMod ("Hclose2" with "[Hl'' Hstack HP]").
          { iExists l'', v', xs; iSplit; iFrame; auto. }
          iModIntro.
          iMod ("Hclose" with "[Hl' HQ'']").
          { iRight; iLeft; iFrame. }
          iModIntro.
          wp_if.
          wp_proj.

          assert (to_val v'' = Some v'') by apply to_of_val.
          assert (is_Some (to_val v'')) by (exists v''; auto).
          assert (to_val (InjRV v'') = Some (InjRV v'')) by apply to_of_val.
          assert (is_Some (to_val (InjRV v''))) by (exists (InjRV v''); auto).
          wp_match.
          iLeft; iExists v''; iFrame; auto.
        + iDestruct "H" as "[Hl' HQ'']".
          wp_cas_fail.
          iMod ("Hclose" with "[Hl' HQ'']").
          { iRight; iLeft; iFrame. }
          iModIntro.
          wp_if.
          wp_match.
          wp_bind (! _)%E.
          iInv (N .@ "stack_inv") as "Hstack" "Hclose".
          iDestruct "Hstack" as (l'' v''' xs) "[>% [Hl' [Hstack HP]]]"; simplify_eq.
          wp_load.
          iDestruct (is_stack_disj with "[Hstack]") as "[Hstack H]"; auto.
          iDestruct "H" as "[% | H]".
          ** subst.
             iDestruct (is_stack_empty with "Hstack") as "%".
             subst.
             iDestruct "Hcont" as "[_ Hfail]".
             iDestruct ("Hfail" with "HP") as "Hfail".
             iDestruct (fupd_mask_mono with "Hfail") as "Hfail";
               last iMod "Hfail" as "[HQ' HP]"; first by solve_ndisj.

             iMod ("Hclose" with "[Hl' Hstack HP]").
             { iExists l'', (InjLV #()), []; iSplit; iFrame; auto. }
             iModIntro.
             wp_match.
             iRight; auto.
          ** iDestruct "H" as (h t) "%".
             subst.
             iMod ("Hclose" with "[Hl' Hstack HP]").
             { iExists l'', (InjRV (h, t)), xs; iSplit; iFrame; auto. }
             iModIntro.

             assert (to_val (h, t)%V = Some (h, t)%V) by apply to_of_val.
             assert (is_Some (to_val (h, t)%V)) by (exists (h, t)%V; auto).
             wp_match.
             unfold subst; simpl; fold of_val.

             wp_proj.
             wp_bind (CAS _ _ _).
             iInv (N .@ "stack_inv") as "Hstack" "Hclose".
             iDestruct "Hstack" as (l''' v''' ys) "[>% [Hl''' [Hstack HP]]]"; simplify_eq.
             destruct (decide (v''' = InjRV (h, t)%V)).
             ++ wp_cas_suc.
                subst.
                iDestruct (is_stack_cons with "Hstack") as "[Hstack H]".
                iDestruct "H" as (ys') "%"; subst.
                iDestruct "Hstack" as (t') "[% Hstack]"; simplify_eq.
                iDestruct "Hcont" as "[Hsucc _]".
                iDestruct ("Hsucc" with "HP") as "Hsucc".
                iDestruct (fupd_mask_mono with "Hsucc") as "Hsucc";
                  last iMod "Hsucc" as "[HQ HP]"; first by solve_ndisj.
                iMod ("Hclose" with "[Hl''' Hstack HP]").
                { iExists l''', t', ys'; iSplit; iFrame; auto. }
                iModIntro.
                wp_if.
                wp_proj.
                iLeft; iExists h; auto.
             ++ wp_cas_fail.
                iMod ("Hclose" with "[Hl''' Hstack HP]").
                { iExists l''', v''', ys; iSplit; iFrame; auto. }
                iModIntro.
                wp_if.
                iApply ("IH" with "Hcont").
        + iDestruct "H" as "[Hl' Hγ']".
          wp_cas_fail.
          iMod ("Hclose" with "[Hl' Hγ']").
          { iRight; iRight; iLeft; iFrame. }
          iModIntro.
          wp_if.
          wp_match.
          wp_bind (! _)%E.
          iInv (N .@ "stack_inv") as "Hstack" "Hclose".
          iDestruct "Hstack" as (l'' v''' xs) "[>% [Hl' [Hstack HP]]]"; simplify_eq.
          wp_load.
          iDestruct (is_stack_disj with "[Hstack]") as "[Hstack H]"; auto.
          iDestruct "H" as "[% | H]".
          ** subst.
             iDestruct (is_stack_empty with "Hstack") as "%".
             subst.
             iDestruct "Hcont" as "[_ Hfail]".
             iDestruct ("Hfail" with "HP") as "Hfail".
             iDestruct (fupd_mask_mono with "Hfail") as "Hfail";
               last iMod "Hfail" as "[HQ HP]"; first by solve_ndisj.
             iMod ("Hclose" with "[Hl' Hstack HP]").
             { iExists l'', (InjLV #()), []; iSplit; iFrame; auto. }
             iModIntro.
             wp_match.
             iRight; auto.
          ** iDestruct "H" as (h t) "%".
             subst.
             iMod ("Hclose" with "[Hl' Hstack HP]").
             { iExists l'', (InjRV (h, t)), xs; iSplit; iFrame; auto. }
             iModIntro.

             assert (to_val (h, t)%V = Some (h, t)%V) by apply to_of_val.
             assert (is_Some (to_val (h, t)%V)) by (exists (h, t)%V; auto).
             wp_match.
             unfold subst; simpl; fold of_val.

             wp_proj.
             wp_bind (CAS _ _ _).
             iInv (N .@ "stack_inv") as "Hstack" "Hclose".
             iDestruct "Hstack" as (l''' v''' ys) "[>% [Hl''' [Hstack HP]]]"; simplify_eq.
             destruct (decide (v''' = InjRV (h, t)%V)).
             ++ wp_cas_suc.
                subst.
                iDestruct (is_stack_cons with "Hstack") as "[Hstack H]".
                iDestruct "H" as (ys') "%"; subst.
                iDestruct "Hstack" as (t') "[% Hstack]"; simplify_eq.
                iDestruct "Hcont" as "[Hsucc _]".
                iDestruct ("Hsucc" with "HP") as "Hsucc".
                iDestruct (fupd_mask_mono with "Hsucc") as "Hsucc";
                  last iMod "Hsucc" as "[HQ HP]"; first by solve_ndisj.
                iMod ("Hclose" with "[Hl''' Hstack HP]").
                { iExists l''', t', ys'; iSplit; iFrame; auto. }
                iModIntro.
                wp_if.
                wp_proj.
                iLeft; iExists h; auto.
             ++ wp_cas_fail.
                iMod ("Hclose" with "[Hl''' Hstack HP]").
                { iExists l''', v''', ys; iSplit; iFrame; auto. }
                iModIntro.
                wp_if.
                iApply ("IH" with "Hcont").

        + iDestruct "H" as "[Hl' Hγ']".
          wp_cas_fail.
          iMod ("Hclose" with "[Hl' Hγ']").
          { iRight; iRight; iRight; iFrame. }
          iModIntro.
          wp_if.
          wp_match.
          wp_bind (! _)%E.
          iInv (N .@ "stack_inv") as "Hstack" "Hclose".
          iDestruct "Hstack" as (l'' v''' xs) "[>% [Hl' [Hstack HP]]]"; simplify_eq.
          wp_load.
          iDestruct (is_stack_disj with "[Hstack]") as "[Hstack H]"; auto.
          iDestruct "H" as "[% | H]".
          ** subst.
             iDestruct (is_stack_empty with "Hstack") as "%".
             subst.
             iDestruct "Hcont" as "[_ Hfail]".
             iDestruct ("Hfail" with "HP") as "Hfail".
             iDestruct (fupd_mask_mono with "Hfail") as "Hfail";
               last iMod "Hfail" as "[HQ HP]"; first by solve_ndisj.
             iMod ("Hclose" with "[Hl' Hstack HP]").
             { iExists l'', (InjLV #()), []; iSplit; iFrame; auto. }
             iModIntro.
             wp_match.
             iRight; auto.
          ** iDestruct "H" as (h t) "%".
             subst.
             iMod ("Hclose" with "[Hl' Hstack HP]").
             { iExists l'', (InjRV (h, t)), xs; iSplit; iFrame; auto. }
             iModIntro.

             assert (to_val (h, t)%V = Some (h, t)%V) by apply to_of_val.
             assert (is_Some (to_val (h, t)%V)) by (exists (h, t)%V; auto).
             wp_match.
             unfold subst; simpl; fold of_val.

             wp_proj.
             wp_bind (CAS _ _ _).
             iInv (N .@ "stack_inv") as "Hstack" "Hclose".
             iDestruct "Hstack" as (l''' v''' ys) "[>% [Hl''' [Hstack HP]]]"; simplify_eq.
             destruct (decide (v''' = InjRV (h, t)%V)).
             ++ wp_cas_suc.
                subst.
                iDestruct (is_stack_cons with "Hstack") as "[Hstack H]".
                iDestruct "H" as (ys') "%"; subst.
                iDestruct "Hstack" as (t') "[% Hstack]"; simplify_eq.
                iDestruct "Hcont" as "[Hsucc _]".
                iDestruct ("Hsucc" with "HP") as "Hsucc".
                iDestruct (fupd_mask_mono with "Hsucc") as "Hsucc";
                  last iMod "Hsucc" as "[HQ HP]"; first by solve_ndisj.
                iMod ("Hclose" with "[Hl''' Hstack HP]").
                { iExists l''', t', ys'; iSplit; iFrame; auto. }
                iModIntro.
                wp_if.
                wp_proj.
                iLeft; iExists h; auto.
             ++ wp_cas_fail.
                iMod ("Hclose" with "[Hl''' Hstack HP]").
                { iExists l''', v''', ys; iSplit; iFrame; auto. }
                iModIntro.
                wp_if.
                iApply ("IH" with "Hcont").
    - iIntros (v) "!# Hpush".
      iLöb as "IH".
      wp_rec.
      wp_rec.
      wp_lam.
      wp_alloc s as "Hs".
      wp_let.
      wp_bind (_ <- _)%E.
      iInv (N .@ "mailbox_inv") as "Hmail" "Hclose".
      iDestruct "Hmail" as (m') "[>% Hmail]"; simplify_eq.
      iMod (own_alloc (Excl ())) as (γ) "Hγ". done.
      iMod (inv_alloc (N .@ "offer_inv") _ (stages N γ P Q'' s v) with "[Hs Hpush]") as "#Istages".
      { iLeft; iFrame; auto. }
      iDestruct "Hmail" as "[H | H]".
      * wp_store.
        iMod ("Hclose" with "[H]").
        { iExists m'. iSplit; auto; iRight; iExists (v, #s)%V, γ.
          iFrame. iExists v, s; iSplit; auto. }
        iModIntro.
        wp_let.
        wp_lam.
        wp_proj.
        wp_bind (CAS _ _ _).
        iInv (N .@ "offer_inv") as "Hstages" "Hclose".
        iDestruct "Hstages" as "[H | [H | [H | H]]]".
        + iDestruct "H" as "[Hs Hpush]".
          wp_cas_suc.
          iMod ("Hclose" with "[Hs Hγ]").
          { iRight; iRight; iRight; iFrame. }
          iModIntro.
          wp_if.
          wp_proj.
          wp_match.

          wp_bind (! _)%E.
          iInv (N .@ "stack_inv") as "Hstack" "Hclose".
          iDestruct "Hstack" as (l' v' ys) "[>% [Hl' [Hstack HP]]]"; simplify_eq.
          wp_load.
          iMod ("Hclose" with "[Hl' Hstack HP]").
          { iExists l', v', ys; iSplit; iFrame; auto. }
          iModIntro.
          wp_let.
          wp_let.
          wp_bind (CAS _ _ _).
          iInv (N .@ "stack_inv") as "Hstack" "Hclose".
          iDestruct "Hstack" as (l'' v'' xs) "[>% [Hl'' [Hstack HP]]]"; simplify_eq.
          destruct (decide (v' = v''%V)).
          ++ wp_cas_suc.
             iDestruct ("Hpush" with "HP") as "Hpush".
             iDestruct (fupd_mask_mono with "Hpush") as "Hpush";
               last iMod "Hpush" as "[HP HQ]"; first by solve_ndisj.
             iMod ("Hclose" with "[Hl'' Hstack HP]").
             { iExists l'', (InjRV (v, v')), (v :: xs); iSplit; iFrame; auto.
               iExists v'; iSplit; subst; auto. }
             iModIntro.
             wp_if.
             done.
          ++ wp_cas_fail.
             iMod ("Hclose" with "[Hl'' Hstack HP]").
             { iExists l'', v'', xs; iSplit; iFrame; auto. }
             iModIntro.
             wp_if.
             iApply ("IH" with "Hpush").
        + iDestruct "H" as "[Hs HQ'']".
          wp_cas_fail.
          iMod ("Hclose" with "[Hs Hγ]").
          { iRight; iRight; iLeft. iFrame. }
          iModIntro.
          wp_if.
          wp_match.
          done.
        + iDestruct "H" as "[Hs Hγ']".
          wp_cas_fail.
          by iDestruct (own_valid_2 with "Hγ Hγ'") as %?.
        + iDestruct "H" as "[Hs Hγ']".
          wp_cas_fail.
          by iDestruct (own_valid_2 with "Hγ Hγ'") as %?.
    * iDestruct "H" as (v' γ') "[Hm Hoffer]".
      wp_store.
      iMod ("Hclose" with "[Hm]").
      { iExists m'. iSplit; auto; iRight; iExists (v, #s)%V, γ.
        iFrame. iExists v, s; iSplit; auto. }
      iModIntro.
      wp_let.
      wp_lam.
      wp_proj.
      wp_bind (CAS _ _ _).
      iInv (N .@ "offer_inv") as "Hstages" "Hclose".
      iDestruct "Hstages" as "[H | [H | [H | H]]]".
      + iDestruct "H" as "[Hs Hpush]".
        wp_cas_suc.
        iMod ("Hclose" with "[Hs Hγ]").
        { iRight; iRight; iRight; iFrame. }
        iModIntro.
        wp_if.
        wp_proj.

        wp_match.
        wp_bind (! _)%E.
        iInv (N .@ "stack_inv") as "Hstack" "Hclose".
        iDestruct "Hstack" as (l' v'' ys) "[>% [Hl' [Hstack HP]]]"; simplify_eq.
        wp_load.
        iMod ("Hclose" with "[Hl' Hstack HP]").
        { iExists l', v'', ys; iSplit; iFrame; auto. }
        iModIntro.
        wp_let.
        wp_let.
        wp_bind (CAS _ _ _).
        iInv (N .@ "stack_inv") as "Hstack" "Hclose".
        iDestruct "Hstack" as (l'' v''' xs) "[>% [Hl'' [Hstack HP]]]"; simplify_eq.
        destruct (decide (v'' = v'''%V)).
        ++ wp_cas_suc.
           iDestruct ("Hpush" with "HP") as "Hpush".
           iDestruct (fupd_mask_mono with "Hpush") as "Hpush";
             last iMod "Hpush" as "[HP HQ]"; first by solve_ndisj.
           iMod ("Hclose" with "[Hl'' Hstack HP]").
           { iExists l'', (InjRV (v, v'')), (v :: xs); iSplit; iFrame; auto.
             iExists v''; iSplit; subst; auto. }
           iModIntro.
           wp_if.
           done.
        ++ wp_cas_fail.
           iMod ("Hclose" with "[Hl'' Hstack HP]").
           { iExists l'', v''', xs; iSplit; iFrame; auto. }
           iModIntro.
           wp_if.
           iApply ("IH" with "Hpush").
      + iDestruct "H" as "[Hs HQ'']".
        wp_cas_fail.
        iMod ("Hclose" with "[Hs Hγ]").
        { iRight; iRight; iLeft. iFrame. }
        iModIntro.
        wp_if.
        wp_match.
        done.
      + iDestruct "H" as "[Hs Hγ']".
        wp_cas_fail.
        by iDestruct (own_valid_2 with "Hγ Hγ'") as %?.
      + iDestruct "H" as "[Hs Hγ']".
        wp_cas_fail.
        by iDestruct (own_valid_2 with "Hγ Hγ'") as %?.
  Qed.

  Program Definition is_concurrent_stack `{!channelG Σ} : concurrent_stack Σ :=
    {| spec.mk_stack := mk_stack |}.
  Next Obligation.
    iIntros (?????? Φ) "HP HΦ". iApply (stack_works with "[HΦ] HP").
    iNext. iIntros (f₁ f₂) "#[Hpop Hpush]". iApply "HΦ". iFrame "#".
  Qed.
End stack_works.
