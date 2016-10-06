From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import excl.
From flatcomb Require Import sync.
Import uPred.

(* CAS, load and store to pair of locations *)
(* TODO: Make it mroe realistic by taking two parameters rather than sharing one for both locations*)
(* TODO: Eliminate the duplication of spec code *)
(* TODO: release spec of lock user *)

Definition casp_seq' (l1 l2: loc) : val :=
  λ: "vp",
     let: "oldv" := Fst "vp" in
     let: "newv" := Snd "vp" in
     if: !(Fst (#l1, #l2)) = "oldv"
       then if: !(Snd (#l1, #l2)) = "oldv"
              then (Fst (#l1, #l2)) <- "newv";; (Snd (#l1, #l2)) <- "newv";; #true
              else #false
       else #false.

Definition casp_seq: val :=
    λ: "lp" "vp",
       let: "oldv" := Fst "vp" in
       let: "newv" := Snd "vp" in
       if: !(Fst "lp") = "oldv"
         then if: !(Snd "lp") = "oldv"
                then (Fst "lp") <- "newv";; (Snd "lp") <- "newv";; #true
                else #false
         else #false.

Definition loadp_seq' (l1 l2: loc) : val := λ: "x", (!(Fst (#l1, #l2)), !(Snd (#l1, #l2))).

Definition loadp_seq: val := λ: "lp" "x", (!(Fst "lp"), !(Snd "lp")).

Definition storep_seq: val :=
  λ: "lp" "x",
     Fst "lp" <- "x";;
     Snd "lp" <- "x".

Definition storep_seq' (l1 l2: loc) : val :=
  λ: "x",
     Fst (#l1, #l2) <- "x";;
     Snd (#l1, #l2) <- "x".

(* constructor that returns operations bound to the same two-locations *)
Definition make_pair: val :=
  λ: "v1" "v2",
     let: "l1" := ref "v1" in
     let: "l2" := ref "v2" in
     let: "s" := mk_sync #() in
     ("s" (casp_seq ("l1", "l2")),
      "s" (loadp_seq ("l1", "l2")),
      "s" (storep_seq ("l1", "l2"))).

Definition casp: val := λ: "s", Fst (Fst "s").
Definition loadp: val := λ: "s", Snd (Fst "s").
Definition storep: val := λ: "s", Snd "s".

Global Opaque casp_seq storep_seq loadp_seq.

(* Instantiate a (stupid) lock of a pair of resource *)

Definition newplock : val := λ: <>, make_pair #false #false.

Definition pacquire : val :=
  rec: "pacquire" "p" :=
    if: casp "p" (#false, #true) then #() else "pacquire" "p".

Definition prelease : val :=
    λ: "p", storep "p" #false.

Section proof.
  Context `{!heapG Σ, !lockG Σ} (N: namespace).

  Definition plocked : iProp Σ :=
    (∃ (γ1 γ2: gname),
       heapN ⊥ N ∧ heap_ctx ∧
       own γ1 (Excl ()) ∧ own γ2 (Excl ()))%I.

  Definition plock_inv (γ1 γ2 : gname) (R1 R2: iProp Σ) (l1 l2: loc) : iProp Σ :=
    (∃ (b1 b2: bool),
       l1 ↦ #b1 ★ l2 ↦ #b2 ★
       (if b1 then True else own γ1 (Excl ()) ★ R1) ★
       (if b2 then True else own γ2 (Excl ()) ★ R2))%I.

  Definition is_plock (fs: val) (R1 R2 : iProp Σ) : iProp Σ :=
    (∃ (l1 l2: loc) (f1 f2 f3: val) (γ1 γ2: gname),
       heapN ⊥ N ∧ heap_ctx ∧ fs = (f1, f2, f3)%V ∧
       synced f1 (casp_seq' l1 l2) (plock_inv γ1 γ2 R1 R2 l1 l2) ∧
       synced f2 (loadp_seq' l1 l2) (plock_inv γ1 γ2 R1 R2 l1 l2) ∧
       synced f3 (storep_seq' l1 l2) (plock_inv γ1 γ2 R1 R2 l1 l2))%I.

  Global Instance is_plock_persistent p R1 R2: PersistentP (is_plock p R1 R2).
  Proof. apply _. Qed.

  Lemma not_false_is_true: ∀ b: bool, b ≠ false -> b = true.
  Proof. intros b H. destruct (Sumbool.sumbool_of_bool b); by (try contradiction). Qed.

  Lemma newplock_spec (R1 R2: iProp Σ) (Φ: val → iProp Σ):
    heapN ⊥ N →
    heap_ctx ★ R1 ★ R2 ★ (∀ p, is_plock p R1 R2 -★ Φ p)
    ⊢ WP newplock #() {{ Φ }}.
  Proof.
    iIntros (HN) "(#? & HR1 & HR2 & HΦ)".
    wp_seq. wp_let. wp_let.
    wp_alloc l1 as "Hl1". wp_let.
    iVs (own_alloc (Excl ())) as (γ1) "Hγ1"; first done.
    wp_alloc l2 as "Hl2". wp_let.
    iVs (own_alloc (Excl ())) as (γ2) "Hγ2"; first done.
    wp_bind (mk_sync _).
    iApply (mk_sync_spec_wp _ (plock_inv γ1 γ2 R1 R2 l1 l2)); try by auto.
    iSplit; first by auto.
    iSplitR "HΦ".
    + rewrite /plock_inv.
      iExists false, false.
      by iFrame.
    + iIntros (s) "#Hs".
      wp_let. wp_bind (s _).
      iApply wp_wand_r.
      iSplitR "HΦ".
      { wp_let. wp_bind (λ: _, _)%E. wp_value. iApply "Hs". }
      iIntros (v) "HRcas".
      wp_bind (s _)%E.
      iApply wp_wand_r.
      iSplitR "HRcas HΦ".
      { wp_let. wp_bind (λ: _, _)%E.
        wp_value. (* XXX: manually force lambda to be value *)
        iApply "Hs". }
      iIntros (v0) "HRload".
      wp_bind (s _)%E.
      iApply wp_wand_r.
      iSplitR "HRcas HRload HΦ".
      { wp_let. wp_bind (λ: _, _)%E. wp_value. iApply "Hs". }
      iIntros (v1) "HRstore".
      wp_value.
      iApply "HΦ".
      rewrite /is_plock. iExists l1, l2, _, _, _, γ1, γ2.
      repeat (iSplit; first by auto).
      rewrite /casp_seq'.
      iApply "HRstore".
  Qed.

  Lemma pacquire_spec (p: val) (R1 R2: iProp Σ) (Φ : val → iProp Σ):
    is_plock p R1 R2 ★ (plocked -★ R1 -★ R2 -★ Φ #()) ⊢ WP pacquire p {{ Φ }}.
  Proof.
    iIntros "(#Hp & HΦ)".
    iLöb as "Hl".
    wp_rec. wp_let.
    rewrite /is_plock /synced.
    iDestruct "Hp" as (l1 l2 casp loadp storep γ1 γ2) "(#? & #? & % & #HRcas & _ & #HRstore)".
    subst. wp_proj. wp_proj. wp_bind (casp _).
    iAssert ({{ True }} casp (#false%V, #true%V)%E {{ z, z = #false ∨ (z =#true ★ plocked ★ R1 ★ R2)}})%I as "#HP".
    (* prove the contextual property of casp closure returned from constructor *)
    {
      iApply ("HRcas" with "[]")=>//.
      iIntros "!# [Hplk _]".
      repeat (try (wp_let); try wp_proj).
      iDestruct "Hplk" as (b1 b2) "(Hl1 & Hl2 & Hdisj1 & Hdisj2)".
      wp_load.
      destruct b1.
      - wp_op=>[|_]//.
        destruct b2; wp_if.
        + iSplitL; last by iLeft.
          iExists true, true. by iFrame.
        + iSplitL; last by auto.
          iExists true, false. by iFrame.
      - wp_op=>[_|]//.
        destruct b2; wp_if; wp_proj; wp_load.
        + wp_op=>[_|]// _; wp_if.
          iSplitL; last by iLeft.
          iExists false, true. by iFrame.
        + wp_op=>[_|]//. wp_if.
          wp_proj. wp_store. wp_proj. wp_store.
          iSplitL "Hl1 Hl2".
          { rewrite /plock_inv. iExists true, true.
            iFrame. iSplitL; done. }
          iRight.
          iDestruct "Hdisj1" as "[Ho1 HR1]".
          iDestruct "Hdisj2" as "[Ho2 HR2]".
          iFrame. iSplitR; first by auto.
          iExists γ1, γ2. iFrame.
          iVsIntro. iSplit; by auto.
    }
    iApply wp_wand_r.
    iSplitR; first by iApply "HP".
    iIntros (v) "[%|(% & Hlocked & HR1 & HR2)]"; subst.
    - wp_if. iApply "Hl". iApply "HΦ".
    - wp_if. iVsIntro. iApply ("HΦ" with "Hlocked HR1 HR2").
  Qed.

End proof.
