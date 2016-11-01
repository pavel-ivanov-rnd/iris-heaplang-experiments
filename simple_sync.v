(* Coarse-grained syncer *)

From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import dec_agree frac.
From iris_atomic Require Import sync.
Import uPred.

Definition mk_sync: val :=
  λ: <>,
       let: "l" := newlock #() in
       λ: "f" "x",
          acquire "l";;
          let: "ret" := "f" "x" in
          release "l";;
          "ret".

Global Opaque mk_sync.

Section syncer.
  Context `{!heapG Σ, !lockG Σ} (N: namespace).
  
  Lemma mk_sync_spec: mk_syncer_spec N mk_sync.
  Proof.
    iIntros (R Φ HN) "(#Hh & HR & HΦ)".
    wp_seq. wp_bind (newlock _).
    iApply newlock_spec; first done.
    iSplitL "HR"; first by iFrame. iNext.
    iIntros (lk γ) "#Hl". wp_let. iApply "HΦ". iIntros "!#".
    iIntros (f). wp_let. iModIntro. iAlways.
    iIntros (P Q x) "#Hf !# HP".
    wp_let. wp_bind (acquire _).
    iApply acquire_spec. iSplit; first done. iNext.
    iIntros "[Hlocked R]". wp_seq. wp_bind (f _).
    iDestruct ("Hf" with "[R HP]") as "Hf'"; first by iFrame.
    iApply wp_wand_r.  iSplitL "Hf'"; first done.
    iIntros (v') "[HR HQv]". wp_let. wp_bind (release _).
    iApply release_spec. iFrame "HR Hl Hlocked".
    iNext. iIntros "_". by wp_seq.
  Qed.
End syncer.
