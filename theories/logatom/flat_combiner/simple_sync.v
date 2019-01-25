(* Coarse-grained syncer *)

From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import frac.
From iris_examples.logatom.flat_combiner Require Import sync.
Import uPred.

Definition mk_sync: val :=
  λ: <>,
       let: "l" := newlock #() in
       λ: "f" "x",
          acquire "l";;
          let: "ret" := "f" "x" in
          release "l";;
          "ret".

Section syncer.
  Context `{!heapG Σ, !lockG Σ} (N: namespace).
  
  Lemma mk_sync_spec: mk_syncer_spec mk_sync.
  Proof.
    iIntros (R Φ) "HR HΦ".
    wp_lam. wp_bind (newlock _).
    iApply (newlock_spec N R with "[HR]"); first done. iNext.
    iIntros (lk γ) "#Hl". wp_pures. iApply "HΦ". iIntros "!#".
    iIntros (f). wp_pures. iAlways.
    iIntros (P Q x) "#Hf !# HP".
    wp_pures. wp_bind (acquire _).
    iApply (acquire_spec with "Hl"). iNext.
    iIntros "[Hlocked R]". wp_seq. wp_bind (f _).
    iSpecialize ("Hf" with "[R HP]"); first by iFrame.
    iApply wp_wand_r.  iSplitL "Hf"; first done.
    iIntros (v') "[HR HQv]". wp_let. wp_bind (release _).
    iApply (release_spec with "[$Hl $HR $Hlocked]").
    iNext. iIntros "_". by wp_seq.
  Qed.
End syncer.
