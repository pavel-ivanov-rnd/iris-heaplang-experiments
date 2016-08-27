From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import invariants tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.tests Require Import atomic sync.
From iris.heap_lang Require Import spin_lock.

Section sync_incr.
  Context `{!heapG Σ, !lockG Σ} (N : namespace).

  Definition α (l: val) (v: Z) := (∃ l': loc, l = #l' ∧ l' ↦ #v)%I.
  Definition β (l: val) (v: Z) ret := (∃ l': loc, l = #l' ∧ ret = #v ★ l' ↦ #(v + 1))%I.
  Variable R: val → iProp Σ.
  
  Definition incr_seq: val :=
    λ: "l",
       let: "v" := !"l" in
       "l" <- "v" + #1;;
       "v".

  Lemma incr_seq_spec:
    ∀ (l: val) (x: Z) (Φ: val → iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ α l x ★ (∀ v, β l x v -★ Φ v)
      ⊢ WP incr_seq l {{ Φ }}.
  Proof.
    rewrite /α /β.
    iIntros (l x Φ HN) "(#Hh & Hl & HΦ)".
    wp_let. iDestruct "Hl" as (l') "[% Hl]". subst.
    wp_load. wp_let. wp_op. wp_store.
    iSpecialize ("HΦ" $! #x with "[Hl]"); first by eauto.
    by iApply "HΦ".
  Qed.

  Local Opaque incr_seq.

  Definition cons: val := λ: <>, ref #0.

  Definition cons_spec :=
    ∀ (Φ: val → iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ (∀ v, R v -★ Φ v)%I
      ⊢ WP cons #() {{ Φ }}.
  
  Lemma mk_increr_spec:
    ∀ (Φ: val → iProp Σ),
      heapN ⊥ N →
      cons_spec →
      heap_ctx ★
      (∀ obj: val, conc_obj_triple α β (nclose heapN) ⊤ (obj #()) -★ Φ obj)
      ⊢ WP mk_whatever cons incr_seq #() {{ Φ }}.
  Proof.
    iIntros (Φ HN Hcons) "[#Hh HΦ]".
    iApply mk_whatever_spec=>//.
    - rewrite /whatever_seq_spec. apply incr_seq_spec.
    - by iFrame.
 Qed.
End sync_incr.
