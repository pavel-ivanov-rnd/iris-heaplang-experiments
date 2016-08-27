From iris.program_logic Require Export weakestpre hoare.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.tests Require Import atomic.
Import uPred.

(* See CaReSL paper §3.2 *)
Definition mk_sync: val :=
  λ: <>,
       let: "l" := newlock #() in
       λ: "f" "x",
          acquire "l";;
          let: "ret" := "f" "x" in
          release "l";;
          "ret".

Global Opaque mk_sync.

Section proof.
  Context `{!heapG Σ, !lockG Σ} (N: namespace).

  (* concurrent object triple: R, p . <l, α p l> e <v, β p l v>*)
  Definition conc_obj_triple {A: Type}
             (α: val → A → iProp Σ)
             (β: val → A → val → iProp Σ)
             (Ei Eo: coPset)
             (e: expr) : iProp Σ :=
    (∀ P Q,
       (□ (∀ (R: val → iProp Σ) p,
             P ★ R p -★
               ∃ l: A, α p l ★
                 (∀ v, β p l v -★ Q l v ★ R p)))
          -★ {{ P }} e {{ v, ∃ l, Q l v }})%I.

  Arguments conc_obj_triple {_} _ _ _ _ _.
  
  (* f' refines f *)
  Definition refines (f' f: val) (R: iProp Σ): iProp Σ :=
    (□ ∀ (x: expr) (v: val) (P: iProp Σ) (Q: val -> iProp Σ),
         to_val x = Some v -★
         {{ R ★ P }} f x {{ z, R ★ Q z }} -★
         {{ P }} f' x {{ z, Q z }})%I.

  Global Instance refines_persistent f f' R: PersistentP (refines f f' R).
  Proof. apply _. Qed.

  Global Opaque refines.
  
  Definition is_syncer (R: iProp Σ) (s: val) : iProp Σ :=
    (∀ (f : val), WP s f {{ f', refines f' f R }})%I.

  Lemma mk_sync_spec_wp:
    ∀ (R: iProp Σ) (Φ: val -> iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ R ★ (∀ s, □ (is_syncer R s) -★ Φ s) ⊢ WP mk_sync #() {{ Φ }}.
  Proof.
    iIntros (R Φ HN) "(#Hh & HR & HΦ)".
    wp_seq. wp_bind (newlock _).
    iApply newlock_spec; first by auto.
    iSplitR "HR HΦ"; first by auto.
    iFrame "HR".
    iIntros (lk γ) "#Hl". wp_let. iApply "HΦ". iIntros "!#".
    rewrite /is_syncer. iIntros (f).
    wp_let. iVsIntro. rewrite /refines. iIntros "!#".
    iIntros (x v P Q <-%of_to_val) "#Hf !# HP".
    wp_let.
    wp_bind (acquire _).
    iApply acquire_spec.
    iSplit; first by auto.
    iIntros "Hlocked R".
    wp_seq. wp_bind (f _).
    iDestruct ("Hf" with "[R HP]") as "Hf'"; first by iFrame.
    iApply wp_wand_r.
    iSplitL "Hf'"; first by auto.
    iIntros (v') "[HR HQv]".
    wp_let.
    wp_bind (release _).
    iApply release_spec.
    iFrame "HR".
    iSplitR; eauto.
    iFrame.
    by wp_seq.
  Qed.
End proof.

Section sync_atomic.
  Context `{!heapG Σ, !lockG Σ} (N : namespace) {A: Type}.

  Variable α: val → A → iProp Σ.
  Variable β: val → A → val → iProp Σ.
  Variable f_cons f_seq: val.
  Variable R: val → iProp Σ.

  Definition mk_whatever (f_cons: val) (f_seq: val) : val :=
    λ: <>,
         let: "x" := f_cons #() in
         let: "s" := mk_sync #() in
         "s" (λ:<>, f_seq "x").

  Definition whatever_triple (obj: val) :=
    conc_obj_triple α β (nclose heapN) ⊤ (obj #()).

  Definition whatever_seq_spec :=
    ∀ (p: val) (l: A) (Φ: val → iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ α p l ★ (∀ v, β p l v -★ Φ v)
      ⊢ WP f_seq p {{ Φ }}.

  Definition f_cons_spec :=
    ∀ (Φ: val → iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ (∀ v, R v -★ Φ v)%I
      ⊢ WP f_cons #() {{ Φ }}.
  
  Lemma mk_whatever_spec:
    ∀ (Φ: val → iProp Σ),
      heapN ⊥ N →
      whatever_seq_spec →
      f_cons_spec →
      heap_ctx ★      
      (∀ obj, whatever_triple obj -★ Φ obj)
      ⊢ WP mk_whatever f_cons f_seq #() {{ Φ }}.
  Proof.
    iIntros (Φ HN Hseq Hcons) "[#Hh HΦ]".
    wp_let. wp_bind (f_cons _). iApply Hcons=>//.
    iFrame "Hh".
    iIntros (v) "HR".
    wp_let. rewrite /mk_sync. (* TODO: use the derived lemmas above *)
    wp_seq. wp_bind (newlock _). iApply (newlock_spec)=>//.
    iFrame "Hh HR".
    iIntros (lk γ) "#Hlk".
    repeat wp_let.
    iApply "HΦ".
    rewrite /whatever_triple /conc_obj_triple.
    iIntros (P Q) "#H".
    iAlways. iIntros "HP". wp_seq.
    iSpecialize ("H" $! R v).
    wp_bind (acquire _).
    iApply acquire_spec.
    iFrame "Hlk". iIntros "Hlked HR".
    iDestruct ("H" with "[HP HR]") as (x) "[Hl Hnext]"; first by iFrame.
    wp_seq. wp_let.
    iApply Hseq=>//. iFrame "Hh Hl".
    iIntros (v') "Hbeta".
    iDestruct ("Hnext" $! v' with "Hbeta") as "[HQ HR]".
    wp_let. wp_bind (release _). iApply release_spec.
    iFrame "Hlk Hlked HR".
    wp_seq. iVsIntro. by iExists x.
  Qed.
End sync_atomic.
