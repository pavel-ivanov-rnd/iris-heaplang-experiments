From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import dec_agree frac.
From iris_atomic Require Import atomic atomic_sync.
Import uPred.

Definition mk_sync: val :=
  λ: "f",
       let: "l" := newlock #() in
       λ: "x",
          acquire "l";;
          let: "ret" := "f" "x" in
          release "l";;
          "ret".

Global Opaque mk_sync.

Section syncer.
  Context `{!heapG Σ, !lockG Σ} (N: namespace).
  

  (* (* R synced f w.r.t f' *) *)
  (* Definition synced (f' f: val) (R: iProp Σ): iProp Σ := *)
  (*   (□ ∀ (x: expr) (v: val) (P: iProp Σ) (Q: val -> iProp Σ), *)
  (*        to_val x = Some v -★ *)
  (*        {{ R ★ P }} f x {{ z, R ★ Q z }} -★ *)
  (*        {{ P }} f' x {{ z, Q z }})%I. *)

  (* Global Instance synced_persistent f f' R: PersistentP (synced f f' R). *)
  (* Proof. apply _. Qed. *)

  (* Global Opaque synced. *)
  
  (* Definition is_syncer (R: iProp Σ) (s: val) : iProp Σ := *)
  (*   (∀ (f : val), WP s f {{ f', synced f' f R }})%I. *)

  Lemma mk_sync_spec (R: iProp Σ) (f: val):
    ∀ (Φ: val -> iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ R ★ (∀ f', □ (synced R f' f) -★ Φ f') ⊢ WP mk_sync f {{ Φ }}.
  Proof.
    iIntros (Φ HN) "(#Hh & HR & HΦ)".
    wp_seq. wp_bind (newlock _).
    iApply newlock_spec; first done.
    iSplitR "HR HΦ"; first done.
    iFrame "HR".
    iIntros (lk γ) "#Hl". wp_let. iApply "HΦ". iIntros "!#".
    rewrite /synced. iIntros (P Q x) "#Hf !# HP".
    wp_let. wp_bind (acquire _).
    iApply acquire_spec. iSplit; first done.
    iIntros "Hlocked R". wp_seq. wp_bind (f _).
    iDestruct ("Hf" with "[R HP]") as "Hf'"; first by iFrame.
    iApply wp_wand_r.  iSplitL "Hf'"; first done.
    iIntros (v') "[HR HQv]". wp_let. wp_bind (release _).
    iApply release_spec. iFrame "HR". iSplitR; first done.
    iFrame. by wp_seq.
  Qed.
End syncer.

Section atomic_sync.
  Context `{!heapG Σ, !lockG Σ, !syncG Σ} (N : namespace).

  Lemma mk_sync_atomic_spec (f_cons f_seq: val) (ϕ: val → A → iProp Σ) α β Ei:
      ∀ (g0: A),
        heapN ⊥ N → seq_spec N f_seq ϕ α β ⊤ → cons_spec N f_cons g0 ϕ →
        heap_ctx
        ⊢ WP (sync mk_sync) f_cons f_seq {{ f, ∃ γ, gHalf γ g0 ★ ∀ x, □ atomic_triple' α β Ei ⊤ f x γ  }}.
  Proof.
    iIntros (????) "#Hh".
    iApply (atomic_spec N mk_sync with "[-]")=>//.
    iIntros (????) "(?&?&?)". iApply (mk_sync_spec N R)=>//.
    iFrame.
  Qed.
  
End atomic_sync.
