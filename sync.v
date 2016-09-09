From iris.program_logic Require Export weakestpre hoare.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.tests Require Import atomic.
From iris.algebra Require Import dec_agree frac.
From iris.program_logic Require Import auth.
From flatcomb Require Import misc.
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

Definition syncR := prodR fracR (dec_agreeR val).  (* FIXME: can't use a general A instead of val *)
Class syncG Σ := sync_tokG :> inG Σ syncR.
Definition syncΣ : gFunctors := #[GFunctor (constRF syncR)].

Instance subG_syncΣ {Σ} : subG syncΣ Σ → syncG Σ.
Proof. by intros ?%subG_inG. Qed.

Section generic.
  Context `{!heapG Σ, !lockG Σ, !syncG Σ} (N : namespace).

  Definition A := val.

  Definition gFragR g : syncR := ((1/2)%Qp, DecAgree g).
  Definition gFullR g : syncR := ((1/2)%Qp, DecAgree g).

  Definition gFrag (γ: gname) g : iProp Σ := own γ (gFragR g).
  Definition gFull (γ: gname) g : iProp Σ := own γ (gFullR g).
  
  Global Instance frag_timeless γ g: TimelessP (gFrag γ g).
  Proof. apply _. Qed.

  Global Instance full_timeless γ g: TimelessP (gFull γ g).
  Proof. apply _. Qed.
  
  Definition atomic_triple'
             (α: val → iProp Σ)
             (β: val → A → A → val → iProp Σ)
             (Ei Eo: coPset)
             (f x: val) γ : iProp Σ :=
    (∀ P Q, (∀ g, (P ={Eo, Ei}=> gFrag γ g ★ α x) ★
                  (∀ g' r, gFrag γ g' ★ β x g g' r ={Ei, Eo}=> Q r))
            -★ {{ P }} f x {{ Q }})%I.


  Definition sync : val :=
    λ: "f_cons" "f_seq",
        let: "l"  := "f_cons" #() in
        let: "s" := mk_sync #() in
        "s" ("f_seq" "l").

  Definition seq_spec (f: val) (ϕ: val → A → iProp Σ) α β (E: coPset) :=
      ∀ (Φ: val → iProp Σ) (l: val),
         {{ True }} f l {{ f', ■ (∀ (x: val) (Φ: val → iProp Σ) (g: A),
                               heapN ⊥ N →
                               heap_ctx ★ ϕ l g ★ α x ★
                               (∀ (v: val) (g': A), ϕ l g' -★ β x g g' v -★ |={E}=> Φ v)
                               ⊢ WP f' x @ E {{ Φ }} )}}.
    
  Definition cons_spec (f: val) (g: A) ϕ :=
      ∀ Φ: val → iProp Σ, heapN ⊥ N →
        heap_ctx ★ (∀ (l: val) (γ: gname), ϕ l g -★ gFull γ g -★ gFrag γ g -★ Φ l)
        ⊢ WP f #() {{ Φ }}.
  
  Lemma atomic_spec (f_cons f_seq: val) (ϕ: val → A → iProp Σ) α β:
      ∀ (g0: A),
        heapN ⊥ N → seq_spec f_seq ϕ α β ⊤ → cons_spec f_cons g0 ϕ →
        heap_ctx
        ⊢ WP sync f_cons f_seq {{ f, ∃ γ, gFrag γ g0 ★ ∀ x, □ atomic_triple' α β ⊤ ⊤ f x γ  }}.
  Proof.
    iIntros (g0 HN Hseq Hcons) "#Hh". repeat wp_let.
    wp_bind (f_cons _). iApply Hcons=>//. iFrame "Hh".
    iIntros (l γ) "Hϕ HFull HFrag".
    wp_let. wp_bind (mk_sync _).
    iApply mk_sync_spec_wp=>//.
    iAssert (∃ g: A, ϕ l g ★ gFull γ g)%I with "[-HFrag]" as "HR".
    { iExists g0. by iFrame. }
    iFrame "Hh HR".
    iIntros (s) "#Hsyncer".
    wp_let. rewrite /is_syncer /seq_spec.
    wp_bind (f_seq _). iApply wp_wand_r. iSplitR; first by iApply (Hseq with "[]")=>//.
    iIntros (f) "%". (* FIXME: name *)
    iApply wp_wand_r. iSplitR; first by iApply "Hsyncer".
    iIntros (v) "#Hrefines".
    iExists γ. iFrame. iIntros (x).
    iAlways. rewrite /atomic_triple'.
    iIntros (P Q) "#Hvss".
    rewrite /refines.
    iDestruct "Hrefines" as "#Hrefines".
    iSpecialize ("Hrefines" $! (of_val x) x P Q).
    iApply ("Hrefines" with "[]"); first by rewrite to_of_val.
    iAlways. iIntros "[HR HP]". iDestruct "HR" as (g) "[Hϕ HgFull]".
    (* we should view shift at this point *)
    iDestruct ("Hvss" $! g) as "[Hvs1 Hvs2]".
    iVs ("Hvs1" with "HP") as "[HgFrag Hα]".
    iApply pvs_wp. iVsIntro.
    iApply H=>//. (* FIXME: name *)
    iFrame "Hh Hϕ Hα". iIntros (ret g') "Hϕ' Hβ".
    iCombine "HgFull" "HgFrag" as "Hg".
    rewrite /gFullR /gFragR.
    iAssert (|=r=> own γ (((1 / 2)%Qp, DecAgree g') ⋅ ((1 / 2)%Qp, DecAgree g')))%I with "[Hg]" as "Hupd".
    { iApply (own_update); last by iAssumption. apply pair_l_frac_update. }
    iVs "Hupd" as "[HgFull HgFrag]".
    iSplitL "HgFull Hϕ'".
    - iExists g'. by iFrame.
    - by iVs ("Hvs2" $! g' ret with "[HgFrag Hβ]"); first by iFrame.
  Qed.
  
End generic.

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
