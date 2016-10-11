From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import dec_agree frac.
From iris_atomic Require Import atomic misc.

Definition syncR := prodR fracR (dec_agreeR val).
Class syncG Σ := sync_tokG :> inG Σ syncR.
Definition syncΣ : gFunctors := #[GFunctor (constRF syncR)].

Instance subG_syncΣ {Σ} : subG syncΣ Σ → syncG Σ.
Proof. by intros ?%subG_inG. Qed.

Section atomic_sync.
  Context `{EqDecision A, !heapG Σ, !lockG Σ, !inG Σ (prodR fracR (dec_agreeR A))} (N : namespace).

  Definition gHalf (γ: gname) g : iProp Σ := own γ ((1/2)%Qp, DecAgree g).

  Definition atomic_triple'
             (α: val → iProp Σ)
             (β: val → A → A → val → iProp Σ)
             (Ei Eo: coPset)
             (f x: val) γ : iProp Σ :=
    (∀ P Q, atomic_triple_base A (fun g => gHalf γ g ★ □ α x)
                                 (fun g v => ∃ g':A, gHalf γ g' ★ β x g g' v)
                                 Ei Eo
                                (f x) (P x) (fun _ => Q x))%I.
       
  Definition sync (mk_syncer: val) : val :=
    λ: "f_seq" "l",
       let: "s" := mk_syncer #() in
       "s" ("f_seq" "l").

  Definition seq_spec (f: val) (ϕ: val → A → iProp Σ) α β (E: coPset) :=
      ∀ (Φ: val → iProp Σ) (l: val),
         {{ True }} f l {{ f', ■ (∀ (x: val) (Φ: val → iProp Σ) (g: A),
                               heapN ⊥ N →
                               heap_ctx ★ ϕ l g ★ □ α x ★
                               (∀ (v: val) (g': A), ϕ l g' -★ β x g g' v -★ |={E}=> Φ v)
                               ⊢ WP f' x @ E {{ Φ }} )}}.

  Definition synced R (f' f: val) :=
    (□ ∀ P Q (x: val), ({{ R ★ P x }} f x {{ v, R ★ Q x v }}) → ({{ P x }} f' x {{ v, Q x v }}))%I.

  Definition is_syncer (R: iProp Σ) (s: val) :=
    (∀ (f : val), WP s f {{ f', synced R f' f }})%I.

  Definition mk_syncer_spec (mk_syncer: val) :=
    ∀ (R: iProp Σ) (Φ: val -> iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ R ★ (∀ s, □ (is_syncer R s) -★ Φ s) ⊢ WP mk_syncer #() {{ Φ }}.
  
  Lemma atomic_spec (mk_syncer f_seq l: val) (ϕ: val → A → iProp Σ) α β Ei:
      ∀ (g0: A),
        heapN ⊥ N → seq_spec f_seq ϕ α β ⊤ →
        mk_syncer_spec mk_syncer →
        heap_ctx ★ ϕ l g0
        ⊢ WP (sync mk_syncer) f_seq l {{ f, ∃ γ, gHalf γ g0 ★ ∀ x, □ atomic_triple' α β Ei ⊤ f x γ  }}.
  Proof.
    iIntros (g0 HN Hseq Hsync) "[#Hh Hϕ]".
    iVs (own_alloc (((1 / 2)%Qp, DecAgree g0) ⋅ ((1 / 2)%Qp, DecAgree g0))) as (γ) "[Hg1 Hg2]".
    { by rewrite pair_op dec_agree_idemp. }
    repeat wp_let. wp_bind (mk_syncer _).
    iApply (Hsync (∃ g: A, ϕ l g ★ gHalf γ g)%I)=>//. iFrame "Hh".
    iSplitL "Hg1 Hϕ".
    { iExists g0. by iFrame. }
    iIntros (s) "#Hsyncer".
    wp_let. wp_bind (f_seq _). iApply wp_wand_r.
    iSplitR; first by iApply (Hseq with "[]")=>//.
    iIntros (f) "%".
    iApply wp_wand_r.
    iSplitR; first iApply "Hsyncer".
    iIntros (f') "#Hsynced".
    iExists γ. iFrame.
    iIntros (x). iAlways.
    rewrite /atomic_triple'.
    iIntros (P Q) "#Hvss".
    rewrite /synced.
    iSpecialize ("Hsynced" $! P Q x). 
    iIntros "!# HP". iApply wp_wand_r. iSplitL "HP".
    - iApply ("Hsynced" with "[]")=>//.
      iAlways. iIntros "[HR HP]". iDestruct "HR" as (g) "[Hϕ Hg1]".
      (* we should view shift at this point *) 
      iDestruct ("Hvss" with "HP") as "Hvss'". iApply pvs_wp.
      iVs "Hvss'". iDestruct "Hvss'" as (?) "[[Hg2 #Hα] [Hvs1 _]]".
      iVs ("Hvs1" with "[Hg2]") as "HP"; first by iFrame.
      iVsIntro. iApply H=>//.
      iFrame "Hh Hϕ". iSplitR; first done. iIntros (ret g') "Hϕ' Hβ".
      iVs ("Hvss" with "HP") as (g'') "[[Hg'' _] [_ Hvs2]]".
      iSpecialize ("Hvs2" $! ret).
      iDestruct (m_frag_agree' with "[Hg'' Hg1]") as "[Hg %]"; first iFrame. subst.
      rewrite Qp_div_2.
      iAssert (|=r=> own γ (((1 / 2)%Qp, DecAgree g') ⋅ ((1 / 2)%Qp, DecAgree g')))%I
              with "[Hg]" as "==>[Hg1 Hg2]".
      { iApply own_update; last by iAssumption.
        apply cmra_update_exclusive. by rewrite pair_op dec_agree_idemp. }
      iVs ("Hvs2" with "[Hg1 Hβ]").
      { iExists g'. iFrame. }
      iVsIntro. iSplitL "Hg2 Hϕ'".
      * iExists g'. by iFrame.
      * done.
    - iIntros (?) "?". by iExists g0.
  Qed.

End atomic_sync.
