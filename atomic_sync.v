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
  Context `{!heapG Σ, !lockG Σ, !inG Σ (prodR fracR (dec_agreeR val))} (N : namespace).

  Definition A := val. (* FIXME: can't use a general A instead of val *)

  Definition gHalf (γ: gname) g : iProp Σ := own γ ((1/2)%Qp, DecAgree g).

  Definition atomic_triple'
             (α: val → iProp Σ)
             (β: val → A → A → val → iProp Σ)
             (Ei Eo: coPset)
             (f x: val) γ : iProp Σ :=
    (∀ P Q, (∀ g, (P x ={Eo, Ei}=> gHalf γ g ★ □ α x) ★
                  (gHalf γ g ★ □ α x ={Ei, Eo}=> P x) ★
                  (∀ g' r, gHalf γ g' ★ β x g g' r ={Ei, Eo}=> Q x r))
            -★ {{ P x }} f x {{ v, Q x v }})%I.

  Definition sync (syncer: val) : val :=
    λ: "f_cons" "f_seq",
        let: "l"  := "f_cons" #() in
        syncer ("f_seq" "l").

  Definition seq_spec (f: val) (ϕ: val → A → iProp Σ) α β (E: coPset) :=
      ∀ (Φ: val → iProp Σ) (l: val),
         {{ True }} f l {{ f', ■ (∀ (x: val) (Φ: val → iProp Σ) (g: A),
                               heapN ⊥ N →
                               heap_ctx ★ ϕ l g ★ □ α x ★
                               (∀ (v: val) (g': A), ϕ l g' -★ β x g g' v -★ |={E}=> Φ v)
                               ⊢ WP f' x @ E {{ Φ }} )}}.

  Definition cons_spec (f: val) (g: A) ϕ :=
      ∀ Φ: val → iProp Σ, heapN ⊥ N →
        heap_ctx ★ (∀ (l: val) (γ: gname), ϕ l g -★ gHalf γ g -★ gHalf γ g -★ Φ l)
        ⊢ WP f #() {{ Φ }}.

  Definition synced R (f' f: val) :=
    (∀ P Q (x: val), ({{ R ★ P x }} f x {{ v, R ★ Q x v }}) → ({{ P x }} f' x {{ v, Q x v }}))%I.

  Definition mk_sync_spec (syncer: val) :=
    ∀ f R (Φ: val → iProp Σ),
      heapN ⊥ N → 
      heap_ctx ★ R ★ (∀ f', □ synced R f' f -★ Φ f') ⊢ WP syncer f {{ Φ }}.
  
  Lemma atomic_spec (syncer f_cons f_seq: val) (ϕ: val → A → iProp Σ) α β Ei:
      ∀ (g0: A),
        heapN ⊥ N → seq_spec f_seq ϕ α β ⊤ → cons_spec f_cons g0 ϕ →
        mk_sync_spec syncer →
        heap_ctx
        ⊢ WP (sync syncer) f_cons f_seq {{ f, ∃ γ, gHalf γ g0 ★ ∀ x, □ atomic_triple' α β Ei ⊤ f x γ  }}.
  Proof.
    iIntros (g0 HN Hseq Hcons Hsync) "#Hh". repeat wp_let.
    wp_bind (f_cons _). iApply Hcons=>//. iFrame "Hh".
    iIntros (l γ) "Hϕ HFull HFrag".
    wp_let. wp_bind (f_seq _)%E.
    iApply wp_wand_r. iSplitR; first by iApply (Hseq with "[]")=>//.
    iIntros (f Hf). iApply (Hsync f (∃ g: A, ϕ l g ★ gHalf γ g)%I)=>//.
    iFrame "#". iSplitL "HFull Hϕ".
    { iExists g0. by iFrame. }
    iIntros (f') "#Hflatten".
    iExists γ. iFrame.
    iIntros (x). iAlways.
    rewrite /atomic_triple'.
    iIntros (P Q) "#Hvss".
    rewrite /synced.
    iSpecialize ("Hflatten" $! P Q).
    iApply ("Hflatten" with "[]").
    iAlways. iIntros "[HR HP]". iDestruct "HR" as (g) "[Hϕ HgFull]".
    (* we should view shift at this point *)
    iDestruct ("Hvss" $! g) as "[Hvs1 [Hvs2 Hvs3]]".
    iApply pvs_wp.
    iVs ("Hvs1" with "HP") as "[HgFrag #Hα]".
    iVs ("Hvs2" with "[HgFrag]") as "HP"; first by iFrame.
    iVsIntro. iApply Hf=>//.
    iFrame "Hh Hϕ". iSplitR; first done. iIntros (ret g') "Hϕ' Hβ".
    iVs ("Hvs1" with "HP") as "[HgFrag _]".
    iCombine "HgFull" "HgFrag" as "Hg".
    rewrite /gHalf.
    iAssert (|=r=> own γ (((1 / 2)%Qp, DecAgree g') ⋅ ((1 / 2)%Qp, DecAgree g')))%I with "[Hg]" as "Hupd".
    { iApply (own_update); last by iAssumption. apply pair_l_frac_update. }
    iVs "Hupd" as "[HgFull HgFrag]".
    iVs ("Hvs3" $! g' ret with "[HgFrag Hβ]"); first by iFrame.
    iVsIntro.
    iSplitL "HgFull Hϕ'".
    - iExists g'. by iFrame.
    - done.
  Qed.
  
End atomic_sync.
