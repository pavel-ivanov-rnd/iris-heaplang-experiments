From iris.program_logic Require Export weakestpre hoare atomic.
From iris.heap_lang Require Export lang proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import agree frac.
From iris_examples.logatom.flat_combiner Require Import sync misc.

(** The simple syncer spec in [sync.v] implies a logically atomic spec. *)

Definition syncR := prodR fracR (agreeR valO). (* track the local knowledge of ghost state *)
Class syncG Σ := sync_tokG :> inG Σ syncR.
Definition syncΣ : gFunctors := #[GFunctor (constRF syncR)].

Instance subG_syncΣ {Σ} : subG syncΣ Σ → syncG Σ.
Proof. solve_inG. Qed.

Section atomic_sync.
  Context `{EqDecision A, !heapG Σ, !lockG Σ}.
  Canonical AO := leibnizO A.
  Context `{!inG Σ (prodR fracR (agreeR AO))}.

  (* TODO: Rename and make opaque; the fact that this is a half should not be visible
           to the user. *)
  Definition gHalf (γ: gname) g : iProp Σ := own γ ((1/2)%Qp, to_agree g).

  Definition atomic_seq_spec (ϕ: A → iProp Σ) α β (f x: val) :=
    (∀ g, {{ ϕ g ∗ α g }} f x {{ v, ∃ g', ϕ g' ∗ β g g' v }})%I.

  (* TODO: Provide better masks. ∅ as inner mask is pretty weak. *)
  Definition atomic_synced (ϕ: A → iProp Σ) γ (f f': val) :=
    (□ ∀ α β (x: val), atomic_seq_spec ϕ α β f x →
                       <<< ∀ g, gHalf γ g ∗ □ α g >>> f' x @ ⊤ <<< ∃ v, ∃ g', gHalf γ g' ∗ β g g' v, RET v >>>)%I.

  (* TODO: Use our usual style with a generic post-condition. *)
  (* TODO: We could get rid of the x, and hard-code a unit. That would
     be no loss in expressiveness, but probably more annoying to apply.
     How much more annoying? And how much to we gain in terms of things
     becomign easier to prove? *)
  (* This is really the core of the spec: It says that executing `s` on `f`
     turns the sequential spec with f, α, β into the concurrent triple with f', α, β. *)
  Definition is_atomic_syncer (ϕ: A → iProp Σ) γ (s: val) := 
    (□ ∀ (f: val), WP s f {{ f', atomic_synced ϕ γ f f' }})%I.

  Definition atomic_syncer_spec (mk_syncer: val) :=
    ∀ (g0: A) (ϕ: A → iProp Σ),
      {{{ ϕ g0 }}} mk_syncer #() {{{ γ s, RET s; gHalf γ g0 ∗ is_atomic_syncer ϕ γ s }}}.

  Lemma atomic_spec (mk_syncer: val):
      mk_syncer_spec mk_syncer → atomic_syncer_spec mk_syncer.
  Proof.
    iIntros (Hsync g0 ϕ ret) "Hϕ Hret".
    iMod (own_alloc (((1 / 2)%Qp, to_agree g0) ⋅ ((1 / 2)%Qp, to_agree g0))) as (γ) "[Hg1 Hg2]".
    { by rewrite -pair_op agree_idemp. }
    iApply (Hsync (∃ g: A, ϕ g ∗ gHalf γ g)%I with "[Hg1 Hϕ]")=>//.
    { iExists g0. by iFrame. }
    iNext. iIntros (s) "#Hsyncer". iApply "Hret".
    iSplitL "Hg2"; first done. iIntros "!#".
    iIntros (f). iApply wp_wand_r. iSplitR; first by iApply "Hsyncer".
    iIntros (f') "#Hsynced {Hsyncer}".
    iAlways. iIntros (α β x) "#Hseq". change (ofe_car AO) with A.
    iIntros (Φ') "?".
    (* TODO: Why can't I iApply "Hsynced"? *)
    iSpecialize ("Hsynced" $! _ Φ' x).
    iApply wp_wand_r. iSplitL.
    - iApply ("Hsynced" with "[]")=>//; last iAccu.
      iAlways. iIntros "[HR HP]". iDestruct "HR" as (g) "[Hϕ Hg1]".
      (* we should view shift at this point *)
      iApply fupd_wp. iMod "HP" as (?) "[[Hg2 #Hα] [Hvs1 _]]".
      iDestruct (m_frag_agree with "Hg1 Hg2") as %Heq. subst.
      iMod ("Hvs1" with "[Hg2]") as "HP"; first by iFrame.
      iModIntro. iApply wp_fupd. iApply wp_wand_r. iSplitL "Hϕ".
      { iApply "Hseq". iFrame. done. }
      iIntros (v) "H". iDestruct "H" as (g') "[Hϕ' Hβ]".
      iMod ("HP") as (g'') "[[Hg'' _] [_ Hvs2]]".
      iSpecialize ("Hvs2" $! v).
      iDestruct (m_frag_agree' with "Hg'' Hg1") as "[Hg %]". subst.
      rewrite Qp_div_2.
      iAssert (|==> own γ (((1 / 2)%Qp, to_agree g') ⋅ ((1 / 2)%Qp, to_agree g')))%I
              with "[Hg]" as ">[Hg1 Hg2]".
      { iApply own_update; last by iAssumption.
        apply cmra_update_exclusive. by rewrite -pair_op agree_idemp. }
      iMod ("Hvs2" with "[Hg1 Hβ]").
      { iExists g'. iFrame. }
      iModIntro. iSplitL "Hg2 Hϕ'"; last done.
      iExists g'. by iFrame.
    - iIntros (?) "?". done.
  Qed.

End atomic_sync.
