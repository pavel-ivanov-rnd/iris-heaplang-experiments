From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap agree.
From iris_examples.logrel.F_mu_ref_conc Require Import logrel_binary.
Import uPred.
From iris.algebra Require deprecated.
Import deprecated.dec_agree.

Definition stackUR : ucmraT := gmapUR loc (agreeR valO).

Class stackG Σ :=
  StackG { stack_inG :> inG Σ (authR stackUR); stack_name : gname }.

Definition stack_mapsto `{stackG Σ} (l : loc) (v : val) : iProp Σ :=
  own stack_name (◯ {[ l := to_agree v ]}).

Notation "l ↦ˢᵗᵏ v" := (stack_mapsto l v) (at level 20) : bi_scope.

Section Rules.
  Context `{stackG Σ}.
  Notation D := (prodO valO valO -n> iPropO Σ).

  Global Instance stack_mapsto_persistent l v : Persistent (l ↦ˢᵗᵏ v).
  Proof. apply _. Qed.

  Lemma stack_mapstos_agree l v w : l ↦ˢᵗᵏ v ∗ l ↦ˢᵗᵏ w ⊢ ⌜v = w⌝.
  Proof.
    rewrite -own_op -auth_frag_op op_singleton own_valid.
    by iIntros (->%auth_frag_valid%singleton_valid%agree_op_invL').
  Qed.

  Program Definition StackLink_pre (Q : D) : D -n> D := λne P v,
    (∃ l w, ⌜v.1 = LocV l⌝ ∗ l ↦ˢᵗᵏ w ∗
            ((⌜w = InjLV UnitV⌝ ∧ ⌜v.2 = FoldV (InjLV UnitV)⌝) ∨
            (∃ y1 z1 y2 z2, ⌜w = InjRV (PairV y1 (FoldV z1))⌝ ∗
              ⌜v.2 = FoldV (InjRV (PairV y2 z2))⌝ ∗ Q (y1, y2) ∗ ▷ P(z1, z2))))%I.
  Solve Obligations with solve_proper.

  Global Instance StackLink_pre_contractive Q : Contractive (StackLink_pre Q).
  Proof. solve_contractive. Qed.

  Definition StackLink (Q : D) : D := fixpoint (StackLink_pre Q).

  Lemma StackLink_unfold Q v :
    StackLink Q v ≡ (∃ l w,
      ⌜v.1 = LocV l⌝ ∗ l ↦ˢᵗᵏ w ∗
      ((⌜w = InjLV UnitV⌝ ∧ ⌜v.2 = FoldV (InjLV UnitV)⌝) ∨
      (∃ y1 z1 y2 z2, ⌜w = InjRV (PairV y1 (FoldV z1))⌝
                      ∗ ⌜v.2 = FoldV (InjRV (PairV y2 z2))⌝
                      ∗ Q (y1, y2) ∗ ▷ @StackLink Q (z1, z2))))%I.
  Proof. rewrite {1}/StackLink (fixpoint_unfold (StackLink_pre Q) v) //. Qed.

  Global Opaque StackLink. (* So that we can only use the unfold above. *)

  Global Instance StackLink_persistent (Q : D) v `{∀ vw, Persistent (Q vw)} :
    Persistent (StackLink Q v).
  Proof.
    unfold Persistent.
    iIntros "H". iLöb as "IH" forall (v). rewrite StackLink_unfold.
    iDestruct "H" as (l w) "[% [#Hl [#Hr|Hr]]]"; subst.
    { iExists l, w; iAlways; eauto. }
    iDestruct "Hr" as (y1 z1 y2 z2) "[#H1 [#H2 [#HQ H']]]".
    rewrite later_forall. iDestruct ("IH" with "H'") as "#H''". iClear "H'".
    iAlways. eauto 20.
  Qed.

  Lemma stackR_alloc (h : stackUR) (i : loc) (v : val) :
    h !! i = None → ● h ~~> ● (<[i := to_agree v]> h) ⋅ ◯ {[i := to_agree v]}.
  Proof. intros. by apply auth_update_alloc, alloc_singleton_local_update. Qed.

  Context `{heapIG Σ}.

  Definition stack_owns (h : gmap loc val) :=
    (own stack_name (● ((to_agree <$> h) : stackUR))
        ∗ [∗ map] l ↦ v ∈ h, l ↦ᵢ v)%I.

  Lemma stack_owns_alloc h l v :
    stack_owns h ∗ l ↦ᵢ v ==∗ stack_owns (<[l := v]> h) ∗ l ↦ˢᵗᵏ v.
  Proof.
    iIntros "[[Hown Hall] Hl]".
    iDestruct (own_valid with "Hown") as %Hvalid.
    destruct (h !! l) as [w|] eqn:?.
    { iDestruct (@big_sepM_lookup with "Hall") as "Hl'"; first done.
      by iDestruct (@mapsto_valid_2 loc val with "Hl Hl'") as %Hvl. }
    iMod (own_update with "Hown") as "[Hown Hl']".
    { eapply auth_update_alloc.
        eapply (alloc_singleton_local_update _ l (to_agree v)); last done.
    by rewrite lookup_fmap Heqo. }
    iModIntro. rewrite /stack_owns. rewrite fmap_insert. iFrame "Hl' Hown".
    iApply @big_sepM_insert; simpl; try iFrame; auto.
  Qed.

  Lemma stack_owns_open_close h l v :
    stack_owns h -∗ l ↦ˢᵗᵏ v -∗ l ↦ᵢ v ∗ (l ↦ᵢ v -∗ stack_owns h).
  Proof.
    iIntros "[Howns Hls] Hl".
    iDestruct (own_valid_2 with "Howns Hl")
      as %[[az [Haz Hq]]%singleton_included _]%auth_both_valid.
    rewrite lookup_fmap in Haz.
    assert (∃ z, h !! l = Some z) as Hz.
    { revert Haz; case: (h !! l) => [z|] Hz; first (by eauto); inversion Hz. }
    destruct Hz as [z Hz]; rewrite Hz in Haz.
    apply Some_equiv_inj in Haz; revert Hq; rewrite -Haz => Hq.
    apply Some_included_total, to_agree_included, leibniz_equiv in Hq; subst.
    rewrite (big_sepM_lookup_acc _ _ l); eauto.
    iDestruct "Hls" as "[Hl' Hls]".
    iIntros "{$Hl'} Hl'". rewrite /stack_owns. iFrame "Howns". by iApply "Hls".
  Qed.

  Lemma stack_owns_later_open_close h l v :
    ▷ stack_owns h -∗ l ↦ˢᵗᵏ v -∗ ▷ (l ↦ᵢ v ∗ (l ↦ᵢ v -∗ stack_owns h)).
  Proof. iIntros "H1 H2". iNext; by iApply (stack_owns_open_close with "H1"). Qed.
End Rules.
