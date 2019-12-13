From iris.algebra Require Import excl auth frac agree gmap list.
From iris.program_logic Require Import lifting.
From iris.proofmode Require Import tactics.
From iris_examples.logrel.F_mu_ref Require Export rules.
Import uPred.

Definition specN := nroot .@ "spec".

(** The CMRA for the heap of the specification. *)
Definition cfgUR := prodUR (optionUR (exclR exprO)) (gen_heapUR loc val).

(** The CMRA for the thread pool. *)
Class cfgSG Σ := CFGSG { cfg_inG :> inG Σ (authR cfgUR); cfg_name : gname }.

Definition spec_ctx `{cfgSG Σ} (ρ : cfg F_mu_ref_lang) : iProp Σ :=
  (∃ e, ∃ σ, own cfg_name (● (Excl' e, to_gen_heap σ))
            ∗ ⌜rtc erased_step ρ ([e],σ)⌝)%I.

Definition spec_inv `{cfgSG Σ} `{invG Σ} (ρ : cfg F_mu_ref_lang) : iProp Σ :=
  inv specN (spec_ctx ρ).

Section definitionsS.
  Context `{cfgSG Σ}.

  Definition heapS_mapsto (l : loc) (q : Qp) (v: val) : iProp Σ :=
    own cfg_name (◯ (ε, {[ l := (q, to_agree v) ]})).

  Definition tpool_mapsto (e: expr) : iProp Σ :=
    own cfg_name (◯ (Excl' e, ∅)).

  Global Instance heapS_mapsto_timeless l q v : Timeless (heapS_mapsto l q v).
  Proof. apply _. Qed.
End definitionsS.
Typeclasses Opaque heapS_mapsto tpool_mapsto.

Notation "l ↦ₛ{ q } v" := (heapS_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦ₛ{ q }  v") : bi_scope.
Notation "l ↦ₛ v" := (heapS_mapsto l 1 v) (at level 20) : bi_scope.
Notation "⤇ e" := (tpool_mapsto e) (at level 20) : bi_scope.

Section cfg.
  Context `{cfgSG Σ}.
  Context `{!invG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.

  Local Hint Resolve to_of_val : core.

  (** Conversion to tpools and back *)
  Lemma step_insert_no_fork K e σ κ e' σ' :
    head_step e σ κ e' σ' [] → erased_step ([fill K e], σ) ([fill K e'], σ').
  Proof. intros Hst. eexists. eapply (step_atomic _ _ _ _ _ _ _ [] [] []); eauto.
         by apply: Ectx_step'.
  Qed.

  Lemma step_pure E ρ K e e' :
    (∀ σ, head_step e σ [] e' σ []) →
    nclose specN ⊆ E →
    spec_inv ρ ∗ ⤇ fill K e ={E}=∗ ⤇ fill K e'.
  Proof.
    iIntros (??) "[Hinv Hj]". rewrite /spec_ctx /tpool_mapsto.
    iInv specN as ">Hspec" "Hclose".
    iDestruct "Hspec" as (e'' σ) "[Hown %]".
    iDestruct (@own_valid_2 with "Hown Hj")
      as %[[?%Excl_included%leibniz_equiv _]%prod_included Hvalid]%auth_both_valid; subst.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, option_local_update,
        (exclusive_local_update _ (Excl (fill K e'))). }
    iFrame "Hj".
    iApply "Hclose". iNext. iExists (fill K e'). iExists σ. iFrame.
    iPureIntro. eapply rtc_r, step_insert_no_fork; eauto.
  Qed.

  Lemma step_fst E ρ K e1 e2 :
    AsVal e1 → AsVal e2 →
    nclose specN ⊆ E →
    spec_inv ρ ∗ ⤇ fill K (Fst (Pair e1 e2)) ={E}=∗ ⤇ fill K e1.
  Proof. intros [? <-] [? <-]. apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_snd E ρ K e1 e2 :
    AsVal e1 → AsVal e2 → nclose specN ⊆ E →
    spec_inv ρ ∗ ⤇ fill K (Snd (Pair e1 e2)) ={E}=∗ ⤇ fill K e2.
  Proof. intros [? <-] [? <-]; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_alloc E ρ K e v:
    IntoVal e v → nclose specN ⊆ E →
    spec_inv ρ ∗ ⤇ fill K (Alloc e) ={E}=∗ ∃ l, ⤇ fill K (Loc l) ∗ l ↦ₛ v.
  Proof.
    iIntros (<- ?) "[#Hinv Hj]". rewrite /spec_ctx /tpool_mapsto.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e2 σ) "[Hown %]".
    destruct (exist_fresh (dom (gset positive) σ)) as [l Hl%not_elem_of_dom].
    iDestruct (own_valid_2 _ with "Hown Hj")
      as %[[?%Excl_included%leibniz_equiv _]%prod_included ?]%auth_both_valid.
    subst.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, option_local_update,
       (exclusive_local_update _ (Excl (fill K (Loc l)))). }
    iMod (own_update with "Hown") as "[Hown Hl]".
    { eapply auth_update_alloc, prod_local_update_2,
        (alloc_singleton_local_update _ l (1%Qp,to_agree v)); last done.
      by apply lookup_to_gen_heap_None. }
    iExists l. rewrite /heapS_mapsto. iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (fill K (Loc l)), (<[l:=v]>σ).
    rewrite to_gen_heap_insert; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_load E ρ K l q v:
    nclose specN ⊆ E →
    spec_inv ρ ∗ ⤇ fill K (Load (Loc l)) ∗ l ↦ₛ{q} v
    ={E}=∗ ⤇ fill K (of_val v) ∗ l ↦ₛ{q} v.
  Proof.
    iIntros (?) "(#Hinv & Hj & Hl)".
    rewrite /spec_ctx /tpool_mapsto /heapS_mapsto.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e2 σ) "[Hown %]".
    iDestruct (own_valid_2 _ with "Hown Hj")
      as %[[?%Excl_included%leibniz_equiv _]%prod_included ?]%auth_both_valid.
    subst.
    iDestruct (own_valid_2 with "Hown Hl")
      as %[[_ ?%gen_heap_singleton_included]%prod_included _]%auth_both_valid.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, option_local_update,
        (exclusive_local_update _ (Excl (fill K (of_val v)))). }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (fill K (of_val v)), σ.
    iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_store E ρ K l v' e v:
    IntoVal e v → nclose specN ⊆ E →
    spec_inv ρ ∗ ⤇ fill K (Store (Loc l) e) ∗ l ↦ₛ v'
    ={E}=∗ ⤇ fill K Unit ∗ l ↦ₛ v.
  Proof.
    iIntros (<- ?) "(#Hinv & Hj & Hl)".
    rewrite /spec_ctx /tpool_mapsto /heapS_mapsto.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e2 σ) "[Hown %]".
    iDestruct (own_valid_2 _ with "Hown Hj")
      as %[[?%Excl_included%leibniz_equiv _]%prod_included ?]%auth_both_valid.
    subst.
    iDestruct (own_valid_2 _ with "Hown Hl")
      as %[[_ Hl%gen_heap_singleton_included]%prod_included _]%auth_both_valid.
    iMod (own_update_2 with "Hown Hj") as "[Hown Hj]".
    { by eapply auth_update, prod_local_update_1, option_local_update,
        (exclusive_local_update _ (Excl (fill K Unit))). }
    iMod (own_update_2 with "Hown Hl") as "[Hown Hl]".
    { eapply auth_update, prod_local_update_2, singleton_local_update,
        (exclusive_local_update _ (1%Qp, to_agree v)); last done.
      by rewrite /to_gen_heap lookup_fmap Hl. }
    iFrame "Hj Hl". iApply "Hclose". iNext.
    iExists (fill K Unit), (<[l:=v]>σ).
    rewrite to_gen_heap_insert; last eauto. iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_lam E ρ K e1 e2 :
    AsVal e2 → nclose specN ⊆ E →
    spec_inv ρ ∗ ⤇ fill K (App (Lam e1) e2)
    ={E}=∗ ⤇ fill K (e1.[e2/]).
  Proof. intros [? <-]; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_tlam E ρ K e :
    nclose specN ⊆ E →
    spec_inv ρ ∗ ⤇ fill K (TApp (TLam e)) ={E}=∗ ⤇ fill K e.
  Proof. apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_Fold E ρ K e :
    AsVal e → nclose specN ⊆ E →
    spec_inv ρ ∗ ⤇ fill K (Unfold (Fold e)) ={E}=∗ ⤇ fill K e.
  Proof. intros [? <-]; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_case_inl E ρ K e0 e1 e2 :
    AsVal e0 → nclose specN ⊆ E →
    spec_inv ρ ∗ ⤇ fill K (Case (InjL e0) e1 e2)
      ={E}=∗ ⤇ fill K (e1.[e0/]).
  Proof. intros [? <-]; apply step_pure => σ; econstructor; eauto. Qed.

  Lemma step_case_inr E ρ K e0 e1 e2 :
    AsVal e0 → nclose specN ⊆ E →
    spec_inv ρ ∗ ⤇ fill K (Case (InjR e0) e1 e2)
      ={E}=∗ ⤇ fill K (e2.[e0/]).
  Proof. intros [? <-]; apply step_pure => σ; econstructor; eauto. Qed.
End cfg.
