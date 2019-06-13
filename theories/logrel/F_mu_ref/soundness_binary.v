From iris_examples.logrel.F_mu_ref Require Export context_refinement.
From iris.algebra Require Import excl auth frac agree.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import adequacy.
From iris_examples.logrel.F_mu_ref Require Import soundness.

Lemma basic_soundness Σ `{heapPreG Σ, inG Σ (authR cfgUR)}
    e e' τ v thp hp :
  (∀ `{heapG Σ, cfgSG Σ}, [] ⊨ e ≤log≤ e' : τ) →
  rtc erased_step ([e], ∅) (of_val v :: thp, hp) →
  (∃ thp' hp' v', rtc erased_step ([e'], ∅) (of_val v' :: thp', hp')).
Proof.
  intros Hlog Hsteps.
  cut (adequate NotStuck e ∅ (λ _ _, ∃ thp' h v, rtc erased_step ([e'], ∅) (of_val v :: thp', h))).
  { destruct 1; naive_solver. }
  eapply (wp_adequacy Σ); first by apply _.
  iIntros (Hinv ?).
  iMod (gen_heap_init (∅: state)) as (Hheap) "Hh".
  iMod (own_alloc (● (Excl' e', ∅)
    ⋅ ◯ ((Excl' e', ∅) : cfgUR))) as (γc) "[Hcfg1 Hcfg2]".
  { apply auth_both_valid. split=>//. }
  set (Hcfg := CFGSG _ _ γc).
  iMod (inv_alloc specN _ (spec_ctx ([e'], ∅)) with "[Hcfg1]") as "#Hcfg".
  { iNext. iExists e', ∅. iSplit; eauto.
    rewrite /to_gen_heap fin_maps.map_fmap_empty.
    iFrame. }
  set (HeapΣ := HeapG Σ Hinv Hheap).
  iExists (λ σ _, gen_heap_ctx σ), (λ _, True%I); iFrame.
  iApply wp_fupd. iApply (wp_wand with "[-]").
  - iPoseProof (Hlog _ _ with "[$Hcfg]") as "Hrel".
    { iApply (@logrel_binary.interp_env_nil Σ HeapΣ). }
    replace e with e.[env_subst[]] at 2 by by asimpl.
    iApply ("Hrel" $! []).
    rewrite /tpool_mapsto. asimpl. iFrame.
  - iModIntro. iIntros (v'). iDestruct 1 as (v2) "[Hj #Hinterp]".
    iInv specN as ">Hinv" "Hclose".
    iDestruct "Hinv" as (e'' σ) "[Hown %]".
    rewrite /tpool_mapsto /=.
    iDestruct (own_valid_2 with "Hown Hj") as %Hvalid.
    move: Hvalid=> /auth_both_valid
      [/prod_included [Hv2 _] _]. apply Excl_included, leibniz_equiv in Hv2. subst.
    iMod ("Hclose" with "[-]") as "_".
    + iExists (#v2), σ. auto.
    + iIntros "!> !%". eauto.
Qed.

Lemma binary_soundness Σ `{heapPreG Σ, inG Σ (authR cfgUR)}
    Γ e e' τ :
  (∀ f, e.[upn (length Γ) f] = e) →
  (∀ f, e'.[upn (length Γ) f] = e') →
  (∀ `{heapG Σ, cfgSG Σ}, Γ ⊨ e ≤log≤ e' : τ) →
  Γ ⊨ e ≤ctx≤ e' : τ.
Proof.
  intros He He' Hlog K thp σ v ?. eapply (basic_soundness Σ)=> ??.
  eapply (bin_log_related_under_typed_ctx _ _ _ _ []); eauto.
Qed.
