From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import auth frac gmap dec_agree upred_big_op.
From iris.prelude Require Import countable.
Import uPred.

Section lemmas.
  Lemma op_some: ∀ {A: cmraT} (a b: A), Some a ⋅ Some b = Some (a ⋅ b).
  Proof. done. Qed.

  Lemma invalid_plus: ∀ (q: Qp), ¬ ✓ (1 + q)%Qp.
  Proof.
    intros q H.
    apply (Qp_not_plus_q_ge_1 q).
    done.
  Qed.

  Lemma pair_l_frac_update (g g': val):
    ((1 / 2)%Qp, DecAgree g) ⋅ ((1 / 2)%Qp, DecAgree g) ~~> ((1 / 2)%Qp, DecAgree g') ⋅ ((1 / 2)%Qp, DecAgree g').
  Proof.
    repeat rewrite pair_op dec_agree_idemp.
    rewrite frac_op' Qp_div_2.
    eapply cmra_update_exclusive.
    done.
  Qed.
  
  Lemma pair_l_frac_op (p q: Qp) (g g': val):
    (((p, DecAgree g') ⋅ (q, DecAgree g'))) ~~> ((p + q)%Qp, DecAgree g').
  Proof. by rewrite pair_op dec_agree_idemp frac_op'. Qed.

  Lemma pair_l_frac_op' (p q: Qp) (g g': val):
     ((p + q)%Qp, DecAgree g') ~~> (((p, DecAgree g') ⋅ (q, DecAgree g'))).
  Proof. by rewrite pair_op dec_agree_idemp frac_op'. Qed.

  Lemma pair_l_frac_op_1' (g g': val):
     (1%Qp, DecAgree g') ~~> (((1/2)%Qp, DecAgree g') ⋅ ((1/2)%Qp, DecAgree g')).
  Proof. by rewrite pair_op dec_agree_idemp frac_op' Qp_div_2. Qed.
  
End lemmas.

Section excl.
  Context `{!inG Σ (exclR unitC)}.
  Lemma excl_falso γ Q':
    own γ (Excl ()) ★ own γ (Excl ()) ⊢ Q'.
  Proof.
    iIntros "[Ho1 Ho2]". iCombine "Ho1" "Ho2" as "Ho".
    iExFalso. by iDestruct (own_valid with "Ho") as "%".
  Qed.
End excl.

Section pair.
  Context `{EqDecision A, !inG Σ (prodR fracR (dec_agreeR A))}.
  
  Lemma m_frag_agree γm (q1 q2: Qp) (a1 a2: A):
    own γm (q1, DecAgree a1) ★ own γm (q2, DecAgree a2)
    ⊢ |=r=> own γm ((q1 + q2)%Qp, DecAgree a1) ★ (a1 = a2).
  Proof.
    iIntros "[Ho Ho']".
    destruct (decide (a1 = a2)) as [->|Hneq].
    - iSplitL=>//.
      iCombine "Ho" "Ho'" as "Ho".
      iDestruct (own_update with "Ho") as "?"; last by iAssumption.
      by rewrite pair_op frac_op' dec_agree_idemp.
    - iCombine "Ho" "Ho'" as "Ho".
      iDestruct (own_valid with "Ho") as %Hvalid.
      exfalso. destruct Hvalid as [_ Hvalid].
      simpl in Hvalid. apply dec_agree_op_inv in Hvalid. inversion Hvalid. subst. auto.
  Qed.
End pair.

Section evidence.  
  Context (K A: Type) `{Countable K, EqDecision A}.
  Definition evkR := prodR fracR (dec_agreeR A).
  Definition evmapR := gmapUR K evkR.
  Definition evidenceR := authR evmapR.
  Class evidenceG Σ := EvidenceG { evidence_G :> inG Σ evidenceR }.
  Definition evidenceΣ : gFunctors := #[ GFunctor (constRF evidenceR) ].

  Instance subG_evidenceΣ {Σ} : subG evidenceΣ Σ → evidenceG Σ.
  Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

  Lemma map_agree_eq m m' (hd: K) (p q: Qp) (x y: A):
    m !! hd = Some (p, DecAgree y) →
    m = {[hd := (q, DecAgree x)]} ⋅ m' → x = y.
  Proof.
    intros H1 H2.
    destruct (decide (x = y)) as [->|Hneq]=>//.
    exfalso.
    subst. rewrite lookup_op lookup_singleton in H1.
    destruct (m' !! hd) as [[b [c|]]|] eqn:Heqn; rewrite Heqn in H1; inversion H1=>//.
    destruct (decide (x = c)) as [->|Hneq3]=>//.
    - rewrite dec_agree_idemp in H3. by inversion H3.
    - rewrite dec_agree_ne in H3=>//.
  Qed.

  Lemma map_agree_somebot m m' (hd: K) (p q: Qp) (x: A):
    m !! hd = Some (p, DecAgreeBot) → m' !! hd = None →
    m = {[hd := (q, DecAgree x)]} ⋅ m' → False.
  Proof.
    intros H1 H2 H3. subst. rewrite lookup_op lookup_singleton in H1.
    destruct (m' !! hd) as [[b [c|]]|] eqn:Heqn; rewrite Heqn in H1; inversion H1=>//.
  Qed.

  Lemma map_agree_none m m' (hd: K) (q: Qp) (x: A):
    m !! hd = None → m = {[hd := (q, DecAgree x)]} ⋅ m' → False.
  Proof.
    intros H1 H2. subst. rewrite lookup_op lookup_singleton in H1.
    destruct (m' !! hd)=>//.
  Qed.

  Context `{!inG Σ (authR evmapR)}.

  Definition ev γm (k : K) (v: A) := (∃ q, own γm (◯ {[ k := (q, DecAgree v) ]}))%I.

  Lemma evmap_alloc γm m k v:
    m !! k = None →
    own γm (● m) ⊢ |=r=> own γm (● (<[ k := (1%Qp, DecAgree v) ]> m) ⋅ ◯ {[ k := (1%Qp, DecAgree v) ]}).
  Proof.
    iIntros (?) "Hm".
    iDestruct (own_update with "Hm") as "?"; last by iAssumption.
    apply auth_update_alloc, alloc_local_update=>//.
  Qed.
  
  Lemma map_agree_none' γm m hd x:
    m !! hd = None →
    own γm (● m) ★ ev γm hd x ⊢ False.
  Proof.
    iIntros (?) "[Hom Hev]". iDestruct "Hev" as (?) "Hfrag".
    iCombine "Hom" "Hfrag" as "Hauth".
    iDestruct (own_valid γm (● m ⋅ ◯ {[hd := (_, DecAgree x)]})
               with "[Hauth]") as %Hvalid=>//.
    iPureIntro.
    apply auth_valid_discrete_2 in Hvalid as [[af Compose%leibniz_equiv_iff] Valid].
    eapply (map_agree_none m)=>//.
  Qed.
  
  Lemma map_agree_eq' γm m hd p x agy:
    m !! hd = Some (p, agy) →
    own γm (● m) ★ ev γm hd x ⊢ own γm (● m) ★ ev γm hd x ★ DecAgree x = agy.
  Proof.
    iIntros (?) "[Hom Hev]". iDestruct "Hev" as (?) "Hfrag".
    iCombine "Hom" "Hfrag" as "Hauth".
    iDestruct (own_valid γm (● m ⋅ ◯ {[hd := (_, DecAgree x)]})
               with "[Hauth]") as %Hvalid=>//.
    apply auth_valid_discrete_2 in Hvalid as [[af Compose%leibniz_equiv_iff] Valid].
    destruct agy as [y|].
    - iDestruct "Hauth" as "[? ?]". iFrame. iSplitL.
      { rewrite /ev. eauto. }
      iPureIntro. destruct (decide (x = y)); try by subst.
      exfalso. apply n. eapply (map_agree_eq m)=>//. (* XXX: Why it is uPred M *)
    - iAssert (✓ m)%I as "H"=>//. rewrite (gmap_validI m).
      iDestruct ("H" $! hd) as "%".
      exfalso. subst. rewrite H0 in H2.
      by destruct H2 as [? ?].
  Qed.

  Lemma pack_ev γm k v q:
    own γm (◯ {[ k := (q, DecAgree v) ]}) ⊢ ev γm k v.
  Proof. iIntros "?". rewrite /ev. eauto. Qed.
  
  Lemma dup_ev γm hd y:
    ev γm hd y ⊢ |=r=> ev γm hd y ★ ev γm hd y.
  Proof.
    rewrite /ev. iIntros "Hev". iDestruct "Hev" as (q) "Hev".
    iAssert (|=r=> own γm (◯ {[hd := ((q/2)%Qp, DecAgree y)]} ⋅
                           ◯ {[hd := ((q/2)%Qp, DecAgree y)]}))%I with "[Hev]" as "==>[Hev1 Hev2]".
    { iDestruct (own_update with "Hev") as "?"; last by iAssumption.
      rewrite <- auth_frag_op.
      by rewrite op_singleton pair_op dec_agree_idemp  frac_op' Qp_div_2. }
    iSplitL "Hev1"; eauto.
  Qed.

  Lemma evmap_frag_agree_split γm p q1 q2 (a1 a2: A):
    own γm (◯ {[p := (q1, DecAgree a1)]}) ★
    own γm (◯ {[p := (q2, DecAgree a2)]})
    ⊢ |=r=> own γm (◯ {[p := (q1, DecAgree a1)]}) ★
            own γm (◯ {[p := (q2, DecAgree a1)]}) ★ (a1 = a2).
  Proof.
    iIntros "[Ho Ho']".
    destruct (decide (a1 = a2)) as [->|Hneq].
    - by iFrame.
    - iCombine "Ho" "Ho'" as "Ho".
      iDestruct (own_valid with "Ho") as %Hvalid.
      exfalso. rewrite <-(@auth_frag_op evmapR) in Hvalid.
      rewrite op_singleton in Hvalid.
      apply auth_valid_discrete in Hvalid. simpl in Hvalid.
      apply singleton_valid in Hvalid.
      destruct Hvalid as [_ Hvalid].
      apply dec_agree_op_inv in Hvalid. inversion Hvalid. subst. auto.
  Qed.

  Lemma evmap_frag_agree γm p q1 q2 (a1 a2: A):
    own γm (◯ {[p := (q1, DecAgree a1)]}) ★
    own γm (◯ {[p := (q2, DecAgree a2)]})
    ⊢ |=r=> own γm (◯ {[p := ((q1 + q2)%Qp, DecAgree a1)]}) ★ (a1 = a2).
  Proof.
    iIntros "Hos".
    iDestruct (evmap_frag_agree_split with "Hos") as "==>[Ho1 [Ho2 %]]".
    iCombine "Ho1" "Ho2" as "Ho". iSplitL; auto.
    iDestruct (own_update with "Ho") as "?"; last by iAssumption.
    rewrite <-(@auth_frag_op evmapR {[p := (q1, DecAgree a1)]} {[p := (q2, DecAgree a1)]}).
    by rewrite op_singleton pair_op frac_op' dec_agree_idemp.
  Qed.

  Lemma ev_agree γm k v1 v2:
    ev γm k v1 ★ ev γm k v2 ⊢ |=r=> ev γm k v1 ★ ev γm k v1 ★ v1 = v2.
  Proof.
    iIntros "[Hev1 Hev2]".
    iDestruct "Hev1" as (?) "Hev1". iDestruct "Hev2" as (?) "Hev2".
    iDestruct (evmap_frag_agree_split with "[-]") as "==>[Hev1 [Hev2 %]]"; first iFrame.
    subst. iSplitL "Hev1"; rewrite /ev; eauto.
  Qed.

End evidence.

Section heap_extra.
  Context `{heapG Σ}.

  Lemma bogus_heap p (q1 q2: Qp) a b:
    ~((q1 + q2)%Qp ≤ 1%Qp)%Qc →
    heap_ctx ★ p ↦{q1} a ★ p ↦{q2} b ⊢ False.
  Proof.
    iIntros (?) "(#Hh & Hp1 & Hp2)".
    iCombine "Hp1" "Hp2" as "Hp".
    iDestruct (heap_mapsto_op_1 with "Hp") as "[_ Hp]".
    rewrite heap_mapsto_eq. iDestruct (own_valid with "Hp") as %H'.
    apply singleton_valid in H'. by destruct H' as [H' _].
  Qed.
  
End heap_extra.

Section big_op_later.
  Context {M : ucmraT}.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → uPred M. 

  Lemma big_sepM_delete_later Φ m i x :
    m !! i = Some x →
    ▷ ([★ map] k↦y ∈ m, Φ k y) ⊣⊢ ▷ Φ i x ★ ▷ [★ map] k↦y ∈ delete i m, Φ k y.
  Proof. intros ?. rewrite big_sepM_delete=>//. apply later_sep. Qed.

  Lemma big_sepM_insert_later Φ m i x :
    m !! i = None →
    ▷ ([★ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ ▷ Φ i x ★ ▷ [★ map] k↦y ∈ m, Φ k y.
  Proof. intros ?. rewrite big_sepM_insert=>//. apply later_sep. Qed.
End big_op_later.
