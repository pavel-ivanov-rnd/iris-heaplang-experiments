From iris.program_logic Require Export weakestpre hoare.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.tests Require Import atomic.
From iris.algebra Require Import dec_agree frac gmap upred_big_op.
From iris.program_logic Require Import auth.
Import uPred.

Section lemmas.
  Lemma frac_op': forall (p q: Qp), (p ⋅ q) = (p + q)%Qp.
  Proof. done. Qed.
  
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

  Lemma split_mapk
        {Σ} {K: Type} `{Countable K} {V: cmraT}
        (m: gmapUR K V) (k: K) (v: V) (R: K → iProp Σ) :
    m !! k = Some v → ([★ map] k ↦ v ∈ m, R k) ⊢ R k ★ ([★ map] k ↦ v ∈ delete k m, R k).
  Proof. iIntros (?) "HRm". by iApply (big_sepM_delete (fun k _ => R k)). Qed.

  Lemma split_mapv
        {Σ} {K: Type} `{Countable K} {V: cmraT}
        (m: gmapUR K V) (k: K) (v: V) (R: V → iProp Σ) :
    m !! k = Some v → ([★ map] k ↦ v ∈ m, R v) ⊢ R v ★ ([★ map] k ↦ v ∈ delete k m, R v).
  Proof. iIntros (?) "HRm". by iApply (big_sepM_delete (fun _ v => R v)). Qed.

  Lemma map_agree {A: cmraT} m m' (hd: loc) (p q: A) x y:
    m !! hd = Some (p, DecAgree y) →
    x ≠ y → m = {[hd := (q, DecAgree x)]} ⋅ m' → False.
  Proof.
    intros H1 H2 H3.
    subst. rewrite lookup_op lookup_singleton in H1.
    destruct (m' !! hd) as [[b [c|]]|] eqn:Heqn; rewrite Heqn in H1; inversion H1=>//.
    destruct (decide (x = c)) as [->|Hneq3]=>//.
    - rewrite dec_agree_idemp in H3. by inversion H3.        
    - rewrite dec_agree_ne in H3=>//.
  Qed.

  Lemma map_agree_none {A: cmraT} m m' (hd: loc) (q: A) x:
    m !! hd = None → m = {[hd := (q, DecAgree x)]} ⋅ m' → False.
  Proof.
    intros H1 H2. subst. rewrite lookup_op lookup_singleton in H1.
    destruct (m' !! hd)=>//.
  Qed.

End lemmas.


Section heap_extra.
  Context `{heapG Σ}.

  Lemma bogus_heap p (q1 q2: Qp) a b:
    ~((q1 + q2)%Qp ≤ 1%Qp)%Qc →
    heap_ctx ★ p ↦{q1} a ★ p ↦{q2} b ⊢ False.
  Proof.
    iIntros (?) "(#Hh & Hp1 & Hp2)".
    iCombine "Hp1" "Hp2" as "Hp".
    iDestruct (heap_mapsto_op_1 with "Hp") as "[_ Hp]".
    rewrite heap_mapsto_eq. iDestruct (auth_own_valid with "Hp") as %H'.
    apply singleton_valid in H'. destruct H' as [H' _].
    auto.
  Qed.
  
End heap_extra.
