From iris.program_logic Require Export weakestpre hoare.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.tests Require Import atomic.
From iris.algebra Require Import dec_agree frac.
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
  
End lemmas.
