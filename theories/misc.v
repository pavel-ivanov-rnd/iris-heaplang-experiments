(* Miscellaneous lemmas *)

From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.algebra Require Import auth frac gmap dec_agree.
From iris.prelude Require Import countable.
From iris.base_logic Require Import big_op auth fractional.
Import uPred.

Section lemmas.
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
    own γ (Excl ()) ∗ own γ (Excl ()) ⊢ Q'.
  Proof.
    iIntros "[Ho1 Ho2]". iCombine "Ho1" "Ho2" as "Ho".
    iExFalso. by iDestruct (own_valid with "Ho") as "%".
  Qed.
End excl.

Section heap_extra.
  Context `{heapG Σ}.

  Lemma bogus_heap p (q1 q2: Qp) a b:
    ~((q1 + q2)%Qp ≤ 1%Qp)%Qc →
    p ↦{q1} a ∗ p ↦{q2} b ⊢ False.
  Proof.
    iIntros (?) "Hp". 
    (* FIXME: If I dont give the types here, it loops. *)
    iDestruct (@mapsto_valid_2 loc val with "Hp") as %H'. done.
  Qed.

End heap_extra.

Section big_op_later.
  Context {M : ucmraT}.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → uPred M. 

  Lemma big_sepM_delete_later Φ m i x :
    m !! i = Some x →
    ▷ ([∗ map] k↦y ∈ m, Φ k y) ⊣⊢ ▷ Φ i x ∗ ▷ [∗ map] k↦y ∈ delete i m, Φ k y.
  Proof. intros ?. rewrite big_sepM_delete=>//. apply later_sep. Qed.

  Lemma big_sepM_insert_later Φ m i x :
    m !! i = None →
    ▷ ([∗ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ ▷ Φ i x ∗ ▷ [∗ map] k↦y ∈ m, Φ k y.
  Proof. intros ?. rewrite big_sepM_insert=>//. apply later_sep. Qed.
End big_op_later.

Section pair.
  Context `{EqDecision A, !inG Σ (prodR fracR (dec_agreeR A))}.

  Lemma m_frag_agree γm (q1 q2: Qp) (a1 a2: A):
    own γm (q1, DecAgree a1) ∗ own γm (q2, DecAgree a2) ⊢ ⌜a1 = a2⌝.
  Proof.
    iIntros "[Ho Ho']".
    destruct (decide (a1 = a2)) as [->|Hneq]=>//.
    iCombine "Ho" "Ho'" as "Ho".
    iDestruct (own_valid with "Ho") as %Hvalid.
    exfalso. destruct Hvalid as [_ Hvalid].
    simpl in Hvalid. apply dec_agree_op_inv in Hvalid. inversion Hvalid. subst. auto.
  Qed.
  
  Lemma m_frag_agree' γm (q1 q2: Qp) (a1 a2: A):
    own γm (q1, DecAgree a1) ∗ own γm (q2, DecAgree a2)
    ⊢ own γm ((q1 + q2)%Qp, DecAgree a1) ∗ ⌜a1 = a2⌝.
  Proof.
    iIntros "[Ho Ho']".
    iDestruct (m_frag_agree with "[Ho Ho']") as %Heq; first iFrame.
    subst. iCombine "Ho" "Ho'" as "Ho".
    rewrite pair_op frac_op' dec_agree_idemp. by iFrame.
  Qed.
End pair.
