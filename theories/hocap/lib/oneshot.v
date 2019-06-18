From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From iris.algebra Require Import cmra agree frac csum.
From iris_examples.hocap Require Export abstract_bag shared_bag.
Set Default Proof Using "Type".

(** We are going to need the oneshot RA to verify the
    Task.Join() method *)
Definition oneshotR := csumR fracR (agreeR valO).
Class oneshotG Σ := { oneshot_inG :> inG Σ oneshotR }.
Definition oneshotΣ : gFunctors := #[GFunctor oneshotR].
Instance subG_oneshotΣ {Σ} : subG oneshotΣ Σ → oneshotG Σ.
Proof. solve_inG. Qed.

Definition pending `{oneshotG Σ} γ q := own γ (Cinl q%Qp).
Definition shot `{oneshotG Σ} γ (v: val) := own γ (Cinr (to_agree v)).
Lemma new_pending `{oneshotG Σ} : (|==> ∃ γ, pending γ 1%Qp)%I.
Proof. by apply own_alloc. Qed.
Lemma shoot `{oneshotG Σ} (v: val) γ : pending γ 1%Qp ==∗ shot γ v.
Proof.
  apply own_update.
  by apply cmra_update_exclusive.
Qed.
Lemma shot_not_pending `{oneshotG Σ} γ v q :
  shot γ v -∗ pending γ q -∗ False.
Proof.
  iIntros "Hs Hp".
  iPoseProof (own_valid_2 with "Hs Hp") as "H".
  iDestruct "H" as %[].
Qed.
Lemma shot_agree `{oneshotG Σ} γ (v w: val) :
  shot γ v -∗ shot γ w -∗ ⌜v = w⌝.
Proof.
  iIntros "Hs1 Hs2".
  iDestruct (own_valid_2 with "Hs1 Hs2") as %Hfoo.
  iPureIntro. by apply agree_op_invL'.
Qed.
Global Instance pending_fractional `{oneshotG Σ} γ : Fractional (pending γ)%I.
Proof.
  intros p q. rewrite /pending.
  rewrite -own_op. f_equiv.
Qed.
Global Instance pending_as_fractional `{oneshotG Σ} γ q:
  AsFractional (pending γ q) (pending γ)%I q.
Proof.
  split; [done | apply _].
Qed.
