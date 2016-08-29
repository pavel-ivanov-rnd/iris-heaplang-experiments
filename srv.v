From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import frac excl dec_agree.

Definition srv : val :=
  rec: "srv" "f" "p" :=
       match: !"p" with
         InjL "x" => "p" <- InjR ("f" "x");; "srv" "f" "p"
       | InjR "_" => "srv" "f" "p"
       end.

Definition mk_srv : val :=
  λ: "f",
     let: "l" := newlock #() in
     let: "p" := ref (InjR #0)%V in
     Fork (srv "f" "p");;
     rec: "wait" "x" :=
        acquire "l";;
        "p" <- InjL "x"
        match: !"p" with
          InjR "r" => "p" <- #0 ;; "r"
        | InjL "_" => "wait" "x"
        end.

(* play with some algebraic structure to see what fit ... *)

Definition srvR := prodR fracR (dec_agreeR val).

Lemma srv_coincide: ∀ (x1 x2: val) (q1 q2: Qp), ✓ ((q1, DecAgree x1) ⋅ (q2, DecAgree x2)) → x1 = x2.
Proof.
  intros x1 x2 q1 q2 H. destruct (decide (x1 = x2))=>//.
  exfalso. destruct H as [H1 H2].
  simpl in H2. apply dec_agree_op_inv in H2.
  by inversion H2.
Qed.

Lemma srv_update: ∀ (x1 x2: val), (1%Qp, DecAgree x1) ~~> (1%Qp, DecAgree x2).
Proof. intros. by apply cmra_update_exclusive. Qed.

(* define the gFunctors *)
Class srvG Σ := FlatG { srv_tokG :> inG Σ srvR }.
Definition srvΣ : gFunctors := #[GFunctor (constRF srvR)].

Instance subG_srvΣ {Σ} : subG srvΣ Σ → srvG Σ.
Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

Section proof.
  Context `{!heapG Σ, !lockG Σ, !srvG Σ} (N : namespace).
  
