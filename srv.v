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

Definition wait: val :=
  rec: "wait" "p" :=
    match: !"p" with
      InjR "r" => "p" <- #0 ;; "r"
    | InjL "_" => "wait" "p"
    end.

Definition mk_srv : val :=
  λ: "f",
     let: "p" := ref (InjR #0)%V in
     let: "l" := newlock #() in
     Fork (srv "f" "p");;
     λ: "x",
        acquire "l";;
                "p" <- InjL "x";;
        let: "ret" := wait "p" in
        release "l";;
        "ret".

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

  Definition srv_inv
             (γ: gname) (p: loc)
             (Q: val → val → Prop): iProp Σ :=
    ((∃ x: val, p ↦ InjRV x) ∨
     (∃ (x: val) (γ2: gname), p ↦ InjLV x ★ own γ ((1/2)%Qp, DecAgree x) ★ own γ2 (Excl ())) ∨
     (∃ (x y: val) (γ2: gname), p ↦ InjRV y ★ own γ ((1/2)%Qp, DecAgree x) ★ ■ Q x y ★ own γ2 (Excl ())))%I.

  Lemma srv_inv_timeless γ p Q: TimelessP (srv_inv γ p Q).
  Proof. apply _. Qed.
  
  Lemma mk_srv_spec (f: val) Q:
    heapN ⊥ N →
    heap_ctx ★ □ (∀ x:val, WP f x {{ v, ■ Q x v }})
    ⊢ WP mk_srv f {{ f', □ (∀ x:val, WP f' x {{ v, ■ Q x v }})}}.
  Proof.
    iIntros (HN) "[#Hh #Hf]".
    wp_let. wp_alloc p as "Hp".
    iVs (own_alloc (Excl ())) as (γ1) "Hγ1"; first done.
    iVs (own_alloc (1%Qp, DecAgree #0)) as (γ2) "Hγ2"; first done.
    iVs (inv_alloc N _ (srv_inv γ1 γ2 p Q) with "[Hp Hγ1]") as "#?".
    { iNext. rewrite /srv_inv. iLeft. iExists #0. by iFrame. }
    wp_let. wp_bind (newlock _).
    iApply newlock_spec=>//. iFrame "Hh".
    iAssert (∃ x: val, own γ2 (1%Qp, DecAgree x))%I with "[Hγ2]" as "Hinv"; first by eauto.
    iFrame "Hinv". iIntros (lk γ) "#Hlk".
    wp_let. wp_apply wp_fork.
    iSplitL.
    - (* client closure *)
      iVsIntro. wp_seq. iVsIntro.
      iAlways. iIntros (x).
      iLöb as "IH". wp_rec.
      wp_bind (acquire _). iApply acquire_spec.
      iFrame "Hlk". iIntros "Hlked Ho". iDestruct "Ho" as (x') "Ho".
      wp_seq. wp_bind (_ <- _)%E.
      iInv N as ">Hinv" "Hclose".
      rewrite /srv_inv.
      iDestruct "Hinv" as "[Hinv|[Hinv|Hinv]]".
      + iDestruct "Hinv" as (x'') "Hp".
        wp_store.
        iAssert (own γ2 (1%Qp, DecAgree x') -★ (own γ2 ((1/2)%Qp, DecAgree x) ★ own γ2 ((1/2)%Qp, DecAgree x)))%I as "Hsplit".
        { admit. }
        iDestruct ("Hsplit" with "Ho") as "[Ho1 Ho2]".
        iVs ("Hclose" with "[Hlked Hp Ho1]").
        * rewrite /locked. iNext. iRight. iLeft.
          iExists x. iFrame.
      + (* Impossible: reenter locked *)
        iExFalso. admit.
      + (* Impossible: reenter locked *)
        iExFalso. admit.
      
     

      