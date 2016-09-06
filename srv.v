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
      InjR "r" => "p" <- InjR #0 ;; "r"
    | InjL "_" => "wait" "p"
    end.

Local Opaque wait.

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
             (γx γ1 γ2: gname) (p: loc)
             (Q: val → val → Prop): iProp Σ :=
    ((∃ (x: val),   p ↦ InjRV x ★ own γ1 (Excl ())) ∨
     (∃ (x: val),   p ↦ InjLV x ★ own γx ((1/2)%Qp, DecAgree x) ★ own γ2 (Excl ())) ∨
     (∃ (x y: val), p ↦ InjRV y ★ own γx ((1/2)%Qp, DecAgree x) ★ ■ Q x y ★ own γ2 (Excl ())))%I.
  
  Lemma srv_inv_timeless γx γ1 γ2 p Q: TimelessP (srv_inv γx γ1 γ2 p Q).
  Proof. apply _. Qed.

  Lemma wait_spec (Φ: val → iProp Σ) (Q: val → val → Prop) x γx γ1 γ2 p:
    heapN ⊥ N →
    heap_ctx ★ inv N (srv_inv γx γ1 γ2 p Q) ★
    own γx ((1/2)%Qp, DecAgree x) ★ own γ1 (Excl ()) ★
    (∀ y, own γ2 (Excl ()) -★ own γx (1%Qp, DecAgree x) -★ ■ Q x y-★ Φ y)
    ⊢ WP wait #p {{ Φ }}.
  Proof.
    iIntros (HN) "(#Hh & #Hsrv & Hx & Hempty & HΦ)".
    iLöb as "IH".
    wp_rec. wp_bind (! #p)%E.
    iInv N as ">[Hinv|[Hinv|Hinv]]" "Hclose".
    + (* collision with Hempty *) admit.
    + (* not finished *)
      iDestruct "Hinv" as (x') "(Hp & Hx' & Hissued)".
      wp_load.
      iVs ("Hclose" with "[Hp Hx' Hissued]").
      { iNext. iRight. iLeft. iExists x'. by iFrame. }
      iVsIntro. wp_match. by iApply ("IH" with "Hx Hempty").
    + (* finished *)
      iDestruct "Hinv" as (x' y) "(Hp & Hx' & % & Hissued)".
      (* assert (x = x'). *)
      (* { admit. (* should use the properties of agreement monoid to fix this *) } *)
      wp_load. iVs ("Hclose" with "[Hp Hx' Hissued]").
      { iNext. iRight. iRight. iExists x', y. by iFrame. }
      iVsIntro. wp_match.
      wp_bind (_ <- _)%E.
      iInv N as ">[Hinv|[Hinv|Hinv]]" "Hclose".
      - (* colission *) admit.
      - (* impossible ... this is why irreversibility is important *)
        admit.
      -  iDestruct "Hinv" as (x'' y') "(Hp & Hx' & % & Hissued)".
         assert (x = x'').
         { admit. (* should use the properties of agreement monoid to fix this *) }
         subst. wp_store.
         iVs ("Hclose" with "[Hp Hempty]").
         { iNext. iLeft. iExists #0. by iFrame. }
         iVsIntro. wp_seq.
         assert (y = y').
         { admit. (* exclusivity *) }
         subst.
         iClear "Hx". iClear "Hx'".
         iAssert (own γx (1%Qp, DecAgree x'')) as "Hx".
         { admit. }
         iSpecialize ("HΦ" $! y' with "Hissued Hx").
         by iApply "HΦ".
  Admitted.
                        
  Lemma mk_srv_spec (f: val) Q:
    heapN ⊥ N →
    heap_ctx ★ □ (∀ x:val, WP f x {{ v, ■ Q x v }})
    ⊢ WP mk_srv f {{ f', □ (∀ x:val, WP f' x {{ v, ■ Q x v }})}}.
  Proof.
    iIntros (HN) "[#Hh #Hf]".
    wp_let. wp_alloc p as "Hp".
    iVs (own_alloc (Excl ())) as (γ1) "Hempty"; first done. (* black token *)
    iVs (own_alloc (Excl ())) as (γ2) "Hissued"; first done. (* white token *)
    iVs (own_alloc (1%Qp, DecAgree #0)) as (γx) "Hx"; first done.
    iVs (inv_alloc N _ (srv_inv γx γ1 γ2 p Q) with "[Hp Hempty]") as "#?".
    { iNext. rewrite /srv_inv. iLeft. iExists #0. by iFrame. }
    wp_let. wp_bind (newlock _).
    iApply newlock_spec=>//. iFrame "Hh".
    iAssert (∃ x, own γx (1%Qp, DecAgree x) ★ own γ2 (Excl ()))%I with "[Hissued Hx]" as "Hinv".
    { iExists #0. by iFrame. }
    iFrame "Hinv". iIntros (lk γlk) "#Hlk".
    wp_let. wp_apply wp_fork.
    iSplitL.
    - (* client closure *)
      iVsIntro. wp_seq. iVsIntro.
      iAlways. iIntros (x).
      wp_let. wp_bind (acquire _). iApply acquire_spec.
      iFrame "Hlk". iIntros "Hlked Ho".
      iDestruct "Ho" as (x') "[Hx Hissued]".
      wp_seq. wp_bind (_ <- _)%E.
      iInv N as ">Hinv" "Hclose".
      rewrite /srv_inv.
      iDestruct "Hinv" as "[Hinv|[Hinv|Hinv]]".
      + iDestruct "Hinv" as (x'') "[Hp Hempty]".
        wp_store.
        iAssert (own γx (1%Qp, DecAgree x') -★ (own γx ((1/2)%Qp, DecAgree x) ★ own γx ((1/2)%Qp, DecAgree x)))%I as "Hsplit".
        { admit. }
        iDestruct ("Hsplit" with "Hx") as "[Hx1 Hx2]".
        iVs ("Hclose" with "[Hp Hissued Hx1]").
        { rewrite /locked. iNext. iRight. iLeft.
          iExists x. by iFrame. }
        (* now prove things about wait *)
        iVsIntro. wp_seq.
        wp_bind (wait _).
        iApply (wait_spec with "[Hempty Hx2 Hlked]"); first by auto.
        { iFrame "Hh". iFrame "~". iFrame.
          iIntros (y) "Hempty Hx HQ".
          wp_let.
          wp_bind (release _).
          iApply release_spec.
          iFrame "Hlk Hlked".
          iSplitL "Hempty Hx".
          - iExists x. by iFrame.
          - by wp_seq.
        }
      + (* Impossible: reenter locked *)
        iExFalso. admit.
      + (* Impossible: reenter locked *)
        iExFalso. admit.      
  Admitted.
