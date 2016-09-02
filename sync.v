From iris.program_logic Require Export weakestpre hoare.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.tests Require Import atomic.
Import uPred.

(* See CaReSL paper §3.2 *)
Definition mk_sync: val :=
  λ: <>,
       let: "l" := newlock #() in
       λ: "f" "x",
          acquire "l";;
          let: "ret" := "f" "x" in
          release "l";;
          "ret".

Global Opaque mk_sync.

Section proof.
  Context `{!heapG Σ, !lockG Σ} (N: namespace).

  (* concurrent object triple: R, p . <l, α p l> e <v, β p l v>*)
  Definition conc_obj_triple {A: Type}
             (α: val → A → iProp Σ)
             (β: val → A → val → iProp Σ)
             (Ei Eo: coPset)
             (e: expr) : iProp Σ :=
    (∀ P Q,
       (□ (∀ (R: val → iProp Σ) p,
             P ★ R p -★
               ∃ l: A, α p l ★
                 (∀ v, β p l v -★ Q l v ★ R p)))
          -★ {{ P }} e {{ v, ∃ l, Q l v }})%I.

  Arguments conc_obj_triple {_} _ _ _ _ _.
  
  (* f' refines f *)
  Definition refines (f' f: val) (R: iProp Σ): iProp Σ :=
    (□ ∀ (x: expr) (v: val) (P: iProp Σ) (Q: val -> iProp Σ),
         to_val x = Some v -★
         {{ R ★ P }} f x {{ z, R ★ Q z }} -★
         {{ P }} f' x {{ z, Q z }})%I.

  Global Instance refines_persistent f f' R: PersistentP (refines f f' R).
  Proof. apply _. Qed.

  Global Opaque refines.
  
  Definition is_syncer (R: iProp Σ) (s: val) : iProp Σ :=
    (∀ (f : val), WP s f {{ f', refines f' f R }})%I.

  Lemma mk_sync_spec_wp:
    ∀ (R: iProp Σ) (Φ: val -> iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ R ★ (∀ s, □ (is_syncer R s) -★ Φ s) ⊢ WP mk_sync #() {{ Φ }}.
  Proof.
    iIntros (R Φ HN) "(#Hh & HR & HΦ)".
    wp_seq. wp_bind (newlock _).
    iApply newlock_spec; first by auto.
    iSplitR "HR HΦ"; first by auto.
    iFrame "HR".
    iIntros (lk γ) "#Hl". wp_let. iApply "HΦ". iIntros "!#".
    rewrite /is_syncer. iIntros (f).
    wp_let. iVsIntro. rewrite /refines. iIntros "!#".
    iIntros (x v P Q <-%of_to_val) "#Hf !# HP".
    wp_let.
    wp_bind (acquire _).
    iApply acquire_spec.
    iSplit; first by auto.
    iIntros "Hlocked R".
    wp_seq. wp_bind (f _).
    iDestruct ("Hf" with "[R HP]") as "Hf'"; first by iFrame.
    iApply wp_wand_r.
    iSplitL "Hf'"; first by auto.
    iIntros (v') "[HR HQv]".
    wp_let.
    wp_bind (release _).
    iApply release_spec.
    iFrame "HR".
    iSplitR; eauto.
    iFrame.
    by wp_seq.
  Qed.

  (* a general way to get atomic triple from mk_styc *)

  Definition atomic_triple' {A: Type}
             (ϕ: A → iProp Σ)
             (β: A → A → val → iProp Σ)
             (Ei Eo: coPset)
             (e: expr) : iProp Σ :=
    (∀ P Q, (P ={Eo, Ei}=> ∃ g g',
                                ϕ g ★
                                (∀ v, β g g' v ={Ei, Eo}=★ Q v)
            ) -★ {{ P }} e @ ⊤ {{ Q }})%I.
  
End proof.

From iris.algebra Require Import dec_agree frac.
From iris.program_logic Require Import auth.

Definition pcas_R := authR (optionUR (prodR fracR (dec_agreeR (val * val)))).

Class pcasG Σ := PcasG { pcas_tokG :> inG Σ pcas_R }.
Definition pcasΣ : gFunctors := #[GFunctor (constRF pcas_R)].

Section atomic_pair.
  Context `{!heapG Σ, !lockG Σ, !pcasG Σ} (N : namespace).
  
  Definition pcas_seq : val :=
    λ: "l1" "l2" "a" "b",
       if: !"l1" = "a"
         then if: !"l2" = "a"
                then "l1" <- "b";; "l2" <- "b";; #true
                else #false
         else #false.

  Lemma pcas_seq_spec (l1 l2: loc) (a b x1 x2: val):
    ∀ (Φ: val → iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ l1 ↦ x1 ★ l2 ↦ x2 ★
      (■ (x1 = a ∧ x2 = a) -★ l1 ↦ b -★ l2 ↦ b -★ Φ #true)%I ★
      (■ (¬ (x1 = a ∧ x2 = a)) -★ l1 ↦ x1 -★ l2 ↦ x2 -★ Φ #false)%I
      ⊢ WP pcas_seq #l1 #l2 a b {{ Φ }}.
  Proof.
    iIntros (Φ HN) "(#Hh & Hl1 & Hl2 & HΦ1 & HΦ2)".
    wp_seq. repeat wp_let.
    wp_load.
    wp_op=>[?|Hx1na].
    - subst.
      wp_if. wp_load.
      wp_op=>[?|Hx2na]. subst.
      + wp_if. wp_store. wp_store.
        iAssert (■ (a = a ∧ a = a))%I as "Ha"; first by auto.
        iApply ("HΦ1" with "Ha Hl1 Hl2").
      + wp_if.
        iAssert (■ ¬ (a = a ∧ x2 = a))%I as "Ha".
        { iPureIntro. move=>[_ Heq]//. }
        iApply ("HΦ2" with "Ha Hl1 Hl2").
    - subst.
      wp_if.
        iAssert (■ ¬ (x1 = a ∧ x2 = a))%I as "Ha".
        { iPureIntro. move=>[_ Heq]//. }
        iApply ("HΦ2" with "Ha Hl1 Hl2").
  Qed.

  Definition mk_pcas : val :=
    λ: "x1" "x2",
       let: "l1" := ref "x1" in
       let: "l2" := ref "x2" in
       let: "lk" := newlock #() in
       λ: "a" "b",
          acquire "lk";;
          let: "v" := pcas_seq "l1" "l2" "a" "b" in
          release "lk";;
          "v".

  Definition gFullR (x1 x2: val) : pcas_R := ● Some ((1/2)%Qp, DecAgree (x1, x2)).
  Definition gFragR (x1 x2: val) : pcas_R := ◯ Some ((1/2)%Qp, DecAgree (x1, x2)).

  Definition gFull (x1 x2: val) γ: iProp Σ := own γ (gFullR x1 x2).
  Definition gFrag (x1 x2: val) γ :iProp Σ := own γ (gFragR x1 x2).

  Definition β (x1 x2 x1' x2' v a b: val) : iProp Σ :=
    ((v = #true  ∧ x1 = a ∧ x2 = a ∧ x1' = b ∧ x2' = b) ∨
     (v = #false ∧ x1 = a ∧ x2 = a ∧ x1' = b ∧ x2' = b))%I.
  
  Definition is_pcas γ (f: val) (Ei Eo: coPset) : iProp Σ :=
    (∀ (a b: val) (Q: val → iProp Σ),
      (∀ x1 x2 x1' x2' (r: val),
         (True ={Ei, Eo}=> gFrag x1 x2 γ) ★
         (gFrag x1' x2' γ ★ β x1 x2 x1' x2' r a b ={Eo, Ei}=> Q r)) -★ WP f a b {{ Q }})%I.

  Lemma pcas_atomic_spec (x10 x20: val): (* let's fix Eo as ⊤, and Ei as heapN *)
    heapN ⊥ N →
    heap_ctx
    ⊢ WP mk_pcas x10 x20 {{ f, ∃ γ, □ is_pcas γ f (⊤ ∖ nclose N) heapN }}.
  Proof.
    iIntros (HN) "#Hh". repeat wp_let.
    wp_alloc l1 as "Hl1". wp_let.
    wp_alloc l2 as "Hl2". iVs (own_alloc (gFullR x10 x20 ⋅ gFragR x10 x20)) as (γ) "Hγ"; first by done.
    iDestruct (own_op with "Hγ") as "[Hfull Hfrag]".
    iAssert (∃ x1 x2, l1 ↦ x1 ★ l2 ↦ x2 ★ gFull x1 x2 γ)%I with "[-Hfrag]" as "HR".
    { iExists x10, x20. by iFrame. }
    wp_let.
    wp_bind (newlock _). iApply newlock_spec=>//.
    iFrame "Hh".
    iFrame "HR".
    iIntros (lk γ') "#Hlk".
    wp_let.
    iClear "Hfrag". (* HFrag should be handled to user? *) 
    iVsIntro. iExists γ. iAlways.
    rewrite /is_pcas.
    iIntros (a b Q) "H".
    repeat wp_let.
    wp_bind (acquire _).
    iApply acquire_spec.
    iFrame "Hlk". iIntros "Hlked Hls".
    iDestruct "Hls" as (x1 x2) "(Hl1 & Hl2 & HFulla)".
    wp_seq. repeat wp_let.
    wp_load.
    destruct (decide (x1 = a)).
    - subst. wp_op=>[_|]//.
      wp_if. wp_load.
      destruct (decide (x2 = a)).
      + subst. wp_op=>[_|]//.
        wp_if. wp_store.
        wp_store. wp_let.
        wp_let.
        iDestruct ("H" $! a a b b #true) as "[Hvs1 Hvs2]".
        rewrite /is_lock.
        iDestruct "Hlk" as (l) "(% & _ & % & Hinv)".
        iInv N as ([]) ">[Hl _]" "Hclose".
        * iVs ("Hvs1" with "[]") as "Hfraga"; first by auto.
          subst. wp_store.
          iAssert (β a a b b #true a b) as "Hβ".
          { iLeft. eauto. }
          iAssert (gFrag a a γ ★ gFull a a γ -★ gFrag b b γ ★ gFull b b γ)%I as "H".
          { admit. }
          iDestruct ("H" with "[Hfraga HFulla]") as "[HFragb HFullb]"; first by iFrame.
          iVs ("Hvs2" with "[HFragb Hβ]"); first by iFrame.
          rewrite /lock_inv.
          iVsIntro. iVs ("Hclose" with "[-~]").
          { iNext. iExists false.
            iFrame. iExists b, b. by iFrame. }
          iVsIntro. wp_seq. done.
Admitted.

Section sync_atomic.
  Context `{!heapG Σ, !lockG Σ} (N : namespace) {A: Type}.

  Variable α: val → A → iProp Σ.
  Variable β: val → A → val → iProp Σ.
  Variable f_cons f_seq: val.
  Variable R: val → iProp Σ.

  Definition mk_whatever (f_cons: val) (f_seq: val) : val :=
    λ: <>,
         let: "x" := f_cons #() in
         let: "s" := mk_sync #() in
         "s" (λ:<>, f_seq "x").

  Definition whatever_triple (obj: val) :=
    conc_obj_triple α β (nclose heapN) ⊤ (obj #()).

  Definition whatever_seq_spec :=
    ∀ (p: val) (l: A) (Φ: val → iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ α p l ★ (∀ v, β p l v -★ Φ v)
      ⊢ WP f_seq p {{ Φ }}.

  Definition f_cons_spec :=
    ∀ (Φ: val → iProp Σ),
      heapN ⊥ N →
      heap_ctx ★ (∀ v, R v -★ Φ v)%I
      ⊢ WP f_cons #() {{ Φ }}.
  
  Lemma mk_whatever_spec:
    ∀ (Φ: val → iProp Σ),
      heapN ⊥ N →
      whatever_seq_spec →
      f_cons_spec →
      heap_ctx ★      
      (∀ obj, whatever_triple obj -★ Φ obj)
      ⊢ WP mk_whatever f_cons f_seq #() {{ Φ }}.
  Proof.
    iIntros (Φ HN Hseq Hcons) "[#Hh HΦ]".
    wp_let. wp_bind (f_cons _). iApply Hcons=>//.
    iFrame "Hh".
    iIntros (v) "HR".
    wp_let. rewrite /mk_sync. (* TODO: use the derived lemmas above *)
    wp_seq. wp_bind (newlock _). iApply (newlock_spec)=>//.
    iFrame "Hh HR".
    iIntros (lk γ) "#Hlk".
    repeat wp_let.
    iApply "HΦ".
    rewrite /whatever_triple /conc_obj_triple.
    iIntros (P Q) "#H".
    iAlways. iIntros "HP". wp_seq.
    iSpecialize ("H" $! R v).
    wp_bind (acquire _).
    iApply acquire_spec.
    iFrame "Hlk". iIntros "Hlked HR".
    iDestruct ("H" with "[HP HR]") as (x) "[Hl Hnext]"; first by iFrame.
    wp_seq. wp_let.
    iApply Hseq=>//. iFrame "Hh Hl".
    iIntros (v') "Hbeta".
    iDestruct ("Hnext" $! v' with "Hbeta") as "[HQ HR]".
    wp_let. wp_bind (release _). iApply release_spec.
    iFrame "Hlk Hlked HR".
    wp_seq. iVsIntro. by iExists x.
  Qed.
End sync_atomic.
