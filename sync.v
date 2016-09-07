From iris.program_logic Require Export weakestpre hoare.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.tests Require Import atomic.
From iris.algebra Require Import dec_agree frac.
From iris.program_logic Require Import auth.
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
End proof.

Section generic.
  Context {A: Type} `{∀ x y : A, Decision (x = y)}.
  
  Definition syncR := authR (optionUR (prodR fracR (dec_agreeR A))).

  Class syncG Σ := SyncG { sync_tokG :> inG Σ syncR }.
  Definition syncΣ : gFunctors := #[GFunctor (constRF syncR)].

  Section triple.
    Context `{!heapG Σ, !lockG Σ, !syncG Σ} (N : namespace).

    Definition gFragR (g: A) : syncR := ◯ Some ((1/2)%Qp, DecAgree g).
    Definition gFullR (g: A) : syncR := ● Some ((1/2)%Qp, DecAgree g).
    
    Definition gFrag (γ: gname) (g: A) : iProp Σ := own γ (gFragR g).
    Definition gFull (γ: gname) (g: A) : iProp Σ := own γ (gFullR g).

    Global Instance frag_timeless γ g: TimelessP (gFrag γ g).
    Proof. apply _. Qed.

    Global Instance full_timeless γ g: TimelessP (gFull γ g).
    Proof. apply _. Qed.
  
    Definition atomic_triple'
               (β: val → A → A → val → iProp Σ)
               (Ei Eo: coPset)
               (f x: val) γ : iProp Σ :=
      (∀ P Q, (∀ g g' r, (P ={Eo, Ei}=> gFrag γ g) ★
                           (gFrag γ g' ★ β x g g' r ={Ei, Eo}=> Q r))
              -★ {{ P }} f x {{ Q }})%I.

    Lemma update_a: ∀ x x': A, (gFullR x ⋅ gFragR x) ~~> (gFullR x' ⋅ gFragR x').
    Proof.
      intros x x'.
    Admitted.

    Definition mk_sync' : val :=
      λ: "init" "f_seq",
        let: "l"  := "init" #() in
        let: "lk" := newlock #() in
          λ: "x",
            acquire "lk";;
            let: "v" := "f_seq" "l" "x" in
            release "lk";;
            "v".

    Definition seq_spec (f: val) ϕ β :=
      ∀ (x : val) (g g': A) (Φ: val → iProp Σ) (l: loc),
        heapN ⊥ N →
        heap_ctx ★ ϕ l g ★ (∀ r g', ϕ l g' -★ β x g g' r -★ Φ r)
        ⊢ WP f #l x {{ Φ }}.
    
    Lemma atomic_spec (f_cons f_seq: val) ϕ β:
      heapN ⊥ N → seq_spec f_seq ϕ β →
      heap_ctx
      ⊢ WP mk_sync' f_cons f_seq {{ f, ∃ γ, ∀ x, □ atomic_triple' β ⊤ ⊤ f x γ  }}.
  Proof.
    (* iIntros (HN) "#Hh". repeat wp_let. *)
    (* wp_alloc l1 as "Hl1". *)
    (* wp_alloc l2 as "Hl2". *)
    (* iVs (own_alloc (gFullR (#0, #0) ⋅ gFragR (#0, #0))) as (γ) "Hγ"; first by done. *)
    (* wp_let.  *)
    (* iDestruct (own_op with "Hγ") as "[Hfull Hfrag]". *)
    (* iAssert (∃ x1 x2, l1 ↦ x1 ★ l2 ↦ x2 ★ gFull γ (x1, x2))%I with "[-Hfrag]" as "HR". *)
    (* { iExists #0, #0. by iFrame. } *)
    (* wp_bind (newlock _). iApply newlock_spec=>//.  *)
    (* iFrame "Hh".  *)
    (* iFrame "HR". *)
    (* iIntros (lk γ') "#Hlk". *)
    (* wp_let.  *)
    (* iClear "Hfrag". (* HFrag should be handled to user? *)  *)
    (* iVsIntro. iExists γ. iAlways. *)
    (* rewrite /is_pcas. *)
    (* iIntros (a b P Q) "#H".  *)
    (* iAlways. iIntros "HP". *)
    (* repeat wp_let. *)
    (* wp_bind (acquire _). *)
    (* iApply acquire_spec. *)
    (* iFrame "Hlk". iIntros "Hlked Hls". *)
    (* iDestruct "Hls" as (x1 x2) "(Hl1 & Hl2 & HFulla)". *)
    (* wp_seq. *)
    (* wp_bind ((pcas_seq _) _). *)
    (* iApply (pcas_seq_spec with "[Hlked HP Hl1 Hl2 HFulla]"); try auto. *)
    (* iFrame "Hh". rewrite /ϕ. iCombine "Hl1" "Hl2" as "Hl". *)
    (* instantiate (H2:=(x1, x2)). iFrame. *)
    (* iIntros (v xs') "[Hl1 Hl2] Hβ". *)
    (* wp_let. wp_bind (release _). wp_let. *)
    (* iDestruct ("H" $! (x1, x2) xs' v) as "[Hvs1 Hvs2]". *)
    (* iVs ("Hvs1" with "HP") as "Hfraga". (* XXX: this Hfraga might be too strong *) *)
    (* iCombine "HFulla" "Hfraga" as "Ha". *)
    (* iVs (own_update with "Ha") as "Hb". *)
    (* { instantiate (H3:=(gFullR xs' ⋅ gFragR xs')). *)
    (*   apply update_a. eauto. } *)
    
    (* (* I should have full access to lk now ... shit *) *)
    (* iAssert (∃ lkl: loc, #lkl = lk ★ lkl ↦ #true)%I as "Hlkl". *)
    (* { admit. } *)
    (* iDestruct "Hlkl" as (lkl) "[% Hlkl]". subst. *)
    (* wp_store. (* now I just simply discard the things ... *) *)
    (* iDestruct (own_op with "Hb") as "[HFullb HFragb]". *)
    (* iVs ("Hvs2" with "[Hβ HFragb]"). *)
    (* { rewrite /gFrag. by iFrame. } *)
    (* by iVsIntro. *)
  Admitted.

  End triple.
End generic.

Section atomic_pair.
  Context `{!heapG Σ, !lockG Σ, !(@syncG (val * val) _ Σ)} (N : namespace).
  
  Definition pcas_seq : val :=
    λ: "ls" "ab",
       if: !(Fst "ls") = Fst "ab"
         then if: !(Snd "ls") = Fst "ab"
                then Fst "ls" <- Snd "ab";; Snd "ls" <- Snd "ab";; #true
                else #false
         else #false.

  Local Opaque pcas_seq.
  
  Definition ϕ (l1 l2: loc) (xs: val * val) : iProp Σ := (l1 ↦ fst xs ★ l2 ↦ snd xs)%I.

  Definition β (a b: val) (xs xs': val * val) (v: val) : iProp Σ :=
    (■ ((v = #true  ∧ fst xs = a ∧ snd xs = a ∧ fst xs' = b ∧ snd xs' = b) ∨
        (v = #false ∧ (fst xs ≠ a ∨ snd xs ≠ a) ∧ xs = xs')))%I.

  Local Opaque β.
  
  Lemma pcas_seq_spec (a b: val) (xs xs': val * val) ls:
    ∀ (Φ: val → iProp Σ) (l1 l2: loc),
      heapN ⊥ N → to_val ls = Some (#l1, #l2)%V →
      heap_ctx ★ ϕ l1 l2 xs ★ (∀ v xs', ϕ l1 l2 xs' -★ β a b xs xs' v -★ Φ v)
      ⊢ WP pcas_seq ls (a, b) {{ Φ }}.
  Proof.
    rewrite /ϕ.
    iIntros (Φ l1 l2 HN Hls) "(#Hh & (Hl1 & Hl2) & HΦ)".
    wp_value. iVsIntro. 
    wp_seq. repeat wp_let.
    subst. wp_proj. wp_load.
    wp_proj. wp_op=>[?|Hx1na].
    - subst.
      wp_if. wp_proj. wp_load. wp_proj.
      wp_op=>[?|Hx2na]. subst.
      + wp_if. wp_proj. wp_proj. wp_store. wp_proj. wp_proj. wp_store.
        iDestruct ("HΦ" $! #true (b, b)) as "H".
        iApply ("H" with "[Hl1 Hl2]"); first by iFrame.
        rewrite /β.
        iPureIntro. left. eauto.
      + wp_if.
        iDestruct ("HΦ" $! #false xs) as "H".
        iApply ("H" with "[Hl1 Hl2]"); first by iFrame.
        rewrite /β.
        iPureIntro. right. eauto.
    - subst.
      wp_if.
      iDestruct ("HΦ" $! #false xs) as "H".
      iApply ("H" with "[Hl1 Hl2]"); first by iFrame.
      rewrite /β.
      iPureIntro. right. eauto.
  Qed.

  Definition is_pcas γ (f: val): iProp Σ :=
    (∀ a b: val, atomic_triple' (β a b) ⊤ (⊤) (f (a, b)%V) γ)%I.

  Lemma pcas_atomic_spec:
    heapN ⊥ N → heap_ctx ⊢ WP mk_sync' (λ: <>, (ref #0, ref #0))%V pcas_seq {{ f, ∃ γ, □ is_pcas γ f }}.
  Proof.
    iIntros (HN) "#Hh". repeat wp_let.
    wp_alloc l1 as "Hl1".
    wp_alloc l2 as "Hl2".
    iVs (own_alloc (gFullR (#0, #0) ⋅ gFragR (#0, #0))) as (γ) "Hγ"; first by done.
    wp_let. 
    iDestruct (own_op with "Hγ") as "[Hfull Hfrag]".
    iAssert (∃ x1 x2, l1 ↦ x1 ★ l2 ↦ x2 ★ gFull γ (x1, x2))%I with "[-Hfrag]" as "HR".
    { iExists #0, #0. by iFrame. }
    wp_bind (newlock _). iApply newlock_spec=>//. 
    iFrame "Hh". 
    iFrame "HR".
    iIntros (lk γ') "#Hlk".
    wp_let. 
    iClear "Hfrag". (* HFrag should be handled to user? *) 
    iVsIntro. iExists γ. iAlways.
    rewrite /is_pcas.
    iIntros (a b P Q) "#H". 
    iAlways. iIntros "HP".
    repeat wp_let.
    wp_bind (acquire _).
    iApply acquire_spec.
    iFrame "Hlk". iIntros "Hlked Hls".
    iDestruct "Hls" as (x1 x2) "(Hl1 & Hl2 & HFulla)".
    wp_seq.
    wp_bind ((pcas_seq _) _).
    iApply (pcas_seq_spec with "[Hlked HP Hl1 Hl2 HFulla]"); try auto.
    iFrame "Hh". rewrite /ϕ. iCombine "Hl1" "Hl2" as "Hl".
    instantiate (H2:=(x1, x2)). iFrame.
    iIntros (v xs') "[Hl1 Hl2] Hβ".
    wp_let. wp_bind (release _). wp_let.
    iDestruct ("H" $! (x1, x2) xs' v) as "[Hvs1 Hvs2]".
    iVs ("Hvs1" with "HP") as "Hfraga". (* XXX: this Hfraga might be too strong *)
    iCombine "HFulla" "Hfraga" as "Ha".
    iVs (own_update with "Ha") as "Hb".
    { instantiate (H3:=(gFullR xs' ⋅ gFragR xs')).
      apply update_a. eauto. }
    
    (* I should have full access to lk now ... shit *)
    iAssert (∃ lkl: loc, #lkl = lk ★ lkl ↦ #true)%I as "Hlkl".
    { admit. }
    iDestruct "Hlkl" as (lkl) "[% Hlkl]". subst.
    wp_store. (* now I just simply discard the things ... *)
    iDestruct (own_op with "Hb") as "[HFullb HFragb]".
    iVs ("Hvs2" with "[Hβ HFragb]").
    { rewrite /gFrag. by iFrame. }
    by iVsIntro.
Admitted.
    
End atomic_pair.

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
