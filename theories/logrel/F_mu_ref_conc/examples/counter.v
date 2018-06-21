From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth list.
From iris_examples.logrel.F_mu_ref_conc Require Export examples.lock.
From iris_examples.logrel.F_mu_ref_conc Require Import soundness_binary.
From iris.program_logic Require Import adequacy.

Definition CG_increment (x : expr) : expr :=
  Rec (Store x.[ren (+ 2)] (BinOp Add (#n 1) (Load x.[ren (+ 2)]))).

Definition CG_locked_increment (x l : expr) : expr :=
  with_lock (CG_increment x) l.
Definition CG_locked_incrementV (x l : expr) : val :=
  with_lockV (CG_increment x) l.

Definition counter_read (x : expr) : expr := Rec (Load x.[ren (+2)]).
Definition counter_readV (x : expr) : val := RecV (Load x.[ren (+2)]).

Definition CG_counter_body (x l : expr) : expr :=
  Pair (CG_locked_increment x l) (counter_read x).
Definition CG_counter : expr :=
  App
    (Rec $ App (Rec (CG_counter_body (Var 1) (Var 3)))
               (Alloc (#n 0)))
    newlock.

Definition FG_increment (x : expr) : expr :=
  Rec $ App
    (Rec $
      (* try increment *)
      If (CAS x.[ren (+4)] (Var 1) (BinOp Add (#n 1) (Var 1)))
          Unit (* increment succeeds we return unit *)
          (App (Var 2) (Var 3)) (* increment fails, we try again *))
    (Load x.[ren (+2)]) (* read the counter *).
Definition FG_counter_body (x : expr) : expr :=
  Pair (FG_increment x) (counter_read x).
Definition FG_counter : expr :=
  App (Rec (FG_counter_body (Var 1))) (Alloc (#n 0)).

Section CG_Counter.
  Context `{heapIG Σ, cfgSG Σ}.

  Notation D := (prodC valC valC -n> iProp Σ).
  Implicit Types Δ : listC D.

  (* Coarse-grained increment *)
  Lemma CG_increment_type x Γ :
    typed Γ x (Tref TNat) →
    typed Γ (CG_increment x) (TArrow TUnit TUnit).
  Proof.
    intros H1. repeat econstructor.
    - eapply (context_weakening [_; _]); eauto.
    - eapply (context_weakening [_; _]); eauto.
  Qed.

  Lemma CG_increment_closed (x : expr) :
    (∀ f, x.[f] = x) → ∀ f, (CG_increment x).[f] = CG_increment x.
  Proof. intros Hx f. unfold CG_increment. asimpl. rewrite ?Hx; trivial. Qed.

  Lemma CG_increment_subst (x : expr) f :
    (CG_increment x).[f] = CG_increment x.[f].
  Proof. unfold CG_increment; asimpl; trivial. Qed.

  Lemma steps_CG_increment E ρ j K x n:
    nclose specN ⊆ E →
    spec_ctx ρ ∗ x ↦ₛ (#nv n) ∗ j ⤇ fill K (App (CG_increment (Loc x)) Unit)
      ⊢ |={E}=> j ⤇ fill K (Unit) ∗ x ↦ₛ (#nv (S n)).
  Proof.
    iIntros (HNE) "[#Hspec [Hx Hj]]". unfold CG_increment.
    iMod (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iMod (step_load _ _ j ((BinOpRCtx _ (#nv _) :: StoreRCtx (LocV _) :: K))
                    _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    simpl. iFrame "Hspec Hj"; trivial.
    simpl.
    iMod (step_nat_binop _ _ j ((StoreRCtx (LocV _)) :: K)
                          _ _ _  with "[Hj]") as "Hj"; eauto.
    simpl.
    iMod (step_store _ _ j K _ _ _ _ _ with "[Hj Hx]") as "[Hj Hx]"; eauto.
    iFrame "Hspec Hj"; trivial.
    iModIntro.
    iFrame "Hj Hx"; trivial.
    Unshelve. all: trivial.
  Qed.

  Global Opaque CG_increment.

  Lemma CG_locked_increment_to_val x l :
    to_val (CG_locked_increment x l) = Some (CG_locked_incrementV x l).
  Proof. by rewrite with_lock_to_val. Qed.

  Lemma CG_locked_increment_of_val x l :
    of_val (CG_locked_incrementV x l) = CG_locked_increment x l.
  Proof. by rewrite with_lock_of_val. Qed.

  Global Opaque CG_locked_incrementV.

  Lemma CG_locked_increment_type x l Γ :
    typed Γ x (Tref TNat) →
    typed Γ l LockType →
    typed Γ (CG_locked_increment x l) (TArrow TUnit TUnit).
  Proof.
    intros H1 H2. repeat econstructor.
    eapply with_lock_type; auto using CG_increment_type.
  Qed.

  Lemma CG_locked_increment_closed (x l : expr) :
    (∀ f, x.[f] = x) → (∀ f, l.[f] = l) →
    ∀ f, (CG_locked_increment x l).[f] = CG_locked_increment x l.
  Proof.
    intros H1 H2 f. asimpl. unfold CG_locked_increment.
    rewrite with_lock_closed; trivial. apply CG_increment_closed; trivial.
  Qed.

  Lemma CG_locked_increment_subst (x l : expr) f :
  (CG_locked_increment x l).[f] = CG_locked_increment x.[f] l.[f].
  Proof.
    unfold CG_locked_increment. simpl.
    rewrite with_lock_subst CG_increment_subst. asimpl; trivial.
  Qed.

  Lemma steps_CG_locked_increment E ρ j K x n l :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ x ↦ₛ (#nv n) ∗ l ↦ₛ (#♭v false)
      ∗ j ⤇ fill K (App (CG_locked_increment (Loc x) (Loc l)) Unit)
    ={E}=∗ j ⤇ fill K Unit ∗ x ↦ₛ (#nv S n) ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE) "[#Hspec [Hx [Hl Hj]]]".
    iMod (steps_with_lock
            _ _ j K _ _ _ _ UnitV UnitV _ _ with "[Hj Hx Hl]") as "Hj"; last done.
    - iIntros (K') "[#Hspec Hxj]".
      iApply steps_CG_increment; first done. iFrame. trivial.
    - by iFrame "Hspec Hj Hx".
      Unshelve. all: trivial.
  Qed.

  Global Opaque CG_locked_increment.

  Lemma counter_read_to_val x : to_val (counter_read x) = Some (counter_readV x).
  Proof. trivial. Qed.

  Lemma counter_read_of_val x : of_val (counter_readV x) = counter_read x.
  Proof. trivial. Qed.

  Global Opaque counter_readV.

  Lemma counter_read_type x Γ :
    typed Γ x (Tref TNat) → typed Γ (counter_read x) (TArrow TUnit TNat).
  Proof.
    intros H1. repeat econstructor.
    eapply (context_weakening [_; _]); trivial.
  Qed.

  Lemma counter_read_closed (x : expr) :
    (∀ f, x.[f] = x) → ∀ f, (counter_read x).[f] = counter_read x.
  Proof. intros H1 f. asimpl. unfold counter_read. by rewrite ?H1. Qed.

  Lemma counter_read_subst (x: expr) f :
    (counter_read x).[f] = counter_read x.[f].
  Proof. unfold counter_read. by asimpl. Qed.

  Lemma steps_counter_read E ρ j K x n :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ x ↦ₛ (#nv n)
               ∗ j ⤇ fill K (App (counter_read (Loc x)) Unit)
    ={E}=∗ j ⤇ fill K (#n n) ∗ x ↦ₛ (#nv n).
  Proof.
    intros HNE. iIntros "[#Hspec [Hx Hj]]". unfold counter_read.
    iMod (step_rec _ _ j K _ Unit with "[Hj]") as "Hj"; eauto.
    iAsimpl.
    iMod (step_load _ _ j K with "[Hj Hx]") as "[Hj Hx]"; eauto.
    { by iFrame "Hspec Hj". }
    iModIntro. by iFrame "Hj Hx".
  Qed.

  Opaque counter_read.

  Lemma CG_counter_body_type x l Γ :
    typed Γ x (Tref TNat) →
    typed Γ l LockType →
    typed Γ (CG_counter_body x l)
            (TProd (TArrow TUnit TUnit) (TArrow TUnit TNat)).
  Proof.
    intros H1 H2; repeat econstructor;
      eauto using CG_locked_increment_type, counter_read_type.
  Qed.

  Lemma CG_counter_body_closed (x l : expr) :
    (∀ f, x.[f] = x) → (∀ f, l.[f] = l) →
    ∀ f, (CG_counter_body x l).[f] = CG_counter_body x l.
  Proof.
    intros H1 H2 f. asimpl.
    rewrite CG_locked_increment_closed; trivial. by rewrite counter_read_closed.
  Qed.

  Lemma CG_counter_type Γ :
    typed Γ CG_counter (TProd (TArrow TUnit TUnit) (TArrow TUnit TNat)).
  Proof.
    econstructor; eauto using newlock_type.
    do 2 econstructor; [|do 2 constructor].
    constructor. apply CG_counter_body_type; by constructor.
  Qed.

  Lemma CG_counter_closed f : CG_counter.[f] = CG_counter.
  Proof.
    asimpl; rewrite CG_locked_increment_subst counter_read_subst; by asimpl.
  Qed.

  (* Fine-grained increment *)
  Lemma FG_increment_type x Γ :
    typed Γ x (Tref TNat) →
    typed Γ (FG_increment x) (TArrow TUnit TUnit).
  Proof.
    intros H1. do 3 econstructor.
    do 2 econstructor; eauto using EqTNat.
    - eapply (context_weakening [_; _; _; _]); eauto.
    - by constructor.
    - repeat constructor.
    - by constructor.
    - by constructor.
    - eapply (context_weakening [_; _]); eauto.
  Qed.

  Lemma FG_increment_closed (x : expr) :
    (∀ f, x.[f] = x) → ∀ f, (FG_increment x).[f] = FG_increment x.
  Proof. intros Hx f. asimpl. unfold FG_increment. rewrite ?Hx; trivial. Qed.

  Lemma FG_counter_body_type x Γ :
    typed Γ x (Tref TNat) →
    typed Γ (FG_counter_body x)
            (TProd (TArrow TUnit TUnit) (TArrow TUnit TNat)).
  Proof.
    intros H1; econstructor.
    - apply FG_increment_type; trivial.
    - apply counter_read_type; trivial.
  Qed.

  Lemma FG_counter_body_closed (x : expr) :
    (∀ f, x.[f] = x) →
    ∀ f, (FG_counter_body x).[f] = FG_counter_body x.
  Proof.
    intros H1 f. asimpl. unfold FG_counter_body, FG_increment.
    rewrite ?H1. by rewrite counter_read_closed.
  Qed.

  Lemma FG_counter_type Γ :
    typed Γ FG_counter (TProd (TArrow TUnit TUnit) (TArrow TUnit TNat)).
  Proof.
    econstructor; eauto using newlock_type, typed.
    constructor. apply FG_counter_body_type; by constructor.
  Qed.

  Lemma FG_counter_closed f : FG_counter.[f] = FG_counter.
  Proof. asimpl; rewrite counter_read_subst; by asimpl. Qed.

  Definition counterN : namespace := nroot .@ "counter".

  Lemma FG_CG_counter_refinement :
    [] ⊨ FG_counter ≤log≤ CG_counter : TProd (TArrow TUnit TUnit) (TArrow TUnit TNat).
  Proof.
    iIntros (Δ [|??] ρ ?) "#(Hspec & HΓ)"; iIntros (j K) "Hj"; last first.
    { iDestruct (interp_env_length with "HΓ") as %[=]. }
    iClear "HΓ". cbn -[FG_counter CG_counter].
    rewrite ?empty_env_subst /CG_counter /FG_counter.
    iApply fupd_wp.
    iMod (steps_newlock _ _ j ((AppRCtx (RecV _)) :: K) _ with "[Hj]")
      as (l) "[Hj Hl]"; eauto.
    iMod (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iAsimpl. rewrite CG_locked_increment_subst /=.
    rewrite counter_read_subst /=.
    iMod (step_alloc _ _ j ((AppRCtx (RecV _)) :: K) _ _ _ _ with "[Hj]")
      as (cnt') "[Hj Hcnt']"; eauto.
    iMod (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    iAsimpl. rewrite CG_locked_increment_subst /=.
    rewrite counter_read_subst /=.
    Unshelve.
    all: try match goal with |- to_val _ = _ => auto using to_of_val end.
    all: trivial.
    iApply (wp_bind (fill [AppRCtx (RecV _)])).
    iApply wp_wand_l. iSplitR; [iModIntro; iIntros (v) "Hv"; iExact "Hv"|].
    iApply (wp_alloc); trivial; iFrame "#"; iModIntro; iNext; iIntros (cnt) "Hcnt /=".
    (* establishing the invariant *)
    iAssert ((∃ n, l ↦ₛ (#♭v false) ∗ cnt ↦ᵢ (#nv n) ∗ cnt' ↦ₛ (#nv n) )%I)
      with "[Hl Hcnt Hcnt']" as "Hinv".
    { iExists _. by iFrame. }
    iApply fupd_wp.
    iMod (inv_alloc counterN with "[Hinv]") as "#Hinv"; [iNext; iExact "Hinv"|].
    (* splitting increment and read *)
    iApply wp_pure_step_later; trivial. iModIntro. iNext. iAsimpl.
    rewrite counter_read_subst /=.
    iApply wp_value; auto.
    iExists (PairV (CG_locked_incrementV _ _) (counter_readV _)); simpl.
    rewrite CG_locked_increment_of_val counter_read_of_val.
    iFrame "Hj".
    iExists (_, _), (_, _); simpl; repeat iSplit; trivial.
    - (* refinement of increment *)
      iAlways. clear j K. iIntros (v) "#Heq". iIntros (j K) "Hj".
      rewrite CG_locked_increment_of_val /=.
      destruct v; iDestruct "Heq" as "[% %]"; simplify_eq/=.
      iLöb as "Hlat".
      iApply wp_pure_step_later; trivial. iAsimpl. iNext.
      (* fine-grained reads the counter *)
      iApply (wp_bind (fill [AppRCtx (RecV _)]));
        iApply wp_wand_l; iSplitR; [iIntros (v) "Hv"; iExact "Hv"|].
      iApply wp_atomic; eauto.
      iInv counterN as (n) ">[Hl [Hcnt Hcnt']]" "Hclose".
      iApply (wp_load with "[Hcnt]"); [iNext; by iFrame|].
      iModIntro. iNext. iIntros "Hcnt".
      iMod ("Hclose" with "[Hl Hcnt Hcnt']").
      { iNext. iExists _. iFrame "Hl Hcnt Hcnt'". }
      iApply wp_pure_step_later; trivial. iAsimpl. iModIntro. iNext.
      (* fine-grained performs increment *)
      iApply (wp_bind (fill [CasRCtx (LocV _) (NatV _); IfCtx _ _]));
        iApply wp_wand_l; iSplitR; [iIntros (v) "Hv"; iExact "Hv"|].
      iApply wp_pure_step_later; auto. iApply wp_value.
      iNext.
      iApply (wp_bind (fill [IfCtx _ _]));
        iApply wp_wand_l; iSplitR; [iIntros (v) "Hv"; iExact "Hv"|].
      iApply wp_atomic; eauto.
      iInv counterN as (n') ">[Hl [Hcnt Hcnt']]" "Hclose".
      (* performing CAS *)
      destruct (decide (n = n')) as [|Hneq]; subst.
      + (* CAS succeeds *)
        (* In this case, we perform increment in the coarse-grained one *)
        iMod (steps_CG_locked_increment
                _ _ _ _ _ _ _ _ with "[Hj Hl Hcnt']") as "[Hj [Hcnt' Hl]]".
        { iFrame "Hspec Hcnt' Hl Hj"; trivial. }
        iApply (wp_cas_suc with "[Hcnt]"); auto.
        iModIntro. iNext. iIntros "Hcnt".
        iMod ("Hclose" with "[Hl Hcnt Hcnt']").
        { iNext. iExists _. iFrame "Hl Hcnt Hcnt'"; trivial. }
        simpl.
        iApply wp_pure_step_later; trivial.
        iModIntro. iNext. iApply wp_value; trivial.
        iExists UnitV; iFrame; auto.
      + (* CAS fails *)
        (* In this case, we perform a recursive call *)
        iApply (wp_cas_fail _ _ _ (#nv n') with "[Hcnt]"); auto;
        [inversion 1; subst; auto | ].
        iModIntro. iNext. iIntros "Hcnt".
        iMod ("Hclose" with "[Hl Hcnt Hcnt']").
        { iNext. iExists _; iFrame "Hl Hcnt Hcnt'". }
        iApply wp_pure_step_later; trivial. iModIntro. iNext. by iApply "Hlat".
    - (* refinement of read *)
      iAlways. clear j K. iIntros (v) "#Heq". iIntros (j K) "Hj".
      rewrite ?counter_read_of_val.
      iDestruct "Heq" as "[% %]"; destruct v; simplify_eq/=.
      Transparent counter_read.
      unfold counter_read.
      iApply wp_pure_step_later; trivial. simpl.
      iNext.
      iApply wp_atomic; eauto.
      iInv counterN as (n) ">[Hl [Hcnt Hcnt']]" "Hclose".
      iMod (steps_counter_read with "[Hj Hcnt']") as "[Hj Hcnt']"; first by solve_ndisj.
      { by iFrame "Hspec Hcnt' Hj". }
      iApply (wp_load with "[Hcnt]"); eauto.
      iModIntro. iNext. iIntros "Hcnt".
      iMod ("Hclose" with "[Hl Hcnt Hcnt']").
      { iNext. iExists _; iFrame "Hl Hcnt Hcnt'". }
      iExists (#nv _); eauto.
      Unshelve. solve_ndisj.
  Qed.
End CG_Counter.

Theorem counter_ctx_refinement :
  [] ⊨ FG_counter ≤ctx≤ CG_counter :
         TProd (TArrow TUnit TUnit) (TArrow TUnit TNat).
Proof.
  set (Σ := #[invΣ ; gen_heapΣ loc val ; GFunctor (authR cfgUR) ]).
  set (HG := soundness_unary.HeapPreIG Σ _ _).
  eapply (binary_soundness Σ _); auto using FG_counter_type, CG_counter_type.
  intros. apply FG_CG_counter_refinement.
Qed.
