From iris.proofmode Require Import tactics.
From iris_examples.logrel.F_mu_ref_conc Require Export rules_binary typing.
From iris.base_logic Require Import namespaces.

(** [newlock = alloc false] *)
Definition newlock : expr := Alloc (#♭ false).
(** [acquire = λ x. if cas(x, false, true) then #() else acquire(x) ] *)
Definition acquire : expr :=
  Rec (If (CAS (Var 1) (#♭ false) (#♭ true)) (Unit) (App (Var 0) (Var 1))).
(** [release = λ x. x <- false] *)
Definition release : expr := Rec (Store (Var 1) (#♭ false)).
(** [with_lock e l = λ x. (acquire l) ;; e x ;; (release l)] *)
Definition with_lock (e : expr) (l : expr) : expr :=
  Rec
    (App (Rec (App (Rec (App (Rec (Var 3)) (App release l.[ren (+6)])))
                   (App e.[ren (+4)] (Var 3))))
         (App acquire l.[ren (+2)])
    ).

Definition with_lockV (e l : expr) : val :=
  RecV
    (App (Rec (App (Rec (App (Rec (Var 3)) (App release l.[ren (+6)])))
                   (App e.[ren (+4)] (Var 3))))
         (App acquire l.[ren (+2)])
    ).

Lemma with_lock_to_val e l : to_val (with_lock e l) = Some (with_lockV e l).
Proof. trivial. Qed.

Lemma with_lock_of_val e l : of_val (with_lockV e l) = with_lock e l.
Proof. trivial. Qed.

Global Opaque with_lockV.

Lemma newlock_closed f : newlock.[f] = newlock.
Proof. by asimpl. Qed.
Hint Rewrite newlock_closed : autosubst.

Lemma acquire_closed f : acquire.[f] = acquire.
Proof. by asimpl. Qed.
Hint Rewrite acquire_closed : autosubst.

Lemma release_closed f : release.[f] = release.
Proof. by asimpl. Qed.
Hint Rewrite release_closed : autosubst.

Lemma with_lock_subst (e l : expr) f :  (with_lock e l).[f] = with_lock e.[f] l.[f].
Proof. unfold with_lock; asimpl; trivial. Qed.

Lemma with_lock_closed e l:
  (∀ f : var → expr, e.[f] = e) →
  (∀ f : var → expr, l.[f] = l) →
  ∀ f, (with_lock e l).[f] = with_lock e l.
Proof. asimpl => H1 H2 f. unfold with_lock. by rewrite ?H1 ?H2. Qed.

Definition LockType := Tref TBool.

Lemma newlock_type Γ : typed Γ newlock LockType.
Proof. repeat constructor. Qed.

Lemma acquire_type Γ : typed Γ acquire (TArrow LockType TUnit).
Proof. do 3 econstructor; eauto using EqTBool; repeat constructor. Qed.

Lemma release_type Γ : typed Γ release (TArrow LockType TUnit).
Proof. repeat econstructor. Qed.

Lemma with_lock_type e l Γ τ τ' :
  typed Γ e (TArrow τ τ') →
  typed Γ l LockType →
  typed Γ (with_lock e l) (TArrow τ τ').
Proof.
  intros H1 H2. do 3 econstructor; eauto.
  - repeat (econstructor; eauto using release_type).
    + eapply (context_weakening [_; _; _; _; _; _]); eauto.
    + eapply (context_weakening [_; _; _; _]); eauto.
  - eapply acquire_type.
  - eapply (context_weakening [_; _]); eauto.
Qed.

Section proof.
  Context `{cfgSG Σ}.
  Context `{heapIG Σ}.
  
  Lemma steps_newlock E ρ j K :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ j ⤇ fill K newlock
      ⊢ |={E}=> ∃ l, j ⤇ fill K (Loc l) ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE) "[#Hspec Hj]".
    by iMod (step_alloc _ _ j K with "[Hj]") as "Hj"; eauto.
  Qed.

  Global Opaque newlock.

  Lemma steps_acquire E ρ j K l :
    nclose specN ⊆ E →
    spec_ctx ρ ∗ l ↦ₛ (#♭v false) ∗ j ⤇ fill K (App acquire (Loc l))
      ⊢ |={E}=> j ⤇ fill K Unit ∗ l ↦ₛ (#♭v true).
  Proof.
    iIntros (HNE) "[#Hspec [Hl Hj]]". unfold acquire.
    iMod (step_rec _ _ j K with "[Hj]") as "Hj"; eauto. done.
    iMod (step_cas_suc _ _ j ((IfCtx _ _) :: K)
                       _ _ _ _ _ _ _ _ _ with "[Hj Hl]") as "[Hj Hl]"; trivial.
    { simpl. iFrame "Hspec Hj Hl"; eauto. }
    iMod (step_if_true _ _ j K _ _ _ with "[Hj]") as "Hj"; trivial.
    { by iFrame. }
    by iIntros "!> {$Hj $Hl}".
    Unshelve. all:trivial.
  Qed.

  Global Opaque acquire.

  Lemma steps_release E ρ j K l b:
    nclose specN ⊆ E →
    spec_ctx ρ ∗ l ↦ₛ (#♭v b) ∗ j ⤇ fill K (App release (Loc l))
      ⊢ |={E}=> j ⤇ fill K Unit ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE) "[#Hspec [Hl Hj]]". unfold release.
    iMod (step_rec _ _ j K with "[Hj]") as "Hj"; eauto; try done.
    iMod (step_store _ _ j K _ _ _ _ _ with "[Hj Hl]") as "[Hj Hl]"; eauto.
    { by iFrame. }
    by iIntros "!> {$Hj $Hl}".
    Unshelve. all: trivial.
  Qed.

  Global Opaque release.

  Lemma steps_with_lock E ρ j K e l P Q v w:
    nclose specN ⊆ E →
    (∀ f, e.[f] = e) (* e is a closed term *) →
    (∀ K', spec_ctx ρ ∗ P ∗ j ⤇ fill K' (App e (of_val w))
            ⊢ |={E}=> j ⤇ fill K' (of_val v) ∗ Q) →
    spec_ctx ρ ∗ P ∗ l ↦ₛ (#♭v false)
                ∗ j ⤇ fill K (App (with_lock e (Loc l)) (of_val w))
      ⊢ |={E}=> j ⤇ fill K (of_val v) ∗ Q ∗ l ↦ₛ (#♭v false).
  Proof.
    iIntros (HNE H1 H2) "[#Hspec [HP [Hl Hj]]]".
    iMod (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl. rewrite H1.
    iMod (steps_acquire _ _ j ((AppRCtx (RecV _)) :: K)
                   _ _ with "[Hj Hl]") as "[Hj Hl]"; eauto.
    { simpl. iFrame "Hspec Hj Hl"; eauto. }
    simpl.
    iMod (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl. rewrite H1.
    iMod (H2 ((AppRCtx (RecV _)) :: K) with "[Hj HP]") as "[Hj HQ]"; eauto.
    { simpl. iFrame "Hspec Hj HP"; eauto. }
    simpl.
    iMod (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl.
    iMod (steps_release _ _ j ((AppRCtx (RecV _)) :: K) _ _ with "[Hj Hl]")
      as "[Hj Hl]"; eauto.
    { simpl. by iFrame. }
    rewrite ?fill_app /=.
    iMod (step_rec _ _ j K _ _ _ _ with "[Hj]") as "Hj"; eauto.
    asimpl. iModIntro; by iFrame.
    Unshelve.
    all: try match goal with |- to_val _ = _ => auto using to_of_val end.
    trivial.
  Qed.

  Global Opaque with_lock.
End proof.
