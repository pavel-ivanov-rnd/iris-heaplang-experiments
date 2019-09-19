From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Export invariants.
From iris_examples.logrel.F_mu_ref Require Export rules_binary typing.
From iris.algebra Require Import list.
From stdpp Require Import tactics.
Import uPred.

(* HACK: move somewhere else *)
Ltac auto_equiv :=
  (* Deal with "pointwise_relation" *)
  repeat lazymatch goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  end;
  (* Normalize away equalities. *)
  repeat match goal with
  | H : _ ≡{_}≡ _ |-  _ => apply (discrete_iff _ _) in H
  | _ => progress simplify_eq
  end;
  (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
  try (f_equiv; fast_done || auto_equiv).

Definition logN : namespace := nroot .@ "logN".

(** interp : is a unary logical relation. *)
Section logrel.
  Context `{heapG Σ, cfgSG Σ}.
  Notation D := (prodO valO valO -n> iPropO Σ).
  Implicit Types τi : D.
  Implicit Types Δ : listO D.
  Implicit Types interp : listO D → D.

  Definition interp_expr (τi : listO D -n> D) (Δ : listO D)
      (ee : expr * expr) : iProp Σ := (∀ K,
    ⤇ fill K (ee.2) →
    WP ee.1 {{ v, ∃ v', ⤇ fill K (of_val v') ∗ τi Δ (v, v') }})%I.
  Global Instance interp_expr_ne n :
    Proper (dist n ==> dist n ==> (=) ==> dist n) interp_expr.
  Proof. solve_proper. Qed.

  Program Definition ctx_lookup (x : var) : listO D -n> D := λne Δ,
    from_option id (cconst True)%I (Δ !! x).
  Solve Obligations with solve_proper.

  Program Definition interp_unit : listO D -n> D := λne Δ ww,
    (⌜ww.1 = UnitV⌝ ∧ ⌜ww.2 = UnitV⌝)%I.
  Solve Obligations with solve_proper_alt.

  Program Definition interp_prod
      (interp1 interp2 : listO D -n> D) : listO D -n> D := λne Δ ww,
    (∃ vv1 vv2, ⌜ww = (PairV (vv1.1) (vv2.1), PairV (vv1.2) (vv2.2))⌝ ∧
                interp1 Δ vv1 ∧ interp2 Δ vv2)%I.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Program Definition interp_sum
      (interp1 interp2 : listO D -n> D) : listO D -n> D := λne Δ ww,
    ((∃ vv, ⌜ww = (InjLV (vv.1), InjLV (vv.2))⌝ ∧ interp1 Δ vv) ∨
     (∃ vv, ⌜ww = (InjRV (vv.1), InjRV (vv.2))⌝ ∧ interp2 Δ vv))%I.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Program Definition interp_arrow
          (interp1 interp2 : listO D -n> D) : listO D -n> D :=
    λne Δ ww,
    (□ ∀ vv, interp1 Δ vv →
             interp_expr
               interp2 Δ (App (of_val (ww.1)) (of_val (vv.1)),
                          App (of_val (ww.2)) (of_val (vv.2))))%I.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Program Definition interp_forall
      (interp : listO D -n> D) : listO D -n> D := λne Δ ww,
    (□ ∀ τi,
          ⌜∀ ww, Persistent (τi ww)⌝ →
          interp_expr
            interp (τi :: Δ) (TApp (of_val (ww.1)), TApp (of_val (ww.2))))%I.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Program Definition interp_rec1
      (interp : listO D -n> D) (Δ : listO D) (τi : D) : D := λne ww,
    (□ ∃ vv, ⌜ww = (FoldV (vv.1), FoldV (vv.2))⌝ ∧ ▷ interp (τi :: Δ) vv)%I.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Global Instance interp_rec1_contractive
    (interp : listO D -n> D) (Δ : listO D) : Contractive (interp_rec1 interp Δ).
  Proof. by solve_contractive. Qed.

  Lemma fixpoint_interp_rec1_eq (interp : listO D -n> D) Δ x :
    fixpoint (interp_rec1 interp Δ) x ≡ interp_rec1 interp Δ (fixpoint (interp_rec1 interp Δ)) x.
  Proof. exact: (fixpoint_unfold (interp_rec1 interp Δ) x). Qed.

  Program Definition interp_rec (interp : listO D -n> D) : listO D -n> D := λne Δ,
    fixpoint (interp_rec1 interp Δ).
  Next Obligation.
    intros interp n Δ1 Δ2 HΔ; apply fixpoint_ne => τi ww. solve_proper.
  Qed.

  Program Definition interp_ref_inv (ll : loc * loc) : D -n> iPropO Σ := λne τi,
    (∃ vv, ll.1 ↦ vv.1 ∗ ll.2 ↦ₛ vv.2 ∗ τi vv)%I.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Program Definition interp_ref
      (interp : listO D -n> D) : listO D -n> D := λne Δ ww,
    (∃ ll, ⌜ww = (LocV (ll.1), LocV (ll.2))⌝ ∧
           inv (logN .@ ll) (interp_ref_inv ll (interp Δ)))%I.
  Solve Obligations with repeat intros ?; simpl; auto_equiv.

  Fixpoint interp (τ : type) : listO D -n> D :=
    match τ return _ with
    | TUnit => interp_unit
    | TProd τ1 τ2 => interp_prod (interp τ1) (interp τ2)
    | TSum τ1 τ2 => interp_sum (interp τ1) (interp τ2)
    | TArrow τ1 τ2 => interp_arrow (interp τ1) (interp τ2)
    | TVar x => ctx_lookup x
    | TForall τ' => interp_forall (interp τ')
    | TRec τ' => interp_rec (interp τ')
    | Tref τ' => interp_ref (interp τ')
    end.
  Notation "⟦ τ ⟧" := (interp τ).

  Definition interp_env (Γ : list type)
      (Δ : listO D) (vvs : list (val * val)) : iProp Σ :=
    (⌜length Γ = length vvs⌝ ∗ [∗] zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vvs)%I.
  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Class env_Persistent Δ :=
    ctx_persistentP : Forall (λ τi, ∀ vv, Persistent (τi vv)) Δ.
  Global Instance ctx_persistent_nil : env_Persistent [].
  Proof. by constructor. Qed.
  Global Instance ctx_persistent_cons τi Δ :
    (∀ vv, Persistent (τi vv)) → env_Persistent Δ → env_Persistent (τi :: Δ).
  Proof. by constructor. Qed.
  Global Instance ctx_persistent_lookup Δ x vv :
    env_Persistent Δ → Persistent (ctx_lookup x Δ vv).
  Proof. intros HΔ; revert x; induction HΔ=>-[|?] /=; apply _. Qed.
  Global Instance interp_persistent τ Δ vv :
    env_Persistent Δ → Persistent (⟦ τ ⟧ Δ vv).
  Proof.
    revert vv Δ; induction τ=> vv Δ HΔ; simpl; try apply _.
    rewrite /Persistent fixpoint_interp_rec1_eq /interp_rec1 /= intuitionistically_into_persistently.
    by apply persistently_intro'.
  Qed.
  Global Instance interp_env_base_persistent Δ Γ vs :
  env_Persistent Δ → TCForall Persistent (zip_with (λ τ, ⟦ τ ⟧ Δ) Γ vs).
  Proof.
    intros HΔ. revert vs.
    induction Γ => vs; simpl; destruct vs; constructor; apply _.
  Qed.
  Global Instance interp_env_persistent Γ Δ vvs :
    env_Persistent Δ → Persistent (⟦ Γ ⟧* Δ vvs) := _.

  Lemma interp_weaken Δ1 Π Δ2 τ :
    ⟦ τ.[upn (length Δ1) (ren (+ length Π))] ⟧ (Δ1 ++ Π ++ Δ2)
    ≡ ⟦ τ ⟧ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Π Δ2. induction τ=> Δ1 Π Δ2; simpl; auto.
    - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - unfold interp_expr.
      intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - apply fixpoint_proper=> τi ww /=.
      properness; auto. apply (IHτ (_ :: _)).
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      (* FIXME: Ideally we wouldn't have to do this kinf of surgery. *)
      change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
      rewrite !lookup_app_r; [|lia ..]. do 2 f_equiv. lia.
    - unfold interp_expr.
      intros ww; simpl; properness; auto. by apply (IHτ (_ :: _)).
    - intros ww; simpl; properness; auto. by apply IHτ.
  Qed.

  Lemma interp_subst_up Δ1 Δ2 τ τ' :
    ⟦ τ ⟧ (Δ1 ++ interp τ' Δ2 :: Δ2)
    ≡ ⟦ τ.[upn (length Δ1) (τ' .: ids)] ⟧ (Δ1 ++ Δ2).
  Proof.
    revert Δ1 Δ2; induction τ=> Δ1 Δ2; simpl; auto.
    - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - unfold interp_expr.
      intros ww; simpl; properness; auto. by apply IHτ1. by apply IHτ2.
    - apply fixpoint_proper=> τi ww /=.
      properness; auto. apply (IHτ (_ :: _)).
    - rewrite iter_up; destruct lt_dec as [Hl | Hl]; simpl.
      { by rewrite !lookup_app_l. }
      (* FIXME: Ideally we wouldn't have to do this kinf of surgery. *)
      change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
      rewrite !lookup_app_r; [|lia ..].
      case EQ: (x - length Δ1) => [|n]; simpl.
      { symmetry. asimpl. apply (interp_weaken [] Δ1 Δ2 τ'). }
      change (bi_ofeO (uPredI (iResUR Σ))) with (uPredO (iResUR Σ)).
      rewrite !lookup_app_r; [|lia ..]. do 2 f_equiv. lia.
    - unfold interp_expr.
      intros ww; simpl; properness; auto. apply (IHτ (_ :: _)).
    - intros ww; simpl; properness; auto. by apply IHτ.
  Qed.

  Lemma interp_subst Δ2 τ τ' v : ⟦ τ ⟧ (⟦ τ' ⟧ Δ2 :: Δ2) v ≡ ⟦ τ.[τ'/] ⟧ Δ2 v.
  Proof. apply (interp_subst_up []). Qed.

  Lemma interp_env_length Δ Γ vvs : ⟦ Γ ⟧* Δ vvs ⊢ ⌜length Γ = length vvs⌝.
  Proof. by iIntros "[% ?]". Qed.

  Lemma interp_env_Some_l Δ Γ vvs x τ :
    Γ !! x = Some τ → ⟦ Γ ⟧* Δ vvs ⊢ ∃ vv, ⌜vvs !! x = Some vv⌝ ∧ ⟦ τ ⟧ Δ vv.
  Proof.
    iIntros (?) "[Hlen HΓ]"; iDestruct "Hlen" as %Hlen.
    destruct (lookup_lt_is_Some_2 vvs x) as [v Hv].
    { by rewrite -Hlen; apply lookup_lt_Some with τ. }
    iExists v; iSplit. done. iApply (big_sepL_elem_of with "HΓ").
    apply elem_of_list_lookup_2 with x.
    rewrite lookup_zip_with; by simplify_option_eq.
  Qed.

  Lemma interp_env_nil Δ : ⟦ [] ⟧* Δ [].
  Proof. iSplit; simpl; auto. Qed.
  Lemma interp_env_cons Δ Γ vvs τ vv :
    ⟦ τ :: Γ ⟧* Δ (vv :: vvs) ⊣⊢ ⟦ τ ⟧ Δ vv ∗ ⟦ Γ ⟧* Δ vvs.
  Proof.
    rewrite /interp_env /= (assoc _ (⟦ _ ⟧ _ _)) -(comm _ ⌜_ = _⌝%I) -assoc.
    by apply sep_proper; [apply pure_proper; lia|].
  Qed.

  Lemma interp_env_ren Δ (Γ : list type) vvs τi :
    ⟦ subst (ren (+1)) <$> Γ ⟧* (τi :: Δ) vvs ⊣⊢ ⟦ Γ ⟧* Δ vvs.
  Proof.
    apply sep_proper; [apply pure_proper; by rewrite fmap_length|].
    revert Δ vvs τi; induction Γ=> Δ [|v vs] τi; csimpl; auto.
    apply sep_proper; auto. apply (interp_weaken [] [τi] Δ).
  Qed.

End logrel.

Typeclasses Opaque interp_env.
Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧ₑ" := (interp_expr (interp τ)).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
