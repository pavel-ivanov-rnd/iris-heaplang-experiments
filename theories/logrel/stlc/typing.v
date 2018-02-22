From iris_examples.logrel.stlc Require Export lang.

Inductive type :=
  | TUnit : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type.

Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).

Inductive typed (Γ : list type) : expr → type → Prop :=
  | Var_typedx x τ : Γ !! x = Some τ → Γ ⊢ₜ Var x : τ
  | Unit_typed : Γ ⊢ₜ Unit : TUnit
  | Pair_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : τ1 → Γ ⊢ₜ e2 : τ2 → Γ ⊢ₜ Pair e1 e2 : TProd τ1 τ2
  | Fst_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Fst e : τ1
  | Snd_typed e τ1 τ2 : Γ ⊢ₜ e : TProd τ1 τ2 → Γ ⊢ₜ Snd e : τ2
  | InjL_typed e τ1 τ2 : Γ ⊢ₜ e : τ1 → Γ ⊢ₜ InjL e : TSum τ1 τ2
  | InjR_typed e τ1 τ2 : Γ ⊢ₜ e : τ2 → Γ ⊢ₜ InjR e : TSum τ1 τ2
  | Case_typed e0 e1 e2 τ1 τ2 ρ :
     Γ ⊢ₜ e0 : TSum τ1 τ2 → τ1 :: Γ ⊢ₜ e1 : ρ → τ2 :: Γ ⊢ₜ e2 : ρ →
     Γ ⊢ₜ Case e0 e1 e2 : ρ
  | Lam_typed e τ1 τ2 : τ1 :: Γ ⊢ₜ e : τ2 → Γ ⊢ₜ Lam e : TArrow τ1 τ2
  | App_typed e1 e2 τ1 τ2 :
     Γ ⊢ₜ e1 : TArrow τ1 τ2 → Γ ⊢ₜ e2 : τ1 → Γ ⊢ₜ App e1 e2 : τ2
where "Γ ⊢ₜ e : τ" := (typed Γ e τ).

Lemma typed_subst_invariant Γ e τ s1 s2 :
  Γ ⊢ₜ e : τ → (∀ x, x < length Γ → s1 x = s2 x) → e.[s1] = e.[s2].
Proof.
  intros Htyped; revert s1 s2.
  assert (∀ s1 s2 x, (x ≠ 0 → s1 (pred x) = s2 (pred x)) → up s1 x = up s2 x).
  { rewrite /up=> s1 s2 [|x] //=; auto with f_equal omega. }
  induction Htyped => s1 s2 Hs; f_equal/=; eauto using lookup_lt_Some with omega.
Qed.

Definition env_subst (vs : list val) (x : var) : expr :=
  from_option id (Var x) (of_val <$> vs !! x).

Lemma typed_subst_head_simpl Δ τ e w ws :
  Δ ⊢ₜ e : τ → length Δ = S (length ws) →
  e.[# w .: env_subst ws] = e.[env_subst (w :: ws)].
Proof.
  intros H1 H2.
  rewrite /env_subst. eapply typed_subst_invariant; eauto=> /= -[|x] ? //=.
  destruct (lookup_lt_is_Some_2 ws x) as [v' Hv]; first omega; simpl.
  by rewrite Hv.
Qed.

Lemma empty_env_subst e : e.[env_subst []] = e.
Proof. change (env_subst []) with ids. by asimpl. Qed.
