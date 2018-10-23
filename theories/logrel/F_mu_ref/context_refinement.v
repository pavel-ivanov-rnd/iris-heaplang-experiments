From iris_examples.logrel.F_mu_ref Require Export fundamental_binary.

Inductive ctx_item :=
  | CTX_Lam
  | CTX_AppL (e2 : expr)
  | CTX_AppR (e1 : expr)
  (* Products *)
  | CTX_PairL (e2 : expr)
  | CTX_PairR (e1 : expr)
  | CTX_Fst
  | CTX_Snd
  (* Sums *)
  | CTX_InjL
  | CTX_InjR
  | CTX_CaseL (e1 : expr) (e2 : expr)
  | CTX_CaseM (e0 : expr) (e2 : expr)
  | CTX_CaseR (e0 : expr) (e1 : expr)
  (* Recursive Types *)
  | CTX_Fold
  | CTX_Unfold
  (* Polymorphic Types *)
  | CTX_TLam
  | CTX_TApp
  (* Reference Types *)
  | CTX_Alloc
  | CTX_Load
  | CTX_StoreL (e2 : expr)
  | CTX_StoreR (e1 : expr).

Fixpoint fill_ctx_item (ctx : ctx_item) (e : expr) : expr :=
  match ctx with
  | CTX_Lam => Lam e
  | CTX_AppL e2 => App e e2
  | CTX_AppR e1 => App e1 e
  | CTX_PairL e2 => Pair e e2
  | CTX_PairR e1 => Pair e1 e
  | CTX_Fst => Fst e
  | CTX_Snd => Snd e
  | CTX_InjL => InjL e
  | CTX_InjR => InjR e
  | CTX_CaseL e1 e2 => Case e e1 e2
  | CTX_CaseM e0 e2 => Case e0 e e2
  | CTX_CaseR e0 e1 => Case e0 e1 e
  | CTX_Fold => Fold e
  | CTX_Unfold => Unfold e
  | CTX_TLam => TLam e
  | CTX_TApp => TApp e
  | CTX_Alloc => Alloc e
  | CTX_Load => Load e
  | CTX_StoreL e2 => Store e e2
  | CTX_StoreR e1 => Store e1 e
  end.

Definition ctx := list ctx_item.

Definition fill_ctx (K : ctx) (e : expr) : expr := foldr fill_ctx_item e K.

(** typed ctx *)
Inductive typed_ctx_item :
    ctx_item → list type → type → list type → type → Prop :=
  | TP_CTX_Lam Γ τ τ' :
     typed_ctx_item CTX_Lam (τ :: Γ) τ' Γ (TArrow τ τ')
  | TP_CTX_AppL Γ e2 τ τ' :
     typed Γ e2 τ →
     typed_ctx_item (CTX_AppL e2) Γ (TArrow τ τ') Γ τ'
  | TP_CTX_AppR Γ e1 τ τ' :
     typed Γ e1 (TArrow τ τ') →
     typed_ctx_item (CTX_AppR e1) Γ τ Γ τ'
  | TP_CTX_PairL Γ e2 τ τ' :
     typed Γ e2 τ' →
     typed_ctx_item (CTX_PairL e2) Γ τ Γ (TProd τ τ')
  | TP_CTX_PairR Γ e1 τ τ' :
     typed Γ e1 τ →
     typed_ctx_item (CTX_PairR e1) Γ τ' Γ (TProd τ τ')
  | TP_CTX_Fst Γ τ τ' :
     typed_ctx_item CTX_Fst Γ (TProd τ τ') Γ τ
  | TP_CTX_Snd Γ τ τ' :
     typed_ctx_item CTX_Snd Γ (TProd τ τ') Γ τ'
  | TP_CTX_InjL Γ τ τ' :
     typed_ctx_item CTX_InjL Γ τ Γ (TSum τ τ')
  | TP_CTX_InjR Γ τ τ' :
     typed_ctx_item CTX_InjR Γ τ' Γ (TSum τ τ')
  | TP_CTX_CaseL Γ e1 e2 τ1 τ2 τ' :
     typed (τ1 :: Γ) e1 τ' → typed (τ2 :: Γ) e2 τ' →
     typed_ctx_item (CTX_CaseL e1 e2) Γ (TSum τ1 τ2) Γ τ'
  | TP_CTX_CaseM Γ e0 e2 τ1 τ2 τ' :
     typed Γ e0 (TSum τ1 τ2) → typed (τ2 :: Γ) e2 τ' →
     typed_ctx_item (CTX_CaseM e0 e2) (τ1 :: Γ) τ' Γ τ'
  | TP_CTX_CaseR Γ e0 e1 τ1 τ2 τ' :
     typed Γ e0 (TSum τ1 τ2) → typed (τ1 :: Γ) e1 τ' →
     typed_ctx_item (CTX_CaseR e0 e1) (τ2 :: Γ) τ' Γ τ'
  | TP_CTX_Fold Γ τ :
     typed_ctx_item CTX_Fold Γ τ.[(TRec τ)/] Γ (TRec τ)
  | TP_CTX_Unfold Γ τ :
     typed_ctx_item CTX_Unfold Γ (TRec τ) Γ τ.[(TRec τ)/]
  | TP_CTX_TLam Γ τ :
     typed_ctx_item CTX_TLam (subst (ren (+1)) <$> Γ) τ Γ (TForall τ)
  | TP_CTX_TApp Γ τ τ' :
     typed_ctx_item CTX_TApp Γ (TForall τ) Γ τ.[τ'/]
  | TPCTX_Alloc Γ τ :
     typed_ctx_item CTX_Alloc Γ τ Γ (Tref τ)
  | TP_CTX_Load Γ τ :
     typed_ctx_item CTX_Load Γ (Tref τ) Γ τ
  | TP_CTX_StoreL Γ e2 τ :
     typed Γ e2 τ → typed_ctx_item (CTX_StoreL e2) Γ (Tref τ) Γ TUnit
  | TP_CTX_StoreR Γ e1 τ :
     typed Γ e1 (Tref τ) →
     typed_ctx_item (CTX_StoreR e1) Γ τ Γ TUnit.

Lemma typed_ctx_item_typed k Γ τ Γ' τ' e :
  typed Γ e τ → typed_ctx_item k Γ τ Γ' τ' →
  typed Γ' (fill_ctx_item k e) τ'.
Proof. induction 2; simpl; eauto using typed. Qed.

Inductive typed_ctx: ctx → list type → type → list type → type → Prop :=
  | TPCTX_nil Γ τ :
     typed_ctx nil Γ τ Γ τ
  | TPCTX_cons Γ1 τ1 Γ2 τ2 Γ3 τ3 k K :
     typed_ctx_item k Γ2 τ2 Γ3 τ3 →
     typed_ctx K Γ1 τ1 Γ2 τ2 →
     typed_ctx (k :: K) Γ1 τ1 Γ3 τ3.

Lemma typed_ctx_typed K Γ τ Γ' τ' e :
  typed Γ e τ → typed_ctx K Γ τ Γ' τ' → typed Γ' (fill_ctx K e) τ'.
Proof. induction 2; simpl; eauto using typed_ctx_item_typed. Qed.

Lemma typed_ctx_n_closed K Γ τ Γ' τ' e :
  (∀ f, e.[upn (length Γ) f] = e) → typed_ctx K Γ τ Γ' τ' →
  ∀ f, (fill_ctx K e).[upn (length Γ') f] = (fill_ctx K e).
Proof.
  intros H1 H2; induction H2; simpl; auto.
  induction H => f; asimpl; simpl in *;
    repeat match goal with H : _ |- _ => rewrite fmap_length in H end;
    try f_equal;
    eauto using typed_n_closed;
    try match goal with H : _ |- _ => eapply (typed_n_closed _ _ _ H) end.
Qed.

Definition ctx_refines (Γ : list type)
    (e e' : expr) (τ : type) := ∀ K thp σ v,
  typed_ctx K Γ τ [] TUnit →
  rtc erased_step ([fill_ctx K e], ∅) (of_val v :: thp, σ) →
  ∃ thp' σ' v', rtc erased_step ([fill_ctx K e'], ∅) (of_val v' :: thp', σ').
Notation "Γ ⊨ e '≤ctx≤' e' : τ" :=
  (ctx_refines Γ e e' τ) (at level 74, e, e', τ at next level).

Ltac fold_interp :=
  match goal with
  | |- context [ interp_expr (interp_arrow (interp ?A) (interp ?A'))
                            ?B (?C, ?D) ] =>
    change (interp_expr (interp_arrow (interp A) (interp A')) B (C, D)) with
    (interp_expr (interp (TArrow A A')) B (C, D))
  | |- context [ interp_expr (interp_prod (interp ?A) (interp ?A'))
                            ?B (?C, ?D) ] =>
    change (interp_expr (interp_prod (interp A) (interp A')) B (C, D)) with
    (interp_expr (interp (TProd A A')) B (C, D))
  | |- context [ interp_expr (interp_prod (interp ?A) (interp ?A'))
                            ?B (?C, ?D) ] =>
    change (interp_expr (interp_prod (interp A) (interp A')) B (C, D)) with
    (interp_expr (interp (TProd A A')) B (C, D))
  | |- context [ interp_expr (interp_sum (interp ?A) (interp ?A'))
                            ?B (?C, ?D) ] =>
    change (interp_expr (interp_sum (interp A) (interp A')) B (C, D)) with
    (interp_expr (interp (TSum A A')) B (C, D))
  | |- context [ interp_expr (interp_rec (interp ?A)) ?B (?C, ?D) ] =>
    change (interp_expr (interp_rec (interp A)) B (C, D)) with
    (interp_expr (interp (TRec A)) B (C, D))
  | |- context [ interp_expr (interp_forall (interp ?A))
                            ?B (?C, ?D) ] =>
    change (interp_expr (interp_forall (interp A)) B (C, D)) with
    (interp_expr (interp (TForall A)) B (C, D))
  | |- context [ interp_expr (interp_ref (interp ?A))
                            ?B (?C, ?D) ] =>
    change (interp_expr (interp_ref (interp A)) B (C, D)) with
    (interp_expr (interp (Tref A)) B (C, D))
  end.

Section bin_log_related_under_typed_ctx.
  Context `{heapG Σ, cfgSG Σ}.

  Lemma bin_log_related_under_typed_ctx Γ e e' τ Γ' τ' K :
    (∀ f, e.[upn (length Γ) f] = e) →
    (∀ f, e'.[upn (length Γ) f] = e') →
    typed_ctx K Γ τ Γ' τ' →
    Γ ⊨ e ≤log≤ e' : τ → Γ' ⊨ fill_ctx K e ≤log≤ fill_ctx K e' : τ'.
  Proof.
    revert Γ τ Γ' τ' e e'.
    induction K as [|k K]=> Γ τ Γ' τ' e e' H1 H2; simpl.
    - inversion_clear 1; trivial.
    - inversion_clear 1 as [|? ? ? ? ? ? ? ? Hx1 Hx2]. intros H3.
      specialize (IHK _ _ _ _ e e' H1 H2 Hx2 H3).
      inversion Hx1; subst; simpl; try fold_interp.
      + eapply bin_log_related_lam; eauto;
          match goal with
            H : _ |- _ => eapply (typed_ctx_n_closed _ _ _ _ _ _ _ H)
          end.
      + eapply bin_log_related_app; eauto using binary_fundamental.
      + eapply bin_log_related_app; eauto using binary_fundamental.
      + eapply bin_log_related_pair; eauto using binary_fundamental.
      + eapply bin_log_related_pair; eauto using binary_fundamental.
      + eapply bin_log_related_fst; eauto.
      + eapply bin_log_related_snd; eauto.
      + eapply bin_log_related_injl; eauto.
      + eapply bin_log_related_injr; eauto.
      + match goal with
          H : typed_ctx_item _ _ _ _ _ |- _ => inversion H; subst
        end.
        eapply bin_log_related_case;
          eauto using binary_fundamental;
          match goal with
            H : _ |- _ => eapply (typed_n_closed _ _ _ H)
          end.
      + match goal with
          H : typed_ctx_item _ _ _ _ _ |- _ => inversion H; subst
        end.
        eapply bin_log_related_case;
          eauto using binary_fundamental;
          try match goal with
                H : _ |- _ => eapply (typed_n_closed _ _ _ H)
              end;
          match goal with
            H : _ |- _ => eapply (typed_ctx_n_closed _ _ _ _ _ _ _ H)
          end.
      + match goal with
          H : typed_ctx_item _ _ _ _ _ |- _ => inversion H; subst
        end.
        eapply bin_log_related_case;
          eauto using binary_fundamental;
          try match goal with
                H : _ |- _ => eapply (typed_n_closed _ _ _ H)
              end;
          match goal with
            H : _ |- _ => eapply (typed_ctx_n_closed _ _ _ _ _ _ _ H)
          end.
      + eapply bin_log_related_fold; eauto.
      + eapply bin_log_related_unfold; eauto.
      + eapply bin_log_related_tlam; eauto with typeclass_instances.
      + eapply bin_log_related_tapp; eauto.
      + eapply bin_log_related_alloc; eauto.
      + eapply bin_log_related_load; eauto.
      + eapply bin_log_related_store; eauto using binary_fundamental.
      + eapply bin_log_related_store; eauto using binary_fundamental.
        Unshelve. all: trivial.
  Qed.
End bin_log_related_under_typed_ctx.
