From iris.program_logic Require Export language ectx_language ectxi_language.
From iris_examples.logrel.prelude Require Export base.
From iris.algebra Require Export ofe.
From stdpp Require Import gmap.

Module F_mu_ref.
  Definition loc := positive.

  Instance loc_dec_eq (l l' : loc) : Decision (l = l') := _.

  Inductive expr :=
  | Var (x : var)
  | Lam (e : {bind 1 of expr})
  | App (e1 e2 : expr)
  (* Unit *)
  | Unit
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr})
  (* Recursive Types *)
  | Fold (e : expr)
  | Unfold (e : expr)
  (* Polymorphic Types *)
  | TLam (e : expr)
  | TApp (e : expr)
  (* Reference Types *)
  | Loc (l : loc)
  | Alloc (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr).

  Instance Ids_expr : Ids expr. derive. Defined.
  Instance Rename_expr : Rename expr. derive. Defined.
  Instance Subst_expr : Subst expr. derive. Defined.
  Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

  Instance expr_dec_eq (e e' : expr) : Decision (e = e').
  Proof. solve_decision. Defined.

  Inductive val :=
  | LamV (e : {bind 1 of expr})
  | TLamV (e : {bind 1 of expr})
  | UnitV
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | FoldV (v : val)
  | LocV (l : loc).

  Instance val_dec_eq (v v' : val) : Decision (v = v').
  Proof. solve_decision. Defined.

  Instance val_inh : Inhabited val := populate UnitV.

  Fixpoint of_val (v : val) : expr :=
    match v with
    | LamV e => Lam e
    | TLamV e => TLam e
    | UnitV => Unit
    | PairV v1 v2 => Pair (of_val v1) (of_val v2)
    | InjLV v => InjL (of_val v)
    | InjRV v => InjR (of_val v)
    | FoldV v => Fold (of_val v)
    | LocV l => Loc l
    end.
  Notation "# v" := (of_val v) (at level 20).

  Fixpoint to_val (e : expr) : option val :=
    match e with
    | Lam e => Some (LamV e)
    | TLam e => Some (TLamV e)
    | Unit => Some UnitV
    | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
    | InjL e => InjLV <$> to_val e
    | InjR e => InjRV <$> to_val e
    | Fold e => v ← to_val e; Some (FoldV v)
    | Loc l => Some (LocV l)
    | _ => None
    end.

  (** Evaluation contexts *)
  Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | TAppCtx
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : {bind expr}) (e2 : {bind expr})
  | FoldCtx
  | UnfoldCtx
  | AllocCtx
  | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val).

  Notation ectx := (list ectx_item).

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | AppLCtx e2 => App e e2
    | AppRCtx v1 => App (of_val v1) e
    | TAppCtx => TApp e
    | PairLCtx e2 => Pair e e2
    | PairRCtx v1 => Pair (of_val v1) e
    | FstCtx => Fst e
    | SndCtx => Snd e
    | InjLCtx => InjL e
    | InjRCtx => InjR e
    | CaseCtx e1 e2 => Case e e1 e2
    | FoldCtx => Fold e
    | UnfoldCtx => Unfold e
    | AllocCtx => Alloc e
    | LoadCtx => Load e
    | StoreLCtx e2 => Store e e2
    | StoreRCtx v1 => Store (of_val v1) e
    end.

  Definition state : Type := gmap loc val.

  Inductive head_step : expr → state → list Empty_set → expr → state → list expr → Prop :=
  (* β *)
  | BetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      head_step (App (Lam e1) e2) σ [] e1.[e2/] σ []
  (* Products *)
  | FstS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      head_step (Fst (Pair e1 e2)) σ [] e1 σ []
  | SndS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      head_step (Snd (Pair e1 e2)) σ [] e2 σ []
  (* Sums *)
  | CaseLS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjL e0) e1 e2) σ [] e1.[e0/] σ []
  | CaseRS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjR e0) e1 e2) σ [] e2.[e0/] σ []
  (* Recursive Types *)
  | Unfold_Fold e v σ :
      to_val e = Some v →
      head_step (Unfold (Fold e)) σ [] e σ []
  (* Polymorphic Types *)
  | TBeta e σ :
      head_step (TApp (TLam e)) σ [] e σ []
  (* Reference Types *)
  | AllocS e v σ l :
     to_val e = Some v → σ !! l = None →
     head_step (Alloc e) σ [] (Loc l) (<[l:=v]>σ) []
  | LoadS l v σ :
     σ !! l = Some v →
     head_step (Load (Loc l)) σ [] (of_val v) σ []
  | StoreS l e v σ :
     to_val e = Some v → is_Some (σ !! l) →
     head_step (Store (Loc l) e) σ [] (Unit) (<[l:=v]>σ) [].

  (** Basic properties about the language *)
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. by induction v; simplify_option_eq. Qed.

  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof.
    revert v; induction e; intros; simplify_option_eq; auto with f_equal.
  Qed.

  Instance of_val_inj : Inj (=) (=) of_val.
  Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

  Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

  Lemma val_stuck e1 σ1 κ e2 σ2 ef :
    head_step e1 σ1 κ e2 σ2 ef → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 ef :
    head_step (fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
           end; auto.
  Qed.

  Lemma alloc_fresh e v σ :
    let l := fresh (dom (gset loc) σ) in
    to_val e = Some v → head_step (Alloc e) σ [] (Loc l) (<[l:=v]>σ) [].
  Proof. by intros; apply AllocS, (not_elem_of_dom (D:=gset loc)), is_fresh. Qed.

  Lemma val_head_stuck e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
  Proof.
    split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
           fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
  Qed.

  Canonical Structure stateO := leibnizO state.
  Canonical Structure valO := leibnizO val.
  Canonical Structure exprO := leibnizO expr.
End F_mu_ref.

Canonical Structure F_mu_ref_ectxi_lang := EctxiLanguage F_mu_ref.lang_mixin.
Canonical Structure F_mu_ref_ectx_lang := EctxLanguageOfEctxi F_mu_ref_ectxi_lang.
Canonical Structure F_mu_ref_lang := LanguageOfEctx F_mu_ref_ectx_lang.

Export F_mu_ref.

Hint Extern 20 (PureExec _ _ _) => progress simpl : typeclass_instances.

Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Hint Extern 5 (AsVal _) => eexists; eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (AsVal _) =>
  eexists; rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Definition is_atomic (e : expr) : Prop :=
  match e with
  | Alloc e => is_Some (to_val e)
  | Load e =>  is_Some (to_val e)
  | Store e1 e2 => is_Some (to_val e1) ∧ is_Some (to_val e2)
  | _ => False
  end.
Local Hint Resolve language.val_irreducible.
Local Hint Resolve to_of_val.
Local Hint Unfold language.irreducible.
Global Instance is_atomic_correct s e : is_atomic e → Atomic s e.
Proof.
  intros Ha; apply strongly_atomic_atomic,  ectx_language_atomic.
  - destruct 1; simpl in *; try tauto; eauto.
  - intros K e' -> Hval%eq_None_not_Some.
    induction K using rev_ind; first done.
    simpl in Ha; rewrite fill_app in Ha; simpl in Ha.
    destruct Hval. apply (fill_val K e'); simpl in *.
    destruct x; naive_solver.
Qed.

Ltac solve_atomic :=
  apply is_atomic_correct; simpl; repeat split;
    rewrite ?to_of_val; eapply mk_is_Some; fast_done.

Hint Extern 0 (Atomic _ _) => solve_atomic.
Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.
