From iris.heap_lang Require Export lang notation tactics.
From iris.program_logic Require Export adequacy.

(** This file contains the proof that prophecies can be safely erased
from programs. We erase a program by replacing prophecy identifiers
with the unit values and respectively adapt the NewProph and Resolve
expressions. We prove that if a program e is safe then so is the
erasure of e. *)


Fixpoint erase_expr (e : expr) : expr :=
  match e with
  | Val v => Val (erase_val v)
  | Var x => Var x
  | Rec f x e => Rec f x (erase_expr e)
  | App e1 e2 => App (erase_expr e1) (erase_expr e2)
  | UnOp op e => UnOp op (erase_expr e)
  | BinOp op e1 e2 => BinOp op (erase_expr e1) (erase_expr e2)
  | If e0 e1 e2 => If (erase_expr e0) (erase_expr e1) (erase_expr e2)
  | Pair e1 e2 => Pair (erase_expr e1) (erase_expr e2)
  | Fst e => Fst (erase_expr e)
  | Snd e => Snd (erase_expr e)
  | InjL e => InjL (erase_expr e)
  | InjR e => InjR (erase_expr e)
  | Case e0 e1 e2 => Case (erase_expr e0) (erase_expr e1) (erase_expr e2)
  | Fork e => Fork (erase_expr e)
  | AllocN e1 e2 => AllocN (erase_expr e1) (erase_expr e2)
  | Load e => Load (erase_expr e)
  | Store e1 e2 => Store (erase_expr e1) (erase_expr e2)
  | CmpXchg e0 e1 e2 => CmpXchg (erase_expr e0) (erase_expr e1) (erase_expr e2)
  | FAA e1 e2 => FAA (erase_expr e1) (erase_expr e2)
  | NewProph => Skip
  | Resolve e0 e1 e2 => Fst (Fst (erase_expr e0, erase_expr e1, erase_expr e2))
  end
with
erase_val (v : val) : val :=
  match v with
  | LitV l =>
    LitV
      match l with
      | LitProphecy p => LitUnit
      | _ => l
      end
  | RecV f x e => RecV f x (erase_expr e)
  | PairV v1 v2 => PairV (erase_val v1) (erase_val v2)
  | InjLV v => InjLV (erase_val v)
  | InjRV v => InjRV (erase_val v)
  end.

Lemma erase_expr_subst x v e :
  erase_expr (subst x v e) = subst x (erase_val v) (erase_expr e)
with
erase_val_subst x v (w : val) :
  erase_expr (subst x v w) = subst x (erase_val v) (erase_val w).
Proof.
  - destruct e; simpl; try destruct decide;
      rewrite ?erase_expr_subst ?erase_val_subst; auto.
  - by destruct v; simpl.
Qed.

Lemma erase_expr_subst' x v e :
  erase_expr (subst' x v e) = subst' x (erase_val v) (erase_expr e).
Proof. destruct x; first done; apply erase_expr_subst. Qed.
Lemma erase_val_subst' x v (w : val) :
  erase_expr (subst x v w) = subst x (erase_val v) (erase_val w).
Proof. destruct x; first done; apply erase_val_subst. Qed.

Fixpoint erase_ectx_item (Ki : ectx_item) : list ectx_item :=
  match Ki with
  | AppLCtx v2 => [AppLCtx (erase_val v2)]
  | AppRCtx e1 => [AppRCtx (erase_expr e1)]
  | UnOpCtx op => [UnOpCtx op]
  | BinOpLCtx op v2 => [BinOpLCtx op (erase_val v2)]
  | BinOpRCtx op e1 => [BinOpRCtx op (erase_expr e1)]
  | IfCtx e1 e2 => [IfCtx (erase_expr e1) (erase_expr e2)]
  | PairLCtx v2 => [PairLCtx (erase_val v2)]
  | PairRCtx e1 => [PairRCtx (erase_expr e1)]
  | FstCtx => [FstCtx]
  | SndCtx => [SndCtx]
  | InjLCtx => [InjLCtx]
  | InjRCtx => [InjRCtx]
  | CaseCtx e1 e2 => [CaseCtx (erase_expr e1) (erase_expr e2)]
  | AllocNLCtx v2 => [AllocNLCtx (erase_val v2)]
  | AllocNRCtx e1 => [AllocNRCtx (erase_expr e1)]
  | LoadCtx => [LoadCtx]
  | StoreLCtx v2 => [StoreLCtx (erase_val v2)]
  | StoreRCtx e1 => [StoreRCtx (erase_expr e1)]
  | CmpXchgLCtx v1 v2 => [CmpXchgLCtx (erase_val v1) (erase_val v2)]
  | CmpXchgMCtx e0 v2 => [CmpXchgMCtx (erase_expr e0) (erase_val v2)]
  | CmpXchgRCtx e0 e1 => [CmpXchgRCtx (erase_expr e0) (erase_expr e1)]
  | FaaLCtx v2 => [FaaLCtx (erase_val v2)]
  | FaaRCtx e1 => [FaaRCtx (erase_expr e1)]
  | ResolveLCtx ctx v1 v2 =>
    erase_ectx_item ctx ++
    [PairLCtx (erase_val v1); PairLCtx (erase_val v2); FstCtx; FstCtx]
  | ResolveMCtx e0 v2 =>
    [PairRCtx (erase_expr e0); PairLCtx (erase_val v2); FstCtx; FstCtx]
  | ResolveRCtx e0 e1 =>
    [PairRCtx (erase_expr e0, erase_expr e1); FstCtx; FstCtx]
  end.

Definition erase_ectx (K : ectx heap_ectx_lang) : ectx heap_ectx_lang :=
  foldr (λ Ki K, erase_ectx_item Ki ++ K) [] K.

Definition erase_tp (tp : list expr) : list expr := erase_expr <$> tp.

Definition erase_heap (h : gmap loc val) : gmap loc val := erase_val <$> h.

Definition erase_state (σ : state) : state :=
  {| heap := erase_heap (heap σ); used_proph_id := ∅ |}.

Definition erase_cfg (ρ : cfg heap_lang) : cfg heap_lang :=
  (erase_tp ρ.1, erase_state ρ.2).

Lemma erase_to_val e v :
  to_val (erase_expr e) = Some v → ∃ v', to_val e = Some v' ∧ erase_val v' = v.
Proof. destruct e; intros ?; simplify_eq/=; eauto. Qed.

Lemma erase_not_val e : to_val e = None → to_val (erase_expr e) = None.
Proof. by destruct e. Qed.

Lemma erase_ectx_app K K' : erase_ectx (K ++ K') = erase_ectx K ++ erase_ectx K'.
Proof.
  revert K'; induction K as [|Ki K IHK]; intros K'; simpl in *; first done.
  by rewrite IHK assoc.
Qed.

Lemma erase_ectx_expr K e :
  erase_expr (fill K e) = fill (erase_ectx K) (erase_expr e).
Proof.
  revert e; induction K as [|Ki K IHK] using rev_ind; intros e;
    simpl in *; rewrite ?erase_ectx_app ?fill_app /=; first done.
  induction Ki;
    rewrite /= ?IHK ?IHKi ?fill_app //=.
Qed.

(* helper lemma consider moving? *)
Lemma ectx_prim_step (K : list ectx_item) e1 σ1 κ e2 σ2 ef :
  prim_step e1 σ1 κ e2 σ2 ef → prim_step (fill K e1) σ1 κ (fill K e2) σ2 ef.
Proof.
  inversion 1; simpl in *; simplify_eq.
  by rewrite -!fill_app; econstructor.
Qed.

(* helper lemma consider moving? *)
Lemma rtc_congruence {A B} (f : A → B) (R : A → A → Prop) (R' : B → B → Prop) x y :
  (∀ x y, R x y → R' (f x) (f y)) → rtc R x y → rtc R' (f x) (f y).
Proof.
  intros Hcng.
  induction 1 as [|e1 em e2 ?]; simpl in *; first done.
  etrans; last done.
  by apply rtc_once, Hcng.
Qed.

(* helper lemma consider moving? *)
Lemma rtc_Ectx_pure_step (K : list ectx_item) e1 e2 :
  rtc pure_step e1 e2 → rtc pure_step (fill K e1) (fill K e2).
Proof.
  apply rtc_congruence.
  by intros; eapply pure_step_ctx; first typeclasses eauto.
Qed.

(* helper lemma consider moving? *)
Definition is_safe e σ :=
  is_Some (to_val e) ∨ reducible e σ.

(* helper lemma consider moving? *)
Lemma is_safe_under_ectx K e σ : is_safe (fill K e) σ → is_safe e σ.
Proof.
  rewrite /is_safe /reducible /=.
  intros [?|(?&?&?&?&Hstp)]; simpl in *;
    first by left; eapply fill_val.
  destruct (to_val e) eqn:Hval; first by left; eauto.
  inversion Hstp as [K' e1' ? He]; simpl in *; simplify_eq.
  edestruct (step_by_val K K' e e1'); eauto; simplify_eq.
  rewrite -fill_comp in He; apply fill_inj in He; simplify_eq.
  right; eauto 10 using Ectx_step.
Qed.

(* helper lemma consider moving? *)
Lemma head_step_safe e σ κ e' σ' efs : head_step e σ κ e' σ' efs → is_safe e σ.
Proof. rewrite /is_safe /reducible /=. eauto 10 using head_prim_step. Qed.

(* helper lemma consider moving? *)
Lemma prim_step_safe e σ κ e' σ' efs : prim_step e σ κ e' σ' efs → is_safe e σ.
Proof. rewrite /is_safe /reducible /=. eauto 10. Qed.

Lemma val_for_compare_erase v1 v2 :
   val_for_compare v1 = val_for_compare v2 ↔
   val_for_compare (erase_val v1) = val_for_compare (erase_val v2).
Proof.
  revert v2; induction v1; induction v2; split; intros Ho; simpl in *;
    repeat case_match; simpl in *; simplify_eq; eauto; firstorder.
Qed.

Lemma val_for_compare_erase_bdec v1 v2 :
  bool_decide (val_for_compare v1 = val_for_compare v2) =
  bool_decide (val_for_compare (erase_val v1) = val_for_compare (erase_val v2)).
Proof. by apply bool_decide_iff; rewrite val_for_compare_erase. Qed.

Lemma vals_cmpxchg_compare_safe_erase v1 v2 :
  vals_cmpxchg_compare_safe (erase_val v1) (erase_val v2) ↔
  vals_cmpxchg_compare_safe v1 v2.
Proof.
  by destruct v1; destruct v2; repeat (done || simpl; case_match).
Qed.

(** if un_op_eval succeeds on erased value,
    the so should it on the original value. *)
Lemma un_op_eval_erase op v v' :
  un_op_eval op (erase_val v) = Some v' ↔
  ∃ w, un_op_eval op v = Some w ∧ erase_val w = v'.
Proof.
  destruct op; simpl; repeat case_match;
    (split; [intros ?|intros [? [? ?]]]);
    simplify_eq; simpl in *; simplify_eq; eauto.
Qed.

(** if unbin_op_eval succeeds on erased value,
    then so should it on the original value. *)
Lemma bin_op_eval_erase op v1 v2 v' :
  bin_op_eval op (erase_val v1) (erase_val v2) = Some v' ↔
  ∃ w, bin_op_eval op v1 v2 = Some w ∧ erase_val w = v'.
Proof.
  rewrite /bin_op_eval /bin_op_eval_int /bin_op_eval_bool;
  destruct decide; simpl; repeat case_match;
    (split; [intros ?|intros [? [? ?]]]);
    simplify_eq; simpl in *; simplify_eq; eauto.
  - eexists _; split; eauto; simpl.
    erewrite bool_decide_iff; first by eauto.
    by rewrite val_for_compare_erase.
  - repeat f_equal.
    erewrite bool_decide_iff; first by eauto.
    by rewrite -val_for_compare_erase.
Qed.

Lemma erase_heap_lookup h l : (erase_heap h) !! l = None ↔ h !! l = None.
Proof. rewrite lookup_fmap; by destruct (h !! l). Qed.

Lemma erase_heap_lookup' h l : (erase_heap h) !! l = erase_val <$> h !! l.
Proof. by rewrite lookup_fmap. Qed.

Lemma erase_heap_insert h l v :
  erase_heap (<[l := v]> h) = <[l := erase_val v]> (erase_heap h).
Proof.
  by rewrite /erase_heap fmap_insert.
Qed.

Lemma fmap_heap_array f l vs :
  f <$> heap_array l vs = heap_array l (f <$> vs).
Proof.
  revert l; induction vs as [|v vs IHvs]; intros l;
    first by rewrite /= fmap_empty.
  by rewrite /= -!insert_union_singleton_l !fmap_insert IHvs.
Qed.

Lemma erase_heap_array l n v σ :
  erase_heap (heap_array l (replicate (Z.to_nat n) v) ∪ heap σ) =
  heap_array l (replicate (Z.to_nat n) (erase_val v)) ∪ (erase_heap (heap σ)).
Proof.
  apply map_eq => i.
  rewrite /erase_heap lookup_fmap !lookup_union -fmap_replicate
  -fmap_heap_array !lookup_fmap.
  by destruct (heap_array l (replicate (Z.to_nat n) v) !! i);
    destruct (heap σ !! i).
Qed.

Lemma erase_state_init l n v σ:
  erase_state (state_init_heap l n v σ) =
  state_init_heap l n (erase_val v) (erase_state σ).
Proof. by rewrite /erase_state /state_init_heap /= erase_heap_array. Qed.

Ltac simplify_erasure :=
  let is_constructor A :=
      let HF := fresh in
      pose (match A with
            | _ => A
            end) as HF;
      (simpl in HF); unify HF A; clear HF
  in
  lazymatch goal with
  | H : erase_expr ?A = Val ?B |- _ => destruct A
  | H : Val ?B = erase_expr ?A |- _ => destruct A
  | H : _ = erase_val ?A |- _ => destruct A
  | H : erase_val ?A = _ |- _ => destruct A
  | H : erase_expr ?A = ?B |- _ =>
    lazymatch B with
    | fill _ _ => fail
    | context [fill _ _] => destruct A
    | _ => is_constructor B; destruct A
    end
  | H : ?B = erase_expr ?A |- _ =>
    lazymatch B with
    | fill _ _ => fail
    | context [fill _ _] => destruct A
    | _ => is_constructor B; destruct A
    end
  | H : Val _ = fill ?K ?e |- _ =>
      edestruct (to_val_fill_some K e);
        first (by rewrite -H; eauto)
  | H : head_step (Val _) _ _ _ _ _ |- _ => apply val_head_stuck in H
  | H : Rec _ _ _ = fill ?K _ |- _ =>
    destruct K as [|[] ? _] using rev_ind; simpl in *;
    rewrite ?fill_app in H
  | H : un_op_eval _ (erase_val _) = Some _ |- _ =>
    apply un_op_eval_erase in H as [? [? ?]]
  | H : bin_op_eval _ (erase_val _) (erase_val _) = Some _ |- _ =>
    apply bin_op_eval_erase in H as [? [? ?]]
  | H : context [erase_heap (heap _) !! _] |- _ =>
    rewrite /erase_heap lookup_fmap in H
  | H : _ <$> (?B !! ?C) = Some _ |- _ =>
    let Hf := fresh in destruct (B !! C) eqn:Hf; simpl in H; try done
  | H : is_Some (_ <$> (?B !! ?C)) |- _ => destruct H as [? ?]
  end; simplify_eq/=.

Definition head_steps_to_erasure_of (e1 : expr) (σ1 : state) (e2 : expr)
           (σ2 : state) (efs : list expr) :=
  ∃ κ' e2' σ2' efs',
    head_step e1 σ1 κ' e2' σ2' efs' ∧
    erase_expr e2' = e2 ∧ erase_state σ2' = σ2 ∧ erase_tp efs' = efs.

(** When the erased program makes a head step, so does the original program. *)
Lemma erased_head_step_head_step e1 σ1 κ e2 σ2 efs:
  head_step (erase_expr e1) (erase_state σ1) κ e2 σ2 efs
  → head_steps_to_erasure_of e1 σ1 e2 σ2 efs.
Proof.
  intros Hstp; rewrite /head_steps_to_erasure_of.
  inversion Hstp;
    (repeat ((repeat simplify_erasure); try case_match; simplify_eq));
    try
      (by (eexists _, _, _, _; simpl; split;
           first match goal with
                 | |- head_step NewProph _ _ _ _ _ => by apply new_proph_id_fresh
                 | _ => by econstructor;
                       eauto using erase_heap_lookup, val_for_compare_erase
                 end;
           try rewrite -val_for_compare_erase;
           rewrite ?erase_expr_subst' /erase_state ?erase_heap_insert /=;
                   eauto using erase_state_init)); [| |].
  - (* case of allocN *)
    eexists _, _, _, _; simpl; split;
      first econstructor; try rewrite -val_for_compare_erase;
        try setoid_rewrite <- erase_heap_lookup;
      rewrite ?erase_heap_insert /=; eauto using erase_state_init.
  - (* case of CmpXchg succeeding *)
    match goal with
    | H : bool_decide (val_for_compare (erase_val _)
                        = val_for_compare (erase_val _)) = _ |- _ =>
      rename H into Hvfc; rewrite -val_for_compare_erase_bdec in Hvfc
    end.
    eexists _, _, _, _; simpl; split.
    { econstructor; first rewrite -vals_cmpxchg_compare_safe_erase; eauto. }
    rewrite Hvfc /erase_state ?erase_heap_insert /=; eauto.
  - (* case of CmpXchg failing *)
    match goal with
    | H : bool_decide (val_for_compare (erase_val _)
                        = val_for_compare (erase_val _)) = _ |- _ =>
      rename H into Hvfc; rewrite -val_for_compare_erase_bdec in Hvfc
    end.
    eexists _, _, _, _; simpl; split.
    { econstructor; first rewrite -vals_cmpxchg_compare_safe_erase; eauto. }
    rewrite Hvfc; eauto.
Qed.

Lemma fill_to_resolve e0 (v1 v2 : val) K e' :
  to_val e' = None →
  Resolve e0 v1 v2 = fill K e' →
  K = [] ∨ ∃ K' Ki, K = K' ++ [ResolveLCtx Ki v1 v2].
Proof.
  intros Hnv Hrs; simpl in *.
  destruct K as [|Ki K _] using rev_ind; first by left.
  rewrite fill_app in Hrs.
  destruct Ki; simplify_eq/=; eauto; simplify_erasure.
Qed.

(* helper lemma, move? *)
Lemma head_step_to_val e σ κ (v : val) σ' efs :
  head_step e σ κ v σ' efs →
  ∀ σ' κ' e' σ'' efs', head_step e σ' κ' e' σ'' efs' → is_Some (to_val e').
Proof.
  inversion 1; simplify_eq/= => ?????; inversion 1; simplify_eq; eauto; [].
  match goal with | H : _ = ?A |- is_Some (to_val ?A) => rewrite -H end; eauto.
Qed.

Ltac solve_for_trivial_pure_head_step :=
  let helper :=
      apply rtc_once;
      apply pure_head_step_pure_step;
      split; rewrite /head_reducible_no_obs /=;
                     first (by eauto using head_step);
      intros ?????; inversion 1; simplify_eq; eauto
  in
  let go K e :=
      ((etrans;
        first (apply (rtc_Ectx_pure_step K); helper)); simpl)
  in
  repeat match goal with
  | |- rtc pure_step ?A _ => reshape_expr A go
  | |- rtc pure_step ?A ?A => done
  end.

Lemma projs_pure_steps (v0 v1 v2 : val) :
  rtc pure_step (Fst (Fst (v0, v1, v2))) v0.
Proof. solve_for_trivial_pure_head_step. Qed.

Lemma prim_step_strip_ctx K K' e1 σ1 κ e2 σ2 efs κ' e2' σ2' efs' :
  head_step e1 σ1 κ' e2' σ2' efs' →
  prim_step (fill K (fill K' e1)) σ1 κ e2 σ2 efs →
  ∃ e2'', e2 = fill K e2'' ∧ prim_step (fill K' e1) σ1 κ e2'' σ2 efs.
Proof.
  rewrite -fill_app => Hhstp Hpstp.
  inversion Hpstp as [K'' ?? HK'' ? hhstp']; simplify_eq/=.
  edestruct (step_by_val (K' ++ K)) as [K3 HK3];
    eauto using val_head_stuck; simplify_eq/=.
  rewrite !fill_app in HK''; repeat apply fill_inj in HK''; simplify_eq.
  rewrite !fill_app.
  eexists; split; first done.
  rewrite -!fill_app.
  by eapply Ectx_step'.
Qed.

Lemma Resolve_3_vals_unsafe (v0 v1 v2 : val) σ :
  is_safe (Resolve v0 v1 v2) σ → False.
Proof.
  intros [[? ?]|(?&?&?&?&Hstp)]; simpl in *; first done.
  inversion Hstp as [??? Hfill ? Hhstp']; simpl in *; simplify_eq.
  destruct K as [|Ki K _] using rev_ind; simpl in *; simplify_eq.
  - inversion Hhstp'; simplify_eq.
    match goal with
    | H : head_step (Val _) _ _ _ _ _ |- _ =>
        by apply val_head_stuck in H
    end.
  - clear Hstp; rewrite fill_app /= in Hfill.
    apply val_head_stuck in Hhstp'.
    destruct Ki; simpl in *; simplify_eq;
      match goal with
      | H : Val _ = fill_item ?Ki ?e |- _ =>
          by destruct (fill_item_val Ki e) as [? [-> ->]%to_val_fill_some];
            first by rewrite -H; eauto
      | H : Val _ = fill ?K ?e |- _ =>
        edestruct (to_val_fill_some K e);
          first (by rewrite -H; eauto); simplify_eq
      end.
Qed.

(** (e1, σ1) takes a [prim_step] to (e2', σ2') forking threads efs'
 such that σ2 is the erasure of σ2' and efs is the erasure of
 efs'. Furthermore, e2 takes [pure_steps] to match up with e2.  It is
 crucial for us that e2 takes [pure_step]s because we need to know
 that e2 does not get stuck and that the steps are deterministic.

 Essentially, the main part of the erasure proof's argument is that if
 the erased program takes steps, then the original program also takes
 matching steps. This however, does not entirely hold. In cases where
 the erasure of [Resovle] takes a step, the original program
 immediately produces the value while the erased program has to still
 perform projections [Fst] to get the result (see the [Resolve] case
 of [erase_expr]). For this purpose, we prove that in those cases (and
 also in general) the erased program also takes a number of (possibly
 zero) steps so that the original and the erased programs are matched
 up again. *)
Definition prim_step_matched_by_erased_steps e1 σ1 e2 σ2 efs :=
  ∃ e2' σ2' κ' efs' e2'',
    prim_step e1 σ1 κ' e2' σ2' efs' ∧ rtc pure_step e2 e2'' ∧
    erase_expr e2' = e2'' ∧ erase_state σ2' = σ2 ∧ erase_tp efs' = efs.

Lemma prim_step_matched_by_erased_steps_ectx K e1 σ1 e2 σ2 efs :
  prim_step_matched_by_erased_steps e1 σ1 e2 σ2 efs →
  prim_step_matched_by_erased_steps (fill K e1) σ1 (fill (erase_ectx K) e2) σ2 efs.
Proof.
  intros (?&?&?&?&?&?&?&?&?&?); simplify_eq/=.
  eexists _, _, _, _, _; repeat split.
  - by eapply ectx_prim_step.
  - by rewrite erase_ectx_expr; apply rtc_Ectx_pure_step.
Qed.

Definition is_Resolve (e : expr) :=
  match e with | Resolve _ _ _ => True | _ => False end.

Global Instance is_Resolve_dec e : Decision (is_Resolve e).
Proof. destruct e; solve_decision. Qed.

Ltac solve_is_safe :=
  match goal with
  | H : is_safe ?C ?B |- is_safe ?A ?B =>
    let tac K e := by (apply (is_safe_under_ectx K)) in
    reshape_expr C tac
  | H : head_step ?A ?B _ _ _ _ |- is_safe ?A ?B => by eapply head_step_safe
  | H : prim_step ?A ?B _ _ _ _ |- is_safe ?A ?B => by eapply prim_step_safe
  end.

Ltac solve_prim_step_ectx :=
  match goal with
  | |- prim_step ?A _ _ _ _ _ =>
    let tac K e :=
        lazymatch K with [] => fail | _ => (apply (ectx_prim_step K)) end
    in
    reshape_expr A tac; eauto
  end.

Ltac solve_rtc_pure_step_ectx :=
  match goal with
  | |- rtc pure_step ?A _ =>
    let tac K e :=
        lazymatch K with [] => fail | _ => (apply (rtc_Ectx_pure_step K)) end
    in
    reshape_expr A tac; eauto
  end.

Lemma non_resolve_prim_step_matched_by_erased_steps_ectx_item
      Ki e1 e1' σ1 e2 σ2 efs :
  to_val e1' = None →
  ¬ is_Resolve e1 →
  is_safe e1 σ1 →
  erase_expr e1 = fill_item Ki e1' →
  (∀ e1, erase_expr e1 = e1' → is_safe e1 σ1 →
         prim_step_matched_by_erased_steps e1 σ1 e2 σ2 efs) →
  prim_step_matched_by_erased_steps e1 σ1 (fill_item Ki e2) σ2 efs.
Proof.
  intros Hnv Hnr Hsf He1 IH.
  destruct Ki; repeat simplify_erasure; try done;
  match goal with
  | |- prim_step_matched_by_erased_steps ?A _ _ _ _ =>
    let tac K e :=
        lazymatch K with
        | [] => fail
        | _ => apply (prim_step_matched_by_erased_steps_ectx K)
        end
    in
    reshape_expr A tac; apply IH; [done|solve_is_safe]
  end.
Qed.

Lemma prim_step_matched_by_erased_steps_ectx_item Ki K e1 e1' σ1 e2 σ2 efs κ :
  head_step e1' (erase_state σ1) κ e2 σ2 efs →
  is_safe e1 σ1 →
  erase_expr e1 = fill_item Ki (fill K e1') →
  (∀ K' e1, length K' ≤ length K →
           erase_expr e1 = (fill K' e1') → is_safe e1 σ1 →
         prim_step_matched_by_erased_steps e1 σ1 (fill K' e2) σ2 efs) →
  prim_step_matched_by_erased_steps e1 σ1 (fill_item Ki (fill K e2)) σ2 efs.
Proof.
  intros Hhstp Hsf He1 IH; simpl in *.
  (** Case split on whether e1 is a [Resolve] expression. *)
  destruct (decide (is_Resolve e1)); last first.
  { (** e1 is not a [Resolve] expression. *)
    eapply non_resolve_prim_step_matched_by_erased_steps_ectx_item; eauto; [|].
    - by eapply fill_not_val, val_head_stuck.
    - intros; eapply (IH K); simpl; eauto with lia. }
  (** e1 is a [Resolve] expression. *)
  destruct Ki; repeat simplify_erasure; try done; [].
  destruct K as [|Ki K _] using rev_ind; simplify_eq/=; [|].
  { (* case where (Fst (erase_expr e1_1, erase_expr e1_2, erase_expr e1_3)) *)
  (*      takes a head_step; it is impossible! *)
    inversion Hhstp. }
  rewrite fill_app /= in He1.
  destruct Ki; simplify_eq/=; rewrite fill_app /=.
  destruct K as [|Ki K _] using rev_ind; simplify_eq/=; [|].
  { (* case where (erase_expr e1_1, erase_expr e1_2, erase_expr e1_3) *)
  (*      takes a head_step; it is impossible! *)
    inversion Hhstp. }
  rewrite fill_app /= in He1.
  destruct Ki; simplify_eq/=; rewrite fill_app /=.
  - destruct K as [|Ki K _] using rev_ind; simplify_eq/=; [|].
    { (** [Resolve v0 v1 v2] is not safe! *)
      inversion Hhstp; repeat simplify_erasure.
      exfalso; eauto using Resolve_3_vals_unsafe. }
    rewrite fill_app /= in He1.
    destruct Ki; simplify_eq/=; rewrite fill_app /=.
    + (** e1 is of the form ([Resolve] e10 e11 v0) and e11 takes a prim_step. *)
      destruct Hsf as [[? ?]| (?&?&?&?&Hrpstp)]; first done; simpl in *.
      inversion Hrpstp as [??? Hrs ? Hhstp']; simpl in *; simplify_eq.
      repeat simplify_erasure.
      edestruct fill_to_resolve as [?|[K' [Ki HK]]]; eauto;
        [by eapply val_head_stuck| |]; simplify_eq/=.
      * (** e1 is of the form ([Resolve] e10 e11 v0) and e11 takes a head_step. *)
        inversion Hhstp'; simplify_eq.
        edestruct (IH K) as (?&?&?&?&?&Hpstp&?&?&?&?);
          [rewrite !app_length /=; lia|done|by eapply head_step_safe|];
            simplify_eq/=.
        apply head_reducible_prim_step in Hpstp; simpl in *;
          last rewrite /head_reducible /=; eauto 10.
        edestruct head_step_to_val as [? ?%of_to_val]; eauto; simplify_eq.
        eexists _, _, _, _, _; repeat split;
          first (by apply head_prim_step; econstructor; eauto); auto.
        etrans.
        { by apply (rtc_Ectx_pure_step
                   [PairLCtx _; PairLCtx _; FstCtx; FstCtx]). }
        apply projs_pure_steps.
      * (** e1 is of the form ([Resolve] e10 v v0) and e10 takes a
           (non-head) prim_step. *)
        rewrite fill_app in Hrs; simplify_eq/=.
        edestruct (IH K) as (?&?&?&?&?&Hpstp&?&?&?&?);
          [rewrite !app_length; lia|done| |].
        { change (fill_item Ki) with (fill [Ki]).
          by rewrite -fill_app; eapply prim_step_safe, Ectx_step. }
          simplify_eq/=.
        eapply (prim_step_strip_ctx [_]) in Hpstp as [e2'' [He2'' Hpstp]];
          last done; simplify_eq/=.
        eexists _, _, _, _, _; repeat split; eauto;
          first by apply (ectx_prim_step [ResolveLCtx _ _ _]).
          by apply (rtc_Ectx_pure_step [PairLCtx _; PairLCtx _; FstCtx; FstCtx]).
    + (** e1 is of the form ([Resolve] e1_ e1_2 v) and e1_2 takes a prim_step. *)
      repeat simplify_erasure.
      apply (prim_step_matched_by_erased_steps_ectx [ResolveMCtx _ _]).
      apply IH; [rewrite !app_length /=; lia|done|solve_is_safe].
  - (** e1 is of the form ([Resolve] e1_ e1_2 e13) and e1_3 takes a prim_step. *)
      apply (prim_step_matched_by_erased_steps_ectx [ResolveRCtx _ _]).
      apply IH; [rewrite !app_length /=; lia|done|solve_is_safe].
Qed.

Lemma erased_prim_step_prim_step e1 σ1 κ e2 σ2 efs:
  prim_step (erase_expr e1) (erase_state σ1) κ e2 σ2 efs → is_safe e1 σ1 →
  prim_step_matched_by_erased_steps e1 σ1 e2 σ2 efs.
Proof.
  intros Hstp He1sf.
  inversion Hstp as [K e1' e2' He1 ? Hhstp]; clear Hstp;
    simpl in *; simplify_eq.
  set (len := length K); assert (length K = len) as Hlen by done; clearbody len.
  revert K Hlen e1 He1 He1sf.
  induction len as [m IHm]using lt_wf_ind; intros K Hlen e1 He1 He1sf;
    simplify_eq.
  destruct K as [|Ki K _] using rev_ind; simpl in *; simplify_eq.
  { apply erased_head_step_head_step in Hhstp as (?&?&?&?&?&<-&?&<-).
    eexists _, _, _, _, _; repeat split;
      first (by apply head_prim_step); auto using rtc_refl. }
  rewrite app_length in IHm; simpl in *.
  rewrite fill_app /=; rewrite fill_app /= in He1.
  eapply prim_step_matched_by_erased_steps_ectx_item; eauto; [].
  { intros; simpl in *; apply (IHm (length K')); auto with lia. }
Qed.

Lemma head_step_erased_head_step e1 σ1 κ e2 σ2 ef:
  head_step e1 σ1 κ e2 σ2 ef →
  ∃ e2' σ2' ef', prim_step (erase_expr e1) (erase_state σ1) [] e2' σ2' ef'.
Proof.
  induction 1 as [| | | | | | | | | | | | | | | | | | | |????????? IH];
    simpl in *; simplify_eq;
    try (by do 3 eexists; apply head_prim_step; econstructor);
    [| | | | | | |].
  - (* UnOp *)
    do 3 eexists; apply head_prim_step; econstructor.
    by apply un_op_eval_erase; eauto.
  - (* BinOp *)
    do 3 eexists; apply head_prim_step; econstructor.
    by apply bin_op_eval_erase; eauto.
  - (* AllocN *)
    do 3 eexists; apply head_prim_step; econstructor; eauto.
    intros; rewrite erase_heap_lookup; eauto.
  - (* Load *)
    do 3 eexists; apply head_prim_step; econstructor.
    rewrite /erase_state /state_upd_heap /= erase_heap_lookup'.
    by destruct lookup; simplify_eq.
  - (* Store *)
    match goal with | H : is_Some _ |- _ => inversion H end.
    do 3 eexists; apply head_prim_step; econstructor.
    by rewrite /erase_state /state_upd_heap /= erase_heap_lookup' H0; eauto.
  - (* CAS-fail *)
    match goal with
    | H : vals_cmpxchg_compare_safe ?A ?B |- _ =>
      destruct (bool_decide (val_for_compare A = val_for_compare B)) eqn:Heqvls
    end.
    + do 3 eexists; apply head_prim_step;
        econstructor; last (by eauto);
          first (by apply vals_cmpxchg_compare_safe_erase); [].
      match goal with
      | H : heap _ !! _ = _ |- _ =>
          by rewrite /erase_state /state_upd_heap /= erase_heap_lookup' H
      end.
    + do 3 eexists; apply head_prim_step;
        econstructor; last (by eauto);
          first (by apply vals_cmpxchg_compare_safe_erase); [].
      match goal with
      | H : heap _ !! _ = _ |- _ =>
          by rewrite /erase_state /state_upd_heap /= erase_heap_lookup' H
      end.
  - (* FAA *)
    do 3 eexists; apply head_prim_step; econstructor.
    by rewrite /erase_state /state_upd_heap /= erase_heap_lookup' H.
  - (* Resolve *)
    destruct IH as (?&?&?&?).
    eexists _, _, _;
      by apply (ectx_prim_step [PairLCtx _; PairLCtx _;FstCtx; FstCtx]).
Qed.

Lemma reducible_erased_reducible e σ :
  reducible e σ → reducible (erase_expr e) (erase_state σ).
Proof.
  intros (?&?&?&?&Hpstp); simpl in *.
  inversion Hpstp; simplify_eq/=.
  rewrite erase_ectx_expr.
  edestruct head_step_erased_head_step as (?&?&?&?); first done; simpl in *.
  eexists _, _, _, _; eapply ectx_prim_step; eauto.
Qed.

Definition erase_prop (φ : val → state → Prop) (v : val) (σ : state) : Prop :=
  ∃ v' σ', erase_val v' = v ∧ erase_state σ' = σ ∧ φ v' σ'.

(* move to std++ perhaps? *)
Lemma nsteps_inv_r {A} (R : A → A → Prop) n x z :
  nsteps R (S n) x z → ∃ y, nsteps R n x y ∧ R y z.
Proof.
  revert x z; induction n as [|n IHn]; intros x z.
  - inversion 1 as [|? ? ? ? ? Hstps]; inversion Hstps; simplify_eq.
    by eexists; split; first constructor.
  - inversion 1 as [|? ? ? ? ? Hstps]; simplify_eq.
    apply IHn in Hstps as [w [Hstps Hw]].
    eexists; split; last done.
    econstructor; eauto.
Qed.

Definition pure_step_tp (t1 t2 : list expr) := Forall2 (rtc pure_step )t1 t2.

Lemma rtc_pure_step_val v e : rtc pure_step (of_val v) e → to_val e = Some v.
Proof.
  intros ?; rewrite <- to_of_val.
  f_equal; symmetry; eapply rtc_nf; eauto.
  intros [? [Hstp _]].
  by destruct (Hstp inhabitant) as (?&?&?&?%val_stuck).
Qed.

Lemma pure_step_tp_safe t1 t2 e1 σ :
  (∀ e2, e2 ∈ t2 → is_safe e2 σ) → pure_step_tp t1 (erase_tp t2) →
  e1 ∈ t1 → is_safe e1 (erase_state σ).
Proof.
  intros Ht2 Hpr [i He1]%elem_of_list_lookup_1.
  eapply Forall2_lookup_l in Hpr as [e2' [He2' Hpr]]; simpl in *; eauto.
  rewrite /erase_tp list_lookup_fmap in He2'.
  destruct (t2 !! i) eqn:He2; simplify_eq/=.
  apply elem_of_list_lookup_2, Ht2 in He2.
  clear -Hpr He2.
  inversion Hpr as [|??? [? _]]; simplify_eq.
  - destruct He2 as [[? ?%of_to_val]|]; simplify_eq/=; first by left; eauto.
    by right; apply reducible_erased_reducible.
  - right; eauto using reducible_no_obs_reducible.
Qed.

Lemma erased_step_pure_step_tp t1 σ1 t2 σ2 t3 :
  erased_step (t1, σ1) (t2, σ2) →
  pure_step_tp t1 t3 →
  (σ1 = σ2 ∧ pure_step_tp t2 t3) ∨
  (∃ (i : nat) e t2' efs e' κ, t3 !! i = Some e ∧ t1 !! i = Some e ∧
              length t1 = length t2' ∧ t2 = t2' ++ efs ∧
              (∀ j, j ≠ i → t1 !! j = t2' !! j) ∧
              t2' !! i = Some e' ∧ prim_step e σ1 κ e' σ2 efs).
Proof.
  intros [κ Hes] Hps; simpl in *.
  inversion Hes as [e σ e' σ' ? t11 t12 ?? Hpstp]; simplify_eq/=.
  edestruct @Forall2_lookup_l as [e'' [Hlu He'']];
    first exact Hps; first apply list_lookup_middle; first done.
  inversion He'' as [|??? [_ Hprs]]; simplify_eq/=.
  - right; eexists (length t11), e'', (t11 ++ e' :: t12), _, _, _;
      repeat split; eauto; rewrite ?app_length -?app_assoc;
        eauto using list_lookup_middle.
    intros j Hneq.
    destruct (decide (j < length t11)%nat).
    + rewrite !lookup_app_l //.
    + rewrite !lookup_app_r; try lia.
      by destruct (j - length t11)%nat eqn:Heq; first lia.
  - edestruct Hprs as (?&?&?&?); eauto; simplify_eq.
    left; split; first done; rewrite app_nil_r.
    apply Forall2_app_inv_l in Hps as (t31&t32&Hps1&Hps2&->).
    apply Forall2_app; first done.
    apply Forall2_cons_inv_l in Hps2 as (e'&t32'&?&?&?); simplify_eq.
    apply Forall2_cons; last done.
    rewrite list_lookup_middle in Hlu; last by eapply Forall2_length.
    by simplify_eq.
Qed.

(* move to std++ or find an easy way to prove this! *)
Lemma elem_of_list_split_length {A : Type} (l : list A) i (x : A) :
  l !! i = Some x → ∃ l1 l2 : list A, l = l1 ++ x :: l2 ∧ i = length l1.
Proof.
  revert i; induction l as [|a l IHl]; intros i Hl; first done.
  destruct i; simplify_eq/=.
  - exists []; eauto.
  - destruct (IHl _ Hl) as (?&?&?&?); simplify_eq/=.
    eexists (a :: _); eauto.
Qed.

Lemma erased_steps_extend i t1 σ1 t2 σ2 (e : expr) κ e' σ3 efs :
  rtc erased_step (t1, σ1) (t2, σ2) →
  t2 !! i = Some e →
  prim_step e σ2 κ e' σ3 efs →
  rtc erased_step (t1, σ1) (<[i := e']>t2 ++ efs, σ3).
Proof.
  intros Hes Hlu Hpstp; simpl in *.
  etrans; first done.
  apply rtc_once.
  edestruct (elem_of_list_split_length t2) as (t21&t22&?&?);
    first (by eauto using elem_of_list_lookup_2); simplify_eq.
  do 2 econstructor; eauto.
  replace (length t21) with (length t21 + 0)%nat by lia.
  by rewrite insert_app_r /= -app_assoc /=.
Qed.

Lemma erasure e σ φ :
  adequate NotStuck e σ φ →
  adequate NotStuck (erase_expr e) (erase_state σ) (erase_prop φ).
Proof.
  intros Hade; simpl in *.
  cut (∀ t2 σ2,
          rtc erased_step ([erase_expr e], erase_state σ) (t2, σ2) →
          (∃ t2' t2'' σ2',
              rtc erased_step ([e], σ) (t2'', σ2') ∧
              t2' = erase_tp t2'' ∧ σ2 = erase_state σ2' ∧
              pure_step_tp t2 t2')).
  { intros Hreach; split; simpl in *.
    - intros ? ? ? Hrtc; edestruct (Hreach _ _ Hrtc) as
          (t2'&t2''&σ2'&Hos&Ht2'&Hσ2&Hptp); simplify_eq/=.
      apply Forall2_cons_inv_l in Hptp as (oe&t3&Hoe%rtc_pure_step_val&_&?);
        destruct t2''; simplify_eq/=.
      apply erase_to_val in Hoe as (?&?%of_to_val&?); simplify_eq.
      pose proof (adequate_result _ _ _ _ Hade _ _ _ Hos);
        rewrite /erase_prop; eauto.
    - intros ? ? ? Hs Hrtc He2; edestruct (Hreach _ _ Hrtc) as
          (t2'&t2''&σ2'&Hos&Ht2'&Hσ2&Hptp); simplify_eq/=.
      eapply pure_step_tp_safe; [|done..].
      intros e2' He2'.
      apply (adequate_not_stuck _ _ _ _ Hade _ _ _ eq_refl Hos He2'). }
  intros t2 σ2 [n Hstps]%rtc_nsteps; simpl in *; revert t2 σ2 Hstps.
  induction n.
  { intros t2 σ2 Hstps; inversion Hstps; simplify_eq /=.
    repeat econstructor. }
  intros t2 σ2 Hstps.
  apply nsteps_inv_r in Hstps as [[t3 σ3] [Hstps Hρ]]; simpl in *.
  destruct (IHn _ _ Hstps) as (t2'&t2''&σ2'&Hostps&?&?&Hprstps); simplify_eq.
  edestruct erased_step_pure_step_tp as [[? Hint]|Hext]; simplify_eq/=;
    eauto 10; [|done..].
  destruct Hext as (i&ei&t2'&efs&e'&κ&Hi1&Hi2&Hlen&?&Hlu&Hi3&Hpstp);
    simplify_eq.
  rewrite /erase_tp list_lookup_fmap in Hi1.
  destruct (t2'' !! i) as [eio|] eqn:Heq; simplify_eq/=.
  edestruct erased_prim_step_prim_step as
      (eio' & σ3 & κ' & efs' & ee & Heiopstp & Hprstps' & ?&?&?); first done;
  last simplify_eq/=.
  { eapply adequate_not_stuck; eauto using elem_of_list_lookup_2. }
  eexists _, _, _; repeat split; first eapply erased_steps_extend; eauto.
  rewrite /pure_step_tp /erase_tp fmap_app.
  apply Forall2_app; last done.
  apply Forall2_same_length_lookup; split.
  { apply Forall2_length in Hprstps; rewrite fmap_length in Hprstps.
    by rewrite fmap_length insert_length -Hlen. }
  intros j x y.
  destruct (decide (i = j)); simplify_eq.
  { rewrite Hi3 list_lookup_fmap list_lookup_insert /=;
      last by eapply lookup_lt_Some.
    by intros ? ?; simplify_eq. }
  rewrite list_lookup_fmap list_lookup_insert_ne // -list_lookup_fmap.
  intros ? ?.
  eapply Forall2_lookup_lr; eauto.
  by rewrite Hlu.
Qed.
