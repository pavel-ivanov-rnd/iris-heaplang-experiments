From iris_examples.iris_logrel.F_mu_ref_conc Require Import  typing.

Definition FG_StackType τ :=
  TRec (Tref (TSum TUnit (TProd τ.[ren (+1)] (TVar 0)))).

Definition FG_push (st : expr) : expr :=
  Rec (App (Rec
              (* try push *)
              (If (CAS (st.[ren (+4)]) (Var 1)
                       (Fold (Alloc (InjR (Pair (Var 3) (Var 1)))))
                  )
                  Unit (* push succeeds we return unit *)
                  (App (Var 2) (Var 3)) (* push fails, we try again *)
              )
           )
           (Load st.[ren (+2)]) (* read the stack pointer *)
      ).
Definition FG_pushV (st : expr) : val :=
  RecV (App (Rec
              (* try push *)
              (If (CAS (st.[ren (+4)]) (Var 1)
                       (Fold (Alloc (InjR (Pair (Var 3) (Var 1)))))
                  )
                  Unit (* push succeeds we return unit *)
                  (App (Var 2) (Var 3)) (* push fails, we try again *)
              )
           )
           (Load st.[ren (+2)]) (* read the stack pointer *)
       ).

Definition FG_pop (st : expr) : expr :=
  Rec (App (Rec
              (App
                 (Rec
                    (
                      Case (Var 1)
                           (InjL Unit)
                           ( (* try popping *)
                             If
                               (CAS
                                  (st.[ren (+7)])
                                  (Fold (Var 4))
                                  (Snd (Var 0))
                               )
                               (InjR (Fst (Var 0))) (* pop succeeds *)
                               (App (Var 5) (Var 6)) (* pop fails, we retry*)
                           )
                     )
                 )
                 (
                   (Load (Var 1))
                 )
              )
           )
           (Unfold (Load st.[ren (+ 2)]))
      ).
Definition FG_popV (st : expr) : val :=
  RecV
    (App
       (Rec
          ( App
              (Rec
                 (
                   Case (Var 1)
                        (InjL Unit)
                        ( (* try popping *)
                          If
                            (CAS
                               (st.[ren (+7)])
                               (Fold (Var 4))
                               (Snd (Var 0))
                            )
                            (InjR (Fst (Var 0))) (* pop succeeds *)
                            (App (Var 5) (Var 6)) (* pop fails, we retry*)
                        )
                 )
              )
              (
                (Load (Var 1))
              )
          )
       )
       (Unfold (Load st.[ren (+ 2)]))
    ).

Definition FG_iter (f : expr) : expr :=
  Rec
    (Case (Load (Unfold (Var 1)))
          Unit
          (App (Rec (App (Var 3) (Snd (Var 2)))) (* recursive_call *)
               (App f.[ren (+3)] (Fst (Var 0)))
          )
    ).
Definition FG_iterV (f : expr) : val :=
  RecV
    (Case (Load (Unfold (Var 1)))
          Unit
          (App (Rec (App (Var 3) (Snd (Var 2)))) (* recursive_call *)
               (App f.[ren (+3)] (Fst (Var 0)))
          )
    ).
Definition FG_read_iter (st : expr) : expr :=
  Rec (App (FG_iter (Var 1)) (Load st.[ren (+2)])).

Definition FG_stack_body (st : expr) : expr :=
  Pair (Pair (FG_push st) (FG_pop st)) (FG_read_iter st).

Definition FG_stack : expr :=
  TLam (App (Rec (FG_stack_body (Var 1)))
                (Alloc (Fold (Alloc (InjL Unit))))).

Section FG_stack.
  (* Fine-grained push *)
  Lemma FG_push_folding (st : expr) :
    FG_push st =
    Rec (App (Rec
                (* try push *)
                (If (CAS (st.[ren (+4)]) (Var 1)
                         (Fold (Alloc (InjR (Pair (Var 3) (Var 1)))))
                    )
                    Unit (* push succeeds we return unit *)
                    (App (Var 2) (Var 3)) (* push fails, we try again *)
                )
             )
             (Load st.[ren (+2)]) (* read the stack pointer *)
        ).
  Proof. trivial. Qed.

  Section FG_push_type.
    (* The following assumption is simply ** WRONG ** *)
    (* We assume it though to just be able to prove that the
       stack we are implementing is /type-sane/ so to speak! *)
    Context (HEQTP : ∀ τ, EqType (FG_StackType τ)).

    Lemma FG_push_type st Γ τ :
      typed Γ st (Tref (FG_StackType τ)) →
      typed Γ (FG_push st) (TArrow τ TUnit).
    Proof.
      intros H1. repeat (econstructor; eauto using HEQTP).
      - eapply (context_weakening [_; _; _; _]); eauto.
      - by asimpl.
      - eapply (context_weakening [_; _]); eauto.
    Qed.
  End FG_push_type.

  Lemma FG_push_to_val st : to_val (FG_push st) = Some (FG_pushV st).
  Proof. trivial. Qed.

  Lemma FG_push_of_val st : of_val (FG_pushV st) = FG_push st.
  Proof. trivial. Qed.

  Global Opaque FG_pushV.

  Lemma FG_push_closed (st : expr) :
    (∀ f, st.[f] = st) → ∀ f, (FG_push st).[f] = FG_push st.
  Proof. intros H f. asimpl. unfold FG_push. rewrite ?H; trivial. Qed.

  Lemma FG_push_subst (st : expr) f : (FG_push st).[f] = FG_push st.[f].
  Proof. unfold FG_push. by asimpl. Qed.

  Global Opaque FG_push.

  (* Fine-grained push *)
  Lemma FG_pop_folding (st : expr) :
    FG_pop st =
    Rec (App (Rec
                ( App
                    (Rec
                       (
                         Case (Var 1)
                              (InjL Unit)
                              ( (* try popping *)
                                If
                                  (CAS
                                     (st.[ren (+7)])
                                     (Fold (Var 4))
                                     (Snd (Var 0))
                                  )
                                  (InjR (Fst (Var 0))) (* pop succeeds *)
                                  (App (Var 5) (Var 6)) (* pop fails, we retry*)
                              )
                       )
                    )
                    (
                      (Load (Var 1))
                    )
                )
             )
             (Unfold (Load st.[ren (+ 2)]))
        ).
  Proof. trivial. Qed.

  Section FG_pop_type.
    (* The following assumption is simply ** WRONG ** *)
    (* We assume it though to just be able to prove that the
       stack we are implementing is /type-sane/ so to speak! *)
    Context (HEQTP : ∀ τ, EqType (FG_StackType τ)).

    Lemma FG_pop_type st Γ τ :
      typed Γ st (Tref (FG_StackType τ)) →
      typed Γ (FG_pop st) (TArrow TUnit (TSum TUnit τ)).
    Proof.
      intros H1. repeat (econstructor; eauto using HEQTP).
      - eapply (context_weakening [_; _; _; _; _; _; _]); eauto.
      - asimpl; trivial.
      - eapply (context_weakening [_; _]); eauto.
    Qed.
  End FG_pop_type.

  Lemma FG_pop_to_val st : to_val (FG_pop st) = Some (FG_popV st).
  Proof. trivial. Qed.

  Lemma FG_pop_of_val st : of_val (FG_popV st) = FG_pop st.
  Proof. trivial. Qed.

  Global Opaque FG_popV.

  Lemma FG_pop_closed (st : expr) :
    (∀ f, st.[f] = st) → ∀ f, (FG_pop st).[f] = FG_pop st.
  Proof. intros H f. asimpl. unfold FG_pop. rewrite ?H; trivial. Qed.

  Lemma FG_pop_subst (st : expr) f : (FG_pop st).[f] = FG_pop st.[f].
  Proof. unfold FG_pop. by asimpl. Qed.

  Global Opaque FG_pop.

  (* Fine-grained iter *)
  Lemma FG_iter_folding (f : expr) :
    FG_iter f =
    Rec
      (Case (Load (Unfold (Var 1)))
            Unit
            (App (Rec (App (Var 3) (Snd (Var 2)))) (* recursive_call *)
                 (App f.[ren (+3)] (Fst (Var 0)))
            )
      ).
  Proof. trivial. Qed.

  Lemma FG_iter_type f Γ τ :
    typed Γ f (TArrow τ TUnit) →
    typed Γ (FG_iter f) (TArrow (FG_StackType τ) TUnit).
  Proof.
    intros H1.
    econstructor.
    eapply (Case_typed _ _ _ _ TUnit);
      [| repeat constructor
       | repeat econstructor; eapply (context_weakening [_; _; _]); eauto].
    econstructor.
    replace (Tref (TSum TUnit (TProd τ (FG_StackType τ)))) with
    ((Tref (TSum TUnit (TProd τ.[ren(+1)] (TVar 0)))).[(FG_StackType τ)/])
      by (by asimpl).
    repeat econstructor.
  Qed.

  Lemma FG_iter_to_val st : to_val (FG_iter st) = Some (FG_iterV st).
  Proof. trivial. Qed.

  Lemma FG_iter_of_val st : of_val (FG_iterV st) = FG_iter st.
  Proof. trivial. Qed.

  Global Opaque FG_popV.

  Lemma FG_iter_closed (f : expr) :
    (∀ g, f.[g] = f) → ∀ g, (FG_iter f).[g] = FG_iter f.
  Proof. intros H g. asimpl. unfold FG_iter. rewrite ?H; trivial. Qed.

  Lemma FG_iter_subst (f : expr) g : (FG_iter f).[g] = FG_iter f.[g].
  Proof. unfold FG_iter. by asimpl. Qed.

  Global Opaque FG_iter.

  Lemma FG_read_iter_type st Γ τ :
    typed Γ st (Tref (FG_StackType τ)) →
    typed Γ (FG_read_iter st)
          (TArrow (TArrow τ TUnit) TUnit).
  Proof.
    intros H1; repeat econstructor.
    - eapply FG_iter_type; by constructor.
    - by eapply (context_weakening [_;_]).
  Qed.

  Transparent FG_iter.

  Lemma FG_read_iter_closed (st : expr) :
    (∀ f, st.[f] = st) →
    ∀ f, (FG_read_iter st).[f] = FG_read_iter st.
  Proof.
    intros H1 f. unfold FG_read_iter, FG_iter. asimpl.
    by rewrite ?H1.
  Qed.

  Lemma FG_read_iter_subst (st : expr) g :
    (FG_read_iter st).[g] = FG_read_iter st.[g].
  Proof. by unfold FG_read_iter; asimpl. Qed.

  Global Opaque FG_iter.

  Section FG_stack_body_type.
    (* The following assumption is simply ** WRONG ** *)
    (* We assume it though to just be able to prove that the
       stack we are implementing is /type-sane/ so to speak! *)
    Context (HEQTP : ∀ τ, EqType (FG_StackType τ)).

    Lemma FG_stack_body_type st Γ τ :
      typed Γ st (Tref (FG_StackType τ)) →
      typed Γ (FG_stack_body st)
            (TProd
               (TProd (TArrow τ TUnit) (TArrow TUnit (TSum TUnit τ)))
               (TArrow (TArrow τ TUnit) TUnit)
            ).
    Proof.
      intros H1.
      repeat (econstructor; eauto using FG_push_type,
                            FG_pop_type, FG_read_iter_type).
    Qed.
  End FG_stack_body_type.

  Opaque FG_read_iter.

  Lemma FG_stack_body_closed (st : expr) :
    (∀ f, st.[f] = st) →
    ∀ f, (FG_stack_body st).[f] = FG_stack_body st.
  Proof.
    intros H1 f. unfold FG_stack_body. asimpl.
    rewrite FG_push_closed; trivial.
    rewrite FG_pop_closed; trivial.
    by rewrite FG_read_iter_closed.
  Qed.

  Section FG_stack_type.
    (* The following assumption is simply ** WRONG ** *)
    (* We assume it though to just be able to prove that the
       stack we are implementing is /type-sane/ so to speak! *)
    Context (HEQTP : ∀ τ, EqType (FG_StackType τ)).

    Lemma FG_stack_type Γ :
      typed Γ FG_stack
            (TForall
               (TProd
                  (TProd
                     (TArrow (TVar 0) TUnit)
                     (TArrow TUnit (TSum TUnit (TVar 0)))
                  )
                  (TArrow (TArrow (TVar 0) TUnit) TUnit)
            )).
    Proof.
      repeat econstructor.
      - eapply FG_push_type; try constructor; simpl; eauto.
      - eapply FG_pop_type; try constructor; simpl; eauto.
      - eapply FG_read_iter_type; constructor; by simpl.
      - asimpl. repeat constructor.
    Qed.
  End FG_stack_type.

  Lemma FG_stack_closed f : FG_stack.[f] = FG_stack.
  Proof.
    unfold FG_stack.
    asimpl; rewrite ?FG_push_subst ?FG_pop_subst.
    asimpl. rewrite ?FG_read_iter_subst. by asimpl.
  Qed.
End FG_stack.
