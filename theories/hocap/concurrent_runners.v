(** Concurrent Runner example from
    "Modular Reasoning about Separation of Concurrent Data Structures"
    <http://www.kasv.dk/articles/hocap-ext.pdf>
*)
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import cmra agree frac csum excl.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris.base_logic.lib Require Import fractional.
From iris_examples.hocap Require Import abstract_bag shared_bag.
Set Default Proof Using "Type".

Definition saR := csumR fracR (csumR (prodR fracR (agreeR valC)) (agreeR valC)).
Class saG Σ := { sa_inG :> inG Σ saR }.
Definition INIT `{saG Σ} γ (q: Qp) := own γ (Cinl q%Qp).
Definition SET_RES `{saG Σ} γ (q: Qp) (v: val) := own γ (Cinr (Cinl (q%Qp, to_agree v))).
Definition FIN `{saG Σ} γ (v: val) := own γ (Cinr (Cinr (to_agree v))).
Global Instance INIT_fractional `{saG Σ} γ : Fractional (INIT γ)%I.
Proof.
  intros p q. rewrite /INIT.
  rewrite -own_op. f_equiv.
Qed.
Global Instance INIT_as_fractional `{saG Σ} γ q:
  AsFractional (INIT γ q) (INIT γ)%I q.
Proof.
  split; [done | apply _].
Qed.
Global Instance SET_RES_fractional `{saG Σ} γ v : Fractional (fun q => SET_RES γ q v)%I.
Proof.
  intros p q. rewrite /SET_RES.
  rewrite -own_op Cinr_op Cinl_op pair_op. repeat f_equiv.
  intros n. split; intros a Ha; exists a; set_solver.
Qed.
Global Instance SET_RES_as_fractional `{saG Σ} γ q v:
  AsFractional (SET_RES γ q v) (fun q => SET_RES γ q v)%I q.
Proof.
  split; [done | apply _].
Qed.

Lemma new_INIT `{saG Σ} : (|==> ∃ γ, INIT γ 1%Qp)%I.
Proof. by apply own_alloc. Qed.
Lemma INIT_not_SET_RES `{saG Σ} γ q q' v :
  (INIT γ q -∗ SET_RES γ q' v -∗ False)%I.
Proof.
  iIntros "Hs Hp".
  iDestruct (own_valid_2 with "Hs Hp") as %[].
Qed.
Lemma INIT_not_FIN `{saG Σ} γ q v :
  (INIT γ q -∗ FIN γ v -∗ False)%I.
Proof.
  iIntros "Hs Hp".
  iDestruct (own_valid_2 with "Hs Hp") as %[].
Qed.
Lemma SET_RES_not_FIN `{saG Σ} γ q v v' :
  (SET_RES γ q v -∗ FIN γ v' -∗ False)%I.
Proof.
  iIntros "Hs Hp".
  iDestruct (own_valid_2 with "Hs Hp") as %[].
Qed.
Lemma SET_RES_agree `{saG Σ} (γ: gname) (q q': Qp) (v w: val) :
  SET_RES γ q v -∗ SET_RES γ q' w -∗ ⌜v = w⌝.
Proof.
  iIntros "Hs1 Hs2".
  iDestruct (own_valid_2 with "Hs1 Hs2") as %Hfoo.
  iPureIntro. rewrite Cinr_op Cinl_op pair_op in Hfoo.
  by destruct Hfoo as [_ ?%agree_op_invL'].
Qed.
Lemma FIN_agree `{saG Σ} (γ: gname) (v w: val) :
  FIN γ v -∗ FIN γ w -∗ ⌜v = w⌝.
Proof.
  iIntros "Hs1 Hs2".
  iDestruct (own_valid_2 with "Hs1 Hs2") as %Hfoo.
  iPureIntro. rewrite Cinr_op Cinr_op in Hfoo.
  by apply agree_op_invL'.
Qed.
Lemma INIT_SET_RES `{saG Σ} (v: val) γ :
  INIT γ 1%Qp ==∗ SET_RES γ 1%Qp v.
Proof.
  apply own_update.
  by apply cmra_update_exclusive.
Qed.
Lemma SET_RES_FIN `{saG Σ} (v w: val) γ :
  SET_RES γ 1%Qp v ==∗ FIN γ w.
Proof.
  apply own_update.
  by apply cmra_update_exclusive.
Qed.

Definition oneshotR := csumR fracR (agreeR valC).
Class oneshotG Σ := { oneshot_inG :> inG Σ oneshotR }.
Definition oneshotΣ : gFunctors := #[GFunctor oneshotR].
Instance subG_oneshotΣ {Σ} : subG oneshotΣ Σ → oneshotG Σ.
Proof. solve_inG. Qed.

Definition pending `{oneshotG Σ} γ q := own γ (Cinl q%Qp).
Definition shot `{oneshotG Σ} γ (v: val) := own γ (Cinr (to_agree v)).
Lemma new_pending `{oneshotG Σ} : (|==> ∃ γ, pending γ 1%Qp)%I.
Proof. by apply own_alloc. Qed.
Lemma shoot `{oneshotG Σ} (v: val) γ : pending γ 1%Qp ==∗ shot γ v.
Proof.
  apply own_update.
  by apply cmra_update_exclusive.
Qed.
Lemma shot_not_pending `{oneshotG Σ} γ v q :
  shot γ v -∗ pending γ q -∗ False.
Proof.
  iIntros "Hs Hp".
  iPoseProof (own_valid_2 with "Hs Hp") as "H".
  iDestruct "H" as %[].
Qed.
Lemma shot_agree `{oneshotG Σ} γ (v w: val) :
  shot γ v -∗ shot γ w -∗ ⌜v = w⌝.
Proof.
  iIntros "Hs1 Hs2".
  iDestruct (own_valid_2 with "Hs1 Hs2") as %Hfoo.
  iPureIntro. by apply agree_op_invL'.
Qed.
Global Instance pending_fractional `{oneshotG Σ} γ : Fractional (pending γ)%I.
Proof.
  intros p q. rewrite /pending.
  rewrite -own_op. f_equiv.
Qed.
Global Instance pending_as_fractional `{oneshotG Σ} γ q:
  AsFractional (pending γ q) (pending γ)%I q.
Proof.
  split; [done | apply _].
Qed.

Section contents.
  Context `{heapG Σ, !oneshotG Σ, !saG Σ}.
  Variable b : bag Σ.
  Variable N : namespace.

  (* new Task : Runner<A,B> -> A -> Task<A,B> *)
  Definition newTask : val := λ: "r" "a", ("r", "a", ref #0, ref NONEV).
  (* task_runner == Fst Fst Fst *)
  (* task_arg    == Snd Fst Fst *)
  (* task_state  == Snd Fst *)
  (* task_res    == Snd *)
  (* Task.Run : Task<A,B> -> () *)
  Definition task_Run : val := λ: "t",
    let: "runner" := Fst (Fst (Fst "t")) in
    let: "arg"    := Snd (Fst (Fst "t")) in
    let: "state"  := Snd (Fst "t") in
    let: "res"    := Snd "t" in
    let: "tmp" := (Fst "runner") "runner" "arg"
                  (* runner.body(runner,arg)*) in
    "res" <- (SOME "tmp");;
    "state" <- #1.

  (* Task.Join : Task<A,B> -> B *)
  Definition task_Join : val := rec: "join" "t" :=
    let: "runner" := Fst (Fst (Fst "t")) in
    let: "arg"    := Snd (Fst (Fst "t")) in
    let: "state"  := Snd (Fst "t") in
    let: "res"    := Snd "t" in
    if: (!"state" = #1) then !"res" else "join" "t".

  (* runner_body == Fst *)
  (* runner_bag  == Snd *)

  (* Runner.Fork : Runner<A,B> -> A -> Task<A,B> *)
  Definition runner_Fork : val := λ: "r" "a",
    let: "bag" := Snd "r" in
    let: "t" := newTask "r" "a" in
    pushBag b "bag" "t";;
    "t".

  (* Runner.runTask : Runner<A,B> -> () *)
  Definition runner_runTask : val := λ: "r",
    let: "bag" := Snd "r" in
    match: popBag b "bag" with
      NONE => #()
    | SOME "t" => task_Run "t"
    end.

  (* Runner.runTasks : Runner<A,B> -> () *)
  Definition runner_runTasks : val := rec: "runTasks" "r" :=
    runner_runTask "r";; "runTasks" "r".

  (* newRunner : (Runner<A,B> -> A -> B) -> nat -> Runner<A,B> *)
  Definition newRunner : val := λ: "body" "n",
    let: "bag" := newBag b #() in
    let: "r" := ("body", "bag") in
    let: "loop" :=
       (rec: "loop" "i" :=
          if: ("i" < "n")
          then Fork (runner_runTasks "r");; "loop" ("i"+#1)
          else "r"
       ) in
    "loop" #0.

  Definition task_inv (γ γ': gname) (state res: loc) (Q: val → iProp Σ) : iProp Σ :=
    ((state ↦ #0 ∗ res ↦ NONEV ∗ pending γ (1/2)%Qp ∗ INIT γ' (1/2)%Qp)
   ∨ (∃ v, state ↦ #0 ∗ res ↦ SOMEV v ∗ pending γ (1/2)%Qp ∗ SET_RES γ' (1/2)%Qp v)
   ∨ (∃ v, state ↦ #1 ∗ res ↦ SOMEV v ∗ FIN γ' v ∗ (Q v ∗ pending γ (1/2)%Qp ∨ shot γ v)))%I.
  Definition isTask (r: val) (γ γ': gname) (t: val) (P Q: val → iProp Σ) : iProp Σ :=
    (∃ (arg : val) (state res : loc),
     ⌜t = (r, arg, #state, #res)%V⌝
     ∗ P arg ∗ INIT γ' (1/2)%Qp
     ∗ inv (N.@"task") (task_inv γ γ' state res Q))%I.
  Definition task (γ γ': gname) (t : val) (P Q: val → iProp Σ) : iProp Σ :=
    (∃ (r arg : val) (state res : loc),
     ⌜t = (r, arg, #state, #res)%V⌝
     ∗ pending γ (1/2)%Qp
     ∗ inv (N.@"task") (task_inv γ γ' state res Q))%I.

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

  Ltac solve_proper ::= solve_proper_core ltac:(fun _ => simpl; auto_equiv).

  Program Definition isRunner1 (γ : name Σ b) (P Q : val → iProp Σ) :
    (valC -n> iProp Σ) -n> (valC -n> iProp Σ) := λne R r,
    (∃ (body bag : val), ⌜r = (body, bag)%V⌝
     ∗ bagS b (N.@"bag") (λ x y, ∃ γ γ', isTask (body,x) γ γ' y P Q) γ bag
     ∗ ▷ ∀ r a: val, □ (R r ∗ P a -∗ WP body r a {{ Q }}))%I.
  Solve Obligations with solve_proper.

  Global Instance isRunner1_contractive (γ : name Σ b) P Q :
    Contractive (isRunner1 γ P Q).
  Proof. unfold isRunner1. solve_contractive. Qed.

  Definition isRunner (γ: name Σ b) (P Q : val → iProp Σ) : valC -n> iProp Σ :=
    (fixpoint (isRunner1 γ P Q))%I.

  Lemma isRunner_unfold γ r P Q :
    isRunner γ P Q r ≡
      (∃ (body bag : val), ⌜r = (body, bag)%V⌝
       ∗ bagS b (N.@"bag") (λ x y, ∃ γ γ', isTask (body,x) γ γ' y P Q) γ bag
       ∗ ▷ ∀ r a: val, □ (isRunner γ P Q r ∗ P a -∗ WP body r a {{ Q }}))%I.
  Proof. rewrite /isRunner. by rewrite {1}fixpoint_unfold. Qed.

  Global Instance isRunner_persistent γ r P Q :
    Persistent (isRunner γ P Q r).
  Proof. rewrite /isRunner fixpoint_unfold. apply _. Qed.

  Lemma newTask_spec γb (r : val) P Q a :
    {{{ isRunner γb P Q r ∗ P a }}}
      newTask r a
    {{{ γ γ' t, RET t; isTask r γ γ' t P Q ∗ task γ γ' t P Q }}}.
  Proof.
    iIntros (Φ) "[#Hrunner HP] HΦ".
    unfold newTask. do 2 wp_rec. iApply wp_fupd.
    wp_alloc status as "Hstatus".
    wp_alloc res as "Hres".
    iMod (new_pending) as (γ) "[Htoken Htask]".
    iMod (new_INIT) as (γ') "[Hinit Hinit']".
    iMod (inv_alloc (N.@"task") _ (task_inv γ γ' status res Q)%I with "[-HP HΦ Htask Hinit]") as "#Hinv".
    { iNext. iLeft. iFrame. }
    iModIntro. iApply "HΦ".
    iFrame. iSplitL; iExists _,_,_;[|iExists _]; iFrame "Hinv"; eauto.
  Qed.

  Lemma task_Join_spec γb γ γ' r t P Q `{∀ v, Timeless (Q v)}:
    {{{ isRunner γb P Q r ∗ task γ γ' t P Q }}}
       task_Join t
    {{{ v res, RET res; ⌜res = SOMEV v⌝ ∗ Q v }}}.
  Proof.
    iIntros (Φ) "[#Hrunner Htask] HΦ".
    iLöb as "IH".
    rewrite {2}/task_Join.
    iDestruct "Htask" as (r' arg state res) "(% & Htoken & #Htask)". simplify_eq.
    repeat wp_pure _.
    wp_bind (! #state)%E. iInv (N.@"task") as ">Hstatus" "Hcl".
    rewrite {2}/task_inv.
    iDestruct "Hstatus" as "[(Hstate & Hres)|[Hstatus|Hstatus]]".
    - wp_load.
      iMod ("Hcl" with "[Hstate Hres]") as "_".
      { iNext; iLeft; iFrame. }
      iModIntro. wp_op. wp_if.
      rewrite /task_Join. iApply ("IH" with "[$Htoken] HΦ").
      iExists _,_,_,_; iFrame "Htask". eauto.
    - iDestruct "Hstatus" as (v) "(Hstate & Hres & HQ)".
      wp_load.
      iMod ("Hcl" with "[Hstate Hres HQ]") as "_".
      { iNext; iRight; iLeft. iExists _; iFrame. }
      iModIntro. wp_op. wp_if.
      rewrite /task_Join. iApply ("IH" with "[$Htoken] HΦ").
      iExists _,_,_,_; iFrame "Htask". eauto.
    - iDestruct "Hstatus" as (v) "(Hstate & Hres & #HFIN & HQ)".
      wp_load.
      iDestruct "HQ" as "[[HQ Htoken2]|Hshot]"; last first.
      { iExFalso. iApply (shot_not_pending with "Hshot Htoken"). }
      iMod (shoot v γ with "[Htoken Htoken2]") as "#Hshot".
      { iApply (fractional_split_2 with "Htoken Htoken2").
        assert ((1 / 2 + 1 / 2)%Qp = 1%Qp) as -> by apply Qp_div_2.
        apply _. }
      iMod ("Hcl" with "[Hstate Hres]") as "_".
      { iNext. iRight. iRight. iExists _. iFrame. iFrame "HFIN".
        iRight. eauto. }
      iModIntro. wp_op. wp_if.
      iInv (N.@"task") as ">[(Hstate & Hres & Hpending & HINIT)|[Hstatus|Hstatus]]" "Hcl".
      { iExFalso. iApply (shot_not_pending with "Hshot Hpending"). }
      { iDestruct "Hstatus" as (v') "(Hstate & Hres & Hpending & HSETRES)".
        iExFalso. iApply (SET_RES_not_FIN with "HSETRES HFIN"). }
      iDestruct "Hstatus" as (v') "(Hstate & Hres & _ & HQ')".
      iAssert (⌜v = v'⌝)%I with "[HQ']" as %<-.
      { iDestruct "HQ'" as "[[? Hpending]|Hshot']".
        - iExFalso. iApply (shot_not_pending with "Hshot Hpending").
        - iApply (shot_agree with "Hshot Hshot'"). }
      iClear "HQ'". wp_load.
      iMod ("Hcl" with "[Hres Hstate]") as "_".
      { iNext. iRight. iRight. iExists _; iFrame. iFrame "HFIN". by iRight. }
      iModIntro. iApply "HΦ"; eauto.
  Qed.

  Lemma task_Run_spec γb γ γ' r t P Q `{∀ v, Timeless (Q v)}:
    {{{ isRunner γb P Q r ∗ isTask r γ γ' t P Q }}}
       task_Run t
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "[#Hrunner Htask] HΦ".
    rewrite isRunner_unfold.
    iDestruct "Hrunner" as (body bag) "(% & #Hbag & #Hbody)".
    iDestruct "Htask" as (arg state res) "(% & HP & HINIT & #Htask)".
    simplify_eq. rewrite /task_Run.
    repeat wp_pure _.
    wp_bind (body _ arg).
    iDestruct ("Hbody" $! (PairV body bag) arg) as "Hbody'".
    iSpecialize ("Hbody'" with "[HP]").
    { iFrame. rewrite isRunner_unfold.
      iExists _,_; iSplitR; eauto. }
    iApply (wp_wand with "Hbody'").
    iIntros (v) "HQ". wp_let.
    wp_bind (#res <- SOME v)%E.
    iInv (N.@"task") as ">[(Hstate & Hres & Hpending & HINIT')|[Hstatus|Hstatus]]" "Hcl".
    - wp_store.
      iMod (INIT_SET_RES v γ' with "[HINIT HINIT']") as "[HSETRES HSETRES']".
      { iApply (fractional_split_2 with "HINIT HINIT'").
        assert ((1 / 2 + 1 / 2)%Qp = 1%Qp) as -> by apply Qp_div_2.
        apply _. }
      iMod ("Hcl" with "[HSETRES Hstate Hres Hpending]") as "_".
      { iNext. iRight. iLeft. iExists _; iFrame. }
      iModIntro. wp_let.
      iInv (N.@"task") as ">[(Hstate & Hres & Hpending & HINIT')|[Hstatus|Hstatus]]" "Hcl".
      { iExFalso. iApply (INIT_not_SET_RES with "HINIT' HSETRES'"). }
      + iDestruct "Hstatus" as (v') "(Hstate & Hres & Hpending & HSETRES)".
        wp_store.
        iDestruct (SET_RES_agree with "HSETRES HSETRES'") as %->.
        iMod (SET_RES_FIN v v with "[HSETRES HSETRES']") as "#HFIN".
        { iApply (fractional_split_2 with "HSETRES HSETRES'").
          assert ((1 / 2 + 1 / 2)%Qp = 1%Qp) as -> by apply Qp_div_2.
          apply _. }
        iMod ("Hcl" with "[-HΦ]") as "_".
        { iNext. do 2 iRight. iExists _; iFrame. iFrame "HFIN". iLeft. iFrame.  }
        iModIntro. by iApply "HΦ".
      + iDestruct "Hstatus" as (v') "(Hstate & Hres & HFIN & HQ')".
        iExFalso. iApply (SET_RES_not_FIN with "HSETRES' HFIN").
    - iDestruct "Hstatus" as (v') "(Hstate & Hres & Hpending & HSETRES)".
      iExFalso. iApply (INIT_not_SET_RES with "HINIT HSETRES").
    - iDestruct "Hstatus" as (v') "(Hstate & Hres & HFIN & HQ')".
      iExFalso. iApply (INIT_not_FIN with "HINIT HFIN").
  Qed.

  Lemma runner_runTask_spec γb P Q r `{∀ v, Timeless (Q v)}:
    {{{ isRunner γb P Q r }}}
      runner_runTask r
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "#Hrunner HΦ".
    rewrite isRunner_unfold /runner_runTask.
    iDestruct "Hrunner" as (body bag) "(% & #Hbag & #Hbody)"; simplify_eq.
    repeat wp_pure _.
    wp_bind (popBag b _).
    iApply (popBag_spec with "Hbag").
    iNext. iIntros (t') "[_ [%|Ht]]"; simplify_eq.
    - wp_match. by iApply "HΦ".
    - iDestruct "Ht" as (t) "[% Ht]".
      iDestruct "Ht" as (γ γ') "Htask".
      simplify_eq. wp_match.
      iApply (task_Run_spec with "[Hbag Hbody Htask]"); last done.
      iFrame "Htask". rewrite isRunner_unfold.
      iExists _,_; iSplit; eauto.
  Qed.

  Lemma runner_runTasks_spec γb P Q r `{∀ v, Timeless (Q v)}:
    {{{ isRunner γb P Q r }}}
      runner_runTasks r
    {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "#Hrunner HΦ".
    iLöb as "IH". rewrite /runner_runTasks.
    wp_rec. wp_bind (runner_runTask r).
    iApply runner_runTask_spec; eauto.
    iNext. iIntros "_". wp_rec. by iApply "IH".
  Qed.

  Lemma loop_spec (n i : nat) P Q γb r `{∀ v, Timeless (Q v)}:
    {{{ isRunner γb P Q r }}}
      (rec: "loop" "i" :=
         if: "i" < #n
         then Fork (runner_runTasks r);; "loop" ("i" + #1)
         else r) #i
    {{{ r, RET r; isRunner γb P Q r }}}.
  Proof.
    iIntros (Φ) "#Hrunner HΦ".
    iLöb as "IH" forall (i).
    wp_rec. wp_op. case_bool_decide; wp_if; last first.
    { by iApply "HΦ". }
    wp_bind (Fork _). iApply wp_fork. iSplitL.
    - iNext. wp_rec. wp_op.
      (* Set Printing Coercions. *)
      assert ((Z.of_nat i + 1) = Z.of_nat (i + 1)) as -> by lia.
      iApply ("IH" with "HΦ").
    - iNext. by iApply runner_runTasks_spec.
  Qed.

  Lemma newRunner_spec (f : val) (n : nat) P Q `{∀ v, Timeless (Q v)}:
    {{{ ∀ (γ: name Σ b) (r: val),
          □ ∀ a: val, (isRunner γ P Q r ∗ P a -∗ WP f r a {{ Q }}) }}}
       newRunner f #n
    {{{ γb r, RET r; isRunner γb P Q r }}}.
  Proof.
    iIntros (Φ) "#Hf HΦ".
    unfold newRunner. iApply wp_fupd.
    repeat wp_pure _.
    wp_bind (newBag b #()).
    iApply (newBag_spec b (N.@"bag") (λ x y, ∃ γ γ', isTask (f,x) γ γ' y P Q)%I); auto.
    iNext. iIntros (bag). iDestruct 1 as (γb) "#Hbag".
    do 3 wp_let.
    iAssert (isRunner γb P Q (PairV f bag))%I with "[]" as "#Hrunner".
    { rewrite isRunner_unfold. iExists _,_. iSplit; eauto. }
    iApply (loop_spec n 0 with "Hrunner [HΦ]"); eauto.
    iNext. iIntros (r) "Hr". by iApply "HΦ".
  Qed.

  Lemma runner_Fork_spec γb r P Q a `{∀ v, Timeless (Q v)}:
    {{{ isRunner γb P Q r ∗ P a }}}
       runner_Fork r a
    {{{ γ γ' t, RET t; task γ γ' t P Q }}}.
  Proof.
    iIntros (Φ) "[#Hrunner HP] HΦ".
    rewrite /runner_Fork isRunner_unfold.
    iDestruct "Hrunner" as (body bag) "(% & #Hbag & #Hbody)". simplify_eq.
    Local Opaque newTask.
    repeat wp_pure _. wp_bind (newTask _ _).
    iApply (newTask_spec γb (PairV body bag) P Q with "[Hbag Hbody HP]").
    { iFrame "HP". rewrite isRunner_unfold.
      iExists _,_; iSplit; eauto. }
    iNext. iIntros (γ γ' t) "[Htask Htask']". wp_let.
    wp_bind (pushBag _ _ _).
    iApply (pushBag_spec with "[$Hbag Htask]"); eauto.
    iNext. iIntros "_". wp_rec. by iApply "HΦ".
  Qed.
End contents.
