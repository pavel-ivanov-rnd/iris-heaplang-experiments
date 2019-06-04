From iris.algebra Require Import excl auth agree frac list cmra.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
Import uPred bi List Decidable.
Set Default Proof Using "Type".

(** Using prophecy variables with helping: implementing conditional counter from
    "Logical Relations for Fine-Grained Concurrency" by Turon et al. (POPL 2013) *)

(** * Implementation of the functions. *)

(*
  new_counter() :=
    let c = ref (injL 0) in
    let f = ref false in
    ref (f, c)
 *)
Definition new_counter : val :=
  λ: <>,
    let: "c" := ref (ref (InjL #0)) in
    let: "f" := ref #true in
    ("f", "c").

(*
  set_flag(ctr, b) :=
    ctr.1 <- b
 *)
Definition set_flag : val :=
  λ: "ctr" "b",
    Fst "ctr" <- "b".

(*
  complete(c, f, x, n, p) :=
    Resolve CAS(c, x, ref (injL (if !f then n+1 else n))) p (ref ()) ;; ()
 *)
Definition complete : val :=
  λ: "c" "f" "x" "n" "p",
    Resolve (CAS "c" "x" (ref (InjL (if: !"f" then "n" + #1 else "n")))) "p" (ref #()) ;; #().

(*
  get(c, f) :=
    let x = !c in
    match !x with
    | injL n      => n
    | injR (n, p) => complete c f x n p; get(c, f)
 *)
Definition get : val :=
  rec: "get" "ctr" :=
    let: "f" := Fst "ctr" in
    let: "c" := Snd "ctr" in
    let: "x" := !"c" in
    match: !"x" with
      InjL "n"    => "n"
    | InjR "args" =>
        complete "c" "f" "x" (Fst "args") (Snd "args") ;;
        "get" "ctr"
    end.

(*
  cinc(c, f) :=
    let x = !c in
    match !x with
    | injL n =>
        let p := new proph in
        let y := ref (injR (n, p)) in
        if CAS(c, x, y) then complete(c, f, y, n, p)
        else cinc(c, f)
    | injR (n, p) =>
        complete(c, f, x, n, p);
        cinc(c, f)
 *)
Definition cinc : val :=
  rec: "cinc" "ctr" :=
    let: "f" := Fst "ctr" in
    let: "c" := Snd "ctr" in
    let: "x" := !"c" in
    match: !"x" with
      InjL "n" =>
        let: "p" := NewProph in
        let: "y" := ref (InjR ("n", "p")) in
        if: CAS "c" "x" "y" then complete "c" "f" "y" "n" "p" ;; Skip
        else "cinc" "ctr"
    | InjR "args'" =>
        complete "c" "f" "x" (Fst "args'") (Snd "args'") ;;
        "cinc" "ctr"
    end.

(** ** Proof setup *)

(** To represent histories of allocated locations, we need some helper lemmas
    about suffixes on lists. *)
Section suffixes.

  Lemma suffix_trans (h1 h2 h3 : list loc) :
    h1 `suffix_of` h2 →
    h2 `suffix_of` h3 →
    h1 `suffix_of` h3.
  Proof.
    intros [? ->] [? ->]. rewrite app_assoc. by eexists.
  Qed.

  Lemma suffix_eq (h1 h2 : list loc) :
    h1 `suffix_of` h2 →
    h2 `suffix_of` h1 →
    h1 = h2.
  Proof.
    intros [xs ->] [ys Heq]. rewrite <- app_nil_l in Heq at 1. rewrite app_assoc in Heq.
    apply app_inv_tail, eq_sym in Heq. by apply app_eq_nil in Heq as [_ ->].
  Qed.

  Lemma suffix_in (h1 h2 : list loc) l :
    h1 `suffix_of` h2 →
    In l h1 →
    In l h2.
  Proof.
    destruct h1 as [|y ys]; first done.
    intros Hs Hin. destruct Hs as [l2' ->]. apply in_or_app. by right.
  Qed.

  Lemma suffix_in_head (h1 h2 : list loc) l :
    h1 `suffix_of` h2 →
    Some l = head h1 →
    In l h2.
  Proof.
    destruct h1 as [|y ys]; first done.
    intros Hs [=->]. eapply suffix_in; first done. apply in_eq.
  Qed.

  (** A helper lemma that will come up in the proof of [complete] *)
  Lemma nodup_suffix_contradiction (l1 l2 l3 : loc) (H1 H2 H3 : list loc) :
    Some l1 = hd_error H1 →
    Some l2 = hd_error H2 →
    Some l3 = hd_error H3 →
    In l3 H1 →
    H1 `suffix_of` H2 →
    H2 `suffix_of` H3 →
    l2 ≠ l3 →
    NoDup H3 →
    False.
  Proof.
    intros Heq Heq' Heq'' Hin Hs Hs' Hn Hd.
    destruct Hs' as [xs ->]. destruct Hs as [ys ->]. destruct (in_split _ _ Hin) as (x & y & ->).
    do 2 rewrite app_assoc in Hd. apply NoDup_remove_2 in Hd.
    (* xs, ys, and x must be empty *)
    destruct xs as [|x' xs]; last first.
    { simpl in *. inversion Heq''. subst.
      contradict Hd. by left. }
    destruct ys as [|y' ys]; last first.
    { simpl in *. inversion Heq''; subst.
      contradict Hd. by left. }
    destruct x as [|z' zs]; last first.
    { simpl in *. inversion Heq''; subst.
      contradict Hd. by left. }
    simpl in *. inversion Heq'; done.
  Qed.

End suffixes.

(** Resource algebra for histories *)
Section histories.

  Inductive hist :=
  | histv (h : list loc) : hist
  | histbot : hist.

  Inductive hist_equiv : Equiv hist :=
  | Hist_equiv h1 h2 : h1 = h2 → h1 ≡ h2.

  Existing Instance hist_equiv.

  Instance hist_equiv_Equivalence : @Equivalence hist equiv.
  Proof.
    split.
    - move => [|]; by constructor.
    - move => [?|] []; inversion 1; subst; by constructor.
    - move => [?|] [] [];
               inversion 1; inversion 1; subst; by constructor.
  Qed.

  Canonical Structure histC : ofeT := discreteC hist.

  Instance hist_valid : Valid hist :=
    λ x, match x with histv _ => True | histbot => False end.

  Instance hist_op : Op hist := λ h1 h2,
                                match h1, h2 with
                                | histv h1', histv h2' =>
                                  if decide (h1' `suffix_of` h2')
                                  then h2
                                  else if decide (h2' `suffix_of` h1')
                                       then h1
                                       else histbot
                                | _, _ =>
                                  histbot
                                end.

  Arguments op _ _ !_ !_ /.

  Instance hist_PCore : PCore hist := Some.

  Global Instance hist_op_comm: Comm equiv hist_op.
  Proof.
    intros [h1|] [h2|]; auto. simpl.
    case_decide as H1; [case_decide as H2|auto]; last auto.
    constructor. destruct H1. subst.  destruct H2.
    rewrite <- app_nil_l in H at 1. rewrite app_assoc in H.
      by apply app_inv_tail, eq_sym, app_eq_nil in H as [-> ->].
  Qed.

  Global Instance hist_op_idemp : IdemP eq hist_op.
  Proof. intros [|]; [by simpl; rewrite decide_True|auto]. Qed.

  Lemma hist_op_l h1 h2 (Le: h1 `suffix_of` h2) :
    histv h1 ⋅ histv h2 = histv h2.
  Proof. simpl. case_decide; done. Qed.

  Lemma hist_op_r h1 h2 (Le: h1 `suffix_of` h2) :
    histv h2 ⋅ histv h1 = histv h2.
  Proof.
    simpl. case_decide.
    - f_equal. by apply suffix_eq.
    - by case_decide.
  Qed.

  Global Instance hist_op_assoc: Assoc equiv (op: Op hist).
  Proof.
    intros [h1|] [h2|] [h3|]; eauto; simpl.
    - repeat (case_decide; auto).
      + rewrite !hist_op_l; auto. etrans; eauto.
      + simpl. repeat case_decide; last done.
        * destruct H as [xs ->]. destruct H2 as [ys [[k [->->]] | [k [->->]]]%app_eq_inv].
          ** contradict H1. by apply suffix_app_r.
          ** contradict H0. by apply suffix_app_r.
        * contradict H1. by etrans.
      + rewrite hist_op_l; [by rewrite hist_op_r|auto].
      + rewrite !hist_op_r; auto. by etrans.
      + simpl. rewrite !decide_False; auto.
      + simpl. rewrite !decide_False; auto.
      + simpl. case_decide.
        * exfalso. apply H. by etrans.
        * case_decide; last done. exfalso.
          destruct H4 as [xs ->]. destruct H2 as [ys [[k [->->]] | [k [->->]]]%app_eq_inv].
          ** contradict H0. by apply suffix_app_r.
          ** contradict H. by apply suffix_app_r.
    - simpl. repeat case_decide; auto.
  Qed.

  Lemma hist_included h1 h2 :
    histv h1 ≼ histv h2 ↔ h1 `suffix_of` h2.
  Proof.
    split.
    - move => [[?|]]; simpl; last by inversion 1.
      case_decide.
      * inversion 1. naive_solver.
      * case_decide; inversion 1; naive_solver.
    - intros. exists (histv h2). by rewrite hist_op_l.
  Qed.

  Lemma hist_valid_op h1 h2 :
    ✓ (histv h1 ⋅ histv h2) → h1 `suffix_of` h2 ∨ h2 `suffix_of` h1.
  Proof. simpl. case_decide; first by left. case_decide; [by right|done]. Qed.

  Lemma hist_core_self (X: hist) : core X = X.
  Proof. done. Qed.

  Instance hist_unit : Unit hist := histv nil.

  Definition hist_ra_mixin : RAMixin hist.
  Proof.
    apply ra_total_mixin; eauto.
    - intros [?|] [?|] [?|]; auto; inversion 1; naive_solver.
    - by destruct 1; constructor.
    - destruct 1. naive_solver.
    - apply hist_op_assoc.
    - apply hist_op_comm.
    - intros ?. by rewrite hist_core_self idemp_L.
    - intros [|] [|]; simpl; done.
  Qed.

  Canonical Structure histR := discreteR hist hist_ra_mixin.

  Global Instance hist_cmra_discrete : CmraDiscrete histR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance hist_core (h: hist) : CoreId h.
  Proof.
    rewrite /CoreId. reflexivity.
  Qed.

  Definition hist_ucmra_mixin : UcmraMixin hist.
  Proof.
    split; [done| |auto]. intros [|]; [simpl|done]. done.
  Qed.

  Lemma hist_local_update h1 X h2 :
    h1 `suffix_of` h2 → (histv h1, X) ~l~> (histv h2, histv h2).
  Proof.
    intros Le. rewrite local_update_discrete.
    move => [[h3|]|] /= ? Eq; split => //; last first; move : Eq.
    - destruct X; by inversion 1.
    - destruct X; rewrite /cmra_op /= => Eq;
                                          repeat case_decide; auto; inversion Eq; subst; try naive_solver.
      + constructor. inversion H1. subst. f_equal. by apply suffix_eq.
      + constructor. inversion H2. subst. f_equal. apply suffix_eq; by etrans.
      + inversion H3; subst. by apply (suffix_trans _ _ _ H0) in Le.
  Qed.

  Canonical Structure histUR := UcmraT hist hist_ucmra_mixin.

End histories.

Definition histListUR := optionUR $ prodR fracR $ agreeR $ listC locC.

Definition historyUR := prodUR (authUR histListUR) (authUR histUR).
Definition flagUR    := authR $ optionUR $ exclR boolC.
Definition numUR     := authR $ optionUR $ exclR ZC.
Definition tokenUR   := authR $ optionUR $ exclR valC.

Class cincG Σ := ConditionalIncrementG {
                     cinc_historyG :> inG Σ historyUR;
                     cinc_flagG    :> inG Σ flagUR;
                     cinc_numG     :> inG Σ numUR;
                     cinc_tokenG   :> inG Σ tokenUR;
                   }.

Definition cincΣ : gFunctors :=
  #[GFunctor historyUR; GFunctor flagUR; GFunctor numUR; GFunctor tokenUR].

Instance subG_cincΣ {Σ} : subG cincΣ Σ → cincG Σ.
Proof. solve_inG. Qed.

Section conditional_counter.
  Context {Σ} `{!heapG Σ, !cincG Σ}.
  Context (N : namespace).

  Local Definition stateN   := N .@ "state".
  Local Definition counterN := N .@ "counter".

  Definition token : tokenUR :=
    ● Excl' #().

  Definition histList (H : list loc) (q : Qp) : histListUR :=
    Some (q, to_agree H).

  Definition half_history_frag (H : list loc) : historyUR :=
    (◯ (histList H (1/2)%Qp), ◯ (histv H)).

  Definition full_history_frag (H : list loc) : historyUR :=
    (◯ (histList H 1%Qp), ◯ (histv H)).

  Definition full_history_auth (H : list loc) : historyUR :=
    (● (histList H 1%Qp), ● (histv H)).

  Definition hist_snapshot H : historyUR :=
    (◯ None, ◯ histv H).

  Global Instance snapshot_persistent H γ_h : Persistent (own γ_h (hist_snapshot H)).
  Proof.
    apply own_core_persistent. rewrite /CoreId. done.
  Qed.

  (** Updating and synchronizing history RAs *)

  Lemma sync_histories H1 H2 γ_h :
    own γ_h (half_history_frag H1) -∗ own γ_h (half_history_frag H2) -∗ ⌜H1 = H2⌝.
  Proof.
    iIntros "H1 H2". iCombine "H1" "H2" as "H". iPoseProof (own_valid with "H") as "H".
    iDestruct "H" as %H. iPureIntro. destruct H as [[_ Hl1%agree_op_inv] _].
    by apply to_agree_inj, leibniz_equiv in Hl1.
  Qed.

  Lemma add_half_histories (H : list loc) γ_h :
    own γ_h (half_history_frag H) -∗
        own γ_h (half_history_frag H) -∗
        own γ_h (full_history_frag H).
  Proof.
    iIntros "H1 H2". iCombine "H1" "H2" as "H". done.
  Qed.

  Lemma update_history H H' l γ_h :
    own γ_h (full_history_auth H) -∗
        own γ_h (half_history_frag H) -∗
        own γ_h (half_history_frag H') ==∗
        own γ_h (full_history_auth (l :: H)) ∗
        own γ_h (half_history_frag (l :: H)) ∗
        own γ_h (half_history_frag (l :: H)).
  Proof.
    iIntros "H● H1◯ H2◯". iDestruct (sync_histories with "H1◯ H2◯") as %<-.
    iDestruct (add_half_histories with "H1◯ H2◯") as "H◯".
    iCombine "H● H◯" as "H". rewrite -own_op -own_op.
    iApply (own_update with "H"). apply prod_update.
    - apply auth_update, option_local_update. rewrite pair_op frac_op' agree_idemp.
      rewrite Qp_div_2. apply exclusive_local_update. by constructor.
    - apply auth_update. simpl. rewrite hist_op_l; last done.
        by apply hist_local_update, suffix_cons_r.
  Qed.

  Lemma sync_snapshot H1 H2 H2' γ_h :
    own γ_h (full_history_auth H1) -∗ own γ_h (◯ H2', ◯ histv H2) -∗ ⌜H2 `suffix_of` H1⌝.
  Proof.
    iIntros "H● H◯". iCombine "H●" "H◯" as "H".
      by iDestruct (own_valid with "H") as %[_ [Hs%hist_included _]%auth_both_valid].
  Qed.

  Lemma extract_snapshot H γ_h :
     own γ_h (half_history_frag H) -∗ □ own γ_h (hist_snapshot H).
   Proof.
     iIntros "H".
     iAssert (own γ_h (half_history_frag H) ∗ own γ_h (hist_snapshot H))%I with "[H]" as "[_ H2]".
     { rewrite -own_op pair_op.
       assert (◯ histList H (1 / 2) ⋅ ◯ None = ◯ (histList H (1 / 2) ⋅ None)) as Heq by apply auth_frag_op.
       assert (◯ histv H ⋅ ◯ histv H = ◯ (histv H ⋅ histv H)) as Heq' by apply auth_frag_op.
       rewrite Heq Heq' right_id. rewrite <- core_id_dup; first done. by rewrite /CoreId. }
     rewrite intuitionistically_into_persistently.
     by iApply persistent.
   Qed.

  Lemma sync_counter_values γ_n (n m : Z) :
    own γ_n (● Excl' n) -∗ own γ_n (◯ Excl' m) -∗ ⌜n = m⌝.
  Proof.
    iIntros "H● H◯". iCombine "H●" "H◯" as "H". iDestruct (own_valid with "H") as "H".
      by iDestruct "H" as %[H%Excl_included%leibniz_equiv _]%auth_both_valid.
  Qed.


  (** Updating and synchronizing the counter and flag RAs *)

  Lemma sync_flag_values γ_n (b1 b2 : bool) :
    own γ_n (● Excl' b1) -∗ own γ_n (◯ Excl' b2) -∗ ⌜b1 = b2⌝.
  Proof.
    iIntros "H● H◯". iCombine "H●" "H◯" as "H". iDestruct (own_valid with "H") as "H".
      by iDestruct "H" as %[H%Excl_included%leibniz_equiv _]%auth_both_valid.
  Qed.

  Lemma update_counter_value γ_n (n1 n2 m : Z) :
    own γ_n (● Excl' n1) -∗ own γ_n (◯ Excl' n2) ==∗ own γ_n (● Excl' m) ∗ own γ_n (◯ Excl' m).
  Proof.
    iIntros "H● H◯". iCombine "H●" "H◯" as "H". rewrite -own_op. iApply (own_update with "H").
    by apply auth_update, option_local_update, exclusive_local_update.
  Qed.

  Lemma update_flag_value γ_n (b1 b2 b : bool) :
    own γ_n (● Excl' b1) -∗ own γ_n (◯ Excl' b2) ==∗ own γ_n (● Excl' b) ∗ own γ_n (◯ Excl' b).
  Proof.
    iIntros "H● H◯". iCombine "H●" "H◯" as "H". rewrite -own_op. iApply (own_update with "H").
    by apply auth_update, option_local_update, exclusive_local_update.
  Qed.

  Definition counter_content (γs : gname * gname * gname) (c : bool * Z) :=
    (own γs.1.2 (◯ Excl' c.1) ∗ own γs.2 (◯ Excl' c.2))%I.


  (** Definition of the invariant *)

  Fixpoint val_to_some_loc (vs : list (val * val)) : option loc :=
    match vs with
    | (#true , LitV (LitLoc l)) :: _  => Some l
    | _                         :: vs => val_to_some_loc vs
    | _                               => None
    end.

  Lemma val_to_some_loc_some vs l :
    val_to_some_loc vs = Some l →
    ∃ v1 v2 vs', vs = (v1, v2) :: vs' ∧
       ( (v1 = #true ∧ v2 = LitV (LitLoc l))
       ∨ val_to_some_loc vs' = Some l).
  Proof.
    intros H. destruct vs as [|[v1 v2] vs']; first done.
    exists v1, v2, vs'. split; first done.
    destruct v1; try by right. destruct l0; try by right.
    destruct b; try by right. destruct v2; try by right.
    destruct l0; try by right. simpl in H. inversion H. by left.
  Qed.

  Inductive abstract_state : Set :=
  | injl : Z → abstract_state
  | injr : Z → proph_id → abstract_state.

  Definition own_token γ_t := (own γ_t token)%I.

  Definition used_up l γ_h :=
    (∃ H, □ own γ_h (hist_snapshot H) ∗ ⌜In l H ∧ Some l ≠ head H⌝)%I.

  Definition not_done_state H l (γ_h : gname) :=
    (own γ_h (half_history_frag H) ∗ ⌜Some l = head H⌝)%I.

  Definition pending_state P (n : Z) vs l_ghost (γ_h γ_n : gname) :=
    (P ∗ ⌜match val_to_some_loc vs with None => True | Some l => l = l_ghost end⌝ ∗ own γ_n (● Excl' n))%I.

  Definition accepted_state Q vs (l l_ghost : loc) (γ_h : gname) :=
    (l_ghost ↦{1/2} - ∗ match val_to_some_loc vs with None => True | Some l => ⌜l = l_ghost⌝ ∗ Q end)%I.

  Definition done_state Q (l l_ghost : loc) (γ_t γ_h  : gname) :=
    ((Q ∨ own_token γ_t) ∗ l_ghost ↦ - ∗ used_up l γ_h)%I.

  Definition state_inv P Q (p : proph_id) n l l_ghost H γ_h γ_n γ_t : iProp Σ :=
    (∃ vs, proph p vs ∗
      ((not_done_state H l γ_h ∗
        ( pending_state P n vs l_ghost γ_h γ_n
        ∨ accepted_state Q vs l l_ghost γ_h ))
      ∨ done_state Q l l_ghost γ_t γ_h))%I.

  Definition pau P Q γs :=
    (▷ P -∗ ◇ AU << ∀ (b : bool) (n : Z), counter_content γs (b, n) >> @ ⊤∖↑N, ∅
                 << counter_content γs (b, (if b then n + 1 else n)), COMM Q >>)%I.

  Definition counter_inv γ_h γ_b γ_n f c :=
    (∃ (b : bool) (l : loc) (H : list loc) (q : Qp) (v : val),
       f ↦ #b ∗ c ↦ #l ∗ l ↦{q} v ∗
       own γ_h (full_history_auth H) ∗
       own γ_h (half_history_frag H) ∗
       ([∗ list] l ∈ H, ∃ q, l ↦{q} -) ∗
       ⌜Some l = head H ∧ NoDup H⌝ ∗
       own γ_b (● Excl' b) ∗
       ((∃ (n : Z), ⌜v = InjLV #n⌝ ∗ own γ_h (half_history_frag H) ∗ own γ_n (● Excl' n)) ∨
        (∃ (n : Z) (p : proph_id), ⌜v = InjRV(#n,#p)⌝ ∗
         ∃ P Q l_ghost γ_t, inv stateN (state_inv P Q p n l l_ghost H γ_h γ_n γ_t) ∗
                    □ pau P Q (γ_h, γ_b, γ_n))))%I.

  Definition is_counter (γs : gname * gname * gname) (ctr : val) :=
    (∃ (γ_h γ_b γ_n : gname) (f c : loc),
        ⌜γs = (γ_h, γ_b, γ_n) ∧ ctr = (#f, #c)%V⌝ ∗
        inv counterN (counter_inv γ_h γ_b γ_n f c))%I.

  Global Instance is_counter_persistent γs ctr : Persistent (is_counter γs ctr) := _.

  Global Instance counter_content_timeless γs ctr : Timeless (counter_content γs ctr) := _.

  Global Instance abstract_state_inhabited: Inhabited abstract_state := populate (injl 0).


  (** A few more helper lemmas that will come up later *)

  Lemma mapsto_valid_3 l v1 v2 q :
    l ↦ v1 -∗ l ↦{q} v2 -∗ ⌜False⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (mapsto_valid_2 with "Hl1 Hl2") as %Hv.
    apply (iffLR (frac_valid' _)) in Hv. by apply Qp_not_plus_q_ge_1 in Hv.
  Qed.

  Instance in_dec (l : loc) H: Decision (In l H).
  Proof.
    induction H as [|a H IH].
    - right. naive_solver.
    - destruct (decide (l = a)).
      + left. naive_solver.
      + destruct IH; [ left | right]; naive_solver.
  Qed.

  Lemma nodup_fresh_loc l v H:
    NoDup H → l ↦ v -∗ ([∗ list] l ∈ H, ∃ q, l ↦{q} -) -∗ ⌜NoDup (l :: H)⌝.
  Proof.
    intros Hd. iIntros "Hl Hls".
    destruct (decide (In l H)) as [(x1 & x2 & ->)%in_split | Hn%NoDup_cons]; last done.
    - destruct x1 as [|x1 x1s];
        [ rewrite app_nil_l in Hd; rewrite app_nil_l; iDestruct "Hls" as "[Hl' _]" |
          iDestruct "Hls" as "[_ [Hl' _]]" ];
        iDestruct "Hl'" as (q v') "Hl'";
        by iDestruct (mapsto_valid_3 with "Hl Hl'") as %?.
    - by iPureIntro.
  Qed.


  (** ** Proof of [complete] *)

  (** The part of [complete] for the succeeding thread that moves from [pending] to [accepted] state *)

  Lemma complete_succeeding_thread_pending γ_h γ_b γ_n γ_t f_l c_l P Q p (m n : Z) l l_ghost l_new H Φ :
    Some l = head H →
    inv counterN (counter_inv γ_h γ_b γ_n f_l c_l) -∗
    inv stateN (state_inv P Q p m l l_ghost H γ_h γ_n γ_t) -∗
    pau P Q (γ_h, γ_b, γ_n) -∗
    l_ghost ↦{1 / 2} #() -∗
    ((own_token γ_t ={⊤}=∗ ▷ Q) -∗ Φ #()) -∗
    own γ_n (● Excl' n) -∗
    l_new ↦ InjLV #n -∗
    WP Resolve (CAS #c_l #l #l_new) #p #l_ghost ;; #() {{ v, Φ v }}.
  Proof.
    iIntros (Heq) "#InvC #InvS PAU Hl_ghost HQ Hn● Hl_new". wp_bind (Resolve _ _ _)%E.
    iInv counterN as (b' l' H' q v) "[>Hf [>Hc [>Hl' [>H● [>H◯ [>HlH [>Heq [Hb● Hrest]]]]]]]]".
    iDestruct "Heq" as %[Heq'' Hd']. simpl.
    iDestruct ((nodup_fresh_loc _ _ _ Hd') with "Hl_new HlH") as %Hd''.
    (* It must be that l' = l because we are in the succeeding thread. *)
    destruct (decide (l' = l)) as [->|HNeq]; last first. {
      iInv stateN as (vs') "[>Hp' [[>[Hh◯ _] State] | Done]]".
      - iDestruct "State" as "[Pending | Accepted]".
        + iDestruct "Pending" as "[_ >[_ Hn●']]".
          iCombine "Hn●'" "Hn●" as "Contra".
          iDestruct (own_valid with "Contra") as %Contra. by inversion Contra.
        + iDestruct (sync_histories with "Hh◯ H◯") as %->.
          rewrite <- Heq'' in Heq. by inversion Heq.
      - iDestruct "Done" as "[_ >[Hlghost _]]".
        wp_apply (wp_resolve with "Hp'"); first done. wp_cas_fail.
        iDestruct "Hlghost" as (?) "Hlghost".
        by iDestruct (mapsto_valid_2 with "Hlghost Hl_ghost") as %?.
    }
    (* To apply the CAS, we need the prophecy variable, so we open the state invariant. *)
    iInv stateN as (vs') "[>Hp' [[>[Hh◯ Heq'] State] | Done]]".
      - iDestruct "State" as "[Pending | Accepted]".
        + (* Pending: contradiction. *)
          iDestruct "Pending" as "[_ >[_ Hn●']]".
          iCombine "Hn●" "Hn●'" as "Contra".
          iDestruct (own_valid with "Contra") as %Contra. by inversion Contra.
        + (* We perform the CAS. *)
          iDestruct (sync_histories with "H◯ Hh◯") as %->.
          wp_apply (wp_resolve with "Hp'"); first done; wp_cas_suc.
          destruct (val_to_some_loc vs') eqn:Hvtsl; last first. {
            (* Wrong prophecy: contradiction. *)
            iIntros (vs ->). inversion Hvtsl.
          }
          (* Update to Done. *)
          iDestruct "Accepted" as "[Hl_ghost_inv H]".
          rewrite Hvtsl. iDestruct "H" as "[HEq Q]".
          (* The first element of H is l. *)
          destruct H as [|l' H]; inversion Heq; subst l'.
          (* And we have l ≠ l_new. *)
          destruct (decide (l = l_new)) as [->|HNeq]. {
            iDestruct "HlH" as "[Hl HlH]". iDestruct "Hl" as (q' v') "Hl".
            by iDestruct (mapsto_valid_3 with "Hl_new Hl") as %Contra.
          }
          (* Update histories. *)
          iDestruct (update_history _ _ l_new with "H● H◯ Hh◯") as ">[Hh● [H◯ H◯']]".
          iIntros (pv' ->) "Hp". iModIntro.
          (* Extract snapshot to prove used_up. *)
          iDestruct (extract_snapshot with "H◯'") as "#Hs".
          iSplitL "Hl_ghost_inv Hl_ghost Q Hp".
          (* Update state to Done. *)
          { iNext. iExists _. iSplitL "Hp"; first done. repeat iRight.
            iDestruct "Hl_ghost_inv" as (v'') "Hl_ghost''".
            iDestruct (mapsto_agree with "Hl_ghost Hl_ghost''") as %<-.
            iCombine "Hl_ghost" "Hl_ghost''" as "Hl_ghost'".
            iSplitL "Q"; first by iFrame. iSplitL "Hl_ghost'"; first by eauto.
            iExists (l_new :: l :: H). iSplit; first done. iPureIntro.
            split; first by apply in_cons, in_eq. by intros [=->]. }
          iModIntro. iSplitR "HQ".
          { iNext. iExists _, _, _, _, _. iSplitL "Hf"; first done.
            iSplitL "Hc"; first done. iDestruct "Hl_new" as "[$ Hl_new]".
            iSplitL "Hh●"; first done. iSplitL "H◯'"; first done.
            iSplitL "HlH Hl_new". { iSplitL "Hl_new"; first by iExists _, _. iFrame. }
            iSplit; first done. iSplitL "Hb●"; first done. iLeft. iExists n. by iFrame. }
          iApply wp_fupd. wp_seq. iApply "HQ". iModIntro. iIntros "Ht".
          iInv stateN as (vs') "[>Hp' [[>[Hh◯ Heq'] _] | Done]]".
          * iInv counterN as (b5 l5 H5 q5 v5) "[>Hf [>Hc [>Hl [>H● [>H◯ _]]]]]".
            iDestruct (sync_histories with "H◯ Hh◯") as %->.
            by iDestruct (sync_snapshot with "H● Hs") as %?%suffix_cons_not.
          * iDestruct "Done" as "[QT [>Hlghost Usedup]]".
            iModIntro. iDestruct (later_intro with "Ht") as "Ht".
            iDestruct (later_or with "QT") as "[Q | T]"; last first.
            { iCombine "Ht" "T" as "Contra". iDestruct (own_valid with "Contra") as "#Contra'".
              iSplitL; try iModIntro; try iNext; iDestruct "Contra'" as %Contra;
              by inversion Contra. }
            iSplitR "Q"; last done. iNext. iExists _. iSplitL "Hp'"; first done.
            repeat iRight. iFrame.
      - (* Done: contradiction. *)
        iDestruct "Done" as "[QT [>Hlghost Usedup]]".
        iDestruct "Hlghost" as (v') "Hlghost".
        by iDestruct (mapsto_valid_2 with "Hl_ghost Hlghost") as %?.
  Qed.

  (** The part of [complete] for the failing thread *)

  Lemma complete_failing_thread γ_h γ_b γ_n γ_t f_l c_l l1 l H1 H P Q p m n l_ghost_inv l_ghost l_new Φ :
    Some l1 = head H1 →
    In l H1 →
    l_ghost_inv ≠ l_ghost →
    inv counterN (counter_inv γ_h γ_b γ_n f_l c_l) -∗
    inv stateN (state_inv P Q p m l l_ghost_inv H γ_h γ_n γ_t) -∗
    pau P Q (γ_h, γ_b, γ_n) -∗
    □ own γ_h (hist_snapshot H1) -∗
    ((own_token γ_t ={⊤}=∗ ▷ Q) -∗ Φ #()) -∗
    l_new ↦ InjLV #n -∗
    WP Resolve (CAS #c_l #l #l_new) #p #l_ghost ;; #() {{ v, Φ v }}.
  Proof.
    iIntros (Heq Hin Hnl) "#InvC #InvS PAU #Hs1 HQ Hl_new". wp_bind (Resolve _ _ _)%E.
    iInv counterN as (b l' H' q v) "[>Hf [>Hc [>Hl [>H● [>H◯ [HlH [>Heq [Hb● Hrest]]]]]]]]".
    iDestruct (extract_snapshot with "H◯") as "#Hs2".
    iDestruct (sync_snapshot with "H● Hs1") as %H12.
    (* It must be that l' = l because we are in the succeeding thread. *)
    destruct (decide (l' = l)) as [->|Hn]. {
      iInv stateN as (vs') "[>Hp' [[>[Hh◯ _] State] | Done]]".
      - wp_apply (wp_resolve with "Hp'"); first done; wp_cas_suc. iIntros (vs ->).
        iDestruct "State" as "[Pending | Accepted]".
        + iDestruct "Pending" as "[_ [Hvs _]]". iDestruct "Hvs" as %Hvs. by inversion Hvs.
        + iDestruct "Accepted" as "[_ [Hvs _]]". iDestruct "Hvs" as %Hvs. by inversion Hvs.
      - iDestruct "Done" as "[QT [>Hlghost Usedup]]".
        iDestruct "Usedup" as (H'') "[Hs >Usedup]".
        iDestruct "Usedup" as %[Hin' Hn].
        iDestruct "Heq" as %[Heq' Hd'].
        iMod (intuitionistically_elim with "Hs") as "Hs".
        iDestruct (sync_snapshot with "H● Hs") as %Hs'.
        destruct Hs' as [xs ->]. destruct (in_split _ _ Hin) as (x & y & ->).
        destruct xs as [|z zs]; first done.
        simpl in *. inversion Heq'; subst. destruct (in_split _ _ Hin') as (x1 & x2 & ->).
        rewrite app_comm_cons in Hd'. rewrite app_assoc in Hd'.
        apply (NoDup_remove _ _ _) in Hd' as [_ Contra].
        rewrite <- app_comm_cons in Contra. simpl in *. exfalso. eauto.
    }
    (* The CAS fails. *)
    iInv stateN as (vs') "[>Hp' State]".
    wp_apply (wp_resolve with "Hp'"); first done. wp_cas_fail.
    iDestruct (extract_snapshot with "H◯") as "#Hs".
    iIntros (vs ->) "Hp". iModIntro. iDestruct "Heq" as %[Heq' Hd'].
    iSplitL "State Hp". { iNext. iExists vs. iFrame. } iModIntro.
    iSplitL "Hf Hc Hl H● H◯ HlH Hb● Hrest". { iNext. iExists _, _, _, _. eauto with iFrame. }
    wp_seq. iApply "HQ". iIntros "Ht".
    iInv counterN as (b3 l3 H3 q3 v3) "[>Hf [>Hc [>Hl [>H● [>H◯ [HlH [>Heq [Hb● Hrest]]]]]]]]".
    iDestruct "Heq" as %[Heq'' Hd''].
    iInv stateN as (vs') "[>Hp' [[>[Hh◯ Heq'] _] | Done]]".
    - iDestruct (sync_histories with "H◯ Hh◯") as %->.
      iDestruct (sync_snapshot with "H● Hs") as %Hs.
      iDestruct "Heq'" as %Heq'''. rewrite <- Heq'' in Heq'''.
      inversion Heq'''. subst. exfalso.
      by eapply (nodup_suffix_contradiction _ _ _ _ _ _ Heq Heq' Heq'').
    - iDestruct "Done" as "[[Q | >T] Hrest']"; iModIntro.
      + iSplitL "Ht Hp' Hrest'".
        { iNext. iExists _. iSplitL "Hp'"; first done. repeat iRight. iFrame. }
        iModIntro. iSplitR "Q"; last done. iNext. iExists _, _, _, _. eauto with iFrame.
      + iCombine "T" "Ht" as "Contra".
        iDestruct (own_valid with "Contra") as %Contra. by inversion Contra.
  Qed.

  (** ** Proof of [complete] *)

  Lemma complete_spec (c f l : loc) H (n : Z) (p : proph_id) γs γ_t l_ghost_inv P Q :
    is_counter γs (#f, #c) -∗
    inv stateN (state_inv P Q p n l l_ghost_inv H γs.1.1 γs.2 γ_t) -∗
    □ pau P Q γs -∗
    {{{ True }}}
       complete #c #f #l #n #p
    {{{ RET #(); own_token γ_t ={⊤}=∗ ▷Q }}}.
  Proof.
    iIntros "#InvC #InvS #PAU". destruct γs as [[γ_h γ_b] γ_n].
    iDestruct "InvC" as (??? f_l c_l [[=<-<-<-][=->->]]) "#InvC".
    iModIntro. iIntros (Φ) "_ HQ". wp_lam. wp_pures.
    wp_alloc l_ghost as "[Hl_ghost' Hl_ghost'2]". wp_bind (! _)%E. simpl.
    (* open outer invariant to read `f` *)
    iInv counterN as (b1 l1 H1 q1 v1) "[>Hf [>Hc [>Hl [>H● [>H◯ [Hlh1 [>Heq [Hb● Hrest]]]]]]]]".
    iDestruct "Heq" as %[Heq Hd]. wp_load.
    (* two different proofs depending on whether we are succeeding thread *)
    destruct (decide (l_ghost_inv = l_ghost)) as [-> | Hnl].
    - (* we are the succeeding thread *)
      (* we need to move from pending to accepted. *)
      iInv stateN as (vs') "[>Hp' [[>[Hh◯ Heq] [Pending | Accepted]] | Done]]".
      + (* Pending: update to accepted *)
        iDestruct "Pending" as "[P >[Hvs Hn●]]". iDestruct "Heq" as %Heq'.
        iDestruct ("PAU" with "P") as ">AU".
        (* open AU, sync flag and counter *)
        iMod "AU" as (b2 n2) "[CC [_ Hclose]]".
        iDestruct "CC" as "[Hb◯ Hn◯]". simpl.
        iDestruct (sync_flag_values with "Hb● Hb◯") as %->.
        iDestruct (sync_counter_values with "Hn● Hn◯") as %->.
        iDestruct (sync_histories with "H◯ Hh◯") as %->.
        rewrite <- Heq in Heq'. inversion_clear Heq'; subst.
        iMod (update_counter_value _ _ _ (if b2 then n2 + 1 else n2) with "Hn● Hn◯")
          as "[Hn● Hn◯]".
        iMod ("Hclose" with "[Hn◯ Hb◯]") as "Q"; first by iFrame.
        (* close state inv *)
        iModIntro. iSplitL "Q H◯ Hl_ghost' Hp' Hvs".
        { iNext. iExists _. iSplitL "Hp'"; first done. iLeft.
          iSplitL "H◯"; first by iFrame. iRight. iSplitL "Hl_ghost'"; first by iExists _.
          destruct (val_to_some_loc vs') eqn:Hvts; iFrame. }
        (* close outer inv *)
        iModIntro. iSplitR "Hl_ghost'2 HQ Hn●".
        { iNext. iExists _, _, _, _, _. iFrame. done. }
        destruct b2; wp_if; [ wp_op | .. ]; wp_alloc l_new as "Hl_new"; wp_pures;
          iApply ((complete_succeeding_thread_pending _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heq)
                    with "InvC InvS PAU Hl_ghost'2 HQ Hn● Hl_new").
      + (* Accepted: contradiction *)
        iDestruct "Accepted" as "[>Hl_ghost_inv _]".
        iDestruct "Hl_ghost_inv" as (v) "Hlghost".
        iCombine "Hl_ghost'" "Hl_ghost'2" as "Hl_ghost'".
        by iDestruct (mapsto_valid_2 with "Hlghost Hl_ghost'") as %?.
      + (* Done: contradiction *)
        iDestruct "Done" as "[QT >[Hlghost _]]".
        iDestruct "Hlghost" as (v) "Hlghost".
        iCombine "Hl_ghost'" "Hl_ghost'2" as "Hl_ghost'".
        by iDestruct (mapsto_valid_2 with "Hlghost Hl_ghost'") as %?.
    - (* we are the failing thread *)
      (* extract history and assert that it contains l *)
      iDestruct (extract_snapshot with "H◯") as "#Hs1".
      iAssert (|={⊤ ∖ ↑counterN}=> (⌜In l H1⌝ ∗ own γ_h (full_history_auth H1)))%I with "[H●]" as "Hin". {
        iInv stateN as (vs') "[>Hp' [[>[Hh◯ Heq'] State] | Done]]".
        - iDestruct (sync_snapshot with "H● Hh◯") as %Hs1. iDestruct "Heq'" as %Heq'.
          iModIntro. iSplitR "H●".
          { iNext. iExists _. iSplitL "Hp'"; first done. iLeft. iFrame. done. }
          iModIntro. iFrame. iPureIntro. by eapply suffix_in_head.
        - iDestruct "Done" as "[QT [>Hlghost Usedup]]".
          iDestruct "Usedup" as (H') "[Hs >Usedup]". iDestruct "Usedup" as %[Hin Hn].
          iMod (intuitionistically_elim with "Hs") as "Hs".
          iDestruct (sync_snapshot with "H● Hs") as %Hs'.
          iModIntro. iSplitR "H●".
          { iNext. iExists _. iSplitL "Hp'"; first done. repeat iRight. iFrame.
            iExists _. iSplit; last by iPureIntro. iDestruct "Hs" as "#Hs". iModIntro.
            iApply "Hs". }
          iModIntro. iSplit; last done.
          iPureIntro. by eapply suffix_in.
      }
      (* close invariant *)
      iMod "Hin" as (Hin) "H●". iModIntro.
      iSplitL "Hf Hc H● H◯ Hb● Hrest Hl Hlh1". { iNext. iExists _, _, _, _. eauto with iFrame. }
      (* two equal proofs depending on value of b1 *)
      destruct b1; wp_if; [ wp_op | ..]; wp_alloc Hl_new as "Hl_new"; wp_pures;
        iApply ((complete_failing_thread _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heq Hin Hnl)
                  with "InvC InvS PAU Hs1 HQ Hl_new").
  Qed.

  (** ** Proof of [cinc] *)

  Lemma cinc_spec c f γs :
    is_counter γs (f, c) -∗
    <<< ∀ (b : bool) (n : Z), counter_content γs (b, n) >>>
        cinc (f, c)%V @⊤∖↑N
    <<< counter_content γs (b, if b then n + 1 else n), RET #() >>>.
  Proof.
    iIntros "#InvC". iDestruct "InvC" as (γ_h γ_b γ_n f_l c_l) "[Heq InvC]".
    iDestruct "Heq" as %[-> [=->->]]. iIntros (Φ) "AU". iLöb as "IH".
    wp_lam. wp_proj. wp_let. wp_proj. wp_let. wp_bind (!_)%E.
    iInv counterN as (b' l' H' q v) "[>Hf [>Hc [>[Hl Hl'] [>H● [>H◯ [Hlh [>Heq [>Hb● Hv]]]]]]]]".
    wp_load. simpl. iDestruct "Hv" as "[Hv|Hv]".
    - iDestruct "Hv" as (n) "[% Hv]"; subst v.
      iModIntro. iSplitR "Hl' AU".
      { iModIntro. iExists _, _, _, (q/2)%Qp, (InjLV #n). eauto with iFrame. }
      wp_let. wp_load. wp_match. wp_apply wp_new_proph; first done.
      iIntros (l_ghost p') "Hp'".
      wp_let. wp_alloc ly as "Hly". wp_let. wp_bind (CAS _ _ _)%E.
      (* open outer invariant to read c_l *)
      iInv counterN as (b l'' H'' q' v') "[>Hf [>Hc [>Hl'2 [>H● [>H◯ [>Hlh [>Heq [Hb● Hrest]]]]]]]]".
      iDestruct "Heq" as %[Heq Hd].
      (* assert that ly is not in the history *)
      iDestruct (extract_snapshot with "H◯") as "#Hs".
      iDestruct ((nodup_fresh_loc _ _ _ Hd) with "Hly Hlh") as %Hd'.
      destruct (decide (l' = l'')) as [<- | Hn].
      + (* CAS succeeds *)
        wp_cas_suc.
        (* We need to update the half history with `ly`.
           For that we will need to get the second half of the history *)
        iDestruct "Hrest" as "[InjL | InjR]";
          iPoseProof (mapsto_agree with "Hl' Hl'2") as "#Heq"; last first.
        { (* injR: contradiction *)
          iDestruct "InjR" as (??) "[Heq' InjR_rest]".
          iDestruct "Heq'" as %->. iDestruct "Heq" as %Heq'. inversion Heq'. }
        (* injL: update history *)
        iDestruct "InjL" as (n'') "[Heq' [H◯' Hn●]]".
        iDestruct "Heq'" as %->. simpl. iDestruct "Heq" as %[=<-].
        iPoseProof ((update_history _ _ ly) with "H● H◯ H◯'") as ">[H● [H◯' H◯'']]".
        iDestruct (laterable with "AU") as (AU_later) "[AU #AU_back]".
        iDestruct (own_alloc token) as ">Ht"; first by apply auth_auth_valid.
        iDestruct "Ht" as (γ_t) "Token".
        destruct (val_to_some_loc l_ghost) eqn:H.
        * destruct (val_to_some_loc_some l_ghost l H) as [v1 [v2 [vs' [-> HCases]]]].
          destruct HCases as [[-> ->] | Hl].
          ++ iMod (inv_alloc stateN _ (state_inv AU_later _ _ _ _ _ _ _ _ γ_t)
               with "[AU H◯' Hp' Hn●]") as "#Hinv".
             { iNext. iExists _. iSplitL "Hp'"; first done. iLeft.
               iSplitL "H◯'"; first by iFrame. iLeft. by iFrame. }
             iModIntro. iDestruct "Hly" as "[Hly1 Hly2]". iSplitR "Hl' Token". {
               (* close invariant *)
               iNext. iExists _, ly, _, _, _. iFrame.
               iSplitL "Hly1"; first by eauto. iSplit; first by iPureIntro.
               iRight. iExists _, _. iSplit; first done. iExists _, _, _, _. iSplit; done.
             }
             wp_if.
             wp_apply complete_spec; [iExists _, _, _, _, _; eauto | done | done | done | ..].
             iIntros "Ht". iMod ("Ht" with "Token") as "Φ". wp_seq. by wp_lam.
          ++ iMod (inv_alloc stateN _ (state_inv AU_later _ _ _ ly l _ _ _ γ_t)
               with "[AU H◯' Hp' Hn●]") as "#Hinv".
             { iNext. iExists _. iSplitL "Hp'"; first done. iLeft.
               iSplitL "H◯'"; first by iFrame. iLeft. iFrame. by rewrite H. }
             iModIntro. iDestruct "Hly" as "[Hly1 Hly2]". iSplitR "Hl' Token". {
               (* close invariant *)
               iNext. iExists _, ly, _, _, _. iFrame.
               iSplitL "Hly1"; first by eauto. iSplit; first by iPureIntro.
               iRight. iExists _, _. iSplit; first done. iExists _, _, _, _. iSplit; done.
             }
             wp_if.
             wp_apply complete_spec; [iExists _, _, _, _, _; eauto | done | done | done | ..].
             iIntros "Ht". iMod ("Ht" with "Token") as "Φ". wp_seq. by wp_lam.
        * iMod (inv_alloc stateN _ (state_inv AU_later _ _ _ ly l' _ _ _ γ_t)
            with "[AU H◯' Hp' Hn●]") as "#Hinv".
          { iNext. iExists _. iSplitL "Hp'"; first done. iLeft.
            iSplitL "H◯'"; first by iFrame. iLeft. iFrame. by rewrite H. }
          iModIntro. iDestruct "Hly" as "[Hly1 Hly2]". iSplitR "Hl' Token". {
            (* close invariant *)
            iNext. iExists _, ly, _, _, _. iFrame.
            iSplitL "Hly1"; first by eauto. iSplit; first by iPureIntro.
            iRight. iExists _, _. iSplit; first done. iExists _, _, _, _. iSplit; done.
          }
          wp_if.
          wp_apply complete_spec; [iExists _, _, _, _, _; eauto | done | done | done | ..].
          iIntros "Ht". iMod ("Ht" with "Token") as "Φ". wp_seq. by wp_lam.
      + (* CAS fails: closing invariant and invoking IH *)
        wp_cas_fail.
        iModIntro. iSplitR "Hl' AU".
        iModIntro. iExists _, _, _, _. eauto 10 with iFrame.
        wp_if. by iApply "IH".
    - (* l' ↦ injR *)
      iModIntro. iDestruct "Hv" as (n p) "[% Hrest]"; subst v.
      (* extract state invariant *)
      iDestruct "Hrest" as (P Q l_ghost γ_t) "[#InvS #P_AU]".
      iSplitR "Hl' AU".
      (* close invariant *)
      { iModIntro. iExists _, _, _, _, _. iFrame. iRight. eauto 10 with iFrame. }
      wp_let. wp_load. wp_match. repeat wp_proj.
      wp_apply complete_spec; [iExists _, _, _, _, _; eauto | done | done | done | ..].
      iIntros "_". wp_seq. by iApply "IH".
  Qed.

  Lemma new_counter_spec :
    {{{ True }}}
        new_counter #()
    {{{ ctr γs, RET ctr ; is_counter γs ctr ∗ counter_content γs (true, 0) }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam. wp_apply wp_fupd.
    wp_alloc l_n as "Hl_n". wp_alloc l_c as "Hl_c". wp_let.
    wp_alloc l_f as "Hl_f". wp_let. wp_pair.
    iMod (own_alloc (full_history_auth [l_n] ⋅ full_history_frag [l_n])) as (γ_h) "[Hh● Hh◯]".
    { rewrite pair_op. apply pair_valid. split; by apply auth_both_valid. }
    iMod (own_alloc (● Excl' true  ⋅ ◯ Excl' true)) as (γ_b) "[Hb● Hb◯]".
    { by apply auth_both_valid. }
    iMod (own_alloc (● Excl' 0  ⋅ ◯ Excl' 0)) as (γ_n) "[Hn● Hn◯]".
    { by apply auth_both_valid. }
    iMod (inv_alloc counterN _ (counter_inv γ_h γ_b γ_n l_f l_c)
      with "[Hl_f Hl_c Hl_n Hh● Hh◯ Hb● Hn●]") as "#InvC".
    { iNext. iDestruct "Hh◯" as "[Hh◯1 Hh◯2]". iDestruct "Hl_n" as "[Hl_n1 Hl_n2]".
      iExists true, l_n, [l_n], _, (InjLV #0). iFrame.
      iSplitL "Hl_n1". { simpl. iSplitL; last done. by iExists _, _. }
      iSplitR. { iPureIntro. split; first done. apply NoDup_cons. apply in_nil. apply NoDup_nil. }
      iLeft. iExists 0. iSplitR; first done. iFrame. }
    iModIntro.
    iApply ("HΦ" $! (#l_f, #l_c)%V (γ_h, γ_b, γ_n)).
    iSplitR; last by iFrame. iExists γ_h, γ_b, γ_n, l_f, l_c. iSplit; done.
  Qed.

  Lemma set_flag_spec γs f c (new_b : bool) :
    is_counter γs (f, c) -∗
    <<< ∀ (b : bool) (n : Z), counter_content γs (b, n) >>>
        set_flag (f, c)%V #new_b @⊤∖↑N
    <<< counter_content γs (new_b, n), RET #() >>>.
  Proof.
    iIntros "#InvC" (Φ) "AU". wp_lam. wp_let. wp_proj.
    iDestruct "InvC" as (γ_h γ_b γ_n l_f l_c) "[[HEq1 HEq2] InvC]".
    iDestruct "HEq1" as %->. iDestruct "HEq2" as %HEq. inversion HEq; subst; clear HEq.
    iInv counterN as (b c H q v) "[>Hl_f [>Hl_c [>Hl [>H● [>H◯ [>HlH [>HEq [Hb● H]]]]]]]]".
    iMod "AU" as (b' n') "[[Hb◯ Hn◯] [_ Hclose]]"; simpl.
    wp_store.
    iDestruct (sync_flag_values with "Hb● Hb◯") as %HEq; subst b.
    iDestruct (update_flag_value with "Hb● Hb◯") as ">[Hb● Hb◯]".
    iMod ("Hclose" with "[Hn◯ Hb◯]") as "HΦ"; first by iFrame.
    iModIntro. iModIntro. iSplitR "HΦ"; last done.
    iNext. iExists new_b, c, H, q, v. iFrame.
  Qed.

  Lemma get_spec γs f c :
    is_counter γs (f, c) -∗
    <<< ∀ (b : bool) (n : Z), counter_content γs (b, n) >>>
        get (f, c)%V @⊤∖↑N
    <<< counter_content γs (b, n), RET #n >>>.
  Proof.
    iIntros "#InvC" (Φ) "AU". iLöb as "IH". wp_lam. repeat (wp_proj; wp_let). wp_bind (! _)%E.
    iDestruct "InvC" as (γ_h γ_b γ_n l_f l_c) "[[HEq1 HEq2] InvC]".
    iDestruct "HEq1" as %->. iDestruct "HEq2" as %HEq. inversion HEq; subst.
    iInv counterN as (b c H q v) "[>Hl_f [>Hl_c [>[Hc Hc'] [>H● [>H◯ [>HlH [>HEq [Hb● [H|H]]]]]]]]]".
    - wp_load. iDestruct "H" as (n) "[% [H◯2 Hn●]]". simpl in *; subst v.
      iMod "AU" as (au_b au_n) "[[Hb◯ Hn◯] [_ Hclose]]"; simpl.
      iDestruct (sync_counter_values with "Hn● Hn◯") as %->.
      iMod ("Hclose" with "[Hn◯ Hb◯]") as "HΦ"; first by iFrame.
      iModIntro. iSplitR "HΦ Hc'". {
        iNext. iExists b, c, H, (q/2)%Qp, (InjLV #au_n). iFrame.
        iLeft. iExists au_n. iFrame. done.
      }
      wp_let. wp_load. wp_match. iApply "HΦ".
    - wp_load. iDestruct "H" as (n p) "[% H]". simpl in *; subst v.
      iDestruct "H" as (P Q l_ghost γ_t) "[#InvS #PAU]".
      iModIntro. iSplitR "AU Hc'". {
        iNext. iExists b, c, H, (q/2)%Qp, (InjRV(#n,#p)). iFrame.
        iRight. iExists n, p. iSplit; first done. iExists P, Q, l_ghost, γ_t. eauto.
      }
      wp_let. wp_load. wp_match. repeat wp_proj. wp_bind (complete _ _ _ _ _)%E.
      wp_apply complete_spec; [ iExists _, _, _, _, _; eauto | done | done | done | .. ].
      iIntros "Ht". wp_seq. iApply "IH". iApply "AU".
  Qed.

End conditional_counter.
