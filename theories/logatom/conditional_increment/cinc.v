From iris.algebra Require Import excl auth agree frac list cmra csum.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris_examples.logatom.conditional_increment Require Import spec.
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

Definition flagUR     := authR $ optionUR $ exclR boolC.
Definition numUR      := authR $ optionUR $ exclR ZC.
Definition tokenUR    := exclR unitC.
Definition one_shotUR := csumR (exclR unitC) (agreeR unitC).

Class cincG Σ := ConditionalIncrementG {
                     cinc_flagG     :> inG Σ flagUR;
                     cinc_numG      :> inG Σ numUR;
                     cinc_tokenG    :> inG Σ tokenUR;
                     cinc_one_shotG :> inG Σ one_shotUR;
                   }.

Definition cincΣ : gFunctors :=
  #[GFunctor flagUR; GFunctor numUR; GFunctor tokenUR; GFunctor one_shotUR].

Instance subG_cincΣ {Σ} : subG cincΣ Σ → cincG Σ.
Proof. solve_inG. Qed.

Section conditional_counter.
  Context {Σ} `{!heapG Σ, !cincG Σ}.
  Context (N : namespace).

  Local Definition stateN   := N .@ "state".
  Local Definition counterN := N .@ "counter".

  (** Updating and synchronizing the counter and flag RAs *)

  Lemma sync_counter_values γ_n (n m : Z) :
    own γ_n (● Excl' n) -∗ own γ_n (◯ Excl' m) -∗ ⌜n = m⌝.
  Proof.
    iIntros "H● H◯". iCombine "H●" "H◯" as "H". iDestruct (own_valid with "H") as "H".
      by iDestruct "H" as %[H%Excl_included%leibniz_equiv _]%auth_both_valid.
  Qed.

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

  Definition counter_content (γs : gname * gname) (b : bool) (n : Z) :=
    (own γs.1 (◯ Excl' b) ∗ own γs.2 (◯ Excl' n))%I.


  (** Definition of the invariant *)

  Fixpoint val_to_some_loc (vs : list (val * val)) : option loc :=
    match vs with
    | (#true , LitV (LitLoc l)) :: _  => Some l
    | _                         :: vs => val_to_some_loc vs
    | _                               => None
    end.

  Inductive abstract_state : Set :=
  | injl : Z → abstract_state
  | injr : Z → proph_id → abstract_state.

  Definition state_to_val (s : abstract_state) : val :=
    match s with
    | injl n => InjLV #n
    | injr n p => InjRV (#n,#p)
    end.

  Global Instance state_to_val_inj : Inj (=) (=) state_to_val.
  Proof.
    intros [|] [|]; simpl; intros Hv; inversion_clear Hv; done.
  Qed.

  Definition own_token γ := (own γ (Excl ()))%I.

  Definition loc_token (l: loc) := (∃ γ, meta l N γ ∗ own_token γ)%I.

  Definition pending_state P (n : Z) (proph_winner : option loc) l_ghost_winner (γ_n : gname) :=
    (P ∗ ⌜match proph_winner with None => True | Some l => l = l_ghost_winner end⌝ ∗ own γ_n (● Excl' n))%I.

  (* After the prophecy said we are going to win the race, we commit and run the AU,
     switching from [pending] to [accepted]. *)
  Definition accepted_state Q (proph_winner : option loc) (l_ghost_winner : loc) :=
    (l_ghost_winner ↦{1/2} - ∗ match proph_winner with None => True | Some l => ⌜l = l_ghost_winner⌝ ∗ Q end)%I.

  (* The same thread then wins the CAS and moves from [accepted] to [done].
     Then, the [γ_t] token guards the transition to take out [Q].
     Remember that the thread winning the CAS might be just helping.  The token
     is owned by the thread whose request this is.
     In this state, [l_ghost_winner] serves as a token to make sure that
     only the CAS winner can transition to here, and [loc_token l] serves as a
     "location" token to ensure there is no ABA going on. *)
  Definition done_state Q (l l_ghost_winner : loc) (γ_t : gname) :=
    ((Q ∨ own_token γ_t) ∗ l_ghost_winner ↦ - ∗ loc_token l)%I.

  (* We always need the [proph] in here so that failing threads coming late can
     always resolve their stuff.
     Moreover, we need a way for anyone who has observed the [done] state to
     prove that we will always remain [done]; that's what the one-shot token [γ_s] is for. *)
  Definition state_inv P Q (p : proph_id) n (c_l l l_ghost_winner : loc) γ_n γ_t γ_s : iProp Σ :=
    (∃ vs, proph p vs ∗
      (own γ_s (Cinl $ Excl ()) ∗
       (c_l ↦{1/2} #l ∗ ( pending_state P n (val_to_some_loc vs) l_ghost_winner γ_n
        ∨ accepted_state Q (val_to_some_loc vs) l_ghost_winner ))
       ∨ own γ_s (Cinr $ to_agree ()) ∗ done_state Q l l_ghost_winner γ_t))%I.

  Definition pau P Q γs :=
    (▷ P -∗ ◇ AU << ∀ (b : bool) (n : Z), counter_content γs b n >> @ ⊤∖↑N, ∅
                 << counter_content γs b (if b then n + 1 else n), COMM Q >>)%I.

  Definition counter_inv γ_b γ_n f c :=
    (∃ (b : bool) (l : loc) (q : Qp) (s : abstract_state),
       f ↦ #b ∗ c ↦{1/2} #l ∗ l ↦{q} (state_to_val s) ∗
       own γ_b (● Excl' b) ∗
       loc_token l ∗ (* the "location" token for ABA protection; also see [done_state] *)
       match s with
        | injl n => c ↦{1/2} #l ∗ own γ_n (● Excl' n)
        | injr n p =>
           ∃ P Q l_ghost_winner γ_t γ_s,
             (* There are two pieces of per-[state]-protocol ghost state:
             - [γ_t] is a token owned by whoever created this protocol and used
               to get out the [Q] in the end.
             - [γ_s] reflects whether the protocol is [done] yet or not. *)
             inv stateN (state_inv P Q p n c l l_ghost_winner γ_n γ_t γ_s) ∗
             □ pau P Q (γ_b, γ_n)
       end)%I.

  Local Hint Extern 0 (environments.envs_entails _ (counter_inv _ _ _ _)) => unfold counter_inv.

  Definition is_counter (γs : gname * gname) (ctr : val) :=
    (∃ (γ_b γ_n : gname) (f c : loc),
        ⌜γs = (γ_b, γ_n) ∧ ctr = (#f, #c)%V⌝ ∗
        inv counterN (counter_inv γ_b γ_n f c))%I.

  Global Instance is_counter_persistent γs ctr : Persistent (is_counter γs ctr) := _.

  Global Instance counter_content_timeless γs b n : Timeless (counter_content γs b n) := _.

  Global Instance abstract_state_inhabited: Inhabited abstract_state := populate (injl 0).

  Lemma counter_content_exclusive γs f1 c1 f2 c2 :
    counter_content γs f1 c1 -∗ counter_content γs f2 c2 -∗ False.
  Proof.
    iIntros "[Hb1 _] [Hb2 _]". iDestruct (own_valid_2 with "Hb1 Hb2") as %?.
    done.
  Qed.

  (** A few more helper lemmas that will come up later *)

  Lemma mapsto_valid_3 l v1 v2 q :
    l ↦ v1 -∗ l ↦{q} v2 -∗ ⌜False⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (mapsto_valid_2 with "Hl1 Hl2") as %Hv.
    apply (iffLR (frac_valid' _)) in Hv. by apply Qp_not_plus_q_ge_1 in Hv.
  Qed.

  Lemma loc_token_exclusive l :
    loc_token l -∗ loc_token l -∗ False.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct "Hl1" as (γ1) "[Hm1 Ht1]".
    iDestruct "Hl2" as (γ2) "[Hm2 Ht2]".
    iDestruct (meta_agree with "Hm1 Hm2") as %->.
    iDestruct (own_valid_2 with "Ht1 Ht2") as %Hcontra.
    by inversion Hcontra.
  Qed.

  Lemma loc_token_alloc v :
    {{{ True }}} ref v {{{ l, RET #l; l ↦ v ∗ loc_token l }}}.
  Proof.
    iIntros (Φ) "HT HΦ". iApply wp_fupd.
    wp_apply (wp_alloc with "HT"). iIntros (l_new) "[Hl_new Hm_new]".
    iMod (own_alloc (Excl ())) as (γ_l) "Htok"; first done.
    iMod ((meta_set _ _ γ_l N) with "Hm_new") as "Hm"; first done.
    iApply "HΦ". iFrame "Hl_new". iExists _. by iFrame.
  Qed.

  (** Once a [state] protocol is [done] (as reflected by the [γ_s] token here),
      we can at any later point in time extract the [Q]. *)
  Lemma state_done_extract_Q P Q p m c_l l l_ghost γ_n γ_t γ_s :
    inv stateN (state_inv P Q p m c_l l l_ghost γ_n γ_t γ_s) -∗
    own γ_s (Cinr (to_agree ())) -∗
    □(own_token γ_t ={⊤}=∗ ▷ Q).
  Proof.
    iIntros "#Hinv #Hs !# Ht".
    iInv stateN as (vs) "(Hp & [NotDone | Done])".
    * (* Moved back to NotDone: contradiction. *)
      iDestruct "NotDone" as "(>Hs' & _ & _)".
      iDestruct (own_valid_2 with "Hs Hs'") as %?. contradiction.
    * iDestruct "Done" as "(_ & QT & Hghost)".
      iDestruct "QT" as "[Q | >T]"; last first.
      { iDestruct (own_valid_2 with "Ht T") as %Contra.
          by inversion Contra. }
      iSplitR "Q"; last done. iIntros "!> !>". unfold state_inv.
      iExists _. iFrame "Hp". iRight.
      unfold done_state. iFrame "#∗".
  Qed.

  (** ** Proof of [complete] *)

  (** The part of [complete] for the succeeding thread that moves from [accepted] to [done] state *)
  Lemma complete_succeeding_thread_pending (γ_b γ_n γ_t γ_s : gname) f_l c_l P Q p
        (m n : Z) (l l_ghost l_new : loc) Φ :
    inv counterN (counter_inv γ_b γ_n f_l c_l) -∗
    inv stateN (state_inv P Q p m c_l l l_ghost γ_n γ_t γ_s) -∗
    pau P Q (γ_b, γ_n) -∗
    l_ghost ↦{1 / 2} #() -∗
    (□(own_token γ_t ={⊤}=∗ ▷ Q) -∗ Φ #()) -∗
    own γ_n (● Excl' n) -∗
    l_new ↦ InjLV #n -∗
    loc_token l_new -∗
    WP Resolve (CAS #c_l #l #l_new) #p #l_ghost ;; #() {{ v, Φ v }}.
  Proof.
    iIntros "#InvC #InvS PAU Hl_ghost HQ Hn● Hlntok Hl_new". wp_bind (Resolve _ _ _)%E.
    iInv counterN as (b' l' q s) "(>Hf & >Hc & >Hl' & Hb● & Hltok & Hrest)".
    iInv stateN as (vs) "(>Hp & [NotDone | Done])"; last first.
    { (* We cannot be [done] yet, as we own the "ghost location" that serves
         as token for that transition. *)
      iDestruct "Done" as "(_ & _ & Hlghost & _)".
      iDestruct "Hlghost" as (v') ">Hlghost".
        by iDestruct (mapsto_valid_2 with "Hl_ghost Hlghost") as %?.
    }
    iDestruct "NotDone" as "(>Hs & >Hc' & [Pending | Accepted])".
    { (* We also cannot be [Pending] any more we have [own γ_n] showing that this
       transition has happened   *)
       iDestruct "Pending" as "[_ >[_ Hn●']]".
       iCombine "Hn●" "Hn●'" as "Contra".
       iDestruct (own_valid with "Contra") as %Contra. by inversion Contra.
    }
    (* So, we are [Accepted]. Now we can show that l = l', because
       while a [state] protocol is not [done], it owns enough of
       the [counter] protocol to ensure that does not move anywhere else. *)
    iDestruct (mapsto_agree with "Hc Hc'") as %[= ->].
    (* We perform the CAS. *)
    iCombine "Hc Hc'" as "Hc".
    wp_apply (wp_resolve with "Hp"); first done; wp_cas_suc.
    iIntros (vs' ->) "Hp'". simpl.
    (* Update to Done. *)
    iDestruct "Accepted" as "[Hl_ghost_inv [HEq Q]]".
    iMod (own_update with "Hs") as "Hs".
    { apply (cmra_update_exclusive (Cinr (to_agree ()))). done. }
    iDestruct "Hs" as "#Hs'". iModIntro.
    iSplitL "Hl_ghost_inv Hl_ghost Q Hltok Hp'".
    (* Update state to Done. *)
    { iNext. iExists _. iFrame "Hp'". iRight. unfold done_state.
      iFrame "#∗". iExists _. done. }
    iModIntro. iSplitR "HQ".
    { iNext. iDestruct "Hc" as "[Hc1 Hc2]".
      iExists _, l_new, _, (injl n). iFrame. }
    iApply wp_fupd. wp_seq. iApply "HQ".
    iApply state_done_extract_Q; done.
  Qed.

  (** The part of [complete] for the failing thread *)
  Lemma complete_failing_thread γ_b γ_n γ_t γ_s f_l c_l l P Q p m n l_ghost_inv l_ghost l_new Φ :
    l_ghost_inv ≠ l_ghost →
    inv counterN (counter_inv γ_b γ_n f_l c_l) -∗
    inv stateN (state_inv P Q p m c_l l l_ghost_inv γ_n γ_t γ_s) -∗
    pau P Q (γ_b, γ_n) -∗
    (□(own_token γ_t ={⊤}=∗ ▷ Q) -∗ Φ #()) -∗
    l_new ↦ InjLV #n -∗
    WP Resolve (CAS #c_l #l #l_new) #p #l_ghost ;; #() {{ v, Φ v }}.
  Proof.
    iIntros (Hnl) "#InvC #InvS PAU HQ Hl_new". wp_bind (Resolve _ _ _)%E.
    iInv counterN as (b' l' q s) "(>Hf & >Hc & >Hl' & >Hb● & >Hltok & Hrest)".
    iInv stateN as (vs) "(>Hp & [NotDone | [#Hs Done]])".
    { (* If the [state] protocol is not done yet, we can show that it
         is the active protocol still (l = l').  But then the CAS would
         succeed, and our prophecy would have told us that.
         So here we can prove that the prophecy was wrong. *)
        iDestruct "NotDone" as "(_ & >Hc' & State)".
        iDestruct (mapsto_agree with "Hc Hc'") as %[=->].
        iCombine "Hc Hc'" as "Hc".
        wp_apply (wp_resolve with "Hp"); first done; wp_cas_suc.
        iIntros (vs' ->). iDestruct "State" as "[Pending | Accepted]".
        + iDestruct "Pending" as "[_ [Hvs _]]". iDestruct "Hvs" as %Hvs. by inversion Hvs.
        + iDestruct "Accepted" as "[_ [Hvs _]]". iDestruct "Hvs" as %Hvs. by inversion Hvs. }
    (* So, we know our protocol is [Done]. *)
    (* It must be that l' ≠ l because we are in the failing thread. *)
    destruct (decide (l' = l)) as [->|Hn]. {
      (* The [state] protocol is [done] while still being the active protocol
         of the [counter]?  Impossible, we got the location token for that! *)
      iDestruct "Done" as "(_ & _ & >Hltok')".
      iDestruct (loc_token_exclusive with "Hltok Hltok'") as "[]".
    }
    (* The CAS fails. *)
    wp_apply (wp_resolve with "Hp"); first done. wp_cas_fail.
    iIntros (vs' ->) "Hp". iModIntro.
    iSplitL "Done Hp". { iNext. iExists _. iFrame "#∗". } iModIntro.
    iSplitL "Hf Hc Hb● Hrest Hl' Hltok". { eauto 10 with iFrame. }
    wp_seq. iApply "HQ".
    iApply state_done_extract_Q; done.
  Qed.

  (** ** Proof of [complete] *)
  (* The postcondition basically says that *if* you were the thread to own
     this request, then you get [Q].  But we also try to complete other
     thread's requests, which is why we cannot ask for the token
     as a precondition. *)
  Lemma complete_spec (c f l : loc) (n : Z) (p : proph_id) γ_b γ_n γ_t γ_s l_ghost_inv P Q :
    inv counterN (counter_inv γ_b γ_n f c) -∗
    inv stateN (state_inv P Q p n c l l_ghost_inv γ_n γ_t γ_s) -∗
    □ pau P Q (γ_b, γ_n) -∗
    {{{ True }}}
       complete #c #f #l #n #p
    {{{ RET #(); □ (own_token γ_t ={⊤}=∗ ▷Q) }}}.
  Proof.
    iIntros "#InvC #InvS #PAU".
    iModIntro. iIntros (Φ) "_ HQ". wp_lam. wp_pures.
    wp_alloc l_ghost as "[Hl_ghost' Hl_ghost'2]". wp_bind (! _)%E. simpl.
    (* open outer invariant to read `f` *)
    iInv counterN as (b' l' q s) "(>Hf & >Hc & >Hl' & >Hb● & >Hltok & Hrest)".
    wp_load.
    (* two different proofs depending on whether we are succeeding thread *)
    destruct (decide (l_ghost_inv = l_ghost)) as [-> | Hnl].
    - (* we are the succeeding thread *)
      (* we need to move from [pending] to [accepted]. *)
      iInv stateN as (vs) "(>Hp & [(>Hs & >Hc' & [Pending | Accepted]) | [#Hs Done]])".
      + (* Pending: update to accepted *)
        iDestruct "Pending" as "[P >[Hvs Hn●]]".
        iDestruct ("PAU" with "P") as ">AU".
        (* open and *COMMIT* AU, sync flag and counter *)
        iMod "AU" as (b2 n2) "[CC [_ Hclose]]".
        iDestruct "CC" as "[Hb◯ Hn◯]". simpl.
        iDestruct (sync_flag_values with "Hb● Hb◯") as %->.
        iDestruct (sync_counter_values with "Hn● Hn◯") as %->.
        iMod (update_counter_value _ _ _ (if b2 then n2 + 1 else n2) with "Hn● Hn◯")
          as "[Hn● Hn◯]".
        iMod ("Hclose" with "[Hn◯ Hb◯]") as "Q"; first by iFrame.
        (* close state inv *)
        iModIntro. iSplitL "Q Hl_ghost' Hp Hvs Hs Hc'".
        { iNext. iExists _. iFrame "Hp". iLeft. iFrame.
          iRight. iSplitL "Hl_ghost'"; first by iExists _.
          destruct (val_to_some_loc vs) eqn:Hvts; iFrame. }
        (* close outer inv *)
        iModIntro. iSplitR "Hl_ghost'2 HQ Hn●".
        { eauto 12 with iFrame. }
        destruct b2; wp_if; [ wp_op | .. ];
        wp_apply (loc_token_alloc with "[//]"); iIntros (l_new) "[Hl_new Hm_new]";
        wp_pures;
          iApply (complete_succeeding_thread_pending
                    with "InvC InvS PAU Hl_ghost'2 HQ Hn● Hl_new Hm_new").
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
      (* close invariant *)
      iModIntro.
      iSplitL "Hf Hc Hrest Hl' Hb● Hltok". { eauto 10 with iFrame. }
      (* two equal proofs depending on value of b1 *)
      destruct b'; wp_if; [ wp_op | ..]; wp_alloc Hl_new as "Hl_new"; wp_pures;
        iApply (complete_failing_thread
                  with "InvC InvS PAU HQ Hl_new"); done.
  Qed.

  (** ** Proof of [cinc] *)

  Lemma cinc_spec γs v :
    is_counter γs v -∗
    <<< ∀ (b : bool) (n : Z), counter_content γs b n >>>
        cinc v @⊤∖↑N
    <<< counter_content γs b (if b then n + 1 else n), RET #() >>>.
  Proof.
    iIntros "#InvC". iDestruct "InvC" as (γ_b γ_n f_l c_l) "[Heq InvC]".
    iDestruct "Heq" as %[-> ->]. iIntros (Φ) "AU". iLöb as "IH".
    wp_lam. wp_proj. wp_let. wp_proj. wp_let. wp_bind (!_)%E.
    iInv counterN as (b' l' q s) "(>Hf & >Hc & >[Hl Hl'] & >Hb● & >Hltok & Hrest)".
    wp_load. destruct s as [n|n p].
    - iDestruct "Hrest" as "(Hc' & Hv)".
      iModIntro. iSplitR "AU Hl".
      { iModIntro. iExists _, _, (q/2)%Qp, (injl n). iFrame. }
      wp_let. wp_load. wp_match. wp_apply wp_new_proph; first done.
      iIntros (l_ghost p') "Hp'".
      wp_let. wp_apply (loc_token_alloc with "[//]"); iIntros (ly) "[Hly Hmy]".
      wp_let. wp_bind (CAS _ _ _)%E.
      (* open outer invariant again to CAS c_l *)
      iInv counterN as (b2 l'' q2 s) "(>Hf & >Hc & >Hl' & >Hb● & >Hltok & Hrest)".
      destruct (decide (l' = l'')) as [<- | Hn].
      + (* CAS succeeds *)
        iDestruct (mapsto_agree with "Hl Hl'") as %<-%state_to_val_inj.
        iDestruct "Hrest" as ">[Hc' Hn●]". iCombine "Hc Hc'" as "Hc".
        wp_cas_suc. iClear "Hltok".
        (* Initialize new [state] protocol .*)
        iDestruct (laterable with "AU") as (AU_later) "[AU #AU_back]".
        iMod (own_alloc (Excl ())) as (γ_t) "Token"; first done.
        iMod (own_alloc (Cinl $ Excl ())) as (γ_s) "Hs"; first done.
        iDestruct "Hc" as "[Hc Hc']".
        set (winner := default ly (val_to_some_loc l_ghost)).
        iMod (inv_alloc stateN _ (state_inv AU_later _ _ _ _ _ winner _ _ _)
               with "[AU Hs Hp' Hc' Hn●]") as "#Hinv".
        { iNext. iExists _. iFrame "Hp'". iLeft. iFrame. iLeft.
          iFrame. destruct (val_to_some_loc l_ghost); simpl; done. }
        iModIntro. iDestruct "Hly" as "[Hly1 Hly2]". iSplitR "Hl' Token". {
          (* close invariant *)
          iNext. iExists _, _, _, (injr n p'). eauto 10 with iFrame.
        }
        wp_if. wp_apply complete_spec; [done..|].
        iIntros "Ht". iMod ("Ht" with "Token") as "Φ". wp_seq. by wp_lam.
      + (* CAS fails: closing invariant and invoking IH *)
        wp_cas_fail.
        iModIntro. iSplitR "AU".
        { iModIntro. iExists _, _, _, s. iFrame. }
        wp_if. by iApply "IH".
    - (* l' ↦ injR *)
      iModIntro.
      (* extract state invariant *)
      iDestruct "Hrest" as (P Q l_ghost γ_t γ_s) "[#InvS #P_AU]".
      iSplitR "Hl' AU".
      (* close invariant *)
      { iModIntro. iExists _, _, _, (injr n p). iFrame. eauto 10 with iFrame. }
      wp_let. wp_load. wp_match. wp_pures.
      wp_apply complete_spec; [done..|].
      iIntros "_". wp_seq. by iApply "IH".
  Qed.

  Lemma new_counter_spec :
    {{{ True }}}
        new_counter #()
    {{{ ctr γs, RET ctr ; is_counter γs ctr ∗ counter_content γs true 0 }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam. wp_apply wp_fupd.
    wp_apply (loc_token_alloc with "[//]"); iIntros (l_n) "[Hl_n Hltok]".
    wp_alloc l_c as "Hl_c". wp_let.
    wp_alloc l_f as "Hl_f". wp_let. wp_pair.
    iMod (own_alloc (● Excl' true  ⋅ ◯ Excl' true)) as (γ_b) "[Hb● Hb◯]".
    { by apply auth_both_valid. }
    iMod (own_alloc (● Excl' 0  ⋅ ◯ Excl' 0)) as (γ_n) "[Hn● Hn◯]".
    { by apply auth_both_valid. }
    iMod (inv_alloc counterN _ (counter_inv γ_b γ_n l_f l_c)
      with "[Hl_f Hl_c Hl_n Hltok Hb● Hn●]") as "#InvC".
    { iNext. iDestruct "Hl_c" as "[Hl_c1 Hl_c2]".
      iExists true, l_n, _, (injl 0). iFrame. }
    iModIntro.
    iApply ("HΦ" $! (#l_f, #l_c)%V (γ_b, γ_n)).
    iSplitR; last by iFrame. iExists γ_b, γ_n, l_f, l_c. iSplit; done.
  Qed.

  Lemma set_flag_spec γs v (new_b : bool) :
    is_counter γs v -∗
    <<< ∀ (b : bool) (n : Z), counter_content γs b n >>>
        set_flag v #new_b @⊤∖↑N
    <<< counter_content γs new_b n, RET #() >>>.
  Proof.
    iIntros "#InvC" (Φ) "AU". iDestruct "InvC" as (γ_b γ_n f_l c_l) "[Heq InvC]".
    iDestruct "Heq" as %[-> ->]. wp_lam. wp_let. wp_proj.
    iInv counterN as (b c q s) "(>Hf & >Hc & >[Hl Hl'] & >Hb● & >Hltok & Hrest)".
    iMod "AU" as (b' n') "[[Hb◯ Hn◯] [_ Hclose]]"; simpl.
    wp_store.
    iDestruct (sync_flag_values with "Hb● Hb◯") as %HEq; subst b.
    iDestruct (update_flag_value with "Hb● Hb◯") as ">[Hb● Hb◯]".
    iMod ("Hclose" with "[Hn◯ Hb◯]") as "HΦ"; first by iFrame.
    iModIntro. iModIntro. iSplitR "HΦ"; last done.
    iNext. iExists new_b, c, q, _. iFrame. done.
  Qed.

  Lemma get_spec γs v :
    is_counter γs v -∗
    <<< ∀ (b : bool) (n : Z), counter_content γs b n >>>
        get v @⊤∖↑N
    <<< counter_content γs b n, RET #n >>>.
  Proof.
    iIntros "#InvC" (Φ) "AU". iDestruct "InvC" as (γ_b γ_n f_l c_l) "[Heq InvC]".
    iDestruct "Heq" as %[-> ->]. iLöb as "IH". wp_lam. repeat (wp_proj; wp_let). wp_bind (! _)%E.
    iInv counterN as (b c q s) "(>Hf & >Hc & >[Hl Hl'] & >Hb● & >Hltok & Hrest)".
    wp_load.
    destruct s as [n|n p].
    - iMod "AU" as (au_b au_n) "[[Hb◯ Hn◯] [_ Hclose]]"; simpl.
      iDestruct "Hrest" as "[Hc' Hn●]".
      iDestruct (sync_counter_values with "Hn● Hn◯") as %->.
      iMod ("Hclose" with "[Hn◯ Hb◯]") as "HΦ"; first by iFrame.
      iModIntro. iSplitR "HΦ Hl'". {
        iNext. iExists b, c, (q/2)%Qp, (injl au_n). iFrame.
      }
      wp_let. wp_load. wp_match. iApply "HΦ".
    - iDestruct "Hrest" as (P Q l_ghost γ_t γ_s) "[#InvS #PAU]".
      iModIntro. iSplitR "AU Hl'". {
        iNext. iExists b, c, (q/2)%Qp, (injr n p). eauto 10 with iFrame.
      }
      wp_let. wp_load. wp_match. repeat wp_proj. wp_bind (complete _ _ _ _ _)%E.
      wp_apply complete_spec; [done..|].
      iIntros "Ht". wp_seq. iApply "IH". iApply "AU".
  Qed.

End conditional_counter.

Definition atomic_cinc `{!heapG Σ, cincG Σ} :
  spec.atomic_cinc Σ :=
  {| spec.new_counter_spec := new_counter_spec;
     spec.cinc_spec := cinc_spec;
     spec.set_flag_spec := set_flag_spec;
     spec.get_spec := get_spec;
     spec.counter_content_exclusive := counter_content_exclusive |}.

Typeclasses Opaque counter_content is_counter.
