From iris.algebra Require Import excl auth list.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode atomic_heap.
From iris_examples.logatom.elimination_stack Require Import spec.
Set Default Proof Using "Type".

(** * Implement a concurrent stack with helping on top of an arbitrary atomic
heap. *)

(** The CMRA & functor we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class stackG Σ := StackG {
  stack_tokG :> inG Σ (exclR unitO);
  stack_stateG :> inG Σ (authR (optionUR $ exclR (listO valO)));
 }.
Definition stackΣ : gFunctors :=
  #[GFunctor (exclR unitO); GFunctor (authR (optionUR $ exclR (listO valO)))].

Instance subG_stackΣ {Σ} : subG stackΣ Σ → stackG Σ.
Proof. solve_inG. Qed.

Section stack.
  Context `{!heapG Σ, stackG Σ} {aheap: atomic_heap Σ} (N : namespace).
  Notation iProp := (iProp Σ).

  Let offerN := N .@ "offer".
  Let stackN := N .@ "stack".

  Import atomic_heap.notation.

  (** Code. A stack is a pair of two pointers-to-option-pointers, one for the
  head element (if the stack is non-empty) and for the current offer (if it
  exists).  A stack element is a pair of a value an an optional pointer to the
  next element. *)
  Definition new_stack : val :=
    λ: <>,
      let: "head" := ref NONE in
      let: "offer" := ref NONE in
      ("head", "offer").

  Definition push : val :=
    rec: "push" "stack" "val" :=
      let: "head_old" := !(Fst "stack") in
      let: "head_new" := ref ("val", "head_old") in
      if: CAS (Fst "stack") "head_old" (SOME "head_new") then #() else
      (* the CAS failed due to a race, let's try an offer on the side-channel *)
      let: "state" := ref #0 in
      let: "offer" := ("val", "state") in
      (Snd "stack") <- SOME "offer" ;;
      (* wait to see if anyone takes it *)
      (* okay, enough waiting *)
      (Snd "stack") <- NONE ;;
      if: CAS "state" #0 #2 then
        (* We retracted the offer. Just try the entire thing again. *)
        "push" "stack" "val"
      else
        (* Someone took the offer. We are done. *)
        #().

  Definition pop : val :=
    rec: "pop" "stack" :=
      match: !(Fst "stack") with
        NONE => NONE (* stack empty *)
      | SOME "head_old" =>
        let: "head_old_data" := !"head_old" in
        (* See if we can change the master head pointer *)
        if: CAS (Fst "stack") (SOME "head_old") (Snd "head_old_data") then
          (* That worked! We are done. Return the value. *)
          SOME (Fst "head_old_data")
        else
          (* See if there is an offer on the side-channel *)
          match: !(Snd "stack") with
            NONE =>
            (* Nope, no offer. Just try again. *)
            "pop" "stack"
          | SOME "offer" =>
            (* Try to accept the offer. *)
            if: CAS (Snd "offer") #0 #1 then
              (* Success! We are done. Return the offered value. *)
              SOME (Fst "offer")
            else
              (* Someone else was faster. Just try again. *)
              "pop" "stack"
          end
      end.

  (** Invariant and protocol. *)
  Definition stack_content (γs : gname) (l : list val) : iProp :=
    (own γs (◯ Excl' l))%I.
  Global Instance stack_content_timeless γs l : Timeless (stack_content γs l) := _.

  Lemma stack_content_exclusive γs l1 l2 :
    stack_content γs l1 -∗ stack_content γs l2 -∗ False.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (own_valid_2 with "Hl1 Hl2") as %[].
  Qed.

  Definition stack_elem_to_val (stack_rep : option loc) : val :=
    match stack_rep with
    | None => NONEV
    | Some l => SOMEV #l
    end.
  Local Instance stack_elem_to_val_inj : Inj (=) (=) stack_elem_to_val.
  Proof. rewrite /Inj /stack_elem_to_val=>??. repeat case_match; congruence. Qed.

  Fixpoint list_inv (l : list val) (rep : option loc) : iProp :=
    match l with
    | nil => ⌜rep = None⌝
    | v::l => ∃ (ℓ : loc) q (rep' : option loc), ⌜rep = Some ℓ⌝ ∗
                              ℓ ↦{q} (v, stack_elem_to_val rep') ∗ list_inv l rep'
    end%I.

  Local Hint Extern 0 (environments.envs_entails _ (list_inv (_::_) _)) => simpl : core.

  Inductive offer_state := OfferPending | OfferRevoked | OfferAccepted | OfferAcked.

  Local Instance: Inhabited offer_state := populate OfferPending.

  Definition offer_state_rep (st : offer_state) : Z :=
    match st with
    | OfferPending => 0
    | OfferRevoked => 2
    | OfferAccepted => 1
    | OfferAcked => 1
    end.

  Definition offer_inv (st_loc : loc) (γo : gname) (P Q : iProp) : iProp :=
    (∃ st : offer_state, st_loc ↦ #(offer_state_rep st) ∗
      match st with
      | OfferPending => P
      | OfferAccepted => Q
      | _ => own γo (Excl ())
      end)%I.

  Local Hint Extern 0 (environments.envs_entails _ (offer_inv _ _ _ _)) => unfold offer_inv : core.

  Definition is_offer (γs : gname) (offer_rep : option (val * loc)) :=
    match offer_rep with
    | None => True
    | Some (v, st_loc) =>
      ∃ P Q γo, inv offerN (offer_inv st_loc γo P Q) ∗
                (* The persistent part of the Laterable AU *)
                □ (▷ P -∗ ◇ AU << ∀ l, stack_content γs l >> @ ⊤∖↑N, ∅
                               << stack_content γs (v::l), COMM Q >>)
    end%I.

  Local Instance is_offer_persistent γs offer_rep : Persistent (is_offer γs offer_rep).
  Proof. destruct offer_rep as [[??]|]; apply _. Qed.

  Definition offer_to_val (offer_rep : option (val * loc)) : val :=
    match offer_rep with
    | None => NONEV
    | Some (v, l) => SOMEV (v, #l)
    end.

  Definition stack_inv (γs : gname) (head : loc) (offer : loc) : iProp :=
    (∃ stack_rep offer_rep l, own γs (● Excl' l) ∗
       head ↦ stack_elem_to_val stack_rep ∗ list_inv l stack_rep ∗
       offer ↦ offer_to_val offer_rep ∗ is_offer γs offer_rep)%I.

  Local Hint Extern 0 (environments.envs_entails _ (stack_inv _ _ _)) => unfold stack_inv : core.

  Definition is_stack (γs : gname) (s : val) : iProp :=
    (∃ head offer : loc, ⌜s = (#head, #offer)%V⌝ ∗ inv stackN (stack_inv γs head offer))%I.
  Global Instance is_stack_persistent γs s : Persistent (is_stack γs s) := _.

  (** Proofs. *)
  Lemma new_stack_spec :
    {{{ True }}} new_stack #() {{{ γs s, RET s; is_stack γs s ∗ stack_content γs [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_fupd. wp_lam.
    wp_apply alloc_spec; first done. iIntros (head) "Hhead". wp_let.
    wp_apply alloc_spec; first done. iIntros (offer) "Hoffer". wp_let.
    iMod (own_alloc (● Excl' [] ⋅ ◯ Excl' [])) as (γs) "[Hs● Hs◯]".
    { apply auth_both_valid. split; done. }
    iMod (inv_alloc stackN _ (stack_inv γs head offer) with "[-HΦ Hs◯]").
    { iNext. iExists None, None, _. iFrame. done. }
    wp_pures. iApply "HΦ". iFrame "Hs◯". iModIntro. iExists _, _. auto.
  Qed.

  Lemma push_spec γs s (v : val) :
    is_stack γs s -∗
    <<< ∀ l : list val, stack_content γs l >>>
      push s v @ ⊤∖↑N
    <<< stack_content γs (v::l), RET #() >>>.
  Proof.
    iIntros "#Hinv". iIntros (Φ) "AU".
    iDestruct "Hinv" as (head offer) "[% #Hinv]". subst s.
    iLöb as "IH".
    wp_lam.
    (* Load the old head. *)
    awp_apply load_spec without "AU".
    iInv stackN as (stack_rep offer_rep l) "(Hs● & >H↦ & Hrem)".
    iAaccIntro with "H↦"; first by eauto 10 with iFrame.
    iIntros "?". iSplitL; first by eauto 10 with iFrame.
    iIntros "!> AU". clear offer_rep l.
    (* Go on. *)
    wp_let. wp_apply alloc_spec; first done. iIntros (head_new) "Hhead_new".
    (* CAS to change the head. *)
    awp_apply cas_spec; [by destruct stack_rep|].
    iInv stackN as (stack_rep' offer_rep l) "(>Hs● & >H↦ & Hlist & Hoffer)".
    iAaccIntro with "H↦"; first by eauto 10 with iFrame.
    iIntros "H↦".
    destruct (decide (stack_elem_to_val stack_rep' = stack_elem_to_val stack_rep)) as
      [->%stack_elem_to_val_inj|_].
    - (* The CAS succeeded. Update everything accordingly. *)
      iMod "AU" as (l') "[Hl' [_ Hclose]]".
      iDestruct (own_valid_2 with "Hs● Hl'") as
        %[->%Excl_included%leibniz_equiv _]%auth_both_valid.
      iMod (own_update_2 with "Hs● Hl'") as "[Hs● Hl']".
      { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
      iMod ("Hclose" with "Hl'") as "HΦ". iModIntro.
      change (InjRV #head_new) with (stack_elem_to_val (Some head_new)).
      iSplitR "HΦ"; first by eauto 12 with iFrame.
      wp_if. by iApply "HΦ".
    - (* The CAS failed, go on making an offer. *)
      iModIntro. iSplitR "AU"; first by eauto 8 with iFrame.
      clear stack_rep stack_rep' offer_rep l head_new.
      wp_if.
      wp_apply alloc_spec; first done. iIntros (st_loc) "Hoffer_st".
      (* Make the offer *)
      awp_apply store_spec.
      iInv stackN as (stack_rep offer_rep l) "(Hs● & >H↦ & Hlist & >Hoffer↦ & Hoffer)".
      iAaccIntro with "Hoffer↦"; first by eauto 10 with iFrame.
      iMod (own_alloc (Excl ())) as (γo) "Htok"; first done.
      iDestruct (laterable with "AU") as (AU_later) "[AU #AU_back]".
      iMod (inv_alloc offerN _ (offer_inv st_loc γo AU_later _)  with "[AU Hoffer_st]") as "#Hoinv".
      { iNext. iExists OfferPending. iFrame. }
      iIntros "?". iSplitR "Htok".
      { iClear "Hoffer". iExists _, (Some (v, st_loc)), _. iFrame.
        rewrite /is_offer /=. iExists _, _, _. iFrame "AU_back Hoinv". done. }
      clear stack_rep offer_rep l. iIntros "!>".
      (* Retract the offer. *)
      awp_apply store_spec.
      iInv stackN as (stack_rep offer_rep l) "(Hs● & >H↦ & Hlist & >Hoffer↦ & Hoffer)".
      iAaccIntro with "Hoffer↦"; first by eauto 10 with iFrame.
      iIntros "?". iSplitR "Htok".
      { iClear "Hoffer". iExists _, None, _. iFrame. done. }
      iIntros "!>". wp_seq.
      clear stack_rep offer_rep l.
      (* See if someone took it. *)
      awp_apply cas_spec; [done|].
      iInv offerN as (offer_st) "[>Hst↦ Hst]".
      iAaccIntro with "Hst↦"; first by eauto 10 with iFrame.
      iIntros "Hst↦". destruct offer_st; simpl.
      + (* Offer was still pending, and we revoked it. Loop around and try again. *)
        iModIntro. iSplitR "Hst".
        { iNext. iExists OfferRevoked. iFrame. }
        iDestruct ("AU_back" with "Hst") as ">AU {AU_back Hoinv}". clear AU_later.
        wp_if. iApply ("IH" with "AU").
      + (* Offer revoked by someone else? Impossible! *)
        iDestruct "Hst" as ">Hst".
        iDestruct (own_valid_2 with "Htok Hst") as %[].
      + (* Offer got accepted by someone, awesome! We are done. *)
        iModIntro. iSplitR "Hst".
        { iNext. iExists OfferAcked. iFrame. }
        wp_if. by iApply "Hst".
      + (* Offer got acked by someone else? Impossible! *)
        iDestruct "Hst" as ">Hst".
        iDestruct (own_valid_2 with "Htok Hst") as %[].
  Qed.

  Lemma pop_spec γs (s : val) :
    is_stack γs s -∗
    <<< ∀ l, stack_content γs l >>>
      pop s @ ⊤∖↑N
    <<< stack_content γs (tail l),
        RET match l with [] => NONEV | v :: _ => SOMEV v end >>>.
  Proof.
    iIntros "#Hinv". iIntros (Φ) "AU".
    iDestruct "Hinv" as (head offer) "[% #Hinv]". subst s.
    iLöb as "IH". wp_lam. wp_pures.
    (* Load the old head *)
    awp_apply load_spec.
    iInv stackN as (stack_rep offer_rep l) "(>Hs● & >H↦ & Hlist & Hrem)".
    iAaccIntro with "H↦"; first by eauto 10 with iFrame.
    iIntros "?". destruct l as [|v l]; simpl.
    - (* The list is empty! We are already done, but it's quite some work to
      prove that. *)
      iDestruct "Hlist" as ">%". subst stack_rep.
      iMod "AU" as (l') "[Hl' [_ Hclose]]".
      iDestruct (own_valid_2 with "Hs● Hl'") as
        %[->%Excl_included%leibniz_equiv _]%auth_both_valid.
      iMod ("Hclose" with "Hl'") as "HΦ".
      iSplitR "HΦ"; first by eauto 10 with iFrame.
      iIntros "!>". wp_pures. by iApply "HΦ".
    - (* Non-empty list, let's try to pop. *)
      iDestruct "Hlist" as (tail q rep) "[>% [[Htail Htail2] Hlist]]". subst stack_rep.
      iSplitR "AU Htail"; first by eauto 15 with iFrame.
      clear offer_rep l.
      iIntros "!>". wp_match.
      wp_apply (atomic_wp_seq $! (load_spec _) with "Htail").
      iIntros "Htail". wp_pures.
      (* CAS to change the head *)
      awp_apply cas_spec; [done|].
      iInv stackN as (stack_rep offer_rep l) "(>Hs● & >H↦ & Hlist & Hrem)".
      iAaccIntro with "H↦"; first by eauto 10 with iFrame.
      iIntros "H↦". change (InjRV #tail) with (stack_elem_to_val (Some tail)).
      destruct (decide (stack_elem_to_val stack_rep = stack_elem_to_val (Some tail))) as
        [->%stack_elem_to_val_inj|_].
      + (* CAS succeeded! It must still be the same head element in the list,
        and we are done. *)
        iMod "AU" as (l') "[Hl' [_ Hclose]]".
        iDestruct (own_valid_2 with "Hs● Hl'") as
          %[->%Excl_included%leibniz_equiv _]%auth_both_valid.
        destruct l as [|v' l]; simpl.
        { (* Contradiction. *) iDestruct "Hlist" as ">%". done. }
        iDestruct "Hlist" as (tail' q' rep') "[>% [>Htail' Hlist]]". simplify_eq.
        iDestruct (mapsto_agree with "Htail Htail'") as %[= <- <-%stack_elem_to_val_inj].
        iMod (own_update_2 with "Hs● Hl'") as "[Hs● Hl']".
        { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
        iMod ("Hclose" with "Hl'") as "HΦ {Htail Htail'}".
        iSplitR "HΦ"; first by eauto 10 with iFrame.
        iIntros "!>". clear q' q offer_rep l.
        wp_pures. by iApply "HΦ".
      + (* CAS failed.  Go on looking for an offer. *)
        iSplitR "AU"; first by eauto 10 with iFrame.
        iIntros "!>". wp_if. clear rep stack_rep offer_rep l q tail v.
        wp_proj.
        (* Load the offer pointer. *)
        awp_apply load_spec.
        iInv stackN as (stack_rep offer_rep l) "(>Hs● & >H↦ & Hlist & >Hoff↦ & #Hoff)".
        iAaccIntro with "Hoff↦"; first by eauto 10 with iFrame.
        iIntros "Hoff↦". iSplitR "AU"; first by eauto 10 with iFrame.
        iIntros "!>". destruct offer_rep as [[v offer_st_loc]|]; last first.
        { (* No offer, just loop. *) wp_match. iApply ("IH" with "AU"). }
        clear l stack_rep. wp_match. wp_proj.
        (* CAS to accept the offer. *)
        awp_apply cas_spec; [done|]. simpl.
        iDestruct "Hoff" as (Poff Qoff γo) "[#Hoinv #AUoff]".
        iInv offerN as (offer_st) "[>Hoff↦ Hoff]".
        iAaccIntro with "Hoff↦"; first by eauto 10 with iFrame.
        iIntros "Hoff↦".
        destruct (decide (#(offer_state_rep offer_st) = #0)) as [Heq|_]; last first.
        { (* CAS failed, we don't do a thing. *)
          iSplitR "AU"; first by eauto 10 with iFrame.
          iIntros "!>". wp_if. iApply ("IH" with "AU"). }
        (* CAS succeeded! We accept and complete the offer. *)
        destruct offer_st; try done; []. clear Heq.
        iMod ("AUoff" with "Hoff") as "{AUoff IH} AUoff".
        iInv stackN as (stack_rep offer_rep l) "(>Hs● & >H↦ & Hlist & Hoff)".
        iMod "AUoff" as (l') "[Hl' [_ Hclose]]".
        iDestruct (own_valid_2 with "Hs● Hl'") as
          %[->%Excl_included%leibniz_equiv _]%auth_both_valid.
        iMod (own_update_2 with "Hs● Hl'") as "[Hs● Hl']".
        { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
        iMod ("Hclose" with "Hl'") as "HQoff".
        iMod "AU" as (l') "[Hl' [_ Hclose]]".
        iDestruct (own_valid_2 with "Hs● Hl'") as
          %[->%Excl_included%leibniz_equiv _]%auth_both_valid.
        iMod (own_update_2 with "Hs● Hl'") as "[Hs● Hl']".
        { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
        iMod ("Hclose" with "Hl'") as "HΦ".
        iSplitR "Hoff↦ HQoff HΦ"; first by eauto 10 with iFrame. iSplitR "HΦ".
        { iIntros "!> !> !>". iExists OfferAccepted. iFrame. }
        iIntros "!> !>". wp_pures. by iApply "HΦ".
  Qed.

End stack.

Definition elimination_stack `{!heapG Σ, stackG Σ} {aheap: atomic_heap Σ} :
  atomic_stack Σ :=
  {| spec.new_stack_spec := new_stack_spec;
     spec.push_spec := push_spec;
     spec.pop_spec := pop_spec;
     spec.stack_content_exclusive := stack_content_exclusive |}.

Typeclasses Opaque stack_content is_stack.
