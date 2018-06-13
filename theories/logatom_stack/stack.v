From iris.heap_lang Require Export lifting notation.
From iris.algebra Require Import excl auth list.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation atomic_heap par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "Type".

(** * Implement a concurrent stack with helping on top of an arbitrary atomic
heap. *)
Definition stackN : namespace := nroot .@ "logatom_stack".
Definition offerN : namespace := nroot .@ "logatom_stack" .@ "offer".
Definition protoN : namespace := nroot .@ "logatom_stack" .@ "protocol".

(** The CMRA & functor we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class stackG Σ := StackG {
  stack_tokG :> inG Σ (exclR unitC);
  stack_stateG :> inG Σ (authR (optionUR $ exclR (listC valC)));
 }.
Definition stackΣ : gFunctors :=
  #[GFunctor (exclR unitC); GFunctor (authR (optionUR $ exclR (listC valC)))].

Instance subG_stackΣ {Σ} : subG stackΣ Σ → stackG Σ.
Proof. solve_inG. Qed.

Section stack.
  Context `{!heapG Σ, stackG Σ} {aheap: atomic_heap Σ}.
  Notation iProp := (iProp Σ).

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
    rec: "push" "args" :=
      let: "stack" := Fst "args" in
      let: "val" := Snd "args" in
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
        "push" "args"
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
          Fst "head_old_data"
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
              Fst "offer"
            else
              (* Someone else was faster. Just try again. *)
              "pop" "stack"
          end
      end.

  (** Invariant and protocol. *)
  Definition stack_content (γs : gname) (l : list val) : iProp :=
    (own γs (◯ Excl' l))%I.
  Global Instance stack_content_timeless γs l : Timeless (stack_content γs l) := _.

  Fixpoint list_inv (l : list val) (rep : val) : iProp :=
    match l with
    | nil => ⌜rep = NONEV⌝
    | v::l => ∃ (ℓ : loc) (rep' : val), ⌜rep = SOMEV #ℓ⌝ ∗ ℓ ↦ (v, rep') ∗ list_inv l rep'
    end%I.

  Inductive offer_state := OfferPending | OfferRevoked | OfferAccepted | OfferAcked.

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
      | _ => True
      end)%I.

  Definition is_offer (γs : gname) (offer_rep : option (val * loc)) :=
    match offer_rep with
    | None => True
    | Some (v, st_loc) =>
      ∃ P Q γo, inv offerN (offer_inv st_loc γo P Q) ∗
                (* The persistent part of the Laterable AU *)
                □ (▷ P -∗ ◇ AU << ∀ l, stack_content γs l >> @ ⊤∖↑stackN, ∅
                               << stack_content γs (v::l), COMM Q >>)
    end%I.

  Definition offer_to_val (offer_rep : option (val * loc)) : val :=
    match offer_rep with
    | None => NONEV
    | Some (v, l) => SOMEV (v, #l)
    end.

  Definition stack_inv (γs : gname) (head : loc) (offer : loc) : iProp :=
    (∃ stack_rep offer_rep l, own γs (● Excl' l) ∗
       head ↦ stack_rep ∗ list_inv l stack_rep ∗
       offer ↦ offer_to_val offer_rep ∗ is_offer γs offer_rep)%I.

  Definition is_stack (γs : gname) (s : val) : iProp :=
    (∃ head offer : loc, ⌜s = (#head, #offer)%V⌝ ∗ inv protoN (stack_inv γs head offer))%I.
  Global Instance is_stack_persistent γs s : Persistent (is_stack γs s) := _.

  (** Proofs. *)
  Lemma new_stack_spec :
    {{{ True }}} new_stack #() {{{ γs s, RET s; is_stack γs s ∗ stack_content γs [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_fupd. wp_lam.
    wp_apply alloc_spec; first done. iIntros (head) "Hhead". wp_let.
    wp_apply alloc_spec; first done. iIntros (offer) "Hoffer". wp_let.
    iMod (own_alloc (● Excl' [] ⋅ ◯ Excl' [])) as (γs) "[Hs● Hs◯]".
    { apply auth_valid_discrete_2. split; done. }
    iMod (inv_alloc protoN _ (stack_inv γs head offer) with "[-HΦ Hs◯]").
    { iNext. iExists _, None, _. iFrame. done. }
    iApply "HΦ". iFrame "Hs◯". iModIntro. iExists _, _. auto.
  Qed.

End stack.

Global Typeclasses Opaque stack_content is_stack.
