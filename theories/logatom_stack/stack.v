From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lifting proofmode notation atomic_heap par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "Type".

(** * Implement a concurrent stack with helping on top of an arbitrary atomic
heap. *)

(** The CMRA & functor we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class stackG Σ := StackG { stack_tokG :> inG Σ (exclR unitC) }.
Definition stackΣ : gFunctors := #[GFunctor (exclR unitC)].

Instance subG_stackΣ {Σ} : subG stackΣ Σ → stackG Σ.
Proof. solve_inG. Qed.

Section stack.
  Context `{!heapG Σ, stackG Σ} {aheap: atomic_heap Σ}.

  Import atomic_heap.notation.

  (** Code. A stack is a pair of two option pointers-to-pointers, one for the
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

End stack.
