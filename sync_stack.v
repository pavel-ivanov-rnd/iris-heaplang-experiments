From iris.program_logic Require Export weakestpre hoare.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From iris.algebra Require Import excl.
From flatcomb Require Import sync.
Import uPred.

Definition mk_stack: val :=
  λ: <>,
       let: "s" := mk_sync #() in
       let: "lhd" := ref NONE in
       ("s" (* push *)
          (λ: "x",
              let: "hd" := !"lhd" in
              "lhd" <- SOME (ref("x", "hd"))),
        "s" (* pop *)
          (λ: <>,
                let: "hd" := !"lhd" in
                match: "hd" with
                  NONE => NONE
                | SOME "l" =>
                      let: "x" := Fst !"l" in
                      let: "xs" := Snd !"l" in
                      "lhd" <- "xs";;
                      SOME "x"
                end),
        "s" (* "iter" *)
          (rec: "iter" "f" :=
             let: "hd" := Fst !"lhd" in
             match: "hd" with
               NONE => #()
             | SOME "l" =>
                 let: "x" := Fst !"l" in
                 let: "xs" := Snd !"l" in
                 "f" "x";;
                 "iter" "xs"
             end)).

Definition push: val := λ: "s", Fst (Fst "s").
Definition pop: val := λ: "s",  Snd (Fst "s").
Definition iter: val := λ: "s", Snd "s".
                    

Section proof.
  Context `{!heapG Σ} (N: namespace).
  Implicit Types l : loc.

  (* copied from /tests/list_reverse.v *)
  Fixpoint is_stack (hd : val) (xs : list val) :=
    match xs with
    | [] => hd = NONEV
    | x :: xs => ∃ l hd', hd = SOMEV #l ★ l ↦ (x,hd') ★ is_stack hd' xs
    end%I.

End proof.

