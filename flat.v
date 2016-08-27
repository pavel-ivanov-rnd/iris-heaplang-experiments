From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spin_lock.
From flatcomb Require Import sync_stack.
Import uPred.

Section flat_combiner.
  Context `{!heapG Σ, !lockG Σ} (N: namespace).
  Implicit Types l : loc.

  Definition install: val :=
    λ: "lcl" "req" "push",
       match: !"lcl" with
         SOME "o" => "o" <- InjL "req";; "o"
       | NONE => let: "o" := ref (InjL "req") in
                 "lcl" <- "o";;
                 "push" "o";;
                 "o"
       end.

  Definition doOp: val :=
    λ: "f" "o",
       match: !"o" with
         InjL "req" => "o" <- InjR ("f" "o")
       | InjR "_" => #()
       end.

  Definition loop: val :=
    rec: "loop" "o" "f" "lock" "iter" :=
      match: !"o" with
        InjL "_" =>
          if: CAS "lock" #false #true
            then "iter" (doOp "f") ;; "lock" <- #false;; "loop" "o" "f" "lock" "iter"
            else "loop" "o" "f" "lock" "iter"
      | InjR "res" => "res"
      end.

  Definition flat: val :=
    λ: "f",
       let: "lock" := ref (#false) in
       let: "lcl" := ref #0 in
       let: "s" := mk_stack #() in
       λ: "x",
          let: "o" := install "x" (push "s") in
          loop "o" "f" "lock" (iter "s").

End flat_combiner.
