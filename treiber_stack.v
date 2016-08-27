From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import invariants ghost_ownership.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.

Section treiber_stack.
  Context `{!heapG Σ} (N: namespace).

  Definition push_treiber: val :=
    rec: "push_treiber" "lhd" "x" :=
      let: "hd" := !"lhd" in
      let: "hd'" := ("x", SOME "lhd") in
      if: CAS "lhd" "hd" "hd'"
        then #()
        else "push_treiber" "lhd" "x".

  Definition pop_treiber: val :=
    rec: "pop_treiber" "lhd" :=
      let: "hd" := !"lhd" in
      match: "hd" with
        SOME "pair" =>
        if: CAS "lhd" "hd" (Snd "pair")
          then SOME (Fst "pair")
          else "pop_treiber" "lhd"
      | NONE => NONE
      end.

End treiber_stack.
