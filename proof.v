From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang.lib.barrier Require Export barrier.
From iris.prelude Require Import functions.
From iris.algebra Require Import upred_big_op.
From iris.program_logic Require Import saved_prop sts.
From iris.heap_lang Require Import proofmode.
From flatcomb Require Import protocol.

Class flatG Σ := FlatG {
  flat_stsG :> stsG Σ sts
}.

Definition flatΣ : gFunctors := #[stsΣ sts].

Instance subG_flatΣ {Σ} : subG flatΣ Σ → flatG Σ.
Admitted.

(** Now we come to the Iris part of the proof. *)
Section proof.
  Context `{!heapG Σ, !flatG Σ} (N : namespace).

  Coercion state_to_val (s : state) : val :=
    match s with
    | Init => #0
    | Req => #1
    | Exec => #2
    | Resp => #3
    | Ack => #4
    end.

  Arguments state_to_val !_ / : simpl nomatch.
  
  Definition flat_inv (l : loc) (s : state) : iProp Σ :=
    (l ↦ s)%I.

  Definition flat_ctx (γ: gname) (l : loc) : iProp Σ :=
  (■ (heapN ⊥ N) ★ heap_ctx ★ sts_ctx γ N (flat_inv l))%I.

