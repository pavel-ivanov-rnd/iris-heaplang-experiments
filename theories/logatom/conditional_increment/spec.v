From stdpp Require Import namespaces.
From iris.heap_lang Require Export lifting notation.
From iris.program_logic Require Export atomic.
From iris_examples.logatom.lib Require Export gc.
Set Default Proof Using "Type".

(** A general logically atomic interface for conditional increment. *)
Record atomic_cinc {Σ} `{!heapG Σ, !gcG Σ} := AtomicCinc {
  (* -- operations -- *)
  new_counter : val;
  cinc : val;
  get : val;
  (* -- other data -- *)
  name : Type;
  name_eqdec : EqDecision name;
  name_countable : Countable name;
  (* -- predicates -- *)
  is_counter (N : namespace) (γs : name) (v : val) : iProp Σ;
  counter_content (γs : name) (c : Z) : iProp Σ;
  (* -- predicate properties -- *)
  is_counter_persistent N γs v : Persistent (is_counter N γs v);
  counter_content_timeless γs c : Timeless (counter_content γs c);
  counter_content_exclusive γs  c1 c2 :
    counter_content γs c1 -∗ counter_content γs c2 -∗ False;
  (* -- operation specs -- *)
  new_counter_spec N :
    N ## gcN →
    gc_inv -∗
    {{{ True }}}
        new_counter #()
    {{{ ctr γs, RET ctr ; is_counter N γs ctr ∗ counter_content γs 0 }}};
  cinc_spec N γs v (f : loc) :
    is_counter N γs v -∗
    <<< ∀ (b : bool) (n : Z), counter_content γs n ∗ gc_mapsto f #b >>>
        cinc v #f @⊤∖↑N∖↑gcN
    <<< counter_content γs (if b then n + 1 else n) ∗ gc_mapsto f #b, RET #() >>>;
  get_spec N γs v:
    is_counter N γs v -∗
    <<< ∀ (n : Z), counter_content γs n >>>
        get v @⊤∖↑N∖↑gcN
    <<< counter_content γs n, RET #n >>>;
}.
Arguments atomic_cinc _ {_ _}.

Existing Instances
  is_counter_persistent counter_content_timeless
  name_countable name_eqdec.
