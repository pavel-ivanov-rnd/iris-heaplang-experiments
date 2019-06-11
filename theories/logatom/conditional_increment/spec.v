From stdpp Require Import namespaces.
From iris.heap_lang Require Export lifting notation.
From iris.program_logic Require Export atomic.
Set Default Proof Using "Type".

(** A general logically atomic interface for conditional increment. *)
Record atomic_cinc {Σ} `{!heapG Σ} := AtomicCinc {
  (* -- operations -- *)
  new_counter : val;
  cinc : val;
  set_flag : val;
  get : val;
  (* -- other data -- *)
  name : Type;
  name_eqdec : EqDecision name;
  name_countable : Countable name;
  (* -- predicates -- *)
  is_counter (N : namespace) (γs : name) (v : val) : iProp Σ;
  counter_content (γs : name) (flag : bool) (c : Z) : iProp Σ;
  (* -- predicate properties -- *)
  is_counter_persistent N γs v : Persistent (is_counter N γs v);
  counter_content_timeless γs f c : Timeless (counter_content γs f c);
  counter_content_exclusive γs f1 c1 f2 c2 :
    counter_content γs f1 c1 -∗ counter_content γs f2 c2 -∗ False;
  (* -- operation specs -- *)
  new_counter_spec N :
    {{{ True }}}
        new_counter #()
    {{{ ctr γs, RET ctr ; is_counter N γs ctr ∗ counter_content γs true 0 }}};
  cinc_spec N γs v :
    is_counter N γs v -∗
    <<< ∀ (b : bool) (n : Z), counter_content γs b n >>>
        cinc v @⊤∖↑N
    <<< counter_content γs b (if b then n + 1 else n), RET #() >>>;
  set_flag_spec N γs v (new_b: bool) :
    is_counter N γs v -∗
    <<< ∀ (b : bool) (n : Z), counter_content γs b n >>>
        set_flag v #new_b @⊤∖↑N
    <<< counter_content γs new_b n, RET #() >>>;
  get_spec N γs v:
    is_counter N γs v -∗
    <<< ∀ (b : bool) (n : Z), counter_content γs b n >>>
        get v @⊤∖↑N
    <<< counter_content γs b n, RET #n >>>;
}.
Arguments atomic_cinc _ {_}.

Existing Instances
  is_counter_persistent counter_content_timeless
  name_countable name_eqdec.
