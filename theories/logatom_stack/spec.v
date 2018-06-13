From stdpp Require Import namespaces.
From iris.heap_lang Require Export lifting notation.
From iris.program_logic Require Export atomic.
Set Default Proof Using "Type".

(** A general logically atomic interface for a stack. *)
Record atomic_stack {Σ} `{!heapG Σ} := AtomicStack {
  (* -- operations -- *)
  new_stack : val;
  push : val;
  pop : val;
  (* -- other data -- *)
  name : Type;
  (* -- predicates -- *)
  is_stack (N : namespace) (γs : name) (v : val) : iProp Σ;
  stack_content (γs : name) (l : list val) : iProp Σ;
  (* -- predicate properties -- *)
  is_stack_persistent N γs v : Persistent (is_stack N γs v);
  stack_content_timeless γs l : Timeless (stack_content γs l);
  stack_content_exclusive γs l1 l2 :
    stack_content γs l1 -∗ stack_content γs l2 -∗ False;
  (* -- operation specs -- *)
  new_stack_spec N :
    {{{ True }}} new_stack #() {{{ γs s, RET s; is_stack N γs s ∗ stack_content γs [] }}};
  push_spec N γs s e v :
    IntoVal e v →
    is_stack N γs s -∗
    <<< ∀ l, stack_content γs l >>>
      push (s, e) @ ⊤∖↑N
    <<< stack_content γs (v::l), RET #() >>>;
  pop_spec N γs s :
    is_stack N γs s -∗
    <<< ∀ l, stack_content γs l >>>
      pop s @ ⊤∖↑N
    <<< stack_content γs (tail l),
        RET match l with [] => NONEV | v :: _ => SOMEV v end >>>;
}.
Arguments atomic_stack _ {_}.

Existing Instance is_stack_persistent.
Existing Instance stack_content_timeless.
