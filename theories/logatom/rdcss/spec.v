From stdpp Require Import namespaces.
From iris.heap_lang Require Export lifting notation.
From iris.program_logic Require Export atomic.
From iris_examples.logatom.lib Require Export gc.
Set Default Proof Using "Type".

(** A general logically atomic interface for RDCSS.
    See [rdcss.v] for references and more details about this data structure.

_Note on the use of GC locations_:  the specification of the [rdcss] operation
as given by [rdcss_spec] relies on the [gc_mapsto l_m m] assertion. It roughly
corresponds to the usual [l_m ↦ m] but with an additional guarantee that [l_m]
will not be deallocated. This guarantees that unique immutable descriptors can
be associated to each operation, and that they cannot be "reused". *)
Record atomic_rdcss {Σ} `{!heapG Σ, !gcG Σ} := AtomicRdcss {
  (* -- operations -- *)
  new_rdcss : val;
  rdcss: val;
  get : val;
  (* -- predicates -- *)
  is_rdcss (N : namespace) (l_n : loc) : iProp Σ;
  rdcss_state (N : namespace) (l_n : loc) (n : val) : iProp Σ;
  (* -- predicate properties -- *)
  is_rdcss_persistent N l_n : Persistent (is_rdcss N l_n);
  rdcss_state_timeless N l_n n : Timeless (rdcss_state N l_n n);
  rdcss_state_exclusive N l_n n1 n2 :
    rdcss_state N l_n n1 -∗ rdcss_state N l_n n2 -∗ False;
  (* -- operation specs -- *)
  new_rdcss_spec N (n : val):
    N ## gcN → gc_inv -∗
    {{{ True }}}
        new_rdcss n
    {{{ l_n, RET #l_n ; is_rdcss N l_n ∗ rdcss_state N l_n n }}};
  rdcss_spec N (l_n l_m : loc) (m1 n1 n2 : val):
    val_is_unboxed m1 →
    val_is_unboxed (InjLV n1) →
    is_rdcss N l_n -∗
    <<< ∀ (m n: val), gc_mapsto l_m m ∗ rdcss_state N l_n n >>>
        rdcss #l_m #l_n m1 n1 n2 @((⊤∖↑N)∖↑gcN)
    <<< gc_mapsto l_m m ∗ rdcss_state N l_n (if decide (m = m1 ∧ n = n1) then n2 else n), RET n >>>;
  get_spec N (l_n : loc):
    is_rdcss N l_n -∗
    <<< ∀ (n : val), rdcss_state N l_n n >>>
        get #l_n @(⊤∖↑N)
    <<< rdcss_state N l_n n, RET n >>>;
}.
Arguments atomic_rdcss _ {_} {_}.

Existing Instances is_rdcss_persistent rdcss_state_timeless.
