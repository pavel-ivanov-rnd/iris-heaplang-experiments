From stdpp Require Import namespaces.
From iris.heap_lang Require Export lifting notation.
From iris.program_logic Require Export atomic.
From iris_examples.logatom.lib Require Export gc.
Set Default Proof Using "Type".

(** A general logically atomic interface for RDCSS.
    See [rdcss.v] for references and more details about this data structure. *)

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
  (* -- other data -- *)
  name : Type;
  name_eqdec : EqDecision name;
  name_countable : Countable name;
  (* -- predicates -- *)
  is_rdcss (N : namespace) (γ : name) (l_n : loc) : iProp Σ;
  rdcss_content (γ : name) (n : val) : iProp Σ;
  (* -- predicate properties -- *)
  is_rdcss_persistent N γ l_n : Persistent (is_rdcss N γ l_n);
  rdcss_content_timeless γ n : Timeless (rdcss_content γ n);
  rdcss_content_exclusive γ n1 n2 : rdcss_content γ n1 -∗ rdcss_content γ n2 -∗ False;
  (* -- operation specs -- *)
  new_rdcss_spec N (n : val):
    N ## gcN → gc_inv -∗
    {{{ True }}}
        new_rdcss n
    {{{ l_n γ, RET #l_n ; is_rdcss N γ l_n ∗ rdcss_content γ n }}};
  rdcss_spec N γ (l_n l_m : loc) (m1 n1 n2 : val):
    val_is_unboxed m1 →
    val_is_unboxed (InjLV n1) →
    is_rdcss N γ l_n -∗
    <<< ∀ (m n: val), gc_mapsto l_m m ∗ rdcss_content γ n >>>
        rdcss #l_m #l_n m1 n1 n2 @((⊤∖↑N)∖↑gcN)
    <<< gc_mapsto l_m m ∗ rdcss_content γ (if decide (m = m1 ∧ n = n1) then n2 else n), RET n >>>;
  get_spec N γ (l_n : loc):
    is_rdcss N γ l_n -∗
    <<< ∀ (n : val), rdcss_content γ n >>>
        get #l_n @(⊤∖↑N)
    <<< rdcss_content γ n, RET n >>>;
}.
Arguments atomic_rdcss _ {_} {_}.

Existing Instances
  is_rdcss_persistent rdcss_content_timeless
  name_countable name_eqdec.

