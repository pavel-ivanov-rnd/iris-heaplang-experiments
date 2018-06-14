From stdpp Require Import namespaces.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export proofmode notation.

(** General (HoCAP-style) spec for a concurrent stack *)

Record concurrent_stack {Σ} `{!heapG Σ} := ConcurrentStack {
  mk_stack : val;
  mk_stack_spec (N : namespace) (P : list val → iProp Σ)
    (Q : val → iProp Σ) (Q' Q'' : iProp Σ) :
    {{{ P [] }}}
      mk_stack #()
    {{{ (f₁ f₂ : val), RET (f₁, f₂);
        (□ ( (∀ v vs, P (v :: vs) ={⊤ ∖ ↑ N}=∗ Q v ∗ P vs)
             ∧ (P [] ={⊤ ∖ ↑ N}=∗ Q' ∗ P []) -∗
            WP f₁ #() {{ v, (∃ (v' : val), v ≡ SOMEV v' ∗ Q v') ∨ (v ≡ NONEV ∗ Q')}}))
        ∗ (∀ (v : val),
             □ ((∀ vs, P vs ={⊤ ∖ ↑ N}=∗ P (v :: vs) ∗ Q'') -∗ WP f₂ v {{ v, Q'' }}))
    }}}
}.
Arguments concurrent_stack _ {_}.
