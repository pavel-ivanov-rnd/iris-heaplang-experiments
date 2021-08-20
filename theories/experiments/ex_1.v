From iris.heap_lang Require Import notation proofmode.
(*From iris_examples.concurrent_stacks Require Import specs.*)

Definition simple_leq : val := 
    rec: "simple_leq" "a" "b" :=
    let: "c" := #0 in
    if: "a" ≤ "b" 
    then "c" <- "a" 
    else "c" <- "b".

Definition simple_plus : val := 
    rec: "simple_plus" "a" "b" :=
    let: "c" := "a" + "b" in
    "c".

Definition lam_simple_plus : val := λ: "a" "b" "c",
    "c" <- "a" + "b".

Section simple_arith.
Context `{!heapGS Σ} (N : namespace).
Implicit Types l : loc.

Theorem lam_simple_plus_spec a b c: 
    {{{ True }}} lam_simple_plus #a #b #c {{{ RET #(); ⌜c = a + b⌝}}}.

Theorem simple_arith a b : 
    {{{ True }}} simple_plus (of_val (#a : nat)) (of_val #(b : nat)) {{{ c, RET c; ⌜c = a + b⌝ }}}.
Proof.
    
Qed.
 

Theorem simple_leq_spec a b :
    {{{ ⌜a ≤ b⌝ }}} simple_leq (of_val #a) (of_val #b) {{{ c, RET c; ⌜c = #a⌝ }}}.
Proof. iIntros (Φ) "H HΦ". wp_rec. do 2 wp_let. 


End simple_arith.