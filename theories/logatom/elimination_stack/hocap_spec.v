From stdpp Require Import namespaces.
From iris.algebra Require Import excl auth list.
From iris.heap_lang Require Export lifting notation.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode atomic_heap.
From iris_examples.logatom.elimination_stack Require spec.
Set Default Proof Using "Type".

Module logatom := elimination_stack.spec.

(** A general HoCAP-style interface for a stack, modeled after the spec in
[hocap/abstract_bag.v].  There are two differences:
- We split [bag_contents] into an authoritative part and a fragment as this
  slightly strnegthens the spec: The logically atomic spec only requires
  [stack_content ∗ stack_content] to derive a contradiction, the abstract bag
  spec requires to get *three* pieces which is only possible when actually
  calling a bag operation.
- We also slightly weaken the spec by adding [make_laterable], which is needed
  because logical atomicity can only capture laterable resources, which is
  needed when implementing e.g. the elimination stack on top of an abstract
  logically atomic heap. *)
Record hocap_stack {Σ} `{!heapG Σ} := AtomicStack {
  (* -- operations -- *)
  new_stack : val;
  push : val;
  pop : val;
  (* -- other data -- *)
  name : Type;
  name_eqdec : EqDecision name;
  name_countable : Countable name;
  (* -- predicates -- *)
  is_stack (N : namespace) (γs : name) (v : val) : iProp Σ;
  stack_content_frag (γs : name) (l : list val) : iProp Σ;
  stack_content_auth (γs : name) (l : list val) : iProp Σ;
  (* -- predicate properties -- *)
  is_stack_persistent N γs v : Persistent (is_stack N γs v);
  stack_content_frag_timeless γs l : Timeless (stack_content_frag γs l);
  stack_content_auth_timeless γs l : Timeless (stack_content_auth γs l);
  stack_content_frag_exclusive γs l1 l2 :
    stack_content_frag γs l1 -∗ stack_content_frag γs l2 -∗ False;
  stack_content_auth_exclusive γs l1 l2 :
    stack_content_auth γs l1 -∗ stack_content_auth γs l2 -∗ False;
  stack_content_agree γs l1 l2 :
    stack_content_frag γs l1 -∗ stack_content_auth γs l2 -∗ ⌜l1 = l2⌝;
  stack_content_update γs l l' :
    stack_content_frag γs l -∗
    stack_content_auth γs l -∗
    |==> stack_content_frag γs l' ∗ stack_content_auth γs l';
  (* -- operation specs -- *)
  new_stack_spec N :
    {{{ True }}} new_stack #() {{{ γs s, RET s; is_stack N γs s ∗ stack_content_frag γs [] }}};
  push_spec N γs s (v : val) (Φ : val → iProp Σ) :
    is_stack N γs s -∗
    make_laterable (∀ l, stack_content_auth γs l ={⊤∖↑N}=∗ stack_content_auth γs (v::l) ∗ Φ #()) -∗
    WP push s v {{ Φ }};
  pop_spec N γs s (Φ : val → iProp Σ) :
    is_stack N γs s -∗
    make_laterable (∀ l, stack_content_auth γs l ={⊤∖↑N}=∗
          match l with [] => stack_content_auth γs [] ∗ Φ NONEV
                | v :: l' => stack_content_auth γs l' ∗ Φ (SOMEV v) end) -∗
    WP pop s {{ Φ }};
}.
Arguments hocap_stack _ {_}.

Existing Instances
  is_stack_persistent stack_content_frag_timeless stack_content_auth_timeless
  name_eqdec name_countable.

(** Show that our way of writing the [pop_spec] is equivalent to what is done in
[concurrent_stack.spec].  IOW, the conjunction-vs-match doesn't matter.  Fixing
the postcondition (the [Q] in [concurrent_stack.spec]) still matters. *)
Section pop_equiv.
  Context `{invG Σ} (T : Type).

  Lemma pop_equiv E (I : list T → iProp Σ) (Φemp : iProp Σ) (Φret : T → iProp Σ) :
    (∀ l, I l ={E}=∗
       match l with [] => I [] ∗ Φemp | v :: l' => I l' ∗ Φret v end)
    ⊣⊢
    (∀ v vs, I (v :: vs) ={E}=∗ Φret v ∗ I vs)
    ∧ (I [] ={E}=∗ Φemp ∗ I []).
  Proof.
    iSplit.
    - iIntros "HΦ". iSplit.
      + iIntros (??) "HI". iMod ("HΦ" with "HI") as "[$ $]". done.
      + iIntros "HI". iMod ("HΦ" with "HI") as "[$ $]". done.
    - iIntros "HΦ" (l) "HI". destruct l; rewrite [(I _ ∗ _)%I]bi.sep_comm; by iApply "HΦ".
  Qed.
End pop_equiv.

(** From a HoCAP stack we can directly implement the logically atomic
interface. *)
Section hocap_logatom.
  Context `{!heapG Σ} (stack: hocap_stack Σ).

  Lemma logatom_push N γs s (v : val) :
    stack.(is_stack) N γs s -∗
    <<< ∀ l : list val, stack.(stack_content_frag) γs l >>>
      stack.(push) s v @ ⊤∖↑N
    <<< stack.(stack_content_frag) γs (v::l), RET #() >>>.
  Proof.
    iIntros "Hstack". iIntros (Φ) "HΦ".
    iApply (push_spec with "Hstack").
    iApply (make_laterable_intro with "[] HΦ"). iIntros "!# >HΦ" (l) "Hauth".
    iMod "HΦ" as (l') "[Hfrag [_ Hclose]]".
    iDestruct (stack_content_agree with "Hfrag Hauth") as %->.
    iMod (stack_content_update with "Hfrag Hauth") as "[Hfrag $]".
    iMod ("Hclose" with "Hfrag") as "HΦ". done.
  Qed.

  Lemma logatom_pop N γs (s : val) :
    stack.(is_stack) N γs s -∗
    <<< ∀ l : list val, stack.(stack_content_frag) γs l >>>
      stack.(pop) s @ ⊤∖↑N
    <<< stack.(stack_content_frag) γs (tail l),
        RET match l with [] => NONEV | v :: _ => SOMEV v end >>>.
  Proof.
    iIntros "Hstack". iIntros (Φ) "HΦ".
    iApply (pop_spec with "Hstack").
    iApply (make_laterable_intro with "[] HΦ"). iIntros "!# >HΦ" (l) "Hauth".
    iMod "HΦ" as (l') "[Hfrag [_ Hclose]]".
    iDestruct (stack_content_agree with "Hfrag Hauth") as %->.
    destruct l;
    iMod (stack_content_update with "Hfrag Hauth") as "[Hfrag $]";
    iMod ("Hclose" with "Hfrag") as "HΦ"; done.
  Qed.

  Definition hocap_logatom : logatom.atomic_stack Σ :=
    {| logatom.new_stack_spec := stack.(new_stack_spec);
       logatom.push_spec := logatom_push;
       logatom.pop_spec := logatom_pop;
       logatom.stack_content_exclusive := stack.(stack_content_frag_exclusive) |}.

End hocap_logatom.

(** From a logically atomic stack, we can implement a HoCAP stack by adding an
auth invariant. *)

(** The CMRA & functor we need. *)
Class hocapG Σ := HocapG {
  hocap_stateG :> inG Σ (authR (optionUR $ exclR (listO valO)));
}.
Definition hocapΣ : gFunctors :=
  #[GFunctor (exclR unitO); GFunctor (authR (optionUR $ exclR (listO valO)))].

Instance subG_hocapΣ {Σ} : subG hocapΣ Σ → hocapG Σ.
Proof. solve_inG. Qed.

Section logatom_hocap.
  Context `{!heapG Σ} `{!hocapG Σ} (stack: logatom.atomic_stack Σ).

  Definition hocap_name : Type := stack.(logatom.name) * gname.
  Implicit Types γs : hocap_name.

  Definition hocap_stack_content_auth γs l : iProp Σ := own γs.2 (● Excl' l).
  Definition hocap_stack_content_frag γs l : iProp Σ := own γs.2 (◯ Excl' l).

  Definition hocap_is_stack N γs v : iProp Σ :=
    (stack.(logatom.is_stack) (N .@ "stack") γs.1 v ∗
     inv (N .@ "wrapper") (∃ l, stack.(logatom.stack_content) γs.1 l ∗ hocap_stack_content_auth γs l))%I.

  Lemma hocap_new_stack N :
    {{{ True }}}
      stack.(logatom.new_stack) #()
    {{{ γs s, RET s; hocap_is_stack N γs s ∗ hocap_stack_content_frag γs [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_fupd. iApply logatom.new_stack_spec; first done.
    iIntros "!>" (γs s) "[Hstack Hcont]".
    iMod (own_alloc (● Excl' [] ⋅ ◯ Excl' [])) as (γw) "[Hs● Hs◯]".
    { apply auth_both_valid. split; done. }
    iApply ("HΦ" $! (γs, γw)). rewrite /hocap_is_stack. iFrame.
    iApply inv_alloc. eauto with iFrame.
  Qed.

  Lemma hocap_push N γs s (v : val) (Φ : val → iProp Σ) :
    hocap_is_stack N γs s -∗
    make_laterable (∀ l, hocap_stack_content_auth γs l ={⊤∖↑N}=∗ hocap_stack_content_auth γs (v::l) ∗ Φ #()) -∗
    WP stack.(logatom.push) s v {{ Φ }}.
  Proof using Type*.
    iIntros "#[Hstack Hwrap] Hupd". awp_apply (logatom.push_spec with "Hstack").
    iInv "Hwrap" as (l) "[>Hcont >H●]".
    iAaccIntro with "Hcont"; first by eauto 10 with iFrame.
    iIntros "Hcont".
    iMod fupd_intro_mask' as "Hclose";
      last iMod (make_laterable_elim with "Hupd H●") as "[H● HΦ]"; first solve_ndisj.
    iMod "Hclose" as "_". iIntros "!>".
    eauto with iFrame.
  Qed.

  Lemma hocap_pop N γs s (Φ : val → iProp Σ) :
    hocap_is_stack N γs s -∗
    make_laterable (∀ l, hocap_stack_content_auth γs l ={⊤∖↑N}=∗
          match l with [] => hocap_stack_content_auth γs [] ∗ Φ NONEV
                | v :: l' => hocap_stack_content_auth γs l' ∗ Φ (SOMEV v) end) -∗
    WP stack.(logatom.pop) s {{ Φ }}.
  Proof using Type*.
    iIntros "#[Hstack Hwrap] Hupd". awp_apply (logatom.pop_spec with "Hstack").
    iInv "Hwrap" as (l) "[>Hcont >H●]".
    iAaccIntro with "Hcont"; first by eauto 10 with iFrame.
    iIntros "Hcont". destruct l.
    - iMod fupd_intro_mask' as "Hclose";
        last iMod (make_laterable_elim with "Hupd H●") as "[H● HΦ]"; first solve_ndisj.
       iMod "Hclose" as "_". iIntros "!>"; eauto with iFrame.
    - iMod fupd_intro_mask' as "Hclose";
        last iMod (make_laterable_elim with "Hupd H●") as "[H● HΦ]"; first solve_ndisj.
       iMod "Hclose" as "_". iIntros "!>"; eauto with iFrame.
  Qed.

  Program Definition logatom_hocap : hocap_stack Σ :=
    {| new_stack_spec := hocap_new_stack;
       push_spec := hocap_push;
       pop_spec := hocap_pop |}.
  Next Obligation.
    iIntros (???) "Hf1 Hf2". iDestruct (own_valid_2 with "Hf1 Hf2") as %[].
  Qed.
  Next Obligation.
    iIntros (???) "Ha1 Ha2". by iDestruct (own_valid_2 with "Ha1 Ha2") as %[].
  Qed.
  Next Obligation.
    iIntros (???) "Hf Ha". iDestruct (own_valid_2 with "Ha Hf") as
      %[->%Excl_included%leibniz_equiv _]%auth_both_valid. done.
  Qed.
  Next Obligation.
    iIntros (???) "Hf Ha". iMod (own_update_2 with "Ha Hf") as "[? ?]".
    { eapply auth_update, option_local_update, (exclusive_local_update _ (Excl _)). done. }
    by iFrame.
  Qed.

End logatom_hocap.
