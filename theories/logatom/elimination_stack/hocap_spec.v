(** This file explores the relation between "logically atomic"-style specs and
HoCAP-style specs.  The key difference between these specs is as follows:
- Logically atomic specs require the client to prove a mask-changing view shift
  which, at the linearization point, gets used to access the atomic
  precondition. The client can open invariants to prove this view shift. The
  library then works with this precondition, transforms it to the postcondition
  (which usually involves changing the abstract state), and gives that back to
  the client for a "closing" mask-changing view shift, where the client can
  close the invariants again.
- HoCAP-style specs require the client to prove a non-mask-changing view shift
  which may assume as an assumption the "old" abstract state of the library, and
  has to produce the "new" abstract state. Unlike with logically atomic specs,
  it is up to the *client* to change the abstract state to match the current
  operation. This pattern also does not really have a notion of "atomic
  precondition"; the relation between a sequential specification and its atomic
  counterpart is much more complex with HoCAP-style specs than it is with
  logically atomic specs.
  HoCAP-style specs come in two variants: "authoritative" and "predicate".
  Both can be found below.

One consequence of this difference is that there are some specs where the HoCAP
style simply does not work: one cannot use the HoCAP style to prove a spec about
the abstraction of *another library*.  See
<https://people.mpi-sws.org/~jung/iris/logatom-talk-2019.pdf#page=89> and
[heap_lang.lib.increment] in the Iris repository for an example of this.

For libraries that only state atomic transitions for their own abstraction, the
two styles are equivalent, as this file shows: we give two different HoCAP-style
specs (the "authoritative" variant, which is closer to the original HoCAP paper,
and the "predicate" variant which is somewhat simpler), and we show them both
equivalent to the logically atomic spec. *)


From stdpp Require Import namespaces.
From iris.algebra Require Import excl auth list.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode notation atomic_heap.
From iris_examples.logatom.elimination_stack Require spec.
Set Default Proof Using "Type".

Module logatom := elimination_stack.spec.

(** A general HoCAP-style interface for a stack, modeled after the spec in
[hocap/abstract_bag.v]. This style is similar to what was done in the HoCAP
paper, except that we avoid unnecessary quantification over propositions and
instead make use of viewn shifts *without* a persistence modality (in HoCAP,
view shifts are always persistent). This does not change the meaning of the
spec, it just makes it easier to use in Coq.
We might call this "Iris-adjusted HoCAP-style specs".

There are two differences to the [abstract_bag] spec:
- We split [bag_contents] into an authoritative part and a fragment as this
  slightly strengthens the spec ([stack_content_frag_exclusive] is added),
- We also slightly weaken the spec by adding [make_laterable], which is needed
  because logical atomicity can only capture laterable resources, which is
  needed when implementing e.g. the elimination stack on top of an abstract
  logically atomic heap.

This spec uses the "authoritative" variant of HoCAP specs.
See below for the "predicate"-based alternative *)
Module hocap_auth.
Record stack {Σ} `{!heapG Σ} := AtomicStack {
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
Arguments stack _ {_}.

Existing Instances
  is_stack_persistent stack_content_frag_timeless stack_content_auth_timeless
  name_eqdec name_countable.

End hocap_auth.

(** A general HoCAP-style interface for a stack, with a user-defined predicate
instead of an authoritative element, thereby departing even further from the
HoCAP paper.  This style matches [concurrent_stacks.spec]. *)
Module hocap_pred.
Record stack {Σ} `{!heapG Σ} := AtomicStack {
  (* -- operations -- *)
  new_stack : val;
  push : val;
  pop : val;
  (* -- predicates -- *)
  is_stack (N : namespace) (v : val) (P : list val → iProp Σ) : iProp Σ;
  (* -- predicate properties -- *)
  is_stack_persistent N P v : Persistent (is_stack N P v);
  is_stack_ne N v n : Proper (pointwise_relation _ (dist n) ==> dist n) (is_stack N v);
  (* -- operation specs -- *)
  new_stack_spec N P :
    {{{ ▷ P [] }}} new_stack #() {{{ s, RET s; is_stack N s P }}};
  push_spec N s P (v : val) (Φ : val → iProp Σ) :
    is_stack N s P -∗
    make_laterable (∀ l, ▷ P l ={⊤∖↑N}=∗ ▷ P (v::l) ∗ Φ #()) -∗
    WP push s v {{ Φ }};
  pop_spec N s P (Φ : val → iProp Σ) :
    is_stack N s P -∗
    make_laterable (∀ l, ▷ P l ={⊤∖↑N}=∗
          match l with [] => ▷ P [] ∗ Φ NONEV
                | v :: l' => ▷ P l' ∗ Φ (SOMEV v) end) -∗
    WP pop s {{ Φ }};
}.
Arguments stack _ {_}.

Existing Instances is_stack_persistent.

End hocap_pred.

(** Now we show the following three implications:
- hocap_auth implies logatom.
- logcatom implies hocap_pred.
- hocap_pred implies hocap_auth.
*)


(** From a HoCAP-"auth" stack we can directly implement the logically atomic
interface.

Roughly:
logatom.is_stack := hocap_auth.is_stack
logatom.stack_content := hocap_auth.stack_content_frag
*)
Section hocap_auth_logatom.
  Context `{!heapG Σ} (stack: hocap_auth.stack Σ).

  Lemma logatom_push N γs s (v : val) :
    stack.(hocap_auth.is_stack) N γs s -∗
    <<< ∀ l : list val, stack.(hocap_auth.stack_content_frag) γs l >>>
      stack.(hocap_auth.push) s v @ ⊤∖↑N
    <<< stack.(hocap_auth.stack_content_frag) γs (v::l), RET #() >>>.
  Proof.
    iIntros "Hstack". iIntros (Φ) "HΦ".
    iApply (hocap_auth.push_spec with "Hstack").
    iApply (make_laterable_intro with "[] HΦ"). iIntros "!# >HΦ" (l) "Hauth".
    iMod "HΦ" as (l') "[Hfrag [_ Hclose]]".
    iDestruct (hocap_auth.stack_content_agree with "Hfrag Hauth") as %->.
    iMod (hocap_auth.stack_content_update with "Hfrag Hauth") as "[Hfrag $]".
    iMod ("Hclose" with "Hfrag") as "HΦ". done.
  Qed.

  Lemma logatom_pop N γs (s : val) :
    stack.(hocap_auth.is_stack) N γs s -∗
    <<< ∀ l : list val, stack.(hocap_auth.stack_content_frag) γs l >>>
      stack.(hocap_auth.pop) s @ ⊤∖↑N
    <<< stack.(hocap_auth.stack_content_frag) γs (tail l),
        RET match l with [] => NONEV | v :: _ => SOMEV v end >>>.
  Proof.
    iIntros "Hstack". iIntros (Φ) "HΦ".
    iApply (hocap_auth.pop_spec with "Hstack").
    iApply (make_laterable_intro with "[] HΦ"). iIntros "!# >HΦ" (l) "Hauth".
    iMod "HΦ" as (l') "[Hfrag [_ Hclose]]".
    iDestruct (hocap_auth.stack_content_agree with "Hfrag Hauth") as %->.
    destruct l;
    iMod (hocap_auth.stack_content_update with "Hfrag Hauth") as "[Hfrag $]";
    iMod ("Hclose" with "Hfrag") as "HΦ"; done.
  Qed.

  Definition hocap_auth_logatom : logatom.atomic_stack Σ :=
    {| logatom.new_stack_spec := stack.(hocap_auth.new_stack_spec);
       logatom.push_spec := logatom_push;
       logatom.pop_spec := logatom_pop;
       logatom.stack_content_exclusive := stack.(hocap_auth.stack_content_frag_exclusive) |}.

End hocap_auth_logatom.

(** From a logically atomic stack, we can implement a HoCAP-"pred" stack by
 adding an invariant.

Roughly:
hocap_pred.is_stack P := logatom.is_stack * inv (∃ l, logatom.stack_content l * P l)
*)
Section logatom_hocap_pred.
  Context `{!heapG Σ} (stack: logatom.atomic_stack Σ).
  Implicit Type P : list val → iProp Σ.

  Definition hocap_pred_is_stack N v P : iProp Σ :=
    (∃ γs, stack.(logatom.is_stack) (N .@ "stack") γs v ∗
     inv (N .@ "wrapper") (∃ l, stack.(logatom.stack_content) γs l ∗ P l))%I.

  Instance hocap_pred_is_stack_ne N v n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (hocap_pred_is_stack N v).
  Proof. solve_proper. Qed.

  Lemma hocap_pred_new_stack N P :
    {{{ ▷ P [] }}}
      stack.(logatom.new_stack) #()
    {{{ s, RET s; hocap_pred_is_stack N s P }}}.
  Proof.
    iIntros (Φ) "HP HΦ". iApply wp_fupd. iApply logatom.new_stack_spec; first done.
    iIntros "!>" (γs s) "[Hstack Hcont]".
    iApply "HΦ". rewrite /hocap_pred_is_stack. iExists γs. iFrame.
    iApply inv_alloc. eauto with iFrame.
  Qed.

  Lemma hocap_pred_push N s P (v : val) (Φ : val → iProp Σ) :
    hocap_pred_is_stack N s P -∗
    make_laterable (∀ l, ▷ P l ={⊤∖↑N}=∗ ▷ P (v::l) ∗ Φ #()) -∗
    WP stack.(logatom.push) s v {{ Φ }}.
  Proof.
    iIntros "#Hstack Hupd". iDestruct "Hstack" as (γs) "[Hstack Hinv]".
    awp_apply (logatom.push_spec with "Hstack").
    iInv "Hinv" as (l) "[>Hcont HP]".
    iAaccIntro with "Hcont"; first by eauto 10 with iFrame.
    iIntros "Hcont".
    iMod fupd_intro_mask' as "Hclose";
      last iMod (make_laterable_elim with "Hupd HP") as "[HP HΦ]"; first solve_ndisj.
    iMod "Hclose" as "_". iIntros "!>".
    eauto with iFrame.
  Qed.

  Lemma hocap_pred_pop N s P (Φ : val → iProp Σ) :
    hocap_pred_is_stack N s P -∗
    make_laterable (∀ l, ▷ P l ={⊤∖↑N}=∗
          match l with [] => ▷ P [] ∗ Φ NONEV
                | v :: l' => ▷ P l' ∗ Φ (SOMEV v) end) -∗
    WP stack.(logatom.pop) s {{ Φ }}.
  Proof.
    iIntros "#Hstack Hupd". iDestruct "Hstack" as (γs) "[Hstack Hinv]".
    awp_apply (logatom.pop_spec with "Hstack").
    iInv "Hinv" as (l) "[>Hcont HP]".
    iAaccIntro with "Hcont"; first by eauto 10 with iFrame.
    iIntros "Hcont". destruct l.
    - iMod fupd_intro_mask' as "Hclose";
        last iMod (make_laterable_elim with "Hupd HP") as "[HP HΦ]"; first solve_ndisj.
       iMod "Hclose" as "_". iIntros "!>"; eauto with iFrame.
    - iMod fupd_intro_mask' as "Hclose";
        last iMod (make_laterable_elim with "Hupd HP") as "[HP HΦ]"; first solve_ndisj.
       iMod "Hclose" as "_". iIntros "!>"; eauto with iFrame.
  Qed.

  Program Definition logatom_hocap_pred : hocap_pred.stack Σ :=
    {| hocap_pred.new_stack_spec := hocap_pred_new_stack;
       hocap_pred.push_spec := hocap_pred_push;
       hocap_pred.pop_spec := hocap_pred_pop |}.

End logatom_hocap_pred.

(** From a hocap_pred stack, we can implement a hocap_auth stack by adding an
auth.

Roughly:
hocap_auth.is_stack := hocap_pred.is_stack (λ l, auth l)
hocap_auth.stack_content_auth := auth
hocap_auth.stack_content_frag := frag
*)

(** The CMRA & functor we need. *)
Class hocapG Σ := HocapG {
  hocap_stateG :> inG Σ (authR (optionUR $ exclR (listO valO)));
}.
Definition hocapΣ : gFunctors :=
  #[GFunctor (exclR unitO); GFunctor (authR (optionUR $ exclR (listO valO)))].

Instance subG_hocapΣ {Σ} : subG hocapΣ Σ → hocapG Σ.
Proof. solve_inG. Qed.

Section hocap_pred_auth.
  Context `{!heapG Σ} `{!hocapG Σ} (stack: hocap_pred.stack Σ).

  Definition hocap_name : Type := gname.
  Implicit Types γs : hocap_name.

  Definition hocap_auth_stack_content_auth γs l : iProp Σ := own γs (● Excl' l).
  Definition hocap_auth_stack_content_frag γs l : iProp Σ := own γs (◯ Excl' l).

  Definition hocap_auth_is_stack N γs v : iProp Σ :=
    stack.(hocap_pred.is_stack) N v (hocap_auth_stack_content_auth γs).

  Lemma hocap_auth_new_stack N :
    {{{ True }}}
      stack.(hocap_pred.new_stack) #()
    {{{ γs s, RET s; hocap_auth_is_stack N γs s ∗ hocap_auth_stack_content_frag γs [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_fupd.
    iMod (own_alloc (● Excl' [] ⋅ ◯ Excl' [])) as (γs) "[Hs● Hs◯]".
    { apply auth_both_valid. split; done. }
    iApply (hocap_pred.new_stack_spec _ _ (hocap_auth_stack_content_auth γs) with "[Hs● //]").
    iIntros "!>" (s) "#Hstack". iApply "HΦ".
    rewrite /hocap_auth_is_stack. by iFrame.
  Qed.

  Lemma hocap_auth_push N γs s (v : val) (Φ : val → iProp Σ) :
    hocap_auth_is_stack N γs s -∗
    make_laterable (∀ l, hocap_auth_stack_content_auth γs l ={⊤∖↑N}=∗
      hocap_auth_stack_content_auth γs (v::l) ∗ Φ #()) -∗
    WP stack.(hocap_pred.push) s v {{ Φ }}.
  Proof.
    iIntros "#Hstack Hupd". iApply (hocap_pred.push_spec with "Hstack").
    (* FIXME can we have proof mode support for make_laterable_intro? *)
    iApply (laterable.make_laterable_intro with "[] Hupd"); iIntros "!# Hupd".
    iIntros (l) ">Hs".
    (* FIXME can we have proof mode support for make_laterable_elim? *)
    iDestruct "Hupd" as ">Hupd". iDestruct (make_laterable_elim with "Hupd") as "Hupd".
    iMod ("Hupd" with "Hs") as "[Hs $]". done.
  Qed.

  Lemma hocap_auth_pop N γs s (Φ : val → iProp Σ) :
    hocap_auth_is_stack N γs s -∗
    make_laterable (∀ l, hocap_auth_stack_content_auth γs l ={⊤∖↑N}=∗
          match l with [] => hocap_auth_stack_content_auth γs [] ∗ Φ NONEV
                | v :: l' => hocap_auth_stack_content_auth γs l' ∗ Φ (SOMEV v) end) -∗
    WP stack.(hocap_pred.pop) s {{ Φ }}.
  Proof.
    iIntros "#Hstack Hupd". iApply (hocap_pred.pop_spec with "Hstack").
    iApply (laterable.make_laterable_intro with "[] Hupd"); iIntros "!# Hupd".
    iIntros (l) ">Hs".
    iDestruct "Hupd" as ">Hupd". iDestruct (make_laterable_elim with "Hupd") as "Hupd".
    iMod ("Hupd" with "Hs") as "HsΦ".
    iModIntro. destruct l; iDestruct "HsΦ" as "[Hs HΦ]"; eauto with iFrame.
  Qed.

  Program Definition hocap_pred_auth : hocap_auth.stack Σ :=
    {| hocap_auth.new_stack_spec := hocap_auth_new_stack;
       hocap_auth.push_spec := hocap_auth_push;
       hocap_auth.pop_spec := hocap_auth_pop |}.
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

End hocap_pred_auth.


(** Show that our way of writing the [pop_spec] is equivalent to what is done in
[concurrent_stack.spec].  IOW, the conjunction-vs-match doesn't matter. *)
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
