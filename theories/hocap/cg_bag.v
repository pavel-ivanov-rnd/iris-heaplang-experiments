(** Concurrent bag specification from the HOCAP paper.
    "Modular Reasoning about Separation of Concurrent Data Structures"
    <http://www.kasv.dk/articles/hocap-ext.pdf>

Coarse-grained implementation of a bag
*)
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import cmra agree frac.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris_examples.hocap Require Import abstract_bag.
Set Default Proof Using "Type".

(** Coarse-grained bag implementation using a spin lock *)
Definition newBag : val := λ: <>,
  (ref NONE, newlock #()).
Definition pushBag : val := λ: "b" "v",
  let: "l" := Snd "b" in
  let: "r" := Fst "b" in
  acquire "l";;
  let: "t" := !"r" in
  "r" <- SOME ("v", "t");;
  release "l".
Definition popBag : val := λ: "b",
  let: "l" := Snd "b" in
  let: "r" := Fst "b" in
  acquire "l";;
  let: "v" := match: !"r" with
                NONE => NONE
              | SOME "s" =>
                "r" <- Snd "s";;
                SOME (Fst "s")
              end in
  release "l";;
  "v".

Canonical Structure valmultisetC := leibnizC (gmultiset valC).
Class bagG Σ := BagG
{ bag_bagG :> inG Σ (prodR fracR (agreeR valmultisetC));
  lock_bagG :> lockG Σ
}.

(** Generic specification for the bag, using view shifts. *)
Section proof.
  Context `{heapG Σ, bagG Σ}.
  Variable N : namespace.

  Fixpoint bag_of_val (ls : val) : gmultiset val :=
    match ls with
    | NONEV => ∅
    | SOMEV (v1, t) => {[v1]} ∪ bag_of_val t
    | _ => ∅
    end.
  Fixpoint val_of_list (ls : list val) : val :=
    match ls with
    | [] => NONEV
    | x::xs => SOMEV (x, val_of_list xs)
    end.

  Definition bag_inv (γb : gname) (b : loc) : iProp Σ :=
    (∃ ls : list val, b ↦ (val_of_list ls) ∗ own γb ((1/2)%Qp, to_agree (of_list ls)))%I.
  Definition isBag (γb : gname) (x : val) :=

    (∃ (lk : val) (b : loc) (γ : gname),
        ⌜x = PairV #b lk⌝ ∗ is_lock N γ lk (bag_inv γb b))%I.
  Definition bagContents (γb : gname) (X : gmultiset val) : iProp Σ :=
    own γb ((1/2)%Qp, to_agree X).

  Global Instance isBag_persistent γb x : Persistent (isBag γb x).
  Proof. apply _. Qed.
  Global Instance bagContents_timeless γb X : Timeless (bagContents γb X).
  Proof. apply _. Qed.

  Lemma bagContents_agree γb X Y :
    bagContents γb X -∗ bagContents γb Y -∗ ⌜X = Y⌝.
  Proof.
    rewrite /bagContents. apply uPred.wand_intro_r.
    rewrite -own_op own_valid uPred.discrete_valid.
    f_equiv=> /=. rewrite pair_op.
    by intros [_ ?%agree_op_invL'].
  Qed.

  Lemma bagContents_update γb X X' Y :
    bagContents γb X ∗ bagContents γb X' ==∗ bagContents γb Y ∗ bagContents γb Y.
  Proof.
    iIntros "[Hb1 Hb2]".
    iDestruct (bagContents_agree with "Hb1 Hb2") as %<-.
    iMod (own_update_2 with "Hb1 Hb2") as "Hb".
    { rewrite pair_op frac_op'.
      assert ((1 / 2 + 1 / 2)%Qp = 1%Qp) as -> by apply Qp_div_2.
      by apply (cmra_update_exclusive (1%Qp, to_agree Y)). }
    iDestruct "Hb" as "[Hb1 Hb2]".
    rewrite /bagContents. by iFrame.
  Qed.

  Lemma newBag_spec :
    {{{ True }}}
      newBag #()
    {{{ x γ, RET x; isBag γ x ∗ bagContents γ ∅ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    unfold newBag. wp_rec.
    wp_alloc r as "Hr".
    iMod (own_alloc (1%Qp, to_agree ∅)) as (γb) "[Ha Hf]"; first done.
    wp_apply (newlock_spec N (bag_inv γb r) with "[Hr Ha]").
    { iExists []. iFrame. }
    iIntros (lk γ) "#Hlk".
    iApply wp_value. iApply "HΦ".
    rewrite /isBag /bagContents. iFrame.
    iExists _,_,_. by iFrame "Hlk".
  Qed.

  Local Opaque acquire release. (* so that wp_pure doesn't stumble *)
  Lemma pushBag_spec (P Q : iProp Σ) γ (x v : val)  :
    □ (∀ (X : gmultiset val), bagContents γ X ∗ P
                     ={⊤}=∗ ▷ (bagContents γ ({[v]} ∪ X) ∗ Q)) -∗
    {{{ isBag γ x ∗ P }}}
      pushBag x (of_val v)
    {{{ RET #(); Q }}}.
  Proof.
    iIntros "#Hvs".
    iIntros (Φ). iAlways. iIntros "[#Hbag HP] HΦ".
    unfold pushBag. do 2 wp_rec.
    rewrite /isBag /bag_inv.
    iDestruct "Hbag" as (lk b γl) "[% #Hlk]"; simplify_eq/=.
    repeat wp_pure _.
    wp_apply (acquire_spec with "Hlk"). iIntros "[Htok Hb1]".
    iDestruct "Hb1" as (ls) "[Hb Ha]".
    wp_seq. wp_load. wp_let.
    (* iApply (wp_mask_mono _ (⊤∖↑N)); first done. *)
    iMod ("Hvs" with "[$Ha $HP]") as "[Hbc HQ]".
    wp_store.
    wp_apply (release_spec with  "[$Hlk $Htok Hbc Hb]").
    { iExists (v::ls); iFrame. }
    iIntros "_". by iApply "HΦ".
  Qed.

  Lemma popBag_spec (P : iProp Σ) (Q : val → iProp Σ) γ x :
    □ (∀ (X : gmultiset val) (y : val),
               bagContents γ ({[y]} ∪ X) ∗ P
               ={⊤}=∗ ▷ (bagContents γ X ∗ Q (SOMEV y))) -∗
    □ (bagContents γ ∅ ∗ P ={⊤}=∗ ▷ (bagContents γ ∅ ∗ Q NONEV)) -∗
    {{{ isBag γ x ∗ P }}}
      popBag x
    {{{ v, RET v; Q v }}}.
  Proof.
    iIntros "#Hvs1 #Hvs2".
    iIntros (Φ). iAlways. iIntros "[#Hbag HP] HΦ".
    unfold popBag. wp_rec.
    rewrite /isBag /bag_inv.
    iDestruct "Hbag" as (lk b γl) "[% #Hlk]"; simplify_eq/=.
    repeat wp_pure _.
    wp_apply (acquire_spec with "Hlk"). iIntros "[Htok Hb1]".
    iDestruct "Hb1" as (ls) "[Hb Ha]".
    wp_seq. wp_load. destruct ls as [|v ls]; simpl.
    - iMod ("Hvs2" with "[$Ha $HP]") as "[Hbc HQ]".
      repeat wp_pure _.
      wp_apply (release_spec with  "[$Hlk $Htok Hbc Hb]").
      { iExists []; iFrame. }
      iIntros "_". repeat wp_pure _. by iApply "HΦ".
    - iMod ("Hvs1" with "[$Ha $HP]") as "[Hbc HQ]".
      repeat wp_pure _. wp_store. do 2 wp_pure _.
      wp_apply (release_spec with  "[$Hlk $Htok Hbc Hb]").
      { iExists ls; iFrame. }
      iIntros "_". repeat wp_pure _. by iApply "HΦ".
  Qed.

End proof.

Typeclasses Opaque bagContents isBag.

Canonical Structure cg_bag `{!heapG Σ, !bagG Σ} : bag Σ :=
  {| is_bag := isBag;
     is_bag_persistent := isBag_persistent;
     bag_contents_timeless := bagContents_timeless;
     bag_contents_agree := bagContents_agree;
     bag_contents_update := bagContents_update;
     abstract_bag.newBag_spec := newBag_spec;
     abstract_bag.pushBag_spec := pushBag_spec;
     abstract_bag.popBag_spec := popBag_spec |}.

