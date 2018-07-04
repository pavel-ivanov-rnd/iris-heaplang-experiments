(** Concurrent bag specification from the HOCAP paper.
    "Modular Reasoning about Separation of Concurrent Data Structures"
    <http://www.kasv.dk/articles/hocap-ext.pdf>

Fine-grained implementation of a bag
*)
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import cmra agree frac.
From iris.heap_lang.lib Require Import lock spin_lock.
From iris_examples.hocap Require Import abstract_bag.
Set Default Proof Using "Type".

(** Fine-grained bag implementation using CAS *)
Definition newBag : val := λ: <>,
  ref NONE.
Definition pushBag : val := rec: "push" "b" "v" :=
  let: "oHead" := !"b" in
  if: CAS "b" "oHead" (SOME (ref ("v", "oHead")))
  then #()
  else "push" "b" "v".

Definition popBag : val := rec: "pop" "b" :=
  match: !"b" with
    NONE => NONE
  | SOME "l" =>
    let: "hd" := !"l" in
    let: "v" := Fst "hd" in
    let: "tl" := Snd "hd" in
    if: CAS "b" (SOME "l") "tl"
    then SOME "v"
    else "pop" "b"
  end.

Canonical Structure valmultisetC := leibnizC (gmultiset valC).
Class bagG Σ := BagG
{ bag_bagG :> inG Σ (prodR fracR (agreeR valmultisetC));
}.

(** Generic specification for the bag, using view shifts. *)
Section proof.
  Context `{heapG Σ, bagG Σ}.
  Variable N : namespace.

  Definition rown (l : loc) (v : val) :=
    (∃ q, l ↦{q} v)%I.
  Lemma rown_duplicate l v : rown l v -∗ rown l v ∗ rown l v.
  Proof. iDestruct 1 as (q) "[Hl Hl']". iSplitL "Hl"; iExists _; eauto. Qed.

  Fixpoint is_list (hd : val) (xs : list val) : iProp Σ :=
    match xs with
    | [] => ⌜hd = NONEV⌝%I
    | x::xs => (∃ (l : loc) (tl : val),
                   ⌜hd = SOMEV #l⌝ ∗ rown l (x, tl) ∗ is_list tl xs)%I
    end.

  Lemma is_list_unboxed hd xs :
    is_list hd xs -∗ ⌜val_is_unboxed hd⌝.
  Proof.
    destruct xs.
    - iIntros (->). done.
    - iIntros "Hl". iDestruct "Hl" as (?? ->) "_". done.
  Qed.

  Lemma is_list_duplicate hd xs : is_list hd xs -∗ is_list hd xs ∗ is_list hd xs.
  Proof.
    iInduction xs as [ | x xs ] "IH" forall (hd); simpl; eauto.
    iDestruct 1 as (l tl) "[% [Hro Htl]]"; simplify_eq.
    rewrite rown_duplicate. iDestruct "Hro" as "[Hro Hro']".
    iDestruct ("IH" with "Htl") as "[Htl Htl']".
    iSplitL "Hro Htl"; iExists _,_; iFrame; eauto.
  Qed.

  Lemma is_list_agree hd xs ys : is_list hd xs -∗ is_list hd ys -∗ ⌜xs = ys⌝.
  Proof.
    iInduction xs as [ | x xs ] "IH" forall (hd ys); simpl; eauto.
    - iIntros "%"; subst.
      destruct ys; eauto. simpl.
      iDestruct 1 as (? ?) "[% ?]". simplify_eq.
    - iDestruct 1 as (l tl) "(% & Hro & Hls)"; simplify_eq.
      destruct ys as [| y ys]; eauto. simpl.
      iDestruct 1 as (l' tl') "(% & Hro' & Hls')"; simplify_eq.
      iDestruct "Hro" as (q) "Hro".
      iDestruct "Hro'" as (q') "Hro'".
      iDestruct (mapsto_agree l' q q' (PairV x tl) (PairV y tl')
                with "Hro Hro'") as %?. simplify_eq/=.
      iDestruct ("IH" with "Hls Hls'") as %->. done.
                                                                             Qed.

  Definition bag_inv (γb : gname) (b : loc) : iProp Σ :=
    (∃ (hd : val) (ls : list val),
        b ↦ hd ∗ is_list hd ls ∗ own γb ((1/2)%Qp, to_agree (of_list ls)))%I.
  Definition is_bag (γb : gname) (x : val) :=
    (∃ (b : loc), ⌜x = #b⌝ ∗ inv N (bag_inv γb b))%I.
  Definition bag_contents (γb : gname) (X : gmultiset val) : iProp Σ :=
    own γb ((1/2)%Qp, to_agree X).

  Global Instance is_bag_persistent γb x : Persistent (is_bag γb x).
  Proof. apply _. Qed.
  Global Instance bag_contents_timeless γb X : Timeless (bag_contents γb X).
  Proof. apply _. Qed.

  Lemma bag_contents_agree γb X Y :
    bag_contents γb X -∗ bag_contents γb Y -∗ ⌜X = Y⌝.
  Proof.
    rewrite /bag_contents. apply bi.wand_intro_r.
    rewrite -own_op own_valid uPred.discrete_valid.
    f_equiv=> /=. rewrite pair_op.
    by intros [_ ?%agree_op_invL'].
  Qed.

  Lemma bag_contents_update γb X X' Y :
    bag_contents γb X ∗ bag_contents γb X' ==∗ bag_contents γb Y ∗ bag_contents γb Y.
  Proof.
    iIntros "[Hb1 Hb2]".
    iDestruct (bag_contents_agree with "Hb1 Hb2") as %<-.
    iMod (own_update_2 with "Hb1 Hb2") as "Hb".
    { rewrite pair_op frac_op'.
      assert ((1 / 2 + 1 / 2)%Qp = 1%Qp) as -> by apply Qp_div_2.
      by apply (cmra_update_exclusive (1%Qp, to_agree Y)). }
    iDestruct "Hb" as "[Hb1 Hb2]".
    rewrite /bag_contents. by iFrame.
  Qed.

  Lemma newBag_spec :
    {{{ True }}}
      newBag #()
    {{{ x γ, RET x; is_bag γ x ∗ bag_contents γ ∅ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    unfold newBag. wp_rec. iApply wp_fupd.
    wp_alloc r as "Hr".
    iMod (own_alloc (1%Qp, to_agree ∅)) as (γb) "[Ha Hf]"; first done.
    iMod (inv_alloc N _ (bag_inv γb r) with "[Ha Hr]") as "#Hinv".
    { iNext. iExists _,[]. simpl. iFrame. eauto. }
    iModIntro. iApply "HΦ".
    rewrite /is_bag /bag_contents. iFrame.
    iExists _. by iFrame "Hinv".
  Qed.

  Lemma pushBag_spec (P Q : iProp Σ) γ (x v : val)  :
    □ (∀ (X : gmultiset val), bag_contents γ X ∗ P
                     ={⊤∖↑N}=∗ ▷ (bag_contents γ ({[v]} ∪ X) ∗ Q)) -∗
    {{{ is_bag γ x ∗ P }}}
      pushBag x (of_val v)
    {{{ RET #(); Q }}}.
  Proof.
    iIntros "#Hvs".
    iIntros (Φ). iAlways. iIntros "[#Hbag HP] HΦ".
    unfold pushBag.
    iLöb as "IH". do 2 wp_rec.
    rewrite /is_bag.
    iDestruct "Hbag" as (b) "[% #Hinv]"; simplify_eq/=.
    repeat wp_pure _.
    wp_bind (! #b)%E.
    iInv N as (o ls) "[Ho [Hls >Hb]]" "Hcl".
    wp_load.
    iMod ("Hcl" with "[Ho Hls Hb]") as "_".
    { iNext. iExists _,_. iFrame. } clear ls.
    iModIntro. repeat wp_pure _.
    wp_alloc n as "Hn".
    wp_bind (CAS _ _ _).
    iInv N as (o' ls) "[Ho [Hls >Hb]]" "Hcl".
    iPoseProof (is_list_unboxed with "Hls") as "#>%".
    destruct (decide (o = o')) as [->|?].
    - wp_cas_suc.
      iMod ("Hvs" with "[$Hb $HP]") as "[Hb HQ]".
      iMod ("Hcl" with "[Ho Hn Hls Hb]") as "_".
      { iNext. iExists _,(v::ls). iFrame "Ho Hb".
        simpl. iExists _,_. iFrame. iSplit; eauto. by iExists 1%Qp. }
      iModIntro. wp_if_true. by iApply "HΦ".
    - wp_cas_fail.
      iMod ("Hcl" with "[Ho Hls Hb]") as "_".
      { iNext. iExists _,ls. by iFrame "Ho Hb". }
      iModIntro. wp_if_false.
      by iApply ("IH" with "HP [HΦ]").
  Qed.

  Lemma popBag_spec (P : iProp Σ) (Q : val → iProp Σ) γ x :
    □ (∀ (X : gmultiset val) (y : val),
               bag_contents γ ({[y]} ∪ X) ∗ P
               ={⊤∖↑N}=∗ ▷ (bag_contents γ X ∗ Q (SOMEV y))) -∗
    □ (bag_contents γ ∅ ∗ P ={⊤∖↑N}=∗ ▷ (bag_contents γ ∅ ∗ Q NONEV)) -∗
    {{{ is_bag γ x ∗ P }}}
      popBag x
    {{{ v, RET v; Q v }}}.
  Proof.
    iIntros "#Hvs1 #Hvs2".
    iIntros (Φ). iAlways. iIntros "[#Hbag HP] HΦ".
    unfold popBag.
    iLöb as "IH". wp_rec.
    rewrite /is_bag.
    iDestruct "Hbag" as (b) "[% #Hinv]"; simplify_eq/=.
    wp_bind (!#b)%E.
    iInv N as (o ls) "[Ho [Hls >Hb]]" "Hcl".
    wp_load.
    destruct ls as [|x ls]; simpl.
    - iDestruct "Hls" as %->.
      iMod ("Hvs2" with "[$Hb $HP]") as "[Hb HQ]".
      iMod ("Hcl" with "[Ho Hb]") as "_".
      { iNext. iExists _,[]. by iFrame. }
      iModIntro. repeat wp_pure _.
      by iApply "HΦ".
    - iDestruct "Hls" as (hd tl) "(% & Hhd & Hls)"; simplify_eq/=.
      rewrite rown_duplicate. iDestruct "Hhd" as "[Hhd Hhd']".
      rewrite is_list_duplicate. iDestruct "Hls" as "[Hls Hls']".
      iMod ("Hcl" with "[Ho Hb Hhd Hls]") as "_".
      { iNext. iExists _,(x::ls). simpl; iFrame; eauto.
        iExists _, _; eauto. by iFrame. }
      iModIntro. repeat wp_pure _.
      iDestruct "Hhd'" as (q) "Hhd".
      wp_load. repeat wp_pure _.
      wp_bind (CAS _ _ _).
      iInv N as (o' ls') "[Ho [Hls >Hb]]" "Hcl".
      destruct (decide (o' = (InjRV #hd))) as [->|?].
      + wp_cas_suc.
        (* The list is still the same *)
        rewrite (is_list_duplicate tl). iDestruct "Hls'" as "[Hls' Htl]".
        iAssert (is_list (InjRV #hd) (x::ls)) with "[Hhd Hls']" as "Hls'".
        { simpl. iExists hd,tl. iFrame; iSplit; eauto.
          iExists q. iFrame. }
        iDestruct (is_list_agree with "Hls Hls'") as %?. simplify_eq.
        iClear "Hls'".
        iDestruct "Hls" as (hd' tl') "(% & Hro' & Htl')". simplify_eq.
        iMod ("Hvs1" with "[$Hb $HP]") as "[Hb HQ]".
        iMod ("Hcl" with "[Ho Htl Hb]") as "_".
        { iNext. iExists _,ls. by iFrame "Ho Hb". }
        iModIntro. wp_if_true. by iApply "HΦ".
      + wp_cas_fail.
        iMod ("Hcl" with "[Ho Hls Hb]") as "_".
        { iNext. iExists _,ls'. by iFrame "Ho Hb". }
        iModIntro. wp_if_false.
        by iApply ("IH" with "HP [HΦ]").
  Qed.
End proof.

Typeclasses Opaque bag_contents is_bag.

Canonical Structure cg_bag `{!heapG Σ, !bagG Σ} : bag Σ :=
  {| abstract_bag.is_bag := is_bag;
     abstract_bag.is_bag_persistent := is_bag_persistent;
     abstract_bag.bag_contents_timeless := bag_contents_timeless;
     abstract_bag.bag_contents_agree := bag_contents_agree;
     abstract_bag.bag_contents_update := bag_contents_update;
     abstract_bag.newBag_spec := newBag_spec;
     abstract_bag.pushBag_spec := pushBag_spec;
     abstract_bag.popBag_spec := popBag_spec |}.
