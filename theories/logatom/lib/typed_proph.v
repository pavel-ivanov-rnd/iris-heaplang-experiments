From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

(** A library defining a typed wrapper for prophecy variables. *)

Record TypedProphSpec : Type := mkTypedProphSpec
 { typed_proph_spec_type     : Set
 ; typed_proph_spec_from_val : val → option typed_proph_spec_type
 ; typed_proph_spec_to_val   : typed_proph_spec_type → val
 ; typed_proph_spec_inj_prop :
     ∀ x, typed_proph_spec_from_val (typed_proph_spec_to_val x) = Some x }.

Record TypedProph `{!heapG Σ} : Type := mkTypedProph
  { typed_proph_type             : Set
  ; typed_proph_from_val         : val → option typed_proph_type
  ; typed_proph_to_val           : typed_proph_type → val
  ; typed_proph_inj_prop         :
      ∀ x, typed_proph_from_val (typed_proph_to_val x) = Some x
  ; typed_proph_prop             : proph_id → list (val * typed_proph_type) → iProp Σ
  ; typed_proph_prop_excl        : (∀ p l1 l2, typed_proph_prop p l1 ∗ typed_proph_prop p l2 -∗ False)%I
  ; typed_proph_wp_new_proph s E :
      {{{ True }}}
        NewProph @ s; E
      {{{ pvs p, RET (LitV (LitProphecy p)); typed_proph_prop p pvs }}}%I
  ; typed_proph_wp_resolve s E e Φ p v w pvs :
      Atomic StronglyAtomic e →
      to_val e = None →
      w = typed_proph_to_val v →
      typed_proph_prop p pvs -∗
      WP e @ s; E {{ r, ∀ pvs', ⌜pvs = (r, v)::pvs'⌝ -∗ typed_proph_prop p pvs' -∗ Φ r }} -∗
      WP Resolve e (Val $ LitV $ LitProphecy p) (Val w) @ s; E {{ Φ }} }.

Fixpoint process_prophecy {A} (f : val → option A) (vs : list (val * val)) : list (val * A) :=
  match vs with
  | []        => []
  | (v,w)::vs =>
    match f w with
    | None   => []
    | Some w => (v,w) :: process_prophecy f vs
    end
   end.

Definition make_TypedProph `{!heapG Σ} (S : TypedProphSpec) : TypedProph.
Proof.
  apply mkTypedProph with
      (typed_proph_spec_type S)
      (typed_proph_spec_from_val S)
      (typed_proph_spec_to_val S)
      (λ p l, ∃ vs, proph p vs ∗ ⌜l = process_prophecy (typed_proph_spec_from_val S) vs⌝)%I.
  - exact (typed_proph_spec_inj_prop S).
  - iIntros (p l1 l2) "[H1 H2]".
    iDestruct "H1" as (vs1) "[H1 _]".
    iDestruct "H2" as (vs2) "[H2 _]".
    iApply (proph_exclusive with "H1 H2").
  - iIntros (s E Φ). iIntros "!> _ HΦ". wp_apply wp_new_proph; first done.
    iIntros (pvs p) "Hp". iApply "HΦ". iExists _. by iFrame.
  - iIntros (s E e Φ p v w pvs H1 H2 H3) "H HΦ". iDestruct "H" as (vs) "[Hp ->]".
    wp_apply (wp_resolve with "Hp"); first done. iApply (wp_wand with "HΦ").
    iIntros (vΦ) "H". iIntros (pvs' ->) "Hp". iApply "H".
    + iPureIntro. by rewrite H3 /= (typed_proph_spec_inj_prop S).
    + iExists _. by iFrame.
Qed.

(** Instantiation of the interface with booleans. *)

Section bool_proph.
  Definition bool_from_val (v : val) : option bool :=
    match v with
    | LitV(LitBool b) => Some b
    | _               => None
    end.

  Definition bool_to_val (b : bool) : val := LitV(LitBool b).

  Lemma bool_inj_prop : ∀ (b : bool), bool_from_val (bool_to_val b) = Some b.
  Proof. done. Qed.

  Definition BoolProph : TypedProphSpec :=
    mkTypedProphSpec bool bool_from_val bool_to_val bool_inj_prop.
End bool_proph.

Definition BoolTypedProph `{!heapG Σ} := make_TypedProph BoolProph.

(** Instantiation of the interface with integers. *)

Section int_proph.
  Definition int_from_val (v : val) : option Z :=
    match v with
    | LitV(LitInt i) => Some i
    | _              => None
    end.

  Definition int_to_val (i : Z) : val := LitV(LitInt i).

  Lemma int_inj_prop : ∀ (i : Z), int_from_val (int_to_val i) = Some i.
  Proof. done. Qed.

  Definition IntProph : TypedProphSpec :=
    mkTypedProphSpec Z int_from_val int_to_val int_inj_prop.
End int_proph.

Definition IntTypedProph `{!heapG Σ} := make_TypedProph IntProph.
