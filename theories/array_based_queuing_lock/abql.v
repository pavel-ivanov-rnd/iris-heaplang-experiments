(** An implementation and safety proof of the Array-Based Queuing Lock (ABQL).

    This data-structure was included in the VerifyThis 2018 program verification
    competition [1]. The example is also described in the chapter "Case study:
    The Array-Based Queuing Lock" in the Iris lecture notes [2].

    1: https://hal.inria.fr/hal-01981937/document
    2: https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf#section.10
 *)

From iris.program_logic Require Export weakestpre.
From stdpp Require Export list.
From iris.heap_lang Require Export notation lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import excl auth gset frac.
From iris_string_ident Require Import ltac2_string_ident.

Section abql_code.

  (* The lock consists of a natural number, an array of booleans, and the length
     of the array. The number is the next ticket available and the array
     contains false at every entry, except for one, which contains true. *)
  Definition newlock : val :=
    λ: "cap", let: "array" := AllocN "cap" #false in
              ("array" +ₗ #0%nat) <- #true ;; ("array", ref #0, "cap").

  Definition wait_loop : val :=
    rec: "spin" "lock" "ticket" :=
      let: "array" := Fst (Fst "lock") in (* Get the first element of the triple *)
      let: "idx" := "ticket" `rem` (Snd "lock") in (* Snd "Lock" gets the third element of the triple *)
      if: ! ("array" +ₗ "idx") then #() else ("spin" "lock" "ticket").

  (* To acquire the lock we first take the next ticket using FAA. We then spin
     on the index in the array corresponding to the ticket (the tickets number mod
     the length of the array) until that index becomes true. *)
  Definition acquire : val :=
    λ: "lock", let: "next" := Snd (Fst "lock") in
               let: "ticket" := FAA "next" #1%nat in
               wait_loop "lock" "ticket" ;;
               "ticket".

  (* To release the lock we set the spot in the array corresponding to our
     ticket to false and set the next spot (possibly wrapping around the end of the
     list) to true. *)
  Definition release : val :=
    λ: "lock" "o", let: "array" := Fst (Fst "lock") in
                   let: "cap" := Snd "lock" in
                   "array" +ₗ ("o" `rem` "cap") <- #false ;;
                   "array" +ₗ (("o" + #1) `rem` "cap") <- #true.

End abql_code.

Open Scope Z_scope.

Section algebra.

  (* The carrier of the resource algebra is pairs of natural numbers. The first
     number represents how many invitations we have and the second how many
     invitations exists in total. *)
  Definition sumRAT : Type := nat * nat.

  Canonical Structure sumRAC := leibnizO sumRAT.

  Instance sumRAop : Op sumRAT :=
    λ a b, match a, b with
             (x, n), (y, m) => (x + y, n `min` m)%nat
           end.

  Instance sumRAValid : Valid sumRAT :=
    λ a, match a with
           (x, n) => (x ≤ n)%nat
         end.

  Instance sumRACore : PCore sumRAT :=
    λ _, None.

  (* We need these auxiliary lemmas in the proof below.
     We need the type annotation to guide the type inference. *)
  Lemma sumRA_op_second a b n: ((a, n) : sumRAT) ⋅ ((b, n) : sumRAT) = (((a + b)%nat, n) : sumRAT).
  Proof.
    unfold op. unfold sumRAop. rewrite Nat.min_id. reflexivity.
  Qed.

  Lemma sumRA_op a b n m: ((a, n) : sumRAT) ⋅ ((b, m) : sumRAT) = ((a + b, n `min` m)%nat : sumRAT).
  Proof.
    unfold op. unfold sumRAop. reflexivity.
  Qed.

  (* If (a, n) is valid ghost state then we can conclude that a ≤ n *)
  Lemma sumRA_valid (a n : nat): ✓((a, n) : sumRAT) ↔ (a ≤ n)%nat.
  Proof.
    (* Both cases below could also be proved using `auto` *)
    split; unfold valid; simpl; intros; assumption.
  Qed.

  Definition sumRA_mixin : RAMixin sumRAT.
  Proof.
    split.
    - intros x. by unfold Proper.
    - intros x y z -> ->. exists z. done.
    - by unfold Proper.
    - intros x y z. destruct x, y, z.
      repeat rewrite sumRA_op. rewrite Nat.add_assoc. rewrite Nat.min_assoc. reflexivity.
    - intros x y. destruct x, y.
      repeat rewrite sumRA_op. rewrite Nat.add_comm. rewrite Nat.min_comm. reflexivity.
    - intros x y. rewrite /pcore /sumRACore. intros H. inversion H.
    - intros x y. rewrite /pcore /sumRACore. intros H. inversion H.
    - rewrite /pcore /sumRACore. intros x y z _ H. inversion H.
    - intros [n c] [n' c'].
      repeat rewrite sumRA_op. intros V%Nat.min_glb_iff.
      apply sumRA_valid. omega.
  Qed.

  Canonical Structure sumRA := discreteR sumRAT sumRA_mixin.

  Global Instance sumRA_cmra_discrete : CmraDiscrete sumRA.
  Proof. apply discrete_cmra_discrete. Qed.

  Class sumG Σ := SumG { sum_inG :> inG Σ sumRA }.
  Definition sumΣ : gFunctors := #[GFunctor sumRA].

  Instance subG_sumΣ {Σ} : subG sumΣ Σ → sumG Σ.
  Proof. solve_inG. Qed.

End algebra.

Section array_model.

  Context `{!heapG Σ}.

  Definition is_array (array : loc) (xs : list bool) : iProp Σ :=
    let vs := (fun b => # (LitBool b)) <$> xs
    in array ↦∗ vs.

  (* Create a Coq list with lenght n, a single true at index i, and false everywhere else *)
  Definition list_with_one (length index : nat) : list bool :=
    <[index:=true]> (replicate length false).

  Lemma wp_load_offset_len s E l off vs :
    (off < length vs)%nat ->
    {{{ ▷ l ↦∗ vs }}} ! #(l +ₗ off) @ s; E {{{ v, RET v; ⌜vs !! off = Some v⌝ ∗ l ↦∗ vs }}}.
  Proof.
    iIntros (Hlen Φ) "Hl HΦ".
    apply lookup_lt_is_Some_2 in Hlen.
    destruct Hlen as (v & Hlookup).
    iDestruct (update_array with "Hl") as "[Hl1 Hl2]"; first done.
    iApply (wp_load with "Hl1"). iIntros "!> Hl1". iApply "HΦ".
    iSplit. { done. }
    iDestruct ("Hl2" $! v) as "Hl2". rewrite list_insert_id; last done.
    iApply "Hl2". iApply "Hl1".
  Qed.

  Lemma wp_store_offset_len s E l (off : nat) vs (v : val) :
    (off < length vs)%nat ->
    {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ <[off:=v]> vs }}}.
  Proof.
    iIntros (Hlen Φ) ">Hl HΦ".
    iApply (wp_store_offset _ _ _ _ vs _ with "Hl").
    { apply lookup_lt_is_Some_2. assumption. }
    iAssumption.
  Qed.

  Lemma array_store E (i : nat) (v : bool) arr (xs : list bool) :
    {{{ ⌜(i < length xs)%nat⌝ ∗ ▷ is_array arr xs }}}
      #(arr +ₗ i) <- #v
    @ E {{{ RET #(); is_array arr (<[i:=v]>xs) }}}.
  Proof.
    iIntros (ϕ) "[% isArr] Post".
    unfold is_array.
    iApply (wp_store_offset_len with "isArr").
    { rewrite fmap_length. assumption. }
    rewrite (list_fmap_insert ((λ b : bool, #b) : bool -> val) xs i v).
    iAssumption.
  Qed.

  Lemma insert_list_with_one (i : nat) l :
    <[i:=false]> (list_with_one l i) = replicate l false.
  Proof.
    unfold list_with_one.
    rewrite list_insert_insert. rewrite insert_replicate. reflexivity.
  Qed.

  (* The repeat code behaves similar to the replicate function *)
  Lemma array_repeat (b : bool) (n : nat) :
    {{{ ⌜(0 < n)%nat⌝ }}} AllocN #n #b {{{ arr, RET #arr; is_array arr (replicate n b) }}}.
  Proof.
    iIntros (ϕ) "% Post".
    apply inj_lt in a.
    iApply wp_allocN; try done.
    iNext. iIntros (l) "[lPts _]".
    iApply "Post".
    unfold is_array.
    rewrite Nat2Z.id.
    rewrite -> fmap_replicate.
    iAssumption.
  Qed.

End array_model.

(** The CMRAs we need. *)

Class alockG Σ :=
  tlock_G :> inG Σ (authR (prodUR (optionUR (exclR natO)) (gset_disjUR nat))).

Definition alockΣ : gFunctors :=
  #[ GFunctor (authR (prodUR (optionUR (exclR natO)) (gset_disjUR nat))) ].

Instance subG_alockΣ Σ : subG alockΣ Σ → alockG Σ.
Proof. solve_inG. Qed.

Class atokenG Σ :=
  ttoken_G :> inG Σ ((prodR (optionUR (exclR natO)) (optionUR (exclR natO)))).

(* Instead of `natO` we could have just used `unitC` here but that did not make Coq happy. *)
Definition atokenΣ : gFunctors :=
  #[ GFunctor ((prodR (optionUR (exclR natO)) (optionUR (exclR natO)))) ].

Instance subG_atokenΣ Σ : subG atokenΣ Σ → atokenG Σ.
Proof. solve_inG. Qed.

Section abql_model.

  Context `{!heapG Σ, !alockG Σ, !sumG Σ, !atokenG Σ}.

  Definition both (κ : gname) : iProp Σ := (own κ (Excl' 1%nat, Excl' 1%nat)).

  Definition left (κ : gname) : iProp Σ := (own κ (Excl' 1%nat, None)).

  Definition right (κ : gname) : iProp Σ := (own κ (None, Excl' 1%nat)).

  Definition invitation (ι : gname) (x : nat) (cap : nat) : iProp Σ :=
    own ι ((x, cap) : sumRA)%I.

  (* The name of a lock. *)
  Definition lockN (l : val) := nroot .@ "lock" .@ l.

  Definition issued (γ : gname) (x : nat) : iProp Σ := own γ (◯ (ε, GSet {[ x ]}))%I.

  (* The lock invariant *)
  Definition lock_inv (γ ι κ : gname) (arr : loc) (cap : nat) (nextPtr : loc) (R : iProp Σ) : iProp Σ :=
    (∃ (o i : nat) (xs : list bool), (* o: who may acquire the lock, i: nr of invitations in lock *)
        nextPtr ↦ #(o + i)%nat ∗
        is_array arr xs ∗
        ⌜length xs = cap⌝ ∗
        invitation ι i cap ∗ (* The invitations currently owned by the lock. *)
        own γ (● (Excl' o, GSet (set_seq o i))) ∗
        ((own γ (◯ (Excl' o, GSet ∅)) ∗ R ∗ both κ ∗ ⌜xs = list_with_one cap (Nat.modulo o cap)⌝) ∨
         (* Lock is open, R belongs to lock *)
         (issued γ o ∗ right κ ∗ ⌜xs = replicate cap false⌝) ∨
         (* Lock is in the process of being released. *)
         (issued γ o ∗ left κ ∗ ⌜xs = list_with_one cap (Nat.modulo o cap)⌝) (* Lock is locked *)
        ))%I.

  (* The lock predicate *)
  (* cap is the length or the capacity of the lock *)
  Definition is_lock γ ι κ (lock : val) (cap : nat) P :=
    (∃ (arr : loc) (nextPtr : loc),
        ⌜lock = (#arr, #nextPtr, #cap)%V⌝ ∗
        ⌜(0 < cap)%nat⌝ ∗
        inv (lockN lock) (lock_inv γ ι κ arr cap nextPtr P))%I.

  Definition locked (γ κ : gname) (o : nat) : iProp Σ := (own γ (◯ (Excl' o, GSet ∅)) ∗ right κ)%I.

End abql_model.

Section abql_spec.

  Context `{!heapG Σ, !alockG Σ, !sumG Σ, !atokenG Σ} (N : namespace).

  Global Instance is_lock_persistent γ ι κ lk n R : Persistent (is_lock γ ι κ lk n R).
  Proof. apply _. Qed.

  Global Instance locked_timeless γ κ o : Timeless (locked γ o κ).
  Proof. apply _. Qed.

  Lemma locked_exclusive (γ κ : gname) o o' : locked γ κ o -∗ locked γ κ o' -∗ False.
  Proof.
    iIntros "[H1 _] [H2 _]".
    iDestruct (own_valid_2 with "H1 H2") as %[[] _].
  Qed.

  (* Only one thread can know the exact value of `o`. *)
  Lemma know_o_exclusive γ o o' :
    own γ (◯ (Excl' o, GSet ∅)) -∗ own γ (◯ (Excl' o', GSet ∅)) -∗ False.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %[[]].
  Qed.

  Lemma left_left_false (κ : gname) : left κ -∗ left κ -∗ False.
  Proof.
    iIntros "L L'". iCombine "L L'" as "L".
    iDestruct (own_valid with "L") as %[Hv _].
    inversion Hv.
  Qed.

  Lemma right_right_false (κ : gname) : right κ -∗ right κ -∗ False.
  Proof.
    iIntros "R R'". iCombine "R R'" as "R".
    iDestruct (own_valid with "R") as %[_ Hv].
    inversion Hv.
  Qed.

  Lemma both_split (κ : gname) : both κ -∗ (left κ ∗ right κ).
  Proof.
    iIntros "Both". iApply own_op. iFrame.
  Qed.

  Lemma left_right_to_both (κ : gname) : left κ -∗ right κ -∗ both κ.
  Proof.
    iIntros "L R". iCombine "L" "R" as "?". iFrame.
  Qed.

  Lemma valid_ticket_range (γ : gname) (x o i : nat) :
    own γ (◯ (ε, GSet {[ x ]})) -∗ own γ (● (Excl' o, GSet (set_seq o i)))
        -∗ ⌜o ≤ x < o + i⌝ ∗ own γ (◯ (ε, GSet {[ x ]})) ∗ own γ (● (Excl' o, GSet (set_seq o i))).
  Proof.
    iIntros "P O".
    iDestruct (own_valid_2 with "O P") as %[[_ xIncl%gset_disj_included]%prod_included Hv]%auth_both_valid.
    iFrame. iPureIntro.
    apply elem_of_subseteq_singleton, elem_of_set_seq in xIncl.
    lia.
  Qed.

  Lemma ticket_i_gt_zero (γ : gname) (o i : nat) :
    own γ (◯ (ε, GSet {[ o ]})) -∗ own γ (● (Excl' o, GSet (set_seq o i)))
      -∗ ⌜0 < i⌝ ∗ own γ (◯ (ε, GSet {[ o ]})) ∗ own γ (● (Excl' o, GSet (set_seq o i))).
  Proof.
    iIntros "P O".
    iDestruct (own_valid_2 with "O P") as %HV%auth_both_valid.
    iFrame. iPureIntro.
    destruct HV as [[_ H%gset_disj_included]%prod_included _].
    apply elem_of_subseteq_singleton, set_seq_len_pos in H.
    lia.
  Qed.

  Lemma invitation_cap_bound γ i cap :
    invitation γ i cap -∗ ⌜i ≤ cap⌝ ∗ invitation γ i cap.
  Proof.
    iIntros "I".
    iDestruct (own_valid _ ((i, cap) : sumRA) with "I") as %H.
    iFrame. iPureIntro. apply inj_le. assumption.
  Qed.

  Lemma invitation_split γ (i cap : nat) :
    ⌜0 < i⌝ -∗ invitation γ i cap -∗ invitation γ 1 cap ∗ invitation γ (i - 1) cap.
  Proof.
    iIntros "% I".
    iDestruct (own_valid with "I") as %H.
    rewrite -own_op (comm op) sumRA_op_second.
    rewrite Nat.sub_add; auto; lia.
  Qed.

  Lemma newlock_spec (R : iProp Σ) (cap : nat) :
    {{{ R ∗ ⌜(0 < cap)%nat⌝ }}}
      newlock (#cap)
    {{{ lk γ ι κ, RET lk; (is_lock γ ι κ lk cap R) ∗ invitation ι cap cap }}}.
  Proof.
    iIntros (Φ) "[Pre %] Post".
    wp_lam.
    wp_apply array_repeat. done.
    iIntros (arr) "isArr".
    wp_pures.
    wp_apply (array_store with "[$isArr]"); first by rewrite replicate_length.
    iIntros "isArr".
    (* We allocate the ghost states for the tickets and value of o. *)
    iMod (own_alloc (● (Excl' 0%nat, GSet ∅) ⋅ ◯ (Excl' 0%nat, GSet ∅))) as (γ) "[Hγ Hγ']".
    { by apply auth_both_valid. }
    (* We allocate the ghost state for the invitations. *)
    iMod (own_alloc (((cap, cap) : sumRA) ⋅ (0%nat, cap))) as (ι) "[Hinvites HNoInvites]".
    { rewrite sumRA_op_second Nat.add_0_r. apply (sumRA_valid cap cap). auto. }
    (* We allocate the ghost state for the lock state indicatior. *)
    iMod (own_alloc ((Excl' 1%nat, Excl' 1%nat))) as (κ) "Both". { done. }
    wp_alloc p as "pts".
    iMod (inv_alloc _ _ (lock_inv γ ι κ arr cap p R) with "[-Post Hinvites]").
    { iNext. rewrite /lock_inv. iExists 0%nat, 0%nat, (<[0%nat:=true]> (replicate cap false)).
      iFrame. iSplitR.
      - rewrite insert_length. rewrite replicate_length. done.
      - iLeft. iFrame. rewrite Nat.mod_0_l. done. omega. }
    wp_pures.
    iApply "Post".
    rewrite /is_lock. iFrame.
    iExists _, _. auto.
  Qed.

  Lemma rem_mod_eq (x y : nat) : (0 < y)%nat -> x `rem` y = (x `mod` y)%nat.
  Proof.
    intros Hpos. rewrite Z2Nat_inj_mod Z.rem_mod_nonneg; omega.
  Qed.

  Lemma minus_plus_eq a b c : a - b = c -> a = c + b.
  Proof. omega. Qed.

  Lemma mod_fact_Z t o cap : 0 < cap -> o <= t -> t < o + cap -> t `mod` cap = o `mod` cap -> t = o.
  Proof.
    intros LeqCap SLeqX XLeqSCap ModEq.
    apply Z.lt_eq_cases in SLeqX.
    destruct SLeqX as [oLeq | ?]; last done.
    destruct (decide (cap = 0)) as [-> | Hcap]; first inversion LeqCap.
    apply Z.lt_gt in LeqCap.
    remember (t `mod` cap) as r.
    rewrite (Zmod_eq _ _ LeqCap) in Heqr.
    symmetry in Heqr.
    apply minus_plus_eq in Heqr.
    rewrite (Zmod_eq _ _ LeqCap) in ModEq.
    symmetry in ModEq.
    apply minus_plus_eq in ModEq.
    rewrite Heqr ModEq in XLeqSCap.
    rewrite Heqr ModEq in oLeq.
    apply Zplus_lt_reg_l in oLeq.
    apply Z.gt_lt in LeqCap.
    apply (Z.mul_lt_mono_pos_r _ _ _ LeqCap) in oLeq.
    rewrite <- Z.add_assoc in XLeqSCap.
    apply Zplus_lt_reg_l in XLeqSCap.
    replace (o `div` cap * cap + cap) with ((1 + o `div` cap) * cap) in XLeqSCap.
    - apply (Z.mul_lt_mono_pos_r _ _ _ LeqCap) in XLeqSCap. omega.
    - by rewrite Z.mul_comm -Zred_factor2 Z.add_comm Z.mul_comm.
  Qed.

  Lemma mod_fact (t o i cap : nat) :
    0%nat < cap -> o <= t -> t < o + i -> i <= cap
      -> (t `mod` cap = o `mod` cap -> t = o)%nat.
  Proof.
    intros LeqCap SLeqX XLeqSi ILeqCap ModEq.
    assert (XLeqSCap: t < o + cap). omega.
    apply inj_eq in ModEq.
    do 2 rewrite Z2Nat_inj_mod in ModEq.
    apply Nat2Z.inj.
    apply (mod_fact_Z _ _ cap LeqCap SLeqX XLeqSCap ModEq).
  Qed.

  Lemma nth_list_with_one (n a b : nat) :
    (list_with_one n a) !! b = Some true -> a = b.
  Proof.
    rewrite /list_with_one.
    by intros [[Eq] | [_ [[=] _]%lookup_replicate_1]]%list_lookup_insert_Some.
  Qed.

  Lemma wait_loop_spec γ ι κ lk cap t R :
    {{{ is_lock γ ι κ lk cap R ∗ issued γ t }}}
      wait_loop lk #t
    {{{ RET #(); locked γ κ t ∗ R }}}.
  Proof.
    iIntros (ϕ) "(Lock & Ticket) Post".
    (* Since `wait_loop` invokes itself recursively we use Löb *)
    iLöb as "IH".
    wp_lam. wp_let.
    iDestruct "Lock" as (arr nextPtr) "(-> & %capPos & #LockInv)".
    wp_pures.
    wp_bind (! _)%E.
    iInv (lockN (#arr, #nextPtr, #(cap))) as (o i xs) "(>nextPts & isArr & >%lenEq & >Inv & Auth & Part)" "Close".
    rewrite /is_array rem_mod_eq //.
    wp_apply (wp_load_offset_len _ _ arr _ ((fun b => # (LitBool b)) <$> xs) with "isArr").
    { rewrite fmap_length. subst. apply Nat.mod_upper_bound. omega. }
    iIntros (v) "[%eqLookup isArr]".
    apply list_lookup_fmap_inv in eqLookup as (x & -> & xsLookup).
    destruct x.
    - rewrite /issued.
      iDestruct (valid_ticket_range with "Ticket Auth") as "([% %] & Ticket & Auth)".
      iDestruct (invitation_cap_bound with "Inv") as "(% & Inv)".
      (* We now destruct the three cases that the lock can be in. *)
      iDestruct "Part" as "[(Ho & Hr & Both & %xsEq) | [(Ticket2 & Right & %xsEq) | (Ticket2 & Left & %xsEq)]]".
      * (* The case where the lock is currently open. *)
        rewrite xsEq in xsLookup.
        apply nth_list_with_one in xsLookup.
        assert (t = o) as tEqO. { apply inj_lt in capPos. apply (mod_fact _ _ i (cap)); auto. }
        rewrite tEqO.
        iDestruct (both_split with "Both") as "[Left Right]".
        iMod ("Close" with "[nextPts isArr Inv Auth Ticket Left]") as "_".
        { iNext. iExists o, i, (list_with_one cap (o `mod` cap)).
          rewrite /is_array xsEq. iFrame.
          iSplit.
          - by rewrite /list_with_one insert_length replicate_length.
          - iRight. iRight. iFrame. done. }
        iModIntro. wp_pures. iApply "Post". iFrame.
      * (* The case where the lock is in the clopen state. In this state all the
           indices in the array are false and hence we can not possibly have
           read a true in the array. *)
        rewrite xsEq in xsLookup.
        apply lookup_replicate_1 in xsLookup as [[=] _].
      * (* The case where the lock is closed. *)
        rewrite xsEq in xsLookup. apply nth_list_with_one in xsLookup.
        assert (t = o) as ->. { apply inj_lt in capPos. apply (mod_fact _ _ i (cap)); auto. }
        iDestruct (own_valid_2 with "Ticket Ticket2") as % [_ ?%gset_disj_valid_op].
        set_solver.
    - iMod ("Close" with "[nextPts isArr Inv Auth Part]") as "_".
      { iNext. iExists o, i, xs. iFrame. auto. }
      iModIntro. wp_pures. iApply ("IH" with "[LockInv] Ticket").
      { iExists arr, nextPtr. auto. }
      done.
  Qed.

  Lemma acquire_spec γ ι κ lk cap R :
    {{{ is_lock γ ι κ lk cap R ∗ invitation ι 1 cap}}}
      acquire lk
    {{{ t, RET #t; locked γ κ t ∗ R }}}.
  Proof.
    iIntros (ϕ) "[#IsLock Invitation] Post".
    iPoseProof "IsLock" as (arr nextPtr) "(-> & % & LockInv)".
    wp_lam. wp_pures. wp_bind (FAA _ _).
    iInv (lockN (#arr, #nextPtr, #cap)) as (o i xs) "(>nextPts & psPts & >% & >Invs & >Auth & np)" "Close".
    wp_faa.
    iMod (own_update with "Auth") as "[Auth Hofull]".
    { eapply auth_update_alloc, prod_local_update_2.
      eapply (gset_disj_alloc_empty_local_update _ {[ (o + i)%nat ]}).
      apply (set_seq_S_end_disjoint o). }
    iMod ("Close" with "[-Post Hofull]") as "_".
    { iNext. rewrite /lock_inv. iExists o, (i+1)%nat, xs. iFrame.
      iSplitL "nextPts".
      { repeat rewrite Nat2Z.inj_add. by rewrite Z.add_assoc. }
      iSplit; first done.
      iSplitL "Invitation Invs".
      { rewrite /invitation -sumRA_op_second own_op. iFrame. }
      by rewrite -(set_seq_S_end_union_L) Nat.add_1_r. }
    iModIntro.
    wp_let.
    wp_apply (wait_loop_spec γ ι κ (#arr, #nextPtr, #cap)%V cap (o + i)%nat R with "[Hofull]").
    { rewrite /issued. by iFrame. }
    iIntros "[locked Res]". wp_seq. iApply "Post". iFrame.
  Qed.

  Lemma frame_update_lemma_discard_ticket o i :
    ● (Excl' o, GSet (set_seq o i)) ⋅ (◯ (Excl' o%nat, GSet ∅) ⋅ ◯ (ε, GSet {[o]})) ~~>
    ● (Excl' (o + 1)%nat, GSet (set_seq (o + 1)%nat (i - 1)%nat)) ⋅ (◯ (Excl' (o + 1)%nat, GSet ∅)).
  Proof.
    rewrite -auth_frag_op -pair_op right_id left_id.
    apply auth_update.
    destruct i.
    - apply local_update_total_valid.
      intros _ _ [_ H%gset_disj_included]%prod_included.
      set_solver.
    - apply prod_local_update; simpl.
      * apply option_local_update, exclusive_local_update. done.
      * rewrite Nat.sub_0_r Nat.add_1_r -gset_op_union -gset_disj_union.
        apply gset_disj_dealloc_empty_local_update.
        apply set_seq_S_start_disjoint.
  Qed.

  Lemma release_spec γ ι κ lk cap o R :
    {{{ is_lock γ ι κ lk cap R ∗ locked γ κ o ∗ R }}}
      release lk #o
    {{{ RET #(); invitation ι 1 cap }}}.
  Proof.
    iIntros (ϕ) "(#IsLock & [Locked Right] & R) Post".
    iPoseProof "IsLock" as (arr nextPtr) "(-> & % & LockInv)".
    wp_lam. wp_pures.
    (* Focus the store such that we can open the invariant. *)
    wp_bind (_ <- _)%E.
    iInv (lockN (#arr, #nextPtr, #cap)) as (o' i xs) "(>nextPts & arrPts & >%lenEq & >Invs & >Auth & Part)" "Close".
    (* We want to show that o and o' are equal. We know this from the loked γ o ghost state. *)
    iDestruct (own_valid_2 with "Auth Locked") as
      %[[<-%Excl_included%leibniz_equiv _]%prod_included _]%auth_both_valid.
    rewrite rem_mod_eq //.
    iApply (array_store with "[arrPts]").
    { iFrame. iPureIntro. rewrite lenEq. apply Nat.mod_upper_bound. omega. }
    iModIntro. iIntros "psPts".
    iDestruct "Part" as "[(Locked' & _ & Both & _) | [(_ & Right' & _) | (Issued & Left & %xsEq)]]".
    { iDestruct (know_o_exclusive with "Locked Locked'") as %[]. }
    { iDestruct (right_right_false with "Right Right'") as %[]. }
    iMod ("Close" with "[nextPts Invs Auth psPts Issued Right]") as "_".
    { iNext. iExists o, i, (<[(o `mod` cap)%nat:=false]> xs).
      rewrite insert_length.
      iFrame. iSplit; first done.
      iRight. iLeft. iFrame. iPureIntro. subst.
      rewrite -> xsEq at 2.
      by rewrite insert_list_with_one. }
    clear xsEq lenEq xs i.
    iModIntro. wp_pures.
    rewrite -(Nat2Z.inj_add o 1).
    iInv (lockN (#arr, #nextPtr, #cap)) as (o' i xs) "(>nextPts & arrPts & >% & >Invs & >Auth & Part)" "Close".
    (* We destruct the disjunction in the lock invariant. We know that we are in
       the half-locked state so the first and third case results in
       contradictions. *)
    iDestruct "Part" as "[(>Locked' & _ & Both & _) | [(Issued & Right & >%xsEq) | (Issued & >Left' & Eq)]]".
    * iDestruct (know_o_exclusive with "Locked Locked'") as "[]".
    (* This is the case where the lock is clopen, that is, the actual state
       of the lock. *)
    * iDestruct (own_valid_2 with "Auth Locked") as
          %[[<-%Excl_included%leibniz_equiv _]%prod_included _]%auth_both_valid.
      rewrite rem_mod_eq //.
      iApply (wp_store_offset_len with "arrPts").
      { rewrite fmap_length. rewrite H0. apply Nat.mod_upper_bound. omega. }
      iModIntro. iIntros "isArr".
      (* Combine the left and right we have into a both. *)
      iDestruct (left_right_to_both with "Left Right") as "Both".
      iDestruct (ticket_i_gt_zero with "Issued Auth") as "(% & Issued & Auth)".
      iMod (own_update with "[Issued Auth Locked]") as "Hγ".
      { apply frame_update_lemma_discard_ticket. }
      { rewrite own_op own_op. iFrame. }
      iDestruct "Hγ" as "[Locked Auth]".
      iDestruct (invitation_split ι i cap with "[% //] [$Invs]") as "[Inv Invs]".
      iMod ("Close" with "[nextPts Invs Auth isArr Both R Locked]") as "_".
      { iNext. iExists (o + 1)%nat, (i - 1)%nat, (list_with_one cap ((o + 1) `mod` cap)).
        assert (o + 1 + (i - 1) = o + i)%nat as -> by lia.
        iFrame.
        iSplitL "isArr". { by rewrite /list_with_one /is_array list_fmap_insert xsEq. }
        iSplit. { by rewrite /list_with_one insert_length replicate_length. }
        iLeft. iFrame. done. }
      iModIntro. iApply "Post". done.
    * iDestruct (left_left_false with "Left Left'") as "[]".
  Qed.

End abql_spec.
