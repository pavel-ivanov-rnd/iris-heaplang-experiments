From iris.algebra Require Import excl auth gmap agree.
From iris.heap_lang Require Export lifting notation.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation par.
From iris.bi.lib Require Import fractional.
From iris_examples.logatom.snapshot Require Import spec.
Set Default Proof Using "Type".

(** Specifying snapshots with histories
    Implementing atomic pair snapshot data structure from Sergey et al. (ESOP 2015) *)


(*
     newPair x y :=
       (ref (ref (x, 0)), ref y)
 *)
Definition newPair : val :=
  λ: "args",
  let: "x" := Fst "args" in
  let: "y" := Snd "args" in
  (ref (ref ("x", #0)), ref "y").

(*
    writeY (xp, yp) y :=
      yp <- y
 *)
Definition writeY : val :=
  λ: "args",
  let: "p" := Fst "args" in
  Snd "p" <- Snd "args".

(*
    writeX (xp, yp) x :=
      let xp1 = !xp in
      let v   = (!xp1).2
      let xp2 = ref (x, v + 1)
      if CAS xp xp1 xp2
        then ()
        else writeX (xp, yp) x
 *)
Definition writeX : val :=
  rec: "writeX" "args" :=
    let: "p"    := Fst "args"             in
    let: "x"    := Snd "args"             in
    let: "xp"   := Fst "p"                in
    let: "xp1"  := !"xp"                  in
    let: "v"    := Snd (!"xp1")           in
    let: "xp2"  := ref ("x", "v" + #1)    in
    if: CAS "xp" "xp1" "xp2"
    then #()
    else "writeX" "args".

(*
    readX (xp, yp) :=
      !!xp
 *)
Definition readX : val :=
  λ: "p",
  let: "xp" := Fst "p" in
  !(!"xp").

Definition readY : val :=
  λ: "p",
  let: "yp" := Snd "p" in
  !"yp".

(*
    readPair l :=
      let (x, v)  = readX l in
      let y       = readY l in
      let (_, v') = readX l in
      if v = v'
        then (x, y)
        else readPair l
 *)
Definition readPair : val :=
  rec: "readPair" "l" :=
    let: "x"  := readX "l"  in
    let: "y"  := readY "l"  in
    let: "x'" := readX "l"  in
    if: Snd "x" = Snd "x'"
    then (Fst "x", Fst "y")
    else  "readPair" "l".

Definition readPair_proph : val :=
  rec: "readPair" "l" :=
    let: "xv1"    := readX "l"           in
    let: "proph"  := NewProph            in
    let: "y"      := readY "l"           in
    let: "xv2"    := readX "l"           in
    let: "v2"     := Snd "xv2"           in
    let: "v_eq"   := Snd "xv1" = "v2"    in
    resolve_proph: "proph" to: "v_eq" ;;
    if: "v_eq"
      then (Fst "xv1", "y")
    else "readPair" "l".


(** The CMRA & functor we need. *)

Definition timestampUR := gmapUR Z $ agreeR valC.

Class atomic_snapshotG Σ := AtomicSnapshotG {
                                atomic_snapshot_stateG :> inG Σ $ authR $ optionUR $ exclR $ valC;
                                atomic_snapshot_timestampG :> inG Σ $ authR $ timestampUR
}.
Definition atomic_snapshotΣ : gFunctors :=
  #[GFunctor (authR $ optionUR $ exclR $ valC); GFunctor (authR timestampUR)].

Instance subG_atomic_snapshotΣ {Σ} : subG atomic_snapshotΣ Σ → atomic_snapshotG Σ.
Proof. solve_inG. Qed.

Section atomic_snapshot.

  Context {Σ} `{!heapG Σ, !atomic_snapshotG Σ}.

  Variable N: namespace.

  Definition gmap_to_UR T : timestampUR := to_agree <$> T.

  Definition pair_inv γ1 γ2 l1 : iProp Σ :=
    (∃ q (l1':loc) (T : gmap Z val) x (t : Z),
      (* we add the q to make the l1' map fractional. that way,
         we can take a fraction of the l1' map out of the invariant
         and do a case analysis on whether the pointer is the same
         throughout invariant openings *)
      l1 ↦ #l1' ∗ l1' ↦{q} (x, #t) ∗
         own γ1 (● Excl' x) ∗ own γ2 (● gmap_to_UR T) ∗
         ⌜T !! t = Some x⌝ ∗
         ⌜forall (t' : Z), t' ∈ dom (gset Z) T → (t' <= t)%Z⌝)%I.

  Definition is_pair (γs: gname * gname * loc) (p : val) :=
    (∃ (l1 : loc), ⌜p = (#l1, #γs.2)%V⌝ ∗ inv N (pair_inv γs.1.1 γs.1.2 l1))%I.

  Global Instance is_pair_persistent γs p : Persistent (is_pair γs p) := _.

  Definition pair_content (γs : gname * gname * loc) (a : val * val) :=
    (own γs.1.1 (◯ Excl' a.1) ∗ γs.2 ↦ a.2)%I.

  Global Instance pair_content_timeless γs a : Timeless (pair_content γs a) := _.

  Lemma pair_content_exclusive γs a1 a2 :
    pair_content γs a1 -∗ pair_content γs a2 -∗ False.
  Proof.
    iIntros "[H1 _] [H2 _]". iDestruct (own_valid_2 with "H1 H2") as %[].
  Qed.

  Definition new_timestamp t v : gmap Z val := {[ t := v ]}.

  Lemma newPair_spec (v1 v2 : val) :
      {{{ True }}}
        newPair (v1, v2)%V
      {{{ γs p, RET p; is_pair γs p ∗ pair_content γs (v1, v2) }}}.
  Proof.
    iIntros (Φ _) "Hx". rewrite /newPair. wp_lam.
    repeat (wp_proj; wp_let).
    iApply wp_fupd.
    wp_alloc ly as "Hly".
    wp_alloc lx' as "Hlx'".
    wp_alloc lx as "Hlx".
    set (Excl' v1) as p.
    iMod (own_alloc (● p ⋅ ◯ p)) as (γ1) "[Hx⚫ Hx◯]". {
      rewrite /p. apply auth_both_valid. split; done.
    }
    set (new_timestamp 0 v1) as t.
    iMod (own_alloc (● gmap_to_UR t ⋅ ◯ gmap_to_UR t)) as (γ2) "[Ht⚫ Ht◯]". {
      rewrite /t /new_timestamp. apply auth_both_valid.
      split; first done. rewrite /gmap_to_UR map_fmap_singleton. apply singleton_valid. done.
    }
    wp_pures. iApply ("Hx" $! (γ1, γ2, ly)).
    iMod (inv_alloc N _ (pair_inv γ1 γ2 _) with "[-Hx◯ Ht◯ Hly]") as "#Hinv". {
      iNext. rewrite /pair_inv. iExists _, _, _, _, 0. iFrame.
      iPureIntro. split; first done. intros ?. subst t. rewrite /new_timestamp dom_singleton.
      rewrite elem_of_singleton. lia.
    }
    iModIntro. rewrite /is_pair /pair_content. iFrame. iExists _.
    iSplitL; first done. done.
  Qed.

 Lemma excl_update γ n' n m :
    own γ (● (Excl' n)) -∗ own γ (◯ (Excl' m)) ==∗
      own γ (● (Excl' n')) ∗ own γ (◯ (Excl' n')).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (● Excl' n' ⋅ ◯ Excl' n') with "Hγ● Hγ◯") as "[$$]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    done.
  Qed.

  Lemma excl_sync γ n m :
    own γ (● (Excl' n)) -∗ own γ (◯ (Excl' m)) -∗ ⌜m = n⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    iDestruct (own_valid_2 with "Hγ● Hγ◯") as
        %[H%Excl_included%leibniz_equiv _]%auth_both_valid.
    done.
  Qed.

  Lemma timestamp_dupl γ T:
    own γ (● T) ==∗ own γ (● T) ∗ own γ (◯ T).
  Proof.
    iIntros "Ht". iApply own_op. iApply (own_update with "Ht").
    apply auth_update_alloc. apply local_update_unital_discrete => f Hv. rewrite left_id => <-.
    split; first done. apply core_id_dup. apply _.
  Qed.

  Lemma timestamp_update γ (T : gmap Z val) (t : Z) x :
    T !! t = None →
    own γ (● gmap_to_UR T) ==∗ own γ (● gmap_to_UR (<[ t := x ]> T)).
  Proof.
    iIntros (HT) "Ht".
    set (<[ t := x ]> T) as T'.
    iDestruct (own_update _ _ (● gmap_to_UR T' ⋅ ◯ gmap_to_UR {[ t := x ]}) with "Ht") as "Ht". {
      apply auth_update_alloc. rewrite /T' /gmap_to_UR map_fmap_singleton. rewrite fmap_insert.
      apply alloc_local_update; last done. rewrite lookup_fmap HT. done.
    }
    iMod (own_op with "Ht") as "[Ht● Ht◯]". iModIntro. iFrame.
  Qed.

  Lemma timestamp_sub γ (T1 T2 : gmap Z val):
    own γ (● gmap_to_UR T1) ∗ own γ (◯ gmap_to_UR T2) -∗
    ⌜forall t x, T2 !! t = Some x → T1 !! t = Some x⌝.
  Proof.
    iIntros "[Hγ⚫ Hγ◯]".
    iDestruct (own_valid_2 with "Hγ⚫ Hγ◯") as
        %[H Hv]%auth_both_valid. iPureIntro. intros t x HT2.
    pose proof (iffLR (lookup_included (gmap_to_UR T2) (gmap_to_UR T1)) H t) as Ht.
    rewrite !lookup_fmap HT2 /= in Ht.
    destruct (is_Some_included _ _ Ht) as [? [t2 [Ht2 ->]]%fmap_Some_1]; first by eauto.
    revert Ht.
    rewrite Ht2 Some_included_total to_agree_included. fold_leibniz.
    by intros ->.
  Qed.

  Lemma writeY_spec γ (y2: val) p :
      is_pair γ p -∗
      <<< ∀ x y : val, pair_content γ (x, y) >>>
        writeY (p, y2)%V
        @ ⊤∖↑N
      <<< pair_content γ (x, y2), RET #() >>>.
  Proof.
    iIntros "Hx". iIntros (Φ) "AU".
    iDestruct "Hx" as (l1 ->) "#Hinv". wp_pures.
    wp_lam. wp_pures.
    iApply wp_fupd.
    iMod "AU" as (xv yv) "[[Hx Hy] [_ Hclose]]".
    wp_store.
    iMod ("Hclose" with "[Hx Hy]") as "HΦ".
    { rewrite /pair_content. iFrame. }
    eauto.
  Qed.

  Lemma writeX_spec γ (x2: val) p :
      is_pair γ p  -∗
      <<< ∀ x y : val, pair_content γ (x, y) >>>
        writeX (p, x2)%V
        @ ⊤∖↑N
      <<< pair_content γ (x2, y), RET #() >>>.
  Proof.
    iIntros "Hx". iIntros (Φ) "AU". iLöb as "IH".
    iDestruct "Hx" as (l1 ->) "#Hinv". wp_pures. wp_lam. wp_pures.
    (* first read *)
    (* open invariant *)
    wp_bind (!_)%E. iInv N as (q l1' T x v') "[Hl1 [Hl1' [Hx⚫ Htime]]]".
      wp_load.
      iDestruct "Hl1'" as "[Hl1'frac1 Hl1'frac2]".
      iModIntro. iSplitR "AU Hl1'frac2".
      (* close invariant *)
      { iNext. rewrite /pair_inv. eauto 10 with iFrame. }
    wp_let. wp_bind (!_)%E. clear T.
    wp_load. wp_proj. wp_let. wp_op. wp_alloc l1'new as "Hl1'new".
    wp_let.
    (* CAS *)
    wp_bind (CAS _ _ _)%E.
    (* open invariant *)
    iInv N as (q' l1'' T x' v'') ">[Hl1 [Hl1'' [Hx⚫ [Ht● Ht]]]]".
    iDestruct "Ht" as %[Ht Hvt].
    destruct (decide (l1'' = l1')) as [-> | Hn].
    - wp_cas_suc.
      iDestruct (mapsto_agree with "Hl1'frac2 Hl1''") as %[= -> ->]. iClear "Hl1'frac2".
      (* open AU *)
      iMod "AU" as (xv yv) "[[Hx Hy] [_ Hclose]]".
        (* update pair ghost state to (x2, y') *)
        iDestruct (excl_sync with "Hx⚫ Hx") as %[= ->].
        iMod (excl_update _ x2 with "Hx⚫ Hx") as "[Hx⚫ Hx◯]".
        (* close AU *)
        iMod ("Hclose" with "[Hx◯ Hy]") as "HΦ".
        { rewrite /pair_content. iFrame. }
      (* update timestamp *)
      iMod (timestamp_update _ T (v'' + 1)%Z x2 with "[Ht●]") as "Ht".
      { eapply (not_elem_of_dom (D:=gset Z) T). intros Hd. specialize (Hvt _ Hd). omega. }
      { done. }
      (* close invariant *)
      iModIntro. iSplitR "HΦ".
      + iNext. rewrite /pair_inv.
        set (<[ v'' + 1 := x2]> T) as T'.
        iExists 1%Qp, l1'new, T', x2, (v'' + 1).
        iFrame.
        iPureIntro. split.
        * apply: lookup_insert.
        * intros ? Hv. destruct (decide (t' = (v'' + 1)%Z)) as [-> | Hn]; first done.
          assert (dom (gset Z) T' = {[(v'' + 1)%Z]} ∪ dom (gset Z) T) as Hd. {
            apply leibniz_equiv. rewrite dom_insert. done.
          }
          rewrite Hd in Hv. clear Hd. apply elem_of_union in Hv.
          destruct Hv as [Hv%elem_of_singleton_1 | Hv]; first done.
          specialize (Hvt _ Hv). lia.
      + wp_if. done.
    - wp_cas_fail. iModIntro. iSplitR "AU".
      + iNext. rewrite /pair_inv. eauto 10 with iFrame.
      + wp_if. iApply "IH"; last eauto. rewrite /is_pair. eauto.
  Qed.

  Lemma readY_spec γ p :
    is_pair γ p -∗
    <<< ∀ v1 v2 : val, pair_content γ (v1, v2) >>>
      readY p
      @ ⊤∖↑N
    <<< pair_content γ (v1, v2), RET v2 >>>.
  Proof.
    iIntros "Hx". iIntros (Φ) "AU".
    iDestruct "Hx" as (l1 ->) "#Hinv".
    repeat (wp_lam; wp_proj). wp_let.
    iApply wp_fupd.
    iMod "AU" as (xv yv) "[[Hx Hy] [_ Hclose]]".
    wp_load.
    rewrite /pair_content.
    iMod ("Hclose" with "[$Hx $Hy]") as "HΦ".
    iModIntro. done.
  Qed.

  Lemma readX_spec γ p :
    is_pair γ p -∗
    <<< ∀ v1 v2 : val, pair_content γ (v1, v2) >>>
      readX p
      @ ⊤∖↑N
    <<< ∃ (t: Z), pair_content γ (v1, v2), RET (v1, #t) >>>.
  Proof.
    iIntros "Hx". iIntros (Φ) "AU".
    iDestruct "Hx" as (l1 ->) "#Hinv".
    repeat (wp_lam; wp_proj). wp_let. wp_bind (! #l1)%E.
    (* open invariant for 1st read *)
    iInv N as (q l1' T x v') ">[Hl1 [Hl1' [Hx⚫ Htime]]]".
      wp_load.
      iDestruct "Hl1'" as "[Hl1' Hl1'frac]".
      iMod "AU" as (xv yv) "[[Hx Hy] [_ Hclose]]".
      iDestruct (excl_sync with "Hx⚫ Hx") as %[= ->].
      iMod ("Hclose" with "[Hx Hy]") as "HΦ".
      { rewrite /pair_content. iFrame. }
      (* close invariant *)
      iModIntro. iSplitR "HΦ Hl1'". {
        iNext. unfold pair_inv. eauto 7 with iFrame.
      }
    iApply wp_fupd. wp_load. eauto.
  Qed.

  Definition prophecy_to_bool (v : list (val * val)) : bool :=
    match v with
    | (_, LitV (LitBool b)) :: _ => b
    | _                          => false
    end.

  Lemma readPair_spec γ p :
    is_pair γ p -∗
    <<< ∀ v1 v2 : val, pair_content γ (v1, v2) >>>
       readPair_proph p
       @ ⊤∖↑N
    <<< pair_content γ (v1, v2), RET (v1, v2) >>>.
  Proof.
    iIntros "Hx". iIntros (Φ) "AU". iLöb as "IH".
    wp_pures.
    (* ************ 1st readX ********** *)
    iDestruct "Hx" as (l1 ->) "#Hinv". repeat (wp_lam; wp_pures).
    wp_bind (! #l1)%E.
    (* open invariant for 1st read *)
    iInv N as (q_x1 l1' T_x x1 v_x1) ">[Hl1 [Hl1' [Hx⚫ [Ht_x Htime_x]]]]".
      iDestruct "Htime_x" as %[Hlookup_x Hdom_x].
      wp_load.
      iDestruct "Hl1'" as "[Hl1' Hl1'frac]".
      iMod "AU" as (xv yv) "[[Hx Hy] [Hclose _]]".
      iDestruct (excl_sync with "Hx⚫ Hx") as %[= ->].
      iMod ("Hclose" with "[Hx Hy]") as "AU".
      { rewrite /pair_content. iFrame. }
      (* duplicate timestamp T_x1 *)
      iMod (timestamp_dupl with "Ht_x") as "[Ht_x1⚫ Ht_x1◯]".
      (* close invariant *)
      iModIntro. iSplitR "AU Hl1' Ht_x1◯". {
        iNext. unfold pair_inv. eauto 8 with iFrame.
      }
    wp_load. wp_let.
    (* ************ new prophecy ********** *)
    wp_apply wp_new_proph; first done.
    iIntros (proph_val proph) "Hpr".
    wp_let.
    (* ************ readY ********** *)
    repeat (wp_lam; wp_pures). wp_bind (!_)%E.
    iInv N as (q_y l1'_y T_y x_y v_y) ">[Hl1 [Hl1'_y [Hx⚫ [Ht_y Htime_y]]]]".
    iDestruct "Htime_y" as %[Hlookup_y Hdom_y].
    (* linearization point *)
    clear yv.
    iMod "AU" as (xv yv) "[[Hx Hy] Hclose]".
    wp_load.
    rewrite /pair_content.
    iDestruct (excl_sync with "Hx⚫ Hx") as %[= ->].
    destruct (prophecy_to_bool proph_val) eqn:Hproph.
    - (* prophecy value is predicting that timestamp has not changed, so we commit *)
      (* committing AU *)
      iMod ("Hclose" with "[$Hx $Hy]") as "HΦ".
      (* duplicate timestamp T_y *)
      iMod (timestamp_dupl with "Ht_y") as "[Ht_y● Ht_y◯]".
      (* show that T_x <= T_y *)
      iDestruct (timestamp_sub with "[Ht_y● Ht_x1◯]") as "#Hs"; first by iFrame.
      iDestruct "Hs" as %Hs.
      iModIntro. iModIntro.
      (* closing invariant *)
      iSplitR "HΦ Hl1' Ht_x1◯ Ht_y◯ Hpr".
      { iNext. unfold pair_inv. eauto 10 with iFrame. }
      wp_let.
      (* ************ 2nd readX ********** *)
      repeat (wp_lam; wp_pures). wp_bind (! #l1)%E.
      (* open invariant *)
      iInv N as (q_x2 l1'_x2 T_x2 x2 v_x2) ">[Hl1 [Hl1'_x2 [Hx⚫ [Ht_x2 Htime_x2]]]]".
      iDestruct "Htime_x2" as %[Hlookup_x2 Hdom_x2].
      iDestruct "Hl1'_x2" as "[Hl1'_x2 Hl1'_x2_frag]".
      wp_load.
      (* show that T_y <= T_x2 *)
      iDestruct (timestamp_sub with "[Ht_x2 Ht_y◯]") as "#Hs'"; first by iFrame.
      iDestruct "Hs'" as %Hs'.
      iModIntro. iSplitR "HΦ Hl1'_x2_frag Hpr". {
        iNext. unfold pair_inv. eauto 8 with iFrame.
      }
      wp_load. wp_let. wp_proj. wp_let. wp_proj. wp_op.
      case_bool_decide; wp_let; wp_apply (wp_resolve_proph with "Hpr");
        iIntros (vs') "[Eq _]"; iDestruct "Eq" as %->; wp_seq; wp_if.
      + inversion H; subst; clear H. wp_pures.
        assert (v_x2 = v_y) as ->. {
          assert (v_x2 <= v_y) as vneq. {
            apply Hdom_y.
            eapply (iffRL (elem_of_dom T_y _)). eauto using mk_is_Some.
          }
          assert (v_y <= v_x2) as vneq'. {
            apply Hdom_x2.
            eapply (iffRL (elem_of_dom T_x2 _)). eauto using mk_is_Some.
          }
          apply Z.le_antisymm; auto.
        }
        assert (x1 = x_y) as ->. {
          specialize (Hs _ _ Hlookup_x). rewrite Hs in Hlookup_y. inversion Hlookup_y. done.
        }
        done.
      + inversion Hproph.
    - iDestruct "Hclose" as "[Hclose _]". iMod ("Hclose" with "[$Hx $Hy]") as "AU".
      iModIntro. iModIntro.
      (* closing invariant *)
      iSplitR "AU Hpr".
      { iNext. unfold pair_inv. eauto 10 with iFrame. }
      wp_let.
      (* ************ 2nd readX ********** *)
      repeat (wp_lam; wp_proj). wp_let. wp_bind (! #l1)%E.
      (* open invariant *)
      iInv N as (q_x2 l1'_x2 T_x2 x2 v_x2) "[Hl1 [Hl1'_x2 [Hx⚫ [Ht_x2 Htime_x2]]]]".
      iDestruct "Hl1'_x2" as "[Hl1'_x2 Hl1'_x2_frag]".
      wp_load.
      iModIntro. iSplitR "AU Hl1'_x2_frag Hpr". {
        iNext. unfold pair_inv. eauto 8 with iFrame.
      }
      wp_load. repeat (wp_let; wp_proj). wp_op. wp_let.
      wp_apply (wp_resolve_proph with "Hpr").
      iIntros (vs') "[Heq _]"; iDestruct "Heq" as %->.
      case_bool_decide.
      + inversion H; subst; clear H. inversion Hproph.
      + wp_seq. wp_if. iApply "IH"; rewrite /is_pair; eauto.
  Qed.

End atomic_snapshot.

Definition atomic_snapshot `{!heapG Σ, atomic_snapshotG Σ} :
  spec.atomic_snapshot Σ :=
  {| spec.newPair_spec := newPair_spec;
     spec.writeX_spec := writeX_spec;
     spec.writeY_spec := writeY_spec;
     spec.readPair_spec := readPair_spec;
     spec.pair_content_exclusive := pair_content_exclusive |}.

Typeclasses Opaque pair_content is_pair.
