From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris_atomic Require Import atomic.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import coPset.
From iris.heap_lang.lib Require Import par.

Section incr.
  Context `{!heapG Σ} (N : namespace).

  Definition incr: val :=
    rec: "incr" "l" :=
       let: "oldv" := !"l" in
       if: CAS "l" "oldv" ("oldv" + #1)
         then "oldv" (* return old value if success *)
         else "incr" "l".

  (* TODO: Can we have a more WP-style definition and avoid the equality? *)
  Definition incr_triple (l: loc) :=
    atomic_triple (fun (v: Z) => l ↦ #v)%I
                  (fun v ret => ⌜ret = #v⌝ ∗ l ↦ #(v + 1))%I
                  ∅
                  ⊤
                  (incr #l).

  Lemma incr_atomic_spec: ∀ (l: loc), incr_triple l.
  Proof.
    iIntros (l).
    rewrite /incr_triple.
    rewrite /atomic_triple.
    iIntros (P Q) "#Hvs".
    iLöb as "IH".
    iIntros "!# HP".
    wp_rec.
    wp_bind (! _)%E.
    iMod ("Hvs" with "HP") as (x) "[Hl [Hvs' _]]".
    wp_load.
    iMod ("Hvs'" with "Hl") as "HP".
    iModIntro. wp_let. wp_bind (CAS _ _ _). wp_op.
    iMod ("Hvs" with "HP") as (x') "[Hl Hvs']".
    destruct (decide (x = x')).
    - subst.
      iDestruct "Hvs'" as "[_ Hvs']".
      iSpecialize ("Hvs'" $! #x').
      wp_cas_suc.
      iMod ("Hvs'" with "[Hl]") as "HQ"; first by iFrame.
      iModIntro. wp_if. done.
    - iDestruct "Hvs'" as "[Hvs' _]".
      wp_cas_fail.
      iMod ("Hvs'" with "[Hl]") as "HP"; first by iFrame.
      iModIntro. wp_if. by iApply "IH".
  Qed.
End incr.


Section user.
  Context `{!heapG Σ, !spawnG Σ} (N : namespace).

  Definition incr_2 : val :=
    λ: "x",
       let: "l" := ref "x" in
       incr "l" ||| incr "l";;
       !"l".

  (* prove that incr is safe w.r.t. data race. TODO: prove a stronger post-condition *)
  Lemma incr_2_safe:
    ∀ (x: Z), (WP incr_2 #x {{ _, True }})%I.
  Proof.
    iIntros (x) "". (* FIXME: I did iIntros, this should not be needed. *)
    rewrite /incr_2 /=.
    wp_lam.
    wp_alloc l as "Hl".
    iMod (inv_alloc N _ (∃x':Z, l ↦ #x')%I with "[Hl]") as "#?"; first eauto.
    wp_let.
    wp_bind (_ ||| _)%E.
    iAssert (□ WP incr #l {{ _, True }})%I as "#?".
    { (* prove worker triple *)
      iDestruct (incr_atomic_spec l) as "Hincr"=>//.
      rewrite /incr_triple /atomic_triple.
      iSpecialize ("Hincr"  $! True%I (fun _ => True%I) with "[]").
      - iIntros "!# _".
        (* open the invariant *)
        iInv N as (x') ">Hl'" "Hclose".
        (* mask magic *)
        iMod (fupd_intro_mask' _ ∅) as "Hvs"; first set_solver.
        iModIntro. iExists x'. iFrame "Hl'". iSplit.
        + (* provide a way to rollback *)
          iIntros "Hl'".
          iMod "Hvs". iMod ("Hclose" with "[Hl']"); eauto.
        + (* provide a way to commit *)
          iIntros (v) "[Heq Hl']".
          iMod "Hvs". iMod ("Hclose" with "[Hl']"); eauto.
      - iDestruct "Hincr" as "#HIncr". iAlways. by iApply "HIncr". }
    iApply (wp_par (λ _, True%I) (λ _, True%I) with "[] []"); [done..|].
    iIntros (v1 v2) "_ !>".
    wp_seq. iInv N as (x') ">Hl" "Hclose".
    wp_load. iApply "Hclose". eauto.
  Qed.
End user.
