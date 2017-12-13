(* Logically atomic triple *)

From iris.base_logic Require Export fancy_updates.
From iris.program_logic Require Export hoare weakestpre.
Import uPred.

Section atomic.
  Context `{irisG Λ Σ} {A: Type}.

  (* NOTE: This triple differs from the one described in the Iris 1.0 paper by
  not having any laters.  That works for this case study, but would not work for
  the case study described in the paper. *)

  (* TODO RJ: IMHO it would make more sense to have the outer mask first, after all, that's what the shifts "starts" with. *)
  (* logically atomic triple: <x, α> e @ E_i, E_o <v, β x v> *)
  Definition atomic_triple
             (α: A → iProp Σ) (* atomic pre-condition *)
             (β: A → val _ → iProp Σ) (* atomic post-condition *)
             (Ei Eo: coPset) (* inside/outside masks *)
             (e: expr _) : iProp Σ :=
    (∀ P Q, (P ={Eo, Ei}=> ∃ x:A,
                       α x ∗
                       ((α x ={Ei, Eo}=∗ P) ∧
                        (∀ v, β x v ={Ei, Eo}=∗ Q v))
     ) -∗ {{ P }} e @ ⊤ {{ Q }})%I.
End atomic.
