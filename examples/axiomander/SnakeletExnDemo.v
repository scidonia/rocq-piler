From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.

(** The 8-lemma gate for the parallel exception development.

    If all eight Qed, convergence with the main pipeline is de-risked and
    we wire the Python side.  Each lemma stresses a different part of the
    hand-rolled WP:
      1. raise_val_irreducible      (in SnakeletExnLang.v)  -- stuck raise
      2. wp_raise                   (in SnakeletExnWp.v)     -- raise rule
      3. wp_try_normal, wp_try_catch                         -- try dispatch
      4. K[raise v] unwinding through a context              -- propagation
      5. wp_bind against the Result postcondition            -- composition
      6. wp_load / wp_store                                  -- heap steps
      7. exception arm carrying a points-to                  -- state-at-raise
      8. wp_call opaque against the FunCtx table             -- calls *)

Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.
Local Notation "'WPE' e {{ Q } }" := (wp_exn e Q)
  (at level 20, e, Q at level 200, format "'WPE'  e  {{  Q  } }") : bi_scope.

Section gate.
  Context `{!snakeletExn_heapGS_gen hlc Sigma}.
  Context `{FC : FunCtx}.


  (* Gate demonstrations: use the promoted WP lemmas. *)
  Local Notation "'WPE' e {{ Q } }" := (wp_exn e Q) (at level 20, e, Q at level 200) : bi_scope.
  Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v) (at level 20) : bi_scope.


  (** * GATE LEMMA 7: exception arm carrying a points-to (state-at-raise).

      A program that mutates a heap cell then raises.  The exceptional
      postcondition arm describes the heap AS IT STOOD AT THE RAISE --
      [l ↦ v] (the mutated value) -- exactly the van Collem/Krebbers idiom
      for state-at-exception via separation-logic resources in [Phi_E].
      Here [bump_then_raise l = (Store l v ;; Raise exn)] desugared as a Let. *)
  Lemma wp_store_then_raise l (w v : sn_val) (lbl : string) (pay : sn_val) :
    l ↦ w ⊢
      WPE (Let "_" (Store (Val (LitLoc l)) (Val v))
                   (Raise (Val (LitExn lbl pay))))
        {{ (fun r => match r with
              | RExn lbl' pay' => (⌜lbl' = lbl⌝ ∗ l ↦ v)%I   (* state at raise *)
              | RVal _ => False%I
              end) }}.
  Proof.
    iIntros "Hl".
    (* bind on the Let context, evaluating the Store first *)
    iApply (wp_bind_item (LetCtx "_" (Raise (Val (LitExn lbl pay)))) ); [reflexivity|].
    iApply (wp_store with "Hl"). iNext. iIntros "Hl". simpl.
    (* now: WPE (Let "_" (Val LitUnit) (Raise ...)) {{ bind_post ... }} *)
    rewrite /bind_post. simpl.
    iApply wp_let. iNext.
    (* WPE (Raise (Val (LitExn lbl pay))) {{ bind_post ... }} *)
    iApply wp_raise. simpl. iFrame "Hl". done.
  Qed.

End gate.