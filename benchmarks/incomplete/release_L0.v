(* Layer 0 obligations for [release]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.
Require Import SpecPrelude.
Require Import release_defs.

Section gen_release_L0.
Context `{FC : FunCtx}.


(** O4: exit coverage — availability and the exit conditions partition. *)
Lemma o4_exit_coverage : forall (on_hand_sku reserved_sku reorder_point_sku quantity : Z) ( sku : string),
  (((reserved_sku >= quantity)%Z)) \/ (((reserved_sku < quantity)%Z)).
Proof. intros. lia. Qed.


(** O1: admissibility sanity — some state and args satisfy pre ∧ invariant. *)
Lemma o1_admissibility_sanity :
  exists sigma vs, gen_pre sigma vs /\ store_inv [(LitString "SKU1", (row_of (100) (10) (10)))].
Proof.
  exists {[ store_loc := LitDict [(LitString "SKU1", (row_of (100) (10) (10)))];
             trace_loc := LitList [] ]},
         [LitString "SKU1"; LitString "O1"; LitInt 5].
  split.
  - exists "SKU1", "O1", 5%Z, [(LitString "SKU1", (row_of (100) (10) (10)))], 100, 10, 10.
    split; [reflexivity|].
    split; [apply lookup_insert_eq|].
    split; [reflexivity|].
    split; [lia| lia].
  - repeat split; try exact I.
    exists 100, 10, 10. split; [reflexivity|]. repeat split; lia.
    
Qed.

End gen_release_L0.