(* Layer 0 obligations for [restock]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.
Require Import SpecPrelude.
Require Import restock_defs.

Section gen_restock_L0.
Context `{FC : FunCtx}.




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
    split; [lia | exact I].
  - repeat split; try exact I.
    exists 100, 10, 10. split; [reflexivity|]. repeat split; lia.
    
Qed.

End gen_restock_L0.