(* Layer 0 obligations for [transfer]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.
Require Import SpecPrelude.
Require Import transfer_defs.

Section gen_transfer_L0.
Context `{FC : FunCtx}.


(** O4: exit coverage — availability and the exit conditions partition. *)
Lemma o4_exit_coverage : forall (balance_source_id balance_target_id amount : Z) (currency_source_id currency_target_id source_id target_id : string),
  (((currency_source_id <> currency_target_id) \/ (balance_source_id >= amount)%Z) /\ ((currency_source_id = currency_target_id))) \/ (((currency_source_id = currency_target_id) /\ (balance_source_id < amount)%Z) \/ ((currency_source_id <> currency_target_id))).
Proof.
  intros.
  destruct (String.eqb currency_source_id currency_target_id) eqn:E.
  - apply String.eqb_eq in E. subst currency_target_id.
    destruct (Z_ge_dec balance_source_id amount)
      as [Hg | Hl].
    + left. split; [right; lia | reflexivity].
    + right. left. split; [reflexivity | lia].
  - right. right. apply String.eqb_neq. exact E.
Qed.


(** O1: admissibility sanity — some state and args satisfy pre ∧ invariant. *)
Lemma o1_admissibility_sanity :
  exists sigma vs, gen_pre sigma vs /\ store_inv [(LitString "SOURCE_ID1", (row_of (100) ("USD"))); (LitString "TARGET_ID1", (row_of (100) ("USD")))].
Proof.
  exists {[ store_loc := LitDict [(LitString "SOURCE_ID1", (row_of (100) ("USD"))); (LitString "TARGET_ID1", (row_of (100) ("USD")))];
             trace_loc := LitList [] ]},
         [LitString "SOURCE_ID1"; LitString "TARGET_ID1"; LitString "O1"; LitInt 5].
  split.
  - exists "SOURCE_ID1", "TARGET_ID1", "O1", 5%Z, [(LitString "SOURCE_ID1", (row_of (100) ("USD"))); (LitString "TARGET_ID1", (row_of (100) ("USD")))], 100, "USD", 100, "USD".
    split; [reflexivity|].
    split; [apply lookup_insert_eq|].
    split; [reflexivity|].
    split; [reflexivity|].
    split; [lia|].
    split; [congruence| split; [try (right; lia); try (left; lia) | try reflexivity; try lia; try congruence]].
  - repeat split; try exact I.
    exists 100, "USD". split; [reflexivity|]. repeat split; lia.
    exists 100, "USD". split; [reflexivity|]. repeat split; lia.
Qed.

End gen_transfer_L0.