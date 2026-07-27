(* Layer 2 obligations for [restock]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.
Require Import SpecPrelude.
Require Import restock_defs.
Require Import restock_L0.
Require Import restock_L1.

Section gen_restock_L2.
Context `{FC : FunCtx}.

Lemma store_inv_lookup : forall store_d k row,
  store_inv store_d ->
  dict_lookup_str k store_d = Some row ->
  row_inv row.
Proof.
  induction store_d as [|kv rest IH]; intros k row Hinv Hlook; simpl in *.
  - discriminate.
  - destruct kv as [k0 v0].
    destruct Hinv as [Hfst Hrest].
    destruct k0 as [| | s | | | | | | | |]; simpl in *;
      try (apply (IH k row Hrest Hlook)).
    destruct (String.eqb k s) eqn:E.
    + injection Hlook as Hlook. subst v0. exact Hfst.
    + apply (IH k row Hrest Hlook).
Qed.

Lemma gen_preserves_inv_0 : forall sku quantity store_d on_hand_sku reserved_sku reorder_point_sku,
  dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  row_inv (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  (quantity > 0)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str sku (row_of (on_hand_sku + quantity) (reserved_sku) (reorder_point_sku)) store_d).
Proof.
  induction store_d as [|kv rest IH]; intros on_hand_sku reserved_sku reorder_point_sku Hlook Hprod Hpos Hinv;
    simpl in Hlook |- *.
  - discriminate.
  - destruct kv as [k0 v0].
    destruct Hinv as [Hfst Hrest].
    destruct k0 as [| | s | | | | | | | |]; simpl in *;
      try (split; [exact Hfst | apply (IH on_hand_sku reserved_sku reorder_point_sku Hlook Hprod Hpos Hrest)]).
    destruct (String.eqb sku s) eqn:E.
    + apply String.eqb_eq in E. subst s.
      injection Hlook as Hlook. subst v0.
      split; [|exact Hrest].
      destruct Hprod as [on_hand_sku0 [reserved_sku0 [reorder_point_sku0 [Heq [Hr Hlo]]
        ]]].
      injection Heq as He_on_hand_sku He_reserved_sku He_reorder_point_sku.
      subst on_hand_sku0 reserved_sku0 reorder_point_sku0.
      exists (on_hand_sku + quantity)%Z, reserved_sku, reorder_point_sku.
      split; [reflexivity|]. split; lia.
    + split; [exact Hfst|].
      apply (IH on_hand_sku reserved_sku reorder_point_sku Hlook Hprod Hpos Hrest).
Qed.

End gen_restock_L2.