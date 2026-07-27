(* Layer 2 obligations for [transfer]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.
Require Import SpecPrelude.
Require Import transfer_defs.
Require Import transfer_L0.
Require Import transfer_L1.

Section gen_transfer_L2.
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

Lemma gen_preserves_inv_0 : forall source_id amount store_d balance_source_id currency_source_id,
  dict_lookup_str source_id store_d = Some (row_of (balance_source_id) (currency_source_id)) ->
  row_inv (row_of (balance_source_id) (currency_source_id)) ->
  (amount > 0)%Z ->
  (balance_source_id - amount >= 0)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str source_id (row_of (balance_source_id - amount) (currency_source_id)) store_d).
Proof.
  induction store_d as [|kv rest IH]; intros balance_source_id currency_source_id Hlook Hprod Hpos Hdelta Hinv;
    simpl in Hlook |- *.
  - discriminate.
  - destruct kv as [k0 v0].
    destruct Hinv as [Hfst Hrest].
    destruct k0 as [| | s | | | | | | | |]; simpl in *;
      try (split; [exact Hfst | apply (IH balance_source_id currency_source_id Hlook Hprod Hpos Hdelta Hrest)]).
    destruct (String.eqb source_id s) eqn:E.
    + apply String.eqb_eq in E. subst s.
      injection Hlook as Hlook. subst v0.
      split; [|exact Hrest].
      destruct Hprod as [balance_source_id0 [currency_source_id0 [Heq Hr]
        ]].
      injection Heq as He_balance_source_id He_currency_source_id.
      subst balance_source_id0 currency_source_id0.
      exists (balance_source_id - amount)%Z, currency_source_id.
      split; [reflexivity|]. lia.
    + split; [exact Hfst|].
      apply (IH balance_source_id currency_source_id Hlook Hprod Hpos Hdelta Hrest).
Qed.

Lemma gen_preserves_inv_1 : forall target_id amount store_d balance_target_id currency_target_id,
  dict_lookup_str target_id store_d = Some (row_of (balance_target_id) (currency_target_id)) ->
  row_inv (row_of (balance_target_id) (currency_target_id)) ->
  (amount > 0)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str target_id (row_of (balance_target_id + amount) (currency_target_id)) store_d).
Proof.
  induction store_d as [|kv rest IH]; intros balance_target_id currency_target_id Hlook Hprod Hpos Hinv;
    simpl in Hlook |- *.
  - discriminate.
  - destruct kv as [k0 v0].
    destruct Hinv as [Hfst Hrest].
    destruct k0 as [| | s | | | | | | | |]; simpl in *;
      try (split; [exact Hfst | apply (IH balance_target_id currency_target_id Hlook Hprod Hpos Hrest)]).
    destruct (String.eqb target_id s) eqn:E.
    + apply String.eqb_eq in E. subst s.
      injection Hlook as Hlook. subst v0.
      split; [|exact Hrest].
      destruct Hprod as [balance_target_id0 [currency_target_id0 [Heq Hr]
        ]].
      injection Heq as He_balance_target_id He_currency_target_id.
      subst balance_target_id0 currency_target_id0.
      exists (balance_target_id + amount)%Z, currency_target_id.
      split; [reflexivity|]. lia.
    + split; [exact Hfst|].
      apply (IH balance_target_id currency_target_id Hlook Hprod Hpos Hrest).
Qed.

End gen_transfer_L2.