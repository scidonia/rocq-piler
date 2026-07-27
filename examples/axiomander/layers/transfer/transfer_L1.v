(* Layer 1 obligations for [transfer]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.
Require Import SpecPrelude.
Require Import transfer_defs.
Require Import transfer_L0.

Section gen_transfer_L1.
Context `{FC : FunCtx}.


(** O2: spec consistency — totality gives a post-satisfying outcome. *)
Lemma o2_spec_consistency : forall sigma vs,
  gen_pre sigma vs ->
  exists r ups, gen_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  eapply (gen_table_total "transfer" gen_pre gen_post vs sigma
            eq_refl Hpre).
Qed.


(** O3.0: exception consistency — the InsufficientFundsError arm is satisfiable. *)
Lemma o3_0_exception_consistency : forall sigma vs,
  gen_exc0_pre sigma vs ->
  exists r ups, gen_exc0_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  destruct Hpre as [source_id [target_id [order [amount [store_d [balance_source_id [currency_source_id [balance_target_id [currency_target_id [Hvs [Hcell [Hlook_source_id [Hlook_target_id Hwhen]]]]]]]]]]]]].
  exists (RExn "InsufficientFundsError" (LitTuple [LitString source_id; LitInt amount])), [].
  split.
  - exists source_id, target_id, order, amount, store_d, balance_source_id, currency_source_id, balance_target_id, currency_target_id. repeat split; auto.
  - unfold updates_dom_in. constructor.
Qed.

(** O3.1: exception consistency — the CurrencyMismatchError arm is satisfiable. *)
Lemma o3_1_exception_consistency : forall sigma vs,
  gen_exc1_pre sigma vs ->
  exists r ups, gen_exc1_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  destruct Hpre as [source_id [target_id [order [amount [store_d [balance_source_id [currency_source_id [balance_target_id [currency_target_id [Hvs [Hcell [Hlook_source_id [Hlook_target_id Hwhen]]]]]]]]]]]]].
  exists (RExn "CurrencyMismatchError" (LitTuple [LitString source_id; LitString target_id])), [].
  split.
  - exists source_id, target_id, order, amount, store_d, balance_source_id, currency_source_id, balance_target_id, currency_target_id. repeat split; auto.
  - unfold updates_dom_in. constructor.
Qed.

End gen_transfer_L1.