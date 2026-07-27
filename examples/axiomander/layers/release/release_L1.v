(* Layer 1 obligations for [release]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.
Require Import SpecPrelude.
Require Import release_defs.
Require Import release_L0.

Section gen_release_L1.
Context `{FC : FunCtx}.


(** O2: spec consistency — totality gives a post-satisfying outcome. *)
Lemma o2_spec_consistency : forall sigma vs,
  gen_pre sigma vs ->
  exists r ups, gen_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  eapply (gen_table_total "release" gen_pre gen_post vs sigma
            eq_refl Hpre).
Qed.


(** O3.0: exception consistency — the ReleaseExceedsReservedError arm is satisfiable. *)
Lemma o3_0_exception_consistency : forall sigma vs,
  gen_exc0_pre sigma vs ->
  exists r ups, gen_exc0_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  destruct Hpre as [sku [order [quantity [store_d [on_hand_sku [reserved_sku [reorder_point_sku [Hvs [Hcell [Hlook_sku Hwhen]]]]]]]]]].
  exists (RExn "ReleaseExceedsReservedError" (LitTuple [LitInt reserved_sku; LitString sku; LitString order; LitInt quantity])), [].
  split.
  - exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku. repeat split; auto.
  - unfold updates_dom_in. constructor.
Qed.

End gen_release_L1.