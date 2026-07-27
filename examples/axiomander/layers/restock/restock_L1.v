(* Layer 1 obligations for [restock]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.
Require Import SpecPrelude.
Require Import restock_defs.
Require Import restock_L0.

Section gen_restock_L1.
Context `{FC : FunCtx}.


(** O2: spec consistency — totality gives a post-satisfying outcome. *)
Lemma o2_spec_consistency : forall sigma vs,
  gen_pre sigma vs ->
  exists r ups, gen_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  eapply (gen_table_total "restock" gen_pre gen_post vs sigma
            eq_refl Hpre).
Qed.

End gen_restock_L1.