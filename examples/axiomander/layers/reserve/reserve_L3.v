(* Layer 3 obligations for [reserve]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.
Require Import SpecPrelude.
Require Import reserve_defs.
Require Import reserve_L0.
Require Import reserve_L1.
Require Import reserve_L2.

Section gen_reserve_L3.
Context `{FC : FunCtx}.


(** O5: invariant preservation across the nested delta updates. *)
Lemma o5_invariant_preservation : forall (sku order : string) (quantity : Z) (store_d : list (sn_val * sn_val)) (on_hand_sku reserved_sku reorder_point_sku : Z),
  ((quantity > 0)%Z) ->
  (((on_hand_sku - reserved_sku >= quantity)%Z)) ->
  dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  store_inv store_d ->
  store_inv (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku + quantity) (reorder_point_sku)) store_d).
Proof.
  intros sku order quantity store_d on_hand_sku reserved_sku reorder_point_sku Hsc0 Havail Hlook_sku Hinv.
  eapply gen_preserves_inv_0;
    [ exact Hlook_sku
      | eapply store_inv_lookup; [exact Hinv | exact Hlook_sku]
      | exact Hsc0
      | lia
      | exact Hinv ].
Qed.


(** O8: frame soundness — everything outside the declared frame is
    unchanged.  The generated footprint is the single store cell; every
    other location (including the trace cell) is preserved. *)
Lemma o8_frame_soundness : forall sigma vs r ups,
  gen_post sigma vs r ups ->
  forall l, l <> store_loc ->
    (apply_updates sigma ups) !! l = sigma !! l.
Proof.
  intros sigma vs r ups Hpost l Hne.
  destruct Hpost as [sku [order [quantity [store_d [on_hand_sku [reserved_sku [reorder_point_sku [Hvs [Hcell [Hlook_sku [Hr Hups]]]]]]]]]]].
  subst ups. simpl. apply lookup_insert_ne. congruence.
Qed.

End gen_reserve_L3.