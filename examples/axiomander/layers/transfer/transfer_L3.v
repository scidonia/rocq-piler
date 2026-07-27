(* Layer 3 obligations for [transfer]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.
Require Import SpecPrelude.
Require Import transfer_defs.
Require Import transfer_L0.
Require Import transfer_L1.
Require Import transfer_L2.

Section gen_transfer_L3.
Context `{FC : FunCtx}.


(** O5: invariant preservation across the nested delta updates. *)
Lemma o5_invariant_preservation : forall (source_id target_id order : string) (amount : Z) (store_d : list (sn_val * sn_val)) (balance_source_id balance_target_id : Z) (currency_source_id currency_target_id : string),
  ((amount > 0)%Z /\ (source_id <> target_id)) ->
  (((currency_source_id <> currency_target_id) \/ (balance_source_id >= amount)%Z) /\ ((currency_source_id = currency_target_id))) ->
  dict_lookup_str source_id store_d = Some (row_of (balance_source_id) (currency_source_id)) ->
    dict_lookup_str target_id store_d = Some (row_of (balance_target_id) (currency_target_id)) ->
  store_inv store_d ->
  store_inv (dict_insert_str target_id (row_of (balance_target_id + amount) (currency_target_id)) (dict_insert_str source_id (row_of (balance_source_id - amount) (currency_source_id)) store_d)).
Proof.
  intros source_id target_id order amount store_d balance_source_id balance_target_id currency_source_id currency_target_id [Hsc0 Hsc1] Havail Hlook_source_id Hlook_target_id Hinv.
  eapply gen_preserves_inv_1;
    [ rewrite dict_lookup_insert_ne; [exact Hlook_target_id | congruence]
      | eapply store_inv_lookup; [exact Hinv | exact Hlook_target_id]
      | exact Hsc0
      | eapply gen_preserves_inv_0;
        [ exact Hlook_source_id
        | eapply store_inv_lookup; [exact Hinv | exact Hlook_source_id]
        | exact Hsc0
        | destruct Havail as [[Hc | Hok] Hav2]; [congruence | lia]
        | exact Hinv ] ].
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
  destruct Hpost as [source_id [target_id [order [amount [store_d [balance_source_id [currency_source_id [balance_target_id [currency_target_id [Hvs [Hcell [Hlook_source_id [Hlook_target_id [Hr Hups]]]]]]]]]]]]]].
  subst ups. simpl. apply lookup_insert_ne. congruence.
Qed.

End gen_transfer_L3.