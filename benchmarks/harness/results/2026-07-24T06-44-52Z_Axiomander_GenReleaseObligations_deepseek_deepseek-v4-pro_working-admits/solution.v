(** GENERATED FILE — proof obligations for [release].

    Source contract: examples.inventory.contract:release_contract
    Generator: specsaver.lower (v2).  Do not edit by hand.

    Shape: multi-delta over keyed rows, N exception arms, typed fields.
    Deferred (v2, trace emission): state.gauge_log, state.release_log *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import AxiomanderLang AxiomanderWp.
Require Import AxiomanderPrelude.

Section gen_release.
Context `{FC : FunCtx}.

Definition store_loc : loc := Loc 1%positive.
Definition trace_loc : loc := Loc 2%positive.


Definition row_of (on_hand reserved reorder_point : Z) : sn_val :=
  LitDict [(LitString "on_hand", LitInt on_hand);
           (LitString "reserved", LitInt reserved);
           (LitString "reorder_point", LitInt reorder_point)].

Definition row_inv (v : sn_val) : Prop :=
  exists on_hand reserved reorder_point,
    v = (row_of (on_hand) (reserved) (reorder_point)) /\ (on_hand >= 0)%Z /\ (reserved >= 0)%Z /\ (reserved <= on_hand)%Z.

Fixpoint store_inv (kvs : list (sn_val * sn_val)) : Prop :=
  match kvs with
  | [] => True
  | (_, v) :: rest => row_inv v /\ store_inv rest
  end.

Definition gen_pre (sigma : sn_state) (vs : list sn_val) : Prop :=
  exists sku order quantity store_d on_hand_sku reserved_sku reorder_point_sku,
    vs = [LitString sku; LitString order; LitInt quantity] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) /\
    (quantity > 0)%Z /\ (((reserved_sku >= quantity)%Z)).

Definition gen_post (sigma : sn_state) (vs : list sn_val)
    (r : Result) (ups : cell_updates) : Prop :=
  exists sku order quantity store_d on_hand_sku reserved_sku reorder_point_sku,
    vs = [LitString sku; LitString order; LitInt quantity] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) /\
    r = RVal (LitInt reserved_sku) /\
    ups = [(store_loc, LitDict (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d))].

Definition gen_exc0_pre (sigma : sn_state) (vs : list sn_val) : Prop :=
  exists sku order quantity store_d on_hand_sku reserved_sku reorder_point_sku,
    vs = [LitString sku; LitString order; LitInt quantity] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) /\
    (reserved_sku < quantity)%Z.

Definition gen_exc0_post (sigma : sn_state) (vs : list sn_val)
    (r : Result) (ups : cell_updates) : Prop :=
  exists sku order quantity store_d on_hand_sku reserved_sku reorder_point_sku,
    vs = [LitString sku; LitString order; LitInt quantity] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) /\
    r = RExn "ReleaseExceedsReservedError" (LitTuple [LitInt reserved_sku; LitString sku; LitString order; LitInt quantity]) /\ ups = [].

Definition gen_table (f : string) : option fun_entry :=
  if String.eqb f "release" then Some (FunSpecS gen_pre gen_post)
  else if String.eqb f "release_exc0" then
  Some (FunSpecS gen_exc0_pre gen_exc0_post)
  else None.

Lemma gen_table_total_pure : forall f pre post vs,
  gen_table f = Some (FunSpec pre post) ->
  pre vs -> exists v, post vs v.
Proof.
  intros f pre post vs H. unfold gen_table in H.
  destruct (String.eqb f "release"); try discriminate H.
  destruct (String.eqb f "release_exc0"); try discriminate H.
Qed.

Lemma gen_table_total : forall f pre post vs sigma,
  gen_table f = Some (FunSpecS pre post) ->
  pre sigma vs ->
  exists r ups, post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros f pre post vs sigma Hf Hpre.
  unfold gen_table in Hf.
  destruct (String.eqb f "release") eqn:Heq1.
  - apply String.eqb_eq in Heq1. subst f.
    inversion Hf. subst pre post. clear Hf.
    destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku
      & Hvs & Hsigma & Hlook & Hpos & Hres).
    exists (RVal (LitInt reserved_sku)),
      [(store_loc, LitDict (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d))].
    split.
    + unfold gen_post.
      exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
      repeat split; assumption.
    + unfold updates_dom_in. apply Forall_cons. 2: apply Forall_nil.
      unfold is_Some. rewrite Hsigma. eauto.
  - destruct (String.eqb f "release_exc0") eqn:Heq2.
    + apply String.eqb_eq in Heq2. subst f.
      inversion Hf. subst pre post. clear Hf.
      destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku
        & Hvs & Hsigma & Hlook & Hlt).
      exists (RExn "ReleaseExceedsReservedError" (LitTuple [LitInt reserved_sku; LitString sku; LitString order; LitInt quantity])),
        [].
      split.
      * unfold gen_exc0_post.
        exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
        repeat split; assumption.
      * apply Forall_nil.
    + discriminate.
Qed.

Lemma row_inv_inj : forall a b c d e f,
  row_of a b c = row_of d e f -> a = d /\ b = e /\ c = f.
Proof.
  intros a b c d e f H.
  unfold row_of in H.
  injection H as Hlist.
  injection Hlist as H0 Hrest0.
  injection Hrest0 as H1 Hrest1.
  injection Hrest1 as H2 Hrest2.
  injection H0 as Hk0 Hv0.
  injection H1 as Hk1 Hv1.
  injection H2 as Hk2 Hv2.
  injection Hv0 as ->.
  injection Hv1 as ->.
  injection Hv2 as ->.
  auto.
Qed.

Lemma row_inv_update : forall on_hand reserved reorder_point quantity,
  row_inv (row_of on_hand reserved reorder_point) ->
  (quantity > 0)%Z ->
  (reserved - quantity >= 0)%Z ->
  row_inv (row_of on_hand (reserved - quantity) reorder_point).
Proof.
  intros * Hrow Hqty Hres.
  unfold row_inv in Hrow.
  destruct Hrow as [oh [res' [rp [Heq [Hoh [Hres' Hle]]]]]].
  apply row_inv_inj in Heq as [-> [-> ->]].
  unfold row_inv.
  exists on_hand, (reserved - quantity), reorder_point.
  split; [reflexivity|].
  split; [| split; [exact Hres | lia]].
  exact Hoh.
Qed.

Lemma gen_preserves_inv_0 : forall sku quantity store_d on_hand_sku reserved_sku reorder_point_sku,
  dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  row_inv (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  (quantity > 0)%Z ->
  (reserved_sku - quantity >= 0)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d).
Proof.
  induction store_d as [|[k' v] rest IH]; intros Hlook Hrow Hqty Hres Hinv; simpl in *.
  - discriminate.
  - destruct Hinv as [Hv_inv Hinv_rest].
    destruct k' as [|[|s| | | | | | |]| | | | |]; simpl in Hlook; simpl.
    + destruct (String.eqb sku s) eqn:Heq.
      * apply String.eqb_eq in Heq. subst s.
        inversion Hlook. subst v.
        simpl. split.
        -- apply row_inv_update; auto.
        -- assumption.
      * split; [assumption|]. apply IH; auto.
    + split; [assumption|]. apply IH; auto.
    + split; [assumption|]. apply IH; auto.
    + split; [assumption|]. apply IH; auto.
    + split; [assumption|]. apply IH; auto.
    + split; [assumption|]. apply IH; auto.
    + split; [assumption|]. apply IH; auto.
    + split; [assumption|]. apply IH; auto.
    + split; [assumption|]. apply IH; auto.
    + split; [assumption|]. apply IH; auto.
Qed.

#[global] Instance gen_fun_ctx : FunCtx :=
  {| fun_entries := gen_table;
     fun_specs_total := gen_table_total_pure;
     fun_specsS_total := gen_table_total |}.

Lemma store_inv_lookup : forall store_d k row,
  store_inv store_d ->
  dict_lookup_str k store_d = Some row ->
  row_inv row.
Proof.
  induction store_d as [|[k' v] rest IH]; intros k row Hinv Hlook; simpl in *.
  - discriminate.
  - destruct Hinv as [Hrow Hinv_rest].
    destruct k' as [|[|s| | | | | | |]| | | | |]; simpl in Hlook; auto;
      try (apply IH; assumption).
    destruct (String.eqb k s) eqn:Heq.
    + apply String.eqb_eq in Heq. inversion Hlook. subst. assumption.
    + apply IH; assumption.
Qed.

(** O1: admissibility sanity — some state and args satisfy pre ∧ invariant. *)
Lemma o1_admissibility_sanity :
  exists sigma vs, gen_pre sigma vs /\ store_inv [(LitString "SKU1", (row_of (100) (10) (10)))].
Proof.
  exists {[store_loc := LitDict [(LitString "SKU1", (row_of (100) (10) (10)))]]},
    [LitString "SKU1"; LitString "order1"; LitInt 5].
  split.
  - unfold gen_pre.
    exists "SKU1", "order1", 5, [(LitString "SKU1", (row_of (100) (10) (10)))]%Z, 100, 10, 10.
    repeat split; simpl; try lia.
    + rewrite lookup_singleton. reflexivity.
    + simpl. rewrite String.eqb_refl. reflexivity.
  - simpl. unfold row_inv. exists 100, 10, 10. split; [reflexivity|]. split; lia. split; lia. split; lia.
Qed.

(** O2: spec consistency — totality gives a post-satisfying outcome. *)
Lemma o2_spec_consistency : forall sigma vs,
  gen_pre sigma vs ->
  exists r ups, gen_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  eapply gen_table_total with (f := "release") (pre := gen_pre) (post := gen_post); eauto.
  unfold gen_table. rewrite String.eqb_refl. reflexivity.
Qed.

(** O3.0: exception consistency — the ReleaseExceedsReservedError arm is satisfiable. *)
Lemma o3_0_exception_consistency : forall sigma vs,
  gen_exc0_pre sigma vs ->
  exists r ups, gen_exc0_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  eapply gen_table_total with (f := "release_exc0") (pre := gen_exc0_pre) (post := gen_exc0_post); eauto.
  unfold gen_table. rewrite String.eqb_refl. reflexivity.
Qed.

(** O4: exit coverage — availability and the exit conditions partition. *)
Lemma o4_exit_coverage : forall (on_hand_sku reserved_sku reorder_point_sku quantity : Z) ( sku : string),
  (((reserved_sku >= quantity)%Z)) \/ (((reserved_sku < quantity)%Z)).
Proof. intros. lia. Qed.

(** O5: invariant preservation across the nested delta updates. *)
Lemma o5_invariant_preservation : forall (sku order : string) (quantity : Z) (store_d : list (sn_val * sn_val)) (on_hand_sku reserved_sku reorder_point_sku : Z),
  ((quantity > 0)%Z) ->
  (((reserved_sku >= quantity)%Z)) ->
  dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  store_inv store_d ->
  store_inv (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d).
Proof.
  intros * Hqty Hres Hlook Hinv.
  apply gen_preserves_inv_0 with (sku := sku) (quantity := quantity) (on_hand_sku := on_hand_sku) (reserved_sku := reserved_sku) (reorder_point_sku := reorder_point_sku); auto.
  - apply store_inv_lookup with (store_d := store_d) (k := sku); auto.
  - lia.
Qed.

(** O8: frame soundness — everything outside the declared frame is
    unchanged.  The generated footprint is the single store cell; every
    other location (including the trace cell) is preserved. *)
Lemma o8_frame_soundness : forall sigma vs r ups,
  gen_post sigma vs r ups ->
  forall l, l <> store_loc ->
    (apply_updates sigma ups) !! l = sigma !! l.
Proof.
  intros sigma vs r ups Hpost.
  destruct Hpost as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku
    & Hvs & Hsigma & Hlook & Hr & Hups).
  subst ups r.
  intros l Hneq. simpl.
  rewrite lookup_insert_ne; auto.
Qed.

End gen_release.