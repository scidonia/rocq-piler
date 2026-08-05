(** GENERATED FILE — proof obligations for [release].

    Source contract: examples.inventory.contract:release_contract
    Generator: specsaver.lower (v2).  Do not edit by hand.

    Shape: multi-delta over keyed rows, N exception arms, typed fields.
    Deferred (v2, trace emission): state.gauge_log, state.release_log *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import AxiomanderLang AxiomanderWp.
Require Import AxiomanderPrelude.
Open Scope Z_scope.

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
  intros f pre post vs Hgen Hpre.
  unfold gen_table in Hgen.
  destruct (String.eqb f "release") eqn:Erel.
  - discriminate.
  - destruct (String.eqb f "release_exc0") eqn:Eexc.
    + discriminate.
    + discriminate.
Qed.

Lemma gen_table_total : forall f pre post vs sigma,
  gen_table f = Some (FunSpecS pre post) ->
  pre sigma vs ->
  exists r ups, post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros f pre post vs sigma Hgen Hpre.
  unfold gen_table in Hgen.
  destruct (String.eqb f "release") eqn:Erel.
  - simpl in Hgen.
    assert (gen_pre = pre) by congruence.
    assert (gen_post = post) by congruence.
    subst pre post; clear Hgen.
    unfold gen_pre in Hpre.
    destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvseq & Hstore & Hlookup & Hqty & Hres).
    exists (RVal (LitInt reserved_sku)).
    exists [(store_loc, LitDict (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d))].
    split.
    + unfold gen_post.
      exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
      intuition.
    + unfold updates_dom_in.
      constructor; [|constructor].
      simpl. rewrite Hstore. eauto.
  - destruct (String.eqb f "release_exc0") eqn:Eexc.
    + simpl in Hgen.
      assert (gen_exc0_pre = pre) by congruence.
      assert (gen_exc0_post = post) by congruence.
      subst pre post; clear Hgen.
      unfold gen_exc0_pre in Hpre.
      destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & ? & ? & ? & ?).
      exists (RExn "ReleaseExceedsReservedError" (LitTuple [LitInt reserved_sku; LitString sku; LitString order; LitInt quantity])).
      exists [].
      split.
      * unfold gen_exc0_post.
        exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
        intuition.
      * unfold updates_dom_in. constructor.
    + discriminate.
Qed.

Lemma row_inv_sub : forall (on_hand reserved reorder q : Z),
  row_inv (row_of on_hand reserved reorder) ->
  (q > 0)%Z ->
  (reserved - q >= 0)%Z ->
  row_inv (row_of on_hand (reserved - q) reorder).
Proof.
  intros on_hand reserved reorder q Hrow Hq Hres.
  unfold row_inv in *.
  destruct Hrow as (oh & r & rp & Heq_row & Hge0 & Hge0' & Hle).
  injection Heq_row as Hoh_eq Hr_eq Hrp_eq.
  rewrite <- Hoh_eq in *. rewrite <- Hr_eq in *.
  clear Hoh_eq Hr_eq Hrp_eq.
  exists on_hand, (reserved - q), reorder.
  split; [reflexivity|].
  split; [assumption|].
  split; [assumption|].
  lia.
Qed.

Lemma gen_preserves_inv_0 : forall sku quantity store_d on_hand_sku reserved_sku reorder_point_sku,
  dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  row_inv (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  (quantity > 0)%Z ->
  (reserved_sku - quantity >= 0)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d).
Proof.
  induction store_d as [|[k' v] store_d IH].
  - intros; inversion H.
  - intros on_hand_sku reserved_sku reorder_point_sku Hlook Hrow Hqty Hres Hinv.
    simpl in Hinv. destruct Hinv as [Hrow_v Hrest].
    simpl in Hlook.
    destruct k' as [| | s | | | | | | | |]; simpl in Hlook.
    all: try (simpl; split; [assumption|apply IH with (on_hand_sku:=on_hand_sku) (reserved_sku:=reserved_sku) (reorder_point_sku:=reorder_point_sku); assumption]).
    destruct (String.eqb sku s) eqn:Heq.
    + inversion Hlook; clear Hlook; subst.
      simpl. rewrite Heq. simpl. split.
      * apply row_inv_sub with (q:=quantity); assumption.
      * assumption.
    + simpl. rewrite Heq. simpl. split.
      * assumption.
      * apply IH with (on_hand_sku:=on_hand_sku) (reserved_sku:=reserved_sku) (reorder_point_sku:=reorder_point_sku); assumption.
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
  induction store_d as [|[k' v] store_d IH]; intros k row Hinv Hlook.
  - inversion Hlook.
  - simpl in Hinv. destruct Hinv as [Hrow Hrest].
    simpl in Hlook.
    destruct k' as [| | s | | | | | | | |]; simpl in Hlook; try (apply IH with (k:=k) (row:=row); assumption).
    destruct (String.eqb k s) eqn:Heq.
    + inversion Hlook; subst; assumption.
    + apply IH with (k:=k) (row:=row); assumption.
Qed.

(** O1: admissibility sanity — some state and args satisfy pre ∧ invariant. *)
Lemma o1_admissibility_sanity :
  exists sigma vs, gen_pre sigma vs /\ store_inv [(LitString "SKU1", (row_of (100) (10) (10)))].
Proof.
  exists {[store_loc := LitDict [(LitString "SKU1", row_of 100 10 10)]]}.
  exists [LitString "SKU1"; LitString "order1"; LitInt 5].
  split.
  - unfold gen_pre.
    exists "SKU1", "order1", 5%Z, [(LitString "SKU1", row_of 100 10 10)], 100%Z, 10%Z, 10%Z.
    split; [reflexivity|].
    rewrite lookup_insert_eq.
    split; [reflexivity|].
    simpl. split; [reflexivity|].
    split; [lia|lia].
  - simpl. split.
    + unfold row_inv. exists 100%Z, 10%Z, 10%Z. split; [reflexivity|].
      split; [lia|split; [lia|lia]].
    + exact I.
Qed.

(** O2: spec consistency — totality gives a post-satisfying outcome. *)
Lemma o2_spec_consistency : forall sigma vs,
  gen_pre sigma vs ->
  exists r ups, gen_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  unfold gen_pre in Hpre.
  destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvseq & Hstore & Hlookup & Hqty & Hres).
  exists (RVal (LitInt reserved_sku)).
  exists [(store_loc, LitDict (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d))].
  split.
  - unfold gen_post.
    exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
    intuition.
  - unfold updates_dom_in.
    constructor; [|constructor].
    rewrite Hstore. eauto.
Qed.

(** O3.0: exception consistency — the ReleaseExceedsReservedError arm is satisfiable. *)
Lemma o3_0_exception_consistency : forall sigma vs,
  gen_exc0_pre sigma vs ->
  exists r ups, gen_exc0_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  unfold gen_exc0_pre in Hpre.
  destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & ? & ? & ? & ?).
  exists (RExn "ReleaseExceedsReservedError" (LitTuple [LitInt reserved_sku; LitString sku; LitString order; LitInt quantity])).
  exists [].
  split.
  - unfold gen_exc0_post.
    exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
    intuition.
  - unfold updates_dom_in. constructor.
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
  intros sku order quantity store_d on_hand_sku reserved_sku reorder_point_sku Hqty Hres Hlook Hinv.
  assert (row_inv (row_of on_hand_sku reserved_sku reorder_point_sku)) as Hrow.
  { eapply store_inv_lookup; eassumption. }
  eapply gen_preserves_inv_0.
  - eassumption.
  - eassumption.
  - eassumption.
  - lia.
  - eassumption.
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
  unfold gen_post in Hpost.
  destruct Hpost as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & ? & ? & ? & ? & Hups).
  subst ups.
  intros l Hneq.
  simpl. rewrite lookup_insert_ne; auto.
Qed.

End gen_release.