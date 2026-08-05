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
  intros f pre post vs Hgen Hpre.
  unfold gen_table in Hgen.
  destruct (String.eqb f "release") eqn:Erel.
  - injection Hgen as H; subst. unfold gen_pre in Hpre.
    destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvs & Hsigma & Hlookup & Hpos & Hge).
    exists (LitInt reserved_sku).
    unfold gen_post.
    subst.
    exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
    repeat split; auto; try lia.
  - destruct (String.eqb f "release_exc0") eqn:Eexc.
    + injection Hgen as H; subst. unfold gen_exc0_pre in Hpre.
      destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvs & Hsigma & Hlookup & Hlt).
      unfold gen_exc0_post.
      exists (LitInt reserved_sku).
      exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
      repeat split; auto.
    + inversion Hgen.
Qed.

Lemma gen_table_total : forall f pre post vs sigma,
  gen_table f = Some (FunSpecS pre post) ->
  pre sigma vs ->
  exists r ups, post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros f pre post vs sigma Hgen Hpre.
  unfold gen_table in Hgen.
  destruct (String.eqb f "release") eqn:Erel.
  - injection Hgen as <- <-.
    destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvs & Hsigma & Hlookup & Hpos & Hge).
    exists (RVal (LitInt reserved_sku)), [(store_loc, LitDict (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d))].
    split.
    + unfold gen_post.
      exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
      subst.
      repeat split; auto.
    + unfold updates_dom_in.
      exists (LitDict store_d).
      split; auto.
      reflexivity.
  - destruct (String.eqb f "release_exc0") eqn:Eexc.
    + injection Hgen as <- <-.
      destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvs & Hsigma & Hlookup & Hlt).
      exists (RExn "ReleaseExceedsReservedError" (LitTuple [LitInt reserved_sku; LitString sku; LitString order; LitInt quantity])), [].
      split.
      * unfold gen_exc0_post.
        exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
        subst.
        repeat split; auto.
      * unfold updates_dom_in.
        reflexivity.
    + inversion Hgen.
Qed.

Lemma gen_preserves_inv_0 : forall sku quantity store_d on_hand_sku reserved_sku reorder_point_sku,
  dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  row_inv (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  (quantity > 0)%Z ->
  (reserved_sku - quantity >= 0)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d).
Proof.
  induction store_d as [|[k' v'] rest]; simpl; intros Hlook Hrow_inv Hpos Hnonneg Hinv.
  - inversion Hlook.
  - destruct Hinv as [Hv' Hrest].
    destruct (String.eqb sku k') eqn:Heq.
    + injection Hlook as ->.
      split; [| auto].
      unfold row_inv.
      unfold row_inv in Hrow_inv.
      destruct Hrow_inv as (on_hand & reserved & reorder_point & Heq_row & Hon_hand & Hreserved & Hle).
      injection Heq_row as -> -> ->.
      exists on_hand_sku, (reserved_sku - quantity), reorder_point_sku.
      split; [auto|].
      split; [lia|].
      split; [auto|].
      lia.
    + apply IHrest with (on_hand_sku := on_hand_sku) (reserved_sku := reserved_sku) (reorder_point_sku := reorder_point_sku); auto.
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
  induction store_d as [|[k' v'] rest]; intros k row Hinv Hlook; simpl in *.
  - inversion Hlook.
  - destruct Hinv as [Hrow_inv Hrest_inv].
    destruct (String.eqb k k') eqn:Heq.
    + injection Hlook as ->; auto.
    + apply IHrest; auto.
Qed.

(** O1: admissibility sanity — some state and args satisfy pre ∧ invariant. *)
Lemma o1_admissibility_sanity :
  exists sigma vs, gen_pre sigma vs /\ store_inv [(LitString "SKU1", (row_of (100) (10) (10)))].
Proof.
  exists [(store_loc, LitDict [(LitString "SKU1", row_of 100 10 10)])].
  exists [LitString "SKU1"; LitString "ORDER1"; LitInt 5].
  split.
  - unfold gen_pre.
    exists "SKU1", "ORDER1", 5, [(LitString "SKU1", row_of 100 10 10)], 100, 10, 10.
    repeat split; simpl; auto; lia.
  - unfold store_inv. simpl.
    unfold row_inv.
    exists 100, 10, 10.
    repeat split; auto; lia.
Qed.

(** O2: spec consistency — totality gives a post-satisfying outcome. *)
Lemma o2_spec_consistency : forall sigma vs,
  gen_pre sigma vs ->
  exists r ups, gen_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  apply (gen_table_total "release" gen_pre gen_post vs sigma).
  - unfold gen_table. rewrite String.eqb_refl. reflexivity.
  - exact Hpre.
Qed.

(** O3.0: exception consistency — the ReleaseExceedsReservedError arm is satisfiable. *)
Lemma o3_0_exception_consistency : forall sigma vs,
  gen_exc0_pre sigma vs ->
  exists r ups, gen_exc0_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  apply (gen_table_total "release_exc0" gen_exc0_pre gen_exc0_post vs sigma).
  - unfold gen_table. rewrite String.eqb_refl. reflexivity.
  - exact Hpre.
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
  intros. apply gen_preserves_inv_0 with (on_hand_sku := on_hand_sku) (reserved_sku := reserved_sku) (reorder_point_sku := reorder_point_sku); auto.
  - apply store_inv_lookup with (store_d := store_d); auto.
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
  intros sigma vs r ups Hpost l Hne.
  unfold gen_post in Hpost.
  destruct Hpost as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvs & Hsigma & Hlookup & Hr & Hups).
  subst ups.
  simpl.
  rewrite list_lookup_insert_ne; auto.
Qed.

End gen_release.