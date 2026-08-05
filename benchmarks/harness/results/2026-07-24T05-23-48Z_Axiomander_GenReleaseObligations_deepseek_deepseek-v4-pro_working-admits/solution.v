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
  - inversion Hgen; subst; clear Hgen.
    destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvs & Hsigma & Hlookup & Hpos & Hge).
    exists (RVal (LitInt reserved_sku)),
      [(store_loc, LitDict (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d))].
    split.
    + exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
      split; [exact Hvs|].
      split; [exact Hsigma|].
      split; [exact Hlookup|].
      auto.
    + unfold updates_dom_in.
      apply Forall_cons; [|apply Forall_nil].
      red. rewrite Hsigma. eauto.
  - destruct (String.eqb f "release_exc0") eqn:Eexc.
    + inversion Hgen; subst; clear Hgen.
      destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvs & Hsigma & Hlookup & Hlt).
      exists (RExn "ReleaseExceedsReservedError" (LitTuple [LitInt reserved_sku; LitString sku; LitString order; LitInt quantity])), [].
      split.
      * exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
        split; [exact Hvs|].
        split; [exact Hsigma|].
        split; [exact Hlookup|].
        auto.
      * unfold updates_dom_in. apply Forall_nil.
    + discriminate.
Qed.

Lemma gen_preserves_inv_0 : forall sku quantity store_d on_hand_sku reserved_sku reorder_point_sku,
  dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  row_inv (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  (quantity > 0)%Z ->
  (reserved_sku - quantity >= 0)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d).
Proof.
  intros sku quantity store_d on_hand_sku reserved_sku reorder_point_sku Hlookup Hrinv Hpos Hnneg Hinv.
  unfold row_inv in Hrinv.
  destruct Hrinv as (on_hand' & reserved' & reorder_point' & Heq & Hon & Hres & Hle).
  injection Heq as -> -> ->. clear Heq.
  induction store_d as [|[k' v'] store_d IH] in Hinv, Hlookup |- *.
  - inversion Hlookup.
  - destruct Hinv as [Hrinv_v' Hinv_rest].
    simpl in Hlookup.
    destruct k' as [| | kstr | | | | | | | |]; simpl in Hlookup.
    1-2,4-11: apply IH; [exact Hrinv_v'|exact Hinv_rest|exact Hlookup].
    destruct (String.eqb sku kstr) eqn:E.
    + inversion Hlookup; subst.
      apply String.eqb_eq in E. subst.
      simpl (dict_insert_str kstr (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) ((LitString kstr, v') :: store_d)).
      rewrite String.eqb_refl.
      split.
      * unfold row_inv.
        exists on_hand_sku, (reserved_sku - quantity), reorder_point_sku.
        split; [reflexivity|].
        split; [exact Hon|].
        split; [exact Hnneg|].
        lia.
      * exact Hinv_rest.
    + apply IH; [exact Hrinv_v'|exact Hinv_rest|exact Hlookup].
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
  induction store_d as [|[k' v] store_d IH].
  - intros k row Hinv Hlook. inversion Hlook.
  - intros k row [Hinv_row Hinv_rest] Hlook.
    simpl in Hlook.
    destruct k' as [| | kstr | | | | | | | |]; simpl in Hlook; try (apply (IH k row Hinv_rest Hlook)).
    destruct (String.eqb k kstr) eqn:E.
    + inversion Hlook; subst. exact Hinv_row.
    + apply (IH k row Hinv_rest Hlook).
Qed.

(** O1: admissibility sanity — some state and args satisfy pre ∧ invariant. *)
Lemma o1_admissibility_sanity :
  exists sigma vs, gen_pre sigma vs /\ store_inv [(LitString "SKU1", (row_of (100) (10) (10)))].
Proof.
  set (store_d := [(LitString "SKU1", row_of 100 10 10)]).
  exists {[store_loc := LitDict store_d]}, [LitString "SKU1"; LitString ""; LitInt 5].
  split.
  - unfold gen_pre.
    exists "SKU1", "", 5, store_d, 100, 10, 10.
    split; [reflexivity|].
    split; [by rewrite lookup_insert|].
    split.
    + simpl. rewrite String.eqb_refl. reflexivity.
    + split; lia.
  - unfold store_inv, store_d.
    simpl. split; [|exact I].
    unfold row_inv.
    exists 100, 10, 10.
    split; [reflexivity|].
    lia.
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
  intros sku order quantity store_d on_hand_sku reserved_sku reorder_point_sku Hpos Hge Hlookup Hinv.
  apply (gen_preserves_inv_0 sku quantity store_d on_hand_sku reserved_sku reorder_point_sku Hlookup).
  - apply (store_inv_lookup store_d sku (row_of on_hand_sku reserved_sku reorder_point_sku) Hinv Hlookup).
  - exact Hpos.
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
  destruct Hpost as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvs & Hsigma & Hlookup & Hr & Hups).
  subst ups; simpl.
  intros l Hneq.
  rewrite lookup_insert_ne; auto.
Qed.

End gen_release.