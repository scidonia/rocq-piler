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
  - injection Hgen as Hpre_eq Hpost; subst pre post.
    unfold gen_pre in Hpre.
    destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & -> & Hsigma & Hlook & Hpos & Hge).
    exists (RVal (LitInt reserved_sku)), [(store_loc, LitDict (dict_insert_str sku (row_of on_hand_sku (reserved_sku - quantity) reorder_point_sku) store_d))].
    split.
    + unfold gen_post.
      exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
      repeat split; auto.
    + unfold updates_dom_in; constructor.
      -- simpl; rewrite Hsigma; eauto.
      -- constructor.
  - destruct (String.eqb f "release_exc0") eqn:Eexc.
    + injection Hgen as Hpre_eq Hpost; subst pre post.
      unfold gen_exc0_pre in Hpre.
      destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & -> & Hsigma & Hlook & Hlt).
      exists (RExn "ReleaseExceedsReservedError" (LitTuple [LitInt reserved_sku; LitString sku; LitString order; LitInt quantity])), [].
      split.
      * unfold gen_exc0_post.
        exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
        repeat split; auto.
      * unfold updates_dom_in; simpl; constructor.
    + discriminate.
Qed.

Open Scope Z_scope.

Lemma row_inv_update : forall on_hand reserved reorder_point quantity,
  (on_hand >= 0)%Z -> (reserved >= 0)%Z -> (reserved <= on_hand)%Z ->
  (quantity > 0)%Z -> (reserved - quantity >= 0)%Z ->
  row_inv (row_of on_hand (reserved - quantity) reorder_point).
Proof.
  intros on_hand reserved reorder_point quantity ? ? ? ? ?.
  unfold row_inv.
  exists on_hand. exists (reserved - quantity). exists reorder_point.
  split; [reflexivity|]. lia.
Qed.

Lemma gen_preserves_inv_0 : forall sku quantity store_d on_hand_sku reserved_sku reorder_point_sku,
  dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  row_inv (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  (quantity > 0)%Z ->
  (reserved_sku - quantity >= 0)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d).
Proof.
  induction store_d as [|[k' v] rest IH]; intros on_hand_sku reserved_sku reorder_point_sku Hlook Hrow Hpos Hge Hinv.
  { inversion Hlook. }
  simpl in Hinv; destruct Hinv as [Hrow_v Hinv_rest].
  simpl in Hlook.
  destruct k'.
  1,2,4-11: (simpl; split; [exact Hrow_v|]; eapply IH; eauto).
  (* LitString s *)
  simpl in Hlook; destruct (String.eqb sku s) eqn:Heq.
  - apply String.eqb_eq in Heq; subst s. inversion Hlook; subst.
    unfold row_inv in Hrow.
    destruct Hrow as (a & b & c & Hrow_eq & Ha & Hb & Hc).
    injection Hrow_eq as <- <- <-.
    simpl dict_insert_str; rewrite String.eqb_refl; simpl dict_insert_str.
    simpl store_inv.
    split; [| exact Hinv_rest].
    apply row_inv_update; assumption.
  - simpl dict_insert_str. rewrite Heq. simpl dict_insert_str. simpl store_inv. split; [exact Hrow_v|]; eapply IH; eauto.
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
  induction store_d as [|[k' v] rest IH]; intros k row Hinv Hlook.
  - inversion Hlook.
  - destruct Hinv as [Hrow Hinv_rest].
    simpl in Hlook.
    destruct k' as [| | s | | | | | | | |]; simpl in Hlook.
    + eapply IH; eauto.
    + eapply IH; eauto.
    + destruct (String.eqb k s) eqn:Heq.
      * apply String.eqb_eq in Heq; subst s.
        inversion Hlook; subst.
        exact Hrow.
      * eapply IH; eauto.
    + eapply IH; eauto.
    + eapply IH; eauto.
    + eapply IH; eauto.
    + eapply IH; eauto.
    + eapply IH; eauto.
    + eapply IH; eauto.
    + eapply IH; eauto.
    + eapply IH; eauto.
Qed.

(** O1: admissibility sanity — some state and args satisfy pre ∧ invariant. *)
Lemma o1_admissibility_sanity :
  exists sigma vs, gen_pre sigma vs /\ store_inv [(LitString "SKU1", (row_of (100) (10) (10)))].
Proof.
  exists {[store_loc := LitDict [(LitString "SKU1", row_of 100 10 10)]]}, [LitString "SKU1"; LitString "ORDER1"; LitInt 5].
  split.
  - unfold gen_pre.
    exists "SKU1", "ORDER1", 5%Z, [(LitString "SKU1", row_of 100 10 10)], 100%Z, 10%Z, 10%Z.
    split; [reflexivity|].
    split.
    + rewrite lookup_singleton. destruct (decide (store_loc = store_loc)); [reflexivity|exfalso; apply n; reflexivity].
    + split; [reflexivity|].
      split; lia.
  - refine (conj _ I).
    unfold row_inv.
    exists 100%Z, 10%Z, 10%Z.
    split; [reflexivity|].
    lia.
Qed.

(** O2: spec consistency — totality gives a post-satisfying outcome. *)
Lemma o2_spec_consistency : forall sigma vs,
  gen_pre sigma vs ->
  exists r ups, gen_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  eapply (gen_table_total "release" gen_pre gen_post).
  - reflexivity.
  - exact Hpre.
Qed.

(** O3.0: exception consistency — the ReleaseExceedsReservedError arm is satisfiable. *)
Lemma o3_0_exception_consistency : forall sigma vs,
  gen_exc0_pre sigma vs ->
  exists r ups, gen_exc0_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  eapply (gen_table_total "release_exc0" gen_exc0_pre gen_exc0_post).
  - reflexivity.
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
  intros sku order quantity store_d on_hand_sku reserved_sku reorder_point_sku Hpos Hge Hlook Hinv.
  apply gen_preserves_inv_0 with (sku:=sku) (quantity:=quantity) (on_hand_sku:=on_hand_sku) (reserved_sku:=reserved_sku) (reorder_point_sku:=reorder_point_sku); auto.
  - apply store_inv_lookup with (store_d:=store_d) (k:=sku) (row:=row_of on_hand_sku reserved_sku reorder_point_sku); auto.
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
  unfold gen_post in Hpost.
  destruct Hpost as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & -> & _ & _ & -> & ->).
  simpl.
  intros l Hneq.
  rewrite lookup_insert_ne; auto.
Qed.

End gen_release.