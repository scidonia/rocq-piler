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
  - apply String.eqb_eq in Erel. subst f.
    simpl in Hgen. inversion Hgen; subst; clear Hgen.
    unfold gen_pre in Hpre.
    destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvs & Hstore & Hlookup & Hgt & Hge).
    subst vs.
    exists (RVal (LitInt reserved_sku)), [(store_loc, LitDict (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d))].
    split.
    + unfold gen_post.
      exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
      repeat split; eauto.
    + unfold updates_dom_in.
      simpl.
      constructor.
      * rewrite Hstore. eexists; eauto.
      * constructor.
  - destruct (String.eqb f "release_exc0") eqn:Eexc.
    + apply String.eqb_eq in Eexc. subst f.
      simpl in Hgen. inversion Hgen; subst; clear Hgen.
      unfold gen_exc0_pre in Hpre.
      destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvs & Hstore & Hlookup & Hlt).
      subst vs.
      exists (RExn "ReleaseExceedsReservedError" (LitTuple [LitInt reserved_sku; LitString sku; LitString order; LitInt quantity])), [].
      split.
      * unfold gen_exc0_post.
        exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
        repeat split; eauto.
      * unfold updates_dom_in.
        constructor.
    + discriminate.
Qed.

Lemma row_inv_ineqs : forall on_hand reserved reorder,
  row_inv (row_of on_hand reserved reorder) ->
  (on_hand >= 0)%Z /\ (reserved >= 0)%Z /\ (reserved <= on_hand)%Z.
Proof.
  intros on_hand reserved reorder H.
  unfold row_inv in H.
  destruct H as (oh & r & rp & Heq & Hoh & Hr & Hle).
  unfold row_of in Heq.
  inversion Heq. subst; auto.
Qed.

Lemma gen_preserves_inv_0 : forall sku quantity store_d on_hand_sku reserved_sku reorder_point_sku,
  dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  row_inv (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  (quantity > 0)%Z ->
  (reserved_sku - quantity >= 0)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d).
Proof.
  induction store_d as [| [k' v] rest IH]; simpl;
    intros on_hand_sku reserved_sku reorder_point_sku Hlook Hrow_inv Hgt Hge Hinv.
  - discriminate.
  - destruct Hinv as [Hv Hrest].
    destruct k' as [n0 | b0 | s0 | f0 | l0 | | lab0 pay0 | vsa0 | vsb0 | kvs0 | vsc0 ].
    + simpl in Hlook; simpl; split; [exact Hv|]; eapply IH; eauto.
    + simpl in Hlook; simpl; split; [exact Hv|]; eapply IH; eauto.
    + simpl in Hlook.
      destruct (String.eqb sku s0).
      * simpl in Hlook. injection Hlook as ->.
        simpl. split.
        { apply row_inv_ineqs in Hrow_inv as (Hoh & Hr & Hle).
          unfold row_inv.
          exists (on_hand_sku : Z), ((reserved_sku - quantity)%Z : Z), (reorder_point_sku : Z).
          split; [reflexivity|].
          split; [exact Hoh|].
          split; [exact Hge|].
          cut ((reserved_sku - quantity <= on_hand_sku)%Z). 1: auto. lia. }
        { exact Hrest. }
      * simpl; split; [exact Hv|]; eapply IH; eauto.
    + simpl in Hlook; simpl; split; [exact Hv|]; eapply IH; eauto.
    + simpl in Hlook; simpl; split; [exact Hv|]; eapply IH; eauto.
    + simpl in Hlook; simpl; split; [exact Hv|]; eapply IH; eauto.
    + simpl in Hlook; simpl; split; [exact Hv|]; eapply IH; eauto.
    + simpl in Hlook; simpl; split; [exact Hv|]; eapply IH; eauto.
    + simpl in Hlook; simpl; split; [exact Hv|]; eapply IH; eauto.
    + simpl in Hlook; simpl; split; [exact Hv|]; eapply IH; eauto.
    + simpl in Hlook; simpl; split; [exact Hv|]; eapply IH; eauto.
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
  induction store_d as [| [k' v] rest IH]; simpl; intros k row Hinv Hlook.
  - discriminate.
  - destruct Hinv as [Hrow Hrest].
    destruct k' as [| | k'_str | | | | | | | |];
      simpl in Hlook; try (apply (IH k row); [exact Hrest| exact Hlook]).
    simpl in Hlook.
    destruct (String.eqb k k'_str) eqn:E.
    + injection Hlook as ->.
      exact Hrow.
    + apply IH with (k := k); auto.
Qed.

(** O1: admissibility sanity — some state and args satisfy pre ∧ invariant. *)
Lemma o1_admissibility_sanity :
  exists sigma vs, gen_pre sigma vs /\ store_inv [(LitString "SKU1", (row_of (100) (10) (10)))].
Proof.
  set (store_d := [(LitString "SKU1", row_of (100) (10) (10))]).
  exists {[ store_loc := LitDict store_d ]}, [LitString "SKU1"; LitString "ORDER1"; LitInt 1].
  split.
  - unfold gen_pre.
    exists "SKU1", "ORDER1", 1%Z, store_d, 100%Z, 10%Z, 10%Z.
    split; [reflexivity|].
    split; [rewrite lookup_singleton_eq; reflexivity|].
    split; [simpl; reflexivity|].
    split; [lia|].
    lia.
  - unfold store_d; simpl.
    split; [| exact I].
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
  unfold gen_pre in Hpre.
  destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvs & Hstore & Hlookup & Hgt & Hge).
  subst vs.
  exists (RVal (LitInt reserved_sku)), [(store_loc, LitDict (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d))].
  split.
  - unfold gen_post.
    exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
    repeat split; eauto.
  - unfold updates_dom_in.
    simpl.
    constructor.
    + rewrite Hstore. eexists; eauto.
    + constructor.
Qed.

(** O3.0: exception consistency — the ReleaseExceedsReservedError arm is satisfiable. *)
Lemma o3_0_exception_consistency : forall sigma vs,
  gen_exc0_pre sigma vs ->
  exists r ups, gen_exc0_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  unfold gen_exc0_pre in Hpre.
  destruct Hpre as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvs & Hstore & Hlookup & Hlt).
  subst vs.
  exists (RExn "ReleaseExceedsReservedError" (LitTuple [LitInt reserved_sku; LitString sku; LitString order; LitInt quantity])), [].
  split.
  - unfold gen_exc0_post.
    exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku.
    repeat split; eauto.
  - unfold updates_dom_in.
    constructor.
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
  intros sku order quantity store_d on_hand_sku reserved_sku reorder_point_sku Hgt Hge Hlook Hinv.
  apply gen_preserves_inv_0 with (quantity := quantity) (on_hand_sku := on_hand_sku) (reserved_sku := reserved_sku) (reorder_point_sku := reorder_point_sku); auto.
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
  unfold gen_post in Hpost.
  destruct Hpost as (sku & order & quantity & store_d & on_hand_sku & reserved_sku & reorder_point_sku & Hvs & Hstore & Hlookup & Hr & Hups).
  subst ups r vs.
  simpl (apply_updates sigma [(store_loc, LitDict (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku - quantity) (reorder_point_sku)) store_d))]).
  intros l Hneq.
  apply lookup_insert_ne; auto.
Qed.

End gen_release.