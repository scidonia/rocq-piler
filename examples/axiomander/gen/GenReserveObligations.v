(** GENERATED FILE — proof obligations for [reserve].

    Source contract: examples.inventory.contract:reserve_contract
    Generator: specsaver.lower (v2).  Do not edit by hand.

    Shape: multi-delta over keyed rows, N exception arms, typed fields.
    Deferred (v2, trace emission): state.gauge_log, state.reservation_log, state.alert_log *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.
Require Import SpecPrelude.

Section gen_reserve.
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
    (quantity > 0)%Z /\ (((on_hand_sku - reserved_sku >= quantity)%Z)).

Definition gen_post (sigma : sn_state) (vs : list sn_val)
    (r : Result) (ups : cell_updates) : Prop :=
  exists sku order quantity store_d on_hand_sku reserved_sku reorder_point_sku,
    vs = [LitString sku; LitString order; LitInt quantity] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) /\
    r = RVal (LitInt reserved_sku) /\
    ups = [(store_loc, LitDict (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku + quantity) (reorder_point_sku)) store_d))].

Definition gen_exc0_pre (sigma : sn_state) (vs : list sn_val) : Prop :=
  exists sku order quantity store_d on_hand_sku reserved_sku reorder_point_sku,
    vs = [LitString sku; LitString order; LitInt quantity] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) /\
    (on_hand_sku - reserved_sku < quantity)%Z.

Definition gen_exc0_post (sigma : sn_state) (vs : list sn_val)
    (r : Result) (ups : cell_updates) : Prop :=
  exists sku order quantity store_d on_hand_sku reserved_sku reorder_point_sku,
    vs = [LitString sku; LitString order; LitInt quantity] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) /\
    r = RExn "InsufficientStockError" (LitTuple [LitInt (on_hand_sku - reserved_sku); LitString sku; LitString order; LitInt quantity]) /\ ups = [].

Definition gen_table (f : string) : option fun_entry :=
  if String.eqb f "reserve" then Some (FunSpecS gen_pre gen_post)
  else if String.eqb f "reserve_exc0" then
  Some (FunSpecS gen_exc0_pre gen_exc0_post)
  else None.

Lemma gen_table_total_pure : forall f pre post vs,
  gen_table f = Some (FunSpec pre post) ->
  pre vs -> exists v, post vs v.
Proof.
  intros f pre post vs Hfe _. unfold gen_table in Hfe.
  destruct (String.eqb f "reserve"), (String.eqb f "reserve_exc0"); discriminate.
Qed.

Lemma gen_table_total : forall f pre post vs sigma,
  gen_table f = Some (FunSpecS pre post) ->
  pre sigma vs ->
  exists r ups, post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros f pre post vs sigma Hfe Hpre. unfold gen_table in Hfe.
  destruct (String.eqb f "reserve") eqn:E,
           (String.eqb f "reserve_exc0") eqn:E2;
    try discriminate.
  all: try solve [injection Hfe as Heq; subst pre post; destruct Hpre as [sku [order [quantity [store_d [on_hand_sku [reserved_sku [reorder_point_sku [Hvs [Hcell [Hlook_sku [Hsc Havail]]]]]]]]]]]; exists (RVal (LitInt reserved_sku)), [(store_loc, LitDict (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku + quantity) (reorder_point_sku)) store_d))]; split; [exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku; repeat split; auto | unfold updates_dom_in; constructor; [|constructor]; simpl; rewrite Hcell; eexists; reflexivity]].
  all: try solve [injection Hfe as Heq; subst pre post; destruct Hpre as [sku [order [quantity [store_d [on_hand_sku [reserved_sku [reorder_point_sku [Hvs [Hcell [Hlook_sku Hwhen]]]]]]]]]]; exists (RExn "InsufficientStockError" (LitTuple [LitInt (on_hand_sku - reserved_sku); LitString sku; LitString order; LitInt quantity])), []; split; [exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku; repeat split; auto | unfold updates_dom_in; constructor]].
Qed.

Lemma gen_preserves_inv_0 : forall sku quantity store_d on_hand_sku reserved_sku reorder_point_sku,
  dict_lookup_str sku store_d = Some (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  row_inv (row_of (on_hand_sku) (reserved_sku) (reorder_point_sku)) ->
  (quantity > 0)%Z ->
  (on_hand_sku - reserved_sku >= quantity)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str sku (row_of (on_hand_sku) (reserved_sku + quantity) (reorder_point_sku)) store_d).
Proof.
  induction store_d as [|kv rest IH]; intros on_hand_sku reserved_sku reorder_point_sku Hlook Hprod Hpos Hdelta Hinv;
    simpl in Hlook |- *.
  - discriminate.
  - destruct kv as [k0 v0].
    destruct Hinv as [Hfst Hrest].
    destruct k0 as [| | s | | | | | | | |]; simpl in *;
      try (split; [exact Hfst | apply (IH on_hand_sku reserved_sku reorder_point_sku Hlook Hprod Hpos Hdelta Hrest)]).
    destruct (String.eqb sku s) eqn:E.
    + apply String.eqb_eq in E. subst s.
      injection Hlook as Hlook. subst v0.
      split; [|exact Hrest].
      destruct Hprod as [on_hand_sku0 [reserved_sku0 [reorder_point_sku0 [Heq [Hr Hlo]]
        ]]].
      injection Heq as He_on_hand_sku He_reserved_sku He_reorder_point_sku.
      subst on_hand_sku0 reserved_sku0 reorder_point_sku0.
      exists on_hand_sku, (reserved_sku + quantity)%Z, reorder_point_sku.
      split; [reflexivity|]. split; lia.
    + split; [exact Hfst|].
      apply (IH on_hand_sku reserved_sku reorder_point_sku Hlook Hprod Hpos Hdelta Hrest).
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
  induction store_d as [|kv rest IH]; intros k row Hinv Hlook; simpl in *.
  - discriminate.
  - destruct kv as [k0 v0].
    destruct Hinv as [Hfst Hrest].
    destruct k0 as [| | s | | | | | | | |]; simpl in *;
      try (apply (IH k row Hrest Hlook)).
    destruct (String.eqb k s) eqn:E.
    + injection Hlook as Hlook. subst v0. exact Hfst.
    + apply (IH k row Hrest Hlook).
Qed.

(** O1: admissibility sanity — some state and args satisfy pre ∧ invariant. *)
Lemma o1_admissibility_sanity :
  exists sigma vs, gen_pre sigma vs /\ store_inv [(LitString "SKU1", (row_of (100) (10) (10)))].
Proof.
  exists {[ store_loc := LitDict [(LitString "SKU1", (row_of (100) (10) (10)))];
             trace_loc := LitList [] ]},
         [LitString "SKU1"; LitString "O1"; LitInt 5].
  split.
  - exists "SKU1", "O1", 5%Z, [(LitString "SKU1", (row_of (100) (10) (10)))], 100, 10, 10.
    split; [reflexivity|].
    split; [apply lookup_insert_eq|].
    split; [reflexivity|].
    split; [lia| lia].
  - repeat split; try exact I.
    exists 100, 10, 10. split; [reflexivity|]. repeat split; lia.
    
Qed.

(** O2: spec consistency — totality gives a post-satisfying outcome. *)
Lemma o2_spec_consistency : forall sigma vs,
  gen_pre sigma vs ->
  exists r ups, gen_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  eapply (gen_table_total "reserve" gen_pre gen_post vs sigma
            eq_refl Hpre).
Qed.

(** O3.0: exception consistency — the InsufficientStockError arm is satisfiable. *)
Lemma o3_0_exception_consistency : forall sigma vs,
  gen_exc0_pre sigma vs ->
  exists r ups, gen_exc0_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  destruct Hpre as [sku [order [quantity [store_d [on_hand_sku [reserved_sku [reorder_point_sku [Hvs [Hcell [Hlook_sku Hwhen]]]]]]]]]].
  exists (RExn "InsufficientStockError" (LitTuple [LitInt (on_hand_sku - reserved_sku); LitString sku; LitString order; LitInt quantity])), [].
  split.
  - exists sku, order, quantity, store_d, on_hand_sku, reserved_sku, reorder_point_sku. repeat split; auto.
  - unfold updates_dom_in. constructor.
Qed.

(** O4: exit coverage — availability and the exit conditions partition. *)
Lemma o4_exit_coverage : forall (on_hand_sku reserved_sku reorder_point_sku quantity : Z) ( sku : string),
  (((on_hand_sku - reserved_sku >= quantity)%Z)) \/ (((on_hand_sku - reserved_sku < quantity)%Z)).
Proof. intros. lia. Qed.

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

End gen_reserve.