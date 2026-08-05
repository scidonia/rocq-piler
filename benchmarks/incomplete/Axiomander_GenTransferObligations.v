(** GENERATED FILE — proof obligations for [transfer].

    Source contract: examples.bank_transfer.contract:transfer_contract
    Generator: specsaver.lower (v2).  Do not edit by hand.

    Shape: multi-delta over keyed rows, N exception arms, typed fields.
    Deferred (v2, trace emission): state.notif_log, state.audit_log *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import AxiomanderLang AxiomanderWp.
Require Import AxiomanderPrelude.

Section gen_transfer.
Context `{FC : FunCtx}.

Definition store_loc : loc := Loc 1%positive.
Definition trace_loc : loc := Loc 2%positive.


Definition row_of (balance : Z) (currency : string) : sn_val :=
  LitDict [(LitString "balance", LitInt balance);
           (LitString "currency", LitString currency)].

Definition row_inv (v : sn_val) : Prop :=
  exists balance currency,
    v = (row_of (balance) (currency)) /\ (balance >= 0)%Z.

Fixpoint store_inv (kvs : list (sn_val * sn_val)) : Prop :=
  match kvs with
  | [] => True
  | (_, v) :: rest => row_inv v /\ store_inv rest
  end.

Definition gen_pre (sigma : sn_state) (vs : list sn_val) : Prop :=
  exists source_id target_id order amount store_d balance_source_id currency_source_id balance_target_id currency_target_id,
    vs = [LitString source_id; LitString target_id; LitString order; LitInt amount] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str source_id store_d = Some (row_of (balance_source_id) (currency_source_id)) /\
    dict_lookup_str target_id store_d = Some (row_of (balance_target_id) (currency_target_id)) /\
    (amount > 0)%Z /\ (source_id <> target_id) /\ (((currency_source_id <> currency_target_id) \/ (balance_source_id >= amount)%Z) /\ ((currency_source_id = currency_target_id))).

Definition gen_post (sigma : sn_state) (vs : list sn_val)
    (r : Result) (ups : cell_updates) : Prop :=
  exists source_id target_id order amount store_d balance_source_id currency_source_id balance_target_id currency_target_id,
    vs = [LitString source_id; LitString target_id; LitString order; LitInt amount] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str source_id store_d = Some (row_of (balance_source_id) (currency_source_id)) /\
    dict_lookup_str target_id store_d = Some (row_of (balance_target_id) (currency_target_id)) /\
    r = RVal (LitInt balance_source_id) /\
    ups = [(store_loc, LitDict (dict_insert_str target_id (row_of (balance_target_id + amount) (currency_target_id)) (dict_insert_str source_id (row_of (balance_source_id - amount) (currency_source_id)) store_d)))].

Definition gen_exc0_pre (sigma : sn_state) (vs : list sn_val) : Prop :=
  exists source_id target_id order amount store_d balance_source_id currency_source_id balance_target_id currency_target_id,
    vs = [LitString source_id; LitString target_id; LitString order; LitInt amount] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str source_id store_d = Some (row_of (balance_source_id) (currency_source_id)) /\
    dict_lookup_str target_id store_d = Some (row_of (balance_target_id) (currency_target_id)) /\
    (currency_source_id = currency_target_id) /\
    (balance_source_id < amount)%Z.

Definition gen_exc0_post (sigma : sn_state) (vs : list sn_val)
    (r : Result) (ups : cell_updates) : Prop :=
  exists source_id target_id order amount store_d balance_source_id currency_source_id balance_target_id currency_target_id,
    vs = [LitString source_id; LitString target_id; LitString order; LitInt amount] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str source_id store_d = Some (row_of (balance_source_id) (currency_source_id)) /\
    dict_lookup_str target_id store_d = Some (row_of (balance_target_id) (currency_target_id)) /\
    r = RExn "InsufficientFundsError" (LitTuple [LitString source_id; LitInt amount]) /\ ups = [].

Definition gen_exc1_pre (sigma : sn_state) (vs : list sn_val) : Prop :=
  exists source_id target_id order amount store_d balance_source_id currency_source_id balance_target_id currency_target_id,
    vs = [LitString source_id; LitString target_id; LitString order; LitInt amount] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str source_id store_d = Some (row_of (balance_source_id) (currency_source_id)) /\
    dict_lookup_str target_id store_d = Some (row_of (balance_target_id) (currency_target_id)) /\
    (currency_source_id <> currency_target_id).

Definition gen_exc1_post (sigma : sn_state) (vs : list sn_val)
    (r : Result) (ups : cell_updates) : Prop :=
  exists source_id target_id order amount store_d balance_source_id currency_source_id balance_target_id currency_target_id,
    vs = [LitString source_id; LitString target_id; LitString order; LitInt amount] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str source_id store_d = Some (row_of (balance_source_id) (currency_source_id)) /\
    dict_lookup_str target_id store_d = Some (row_of (balance_target_id) (currency_target_id)) /\
    r = RExn "CurrencyMismatchError" (LitTuple [LitString source_id; LitString target_id]) /\ ups = [].

Definition gen_table (f : string) : option fun_entry :=
  if String.eqb f "transfer" then Some (FunSpecS gen_pre gen_post)
  else if String.eqb f "transfer_exc0" then
  Some (FunSpecS gen_exc0_pre gen_exc0_post)
  else if String.eqb f "transfer_exc1" then
  Some (FunSpecS gen_exc1_pre gen_exc1_post)
  else None.

Lemma gen_table_total : forall f pre post vs sigma,
  gen_table f = Some (FunSpecS pre post) ->
  pre sigma vs ->
  exists r ups, post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
Admitted.

Lemma gen_preserves_inv_0 : forall source_id amount store_d balance_source_id currency_source_id,
  dict_lookup_str source_id store_d = Some (row_of (balance_source_id) (currency_source_id)) ->
  row_inv (row_of (balance_source_id) (currency_source_id)) ->
  (amount > 0)%Z ->
  (balance_source_id - amount >= 0)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str source_id (row_of (balance_source_id - amount) (currency_source_id)) store_d).
Proof.
Admitted.

Lemma gen_preserves_inv_1 : forall target_id amount store_d balance_target_id currency_target_id,
  dict_lookup_str target_id store_d = Some (row_of (balance_target_id) (currency_target_id)) ->
  row_inv (row_of (balance_target_id) (currency_target_id)) ->
  (amount > 0)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str target_id (row_of (balance_target_id + amount) (currency_target_id)) store_d).
Proof.
Admitted.

#[global] Instance gen_fun_ctx : FunCtx :=
  {| fun_entries := gen_table;
     fun_specs_total := gen_table_total_pure;
     fun_specsS_total := gen_table_total |}.

Lemma store_inv_lookup : forall store_d k row,
  store_inv store_d ->
  dict_lookup_str k store_d = Some row ->
  row_inv row.
Proof.
Admitted.

(** O1: admissibility sanity — some state and args satisfy pre ∧ invariant. *)
Lemma o1_admissibility_sanity :
  exists sigma vs, gen_pre sigma vs /\ store_inv [(LitString "SOURCE_ID1", (row_of (100) ("USD"))); (LitString "TARGET_ID1", (row_of (100) ("USD")))].
Proof.
Admitted.

(** O2: spec consistency — totality gives a post-satisfying outcome. *)
Lemma o2_spec_consistency : forall sigma vs,
  gen_pre sigma vs ->
  exists r ups, gen_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
Admitted.

(** O3.0: exception consistency — the InsufficientFundsError arm is satisfiable. *)
Lemma o3_0_exception_consistency : forall sigma vs,
  gen_exc0_pre sigma vs ->
  exists r ups, gen_exc0_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
Admitted.

(** O3.1: exception consistency — the CurrencyMismatchError arm is satisfiable. *)
Lemma o3_1_exception_consistency : forall sigma vs,
  gen_exc1_pre sigma vs ->
  exists r ups, gen_exc1_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
Admitted.

(** O4: exit coverage — availability and the exit conditions partition. *)
Lemma o4_exit_coverage : forall (balance_source_id balance_target_id amount : Z) (currency_source_id currency_target_id source_id target_id : string),
  (((currency_source_id <> currency_target_id) \/ (balance_source_id >= amount)%Z) /\ ((currency_source_id = currency_target_id))) \/ (((currency_source_id = currency_target_id) /\ (balance_source_id < amount)%Z) \/ ((currency_source_id <> currency_target_id))).
Proof.
Admitted.

(** O5: invariant preservation across the nested delta updates. *)
Lemma o5_invariant_preservation : forall (source_id target_id order : string) (amount : Z) (store_d : list (sn_val * sn_val)) (balance_source_id balance_target_id : Z) (currency_source_id currency_target_id : string),
  ((amount > 0)%Z /\ (source_id <> target_id)) ->
  (((currency_source_id <> currency_target_id) \/ (balance_source_id >= amount)%Z) /\ ((currency_source_id = currency_target_id))) ->
  dict_lookup_str source_id store_d = Some (row_of (balance_source_id) (currency_source_id)) ->
    dict_lookup_str target_id store_d = Some (row_of (balance_target_id) (currency_target_id)) ->
  store_inv store_d ->
  store_inv (dict_insert_str target_id (row_of (balance_target_id + amount) (currency_target_id)) (dict_insert_str source_id (row_of (balance_source_id - amount) (currency_source_id)) store_d)).
Proof.
Admitted.

(** O8: frame soundness — everything outside the declared frame is
    unchanged.  The generated footprint is the single store cell; every
    other location (including the trace cell) is preserved. *)
Lemma o8_frame_soundness : forall sigma vs r ups,
  gen_post sigma vs r ups ->
  forall l, l <> store_loc ->
    (apply_updates sigma ups) !! l = sigma !! l.
Proof.
Admitted.

End gen_transfer.