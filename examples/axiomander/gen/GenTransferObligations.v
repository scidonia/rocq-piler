(** GENERATED FILE — proof obligations for [transfer].

    Source contract: examples.bank_transfer.contract:transfer_contract
    Generator: specsaver.lower (v2).  Do not edit by hand.

    Shape: multi-delta over keyed rows, N exception arms, typed fields.
    Deferred (v2, trace emission): state.notif_log, state.audit_log *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.
Require Import SpecPrelude.

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

Lemma gen_table_total_pure : forall f pre post vs,
  gen_table f = Some (FunSpec pre post) ->
  pre vs -> exists v, post vs v.
Proof.
  intros f pre post vs Hfe _. unfold gen_table in Hfe.
  destruct (String.eqb f "transfer"), (String.eqb f "transfer_exc0"), (String.eqb f "transfer_exc1"); discriminate.
Qed.

Lemma gen_table_total : forall f pre post vs sigma,
  gen_table f = Some (FunSpecS pre post) ->
  pre sigma vs ->
  exists r ups, post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros f pre post vs sigma Hfe Hpre. unfold gen_table in Hfe.
  destruct (String.eqb f "transfer") eqn:E,
           (String.eqb f "transfer_exc0") eqn:E2,
           (String.eqb f "transfer_exc1") eqn:E3;
    try discriminate.
  all: try solve [injection Hfe as Heq; subst pre post; destruct Hpre as [source_id [target_id [order [amount [store_d [balance_source_id [currency_source_id [balance_target_id [currency_target_id [Hvs [Hcell [Hlook_source_id [Hlook_target_id [Hsc Havail]]]]]]]]]]]]]]; exists (RVal (LitInt balance_source_id)), [(store_loc, LitDict (dict_insert_str target_id (row_of (balance_target_id + amount) (currency_target_id)) (dict_insert_str source_id (row_of (balance_source_id - amount) (currency_source_id)) store_d)))]; split; [exists source_id, target_id, order, amount, store_d, balance_source_id, currency_source_id, balance_target_id, currency_target_id; repeat split; auto | unfold updates_dom_in; constructor; [|constructor]; simpl; rewrite Hcell; eexists; reflexivity]].
  all: try solve [injection Hfe as Heq; subst pre post; destruct Hpre as [source_id [target_id [order [amount [store_d [balance_source_id [currency_source_id [balance_target_id [currency_target_id [Hvs [Hcell [Hlook_source_id [Hlook_target_id Hwhen]]]]]]]]]]]]]; exists (RExn "InsufficientFundsError" (LitTuple [LitString source_id; LitInt amount])), []; split; [exists source_id, target_id, order, amount, store_d, balance_source_id, currency_source_id, balance_target_id, currency_target_id; repeat split; auto | unfold updates_dom_in; constructor]].
  all: try solve [injection Hfe as Heq; subst pre post; destruct Hpre as [source_id [target_id [order [amount [store_d [balance_source_id [currency_source_id [balance_target_id [currency_target_id [Hvs [Hcell [Hlook_source_id [Hlook_target_id Hwhen]]]]]]]]]]]]]; exists (RExn "CurrencyMismatchError" (LitTuple [LitString source_id; LitString target_id])), []; split; [exists source_id, target_id, order, amount, store_d, balance_source_id, currency_source_id, balance_target_id, currency_target_id; repeat split; auto | unfold updates_dom_in; constructor]].
Qed.

Lemma gen_preserves_inv_0 : forall source_id amount store_d balance_source_id currency_source_id,
  dict_lookup_str source_id store_d = Some (row_of (balance_source_id) (currency_source_id)) ->
  row_inv (row_of (balance_source_id) (currency_source_id)) ->
  (amount > 0)%Z ->
  (balance_source_id - amount >= 0)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str source_id (row_of (balance_source_id - amount) (currency_source_id)) store_d).
Proof.
  induction store_d as [|kv rest IH]; intros balance_source_id currency_source_id Hlook Hprod Hpos Hdelta Hinv;
    simpl in Hlook |- *.
  - discriminate.
  - destruct kv as [k0 v0].
    destruct Hinv as [Hfst Hrest].
    destruct k0 as [| | s | | | | | | | |]; simpl in *;
      try (split; [exact Hfst | apply (IH balance_source_id currency_source_id Hlook Hprod Hpos Hdelta Hrest)]).
    destruct (String.eqb source_id s) eqn:E.
    + apply String.eqb_eq in E. subst s.
      injection Hlook as Hlook. subst v0.
      split; [|exact Hrest].
      destruct Hprod as [balance_source_id0 [currency_source_id0 [Heq Hr]
        ]].
      injection Heq as He_balance_source_id He_currency_source_id.
      subst balance_source_id0 currency_source_id0.
      exists (balance_source_id - amount)%Z, currency_source_id.
      split; [reflexivity|]. lia.
    + split; [exact Hfst|].
      apply (IH balance_source_id currency_source_id Hlook Hprod Hpos Hdelta Hrest).
Qed.

Lemma gen_preserves_inv_1 : forall target_id amount store_d balance_target_id currency_target_id,
  dict_lookup_str target_id store_d = Some (row_of (balance_target_id) (currency_target_id)) ->
  row_inv (row_of (balance_target_id) (currency_target_id)) ->
  (amount > 0)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str target_id (row_of (balance_target_id + amount) (currency_target_id)) store_d).
Proof.
  induction store_d as [|kv rest IH]; intros balance_target_id currency_target_id Hlook Hprod Hpos Hinv;
    simpl in Hlook |- *.
  - discriminate.
  - destruct kv as [k0 v0].
    destruct Hinv as [Hfst Hrest].
    destruct k0 as [| | s | | | | | | | |]; simpl in *;
      try (split; [exact Hfst | apply (IH balance_target_id currency_target_id Hlook Hprod Hpos Hrest)]).
    destruct (String.eqb target_id s) eqn:E.
    + apply String.eqb_eq in E. subst s.
      injection Hlook as Hlook. subst v0.
      split; [|exact Hrest].
      destruct Hprod as [balance_target_id0 [currency_target_id0 [Heq Hr]
        ]].
      injection Heq as He_balance_target_id He_currency_target_id.
      subst balance_target_id0 currency_target_id0.
      exists (balance_target_id + amount)%Z, currency_target_id.
      split; [reflexivity|]. lia.
    + split; [exact Hfst|].
      apply (IH balance_target_id currency_target_id Hlook Hprod Hpos Hrest).
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
  exists sigma vs, gen_pre sigma vs /\ store_inv [(LitString "SOURCE_ID1", (row_of (100) ("USD"))); (LitString "TARGET_ID1", (row_of (100) ("USD")))].
Proof.
  exists {[ store_loc := LitDict [(LitString "SOURCE_ID1", (row_of (100) ("USD"))); (LitString "TARGET_ID1", (row_of (100) ("USD")))];
             trace_loc := LitList [] ]},
         [LitString "SOURCE_ID1"; LitString "TARGET_ID1"; LitString "O1"; LitInt 5].
  split.
  - exists "SOURCE_ID1", "TARGET_ID1", "O1", 5%Z, [(LitString "SOURCE_ID1", (row_of (100) ("USD"))); (LitString "TARGET_ID1", (row_of (100) ("USD")))], 100, "USD", 100, "USD".
    split; [reflexivity|].
    split; [apply lookup_insert_eq|].
    split; [reflexivity|].
    split; [reflexivity|].
    split; [lia|].
    split; [congruence| split; [try (right; lia); try (left; lia) | try reflexivity; try lia; try congruence]].
  - repeat split; try exact I.
    exists 100, "USD". split; [reflexivity|]. repeat split; lia.
    exists 100, "USD". split; [reflexivity|]. repeat split; lia.
Qed.

(** O2: spec consistency — totality gives a post-satisfying outcome. *)
Lemma o2_spec_consistency : forall sigma vs,
  gen_pre sigma vs ->
  exists r ups, gen_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  eapply (gen_table_total "transfer" gen_pre gen_post vs sigma
            eq_refl Hpre).
Qed.

(** O3.0: exception consistency — the InsufficientFundsError arm is satisfiable. *)
Lemma o3_0_exception_consistency : forall sigma vs,
  gen_exc0_pre sigma vs ->
  exists r ups, gen_exc0_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  destruct Hpre as [source_id [target_id [order [amount [store_d [balance_source_id [currency_source_id [balance_target_id [currency_target_id [Hvs [Hcell [Hlook_source_id [Hlook_target_id Hwhen]]]]]]]]]]]]].
  exists (RExn "InsufficientFundsError" (LitTuple [LitString source_id; LitInt amount])), [].
  split.
  - exists source_id, target_id, order, amount, store_d, balance_source_id, currency_source_id, balance_target_id, currency_target_id. repeat split; auto.
  - unfold updates_dom_in. constructor.
Qed.

(** O3.1: exception consistency — the CurrencyMismatchError arm is satisfiable. *)
Lemma o3_1_exception_consistency : forall sigma vs,
  gen_exc1_pre sigma vs ->
  exists r ups, gen_exc1_post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros sigma vs Hpre.
  destruct Hpre as [source_id [target_id [order [amount [store_d [balance_source_id [currency_source_id [balance_target_id [currency_target_id [Hvs [Hcell [Hlook_source_id [Hlook_target_id Hwhen]]]]]]]]]]]]].
  exists (RExn "CurrencyMismatchError" (LitTuple [LitString source_id; LitString target_id])), [].
  split.
  - exists source_id, target_id, order, amount, store_d, balance_source_id, currency_source_id, balance_target_id, currency_target_id. repeat split; auto.
  - unfold updates_dom_in. constructor.
Qed.

(** O4: exit coverage — availability and the exit conditions partition. *)
Lemma o4_exit_coverage : forall (balance_source_id balance_target_id amount : Z) (currency_source_id currency_target_id source_id target_id : string),
  (((currency_source_id <> currency_target_id) \/ (balance_source_id >= amount)%Z) /\ ((currency_source_id = currency_target_id))) \/ (((currency_source_id = currency_target_id) /\ (balance_source_id < amount)%Z) \/ ((currency_source_id <> currency_target_id))).
Proof.
  intros.
  destruct (String.eqb currency_source_id currency_target_id) eqn:E.
  - apply String.eqb_eq in E. subst currency_target_id.
    destruct (Z_ge_dec balance_source_id amount)
      as [Hg | Hl].
    + left. split; [right; lia | reflexivity].
    + right. left. split; [reflexivity | lia].
  - right. right. apply String.eqb_neq. exact E.
Qed.

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

End gen_transfer.