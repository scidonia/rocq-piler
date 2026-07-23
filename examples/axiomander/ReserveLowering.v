From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.
Require Import SpecPrelude.

(** Lowering a real contract: the inventory [reserve] operation as a
    stateful opaque spec (FunSpecS).

    This is the first hand-lowering of a specsaver domain contract into
    the Rocq model, to see where the machinery carries us.  The theory
    state lives in two heap cells:

      store_loc ↦ LitDict [(sku, LitDict [on_hand, reserved, reorder_point])]
      trace_loc ↦ LitList events

    Obligations proved below: totality (the FunCtx field), the
    exact-delta step, and invariant preservation for the reserve
    transition.

    Simplification (spike): reserve_post updates only the store cell;
    trace events (StockReserved, gauge, alert) are the next increment.

    FRICTION INVENTORY — what the lowering generator must handle so
    human proofs never see this:
      1. booleans: destruct on an eqb does not substitute into the goal;
         `case` substitutes; inner self-tests need `eqb_refl`;
         `rewrite E` only AFTER simpl introduces the occurrence.
         Emit the structured pattern (destruct eqn:E; simpl; branch).
      2. `try apply IH` unifies with cons-goals and closes branches
         prematurely, unbinding variables — apply IH fully-explicit.
      3. this stdpp: `lookup_insert` is the conditional form;
         `lookup_insert_eq` is direct.  For map equalities:
         `rewrite !lookup_insert; repeat case_decide; congruence`.
      4. gmap insert is propositional, not definitional — singleton
         updates need map_eq + lookup lemmas (see apply_updates_single
         in SnakeletExnSpecSDemo.v).
      5. keep definitions folded: pin table entries with
         `assert ... by reflexivity` + rewrite (compute unfolds them
         into raw lambdas that break pattern matching).
      6. `subst` clears hypotheses you still need — rewrite H in H'
         instead of subst-ing when a hypothesis is reused.
      7. invariants need requires: preservation used `qty > 0` —
         admissibility is a premise of O5, not an afterthought.
      8. membership IS lookup-some: `dict_lookup_str k d = Some v`
         is the machine form of `k ∈ d`. *)

Section reserve_lowering.
Context `{FC : FunCtx}.


(* ---------------------------------------------------------------- *)
(* The theory state: two heap cells.                                 *)
(* ---------------------------------------------------------------- *)

Definition store_loc : loc := Loc 1%positive.
Definition trace_loc : loc := Loc 2%positive.

(* A product row: dict with int fields on_hand, reserved, reorder_point. *)
Definition row_of (oh rs rp : Z) : sn_val :=
  LitDict [(LitString "on_hand", LitInt oh);
           (LitString "reserved", LitInt rs);
           (LitString "reorder_point", LitInt rp)].

Definition product_inv (v : sn_val) : Prop :=
  exists oh rs rp,
    v = row_of oh rs rp /\ (rs >= 0)%Z /\ (rs <= oh)%Z.

(* The store invariant: every row satisfies product_inv. *)
Fixpoint store_inv (kvs : list (sn_val * sn_val)) : Prop :=
  match kvs with
  | [] => True
  | (_, v) :: rest => product_inv v /\ store_inv rest
  end.

(* ---------------------------------------------------------------- *)
(* The reserve spec (single-sku specialization).                     *)
(* ---------------------------------------------------------------- *)

Definition reserve_pre (sku : string) (qty : Z)
    (sigma : sn_state) (vs : list sn_val) : Prop :=
  exists store_d oh rs rp,
    vs = [LitString sku; LitInt qty] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str sku store_d = Some (row_of oh rs rp) /\
    (qty > 0)%Z /\ (oh - rs >= qty)%Z.

Definition reserve_post (sku : string) (qty : Z)
    (sigma : sn_state) (vs : list sn_val) (r : Result)
    (ups : cell_updates) : Prop :=
  exists store_d oh rs rp,
    vs = [LitString sku; LitInt qty] /\
    sigma !! store_loc = Some (LitDict store_d) /\
    dict_lookup_str sku store_d = Some (row_of oh rs rp) /\
    r = RVal (LitInt rs) /\
    ups = [(store_loc,
            LitDict (dict_insert_str sku (row_of oh (rs + qty) rp) store_d))].

(* The reserve transition preserves the store invariant — the exact
   delta keeps rs + qty <= oh because the pre gave oh - rs >= qty. *)
Lemma reserve_preserves_inv_single : forall sku qty store_d oh rs rp,
  dict_lookup_str sku store_d = Some (row_of oh rs rp) ->
  product_inv (row_of oh rs rp) ->
  (qty > 0)%Z ->
  (oh - rs >= qty)%Z ->
  store_inv store_d ->
  store_inv (dict_insert_str sku (row_of oh (rs + qty) rp) store_d).
Proof.
  induction store_d as [|kv rest IH]; intros oh rs rp Hlook Hprod Hpos Hdelta Hinv;
    simpl in Hlook |- *.
  - discriminate.
  - destruct kv as [k0 v0].
    destruct Hinv as [Hfst Hrest].
    destruct k0 as [| | s | | | | | | | |]; simpl in *;
      try (split; [exact Hfst | apply (IH oh rs rp Hlook Hprod Hpos Hdelta Hrest)]).
    destruct (String.eqb sku s) eqn:E.
    + apply String.eqb_eq in E. subst s.
      injection Hlook as Hlook. subst v0.
      split; [|exact Hrest].
      destruct Hprod as [o [r [p [Heq [Hr Hlo]]]]].
      injection Heq as Ho Hrs Hrp. subst o r p.
      exists oh, (rs + qty)%Z, rp.
      split; [reflexivity|]. split; lia.
    + split; [exact Hfst|].
      apply (IH oh rs rp Hlook Hprod Hpos Hdelta Hrest).
Qed.

(* ---------------------------------------------------------------- *)
(* The reserve table and its totality obligation.                    *)
(* ---------------------------------------------------------------- *)

Definition reserve_pre_t (sigma : sn_state) (vs : list sn_val) : Prop :=
  exists sku qty, reserve_pre sku qty sigma vs.

Definition reserve_post_t (sigma : sn_state) (vs : list sn_val)
    (r : Result) (ups : cell_updates) : Prop :=
  exists sku qty, reserve_post sku qty sigma vs r ups.

Definition reserve_table (f : string) : option fun_entry :=
  if String.eqb f "reserve" then Some (FunSpecS reserve_pre_t reserve_post_t)
  else None.

Lemma reserve_table_total_pure : forall f pre post vs,
  reserve_table f = Some (FunSpec pre post) ->
  pre vs -> exists v, post vs v.
Proof.
  intros f pre post vs Hfe _. unfold reserve_table in Hfe.
  destruct (String.eqb f "reserve"); discriminate.
Qed.

Lemma reserve_table_total : forall f pre post vs sigma,
  reserve_table f = Some (FunSpecS pre post) ->
  pre sigma vs ->
  exists r ups, post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros f pre post vs sigma Hfe Hpre. unfold reserve_table in Hfe.
  destruct (String.eqb f "reserve") eqn:E; [|discriminate].
  injection Hfe as Heq; subst pre post.
  destruct Hpre as [sku [qty Hpre]].
  destruct Hpre as [store_d [oh [rs [rp [Hvs [Hcell [Hlook [Hpos Havail]]]]]]]].
  exists (RVal (LitInt rs)),
    [(store_loc,
      LitDict (dict_insert_str sku (row_of oh (rs + qty) rp) store_d))].
  split.
  - exists sku, qty, store_d, oh, rs, rp. auto.
  - unfold updates_dom_in. constructor; [|constructor].
    simpl. rewrite Hcell. eexists. reflexivity.
Qed.

#[global] Instance reserve_fun_ctx : FunCtx :=
  {| fun_entries := reserve_table;
     fun_specs_total := reserve_table_total_pure;
     fun_specsS_total := reserve_table_total |}.

(* ---------------------------------------------------------------- *)
(* The concrete step: reserve 30 of sku "S1" with 100 on hand and    *)
(* 10 reserved returns the old reserved and leaves 40 reserved.      *)
(* ---------------------------------------------------------------- *)

Example reserve_steps :
  prim_step (Call "reserve" [Val (LitString "S1"); Val (LitInt 30)])
    {[store_loc := LitDict [(LitString "S1", row_of 100 10 20)];
      trace_loc := LitList []]} []
    (Val (LitInt 10))
    {[store_loc := LitDict [(LitString "S1", row_of 100 40 20)];
      trace_loc := LitList []]} [].
Proof.
  replace (Val (LitInt 10)) with (expr_of_result (RVal (LitInt 10)))
    by reflexivity.
  replace {[store_loc := LitDict [(LitString "S1", row_of 100 40 20)];
            trace_loc := LitList []]}
    with (apply_updates
            {[store_loc := LitDict [(LitString "S1", row_of 100 10 20)];
              trace_loc := LitList []]}
            [(store_loc,
              LitDict (dict_insert_str "S1" (row_of 100 40 20)
                         [(LitString "S1", row_of 100 10 20)]))]).
  2: { simpl. apply map_eq. intros k.
       rewrite !lookup_insert.
       repeat case_decide; congruence. }
  apply (PrimHeadStep [] (Call "reserve" [Val (LitString "S1"); Val (LitInt 30)])
          _ _ _ []).
  apply (HeadCallSpecS "reserve" [LitString "S1"; LitInt 30] _
          reserve_pre_t reserve_post_t (RVal (LitInt 10)) _).
  - reflexivity.
  - exists "S1", 30%Z.
    exists [(LitString "S1", row_of 100 10 20)], 100, 10, 20.
    split; [reflexivity|]. split; [apply lookup_insert_eq|].
    split; [reflexivity|]. lia.
  - exists "S1", 30%Z.
    exists [(LitString "S1", row_of 100 10 20)], 100, 10, 20.
    split; [reflexivity|]. split; [apply lookup_insert_eq|]. auto.
  - unfold updates_dom_in. constructor; [|constructor].
    simpl. rewrite lookup_insert_eq. eexists. reflexivity.
Qed.

End reserve_lowering.
