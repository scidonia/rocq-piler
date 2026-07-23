From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.

(** Stateful opaque specs (FunSpecS) — end-to-end demonstration.

    One stateful spec: ["bump"] reads a cell and increments it,
    returning the old value.  Proves the kernel end-to-end:
    the FunCtx totality obligation, the HeadCallSpecS step, and a
    concrete prim_step over a gmap heap. *)

Section specS_demo.

Definition bump_pre (sigma : sn_state) (vs : list sn_val) : Prop :=
  exists l n, vs = [LitLoc l] /\ sigma !! l = Some (LitInt n).

Definition bump_post (sigma : sn_state) (vs : list sn_val)
    (r : Result) (ups : cell_updates) : Prop :=
  exists l n, vs = [LitLoc l] /\ sigma !! l = Some (LitInt n) /\
              r = RVal (LitInt n) /\ ups = [(l, LitInt (n + 1))].

Definition fail_pre (sigma : sn_state) (vs : list sn_val) : Prop :=
  vs = [].
Definition fail_post (sigma : sn_state) (vs : list sn_val)
    (r : Result) (ups : cell_updates) : Prop :=
  vs = [] /\ r = RExn "IntegrityError" (LitString "duplicate key") /\ ups = [].

Definition specS_demo_table (f : string) : option fun_entry :=
  if String.eqb f "bump" then Some (FunSpecS bump_pre bump_post)
  else if String.eqb f "fail" then Some (FunSpecS fail_pre fail_post)
  else None.

Lemma specS_demo_table_total_pure : forall f pre post vs,
  specS_demo_table f = Some (FunSpec pre post) ->
  pre vs -> exists v, post vs v.
Proof.
  intros f pre post vs Hfe _. unfold specS_demo_table in Hfe.
  destruct (String.eqb f "bump"), (String.eqb f "fail"); discriminate.
Qed.

Lemma specS_demo_table_total : forall f pre post vs sigma,
  specS_demo_table f = Some (FunSpecS pre post) ->
  pre sigma vs ->
  exists r ups, post sigma vs r ups /\ updates_dom_in sigma ups.
Proof.
  intros f pre post vs sigma Hfe Hpre. unfold specS_demo_table in Hfe.
  destruct (String.eqb f "bump") eqn:E.
  - injection Hfe as Heq; subst pre post.
    destruct Hpre as [l [n [-> Hl]]].
    exists (RVal (LitInt n)), [(l, LitInt (n + 1))]. split.
    + exists l, n. auto.
    + unfold updates_dom_in. constructor; [|constructor]. simpl. eauto.
  - destruct (String.eqb f "fail") eqn:E2; [|discriminate].
    injection Hfe as Heq; subst pre post.
    unfold fail_pre in Hpre; subst vs.
    exists (RExn "IntegrityError" (LitString "duplicate key")), []. split.
    + split; [reflexivity|]. split; reflexivity.
    + unfold updates_dom_in. constructor.
Qed.

#[global] Instance specS_demo_fun_ctx : FunCtx :=
  {| fun_entries := specS_demo_table;
     fun_specs_total := specS_demo_table_total_pure;
     fun_specsS_total := specS_demo_table_total |}.

(** Applying a one-cell update to the singleton heap yields the updated
    singleton — propositionally, not definitionally (gmap insert). *)
Lemma apply_updates_single (l : loc) (v w : sn_val) :
  apply_updates {[l := v]} [(l, w)] = {[l := w]}.
Proof.
  simpl. apply map_eq. intros k.
  destruct (decide (k = l)) as [->|Hne].
  - rewrite !lookup_insert. case_decide; [reflexivity|congruence].
  - rewrite !lookup_insert_ne; done.
Qed.

(** The concrete step: calling bump on a heap where l holds n returns
    n and leaves l holding n+1 — the state change a pure FunSpec
    cannot express. *)
Example bump_steps : forall (l : loc) (n : Z),
  prim_step (Call "bump" [Val (LitLoc l)])
            {[l := LitInt n]} []
            (Val (LitInt n)) {[l := LitInt (n + 1)]} [].
Proof.
  intros l n.
  rewrite -(apply_updates_single l (LitInt n) (LitInt (n + 1))).
  replace (Val (LitInt n)) with (expr_of_result (RVal (LitInt n))) by reflexivity.
  apply (PrimHeadStep [] (Call "bump" [Val (LitLoc l)])
          {[l := LitInt n]} (expr_of_result (RVal (LitInt n)))
          (apply_updates {[l := LitInt n]} [(l, LitInt (n + 1))]) []).
  apply (HeadCallSpecS "bump" [LitLoc l] {[l := LitInt n]}
          bump_pre bump_post (RVal (LitInt n)) [(l, LitInt (n + 1))]).
  - reflexivity.
  - exists l, n. split; [done|]. apply lookup_insert_eq.
  - exists l, n. split; [done|]. split; [apply lookup_insert_eq|done].
  - unfold updates_dom_in. constructor; [|constructor].
    simpl. eexists. apply lookup_insert_eq.
Qed.

(** BDD scenario: pre-violation is stuck.  Calling bump on a heap
    where the cell is missing cannot step — the spec's precondition is
    enforced, not assumed. *)
Example bump_stuck_when_cell_missing : forall (l : loc),
  ~ reducible (Call "bump" [Val (LitLoc l)]) (∅ : sn_state).
Proof.
  intros l [kappa [e' [sigma' [efs Hstep]]]].
  inversion Hstep as [K x sg x1 Hpure Heq | K x sg x1 sg2 efs2 Hhead Heq]; subst.
  - destruct K as [|Ki K2]; simpl in Heq.
    + subst x. inversion Hpure; subst; simpl in *.
      destruct Ki; simpl in *; discriminate.
    + destruct Ki; simpl in Heq; discriminate Heq.
  - destruct K as [|Ki K2]; simpl in Heq.
    + subst x. assert (Hentry : fun_entries "bump" = Some (FunSpecS bump_pre bump_post)) by reflexivity.
      inversion Hhead; subst.
      * match goal with H : fun_entries _ = Some (FunSpec _ _) |- _ =>
          rewrite Hentry in H; discriminate H end.
      * match goal with H : fun_entries _ = Some (FunSpecS _ _) |- _ =>
          rewrite Hentry in H; injection H; intros; subst end.
        unfold bump_pre in H2. destruct H2 as [l' [n [Hvs Hl]]].
        change [Val (LitLoc l)] with (map Val [LitLoc l]) in H0.
        apply map_Val_inj in H0.
        rewrite H0 in Hvs. injection Hvs as Heq; subst l'.
        rewrite lookup_empty in Hl. discriminate.
      * match goal with H : fun_entries _ = Some (FunDef _ _) |- _ =>
          rewrite Hentry in H; discriminate H end.
    + destruct Ki; simpl in Heq; discriminate Heq.
Qed.

(** A spec with an exceptional post: the call steps to an uncaught
    raise carrying the label and payload. *)
Example fail_steps_to_raise :
  prim_step (Call "fail" [])
            (∅ : sn_state) []
            (Raise (Val (LitExn "IntegrityError" (LitString "duplicate key"))))
            (∅ : sn_state) [].
Proof.
  replace (Raise (Val (LitExn "IntegrityError" (LitString "duplicate key"))))
    with (expr_of_result (RExn "IntegrityError" (LitString "duplicate key")))
    by reflexivity.
  replace (∅ : sn_state) with (apply_updates ∅ ([] : cell_updates)) at 2
    by reflexivity.
  apply (PrimHeadStep [] (Call "fail" []) ∅ _ ∅ []).
  apply (HeadCallSpecS "fail" [] ∅ fail_pre fail_post
          (RExn "IntegrityError" (LitString "duplicate key")) []).
  - reflexivity.
  - reflexivity.
  - split; [reflexivity|]. split; reflexivity.
  - unfold updates_dom_in. constructor.
Qed.

(** The terminal result of the raised call reads off as the exception. *)
Example fail_result_is_exception :
  result_of (Raise (Val (LitExn "IntegrityError" (LitString "duplicate key"))))
  = Some (RExn "IntegrityError" (LitString "duplicate key")).
Proof. reflexivity. Qed.

End specS_demo.
