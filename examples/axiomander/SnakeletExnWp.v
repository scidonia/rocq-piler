From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export gen_heap fancy_updates.
From iris.bi Require Import fixpoint_mono.
From stdpp Require Import fin_maps.
Require Import SnakeletExnLang.

(** Hand-rolled weakest precondition for SnakeletExnLang.

    Unlike the stock Iris [wp] (postcondition [val -> iProp]), our
    postcondition ranges over [Result := RVal v | RExn label payload],
    following van Collem/de Vilhena/Krebbers (PLDI 2026): the result of a
    program is either a value or an uncaught raise.  A terminal expression
    [result_of e = Some r] feeds [r] to the postcondition; otherwise the
    expression must be reducible and we reason about the next step.

    We keep the model deliberately simple: no [num_laters_per_step], no
    later credits, empty observation list -- just enough to prove the
    8-lemma gate.  The heap interpretation reuses Iris [gen_heap]. *)

Class snakeletExn_heapGS_gen hlc Sigma := SnakeletExnHeapGS {
  #[global] snakeletExn_invGS :: invGS_gen hlc Sigma;
  #[global] snakeletExn_gen_heapG :: gen_heapGS loc sn_val Sigma;
}.
Global Existing Instance snakeletExn_invGS.
Global Existing Instance snakeletExn_gen_heapG.

Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Section wp.
  Context `{!snakeletExn_heapGS_gen hlc Sigma}.
  Context `{FC : FunCtx}.

  (** State interpretation: just the gen_heap authoritative view. *)
  Definition state_interp (sigma : sn_state) : iProp Sigma :=
    gen_heap_interp sigma.

  Implicit Types Phi : Result -> iProp Sigma.
  Implicit Types e : sn_expr.
  Implicit Types sigma : sn_state.

  (** The predicate whose fixpoint defines the WP. *)
  Definition wp_pre
      (wp : sn_expr -d> (Result -d> iPropO Sigma) -d> iPropO Sigma) :
      sn_expr -d> (Result -d> iPropO Sigma) -d> iPropO Sigma := fun e Phi =>
    match result_of e with
    | Some r => |={top}=> Phi r
    | None => ∀ sigma,
        state_interp sigma ={top,∅}=∗
          ⌜reducible e sigma⌝ ∗
          ∀ e' sigma' efs, ⌜prim_step e sigma [] e' sigma' efs⌝ ={∅}=∗ ▷ |={∅,top}=>
            state_interp sigma' ∗ wp e' Phi ∗
            ([∗ list] ef ∈ efs, wp ef (fun _ => True%I))
    end%I.

  Local Instance wp_pre_contractive : Contractive wp_pre.
  Proof.
    rewrite /wp_pre => n wp wp' Hwp e Phi.
    repeat (f_contractive || f_equiv); apply Hwp.
  Qed.

  Definition wp_exn : sn_expr -> (Result -> iProp Sigma) -> iProp Sigma :=
    fixpoint wp_pre.

  Lemma wp_exn_unfold e Phi : wp_exn e Phi ⊣⊢ wp_pre wp_exn e Phi.
  Proof. apply (fixpoint_unfold wp_pre). Qed.

  (** Filling a non-value into any context yields a non-terminal expr. *)
  Lemma result_of_fill_none Ki e :
    to_val e = None -> result_of (fill_item Ki e) = None.
  Proof.
    intros Hev. destruct Ki; try reflexivity. simpl.
    destruct e; simpl in Hev; try discriminate Hev; reflexivity.
  Qed.

  (** Determinism for heap head steps. *)
  Lemma prim_load_det l v sigma kappa er sigma2 efs :
    sigma !! l = Some v ->
    prim_step (Load (Val (LitLoc l))) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Val v /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hl Hstep.
    inversion Hstep as [K x sg x1 Hpure Heq | K x sg x1 sg2 efs2 Hhead Heq]; subst.
    - destruct K as [|Ki K2]; simpl in Heq.
      + subst x. inversion Hpure; subst; simpl in *. destruct Ki; simpl in H; discriminate H.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin. apply fill_K_val in Hin as [-> ->].
        apply to_val_pure_step in Hpure. discriminate.
    - destruct K as [|Ki K2]; simpl in Heq.
      + subst x. inversion Hhead; subst. rewrite Hl in H0. injection H0 as ->. repeat split; reflexivity.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin. apply fill_K_val in Hin as [-> ->].
        apply to_val_head_step in Hhead. discriminate.
  Qed.

  Lemma prim_store_det l w v sigma kappa er sigma2 efs :
    sigma !! l = Some w ->
    prim_step (Store (Val (LitLoc l)) (Val v)) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Val LitUnit /\ sigma2 = <[l:=v]> sigma /\ efs = [].
  Proof.
    intros Hl Hstep.
    inversion Hstep as [K x sg x1 Hpure Heq | K x sg x1 sg2 efs2 Hhead Heq]; subst.
    - destruct K as [|Ki K2]; simpl in Heq.
      + subst x. inversion Hpure; subst; simpl in *.
        destruct Ki; simpl in H; try discriminate H; injection H; intros; subst; simpl in *; try discriminate.
      + destruct Ki; simpl in Heq; try discriminate Heq;
          injection Heq; intros; subst;
          match goal with Hin : fill_K _ _ = Val _ |- _ => apply fill_K_val in Hin as [-> ->] end;
          apply to_val_pure_step in Hpure; discriminate.
    - destruct K as [|Ki K2]; simpl in Heq.
      + subst x. inversion Hhead; subst. repeat split; reflexivity.
      + destruct Ki; simpl in Heq; try discriminate Heq;
          injection Heq; intros; subst;
          match goal with Hin : fill_K _ _ = Val _ |- _ => apply fill_K_val in Hin as [-> ->] end;
          apply to_val_head_step in Hhead; discriminate.
  Qed.

  (** Inversion for an opaque call step: it produces some post-satisfying
      value, with no state change or forks. *)
  Lemma prim_call_inv f pre post vs sigma kappa er sigma2 efs :
    fun_entries f = Some (FunSpec pre post) ->
    prim_step (Call f (map Val vs)) sigma kappa er sigma2 efs ->
    kappa = [] /\ sigma2 = sigma /\ efs = [] /\
    exists v, er = Val v /\ post vs v.
  Proof.
    intros Hfe Hstep.
    inversion Hstep as [K x sg x1 Hpure Heq | K x sg x1 sg2 efs2 Hhead Heq]; subst.
    - destruct K as [|Ki K2]; simpl in Heq.
      + subst x. inversion Hpure; subst; simpl in *.
        destruct Ki; simpl in *; discriminate.
      + destruct Ki; simpl in Heq; discriminate Heq.
    - destruct K as [|Ki K2]; simpl in Heq.
      + subst x. inversion Hhead; subst.
        * match goal with Hm : map Val ?vs0 = map Val vs |- _ =>
            apply map_Val_inj in Hm; subst vs0 end.
          match goal with He : fun_entries f = Some (FunSpec ?p ?q) |- _ =>
            rewrite Hfe in He; injection He; intros Hpost_eq Hpre_eq; subst end.
          repeat split. eexists; split; [reflexivity|]. eassumption.
        * match goal with He : fun_entries f = Some (FunSpecS _ _) |- _ =>
            rewrite Hfe in He; discriminate He end.
        * match goal with Hm : map Val ?vs0 = map Val vs |- _ =>
            apply map_Val_inj in Hm; subst vs0 end.
          match goal with He : fun_entries f = Some (FunDef _ _) |- _ =>
            rewrite Hfe in He; discriminate He end.
      + destruct Ki; simpl in Heq; discriminate Heq.
  Qed.

  (** A fancy update in front of a WP can be absorbed. *)
  Lemma fupd_wp e Phi : (|={top}=> wp_exn e Phi) ⊢ wp_exn e Phi.
  Proof.
    rewrite (wp_exn_unfold e) /wp_pre.
    destruct (result_of e) as [r|] eqn:Hr.
    - iIntros "H". by iMod "H".
    - iIntros "H" (sigma) "Hs". iMod "H". iApply ("H" with "Hs").
  Qed.

  Local Notation "'WPE' e {{ Q } }" := (wp_exn e Q)
    (at level 20, e, Q at level 200, format "'WPE'  e  {{  Q  } }") : bi_scope.

  (** A value terminates with [RVal v]. *)
  Lemma wp_value v Phi : Phi (RVal v) ⊢ WPE (Val v) {{ Phi }}.
  Proof.
    iIntros "H". rewrite wp_exn_unfold /wp_pre /=. by iModIntro.
  Qed.

  (** Monotonicity of the exception WP: weaken the postcondition. *)
  Lemma wp_wand e Phi Psi :
    WPE e {{ Phi }} -∗ (∀ r, Phi r -∗ Psi r) -∗ WPE e {{ Psi }}.
  Proof.
    iIntros "H HΦ". iLöb as "IH" forall (e Phi Psi).
    rewrite !wp_exn_unfold /wp_pre.
    destruct (result_of e) as [r|] eqn:Hr.
    - iMod "H". iModIntro. by iApply "HΦ".
    - iIntros (sigma) "Hs".
      iMod ("H" $! sigma with "Hs") as "[%Hred Hstep]".
      iModIntro. iSplit; [done|].
      iIntros (e2 sigma2 efs Hps).
      iMod ("Hstep" $! e2 sigma2 efs with "[%]") as "Hstep"; [exact Hps|].
      iModIntro. iNext. iMod "Hstep" as "(Hs2 & Hwp & Hefs)". iModIntro.
      iFrame "Hs2 Hefs". iApply ("IH" with "Hwp HΦ").
  Qed.

  (** * GATE LEMMA 2: wp_raise.
      An uncaught [Raise (Val (LitExn lbl pay))] terminates with the
      exception result [RExn lbl pay].  The exceptional postcondition
      arm [Phi (RExn lbl pay)] is discharged against the CURRENT heap
      (state-at-raise), since the raise is terminal. *)
  Lemma wp_raise lbl pay Phi :
    Phi (RExn lbl pay) ⊢ WPE (Raise (Val (LitExn lbl pay))) {{ Phi }}.
  Proof.
    iIntros "H". rewrite wp_exn_unfold /wp_pre /=. by iModIntro.
  Qed.

  (** Generic pure-step lifting: if [e] is non-terminal, reducible in
      every state, and every step is the deterministic pure step to [e']
      (no heap change, no forks), then [WPE e] follows from [▷ WPE e'].
      All the pure WP lemmas (let, binop, if, try, unwind) instantiate
      this. *)
  Lemma wp_lift_pure_det e e' Phi :
    result_of e = None ->
    (forall sigma, reducible e sigma) ->
    (forall sigma kappa e2 sigma2 efs,
        prim_step e sigma kappa e2 sigma2 efs ->
        kappa = [] /\ e2 = e' /\ sigma2 = sigma /\ efs = []) ->
    ▷ WPE e' {{ Phi }} ⊢ WPE e {{ Phi }}.
  Proof.
    intros Hterm Hred Hdet.
    iIntros "H". rewrite (wp_exn_unfold e) /wp_pre Hterm.
    iIntros (sigma) "Hs".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit; [iPureIntro; apply Hred|].
    iIntros (e2 sigma2 efs Hstep).
    destruct (Hdet _ _ _ _ _ Hstep) as (_ & -> & -> & ->).
    iModIntro. iNext. iMod "Hclose". iModIntro.
    simpl. iFrame "Hs H".
  Qed.

  (** Reducibility witness from a pure step at the empty context. *)
  Lemma reducible_pure e e' sigma :
    pure_step e e' -> reducible e sigma.
  Proof.
    intros Hp. exists [], e', sigma, [].
    apply (PrimPureStep [] e sigma e' Hp).
  Qed.

  Lemma reducible_head e sigma e' sigma' efs :
    head_step e sigma e' sigma' efs -> reducible e sigma.
  Proof.
    intros Hh. exists [], e', sigma', efs.
    apply (PrimHeadStep [] e sigma e' sigma' efs Hh).
  Qed.

  (** If the hole steps, the filled expression is reducible. *)
  Lemma fill_reducible_pure K x x' sigma :
    pure_step x x' -> reducible (fill_K K x) sigma.
  Proof.
    intros Hp. exists [], (fill_K K x'), sigma, [].
    apply (PrimPureStep K x sigma x' Hp).
  Qed.

  Lemma fill_reducible_head K x sigma x' sigma' efs :
    head_step x sigma x' sigma' efs -> reducible (fill_K K x) sigma.
  Proof.
    intros Hh. exists [], (fill_K K x'), sigma', efs.
    apply (PrimHeadStep K x sigma x' sigma' efs Hh).
  Qed.

  (** result_of inversion. *)
  Lemma result_of_val e v : result_of e = Some (RVal v) -> e = Val v.
  Proof.
    destruct e; simpl; intros H; try discriminate H.
    - injection H as ->; reflexivity.
    - (* Raise case: result_of is Some (RExn..) or None, never RVal *)
      destruct e; try discriminate H. destruct v0; discriminate H.
  Qed.

  Lemma result_of_exn e lbl pay :
    result_of e = Some (RExn lbl pay) -> e = Raise (Val (LitExn lbl pay)).
  Proof.
    destruct e; simpl; try discriminate.
    destruct e; simpl; try discriminate.
    destruct v; simpl; try discriminate.
    intros H; inversion H; subst; reflexivity.
  Qed.

  (** Single-item step lifting: a step of [e] lifts to a step of
      [fill_item Ki e] in the same context.  Uses [fill_K (Ki :: K) = fill_item Ki o fill_K K]. *)
  Lemma prim_step_fill_item Ki e sigma kappa e' sigma' efs :
    prim_step e sigma kappa e' sigma' efs ->
    prim_step (fill_item Ki e) sigma kappa (fill_item Ki e') sigma' efs.
  Proof.
    intros Hstep. inversion Hstep as [K x sg x' Hpure Heq | K x sg x' sg' efs' Hhead Heq]; subst.
    - apply (PrimPureStep (Ki :: K) x _ x' Hpure).
    - apply (PrimHeadStep (Ki :: K) x _ x' _ efs Hhead).
  Qed.

  Lemma reducible_fill_item Ki e sigma :
    reducible e sigma -> reducible (fill_item Ki e) sigma.
  Proof.
    intros (kappa & e' & sigma' & efs & Hstep).
    exists kappa, (fill_item Ki e'), sigma', efs.
    by apply prim_step_fill_item.
  Qed.

  (** A pure redex of shape [fill_item Ki e] with [e] non-value and not a
      stuck raise is impossible -- the redex must be live inside [e]. *)
  Lemma kempty Ki e e' :
    to_val e = None -> (forall v, e <> Raise (Val v)) ->
    pure_step (fill_item Ki e) e' -> False.
  Proof.
    intros Hnv Hnr Hpure.
    inversion Hpure as [vv xx ee2 Hp | op vv1 vv2 Hp | ee1 ee2 Hp | ee1 ee2 Hp
                       | vv xx hh Hp | ev xx hh Hp | Ki0 w Hneu Hp
                       | ee1 ee2 Hp | xx bb Hp | xx vv vvs bb Hp ]; subst.
    (* Let / BinOp / IfTrue / IfFalse / TryVal: the redex shape forces
       Ki's hole to be a value, contradicting Hnv. *)
    1-5: destruct Ki; simpl in Hp; try discriminate Hp;
         injection Hp; intros; subst; simpl in Hnv; discriminate.
    - (* TryCatch: hole would be [Raise (Val ev)], excluded by Hnr. *)
      destruct Ki; simpl in Hp; try discriminate Hp.
      injection Hp; intros; subst. exfalso. eapply Hnr. reflexivity.
    - (* RaiseUnwind: hole is a stuck raise, excluded by Hnr. *)
      assert (Ki0 = Ki) as ->.
      { eapply (fill_item_no_val_inj Ki0 Ki (Raise (Val w)) e);
          [ reflexivity | exact Hnv | exact Hp ]. }
      apply fill_item_inj in Hp. exfalso. eapply Hnr. symmetry. exact Hp.
    - (* While: no Ki has [While _ _] as a fill_item shape. *)
      destruct Ki; simpl in Hp; discriminate Hp.
    - (* ForNil: hole would be [Val (LitList [])], contradicting Hnv. *)
      destruct Ki; simpl in Hp; try discriminate Hp.
      injection Hp; intros; subst; simpl in Hnv; discriminate.
    - (* ForCons: hole would be [Val (LitList (_::_))], contradicting Hnv. *)
      destruct Ki; simpl in Hp; try discriminate Hp.
      injection Hp; intros; subst; simpl in Hnv; discriminate.
  Qed.

  Lemma kempty_head Ki e sigma e' sigma' efs :
    to_val e = None ->
    head_step (fill_item Ki e) sigma e' sigma' efs -> False.
  Proof.
    intros Hnv Hhead.
    destruct Ki; simpl in Hhead; inversion Hhead; subst;
      simpl in Hnv; discriminate.
  Qed.

  (** Fill-context step inversion: if [fill_item Ki e] steps and [e] is
      non-value and not a stuck raise (hence its redex is live), the step
      happens inside [e].  This is the [step_by_val] analogue and the
      linchpin for [wp_bind]. *)
  Lemma fill_item_step_inv Ki e sigma kappa e2 sigma2 efs :
    to_val e = None ->
    (forall v, e <> Raise (Val v)) ->
    prim_step (fill_item Ki e) sigma kappa e2 sigma2 efs ->
    exists e', e2 = fill_item Ki e' /\ prim_step e sigma kappa e' sigma2 efs.
  Proof.
    intros Hnv Hnr Hstep.
    inversion Hstep as [K x sg x' Hpure Heq | K x sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki2 K2]; simpl in Heq.
      + exfalso. subst x. eapply kempty; eauto.
      + assert (Ki2 = Ki) as ->.
        { eapply (fill_item_no_val_inj Ki2 Ki (fill_K K2 x) e); [ | exact Hnv | exact Heq ].
          apply fill_not_val. by apply to_val_pure_step in Hpure. }
        apply fill_item_inj in Heq. subst e.
        exists (fill_K K2 x'). split; [reflexivity|].
        apply (PrimPureStep K2 x _ x' Hpure).
    - destruct K as [|Ki2 K2]; simpl in Heq.
      + exfalso. subst x. eapply kempty_head; eauto.
      + assert (Ki2 = Ki) as ->.
        { eapply (fill_item_no_val_inj Ki2 Ki (fill_K K2 x) e); [ | exact Hnv | exact Heq ].
          apply fill_not_val. by apply to_val_head_step in Hhead. }
        apply fill_item_inj in Heq. subst e.
        exists (fill_K K2 x'). split; [reflexivity|].
        apply (PrimHeadStep K2 x _ x' _ efs Hhead).
  Qed.

  (** Determinism of the unwind step: [fill_item Ki (Raise (Val ev))] for
      a neutral [Ki] steps only to [Raise (Val ev)] (raise propagation). *)
  Lemma prim_unwind_det Ki ev sigma kappa er sigma2 efs :
    neutral Ki = true ->
    prim_step (fill_item Ki (Raise (Val ev))) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Raise (Val ev) /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hneu Hstep.
    inversion Hstep as [K x sg x1 Hpure Heq | K x sg x1 sg2 efs2 Hhead Heq]; subst.
    - destruct K as [|Ki2 K2]; simpl in Heq.
      + subst x. inversion Hpure as [| | | | | | Ki0 w Hneu0 Hp | | | ]; subst; simpl in *.
        1-6: destruct Ki; simpl in *; try discriminate; congruence.
        2-4: destruct Ki; simpl in *; try discriminate; congruence.
        assert (Ki0 = Ki) as ->.
        { eapply (fill_item_no_val_inj Ki0 Ki (Raise (Val w)) (Raise (Val ev)));
            [ reflexivity | reflexivity | exact Hp ]. }
        apply fill_item_inj in Hp. injection Hp as ->. repeat split; reflexivity.
      + assert (Ki2 = Ki) as ->.
        { eapply (fill_item_no_val_inj Ki2 Ki (fill_K K2 x) (Raise (Val ev)));
            [ apply fill_not_val; exact (to_val_pure_step _ _ Hpure) | reflexivity | exact Heq ]. }
        apply fill_item_inj in Heq.
        exfalso. pose proof (fill_reducible_pure K2 x x1 empty Hpure) as Hr.
        rewrite Heq in Hr. eapply raise_val_irreducible. exact Hr.
    - destruct K as [|Ki2 K2]; simpl in Heq.
      + subst x. exfalso. eapply kempty_head. 2: exact Hhead. reflexivity.
      + assert (Ki2 = Ki) as ->.
        { eapply (fill_item_no_val_inj Ki2 Ki (fill_K K2 x) (Raise (Val ev)));
            [ apply fill_not_val; exact (to_val_head_step _ _ _ _ _ Hhead) | reflexivity | exact Heq ]. }
        apply fill_item_inj in Heq.
        exfalso. pose proof (fill_reducible_head K2 x _ _ _ _ Hhead) as Hr.
        rewrite Heq in Hr. eapply raise_val_irreducible. exact Hr.
  Qed.


  (* ==== promoted from Demo: determinism + WP rules + bind ==== *)
  (** Determinism for a top-level [Let x (Val v) e2] redex. *)
  Lemma prim_let_det x v e2 sigma kappa er sigma2 efs :
    prim_step (Let x (Val v) e2) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = subst x v e2 /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x' Hpure Heq | K x0 sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hpure; subst; auto.
        match goal with Ki' : sn_ectx_item |- _ => destruct Ki'; simpl in *; try discriminate end.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as -> Hin ->. apply fill_K_val in Hin as [-> ->].
        apply to_val_pure_step in Hpure. discriminate.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as -> Hin ->. apply fill_K_val in Hin as [-> ->].
        apply to_val_head_step in Hhead. discriminate.
  Qed.

  (** Determinism for [BinOp op (Val v1) (Val v2)]. *)
  Lemma prim_binop_det op v1 v2 sigma kappa er sigma2 efs :
    prim_step (BinOp op (Val v1) (Val v2)) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Val (binop_eval op v1 v2) /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x' Hpure Heq | K x0 sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hpure; subst; auto.
        match goal with Ki' : sn_ectx_item |- _ => destruct Ki'; simpl in *; try discriminate end.
      + destruct Ki; simpl in Heq; try discriminate Heq;
          injection Heq as ?; subst;
          match goal with Hin : fill_K _ _ = Val _ |- _ =>
            apply fill_K_val in Hin as [-> ->] end;
          first [ apply to_val_pure_step in Hpure | idtac ]; try discriminate.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; try discriminate Heq;
          injection Heq as ?; subst;
          match goal with Hin : fill_K _ _ = Val _ |- _ =>
            apply fill_K_val in Hin as [-> ->] end;
          apply to_val_head_step in Hhead; discriminate.
  Qed.

  (** Determinism for [If (Val (LitBool true)) e1 e2]. *)
  Lemma prim_if_true_det e1 e2 sigma kappa er sigma2 efs :
    prim_step (If (Val (LitBool true)) e1 e2) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = e1 /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x' Hpure Heq | K x0 sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hpure; subst; auto.
        match goal with Ki' : sn_ectx_item |- _ => destruct Ki'; simpl in *; try discriminate end.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin ? ?; subst.
        apply fill_K_val in Hin as [-> ->]. apply to_val_pure_step in Hpure. discriminate.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin ? ?; subst.
        apply fill_K_val in Hin as [-> ->]. apply to_val_head_step in Hhead. discriminate.
  Qed.

  Lemma prim_if_false_det e1 e2 sigma kappa er sigma2 efs :
    prim_step (If (Val (LitBool false)) e1 e2) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = e2 /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x' Hpure Heq | K x0 sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hpure; subst; auto.
        match goal with Ki' : sn_ectx_item |- _ => destruct Ki'; simpl in *; try discriminate end.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin ? ?; subst.
        apply fill_K_val in Hin as [-> ->]. apply to_val_pure_step in Hpure. discriminate.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin ? ?; subst.
        apply fill_K_val in Hin as [-> ->]. apply to_val_head_step in Hhead. discriminate.
  Qed.

  (** Determinism for [Try (Val v) x h] (normal: handler skipped). *)
  Lemma prim_try_val_det v x h sigma kappa er sigma2 efs :
    prim_step (Try (Val v) x h) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Val v /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x' Hpure Heq | K x0 sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hpure; subst; auto.
        (* PureTryCatch: body is Raise (Val ev); but here body = Val v *)
        match goal with Ki' : sn_ectx_item |- _ => destruct Ki'; simpl in *; try discriminate end.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin ? ?; subst.
        apply fill_K_val in Hin as [-> ->].
        apply to_val_pure_step in Hpure. discriminate.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin ? ?; subst.
        apply fill_K_val in Hin as [-> ->].
        apply to_val_head_step in Hhead. discriminate.
  Qed.

  (** Determinism for [Try (Raise (Val ev)) x h] (catch: run handler).
      The interesting case: when [Try] is the outer context (K nonempty),
      its body [Raise (Val ev)] would have to step -- but it is irreducible
      (gate lemma 1), giving the contradiction. *)
  Lemma prim_try_catch_det ev x h sigma kappa er sigma2 efs :
    prim_step (Try (Raise (Val ev)) x h) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = subst x ev h /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x1 Hpure Heq | K x0 sg x1 sg2 efs2 Hhead Heq]; subst.
    (* head branch *)
    2: { destruct K as [|Ki K2]; simpl in Heq.
         { subst x0. inversion Hhead. }
         destruct Ki; simpl in Heq; try discriminate Heq.
         injection Heq as Hin ? ?; subst.
         exfalso.
         pose proof (fill_reducible_head K2 x0 _ _ _ _ Hhead) as Hred.
         rewrite Hin in Hred. eapply raise_val_irreducible. exact Hred. }
    (* pure branch *)
    destruct K as [|Ki K2]; simpl in Heq.
    { subst x0. inversion Hpure; subst; simpl in *.
      { repeat split; reflexivity. }
      destruct Ki; simpl in *; discriminate. }
    destruct Ki; simpl in Heq; try discriminate Heq.
    injection Heq as Hin ? ?; subst.
    exfalso.
    pose proof (fill_reducible_pure K2 x0 x1 empty Hpure) as Hred.
    rewrite Hin in Hred. eapply raise_val_irreducible. exact Hred.
  Qed.

  (** Determinism for [While e1 e2] (no value sub-context: like Let). *)
  Lemma prim_while_det e1 e2 sigma kappa er sigma2 efs :
    prim_step (While e1 e2) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = If e1 (Let "_" e2 (While e1 e2)) (Val LitUnit)
    /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x' Hpure Heq | K x0 sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hpure; subst; auto.
        match goal with Ki' : sn_ectx_item |- _ => destruct Ki'; simpl in *; try discriminate end.
      + destruct Ki; simpl in Heq; discriminate Heq.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; discriminate Heq.
  Qed.

  (** Determinism for [For x (Val (LitList [])) body] (empty: terminate). *)
  Lemma prim_for_nil_det x body sigma kappa er sigma2 efs :
    prim_step (For x (Val (LitList [])) body) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Val LitUnit /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x' Hpure Heq | K x0 sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hpure; subst; auto.
        match goal with Ki' : sn_ectx_item |- _ => destruct Ki'; simpl in *; try discriminate end.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as ? Hin ?; subst.
        apply fill_K_val in Hin as [-> ->].
        apply to_val_pure_step in Hpure. discriminate.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as ? Hin ?; subst.
        apply fill_K_val in Hin as [-> ->].
        apply to_val_head_step in Hhead. discriminate.
  Qed.

  (** Determinism for [For x (Val (LitList (v::vs))) body] (cons: peel). *)
  Lemma prim_for_cons_det x v vs body sigma kappa er sigma2 efs :
    prim_step (For x (Val (LitList (v :: vs))) body) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Let "_" (subst x v body) (For x (Val (LitList vs)) body)
    /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x' Hpure Heq | K x0 sg x' sg' efs' Hhead Heq]; subst.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hpure; subst; auto.
        match goal with Ki' : sn_ectx_item |- _ => destruct Ki'; simpl in *; try discriminate end.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as ? Hin ?; subst.
        apply fill_K_val in Hin as [-> ->].
        apply to_val_pure_step in Hpure. discriminate.
    - destruct K as [|Ki K']; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as ? Hin ?; subst.
        apply fill_K_val in Hin as [-> ->].
        apply to_val_head_step in Hhead. discriminate.
  Qed.

  (** Pure WP lemmas via wp_lift_pure_det + the determinism lemmas. *)
  Lemma wp_let x v e2 Phi :
    ▷ WPE (subst x v e2) {{ Phi }} ⊢ WPE (Let x (Val v) e2) {{ Phi }}.
  Proof.
    apply wp_lift_pure_det; [done | | ].
    - intros sigma. eapply reducible_pure, PureLet.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_let_det in Hstep. tauto.
  Qed.

  Lemma wp_binop op v1 v2 Phi :
    ▷ WPE (Val (binop_eval op v1 v2)) {{ Phi }}
      ⊢ WPE (BinOp op (Val v1) (Val v2)) {{ Phi }}.
  Proof.
    apply wp_lift_pure_det; [done | | ].
    - intros sigma. eapply reducible_pure, PureBinOp.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_binop_det in Hstep. tauto.
  Qed.

  Lemma wp_if_true e1 e2 Phi :
    ▷ WPE e1 {{ Phi }} ⊢ WPE (If (Val (LitBool true)) e1 e2) {{ Phi }}.
  Proof.
    apply wp_lift_pure_det; [done | | ].
    - intros sigma. eapply reducible_pure, PureIfTrue.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_if_true_det in Hstep. tauto.
  Qed.

  Lemma wp_if_false e1 e2 Phi :
    ▷ WPE e2 {{ Phi }} ⊢ WPE (If (Val (LitBool false)) e1 e2) {{ Phi }}.
  Proof.
    apply wp_lift_pure_det; [done | | ].
    - intros sigma. eapply reducible_pure, PureIfFalse.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_if_false_det in Hstep. tauto.
  Qed.

  (** * GATE LEMMA 3a: wp_try_normal.
      A try whose body returns a value [Val v] yields [v]; the handler
      is skipped. *)
  Lemma wp_try_normal v x h Phi :
    ▷ WPE (Val v) {{ Phi }} ⊢ WPE (Try (Val v) x h) {{ Phi }}.
  Proof.
    apply wp_lift_pure_det; [done | | ].
    - intros sigma. eapply reducible_pure, PureTryVal.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_try_val_det in Hstep. tauto.
  Qed.

  (** * GATE LEMMA 3b: wp_try_catch.
      A try whose body raises [Raise (Val ev)] runs the handler with the
      exception object substituted for [x]. *)
  Lemma wp_try_catch ev x h Phi :
    ▷ WPE (subst x ev h) {{ Phi }} ⊢ WPE (Try (Raise (Val ev)) x h) {{ Phi }}.
  Proof.
    apply wp_lift_pure_det; [done | | ].
    - intros sigma. eapply reducible_pure, PureTryCatch.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_try_catch_det in Hstep. tauto.
  Qed.

  (** * Loop WP rules.  [While] unfolds to a guarded body-then-loop; [For]
      peels its (value) list operand one element at a time. *)
  Lemma wp_while e1 e2 Phi :
    ▷ WPE (If e1 (Let "_" e2 (While e1 e2)) (Val LitUnit)) {{ Phi }}
      ⊢ WPE (While e1 e2) {{ Phi }}.
  Proof.
    apply wp_lift_pure_det; [done | | ].
    - intros sigma. eapply reducible_pure, PureWhile.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_while_det in Hstep. tauto.
  Qed.

  Lemma wp_for_nil x body Phi :
    ▷ Phi (RVal LitUnit) ⊢ WPE (For x (Val (LitList [])) body) {{ Phi }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_pure_det (For x (Val (LitList [])) body) (Val LitUnit));
      [done | | | ].
    - intros sigma. eapply reducible_pure, PureForNil.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_for_nil_det in Hstep. tauto.
    - iNext. iApply wp_value. iExact "H".
  Qed.

  Lemma wp_for_cons x v vs body Phi :
    ▷ WPE (Let "_" (subst x v body) (For x (Val (LitList vs)) body)) {{ Phi }}
      ⊢ WPE (For x (Val (LitList (v :: vs))) body) {{ Phi }}.
  Proof.
    apply wp_lift_pure_det; [done | | ].
    - intros sigma. eapply reducible_pure, PureForCons.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_for_cons_det in Hstep. tauto.
  Qed.

  (** Determinism for the unwind step [Let x (Raise (Val ev)) e2]. *)
  Lemma prim_unwind_let_det x ev e2 sigma kappa er sigma2 efs :
    prim_step (Let x (Raise (Val ev)) e2) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Raise (Val ev) /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hstep.
    inversion Hstep as [K x0 sg x1 Hpure Heq | K x0 sg x1 sg2 efs2 Hhead Heq]; subst.
    - destruct K as [|Ki K2]; simpl in Heq.
      + subst x0. inversion Hpure; subst; simpl in *.
        destruct Ki; simpl in H; try discriminate H.
        injection H; intros; subst; repeat split; reflexivity.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as ? Hin ?; subst.
        exfalso. pose proof (fill_reducible_pure K2 x0 x1 empty Hpure) as Hr.
        rewrite Hin in Hr. eapply raise_val_irreducible. exact Hr.
    - destruct K as [|Ki K2]; simpl in Heq.
      + subst x0. inversion Hhead.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as ? Hin ?; subst.
        exfalso. pose proof (fill_reducible_head K2 x0 _ _ _ _ Hhead) as Hr.
        rewrite Hin in Hr. eapply raise_val_irreducible. exact Hr.
  Qed.

  (** * GATE LEMMA 5: wp_bind -- composition against the Result postcondition.

      The bind postcondition splits: on a value result, continue evaluating
      the context [fill_item Ki (Val v)]; on an exception result, propagate
      it (the raise unwinds through the neutral context).  This is THE
      convergence-critical lemma -- it proves the exception WP composes. *)
  Definition bind_post (Ki : sn_ectx_item) (Phi : Result -> iProp Sigma)
      : Result -> iProp Sigma := fun r =>
    match r with
    | RVal v => WPE (fill_item Ki (Val v)) {{ Phi }}
    | RExn lbl pay => Phi (RExn lbl pay)
    end%I.

  Lemma wp_bind_item Ki e Phi :
    neutral Ki = true ->
    WPE e {{ bind_post Ki Phi }} ⊢ WPE (fill_item Ki e) {{ Phi }}.
  Proof.
    intros Hneu. iIntros "H". iLöb as "IH" forall (e).
    rewrite (wp_exn_unfold e) /wp_pre.
    destruct (result_of e) as [r|] eqn:Hr.
    - destruct r as [v | lbl pay].
      + apply result_of_val in Hr as ->. iApply fupd_wp. simpl. done.
      + apply result_of_exn in Hr as ->.
        iApply (wp_lift_pure_det _ (Raise (Val (LitExn lbl pay)))).
        { destruct Ki; reflexivity. }
        { intros sigma. eapply reducible_pure.
          apply (PureRaiseUnwind Ki (LitExn lbl pay)); exact Hneu. }
        { intros sigma kappa e2 sigma2 efs Hps.
          apply (prim_unwind_det _ _ _ _ _ _ _ Hneu) in Hps. tauto. }
        iNext. simpl. iApply fupd_wp. iMod "H". iModIntro. by iApply wp_raise.
    - assert (to_val e = None) as Hev by (destruct e; simpl in Hr |- *; congruence).
      rewrite (wp_exn_unfold (fill_item Ki e)) /wp_pre.
      rewrite (result_of_fill_none Ki e Hev).
      iIntros (sigma) "Hs".
      iMod ("H" $! sigma with "Hs") as "[%Hred Hstep]".
      assert (forall v, e <> Raise (Val v)) as Hnr.
      { intros vv Heq. rewrite Heq in Hred. eapply raise_val_irreducible, Hred. }
      iModIntro. iSplit. { iPureIntro. by apply reducible_fill_item. }
      iIntros (e2 sigma2 efs Hps).
      destruct (fill_item_step_inv _ _ _ _ _ _ _ Hev Hnr Hps) as (e3 & -> & Hps3).
      iMod ("Hstep" $! e3 sigma2 efs with "[%]") as "Hstep"; [exact Hps3|].
      iModIntro. iNext.
      iMod "Hstep" as "(Hs2 & Hwp & Hefs)". iModIntro.
      iFrame "Hs2 Hefs". iApply ("IH" with "Hwp").
  Qed.

  (** * GATE LEMMA 6: wp_load and wp_store -- heap steps under the
      exception WP.  Confirms heap reasoning is orthogonal to the
      exception machinery (the paper's claim). *)
  Lemma wp_load l v Phi :
    l ↦ v -∗ ▷ (l ↦ v -∗ Phi (RVal v)) -∗ WPE (Load (Val (LitLoc l))) {{ Phi }}.
  Proof.
    iIntros "Hl HPhi". rewrite wp_exn_unfold /wp_pre /=.
    iIntros (sigma) "Hs".
    iDestruct (gen_heap_valid with "Hs Hl") as %Hlk.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit. { iPureIntro. eapply reducible_head, HeadLoad. exact Hlk. }
    iIntros (e2 sigma2 efs Hps).
    destruct (prim_load_det _ _ _ _ _ _ _ Hlk Hps) as (_ & -> & -> & ->).
    iModIntro. iNext. iMod "Hclose". iModIntro.
    iFrame "Hs". iSplitL; [|done].
    iApply wp_value. iApply ("HPhi" with "Hl").
  Qed.

  Lemma wp_store l v w Phi :
    l ↦ w -∗ ▷ (l ↦ v -∗ Phi (RVal LitUnit)) -∗
      WPE (Store (Val (LitLoc l)) (Val v)) {{ Phi }}.
  Proof.
    iIntros "Hl HPhi". rewrite wp_exn_unfold /wp_pre /=.
    iIntros (sigma) "Hs".
    iDestruct (gen_heap_valid with "Hs Hl") as %Hlk.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit. { iPureIntro. eapply reducible_head, HeadStore. by eexists. }
    iIntros (e2 sigma2 efs Hps).
    destruct (prim_store_det _ _ _ _ _ _ _ _ Hlk Hps) as (_ & -> & -> & ->).
    iMod (gen_heap_update _ _ _ v with "Hs Hl") as "[Hs Hl]".
    iModIntro. iNext. iMod "Hclose". iModIntro.
    iFrame "Hs". iSplitL; [|done]. iApply wp_value. iApply ("HPhi" with "Hl").
  Qed.

  (** * GATE LEMMA 8: wp_call -- opaque call against the FunCtx table.
      Reducibility from [fun_specs_total]; the caller proves the
      precondition and receives the postcondition for the result.
      Confirms the call/ghost machinery composes with the exception WP. *)
  Lemma wp_call f pre post vs Phi :
    fun_entries f = Some (FunSpec pre post) ->
    pre vs ->
    ▷ (∀ v, ⌜post vs v⌝ -∗ Phi (RVal v)) -∗
    WPE (Call f (map Val vs)) {{ Phi }}.
  Proof.
    intros Hfe Hpre. iIntros "HPhi".
    rewrite wp_exn_unfold /wp_pre /=.
    iIntros (sigma) "Hs".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit.
    { iPureIntro.
      destruct (fun_specs_total f pre post vs Hfe Hpre) as [v Hv].
      eapply reducible_head. eapply HeadCallSpec; eauto. }
    iIntros (e2 sigma2 efs Hps).
    destruct (prim_call_inv _ _ _ _ _ _ _ _ _ Hfe Hps) as (_ & -> & -> & v & -> & Hpost).
    iModIntro. iNext. iMod "Hclose". iModIntro.
    iFrame "Hs". iSplitL; [|done].
    iApply wp_value. iApply ("HPhi" with "[%]"). exact Hpost.
  Qed.


  (** * GATE LEMMA 4: raise unwinding through a neutral (Let) context.
      [Let x (Raise (Val (LitExn lbl pay))) e2] unwinds the raise out of
      the let -- the continuation [e2] is discarded -- yielding the
      exception result.  This is Python/ML semantics: an exception
      propagates up through the evaluation context until caught. *)
  Lemma wp_let_raise_unwind x lbl pay e2 Phi :
    Phi (RExn lbl pay) ⊢
      WPE (Let x (Raise (Val (LitExn lbl pay))) e2) {{ Phi }}.
  Proof.
    iIntros "H".
    iApply (wp_lift_pure_det _ (Raise (Val (LitExn lbl pay)))); [done | | | ].
    - intros sigma. eapply reducible_pure.
      apply (PureRaiseUnwind (LetCtx x e2) (LitExn lbl pay)). reflexivity.
    - intros sigma kappa e2' sigma2 efs Hstep.
      apply prim_unwind_let_det in Hstep. tauto.
    - iNext. by iApply wp_raise.
  Qed.


  (* ==== transparent call unfold ==== *)
  Lemma prim_callunfold_inv f params body vs sigma kappa er sigma2 efs :
    fun_entries f = Some (FunDef params body) ->
    length vs = length params ->
    prim_step (Call f (map Val vs)) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = subst_list params vs body /\ sigma2 = sigma /\ efs = [].
  Proof.
    intros Hfe Hlen Hstep.
    inversion Hstep as [K x sg x1 Hpure Heq | K x sg x1 sg2 efs2 Hhead Heq]; subst.
    - destruct K as [|Ki K2]; simpl in Heq.
      + subst x. inversion Hpure; subst; simpl in *. destruct Ki; simpl in *; discriminate.
      + destruct Ki; simpl in Heq; discriminate Heq.
    - destruct K as [|Ki K2]; simpl in Heq.
      + subst x. inversion Hhead; subst.
        * match goal with Hm : map Val ?vs0 = map Val vs |- _ => apply map_Val_inj in Hm; subst vs0 end.
          match goal with He : fun_entries f = Some (FunSpec _ _) |- _ => rewrite Hfe in He; discriminate He end.
        * match goal with He : fun_entries f = Some (FunSpecS _ _) |- _ => rewrite Hfe in He; discriminate He end.
        * match goal with Hm : map Val ?vs0 = map Val vs |- _ => apply map_Val_inj in Hm; subst vs0 end.
          match goal with He : fun_entries f = Some (FunDef _ _) |- _ =>
            rewrite Hfe in He; injection He; intros; subst end.
          repeat split; reflexivity.
      + destruct Ki; simpl in Heq; discriminate Heq.
  Qed.

  Lemma wp_call_unfold f params body vs Phi :
    fun_entries f = Some (FunDef params body) ->
    length vs = length params ->
    ▷ WPE (subst_list params vs body) {{ Phi }} -∗
    WPE (Call f (map Val vs)) {{ Phi }}.
  Proof.
    intros Hfe Hlen. iIntros "H".
    rewrite (wp_exn_unfold (Call f (map Val vs))) /wp_pre /=.
    iIntros (sigma) "Hs".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit.
    { iPureIntro. eapply reducible_head. eapply HeadCallUnfold; eauto. }
    iIntros (e2 sigma2 efs Hps).
    destruct (prim_callunfold_inv _ _ _ _ _ _ _ _ _ Hfe Hlen Hps) as (_ & -> & -> & ->).
    iModIntro. iNext. iMod "Hclose". iModIntro. iFrame "Hs". iSplitL; [iApply "H"|done].
  Qed.

  (* ==== heap alloc ==== *)
  Lemma prim_alloc_inv v sigma kappa er sigma2 efs :
    prim_step (Alloc (Val v)) sigma kappa er sigma2 efs ->
    kappa = [] /\ efs = [] /\ exists l, sigma !! l = None /\ er = Val (LitLoc l) /\ sigma2 = <[l:=v]> sigma.
  Proof.
    intros Hstep.
    inversion Hstep as [K x sg x1 Hpure Heq | K x sg x1 sg2 efs2 Hhead Heq]; subst.
    - destruct K as [|Ki K2]; simpl in Heq.
      + subst x. inversion Hpure; subst; simpl in *. destruct Ki; simpl in *; discriminate.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin. apply fill_K_val in Hin as [-> ->].
        apply to_val_pure_step in Hpure. discriminate.
    - destruct K as [|Ki K2]; simpl in Heq.
      + subst x. inversion Hhead; subst.
        repeat split. eexists; repeat split; eauto.
      + destruct Ki; simpl in Heq; try discriminate Heq.
        injection Heq as Hin. apply fill_K_val in Hin as [-> ->].
        apply to_val_head_step in Hhead. discriminate.
  Qed.

  Lemma wp_alloc v Phi :
    ▷ (∀ l, l ↦ v -∗ Phi (RVal (LitLoc l))) -∗ WPE (Alloc (Val v)) {{ Phi }}.
  Proof.
    iIntros "HPhi". rewrite (wp_exn_unfold (Alloc (Val v))) /wp_pre /=.
    iIntros (sigma) "Hs".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iSplit.
    { iPureIntro. destruct (exist_fresh (dom sigma)) as [l Hl].
      eapply reducible_head. eapply HeadAlloc. by apply not_elem_of_dom. }
    iIntros (e2 sigma2 efs Hps).
    destruct (prim_alloc_inv _ _ _ _ _ _ Hps) as (_ & -> & l & Hfree & -> & ->).
    iMod (gen_heap_alloc _ l v with "Hs") as "(Hs & Hl & _)"; [exact Hfree|].
    iModIntro. iNext. iMod "Hclose". iModIntro. iFrame "Hs". iSplitL; [|done].
    iApply wp_value. iApply ("HPhi" with "Hl").
  Qed.

  (** * Loop fold rule.  Iterate [body] over the list model [M].  The
      invariant [P : list sn_val -> iProp] holds over the *remaining*
      suffix.  The per-element step either returns a value (and [P] shrinks
      to the tail) or raises (and the exception escapes via [Phi]).  Proven
      by structural induction on [M] -- no extra later beyond the per-step
      pure delay.  [Hclosed] states the body does not capture the "_"
      sequencing binder (always true for generated bodies). *)
  Lemma wp_for_list' x body (M : list sn_val)
      (P : list sn_val -> iProp Sigma) (Phi : Result -> iProp Sigma) :
    (forall w, subst "_" w body = body) ->
    P M -∗
    (□ ∀ v vs, P (v :: vs) -∗
        WPE (subst x v body)
          {{ (fun r => match r with
                       | RVal _ => P vs
                       | RExn l p => Phi (RExn l p) end) }}) -∗
    (P [] -∗ Phi (RVal LitUnit)) -∗
    WPE (For x (Val (LitList M)) body) {{ Phi }}.
  Proof.
    iIntros (Hclosed) "HP #Hstep Hpost".
    iInduction M as [|v vs] "IH"; simpl.
    - iApply wp_for_nil. iNext. by iApply "Hpost".
    - iApply wp_for_cons. iNext.
      iApply (wp_bind_item (LetCtx "_" _)); [reflexivity|].
      iApply (wp_wand with "[HP]").
      { iApply ("Hstep" with "HP"). }
      iIntros (r) "Hr". destruct r as [w | l p]; simpl.
      + (* body returned a value: [bind_post] left the sequencing Let *)
        iApply wp_let. iNext.
        assert (subst "_" w (For x (Val (LitList vs)) body)
                = For x (Val (LitList vs)) body) as Heq.
        { cbn [subst]. destruct (String.eqb "_" x) eqn:E;
            by rewrite ?Hclosed. }
        rewrite Heq.
        iApply ("IH" with "Hr Hpost").
      + (* body raised: [bind_post] already propagated the exception *)
        iExact "Hr".
  Qed.

  (** Forall-accumulating for-loop: specialise [wp_for_list'] with the
      suffix invariant [P M := Forall Q M].  Each element step preserves
      [Forall Q] on the tail (or raises); when the list is consumed the
      [Forall Q []] fact feeds the post.  This is the shape the generator
      uses for loops with a per-element invariant. *)
  Lemma wp_for_list_forall (Q : sn_val -> Prop) x body (M : list sn_val)
      (Phi : Result -> iProp Sigma) :
    (forall w, subst "_" w body = body) ->
    ⌜Forall Q M⌝ -∗
    (□ ∀ v vs, ⌜Forall Q (v :: vs)⌝ -∗
        WPE (subst x v body)
          {{ (fun r => match r with
                       | RVal _ => ⌜Forall Q vs⌝
                       | RExn l p => Phi (RExn l p) end) }}) -∗
    (⌜Forall Q []⌝ -∗ Phi (RVal LitUnit)) -∗
    WPE (For x (Val (LitList M)) body) {{ Phi }}.
  Proof.
    iIntros (Hclosed) "HP #Hstep Hpost".
    iApply (wp_for_list' x body M (fun M0 => ⌜Forall Q M0⌝%I) Phi Hclosed
              with "HP [] Hpost").
    iModIntro. iIntros (v vs) "HF". iApply ("Hstep" with "HF").
  Qed.

End wp.

(** Notation for the WP and the two-postcondition form. *)
Notation "'WPE' e {{ Phi } }" := (wp_exn e Phi)
  (at level 20, e, Phi at level 200, format "'WPE'  e  {{  Phi  } }") : bi_scope.
