From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export gen_heap fancy_updates.
From iris.bi Require Import fixpoint_mono.
From stdpp Require Import fin_maps.
Require Import AxiomanderLang.

(** Hand-rolled weakest precondition for AxiomanderLang.

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
  Admitted.

  Definition wp_exn : sn_expr -> (Result -> iProp Sigma) -> iProp Sigma :=
    fixpoint wp_pre.

  Lemma wp_exn_unfold e Phi : wp_exn e Phi ⊣⊢ wp_pre wp_exn e Phi.
  Proof. apply (fixpoint_unfold wp_pre). Admitted.

  (** Filling a non-value into any context yields a non-terminal expr. *)
  Lemma result_of_fill_none Ki e :
    to_val e = None -> result_of (fill_item Ki e) = None.
  Proof.
  Admitted.

  (** Determinism for heap head steps. *)
  Lemma prim_load_det l v sigma kappa er sigma2 efs :
    sigma !! l = Some v ->
    prim_step (Load (Val (LitLoc l))) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Val v /\ sigma2 = sigma /\ efs = [].
  Proof.
  Admitted.

  Lemma prim_store_det l w v sigma kappa er sigma2 efs :
    sigma !! l = Some w ->
    prim_step (Store (Val (LitLoc l)) (Val v)) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Val LitUnit /\ sigma2 = <[l:=v]> sigma /\ efs = [].
  Proof.
  Admitted.

  (** Inversion for an opaque call step: it produces some post-satisfying
      value, with no state change or forks. *)
  Lemma prim_call_inv f pre post vs sigma kappa er sigma2 efs :
    fun_entries f = Some (FunSpec pre post) ->
    prim_step (Call f (map Val vs)) sigma kappa er sigma2 efs ->
    kappa = [] /\ sigma2 = sigma /\ efs = [] /\
    exists v, er = Val v /\ post vs v.
  Proof.
  Admitted.

  (** A fancy update in front of a WP can be absorbed. *)
  Lemma fupd_wp e Phi : (|={top}=> wp_exn e Phi) ⊢ wp_exn e Phi.
  Proof.
  Admitted.

  Local Notation "'WPE' e {{ Q } }" := (wp_exn e Q)
    (at level 20, e, Q at level 200, format "'WPE'  e  {{  Q  } }") : bi_scope.

  (** A value terminates with [RVal v]. *)
  Lemma wp_value v Phi : Phi (RVal v) ⊢ WPE (Val v) {{ Phi }}.
  Proof.
  Admitted.

  (** Monotonicity of the exception WP: weaken the postcondition. *)
  Lemma wp_wand e Phi Psi :
    WPE e {{ Phi }} -∗ (∀ r, Phi r -∗ Psi r) -∗ WPE e {{ Psi }}.
  Proof.
  Admitted.

  (** * GATE LEMMA 2: wp_raise.
      An uncaught [Raise (Val (LitExn lbl pay))] terminates with the
      exception result [RExn lbl pay].  The exceptional postcondition
      arm [Phi (RExn lbl pay)] is discharged against the CURRENT heap
      (state-at-raise), since the raise is terminal. *)
  Lemma wp_raise lbl pay Phi :
    Phi (RExn lbl pay) ⊢ WPE (Raise (Val (LitExn lbl pay))) {{ Phi }}.
  Proof.
  Admitted.

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
  Admitted.

  (** Reducibility witness from a pure step at the empty context. *)
  Lemma reducible_pure e e' sigma :
    pure_step e e' -> reducible e sigma.
  Proof.
  Admitted.

  Lemma reducible_head e sigma e' sigma' efs :
    head_step e sigma e' sigma' efs -> reducible e sigma.
  Proof.
  Admitted.

  (** If the hole steps, the filled expression is reducible. *)
  Lemma fill_reducible_pure K x x' sigma :
    pure_step x x' -> reducible (fill_K K x) sigma.
  Proof.
  Admitted.

  Lemma fill_reducible_head K x sigma x' sigma' efs :
    head_step x sigma x' sigma' efs -> reducible (fill_K K x) sigma.
  Proof.
  Admitted.

  (** result_of inversion. *)
  Lemma result_of_val e v : result_of e = Some (RVal v) -> e = Val v.
  Proof.
  Admitted.

  Lemma result_of_exn e lbl pay :
    result_of e = Some (RExn lbl pay) -> e = Raise (Val (LitExn lbl pay)).
  Proof.
  Admitted.

  (** Single-item step lifting: a step of [e] lifts to a step of
      [fill_item Ki e] in the same context.  Uses [fill_K (Ki :: K) = fill_item Ki o fill_K K]. *)
  Lemma prim_step_fill_item Ki e sigma kappa e' sigma' efs :
    prim_step e sigma kappa e' sigma' efs ->
    prim_step (fill_item Ki e) sigma kappa (fill_item Ki e') sigma' efs.
  Proof.
  Admitted.

  Lemma reducible_fill_item Ki e sigma :
    reducible e sigma -> reducible (fill_item Ki e) sigma.
  Proof.
  Admitted.

  (** A pure redex of shape [fill_item Ki e] with [e] non-value and not a
      stuck raise is impossible -- the redex must be live inside [e]. *)
  Lemma kempty Ki e e' :
    to_val e = None -> (forall v, e <> Raise (Val v)) ->
    pure_step (fill_item Ki e) e' -> False.
  Proof.
  Admitted.

  Lemma kempty_head Ki e sigma e' sigma' efs :
    to_val e = None ->
    head_step (fill_item Ki e) sigma e' sigma' efs -> False.
  Proof.
  Admitted.

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
  Admitted.

  (** Determinism of the unwind step: [fill_item Ki (Raise (Val ev))] for
      a neutral [Ki] steps only to [Raise (Val ev)] (raise propagation). *)
  Lemma prim_unwind_det Ki ev sigma kappa er sigma2 efs :
    neutral Ki = true ->
    prim_step (fill_item Ki (Raise (Val ev))) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Raise (Val ev) /\ sigma2 = sigma /\ efs = [].
  Proof.
  Admitted.


  (* ==== promoted from Demo: determinism + WP rules + bind ==== *)
  (** Determinism for a top-level [Let x (Val v) e2] redex. *)
  Lemma prim_let_det x v e2 sigma kappa er sigma2 efs :
    prim_step (Let x (Val v) e2) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = subst x v e2 /\ sigma2 = sigma /\ efs = [].
  Proof.
  Admitted.

  (** Determinism for [BinOp op (Val v1) (Val v2)]. *)
  Lemma prim_binop_det op v1 v2 sigma kappa er sigma2 efs :
    prim_step (BinOp op (Val v1) (Val v2)) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Val (binop_eval op v1 v2) /\ sigma2 = sigma /\ efs = [].
  Proof.
  Admitted.

  (** Determinism for [If (Val (LitBool true)) e1 e2]. *)
  Lemma prim_if_true_det e1 e2 sigma kappa er sigma2 efs :
    prim_step (If (Val (LitBool true)) e1 e2) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = e1 /\ sigma2 = sigma /\ efs = [].
  Proof.
  Admitted.

  Lemma prim_if_false_det e1 e2 sigma kappa er sigma2 efs :
    prim_step (If (Val (LitBool false)) e1 e2) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = e2 /\ sigma2 = sigma /\ efs = [].
  Proof.
  Admitted.

  (** Determinism for [Try (Val v) x h] (normal: handler skipped). *)
  Lemma prim_try_val_det v x h sigma kappa er sigma2 efs :
    prim_step (Try (Val v) x h) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Val v /\ sigma2 = sigma /\ efs = [].
  Proof.
  Admitted.

  (** Determinism for [Try (Raise (Val ev)) x h] (catch: run handler).
      The interesting case: when [Try] is the outer context (K nonempty),
      its body [Raise (Val ev)] would have to step -- but it is irreducible
      (gate lemma 1), giving the contradiction. *)
  Lemma prim_try_catch_det ev x h sigma kappa er sigma2 efs :
    prim_step (Try (Raise (Val ev)) x h) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = subst x ev h /\ sigma2 = sigma /\ efs = [].
  Proof.
  Admitted.

  (** Determinism for [While e1 e2] (no value sub-context: like Let). *)
  Lemma prim_while_det e1 e2 sigma kappa er sigma2 efs :
    prim_step (While e1 e2) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = If e1 (Let "_" e2 (While e1 e2)) (Val LitUnit)
    /\ sigma2 = sigma /\ efs = [].
  Proof.
  Admitted.

  (** Determinism for [For x (Val (LitList [])) body] (empty: terminate). *)
  Lemma prim_for_nil_det x body sigma kappa er sigma2 efs :
    prim_step (For x (Val (LitList [])) body) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Val LitUnit /\ sigma2 = sigma /\ efs = [].
  Proof.
  Admitted.

  (** Determinism for [For x (Val (LitList (v::vs))) body] (cons: peel). *)
  Lemma prim_for_cons_det x v vs body sigma kappa er sigma2 efs :
    prim_step (For x (Val (LitList (v :: vs))) body) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Let "_" (subst x v body) (For x (Val (LitList vs)) body)
    /\ sigma2 = sigma /\ efs = [].
  Proof.
  Admitted.

  (** Pure WP lemmas via wp_lift_pure_det + the determinism lemmas. *)
  Lemma wp_let x v e2 Phi :
    ▷ WPE (subst x v e2) {{ Phi }} ⊢ WPE (Let x (Val v) e2) {{ Phi }}.
  Proof.
  Admitted.

  Lemma wp_binop op v1 v2 Phi :
    ▷ WPE (Val (binop_eval op v1 v2)) {{ Phi }}
      ⊢ WPE (BinOp op (Val v1) (Val v2)) {{ Phi }}.
  Proof.
  Admitted.

  Lemma wp_if_true e1 e2 Phi :
    ▷ WPE e1 {{ Phi }} ⊢ WPE (If (Val (LitBool true)) e1 e2) {{ Phi }}.
  Proof.
  Admitted.

  Lemma wp_if_false e1 e2 Phi :
    ▷ WPE e2 {{ Phi }} ⊢ WPE (If (Val (LitBool false)) e1 e2) {{ Phi }}.
  Proof.
  Admitted.

  (** * GATE LEMMA 3a: wp_try_normal.
      A try whose body returns a value [Val v] yields [v]; the handler
      is skipped. *)
  Lemma wp_try_normal v x h Phi :
    ▷ WPE (Val v) {{ Phi }} ⊢ WPE (Try (Val v) x h) {{ Phi }}.
  Proof.
  Admitted.

  (** * GATE LEMMA 3b: wp_try_catch.
      A try whose body raises [Raise (Val ev)] runs the handler with the
      exception object substituted for [x]. *)
  Lemma wp_try_catch ev x h Phi :
    ▷ WPE (subst x ev h) {{ Phi }} ⊢ WPE (Try (Raise (Val ev)) x h) {{ Phi }}.
  Proof.
  Admitted.

  (** * Loop WP rules.  [While] unfolds to a guarded body-then-loop; [For]
      peels its (value) list operand one element at a time. *)
  Lemma wp_while e1 e2 Phi :
    ▷ WPE (If e1 (Let "_" e2 (While e1 e2)) (Val LitUnit)) {{ Phi }}
      ⊢ WPE (While e1 e2) {{ Phi }}.
  Proof.
  Admitted.

  Lemma wp_for_nil x body Phi :
    ▷ Phi (RVal LitUnit) ⊢ WPE (For x (Val (LitList [])) body) {{ Phi }}.
  Proof.
  Admitted.

  Lemma wp_for_cons x v vs body Phi :
    ▷ WPE (Let "_" (subst x v body) (For x (Val (LitList vs)) body)) {{ Phi }}
      ⊢ WPE (For x (Val (LitList (v :: vs))) body) {{ Phi }}.
  Proof.
  Admitted.

  (** Determinism for the unwind step [Let x (Raise (Val ev)) e2]. *)
  Lemma prim_unwind_let_det x ev e2 sigma kappa er sigma2 efs :
    prim_step (Let x (Raise (Val ev)) e2) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = Raise (Val ev) /\ sigma2 = sigma /\ efs = [].
  Proof.
  Admitted.

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
  Admitted.

  (** * GATE LEMMA 6: wp_load and wp_store -- heap steps under the
      exception WP.  Confirms heap reasoning is orthogonal to the
      exception machinery (the paper's claim). *)
  Lemma wp_load l v Phi :
    l ↦ v -∗ ▷ (l ↦ v -∗ Phi (RVal v)) -∗ WPE (Load (Val (LitLoc l))) {{ Phi }}.
  Proof.
  Admitted.

  Lemma wp_store l v w Phi :
    l ↦ w -∗ ▷ (l ↦ v -∗ Phi (RVal LitUnit)) -∗
      WPE (Store (Val (LitLoc l)) (Val v)) {{ Phi }}.
  Proof.
  Admitted.

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
  Admitted.


  (** * GATE LEMMA 4: raise unwinding through a neutral (Let) context.
      [Let x (Raise (Val (LitExn lbl pay))) e2] unwinds the raise out of
      the let -- the continuation [e2] is discarded -- yielding the
      exception result.  This is Python/ML semantics: an exception
      propagates up through the evaluation context until caught. *)
  Lemma wp_let_raise_unwind x lbl pay e2 Phi :
    Phi (RExn lbl pay) ⊢
      WPE (Let x (Raise (Val (LitExn lbl pay))) e2) {{ Phi }}.
  Proof.
  Admitted.


  (* ==== transparent call unfold ==== *)
  Lemma prim_callunfold_inv f params body vs sigma kappa er sigma2 efs :
    fun_entries f = Some (FunDef params body) ->
    length vs = length params ->
    prim_step (Call f (map Val vs)) sigma kappa er sigma2 efs ->
    kappa = [] /\ er = subst_list params vs body /\ sigma2 = sigma /\ efs = [].
  Proof.
  Admitted.

  Lemma wp_call_unfold f params body vs Phi :
    fun_entries f = Some (FunDef params body) ->
    length vs = length params ->
    ▷ WPE (subst_list params vs body) {{ Phi }} -∗
    WPE (Call f (map Val vs)) {{ Phi }}.
  Proof.
  Admitted.

  (* ==== heap alloc ==== *)
  Lemma prim_alloc_inv v sigma kappa er sigma2 efs :
    prim_step (Alloc (Val v)) sigma kappa er sigma2 efs ->
    kappa = [] /\ efs = [] /\ exists l, sigma !! l = None /\ er = Val (LitLoc l) /\ sigma2 = <[l:=v]> sigma.
  Proof.
  Admitted.

  Lemma wp_alloc v Phi :
    ▷ (∀ l, l ↦ v -∗ Phi (RVal (LitLoc l))) -∗ WPE (Alloc (Val v)) {{ Phi }}.
  Proof.
  Admitted.

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
  Admitted.

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
  Admitted.

End wp.

(** Notation for the WP and the two-postcondition form. *)
Notation "'WPE' e {{ Phi } }" := (wp_exn e Phi)
  (at level 20, e, Phi at level 200, format "'WPE'  e  {{  Phi  } }") : bi_scope.
