From iris.proofmode Require Import proofmode coq_tactics reduction.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith.
Require Import SnakeletExnLang SnakeletExnWp.
Require Import ListPredicates.

(** Stage-tactic layer for the exception-aware WP (Result postcondition).

    Ported from the old SnakeletTactics.v but against [wp_exn] (WPE):
    the postcondition ranges over [Result := RVal v | RExn label payload],
    there is no stuckness / mask, and bind composition goes through
    [wp_bind_item] with the [bind_post] transformer (both in SnakeletExnWp.v).

    The generated proof scripts use the same instruction set as before:
      pure_step, call_opaque, case_bool, finish_pure, heap_load/store/alloc,
      raise_step, try_step.
    Each stage tactic extracts everything it needs from the goal. *)

(** [reshape_expr e tac] decomposes [e] into an evaluation context [K]
    (a single context item, since our WP bind is per-item) and a redex
    [e'], then calls [tac Ki e'] for the innermost evaluation position.
    Try is a context (body reduces inside) but is NOT neutral, so it is
    handled by the dedicated try tactics, not generic bind. *)
Ltac reshape_item e tac :=
  lazymatch e with
  | Let ?x (Val ?v) ?e2          => tac (@None sn_ectx_item) e
  | Let ?x ?e1 ?e2               => tac (Some (LetCtx x e2)) e1
  | BinOp ?op (Val ?v1) (Val ?v2) => tac (@None sn_ectx_item) e
  | BinOp ?op ?e1 (Val ?v2)      => tac (Some (BinOpLCtx op v2)) e1
  | BinOp ?op ?e1 ?e2            => tac (Some (BinOpRCtx op e1)) e2
  | If (Val _) _ _               => tac (@None sn_ectx_item) e
  | If ?e0 ?e1 ?e2               => tac (Some (IfCtx e1 e2)) e0
  | Load (Val _)                 => tac (@None sn_ectx_item) e
  | Load ?e0                     => tac (Some LoadCtx) e0
  | Store (Val ?v1) (Val ?v2)    => tac (@None sn_ectx_item) e
  | Store ?e1 (Val ?v2)          => tac (Some (StoreLCtx v2)) e1
  | Store ?e1 ?e2                => tac (Some (StoreRCtx e1)) e2
  | Alloc (Val _)                => tac (@None sn_ectx_item) e
  | Alloc ?e0                    => tac (Some AllocCtx) e0
  | Raise (Val _)                => tac (@None sn_ectx_item) e
  | Raise ?e0                    => tac (Some RaiseCtx) e0
  | _                            => tac (@None sn_ectx_item) e
  end.

Section tactics.
  Context `{!snakeletExn_heapGS_gen hlc Sigma}.
  Context `{FC : FunCtx}.
  Local Notation "'WPE' e {{ Q } }" := (wp_exn e Q)
    (at level 20, e, Q at level 200) : bi_scope.
  Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v) (at level 20) : bi_scope.

  Implicit Types Phi : Result -> iProp Sigma.

End tactics.

(** [wp_bind Ki] focuses the WP on the sub-expression in context [Ki]
    using [wp_bind_item].  The neutrality side-condition is discharged by
    [reflexivity] (all bind contexts are neutral; Try is handled separately). *)
Ltac wp_bind_ctx Ki :=
  iApply (wp_bind_item Ki); [reflexivity|].

(** After a redex reduces to a value under a [bind_post], pop the value
    through [wp_value] so the enclosing context's next redex is exposed.
    [simpl] then unfolds [bind_post (RVal v)] back to the context WP. *)
Ltac popvals :=
  repeat lazymatch goal with
  | |- envs_entails _ (wp_exn (Val _) ?Q) =>
      lazymatch Q with
      | bind_post _ _ => iApply wp_value; simpl
      end
  end.

(** Reduce the redex once it is in focus position (top of WP). *)
Ltac pure_step_redex :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Let _ (Val _) _) _) =>
      iApply wp_let; iNext; simpl
  | |- envs_entails _ (wp_exn (BinOp _ (Val _) (Val _)) _) =>
      iApply wp_binop; iNext; simpl
  | |- envs_entails _ (wp_exn (If (Val (LitBool true)) _ _) _) =>
      iApply wp_if_true; iNext; simpl
  | |- envs_entails _ (wp_exn (If (Val (LitBool false)) _ _) _) =>
      iApply wp_if_false; iNext; simpl
  | |- envs_entails _ (wp_exn (If (Val (LitBool ?b)) _ _) _) =>
      (* the boolean may be an unreduced [Z.ltb]/[Z.leb]/[Z.eqb] term
         (e.g. after a concrete heap-loop binop): compute it, then retry. *)
      let bv := eval cbv in b in
      lazymatch bv with
      | true  => replace b with true by (cbv; reflexivity);
                 iApply wp_if_true; iNext; simpl
      | false => replace b with false by (cbv; reflexivity);
                 iApply wp_if_false; iNext; simpl
      | _ => fail "pure_step: symbolic condition; use case_bool"
      end
  | |- envs_entails _ (wp_exn (Try (Val _) _ _) _) =>
      iApply wp_try_normal; iNext; simpl
  | |- envs_entails _ (wp_exn (Try (Raise (Val _)) _ _) _) =>
      iApply wp_try_catch; iNext; simpl
  | |- envs_entails _ (wp_exn (Call _ _) _) =>
      fail "pure_step: redex is a call; use call_opaque"
  | _ => fail "pure_step: no pure redex"
  end.

(** One pure reduction.  Focusing is goal-driven: [reshape_item] finds the
    innermost evaluation position; if it is nested, [wp_bind] focuses it
    first.  Calls are never reduced here. *)
(** Focus the innermost evaluation position by repeatedly binding the
    outermost non-value context item until a redex sits at the top. *)
Ltac focus_redex :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn ?e _) =>
      reshape_item e ltac:(fun Ki e' =>
        lazymatch Ki with
        | @None sn_ectx_item => idtac      (* redex already at top *)
        | Some ?K => wp_bind_ctx K; focus_redex
        end)
  end.

Ltac pure_step :=
  popvals; focus_redex; pure_step_redex.

(** Unfold a concrete [While] one iteration.  Focuses the loop (it may
    sit under a [Let "_" _ cont] bind), applies [wp_while] to expose
    [If cond (Let "_" body (While ..)) (Val LitUnit)], then simplifies.
    The subsequent case_bool / pure_step / heap stages drive the body. *)
Ltac loop_unfold :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (While _ _) _) =>
      iApply wp_while; iNext; simpl
  | _ => fail "loop_unfold: goal is not a While"
  end.

(** Convert boolean path constraints into Props for [lia]. *)
(** Tactic to close a contradiction when the postcondition is an implication
    that's vacuously satisfied by a false branch condition from [case_bool]. *)
Ltac close_case_contradiction :=
  try match goal with
  | Hcond : _ = false |- _ =>
      apply Bool.andb_false_iff in Hcond;
      destruct Hcond as [Hn | Hs];
      [ apply negb_false_iff in Hn; apply Z.eqb_eq in Hn; subst;
        repeat match goal with H: _ /\ _ |- _ => destruct H end;
        try (exfalso; assumption; fail); try done
      | apply Bool.orb_false_iff in Hs; destruct Hs as [Ha Hb];
        try congruence ]
  end.

Ltac snakelet_pure_hyps :=
  repeat match goal with
  | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H : Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
  | H : Z.leb _ _ = false |- _ => apply Z.leb_gt in H
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H; subst
  | H : Z.eqb _ _ = false |- _ => apply Z.eqb_neq in H
  | H : negb (Z.eqb ?a ?b) = true |- _ =>
      apply negb_true_iff in H; apply Z.eqb_eq in H; subst
  | H : negb (Z.eqb ?a ?b) = false |- _ =>
      apply negb_false_iff in H; apply Z.eqb_eq in H; subst
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  end.

(** Tactic to destruct all bool equalities into Props suitable for [done]. *)
Ltac snakelet_bool_hyps :=
  repeat match goal with
  | H : _ && _ = true |- _ => apply Bool.andb_true_iff in H
  | H : _ || _ = false |- _ => apply Bool.orb_false_iff in H
  | H : true = _ && _ |- _ => symmetry in H; apply Bool.andb_true_iff in H
  | H : false = _ || _ |- _ => symmetry in H; apply Bool.orb_false_iff in H
  | H : true = negb _ |- _ => symmetry in H; apply negb_true_iff in H
  | H : false = negb _ |- _ => symmetry in H; apply negb_false_iff in H
  | H : true = Z.eqb ?a ?b |- _ => symmetry in H; apply Z.eqb_eq in H; subst
  | H : false = Z.eqb ?a ?b |- _ => symmetry in H; apply Z.eqb_neq in H
  end.

(** Raise step: reduce an in-focus [Raise (Val (LitExn ...))] to its
    exception result.  Also handles a raise nested in a neutral context
    (it unwinds). *)
Ltac raise_step :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Raise (Val (LitExn _ _))) _) =>
      iApply wp_raise
  | _ => fail "raise_step: goal is not a raise"
  end;
  (* discharge the resulting RExn arm: String.eqb on the concrete label
     reduces, leaving the raises-condition Prop (or False). *)
  simpl; try (iPureIntro; snakelet_pure_hyps;
              first [ reflexivity | lia | done ]).

(** Path fork on a symbolic boolean condition. *)
Ltac case_bool :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (If (Val (LitBool ?b)) _ _) _) =>
      let Hcond := fresh "Hcond" in destruct b eqn:Hcond
  | _ => fail "case_bool: goal is not an If on a boolean value"
  end.

(** Terminal stage: a value meets the postcondition.  Pops any pending
    bind contexts, applies [wp_value] to expose the [RVal v] arm of the
    Result-match postcondition, then discharges the pure obligation with
    path constraints + lia. *)
Ltac finish_pure :=
  popvals;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Val _) _) => iApply wp_value
  | _ => idtac
  end;
  simpl; iPureIntro; snakelet_pure_hyps;
  (* Unfold forallb facts into In-based form for intros/specialize. *)
  repeat rewrite forallb_true in *;
  cbn in *; repeat rewrite existsb_true in *;
  (* Handle (A -> B) implications *)
  repeat match goal with
  | |- (_ -> _) /\ _ => split; [| idtac]
  end;
  try (intros);
  (* Destruct disjunctions before conjunctions *)
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H
  end;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end;
  snakelet_pure_hyps;
  try (first
         [ reflexivity
         | nia
         | lia
         | (f_equal; nia)
         | done
          (* Z.leb / Z.ltb goal: rewrite to Prop inequality, then nia *)
          | (rewrite Z.leb_le; nia)
          | (rewrite Z.ltb_lt; nia)
          (* Z.of_nat (S n) = Z.of_nat n + 1 — common after list append *)
          | (rewrite ?Nat2Z.inj_succ; nia)
          | (rewrite ?length_app; simpl; nia)
         (* existential value-shape postcondition.  The side-condition may
            contain Z.leb/Z.ltb goals; convert them before using nia. *)
           | (eexists; split;
              [ reflexivity
              | try rewrite Z.leb_le; try rewrite Z.ltb_lt;
                try rewrite Z.eqb_eq; try rewrite Nat2Z.inj_succ;
                try rewrite length_app; simpl;
                try intros;
                try (solve [
                     repeat match goal with
                     | H : _ \/ _ |- _ => destruct H
                     end;
                     repeat match goal with
                     | H : _ /\ _ |- _ => destruct H
                     end;
                     snakelet_bool_hyps;
                     snakelet_pure_hyps;
                     repeat match goal with
                     | H : _ \/ _ |- _ => destruct H
                     end;
                     snakelet_bool_hyps;
                     snakelet_pure_hyps;
                     repeat match goal with
                     | H : _ /\ _ |- _ => destruct H
                     end;
                     first [ reflexivity | done | congruence 
                           | close_case_contradiction
                           | exfalso; eauto | nia | lia ]
                      ]);
                first [ reflexivity | nia
                     (* string set-membership: pick a disjunct *)
                     | left; nia | right; nia | left; nia | right; nia
                     | (repeat first [ left; nia | right; nia
                                     | left; nia
                                     | right
                                     | reflexivity ])
                     | done
          | congruence
          | close_case_contradiction
          | exfalso; eauto | lia ] ])
           | (repeat split; first [ reflexivity | nia ]) ]).

(** Convert a syntactic list of value expressions [[Val v1; ...; Val vn]]
    to the value list [[v1; ...; vn]] so [Call f args] matches the
    [Call f (map Val vs)] shape of [wp_call]. *)
Ltac strip_vals args :=
  lazymatch args with
  | nil => constr:(@nil sn_val)
  | Val ?v :: ?rest => let r := strip_vals rest in constr:(v :: r)
  end.

Ltac snakelet_solve_pre :=
  solve [ done
        | hnf; repeat lazymatch goal with |- @ex _ _ => eexists end;
          first [ done | split; [done | lia] | split; [reflexivity | lia] | lia ] ].

(** Apply [wp_call] once the Call redex is at the top of the WP. *)
Ltac call_opaque_redex solver :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Call ?f ?args) _) =>
      let vs := strip_vals args in
      let entry := eval hnf in (fun_entries f) in
      lazymatch entry with
      | Some (FunSpec ?pre ?post) =>
          iApply (wp_call f pre post vs); [ reflexivity | solve [solver] | ];
          iNext; let v := fresh "v" in let Hv := fresh "Hv" in
          iIntros (v Hv); simpl in Hv; subst v; simpl
      | _ => fail "call_opaque: not an opaque (FunSpec) call"
      end
  | _ => fail "call_opaque: redex is not a Call"
  end.

(** Opaque call: focus the Call redex (it is typically the bound
    expression of a Let), then apply [wp_call].  [solver] discharges the
    precondition (default: [snakelet_solve_pre]). *)
Ltac call_opaque_pre solver :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Call _ _) _) => call_opaque_redex solver
  | _ => fail "call_opaque: redex is not a Call"
  end.

Ltac call_opaque_core := call_opaque_pre snakelet_solve_pre.

(** Walk nested evaluation contexts to the innermost redex and check it
    is a [Call fname _].  Non-destructive (inspection only). *)
Ltac check_redex_call fname e :=
  reshape_item e ltac:(fun Ki e' =>
    lazymatch Ki with
    | @None sn_ectx_item =>
        lazymatch e' with
        | Call fname _ => idtac
        | _ => fail "call_opaque: goal redex is not a call to the given function"
        end
    | Some _ => check_redex_call fname e'
    end).

(** Drift check: assert the expected callee, then run the core. *)
Ltac check_callee fname :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn ?e _) => check_redex_call fname e
  | _ => fail "call_opaque: not a WPE goal"
  end.

Tactic Notation "call_opaque" := call_opaque_core.
Tactic Notation "call_opaque" constr(f) := check_callee f; call_opaque_core.
Tactic Notation "call_opaque_pre" tactic3(t) := call_opaque_pre t.

(** Opaque call with a PREDICATE postcondition [exists r_z, v = LitInt r_z
    /\ P].  Unlike [call_opaque] (which expects a functional equation
    [v = LitInt e] and [subst]s the result), this destructs the existential,
    substitutes [v := LitInt r_z], and KEEPS the predicate [P] as a
    hypothesis so the continuation can use the result bound (e.g.
    [0 <= r_z <= 1]).  [r_z] is the result-as-Z, [Hr] the predicate.

    The precondition is discharged by extracting concrete Z witnesses
    directly from [vs] ([LitInt n] -> [n]), avoiding the variable-
    shadowing problem that [snakelet_solve_pre]'s [exists _] hits when
    the [_pre] binder reuse the call-site parameter name.

    Note: this only handles LitInt args.  String/bool args are not
    supported in opaque callee specs yet. *)
Ltac call_opaque_pred_redex :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Call ?f ?args) _) =>
      let vs := strip_vals args in
      let entry := eval hnf in (fun_entries f) in
      lazymatch entry with
      | Some (FunSpec ?pre ?post) =>
          iApply (wp_call f pre post vs); [ reflexivity | | ];
          [ hnf;
            (* Provide the concrete Z values from vs as exists witnesses. *)
            let ts := strip_vals args in
            let rec extract_wit ts :=
              lazymatch ts with
              | nil => idtac
              | (LitInt ?z) :: ?rest => exists (z : Z); extract_wit rest
              | _ :: ?rest => extract_wit rest
              end in
            extract_wit ts;
            split; [ reflexivity | lia ] | ];
          iNext; let v := fresh "v" in let Hv := fresh "Hv" in
          iIntros (v Hv); simpl in Hv;
          (* Destruct result binder: LitInt (rz : Z) or LitString (rs : string) *)
          try (let rz := fresh "r_z" in let Hr := fresh "Hr" in
               destruct Hv as (rz & -> & Hr); simpl);
          try (let rs := fresh "r_s" in let Hr := fresh "Hr" in
               destruct Hv as (rs & -> & Hr); simpl)
      | _ => fail "call_opaque_pred: not an opaque (FunSpec) call"
      end
  | _ => fail "call_opaque_pred: redex is not a Call"
  end.

Ltac call_opaque_pred_pre :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Call _ _) _) => call_opaque_pred_redex
  | _ => fail "call_opaque_pred: redex is not a Call"
  end.

Ltac call_opaque_pred_core := call_opaque_pred_pre.

Tactic Notation "call_opaque_pred" := call_opaque_pred_core.
Tactic Notation "call_opaque_pred" constr(f) := check_callee f; call_opaque_pred_core.

(** Heap stages.  Each focuses its redex (typically the bound expression
    of a Let) via [focus_redex], applies the heap WP lemma framing the
    relevant points-to from the spatial context, and reintroduces the
    (possibly updated) points-to under a fresh hypothesis.  [simpl] then
    pops the value through [bind_post]. *)
Ltac heap_load :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Load (Val (LitLoc ?l))) _) =>
      iApply (wp_load l with "[$]"); iNext; iIntros "?"; simpl
  | _ => fail "heap_load: redex is not a Load"
  end.

Ltac heap_store :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Store (Val (LitLoc ?l)) (Val ?v)) _) =>
      iApply (wp_store l v with "[$]"); iNext; iIntros "?"; simpl
  | _ => fail "heap_store: redex is not a Store"
  end.

Ltac heap_alloc :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Alloc (Val _)) _) =>
      iApply wp_alloc; iNext;
      let l := fresh "l" in iIntros (l) "?"; simpl
  | _ => fail "heap_alloc: redex is not an Alloc"
  end.

(** Transparent call: unfold the FunDef body. *)
Ltac call_transparent_redex :=
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Call ?f ?args) _) =>
      let vs := strip_vals args in
      let entry := eval hnf in (fun_entries f) in
      lazymatch entry with
      | Some (FunDef ?params ?body) =>
          iApply (wp_call_unfold f params body vs);
            [ reflexivity | reflexivity | iNext; simpl ]
      | _ => fail "call_transparent: not a transparent (FunDef) call"
      end
  | _ => fail "call_transparent: redex is not a Call"
  end.

Ltac call_transparent_core :=
  popvals; focus_redex;
  lazymatch goal with
  | |- envs_entails _ (wp_exn (Call _ _) _) => call_transparent_redex
  | _ => fail "call_transparent: redex is not a Call"
  end.

Tactic Notation "call_transparent" := call_transparent_core.
Tactic Notation "call_transparent" constr(f) := check_callee f; call_transparent_core.


(** * While-loop invariant lemma (Loeb induction on a heap counter).

    Proves that a while loop of the standard form
      While {BinOp LtOp {Load l} {Val (LitInt bound)}}
            {Let "_t2" {Let "_t1" {Load l} {BinOp AddOp {Var "_t1"} ...}} {Store l ...}}
    with invariant [z <= bound] terminates with cell value [bound]. *)
Section while_lemma.
  Context `{!snakeletExn_heapGS_gen hlc Sigma}.
  Context `{FC : FunCtx}.
  Local Notation "'WPE' e {{ Q } }" := (wp_exn e Q)
    (at level 20, e, Q at level 200) : bi_scope.
  Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v) (at level 20) : bi_scope.

  Lemma wp_while_inv (l : loc) (bound : Z) (z : Z) (Phi : Result -> iProp Sigma) :
    l ↦ LitInt z -∗
    ⌜Z.le z bound⌝ -∗
    (l ↦ LitInt bound -∗ Phi (RVal LitUnit)) -∗
    WPE (While (BinOp LtOp (Load (Val (LitLoc l))) (Val (LitInt bound)))
              (Let "_t2" (Let "_t1" (Load (Val (LitLoc l)))
                 (BinOp AddOp (Var "_t1") (Val (LitInt 1))))
                 (Store (Val (LitLoc l)) (Var "_t2")))) {{ Phi }}.
  Proof.
    iLöb as "IH" forall (z Phi).
    iIntros "Hc %Hz Hwand".
    iApply wp_while; iNext; simpl.
    heap_load. pure_step. case_bool.
    - snakelet_pure_hyps.
      pure_step.  (* if true branch *)
      heap_load.  (* Load cell for body *)
      pure_step.  (* _t1 Let *)
      pure_step.  (* binop add *)
      pure_step.  (* _t2 Let *)
      heap_store. (* store result *)
      pure_step.  (* sequencing _ *)
      iRename select (_ ↦ _)%I into "Hpt".
      iApply ("IH" $! (z + 1)%Z Phi with "Hpt [] Hwand").
      { iPureIntro. apply (proj2 (Z.le_succ_l z bound)). exact Hcond. }
    - snakelet_pure_hyps.
      assert (z = bound) by lia. subst z.
      pure_step.  (* if false branch *)
      iApply wp_value. iApply "Hwand". iFrame.
  Qed.

  (** Generic while-loop invariant: the body's WP is a boxed hypothesis.
      Works for ANY body (including multi-cell) as long as the body
      increments the counter cell [l] by 1 each iteration.

      SIDE CONDITION [body_closed]: the throwaway binder ["_"] used by the
      While desugaring [Let "_" body (While ...)] must not occur free in
      [body], i.e. substituting through it is a no-op.  This is required
      for soundness: after one iteration the loop re-emerges as
      [While ... (subst "_" vv body)], and we need this to equal the
      original [While ... body] to apply the Loeb hypothesis.  For all
      generated bodies ["_"] is only ever a *binding* occurrence (Let "_"
      sequencing), never a free use, so callers discharge this by
      [intros; reflexivity]. *)
  Lemma wp_while_inv_gen (l : loc) (bound : Z) (z : Z) (body : sn_expr)
      (Phi : Result -> iProp Sigma) :
    (forall v, subst "_" v body = body) ->
    l ↦ LitInt z -∗
    ⌜Z.le z bound⌝ -∗
    □ (∀ (z' : Z), l ↦ LitInt z' -∗ ⌜(z' < bound)%Z⌝ -∗
        wp_exn body (fun r => match r with
            | RVal _ => l ↦ LitInt (z' + 1)
            | RExn lbl p => Phi (RExn lbl p)
            end)) -∗
    (l ↦ LitInt bound -∗ Phi (RVal LitUnit)) -∗
    WPE (While (BinOp LtOp (Load (Val (LitLoc l))) (Val (LitInt bound))) body) {{ Phi }}.
  Proof.
    intros Hbc.
    iLöb as "IH" forall (z Phi).
    iIntros "Hc %Hz #Hbody Hwand".
    iApply wp_while; iNext; simpl.
    (* Condition: focus into Load via heap_load *)
    heap_load. pure_step. case_bool.
    - snakelet_pure_hyps.
      pure_step.  (* if true branch *)
      iRename select (_ ↦ _)%I into "Hpt2".
      (* Focus into the body via wp_bind_item *)
      iApply (wp_bind_item (LetCtx "_" (While (BinOp LtOp (Load (Val (LitLoc l))) (Val (LitInt bound))) body))); [reflexivity|].
      iPoseProof ("Hbody" $! z with "Hpt2 []") as "Hwp".
      { iPureIntro. exact Hcond. }
      iApply (wp_wand with "Hwp").
      iIntros (r) "Hr". destruct r as [vv | lbl p].
      + (* RVal: cell is at z+1. Sequence into the While and recurse. *)
        iApply wp_let. iNext. simpl.
        (* Goal body is [subst "_" vv body]; the side condition rewrites
           it back to [body] so the Loeb hypothesis applies. *)
        rewrite (Hbc vv).
        iApply ("IH" $! (z + 1)%Z Phi with "Hr [] Hbody Hwand").
        iPureIntro. lia.
      + (* RExn: the exception escapes through wp_wand/implicit propagation *)
        iExact "Hr".
    - snakelet_pure_hyps.
      assert (z = bound) by lia. subst z.
      pure_step.  (* if false branch *)
      iApply wp_value. iApply "Hwand". iFrame.
  Qed.

  (** String-guard while loop, in genuine Hoare-rule form.

      This is the loop rule [{Inv /\ B} body {Inv}  =>  {Inv} while B do
      body {Inv /\ ~B}] specialised to the guard [B = (load c == g)], where
      the guard cell IS the loop variable.  [Inv : string -> iProp] is the
      loop invariant indexed by the guard cell's current value: [Inv s]
      holds all the OTHER loop state when the guard cell reads [s].

      Decomposition: the body obligation [Hbody] is a PREMISE -- it is the
      Hoare triple [{l ↦ g * Inv g} body {∃ s', l ↦ s' * Inv s' * guard-
      false}].  Callers discharge it with a SEPARATE named lemma
      ([<fn>_body_spec]), so the body is an independent, durable obligation
      rather than inline reasoning.

      Termination: the body's postcondition asserts [String.eqb s' g =
      false] -- one body run falsifies the guard, the well-founded measure.
      So the loop runs the body at most once: two finite [wp_while]
      unfoldings, NO coinduction / Loeb.

      [Hbc]: the desugaring binder ["_"] is not free in [body] (callers
      discharge by [intros; reflexivity]). *)
  Lemma wp_while_str (l : loc) (s0 g : string) (body : sn_expr)
      (Inv : string -> iProp Sigma) (Phi : Result -> iProp Sigma) :
    (forall v, subst "_" v body = body) ->
    l ↦ LitString s0 -∗
    Inv s0 -∗
    (* Body obligation (the Hoare triple, guard true so the cell reads g):
         {l ↦ g * Inv g} body {∃ s', l ↦ s' * Inv s' * eqb s' g = false}. *)
    (l ↦ LitString g -∗ Inv g -∗
        wp_exn body (fun r => match r with
            | RVal _ => ∃ s', l ↦ LitString s' ∗ Inv s' ∗ ⌜String.eqb s' g = false⌝
            | RExn lbl p => Phi (RExn lbl p)
            end)) -∗
    (* Closing wand: any guard-false state with the invariant establishes
       the post.  ONE wand covers both exits -- immediate (s0) and
       after-body (s') -- since both are guard-false states holding Inv. *)
    (∀ sf, ⌜String.eqb sf g = false⌝ -∗ l ↦ LitString sf -∗ Inv sf -∗ Phi (RVal LitUnit)) -∗
    WPE (While (BinOp EqOp (Load (Val (LitLoc l))) (Val (LitString g))) body) {{ Phi }}.
  Proof.
    intros Hbc.
    iIntros "Hc Hinv Hbody Hwand".
    (* First unfolding: evaluate the guard on [s0]. *)
    iApply wp_while; iNext; simpl.
    heap_load. pure_step. case_bool.
    - (* guard true: String.eqb s0 g = true, so s0 = g; run the body. *)
      snakelet_pure_hyps.
      apply String.eqb_eq in Hcond. subst s0.
      pure_step.  (* if true branch *)
      iRename select (_ ↦ _)%I into "Hpt2".
      iApply (wp_bind_item (LetCtx "_" (While (BinOp EqOp (Load (Val (LitLoc l))) (Val (LitString g))) body))); [reflexivity|].
      iPoseProof ("Hbody" with "Hpt2 Hinv") as "Hwp".
      iApply (wp_wand with "Hwp").
      iIntros (r) "Hr". destruct r as [vv | lbl p].
      + (* body returned: cell at s', Inv s', guard false.  Do the SECOND
           unfolding -- guard now false so the loop exits.  No Loeb. *)
        iDestruct "Hr" as (s') "(Hpt & Hinv' & %Hsf)".
        iApply wp_let. iNext. simpl.
        rewrite (Hbc vv).
        iApply wp_while; iNext; simpl.
        heap_load. pure_step.
        (* guard evaluates to LitBool (String.eqb s' g) = LitBool false *)
        rewrite Hsf. pure_step.  (* if false branch *)
        iRename select (_ ↦ _)%I into "Hpt3".
        iApply wp_value. iApply ("Hwand" $! s' with "[//] Hpt3 Hinv'").
      + (* body raised: exception propagates, Phi already holds. *)
        iExact "Hr".
    - (* guard false: String.eqb s0 g = false, exit immediately with Inv s0. *)
      snakelet_pure_hyps.
      pure_step.  (* if false branch *)
      iRename select (_ ↦ _)%I into "Hpt0".
      iApply wp_value. iApply ("Hwand" $! s0 with "[] Hpt0 Hinv").
      iPureIntro. exact Hcond || reflexivity.
  Qed.

(** Int-guard while loop — the integer analogue of [wp_while_str].

    [wp_while_int_guard] handles [while (load c > 0) do body] where the
    body stores a guard-falsifying value (<= 0) to the cell [c] in one
    step, exactly like [wp_while_str] falisifies the string guard.
    The invariant [Inv : Z -> iProp Sigma] is indexed by the cell's
    current value.  The body's postcondition asserts the new value [v']
    is NOT > 0, i.e. the guard is false.

    This is the direct integer analogue — two finite [wp_while] unfoldings,
    NO coinduction / Löb.  For multi-iteration loops (e.g. counting down
    from n to 0), a more general induction lemma is future work. *)

(** Löb-based while with a decreasing [nat] measure.

    [wp_while_decreasing] is the general multi-iteration lemma.  Instead of
    encoding the guard into the lemma (like [wp_while_str] hardcodes
    [String.eqb] and [wp_while_int_guard] hardcodes [GtOp 0]), this lemma
    takes the guard expression [c] as a parameter and requires the body
    obligation to prove the measure [n] strictly decreases.

    The invariant [I : nat -> iProp Sigma] carries the loop state indexed
    by the remaining iteration count.  The body takes [I n] and must prove
    [∃ n', n' < n ∗ I n'] on normal return.  When [n = 0], the guard is
    assumed to be false and the loop exits via [I 0 -∗ Φ (RVal LitUnit)].

    Termination follows from [Nat.lt_wf] via the step-indexed Löb induction. *)

End while_lemma.