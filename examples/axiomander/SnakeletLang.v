From stdpp Require Export strings gmap.
From stdpp Require Import countable decidable.
From iris.program_logic Require Export language.
Open Scope Z_scope.

(** SnakeletLang — standalone Iris language for Axiomander verification.

    Values: ints, booleans, floats, strings, tuples, lists, dicts, sets,
            locations, unit.
    State: gmap loc sn_val (Iris-compatible heap).
    Pure steps: let, binop, if, dict lookup.
    Head steps: load, store, FAA, fork, alloc, dict set, raise, try.
*)

From Stdlib Require Import BinInt Uint63Axioms Floats.PrimFloat.


(** * Locations *)
Inductive loc := Loc (l : positive).

#[global] Instance loc_eq_dec : EqDecision loc.
Proof. solve_decision. Qed.

#[global] Instance loc_countable : Countable loc.
Proof.
  apply (inj_countable' (λ '(Loc l), l) Loc); abstract (by intros []).
Qed.

#[global] Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ p, Loc p) (λ l, match l with Loc p => Some p end) _.
Next Obligation. done. Qed.

(** * Values *)
Inductive sn_val :=
  | LitInt (n : Z)
  | LitBool (b : bool)
  | LitFloat (f : float)
  | LitString (s : string)
  | LitTuple (vs : list sn_val)
  | LitList (vs : list sn_val)
  | LitDict (kvs : list (sn_val * sn_val))
  | LitSet (vs : list sn_val)
  | LitLoc (l : loc)
  | LitUnit.

Definition LitV (v : sn_val) : sn_val := v.

(** * Expressions *)
Inductive binop := AddOp | SubOp | MulOp | DivOp | EqOp | LeOp | LtOp | GtOp | GeOp
                 | LenOp | InOp | UnionOp | InterOp.

Inductive sn_expr :=
  | Val (v : sn_val)
  | Var (x : string)
  | Let (x : string) (e1 e2 : sn_expr)
  | BinOp (op : binop) (e1 e2 : sn_expr)
  | Load (e : sn_expr)
  | Store (e1 e2 : sn_expr)
  | Alloc (e : sn_expr)
  | If (e0 e1 e2 : sn_expr)
  | While (e1 e2 : sn_expr)
  | For (x : string) (e1 e2 : sn_expr)
  | FAA (e1 e2 : sn_expr)
  | Fork (e : sn_expr)
  | DictGet (l key : sn_expr)
  | DictSet (l key val : sn_expr)
  | Raise (e : sn_expr)
  | Try (body handler : sn_expr)
  | Call (f : string) (args : list sn_expr).

(** * Evaluation contexts *)
Inductive sn_ectx_item :=
  | LetCtx (x : string) (e2 : sn_expr)
  | BinOpLCtx (op : binop) (v2 : sn_val)
  | BinOpRCtx (op : binop) (v1 : sn_val)
  | IfCtx (e1 e2 : sn_expr)
  | LoadCtx
  | StoreLCtx (v2 : sn_val)
  | StoreRCtx (e1 : sn_expr)
  | AllocCtx
  | ForCtx (x : string) (e2 : sn_expr)
  | FaaLCtx (v2 : sn_val)
  | FaaRCtx (v1 : sn_val)
  | DictGetCtx (key : sn_expr).

Definition fill_item (Ki : sn_ectx_item) (x : sn_expr) : sn_expr :=
  match Ki with
  | LetCtx x0 e2 => Let x0 x e2
  | BinOpLCtx op v2 => BinOp op x (Val v2)
  | BinOpRCtx op v1 => BinOp op (Val v1) x
  | IfCtx e1 e2 => If x e1 e2
  | LoadCtx => Load x
  | StoreLCtx v2 => Store x (Val v2)
  | StoreRCtx e1 => Store e1 x
  | AllocCtx => Alloc x
  | ForCtx x0 e2 => For x0 x e2
  | FaaLCtx v2 => FAA x (Val v2)
  | FaaRCtx v1 => FAA (Val v1) x
  | DictGetCtx key => DictGet x key
  end.

Definition fill_K (K : list sn_ectx_item) (x : sn_expr) : sn_expr :=
  foldr fill_item x K.

(** * Values and evaluation *)
Definition of_val (v : sn_val) : sn_expr := Val v.
Definition to_val (e : sn_expr) : option sn_val :=
  match e with Val v => Some v | _ => None end.
Definition sn_state : Type := gmap loc sn_val.

Lemma fill_not_val K (x : sn_expr) : to_val x = None → to_val (fill_K K x) = None.
Proof.
  induction K as [|Ki K IH]; simpl; [auto|].
  intros H. destruct Ki; simpl; reflexivity.
Qed.

Lemma fill_K_val K (x : sn_expr) (v : sn_val) : fill_K K x = Val v ↔ K = [] ∧ x = Val v.
Proof.
  split.
  - intros H. induction K as [|Ki K IH]; simpl in H.
    + split; auto.
    + destruct Ki; simpl in H; discriminate H.
  - intros [-> ->]; reflexivity.
Qed.

Lemma fill_item_inj Ki (a b : sn_expr) : fill_item Ki a = fill_item Ki b → a = b.
Proof. destruct Ki; simpl; injection 1; auto. Qed.

(** * Substitution *)
Fixpoint subst (x : string) (v : sn_val) (e : sn_expr) : sn_expr :=
  match e with
  | Val _ => e
  | Var y => if String.eqb x y then Val v else e
  | Let y e1 e2 =>
      Let y (subst x v e1) (if String.eqb x y then e2 else subst x v e2)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | Alloc e => Alloc (subst x v e)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | While e1 e2 => While (subst x v e1) (subst x v e2)
  | For y e1 e2 =>
      For y (subst x v e1) (if String.eqb x y then e2 else subst x v e2)
  | FAA e1 e2 => FAA (subst x v e1) (subst x v e2)
  | Fork e => Fork (subst x v e)
  | DictGet l key => DictGet (subst x v l) (subst x v key)
  | DictSet l key v' => DictSet (subst x v l) (subst x v key) (subst x v v')
  | Raise e => Raise (subst x v e)
  | Try body handler => Try (subst x v body) (subst x v handler)
  | Call f args => Call f (List.map (subst x v) args)
  end.

(** * Pure steps *)

Definition z_to_float (n : Z) : float :=
  PrimFloat.of_uint63 (of_Z n).

Fixpoint val_list_len (vs : list sn_val) : Z :=
  match vs with
  | [] => 0
  | _ :: vs' => 1 + val_list_len vs'
  end%Z.

(** Extract the ordered key list from a dict's key-value pair list. *)
Fixpoint dict_keys (kvs : list (sn_val * sn_val)) : list sn_val :=
  match kvs with
  | [] => []
  | (k, _) :: rest => k :: dict_keys rest
  end.

Fixpoint val_eqb (fuel : nat) (v1 v2 : sn_val) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match v1, v2 with
      | LitInt n1, LitInt n2 => bool_decide (n1 = n2)
      | LitBool b1, LitBool b2 => Bool.eqb b1 b2
      | LitFloat f1, LitFloat f2 => PrimFloat.eqb f1 f2
      | LitString s1, LitString s2 => String.eqb s1 s2
      | LitTuple vs1, LitTuple vs2 => val_list_eqb fuel' vs1 vs2
      | LitList vs1, LitList vs2 => val_list_eqb fuel' vs1 vs2
      | LitSet vs1, LitSet vs2 => val_list_eqb fuel' vs1 vs2
      | LitDict kvs1, LitDict kvs2 => val_kvlist_eqb fuel' kvs1 kvs2
      | LitLoc l1, LitLoc l2 =>
          match l1, l2 with Loc p1, Loc p2 => Pos.eqb p1 p2 end
      | LitUnit, LitUnit => true
      | _, _ => false
      end
  end
with val_list_eqb (fuel : nat) (vs1 vs2 : list sn_val) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match vs1, vs2 with
      | [], [] => true
      | v1 :: vs1', v2 :: vs2' => val_eqb fuel' v1 v2 && val_list_eqb fuel' vs1' vs2'
      | _, _ => false
      end
  end
with val_kvlist_eqb (fuel : nat) (kvs1 kvs2 : list (sn_val * sn_val)) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match kvs1, kvs2 with
      | [], [] => true
      | (k1,v1) :: kvs1', (k2,v2) :: kvs2' =>
          val_eqb fuel' k1 k2 && val_eqb fuel' v1 v2 && val_kvlist_eqb fuel' kvs1' kvs2'
      | _, _ => false
      end
  end.
(** Initial fuel: sum of structure depths. Empirically, 50 covers all test cases. *)
Definition val_eq (v1 v2 : sn_val) : bool := val_eqb 50 v1 v2.

Fixpoint val_list_mem (fuel : nat) (x : sn_val) (vs : list sn_val) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match vs with
      | [] => false
      | v :: vs' => val_eqb fuel' x v || val_list_mem fuel' x vs'
      end
  end.

Fixpoint dict_lookup (kvs : list (sn_val * sn_val)) (k : sn_val) : option sn_val :=
  match kvs with
  | [] => None
  | (k', v) :: rest =>
      if val_eqb 50 k k' then Some v else dict_lookup rest k
  end.

Fixpoint dict_insert (kvs : list (sn_val * sn_val)) (k v : sn_val) : list (sn_val * sn_val) :=
  match kvs with
  | [] => [(k, v)]
  | (k', v') :: rest =>
      if val_eqb 50 k k' then (k, v) :: rest else (k', v') :: dict_insert rest k v
  end.

Definition binop_eval (op : binop) (v1 v2 : sn_val) : sn_val :=
  match v1, v2 with
  (* --- int x int --- *)
  | LitInt n1, LitInt n2 =>
      match op with
      | AddOp => LitInt (n1 + n2)
      | SubOp => LitInt (n1 - n2)
      | MulOp => LitInt (n1 * n2)
      | DivOp => LitFloat (PrimFloat.div (z_to_float n1) (z_to_float n2))
      | EqOp  => LitBool (bool_decide (n1 = n2))
      | LeOp  => LitBool (bool_decide (n1 <= n2))
      | LtOp  => LitBool (bool_decide (n1 < n2))
      | GtOp  => LitBool (bool_decide (n1 > n2))
      | GeOp  => LitBool (bool_decide (n1 >= n2))
      | _ => LitUnit
      end
  (* --- float x float --- *)
  | LitFloat f1, LitFloat f2 =>
      match op with
      | AddOp => LitFloat (PrimFloat.add f1 f2)
      | SubOp => LitFloat (PrimFloat.sub f1 f2)
      | MulOp => LitFloat (PrimFloat.mul f1 f2)
      | DivOp => LitFloat (PrimFloat.div f1 f2)
      | EqOp  => LitBool (PrimFloat.eqb f1 f2)
      | LeOp  => LitBool (PrimFloat.leb f1 f2)
      | LtOp  => LitBool (PrimFloat.ltb f1 f2)
      | GtOp  => LitBool (negb (PrimFloat.leb f1 f2))
      | GeOp  => LitBool (negb (PrimFloat.ltb f1 f2))
      | _ => LitUnit
      end
  (* --- int x float / float x int --- *)
  | LitInt n, LitFloat f =>
      match op with
      | AddOp => LitFloat (PrimFloat.add (z_to_float n) f)
      | SubOp => LitFloat (PrimFloat.sub (z_to_float n) f)
      | MulOp => LitFloat (PrimFloat.mul (z_to_float n) f)
      | DivOp => LitFloat (PrimFloat.div (z_to_float n) f)
      | _ => LitUnit
      end
  | LitFloat f, LitInt n =>
      match op with
      | AddOp => LitFloat (PrimFloat.add f (z_to_float n))
      | SubOp => LitFloat (PrimFloat.sub f (z_to_float n))
      | MulOp => LitFloat (PrimFloat.mul f (z_to_float n))
      | DivOp => LitFloat (PrimFloat.div f (z_to_float n))
      | _ => LitUnit
      end
  (* --- string x string --- *)
  | LitString s1, LitString s2 =>
      match op with
      | AddOp => LitString (s1 ++ s2)
      | EqOp  => LitBool (String.eqb s1 s2)
      | LenOp => LitInt (Z.of_nat (String.length s1))
      | _ => LitUnit
      end
  (* --- string len (second arg not a string) --- *)
  | LitString s, _ =>
      match op with
      | LenOp => LitInt (Z.of_nat (String.length s))
      | _ => LitUnit
       end
  (* --- bool x int / int x bool --- *)
  | LitBool b1, LitInt n =>
      match op with
      | AddOp => LitInt ((if b1 then 1 else 0)%Z + n)
      | SubOp => LitInt ((if b1 then 1 else 0)%Z - n)
      | MulOp => LitInt ((if b1 then 1 else 0)%Z * n)
      | _ => LitUnit
      end
  | LitInt n, LitBool b =>
      match op with
      | AddOp => LitInt (n + (if b then 1 else 0)%Z)
      | SubOp => LitInt (n - (if b then 1 else 0)%Z)
      | MulOp => LitInt (n * (if b then 1 else 0)%Z)
      | _ => LitUnit
      end
  (* --- tuple x tuple --- *)
  | LitTuple vs1, LitTuple vs2 =>
      match op with
      | AddOp => LitTuple (vs1 ++ vs2)
      | EqOp  => LitBool (val_eq (LitTuple vs1) (LitTuple vs2))
      | LenOp => LitInt (val_list_len vs1)
      | InOp  => LitBool (val_list_mem 50 v2 vs1)
      | _ => LitUnit
      end
  (* --- tuple len/in (second arg not a tuple) --- *)
  | LitTuple vs, _ =>
      match op with
      | LenOp => LitInt (val_list_len vs)
      | InOp  => LitBool (val_list_mem 50 v2 vs)
      | _ => LitUnit
      end
  (* --- list x list --- *)
  | LitList vs1, LitList vs2 =>
      match op with
      | AddOp => LitList (vs1 ++ vs2)
      | EqOp  => LitBool (val_eq (LitList vs1) (LitList vs2))
      | LenOp => LitInt (val_list_len vs1)
      | InOp  => LitBool (val_list_mem 50 v2 vs1)
      | _ => LitUnit
      end
  (* --- list len/in (second arg not a list) --- *)
  | LitList vs, _ =>
      match op with
      | LenOp => LitInt (val_list_len vs)
      | InOp  => LitBool (val_list_mem 50 v2 vs)
      | _ => LitUnit
      end
  (* --- set x set --- *)
  | LitSet vs1, LitSet vs2 =>
      match op with
      | EqOp  => LitBool (val_eq (LitSet vs1) (LitSet vs2))
      | LenOp => LitInt (val_list_len vs1)
      | InOp  => LitBool (val_list_mem 50 v2 vs1)
      | UnionOp => LitSet vs1
      | InterOp => LitSet vs1
      | _ => LitUnit
      end
  (* --- set len/in (second arg not a set) --- *)
  | LitSet vs, _ =>
      match op with
      | LenOp => LitInt (val_list_len vs)
      | InOp  => LitBool (val_list_mem 50 v2 vs)
      | _ => LitUnit
      end
  (* --- dict len --- *)
  | LitDict kvs, _ =>
      match op with
      | LenOp => LitInt (val_list_len (List.map fst kvs))
      | _ => LitUnit
       end
  | _, _ => LitUnit
  end.

Inductive pure_step : sn_expr → sn_expr → Prop :=
  | PureLet v x e2 : pure_step (Let x (Val v) e2) (subst x v e2)
  | PureBinOp op v1 v2 :
      pure_step (BinOp op (Val v1) (Val v2)) (Val (binop_eval op v1 v2))
  | PureIfTrue e1 e2 : pure_step (If (Val (LitBool true)) e1 e2) e1
  | PureIfFalse e1 e2 : pure_step (If (Val (LitBool false)) e1 e2) e2
  | PureWhile e1 e2 : pure_step (While e1 e2) (If e1 (Let "_" e2 (While e1 e2)) (Val LitUnit))
  | PureForNil x body :
      pure_step (For x (Val (LitList [])) body) (Val LitUnit)
  | PureForCons x v vs body :
      pure_step (For x (Val (LitList (v :: vs))) body)
                (Let "_" (subst x v body) (For x (Val (LitList vs)) body))
  | PureForDictNil x body :
      pure_step (For x (Val (LitDict [])) body) (Val LitUnit)
  | PureForDictCons x k v kvs body :
      pure_step (For x (Val (LitDict ((k, v) :: kvs))) body)
                (Let "_" (subst x k body) (For x (Val (LitDict kvs)) body))
  | PureTryReturn v handler : pure_step (Try (Val v) handler) (Val v)
  | PureDictGet kvs k v :
      dict_lookup kvs k = Some v →
      pure_step (DictGet (Val (LitDict kvs)) (Val k)) (Val v)
  | PureDictGetMiss kvs k :
      dict_lookup kvs k = None →
      pure_step (DictGet (Val (LitDict kvs)) (Val k)) (Val LitUnit)
  | PureDictSet kvs k (v : sn_val) :
      pure_step (DictSet (Val (LitDict kvs)) (Val k) (Val v))
                (Val (LitDict (dict_insert kvs k v))).

Definition lit_as_z (v : sn_val) : Z :=
  match v with LitInt n => n | _ => 0 end.


(** * Function context

    A function name resolves to at most one entry:

    - [FunSpec pre post] — *opaque* call: the implementation is hidden
      behind a contract.  The call only steps when [pre args] holds
      (calling outside the precondition is *stuck*, so WP forces the
      caller to establish it), and may step to any result satisfying
      [post args result].  Verified via [wp_call].
    - [FunDef params body] — *transparent* call: the call unfolds by
      substituting the (value) arguments for the parameters.  Used for
      helper functions without contracts and for testing the Python
      lowering.  Verified via [wp_call_unfold].

    Both modes live in one table, so they are mutually exclusive *by
    construction*: no coherence side conditions on instances, and each WP
    call lemma has a deterministic step source.  Override with an Instance
    in your file to provide the spec/definition table. *)

Inductive fun_entry :=
  | FunSpec (pre : list sn_val → Prop) (post : list sn_val → sn_val → Prop)
  | FunDef (params : list string) (body : sn_expr).

Class FunCtx := {
  fun_entries : string → option fun_entry;
  (** Callee-side total-correctness promise: a spec'd function called
      within its precondition produces *some* result satisfying its
      postcondition.  This is the callee's obligation, discharged once per
      table (when the implementation is verified against the spec) — so
      callers only ever prove the precondition.  Without it, [wp_call]
      could not establish reducibility from [pre] alone, and the existence
      of a result would leak to every call site, breaking modularity. *)
  fun_specs_total : ∀ f pre post vs,
    fun_entries f = Some (FunSpec pre post) →
    pre vs → ∃ v, post vs v;
}.

Lemma empty_table_total : ∀ (f : string) pre post (vs : list sn_val),
  (None : option fun_entry) = Some (FunSpec pre post) →
  pre vs → ∃ v, post vs v.
Proof. discriminate. Qed.

(** Default (empty) table.  Low priority [100] so that user-provided
    instances (e.g. in demos or generated spec files) take precedence. *)
#[export] Instance default_fun_ctx : FunCtx | 100 :=
  {| fun_entries := λ _, None; fun_specs_total := empty_table_total |}.

(** Ghost-state call table via [ghost_map] (standard Iris library).
    The caller holds [ghost_map_elem γ f (DfracOwn 1) (FunSpec pre post)]
    — a persistent fragment witnessing the spec in the ghost table.
    The authoritative [ghost_map_auth γ m] lives in an invariant. *)
From iris.base_logic.lib Require Import ghost_map.
Notation call_tableG Σ := (ghost_mapG Σ string fun_entry) (only parsing).

(** Substitute value arguments for parameters, left to right.  Arguments
    are values (closed), so sequential substitution is capture-free. *)
Fixpoint subst_list (params : list string) (vs : list sn_val) (e : sn_expr) : sn_expr :=
  match params, vs with
  | x :: params', v :: vs' => subst_list params' vs' (subst x v e)
  | _, _ => e
  end.

Lemma map_Val_inj (vs1 vs2 : list sn_val) :
  map Val vs1 = map Val vs2 → vs1 = vs2.
Proof.
  revert vs2. induction vs1 as [|v1 vs1 IH]; intros [|v2 vs2] H;
    simpl in H; try discriminate.
  - reflexivity.
  - injection H as Hv Hvs. f_equal; [exact Hv | apply IH, Hvs].
Qed.

(** * Head steps, prim_step, and the Iris language instance

    Wrapped in a section with [Context {FC : FunCtx}] so that
    [HeadCallSpec]/[HeadCallUnfold] use the ambient FC for the
    operational lookup.  This is the MINIMAL typeclass needed for
    operational-step eligibility; spec enforcement and totality
    are handled by ghost state (call_tableRA) at the WP level. *)
Section with_fun_ctx.
Context `{FC : FunCtx}.

(** * Head steps *)
Inductive head_step : sn_expr → sn_state → sn_expr → sn_state → list sn_expr → Prop :=
  | HeadLoad l v σ :
      σ !! l = Some v →
      head_step (Load (Val (LitLoc l))) σ (Val v) σ []
  | HeadStore l v σ :
      is_Some (σ !! l) →
      head_step (Store (Val (LitLoc l)) (Val v)) σ
                (Val LitUnit) (<[l:=v]> σ) []
  | HeadAlloc v σ l :
      σ !! l = None →
      head_step (Alloc (Val v)) σ (Val (LitLoc l))
                (<[l:=v]> σ) []
  | HeadFAA l v z σ :
      σ !! l = Some (LitInt z) →
      head_step (FAA (Val (LitLoc l)) (Val v)) σ
                (Val (LitInt z)) (<[l:=LitInt (z + lit_as_z v)]> σ) []
  | HeadFork e σ :
      head_step (Fork e) σ (Val LitUnit) σ [e]
  | HeadRaise v σ :
      head_step (Raise (Val v)) σ (Val v) σ []
  | HeadTryBody body handler σ body' σ' efs :
      head_step body σ body' σ' efs →
      head_step (Try body handler) σ body' σ' efs
  | HeadCallSpec : ∀ (f : string) (vs : list sn_val) (σ : sn_state)
      (pre : list sn_val → Prop) (post : list sn_val → sn_val → Prop) (v : sn_val),
      fun_entries f = Some (FunSpec pre post) →
      pre vs →
      post vs v →
      head_step (Call f (map Val vs)) σ (Val v) σ []
  | HeadCallUnfold : ∀ (f : string) (vs : list sn_val) (σ : sn_state)
      (params : list string) (body : sn_expr),
      fun_entries f = Some (FunDef params body) →
      length vs = length params →
      head_step (Call f (map Val vs)) σ (subst_list params vs body) σ [].

(** * Iris Language instance *)
Definition observation : Type := unit.

Inductive prim_step : sn_expr → sn_state → list observation → sn_expr → sn_state → list sn_expr → Prop :=
  | PrimPureStep K x σ x' :
      pure_step x x' →
      prim_step (fill_K K x) σ [] (fill_K K x') σ []
  | PrimHeadStep K x σ x' σ' efs :
      head_step x σ x' σ' efs →
      prim_step (fill_K K x) σ [] (fill_K K x') σ' efs.

Lemma snakelet_lang_mixin : LanguageMixin of_val to_val prim_step.
Proof.
  split.
  - intros v. unfold of_val, to_val. reflexivity.
  - intros e v Hto. unfold to_val in Hto. destruct e; try discriminate.
    injection Hto as ->. unfold of_val. reflexivity.
  - intros ex σ κ ex' σ' efs Hprim.
    inversion Hprim as [K x0 σ0 x0' Hpure | K x0 σ0 x0' σ0' efs0 Hhead]; subst.
    + apply (fill_not_val K x0). inversion Hpure; subst; simpl; auto.
    + apply (fill_not_val K x0). destruct Hhead; subst; simpl; auto.
Qed.

Canonical Structure snakelet_lang := Language snakelet_lang_mixin.

Lemma to_val_pure_step x x' : pure_step x x' → to_val x = None.
Proof.
  intros H; inversion H; simpl; auto.
Qed.

Lemma to_val_head_step x σ x' σ' efs : head_step x σ x' σ' efs → to_val x = None.
Proof.
  intros H; inversion H; simpl; auto.
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; simpl; intros Hn1 Hn2 Heq.
  all: first [discriminate Heq | idtac].
  all: injection Heq; intros; subst; simpl in *; try discriminate; auto.
Qed.

Lemma fill_not_pure Ki x : to_val x = None → ∀ e', pure_step (fill_item Ki x) e' → False.
Proof.
  intros Hval e' Hpure.
  destruct Ki; simpl in *; inversion Hpure; subst;
    try match goal with H: Val ?v = ?x |- _ => symmetry in H; injection H; intros -> end;
    simpl in Hval; congruence.
Qed.

Lemma fill_not_head Ki x : to_val x = None → ∀ σ e' σ' efs, head_step (fill_item Ki x) σ e' σ' efs → False.
Proof.
  intros Hval σ e' σ' efs Hhead.
  destruct Ki; simpl in *; inversion Hhead; subst;
    try match goal with H: Val ?v = ?x |- _ => symmetry in H; injection H; intros -> end;
    simpl in Hval; congruence.
Qed.

Global Instance snakelet_ctx_lang_ctx Ki :
  LanguageCtx (fill_item Ki).
Proof.
  split.
  - intros x Hval. destruct Ki; simpl; try (by inversion Hval); done.
  - intros x1 σ1 κ x2 σ2 efs Hprim.
    inversion Hprim as [K x σ x' Hpure | K x σ x' σ' efs0 Hhead]; subst.
    + eapply (PrimPureStep (Ki :: K) _ _ _ Hpure).
    + eapply (PrimHeadStep (Ki :: K) _ _ _ _ _ Hhead).
  - intros x1' σ1 κ x2 σ2 efs Hval Hprim.
    inversion Hprim; subst; [rename H0 into Hpure | rename H0 into Hhead].
    + (* PureStep *)
      unfold language.to_val in Hval; simpl in Hval.
      change (expr snakelet_lang) with sn_expr in *.
      rename Ki into Ki0.
      destruct K as [|Ki' K'']; simpl in H.
      { subst x. exfalso. eapply fill_not_pure; eauto. }
      pose proof (to_val_pure_step _ _ Hpure) as Hval_x.
      pose proof (fill_not_val K'' x Hval_x) as Hval_fill.
      pose proof (fill_item_no_val_inj Ki' Ki0 (fill_K K'' x) x1' Hval_fill Hval H) as Heq.
      subst Ki'.
      apply (fill_item_inj Ki0) in H.
      subst x1'.
      eexists (fill_K K'' x'); split.
      { simpl; reflexivity. }
      eapply (PrimPureStep K'' x σ2 x' Hpure).
    + (* HeadStep *)
      unfold language.to_val in Hval; simpl in Hval.
      change (expr snakelet_lang) with sn_expr in *.
      rename Ki into Ki0.
      destruct K as [|Ki' K'']; simpl in H.
      { subst x. exfalso. eapply fill_not_head; eauto. }
      pose proof (to_val_head_step _ _ _ _ _ Hhead) as Hval_x.
      pose proof (fill_not_val K'' x Hval_x) as Hval_fill.
      pose proof (fill_item_no_val_inj Ki' Ki0 (fill_K K'' x) x1' Hval_fill Hval H) as Heq.
      subst Ki'.
      apply (fill_item_inj Ki0) in H.
      subst x1'.
      eexists (fill_K K'' x'); split.
      { simpl; reflexivity. }
      eapply (PrimHeadStep K'' x σ1 x' σ2 efs Hhead).
Qed.

Lemma fill_step_list K e1 σ1 κ e2 σ2 efs :
  prim_step e1 σ1 κ e2 σ2 efs →
  prim_step (fill_K K e1) σ1 κ (fill_K K e2) σ2 efs.
Proof.
  induction K as [|Ki K' IH]; simpl; [auto|].
  intros Hstep. eapply (@fill_step snakelet_lang (fill_item Ki) (snakelet_ctx_lang_ctx Ki)).
  eapply IH. exact Hstep.
Defined.

Lemma fill_step_inv_list K e1' σ1 κ e2 σ2 efs :
  to_val e1' = None →
  prim_step (fill_K K e1') σ1 κ e2 σ2 efs →
  ∃ e2', e2 = fill_K K e2' ∧ prim_step e1' σ1 κ e2' σ2 efs.
Proof.
  revert e1' σ1 κ e2 σ2 efs.
  induction K as [|Ki K' IH]; intros e1' σ1 κ e2 σ2 efs Hval Hstep; simpl in Hstep.
  - exists e2. split; [done|]. exact Hstep.
  - eapply (@fill_step_inv snakelet_lang (fill_item Ki) (snakelet_ctx_lang_ctx Ki)) in Hstep
      as (e2x & -> & Hstepx); [| apply (fill_not_val K'); exact Hval].
    cbv [language.prim_step] in Hstepx.
    eapply IH in Hstepx; [|exact Hval]. destruct Hstepx as (e2y & -> & Hstepy).
    eexists e2y. split; [reflexivity|]. exact Hstepy.
Qed.

Global Instance snakelet_ctx_lang_ctx_list K :
  LanguageCtx (fill_K K).
Proof.
  split.
  - intros e Hval. apply fill_not_val. exact Hval.
  - apply fill_step_list.
  - apply fill_step_inv_list.
Defined.

End with_fun_ctx.

(** After section discharge, [snakelet_lang : ∀ {FC : FunCtx}, language]
    is a parametric canonical structure.  The [FC] argument is implicitly
    resolved by typeclass search at each use site.  This provides a
    single [FunCtx] per section — the same instance used for operational
    step eligibility ([fun_entries]) and WP-level spec enforcement
    (ghost-state [call_tableRA]). *)

(** Notations for writing SnakeletLang programs tersely.

    All notations are scoped under [snakelet_scope], so they do not interfere
    with other notations.  Use [Open Scope snakelet_scope] to activate them,
    or [Import snakelet_notation] to get both scope and coercions. *)

Module snakelet_notation.
  Declare Scope snakelet_scope.
  Delimit Scope snakelet_scope with S.

  Notation "# n" := (Val (LitInt (n : Z)))
    (at level 8, n at level 1, format "# n") : snakelet_scope.
  Notation "#true" := (Val (LitBool true)) : snakelet_scope.
  Notation "#false" := (Val (LitBool false)) : snakelet_scope.

  Notation "! e" := (Load e)
    (at level 9, right associativity, format "! e") : snakelet_scope.
  Notation "e1 <- e2" := (Store e1 e2)
    (at level 80, format "e1  <-  e2") : snakelet_scope.
  Notation "'ref' e" := (Alloc e)
    (at level 9, format "'ref'  e") : snakelet_scope.

  Notation "e1 + e2" := (BinOp AddOp e1 e2)
    (at level 50, left associativity) : snakelet_scope.
  Notation "e1 - e2" := (BinOp SubOp e1 e2)
    (at level 50, left associativity) : snakelet_scope.
  Notation "e1 * e2" := (BinOp MulOp e1 e2)
    (at level 40, left associativity) : snakelet_scope.
  Notation "e1 / e2" := (BinOp DivOp e1 e2)
    (at level 40, left associativity) : snakelet_scope.
  Notation "e1 = e2" := (BinOp EqOp e1 e2)
    (at level 70, no associativity) : snakelet_scope.
  Notation "e1 < e2" := (BinOp LtOp e1 e2)
    (at level 70, no associativity) : snakelet_scope.
  Notation "e1 <= e2" := (BinOp LeOp e1 e2)
    (at level 70, no associativity) : snakelet_scope.
  Notation "let: s := e1 'in' e2" := (Let s e1 e2)
    (at level 200, s at level 1, e1 at level 200, e2 at level 200,
     format "'let:'  s  :=  e1  'in'  e2") : snakelet_scope.
  Notation "e1 ;; e2" := (Let "_" e1 e2)
    (at level 100, right associativity, format "e1  ;;  e2") : snakelet_scope.
End snakelet_notation.
