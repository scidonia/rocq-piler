From stdpp Require Export strings gmap.
From stdpp Require Import countable decidable.
From Stdlib Require Import PrimFloat.
From Stdlib Require Import Uint63.
Open Scope Z_scope.
Open Scope float_scope.

(** SnakeletExnLang -- parallel development of SnakeletLang with first-class
    exceptions, following van Collem / de Vilhena / Krebbers, "Backwards-
    Compatible Row-Based Exceptions in ML" (PLDI 2026).

    Design:
    - [Raise (Val v)] is a STUCK terminal expression (uncaught exception),
      not a value.  [to_val (Raise (Val v)) = None].
    - [Result := RVal v | RExn label payload] captures the two ways a
      program terminates.  The (hand-rolled) WP postcondition ranges over
      [Result], split into the two-postcondition form (Phi_E | Phi_V).
    - Exceptions are label + payload: [LitExn label payload], matching the
      paper's [l v].  [raises(ValueError, cond)] dispatches on [label].
    - [Try] is an evaluation context (so the body reduces inside it), but
      has NO head step.  Pure rules:
        try (Val v) h          -> v                 (normal: handler skipped)
        try (Raise (Val ev)) h -> App-of-handler    (exception: handler runs)
    - Raise unwinding: for any NON-try context item Ki,
        fill_item Ki (Raise (Val v)) -> Raise (Val v)
      i.e. [K[raise v] -> raise v] when K is neutral (paper's rule).

    This file is standalone; it does not touch SnakeletLang.v.  Once the
    8-lemma gate in SnakeletExnDemo.v is Qed, we wire the Python pipeline. *)

From Stdlib Require Import BinInt.

(** * Locations *)
Inductive loc := Loc (l : positive).

#[global] Instance loc_eq_dec : EqDecision loc.
Proof. solve_decision. Qed.

#[global] Instance loc_countable : Countable loc.
Proof.
  apply (inj_countable' (fun '(Loc l) => l) Loc); abstract (by intros []).
Qed.

#[global] Program Instance loc_infinite : Infinite loc :=
  inj_infinite (fun p => Loc p) (fun l => match l with Loc p => Some p end) _.
Next Obligation. done. Qed.

(** * Values *)
Inductive sn_val :=
  | LitInt (n : Z)
  | LitBool (b : bool)
  | LitString (s : string)
  | LitFloat (f : float)
  | LitLoc (l : loc)
  | LitUnit
  | LitExn (label : string) (payload : sn_val)    (* exception object: label + value *)
  | LitList (vs : list sn_val)                    (* immutable list value *)
  | LitTuple (vs : list sn_val)                   (* immutable tuple value *)
  | LitDict (kvs : list (sn_val * sn_val))        (* immutable dict value *)
  | LitSet (vs : list sn_val).                    (* immutable set value *)

(** * Expressions *)
Inductive binop := AddOp | SubOp | MulOp | DivOp | EqOp | LeOp | LtOp | GtOp | GeOp
  | AndOp | OrOp | NeOp | ModOp | InOp | LenOp | UnionOp | InterOp
  | AppendOp | LengthOp | DictGetOp | DictGetIntOp | MkKeyErrOp | SetAddOp
  | StrIndexOp | StartsWithOp | EndsWithOp | ToLowerOp | ToUpperOp | DictSetOp
  | StrContainsOp | TupleOp.

Inductive sn_expr :=
  | Val (v : sn_val)
  | Var (x : string)
  | Let (x : string) (e1 e2 : sn_expr)
  | BinOp (op : binop) (e1 e2 : sn_expr)
  | Load (e : sn_expr)
  | Store (e1 e2 : sn_expr)
  | Alloc (e : sn_expr)
  | If (e0 e1 e2 : sn_expr)
  | Raise (e : sn_expr)
  | Try (body : sn_expr) (x : string) (handler : sn_expr)
  | While (e1 e2 : sn_expr)
  | For (x : string) (e1 e2 : sn_expr)
  | Call (f : string) (args : list sn_expr).

(** * Evaluation contexts.  Try IS a context (body reduces inside it). *)
Inductive sn_ectx_item :=
  | LetCtx (x : string) (e2 : sn_expr)
  | BinOpLCtx (op : binop) (v2 : sn_val)
  | BinOpRCtx (op : binop) (e1 : sn_expr)
  | LoadCtx
  | StoreLCtx (v2 : sn_val)
  | StoreRCtx (e1 : sn_expr)
  | AllocCtx
  | IfCtx (e1 e2 : sn_expr)
  | RaiseCtx
  | TryCtx (x : string) (handler : sn_expr)
  | ForCtx (x : string) (e2 : sn_expr).

(** Is this context item neutral (i.e. NOT a try frame)?  Raise unwinds
    through neutral contexts but is caught by try frames. *)
Definition neutral (Ki : sn_ectx_item) : bool :=
  match Ki with TryCtx _ _ => false | _ => true end.

Definition fill_item (Ki : sn_ectx_item) (x : sn_expr) : sn_expr :=
  match Ki with
  | LetCtx x0 e2 => Let x0 x e2
  | BinOpLCtx op v2 => BinOp op x (Val v2)
  | BinOpRCtx op e1 => BinOp op e1 x
  | LoadCtx => Load x
  | StoreLCtx v2 => Store x (Val v2)
  | StoreRCtx e1 => Store e1 x
  | AllocCtx => Alloc x
  | IfCtx e1 e2 => If x e1 e2
  | RaiseCtx => Raise x
  | TryCtx x0 h => Try x x0 h
  | ForCtx x0 e2 => For x0 x e2
  end.

Definition fill_K (K : list sn_ectx_item) (x : sn_expr) : sn_expr :=
  foldr fill_item x K.

(** * Values and to_val.  CRUCIAL: Raise (Val v) is NOT a value. *)
Definition of_val (v : sn_val) : sn_expr := Val v.
Definition to_val (e : sn_expr) : option sn_val :=
  match e with Val v => Some v | _ => None end.
Definition sn_state : Type := gmap loc sn_val.

(** * Results: the two ways a program terminates. *)
Inductive Result :=
  | RVal (v : sn_val)
  | RExn (label : string) (payload : sn_val).

(** Reify a Result as an expression: a value, or an uncaught raise. *)
Definition expr_of_result (r : Result) : sn_expr :=
  match r with
  | RVal v => Val v
  | RExn lbl pay => Raise (Val (LitExn lbl pay))
  end.

(** * Cell updates: the explicit state change of a stateful opaque call.
    An opaque spec's post yields a [Result] plus a list of cell
    replacements; applying them to the heap gives the post-state.
    Explicit updates (not abstract state relations) are what let the WP
    continuation thread [gen_heap_interp] across the call. *)
Definition cell_updates : Type := list (loc * sn_val).

Fixpoint apply_updates (sigma : sn_state) (ups : cell_updates) : sn_state :=
  match ups with
  | [] => sigma
  | (l, v) :: rest => apply_updates (<[l := v]> sigma) rest
  end.

(** Every updated cell already exists (no allocation through specs). *)
Definition updates_dom_in (sigma : sn_state) (ups : cell_updates) : Prop :=
  Forall (fun '(l, _) => is_Some (sigma !! l)) ups.

(** A terminal expression is either a value or an uncaught [Raise (Val v)].
    [result_of] reads off the Result; it is None for reducible expressions. *)
Definition result_of (e : sn_expr) : option Result :=
  match e with
  | Val v => Some (RVal v)
  | Raise (Val (LitExn lbl pay)) => Some (RExn lbl pay)
  | _ => None
  end.

(** * Foundational fill / to_val lemmas (FC-independent). *)
Lemma fill_not_val K (x : sn_expr) : to_val x = None -> to_val (fill_K K x) = None.
Proof.
  induction K as [|Ki K IH]; simpl; [auto|].
  intros H. destruct Ki; simpl; reflexivity.
Qed.

Lemma fill_K_val K (x : sn_expr) (v : sn_val) : fill_K K x = Val v <-> K = [] /\ x = Val v.
Proof.
  split.
  - intros H. induction K as [|Ki K IH]; simpl in H.
    + split; auto.
    + destruct Ki; simpl in H; discriminate H.
  - intros [-> ->]; reflexivity.
Qed.

Lemma fill_item_inj Ki (a b : sn_expr) : fill_item Ki a = fill_item Ki b -> a = b.
Proof. destruct Ki; simpl; injection 1; auto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None -> to_val e2 = None ->
  fill_item Ki1 e1 = fill_item Ki2 e2 -> Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; simpl; intros Hn1 Hn2 Heq;
    first [discriminate Heq | idtac];
    injection Heq; intros; subst; simpl in *; try discriminate; auto.
Qed.

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
  | Raise e => Raise (subst x v e)
  | Try body y h =>
      Try (subst x v body) y (if String.eqb x y then h else subst x v h)
  | While e1 e2 => While (subst x v e1) (subst x v e2)
  | For y e1 e2 =>
      For y (subst x v e1) (if String.eqb x y then e2 else subst x v e2)
  | Call f args => Call f (List.map (subst x v) args)
  end.

Fixpoint subst_list (xs : list string) (vs : list sn_val) (e : sn_expr) : sn_expr :=
  match xs, vs with
  | x :: xs', v :: vs' => subst_list xs' vs' (subst x v e)
  | _, _ => e
  end.

(** * Structural value equality on scalar keys.

    Dict/field keys in practice are scalar literals (strings for model
    field names, ints/strings for dict keys).  Compound keys (lists,
    dicts, sets) are not hashable in Python and never appear as keys, so
    [sn_val_eqb] returns [false] for them -- a sound under-approximation
    of structural equality restricted to the hashable domain. *)
Definition sn_val_eqb (a b : sn_val) : bool :=
  match a, b with
  | LitInt n1, LitInt n2 => Z.eqb n1 n2
  | LitBool b1, LitBool b2 => Bool.eqb b1 b2
  | LitString s1, LitString s2 => String.eqb s1 s2
  | LitFloat f1, LitFloat f2 => PrimFloat.eqb f1 f2
  | LitUnit, LitUnit => true
  | _, _ => false
  end.

(** Full structural comparison for compound sn_val types (lists,
    tuples).  Used in contract value comparisons.  Dicts and sets
    are omitted — they use set-bag semantics which need a more
    sophisticated comparison. *)
Fixpoint sn_val_eqb_full (a b : sn_val) : bool :=
  match a, b with
  | LitInt n1, LitInt n2 => Z.eqb n1 n2
  | LitBool b1, LitBool b2 => Bool.eqb b1 b2
  | LitString s1, LitString s2 => String.eqb s1 s2
  | LitFloat f1, LitFloat f2 => PrimFloat.eqb f1 f2
  | LitUnit, LitUnit => true
  | LitList vs1, LitList vs2 =>
      (fix go xs ys := match xs, ys with
       | [], [] => true
       | x::xs', y::ys' => sn_val_eqb_full x y && go xs' ys'
       | _, _ => false end) vs1 vs2
  | LitTuple vs1, LitTuple vs2 =>
      (fix go xs ys := match xs, ys with
       | [], [] => true
       | x::xs', y::ys' => sn_val_eqb_full x y && go xs' ys'
       | _, _ => false end) vs1 vs2
  | _, _ => false
  end.

(** * Dictionary / model field projection.

    [dict_lookup d k] walks the key-value list of an immutable [LitDict]
    and returns the value paired with the first key structurally equal to
    [k].  A missing key (or a non-dict receiver) yields [LitUnit].

    NOTE on partiality.  [dict_lookup] is the TOTAL projection: it is the
    correct semantics for Pydantic model field access ([field_access]),
    because a well-typed model always carries every declared field, so the
    lookup never misses.  Python subscript [d[k]], by contrast, is PARTIAL:
    a miss must [raise KeyError(k)] (the key value is the exception
    payload).  That partial behaviour is modelled at the expression level
    by [dict_index]'s body, which branches on [dict_has] and emits
    [Raise (LitExn "KeyError" k)] on a miss -- see the IRIS_BUILTINS table.
    [dict_lookup_kvs]'s [LitUnit] on [nil] is therefore only ever reached
    on the hit path (guarded by [dict_has]) or for the total [field_access].

    The projection preserves object identity: [d] is a single [sn_val],
    never flattened, so whole-object operations and nested projections
    compose without loss of semantics. *)
Fixpoint dict_lookup_kvs (kvs : list (sn_val * sn_val)) (k : sn_val) : sn_val :=
  match kvs with
  | nil => LitUnit
  | (k', v') :: rest =>
      if sn_val_eqb k' k then v' else dict_lookup_kvs rest k
  end.

Definition dict_lookup (d k : sn_val) : sn_val :=
  match d with
  | LitDict kvs => dict_lookup_kvs kvs k
  | _ => LitUnit
  end.

(** Membership: does the model carry key [k]?  Drives the KeyError branch
    in [dict_index]: [k in d] is true iff [d[k]] succeeds. *)
Fixpoint dict_has_kvs (kvs : list (sn_val * sn_val)) (k : sn_val) : bool :=
  match kvs with
  | nil => false
  | (k', _) :: rest => if sn_val_eqb k' k then true else dict_has_kvs rest k
  end.


(** Check key membership in any value.  Delegates to the appropriate
    representation based on the value's shape.  Returns a [bool] so
    it composes with [LitBool] directly, avoiding a raw [match]
    that [simpl] leaves irreducible on opaque arguments. *)
Definition dict_has (d : sn_val) (k : sn_val) : bool :=
  match d with
  | LitDict kvs => dict_has_kvs kvs k
  | LitSet vs => List.existsb (fun x => sn_val_eqb x k) vs
  | _ => false
  end.

(** Z-valued field projection: extract the integer value of a string-keyed
    field from a model's [LitDict] representation, returning 0%Z if the
    field is absent or non-integer.  This is the contract-level projection
    -- it returns a bare Z, not an sn_val, so that pre/postconditions can
    use standard Z arithmetic rather than matching on constructors. *)
Definition dict_lookup_Z (m : sn_val) (f : string) : Z :=
  match dict_lookup m (LitString f) with
  | LitInt n => n
  | _ => 0%Z
  end.

Fixpoint dict_set_kvs (kvs : list (sn_val * sn_val)) (k v : sn_val) : list (sn_val * sn_val) :=
  match kvs with
  | nil => (k, v) :: nil
  | (k', v') :: rest =>
      if sn_val_eqb k' k
      then (k, v) :: rest
      else (k', v') :: dict_set_kvs rest k v
  end.

(** [model_field_Z] is an alias for contract-level readability. *)
Definition model_field_Z (m : sn_val) (f : string) : Z := dict_lookup_Z m f.

(** ASCII case mapping via byte-value arithmetic on [Ascii.N_of_ascii].
    Characters outside the A-Z / a-z ranges are left unchanged. *)
Definition ascii_to_lower (c : Ascii.ascii) : Ascii.ascii :=
  let n := Ascii.N_of_ascii c in
  if (65 <=? n)%N && (n <=? 90)%N
  then Ascii.ascii_of_N (n + 32)%N
  else c.

Definition ascii_to_upper (c : Ascii.ascii) : Ascii.ascii :=
  let n := Ascii.N_of_ascii c in
  if (97 <=? n)%N && (n <=? 122)%N
  then Ascii.ascii_of_N (n - 32)%N
  else c.

Fixpoint str_to_lower (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String (ascii_to_lower c) (str_to_lower rest)
  end.

Fixpoint str_to_upper (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String (ascii_to_upper c) (str_to_upper rest)
  end.

(** Check if an ASCII character is a hex digit (0-9, a-f). *)
Definition is_hex_char (c : Ascii.ascii) : bool :=
  let n := Ascii.N_of_ascii c in
  ((48 <=? n)%N && (n <=? 57)%N) || ((97 <=? n)%N && (n <=? 102)%N).

(** Check if every character in a string is a hex digit. *)
Fixpoint str_all_hex (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest => is_hex_char c && str_all_hex rest
  end.

(** * Z to float conversion (Python int → float coercion).

    IEEE 754 double-precision; integers > 2^63-1 lose precision but our
    uint63-based conversion matches [PrimFloat.of_uint63 (of_Z z)] for
    non-negative z and [PrimFloat.opp] for negative z. *)
Definition z2float (z : Z) : float :=
  if Z.ltb z 0
  then PrimFloat.opp (PrimFloat.of_uint63 (of_Z (Z.abs z)))
  else PrimFloat.of_uint63 (of_Z z).

(** Substring containment: true iff [needle] occurs anywhere in [haystack]. *)
Fixpoint string_contains (needle haystack : string) : bool :=
  match haystack with
  | EmptyString => false
  | String _ rest =>
      if String.prefix needle haystack
      then true
      else string_contains needle rest
  end.

(** Total to-lower / to-upper over sn_val: non-strings pass through unchanged. *)
Definition str_to_lower_val (v : sn_val) : sn_val :=
  match v with LitString s => LitString (str_to_lower s) | _ => v end.

Definition str_to_upper_val (v : sn_val) : sn_val :=
  match v with LitString s => LitString (str_to_upper s) | _ => v end.

(** Substring containment over sn_val: false if either arg is non-string. *)
Definition str_contains_val (needle haystack : sn_val) : bool :=
  match needle, haystack with
  | LitString n, LitString h => string_contains n h
  | _, _ => false
  end.

(** Start/end checks over sn_val: false if either arg is non-string. *)
Definition starts_with_val (a p : sn_val) : bool :=
  match a, p with
  | LitString a', LitString p' => String.prefix p' a'
  | _, _ => false
  end.

Definition ends_with_val (a s : sn_val) : bool :=
  match a, s with
  | LitString a', LitString s' =>
      let l1 := String.length a' in
      let l2 := String.length s' in
      if Nat.leb l2 l1
      then String.prefix s' (String.substring (Nat.sub l1 l2) l2 a')
      else false
  | _, _ => false
  end.

(** * Binary operation evaluation (minimal: ints + comparisons). *)
Definition binop_eval (op : binop) (v1 v2 : sn_val) : sn_val :=
  match op with
  (* Construct a KeyError whose payload is the (first) key value, so that
     [Raise (BinOp MkKeyErrOp k _)] raises exactly Python's KeyError(k). *)
  | MkKeyErrOp => LitExn "KeyError" v1
  | TupleOp => LitTuple [v1; v2]
  | InOp => LitBool (dict_has v1 v2)
  | ToLowerOp => str_to_lower_val v1
  | ToUpperOp => str_to_upper_val v1
  | StrContainsOp => LitBool (str_contains_val v1 v2)
  | StartsWithOp => LitBool (starts_with_val v1 v2)
  | EndsWithOp => LitBool (ends_with_val v1 v2)
  (* DictGetIntOp: integer-valued projection that ALWAYS returns LitInt,
     even for non-dict receivers (model_field_Z returns 0).  This
     guarantees [exists z, v = LitInt z /\ ...] is provable by reflexivity
     without needing an is_shape typing hypothesis. *)
  | DictGetIntOp =>
      let f := match v2 with LitString s => s | _ => ""%string end in
      LitInt (model_field_Z v1 f)
  | _ =>
  match v1, v2 with
  (* --- float arithmetic --- *)
  | LitFloat f1, LitFloat f2 =>
      match op with
      | AddOp => LitFloat (PrimFloat.add f1 f2)
      | SubOp => LitFloat (PrimFloat.sub f1 f2)
      | MulOp => LitFloat (PrimFloat.mul f1 f2)
      | DivOp => LitFloat (PrimFloat.div f1 f2)
      | EqOp  => LitBool (PrimFloat.eqb f1 f2)
      | LeOp  => LitBool (PrimFloat.leb f1 f2)
      | LtOp  => LitBool (PrimFloat.ltb f1 f2)
      | GtOp  => LitBool (PrimFloat.ltb f2 f1)
      | GeOp  => LitBool (PrimFloat.leb f2 f1)
      | NeOp  => LitBool (negb (PrimFloat.eqb f1 f2))
      | _ => LitUnit
      end
  (* --- int+float → float (Python coercion) --- *)
  | LitInt n, LitFloat f =>
      match op with
      | AddOp => LitFloat (PrimFloat.add (z2float n) f)
      | SubOp => LitFloat (PrimFloat.sub (z2float n) f)
      | MulOp => LitFloat (PrimFloat.mul (z2float n) f)
      | DivOp => LitFloat (PrimFloat.div (z2float n) f)
      | EqOp  => LitBool (PrimFloat.eqb (z2float n) f)
      | LeOp  => LitBool (PrimFloat.leb (z2float n) f)
      | LtOp  => LitBool (PrimFloat.ltb (z2float n) f)
      | GtOp  => LitBool (PrimFloat.ltb f (z2float n))
      | GeOp  => LitBool (PrimFloat.leb f (z2float n))
      | NeOp  => LitBool (negb (PrimFloat.eqb (z2float n) f))
      | _ => LitUnit
      end
  (* --- float+int → float (Python coercion) --- *)
  | LitFloat f, LitInt n =>
      match op with
      | AddOp => LitFloat (PrimFloat.add f (z2float n))
      | SubOp => LitFloat (PrimFloat.sub f (z2float n))
      | MulOp => LitFloat (PrimFloat.mul f (z2float n))
      | DivOp => LitFloat (PrimFloat.div f (z2float n))
      | EqOp  => LitBool (PrimFloat.eqb f (z2float n))
      | LeOp  => LitBool (PrimFloat.leb f (z2float n))
      | LtOp  => LitBool (PrimFloat.ltb f (z2float n))
      | GtOp  => LitBool (PrimFloat.ltb (z2float n) f)
      | GeOp  => LitBool (PrimFloat.leb (z2float n) f)
      | NeOp  => LitBool (negb (PrimFloat.eqb f (z2float n)))
      | _ => LitUnit
      end
  | LitInt n1, LitInt n2 =>
      match op with
      | AddOp => LitInt (n1 + n2)
      | SubOp => LitInt (n1 - n2)
      | MulOp => LitInt (n1 * n2)
      | EqOp  => LitBool (Z.eqb n1 n2)
      | LeOp  => LitBool (Z.leb n1 n2)
      | LtOp  => LitBool (Z.ltb n1 n2)
      | GtOp  => LitBool (Z.ltb n2 n1)
      | GeOp  => LitBool (Z.leb n2 n1)
      | NeOp  => LitBool (negb (Z.eqb n1 n2))
      | ModOp => LitInt (Z.rem n1 n2)
      | _ => LitUnit
      end
  | LitBool b1, LitBool b2 =>
      match op with
      | AndOp => LitBool (b1 && b2)
      | OrOp  => LitBool (b1 || b2)
       | EqOp  => LitBool (Bool.eqb b1 b2)
       | _ => LitUnit
       end
  | LitList vs, v =>
      match op with
      | AppendOp => LitList (vs ++ [v])
      | LengthOp => LitInt (Z.of_nat (List.length vs))
      | _ => LitUnit
      end
  | LitDict kvs, k =>
      match op with
      | DictGetOp => dict_lookup_kvs kvs k
      | DictSetOp => match k with LitTuple (key :: val :: nil) => LitDict (dict_set_kvs kvs key val) | _ => LitUnit end
      | InOp => LitBool (dict_has_kvs kvs k)
      | LenOp | LengthOp => LitInt (Z.of_nat (List.length kvs))
      | _ => LitUnit
      end
  | LitString s1, LitString s2 =>
      match op with
      | AddOp => LitString (String.append s1 s2)
      | EqOp  => LitBool (String.eqb s1 s2)
      | NeOp  => LitBool (negb (String.eqb s1 s2))
      | LenOp => LitInt (Z.of_nat (String.length s1))
      | StartsWithOp => LitBool (String.prefix s2 s1)
      | EndsWithOp =>
          let l1 := String.length s1 in
          let l2 := String.length s2 in
          if Nat.leb l2 l1
          then LitBool (String.prefix s2
                          (String.substring (Nat.sub l1 l2) l2 s1))
          else LitBool false
      | StrContainsOp => LitBool (string_contains s2 s1)
      | _ => LitUnit
      end
  | LitString s, v =>
      match op with
      | LenOp => LitInt (Z.of_nat (String.length s))
      | StrIndexOp =>
          match v with
          | LitInt n =>
              LitString (String.substring (Z.to_nat n) 1 s)
          | _ => LitUnit
          end
      | ToLowerOp => LitString (str_to_lower s)
      | ToUpperOp => LitString (str_to_upper s)
      | _ => LitUnit
      end
  (* --- set operations --- *)
  | LitSet vs1, LitSet vs2 =>
      match op with
      | UnionOp => LitSet (vs1 ++ vs2)
      | InterOp => LitSet (List.filter (fun x => List.existsb (fun y => sn_val_eqb x y) vs2) vs1)
      | _ => LitUnit
      end
  | LitSet vs, v =>
      match op with
      | InOp => LitBool (List.existsb (fun x => sn_val_eqb x v) vs)
      | SetAddOp => LitSet (v :: vs)
      | _ => LitUnit
      end
  | _, _ => LitUnit
  end
  end.

(** ** Soundness of the structural field/dict projection.

    These lemmas pin the semantics of [DictGetOp]: it is the structural
    [dict_lookup] over the model's key-value list, and it distinguishes
    distinct fields rather than collapsing them (the failure mode of naive
    flattening).  They guard against regressing [field_access]/[dict_index]
    back to a mock. *)

Lemma dict_get_eval :
  forall kvs k, binop_eval DictGetOp (LitDict kvs) k = dict_lookup_kvs kvs k.
Proof. reflexivity. Qed.

Lemma dict_get_hit :
  forall kvs k v, binop_eval DictGetOp (LitDict ((k, v) :: kvs)) k
                  = (if sn_val_eqb k k then v else dict_lookup_kvs kvs k).
Proof. reflexivity. Qed.

Lemma dict_get_string_hit :
  forall kvs s v,
    binop_eval DictGetOp (LitDict ((LitString s, v) :: kvs)) (LitString s) = v.
Proof.
  intros. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

Lemma dict_get_string_miss :
  forall kvs s s' v, s <> s' ->
    binop_eval DictGetOp (LitDict ((LitString s, v) :: kvs)) (LitString s')
      = dict_lookup_kvs kvs (LitString s').
Proof.
  intros kvs s s' v Hne. simpl.
  destruct (String.eqb s s') eqn:E.
  - apply String.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

(** Distinct string fields project distinct values: identity is preserved,
    not flattened away. *)
Lemma dict_get_distinct_fields :
  forall a b va vb, a <> b ->
    let m := LitDict ((LitString a, va) :: (LitString b, vb) :: nil) in
    binop_eval DictGetOp m (LitString a) = va /\
    binop_eval DictGetOp m (LitString b) = vb.
Proof.
  intros a b va vb Hne. simpl.
  rewrite String.eqb_refl. split; [reflexivity|].
  destruct (String.eqb a b) eqn:E.
  - apply String.eqb_eq in E. contradiction.
  - rewrite String.eqb_refl. reflexivity.
Qed.

(** ** KeyError semantics for subscript [d[k]].

    [InOp] decides membership; the [dict_index] body branches on it and
    raises [KeyError k] on a miss.  These lemmas pin both arms. *)

Lemma dict_in_eval :
  forall kvs k, binop_eval InOp (LitDict kvs) k = LitBool (dict_has_kvs kvs k).
Proof. reflexivity. Qed.

(** A present key reports membership and projects to its value (success
    arm of [d[k]]). *)
Lemma dict_in_hit :
  forall kvs s v,
    dict_has_kvs ((LitString s, v) :: kvs) (LitString s) = true.
Proof. intros. simpl. rewrite String.eqb_refl. reflexivity. Qed.

(** An absent key reports non-membership: the [dict_index] body then takes
    the [Raise (LitExn "KeyError" k)] branch.  The exception payload IS the
    looked-up key [k], matching Python's [KeyError(k)]. *)
Lemma dict_in_miss_nil :
  forall k, dict_has_kvs nil k = false.
Proof. reflexivity. Qed.

Lemma dict_has_lookup_consistent :
  forall kvs k, dict_has_kvs kvs k = false -> dict_lookup_kvs kvs k = LitUnit.
Proof.
  induction kvs as [|[k' v'] rest IH]; intros k H.
  - reflexivity.
  - simpl in *. destruct (sn_val_eqb k' k).
    + discriminate H.
    + apply IH, H.
Qed.

(** The KeyError raised on a miss carries the looked-up key as its payload,
    exactly like Python's [KeyError(k)].  [Raise (BinOp MkKeyErrOp k _)]
    therefore evaluates to the terminal [RExn "KeyError" k]. *)
Lemma mk_key_err_payload :
  forall k junk, binop_eval MkKeyErrOp k junk = LitExn "KeyError" k.
Proof. reflexivity. Qed.

(** The integer-valued field projection [DictGetIntOp] unconditionally
    returns [LitInt (model_field_Z m f)], even for non-dict receivers
    (where [model_field_Z] returns 0%Z).  This guarantees the
    postcondition existential [exists z, v = LitInt z /\ ...] is
    provable by reflexivity without an [is_shape] typing hypothesis. *)
Lemma dict_get_int_eval :
  forall m s,
    binop_eval DictGetIntOp m (LitString s) = LitInt (model_field_Z m s).
Proof. reflexivity. Qed.

(** * Function context (opaque specs + transparent defs). *)
Inductive fun_entry :=
  | FunSpec (pre : list sn_val -> Prop) (post : list sn_val -> sn_val -> Prop)
  | FunSpecS (pre : sn_state -> list sn_val -> Prop)
             (post : sn_state -> list sn_val -> Result -> cell_updates -> Prop)
  | FunDef (params : list string) (body : sn_expr).

Class FunCtx := {
  fun_entries : string -> option fun_entry;
  fun_specs_total : forall f pre post vs,
    fun_entries f = Some (FunSpec pre post) ->
    pre vs -> exists v, post vs v;
  fun_specsS_total : forall f pre post vs sigma,
    fun_entries f = Some (FunSpecS pre post) ->
    pre sigma vs ->
    exists r ups, post sigma vs r ups /\ updates_dom_in sigma ups;
}.

(** * Pure steps. *)
Inductive pure_step : sn_expr -> sn_expr -> Prop :=
  | PureLet v x e2 : pure_step (Let x (Val v) e2) (subst x v e2)
  | PureBinOp op v1 v2 :
      pure_step (BinOp op (Val v1) (Val v2)) (Val (binop_eval op v1 v2))
  | PureIfTrue e1 e2 : pure_step (If (Val (LitBool true)) e1 e2) e1
  | PureIfFalse e1 e2 : pure_step (If (Val (LitBool false)) e1 e2) e2
  (* Try, normal: body is a value, handler skipped *)
  | PureTryVal v x h : pure_step (Try (Val v) x h) (Val v)
  (* Try, exception: body raised, run handler with x bound to the exn object *)
  | PureTryCatch ev x h :
      pure_step (Try (Raise (Val ev)) x h) (subst x ev h)
  (* Raise unwinding through a neutral context item *)
  | PureRaiseUnwind Ki v :
      neutral Ki = true ->
      pure_step (fill_item Ki (Raise (Val v))) (Raise (Val v))
  (* While unfolds to a guarded body-then-loop *)
  | PureWhile e1 e2 :
      pure_step (While e1 e2)
                (If e1 (Let "_" e2 (While e1 e2)) (Val LitUnit))
  (* For over an empty list terminates *)
  | PureForNil x body :
      pure_step (For x (Val (LitList [])) body) (Val LitUnit)
  (* For over a cons peels the head: bind it, then recurse on the tail *)
  | PureForCons x v vs body :
      pure_step (For x (Val (LitList (v :: vs))) body)
                (Let "_" (subst x v body) (For x (Val (LitList vs)) body)).

(** A pure redex is never a value. *)
Lemma to_val_pure_step x x' : pure_step x x' -> to_val x = None.
Proof.
  intros H; inversion H; subst; simpl; auto.
  destruct Ki; simpl; reflexivity.
Qed.

(** Map value-arguments-to-expressions injection helper. *)
Lemma map_Val_inj (vs1 vs2 : list sn_val) :
  map Val vs1 = map Val vs2 -> vs1 = vs2.
Proof.
  revert vs2. induction vs1 as [|v1 vs1 IH]; intros [|v2 vs2] H;
    simpl in H; try discriminate.
  - reflexivity.
  - injection H as Hv Hvs. f_equal; [exact Hv | apply IH, Hvs].
Qed.

(** * Head steps, prim_step, and the Iris language instance.
    Wrapped in a section with [Context {FC : FunCtx}] so the call
    head steps use the ambient FC. *)
Section with_fun_ctx.
Context `{FC : FunCtx}.

Inductive head_step : sn_expr -> sn_state -> sn_expr -> sn_state -> list sn_expr -> Prop :=
  | HeadLoad l v sigma :
      sigma !! l = Some v ->
      head_step (Load (Val (LitLoc l))) sigma (Val v) sigma []
  | HeadStore l v sigma :
      is_Some (sigma !! l) ->
      head_step (Store (Val (LitLoc l)) (Val v)) sigma
                (Val LitUnit) (<[l:=v]> sigma) []
  | HeadAlloc v sigma l :
      sigma !! l = None ->
      head_step (Alloc (Val v)) sigma (Val (LitLoc l)) (<[l:=v]> sigma) []
  | HeadCallSpec : forall (f : string) (vs : list sn_val) (sigma : sn_state)
      (pre : list sn_val -> Prop) (post : list sn_val -> sn_val -> Prop) (v : sn_val),
      fun_entries f = Some (FunSpec pre post) ->
      pre vs ->
      post vs v ->
      head_step (Call f (map Val vs)) sigma (Val v) sigma []
  | HeadCallSpecS : forall (f : string) (vs : list sn_val) (sigma : sn_state)
      (pre : sn_state -> list sn_val -> Prop)
      (post : sn_state -> list sn_val -> Result -> cell_updates -> Prop)
      (r : Result) (ups : cell_updates),
      fun_entries f = Some (FunSpecS pre post) ->
      pre sigma vs ->
      post sigma vs r ups ->
      updates_dom_in sigma ups ->
      head_step (Call f (map Val vs)) sigma
                (expr_of_result r) (apply_updates sigma ups) []
  | HeadCallUnfold : forall (f : string) (vs : list sn_val) (sigma : sn_state)
      (params : list string) (body : sn_expr),
      fun_entries f = Some (FunDef params body) ->
      length vs = length params ->
      head_step (Call f (map Val vs)) sigma (subst_list params vs body) sigma [].

(** A head redex is never a value. *)
Lemma to_val_head_step x sigma x' sigma' efs :
  head_step x sigma x' sigma' efs -> to_val x = None.
Proof. intros H; inversion H; subst; simpl; auto. Qed.

(** * Primitive step: decompose into an evaluation context + a redex. *)
Definition observation : Type := unit.

Inductive prim_step : sn_expr -> sn_state -> list observation -> sn_expr -> sn_state -> list sn_expr -> Prop :=
  | PrimPureStep K x sigma x' :
      pure_step x x' ->
      prim_step (fill_K K x) sigma [] (fill_K K x') sigma []
  | PrimHeadStep K x sigma x' sigma' efs :
      head_step x sigma x' sigma' efs ->
      prim_step (fill_K K x) sigma [] (fill_K K x') sigma' efs.

Definition reducible (e : sn_expr) (sigma : sn_state) : Prop :=
  exists kappa e' sigma' efs, prim_step e sigma kappa e' sigma' efs.

(** * GATE LEMMA 1: [Raise (Val v)] is a stuck terminal expression.

    An uncaught raise reduces to nothing: it sits in evaluation position
    as the program's exceptional result.  This is the foundational
    encoding -- [Raise (Val v)] is observable but irreducible. *)
Lemma raise_val_irreducible v sigma : ~ reducible (Raise (Val v)) sigma.
Proof.
  intros (kappa & e2 & sigma2 & efs & Hstep).
  inversion Hstep as [K x sg x2 Hpure Heq | K x sg x2 sg2 efs2 Hhead Heq]; subst.
  2: { (* PrimHeadStep *)
       destruct K as [|Ki K2]; simpl in Heq;
       [ subst x; inversion Hhead
       | destruct Ki; simpl in Heq; try discriminate Heq;
         injection Heq as Hin; apply fill_K_val in Hin as [-> ->]; inversion Hhead ]. }
  (* PrimPureStep *)
  destruct K as [|Ki K2]; simpl in Heq.
  2: { destruct Ki; simpl in Heq; try discriminate Heq.
       injection Heq as Hin. apply fill_K_val in Hin as [-> ->].
       apply to_val_pure_step in Hpure. simpl in Hpure. discriminate. }
  subst x.
  inversion Hpure; subst.
  destruct Ki; simpl in H; try discriminate H.
Qed.

End with_fun_ctx.
