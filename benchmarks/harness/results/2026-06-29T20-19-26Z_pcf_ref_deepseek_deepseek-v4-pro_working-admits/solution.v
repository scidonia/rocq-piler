From Stdlib Require Import Arith List Lia.
Import ListNotations.

(** * PCF + References: Type Preservation — Benchmark *)

Inductive ty : Type :=
  | TyNat | TyBool | TyArrow : ty -> ty -> ty | TyRef : ty -> ty.

Inductive tm : Type :=
  | Var : nat -> tm | Num : nat -> tm | BOOL : bool -> tm
  | Succ : tm -> tm | Pred : tm -> tm | IsZero : tm -> tm
  | If : tm -> tm -> tm -> tm
  | Lam : ty -> tm -> tm | App : tm -> tm -> tm | Fix : tm -> tm
  | Ref : tm -> tm | Deref : tm -> tm | Assign : tm -> tm -> tm | Loc : nat -> tm.

Definition ctx := list ty.
Definition store_ty := list ty.

Inductive has_type : ctx -> store_ty -> tm -> ty -> Prop :=
  | T_Var : forall G S x T, nth_error G x = Some T -> has_type G S (Var x) T
  | T_Num : forall G S n, has_type G S (Num n) TyNat
  | T_Bool : forall G S b, has_type G S (BOOL b) TyBool
  | T_Succ : forall G S t, has_type G S t TyNat -> has_type G S (Succ t) TyNat
  | T_Pred : forall G S t, has_type G S t TyNat -> has_type G S (Pred t) TyNat
  | T_IsZero : forall G S t, has_type G S t TyNat -> has_type G S (IsZero t) TyBool
  | T_If : forall G S t1 t2 t3 T, has_type G S t1 TyBool -> has_type G S t2 T -> has_type G S t3 T -> has_type G S (If t1 t2 t3) T
  | T_Lam : forall G S T1 T2 t, has_type (T1 :: G) S t T2 -> has_type G S (Lam T1 t) (TyArrow T1 T2)
  | T_App : forall G S t1 t2 T1 T2, has_type G S t1 (TyArrow T1 T2) -> has_type G S t2 T1 -> has_type G S (App t1 t2) T2
  | T_Fix : forall G S t T, has_type (T :: G) S t T -> has_type G S (Fix t) T
  | T_Ref : forall G S t T, has_type G S t T -> has_type G S (Ref t) (TyRef T)
  | T_Deref : forall G S t T, has_type G S t (TyRef T) -> has_type G S (Deref t) T
  | T_Assign : forall G S t1 t2 T, has_type G S t1 (TyRef T) -> has_type G S t2 T -> has_type G S (Assign t1 t2) TyNat
  | T_Loc : forall G S l T, nth_error S l = Some T -> has_type G S (Loc l) (TyRef T).

Inductive value : tm -> Prop :=
  | V_Num : forall n, value (Num n)
  | V_Bool : forall b, value (BOOL b)
  | V_Lam : forall T t, value (Lam T t)
  | V_Loc : forall l, value (Loc l).

Fixpoint shift_at (d : nat) (t : tm) : tm :=
  match t with
  | Var x => if x <? d then Var x else Var (x + 1)
  | Num n => Num n | BOOL b => BOOL b
  | Succ t1 => Succ (shift_at d t1) | Pred t1 => Pred (shift_at d t1)
  | IsZero t1 => IsZero (shift_at d t1)
  | If t1 t2 t3 => If (shift_at d t1) (shift_at d t2) (shift_at d t3)
  | Lam T t1 => Lam T (shift_at (S d) t1)
  | App t1 t2 => App (shift_at d t1) (shift_at d t2)
  | Fix t1 => Fix (shift_at (S d) t1)
  | Ref t1 => Ref (shift_at d t1) | Deref t1 => Deref (shift_at d t1)
  | Assign t1 t2 => Assign (shift_at d t1) (shift_at d t2)
  | Loc l => Loc l
  end.

Definition shift (t : tm) : tm := shift_at 0 t.

Fixpoint subst (j : nat) (s t : tm) : tm :=
  match t with
  | Var x => if Nat.eqb x j then s else Var x
  | Num n => Num n | BOOL b => BOOL b
  | Succ t1 => Succ (subst j s t1) | Pred t1 => Pred (subst j s t1)
  | IsZero t1 => IsZero (subst j s t1)
  | If t1 t2 t3 => If (subst j s t1) (subst j s t2) (subst j s t3)
  | Lam T t1 => Lam T (subst (S j) (shift s) t1)
  | App t1 t2 => App (subst j s t1) (subst j s t2)
  | Fix t1 => Fix (subst (S j) (shift s) t1)
  | Ref t1 => Ref (subst j s t1) | Deref t1 => Deref (subst j s t1)
  | Assign t1 t2 => Assign (subst j s t1) (subst j s t2)
  | Loc l => Loc l
  end.

Definition heap := list (nat * tm).

Fixpoint heap_lookup (l : nat) (mu : heap) : option tm :=
  match mu with
  | [] => None
  | (l', v) :: mu' => if Nat.eqb l l' then Some v else heap_lookup l mu'
  end.

Fixpoint heap_update (l : nat) (v : tm) (mu : heap) : heap :=
  match mu with
  | [] => []
  | (l', v') :: mu' => if Nat.eqb l l' then (l, v) :: mu'
                        else (l', v') :: heap_update l v mu'
  end.

Inductive heap_ok : heap -> store_ty -> Prop :=
  | heap_empty : forall S, heap_ok [] S
  | heap_cons : forall l v mu S T, heap_ok mu S -> has_type [] S v T -> nth_error S l = Some T -> heap_ok ((l, v) :: mu) S.

Inductive step : tm -> heap -> tm -> heap -> Prop :=
  | S_Succ : forall t mu t' mu', step t mu t' mu' -> step (Succ t) mu (Succ t') mu'
  | S_PredZero : forall mu, step (Pred (Num 0)) mu (Num 0) mu
  | S_PredSucc : forall n mu, step (Pred (Num (S n))) mu (Num n) mu
  | S_Pred : forall t mu t' mu', step t mu t' mu' -> step (Pred t) mu (Pred t') mu'
  | S_IsZeroZero : forall mu, step (IsZero (Num 0)) mu (BOOL true) mu
  | S_IsZeroSucc : forall n mu, step (IsZero (Num (S n))) mu (BOOL false) mu
  | S_IsZero : forall t mu t' mu', step t mu t' mu' -> step (IsZero t) mu (IsZero t') mu'
  | S_IfTrue : forall t1 t2 mu, step (If (BOOL true) t1 t2) mu t1 mu
  | S_IfFalse : forall t1 t2 mu, step (If (BOOL false) t1 t2) mu t2 mu
  | S_If : forall t1 mu t1' mu' t2 t3, step t1 mu t1' mu' -> step (If t1 t2 t3) mu (If t1' t2 t3) mu'
  | S_App1 : forall t1 mu t1' mu' t2, step t1 mu t1' mu' -> step (App t1 t2) mu (App t1' t2) mu'
  | S_App2 : forall v1 t2 mu t2' mu', value v1 -> step t2 mu t2' mu' -> step (App v1 t2) mu (App v1 t2') mu'
  | S_AppAbs : forall T t1 v2 mu, value v2 -> step (App (Lam T t1) v2) mu (subst 0 v2 t1) mu
  | S_Fix : forall t mu, step (Fix t) mu (subst 0 (Fix t) t) mu
  | S_Ref : forall t mu t' mu', step t mu t' mu' -> step (Ref t) mu (Ref t') mu'
  | S_RefV : forall v mu, value v -> step (Ref v) mu (Loc (length mu)) ((length mu, v) :: mu)
  | S_Deref : forall t mu t' mu', step t mu t' mu' -> step (Deref t) mu (Deref t') mu'
  | S_DerefLoc : forall l mu v, heap_lookup l mu = Some v -> step (Deref (Loc l)) mu v mu
  | S_Assign1 : forall t1 mu t1' mu' t2, step t1 mu t1' mu' -> step (Assign t1 t2) mu (Assign t1' t2) mu'
  | S_Assign2 : forall l t2 mu t2' mu', step t2 mu t2' mu' -> step (Assign (Loc l) t2) mu (Assign (Loc l) t2') mu'
  | S_AssignV : forall l v mu, value v -> step (Assign (Loc l) v) mu (Num 0) (heap_update l v mu).

Definition extends (S' S : store_ty) : Prop := exists S2, S' = S ++ S2.

Lemma extends_length : forall S' S, extends S' S -> length S <= length S'.
Proof.
  intros S' S [S2 ->]. rewrite app_length. lia.
Qed.

Lemma has_type_weaken_store : forall G S t T, has_type G S t T -> forall S', extends S' S -> has_type G S' t T.
Proof.
  induction 1 as [G S x T Hx | | | G S t Ht IH | G S t Ht IH | G S t Ht IH
                  | G S t1 t2 t3 T Ht1 IH1 Ht2 IH2 Ht3 IH3
                  | G S T1 T2 t Ht IH
                  | G S t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
                  | G S t T Ht IH
                  | G S t T Ht IH
                  | G S t T Ht IH
                  | G S t1 t2 T Ht1 IH1 Ht2 IH2
                  | G S l T Hl];
    intros S' Hext.
  - apply T_Var; auto.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ; auto.
  - apply T_Pred; auto.
  - apply T_IsZero; auto.
  - apply T_If; auto.
  - apply T_Lam. apply IH. exact Hext.
  - eapply T_App; eauto.
  - apply T_Fix. apply IH. exact Hext.
  - apply T_Ref; auto.
  - apply T_Deref; auto.
  - eapply T_Assign; eauto.
  - eapply T_Loc.
    destruct Hext as [S2 ->].
    assert (Hlen : l < length S). {
      apply nth_error_Some. rewrite Hl. discriminate.
    }
    erewrite nth_error_app1; eauto.
Qed.

Lemma heap_ok_extends : forall mu S, heap_ok mu S -> forall S', extends S' S -> heap_ok mu S'.
Proof.
  induction 1 as [S | l v mu S T Hok IH Hty Hl]; intros S' Hext.
  - apply heap_empty.
  - apply heap_cons with (T := T).
    + apply IH. exact Hext.
    + apply has_type_weaken_store with (S := S); auto.
    + destruct Hext as [S2 ->].
      assert (Hlen : l < length S). {
        apply nth_error_Some. rewrite Hl. discriminate.
      }
      erewrite nth_error_app1; eauto.
Qed.

Lemma heap_ok_lookup : forall mu S l v,
  heap_ok mu S ->
  heap_lookup l mu = Some v ->
  exists T, nth_error S l = Some T /\ has_type [] S v T.
Proof.
  induction mu as [| [l' v'] mu' IH]; intros S l v Hok Hlook; simpl in *.
  - discriminate.
  - destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst l'.
      inversion Hlook. subst v'.
      inversion Hok as [| ? ? ? ? T' ? ? Hl']; subst.
      exists T'. split; auto.
    + apply IH; auto.
      inversion Hok; subst; auto.
Qed.

Lemma heap_ok_update : forall mu S l v T,
  heap_ok mu S ->
  nth_error S l = Some T ->
  has_type [] S v T ->
  heap_ok (heap_update l v mu) S.
Proof.
  induction mu as [| [l' v'] mu' IH]; intros S l v T Hok Hl Hty; simpl.
  - apply heap_empty.
  - inversion Hok as [| ? ? ? ? T' Hok' Hty' Hl']; subst.
    destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst l'.
      rewrite Hl in Hl'. inversion Hl'. subst T'.
      apply heap_cons with (T := T); auto.
    + apply heap_cons with (T := T'); [apply (IH S l v T); auto|auto|auto].
Qed.

Lemma shift_at_typing : forall G S t T,
  has_type G S t T ->
  forall d U, has_type (firstn d G ++ U :: skipn d G) S (shift_at d t) T.
Proof.
  induction 1 as [G S x T Hx | | | G S t Ht IH | G S t Ht IH | G S t Ht IH
                  | G S t1 t2 t3 T Ht1 IH1 Ht2 IH2 Ht3 IH3
                  | G S T1 T2 t Ht IH
                  | G S t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
                  | G S t T Ht IH
                  | G S t T Ht IH
                  | G S t T Ht IH
                  | G S t1 t2 T Ht1 IH1 Ht2 IH2
                  | G S l T Hl];
    intros d U; simpl.
  - simpl.
    destruct (x <? d) eqn:Hlt.
    + apply T_Var.
      rewrite nth_error_app.
      rewrite (proj2 (Nat.ltb_lt x (length (firstn d G)))).
      * rewrite nth_error_firstn. rewrite Hlt. exact Hx.
      * rewrite firstn_length.
        apply Nat.min_glb_lt.
        -- apply Nat.ltb_lt in Hlt. exact Hlt.
        -- apply nth_error_Some. rewrite Hx. discriminate.
    + apply T_Var.
      rewrite nth_error_app.
      assert (Hx_len : x < length G) by
        (apply nth_error_Some; rewrite Hx; discriminate).
      assert (Hge : length (firstn d G) <= x + 1). {
        rewrite firstn_length.
        apply Nat.le_trans with d; [apply Nat.le_min_l|].
        apply Nat.ltb_ge in Hlt. lia.
      }
      assert (Hxge : Nat.min d (length G) <= x). {
        apply Nat.le_trans with d; [apply Nat.le_min_l|].
        apply Nat.ltb_ge in Hlt. exact Hlt.
      }
      rewrite (proj2 (Nat.ltb_ge (x + 1) (length (firstn d G))) Hge).
      rewrite firstn_length.
      replace ((x + 1) - Nat.min d (length G)) with (Datatypes.S (x - Nat.min d (length G))) by lia.
      simpl.
      rewrite nth_error_skipn.
      rewrite <- Hx. f_equal. lia.
  - apply T_Num.
  - apply T_Bool.
  - apply T_Succ; auto.
  - apply T_Pred; auto.
  - apply T_IsZero; auto.
  - apply T_If; auto.
  - apply T_Lam. apply (IH (Datatypes.S d) U).
  - eapply T_App; eauto.
  - apply T_Fix. apply (IH (Datatypes.S d) U).
  - apply T_Ref; auto.
  - apply T_Deref; auto.
  - eapply T_Assign; eauto.
  - apply T_Loc. simpl. exact Hl.
Qed.

Lemma subst_typing_aux : forall G S body T U,
  has_type G S body T ->
  forall G1 s, G = G1 ++ U :: [] ->
    has_type (G1 ++ []) S s U ->
    has_type (G1 ++ []) S (subst (length G1) s body) T.
Proof.
  refine (fix aux G S body T U (Ht : has_type G S body T) {struct Ht} :
    forall G1 s, G = G1 ++ U :: [] ->
      has_type (G1 ++ []) S s U ->
      has_type (G1 ++ []) S (subst (length G1) s body) T :=
    match Ht with
    | @T_Var G' S' x T' Hx => _
    | @T_Num G' S' n => _
    | @T_Bool G' S' b => _
    | @T_Succ G' S' t' Ht' => _
    | @T_Pred G' S' t' Ht' => _
    | @T_IsZero G' S' t' Ht' => _
    | @T_If G' S' t1 t2 t3 T' H1 H2 H3 => _
    | @T_Lam G' S' T1 T2 t' Ht' => _
    | @T_App G' S' t1 t2 T1 T2 H1 H2 => _
    | @T_Fix G' S' t' T' Ht' => _
    | @T_Ref G' S' t' T' Ht' => _
    | @T_Deref G' S' t' T' Ht' => _
    | @T_Assign G' S' t1 t2 T' H1 H2 => _
    | @T_Loc G' S' l T' Hl => _
    end); clear aux; intros G1 s HGeq Hs; subst G'; simpl.
  - (* T_Var *)
    simpl in Hx.
    destruct (Nat.eqb x (length G1)) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst x.
      rewrite (@nth_error_app2 ty G1 (U :: []) (length G1)) in Hx; [|apply Nat.le_refl].
      rewrite Nat.sub_diag in Hx. simpl in Hx. inversion Hx. subst.
      exact Hs.
    + apply T_Var.
      rewrite (@nth_error_app ty G1 [] x).
      destruct (x <? length G1) eqn:Hlt.
      * rewrite (@nth_error_app ty G1 (U :: []) x) in Hx.
        rewrite Hlt in Hx. simpl in Hx.
        destruct (x <? length G1); [exact Hx|discriminate Hlt].
      * rewrite (@nth_error_app ty G1 (U :: []) x) in Hx.
        rewrite Hlt in Hx.
        destruct (x - length G1) eqn:Hd.
        -- apply Nat.ltb_ge in Hlt. apply Nat.eqb_neq in Heq. exfalso. apply Heq. lia.
         -- assert (Heqsub: x - length G1 = Datatypes.S n) by (rewrite Hd; reflexivity).
            rewrite Heqsub in Hx. simpl in Hx. inversion Hx.
  - (* T_Num *) apply T_Num.
  - (* T_Bool *) apply T_Bool.
  - (* T_Succ *) apply T_Succ. apply aux with (Ht := Ht'); auto.
  - (* T_Pred *) apply T_Pred. apply aux with (Ht := Ht'); auto.
  - (* T_IsZero *) apply T_IsZero. apply aux with (Ht := Ht'); auto.
  - (* T_If *)
    apply T_If.
    + apply aux with (Ht := H1); auto.
    + apply aux with (Ht := H2); auto.
    + apply aux with (Ht := H3); auto.
  - (* T_Lam *)
    apply T_Lam.
    apply aux with (Ht := Ht') (G1 := T1 :: G1) (s := shift s).
    + rewrite <- app_comm_cons. reflexivity.
    + change (shift s) with (shift_at 0 s).
      apply shift_at_typing with (d := 0) (U := T1) (G := G1 ++ []).
      simpl firstn. simpl skipn. exact Hs.
  - (* T_App *)
    eapply T_App.
    + apply aux with (Ht := H1); auto.
    + apply aux with (Ht := H2); auto.
  - (* T_Fix *)
    apply T_Fix.
    apply aux with (Ht := Ht') (G1 := T' :: G1) (s := shift s).
    + rewrite <- app_comm_cons. reflexivity.
    + change (shift s) with (shift_at 0 s).
      apply shift_at_typing with (d := 0) (U := T') (G := G1 ++ []).
      simpl firstn. simpl skipn. exact Hs.
  - (* T_Ref *) apply T_Ref. apply aux with (Ht := Ht'); auto.
  - (* T_Deref *) apply T_Deref. apply aux with (Ht := Ht'); auto.
  - (* T_Assign *)
    eapply T_Assign.
    + apply aux with (Ht := H1); auto.
    + apply aux with (Ht := H2); auto.
  - (* T_Loc *) apply T_Loc. exact Hl.
Qed.

Lemma subst0_typing : forall S body T U s,
  has_type (U :: []) S body T ->
  has_type [] S s U ->
  has_type [] S (subst 0 s body) T.
Proof.
  intros S body T U s Ht Hs.
  apply subst_typing_aux with (G1 := []) (Ht := Ht); auto.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem preservation :
  forall t mu t' mu' T S,
    has_type [] S t T ->
    step t mu t' mu' ->
    heap_ok mu S ->
    length mu >= length S ->
    exists S',
      extends S' S /\
      heap_ok mu' S' /\
      has_type [] S' t' T.
Proof.
  intros t mu t' mu' T S Ht Hstep Hok Hlen. revert T Ht. induction Hstep; intros T0 Ht; inversion Ht; subst; clear Ht.
  - specialize (IHHstep Hok Hlen). edestruct (IHHstep TyNat H2) as [S' [Hext [Hok' Hty]]].
    exists S'; split; auto; split; auto. apply T_Succ; auto.
  - exists S; split; [exists []; symmetry; apply app_nil_r|]; split; [auto|apply T_Num].
  - exists S; split; [exists []; symmetry; apply app_nil_r|]; split; [auto|apply T_Num].
  - specialize (IHHstep Hok Hlen). edestruct (IHHstep TyNat H2) as [S' [Hext [Hok' Hty]]].
    exists S'; split; auto; split; auto. apply T_Pred; auto.
  - exists S; split; [exists []; symmetry; apply app_nil_r|]; split; [auto|apply T_Bool].
  - exists S; split; [exists []; symmetry; apply app_nil_r|]; split; [auto|apply T_Bool].
  - specialize (IHHstep Hok Hlen). edestruct (IHHstep TyNat H2) as [S' [Hext [Hok' Hty]]].
    exists S'; split; auto; split; auto. apply T_IsZero; auto.
  - exists S; split; [exists []; symmetry; apply app_nil_r|]; split; [auto|auto].
  - exists S; split; [exists []; symmetry; apply app_nil_r|]; split; [auto|auto].
  - specialize (IHHstep Hok Hlen). edestruct (IHHstep TyBool H4) as [S' [Hext [Hok' Hty]]].
    exists S'; split; auto; split; auto.
    eapply T_If; [apply Hty| eapply has_type_weaken_store; eauto| eapply has_type_weaken_store; eauto].
  - specialize (IHHstep Hok Hlen). edestruct (IHHstep (TyArrow T1 T0) H3) as [S' [Hext [Hok' Hty]]].
    exists S'; split; auto; split; auto.
    eapply T_App; [apply Hty| eapply has_type_weaken_store; eauto].
  - specialize (IHHstep Hok Hlen). edestruct (IHHstep T1 H6) as [S' [Hext [Hok' Hty]]].
    exists S'; split; auto; split; auto.
    eapply T_App; [eapply has_type_weaken_store; eauto| apply Hty].
  - exists S; split; [exists []; symmetry; apply app_nil_r|]; split; [auto|].
    inversion H4; subst. eapply subst0_typing; eauto.
  - exists S; split; [exists []; symmetry; apply app_nil_r|]; split; [auto|].
    eapply subst0_typing; [exact H2|]. apply T_Fix; exact H2.
  - specialize (IHHstep Hok Hlen). edestruct (IHHstep T H2) as [S' [Hext [Hok' Hty]]].
    exists S'; split; auto; split; auto. apply T_Ref; auto.
  - set (S' := S ++ repeat TyNat (length mu - length S) ++ [T]).
    exists S'.
    split; [exists (repeat TyNat (length mu - length S) ++ [T]); subst S'; reflexivity|].
    split.
    + apply heap_cons with (T := T); auto.
      * apply heap_ok_extends with (S := S); auto.
        subst S'. exists (repeat TyNat (length mu - length S) ++ [T]). reflexivity.
      * apply has_type_weaken_store with (S := S); auto.
        subst S'. exists (repeat TyNat (length mu - length S) ++ [T]). reflexivity.
      * subst S'.
        rewrite (@nth_error_app2 ty S (repeat TyNat (length mu - length S) ++ [T]) (length mu)); [|auto with zarith].
        rewrite (@nth_error_app2 ty (repeat TyNat (length mu - length S)) [T] (length mu - length S)); [|rewrite repeat_length; apply Nat.le_refl].
        replace (length mu - length S - length (repeat TyNat (length mu - length S))) with 0
          by (rewrite repeat_length; lia).
        simpl. reflexivity.
    + subst S'. apply T_Loc.
      rewrite (@nth_error_app2 ty S (repeat TyNat (length mu - length S) ++ [T]) (length mu)); [|auto with zarith].
      rewrite (@nth_error_app2 ty (repeat TyNat (length mu - length S)) [T] (length mu - length S)); [|rewrite repeat_length; apply Nat.le_refl].
      replace (length mu - length S - length (repeat TyNat (length mu - length S))) with 0
        by (rewrite repeat_length; lia).
      simpl. reflexivity.
  - specialize (IHHstep Hok Hlen). edestruct (IHHstep (TyRef T0) H2) as [S' [Hext [Hok' Hty]]].
    exists S'; split; auto; split; auto. apply T_Deref; auto.
  - exists S; split; [exists []; symmetry; apply app_nil_r|]; split; [auto|].
    edestruct heap_ok_lookup as [T' [Hl' Hv]]; eauto.
    inversion H3; subst; match goal with H: nth_error S l = Some T0 |- _ => rewrite Hl' in H; inversion H; subst end.
    exact Hv.
  - specialize (IHHstep Hok Hlen). edestruct (IHHstep (TyRef T) H3) as [S' [Hext [Hok' Hty]]].
    exists S'; split; auto; split; auto.
    eapply T_Assign; [apply Hty| eapply has_type_weaken_store; eauto].
  - specialize (IHHstep Hok Hlen). edestruct (IHHstep T H5) as [S' [Hext [Hok' Hty]]].
    exists S'; split; auto; split; auto.
    eapply T_Assign; [eapply has_type_weaken_store; [exact H3|exact Hext]| apply Hty].
  - exists S; split; [exists []; symmetry; apply app_nil_r|]; split; [|apply T_Num].
    inversion H4; subst. apply heap_ok_update with (T := T); auto.
Qed.

Theorem preservation_neg : ~ (
  forall t mu t' mu' T S,
    has_type [] S t T ->
    step t mu t' mu' ->
    heap_ok mu S ->
    length mu >= length S ->
    exists S',
      extends S' S /\
      heap_ok mu' S' /\
      has_type [] S' t' T).
Proof.
Admitted.
