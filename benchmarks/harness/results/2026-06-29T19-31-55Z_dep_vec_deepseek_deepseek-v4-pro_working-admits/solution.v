From Stdlib Require Import Arith Lia.

(** * A simple dependently-typed language: Nat + Vec — Benchmark *)

(** ** Types *)
Inductive ty : Type :=
  | TNat  : ty
  | TVec  : nat -> ty.

(** ** Terms *)
Inductive tm : Type :=
  | tzero  : tm
  | tsucc  : tm -> tm
  | tlit   : nat -> tm
  | tnil   : tm
  | tcons  : tm -> tm -> tm
  | thead  : tm -> tm
  | ttail  : tm -> tm.

(** ** Typing *)
Inductive has_type : tm -> ty -> Prop :=
  | T_Zero  : has_type tzero TNat
  | T_Succ  : forall t,
      has_type t TNat ->
      has_type (tsucc t) TNat
  | T_Lit   : forall n,
      has_type (tlit n) TNat
  | T_Nil   : has_type tnil (TVec 0)
  | T_Cons  : forall hd tl n,
      has_type hd TNat ->
      has_type tl (TVec n) ->
      has_type (tcons hd tl) (TVec (S n))
  | T_Head  : forall v n,
      has_type v (TVec (S n)) ->
      has_type (thead v) TNat
  | T_Tail  : forall v n,
      has_type v (TVec (S n)) ->
      has_type (ttail v) (TVec n).

(** ** Values *)
Inductive value : tm -> Prop :=
  | V_Zero  : value tzero
  | V_Succ  : forall t, value t -> value (tsucc t)
  | V_Lit   : forall n, value (tlit n)
  | V_Nil   : value tnil
  | V_Cons  : forall hd tl, value hd -> value tl -> value (tcons hd tl).

(** ** Small-step reduction *)
Inductive step : tm -> tm -> Prop :=
  | S_Succ  : forall t t',
      step t t' ->
      step (tsucc t) (tsucc t')
  | S_ConsHd : forall hd hd' tl,
      step hd hd' ->
      step (tcons hd tl) (tcons hd' tl)
  | S_ConsTl : forall hd tl tl',
      value hd ->
      step tl tl' ->
      step (tcons hd tl) (tcons hd tl')
  | S_Head  : forall v v',
      step v v' ->
      step (thead v) (thead v')
  | S_Tail  : forall v v',
      step v v' ->
      step (ttail v) (ttail v')
  | S_HeadCons : forall hd tl,
      value hd -> value tl ->
      step (thead (tcons hd tl)) hd
  | S_TailCons : forall hd tl,
      value hd -> value tl ->
      step (ttail (tcons hd tl)) tl.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem preservation : forall t t' T,
  has_type t T ->
  step t t' ->
  has_type t' T.
Proof.
  intros t t' T Htype Hstep.
  generalize dependent t'.
  induction Htype; intros t' Hstep.
  - inversion Hstep.
  - inversion Hstep; subst. apply T_Succ. apply IHHtype. assumption.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep; subst.
    + apply T_Cons. apply IHHtype1. assumption. apply Htype2.
    + apply T_Cons; try apply Htype1. apply IHHtype2. assumption.
  - inversion Hstep; subst.
    + apply T_Head with (n := n). apply IHHtype. assumption.
    + inversion_clear Htype. assumption.
  - inversion Hstep; subst.
    + apply T_Tail with (n := n). apply IHHtype. assumption.
    + inversion_clear Htype. assumption.
Qed.

Theorem preservation_neg : ~ (forall t t' T,
  has_type t T ->
  step t t' ->
  has_type t' T).
Proof.
Admitted.

Lemma canonical_TVec_S : forall v n,
  has_type v (TVec (S n)) ->
  value v ->
  exists hd tl, v = tcons hd tl /\ value hd /\ value tl.
Proof.
  intros v n Ht Hv.
  destruct Hv as [ | t Hv_val | n0 | | hd tl Hv_hd Hv_tl ].
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
  - exists hd, tl. auto.
Qed.

(** ** Progress *)
Theorem progress : forall t T,
  has_type t T ->
  value t \/ exists t', step t t'.
Proof.
  intros t T Ht.
  induction Ht as [
    | t H IH
    | n
    |
    | hd tl n Hhd IHhd Htl IHtl
    | v n Hv IH
    | v n Hv IH
  ].
  - left. constructor.
  - destruct IH as [Hval | [t' Hstep]].
    + left. constructor. assumption.
    + right. exists (tsucc t'). constructor. assumption.
  - left. constructor.
  - left. constructor.
  - destruct IHhd as [Hv_hd | [hd' Hstep_hd]].
    + destruct IHtl as [Hv_tl | [tl' Hstep_tl]].
      * left. constructor; assumption.
      * right. exists (tcons hd tl'). apply S_ConsTl; assumption.
    + right. exists (tcons hd' tl). apply S_ConsHd; assumption.
  - destruct IH as [Hval | [v' Hstep_v]].
    + destruct (canonical_TVec_S v n Hv Hval) as (hd' & tl' & Heq & Hv_hd & Hv_tl). subst.
      right. exists hd'. apply S_HeadCons; assumption.
    + right. exists (thead v'). constructor. assumption.
  - destruct IH as [Hval | [v' Hstep_v]].
    + destruct (canonical_TVec_S v n Hv Hval) as (hd' & tl' & Heq & Hv_hd & Hv_tl). subst.
      right. exists tl'. apply S_TailCons; assumption.
    + right. exists (ttail v'). constructor. assumption.
Qed.

Theorem progress_neg : ~ (forall t T,
  has_type t T ->
  value t \/ exists t', step t t').
Proof.
Admitted.
