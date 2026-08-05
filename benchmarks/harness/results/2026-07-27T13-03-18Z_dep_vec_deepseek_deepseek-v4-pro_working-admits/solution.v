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

(** ** Canonical forms *)
Lemma canonical_vec_succ : forall v n,
  value v ->
  has_type v (TVec (S n)) ->
  exists hd tl, v = tcons hd tl /\ value hd /\ value tl.
Proof.
  intros v n Hv Ht.
  induction Hv.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
  - exists hd, tl. auto.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem preservation : forall t t' T,
  has_type t T ->
  step t t' ->
  has_type t' T.
Proof.
  intros t t' T Htype Hstep.
  revert T Htype.
  induction Hstep as
    [ t1 t2 Hstep IH
    | hd1 hd2 tl Hstep IH
    | hd tl1 tl2 Hval Hstep IH
    | v1 v2 Hstep IH
    | v1 v2 Hstep IH
    | hd tl Hv_hd Hv_tl
    | hd tl Hv_hd Hv_tl ];
    intros T Htype; inversion Htype; subst; clear Htype.
  - apply T_Succ. apply IH with (T := TNat). assumption.
  - apply T_Cons; [ apply IH with (T := TNat); assumption | assumption ].
  - apply T_Cons; [ assumption | apply IH with (T := TVec n); assumption ].
  - apply T_Head with (n := n). apply IH with (T := TVec (S n)). assumption.
  - apply T_Tail with (n := n). apply IH with (T := TVec (S n)). assumption.
   - inversion H0; subst. assumption.
   - inversion H0; subst. assumption.
Qed.

Theorem preservation_neg : ~ (forall t t' T,
  has_type t T ->
  step t t' ->
  has_type t' T).
Proof.
Admitted.

(** ** Progress *)
Theorem progress : forall t T,
  has_type t T ->
  value t \/ exists t', step t t'.
Proof.
  intros t T H; induction H.
  { (* T_Zero:82f70714 *) solve [ left; constructor ]. }
  { (* T_Succ:d627f52a *) destruct IHhas_type as [Hv | [t' Hstep]].
- left. apply V_Succ; exact Hv.
- right. exists (tsucc t'). apply S_Succ; exact Hstep.
  }
  { (* T_Lit:df0386de *) solve [ left; constructor ]. }
  { (* T_Nil:1b3ed6d8 *) solve [ left; constructor ]. }
  { (* T_Cons:8c5411b3 *) destruct IHhas_type1 as [Hv_hd | [hd' Hstep_hd]].
- destruct IHhas_type2 as [Hv_tl | [tl' Hstep_tl]].
  + left. apply V_Cons; auto.
  + right. exists (tcons hd tl'). apply S_ConsTl; auto.
- right. exists (tcons hd' tl). apply S_ConsHd; auto.
  }
  { (* T_Head:24fffffc *) destruct IHhas_type as [Hv_val | [v' Hstep_v]].
    - destruct (canonical_vec_succ _ _ Hv_val H) as [hd0 [tl0 [Heq [Hv_hd Hv_tl]]]]; subst.
      right. eexists. apply S_HeadCons; eauto.
    - right. eexists. apply S_Head; eauto. }
  { (* T_Tail:ef375e2c *) destruct IHhas_type as [Hv_val | [v' Hstep_v]].
    - destruct (canonical_vec_succ _ _ Hv_val H) as [hd0 [tl0 [Heq [Hv_hd Hv_tl]]]]; subst.
      right. eexists. apply S_TailCons; eauto.
    - right. eexists. apply S_Tail; eauto. }
Qed.

Theorem progress_neg : ~ (forall t T,
  has_type t T ->
  value t \/ exists t', step t t').
Proof.
Admitted.
