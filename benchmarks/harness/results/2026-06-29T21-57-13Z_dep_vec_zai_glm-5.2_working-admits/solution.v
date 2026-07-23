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

(** ** Canonical forms: a value of type TVec (S n) must be a cons *)
Lemma vec_cons_canonical : forall v n,
  value v ->
  has_type v (TVec (S n)) ->
  exists hd tl, v = tcons hd tl /\ value hd /\ value tl.
Proof.
  intros v n Hv Ht.
  inversion Hv; subst; inversion Ht; subst; try discriminate.
  eexists. eexists. split; [ reflexivity | split; eassumption ].
Qed.

(** ** Conjecture pairs
     For each conjecture, both the statement and its negation are given.
     Prove exactly one of each pair. *)

Theorem preservation : forall t t' T,
  has_type t T ->
  step t t' ->
  has_type t' T.
Proof.
  intros t t' T Ht Hstep.
  generalize dependent T.
  induction Hstep as
    [ t0 t1 Hs IHs
    | hd hd' tl Hs IHs
    | hd tl tl' Hv Hs IHs
    | v0 v1 Hs IHs
    | v0 v1 Hs IHs
    | hd tl Hv1 Hv2
    | hd tl Hv1 Hv2
    ]; intros T Ht; inversion Ht; subst.
  - apply T_Succ; apply IHs; eassumption.
  - apply T_Cons; [ apply IHs; eassumption | eassumption ].
  - apply T_Cons; [ eassumption | apply IHs; eassumption ].
  - eapply T_Head; apply IHs; eassumption.
  - eapply T_Tail; apply IHs; eassumption.
  - match goal with H : has_type (tcons _ _) _ |- _ => inversion H; subst; eassumption end.
  - match goal with H : has_type (tcons _ _) _ |- _ => inversion H; subst; eassumption end.
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
  intros t T Ht.
  induction Ht as [ | t' Ht' IHt' | n | | hd tl n Hhd IHhd Htl IHtl | v n Hv IHv | v n Hv IHv ].
  - left. constructor.
  - destruct IHt' as [ Hv | [t'' Hstep] ].
    + left. constructor; exact Hv.
    + right. exists (tsucc t''). apply S_Succ; exact Hstep.
  - left. constructor.
  - left. constructor.
  - destruct IHhd as [ Hvhd | [hd' Hstephd] ].
    + destruct IHtl as [ Hvtl | [tl' Hsteptl] ].
      * left. constructor; [ exact Hvhd | exact Hvtl ].
      * right. exists (tcons hd tl'). apply S_ConsTl; [ exact Hvhd | exact Hsteptl ].
    + right. exists (tcons hd' tl). apply S_ConsHd; exact Hstephd.
  - destruct IHv as [ Hval | [v' Hstep] ].
    + destruct (vec_cons_canonical v n Hval Hv) as [hd [tl [Heq [Hvhd Hvtl]]]].
      subst v.
      right. exists hd. apply S_HeadCons; [ exact Hvhd | exact Hvtl ].
    + right. exists (thead v'). apply S_Head; exact Hstep.
  - destruct IHv as [ Hval | [v' Hstep] ].
    + destruct (vec_cons_canonical v n Hval Hv) as [hd [tl [Heq [Hvhd Hvtl]]]].
      subst v.
      right. exists tl. apply S_TailCons; [ exact Hvhd | exact Hvtl ].
    + right. exists (ttail v'). apply S_Tail; exact Hstep.
Qed.

Theorem progress_neg : ~ (forall t T,
  has_type t T ->
  value t \/ exists t', step t t').
Proof.
Admitted.
