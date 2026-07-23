From Stdlib Require Import Arith List Lia PeanoNat Utf8.
Import ListNotations.

(** * Indexed Inductive Families — Benchmark
    Self-contained CIC fragment with:
    - Dependent function types (Pi/Lam/App)
    - General recursion (Fix)
    - Inductive families described by signatures
    - Dependent case analysis with motives
    Based on the term language and typing from github.com/Scidonia/cyclic *)

(** ** Inductive signatures *)

Record ctor_sig : Type := {
  ctor_param_tys : list nat;        (* non-recursive arg type indices — simplified to nats *)
  ctor_rec_arity : nat;             (* number of recursive arguments *)
}.

Record ind_sig : Type := {
  ind_level : nat;
  ind_ctors : list ctor_sig
}.

Definition lookup {A : Type} (xs : list A) (n : nat) : option A :=
  nth_error xs n.

Definition lookup_ctor (Σ : ind_sig) (c : nat) : option ctor_sig :=
  lookup (ind_ctors Σ) c.

Definition ctor_param_arity (c : ctor_sig) : nat :=
  length (ctor_param_tys c).

Definition ctor_arity (c : ctor_sig) : nat :=
  ctor_param_arity c + ctor_rec_arity c.

(** ** Term language *)

Inductive tm : Type :=
| tVar (x : nat)
| tSort (i : nat)
| tPi (A : tm) (B : tm)
| tLam (A : tm) (t : tm)
| tApp (t u : tm)
| tFix (A : tm) (t : tm)
| tInd (I : nat)
| tRoll (I : nat) (c : nat) (args : list tm)
| tCase (I : nat) (scrut : tm) (C : tm) (brs : list tm).

Definition branch (brs : list tm) (c : nat) : option tm :=
  nth_error brs c.

(** ** Substitution machinery (reimplements Autosubst core) *)

Definition sub := nat -> tm.
Definition ids : sub := tVar.
Definition scons (s : tm) (σ : sub) : sub :=
  fun x => match x with 0 => s | S x => σ x end.

Fixpoint rename (ξ : nat -> nat) (t : tm) : tm :=
  match t with
  | tVar x => tVar (ξ x)
  | tSort i => tSort i
  | tPi A B => tPi (rename ξ A) (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) B)
  | tLam A t => tLam (rename ξ A) (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) t)
  | tApp t u => tApp (rename ξ t) (rename ξ u)
  | tFix A t => tFix (rename ξ A) (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) t)
  | tInd Ix => tInd Ix
  | tRoll Ix c args => tRoll Ix c (map (rename ξ) args)
  | tCase Ix scrut C brs =>
      tCase Ix (rename ξ scrut) (rename (fun x => match x with 0 => 0 | S x => S (ξ x) end) C) (map (rename ξ) brs)
  end.

Definition shift (n : nat) (t : tm) : tm := rename (Nat.add n) t.
Definition shift1 (t : tm) : tm := shift 1 t.

Definition up_sub (σ : sub) : sub :=
  scons (tVar 0) (fun x => shift1 (σ x)).

Fixpoint apply_sub (σ : sub) (t : tm) : tm :=
  match t with
  | tVar x => σ x
  | tSort i => tSort i
  | tPi A B => tPi (apply_sub σ A) (apply_sub (up_sub σ) B)
  | tLam A t => tLam (apply_sub σ A) (apply_sub (up_sub σ) t)
  | tApp t u => tApp (apply_sub σ t) (apply_sub σ u)
  | tFix A t => tFix (apply_sub σ A) (apply_sub (up_sub σ) t)
  | tInd Ix => tInd Ix
  | tRoll Ix c args => tRoll Ix c (map (apply_sub σ) args)
  | tCase Ix scrut C brs =>
      tCase Ix (apply_sub σ scrut) (apply_sub (up_sub σ) C) (map (apply_sub σ) brs)
  end.

Definition subst0 (s : tm) (t : tm) : tm :=
  apply_sub (scons s ids) t.

Definition ren (ξ : nat -> nat) : sub := fun x => tVar (ξ x).

(** ** Helpers *)

Fixpoint apps (t : tm) (us : list tm) : tm :=
  match us with
  | [] => t
  | u :: us => apps (tApp t u) us
  end.

Fixpoint mk_pis (As : list tm) (B : tm) : tm :=
  match As with
  | [] => B
  | A :: As => tPi A (mk_pis As B)
  end.

Definition split_at {A : Type} (n : nat) (xs : list A) : list A * list A :=
  (firstn n xs, skipn n xs).

Definition motive_inst (I c m : nat) (C : tm) : tm :=
  apply_sub (scons (tRoll I c (map tVar (rev (seq 0 m)))) (ren (Nat.add m))) C.

(** ** Typing context *)

Definition env := list ind_sig.
Definition ctx := list tm.

Fixpoint ctx_lookup (Γ : ctx) (x : nat) : option tm :=
  match Γ, x with
  | [], _ => None
  | A :: _, 0 => Some (shift1 A)
  | _ :: Γ, S x => option_map shift1 (ctx_lookup Γ x)
  end.

(** ** Typing judgment *)

Inductive has_type (Σenv : env) : ctx -> tm -> tm -> Prop :=
| ty_var Γ x A :
    ctx_lookup Γ x = Some A ->
    has_type Σenv Γ (tVar x) A

| ty_sort Γ i :
    has_type Σenv Γ (tSort i) (tSort (S i))

| ty_pi Γ A B i j :
    has_type Σenv Γ A (tSort i) ->
    has_type Σenv (A :: Γ) B (tSort j) ->
    has_type Σenv Γ (tPi A B) (tSort (Nat.max i j))

| ty_lam Γ A t B i :
    has_type Σenv Γ A (tSort i) ->
    has_type Σenv (A :: Γ) t B ->
    has_type Σenv Γ (tLam A t) (tPi A B)

| ty_app Γ t u A B :
    has_type Σenv Γ t (tPi A B) ->
    has_type Σenv Γ u A ->
    has_type Σenv Γ (tApp t u) (subst0 u B)

| ty_fix Γ A t i :
    has_type Σenv Γ A (tSort i) ->
    has_type Σenv (A :: Γ) t (shift1 A) ->
    has_type Σenv Γ (tFix A t) A

| ty_ind Γ I ΣI :
    lookup Σenv I = Some ΣI ->
    has_type Σenv Γ (tInd I) (tSort (S (ind_level ΣI)))

| ty_roll Γ I ΣI c ctor args :
    lookup Σenv I = Some ΣI ->
    lookup_ctor ΣI c = Some ctor ->
    length args = ctor_arity ctor ->
    Forall (fun a => has_type Σenv Γ a (tInd I)) args ->
    has_type Σenv Γ (tRoll I c args) (tInd I)

| ty_case Γ I ΣI scrut C brs i :
    lookup Σenv I = Some ΣI ->
    length brs = length (ind_ctors ΣI) ->
    has_type Σenv Γ scrut (tInd I) ->
    has_type Σenv (tInd I :: Γ) C (tSort i) ->
    (forall c ctor,
      lookup_ctor ΣI c = Some ctor ->
      exists br,
        branch brs c = Some br
        /\
        let As := repeat (tInd I) (ctor_param_arity ctor + ctor_rec_arity ctor) in
        let m := length As in
        has_type Σenv Γ br (mk_pis As (motive_inst I c m C))) ->
    has_type Σenv Γ (tCase I scrut C brs) (subst0 scrut C).

(** ** Values and step relation *)

Inductive value : tm -> Prop :=
| v_sort i : value (tSort i)
| v_pi A B : value (tPi A B)
| v_lam A t : value (tLam A t)
| v_ind I : value (tInd I)
| v_roll I c args : value (tRoll I c args).

Inductive step : tm -> tm -> Prop :=
| step_beta A t u :
    step (tApp (tLam A t) u) (subst0 u t)
| step_app1 t t' u :
    step t t' ->
    step (tApp t u) (tApp t' u)
| step_fix A t :
    step (tFix A t) (subst0 (tFix A t) t)
| step_case_scrut I scrut scrut' C brs :
    step scrut scrut' ->
    step (tCase I scrut C brs) (tCase I scrut' C brs)
| step_case_roll I c args C brs br :
    branch brs c = Some br ->
    step (tCase I (tRoll I c args) C brs) (apps br args).

(** ** Example signatures *)

Definition Nat_sig : ind_sig := {|
  ind_level := 0;
  ind_ctors := [
    {| ctor_param_tys := []; ctor_rec_arity := 0 |};   (* zero *)
    {| ctor_param_tys := []; ctor_rec_arity := 1 |}    (* succ *)
  ]
|}.

Definition zero : tm := tRoll 0 0 [].
Definition succ_tm (n : tm) : tm := tRoll 0 1 [n].

Definition Bool_sig : ind_sig := {|
  ind_level := 0;
  ind_ctors := [
    {| ctor_param_tys := []; ctor_rec_arity := 0 |};   (* true *)
    {| ctor_param_tys := []; ctor_rec_arity := 0 |}    (* false *)
  ]
|}.

Definition List_sig : ind_sig := {|
  ind_level := 1;
  ind_ctors := [
    {| ctor_param_tys := []; ctor_rec_arity := 0 |};   (* nil *)
    {| ctor_param_tys := [0]; ctor_rec_arity := 1 |}   (* cons: one param + one rec *)
  ]
|}.

(** Standard global environment for examples *)
Definition Σ_std : env := [Nat_sig; Bool_sig; List_sig].

(** ** Helper definitions and inversion lemmas *)

Definition Empty_sig : ind_sig := {| ind_level := 0; ind_ctors := [] |}.

Lemma case_type_inv :
  forall Σ Γ I s C brs T,
    has_type Σ Γ (tCase I s C brs) T -> T = subst0 s C.
Proof.
  intros Σ Γ I s C brs T Hty.
  inversion Hty; subst.
  reflexivity.
Qed.

Lemma canonical_pi :
  forall Σ v A B,
    value v -> has_type Σ [] v (tPi A B) ->
    exists A' t', v = tLam A' t'.
Proof.
  intros Σ v A B Hv Hty.
  destruct Hv as [i|A1 B1|A1 t1|I|I c args].
  - inversion Hty.
  - inversion Hty.
  - exists A1, t1. reflexivity.
  - inversion Hty.
  - inversion Hty.
Qed.

Lemma canonical_ind :
  forall Σ v I,
    value v -> has_type Σ [] v (tInd I) ->
    exists c args, v = tRoll I c args.
Proof.
  intros Σ v I Hv Hty.
  destruct Hv as [i|A1 B1|A1 t1|J|J c args].
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty; subst. exists c, args. reflexivity.
Qed.

Lemma roll_type_inv :
  forall Σ Γ I c args T,
    has_type Σ Γ (tRoll I c args) T ->
    exists ΣI ctor,
      lookup Σ I = Some ΣI /\ lookup_ctor ΣI c = Some ctor /\ T = tInd I.
Proof.
  intros Σ Γ I c args T Hty.
  inversion Hty; subst.
  do 2 eexists. split; [eassumption | split; [eassumption | reflexivity]].
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem preservation :
  forall Σenv Γ t t' T,
    has_type Σenv Γ t T ->
    step t t' ->
    has_type Σenv Γ t' T.
Proof. Admitted.

Theorem preservation_neg : ~ (
  forall Σenv Γ t t' T,
    has_type Σenv Γ t T ->
    step t t' ->
    has_type Σenv Γ t' T).
Proof.
  intros H.
  assert (Hty : has_type [Empty_sig] []
    (tCase 0 (tApp (tLam (tInd 0) (tVar 0)) (tFix (tInd 0) (tVar 0)))
             (tApp (tLam (tInd 0) (tSort 0)) (tVar 0)) [])
    (subst0 (tApp (tLam (tInd 0) (tVar 0)) (tFix (tInd 0) (tVar 0)))
            (tApp (tLam (tInd 0) (tSort 0)) (tVar 0)))).
  { eapply ty_case with (ΣI := Empty_sig) (i := 1).
    - reflexivity.
    - reflexivity.
    - eapply ty_app with (A := tInd 0) (B := tInd 0).
      + eapply ty_lam with (i := 1).
        * eapply ty_ind with (ΣI := Empty_sig). reflexivity.
        * eapply ty_var. reflexivity.
      + eapply ty_fix with (i := 1).
        * eapply ty_ind with (ΣI := Empty_sig). reflexivity.
        * eapply ty_var. reflexivity.
    - eapply ty_app with (A := tInd 0) (B := tSort 1).
      + eapply ty_lam with (i := 1).
        * eapply ty_ind with (ΣI := Empty_sig). reflexivity.
        * eapply ty_sort.
      + eapply ty_var. reflexivity.
    - intros c ctor Hc. destruct c; cbn in Hc; discriminate Hc. }
  assert (Hstep : step
    (tCase 0 (tApp (tLam (tInd 0) (tVar 0)) (tFix (tInd 0) (tVar 0)))
             (tApp (tLam (tInd 0) (tSort 0)) (tVar 0)) [])
    (tCase 0 (tFix (tInd 0) (tVar 0))
             (tApp (tLam (tInd 0) (tSort 0)) (tVar 0)) [])).
  { apply step_case_scrut. apply step_beta. }
  specialize (H _ _ _ _ _ Hty Hstep).
  apply case_type_inv in H.
  cbn in H.
  discriminate H.
Qed.

Theorem progress :
  forall Σenv t T,
    has_type Σenv [] t T ->
    value t \/ exists t', step t t'.
Proof.
  intros Σenv t T Ht.
  remember (@nil tm) as Γ eqn:HΓ.
  induction Ht as [
    Γ x A Hlk
  | Γ i
  | Γ A B i j HA IHA HB IHB
  | Γ A tb B i HA IHA Htb IHtb
  | Γ tf u A B Htf IHtf Hu IHu
  | Γ A tb i HA IHA Htb IHtb
  | Γ I ΣI Hlk
  | Γ I ΣI c ctor args Hlk Hlc Hlen HF
  | Γ I ΣI scrut C brs i Hlk Hlen Hscrut IHscrut HC IHC Hbr
  ]; intros; subst.
  - (* ty_var *) cbn in Hlk. discriminate Hlk.
  - (* ty_sort *) left. constructor.
  - (* ty_pi *) left. constructor.
  - (* ty_lam *) left. constructor.
  - (* ty_app *)
    right.
    destruct (IHtf eq_refl) as [Hv | [tf' Hstep]].
    + destruct (canonical_pi _ _ _ _ Hv Htf) as [A' [tb' Heq]]. subst.
      eexists. apply step_beta.
    + eexists. apply step_app1. eassumption.
  - (* ty_fix *) right. eexists. apply step_fix.
  - (* ty_ind *) left. constructor.
  - (* ty_roll *) left. constructor.
  - (* ty_case *)
    right.
    destruct (IHscrut eq_refl) as [Hv | [scrut' Hstep]].
    + destruct (canonical_ind _ _ _ Hv Hscrut) as [c0 [args0 Heqs]]. subst.
      destruct (roll_type_inv _ _ _ _ _ _ Hscrut)
        as [ΣI' [ctor' [Hlk' [Hlc' _]]]].
      assert (HΣ : ΣI' = ΣI) by congruence. subst ΣI'.
      assert (Hc0 : c0 < length (ind_ctors ΣI)).
      { apply nth_error_Some. unfold lookup_ctor, lookup in Hlc'.
        rewrite Hlc'. discriminate. }
      rewrite <- Hlen in Hc0.
      destruct (nth_error brs c0) as [br|] eqn:Ebr.
      * exists (apps br args0). apply step_case_roll. unfold branch. exact Ebr.
      * exfalso. apply nth_error_Some in Hc0. apply Hc0. exact Ebr.
    + eexists. apply step_case_scrut. eassumption.
Qed.

Theorem progress_neg : ~ (
  forall Σenv t T,
    has_type Σenv [] t T ->
    value t \/ exists t', step t t').
Proof. Admitted.
