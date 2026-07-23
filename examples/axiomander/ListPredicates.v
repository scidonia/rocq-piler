From Stdlib Require Import List ZArith Bool.
Import ListNotations.

(* Library of recursor combinators for list predicates.

   Each recursor is a Fixpoint — structurally recursive, Coq accepts
   natively.  Proved lemmas are proved once and applied everywhere.
   User-defined `for x in xs:` predicates lower to these combinators.
*)

Fixpoint forallb {A} (p : A -> bool) (xs : list A) : bool :=
  match xs with
  | [] => true
  | x :: rest => p x && forallb p rest
  end.

Fixpoint existsb {A} (p : A -> bool) (xs : list A) : bool :=
  match xs with
  | [] => false
  | x :: rest => p x || existsb p rest
  end.

Fixpoint countb {A} (p : A -> bool) (xs : list A) : nat :=
  match xs with
  | [] => 0
  | x :: rest => (if p x then 1 else 0) + countb p rest
  end.

Fixpoint fold_left_acc {A B} (f : B -> A -> B) (acc : B) (xs : list A) : B :=
  match xs with
  | [] => acc
  | x :: rest => fold_left_acc f (f acc x) rest
  end.

Fixpoint filterb {A} (p : A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: rest => if p x then x :: filterb p rest else filterb p rest
  end.

(* Lemmas proved once — callers use these instead of re-proving per predicate. *)

Lemma forallb_true : forall A (p : A -> bool) (xs : list A),
  forallb p xs = true <-> (forall x, In x xs -> p x = true).
Proof.
  intros A p xs.
  induction xs as [|y ys IH]; simpl.
  - split; auto.
  - rewrite Bool.andb_true_iff.
    split.
    + intros [Hpy Hforall] z [-> | Hz].
      * exact Hpy.
      * apply IH; auto.
    + intros H. split.
      * apply H; left; reflexivity.
      * apply IH; intros z Hz; apply H; right; exact Hz.
Qed.

Lemma existsb_true : forall A (p : A -> bool) (xs : list A),
  existsb p xs = true <-> exists x, In x xs /\ p x = true.
Proof.
  intros A p xs.
  induction xs as [|y ys IH]; simpl.
  - split; [easy | intros [x [H _]]; easy].
  - rewrite Bool.orb_true_iff.
    split.
    + intros [Hpy | Hex].
      * exists y; split; [left; reflexivity | exact Hpy].
      * apply IH in Hex as [x [Hx Hpx]].
        exists x; split; [right; exact Hx | exact Hpx].
    + intros [x [[-> | Hx] Hpx]].
      * left; exact Hpx.
      * right; apply IH; exists x; split; [exact Hx | exact Hpx].
Qed.

Lemma countb_app : forall A (p : A -> bool) (xs ys : list A),
  countb p (xs ++ ys) = countb p xs + countb p ys.
Proof.
  intros A p xs ys.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH; destruct (p x); reflexivity.
Qed.

(* ------------------------------------------------------------- *)
(* Tail: structural destructor for list-decreasing recursion.     *)
(* ------------------------------------------------------------- *)

Definition tail {A} (xs : list A) : list A :=
  match xs with
  | [] => []
  | _ :: rest => rest
  end.

Lemma tail_length {A} (xs : list A) :
  xs <> [] -> List.length (tail xs) < List.length xs.
Proof.
  intros Hnotnil.
  destruct xs as [|x xs]; [congruence |].
  simpl. apply Nat.lt_succ_diag_r.
Qed.

(* ------------------------------------------------------------- *)
(* Admissible rewrite: fold_left_acc patterns → specialised       *)
(* recursors.  These lemmas allow the prover to rewrite generic   *)
(* fold_left_acc terms to forallb / existsb / countb when the     *)
(* fold pattern matches a known form, gaining lemma support.      *)
(* ------------------------------------------------------------- *)

Lemma fold_left_andb_equiv {A} (p : A -> bool) (b : bool) (xs : list A) :
  fold_left_acc (fun (acc : bool) (x : A) => andb acc (p x)) b xs =
  andb b (forallb p xs).
Proof.
  revert b. induction xs as [|x xs IH].
  - intro b. simpl. rewrite Bool.andb_true_r. reflexivity.
  - intro b. simpl. rewrite IH. rewrite Bool.andb_assoc. reflexivity.
Qed.

Lemma fold_to_forallb {A} (p : A -> bool) (xs : list A) :
  fold_left_acc (fun (acc : bool) (x : A) => andb acc (p x)) true xs = forallb p xs.
Proof.
  rewrite fold_left_andb_equiv. simpl. reflexivity.
Qed.

Lemma fold_left_orb_equiv {A} (p : A -> bool) (b : bool) (xs : list A) :
  fold_left_acc (fun (acc : bool) (x : A) => orb acc (p x)) b xs =
  orb b (existsb p xs).
Proof.
  revert b. induction xs as [|x xs IH].
  - intro b. simpl. rewrite Bool.orb_false_r. reflexivity.
  - intro b. simpl. rewrite IH. rewrite Bool.orb_assoc. reflexivity.
Qed.

Lemma fold_to_existsb {A} (p : A -> bool) (xs : list A) :
  fold_left_acc (fun (acc : bool) (x : A) => orb acc (p x)) false xs = existsb p xs.
Proof.
  rewrite fold_left_orb_equiv. simpl. reflexivity.
Qed.

Lemma fold_left_count_equiv {A} (p : A -> bool) (n : nat) (xs : list A) :
  fold_left_acc (fun (acc : nat) (x : A) => if p x then S acc else acc) n xs =
  n + countb p xs.
Proof.
  revert n. induction xs as [|x xs IH].
  - intro n. cbn. auto with arith.
  - intro n. simpl. destruct (p x); simpl; rewrite IH; auto with arith.
Qed.

Lemma fold_to_countb {A} (p : A -> bool) (xs : list A) :
  fold_left_acc (fun (acc : nat) (x : A) => if p x then S acc else acc) O xs = countb p xs.
Proof.
  rewrite fold_left_count_equiv. auto with arith.
Qed.

(* ------------------------------------------------------------- *)
(* Bridge: forallb -> Forall (for wp_for_list_forall).            *)
(* Connects pure forallb preconditions to per-element loop        *)
(* invariants in the Iris WP.                                     *)
(* ------------------------------------------------------------- *)

Lemma forallb_to_Forall {A} (f : A -> bool) (xs : list A) :
  forallb f xs = true -> Forall (fun x => f x = true) xs.
Proof.
  intro H.
  rewrite forallb_true in H.
  apply Forall_forall. exact H.
Qed.

(* ------------------------------------------------------------- *)
(* dropn: skip n elements; decreases structurally on n.           *)
(* Allows xs[n:] recursion with a nat counter as the measure.     *)
(* ------------------------------------------------------------- *)

Fixpoint dropn {A} (xs : list A) (n : nat) : list A :=
  match n, xs with
  | O, _ => xs
  | S n', _ :: rest => dropn rest n'
  | _, [] => []
  end.
