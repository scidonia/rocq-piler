From Stdlib Require Import Arith List.
Import ListNotations.

(** * Insertion Sort Correctness — Benchmark *)

Fixpoint insert (n : nat) (l : list nat) : list nat :=
  match l with
  | [] => [n]
  | h :: t => if n <=? h then n :: h :: t else h :: insert n t
  end.

Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (insertion_sort t)
  end.

Inductive sorted : list nat -> Prop :=
| sorted_nil : sorted []
| sorted_single : forall x, sorted [x]
| sorted_cons : forall x y l, x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Lemma sorted_insert : forall (n : nat) (l : list nat),
  sorted l -> sorted (insert n l).
Proof.
  intros n l H. induction H as [ | x | x y l Hxy Hs IH]; simpl.
  - constructor.
  - destruct (n <=? x) eqn:E.
    + apply Nat.leb_le in E. apply sorted_cons; [exact E | constructor].
    + apply Nat.leb_gt in E. apply sorted_cons.
      * apply Nat.lt_le_incl; exact E.
      * constructor.
  - destruct (n <=? x) eqn:E.
    + apply Nat.leb_le in E. apply sorted_cons.
      * exact E.
      * apply sorted_cons; assumption.
    + apply Nat.leb_gt in E.
      destruct (n <=? y) eqn:E2; simpl in IH; rewrite E2 in IH.
      * apply sorted_cons.
        -- apply Nat.lt_le_incl; exact E.
        -- exact IH.
      * apply sorted_cons; assumption.
Qed.

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [ | h t IH]; simpl.
  - constructor.
  - apply sorted_insert. exact IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
