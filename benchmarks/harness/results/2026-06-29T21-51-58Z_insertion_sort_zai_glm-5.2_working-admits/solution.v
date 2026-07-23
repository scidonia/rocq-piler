From Stdlib Require Import Arith List Lia.
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

(** ** Helper lemma: inserting into a sorted list yields a sorted list *)

Lemma insert_sorted : forall n l, sorted l -> sorted (insert n l).
Proof.
  intros n l H.
  induction H as [| x | x y l Hxy Hs IH].
  - simpl. constructor.
  - simpl. destruct (n <=? x) eqn:E.
    + apply Nat.leb_le in E. constructor; [exact E | constructor].
    + apply Nat.leb_gt in E. constructor; [lia | constructor].
  - simpl. simpl in IH. destruct (n <=? x) eqn:E.
    + apply Nat.leb_le in E. constructor; [exact E | constructor; [exact Hxy | exact Hs]].
    + apply Nat.leb_gt in E.
      destruct (n <=? y) eqn:E2.
      * apply Nat.leb_le in E2.
        constructor; [lia | constructor; [exact E2 | exact Hs]].
      * apply Nat.leb_gt in E2.
        constructor; [exact Hxy | exact IH].
Qed.

(** ** Conjecture pairs
     For each conjecture, both the statement and its negation are given.
     Prove exactly one of each pair. *)

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [| h t IH].
  - simpl. constructor.
  - simpl. apply insert_sorted. exact IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
