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

Lemma insert_sorted : forall n l, sorted l -> sorted (insert n l).
Proof.
  induction 1 as [|x| x y l Hle Hsorted IH].
  - apply sorted_single.
  - simpl. destruct (n <=? x) eqn:Hnx.
    + apply sorted_cons with (l:=[]).
      * apply Nat.leb_le. exact Hnx.
      * apply sorted_single.
    + apply leb_complete_conv in Hnx.
      apply Nat.lt_le_incl in Hnx.
      apply sorted_cons with (l:=[]).
      * exact Hnx.
      * apply sorted_single.
  - simpl. destruct (n <=? x) eqn:Hnx.
    + apply sorted_cons with (y:=x) (l:=y::l).
      * apply Nat.leb_le. exact Hnx.
      * constructor; assumption.
    + apply leb_complete_conv in Hnx.
      apply Nat.lt_le_incl in Hnx.
      simpl in IH.
      destruct (n <=? y) eqn:Hny.
      * apply sorted_cons with (y:=n) (l:=y :: l).
        -- exact Hnx.
        -- exact IH.
      * apply sorted_cons with (y:=y) (l:=insert n l).
        -- exact Hle.
        -- exact IH.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [|h t IH].
  - apply sorted_nil.
  - simpl. apply insert_sorted. exact IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
