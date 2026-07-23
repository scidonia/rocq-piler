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

Lemma insert_cons_gt : forall n y l, (n <=? y) = false -> insert n (y :: l) = y :: insert n l.
Proof.
  intros n y l H.
  simpl. rewrite H. reflexivity.
Qed.

Lemma insert_sorted : forall n l, sorted l -> sorted (insert n l).
Proof.
  intros n l Hsorted. revert n. induction Hsorted as [|x|x y l Hle Hsub]; intros n.
  - simpl. apply sorted_single.
  - simpl.
    destruct (n <=? x) eqn:Hcmp.
    + apply Nat.leb_le in Hcmp.
      apply sorted_cons; auto. apply sorted_single.
    + apply Nat.leb_gt in Hcmp.
      apply sorted_cons.
      * apply Nat.lt_le_incl. exact Hcmp.
      * apply sorted_single.
  - simpl.
    destruct (n <=? x) eqn:Hcmp.
    + apply Nat.leb_le in Hcmp.
      apply sorted_cons; auto.
      apply sorted_cons with (y:=y) (l:=l); auto.
    + apply Nat.leb_gt in Hcmp.
      simpl.
      destruct (n <=? y) eqn:Hcmp2.
      * apply Nat.leb_le in Hcmp2.
        apply sorted_cons.
        -- apply Nat.lt_le_incl. exact Hcmp.
        -- apply sorted_cons; auto.
      * apply sorted_cons; auto.
        specialize (IHHsub n).
        rewrite (insert_cons_gt n y l Hcmp2) in IHHsub.
        exact IHHsub.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem insertion_sort_sorted : forall (l : list nat),
  sorted (insertion_sort l).
Proof.
  induction l as [|h t IH].
  - simpl. apply sorted_nil.
  - simpl. apply insert_sorted. apply IH.
Qed.

Theorem insertion_sort_sorted_neg : ~ (forall (l : list nat),
  sorted (insertion_sort l)).
Proof.
Admitted.
