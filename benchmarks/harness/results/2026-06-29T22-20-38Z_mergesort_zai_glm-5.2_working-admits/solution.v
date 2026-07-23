From Stdlib Require Import Arith List Lia PeanoNat Permutation.
Import ListNotations.

(** * Merge Sort Correctness — Benchmark *)

Fixpoint merge (l1 l2 : list nat) {struct l1} : list nat :=
  match l1 with
  | [] => l2
  | x :: xs =>
    (fix merge_inner (l2 : list nat) : list nat :=
      match l2 with
      | [] => x :: xs
      | y :: ys =>
        if x <=? y then x :: merge xs l2
        else y :: merge_inner ys
      end) l2
  end.

Inductive sorted : list nat -> Prop :=
  | sorted_nil : sorted []
  | sorted_singleton x : sorted [x]
  | sorted_cons x y l :
      x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Fixpoint split (l : list nat) : list nat * list nat :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
    let (l1, l2) := split rest in
    (x :: l1, y :: l2)
  end.

Fixpoint mergesort (fuel : nat) (l : list nat) : list nat :=
  match fuel with
  | 0 => l
  | S fuel' =>
    match l with
    | [] => []
    | [x] => [x]
    | _ :: _ :: _ =>
      let (l1, l2) := split l in
      merge (mergesort fuel' l1) (mergesort fuel' l2)
    end
  end.

(** ** Helper lemmas *)

Lemma split_aux : forall n l, length l <= n -> forall l1 l2,
  split l = (l1, l2) -> Permutation l (l1 ++ l2) /\ length l1 + length l2 = length l.
Proof.
  induction n as [| n IH]; intros l Hle l1 l2 H.
  - destruct l as [| x l'].
    + simpl in H. inversion H; subst. simpl. split; [ apply Permutation_refl | reflexivity ].
    + simpl in Hle. lia.
  - destruct l as [| x l'].
    + simpl in H. inversion H; subst. simpl. split; [ apply Permutation_refl | reflexivity ].
    + destruct l' as [| y rest].
      * simpl in H. inversion H; subst. simpl. split; [ apply Permutation_refl | reflexivity ].
      * destruct (split rest) as [r1 r2] eqn:E.
        assert (Hl : l1 = x :: r1 /\ l2 = y :: r2).
        { simpl in H. rewrite E in H. inversion H; subst. split; reflexivity. }
        destruct Hl as [-> ->]. simpl.
        assert (Hrest : length rest <= n) by (simpl in Hle; lia).
        destruct (IH rest Hrest r1 r2 E) as [Hperm Hlen].
        split.
        { eapply Permutation_trans.
          - apply perm_skip. apply perm_skip. exact Hperm.
          - apply perm_skip. apply Permutation_middle. }
        { lia. }
Qed.

Lemma split_perm : forall l l1 l2,
  split l = (l1, l2) -> Permutation l (l1 ++ l2).
Proof.
  intros l l1 l2 H. destruct (split_aux (length l) l (Nat.le_refl _) l1 l2 H) as [Hp _]. exact Hp.
Qed.

Lemma split_length : forall l l1 l2,
  split l = (l1, l2) -> length l1 + length l2 = length l.
Proof.
  intros l l1 l2 H. destruct (split_aux (length l) l (Nat.le_refl _) l1 l2 H) as [_ Hl]. exact Hl.
Qed.

Lemma merge_perm : forall l1 l2, Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction l1 as [| x xs IH]; intros l2.
  - simpl. apply Permutation_refl.
  - induction l2 as [| y ys IH2].
    + simpl. rewrite app_nil_r. apply Permutation_refl.
    + simpl. destruct (x <=? y) eqn:Hxy.
      * apply perm_skip. apply IH.
      * eapply Permutation_trans.
        apply (Permutation_sym (Permutation_middle (x :: xs) ys y)).
        apply perm_skip. apply IH2.
Qed.

Lemma mergesort_perm_gen : forall fuel l, length l <= fuel -> Permutation l (mergesort fuel l).
Proof.
  induction fuel as [| fuel' IH]; intros l Hle.
  - destruct l as [| x l'].
    + simpl. apply Permutation_refl.
    + simpl in Hle. lia.
  - destruct l as [| x l'].
    + simpl. apply Permutation_refl.
    + destruct l' as [| y rest].
      * simpl. apply Permutation_refl.
      * destruct (split rest) as [r1 r2] eqn:E.
        assert (Hsl : split (x :: y :: rest) = (x :: r1, y :: r2))
          by (simpl; rewrite E; reflexivity).
        assert (Hms : mergesort (S fuel') (x :: y :: rest)
                       = merge (mergesort fuel' (x :: r1)) (mergesort fuel' (y :: r2))).
        { simpl. rewrite E. reflexivity. }
        rewrite Hms.
        assert (Hlen : length (x :: r1) + length (y :: r2) = length (x :: y :: rest))
          by (apply (split_length (x::y::rest) (x::r1) (y::r2) Hsl)).
        assert (Hle1 : length (x :: r1) <= fuel') by (simpl in Hle, Hlen; simpl; lia).
        assert (Hle2 : length (y :: r2) <= fuel') by (simpl in Hle, Hlen; simpl; lia).
        assert (Hp1 : Permutation (x :: r1) (mergesort fuel' (x :: r1)))
          by (apply IH; exact Hle1).
        assert (Hp2 : Permutation (y :: r2) (mergesort fuel' (y :: r2)))
          by (apply IH; exact Hle2).
        eapply Permutation_trans.
        { apply (split_perm (x::y::rest) (x::r1) (y::r2) Hsl). }
        eapply Permutation_trans.
        { apply (Permutation_app Hp1 Hp2). }
        apply merge_perm.
Qed.

(** ** Sortedness helper lemmas *)

Definition le_all (a : nat) (l : list nat) : Prop :=
  forall y, In y l -> a <= y.

Lemma le_all_le : forall a b l, a <= b -> le_all b l -> le_all a l.
Proof.
  intros a b l Hab Hbl. unfold le_all in *. intros y Hin. specialize (Hbl y Hin). lia.
Qed.

Lemma le_all_head : forall a b l, le_all a (b :: l) -> a <= b.
Proof.
  intros a b l H. unfold le_all in H. apply H. left. reflexivity.
Qed.

Lemma le_all_tail : forall a b l, le_all a (b :: l) -> le_all a l.
Proof.
  intros a b l H. unfold le_all in *. intros y Hin. apply H. right. exact Hin.
Qed.

Lemma le_all_cons : forall a b l, a <= b -> le_all a l -> le_all a (b :: l).
Proof.
  intros a b l Hab Hl. unfold le_all in *. intros y Hin. destruct Hin as [Hy | Hin'].
  - subst y. exact Hab.
  - apply Hl. exact Hin'.
Qed.

Lemma sorted_cons_inv : forall x y l, sorted (x :: y :: l) -> x <= y /\ sorted (y :: l).
Proof.
  intros x y l Hs. inversion Hs; subst. split; assumption.
Qed.

Lemma sorted_tail : forall x l, sorted (x :: l) -> sorted l.
Proof.
  intros x l Hs. destruct l as [| h t].
  - apply sorted_nil.
  - destruct (sorted_cons_inv x h t Hs) as [_ Hst]. exact Hst.
Qed.

Lemma sorted_le_all : forall l x, sorted (x :: l) -> le_all x l.
Proof.
  induction l as [| h t IH]; intros x Hs.
  - intros y Hin. destruct Hin.
  - destruct (sorted_cons_inv x h t Hs) as [Hxh Hst].
    unfold le_all. intros y Hin. destruct Hin as [Hy | Hin'].
    + subst y. exact Hxh.
    + exact (le_all_le x h t Hxh (IH h Hst) y Hin').
Qed.

Lemma sorted_le_all_cons : forall l x, sorted (x :: l) -> le_all x (x :: l).
Proof.
  intros l x Hs. apply le_all_cons.
  - lia.
  - apply (sorted_le_all l x Hs).
Qed.

Lemma sorted_cons_le_all : forall x l, le_all x l -> sorted l -> sorted (x :: l).
Proof.
  intros x l Hle Hs. destruct l as [| h t].
  - apply sorted_singleton.
  - apply sorted_cons.
    + apply (le_all_head x h t Hle).
    + exact Hs.
Qed.

Lemma merge_le_all : forall a l1 l2, le_all a l1 -> le_all a l2 -> le_all a (merge l1 l2).
Proof.
  intros a l1. induction l1 as [| x xs IH]; intros l2 H1 H2.
  - simpl. exact H2.
  - induction l2 as [| y ys IH2].
    + simpl. exact H1.
    + simpl. destruct (x <=? y) eqn:Hxy.
      * apply le_all_cons.
        { exact (le_all_head a x xs H1). }
        { exact (IH (y :: ys) (le_all_tail a x xs H1) H2). }
      * apply le_all_cons.
        { exact (le_all_head a y ys H2). }
        { exact (IH2 (le_all_tail a y ys H2)). }
Qed.

Lemma merge_sorted : forall l1 l2, sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  intros l1. induction l1 as [| x xs IH]; intros l2 Hs1 Hs2.
  - simpl. exact Hs2.
  - induction l2 as [| y ys IH2].
    + simpl. exact Hs1.
    + simpl. destruct (x <=? y) eqn:Hxy.
      * apply Nat.leb_le in Hxy.
        apply sorted_cons_le_all.
        { exact (merge_le_all x xs (y :: ys)
                  (sorted_le_all xs x Hs1)
                  (le_all_le x y (y :: ys) Hxy (sorted_le_all_cons ys y Hs2))). }
        { exact (IH (y :: ys) (sorted_tail x xs Hs1) Hs2). }
      * apply Nat.leb_gt in Hxy.
        assert (Hyx : y <= x) by lia.
        apply sorted_cons_le_all.
        { exact (merge_le_all y (x :: xs) ys
                  (le_all_le y x (x :: xs) Hyx (sorted_le_all_cons xs x Hs1))
                  (sorted_le_all ys y Hs2)). }
        { exact (IH2 (sorted_tail y ys Hs2)). }
Qed.

Lemma mergesort_sorted_gen : forall fuel l, length l <= fuel -> sorted (mergesort fuel l).
Proof.
  induction fuel as [| fuel' IH]; intros l Hle.
  - destruct l as [| x l'].
    + simpl. apply sorted_nil.
    + simpl in Hle. lia.
  - destruct l as [| x l'].
    + simpl. apply sorted_nil.
    + destruct l' as [| y rest].
      * simpl. apply sorted_singleton.
      * destruct (split rest) as [r1 r2] eqn:E.
        assert (Hsl : split (x :: y :: rest) = (x :: r1, y :: r2))
          by (simpl; rewrite E; reflexivity).
        assert (Hms : mergesort (S fuel') (x :: y :: rest)
                       = merge (mergesort fuel' (x :: r1)) (mergesort fuel' (y :: r2))).
        { simpl. rewrite E. reflexivity. }
        rewrite Hms.
        assert (Hlen : length (x :: r1) + length (y :: r2) = length (x :: y :: rest))
          by (apply (split_length (x::y::rest) (x::r1) (y::r2) Hsl)).
        assert (Hle1 : length (x :: r1) <= fuel') by (simpl in Hle, Hlen; simpl; lia).
        assert (Hle2 : length (y :: r2) <= fuel') by (simpl in Hle, Hlen; simpl; lia).
        assert (Hs1 : sorted (mergesort fuel' (x :: r1))) by (apply IH; exact Hle1).
        assert (Hs2 : sorted (mergesort fuel' (y :: r2))) by (apply IH; exact Hle2).
        apply merge_sorted; [exact Hs1 | exact Hs2].
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem mergesort_sorted : forall l,
  sorted (mergesort (length l) l).
Proof.
  intros l. apply (mergesort_sorted_gen (length l) l (Nat.le_refl _)).
Qed.

Theorem mergesort_sorted_neg : ~ (forall l,
  sorted (mergesort (length l) l)).
Proof.
Admitted.

Theorem mergesort_perm : forall l,
  Permutation l (mergesort (length l) l).
Proof.
  intros l. apply (mergesort_perm_gen (length l) l (Nat.le_refl _)).
Qed.

Theorem mergesort_perm_neg : ~ (forall l,
  Permutation l (mergesort (length l) l)).
Proof.
Admitted.
