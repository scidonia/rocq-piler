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

(** * Merge helper lemmas *)

Lemma merge_nil l2 : merge [] l2 = l2.
Proof. reflexivity. Qed.

Lemma merge_cons_nil x xs : merge (x :: xs) [] = x :: xs.
Proof. reflexivity. Qed.

Lemma merge_cons_cons x xs y ys :
  merge (x :: xs) (y :: ys) =
  if x <=? y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys.
Proof.
  simpl.
  destruct (x <=? y) eqn:H; auto.
Qed.

(** * Sorted helper lemmas *)

Lemma sorted_inv x l : sorted (x :: l) -> sorted l.
Proof.
  intros H.
  inversion H as [| |? ? ? Hle Hs]; subst; auto.
  apply sorted_nil.
Qed.

Lemma sorted_head_le x y l : sorted (x :: y :: l) -> x <= y.
Proof.
  intros H.
  inversion H as [| |? ? ? Hle Hs]; subst; auto.
Qed.

Lemma sorted_all_ge a l : sorted (a :: l) -> forall b, In b l -> a <= b.
Proof.
  induction l as [|h t IH] in a |- *.
  - intros H b Hb; inversion Hb.
  - intros H.
    inversion H as [| |? ? ? Hle Hs]; subst.
    intros b [Hb | Hb].
    + subst; auto.
    + specialize (IH h Hs).
      apply (PeanoNat.Nat.le_trans _ _ _ Hle).
      apply IH; exact Hb.
Qed.

Lemma sorted_cons_any a l : sorted l -> (forall b, In b l -> a <= b) -> sorted (a :: l).
Proof.
  destruct l as [|h t].
  - intros _ _. apply sorted_singleton.
  - intros Hs Hall.
    apply sorted_cons.
    + apply Hall. left; reflexivity.
    + assumption.
Qed.

(** * Merge elements and In *)

Lemma In_merge a l1 l2 : In a (merge l1 l2) -> In a l1 \/ In a l2.
Proof.
  generalize dependent l2.
  induction l1 as [|x xs IH]; intros l2 H.
  - rewrite merge_nil in H; auto.
  - induction l2 as [|y ys IHl2] in H |- *.
    + rewrite merge_cons_nil in H; auto.
    + rewrite merge_cons_cons in H.
      destruct (x <=? y) eqn:Hcmp; simpl in H.
      * destruct H as [H|H]; [left; left; auto|].
        apply IH in H as [H'|H']; [left; right; auto|right; auto].
      * destruct H as [H|H]; [right; left; auto|].
        apply IHl2 in H as [H'|H']; [left; auto|right; right; auto].
Qed.

Lemma merge_all_ge a l1 l2 :
  (forall b, In b l1 -> a <= b) ->
  (forall b, In b l2 -> a <= b) ->
  forall b, In b (merge l1 l2) -> a <= b.
Proof.
  intros H1 H2 b Hb.
  apply In_merge in Hb as [Hb|Hb]; auto.
Qed.

(** * Merge produces a sorted list *)

Lemma merge_sorted l1 l2 : sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  induction l1 as [|x xs IH] in l2 |- *.
  - intros _ Hs2; rewrite merge_nil; assumption.
  - induction l2 as [|y ys IHl2].
    + intros Hs1 _; rewrite merge_cons_nil; assumption.
    + intros Hs1 Hs2.
      rewrite merge_cons_cons.
      destruct (x <=? y) eqn:Hcmp.
      * apply Nat.leb_le in Hcmp.
        apply sorted_cons_any.
        { apply IH; [apply sorted_inv in Hs1|]; auto. }
        { apply merge_all_ge.
          { intros z Hz. apply (sorted_all_ge _ _ Hs1); auto. }
          { intros z Hz. destruct Hz as [Hz|Hz]; [subst; auto|].
            apply (sorted_all_ge _ _ Hs2) in Hz.
            eapply PeanoNat.Nat.le_trans; eauto. } }
      * apply Nat.leb_gt in Hcmp.
        apply sorted_cons_any.
        { apply IHl2; [|apply sorted_inv in Hs2]; auto. }
        { apply merge_all_ge.
          { intros z Hz. destruct Hz as [Hz|Hz].
            - subst. apply Nat.lt_le_incl; assumption.
            - apply (sorted_all_ge _ _ Hs1) in Hz.
              apply PeanoNat.Nat.le_trans with x; auto.
              apply Nat.lt_le_incl; assumption. }
          { intros z Hz. apply (sorted_all_ge _ _ Hs2); auto. } }
Qed.

(** * Split lemmas *)

Lemma split_length_fst l : length (fst (split l)) <= length l.
Proof.
  refine ((fix F l : length (fst (split l)) <= length l :=
    match l with
    | [] => _
    | [x] => _
    | x :: y :: rest => _
    end) l).
  - simpl; lia.
  - simpl; lia.
  - simpl.
    case_eq (split rest); intros a b E.
    simpl.
    apply le_n_S.
    apply Nat.le_trans with (length rest).
    + apply (f_equal fst) in E. simpl in E. rewrite <- E. apply F.
    + lia.
Qed.

Lemma split_length_snd l : length (snd (split l)) <= length l.
Proof.
  refine ((fix F l : length (snd (split l)) <= length l :=
    match l with
    | [] => _
    | [x] => _
    | x :: y :: rest => _
    end) l).
  - simpl; lia.
  - simpl; lia.
  - simpl.
    case_eq (split rest); intros a b E.
    simpl.
    apply le_n_S.
    apply Nat.le_trans with (length rest).
    + apply (f_equal snd) in E. simpl in E. rewrite <- E. apply F.
    + lia.
Qed.

(** * Permutation for split and merge *)

Lemma split_perm l : Permutation l ((fst (split l)) ++ (snd (split l))).
Proof.
  refine ((fix F l : Permutation l ((fst (split l)) ++ (snd (split l))) :=
    match l with
    | [] => _
    | [x] => _
    | x :: y :: rest => _
    end) l).
  - simpl. apply Permutation_refl.
  - simpl. apply Permutation_refl.
  - simpl.
    case_eq (split rest); intros a b E.
    simpl.
    apply Permutation_trans with (l' := x :: y :: (a ++ b)).
    + apply perm_skip. apply perm_skip.
      pose proof (f_equal fst E) as Hfst. simpl in Hfst.
      pose proof (f_equal snd E) as Hsnd. simpl in Hsnd.
      rewrite <- Hfst, <- Hsnd.
      apply F.
    + apply perm_skip.
      apply Permutation_app_swap_app with (l1 := [y]) (l2 := a) (l3 := b).
Qed.

Lemma merge_perm l1 l2 : Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction l1 as [|x xs IH] in l2 |- *.
  - rewrite merge_nil. apply Permutation_refl.
  - induction l2 as [|y ys IHl2].
    + rewrite merge_cons_nil, app_nil_r. apply Permutation_refl.
    + rewrite merge_cons_cons.
      destruct (x <=? y) eqn:Hcmp.
      * simpl. apply perm_skip. apply IH.
      * rewrite <- app_comm_cons.
        apply Permutation_trans with (l' := x :: y :: xs ++ ys).
        { apply perm_skip. apply Permutation_app_swap_app with (l1 := xs) (l2 := [y]) (l3 := ys). }
        apply Permutation_trans with (l' := y :: x :: xs ++ ys).
        { apply perm_swap. }
        apply perm_skip.
        rewrite app_comm_cons. apply IHl2.
Qed.

(** * Main correctness lemmas *)

Lemma mergesort_sorted_fuel n l : length l <= n -> sorted (mergesort n l).
Proof.
  revert l. induction n as [|n' IH]; intros l Hlen.
  - destruct l; simpl; try apply sorted_nil. inversion Hlen.
  - destruct l as [|x l'].
    { simpl. apply sorted_nil. }
    destruct l' as [|y l''].
    { simpl. apply sorted_singleton. }
    simpl in Hlen.
    simpl.
    destruct (split l'') as [l1 l2] eqn:E.
    simpl.
    apply merge_sorted.
    + apply IH.
      apply Nat.le_trans with (S (length l'')).
      * simpl. apply le_n_S.
        pose proof (f_equal fst E) as Hfst. simpl in Hfst. rewrite <- Hfst.
        apply split_length_fst.
      * lia.
    + apply IH.
      apply Nat.le_trans with (S (length l'')).
      * simpl. apply le_n_S.
        pose proof (f_equal snd E) as Hsnd. simpl in Hsnd. rewrite <- Hsnd.
        apply split_length_snd.
      * lia.
Qed.

Lemma mergesort_perm_fuel n l : length l <= n -> Permutation l (mergesort n l).
Proof.
  revert l. induction n as [|n' IH]; intros l Hlen.
  - destruct l; simpl.
    + apply Permutation_refl.
    + inversion Hlen.
  - destruct l as [|x l'].
    { simpl. apply Permutation_refl. }
    destruct l' as [|y l''].
    { simpl. apply Permutation_refl. }
    simpl in Hlen.
    destruct (split l'') as [l1 l2] eqn:E.
    apply Permutation_trans with (l' := (fst (split (x :: y :: l''))) ++ (snd (split (x :: y :: l'')))).
    { apply split_perm. }
    simpl. rewrite E.
    change (fst (x :: l1, y :: l2)) with (x :: l1).
    change (snd (x :: l1, y :: l2)) with (y :: l2).
    replace (mergesort (S n') (x :: y :: l''))
      with (merge (mergesort n' (x :: l1)) (mergesort n' (y :: l2))).
    2: { simpl. rewrite E. reflexivity. }
    apply Permutation_trans with (l' := (mergesort n' (x :: l1)) ++ (mergesort n' (y :: l2))).
    { apply Permutation_app.
      - apply IH.
        apply Nat.le_trans with (S (length l'')).
        + simpl. apply le_n_S. pose proof (f_equal fst E) as Hf. simpl in Hf. rewrite <- Hf. apply split_length_fst.
        + lia.
      - apply IH.
        apply Nat.le_trans with (S (length l'')).
        + simpl. apply le_n_S. pose proof (f_equal snd E) as Hs. simpl in Hs. rewrite <- Hs. apply split_length_snd.
        + lia. }
    apply merge_perm.
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Theorem mergesort_sorted : forall l,
  sorted (mergesort (length l) l).
Proof.
  intro l. apply mergesort_sorted_fuel with (n := length l). lia.
Qed.

Theorem mergesort_sorted_neg : ~ (forall l,
  sorted (mergesort (length l) l)).
Proof.
Admitted.

Theorem mergesort_perm : forall l,
  Permutation l (mergesort (length l) l).
Proof.
  intro l. apply mergesort_perm_fuel with (n := length l). lia.
Qed.

Theorem mergesort_perm_neg : ~ (forall l,
  Permutation l (mergesort (length l) l)).
Proof.
Admitted.
