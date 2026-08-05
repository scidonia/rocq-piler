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

(** Helper lemmas *)

Lemma split_perm : forall l,
  Permutation (fst (split l) ++ snd (split l)) l.
Proof.
  fix F 1.
  intros l.
  destruct l as [|h t].
  - simpl. apply Permutation_refl.
  - destruct t as [|h' t'].
    + simpl. apply Permutation_refl.
    + simpl.
      destruct (split t') as [l1 l2] eqn:Hsplit; simpl.
      eapply Permutation_trans.
      * apply perm_skip.
        apply Permutation_sym.
        apply Permutation_middle.
      * apply perm_skip. apply perm_skip.
        pose proof (F t') as Hrec.
        rewrite Hsplit in Hrec. simpl in Hrec.
        apply Hrec.
Qed.

Lemma split_length : forall l l1 l2,
  split l = (l1, l2) -> length l1 + length l2 = length l.
Proof.
  intros l l1 l2 Hsplit.
  pose proof (split_perm l) as Hperm.
  rewrite Hsplit in Hperm. simpl in Hperm.
  apply Permutation_length in Hperm.
  rewrite app_length in Hperm.
  exact Hperm.
Qed.

Lemma split_nonempty_elts : forall x y rest l1 l2,
  split (x :: y :: rest) = (l1, l2) ->
  length l1 >= 1 /\ length l2 >= 1.
Proof.
  intros x y rest l1 l2 H. simpl in H.
  destruct (split rest) as [l1' l2'] eqn:?.
  inversion H; subst. simpl. split; lia.
Qed.

Lemma merge_perm : forall l1 l2,
  Permutation (l1 ++ l2) (merge l1 l2).
Proof.
  induction l1 as [|x xs IHouter].
  - simpl. intros. apply Permutation_refl.
  - induction l2 as [|y ys IHinner].
    + simpl. rewrite app_nil_r. apply Permutation_refl.
    + simpl. destruct (x <=? y) eqn:Heq.
      * simpl. apply perm_skip. apply IHouter.
      * simpl.
        assert (Hmid : Permutation (x :: xs ++ y :: ys) (y :: x :: xs ++ ys)).
        { apply Permutation_sym.
          apply (Permutation_middle (x :: xs) ys y). }
        assert (Hind : Permutation (y :: x :: xs ++ ys) (y :: merge (x :: xs) ys)).
        { apply perm_skip. apply IHinner. }
        eapply Permutation_trans; eassumption.
Qed.

Lemma sorted_head_le : forall x l,
  sorted (x :: l) -> forall y, In y l -> x <= y.
Proof.
  fix F 2.
  intros x l H y Hin.
  destruct l as [|z l'].
  - destruct Hin.
  - inversion H; subst; clear H.
    destruct Hin as [<-|Hz].
    + assumption.
    + apply Nat.le_trans with (m := z).
      * assumption.
      * apply (F z l'); auto.
Qed.

Lemma merge_cons_cons : forall x xs y ys,
  merge (x :: xs) (y :: ys) =
  if x <=? y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma merge_singleton_eq : forall x ys,
  merge [x] ys =
  match ys with
  | [] => [x]
  | y :: ys' => if x <=? y then x :: y :: ys' else y :: merge [x] ys'
  end.
Proof.
  induction ys; simpl; auto.
Qed.

Lemma merge_singleton_nonempty : forall x ys, merge [x] ys <> [].
Proof.
  intros x ys. rewrite merge_singleton_eq.
  destruct ys as [|h t]; simpl.
  - congruence.
  - destruct (x <=? h); congruence.
Qed.

Lemma merge_preserves_lower_bound : forall l1 l2 a,
  (forall b, In b l1 -> a <= b) ->
  (forall b, In b l2 -> a <= b) ->
  forall b, In b (merge l1 l2) -> a <= b.
Proof.
  induction l1 as [|x xs IHouter]; intros l2 a Hbound_l1 Hbound_l2.
  - simpl. intros b Hin. apply Hbound_l2. exact Hin.
  - induction l2 as [|y ys IHinner].
    + simpl. intros b Hin. apply Hbound_l1. exact Hin.
    + rewrite merge_cons_cons.
      intros b Hin.
      destruct (x <=? y) eqn:Heq; simpl in Hin.
      * destruct Hin as [->|Hin'].
        -- apply Hbound_l1. left. reflexivity.
        -- eapply IHouter.
           ++ intros c Hc. apply Hbound_l1. right. exact Hc.
           ++ exact Hbound_l2.
           ++ exact Hin'.
      * destruct Hin as [->|Hin'].
        -- apply Hbound_l2. left. reflexivity.
        -- eapply IHinner.
           ++ intros c Hc. apply Hbound_l2. right. exact Hc.
           ++ exact Hin'.
Qed.

Lemma sorted_cons_nonempty : forall a l,
  l <> [] -> (forall b, In b l -> a <= b) -> sorted l -> sorted (a :: l).
Proof.
  intros a l Hne Hle Hsl.
  destruct l as [|h t].
  - exfalso; apply Hne; reflexivity.
  - apply sorted_cons with (y := h) (l := t); auto.
    apply Hle. left. reflexivity.
Qed.

Lemma merge_nonempty_l1 : forall l1 l2, l1 <> [] -> merge l1 l2 <> [].
Proof.
  intros l1 l2 Hne. induction l1 as [|x xs IH].
  - congruence.
  - simpl. destruct l2 as [|y ys].
    + congruence.
    + destruct (x <=? y); simpl; congruence.
Qed.

Lemma merge_sorted_singleton : forall x l2,
  sorted l2 -> sorted (merge [x] l2).
Proof.
  induction l2 as [|y' ys IHl2]; intros H2.
  - simpl. apply sorted_singleton.
  - rewrite merge_cons_cons.
    destruct (x <=? y') eqn:Hcmp.
    + apply Nat.leb_le in Hcmp. simpl.
      apply sorted_cons with (y := y') (l := merge [] ys).
      * exact Hcmp.
      * simpl. inversion H2; subst; [ apply sorted_singleton | assumption ].
    + apply Nat.leb_gt in Hcmp.
      apply sorted_cons_nonempty with (a := y').
      * apply merge_singleton_nonempty.
      * apply (merge_preserves_lower_bound [x] ys y').
        -- intros b Hb; simpl in Hb; destruct Hb as [<-|Hb'].
           ++ apply Nat.lt_le_incl, Hcmp.
           ++ destruct Hb'.
        -- intros b Hb; inversion H2; subst; eapply sorted_head_le; eauto.
      * apply IHl2; inversion H2; subst; [ apply sorted_nil | assumption ].
Qed.

Lemma merge_sorted : forall l1 l2,
  sorted l1 -> sorted l2 -> sorted (merge l1 l2).
Proof.
  intros l1 l2 H1. revert l2.
  induction H1 as [|x| x y l Hxle Hy_sorted IHy].
  - intros. simpl. assumption.
  - intros. apply merge_sorted_singleton; auto.
  - intros l2 H2. induction l2 as [|y' ys IHl2].
    + simpl. apply sorted_cons with (y := y) (l := l); auto.
    + rewrite merge_cons_cons.
      destruct (x <=? y') eqn:Hcmp.
      * apply Nat.leb_le in Hcmp.
        apply sorted_cons_nonempty with (a := x).
        -- apply merge_nonempty_l1; congruence.
        -- apply (merge_preserves_lower_bound (y :: l) (y' :: ys) x).
           ++ intros b Hb; destruct Hb as [<-|Hb].
              ** assumption.
               ** apply Nat.le_trans with (m := y); [ exact Hxle | eapply sorted_head_le; eauto ].
           ++ intros b Hb; destruct Hb as [<-|Hb].
              ** assumption.
              ** apply Nat.le_trans with (m := y'); [ assumption | eapply sorted_head_le; eauto ].
        -- apply IHy; assumption.
      * apply Nat.leb_gt in Hcmp.
        apply sorted_cons_nonempty with (a := y').
        -- apply merge_nonempty_l1; congruence.
        -- apply (merge_preserves_lower_bound (x :: y :: l) ys y').
           ++ intros b Hb; destruct Hb as [<-|Hb].
              ** apply Nat.lt_le_incl, Hcmp.
              ** destruct Hb as [<-|Hb].
                 --- apply Nat.le_trans with (m := x); [ apply Nat.lt_le_incl, Hcmp | assumption ].
                 --- apply Nat.le_trans with (m := y); [ apply Nat.le_trans with (m := x); [ apply Nat.lt_le_incl, Hcmp | assumption ] | eapply sorted_head_le; eauto ].
           ++ intros b Hb; inversion H2; subst; eapply sorted_head_le; eauto.
        -- apply IHl2; inversion H2; subst; [ apply sorted_nil | assumption ].
Qed.

(** ** Conjecture pairs
    For each conjecture, both the statement and its negation are given.
    Prove exactly one of each pair. *)

Lemma mergesort_sorted_aux : forall fuel l,
  length l <= fuel -> sorted (mergesort fuel l).
Proof.
  induction fuel as [|n IH].
  - intros l Hlen. simpl. destruct l as [|a l'].
    + apply sorted_nil.
    + simpl in Hlen. lia.
  - intros l Hlen. simpl.
    destruct l as [|x [|y rest]].
    + apply sorted_nil.
    + apply sorted_singleton.
    + destruct (split (x :: y :: rest)) as [l1 l2] eqn:Hsplit; simpl.
      apply merge_sorted.
      * apply IH.
        pose proof (split_nonempty_elts x y rest l1 l2 Hsplit) as [Hl1 Hl2].
        pose proof (split_length _ _ _ Hsplit) as Hlen_sum.
        simpl in Hlen. simpl in Hlen_sum.
        assert (length l1 <= n). {
          cut (length l1 + length l2 <= n + length l2). 1: lia.
          rewrite Hlen_sum. lia. }
        exact H.
      * apply IH.
        pose proof (split_nonempty_elts x y rest l1 l2 Hsplit) as [Hl1 Hl2].
        pose proof (split_length _ _ _ Hsplit) as Hlen_sum.
        simpl in Hlen. simpl in Hlen_sum.
        assert (length l2 <= n). {
          cut (length l1 + length l2 <= length l1 + n). 1: lia.
          rewrite Hlen_sum. lia. }
        exact H.
Qed.

Theorem mergesort_sorted : forall l,
  sorted (mergesort (length l) l).
Proof.
  intros l. apply mergesort_sorted_aux. reflexivity.
Qed.

Theorem mergesort_sorted_neg : ~ (forall l,
  sorted (mergesort (length l) l)).
Proof.
Admitted.

Lemma mergesort_perm_aux : forall fuel l,
  length l <= fuel -> Permutation l (mergesort fuel l).
Proof.
  induction fuel as [|n IH].
  - intros l Hlen. simpl. destruct l as [|a l'].
    + apply Permutation_refl.
    + simpl in Hlen. lia.
  - intros l Hlen. simpl.
    destruct l as [|x [|y rest]].
    + apply Permutation_refl.
    + apply Permutation_refl.
    + destruct (split (x :: y :: rest)) as [l1 l2] eqn:Hsplit.
      simpl.
      pose proof (split_perm (x :: y :: rest)) as Hsplit_perm.
      rewrite Hsplit in Hsplit_perm. simpl in Hsplit_perm.
      apply Permutation_trans with (l' := mergesort n l1 ++ mergesort n l2).
      * apply Permutation_trans with (l' := l1 ++ l2).
        -- apply Permutation_sym. exact Hsplit_perm.
        -- apply Permutation_app; apply IH.
           ++ pose proof (split_nonempty_elts x y rest l1 l2 Hsplit) as [Hl1 Hl2].
              pose proof (split_length _ _ _ Hsplit) as Hlen_sum.
              simpl in Hlen. simpl in Hlen_sum.
              assert (length l1 <= n). {
                cut (length l1 + length l2 <= n + length l2). 1: lia.
                rewrite Hlen_sum. lia. }
              exact H.
           ++ pose proof (split_nonempty_elts x y rest l1 l2 Hsplit) as [Hl1 Hl2].
              pose proof (split_length _ _ _ Hsplit) as Hlen_sum.
              simpl in Hlen. simpl in Hlen_sum.
              assert (length l2 <= n). {
                cut (length l1 + length l2 <= length l1 + n). 1: lia.
                rewrite Hlen_sum. lia. }
              exact H.
      * apply merge_perm.
Qed.

Theorem mergesort_perm : forall l,
  Permutation l (mergesort (length l) l).
Proof.
  intros l. apply mergesort_perm_aux. reflexivity.
Qed.

Theorem mergesort_perm_neg : ~ (forall l,
  Permutation l (mergesort (length l) l)).
Proof.
Admitted.
