From Stdlib Require Import Arith List Lia.
Import ListNotations.

Lemma correct_proof : forall n, n + 0 = n.
Proof. intros. lia. Qed.

Lemma tactic_error : forall n m, n + m = m + n.
Proof. intros. destruct n. auto. apply nonexistent_lemma.
   { (* tactic_error:813cbe3c *) admit. }
Admitted.

Definition good_def (n : nat) : nat := n + 1.

Lemma type_mismatch : forall n : nat, n = true.
Proof. intros. reflexivity.
   { (* type_mismatch:unknown *) admit. }
Admitted.

Lemma admitted_proof : forall n, n * 1 = n.
Proof. Admitted.

Lemma late_error : forall l : list nat, length (rev l) = length l.
Proof. intros. induction l. simpl. auto. simpl. rewrite app_length. simpl. lia_notactic.
   { (* late_error:unknown *) admit. }
Admitted.

Lemma another_correct : forall n, 0 + n = n.
Proof. intros. simpl. reflexivity. Qed.
