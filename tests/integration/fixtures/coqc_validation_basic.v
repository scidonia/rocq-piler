(* Fixture for coqc validation tests *)
Lemma good_proof : 1 = 1.
Proof. reflexivity. Qed.

Lemma bad_proof : 1 = 2.
Proof.
  reflexivity.
Qed.
