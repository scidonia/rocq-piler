(** * Dict Model — pure-functional dictionary with map-like semantics.

    Models dicts as functions Z → Z where 0 means "key absent".
    Provides lemmas that can be used in WP proofs for CDictSet/CDictGet.

    This is the semantic layer: proofs reason about the functional model,
    and the operational IMP commands implement it via the flat state encoding.
 *)

From Stdlib Require Import ZArith String List.
From Stdlib Require Import Sets.Ensembles.
Import ListNotations.
Open Scope Z_scope.

Definition dict : Type := Z -> Z.

Definition empty_dict : dict := fun _ => 0%Z.

Definition dict_get (d : dict) (k : Z) : Z := d k.

Definition dict_set (d : dict) (k v : Z) : dict :=
  fun k' => if Z.eqb k k' then v else d k'.

Definition dict_has (d : dict) (k : Z) : Prop := dict_get d k <> 0.

Definition dict_count (d : dict) : Z :=
  (* countable — number of keys with non-zero entries *)
  0%Z.

(** ** Basic lemmas *)

Lemma dict_set_eq : forall d k v,
    dict_get (dict_set d k v) k = v.
Proof.
  intros. unfold dict_get, dict_set.
  rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma dict_set_ne : forall d k k' v, k <> k' ->
    dict_get (dict_set d k v) k' = dict_get d k'.
Proof.
  intros. unfold dict_get, dict_set.
  apply Z.eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma dict_set_has : forall d k v, v <> 0 ->
    dict_has (dict_set d k v) k.
Proof.
  intros. unfold dict_has. rewrite dict_set_eq. exact H.
Qed.

Lemma dict_set_preserves_other : forall d k v k',
    k <> k' -> dict_has d k' -> dict_has (dict_set d k v) k'.
Proof.
  unfold dict_has. intros. rewrite dict_set_ne; auto.
Qed.

Lemma empty_dict_get : forall k, dict_get empty_dict k = 0.
Proof.
  intros. unfold dict_get, empty_dict. reflexivity.
Qed.

Lemma empty_dict_nohas : forall k, ~ dict_has empty_dict k.
Proof.
  intros k H. unfold dict_has in H. rewrite empty_dict_get in H. auto.
Qed.
