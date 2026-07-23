From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SnakeletExnLang SnakeletExnWp.

(** Shared prelude for generated obligations: LitDict helpers.

    Generated files Require Import this; the helpers and their lemmas
    are proven once here instead of re-emitted per contract. *)

Section spec_prelude.
Context `{FC : FunCtx}.

Fixpoint dict_lookup_str (k : string) (kvs : list (sn_val * sn_val))
    : option sn_val :=
  match kvs with
  | [] => None
  | (LitString k', v) :: rest =>
      if String.eqb k k' then Some v else dict_lookup_str k rest
  | _ :: rest => dict_lookup_str k rest
  end.

Fixpoint dict_insert_str (k : string) (v : sn_val)
    (kvs : list (sn_val * sn_val)) : list (sn_val * sn_val) :=
  match kvs with
  | [] => [(LitString k, v)]
  | (LitString k', v') :: rest =>
      if String.eqb k k' then (LitString k, v) :: rest
      else (LitString k', v') :: dict_insert_str k v rest
  | kv :: rest => kv :: dict_insert_str k v rest
  end.

Lemma dict_lookup_insert_eq : forall kvs k v,
  dict_lookup_str k (dict_insert_str k v kvs) = Some v.
Proof.
  induction kvs as [|kv rest IH]; intros k v; simpl.
  - rewrite String.eqb_refl. reflexivity.
  - destruct kv as [k0 v0].
    destruct k0 as [| | s | | | | | | | |]; simpl; try apply IH.
    destruct (String.eqb k s) eqn:E; simpl.
    + rewrite String.eqb_refl. reflexivity.
    + rewrite E. apply IH.
Qed.

Lemma dict_lookup_insert_ne : forall kvs k k' v,
  k <> k' ->
  dict_lookup_str k (dict_insert_str k' v kvs) = dict_lookup_str k kvs.
Proof.
  induction kvs as [|kv rest IH]; intros k k' v Hne; simpl.
  - destruct (String.eqb k k') eqn:E; simpl; auto.
    apply String.eqb_eq in E. contradiction.
  - destruct kv as [k0 v0].
    destruct k0 as [| | s | | | | | | | |]; simpl.
    1-2,4-11: apply (IH k k' v Hne).
    destruct (String.eqb k' s) eqn:E1; simpl.
    + apply String.eqb_eq in E1. subst s.
      destruct (String.eqb k k') eqn:E2; simpl.
      * apply String.eqb_eq in E2. subst k'. contradiction.
      * reflexivity.
    + destruct (String.eqb k s) eqn:E2; simpl.
      * reflexivity.
      * apply (IH k k' v Hne).
Qed.

End spec_prelude.
