From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import AxiomanderLang AxiomanderWp.

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
Admitted.

Lemma dict_lookup_insert_ne : forall kvs k k' v,
  k <> k' ->
  dict_lookup_str k (dict_insert_str k' v kvs) = dict_lookup_str k kvs.
Proof.
Admitted.

End spec_prelude.
