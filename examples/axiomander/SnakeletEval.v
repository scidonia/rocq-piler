From stdpp Require Import gmap.
Require Import SnakeletLang.

Fixpoint eval_pure (fuel : nat) (e : sn_expr) : option sn_expr :=
  match fuel with
  | O => None
  | S fuel' =>
      match to_val e with
      | Some v => Some e
      | None =>
          match e with
          | Let x e1 e2 =>
              match eval_pure fuel' e1 with
              | Some (Val v) => eval_pure fuel' (subst x v e2)
              | _ => None
              end
          | BinOp op (Val v1) (Val v2) =>
              Some (Val (binop_eval op v1 v2))
          | BinOp op e1 e2 =>
              match eval_pure fuel' e1 with
              | Some (Val v1) =>
                  match eval_pure fuel' e2 with
                  | Some (Val v2) =>
                      Some (Val (binop_eval op v1 v2))
                  | _ => None
                  end
              | _ => None
              end
          | If (Val (LitBool true)) e1 e2 =>
              eval_pure fuel' e1
          | If (Val (LitBool false)) e1 e2 =>
              eval_pure fuel' e2
          | If c e1 e2 =>
              match eval_pure fuel' c with
              | Some (Val (LitBool true)) => eval_pure fuel' e1
              | Some (Val (LitBool false)) => eval_pure fuel' e2
              | _ => None
              end
          | _ => None
          end
      end
  end.
