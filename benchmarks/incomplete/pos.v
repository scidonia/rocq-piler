(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import List Arith Lia.
From Stdlib Require Fin.

  Require Import utils.

Set Implicit Arguments.

(* @DLW: former definition

Inductive pos : nat -> Set :=
  | pos_fst : forall n, pos (S n)
  | pos_nxt : forall n, pos n -> pos (S n).

Arguments pos_fst {n}.
Arguments pos_nxt {n}.

*)

Abbreviation pos := Fin.t.
Abbreviation pos_fst := Fin.F1.
Abbreviation pos_nxt := Fin.FS.

Abbreviation pos0  := (@pos_fst _).
Abbreviation pos1  := (pos_nxt pos0).
Abbreviation pos2  := (pos_nxt pos1).
Abbreviation pos3  := (pos_nxt pos2).
Abbreviation pos4  := (pos_nxt pos3).
Abbreviation pos5  := (pos_nxt pos4).
Abbreviation pos6  := (pos_nxt pos5).
Abbreviation pos7  := (pos_nxt pos6).
Abbreviation pos8  := (pos_nxt pos7).
Abbreviation pos9  := (pos_nxt pos8).
Abbreviation pos10 := (pos_nxt pos9).
Abbreviation pos11 := (pos_nxt pos10).
Abbreviation pos12 := (pos_nxt pos11).
Abbreviation pos13 := (pos_nxt pos12).
Abbreviation pos14 := (pos_nxt pos13).
Abbreviation pos15 := (pos_nxt pos14).
Abbreviation pos16 := (pos_nxt pos15).
Abbreviation pos17 := (pos_nxt pos16).
Abbreviation pos18 := (pos_nxt pos17).
Abbreviation pos19 := (pos_nxt pos18).
Abbreviation pos20 := (pos_nxt pos19).

Definition pos_iso n m : n = m -> pos n -> pos m.
Proof. intros []; auto. Admitted.

Section pos_inv.

  Let pos_inv_t n := 
    match n as x return pos x -> Set with 
      | 0   => fun _ => False 
      | S n => fun i => (( i = pos_fst ) + { p | i = pos_nxt p })%type
    end.

  Let pos_inv : forall n p, @pos_inv_t n p.
  Proof.
  Admitted.

  Definition pos_O_inv : pos 0 -> False.
  Proof. apply pos_inv. Admitted.

  Definition pos_S_inv n (p : pos (S n)) : ( p = pos_fst ) + { q | p = pos_nxt q }.
  Proof. apply (pos_inv p). Admitted.

  Definition pos_nxt_inj n (p q : pos n) (H : pos_nxt p = pos_nxt q) : p = q :=
    match H in _ = a return 
       match a as a' in pos m return 
           match m with 
             | 0 => Prop 
             | S n' => pos n' -> Prop 
           end with
         | pos_fst   => fun _  => True 
         | pos_nxt y => fun x' => x' = y 
       end p with 
     | eq_refl => eq_refl
   end.

End pos_inv.

Arguments pos_S_inv {n} p /.

Section pos_invert.

  (* Position inversion, "singleton elimination" free version 
     One problem remains to fully use it ... it is not
     correctly traversed by type checking algorithm
     of fixpoints (structural recursion)
     
     pos_S_inv work better in that respect 
  *)

  Let pos_invert_t n : (pos n -> Type) -> Type :=
    match n with
        0   => fun P => True
      | S n => fun P => (P (pos_fst) * forall p, P (pos_nxt p))%type
    end.

  Let pos_invert n : forall (P : pos n -> Type), pos_invert_t P -> forall p, P p.
  Proof.
  Admitted.
  
  Theorem pos_O_invert X : pos 0 -> X.
  Proof.
  Admitted.

  Theorem pos_S_invert n P : P (@pos_fst n) -> (forall p, P (pos_nxt p)) -> forall p, P p.
  Proof.
  Admitted.
  
End pos_invert.

Arguments pos_S_invert [n] P _ _ p /.

Ltac pos_O_inv p := exfalso; apply (pos_O_inv p).

Ltac pos_S_inv p := 
  let H := fresh in
  let q := fresh
  in  rename p into q; destruct (pos_S_inv q) as [ H | (p & H) ]; subst q.
 
(* 
Ltac pos_O_inv p := apply (@pos_O_invert _ p).
Ltac pos_S_inv x := induction x as [ | x ] using pos_S_invert.
*)

Ltac pos_inv p :=   
  match goal with
    | [ H: pos 0     |- _ ] => match H with p => pos_O_inv p end
    | [ H: pos (S _) |- _ ] => match H with p => pos_S_inv p end
  end.

Tactic Notation "invert" "pos" hyp(H) := pos_inv H; simpl.

Ltac analyse_pos p := 
  match type of p with
    | pos 0     => pos_inv p
    | pos (S _) => pos_inv p; [ | try analyse_pos p ]
  end. 

Tactic Notation "analyse" "pos" hyp(p) := analyse_pos p.

Definition pos_O_any X : pos 0 -> X.
Proof. intro p; invert pos p. Admitted.

Definition pos_eq_dec n (x y : pos n) : { x = y } + { x <> y }.
Proof.
Admitted.

Fixpoint pos_left n m (p : pos n) : pos (n+m) :=
  match p with
    | pos_fst   => pos_fst
    | pos_nxt p => pos_nxt (pos_left m p)
  end.

Fixpoint pos_right n m : pos m -> pos (n+m) :=
  match n with 
    | 0   => fun x => x
    | S n => fun p => pos_nxt (pos_right n p)
  end.

Definition pos_both n m : pos (n+m) -> pos n + pos m.
Proof.
Admitted.

Definition pos_lr n m : pos n + pos m -> pos (n+m).
Proof.
Admitted.

Fact pos_both_left n m p : @pos_both n m (@pos_left n m p) = inl p.
Proof.
Admitted.

Fact pos_both_right n m p : @pos_both n m (@pos_right n m p) = inr p.
Proof.
Admitted.

Fact pos_left_right_neq n m p q : @pos_left n m p <> @pos_right n m q.
Proof.
Admitted.

Fact pos_left_inj n m p q : @pos_left n m p = @pos_left n m q -> p = q.
Proof.
Admitted.

Fact pos_right_inj n m p q : @pos_right n m p = @pos_right n m q -> p = q.
Proof.
Admitted.

(* A bijection between pos n + pos m <-> pos (n+m) **)

Fact pos_both_lr n m p : @pos_both n m (pos_lr p) = p.
Proof.
Admitted.

Fact pos_lr_both n m p : pos_lr (@pos_both n m p) = p.
Proof.
Admitted.

Section pos_left_right_rect.

  Variable (n m : nat) (P : pos (n+m) -> Type).

  Hypothesis (HP1 : forall p, P (pos_left _ p))
             (HP2 : forall p, P (pos_right _ p)).

  Theorem pos_left_right_rect : forall p, P p.
  Proof using HP1 HP2.
  Admitted.

End pos_left_right_rect.

Fixpoint pos_list n : list (pos n) :=
  match n with
    | 0   => nil
    | S n => pos0::map pos_nxt (pos_list n) 
  end.

Fact pos_list_prop n p : In p (pos_list n).
Proof.
Admitted.

Fact pos_list_length n : length (pos_list n) = n.
Proof.
Admitted.

Fact pos_list_NoDup n : NoDup (pos_list n).
Proof.
Admitted.

Section pos_map.

  Definition pos_map m n := pos m -> pos n.
 
  Definition pm_ext_eq m n (r1 r2 : pos_map m n) := forall p, r1 p = r2 p.  

  Definition pm_lift m n (r : pos_map m n) : pos_map (S m) (S n).
  Proof.
  Admitted.
  
  Fact pm_lift_fst m n (r : pos_map m n) : pm_lift r pos0 = pos0.
  Proof. auto. Admitted.
  
  Fact pm_lift_nxt m n (r : pos_map m n) p : pm_lift r (pos_nxt p) = pos_nxt (r p).
  Proof. auto. Admitted.

  Arguments pm_lift [ m n ] r p.

  Fact pm_lift_ext m n r1 r2 : @pm_ext_eq m n r1 r2 -> pm_ext_eq (pm_lift r1) (pm_lift r2). 
  Proof.
  Admitted.

  Definition pm_comp l m n : pos_map l m -> pos_map m n -> pos_map l n.
  Proof.
  Admitted.
 
  Fact pm_comp_lift l m n r s : pm_ext_eq (pm_lift (@pm_comp l m n r s)) (pm_comp (pm_lift r) (pm_lift s)).
  Proof.
  Admitted.

  Definition pm_id n : pos_map n n := fun p => p.

End pos_map.

Arguments pm_lift { m n } _ _ /.
Arguments pm_comp [ l m n ] _ _ _ /.
Arguments pm_id : clear implicits.

Section pos_nat.

  Fixpoint pos_nat n (p : pos n) : { i | i < n }.
  Proof.
  Admitted.

  Definition pos2nat n p := proj1_sig (@pos_nat n p).
  
  Fact pos2nat_prop n p : @pos2nat n p < n.
  Proof. apply (proj2_sig (pos_nat p)). Admitted.

  Fixpoint nat2pos n : forall x, x < n -> pos n.
  Proof.
  Admitted.

  Definition nat_pos n : { i | i < n } -> pos n.
  Proof. intros (? & H); revert H; apply nat2pos. Admitted.

  Arguments pos2nat n !p /.

  Fact pos2nat_inj n (p q : pos n) : pos2nat p = pos2nat q -> p = q.
  Proof.
  Admitted.

  Fact pos2nat_nat2pos n i (H : i < n) : pos2nat (nat2pos H) = i.
  Proof.
  Admitted.
  
  Fact nat2pos_pos2nat n p (H : pos2nat p < n) : nat2pos H = p.
  Proof.
  Admitted.
  
  Fact pos2nat_fst n : pos2nat (@pos_fst n) = 0.
  Proof. auto. Admitted.
  
  Fact pos2nat_nxt n p : pos2nat (@pos_nxt n p) = S (pos2nat p).
  Proof. auto. Admitted.

  Fact pos2nat_left n m p : pos2nat (@pos_left n m p) = pos2nat p.
  Proof. induction p; simpl; auto. Admitted.

  Fact pos2nat_right n m p : pos2nat (@pos_right n m p) = n+pos2nat p.
  Proof.
  Admitted.

  Fixpoint pos_sub n (p : pos n) { struct p } : forall m, n < m -> pos m.
  Proof.
  Admitted.
  
  Fact pos_sub2nat n p m Hm : pos2nat (@pos_sub n p m Hm) = pos2nat p.
  Proof.
  Admitted.
  
End pos_nat.

Global Opaque pos_nat.

Fact pos_list2nat n : map (@pos2nat n) (pos_list n) = list_an 0 n.
Proof.
Admitted.

Section pos_prod.
  
  Variable n : nat.
  
  Let ll := flat_map (fun p => map (fun q => (p,q)) (pos_list n)) (pos_list n).
  Let ll_prop p q : In (p,q) ll.
  Proof. 
  Admitted.
  
  Definition pos_not_diag := filter (fun c => if pos_eq_dec (fst c) (snd c) then false else true) ll.

  Fact pos_not_diag_spec p q : In (p,q) pos_not_diag <-> p <> q.
  Proof.
  Admitted.
  
End pos_prod.
