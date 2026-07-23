From Stdlib Require Import Arith Lia List Permutation.
From Stdlib Require Vector.
From Stdlib Require Fin.

Set Implicit Arguments.
Set Default Goal Selector "!".

Set Implicit Arguments.

(* @DLW: former definition

Inductive pos : nat -> Set :=
  | pos_fst : forall n, pos (S n)
  | pos_nxt : forall n, pos n -> pos (S n).

Arguments pos_fst {n}.
Arguments pos_nxt {n}.

*)

Notation pos := Fin.t.
Notation pos_fst := Fin.F1.
Notation pos_nxt := Fin.FS.

Notation pos0  := (@pos_fst _).
Notation pos1  := (pos_nxt pos0).
Notation pos2  := (pos_nxt pos1).
Notation pos3  := (pos_nxt pos2).
Notation pos4  := (pos_nxt pos3).
Notation pos5  := (pos_nxt pos4).
Notation pos6  := (pos_nxt pos5).
Notation pos7  := (pos_nxt pos6).
Notation pos8  := (pos_nxt pos7).
Notation pos9  := (pos_nxt pos8).
Notation pos10 := (pos_nxt pos9).
Notation pos11 := (pos_nxt pos10).
Notation pos12 := (pos_nxt pos11).
Notation pos13 := (pos_nxt pos12).
Notation pos14 := (pos_nxt pos13).
Notation pos15 := (pos_nxt pos14).
Notation pos16 := (pos_nxt pos15).
Notation pos17 := (pos_nxt pos16).
Notation pos18 := (pos_nxt pos17).
Notation pos19 := (pos_nxt pos18).
Notation pos20 := (pos_nxt pos19).

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

(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib Require Import Arith Lia List Permutation. 
From Stdlib Require Vector.
From Stdlib Require Fin.


Set Implicit Arguments.
Set Default Goal Selector "!".

Notation vec_nil := (@Vector.nil _).
Notation "x ## v" := (@Vector.cons _ x _ v) (at level 60, right associativity).

Section vector.

  Variable X : Type.

  Abbreviation vec := (@Vector.t X).

(* @DLW: former definition

  Inductive vec : nat -> Type :=
    | vec_nil  : vec 0
    | vec_cons : forall n, X -> vec n -> vec (S n).
*)

  Let vec_decomp_type n := 
    match n with
      | 0   => Prop
      | S n => (X * vec n)%type
    end.

  Definition vec_decomp n (v : vec n) :=
    match v in Vector.t _ k return vec_decomp_type k with
      | vec_nil => False
      | x ## v  => (x,v)
    end.
    
  Definition vec_head n (v : vec (S n)) := match v with x ## _ => x end.
  Definition vec_tail n (v : vec (S n)) := match v with _ ## w => w end.

  Let vec_head_tail_type n : vec n -> Prop := 
    match n with
      | 0   => fun v => v = vec_nil
      | S n => fun v => v = vec_head v ## vec_tail v
    end.

  Let vec_head_tail_prop n v :  @vec_head_tail_type n v.
  Proof. Admitted.

  Fact vec_0_nil (v : vec 0) : v = vec_nil.
  Proof. Admitted.

  Fact vec_head_tail n (v : vec (S n)) : v = vec_head v ## vec_tail v.
  Proof. Admitted.

  Fact vec_cons_inv n x y (v w : vec n) : x ## v = y ## w -> x = y /\ v = w.
  Proof.
  Admitted.

  Fixpoint vec_pos n (v : vec n) : pos n -> X.
  Proof.
  Admitted.

  Fact vec_pos0 n (v : vec (S n)) : vec_pos v pos0 = vec_head v.
  Proof. 
  Admitted.
  
  Fact vec_pos_tail n (v : vec (S n)) p : vec_pos (vec_tail v) p = vec_pos v (pos_nxt p).
  Proof.
  Admitted.
  
  Fact vec_pos1 n (v : vec (S (S n))) : vec_pos v pos1 = vec_head (vec_tail v).
  Proof.
  Admitted.

  Fact vec_pos_ext n (v w : vec n) : (forall p, vec_pos v p = vec_pos w p) -> v = w.
  Proof.
  Admitted.

  Fixpoint vec_set_pos n : (pos n -> X) -> vec n :=
    match n return (pos n -> X) -> vec n with 
      | 0   => fun _ => vec_nil
      | S n => fun g => g pos0 ## vec_set_pos (fun p => g (pos_nxt p))
    end.

  Fact vec_pos_set n (g : pos n -> X) p : vec_pos (vec_set_pos g) p = g p. 
  Proof.
  Admitted.

  Fixpoint vec_change n (v : vec n) : pos n -> X -> vec n.
  Proof.
  Admitted.

  Fact vec_change_eq n v p q x : p = q -> vec_pos (@vec_change n v p x) q = x.
  Proof. 
  Admitted.

  Fact vec_change_neq n v p q x : p <> q -> vec_pos (@vec_change n v p x) q = vec_pos v q.
  Proof. 
  Admitted.

  Fact vec_change_idem n v p x y : vec_change (@vec_change n v p x) p y = vec_change v p y.
  Proof.
  Admitted.

  Fact vec_change_same n v p : @vec_change n v p (vec_pos v p) = v.
  Proof.
  Admitted.

  Section vec_eq_dec_pos.

    Fixpoint vec_eq_dec_pos n (u v : vec n) { struct u } :
         (forall p, { vec_pos u p = vec_pos v p } + { vec_pos u p <> vec_pos v p })
      -> { u = v } + { u <> v }.
    Proof.
    Admitted.

  End vec_eq_dec_pos.

  Variable eq_X_dec : forall x y : X, { x = y } + { x <> y }.

  Fact vec_eq_dec n (u v : vec n) : { u = v } + { u <> v }.
  Proof using eq_X_dec. apply vec_eq_dec_pos; auto. Admitted.
  
  Fixpoint vec_list n (v : vec n) := 
    match v with  
      | vec_nil => nil
      | x ## v  => x::vec_list v
    end.

  Fact vec_list_In n v p : In (vec_pos v p) (@vec_list n v).
  Proof.
  Admitted.

  Fact vec_list_vec_set_pos n f : vec_list (@vec_set_pos n f) = map f (pos_list n).
  Proof.
  Admitted.

  Fact map_pos_list_vec n f : map f (pos_list n) = vec_list (@vec_set_pos n f).
  Proof. Admitted.
    
  Fact vec_list_length n v : length (@vec_list n v) = n.
  Proof. Admitted.

  Fixpoint list_vec (l : list X) : vec (length l) := 
    match l with 
      | nil  => vec_nil
      | x::l => x ## list_vec l
    end.

  Fact list_vec_iso l : vec_list (list_vec l) = l.
  Proof. Admitted.

  (* The other part needs a transport *)

  Fact vec_list_iso n v : list_vec (@vec_list n v) = eq_rect_r _ v (vec_list_length v).
  Proof. 
  Admitted.

  Definition list_vec_full l : { v : vec (length l) | vec_list v = l }.
  Proof. Admitted.

  Fact vec_list_inv n v x : In x (@vec_list n v) -> exists p, x = vec_pos v p.
  Proof.
  Admitted.
 
  Fact vec_list_In_iff n v x : In x (@vec_list n v) <-> exists p, x = vec_pos v p.
  Proof.
  Admitted.

  Variable x : X.

  Fixpoint in_vec n (v : vec n) : Prop :=
    match v with
      | vec_nil => False
      | y ## v  => y = x \/ in_vec v
    end.

  Fact in_vec_list n v : @in_vec n v <-> In x (vec_list v).
  Proof. Admitted.

End vector.

Notation vec := Vector.t.
Notation vec_cons := (fun x => @Vector.cons _ x _).

Fact in_vec_pos X n (v : vec X n) p : in_vec (vec_pos v p) v.
Proof. Admitted.

Fact in_vec_inv X n (v : vec X n) x : in_vec x v -> exists p, vec_pos v p = x.
Proof.
Admitted.

Fact in_vec_dec_inv X n (v : vec X n) : 
        (forall x y : X, { x = y } + { x <> y })
     -> forall x, in_vec x v -> { p | vec_pos v p = x }.
Proof.
Admitted.

(* notations *)

Section vec_app_split.

  Variable (X : Type) (n m : nat).

  Definition vec_app (v : vec X n) (w : vec X m) : vec X (n+m).
  Proof. 
  Admitted.

  Definition vec_split (v : vec X (n+m)) : vec X n * vec X m.
  Proof.
  Admitted.

  Fact vec_app_split u : let (v,w) := vec_split u in vec_app v w = u.
  Proof.
  Admitted.

  Fact vec_split_app v w : vec_split (vec_app v w) = (v,w).
  Proof.
  Admitted.

  Fact vec_pos_app_left v w i : vec_pos (vec_app v w) (pos_left _ i) = vec_pos v i.
  Proof. Admitted.

  Fact vec_pos_app_right v w i : vec_pos (vec_app v w) (pos_right _ i) = vec_pos w i.
  Proof. Admitted.

End vec_app_split.

Fact vec_app_nil X n v : @vec_app X 0 n vec_nil v = v.
Proof.
Admitted.

Fact vec_app_cons X n m x v w : @vec_app X (S n) m (x##v) w = x##vec_app v w.
Proof.
Admitted.

Fact vec_change_app_left X n m v w i x :
  vec_change (@vec_app X n m v w) (pos_left m i) x = vec_app (vec_change v i x) w.
Proof.
Admitted.

Fact vec_change_app_right X n m v w i x :
  vec_change (@vec_app X n m v w) (pos_right _ i) x = vec_app v (vec_change w i x).
Proof.
Admitted.

Section vec_map_def.

Variable (X Y : Type).
Variable (f : X -> Y).

Fixpoint vec_map n (v : vec X n) :=
  match v with 
    | vec_nil => vec_nil
    | x ## v  => f x ## vec_map v 
  end.

End vec_map_def.

Section vec_map.

  Variable (X Y : Type).

  Fixpoint vec_in_map n v : (forall x, @in_vec X x n v -> Y) -> vec Y n.
  Proof.
  Admitted.

  Fact vec_in_map_vec_map_eq f n v : @vec_in_map n v (fun x _ => f x) = vec_map f v.
  Proof. Admitted.

  Fact vec_in_map_ext n v f g : (forall x Hx, @f x Hx = @g x Hx) 
                             -> @vec_in_map n v f = vec_in_map v g.
  Proof. Admitted.

  Fact vec_map_ext f g n v : (forall x, in_vec x v -> f x = g x) 
                          -> @vec_map X Y f n v = vec_map g v.
  Proof.
  Admitted.

  Fact vec_list_vec_map (f : X -> Y) n v : vec_list (@vec_map X Y f n v) = map f (vec_list v).
  Proof. Admitted.

End vec_map.

Fact vec_map_map X Y Z (f : X -> Y) (g : Y -> Z) n (v : vec _ n) :
          vec_map g (vec_map f v) = vec_map (fun x => g (f x)) v.
Proof. Admitted.

Section vec_map2.

  (* Definitions taken from stdlib *)
  
  Definition case0 {A} (P:vec A 0 -> Type) (H:P (@Vector.nil A)) v:P v :=
    match v with
    |vec_nil => H
    |_ => fun devil => False_ind (@IDProp) devil (* subterm !!! *)
    end.

  Definition caseS' {A} {n : nat} (v : vec A (S n)) : forall (P : vec A (S n) -> Type)
                                                      (H : forall h t, P (h ## t)), P v :=
    match v with
    | h ## t => fun P H => H h t
    | _ => fun devil => False_rect (@IDProp) devil
    end.

  Definition rect2 {A B} (P:forall {n}, vec A n -> vec B n -> Type)
             (bas : P vec_nil vec_nil) (recvec : forall {n v1 v2}, P v1 v2 ->
                                                              forall a b, P (a ## v1) (b ## v2)) :=
    fix rect2_fix {n} (v1 : vec A n) : forall v2 : vec B n, P v1 v2 :=
      match v1 with
      | vec_nil  => fun v2 => case0 _ bas v2
      | h1 ## t1 => fun v2 => caseS' v2 (fun v2' => P (h1##t1) v2') (fun h2 t2 => recvec (rect2_fix t1 t2) h1 h2)
      end.

  Definition vec_map2 {A B C} (g:A -> B -> C) :
    forall (n : nat), vec A n -> vec B n -> vec C n :=
    @rect2 _ _ (fun n _ _ => vec C n) vec_nil (fun _ _ _ H a b => (g a b) ## H).

  Global Arguments vec_map2 {A B C} g {n} v1 v2.

End vec_map2.

Fact vec_pos_map X Y (f : X -> Y) n (v : vec X n) p : vec_pos (vec_map f v) p = f (vec_pos v p).
Proof.
Admitted.

Fact vec_map_set_pos X Y f n s : @vec_map X Y f _ (@vec_set_pos _ n s)
                               = vec_set_pos (fun p => f (s p)).
Proof.
Admitted.

Section vec_plus.

  Variable n : nat.

  Definition vec_plus (v w : vec nat n) := vec_set_pos (fun p => vec_pos v p + vec_pos w p).
  Definition vec_zero : vec nat n := vec_set_pos (fun _ => 0).
  
  Fact vec_pos_plus v w p : vec_pos (vec_plus v w) p = vec_pos v p + vec_pos w p.
  Proof.
  Admitted.

  Fact vec_zero_plus v : vec_plus vec_zero v = v.
  Proof. 
  Admitted.
  
  Fact vec_zero_spec p : vec_pos vec_zero p = 0.
  Proof. Admitted.

  Fact vec_add_comm v w : vec_plus v w = vec_plus w v.
  Proof.
  Admitted.

  Fact vec_add_assoc u v w : vec_plus u (vec_plus v w) = vec_plus (vec_plus u v) w.
  Proof.
  Admitted.

  Fact vec_plus_is_zero u v : vec_zero = vec_plus u v -> u = vec_zero /\ v = vec_zero.
  Proof.
  Admitted.
  
  Definition vec_one p : vec _ n := vec_set_pos (fun q => if pos_eq_dec p q then 1 else 0).
  
  Fact vec_one_spec_eq p q : p = q -> vec_pos (vec_one p) q = 1.
  Proof.
  Admitted.
  
  Fact vec_one_spec_neq p q : p <> q -> vec_pos (vec_one p) q = 0.
  Proof.
  Admitted.
  
End vec_plus.

Arguments vec_plus {n}.
Arguments vec_zero {n}.
Arguments vec_one {n}.

Module vec_notations.

  Reserved Notation " e '#>' x " (at level 58, format "e #> x").
  Reserved Notation " e [ v / x ] " (at level 1, v at level 0, x at level 0, 
                                   left associativity, format "e [ v / x ]").

  Notation " e '#>' x " := (vec_pos e x).
  Notation " e [ v / x ] " := (vec_change e x v).

End vec_notations.

Import vec_notations.

Tactic Notation "rew" "vec" :=
  repeat lazymatch goal with 
    |              |- context[ _[_/?x]#>?x ] => rewrite vec_change_eq with (p := x) (1 := eq_refl)
    | _ : ?x = ?y  |- context[ _[_/?x]#>?y ] => rewrite vec_change_eq with (p := x) (q := y)
    | _ : ?y = ?x  |- context[ _[_/?x]#>?y ] => rewrite vec_change_eq with (p := x) (q := y)
    | _ : ?x <> ?y |- context[ _[_/?x]#>?y ] => rewrite vec_change_neq with (p := x) (q := y)
    | _ : ?y <> ?x |- context[ _[_/?x]#>?y ] => rewrite vec_change_neq with (p := x) (q := y)
    |              |- context[ vec_pos vec_zero ?x ] => rewrite vec_zero_spec with (p := x)
    |              |- context[ vec_pos (vec_one ?x) ?x ] => rewrite vec_one_spec_eq with (p := x) (1 := eq_refl)
    | _ : ?x = ?y  |- context[ vec_pos (vec_one ?x) ?y ] => rewrite vec_one_spec_eq with (p := x) (q := y)
    | _ : ?y = ?x  |- context[ vec_pos (vec_one ?x) ?y ] => rewrite vec_one_spec_eq with (p := x) (q := y)
    | _ : ?x <> ?y |- context[ vec_pos (vec_one ?x) ?y ] => rewrite vec_one_spec_neq with (p := x) (q := y)
    | _ : ?y <> ?x |- context[ vec_pos (vec_one ?x) ?y ] => rewrite vec_one_spec_neq with (p := x) (q := y)
    | |- context[ _[_/?x][_/?x] ] => rewrite vec_change_idem with (p := x) 
    | |- context[ ?v[(?v#>?x)/?x] ] => rewrite vec_change_same with (p := x)
    | |- context[ _[_/?x]#>?y ] => rewrite vec_change_neq with (p := x) (q := y); [ | discriminate ]
    | |- context[ vec_plus vec_zero ?x ] => rewrite vec_zero_plus with (v := x)
    | |- context[ vec_plus ?x vec_zero ] => rewrite (vec_add_comm x vec_zero); rewrite vec_zero_plus with (v := x)
    | |- context[ (vec_set_pos ?f) #> ?p ] => rewrite (vec_pos_set f p)
    | |- context[ (vec_map ?f ?v) #> ?p ] => rewrite (vec_pos_map f v p)
    | |- vec_plus ?x ?y = vec_plus ?y ?x => apply vec_add_comm
  end; auto.

Tactic Notation "vec" "split" hyp(v) "with" ident(n) :=
  rewrite (vec_head_tail v); generalize (vec_head v) (vec_tail v); clear v; intros n v.

Tactic Notation "vec" "nil" hyp(v) := rewrite (vec_0_nil v).

Fact Forall2_vec_list X Y (R : X -> Y -> Prop) n v w : Forall2 R (@vec_list X n v) (vec_list w) <-> forall p, R (vec_pos v p) (vec_pos w p).
Proof.
Admitted.

Fact vec_zero_S n : @vec_zero (S n) = 0##vec_zero.
Proof. Admitted.

Fact vec_one_fst n : @vec_one (S n) pos0 = 1##vec_zero.
Proof. Admitted.

Lemma vec_change_comm {X} n v p q x y : p <> q ->
vec_change (@vec_change X n v p x) q y = vec_change (vec_change v q y) p x.
Proof.
Admitted.

Fact vec_one_nxt n p : @vec_one (S n) (pos_nxt p) = 0##vec_one p.
Proof.
Admitted.

Fact vec_plus_cons n x v y w : @vec_plus (S n) (x##v) (y##w) = x+y ## vec_plus v w.
Proof.
Admitted.

Fact vec_change_succ n v p : v[(S (v#>p))/p] = @vec_plus n (vec_one p) v.
Proof.
Admitted.

Fact vec_change_pred n v p u : v#>p = S u -> v = @vec_plus n (vec_one p) (v[u/p]).
Proof.
Admitted.

Fixpoint vec_sum n (v : vec nat n) := 
  match v with 
    | vec_nil => 0
    | x##w    => x + vec_sum w
  end.
  
Fact vec_sum_plus n v w : @vec_sum n (vec_plus v w) = vec_sum v + vec_sum w.
Proof.
Admitted.

Fact vec_sum_zero n : @vec_sum n vec_zero = 0.
Proof. Admitted.

Fact vec_sum_one n p : @vec_sum n (vec_one p) = 1.
Proof.
Admitted.
  
Fact vec_sum_is_zero n v : @vec_sum n v = 0 -> v = vec_zero.
Proof.
Admitted.

Fact vec_sum_is_nzero n v : 0 < @vec_sum n v -> { p : _ & { w | v = vec_plus (vec_one p) w } }.
Proof.
Admitted.

Section vec_nat_induction.

  (* Specialized induction on vec nat n, with constant n *)

  Variable (n : nat) (P : vec nat n -> Type).
  
  Hypothesis HP0 : P vec_zero.
  Hypothesis HP1 : forall p, P (vec_one p).
  Hypothesis HP2 : forall v w, P v -> P w -> P (vec_plus v w).
  
  Theorem vec_nat_induction v : P v.
  Proof using HP0 HP1 HP2.
  Admitted.
  
End vec_nat_induction.

Section vec_map_list.

  Variable X : Type.

  (* morphism between vec nat n and (list X)/~p *)

  Fixpoint vec_map_list X n v : (pos n -> X) -> list X :=
    match v in vec _ m return (pos m -> _) -> _ with
      | vec_nil => fun _ => nil
      | a##v    => fun f => list_repeat (f pos0) a ++ vec_map_list v (fun p => f (pos_nxt p))
    end.

  Fact vec_map_list_zero n f : vec_map_list (@vec_zero n) f = @nil X.
  Proof. Admitted.

  Fact vec_map_list_one n p f : vec_map_list (@vec_one n p) f = f p :: @nil X.
  Proof.
  Admitted.

  (* The morphism *)

  Fact vec_map_list_plus n v w f : @vec_map_list X n (vec_plus v w) f ~p vec_map_list v f ++ vec_map_list w f.
  Proof.
  Admitted.

End vec_map_list.

Fact map_vec_map_list X Y (f : X -> Y) n v g : map f (@vec_map_list _ n v g) = vec_map_list v (fun p => f (g p)).
Proof.
Admitted.

Section fun2vec.

  Variable X : Type.

  Fixpoint fun2vec i n f : vec X _ :=
    match n with 
      | 0   => vec_nil
      | S n => f i##fun2vec (S i) n f
    end.

  Fact fun2vec_id i n f : fun2vec i n f = vec_set_pos (fun p => f (i+pos2nat p)).
  Proof.
  Admitted.

  Fact fun2vec_lift i n f : fun2vec i n (fun j => f (S j)) = fun2vec (S i) n f.
  Proof. Admitted.

  Fact vec_pos_fun2vec i n f p : vec_pos (fun2vec i n f) p = f (i+pos2nat p).
  Proof. Admitted.

  Definition vec2fun n (v : vec X n) x i := 
    match le_lt_dec n i with
      | left  _ => x
      | right H => vec_pos v (nat2pos H)
    end.

  Fact fun2vec_vec2fun n v x : fun2vec 0 n (@vec2fun n v x) = v.
  Proof.
  Admitted.

  Fact vec2fun_fun2vec n f x i : i < n -> @vec2fun n (fun2vec 0 n f) x i = f i.
  Proof.
  Admitted.

End fun2vec.

Section map_vec_pos_equiv.

  Variable (X : Type) (R : X -> X -> Prop)
           (Y : Type) (T : Y -> Y -> Prop)
           (T_refl : forall y, T y y)
           (T_trans : forall x y z, T x y -> T y z -> T x z). 

  Theorem map_vec_pos_equiv n (f : vec X n -> Y) : 
           (forall p v x y, R x y -> T (f (v[x/p])) (f (v[y/p])))
        -> forall v w, (forall p, R (v#>p) (w#>p)) -> T (f v) (f w).
  Proof using T_refl T_trans.
  Admitted.

End map_vec_pos_equiv.
