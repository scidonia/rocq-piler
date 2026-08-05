From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
From iris.base_logic.lib Require Export gen_heap.
From iris.algebra Require Import dfrac.
From stdpp Require Import fin_maps fin_map_dom.
Require Import SnakeletLang.
Import snakelet_notation.

Local Notation "l ↦{ dq } v" := (pointsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦{ dq }  v") : bi_scope.
Local Notation "l ↦ v" := (pointsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.

Class snakelet_heapGS_gen hlc Σ := SnakeletHeapGS {
  #[global] snakelet_invGS :: invGS_gen hlc Σ;
  #[global] snakelet_gen_heapG :: gen_heapGS loc sn_val Σ;
}.
Global Existing Instance snakelet_invGS.
Global Existing Instance snakelet_gen_heapG.
Notation snakelet_heapGS := (snakelet_heapGS_gen HasLc).

Section snakelet_wp.
  Context `{!snakelet_heapGS_gen hlc Σ}.

  Definition snakelet_state_interp (σ : sn_state) (ns : nat) (κs : list observation) (nt : nat) : iProp Σ :=
    gen_heap_interp σ.

  Global Program Instance snakelet_irisGS : irisGS_gen hlc snakelet_lang Σ := {|
    iris_invGS := snakelet_invGS;
    state_interp := snakelet_state_interp;
    fork_post _ := True%I;
    num_laters_per_step _ := 0%nat;
    state_interp_mono _ _ _ _ := fupd_intro _ _
  |}.
  Global Opaque iris_invGS.
  Implicit Types l : loc.

  (** Determinant lemmas — pure steps *)
  Lemma reducible_pure_step e e' σ :
    pure_step e e' → reducible e σ.
  Proof.
    intros Hpure. eexists [], e', σ, [].
    eapply (PrimPureStep [] _ σ). exact Hpure.
  Qed.

  Lemma reducible_no_obs_pure_step e e' σ :
    pure_step e e' → reducible_no_obs e σ.
  Proof.
    intros Hpure. eexists e', σ, [].
    eapply (PrimPureStep [] _ σ). exact Hpure.
  Qed.

  Lemma prim_binop_det op v1 v2 σ κ e2 σ2 efs :
    prim_step (BinOp op (Val v1) (Val v2)) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2 = Val (binop_eval op v1 v2).
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. inversion H0; subst. repeat split; reflexivity.
      + destruct Ki; simpl in H.
        1: discriminate H.
        2: { injection H; intros _ Hval _; apply fill_K_val in Hval as [-> ->]; inversion H0. }
        3: { injection H; intros _ _ Hval; apply fill_K_val in Hval as [-> ->]; inversion H0. }
        all: discriminate H.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. inversion H0.
      + destruct Ki; simpl in H.
        1: discriminate H.
        2: { injection H; intros _ Hval _; apply fill_K_val in Hval as [-> ->]; inversion H0. }
        3: { injection H; intros _ _ Hval; apply fill_K_val in Hval as [-> ->]; inversion H0. }
        all: discriminate H.

    { (* prim_binop_det:72fe62b2 *) admit. }
Admitted.

  Lemma prim_let_det x v e σ κ e2 σ2 efs :
    prim_step (Let x (Val v) e) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2 = subst x v e.
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x0. inversion H0; subst. repeat split; reflexivity.
      + destruct Ki; simpl in H; first [discriminate H | idtac].
        injection H; intros _ Hval _.
        apply fill_K_val in Hval as [-> ->]. inversion H0.
    - destruct K as [|Ki K']; simpl in H.
      + subst x0. inversion H0.
      + destruct Ki; simpl in H; first [discriminate H | idtac].
        injection H; intros _ Hval _.
        apply fill_K_val in Hval as [-> ->]. inversion H0.
  Qed.

  Lemma prim_if_true_det e1 e2 σ κ e2' σ2 efs :
    prim_step (If (Val (LitBool true)) e1 e2) σ κ e2' σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2' = e1.
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. inversion H0; subst. repeat split; reflexivity.
      + destruct Ki; simpl in H; first [discriminate H | idtac].
        injection H; intros Hval _ _.
        apply fill_K_val in Hval as [-> ->]. inversion H0.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. inversion H0.
      + destruct Ki; simpl in H; first [discriminate H | idtac].
        injection H; intros Hval _ _.
        apply fill_K_val in Hval as [-> ->]. inversion H0.

    { (* prim_if_true_det:unknown *) admit. }
Admitted.

  Lemma prim_if_false_det e1 e2 σ κ e2' σ2 efs :
    prim_step (If (Val (LitBool false)) e1 e2) σ κ e2' σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2' = e2.
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. inversion H0; subst. repeat split; reflexivity.
      + destruct Ki; simpl in H; first [discriminate H | idtac].
        injection H; intros Hval _ _.
        apply fill_K_val in Hval as [-> ->]. inversion H0.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. inversion H0.
      + destruct Ki; simpl in H; first [discriminate H | idtac].
        injection H; intros Hval _ _.
        apply fill_K_val in Hval as [-> ->]. inversion H0.

    { (* prim_if_false_det:unknown *) admit. }
Admitted.

  Lemma prim_load_det l σ κ e2 σ2 efs v :
    σ !! l = Some v →
    prim_step (Load (Val (LitLoc l))) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = σ ∧ efs = [] ∧ e2 = Val v.
  Proof.
    intros Hlookup Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. exfalso. inversion H0.
      + destruct Ki; simpl in H; first [discriminate H | idtac].
        injection H; intros Hval.
        apply fill_K_val in Hval as [-> ->]. inversion H0.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. eapply head_load_det in H0 as (v'&?&->&->&->). auto.
      + destruct Ki; simpl in H; first [discriminate H | idtac].
        injection H; intros Hval.
        apply fill_K_val in Hval as [-> ->]. inversion H0.

    { (* prim_load_det:302965af *) admit. }
Admitted.

  Lemma prim_store_det l v σ κ e2 σ2 efs :
    is_Some (σ !! l) →
    prim_step (Store (Val (LitLoc l)) (Val v)) σ κ e2 σ2 efs →
    κ = [] ∧ σ2 = <[l:=v]> σ ∧ efs = [] ∧ e2 = Val LitUnit.
  Proof.
    intros Hlookup Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. exfalso. inversion H0.
      + destruct Ki; simpl in H; first [discriminate H | idtac].
        * injection H; intros Hval _.
          apply fill_K_val in Hval as [-> ->]. inversion H0.
        * injection H; intros _ Hval.
          apply fill_K_val in Hval as [-> ->]. inversion H0.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. eapply head_store_det in H0 as (?&->&->&->). auto.
      + destruct Ki; simpl in H; first [discriminate H | idtac].
        * injection H; intros Hval _.
          apply fill_K_val in Hval as [-> ->]. inversion H0.
        * injection H; intros _ Hval.
          apply fill_K_val in Hval as [-> ->]. inversion H0.

    { (* prim_store_det:304cb084 *) admit. }
Admitted.

  Lemma prim_alloc_det v σ κ e2 σ2 efs :
    prim_step (Alloc (Val v)) σ κ e2 σ2 efs →
    ∃ l, σ !! l = None ∧ κ = [] ∧ σ2 = <[l:=v]> σ ∧ efs = [] ∧ e2 = Val (LitLoc l).
  Proof.
    intros Hprim. inversion Hprim; subst.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. exfalso. inversion H0.
      + destruct Ki; simpl in H; first [discriminate H | idtac].
        injection H; intros Hval.
        apply fill_K_val in Hval as [-> ->]. inversion H0.
    - destruct K as [|Ki K']; simpl in H.
      + subst x. eapply head_alloc_det in H0 as (l&?&->&->&->). exists l; split; [done|]. auto.
      + destruct Ki; simpl in H; first [discriminate H | idtac].
        injection H; intros Hval.
        apply fill_K_val in Hval as [-> ->]. inversion H0.

    { (* prim_alloc_det:unknown *) admit. }
Admitted.

  (** Head-step determinant lemmas *)
  Lemma head_load_det l σ e2 σ2 efs :
    head_step (Load (Val (LitLoc l))) σ e2 σ2 efs →
    ∃ v, σ !! l = Some v ∧ e2 = Val v ∧ σ2 = σ ∧ efs = [].
  Proof. intros H. inversion H; subst. eauto. Qed.

  Lemma head_store_det l v σ e2 σ2 efs :
    head_step (Store (Val (LitLoc l)) (Val v)) σ e2 σ2 efs →
    is_Some (σ !! l) ∧ e2 = Val LitUnit ∧ σ2 = <[l:=v]> σ ∧ efs = [].
  Proof. intros H. inversion H; subst. split; [done|]. auto. Qed.

  Lemma head_alloc_det v σ e2 σ2 efs :
    head_step (Alloc (Val v)) σ e2 σ2 efs →
    ∃ l, σ !! l = None ∧ e2 = Val (LitLoc l) ∧ σ2 = <[l:=v]> σ ∧ efs = [].
  Proof. intros H. inversion H; subst. eauto. Qed.

  Lemma head_faa_det l v σ e2 σ2 efs :
    head_step (FAA (Val (LitLoc l)) (Val v)) σ e2 σ2 efs →
    ∃ z, σ !! l = Some (LitInt z) ∧
         e2 = Val (LitInt z) ∧ σ2 = <[l:=LitInt (z + lit_as_z v)]> σ ∧ efs = [].
  Proof. intros H. inversion H; subst. eauto. Qed.

  Lemma head_fork_det e σ e2 σ2 efs :
    head_step (Fork e) σ e2 σ2 efs →
    e2 = Val LitUnit ∧ σ2 = σ ∧ efs = [e].
  Proof. intros H. inversion H; subst. auto. Qed.

  (** Pure WP lemmas *)
  Lemma wp_binop s E op v1 v2 Φ :
    ▷ Φ (binop_eval op v1 v2) -∗
    WP BinOp op (Val v1) (Val v2) @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ. destruct s.
      + pose proof (reducible_no_obs_pure_step
            (BinOp op (Val v1) (Val v2)) (Val (binop_eval op v1 v2)) σ
            (PureBinOp op v1 v2)) as Hred.
        apply reducible_no_obs_reducible, Hred.
      + simpl. reflexivity.
    - intros κ σ1 e2 σ2 efs Hprim.
      pose proof (prim_binop_det _ _ _ _ _ _ _ _ Hprim) as (->&->&->&_); done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2 efs σ Hprim) "Hcred".
      pose proof (prim_binop_det _ _ _ _ _ _ _ _ Hprim) as [Hκ [Hσ [Hefs He2]]].
      rewrite He2.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      iApply (wp_value' with "HΦ").
  Qed.

  Lemma wp_let s E x v e2 Φ :
    ▷ WP subst x v e2 @ s; E {{ Φ }} -∗
    WP Let x (Val v) e2 @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ. destruct s.
      + pose proof (reducible_no_obs_pure_step
            (Let x (Val v) e2) (subst x v e2) σ
            (PureLet v x e2)) as Hred.
        apply reducible_no_obs_reducible, Hred.
      + simpl. reflexivity.
    - intros κ σ1 e2' σ2 efs Hprim.
      pose proof (prim_let_det _ _ _ _ _ _ _ _ Hprim) as (->&->&->&_); done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2' efs σ Hprim) "Hcred".
      pose proof (prim_let_det _ _ _ _ _ _ _ _ Hprim) as [Hκ [Hσ [Hefs He2]]].
      rewrite He2.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      iFrame "HΦ".
  Qed.

  Lemma wp_if_true s E e1 e2 Φ :
    ▷ WP e1 @ s; E {{ Φ }} -∗
    WP If (#true)%S e1 e2 @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ. destruct s.
      + pose proof (reducible_no_obs_pure_step
            (If (Val (LitBool true)) e1 e2) e1 σ
            (PureIfTrue e1 e2)) as Hred.
        apply reducible_no_obs_reducible, Hred.
      + simpl. reflexivity.
    - intros κ σ1 e2' σ2 efs Hprim.
      pose proof (prim_if_true_det _ _ _ _ _ _ _ Hprim) as (->&->&->&_); done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2' efs σ Hprim) "Hcred".
      pose proof (prim_if_true_det _ _ _ _ _ _ _ Hprim) as [Hκ [Hσ [Hefs He2]]].
      rewrite He2.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      iFrame "HΦ".
  Qed.

  Lemma wp_if_false s E e1 e2 Φ :
    ▷ WP e2 @ s; E {{ Φ }} -∗
    WP If (#false)%S e1 e2 @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step_no_fork; [ | | ].
    - intros σ. destruct s.
      + pose proof (reducible_no_obs_pure_step
            (If (Val (LitBool false)) e1 e2) e2 σ
            (PureIfFalse e1 e2)) as Hred.
        apply reducible_no_obs_reducible, Hred.
      + simpl. reflexivity.
    - intros κ σ1 e2' σ2 efs Hprim.
      pose proof (prim_if_false_det _ _ _ _ _ _ _ Hprim) as (->&->&->&_); done.
    - iModIntro. iNext. iModIntro. iIntros (κ e2' efs σ Hprim) "Hcred".
      pose proof (prim_if_false_det _ _ _ _ _ _ _ Hprim) as [Hκ [Hσ [Hefs He2]]].
      rewrite He2.
      iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
      iFrame "HΦ".
  Qed.

  (** Stateful WP lemmas.

      Puzzle: after [wp_lift_atomic_step], the postcondition is
      [from_option Φ False (to_val e2)].  We use [wp_lift_step] (which returns
      [WP e2 {{ Φ }}]) and handle the pure step directly — this avoids the
      [from_option] wrinkle entirely. *)

  Lemma wp_load s E l v Φ :
    l ↦ v -∗
    (l ↦ v -∗ Φ v) -∗
    WP (! #l)%S @ s; E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". iApply wp_lift_step; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ".
    iDestruct (gen_heap_valid with "Hσ Hl") as %Hlookup.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose". iSplit.
    { iPureIntro. destruct s; [|done]. apply reducible_no_obs_reducible.
      eexists _, _, []. eapply (PrimHeadStep [] (Load _) σ1).
      eapply (HeadLoad l v σ1). done. }
    iNext. iIntros (e2 σ2 efs Hprim) "Hcred".
    iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
    pose proof (prim_load_det l σ1 κ e2 σ2 efs v Hlookup Hprim) as [Hκ [Hσ2 [Hefs He2]]].
    rewrite He2 Hκ Hσ2 Hefs.
    iMod "Hclose". iModIntro. iFrame "Hσ".
    iSpecialize ("HΦ" with "Hl").
    iSplitL.
    { rewrite wp_unfold /wp_pre /=. iModIntro. iExact "HΦ". }
    { done. }
  Qed.

  Lemma wp_store s E l v (w : sn_val) Φ :
    l ↦ v -∗
    (l ↦ w -∗ Φ LitUnit) -∗
    WP (#l <- Val w)%S @ s; E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". iApply wp_lift_step; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ".
    iDestruct (gen_heap_valid with "Hσ Hl") as %Hlookup.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose". iSplit.
    { iPureIntro. destruct s; [|done]. apply reducible_no_obs_reducible.
      eexists _, _, []. eapply (PrimHeadStep [] (Store _ _) σ1).
      eapply (HeadStore l w σ1). eauto. }
    iNext. iIntros (e2 σ2 efs Hprim) "Hcred".
    iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
    assert (is_Some (σ1 !! l)). { eexists; eauto. }
    pose proof (prim_store_det l w σ1 κ e2 σ2 efs H Hprim) as [Hκ [Hσ2 [Hefs He2]]].
    rewrite He2 Hκ Hσ2 Hefs.
    iMod (gen_heap_update with "Hσ Hl") as "[Hσ Hl]".
    iMod "Hclose". iModIntro. iFrame "Hσ".
    iSpecialize ("HΦ" with "Hl").
    iSplitL.
    { rewrite wp_unfold /wp_pre /=. iModIntro. iExact "HΦ". }
    { done. }
  Qed.

  Lemma fresh_loc (σ : sn_state) : ∃ l, σ !! l = None.
  Proof.
    set (d := @dom (gmap loc sn_val) (gset loc) (@gset_dom loc _ _ sn_val) σ).
    destruct (exist_fresh d) as [l Hl].
    exists l. eapply (not_elem_of_dom_1 (M:=gmap loc) (D:=gset loc)). exact Hl.
  Qed.

  Lemma wp_alloc s E v Φ :
    (∀ l, l ↦ v -∗ Φ (LitLoc l)) -∗
    WP Alloc (Val v) @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply wp_lift_step; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ".
    edestruct fresh_loc as [l Hfree].
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose". iSplit.
    { iPureIntro. destruct s; [|done]. apply reducible_no_obs_reducible.
      eexists (Val (LitLoc l)), (<[l:=v]> σ1), [].
      eapply (PrimHeadStep [] (Alloc _) σ1).
      eapply (HeadAlloc v σ1 l). done. }
    iNext. iIntros (e2 σ2 efs Hprim) "Hcred".
    iDestruct (lc_weaken 1 with "Hcred") as "Hcred"; first done.
    pose proof (prim_alloc_det v σ1 κ e2 σ2 efs Hprim) as (l'&Hfree2&Hκ&Hσ2&Hefs&He2).
    rewrite He2 Hκ Hσ2 Hefs.
    iMod (gen_heap_alloc with "Hσ") as "[Hσ Hl]"; first done.
    iDestruct "Hl" as "[Hl _]".
    iMod "Hclose". iModIntro. iFrame "Hσ".
    iSpecialize ("HΦ" $! l' with "Hl").
    iSplitL.
    { rewrite wp_unfold /wp_pre /=. iModIntro. iExact "HΦ". }
    { done. }
  Qed.

  (** Automation: repeatedly apply pure WP reductions. *)
  Ltac snakelet_pures :=
    repeat (iApply wp_binop || iApply wp_let || iApply wp_if_true || iApply wp_if_false).

End snakelet_wp.

(** Automation: match the WP goal to extract arguments, then apply the
    lemma explicitly.  Works outside the section. *)
Ltac snakelet_pure_step :=
  lazymatch goal with
  | |- environments.envs_entails _ (wp _ _ (BinOp ?op (Val ?v1) (Val ?v2)) ?Φ) =>
      iApply (@wp_binop _ _ _ _ _ op v1 v2 Φ)
  | |- environments.envs_entails _ (wp _ _ (Let ?x (Val ?v) ?e2) ?Φ) =>
      iApply (@wp_let _ _ _ _ _ x v e2 Φ)
  | |- environments.envs_entails _ (wp _ _ (If (Val (LitBool true)) ?e1 ?e2) ?Φ) =>
      iApply (@wp_if_true _ _ _ _ _ e1 e2 Φ)
  | |- environments.envs_entails _ (wp _ _ (If (Val (LitBool false)) ?e1 ?e2) ?Φ) =>
      iApply (@wp_if_false _ _ _ _ _ e1 e2 Φ)
  end.

Ltac snakelet_pures := repeat snakelet_pure_step.

(** Register [IntoVal] so [wp_value] resolves correctly. *)
Global Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
