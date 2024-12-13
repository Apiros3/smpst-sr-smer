From SST Require Export src.expressions process.processes process.typecheck type.global type.local process.beta process.sessions process.inversion  type.isomorphism type.projection type.proj_part type.wfgC_after_step process.subject_reduction.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.

Lemma pc_par5 : forall M M' M'', unfoldP (M ||| (M' ||| M'')) ((M ||| M') ||| M'').
Proof.
  intros.
  apply pc_trans with (M' := (M' ||| M'') ||| M). constructor.
  apply pc_trans with (M' := (M' ||| (M'' ||| M))). constructor.
  apply pc_trans with (M' := (M'' ||| M) ||| M'). constructor.
  apply pc_trans with (M' := M'' ||| (M ||| M')). constructor. constructor. 
Qed.

Lemma unf_cont_l : forall M1 M1' M2,
  unfoldP M1 M1' -> 
  unfoldP (M1 ||| M2) (M1' ||| M2).
Proof.
  intros. revert M2.
  induction H; intros.
  - {
      apply pc_trans with (M' := (p <-- p_rec P) ||| (M ||| M2)). apply pc_par2.
      apply pc_trans with (M' := (p <-- Q) ||| (M ||| M2)). constructor. easy.
      apply pc_par5. 
      
    }
  - constructor. easy.
  - apply pc_refl.
  - apply pc_trans with (M' := (M' ||| M2)). apply IHunfoldP1. apply IHunfoldP2.
  - constructor.
  - constructor.
  - {
      apply pc_trans with (M' := (M ||| M') ||| (M'' ||| M2)). constructor.
      apply pc_trans with (M' := (M' ||| M) ||| (M'' ||| M2)). constructor.
      apply pc_par5.
    }
  - {
      apply pc_trans with (M' := (((M ||| M') ||| M'') ||| (M''' ||| M2))). constructor.
      apply pc_trans with (M' := ((M ||| (M' ||| M'')) ||| (M''' ||| M2))). constructor.
      apply pc_par5.
    }
Qed.

Lemma unf_cont_r : forall M1 M2 M2', 
    unfoldP M2 M2' -> 
    unfoldP (M1 ||| M2) (M1 ||| M2').
Proof.
  intros.
  apply pc_trans with (M' := M2 ||| M1). constructor.
  apply pc_trans with (M' := M2' ||| M1). apply unf_cont_l. easy.
  constructor.
Qed.

Lemma unf_cont : forall M1 M1' M2 M2',
    unfoldP M1 M1' -> unfoldP M2 M2' -> 
    unfoldP (M1 ||| M2) (M1' ||| M2').
Proof.
  intros.
  apply pc_trans with (M' := (M1 ||| M2')). apply unf_cont_r. easy.
  apply unf_cont_l. easy.
Qed.

Lemma move_forward_h : forall M,
    forall p : string,
    InT p M ->
    (exists (P : process) (M' : session), unfoldP M ((p <-- P) ||| M')) \/
    (exists P : process, unfoldP M (p <-- P)).
Proof.
  induction M; intros.
  - rename H into H2. unfold InT in H2. simpl in H2. destruct H2; try easy.
    subst. right. exists p. constructor.
  - rename H into H2. unfold InT in *. simpl in *.
    specialize(in_or (flattenT M1) (flattenT M2) p H2); intros.
    destruct H.
    - specialize(IHM1 p H). 
      destruct IHM1.
      - destruct H0 as (P,(M',Ha)).
        left. exists P. exists (M' ||| M2).
        apply pc_trans with (M' := ((p <-- P) ||| M') ||| M2). apply unf_cont_l. easy. 
        constructor.
      - destruct H0 as (P,Ha).
        left. exists P. exists M2. apply unf_cont_l. easy.
    - specialize(IHM2 p H). clear IHM1 H2.
      destruct IHM2.
      - destruct H0 as (P,(M',Ha)).
        left. exists P. exists (M1 ||| M').
        apply pc_trans with (M' := M1 ||| ((p <-- P) ||| M')). apply unf_cont_r. easy.
        apply pc_trans with (M' := (M1 ||| (p <-- P)) ||| M'). apply pc_par5.
        apply pc_trans with (M' := ((p <-- P) ||| M1) ||| M'). constructor. constructor.
      - destruct H0 as (P,Ha).
        left. exists P. exists M1.
        apply pc_trans with (M' := M1 ||| (p <-- P)). apply unf_cont_r. easy.
        constructor.
Qed.

Lemma move_forward : forall p M G, 
    typ_sess M G -> 
    isgPartsC p G -> 
    (exists P M', unfoldP M (p <-- P ||| M')) \/ (exists P, unfoldP M (p <-- P)).
Proof.
  intros. inversion H. subst. clear H1 H3 H4 H.
  specialize(H2 p H0). clear H0.
  revert H2. revert p. clear G.
  apply move_forward_h.
Qed.


Lemma part_after_unf : forall M M' p,
    unfoldP M M' -> 
    InT p M ->
    InT p M'.
Proof.
  intros. revert H0. revert p.
  induction H; intros; try easy.
  - apply IHunfoldP2. apply IHunfoldP1. easy.
  - unfold InT in *.
    simpl in *. apply in_swap. easy.
  - unfold InT in *. simpl in *.
    specialize(app_assoc (flattenT M) (flattenT M') (flattenT M'')); intros.
    replace (flattenT M ++ flattenT M' ++ flattenT M'') with ((flattenT M ++ flattenT M') ++ flattenT M'') in *. easy.
  - unfold InT in *. simpl in *.
    apply in_or_app. specialize(in_or ((flattenT M ++ flattenT M')) (flattenT M'') p H0); intros.
    destruct H.
    - left. apply in_swap. easy. right. easy.
  - unfold InT in *. simpl in *.
    specialize(app_assoc (flattenT M) (flattenT M') (flattenT M'')); intros.
    replace (flattenT M ++ flattenT M' ++ flattenT M'') with ((flattenT M ++ flattenT M') ++ flattenT M'') in *. easy.
Qed.

Lemma sub_mon : monotone2 subtype.
Proof.
  unfold monotone2.
  intros.
  induction IN; intros.
  - constructor.
  - constructor.
    revert H. revert xs. induction ys; intros. constructor.
    destruct xs; try easy.
    simpl in *.
    - destruct a. destruct p0. destruct o; try easy.
      destruct p0. destruct H as (Ha,(Hb,Hc)). split. easy.
      split. apply LE. easy. apply IHys; try easy.
    - destruct o. destruct p0. apply IHys; try easy. 
      apply IHys; try easy.
  - constructor.
    revert H. revert ys.
    induction xs; intros.
    - constructor.
      destruct ys; try easy.
      simpl in *.
      destruct a. destruct p0. destruct o; try easy.
      destruct p0. destruct H as (Ha,(Hb,Hc)). split. easy. split. apply LE. easy.
      apply IHxs. easy.
      destruct o. destruct p0. apply IHxs. easy. apply IHxs. easy.
Qed.

Lemma expr_eval_n : forall e, typ_expr nil e snat -> (exists k, stepE e (e_val (vnat k))).
Proof.
  induction e; intros; try easy.
  - specialize(inv_expr_var (e_var n) n nil snat H (eq_refl (e_var n))); intros.
    destruct H0 as (S',(Ha,Hb)). destruct n; try easy.
  - specialize(inv_expr_vali nil (e_val v) snat v H (eq_refl (e_val v))); intros.
    destruct H0.
    - destruct H0 as (k,(Ha,Hb)). subst. easy.
    - destruct H0. destruct H0 as (k,(Ha,Hb)). subst. exists k. constructor.
    - destruct H0 as (k,(Ha,Hb)). subst. easy.
  - specialize(inv_expr_succ nil (e_succ e) snat e H (eq_refl (e_succ e))); intros.
    destruct H0 as (H0,H1). destruct H1. specialize(IHe H0). destruct IHe as (k,Ha). exists (k+1). constructor. easy. easy.
  - specialize(inv_expr_neg nil (e_neg e) snat e H (eq_refl (e_neg e))); intros.
    easy.
  - specialize(inv_expr_not nil (e_not e) snat e H (eq_refl (e_not e))); intros.
    destruct H0. easy.
  - specialize(inv_expr_gt nil (e_gt e1 e2) snat e1 e2 H (eq_refl (e_gt e1 e2))); intros.
    destruct H0 as (Ha,(Hb,Hc)). easy.
  - specialize(inv_expr_plus nil (e_plus e1 e2) snat e1 e2 H (eq_refl (e_plus e1 e2))); intros.
    easy.
  - specialize(inv_expr_det nil (e_det e1 e2) snat e1 e2 H (eq_refl (e_det e1 e2))); intros.
    destruct H0 as (k,(Ha,(Hb,Hc))). inversion Hc. subst.
    specialize(IHe1 Ha). destruct IHe1. exists x. constructor. easy.
Qed.

Lemma expr_eval_i : forall e, typ_expr nil e sint -> (exists k, stepE e (e_val (vint k))) \/ (exists k, stepE e (e_val (vnat k))).
Proof.
  induction e; intros; try easy.
  - specialize(inv_expr_var (e_var n) n nil sint H (eq_refl (e_var n))); intros.
    destruct H0 as (S',(Ha,Hb)). destruct n; try easy.
  - specialize(inv_expr_vali nil (e_val v) sint v H (eq_refl (e_val v))); intros.
    destruct H0.
    - destruct H0 as (k,(Ha,Hb)). subst. left. exists k. constructor.
    - destruct H0. destruct H0 as (k,(Ha,Hb)). subst. right. exists k. constructor.
    - destruct H0 as (k,(Ha,Hb)). subst. easy.
  - specialize(inv_expr_succ nil (e_succ e) sint e H (eq_refl (e_succ e))); intros.
    destruct H0 as (H0,H1). destruct H1. right. easy.
    specialize(expr_eval_n e H0); intros. destruct H2 as (k,H2). 
    right. exists (k+1). constructor. easy.
  - specialize(inv_expr_neg nil (e_neg e) sint e H (eq_refl (e_neg e))); intros.
    destruct H0. specialize(IHe H1).
    destruct IHe.
    - destruct H2 as (k,Ha). left. exists (Z.opp k). constructor. easy.
    - destruct H2 as (k,Ha). left. exists (Z.opp (Z.of_nat k)). apply ec_neg2. easy.
  - specialize(inv_expr_not nil (e_not e) sint e H (eq_refl (e_not e))); intros.
    destruct H0. easy.
  - specialize(inv_expr_gt nil (e_gt e1 e2) sint e1 e2 H (eq_refl (e_gt e1 e2))); intros.
    destruct H0 as (Ha,(Hb,Hc)). easy.
  - specialize(inv_expr_plus nil (e_plus e1 e2) sint e1 e2 H (eq_refl (e_plus e1 e2))); intros.
    destruct H0 as (Ha,(Hb,Hc)). specialize(IHe1 Hb). specialize(IHe2 Hc).
    left.
    - destruct IHe1.
      destruct H0 as (k,H0).
      destruct IHe2.
      - destruct H1 as (k1,H1). exists (Z.add k k1). constructor; try easy.
      - destruct H1 as (k1,H1). exists (Z.add k (Z.of_nat k1)). constructor; try easy.
    - destruct H0 as (k,H0).
      destruct IHe2.
      - destruct H1 as (k1,H1). exists (Z.add (Z.of_nat k) k1). constructor; try easy.
      - destruct H1 as (k1,H1). exists (Z.add (Z.of_nat k) (Z.of_nat k1)). constructor; try easy.
  - specialize(inv_expr_det nil (e_det e1 e2) sint e1 e2 H (eq_refl (e_det e1 e2))); intros.
    destruct H0 as (k,(Ha,(Hb,Hc))). inversion Hc. subst.
    - specialize(expr_eval_n e1 Ha); intros. destruct H0 as (k,Hd). right. exists k. constructor. easy.
    - subst.
      specialize(IHe1 Ha). destruct IHe1.
      destruct H0. left. exists x. constructor. easy.
      destruct H0. right. exists x. constructor. easy.
Qed.

Lemma expr_eval_b : forall e, typ_expr nil e sbool -> (stepE e (e_val (vbool true)) \/ stepE e (e_val (vbool false))).
Proof.
  induction e; intros; try easy.
  - specialize(inv_expr_var (e_var n) n nil sbool H (eq_refl (e_var n))); intros.
    destruct H0 as (S',(Ha,Hb)). destruct n; try easy.
  - specialize(inv_expr_vali nil (e_val v) sbool v H (eq_refl (e_val v))); intros.
    destruct H0.
    - destruct H0 as (k,(Ha,Hb)). easy.
    - destruct H0. destruct H0 as (k,(Ha,Hb)). subst. inversion Ha.
    - destruct H0 as (k,(Ha,Hb)). subst. destruct k. left. apply ec_refl. right. apply ec_refl. 
  - specialize(inv_expr_succ nil (e_succ e) sbool e H (eq_refl (e_succ e))); intros.
    destruct H0 as (H0,H1). destruct H1. right. easy. easy.
  - specialize(inv_expr_neg nil (e_neg e) sbool e H (eq_refl (e_neg e))); intros.
    easy.
  - specialize(inv_expr_not nil (e_not e) sbool e H (eq_refl (e_not e))); intros.
    destruct H0.
    specialize(IHe H1).
    destruct IHe. right. constructor; try easy.
    left. constructor; try easy.
  - specialize(inv_expr_gt nil (e_gt e1 e2) sbool e1 e2 H (eq_refl (e_gt e1 e2))); intros.
    destruct H0 as (Ha,(Hb,Hc)).
    specialize(expr_eval_i e1 Hb); intros. 
    specialize(expr_eval_i e2 Hc); intros.
    clear Ha H IHe1 IHe2.
    destruct H0.
    - destruct H as (k,H).
      destruct H1.
      - destruct H0 as (k1,H0). 
        specialize(Zle_or_lt k k1); intros. destruct H1. 
        right. apply ec_gt_f3 with (m := k) (n := k1); try easy.
        left. apply ec_gt_t3 with (m := k) (n := k1); try easy.
      - destruct H0 as (k1,H0).
        specialize(Zle_or_lt k (Z.of_nat k1)); intros. destruct H1. 
        right. apply ec_gt_f2 with (m := k) (n := k1); try easy.
        left. apply ec_gt_t2 with (m := k) (n := k1); try easy.
    - destruct H as (k,H).
      destruct H1.
      - destruct H0 as (k1,H0).
        specialize(Zle_or_lt (Z.of_nat k) k1); intros. destruct H1. 
        right. apply ec_gt_f1 with (m := k) (n := k1); try easy.
        left. apply ec_gt_t1 with (m := k) (n := k1); try easy.
      - destruct H0 as (k1,H0).
        specialize(Zle_or_lt (Z.of_nat k) (Z.of_nat k1)); intros. destruct H1. 
        right. apply ec_gt_f0 with (m := k) (n := k1); try easy.
        left. apply ec_gt_t0 with (m := k) (n := k1); try easy.
  - specialize(inv_expr_plus nil (e_plus e1 e2) sbool e1 e2 H (eq_refl (e_plus e1 e2))); intros.
    easy.
  - specialize(inv_expr_det nil (e_det e1 e2) sbool e1 e2 H (eq_refl (e_det e1 e2))); intros.
    destruct H0 as (k,(Ha,(Hb,Hc))). inversion Hc. subst.
    specialize(IHe1 Ha). destruct IHe1. left. constructor. easy. right. constructor. easy.
Qed.

Lemma expr_eval_ss : forall ex S, typ_expr nil ex S -> exists v, stepE ex (e_val v).
Proof.
  intros.
  destruct S. 
  - specialize(expr_eval_b ex H); intros. destruct H0. exists (vbool true). easy. exists (vbool false). easy.
  - specialize(expr_eval_i ex H); intros. destruct H0. destruct H0. exists (vint x). easy. destruct H0. exists (vnat x). easy.
  - specialize(expr_eval_n ex H); intros. destruct H0. exists (vnat x). easy.
Qed.

Inductive betaPr : relation process := 
  | betaPr_sin : forall P Q, substitutionP 0 0 0 (p_rec P) P Q -> betaPr (p_rec P) Q.

Lemma guardP_break : forall P,
    (forall n : fin, exists m : fin, guardP n m P) -> 
    exists Q, multi betaPr P Q /\ (Q = p_inact \/ (exists e p1 p2, Q = p_ite e p1 p2) \/ (exists pt lb ex pr, Q = p_send pt lb ex pr) \/ (exists pt llp, Q = p_recv pt llp)).
Proof.
  intros.
  specialize(H 1). destruct H as (m, H).
  revert H. revert P.
  induction m; intros.
  - inversion H.
    - subst. exists p_inact. split. constructor. left. easy.
    - subst. exists (p_send pt l e g). split. constructor. right. right. left. exists pt. exists l. exists e. exists g. easy.
    - subst. exists (p_recv p lis). split. constructor. right. right. right. exists p. exists lis. easy.
  - inversion H. 
    - subst. exists p_inact. split. constructor. left. easy.
    - subst. exists (p_send pt l e g). split. constructor. right. right. left. exists pt. exists l. exists e. exists g. easy.
    - subst. exists (p_recv p lis). split. constructor. right. right. right. exists p. exists lis. easy.
    - subst. exists (p_ite e P0 Q). split. constructor.
      right. left. exists e. exists P0. exists Q. easy.
    - subst. specialize(IHm Q H3).
      destruct IHm as (Q1,(Ha,Hb)). exists Q1. split; try easy.
      apply multi_step with (y := Q); try easy. 
Qed.

Lemma typ_proc_after_betaPr : forall P Q Gs Gt T, 
    multi betaPr P Q ->
    typ_proc Gs Gt P T -> typ_proc Gs Gt Q T.
Proof.
  intros. revert H0. revert T Gt Gs.
  induction H; intros.
  - easy.
  - apply IHmulti. clear IHmulti H0. clear z.
    inversion H. subst.
    specialize(inv_proc_rec (p_rec P) P T Gs Gt H1 (eq_refl (p_rec P))); intros.
    destruct H2 as (T0,(Ha,Hb)).
    specialize(_a21f P (p_rec P) T0 T0 Gs Gt y); intros.
    specialize(typable_implies_wfC H1); intros.
    apply tc_sub with (t := T0); try easy.
    apply H2; try easy. apply tc_mu. easy.
Qed.

Lemma betaPr_unfold_h : forall P Q1 Q Q2 p q,
          multi betaPr P Q1 -> 
          multi betaPr Q Q2 ->
          unfoldP (((p <-- P) ||| (q <-- Q))) (((p <-- Q1) ||| (q <-- Q2))).
Proof.
  intros.
  apply pc_trans with (M' := (p <-- Q1) ||| (q <-- Q)).
  - apply unf_cont_l. clear H0. clear Q Q2. 
    induction H; intros. constructor. apply pc_trans with (M' := (p <-- y)); try easy.
    clear IHmulti H0. inversion H. subst. constructor. easy.
  - apply unf_cont_r. clear H. clear P Q1.
    induction H0; intros. constructor. apply pc_trans with (M' := (q <-- y)); try easy.
    clear IHmulti H0. inversion H. subst. constructor. easy.
Qed.

Lemma betaPr_unfold : forall P Q1 Q Q2 p q M',
          multi betaPr P Q1 -> 
          multi betaPr Q Q2 ->
          unfoldP (((p <-- P) ||| (q <-- Q)) ||| M') (((p <-- Q1) ||| (q <-- Q2)) ||| M').
Proof.
  intros. apply unf_cont_l; try easy. apply betaPr_unfold_h; try easy.
Qed.


