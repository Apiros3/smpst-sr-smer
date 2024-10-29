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

Lemma canonical_glob_nt : forall M p q l,
    typ_sess M (gtt_send p q l) -> 
    (exists M' P Q, unfoldP M ((p <-- P) ||| (q <-- Q) ||| M')) \/ (exists P Q, unfoldP M ((p <-- P) ||| (q <-- Q))).
Proof.
  intros.
  inversion H. subst.
  assert(InT p M). apply H1. apply triv_pt_p. easy.
  assert(InT q M). apply H1. apply triv_pt_q. easy.
  specialize(move_forward_h M p H4); intros.
  specialize(wfgC_triv p q l H0); intros. destruct H7.
  destruct H6.
  - destruct H6 as (P,(M',Ha)). specialize(part_after_unf M ((p <-- P) ||| M') q Ha H5); intros.
    unfold InT in *.
    inversion H6. subst. easy. simpl in H9.
    specialize(move_forward_h M' q); intros.
    unfold InT in H10.
    specialize(H10 H9).
    destruct H10.
    - destruct H10 as (P1,(M'',Hb)). left.
      exists M''. exists P. exists P1.
      apply pc_trans with (M' := ((p <-- P) ||| M')); try easy.
      apply pc_trans with (M' := ((p <-- P) ||| ((q <-- P1) ||| M''))). apply unf_cont_r. easy.
      apply pc_par5.
    - destruct H10 as (P1,Hb).
      right. exists P. exists P1. 
      apply pc_trans with (M' := ((p <-- P) ||| M')); try easy.
      apply unf_cont_r. easy.
  - destruct H6 as (P,H6).
    specialize(part_after_unf M (p <-- P) q H6 H5); intros.
    inversion H9; try easy.
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

Lemma canonical_glob_n : forall M,
    typ_sess M gtt_end -> 
    exists M', unfoldP M M' /\ ForallT (fun _ P => P = p_inact \/ (exists e p1 p2, P = p_ite e p1 p2 /\ typ_proc nil nil (p_ite e p1 p2) ltt_end)) M'.
Proof.
  intros.
  inversion H. subst.
  clear H H1 H2.
  revert H3.
  induction M; intros.
  - inversion H3. subst. clear H3.
    destruct H1 as (T,(Ha,(Hb,Hc))).
    specialize(Hc 1). destruct Hc as (m, Hc).
    revert Hc Hb Ha H0. revert s p T.
    induction m; intros. pinversion Ha. subst.
    - inversion Hc. subst. exists (s <-- p_inact). split.
      apply pc_refl.
      constructor. left. easy.
      subst.
      specialize(_a23_bf pt l e g (p_send pt l e g) nil nil ltt_end Hb (eq_refl (p_send pt l e g))); intros.
      destruct H1 as (S1,(T1,(Hd,(He,Hf)))). pinversion Hf.
      apply sub_mon.
      subst.
      specialize(_a23_a p0 lis (p_recv p0 lis) nil nil ltt_end Hb (eq_refl (p_recv p0 lis))); intros.
      destruct H1 as (STT,(Hd,(He,(Hf,Hg)))). pinversion He. apply sub_mon.
    apply proj_mon.
    pinversion Ha. subst.
    inversion Hc; try easy.
    - subst. exists (s <-- p_inact). split. apply pc_refl. constructor. left. easy.
    - subst.
      specialize(_a23_bf pt l e g (p_send pt l e g) nil nil ltt_end Hb (eq_refl (p_send pt l e g))); intros. destruct H1 as (S1,(T1,(Hd,(He,Hf)))). pinversion Hf. apply sub_mon.
    - subst.
      specialize(_a23_a p0 lis (p_recv p0 lis) nil nil ltt_end Hb (eq_refl (p_recv p0 lis))); intros.
      destruct H1 as (STT,(Hd,(He,(Hf,Hg)))). pinversion He. apply sub_mon.
    - subst.
      specialize(_a23_c (p_ite e P Q) e P Q ltt_end nil nil Hb (eq_refl (p_ite e P Q))); intros.
      destruct H1 as (T1,(T2,(Hd,(He,(Hf,(Hg,Hh)))))).
      pinversion Hf. subst. pinversion Hg. subst.
      exists (s <-- p_ite e P Q). split. apply pc_refl.
      constructor. right. exists e. exists P. exists Q. easy.
      apply sub_mon. apply sub_mon.
    - subst.
      specialize(IHm s Q ltt_end).
      assert(exists M' : session,
        unfoldP (s <-- Q) M' /\
        ForallT
          (fun (_ : string) (P : process) =>
           P = p_inact \/
           (exists (e : expr) (p1 p2 : process),
              P = p_ite e p1 p2 /\ typ_proc nil nil (p_ite e p1 p2) ltt_end)) M').
      {
        apply IHm; try easy.
        - specialize(_a23_d (p_rec g) g ltt_end nil nil Hb (eq_refl (p_rec g))); intros.
          destruct H1 as (T1,(Hd,He)). pinversion He. subst.
          specialize(_a21f g (p_rec g) ltt_end ltt_end nil nil Q); intros.
          apply H1; try easy. apply sub_mon.
        - pfold. easy.
      }
      destruct H1 as (M1,(Hd,He)). exists M1. split; try easy.
      apply pc_trans with (M' := (s <-- Q)); try easy.
      constructor. easy.
      apply proj_mon.
  - inversion H3. subst. clear H3.
    specialize(IHM1 H2). specialize(IHM2 H4). clear H2 H4.
    destruct IHM1 as (M1',(Ha,Hb)).
    destruct IHM2 as (M2',(Hc,Hd)). exists (M1' ||| M2'). 
    split. apply unf_cont; try easy.
    constructor; try easy.
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
    admit.
  - specialize(inv_expr_plus nil (e_plus e1 e2) sbool e1 e2 H (eq_refl (e_plus e1 e2))); intros.
    easy.
  - specialize(inv_expr_det nil (e_det e1 e2) sbool e1 e2 H (eq_refl (e_det e1 e2))); intros.
    destruct H0 as (k,(Ha,(Hb,Hc))). inversion Hc. subst.
    specialize(IHe1 Ha). destruct IHe1. left. constructor. easy. right. constructor. easy.
Admitted.



Theorem _3_23 : forall M G, typ_sess M G -> (exists M', unfoldP M M' /\ (ForallT (fun _ P => P = p_inact) M')) \/ exists M', betaP M M'.
Proof.
  intros.
  destruct G.
  - specialize(canonical_glob_n M H); intros.
    destruct H0 as (M',(Ha,Hb)).
    assert(ForallT (fun _ P => P = p_inact) M' \/ (exists p e p1 p2, typ_proc nil nil (p_ite e p1 p2) ltt_end /\ ((exists M'', unfoldP M' ((p <-- p_ite e p1 p2) ||| M'')) \/ unfoldP M' (p <-- p_ite e p1 p2)))).
    {
      clear H Ha. clear M. revert Hb.
      induction M'; intros.
      - inversion Hb. subst. clear Hb. destruct H0.
        - subst. left. constructor. easy.
        - destruct H as (e,(p1,(p2,(Ha,Hb)))).
          right. exists s. exists e. exists p1. exists p2.  
          split. easy.
          right. subst. apply pc_refl.
      - inversion Hb. subst. clear Hb.
        specialize(IHM'1 H1). specialize(IHM'2 H2). clear H1 H2.
        destruct IHM'1.
        - destruct IHM'2. left. constructor; try easy.
        - destruct H0 as (p0,(e,(p1,(p2,(Ha,Hb))))).
          right. exists p0. exists e. exists p1. exists p2. split. easy.
          left. destruct Hb.
          - destruct H0 as (M1,Hc).
            exists (M1 ||| M'1).
            apply pc_trans with (M' := M'2 ||| M'1). constructor.
            apply pc_trans with (M' := ((p0 <-- p_ite e p1 p2) ||| M1) ||| M'1).
            apply unf_cont_l. easy. constructor.
          - exists M'1. 
            apply pc_trans with (M' := M'2 ||| M'1). constructor.
            apply unf_cont_l. easy.
        - destruct H as (p,(e,(p1,(p2,(Ha,Hb))))).
          destruct Hb.
          - destruct H as (M',H). 
            right. exists p. exists e. exists p1. exists p2. split. easy.
            left. exists (M' ||| M'2).
            apply pc_trans with (M' := ((p <-- p_ite e p1 p2 ||| M') ||| M'2)). apply unf_cont_l. easy.
            constructor.
          - right. exists p. exists e. exists p1. exists p2.
            split. easy.
            left. exists M'2. apply unf_cont_l. easy.
    }
    clear Hb. destruct H0.
    - left. exists M'. easy.
    - destruct H0 as (p,(e,(p1,(p2,(Hb,Hc))))). right.
      destruct Hc. 
      - destruct H0 as (M1,H0).
        assert(unfoldP M ((p <-- p_ite e p1 p2) ||| M1)). apply pc_trans with (M' := M'); try easy.
        clear H0 Ha.
        assert(exists M2, betaP ((p <-- p_ite e p1 p2) ||| M1) M2).
        {
          specialize(_a23_c (p_ite e p1 p2) e p1 p2 ltt_end nil nil Hb (eq_refl (p_ite e p1 p2))); intros.
          destruct H0 as (T1,(T2,(Ha,(Hf,(Hc,(Hd,He)))))).
          specialize(expr_eval_b e He); intros.
          destruct H0.
          - exists ((p <-- p1) ||| M1). constructor. easy.
          - exists ((p <-- p2) ||| M1). constructor. easy.
        }
        destruct H0 as (M2,H0). exists M2.
        apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| M1)) (M2' := M2); try easy. 
        constructor.
      - assert(exists M2, betaP ((p <-- p_ite e p1 p2)) M2).
        { 
          specialize(_a23_c (p_ite e p1 p2) e p1 p2 ltt_end nil nil Hb (eq_refl (p_ite e p1 p2))); intros.
          destruct H1 as (T1,(T2,(Hg,(Hf,(Hc,(Hd,He)))))).
          specialize(expr_eval_b e He); intros. destruct H1.
          - exists ((p <-- p1)). constructor. easy.
          - exists ((p <-- p2)). constructor. easy.
        }
        destruct H1 as (M2,H1). exists M2.
        apply r_struct with (M1' := (p <-- p_ite e p1 p2)) (M2' := M2); try easy.
        apply pc_trans with (M' := M'); try easy. constructor.
  - right.
    rename s into p. rename s0 into q.
    specialize(canonical_glob_nt M p q l H); intros.
    destruct H0.
    - destruct H0 as (M',(P,(Q,Ha))).
      specialize(_a22_2 M (((p <-- P) ||| (q <-- Q)) ||| M') (gtt_send p q l)); intros.
      assert(typ_sess (((p <-- P) ||| (q <-- Q)) ||| M') (gtt_send p q l)). apply H0; try easy.
      clear H0.
      assert(exists M1, betaP (((p <-- P) ||| (q <-- Q)) ||| M') M1).
      {
        admit.
      }
      destruct H0 as (M1,H0). exists M1.
      apply r_struct with (M1' := (((p <-- P) ||| (q <-- Q)) ||| M')) (M2' := M1); try easy. constructor.
    - destruct H0 as (P,(Q,Ha)).
      specialize(_a22_2 M (((p <-- P) ||| (q <-- Q))) (gtt_send p q l)); intros.
      assert(typ_sess ((p <-- P) ||| (q <-- Q)) (gtt_send p q l)). apply H0; try easy.
      clear H0.
      assert(exists M1, betaP (((p <-- P) ||| (q <-- Q))) M1).
      {
        admit.
      }
      destruct H0 as (M1,H0). exists M1.
      apply r_struct with (M1' := (((p <-- P) ||| (q <-- Q)))) (M2' := M1); try easy. constructor.
Admitted.










