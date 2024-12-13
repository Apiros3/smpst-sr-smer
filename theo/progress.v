From SST Require Export src.expressions process.processes process.typecheck type.global type.local process.beta process.sessions process.inversion  type.isomorphism type.projection type.proj_part type.wfgC_after_step process.subject_reduction process.progress_helper.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.

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
      specialize(inv_proc_send pt l e g (p_send pt l e g) nil nil ltt_end Hb (eq_refl (p_send pt l e g))); intros.
      destruct H1 as (S1,(T1,(Hd,(He,Hf)))). pinversion Hf.
      apply sub_mon.
      subst.
      specialize(inv_proc_recv p0 lis (p_recv p0 lis) nil nil ltt_end Hb (eq_refl (p_recv p0 lis))); intros.
      destruct H1 as (STT,(Hd,(He,(Hf,Hg)))). pinversion He. apply sub_mon.
    apply proj_mon.
    pinversion Ha. subst.
    inversion Hc; try easy.
    - subst. exists (s <-- p_inact). split. apply pc_refl. constructor. left. easy.
    - subst.
      specialize(inv_proc_send pt l e g (p_send pt l e g) nil nil ltt_end Hb (eq_refl (p_send pt l e g))); intros. destruct H1 as (S1,(T1,(Hd,(He,Hf)))). pinversion Hf. apply sub_mon.
    - subst.
      specialize(inv_proc_recv p0 lis (p_recv p0 lis) nil nil ltt_end Hb (eq_refl (p_recv p0 lis))); intros.
      destruct H1 as (STT,(Hd,(He,(Hf,Hg)))). pinversion He. apply sub_mon.
    - subst.
      specialize(inv_proc_ite (p_ite e P Q) e P Q ltt_end nil nil Hb (eq_refl (p_ite e P Q))); intros.
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
        - specialize(inv_proc_rec (p_rec g) g ltt_end nil nil Hb (eq_refl (p_rec g))); intros.
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
          specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 ltt_end nil nil Hb (eq_refl (p_ite e p1 p2))); intros.
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
          specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 ltt_end nil nil Hb (eq_refl (p_ite e p1 p2))); intros.
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
        inversion H1. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
        inversion H6. subst. clear H6. inversion H9. subst. clear H9.
        destruct H5 as (T,(Hd,(Hb,Hc))). destruct H6 as (T1,(He,(Hf,Hg))).
        clear Ha H2 H3 H8.
        specialize(guardP_break P Hc); intros.
        destruct H2 as (Q1,(Hh,Ho)).
        specialize(typ_proc_after_betaPr P Q1 nil nil T Hh Hb); intros.
        pinversion Hd. subst. assert False. apply H3. apply triv_pt_p; try easy. easy. subst. easy. subst. 
        - specialize(guardP_break Q Hg); intros.
          destruct H3 as (Q2,(Hj,Hl)).
          specialize(typ_proc_after_betaPr Q Q2 nil nil T1 Hj Hf); intros.
          clear H7 H9 Hg Hc H H1 Hd.
          pinversion He; try easy. subst. assert False. apply H. apply triv_pt_q; try easy. easy.
          subst. clear H7 H9 H5 He Hb Hf.
          assert(exists M1, betaP (((p <-- Q1) ||| (q <-- Q2)) ||| M') M1).
          {
            clear Hh Hj.
            destruct Ho.
            - subst. specialize(inv_proc_inact p_inact (ltt_send q ys) nil nil H2 (eq_refl (p_inact))); intros. 
              easy.
            - destruct H. destruct H as (e,(p1,(p2,Ha))). subst.
              specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 (ltt_send q ys) nil nil H2 (eq_refl (p_ite e p1 p2))); intros.
              destruct H as (T1,(T2,(Ha,(Hb,(Hc,(Hd,He)))))).
              specialize(expr_eval_b e He); intros. 
              destruct H.
              - exists ((p <-- p1) ||| ((q <-- Q2) ||| M')).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2) ||| M'))) (M2' := ((p <-- p1) ||| ((q <-- Q2) ||| M'))); try easy. constructor. constructor. constructor. easy.
              - exists ((p <-- p2) ||| ((q <-- Q2) ||| M')).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2) ||| M'))) (M2' := ((p <-- p2) ||| ((q <-- Q2) ||| M'))); try easy. constructor. constructor. constructor. easy.
            - destruct H.
              destruct H as (pt,(lb,(ex,(pr,Ha)))). subst.
              specialize(inv_proc_send pt lb ex pr (p_send pt lb ex pr) nil nil (ltt_send q ys) H2 (eq_refl ((p_send pt lb ex pr)))); intros. destruct H as (S,(T1,(Ht,Hb))). clear H2. rename T1 into Tl. rename Hb into Hta. clear M P Q.
              destruct Hl.
              - subst. specialize(inv_proc_inact p_inact (ltt_recv p ys0) nil nil H3 (eq_refl (p_inact))); intros. 
                easy.
              - destruct H. destruct H as (e,(p1,(p2,Ha))). subst. 
                specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 (ltt_recv p ys0) nil nil H3 (eq_refl (p_ite e p1 p2))); intros.
                destruct H as (T1,(T2,(Ha,(Hb,(Hc,(Hd,He)))))).
                specialize(expr_eval_b e He); intros. 
                destruct H.
                - exists ((q <-- p1) ||| ((p <-- p_send pt lb ex pr) ||| M')).
                  apply r_struct with (M1' := ((q <-- p_ite e p1 p2) ||| ((p <-- p_send pt lb ex pr) ||| M'))) (M2' := ((q <-- p1) ||| ((p <-- p_send pt lb ex pr) ||| M'))).
                  apply pc_trans with (M' := ((q <-- p_ite e p1 p2) ||| (p <-- p_send pt lb ex pr)) ||| M').
                  constructor. constructor. apply unf_cont_r. constructor.
                  constructor. easy.
                - exists ((q <-- p2) ||| ((p <-- p_send pt lb ex pr) ||| M')).
                  apply r_struct with (M1' := ((q <-- p_ite e p1 p2) ||| ((p <-- p_send pt lb ex pr) ||| M'))) (M2' := ((q <-- p2) ||| ((p <-- p_send pt lb ex pr) ||| M'))).
                  apply pc_trans with (M' := ((q <-- p_ite e p1 p2) ||| (p <-- p_send pt lb ex pr)) ||| M').
                  constructor. constructor. apply unf_cont_r. constructor.
                  constructor. easy.
              - destruct H. destruct H as (pt1,(lb1,(ex1,(pr1,Ha)))). subst.
                specialize(inv_proc_send pt1 lb1 ex1 pr1 (p_send pt1 lb1 ex1 pr1) nil nil (ltt_recv p ys0) H3 (eq_refl (p_send pt1 lb1 ex1 pr1))); intros.
                destruct H as (S1,(T1,(Ha,(Hb,Hc)))). pinversion Hc. apply sub_mon.
              - destruct H as (pt2,(llp,Ha)). subst.
                specialize(expr_eval_ss ex S Ht); intros. destruct H as (v, Ha).
                destruct Hta as (Hta,Htb).
                pinversion Htb. subst.
                specialize(inv_proc_recv pt2 llp (p_recv pt2 llp) nil nil (ltt_recv p ys0) H3 (eq_refl (p_recv pt2 llp))); intros.
                destruct H as (STT,(He,(Hb,(Hc,Hd)))).
                pinversion Hb. subst.
                assert(exists y, onth lb llp = Some y).
                {
                  specialize(subtype_send_inv q (extendLis lb (Some (S, Tl))) ys); intros.
                  assert(Forall2R
                    (fun u v : option (sort * ltt) =>
                     u = None \/
                     (exists (s s' : sort) (t t' : ltt),
                        u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t'))
                    (extendLis lb (Some (S, Tl))) ys). apply H; try easy.
                  pfold. easy.
                  
                  specialize(subtype_recv_inv p STT ys0); intros.
                  assert(Forall2R
                   (fun u v : option (sort * ltt) =>
                    u = None \/
                    (exists (s s' : sort) (t t' : ltt),
                       u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) ys0 STT). apply H5. pfold. easy.
                  clear H2 H5 Hd Hb He H H1 Ha Htb Hta Ht H3 H6 H0.
                  revert H7 Hc H4 H11 H10.
                  revert p q l ys ys0 llp S Tl STT. 
                  induction lb; intros.
                  - destruct ys; try easy. destruct l; try easy. destruct ys0; try easy. destruct STT; try easy. destruct llp; try easy.
                    inversion H10. subst. clear H10. inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion Hc. subst. clear Hc. inversion H4. subst. clear H4.
                    clear H13 H11 H10 H8 H5.
                    destruct H9; try easy. destruct H as (s1,(s2,(t1,(t2,(Ha,(Hb,(Hc,Hd))))))). subst.
                    destruct H2; try easy. destruct H as (s3,(g1,(t3,(He,(Hf,Hg))))). subst.
                    destruct H3; try easy. destruct H as (s4,(g2,(t4,(Hh,(Hi,Hj))))). subst.
                    destruct H6; try easy. destruct H as (s5,(s6,(t5,(t6,(Hk,(Hl,(Hm,Hn))))))). subst.
                    destruct H7; try easy. destruct H as (p1,(s7,(t7,(Ho,(Hp,Hq))))). subst.
                    exists p1. easy.
                  - destruct ys; try easy. destruct l; try easy. destruct ys0; try easy. destruct STT; try easy. destruct llp; try easy.
                    inversion H10. subst. clear H10. inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion Hc. subst. clear Hc. inversion H4. subst. clear H4.
                    specialize(IHlb p q l ys ys0 llp S Tl STT). apply IHlb; try easy.
                }
                destruct H as (y, H).
                exists ((q <-- subst_expr_proc y (e_val v) 0 0) ||| (p <-- pr) ||| M').
                apply r_struct with (M1' := (((q <-- p_recv p llp) ||| (p <-- p_send q lb ex pr)) ||| M')) (M2' := (((q <-- subst_expr_proc y (e_val v) 0 0) ||| (p <-- pr)) ||| M')); try easy.
                constructor. constructor. constructor. easy. easy.
                apply sub_mon. apply sub_mon.
            - destruct H as (pt,(llp,Ha)). subst.
              specialize(inv_proc_recv pt llp (p_recv pt llp) nil nil (ltt_send q ys) H2 (eq_refl (p_recv pt llp))); intros.
              destruct H as (STT,(Ha,(Hb,Hc))). pinversion Hb. apply sub_mon.
          }
          destruct H as (M1,Hta). exists M1.
          apply r_struct with (M1' := (((p <-- Q1) ||| (q <-- Q2)) ||| M')) (M2' := M1); try easy.
          apply betaPr_unfold; try easy.
          constructor.
          apply proj_mon.
        subst. easy.
        apply proj_mon.
      }
      destruct H0 as (M1,H0). exists M1.
      apply r_struct with (M1' := (((p <-- P) ||| (q <-- Q)) ||| M')) (M2' := M1); try easy. constructor.
    - destruct H0 as (P,(Q,Ha)).
      specialize(_a22_2 M (((p <-- P) ||| (q <-- Q))) (gtt_send p q l)); intros.
      assert(typ_sess ((p <-- P) ||| (q <-- Q)) (gtt_send p q l)). apply H0; try easy.
      clear H0.
      assert(exists M1, betaP (((p <-- P) ||| (q <-- Q))) M1).
      {
        inversion H1. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
        inversion H8. subst. clear H8.
        destruct H5 as (T,(Hd,(Hb,Hc))). destruct H6 as (T1,(He,(Hf,Hg))).
        clear Ha H2 H3.
        specialize(guardP_break P Hc); intros.
        destruct H2 as (Q1,(Hh,Ho)).
        specialize(typ_proc_after_betaPr P Q1 nil nil T Hh Hb); intros.
        pinversion Hd. subst. assert False. apply H3. apply triv_pt_p; try easy. easy. subst. easy. subst. 
        - specialize(guardP_break Q Hg); intros.
          destruct H3 as (Q2,(Hj,Hl)).
          specialize(typ_proc_after_betaPr Q Q2 nil nil T1 Hj Hf); intros.
          clear H7 H9 Hg Hc H H1 Hd.
          pinversion He; try easy. subst. assert False. apply H. apply triv_pt_q; try easy. easy.
          subst. clear H7 H9 H5 He Hb Hf.
          assert(exists M1, betaP (((p <-- Q1) ||| (q <-- Q2))) M1).
          {
            clear Hh Hj.
            destruct Ho.
            - subst. specialize(inv_proc_inact p_inact (ltt_send q ys) nil nil H2 (eq_refl (p_inact))); intros. 
              easy.
            - destruct H. destruct H as (e,(p1,(p2,Ha))). subst.
              specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 (ltt_send q ys) nil nil H2 (eq_refl (p_ite e p1 p2))); intros.
              destruct H as (T1,(T2,(Ha,(Hb,(Hc,(Hd,He)))))).
              specialize(expr_eval_b e He); intros. 
              destruct H.
              - exists ((p <-- p1) ||| ((q <-- Q2))).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2)))) (M2' := ((p <-- p1) ||| ((q <-- Q2)))); try easy. constructor. constructor. constructor. easy.
              - exists ((p <-- p2) ||| ((q <-- Q2))).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2)))) (M2' := ((p <-- p2) ||| ((q <-- Q2)))); try easy. constructor. constructor. constructor. easy.
            - destruct H.
              destruct H as (pt,(lb,(ex,(pr,Ha)))). subst.
              specialize(inv_proc_send pt lb ex pr (p_send pt lb ex pr) nil nil (ltt_send q ys) H2 (eq_refl ((p_send pt lb ex pr)))); intros. destruct H as (S,(T1,(Ht,Hb))). clear H2. rename T1 into Tl. rename Hb into Hta. clear M P Q.
              destruct Hl.
              - subst. specialize(inv_proc_inact p_inact (ltt_recv p ys0) nil nil H3 (eq_refl (p_inact))); intros. 
                easy.
              - destruct H. destruct H as (e,(p1,(p2,Ha))). subst. 
                specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 (ltt_recv p ys0) nil nil H3 (eq_refl (p_ite e p1 p2))); intros.
                destruct H as (T1,(T2,(Ha,(Hb,(Hc,(Hd,He)))))).
                specialize(expr_eval_b e He); intros. 
                destruct H.
                - exists ((q <-- p1) ||| ((p <-- p_send pt lb ex pr))).
                  apply r_struct with (M1' := ((q <-- p_ite e p1 p2) ||| ((p <-- p_send pt lb ex pr)))) (M2' := ((q <-- p1) ||| ((p <-- p_send pt lb ex pr)))).
                  apply pc_trans with (M' := ((q <-- p_ite e p1 p2) ||| (p <-- p_send pt lb ex pr))).
                  constructor. constructor. apply unf_cont_r. constructor.
                  constructor. easy.
                - exists ((q <-- p2) ||| ((p <-- p_send pt lb ex pr))).
                  apply r_struct with (M1' := ((q <-- p_ite e p1 p2) ||| ((p <-- p_send pt lb ex pr)))) (M2' := ((q <-- p2) ||| ((p <-- p_send pt lb ex pr)))).
                  apply pc_trans with (M' := ((q <-- p_ite e p1 p2) ||| (p <-- p_send pt lb ex pr))).
                  constructor. constructor. apply unf_cont_r. constructor.
                  constructor. easy.
              - destruct H. destruct H as (pt1,(lb1,(ex1,(pr1,Ha)))). subst.
                specialize(inv_proc_send pt1 lb1 ex1 pr1 (p_send pt1 lb1 ex1 pr1) nil nil (ltt_recv p ys0) H3 (eq_refl (p_send pt1 lb1 ex1 pr1))); intros.
                destruct H as (S1,(T1,(Ha,(Hb,Hc)))). pinversion Hc. apply sub_mon.
              - destruct H as (pt2,(llp,Ha)). subst.
                specialize(expr_eval_ss ex S Ht); intros. destruct H as (v, Ha).
                destruct Hta as (Hta,Htb).
                pinversion Htb. subst.
                specialize(inv_proc_recv pt2 llp (p_recv pt2 llp) nil nil (ltt_recv p ys0) H3 (eq_refl (p_recv pt2 llp))); intros.
                destruct H as (STT,(He,(Hb,(Hc,Hd)))).
                pinversion Hb. subst.
                assert(exists y, onth lb llp = Some y).
                {
                  specialize(subtype_send_inv q (extendLis lb (Some (S, Tl))) ys); intros.
                  assert(Forall2R
                    (fun u v : option (sort * ltt) =>
                     u = None \/
                     (exists (s s' : sort) (t t' : ltt),
                        u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t'))
                    (extendLis lb (Some (S, Tl))) ys). apply H; try easy.
                  pfold. easy.
                  
                  specialize(subtype_recv_inv p STT ys0); intros.
                  assert(Forall2R
                   (fun u v : option (sort * ltt) =>
                    u = None \/
                    (exists (s s' : sort) (t t' : ltt),
                       u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) ys0 STT). apply H5. pfold. easy.
                  clear H2 H5 Hd Hb He H H1 Ha Htb Hta Ht H3 H6 H0.
                  revert H7 Hc H4 H11 H10.
                  revert p q l ys ys0 llp S Tl STT. 
                  induction lb; intros.
                  - destruct ys; try easy. destruct l; try easy. destruct ys0; try easy. destruct STT; try easy. destruct llp; try easy.
                    inversion H10. subst. clear H10. inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion Hc. subst. clear Hc. inversion H4. subst. clear H4.
                    clear H13 H11 H10 H8 H5.
                    destruct H9; try easy. destruct H as (s1,(s2,(t1,(t2,(Ha,(Hb,(Hc,Hd))))))). subst.
                    destruct H2; try easy. destruct H as (s3,(g1,(t3,(He,(Hf,Hg))))). subst.
                    destruct H3; try easy. destruct H as (s4,(g2,(t4,(Hh,(Hi,Hj))))). subst.
                    destruct H6; try easy. destruct H as (s5,(s6,(t5,(t6,(Hk,(Hl,(Hm,Hn))))))). subst.
                    destruct H7; try easy. destruct H as (p1,(s7,(t7,(Ho,(Hp,Hq))))). subst.
                    exists p1. easy.
                  - destruct ys; try easy. destruct l; try easy. destruct ys0; try easy. destruct STT; try easy. destruct llp; try easy.
                    inversion H10. subst. clear H10. inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion Hc. subst. clear Hc. inversion H4. subst. clear H4.
                    specialize(IHlb p q l ys ys0 llp S Tl STT). apply IHlb; try easy.
                }
                destruct H as (y, H).
                exists ((q <-- subst_expr_proc y (e_val v) 0 0) ||| (p <-- pr)).
                apply r_struct with (M1' := (((q <-- p_recv p llp) ||| (p <-- p_send q lb ex pr)))) (M2' := (((q <-- subst_expr_proc y (e_val v) 0 0) ||| (p <-- pr)))); try easy.
                constructor. constructor. constructor. easy. easy.
                apply sub_mon. apply sub_mon.
            - destruct H as (pt,(llp,Ha)). subst.
              specialize(inv_proc_recv pt llp (p_recv pt llp) nil nil (ltt_send q ys) H2 (eq_refl (p_recv pt llp))); intros.
              destruct H as (STT,(Ha,(Hb,Hc))). pinversion Hb. apply sub_mon.
          }
          destruct H as (M1,Hta). exists M1.
          apply r_struct with (M1' := (((p <-- Q1) ||| (q <-- Q2)))) (M2' := M1); try easy.
          apply betaPr_unfold_h; try easy.
          constructor.
          apply proj_mon.
        subst. easy.
        apply proj_mon.
      }
      destruct H0 as (M1,H0). exists M1.
      apply r_struct with (M1' := (((p <-- P) ||| (q <-- Q)))) (M2' := M1); try easy. constructor.
Qed.


Definition stuck (M : session) := ((exists M', unfoldP M M' /\ ForallT (fun _ P => P = p_inact) M') -> False) /\ ((exists M', betaP M M') -> False).

Definition stuckM (M : session) := exists M', multi betaP M M' /\ stuck M'.

Theorem _3_24 : forall M G, typ_sess M G -> stuckM M -> False.
Proof.
  intros. 
  unfold stuckM in H0. destruct H0 as (M',(Ha,Hb)).
  revert Hb H. revert G.
  induction Ha; intros.
  - destruct Hb.
    specialize(_3_23 x G H); intros. destruct H2. apply H0. easy. apply H1. easy.
  - specialize(_3_21 x y G H0 H); intros.
    destruct H1 as (G',(Hc,Hd)).
    apply IHHa with (G := G'); try easy.
Qed.


