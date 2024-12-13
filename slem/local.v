From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header src.local src.mono.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations.
Import ListNotations. 

Lemma guardL_more : forall n m k T, guardL n m T -> m <= k -> guardL n k T.
Proof.
  induction n; intros; try easy.
  - apply gl_nil.
  - revert IHn H H0. revert n k T. induction m; intros; try easy.
    inversion H. subst. 
    - apply gl_end.
    - subst. apply gl_send; try easy.
      clear H. revert IHn H0 H2. revert n k p.
      induction lis; intros; try easy.
      inversion H2. subst. clear H2.
      constructor.
      - destruct H3. subst. left. easy.
        right. destruct H. destruct H. destruct H. subst. exists x. exists x0.
        split; try easy. apply IHn with (m := 0); try easy.
      - apply IHlis; try easy.
    - subst. apply gl_recv; try easy.
      clear H. revert IHn H0 H2. revert n k p.
      induction lis; intros; try easy.
      inversion H2. subst. clear H2.
      constructor.
      - destruct H3. subst. left. easy.
        right. destruct H. destruct H. destruct H. subst. exists x. exists x0.
        split; try easy. apply IHn with (m := 0); try easy.
      - apply IHlis; try easy.
    - destruct T.
      - inversion H.
      - apply gl_end.
      - apply gl_send.
        inversion H. subst.
        revert IHm IHn H H0 H4. revert m n k s.
        induction l; intros; try easy.
        inversion H4. subst.
        constructor.
        - destruct H3. subst. left. easy.
          destruct H1. destruct H1. destruct H1. subst. right.
          exists x. exists x0. split; try easy.
          apply IHn with (m := m.+1); try easy.
        - apply IHl with (m := m) (s := s); try easy.
        apply gl_send. easy.
      - apply gl_recv.
        inversion H. subst.
        revert IHm IHn H H0 H4. revert m n k s.
        induction l; intros; try easy.
        inversion H4. subst.
        constructor.
        - destruct H3. subst. left. easy.
          destruct H1. destruct H1. destruct H1. subst. right.
          exists x. exists x0. split; try easy.
          apply IHn with (m := m.+1); try easy.
        - apply IHl with (m := m) (s := s); try easy.
        apply gl_recv. easy.
      - inversion H. subst.
        destruct k; try easy.
        apply gl_rec with (Q := Q); try easy.
        apply IHm; try easy.
Qed.

Lemma subst_injL : forall m n G G1 Q Q0, subst_local m n G G1 Q0 -> subst_local m n G G1 Q -> Q = Q0.
Proof.
  intros m n G G1.
  revert m n G. induction G1 using local_ind_ref; intros; try easy.
  inversion H. subst. 
  - inversion H0; try easy. 
  - subst. inversion H0; try easy.
  - subst. inversion H0; try easy.
    subst. specialize(triad_le m t' H6 H8); try easy.
  - subst. inversion H0; try easy. 
    subst. specialize(triad_le m t' H8 H6); try easy.
  
  inversion H. subst. inversion H0. subst. easy.
  
  inversion H0. subst. inversion H1. subst.
  assert (ys0 = ys). {
    clear H0 H1. revert H H8 H9. revert p m n G ys ys0.
    induction lis; intros; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    inversion H. subst. clear H.
    inversion H8. subst. clear H8.
    inversion H9. subst. clear H9.
    specialize(IHlis p m n G ys ys0 H3 H6 H8). subst.
    clear H3 H6 H8.
    destruct H4. destruct H. subst.
    destruct H5. destruct H. subst. easy.
    destruct H. destruct H. destruct H. easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
    destruct H5; try easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H. subst. 
    destruct H2; try easy. destruct H0. destruct H0. destruct H0. 
    inversion H0. subst.
    specialize(H2 m n G x1 x4 H3 H1). subst. easy.
  }
  subst. easy.
  
  inversion H0. subst. inversion H1. subst.
  assert (ys0 = ys). {
    clear H0 H1. revert H H8 H9. revert p m n G ys ys0.
    induction lis; intros; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    inversion H. subst. clear H.
    inversion H8. subst. clear H8.
    inversion H9. subst. clear H9.
    specialize(IHlis p m n G ys ys0 H3 H6 H8). subst.
    clear H3 H6 H8.
    destruct H4. destruct H. subst.
    destruct H5. destruct H. subst. easy.
    destruct H. destruct H. destruct H. easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
    destruct H5; try easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H. subst. 
    destruct H2; try easy. destruct H0. destruct H0. destruct H0. 
    inversion H0. subst.
    specialize(H2 m n G x1 x4 H3 H1). subst. easy.
  }
  subst. easy.
  
  inversion H. subst. inversion H0. subst.
  specialize(IHG1 (S m) (S n) G Q1 Q0 H6 H5). subst. easy.
Qed.

Lemma wfL_after_incr : forall G1 m n,
     wfL G1 -> wfL (incr_freeL m n G1).
Proof.
  induction G1 using local_ind_ref; intros; try easy.
  - simpl in *.
    constructor.
  - revert m n H0 H. revert p.
    induction lis; intros; try easy.
    - inversion H. subst. clear H.
      inversion H0. subst. inversion H5. subst.
      specialize(SList_f a lis H2); intros.
      destruct H.
      - assert (wfL (incr_freeL m n (l_send p lis))).
        {
          apply IHlis; try easy.
          inversion H0. subst. inversion H5. subst.
          constructor; try easy.
        }
        destruct H6. subst.
        - constructor. 
          {
            simpl. clear IHlis H3 H0 H4 H5 H2 H7 H1. 
            revert m n p H. induction lis; intros; try easy.
            specialize(SList_f a lis H); intros.
            destruct H0.
            - apply SList_b. apply IHlis; try easy.
            - destruct H0. destruct H1. subst. 
            simpl. destruct x; try easy.
          }
          constructor; try easy. left. easy.
          {
            clear IHlis H3 H0 H5 H2 H H1. clear p.
            revert H4. revert m n. induction lis; intros; try easy. 
            inversion H4. inversion H7. subst. clear H4 H7.
            constructor. 
            - destruct H1. subst. left. easy.
            - destruct H. destruct H. destruct H. subst. right.
              exists x. exists (incr_freeL m n x0). split; try easy. apply H0.
              destruct H6; try easy. destruct H. destruct H. destruct H. inversion H. subst. easy.
            - apply IHlis; try easy.
          }
        - destruct H6. destruct H6. destruct H6. subst. 
          constructor; try easy.
          {
             apply SList_b.
             clear IHlis H3 H0 H4 H5 H2 H8 H7 H1. clear x x0 p.
             revert m n H.
             induction lis; intros; try easy.
             specialize(SList_f a lis H); intros.
             destruct H0. apply SList_b. apply IHlis; try easy.
             destruct H0. destruct H1. subst. destruct x. easy.
          }
          constructor. right. exists x. exists (incr_freeL m n x0).
          split; try easy.
          destruct H3; try easy. destruct H3. destruct H3. destruct H3. inversion H3. subst. 
          apply H6; try easy.
          {
            clear IHlis H3 H0 H5 H2 H H1. clear p.
            revert H4. revert m n. induction lis; intros; try easy. 
            inversion H4. inversion H7. subst. clear H4 H7.
            constructor. 
            - destruct H1. subst. left. easy.
            - destruct H. destruct H. destruct H. subst. right.
              exists x1. exists (incr_freeL m n x2). split; try easy. apply H0.
              destruct H6; try easy. destruct H. destruct H. destruct H. inversion H. subst. easy.
            - apply IHlis; try easy.
          }
        - destruct H. destruct H1. subst.
          destruct H6; try easy. destruct H. destruct H. destruct H. subst.
          destruct H3; try easy. destruct H3. destruct H3. destruct H3. 
          replace (Some x) with (Some (x2, x3)) in *. inversion H. subst. clear H H3 H4 H7 H5.
          constructor; try easy. constructor; try easy.
          right. exists x0. exists (incr_freeL m n x1).
          split; try easy. apply H6; try easy.
  - revert m n H0 H. revert p.
    induction lis; intros; try easy.
    - inversion H. subst. clear H.
      inversion H0. subst. inversion H5. subst.
      specialize(SList_f a lis H2); intros.
      destruct H.
      - assert (wfL (incr_freeL m n (l_recv p lis))).
        {
          apply IHlis; try easy.
          inversion H0. subst. inversion H5. subst.
          constructor; try easy.
        }
        destruct H6. subst.
        - constructor. 
          {
            simpl. clear IHlis H3 H0 H4 H5 H2 H7 H1. 
            revert m n p H. induction lis; intros; try easy.
            specialize(SList_f a lis H); intros.
            destruct H0.
            - apply SList_b. apply IHlis; try easy.
            - destruct H0. destruct H1. subst. 
            simpl. destruct x; try easy.
          }
          constructor; try easy. left. easy.
          {
            clear IHlis H3 H0 H5 H2 H H1. clear p.
            revert H4. revert m n. induction lis; intros; try easy. 
            inversion H4. inversion H7. subst. clear H4 H7.
            constructor. 
            - destruct H1. subst. left. easy.
            - destruct H. destruct H. destruct H. subst. right.
              exists x. exists (incr_freeL m n x0). split; try easy. apply H0.
              destruct H6; try easy. destruct H. destruct H. destruct H. inversion H. subst. easy.
            - apply IHlis; try easy.
          }
        - destruct H6. destruct H6. destruct H6. subst. 
          constructor; try easy.
          {
             apply SList_b.
             clear IHlis H3 H0 H4 H5 H2 H8 H7 H1. clear x x0 p.
             revert m n H.
             induction lis; intros; try easy.
             specialize(SList_f a lis H); intros.
             destruct H0. apply SList_b. apply IHlis; try easy.
             destruct H0. destruct H1. subst. destruct x. easy.
          }
          constructor. right. exists x. exists (incr_freeL m n x0).
          split; try easy.
          destruct H3; try easy. destruct H3. destruct H3. destruct H3. inversion H3. subst. 
          apply H6; try easy.
          {
            clear IHlis H3 H0 H5 H2 H H1. clear p.
            revert H4. revert m n. induction lis; intros; try easy. 
            inversion H4. inversion H7. subst. clear H4 H7.
            constructor. 
            - destruct H1. subst. left. easy.
            - destruct H. destruct H. destruct H. subst. right.
              exists x1. exists (incr_freeL m n x2). split; try easy. apply H0.
              destruct H6; try easy. destruct H. destruct H. destruct H. inversion H. subst. easy.
            - apply IHlis; try easy.
          }
        - destruct H. destruct H1. subst.
          destruct H6; try easy. destruct H. destruct H. destruct H. subst.
          destruct H3; try easy. destruct H3. destruct H3. destruct H3. 
          replace (Some x) with (Some (x2, x3)) in *. inversion H. subst. clear H H3 H4 H7 H5.
          constructor; try easy. constructor; try easy.
          right. exists x0. exists (incr_freeL m n x1).
          split; try easy. apply H6; try easy.
  - inversion H. subst.
    constructor; try easy. apply IHG1; try easy.
Qed.
        
Lemma wfL_after_subst : forall Q G1 G2 m n,
    wfL G1 -> wfL G2 -> subst_local m n G1 G2 Q -> wfL Q.
Proof.
  induction Q using local_ind_ref; intros; try easy.
  - apply wfl_var.
  - apply wfl_end.
  - inversion H2; try easy. 
    - subst.
      apply wfL_after_incr. easy.
    - subst.
      inversion H1. subst.
      revert H H0 H1 H2 H8 H5 H6.
      revert p G1 m n xs.
      induction lis; intros; try easy. 
      - destruct xs; try easy.
      - destruct xs; try easy.
        specialize(SList_f o xs H5); intros. clear H5.
        inversion H8. subst. clear H8. inversion H6. subst. clear H6.
        destruct H3.
        - constructor; try easy. apply SList_b.
          {
            clear IHlis H H0 H1 H2 H9 H7 H8. revert H11 H3. revert xs.
            induction lis; intros; try easy.
            destruct xs; try easy.
            inversion H11. subst.
            specialize(SList_f x l H3); intros. destruct H. 
            - apply SList_b. apply IHlis with (xs := l); try easy.
            - destruct H. destruct H0. subst. destruct lis; try easy.
              destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. subst. easy.
          } 
        - inversion H. subst. clear H.
          assert (wfL (l_send p lis)). 
          {
            apply IHlis with (G1 := G1) (m := m) (n := n) (xs := xs); try easy.
            inversion H1. subst. inversion H12. subst. clear H12.
            constructor; try easy.
            inversion H2. subst. inversion H13. subst. clear H13.
            constructor; try easy.
          }
          inversion H. subst. constructor; try easy.
          clear H11 H8 H10 H12 H13 IHlis.
          destruct H6.
          - left. easy.
          - right. destruct H4. destruct H4. destruct H4. subst.
            destruct H9; try easy. destruct H4. destruct H4. destruct H4. destruct H4. destruct H6. inversion H6. subst.
            exists x1. exists x3. split; try easy.
            destruct H7; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst. 
            specialize(H5 G1 x0 m n). apply H5; try easy.
        - destruct H3. destruct H4. subst.
          destruct H9; try easy. destruct H3. destruct H3. destruct H3. destruct H3. destruct H4. inversion H3. subst.
          destruct H7; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst. 
          destruct lis; try easy.
          constructor; try easy. constructor; try easy. right.
          exists x. exists x2. split; try easy.
          inversion H. subst. clear H. destruct H10; try easy. destruct H. destruct H. destruct H. inversion H. subst.
          specialize(H7 G1 x3 m n). apply H7; try easy.
  - inversion H2; try easy. 
    - subst.
      apply wfL_after_incr. easy.
    - subst.
      inversion H1. subst.
      revert H H0 H1 H2 H8 H5 H6.
      revert p G1 m n xs.
      induction lis; intros; try easy. 
      - destruct xs; try easy.
      - destruct xs; try easy.
        specialize(SList_f o xs H5); intros. clear H5.
        inversion H8. subst. clear H8. inversion H6. subst. clear H6.
        destruct H3.
        - constructor; try easy. apply SList_b.
          {
            clear IHlis H H0 H1 H2 H9 H7 H8. revert H11 H3. revert xs.
            induction lis; intros; try easy.
            destruct xs; try easy.
            inversion H11. subst.
            specialize(SList_f x l H3); intros. destruct H. 
            - apply SList_b. apply IHlis with (xs := l); try easy.
            - destruct H. destruct H0. subst. destruct lis; try easy.
              destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. subst. easy.
          } 
        - inversion H. subst. clear H.
          assert (wfL (l_recv p lis)). 
          {
            apply IHlis with (G1 := G1) (m := m) (n := n) (xs := xs); try easy.
            inversion H1. subst. inversion H12. subst. clear H12.
            constructor; try easy.
            inversion H2. subst. inversion H13. subst. clear H13.
            constructor; try easy.
          }
          inversion H. subst. constructor; try easy.
          clear H11 H8 H10 H12 H13 IHlis.
          destruct H6.
          - left. easy.
          - right. destruct H4. destruct H4. destruct H4. subst.
            destruct H9; try easy. destruct H4. destruct H4. destruct H4. destruct H4. destruct H6. inversion H6. subst.
            exists x1. exists x3. split; try easy.
            destruct H7; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst. 
            specialize(H5 G1 x0 m n). apply H5; try easy.
        - destruct H3. destruct H4. subst.
          destruct H9; try easy. destruct H3. destruct H3. destruct H3. destruct H3. destruct H4. inversion H3. subst.
          destruct H7; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst. 
          destruct lis; try easy.
          constructor; try easy. constructor; try easy. right.
          exists x. exists x2. split; try easy.
          inversion H. subst. clear H. destruct H10; try easy. destruct H. destruct H. destruct H. inversion H. subst.
          specialize(H7 G1 x3 m n). apply H7; try easy.
  - inversion H1. subst.
    apply wfL_after_incr; try easy.
    subst.
    specialize(IHQ G1 P (S m) (S n)). 
    constructor. apply IHQ; try easy.
    inversion H0. easy.
Qed.
  
Lemma guard_break : forall x, (forall n, exists m, guardL n m (l_rec x)) -> exists T, multiS betaL (l_rec x) T /\  (forall n, exists m, guardL n m T) /\ (T = l_end \/ (exists p lis, T = l_send p lis \/ T = l_recv p lis)).
Proof.
  intros.
  pose proof H as H1.
  specialize(H1 1). destruct H1.
  assert (exists T, multiS betaL (l_rec x) T /\
  (T = l_end \/
   (exists
      (p : string) (lis : seq.seq (option (sort * local))),
      T = l_send p lis \/ T = l_recv p lis))).
  {
    clear H. revert H0. revert x. induction x0; intros; try easy.
    inversion H0. subst.
    destruct Q; try easy.
    - exists l_end.
      split. apply multi_sing. constructor; try easy.
      left. easy.
    - exists (l_send s l).
      split. apply multi_sing. constructor; try easy.
      right. exists s. exists l. left. easy.
    - exists (l_recv s l).
      split. apply multi_sing. constructor; try easy.
      right. exists s. exists l. right. easy.
    - specialize(IHx0 Q H4). 
      destruct IHx0. destruct H. exists x1. split; try easy.
      apply multi_sstep with (y := (l_rec Q)).
      constructor; try easy.
      easy.
  }
  destruct H1. destruct H1. exists x1.
  split; try easy. split; try easy.
  clear H0 H2. clear x0.
  revert H. induction H1; intros; try easy.
  - inversion H. subst.
    specialize(H0 n). destruct H0. 
    inversion H0. subst.
    - exists 0. apply gl_nil.
    - subst. exists m.
      specialize(subst_injL 0 0 (l_rec G) G y Q H3 H1); intros. subst. easy.
  - inversion H. subst.
    apply IHmultiS; try easy.
    intros. specialize(H0 n0). destruct H0.
    inversion H0. subst. exists 0. apply gl_nil.
    subst. exists m.
    specialize(subst_injL 0 0 (l_rec G) G y Q H4 H2); intros. subst. easy.
Qed.




