From SST Require Import src.expressions process.processes process.typecheck type.global type.local type.isomorphism.
From mathcomp Require Import ssreflect.seq.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
Import ListNotations.
From Paco Require Import paco.

Lemma typable_implies_wfC_helper_p2 : forall x T',
      lttTC (l_rec x) T' ->
      wfL (l_rec x) -> 
      (forall n, exists m, guardL n m (l_rec x)) ->
      exists T, lttTC T T' /\ wfL T /\ (forall n, exists m, guardL n m T) /\ (T = l_end \/ (exists p lis, T = l_send p lis \/ T = l_recv p lis)).
Proof.
      intros.
      specialize(guard_break x H1); intros.
      destruct H2. exists x0. destruct H2.
      split.
      - clear H0 H1 H3.
        revert H. revert T'. induction H2; intros; try easy.
        inversion H. subst. 
        pinversion H0. subst. 
        specialize(subst_injL 0 0 (l_rec G) G Q y H1 H3); intros. subst.
        unfold lttTC. pfold. easy.
        apply lttT_mon.
      - apply IHmultiS; try easy.
        inversion H. subst.
        pinversion H0. subst. 
        specialize(subst_injL 0 0 (l_rec G) G Q y H1 H4); intros. subst.
        unfold lttTC. pfold. easy.
        apply lttT_mon.
      split; try easy.
      - clear H H1 H3.
        revert H0. revert T'. induction H2; intros; try easy.
        inversion H. subst.
        inversion H0. subst.
        specialize(wfL_after_subst y (l_rec G) G 0 0); intros. apply H2; try easy.
      - apply IHmultiS; try easy.
         inversion H. subst.
        inversion H0. subst.
        specialize(wfL_after_subst y (l_rec G) G 0 0); intros. apply H3; try easy.
Qed.

Lemma typable_implies_wfC_helper_recv : forall x p STT,
      lttTC x (ltt_recv p STT) ->
      wfL x -> 
      (forall n, exists m, guardL n m x) ->
      exists T, lttTC (l_recv p T) (ltt_recv p STT) /\ wfL (l_recv p T) /\ (forall n, exists m, guardL n m (l_recv p T)).
Proof.
  induction x using local_ind_ref; intros; try easy.
  - pinversion H.
    apply lttT_mon.
  - pinversion H.
    apply lttT_mon.
  - exists lis. 
    pinversion H0. subst. 
    apply lttT_mon.
  - exists lis.
    pinversion H0. subst.
    split.
    pfold. easy. easy.
    apply lttT_mon.
  - pinversion H. subst.
    
    specialize(typable_implies_wfC_helper_p2 x (ltt_recv p STT)); intros.
    unfold lttTC in H2 at 1. 
    assert (exists T : local,
       lttTC T (ltt_recv p STT) /\
       wfL T /\
       (forall n : fin, exists m : fin, guardL n m T) /\
       (T = l_end \/
        (exists
           (p : string) (lis : seq.seq (option (sort * local))),
           T = l_send p lis \/ T = l_recv p lis))).
    {
      apply H2; try easy.
      pfold. easy.
    }
    clear H2. destruct H5. destruct H2. destruct H5. destruct H6.
    pinversion H2. subst.
    - destruct H7; try easy. destruct H7. destruct H7. destruct H7. easy.
      inversion H7. subst. exists x1. unfold lttTC. split. pfold. easy. easy.
    - subst. destruct H7; try easy. destruct H7. destruct H7. destruct H7; try easy.
    apply lttT_mon.
    apply lttT_mon.
Qed.


Lemma typable_implies_wfC_helper_recv2 : forall STT Pr p,
    SList Pr ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt), u = Some p /\ v = Some (s, t) /\ wfC t)) Pr STT ->
    wfC (ltt_recv p STT).
Proof.
  induction STT; intros; try easy.
  - destruct Pr; try easy.
  - destruct Pr; try easy.
    inversion H0. subst.
    unfold wfC. destruct H4.
    - destruct H1. subst. 
      specialize(IHSTT Pr p H H6).
      unfold wfC in IHSTT. destruct IHSTT. destruct H1. destruct H2.
      specialize(typable_implies_wfC_helper_recv x p STT H1 H2 H3); intros.
      destruct H4. destruct H4. destruct H5. 
      exists (l_recv p (None :: x0)).
      split.
      - pinversion H4. subst.
        unfold lttTC. pfold. constructor. constructor; try easy. left. easy.
        apply lttT_mon.
      split; try easy.
      - inversion H5. subst. constructor; try easy. constructor; try easy.
        left. easy. 
        intros. specialize(H7 n). destruct H7. inversion H7. subst. exists 0. apply gl_nil.
        subst. exists x1. constructor; try easy. constructor; try easy. left. easy.
    - destruct H1. destruct H1. destruct H1. destruct H1. destruct H2. subst. clear H0.
      unfold wfC in H3. destruct H3. destruct H0. destruct H1.
      specialize(SList_f (Some x) Pr H); intros. destruct H3.
      - specialize(IHSTT Pr p H3 H6). 
        unfold wfC in IHSTT. destruct IHSTT. destruct H4. destruct H5.
        specialize(typable_implies_wfC_helper_recv x3 p STT H4 H5 H7); intros.
        destruct H8. destruct H8. destruct H9.
        exists (l_recv p (Some (x0, x2) :: x4)).
        split.
        - pfold. constructor.
          pinversion H8. subst. constructor; try easy.
          right. exists x0. exists x2. exists x1. split. easy. split. easy.
          left. easy.
          apply lttT_mon.
        split.
        - constructor; try easy.
          specialize(SList_f (Some x) Pr H); intros.
          {
            clear H4 H5 H7 H H0 H1 H2 H3 H9 H10.
            destruct H11.
            apply SList_b. pinversion H8. subst. clear H8. clear p x3 x x0 x1 x2. 
            revert H6 H1 H. revert Pr x4. induction STT; intros; try easy.
            - destruct Pr; try easy.
            - destruct Pr; try easy.
              destruct x4; try easy.
              inversion H6. subst. clear H6. inversion H1. subst. clear H1.
              specialize(SList_f o Pr H); intros. destruct H0.
              - apply SList_b. apply IHSTT with (Pr := Pr); try easy.
              - destruct H0. destruct H1. subst.
                destruct STT; try easy. destruct x4; try easy.
                destruct H4; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. inversion H0. subst.
                destruct H5; try easy. destruct H1. destruct H1. destruct H1. destruct H1. destruct H3. inversion H3. subst. easy.
                apply lttT_mon.
            - destruct H. subst. destruct STT; try easy.
              pinversion H8. subst. destruct x4; try easy.
              apply lttT_mon.
          }
        - pinversion H8. subst. constructor.
          right. exists x0. exists x2. split; try easy.
          inversion H9. subst. easy.
          apply lttT_mon.
        - clear H4 H5 H7 H H0 H1 H6 H3 H8 H9.
          clear STT x3 Pr x x1.
          intros.
          destruct n. exists 0. apply gl_nil.
          specialize(H2 n). specialize(H10 (S n)). destruct H2. destruct H10.
          exists (ssrnat.maxn x1 x). apply gl_recv.
          constructor.
          - right. exists x0. exists x2. split; try easy.
            specialize(guardL_more n x); intros. apply H1; try easy.
            specialize(ssrnat.leq_maxr x1 x); intros. easy.
          - inversion H0. subst. clear H0 H. clear p x0 x2. revert H4. revert n x x1.
            induction x4; intros; try easy.
            inversion H4. subst.
            constructor; try easy.
            destruct H1.
            - left. easy.
            - right. destruct H. destruct H. destruct H. subst. exists x0. exists x2.
              split; try easy.
              specialize(guardL_more n x1 (ssrnat.maxn x1 x) x2 H0); intros.
              apply H.
              specialize(ssrnat.leq_maxl x1 x); intros. easy.
            apply IHx4; try easy.
      - destruct H3. destruct H4. subst.
        destruct STT; try easy. inversion H4. subst.
        exists (l_recv p [Some (x0, x2)]).
        split.
        - unfold lttTC. pfold. constructor.
          constructor. right. exists x0. exists x2. exists x1.
          split. easy. split. easy.
          left. easy.
        - easy.
        split.
        - constructor. easy.
          constructor. right. exists x0. exists x2. split; try easy.
        - easy.
        - intro. 
          destruct n. exists 0. apply gl_nil.
          specialize(H2 n). destruct H2.
          exists x. apply gl_recv. constructor; try easy.
          right. exists x0. exists x2. split. easy. easy.
Qed.