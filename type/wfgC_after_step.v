From SST Require Export type.global type.local type.isomorphism type.projection type.merge type.step type.proj_part.
Require Import List String Datatypes ZArith Relations PeanoNat. 
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.


Lemma proj_cont_pq_step : forall G G' p q l,
    wfgC G -> 
    gttstepC G G' p q l -> 
    projectableA G ->
    exists LP LQ S S' T T',
    projectionC G p (ltt_send q LP) /\ 
    projectionC G q (ltt_recv p LQ) /\
    onth l LP = Some(S, T) /\ onth l LQ = Some(S', T').
Proof.
  intros.
  specialize(wfgC_step_part G G' p q l H H0); intros.
  specialize(balanced_to_tree G p H H2); intros. clear H2.
  destruct H3 as (Gl,(ct,(Ha,(Hb,(Hc,Hd))))). clear Hd.
  revert H H0 H1 Ha Hb Hc. revert G G' p q l ct.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha. subst.
    specialize(some_onth_implies_In n ct G H4); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : list (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ct); intros.
    destruct H3. specialize(H3 Hc). clear Hc H5.
    specialize(H3 (Some G) H2). destruct H3; try easy.
    destruct H3 as (q1,(lsg,Hc)). clear H2.
    - destruct Hc. inversion H2. subst.  
      pinversion H0; try easy. subst.
      unfold projectableA in H1. pose proof H1 as Ht.
      specialize(H1 p). destruct H1. pinversion H1; try easy. subst.
      assert False. apply H3. apply triv_pt_p; try easy. easy.
      subst. specialize(Ht q). destruct Ht. pinversion H3; try easy. 
      subst. assert False. apply H5. apply triv_pt_q; try easy. easy. subst.
      exists ys. exists ys0.
      assert(exists (S S' : sort) (T T' : ltt),
        onth l ys = Some (S, T) /\ onth l ys0 = Some (S', T')).
      {
        clear H16 H18 H15 H9 H13 H7 H3 H8 H11 H4 Hb H2 Ha H1 H0 H.
        revert H19 H14 H12.
        revert G' p q lsg ys s ys0. clear n ct.
        induction l; intros.
        - destruct lsg; try easy. 
          destruct ys; try easy. destruct ys0; try easy.
          inversion H19. subst. clear H19. inversion H14. subst. clear H14.
          simpl in H12. subst.
          destruct H2; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
          destruct H3; try easy. destruct H as (s2,(g2,(t2,(Hd,(He,Hf))))). inversion Hd. subst.
          simpl. exists s2. exists s2. exists t2. exists t1. easy.
        - destruct lsg; try easy. 
          destruct ys; try easy. destruct ys0; try easy.
          inversion H19. subst. clear H19. inversion H14. subst. clear H14.
          specialize(IHl G' p q lsg ys s ys0). apply IHl; try easy.
      }
      destruct H5 as (s1,(s2,(t1,(t2,(Hl,Hk))))). exists s1. exists s2. exists t1. exists t2. 
      split. pfold. easy. split. pfold. easy. easy.
    apply proj_mon. apply proj_mon. apply step_mon.
    - destruct H2. inversion H2. subst. pinversion H0; try easy. apply step_mon.
    - inversion H2. subst. pinversion H0; try easy. apply step_mon.
  - inversion Ha. subst.
    clear Ha. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    specialize(proj_forward s s' ys H0 H2); intros. 
    pinversion H1; try easy. subst. assert False. apply Hb. constructor. easy.
    subst.
    specialize(wfgC_after_step_all H10 H0); intros. rename H1 into Htt.
    clear H19.
    unfold projectableA in H2. pose proof H2 as Ht.
    specialize(H2 p). destruct H2 as (T,H2). specialize(Ht q). destruct Ht as (T',Ht).
    specialize(slist_implies_some xs H8); intros.
    destruct H1 as (n,(gl,H1)). destruct gl.
    specialize(Forall2_prop_r n xs ys (s0, g) (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ct g g')) H1 H9); intros.
    destruct H5 as (p1,(Hd,He)). destruct He; try easy.
    destruct H5 as (s1,(g1,(g2,(Hf,(Hg,Hh))))). inversion Hf. subst. clear Hf.
    specialize(Forall_prop n ys (s1, g2) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) Hg H4); intros.
    destruct H5; try easy. destruct H5 as (s2,(g3,(Hi,Hj))). inversion Hi. subst. clear Hi.
    clear H9 H4 H8.
    specialize(Forall2_prop_r n ys ys0 (s2, g3) (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q l)) Hg H20); intros.
    destruct H4 as (p1,(Hi,Hk)). destruct Hk; try easy. destruct H4 as (s3,(g4,(g5,(Hl,(Hm,Hn))))).
    inversion Hl. subst. clear Hl H20.
    specialize(Forall_prop n ys (s3, g4) (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ projectableA g)) Hg H3); intros.
    destruct H4; try easy. destruct H4 as (s4,(g6,(Ho,Hp))). inversion Ho. subst. clear H3.
    specialize(some_onth_implies_In n xs (s4, g1) H1); intros.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G G' : gtt) (p q : string) (l : fin) (ct : list (option gtt)),
           wfgC G ->
           gttstepC G G' p q l ->
           projectableA G ->
           typ_gtth ct g G ->
           (ishParts p g -> False) ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (q0 : string) (lsg : list (option (sort * gtt))),
                 u0 = Some (gtt_send p q0 lsg) \/ u0 = Some (gtt_send q0 p lsg) \/ u0 = Some gtt_end))
             ct ->
           exists (LP LQ : list (option (sort * ltt))) (S S' : sort) (T T' : ltt),
             projectionC G p (ltt_send q LP) /\
             projectionC G q (ltt_recv p LQ) /\ onth l LP = Some (S, T) /\ onth l LQ = Some (S', T')))) xs); intros. 
    destruct H4. specialize(H4 H). clear H H5.
    specialize(H4 (Some (s4, g1)) H3). destruct H4; try easy.
    destruct H as (s5,(g7,(Hq,Hr))). inversion Hq. subst.
    clear H3.
    specialize(Hr g6 g5 p q l ct).
    assert(exists (LP LQ : list (option (sort * ltt))) (S S' : sort) (T T' : ltt),
       projectionC g6 p (ltt_send q LP) /\
       projectionC g6 q (ltt_recv p LQ) /\ onth l LP = Some (S, T) /\ onth l LQ = Some (S', T')).
    {
      apply Hr; try easy.
      destruct Hn; try easy.
      specialize(ishParts_n Hb H1); intros. apply H; try easy.
    }
    clear Hr. 
    clear Hp Hn Hm Hj Hh Ho H1 Hq. clear g7 g5.
    destruct H as (lp,(lq,(s1,(s2,(t1,(t2,(Hta,(Htb,(Htc,Htd))))))))).
    clear Htt.
    assert(isgPartsC p g6). 
    {
      pinversion Hta; try easy.
      apply proj_mon.
    }
    assert(isgPartsC q g6).
    {
      pinversion Htb; try easy.
      apply proj_mon.
    }
    specialize(part_cont_b n ys s5 g6 p s s' Hg); intros.
    assert(isgPartsC p (gtt_send s s' ys)). apply H3; try easy.
    specialize(part_cont_b n ys s5 g6 q s s' Hg); intros.
    assert(isgPartsC q (gtt_send s s' ys)). apply H5; try easy.
    clear H3 H5.
    pinversion Ht; try easy. subst. pinversion H2; try easy. subst.
    clear H23 H22 H19 H18 H17 H16 H15 H6 H4 H1 H H14 H13 H12 H11 H10 H7 Hc Hb.
    specialize(Forall2_prop_r n ys ys1 (s5, g6) (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) Hg H20); intros.
    destruct H as (p1,(Ha,Hb)). destruct Hb; try easy. destruct H as (s3,(g1,(t3,(Hb,(Hc,Hd))))).
    inversion Hb. subst. clear Hb.
    specialize(Forall2_prop_r n ys ys2 (s3, g1) (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) Hg H26); intros.
    destruct H as (p2,(He,Hf)). destruct Hf; try easy. destruct H as (s4,(g2,(t4,(Hj,(Hh,Hi))))).
    inversion Hj. subst.
    pclearbot.
    specialize(wfgC_after_step_all H9 H0); intros.
    specialize(Forall_prop n ys (s4, g2) (fun u : option (sort * gtt) =>
       u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) Hg H); intros.
    destruct H1; try easy. destruct H1 as (s5,(g3,(Hk,Hl))). inversion Hk. subst.
    specialize(proj_inj Hl Hi Hta); intros. subst.
    specialize(proj_inj Hl Hd Htb); intros. subst.
    clear H H26 H20 Hi Hd.
    specialize(merge_send_T n T ys2 q lp H27 Hh); intros. destruct H as (lp',H). subst.
    specialize(merge_recv_T n T' ys1 p lq H21 Hc); intros. destruct H as (lq',H). subst.
    exists lp'. exists lq'. 
    specialize(merge_label_recv ys1 lq' lq (s2, t2) n l p H21 Hc Htd); intros. destruct H as (ta,H). 
    specialize(merge_label_send ys2 lp' lp (s1, t1) n l q H27 Hh Htc); intros. destruct H1 as (tb,H1).
    destruct ta. destruct tb.
    exists s3. exists s0. exists l1. exists l0.
    split. pfold. easy. split. pfold. easy. easy.
  apply proj_mon.
  apply proj_mon.
  apply step_mon.
Qed.

Lemma proj_cont_pq_step_full : forall G G' p q l,
    wfgC G -> 
    gttstepC G G' p q l -> 
    projectableA G ->
    exists (T T' : ltt), projectionC G' p T /\ projectionC G' q T'.
Proof.
  intros.
  specialize(proj_cont_pq_step G G' p q l H H0 H1); intros.
  destruct H2 as (l1,(l2,(s1,(s2,(t1,(t2,(Ha,(Hb,(Hc,Hd))))))))).
  specialize(_3_19_1_helper p q l G G' l1 l2 s1 t1 s2 t2); intros.
  exists t1.
  specialize(_3_19_2_helper p q l G G' l1 l2 s1 t1 s2 t2); intros.
  exists t2.
  split. apply H2; try easy. apply H3; try easy.
Qed.

Lemma nil_word : forall G, exists tc, gttmap G nil None tc.
Proof.
  intros.
  destruct G.
  exists gnode_end. constructor.
  exists (gnode_pq s s0). constructor.
Qed.

Lemma word_step_back_s : forall [w G G' tc p q l], 
    gttstepC G G' p q l ->
    gttmap G' w None tc ->
    gttmap G w None tc \/ (exists w0 w1, w = (w0 ++ w1) /\ gttmap G (w0 ++ l :: w1) None tc /\ gttmap G w0 None (gnode_pq p q)).
Proof.
  induction w; intros.
  - pinversion H.
    - subst. right. exists nil. exists nil. split. easy.
      simpl. split. apply gmap_con with (st := s) (gk := G'); try easy.
      constructor.
    - subst. left. inversion H0; try easy. subst. constructor.
    apply step_mon.
  - pinversion H.
    - subst. right. exists nil. exists (a :: w).
      split. easy. split. apply gmap_con with (st := s) (gk := G'); try easy.
      constructor.
    - subst.
      inversion H0. subst. clear H7.
      specialize(Forall2_prop_l a xs ys (st, gk) (fun u v : option (sort * gtt) =>
        u = None /\ v = None \/
        (exists (s : sort) (g g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q l)) H16 H8); intros.
      destruct H7 as (p1,(Ha,Hb)). destruct Hb; try easy.
      destruct H7 as (s1,(g1,(g2,(Hb,(Hc,Hd))))). inversion Hc. subst.
      destruct Hd; try easy.
      specialize(IHw g1 g2 tc p q l H7 H17).
      destruct IHw.
      - left. apply gmap_con with (st := s1) (gk := g1); try easy.
      - right.
        destruct H9 as (w0,(w1,(Hd,He))). subst.
        exists (a :: w0). exists w1. split. easy.
        split.
        apply gmap_con with (st := s1) (gk := g1); try easy.
        apply gmap_con with (st := s1) (gk := g1); try easy.
      apply step_mon.
Qed.


Lemma word_step_back_ss : forall [w G G' tc p q l], 
    gttstepC G G' p q l ->
    gttmap G' w None tc ->
    (forall w0 w1 tc1, w = w0 ++ w1 -> (gttmap G' w0 None tc1 <-> gttmap G w0 None tc1)) \/ 
    (exists w0 w1, w = (w0 ++ w1) /\ 
    (forall s1 s2 s3 tc1, w0 = s1 ++ s2 ++ (s3 :: nil) -> (gttmap G' s1 None tc1 <-> gttmap G s1 None tc1)) /\
    (forall s1 s2 tc1, w1 = s1 ++ s2 -> (gttmap G' (w0 ++ s1) None tc1 <-> gttmap G (w0 ++ l :: s1) None tc1)) 
     /\ gttmap G w0 None (gnode_pq p q)).
Proof.
  induction w; intros.
  - pinversion H.
    - subst. right. exists nil. exists nil. split. easy.
      - split. intros. destruct s1; try easy. destruct s2; try easy.
      - split. intros. destruct s1; try easy. simpl in *.
        split.
        - intros.
          apply gmap_con with (st := s) (gk := G'); try easy.
        - intros. inversion H4. subst.
          specialize(eq_trans H2 H12); intros. inversion H3. subst. easy.
      - constructor. 
    - subst. left. inversion H0; try easy. subst.
      intros. split.
      - intros. destruct w0; try easy. inversion H10; try easy. subst. constructor.
      - intros. destruct w0; try easy. inversion H10; try easy. 
    apply step_mon.
  - pinversion H.
    - subst. right. exists nil. exists (a :: w).
      split. easy.
      - split. intros. destruct s1; try easy. destruct s2; try easy.
      - split. intros.
        split.
        - intros. apply gmap_con with (st := s) (gk := G'); try easy.
        - intros. inversion H4. subst.
          specialize(eq_trans H2 H12); intros. inversion H5. subst. easy.
      - constructor.
    - subst.
      inversion H0. subst. clear H7.
      specialize(Forall2_prop_l a xs ys (st, gk) (fun u v : option (sort * gtt) =>
        u = None /\ v = None \/
        (exists (s : sort) (g g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q l)) H16 H8); intros.
      destruct H7 as (p1,(Ha,Hb)). destruct Hb; try easy.
      destruct H7 as (s1,(g1,(g2,(Hb,(Hc,Hd))))). inversion Hc. subst.
      destruct Hd; try easy.
      specialize(IHw g1 g2 tc p q l H7 H17).
      destruct IHw.
      - left.
        intros. split. intros. destruct w0. 
        - inversion H11. subst. constructor.
        - inversion H10. subst.
          inversion H11. subst.
          specialize(eq_trans (eq_sym H21) H16); intros. inversion H12. subst.
          specialize(H9 w0 w1 tc1).
          assert(gttmap g1 w0 None tc1). apply H9; try easy.
          apply gmap_con with (st := s1) (gk := g1); try easy.
        intros. destruct w0.
        - inversion H11. subst. constructor.
        - inversion H10. subst.
          inversion H11. subst.
          specialize(eq_trans (eq_sym H21) Hb); intros. inversion H12. subst.
          specialize(H9 w0 w1 tc1).
          assert(gttmap g2 w0 None tc1). apply H9; try easy.
          apply gmap_con with (st := s1) (gk := g2); try easy.
      - right.
        destruct H9 as (w0,(w1,(Hd,He))). subst.
        exists (a :: w0). exists w1. split. easy.
        destruct He as (He,(Hf,Hg)).
        - split. intros. 
          destruct s0. split. intros.
          - inversion H10. subst. constructor.
          - intros. inversion H10. subst. constructor.
          - inversion H9. subst.
          split. intros. inversion H10. subst. 
            specialize(eq_trans (eq_sym H20) H16); intros. inversion H11. subst.
            specialize(He s0 s2 s3 tc1).
            assert(gttmap g1 s0 None tc1). apply He; try easy.
            apply gmap_con with (st := s1) (gk := g1); try easy.
          - intros. inversion H10. subst.
            specialize(eq_trans (eq_sym H20) Hb); intros. inversion H11. subst.
            specialize(He s0 s2 s3 tc1).
            assert(gttmap g2 s0 None tc1). apply He; try easy.
            apply gmap_con with (st := s1) (gk := g2); try easy.
        - split. intros.
          specialize(Hf s0 s2 tc1).
          split. intros.
            inversion H10. subst. specialize(eq_trans (eq_sym H20) H16); intros. inversion H9. subst.
            assert(gttmap g1 (w0 ++ l :: s0) None tc1). apply Hf; try easy.
            apply gmap_con with (st := s1) (gk := g1); try easy.
          - intros.
            inversion H10. subst. specialize(eq_trans (eq_sym H20) Hb); intros. inversion H9. subst.
            assert(gttmap g2 (w0 ++ s0) None tc1). apply Hf; try easy.
            apply gmap_con with (st := s1) (gk := g2); try easy.
          - apply gmap_con with (st := s1) (gk := g1); try easy.
      apply step_mon.
Qed.

Lemma decon_word {A} : forall (w2 : list A) l w0 w1 w3,
    w0 ++ l :: w1 = w2 ++ w3 -> 
    w0 = w2 \/ (exists wi wj, w0 = w2 ++ wi ++ (wj :: nil)) \/ (exists wi wj, w1 = wi ++ wj /\ w2 = w0 ++ l :: wi).
Proof.
  induction w2; intros.
  - destruct w0. left. easy.
    right. simpl. left. 
    clear H. revert a. induction w0; intros. exists nil. exists a. easy.
    specialize(IHw0 a). destruct IHw0 as (wi,(wj,Ha)). exists (a0 :: wi). exists wj. 
    replace (a :: w0) with (wi ++ wj :: nil) in *. constructor.
  - destruct w0.
    simpl. right. right. inversion H. subst. exists w2. exists w3. easy.
    inversion H. subst. clear H.
    specialize(IHw2 l w0 w1 w3 H2).
    destruct IHw2. left. subst. easy.
    destruct H.
    - destruct H as (wi,(wj,Ha)). right. left. exists wi. exists wj. subst. easy.
    - destruct H as (wi,(wj,Ha)). right. right. destruct Ha. subst.
      exists wi. exists wj. easy.
Qed.

Lemma inj_gttmap : forall [w G tc1 tc2], gttmap G w None tc1 -> gttmap G w None tc2 -> tc1 = tc2.
Proof.
  induction w; intros.
  - inversion H. subst. inversion H0. subst. easy.
    subst. inversion H0. subst. easy.
  - inversion H. subst.
    inversion H0. subst.
    specialize(eq_trans (eq_sym H4) H10); intros. inversion H1. subst.
    specialize(IHw gk0 tc1 tc2 H7 H11). subst. easy.
Qed.

Lemma stword {A} : forall w2 wi (wj : A) w1,
    (w2 ++ wi ++ wj :: nil) ++ w1 = w2 ++ wi ++ wj :: w1.
Proof.
  intros.
  specialize(app_assoc w2 wi (wj :: w1)); intros.
  apply eq_trans with (y := (w2 ++ wi) ++ wj :: w1); try easy. clear H.
  specialize(app_assoc w2 wi (wj :: nil)); intros.
  replace (w2 ++ wi ++ wj :: nil) with ((w2 ++ wi) ++ wj :: nil) in *. clear H.
  specialize(app_assoc (w2 ++ wi) (wj :: nil) w1); intros.
  replace (((w2 ++ wi) ++ wj :: nil) ++ w1) with ((w2 ++ wi) ++ (wj :: nil) ++ w1) in *. clear H.
  constructor.
Qed.

Lemma cut_word {A} : forall (w : list A) k k',
    k <= k' -> 
    length w = k' ->
    exists w' w2, length w' = k /\ w = w' ++ w2.
Proof.
  induction w; intros.
  - destruct k'; try easy. 
    destruct k; try easy. exists nil. exists nil. easy.
  - destruct k'; try easy.
    destruct k.
    - exists nil. exists (a :: w). easy.
    - specialize(IHw k k').
      assert(exists w' w2 : list A, length w' = k /\ w = w' ++ w2).
      {
        apply IHw; try easy. 
        apply le_S_n; try easy.
        simpl in H0.
        apply eq_add_S; try easy.
      }
      destruct H1 as (w1,(w2,(Ha,Hb))).
      exists (a :: w1). exists w2. subst. easy.
Qed.

Lemma map_back_word : forall [w0 G w1 tc],
    gttmap G (w0 ++ w1) None tc -> 
    exists tc, gttmap G w0 None tc.
Proof.
  induction w0; intros.
  - destruct G.
    - exists gnode_end. constructor.
    - exists (gnode_pq s s0). constructor.
  - inversion H. subst.
    specialize(IHw0 gk w1 tc H6). destruct IHw0 as (tc1,H1).
    exists tc1.
    apply gmap_con with (st := st) (gk := gk); try easy.
Qed.

Lemma cut_further : forall k k' G p0,
    k <= k' -> 
    (forall w'0 : list fin,
     gttmap G w'0 None gnode_end \/
     length w'0 = k /\ (exists tc : gnode, gttmap G w'0 None tc) ->
     exists w2 w0 : list fin,
       w'0 = w2 ++ w0 /\
       (exists r : string,
          gttmap G w2 None (gnode_pq p0 r) \/ gttmap G w2 None (gnode_pq r p0))) ->
    (forall w'0 : list fin,
     gttmap G w'0 None gnode_end \/
     length w'0 = k' /\ (exists tc : gnode, gttmap G w'0 None tc) ->
     exists w2 w0 : list fin,
       w'0 = w2 ++ w0 /\
       (exists r : string,
          gttmap G w2 None (gnode_pq p0 r) \/ gttmap G w2 None (gnode_pq r p0))).
Proof.
  intros.
  destruct H1.
  - specialize(H0 w'0). apply H0. left. easy.
  - destruct H1 as (H1,(tc,H2)). rename w'0 into w.
    specialize(cut_word w k k' H H1); intros.
    destruct H3 as (w0,(w1,(Ha,Hb))).
    specialize(H0 w0). subst.
    assert(gttmap G w0 None gnode_end \/
     length w0 = length w0 /\ (exists tc : gnode, gttmap G w0 None tc)).
    {
      right. split. easy.
      apply map_back_word with (w1 := w1) (tc := tc); try easy.
    }
    specialize(H0 H1). clear H1.
    destruct H0 as (w2,(w3,(Ha,(r,Hb)))). subst.
    exists w2. exists (w3 ++ w1). split. apply eq_sym. apply app_assoc.
    exists r. easy.
Qed.

Lemma word_to_parts : forall G w' p q0,
             gttmap G w' None (gnode_pq p q0) \/
             gttmap G w' None (gnode_pq q0 p) -> 
             wfgCw G -> 
             isgPartsC p G.
Proof.
  intros G w'. revert G.
  induction w'; intros.
  - destruct H.
    inversion H. subst. apply triv_pt_p_s; try easy.
    inversion H. subst. apply triv_pt_q_s; try easy.
  - destruct H.
    - inversion H. subst.
      specialize(wfgCw_after_step_all); intros.
      specialize(wfgCw_triv p0 q xs H0); intros. destruct H2.
      specialize(H1 xs p0 q H2 H0); intros.
      clear H2 H3.
      specialize(Forall_prop a xs (st, gk) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgCw g)) H4 H1); intros.
      destruct H2; try easy. destruct H2 as (s1,(g1,(Ha,Hb))). inversion Ha. subst.
      specialize(IHw' g1 p q0).
      assert(isgPartsC p g1). apply IHw'; try easy.
      left. easy.
      - case_eq (eqb p p0); intros.
        assert (p = p0). apply eqb_eq; try easy. subst. apply triv_pt_p_s; try easy.
      - case_eq (eqb p q); intros.
        assert (p = q). apply eqb_eq; try easy. subst. apply triv_pt_q_s; try easy.
      - assert (p <> p0). apply eqb_neq; try easy.
        assert (p <> q). apply eqb_neq; try easy.
        apply part_cont_b_s with (n := a) (s := s1) (g := g1); try easy.
    - inversion H. subst.
      specialize(wfgCw_after_step_all); intros.
      specialize(wfgCw_triv p0 q xs H0); intros. destruct H2.
      specialize(H1 xs p0 q H2 H0); intros.
      clear H2 H3.
      specialize(Forall_prop a xs (st, gk) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgCw g)) H4 H1); intros.
      destruct H2; try easy. destruct H2 as (s1,(g1,(Ha,Hb))). inversion Ha. subst.
      specialize(IHw' g1 p q0).
      assert(isgPartsC p g1). apply IHw'; try easy.
      right. easy.
      - case_eq (eqb p p0); intros.
        assert (p = p0). apply eqb_eq; try easy. subst. apply triv_pt_p_s; try easy.
      - case_eq (eqb p q); intros.
        assert (p = q). apply eqb_eq; try easy. subst. apply triv_pt_q_s; try easy.
      - assert (p <> p0). apply eqb_neq; try easy.
        assert (p <> q). apply eqb_neq; try easy.
        apply part_cont_b_s with (n := a) (s := s1) (g := g1); try easy.
Qed.

Lemma balanced_step : forall [G G' p q l],
    wfgC G -> 
    gttstepC G G' p q l -> 
    projectableA G ->
    balancedG G'.
Proof.
  intros. pose proof H as Ht.
  unfold wfgC in H. destruct H as (Gl,(Ha,(Hb,(Hc,H)))). clear Ha Hb Hc. clear Gl.
  specialize(wfgC_step_part G G' p q l Ht H0); intros.
  specialize(balanced_to_tree G p Ht H2); intros.
  destruct H3 as (Gl,(ct,(Ha,(Hb,(Hc,Hd))))). clear Hd H2.
  revert Hc Hb Ha Ht H1 H0. clear H.
  revert G G' p q l ct.
  induction Gl using gtth_ind_ref; intros; try easy.
  - inversion Ha. subst.
    specialize(some_onth_implies_In n ct G H3); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : list (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ct); intros.
    destruct H2. specialize(H2 Hc). clear H4 Hc.
    specialize(H2 (Some G) H). destruct H2; try easy.
    destruct H2 as (q1,(lsg,Hc)).
    - destruct Hc. inversion H2. subst.
      pinversion H0; try easy. subst.
      unfold wfgC in Ht. destruct Ht as (G1,(Hta,(Htb,(Htc,Htd)))).
      specialize(balanced_cont Htd); intros.
      specialize(some_onth_implies_In l lsg (s, G') (eq_sym H12)); intros.
      specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) lsg); intros. 
      destruct H6. specialize(H6 H4). clear H4 H7.
      specialize(H6 (Some (s, G')) H5). destruct H6; try easy.
      destruct H4 as (s1,(g1,(Hsa,Hsb))). inversion Hsa. subst. easy.
      apply step_mon.
    - destruct H2. inversion H2. subst. pinversion H0; try easy.
      apply step_mon.
    - inversion H2. subst. pinversion H0; try easy.
      apply step_mon.
  - inversion Ha. subst. 
    pinversion H0; try easy.
    - subst. assert False. apply Hb. constructor. easy.
    subst. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    assert(Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ balancedG g)) ys0).
    {
      clear Ha H7. 
      specialize(wfgC_after_step_all H6 Ht); intros.
      specialize(proj_forward s s' ys Ht H1); intros. clear H1.
      clear H5 H6 H9 H10 H11 H12 Ht H0 H17.
      revert H3 H2 H18 H8 Hc H Hb. revert s s' xs p q l ct ys.
      induction ys0; intros; try easy.
      destruct ys; try easy. destruct xs; try easy.
      inversion H3. subst. clear H3. inversion H2. subst. clear H2.
      inversion H18. subst. clear H18. 
      inversion H8. subst. clear H8. inversion H. subst. clear H.
      specialize(IHys0 s s' xs p q l ct ys).
      assert(Forall
          (fun u : option (sort * gtt) =>
           u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) ys0).
      {
        apply IHys0; try easy.
        specialize(ishParts_hxs Hb); try easy.
      }
      constructor; try easy.
      clear H H8 H12 H10 H6 H5 IHys0.
      destruct H7. left. easy.
      destruct H as (s1,(g1,(g2,(Hd,(He,Hf))))). subst.
      destruct H3; try easy. destruct H as (s2,(g3,(Hg,Hh))). inversion Hg. subst.
      destruct H4; try easy. destruct H as (s3,(g4,(Hi,Hj))). inversion Hi. subst.
      destruct H9; try easy. destruct H as (s4,(g5,(g6,(Hk,(Hl,Hm))))). inversion Hl. subst.
      destruct H2; try easy. destruct H as (s5,(g7,(Hn,Ho))). inversion Hn. subst.
      right. exists s5. exists g2. split. easy.
      clear Hn Hl Hg Hi. destruct Hf; try easy. 
      specialize(Ho g6 g2 p q l ct). apply Ho; try easy.
      specialize(ishParts_x Hb); try easy.
    }
    clear H18 H17 H8 H7 H.
    unfold balancedG.
    intros.
    destruct w.
    - simpl.
      {
        simpl in *. 
        assert(exists Gl, Gl = (gtth_send s s' xs)). exists (gtth_send s s' xs). easy.
        destruct H4 as (Gl,H4). replace (gtth_send s s' xs) with Gl in *.
        assert(exists G, G = (gtt_send s s' ys)). exists (gtt_send s s' ys). easy.
        destruct H7 as (G,H7). replace (gtt_send s s' ys) with G in *.
        assert(exists G', G' = (gtt_send s s' ys0)). exists (gtt_send s s' ys0). easy.
        - case_eq (eqb p0 p); intros.
          assert (p0 = p). apply eqb_eq; try easy. subst. 
          {
            clear H4 Hc Hb Ha. 
            clear H8 H7 H13.
            assert(gttstepC G (gtt_send s s' ys0) p q l). pfold. easy. clear H0.
            specialize(proj_cont_pq_step_full G (gtt_send s s' ys0) p q l Ht H4 H1); intros.
            destruct H0 as (T,(T1,(Ha,Hb))). clear Hb. clear T1.
            
            specialize(wfgCw_after_step G (gtt_send s s' ys0) p q l Ht H4); intros. 
            
            assert(isgPartsC p (gtt_send s s' ys0)).
            {
              apply word_to_parts with (w' := w') (q0 := q0); try easy.
            }
            assert(Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ isgPartsC p g)) ys0).
            {
              apply Forall_forall; intros.
              destruct x.
              - right. destruct p0. exists s0. exists g. split. easy.
                pinversion Ha; try easy. subst.
                specialize(in_some_implies_onth (s0, g) ys0 H8); intros.
                destruct H13 as (n, H13).
                specialize(Forall2_prop_r n ys0 ys1 (s0, g) (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) H13 H22); intros.
                destruct H14 as (p1,(Hta,Htb)). destruct Htb; try easy.
                destruct H14 as (s1,(g1,(t1,(Htb,(Htc,Htd))))). inversion Htb. subst.
                destruct Htd; try easy.
                pinversion H14; try easy. subst.
                specialize(merge_end_back n ys1 T Htc H23); intros. subst.
                specialize(pmergeCR_s (gtt_send s s' ys0) p); intros.
                assert False. apply H20; try easy.
                pfold. easy. easy.
                apply proj_mon. apply proj_mon.
              - left. easy.
            }
            unfold balancedG in H2.
            assert((Forall (fun u : option (sort * gtt) =>
              u = None \/
              (exists (s : sort) (g : gtt),
                 u = Some (s, g) /\
                  exists k : fin,
                    forall w'0 : list fin,
                    gttmap g w'0 None gnode_end \/
                    length w'0 = k /\ (exists tc : gnode, gttmap g w'0 None tc) ->
                    exists w2 w0 : list fin,
                      w'0 = w2 ++ w0 /\
                      (exists r : string,
                         gttmap g w2 None (gnode_pq p r) \/
                         gttmap g w2 None (gnode_pq r p))))) ys0).
            {
              apply Forall_forall; intros.
              specialize(Forall_forall  (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall (w w' : list fin) (p q : string) (gn : gnode),
            gttmap g w None gn ->
            gttmap g (seq.cat w w') None (gnode_pq p q) \/ gttmap g (seq.cat w w') None (gnode_pq q p) ->
            exists k : fin,
              forall w'0 : list fin,
              gttmap g (seq.cat w w'0) None gnode_end \/
              length w'0 = k /\ (exists tc : gnode, gttmap g (seq.cat w w'0) None tc) ->
              exists w2 w0 : list fin,
                w'0 = w2 ++ w0 /\
                (exists r : string,
                   gttmap g (seq.cat w w2) None (gnode_pq p r) \/
                   gttmap g (seq.cat w w2) None (gnode_pq r p))))) ys0); intros.
              destruct H14. specialize(H14 H2). clear H15 H2.
              specialize(H14 x H13).
              specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ isgPartsC p g)) ys0); intros.
              destruct H2. specialize(H2 H8). clear H8 H15.
              specialize(H2 x H13).
              destruct H2. left. easy.
              destruct H2 as (s1,(g1,(Hb,Hc))). subst.
              destruct H14; try easy.
              destruct H2 as (s2,(g2,(Hd,He))). inversion Hd. subst.
              clear H13 Hd.
              right. exists s2. exists g2. split. easy.
              specialize(parts_to_word p g2 Hc); intros.
              destruct H2 as (w1,(r,Hd)).
              specialize(He nil w1 p r).
              specialize(nil_word g2); intros. destruct H2 as (tc,H2).
              specialize(He tc). apply He; try easy. simpl.
              destruct Hd. right. easy. left. easy.
            }
            clear H8 H7 Ha H4 H2.
            assert(exists K, 
                Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt),
            u = Some (s, g) /\
            (exists k : fin, k <= K /\
               forall w'0 : list fin,
               gttmap g w'0 None gnode_end \/
               length w'0 = k /\ (exists tc : gnode, gttmap g w'0 None tc) ->
               exists w2 w0 : list fin,
                 w'0 = w2 ++ w0 /\
                 (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p)))))
        ys0).
            {
              clear H0 H3 H H12 H11 H10 H9 H6 H5 H1 Ht.
              revert H13. revert p. clear s s' xs q l ct Gl ys G w' q0 gn T.
              induction ys0; intros; try easy.
              exists 0. constructor.
              inversion H13. subst. clear H13. specialize(IHys0 p H2).
              destruct IHys0 as (K, Ha). clear H2.
              destruct H1.
              - subst. exists K. constructor; try easy. left. easy.
              - destruct H as (s1,(g1,(Hb,(k,Hc)))). subst.
                exists (Nat.max k K).
                constructor; try easy.
                - right. exists s1. exists g1. split. easy.
                  exists k. split; try easy.
                  apply Nat.le_max_l.
                - revert Ha. clear Hc. clear g1 s1.
                  apply Forall_mono; intros.
                  destruct H. left. easy.
                  destruct H as (s1,(g1,(Ha,(k1,(Hb,Hc))))).
                  right. subst. exists s1. exists g1.
                  split. easy. exists k1. split; try easy.
                  apply Nat.le_trans with (m := K); try easy.
                  apply Nat.le_max_r.
            }
            destruct H2 as (K, H2). clear H13.
            assert(Forall
             (fun u : option (sort * gtt) =>
              u = None \/
              (exists (s : sort) (g : gtt),
                 u = Some (s, g) /\
                    (forall w'0 : list fin,
                     gttmap g w'0 None gnode_end \/
                     length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
                     exists w2 w0 : list fin,
                       w'0 = w2 ++ w0 /\
                       (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p))))) ys0).
            {
              revert H2. apply Forall_mono; intros.
              destruct H2. left. easy.
              destruct H2 as (s1,(g1,(Ha,(k,(Hb,Hc))))).
              subst. right. exists s1. exists g1. split. easy.
              apply cut_further with (k := k); try easy.
            }
            clear H2.
            exists (S K).
            intros. clear H H3. clear gn w' ct Gl. clear ys xs H1 Ht.
            destruct H2.
            - inversion H. subst.
              specialize(Forall_prop n ys0 (st, gk) (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall w'0 : list fin,
            gttmap g w'0 None gnode_end \/ length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
            exists w2 w0 : list fin,
              w'0 = w2 ++ w0 /\
              (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p))))) H14 H4); intros.
               destruct H1; try easy. destruct H1 as (s1,(g1,(Ha,Hb))). inversion Ha. subst.
               specialize(Hb lis).
               assert(gttmap g1 lis None gnode_end \/ length lis = K /\ (exists tc : gnode, gttmap g1 lis None tc)). left. easy.
               specialize(Hb H1). clear H1.
               destruct Hb as (w2,(w0,(Hc,(r,Hd)))). subst.
               exists (n :: w2). exists w0. split. constructor.
               exists r.
               destruct Hd.
               - left. apply gmap_con with (st := s1) (gk := g1); try easy.
               - right. apply gmap_con with (st := s1) (gk := g1); try easy.
            - destruct H as (H,(tc,Ha)).
              inversion Ha; try easy. subst. easy.
              subst.
              specialize(Forall_prop n ys0 (st, gk) (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall w'0 : list fin,
            gttmap g w'0 None gnode_end \/ length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
            exists w2 w0 : list fin,
              w'0 = w2 ++ w0 /\
              (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p))))) H14 H4); intros.
              destruct H1; try easy. destruct H1 as (s1,(g1,(Hb,Hc))). inversion Hb. subst.
              specialize(Hc lis).
              assert(gttmap g1 lis None gnode_end \/ length lis = K /\ (exists tc : gnode, gttmap g1 lis None tc)). right. split. apply eq_add_S. easy. exists tc. easy.
              specialize(Hc H1). clear H1.
              destruct Hc as (w2,(w0,(Hc,(r,Hd)))). subst.
              exists (n :: w2). exists w0. split. constructor. exists r.
              destruct Hd.
               - left. apply gmap_con with (st := s1) (gk := g1); try easy.
               - right. apply gmap_con with (st := s1) (gk := g1); try easy.
          }
        - case_eq (eqb p0 q); intros.
          assert (p0 = q). apply eqb_eq; try easy. subst. 
          {
            simpl in *. 
            clear H4 Hc Hb Ha. 
            clear H8 H7 H13 H14.
            assert(gttstepC G (gtt_send s s' ys0) p q l). pfold. easy. clear H0.
            specialize(proj_cont_pq_step_full G (gtt_send s s' ys0) p q l Ht H4 H1); intros.
            destruct H0 as (T1,(T,(Hb,Ha))). clear Hb. clear T1.
            
            specialize(wfgCw_after_step G (gtt_send s s' ys0) p q l Ht H4); intros. 
            
            assert(isgPartsC q (gtt_send s s' ys0)).
            {
              apply word_to_parts with (w' := w') (q0 := q0); try easy.
            }
            assert(Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ isgPartsC q g)) ys0).
            {
              apply Forall_forall; intros.
              destruct x.
              - right. destruct p0. exists s0. exists g. split. easy.
                pinversion Ha; try easy. subst.
                specialize(in_some_implies_onth (s0, g) ys0 H8); intros.
                destruct H13 as (n, H13).
                specialize(Forall2_prop_r n ys0 ys1 (s0, g) (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) H13 H22); intros.
                destruct H14 as (p1,(Hta,Htb)). destruct Htb; try easy.
                destruct H14 as (s1,(g1,(t1,(Htb,(Htc,Htd))))). inversion Htb. subst.
                destruct Htd; try easy.
                pinversion H14; try easy. subst.
                specialize(merge_end_back n ys1 T Htc H23); intros. subst.
                specialize(pmergeCR_s (gtt_send s s' ys0) q); intros.
                assert False. apply H20; try easy.
                pfold. easy. easy.
                apply proj_mon. apply proj_mon.
              - left. easy.
            }
            unfold balancedG in H2.
            assert((Forall (fun u : option (sort * gtt) =>
              u = None \/
              (exists (s : sort) (g : gtt),
                 u = Some (s, g) /\
                  exists k : fin,
                    forall w'0 : list fin,
                    gttmap g w'0 None gnode_end \/
                    length w'0 = k /\ (exists tc : gnode, gttmap g w'0 None tc) ->
                    exists w2 w0 : list fin,
                      w'0 = w2 ++ w0 /\
                      (exists r : string,
                         gttmap g w2 None (gnode_pq q r) \/
                         gttmap g w2 None (gnode_pq r q))))) ys0).
            {
              apply Forall_forall; intros.
              specialize(Forall_forall  (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall (w w' : list fin) (p q : string) (gn : gnode),
            gttmap g w None gn ->
            gttmap g (seq.cat w w') None (gnode_pq p q) \/ gttmap g (seq.cat w w') None (gnode_pq q p) ->
            exists k : fin,
              forall w'0 : list fin,
              gttmap g (seq.cat w w'0) None gnode_end \/
              length w'0 = k /\ (exists tc : gnode, gttmap g (seq.cat w w'0) None tc) ->
              exists w2 w0 : list fin,
                w'0 = w2 ++ w0 /\
                (exists r : string,
                   gttmap g (seq.cat w w2) None (gnode_pq p r) \/
                   gttmap g (seq.cat w w2) None (gnode_pq r p))))) ys0); intros.
              destruct H14. specialize(H14 H2). clear H15 H2.
              specialize(H14 x H13).
              specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ isgPartsC q g)) ys0); intros.
              destruct H2. specialize(H2 H8). clear H8 H15.
              specialize(H2 x H13).
              destruct H2. left. easy.
              destruct H2 as (s1,(g1,(Hb,Hc))). subst.
              destruct H14; try easy.
              destruct H2 as (s2,(g2,(Hd,He))). inversion Hd. subst.
              clear H13 Hd.
              right. exists s2. exists g2. split. easy.
              specialize(parts_to_word q g2 Hc); intros.
              destruct H2 as (w1,(r,Hd)).
              specialize(He nil w1 q r).
              specialize(nil_word g2); intros. destruct H2 as (tc,H2).
              specialize(He tc). apply He; try easy. simpl.
              destruct Hd. right. easy. left. easy.
            }
            clear H8 H7 Ha H4 H2.
            assert(exists K, 
                Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt),
            u = Some (s, g) /\
            (exists k : fin, k <= K /\
               forall w'0 : list fin,
               gttmap g w'0 None gnode_end \/
               length w'0 = k /\ (exists tc : gnode, gttmap g w'0 None tc) ->
               exists w2 w0 : list fin,
                 w'0 = w2 ++ w0 /\
                 (exists r : string, gttmap g w2 None (gnode_pq q r) \/ gttmap g w2 None (gnode_pq r q)))))
        ys0).
            {
              clear H0 H3 H H12 H11 H10 H9 H6 H5 H1 Ht.
              revert H13. revert q. clear s s' xs p l ct Gl ys G w' q0 gn T.
              induction ys0; intros; try easy.
              exists 0. constructor.
              inversion H13. subst. clear H13. specialize(IHys0 q H2).
              destruct IHys0 as (K, Ha). clear H2.
              destruct H1.
              - subst. exists K. constructor; try easy. left. easy.
              - destruct H as (s1,(g1,(Hb,(k,Hc)))). subst.
                exists (Nat.max k K).
                constructor; try easy.
                - right. exists s1. exists g1. split. easy.
                  exists k. split; try easy.
                  apply Nat.le_max_l.
                - revert Ha. clear Hc. clear g1 s1.
                  apply Forall_mono; intros.
                  destruct H. left. easy.
                  destruct H as (s1,(g1,(Ha,(k1,(Hb,Hc))))).
                  right. subst. exists s1. exists g1.
                  split. easy. exists k1. split; try easy.
                  apply Nat.le_trans with (m := K); try easy.
                  apply Nat.le_max_r.
            }
            destruct H2 as (K, H2). clear H13.
            assert(Forall
             (fun u : option (sort * gtt) =>
              u = None \/
              (exists (s : sort) (g : gtt),
                 u = Some (s, g) /\
                    (forall w'0 : list fin,
                     gttmap g w'0 None gnode_end \/
                     length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
                     exists w2 w0 : list fin,
                       w'0 = w2 ++ w0 /\
                       (exists r : string, gttmap g w2 None (gnode_pq q r) \/ gttmap g w2 None (gnode_pq r q))))) ys0).
            {
              revert H2. apply Forall_mono; intros.
              destruct H2. left. easy.
              destruct H2 as (s1,(g1,(Ha,(k,(Hb,Hc))))).
              subst. right. exists s1. exists g1. split. easy.
              apply cut_further with (k := k); try easy.
            }
            clear H2.
            exists (S K).
            intros. clear H H3. clear gn w' ct Gl. clear ys xs H1 Ht.
            destruct H2.
            - inversion H. subst.
              specialize(Forall_prop n ys0 (st, gk) (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall w'0 : list fin,
            gttmap g w'0 None gnode_end \/ length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
            exists w2 w0 : list fin,
              w'0 = w2 ++ w0 /\
              (exists r : string, gttmap g w2 None (gnode_pq q r) \/ gttmap g w2 None (gnode_pq r q))))) H14 H4); intros.
               destruct H1; try easy. destruct H1 as (s1,(g1,(Ha,Hb))). inversion Ha. subst.
               specialize(Hb lis).
               assert(gttmap g1 lis None gnode_end \/ length lis = K /\ (exists tc : gnode, gttmap g1 lis None tc)). left. easy.
               specialize(Hb H1). clear H1.
               destruct Hb as (w2,(w0,(Hc,(r,Hd)))). subst.
               exists (n :: w2). exists w0. split. constructor.
               exists r.
               destruct Hd.
               - left. apply gmap_con with (st := s1) (gk := g1); try easy.
               - right. apply gmap_con with (st := s1) (gk := g1); try easy.
            - destruct H as (H,(tc,Ha)).
              inversion Ha; try easy. subst. easy.
              subst.
              specialize(Forall_prop n ys0 (st, gk) (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall w'0 : list fin,
            gttmap g w'0 None gnode_end \/ length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
            exists w2 w0 : list fin,
              w'0 = w2 ++ w0 /\
              (exists r : string, gttmap g w2 None (gnode_pq q r) \/ gttmap g w2 None (gnode_pq r q))))) H14 H4); intros.
              destruct H1; try easy. destruct H1 as (s1,(g1,(Hb,Hc))). inversion Hb. subst.
              specialize(Hc lis).
              assert(gttmap g1 lis None gnode_end \/ length lis = K /\ (exists tc : gnode, gttmap g1 lis None tc)). right. split. apply eq_add_S. easy. exists tc. easy.
              specialize(Hc H1). clear H1.
              destruct Hc as (w2,(w0,(Hc,(r,Hd)))). subst.
              exists (n :: w2). exists w0. split. constructor. exists r.
              destruct Hd.
               - left. apply gmap_con with (st := s1) (gk := g1); try easy.
               - right. apply gmap_con with (st := s1) (gk := g1); try easy.
          }
        - destruct H8 as (G',H8). replace (gtt_send s s' ys0) with G' in *. clear H4 H7 H8.
          assert (p0 <> p). apply eqb_neq; try easy. 
          assert (p0 <> q). apply eqb_neq; try easy.
          {
            pose proof Ht as Htt.
            unfold wfgC in Htt. destruct Htt as (G1,(Hf,(Hg,(Hd,He)))). clear Hf Hg Hd. clear G1.
            clear H13 H14 H H12 H11 H10 H9 H6 H5 Ht.
            assert(gttstepC G G' p q l). pfold. easy. clear H0 H1 H2. clear s s' xs ys ys0.
            unfold balancedG in He. specialize(He nil). simpl in He.
            
            assert(exists k : fin,
       forall w'0 : list fin,
       gttmap G w'0 None gnode_end \/ length w'0 = k /\ (exists tc : gnode, gttmap G w'0 None tc) ->
       exists w2 w0 : list fin,
         w'0 = w2 ++ w0 /\
         (exists r : string, gttmap G w2 None (gnode_pq p0 r) \/ gttmap G w2 None (gnode_pq r p0))).
            {
              specialize(nil_word G); intros.
              destruct H0 as (tc1,H0).
              destruct H3.
              - specialize(word_step_back_s H H1); intros.
                destruct H2. specialize(He w' p0 q0 tc1). apply He; try easy.
                left. easy.
              - destruct H2 as (w0,(w1,(Hd,Hf))). specialize(He (w0 ++ l :: w1) p0 q0 tc1).
                apply He; try easy.
                left. easy.
              - specialize(word_step_back_s H H1); intros.
                destruct H2. specialize(He w' p0 q0 tc1). apply He; try easy.
                right. easy.
              - destruct H2 as (w0,(w1,(Hd,Hf))). specialize(He (w0 ++ l :: w1) p0 q0 tc1).
                apply He; try easy.
                right. easy.
            }
            clear He H3.
            
            destruct H0 as (k, H0). exists k.
            intros.
            destruct H1.
            - specialize(word_step_back_ss H H1); intros.
              destruct H2.
              - specialize(H0 w'0).
                assert(gttmap G w'0 None gnode_end \/ length w'0 = k /\ (exists tc : gnode, gttmap G w'0 None tc)).
                {
                  left. specialize(H2 w'0 nil gnode_end). apply H2; try easy.
                  apply eq_sym.
                  apply app_nil_r.
                }
                specialize(H0 H3). clear H3.
                destruct H0 as (w2,(w0,(Hta,(r,Htb)))).
                exists w2. exists w0. split. easy. exists r.
                destruct Htb.
                - specialize(H2 w2 w0 (gnode_pq p0 r)). left. apply H2; try easy.
                - specialize(H2 w2 w0 (gnode_pq r p0)). right. apply H2; try easy.
              - destruct H2 as (w0,(w1,(Hd,(He,(Hf,Hg))))). subst.
                pose proof Hf as Ht.
                specialize(Hf w1 nil gnode_end).
                assert(gttmap G (w0 ++ l :: w1) None gnode_end). apply Hf; try easy.
                apply eq_sym. apply app_nil_r.
                specialize(H0 (w0 ++ l :: w1)).
                assert(gttmap G (w0 ++ l :: w1) None gnode_end \/
     length (w0 ++ l :: w1) = k /\ (exists tc : gnode, gttmap G (w0 ++ l :: w1) None tc)). left. easy.
                specialize(H0 H3). clear H3.
                destruct H0 as (w2,(w3,(Hh,(r,Hi)))).
                clear Hc Hb Ha H H1 H2 Hf.
                specialize(decon_word w2 l w0 w1 w3 Hh); intros.
                - destruct H.
                  subst. destruct Hi.
                  specialize(inj_gttmap Hg H); intros. inversion H0. subst. easy.
                  specialize(inj_gttmap Hg H); intros. inversion H0. subst. easy.
                - destruct H.
                  destruct H as (wi,(wj,Hta)). subst.
                  specialize(He w2 wi wj). exists w2. exists (wi ++ wj :: w1).
                  split.
                  apply stword.
                  exists r. destruct Hi.
                  specialize(He (gnode_pq p0 r)). left. apply He; try easy.
                  specialize(He (gnode_pq r p0)). right. apply He; try easy.
                - destruct H as (wi,(wj,(Hta,Htb))). subst.
                  specialize(Ht wi wj). exists (w0 ++ wi). exists wj. split. 
                  apply app_assoc. exists r.
                  destruct Hi.
                  - left. apply Ht; try easy.
                  - right. apply Ht; try easy.
          - destruct H1 as (H1,(tc,H2)).
            specialize(word_step_back_ss H H2); intros.
            clear Hc Hb Ha H. clear Gl ct. clear w' gn.
            destruct H3.
            - assert(gttmap G w'0 None gnode_end \/
     length w'0 = k /\ (exists tc : gnode, gttmap G w'0 None tc)).
              {
                right. split. easy. exists tc.
                specialize(H w'0 nil). apply H; try easy.
                apply eq_sym. apply app_nil_r.
              }
              specialize(H0 w'0 H3). clear H3.
              destruct H0 as (w2,(w0,(Ha,(r,Hb)))).
              subst. exists w2. exists w0. split. easy. exists r.
              specialize(H w2 w0). destruct Hb.
              - left. apply H; try easy.
              - right. apply H; try easy.
            - destruct H as (w0,(w1,(Ha,(Hb,(Hc,Hd))))).
              assert(k <= S k). constructor. constructor.
              specialize(cut_further k (S k) G p0 H H0); intros. clear H H0.
              assert(gttmap G (w0 ++ l :: w1) None tc).
              {
                specialize(Hc w1 nil tc). apply Hc; try easy.
                apply eq_sym. apply app_nil_r; try easy. subst. easy.
              }
              specialize(H3 (w0 ++ l :: w1)).
              assert(gttmap G (w0 ++ l :: w1) None gnode_end \/
               length (w0 ++ l :: w1) = S k /\
               (exists tc : gnode, gttmap G (w0 ++ l :: w1) None tc)).
              {
                right. split. subst.
                clear H H3 Hd Hc Hb H2 H7 H4. clear p q G G' p0 q0 tc.
                revert w1 l. induction w0; intros; try easy.
                simpl in *. apply eq_S. apply IHw0; try easy.
                exists tc. easy.
              }
              specialize(H3 H0). clear H0.
              destruct H3 as (w2,(w3,(He,(r,Hf)))). subst.
              specialize(decon_word w2 l w0 w1 w3 He); intros.
              - destruct H0.
                subst.
                destruct Hf. 
                - specialize(inj_gttmap H0 Hd); intros. inversion H1. subst. easy.
                - specialize(inj_gttmap H0 Hd); intros. inversion H1. subst. easy.
              - destruct H0.
                destruct H0 as (wi,(wj,Hg)). subst.
                specialize(Hb w2 wi wj). exists w2. exists (wi ++ wj :: w1). 
                split. apply stword.
                exists r.
                destruct Hf.
                - left. apply Hb; try easy.
                - right. apply Hb; try easy.
              - destruct H0 as (wi,(wj,(Hg,Hh))). subst.
                specialize(Hc wi wj).
                exists (w0 ++ wi). exists wj. split. apply app_assoc.
                exists r.
                destruct Hf.
                - left. apply Hc; try easy.
                - right. apply Hc; try easy.
            }
      }
    - inversion H. subst.
      specialize(some_onth_implies_In n ys0 (st, gk) H17); intros.
      specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) ys0); intros.
      destruct H7. specialize(H7 H2). clear H8 H2.
      specialize(H7 (Some (st, gk)) H4). destruct H7; try easy.
      destruct H2 as (s1,(g1,(Hta,Htb))). inversion Hta. subst. clear H4 Hta.
      unfold balancedG in Htb.
      specialize(Htb w w' p0 q0 gn H18).
      assert(gttmap g1 (seq.cat w w') None (gnode_pq p0 q0) \/ gttmap g1 (seq.cat w w') None (gnode_pq q0 p0)).
      {
        destruct H3. left. inversion H2; try easy. subst. specialize(eq_trans (eq_sym H16) H17); intros.
        inversion H3. subst. easy.
        right. inversion H2; try easy. subst. specialize(eq_trans (eq_sym H16) H17); intros.
        inversion H3. subst. easy.
      }
      specialize(Htb H2). clear H2 H3.
      destruct Htb. exists x. intros.
      specialize(H2 w'0).
      assert(gttmap g1 (seq.cat w w'0) None gnode_end \/
     length w'0 = x /\ (exists tc : gnode, gttmap g1 (seq.cat w w'0) None tc)).
      {
        destruct H3. left.
        inversion H3. subst. specialize(eq_trans (eq_sym H19) H17); intros. inversion H4. subst.
        easy.
        destruct H3. destruct H4 as (tc, H4).
        right. split; try easy.
        exists tc. inversion H4. subst.
        specialize(eq_trans (eq_sym H20) H17); intros. inversion H3. subst.
        easy.
      }
      specialize(H2 H4).
      destruct H2 as (w2,(w0,(Hsa,Hsb))). exists w2. exists w0.
      split. easy. destruct Hsb as (r, Hsb). exists r.
      {
        destruct Hsb.
        left. apply gmap_con with (st := s1) (gk := g1); try easy.
        right. apply gmap_con with (st := s1) (gk := g1); try easy.
      }
    apply step_mon.
Qed.

Theorem wfgC_after_step : forall G G' p q n, wfgC G -> gttstepC G G' p q n -> projectableA G -> wfgC G'. 
Proof.
  intros. rename H1 into Htt. 
  pose proof H as Ht. unfold wfgC in H.
  destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))).
  specialize(wfgC_step_part G G' p q n Ht H0); intros.
  specialize(balanced_to_tree G p Ht H); intros. clear Ht H.
  destruct H1 as (Gt,(ctxG,(Hta,(Htb,(Htc,Htd))))).
  clear Htd.
  revert Htc Htb Hta H0 Hd Hc Hb Ha Htt.
  revert G G' p q n Gl ctxG.
  induction Gt using gtth_ind_ref; intros; try easy.
  - inversion Hta. subst.
    specialize(Forall_forall (fun u : option gtt =>
         u = None \/
         (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
            u = Some (gtt_send p q lsg) \/
            u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
    destruct H. specialize(H Htc). clear H1 Htc.
    specialize(some_onth_implies_In n ctxG G H2); intros.
    specialize(H (Some G) H1). destruct H; try easy. destruct H as (r,(lsg,Hsa)). clear H1.
    - destruct Hsa. inversion H. subst. 
      pinversion H0; try easy. subst. clear H6 H.
      specialize(guard_breakG_s2 (gtt_send p q lsg) Gl Hc Hb Ha); intros.
      clear Ha Hb Hc. clear Gl. destruct H as (Gl,(Ha,(Hb,(Hc,He)))).
      destruct Ha. subst. pinversion He. apply gttT_mon.
      destruct H as (p1,(q1,(lis1,H))). subst. pinversion He; try easy. subst.
      inversion Hc. subst.
      specialize(balanced_cont Hd); intros.
      specialize(guard_cont Hb); intros.
      specialize(wfgC_after_step_helper n0 s G' lsg lis1); intros.
      assert(exists G1 : global,
       onth n0 lis1 = Some (s, G1) /\
       gttTC G1 G' /\
       wfG G1 /\ balancedG G' /\ (forall n : fin, exists m : fin, guardG n m G1)).
      apply H4; try easy. clear H4. clear H3 H H7 H1.
      destruct H8 as (G1,(Hsa,(Hsb,(Htc,(Htd,Hte))))). exists G1. easy.
      apply gttT_mon.
      apply step_mon.
    - destruct H. inversion H. subst. pinversion H0; try easy. apply step_mon.
    - inversion H. subst. pinversion H0; try easy. apply step_mon.
  - inversion Hta. subst.
    assert(wfgC (gtt_send p q ys)).
    {
      unfold wfgC. exists Gl. easy.
    }
    rename H1 into Ht.
    pinversion H0; try easy.
    - subst. assert False. apply Htb. constructor. easy.
    subst. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    specialize(guard_breakG_s2 (gtt_send s s' ys) Gl Hc Hb Ha); intros. clear Ha Hb Hc. clear Gl.
    destruct H1 as (Gl,(Ha,(Hb,(Hc,He)))). destruct Ha. subst. pinversion He; try easy. apply gttT_mon.
    destruct H1 as (p1,(q1,(lis,H1))). subst. pinversion He; try easy. subst. inversion Hc. subst.
    specialize(balanced_cont Hd); intros.
    specialize(guard_cont Hb); intros.
    assert(List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ wfgC g)) ys0).
    {
      specialize(proj_forward s s' ys Ht Htt); intros. clear Ht Htt. rename H12 into Ht.
      clear H14 H13 Hb Hc He H16 H11 H10 H9 H8 H5 H4 H6 Hta H0 Hd.
      apply Forall_forall; intros. 
      destruct x.
      - specialize(in_some_implies_onth p0 ys0 H0); intros. destruct H4 as (n0 ,H4). clear H0.
        right. destruct p0. exists s0. exists g. split. easy.
        
        revert H4 H3 H1 H15 H2 H17 H7 Htc H Htb Ht.
        revert g s0 lis ys ys0 ctxG n p q xs s s'.
        induction n0; intros.
        - destruct ys0; try easy. destruct ys; try easy. destruct lis; try easy.
          destruct xs; try easy.
          inversion H3. subst. clear H3. inversion H1. subst. clear H1. inversion H15. subst. clear H15.
          inversion H2. subst. clear H2. inversion H17. subst. clear H17. inversion H7. subst. clear H7.
          inversion H. subst. clear H. inversion Ht. subst. clear Ht.
          clear H8 H9 H10 H14 H15 H17 H7.
          simpl in H4. subst.
          destruct H11; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Hb. subst.
          destruct H13; try easy. destruct H as (s2,(g3,(g4,(Hd,(He,Hf))))). inversion He. subst.
          destruct H12; try easy. destruct H as (s3,(g5,(g6,(Hg,(Hh,Hi))))). inversion Hh. subst.
          destruct H3; try easy. destruct H as (s4,(g7,(Hj,Hk))). inversion Hj. subst.
          destruct H6; try easy. destruct H as (s5,(g8,(Hl,Hm))). inversion Hl. subst.
          destruct H5; try easy. destruct H as (s6,(g9,(Hn,Ho))). inversion Hn. subst.
          destruct H2; try easy. clear Hn Hh He Hj Hl Hb.
          destruct H as (s7,(g10,(Hp,Hq))). inversion Hp. subst.
          destruct H1; try easy. destruct H as (s8,(g11,(Hr,Hs))). inversion Hr. subst.
          specialize(Hq g11 g2 p q n g8 ctxG). unfold wfgC.
          apply Hq; try easy. 
          specialize(ishParts_x Htb); try easy.
          destruct Hc; try easy.
          destruct Hi; try easy. 
        - destruct ys0; try easy. destruct ys; try easy. destruct lis; try easy.
          destruct xs; try easy.
          inversion H3. subst. clear H3. inversion H1. subst. clear H1. inversion H15. subst. clear H15.
          inversion H2. subst. clear H2. inversion H17. subst. clear H17. inversion H7. subst. clear H7.
          inversion H. subst. clear H. inversion Ht. subst. clear Ht.
          specialize(IHn0 g s0 lis ys ys0 ctxG n p q xs s s').
          apply IHn0; try easy.
          specialize(ishParts_hxs Htb); try easy.
        left. easy.
    }
    specialize(wfgC_after_step_helper2 lis ys ys0 n p q H13 H2 H17); intros.
    assert(wfgC (gtt_send s s' ys) /\ gttstepC (gtt_send s s' ys) (gtt_send s s' ys0) p q n). 
    {
      unfold wfgC. split. exists (g_send s s' lis). split. pfold. easy. easy.
      pfold. easy.
    }
    destruct H19.
    specialize(balanced_step H19 H20 Htt); intros. clear H19 H20 Htt Ht. rename H21 into Ht.
    clear H3 H1 H15 H2 Hb Hc He H17 H16 H11 H10 H9 H8 H5 H4 H7 Hta H0 Hd Htb Htc H H6 H13.
    clear p q xs n ctxG ys lis. rename H14 into H. rename H12 into H1.
    assert(exists xs, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ gttTC g g')) xs ys0 /\ 
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ balancedG g)) ys0 /\
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfG g)) xs /\
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ (forall n, exists m, guardG n m g))) xs).
    {
      clear H. revert H1. clear H18. clear Ht. revert ys0. clear s s'.
      induction ys0; intros; try easy.
      - exists nil. easy.
      - inversion H1. subst. clear H1.
        specialize(IHys0 H3). destruct IHys0 as (xs,H).
        destruct H2. 
        - subst. exists (None :: xs).
          split. constructor; try easy. left. easy.
          split. constructor; try easy. left. easy.
          split. constructor; try easy. left. easy.
          constructor; try easy. left. easy.
        - destruct H0 as (s,(g,(Ha,Hb))). subst.
          unfold wfgC in Hb. destruct Hb.
          exists (Some(s, x) :: xs).
          split. constructor; try easy. right. exists s. exists x. exists g. easy.
          split. constructor; try easy. right. exists s. exists g. easy.
          split. constructor; try easy. right. exists s. exists x. easy.
          constructor; try easy. right. exists s. exists x. easy.
    }
    destruct H0 as (xs,(Ha,(Hb,(Hc,Hd)))).
    exists (g_send s s' xs).
    - split. pfold. constructor; try easy.
      revert Ha. apply Forall2_mono; intros; try easy. destruct H0. left. easy.
      destruct H0 as (s0,(g0,(g1,(Hta,(Htb,Htc))))). subst. right. exists s0. exists g0. exists g1. 
      split. easy. split. easy. left. easy.
    - split. constructor; try easy.
      specialize(wfgC_after_step_helper3 ys0 xs H18 Ha); try easy.
    - split.
      apply guard_cont_b; try easy.
    - easy.
    apply gttT_mon.
    apply step_mon.
Qed.
