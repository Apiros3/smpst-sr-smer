From SST Require Export type.global type.local type.isomorphism type.projection type.merge.
Require Import List String Datatypes ZArith Relations PeanoNat. 
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.

Lemma _3_19_ctx_loose : forall [ctxG p q l T T' SI],
     Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s', Gjk) /\
              projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option sort) =>
              u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s))
             lsg SI)) ctxG ->
      Forall
        (fun u : option gtt =>
         u = None \/
         (exists (g : gtt) (lsg : list (option (sort * gtt))),
            u = Some g /\
            g = gtt_send p q lsg /\
            (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
               onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG.
Proof.
  intros.
  apply Forall_forall; intros.
  specialize(Forall_forall (fun u : option gtt =>
       u = None \/
       (exists (g : gtt) (lsg : list (option (sort * gtt))),
          u = Some g /\
          g = gtt_send p q lsg /\
          (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
             onth l lsg = Some (s', Gjk) /\
             projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
          Forall2
            (fun (u0 : option (sort * gtt)) (v : option sort) =>
             u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s)) lsg
            SI)) ctxG); intros.
  destruct H1. specialize(H1 H). clear H H2.
  destruct x. 
  specialize(H1 (Some g) H0). destruct H1; try easy.
  - destruct H. destruct H. destruct H. destruct H1. destruct H2.
    destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4. destruct H5. destruct H6.
    subst.
    inversion H. subst.
    right. exists (gtt_send p q x0). exists x0. split; try easy. split; try easy.
    exists x1. exists x2. exists x3. exists x4. easy.
  left. easy.
Qed.




Lemma proj_inv_lis_helper : forall n ys s0 g xs ys0 ys1 ctxG p q,
    onth n ys = Some (s0, g) -> 
    Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys ->
    Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys ->
    Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) ys ys0 ->
    Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) ys ys1 -> 
    exists g' t t',
    onth n xs = Some(s0, g') /\ typ_gtth ctxG g' g /\
    onth n ys0 = Some t /\ projectionC g q t /\
    onth n ys1 = Some t' /\ projectionC g p t' /\ wfgC g.
Proof.
  induction n; intros; try easy.
  - destruct ys; try easy. destruct xs; try easy. destruct ys0; try easy. destruct ys1; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1.
    inversion H2. subst. clear H2. inversion H3. subst. clear H3.
    simpl in H. subst.
    destruct H6; try easy. destruct H as (st,(g1,(Ha,Hb))). inversion Ha. subst. clear Ha.
    destruct H5; try easy. destruct H as (st1,(g2,(t1,(Hc,(Hd,He))))). inversion Hc. subst. clear Hc.
    destruct H4; try easy. destruct H as (st2,(g3,(t2,(Hf,(Hg,Hh))))). inversion Hf. subst. clear Hf.
    destruct H8; try easy. destruct H as (st3,(g4,(g5,(Hi,(Hj,Hk))))). inversion Hj. subst. clear Hj.
    simpl. exists g4. exists t1. exists t2. destruct He; try easy. destruct Hh; try easy.
  - destruct ys; try easy. destruct xs; try easy. destruct ys0; try easy. destruct ys1; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1.
    inversion H2. subst. clear H2. inversion H3. subst. clear H3.
    specialize(IHn ys s0 g xs ys0 ys1 ctxG p q). apply IHn; try easy.
Qed.

Lemma _3_19_step_helper3 : forall xs ys ctxG,
      SList xs ->
      Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys ->
      SList ys.
Proof.
  induction xs; intros; try easy.
  specialize(SList_f a xs H); intros.
  destruct ys; try easy. inversion H0.
  subst.
  destruct H1; try easy.
  - specialize(IHxs ys ctxG). apply SList_b. apply IHxs; try easy.
  - destruct H1. destruct H2. subst. destruct ys; try easy. destruct H5; try easy.
    destruct H1. destruct H1. destruct H1. destruct H1. destruct H2. subst. easy.
Qed.

Lemma proj_inv_lis_helper2 : forall ys2 ys3 ys4 p q,
          SList ys2 -> 
          Forall2
            (fun (u : option (sort * gtt)) (v : option ltt) =>
             u = None /\ v = None \/
             (exists (s : sort) (g : gtt) (t : ltt),
                u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) ys2 ys3 -> 
          Forall2
            (fun (u : option (sort * gtt)) (v : option ltt) =>
             u = None /\ v = None \/
             (exists (s : sort) (g : gtt) (t : ltt),
                u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) ys2 ys4 ->
          Forall
             (fun u : option (sort * gtt) =>
              u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys2 -> 
          exists n st g t t', 
          onth n ys2 = Some (st, g) /\ wfgC g /\
          onth n ys3 = Some t /\ projectionC g p t /\
          onth n ys4 = Some t' /\ projectionC g q t'.
Proof.
  induction ys2; intros; try easy.
  destruct ys3; try easy. destruct ys4; try easy.
  inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
  specialize(SList_f a ys2 H); intros.
  specialize(IHys2 ys3 ys4 p q).
  destruct H0. 
  assert (exists (n : fin) (st : sort) (g : gtt) (t t' : ltt),
          onth n ys2 = Some (st, g) /\
          wfgC g /\
          onth n ys3 = Some t /\ projectionC g p t /\ onth n ys4 = Some t' /\ projectionC g q t').
  apply IHys2; try easy. destruct H1. exists (S x). easy.
  destruct H0. destruct H1. subst. clear H4 H9 H8 IHys2 H. exists 0. simpl.
  destruct H6; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
  destruct H3; try easy. destruct H as (s2,(g2,(Hd,He))). inversion Hd. subst.
  destruct H5; try easy. destruct H as (s3,(g3,(t2,(Hf,(Hg,Hh))))).
  inversion Hf. subst.
  exists s3. exists g3. exists t1. exists t2. destruct Hc; try easy. destruct Hh; try easy.
Qed.

Lemma proj_inv_lis_helper3 : forall [l lsg s2 Gjk ys2 ys3 p q],
          onth l lsg = Some (s2, Gjk) ->
          Forall2
          (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
           u = None /\ v = None \/
           (exists (s : sort) (g : gtt) (t : ltt),
              u = Some (s, g) /\ v = Some (s, t) /\ upaco3 projection bot3 g q t)) lsg ys2 -> 
          Forall2
          (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
           u = None /\ v = None \/
           (exists (s : sort) (g : gtt) (t : ltt),
              u = Some (s, g) /\ v = Some (s, t) /\ upaco3 projection bot3 g p t)) lsg ys3 -> 
          exists T T' : sort * ltt, onth l ys3 = Some T /\ onth l ys2 = Some T'.
Proof.
  induction l; intros; try easy.
  - destruct lsg; try easy. destruct ys2; try easy. destruct ys3; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. simpl in H. subst.
    destruct H5; try easy. destruct H as (s,(g,(t,(Ha,(Hb,Hc))))). inversion Ha. subst.
    destruct H4; try easy. destruct H as (s1,(g1,(t1,(Hd,(He,Hf))))). inversion Hd. subst.
    simpl. exists (s1, t1). exists (s1, t). easy.
  - destruct lsg; try easy. destruct ys2; try easy. destruct ys3; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. simpl in H. subst.
    specialize(IHl lsg s2 Gjk ys2 ys3 p q). apply IHl; try easy.
Qed.

Lemma proj_inv_lis : forall p q l s s' ys LP LQ S T S' T',
    wfgC (gtt_send s s' ys) ->
    projectionC (gtt_send s s' ys) p (ltt_send q LP) -> 
    onth l LP = Some (S, T) ->
    projectionC (gtt_send s s' ys) q (ltt_recv p LQ) -> 
    onth l LQ = Some (S', T') ->
    (s = p /\ s' = q /\ exists Gk, onth l ys = Some Gk) \/
    (s <> p /\ s' <> q /\ List.Forall (fun u => u = None \/ 
        (exists s g LP' LQ' T T', u = Some(s, g) /\ projectionC g p (ltt_send q LP') /\ projectionC g q (ltt_recv p LQ') /\ 
          onth l LP' = Some T /\ onth l LQ' = Some T')) ys).
Proof.
  intros.
  specialize(_a_29_s (gtt_send s s' ys) p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
  destruct H4. destruct H4. destruct H4. destruct H4. destruct H4. destruct H5. destruct H6.
  rename x0 into ctxG. rename x into Gl.
  destruct H7.
  specialize(_3_19_ctx_loose H7); intros. clear H7 H8 H3 H1.
  revert H9 H6 H5 H4 H2 H0 H.
  revert p q l s s' ys LP LQ ctxG. clear S T S' T' x1 x2.
  induction Gl using gtth_ind_ref; intros; try easy.
  - inversion H4. subst. 
    specialize(some_onth_implies_In n ctxG (gtt_send s s' ys) H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG); intros.
    destruct H3. specialize(H3 H9). clear H8 H9.
    specialize(H3 (Some (gtt_send s s' ys)) H1); intros.
    destruct H3; try easy. destruct H3. destruct H3. destruct H3. destruct H8. subst.
    inversion H3. subst. clear H3.
    destruct H9. destruct H3. destruct H3. destruct H3. destruct H3.
    left. split. easy. split. easy. exists (x, x1). easy.
  - inversion H4. subst.
    pinversion H2. subst. assert False. apply H6. constructor. easy.
    subst. clear H14. rename H18 into H14. rename H19 into H18. 
    pinversion H0; try easy. subst. clear H20. rename H23 into H20. rename H24 into H23.
    rename p0 into p. rename q0 into q.
    specialize(wfgC_after_step_all H11 H1); intros. clear H1.
    right. split. easy. split. easy.
    apply Forall_forall; intros. destruct x.
    right. destruct p0. exists s0. exists g.
    specialize(in_some_implies_onth (s0, g) ys H1); intros. destruct H7. rename x into n. clear H1.
    clear H2 H0 H4.
    specialize(proj_inv_lis_helper n ys s0 g xs ys0 ys1 ctxG p q); intros.
    assert(exists (g' : gtth) (t t' : ltt),
       onth n xs = Some (s0, g') /\
       typ_gtth ctxG g' g /\
       onth n ys0 = Some t /\ projectionC g q t /\ onth n ys1 = Some t' /\ projectionC g p t' /\ wfgC g).
    apply H0; try easy. clear H0 H3 H17 H15.
    destruct H1 as (g',(t,(t',(Ha,(Hb,(Hc,(Hd,(He,(Hf,Hg))))))))).
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (p q : string) (l : fin) (s0 s' : string) (ys : list (option (sort * gtt)))
             (LP LQ : list (option (sort * ltt))) (ctxG : list (option gtt)),
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
                    onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG ->
           (ishParts q g -> False) ->
           (ishParts p g -> False) ->
           typ_gtth ctxG g (gtt_send s0 s' ys) ->
           projectionC (gtt_send s0 s' ys) q (ltt_recv p LQ) ->
           projectionC (gtt_send s0 s' ys) p (ltt_send q LP) ->
           wfgC (gtt_send s0 s' ys) ->
           s0 = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
           s0 <> p /\
           s' <> q /\
           Forall
             (fun u0 : option (sort * gtt) =>
              u0 = None \/
              (exists (s1 : sort) (g0 : gtt) (LP' LQ' : list (option (sort * ltt))) 
               (T T' : sort * ltt),
                 u0 = Some (s1, g0) /\
                 projectionC g0 p (ltt_send q LP') /\
                 projectionC g0 q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys)))
      xs); intros. destruct H0. specialize(H0 H). clear H H1.
      specialize(some_onth_implies_In n xs (s0, g') Ha); intros.
      specialize(H0 (Some (s0, g')) H). clear H.
      destruct H0; try easy. destruct H as (s1,(g1,(H1,H2))).
      specialize(H2 p q l). inversion H1. subst. clear H1.
      
      inversion Hb.
      - subst.
        specialize(some_onth_implies_In n0 ctxG g H); intros.
        specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG); intros.
        destruct H1. specialize(H1 H9). clear H3 H9.
        specialize(H1 (Some g) H0). destruct H1; try easy.
        destruct H1 as (g2,(lsg,(H3,(H4,H8)))). subst. inversion H3. subst. clear H3.
        pinversion Hd; try easy. subst. assert False. apply H1. apply triv_pt_q; try easy. easy.
        subst. clear H15.
        pinversion Hf; try easy. subst. assert False. apply H1. apply triv_pt_p; try easy. easy.
        subst. clear H17.
        exists ys3. exists ys2.
        destruct H8 as (s2,(Gjk,(Tp,(Tq,(Hm,Ht))))). 
        assert(exists T T', onth l ys3 = Some T /\ onth l ys2 = Some T').
        {
          specialize(proj_inv_lis_helper3 Hm H22 H26); intros; try easy.
        }
        destruct H1 as (T,(T',(Ht1,Ht2))). exists T. exists T'. split. easy. split. pfold.
        easy. split. pfold. easy. easy.
      apply proj_mon.
      apply proj_mon.
      - subst. rename p0 into s0. rename q0 into s0'.
        specialize(H2 s0 s0' ys2).
        assert(exists LP' LQ', projectionC (gtt_send s0 s0' ys2) p (ltt_send q LP') /\ projectionC (gtt_send s0 s0' ys2) q (ltt_recv p LQ')).
        {
          specialize(merge_onth_recv n p LQ ys0 t H18 Hc); intros. destruct H1. subst.
          specialize(merge_onth_send n q LP ys1 t' H23 He); intros. destruct H1. subst. exists x0. exists x.
          easy.
        }
        destruct H1 as (LP',(LQ',(Ht1,Ht2))).
        specialize(H2 LP' LQ' ctxG).
        assert(s0 = p /\ s0' = q /\ (exists Gk : sort * gtt, onth l ys2 = Some Gk) \/
           s0 <> p /\
           s0' <> q /\
           Forall
             (fun u0 : option (sort * gtt) =>
              u0 = None \/
              (exists (s1 : sort) (g0 : gtt) (LP' LQ' : list (option (sort * ltt))) 
               (T T' : sort * ltt),
                 u0 = Some (s1, g0) /\
                 projectionC g0 p (ltt_send q LP') /\
                 projectionC g0 q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys2).
        {
          apply H2; try easy.
          - specialize(ishParts_n H6 Ha); intros. apply H1; try easy.
          - specialize(ishParts_n H5 Ha); intros. apply H1; try easy.
        }
        exists LP'. exists LQ'. 
        destruct H1.
        - destruct H1 as (Hs1,(Hs2,Hs3)). destruct Hs3. subst.
          assert False. apply H6. apply ha_sendr with (n := n) (s := s1) (g := gtth_send p q xs0); try easy.
          constructor. easy.
        - destruct H1 as (Hs1,(Hs2,Hs3)).
          specialize(_3_19_step_helper3 xs0 ys2 ctxG H H0); intros.
          clear H2.
          pinversion Ht1; try easy. subst.
          pinversion Ht2; try easy. subst.
          specialize(wfgC_after_step_all H8 Hg); intros.
          specialize(proj_inv_lis_helper2 ys2 ys3 ys4 p q); intros.
          assert(exists (n : fin) (st : sort) (g : gtt) (t t' : ltt),
       onth n ys2 = Some (st, g) /\
       wfgC g /\ onth n ys3 = Some t /\ projectionC g p t /\ onth n ys4 = Some t' /\ projectionC g q t').
          apply H3; try easy. clear H3.
          destruct H4 as (n',(st,(g3,(t1,(t2,(Hta,(Htb,(Htc,(Htd,(Hte,Htf)))))))))).
          specialize(Forall_forall (fun u0 : option (sort * gtt) =>
         u0 = None \/
         (exists (s1 : sort) (g0 : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u0 = Some (s1, g0) /\
            projectionC g0 p (ltt_send q LP') /\
            projectionC g0 q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys2); intros.
          destruct H3. specialize(H3 Hs3). clear Hs3 H4.
          specialize(some_onth_implies_In n' ys2 (st, g3) Hta); intros.
          specialize(H3 (Some (st, g3)) H4); intros. destruct H3; try easy.
          destruct H3 as (s3,(g0,(LP0',(LQ0',(T,(T',(Hsa,(Hsb,(Hsc,(Hsd,Hse)))))))))). inversion Hsa. subst.
          specialize(proj_inj Htb Htd Hsb); intros. subst. 
          specialize(proj_inj Htb Htf Hsc); intros. subst.
          specialize(merge_label_send ys3 LP' LP0' T n' l q H26 Htc Hsd); intros. destruct H3. exists x.
          specialize(merge_label_recv ys4 LQ' LQ0' T' n' l p H32 Hte Hse); intros. destruct H29. exists x0.
          split. easy. split. pfold. easy. split. pfold. easy. easy.
        apply proj_mon.
        apply proj_mon.
        left. easy.
      apply proj_mon.
      apply proj_mon.
Qed.

Lemma projection_step_label : forall G G' p q l LP LQ,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  projectionC G q (ltt_recv p LQ) ->
  gttstepC G G' p q l ->
  exists LS LS' LT LT', onth l LP = Some(LS, LT) /\ onth l LQ = Some(LS', LT').
Proof.
  intros.
  specialize(_a_29_11 G p q LP H H0); intros.
  destruct H3. rename x into Gl.
  assert (exists ctxJ : list (option gtt),
       typ_gtth ctxJ Gl G /\
       (ishParts p Gl -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (g : gtt) (lsg : list (option (sort * gtt))),
             u = Some g /\
             g = gtt_send p q lsg)) ctxJ). 
  {
    destruct H3. exists x. destruct H3. destruct H4. split. easy. split. easy.
    clear H4 H3 H2 H1 H0 H. destruct H5 as (H5,H0). clear H0.  clear Gl LQ l. clear G G'.
    revert H5. revert LP p q. induction x; intros; try easy.
    inversion H5. subst. clear H5. specialize(IHx LP p q H2). constructor; try easy. clear H2 IHx.
    destruct H1. left. easy.
    destruct H. destruct H. destruct H. destruct H0. right. exists x0. exists x1. easy.
  } 
  clear H3. rename H4 into H3.
  revert H0 H1 H2 H3. clear H.
  revert G G' p q l LP LQ.
  induction Gl using gtth_ind_ref; intros; try easy.
  - destruct H3. destruct H. destruct H3. inversion H. subst. 
    specialize(some_onth_implies_In n x G H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg)) x); intros.
    destruct H6. specialize(H6 H4). clear H8. specialize(H6 (Some G) H5). clear H5 H4.
    destruct H6; try easy. destruct H4. destruct H4. destruct H4. inversion H4.
    subst.
    pinversion H1; try easy. subst.
    pinversion H2; try easy. subst.
    pinversion H0; try easy. subst.
    clear H16 H20 H19 H15 H14 H17 H10 H12 H11 H7 H3 H H0 H1 H2 H4. clear n x.
    revert H13 H18 H21. revert G' p q LP LQ x1 s.
    induction l; intros; try easy.
    - destruct x1; try easy.
      destruct LP; try easy. destruct LQ; try easy.
      inversion H21. subst. clear H21. inversion H13. subst. clear H13. 
      simpl in *. subst.
      destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H. subst.
      destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2.
      inversion H0. subst.
      exists x3. exists x3. exists x2. exists x5. easy.
    - destruct x1; try easy.
      destruct LP; try easy. destruct LQ; try easy.
      inversion H21. subst. clear H21. inversion H13. subst. clear H13. 
      specialize(IHl G' p q LP LQ x1 s). apply IHl; try easy.
    apply proj_mon.
    apply step_mon. 
    apply proj_mon.
  - destruct H3. destruct H3. destruct H4. 
    rename p into s. rename q into s0. rename p0 into p. rename q0 into q.
    specialize(_a_29_part x (gtth_send s s0 xs) G p q LP LQ H3 H0 H1 H4); intros.
    inversion H3. subst.
    pinversion H1. subst.
    - assert False. apply H4. constructor. easy.
    pinversion H0; try easy. subst. 
    specialize(SList_to_In xs H12); intros. destruct H7.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G G' : gtt) (p q : string) (l : fin) (LP LQ : list (option (sort * ltt))),
           projectionC G p (ltt_send q LP) ->
           projectionC G q (ltt_recv p LQ) ->
           gttstepC G G' p q l ->
           (exists ctxJ : list (option gtt),
              typ_gtth ctxJ g G /\
              (ishParts p g -> False) /\
              Forall
                (fun u0 : option gtt =>
                 u0 = None \/
                 (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                    u0 = Some g0 /\
                    g0 = gtt_send p q lsg)) ctxJ) ->
           exists (LS LS' : sort) (LT LT' : ltt),
             onth l LP = Some (LS, LT) /\ onth l LQ = Some (LS', LT')))) xs); intros.
    destruct H8. specialize(H8 H). clear H H9.
    specialize(H8 (Some x0) H7). destruct H8; try easy. destruct H. destruct H.
    destruct H. inversion H. subst. clear H. rename x2 into G.
    specialize(in_some_implies_onth (x1, G) xs H7); intros. destruct H. clear H7. rename x0 into n.
    rename x into ctxG.
    pinversion H2; try easy. subst.
    assert(exists g g' t t', onth n ys = Some(x1, g) /\ typ_gtth ctxG G g /\ onth n ys0 = Some t /\ projectionC g q t /\
           onth n ys1 = Some t' /\ projectionC g p t' /\ onth n ys2 = Some (x1, g') /\ gttstepC g g' p q l).
    {
      clear H35 H28 H27 H22 H21 H20 H17 H8 H30 H26 H25 H24 H23 H19 H15 H14 H11 H10 H12 H6 H5 H3 H0 H1 H2 H4.
      clear LP LQ. clear s s0.
      revert H H36 H29 H18 H13. 
      revert xs p q ys ctxG ys0 ys1 x1 G. revert l ys2.
      induction n; intros; try easy.
      - destruct xs; try easy.
        destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H36. subst. inversion H29. subst. inversion H18. subst. inversion H13. subst.
        clear H36 H29 H18 H13.
        simpl in *. subst.
        destruct H8; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
        destruct H6; try easy. destruct H as (s2,(g3,(t1,(Hd,(He,Hf))))). inversion Hd. subst.
        destruct H2; try easy. destruct H as (s3,(g4,(g5,(Hg,(Hh,Hi))))). inversion Hg. subst.
        destruct H5; try easy. destruct H as (s4,(g6,(t2,(Hj,(Hk,Hl))))). inversion Hj. subst.
        exists g6. exists g5. exists t1. exists t2. pclearbot. easy.
      - destruct xs; try easy.
        destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H36. subst. inversion H29. subst. inversion H18. subst. inversion H13. subst. apply IHn with (xs := xs); try easy.
    }
    destruct H7. destruct H7. destruct H7. destruct H7. destruct H7. destruct H9. destruct H16. destruct H31.
    destruct H32. destruct H33. destruct H34. 
    rename x into G0'. rename x2 into LP0. rename x3 into LQ0. rename x0 into G''.
    specialize(H8 G0' G'' p q l).
    specialize(merge_onth_recv n p LQ ys0 LP0 H19 H16); intros. destruct H38 as [LQ' H38].
    specialize(merge_onth_send n q LP ys1 LQ0 H30 H32); intros. destruct H39 as [LP' H39].
    subst.
    specialize(H8 LP' LQ' H33 H31 H37).
    assert (exists (LS LS' : sort) (LT LT' : ltt), onth l LP' = Some (LS, LT) /\ onth l LQ' = Some (LS', LT')).
    {
      apply H8; try easy.
      exists ctxG. split. easy. split; try easy.
      intros. apply H4.
      - case_eq (eqb p s); intros.
        assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
      - case_eq (eqb p s0); intros.
        assert (p = s0). apply eqb_eq; try easy. subst. apply ha_sendq.
      - assert (p <> s). apply eqb_neq; try easy. 
        assert (p <> s0). apply eqb_neq; try easy.
        apply ha_sendr with (n := n) (s := x1) (g := G); try easy.
    }
    destruct H38. destruct H38. destruct H38. destruct H38. destruct H38. 
    
    specialize(merge_label_send ys1 LP LP' (x, x2) n l q H30 H32 H38); intros.
    destruct H40. 
    specialize(merge_label_recv ys0 LQ LQ' (x0, x3) n l p H19 H16 H39); intros.
    destruct H41. destruct x4. destruct x5.
    exists s1. exists s2. exists l0. exists l1. easy.
  apply step_mon.
  apply proj_mon.
  apply proj_mon.
Qed.

Lemma projection_step_label_s : forall G p q l LP LQ ST,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some ST -> 
  projectionC G q (ltt_recv p LQ) ->
  exists LS' LT', onth l LQ = Some(LS', LT').
Proof.
  intros.
  specialize(_a_29_11 G p q LP H H0); intros.
  destruct H3. rename x into Gl.
  assert (exists ctxJ : list (option gtt),
       typ_gtth ctxJ Gl G /\
       (ishParts p Gl -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (g : gtt) (lsg : list (option (sort * gtt))),
             u = Some g /\
             g = gtt_send p q lsg)) ctxJ). 
  {
    destruct H3. exists x. destruct H3. destruct H4. split. easy. split. easy.
    clear H4 H3 H2 H1 H0 H. destruct H5 as (H5, H0). clear H0. clear Gl LQ l. clear G.
    revert H5. revert LP p q. induction x; intros; try easy.
    inversion H5. subst. clear H5. specialize(IHx LP p q H2). constructor; try easy. clear H2 IHx.
    destruct H1. left. easy.
    destruct H. destruct H. destruct H. destruct H0. right. exists x0. exists x1. easy.
  }
  clear H3. clear H.
  revert H4 H2 H1 H0. revert G p q l LP LQ ST.
  induction Gl using gtth_ind_ref; intros.
  - destruct H4. destruct H. destruct H3.
    inversion H. subst. 
    specialize(some_onth_implies_In n x G H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg)) x); intros.
    destruct H6. specialize(H6 H4 (Some G) H5). clear H4 H8.
    destruct H6; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst.
    pinversion H0; try easy. subst.
    pinversion H2; try easy. subst.
    clear H11 H15 H11 H12 H0 H7 H5 H2 H3 H H4. clear H17 H16 H13. clear n x.
    revert H18 H14 H1. revert p q LP LQ ST x1.
    induction l; intros.
    - destruct LP; try easy. destruct x1; try easy. destruct LQ; try easy.
      inversion H18. inversion H14. subst. clear H18 H14.
      simpl in H1. subst.
      destruct H9; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H0. subst.
      destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H2.
      inversion H. subst. 
      exists x3. exists x5. easy.
    - destruct LP; try easy. destruct x1; try easy. destruct LQ; try easy.
      inversion H18. inversion H14. subst. clear H18 H14.
      specialize(IHl p q LP LQ ST x1). apply IHl; try easy.
    apply proj_mon. 
    apply proj_mon.
  - destruct H4. destruct H3. destruct H4. 
    inversion H3. subst.
    specialize(SList_to_In xs H11); intros. destruct H6.
    specialize(in_some_implies_onth x0 xs H6); intros. destruct H7. rename x1 into n.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G : gtt) (p q : string) (l : fin) (LP LQ : list (option (sort * ltt)))
             (ST : sort * ltt),
           (exists ctxJ : list (option gtt),
              typ_gtth ctxJ g G /\
              (ishParts p g -> False) /\
              Forall
                (fun u0 : option gtt =>
                 u0 = None \/
                 (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                    u0 = Some g0 /\ g0 = gtt_send p q lsg)) ctxJ) ->
           projectionC G q (ltt_recv p LQ) ->
           onth l LP = Some ST ->
           projectionC G p (ltt_send q LP) ->
           exists (LS' : sort) (LT' : ltt), onth l LQ = Some (LS', LT')))) xs); intros.
    destruct H8. specialize(H8 H (Some x0) H6). clear H9 H. destruct H8; try easy.
    destruct H. destruct H. destruct H. inversion H. subst.
    pinversion H0. subst.
    assert False. apply H4. constructor. easy.
    subst.
    pinversion H2; try easy. subst.
    rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    rename x1 into s0. rename x2 into g. rename x into ctxG.
    clear H H6 H11 H2 H0 H3.
    assert(exists g' t t', onth n ys = Some (s0, g') /\ typ_gtth ctxG g g' /\ onth n ys0 = Some t /\ projectionC g' p t 
          /\ onth n ys1 = Some t' /\ projectionC g' q t').
    {
      clear H27 H23 H22 H19 H18 H21 H17 H16 H15 H14 H8 H1 H5 H4. 
      clear ST LP LQ. clear s s'. clear l.
      revert H26 H20 H12 H7. revert xs p q ctxG ys s0 g ys0 ys1.
      induction n; intros.
      - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H26. inversion H20. inversion H12. subst. clear H26 H20 H12.
        simpl in H7. subst.
        destruct H16; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        destruct H9; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
        inversion H. subst. clear H.
        simpl. exists x1. exists x4. exists x5. pclearbot. easy.
      - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H26. inversion H20. inversion H12. subst. clear H26 H20 H12.
        specialize(IHn xs p q ctxG ys s0 g ys0 ys1). apply IHn; try easy.
    }
    destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H2. destruct H3. destruct H6.
    rename x into g'. 
    specialize(merge_onth_recv n p LQ ys1 x1 H27 H6); intros. destruct H10. subst.
    specialize(merge_onth_send n q LP ys0 x0 H21 H2); intros. destruct H10. subst.
    rename x1 into LP'. rename x into LQ'.
    
    specialize(H8 g' p q l LP' LQ' ST).
    specialize(merge_label_sendb ys0 LP LP' ST n l q H21 H2 H1); intros. 
    assert (exists (LS' : sort) (LT' : ltt), onth l LQ' = Some (LS', LT')).
    {
      apply H8; try easy.
      exists ctxG. split; try easy. split; try easy.
      intros. apply H4. apply ha_sendr with (n := n) (s := s0) (g := g); try easy.
      
    }
    destruct H11. destruct H11.
    specialize(merge_label_recv ys1 LQ LQ' (x, x0) n l p H27 H6 H11); intros. destruct H13.
    destruct x1. exists s1. exists l0. easy.
  apply proj_mon.
  apply proj_mon.
Qed.


Lemma _3_19_step_helper2 : forall xs ys p q l ctxG,
    Forall2
       (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (g' : gtt),
           u = Some (s, g) /\
           v = Some (s, g') /\
           typ_gtth ctxG g g' /\
           isgPartsC p g' /\ isgPartsC q g' /\ (exists G' : gtt, gttstepC g' G' p q l))) xs
       ys -> 
    exists zs,
    Forall (fun u => (u = None) \/ (exists s g, u = Some(s, g) /\ isgPartsC p g /\ isgPartsC q g)) ys /\ 
    Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ gttstepC g g' p q l)) ys zs.
Proof.
  induction xs; intros; try easy.
  - destruct ys; try easy. exists nil. easy.
  - destruct ys; try easy. inversion H. subst. clear H.
    specialize(IHxs ys p q l ctxG H5). destruct IHxs. rename x into zs.
    clear H5. destruct H. destruct H3.
    - exists (None :: zs). destruct H1. subst.
      split. constructor; try easy. left. easy.
      constructor; try easy. left. easy.
    - destruct H1. destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. destruct H4. destruct H5.
      destruct H6. exists (Some (x, x2) :: zs). subst. split.
      constructor; try easy. right. exists x. exists x1. easy.
      constructor; try easy. right. exists x. exists x1. exists x2. easy.
Qed.



Lemma _3_19_step_helper4 : forall ys zs p q l,
      SList ys ->
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ gttstepC g g' p q l)) ys zs ->
      p <> q.
Proof.
  induction ys; intros; try easy.
  specialize(SList_f a ys H); intros. destruct zs; try easy.
  inversion H0. subst.
  destruct H1.
  specialize(IHys zs p q l H1 H7). easy. destruct H1. destruct H2. subst.
  destruct zs; try easy. clear IHys H7 H0.
  destruct H5; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
  inversion H0. subst.
  pinversion H2; try easy.
  apply step_mon.
Qed. 


Lemma _3_19_step_helper5 : forall ys zs p q l,
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt), u = Some (s, g) /\ v = Some (s, g') /\ gttstepC g g' p q l)) ys
        zs ->
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g g' : gtt),
            u = Some (s0, g) /\ v = Some (s0, g') /\ upaco5 gttstep bot5 g g' p q l)) ys zs.
Proof.
  induction ys; intros; try easy.
  - destruct zs; try easy.
  - destruct zs; try easy. inversion H. subst.
    specialize(IHys zs p q l H5).
    constructor; try easy.
    destruct H3. left. easy.
    right. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. subst.
    exists x. exists x0. exists x1. split. easy. split. easy. left. easy.
Qed.

Lemma _3_19_step_helper6 : forall ys p q,
    Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt), u = Some (s, g) /\ isgPartsC p g /\ isgPartsC q g)) ys ->
    exists zs1 zs2, 
    Forall2 
         (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts p g' /\ (forall n : fin, exists m : fin, guardG n m g'))) ys zs1 /\
    Forall2 
         (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts q g' /\ (forall n : fin, exists m : fin, guardG n m g'))) ys zs2.
Proof.
  induction ys; intros.
  - exists nil. exists nil. easy.
  - inversion H. subst. clear H.
    specialize(IHys p q H3). destruct IHys. destruct H. destruct H. rename x into zs1. rename x0 into zs2. clear H3.
    destruct H2.
    - exists (None :: zs1). exists (None :: zs2).
      subst. split. constructor; try easy. left. easy.
      constructor; try easy. left. easy.
    - destruct H1. destruct H1. destruct H1. destruct H2. subst.
      unfold isgPartsC in *. destruct H2. destruct H3.
      exists (Some (x, x1) :: zs1). exists (Some (x, x2) :: zs2).
      split. constructor; try easy. right. exists x. exists x0. exists x1. easy.
      constructor; try easy. right. exists x. exists x0. exists x2.
      easy.
Qed.

Lemma _3_19_step_helper7 : forall ys x p,
    Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * global)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (g' : global),
            u = Some (s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts p g' /\ (forall n : fin, exists m : fin, guardG n m g'))) ys x ->
      Forall2
        (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g : global) (g' : gtt),
            u = Some (s0, g) /\ v = Some (s0, g') /\ upaco2 gttT bot2 g g')) x ys.
Proof.
  induction ys; intros.
  - destruct x; try easy.
  - destruct x; try easy. inversion H.
    subst. specialize(IHys x p H5). clear H5 H. constructor; try easy.
    destruct H3. left. easy. destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H1.
    subst. right. exists x0. exists x2. exists x1. split. easy. split. easy. left. easy.
Qed.

Lemma guardG_xs : forall [x s s' o],
    (forall n : fin, exists m : fin, guardG n m (g_send s s' (o :: x))) ->
    (forall n : fin, exists m : fin, guardG n m (g_send s s' x)). 
Proof.
  intros.
  specialize(H n). destruct H. exists x0.
  inversion H. constructor. subst.
  constructor. inversion H3; try easy.
Qed.

Lemma _3_19_step_helper8 : forall ys x s s' p,
      SList ys ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * global)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (g' : global),
            u = Some (s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts p g' /\ (forall n : fin, exists m : fin, guardG n m g'))) ys x ->
      (forall n : fin, exists m : fin, guardG n m (g_send s s' x)) /\ isgParts p (g_send s s' x).
Proof.
  induction ys; intros; try easy.
  destruct x; try easy.
  inversion H0. subst. clear H0.
  specialize(SList_f a ys H); intros. destruct H0.
  specialize(IHys x s s' p). 
  specialize(IHys H0 H6). split. 
  destruct IHys. destruct H4. destruct H3. subst. intros. specialize(H1 n). destruct H1.
  exists x0. inversion H1. constructor. subst. constructor; try easy. constructor; try easy. left. easy.
  destruct H3 as (s1,(g,(g',(Ha,(Hb,(Hc,(Hd,He))))))). subst.
  intros. specialize(H1 n). destruct H1. destruct n. exists 0. constructor.
  specialize(He n). destruct He. exists (Nat.max x1 x0); intros.
  constructor. constructor; try easy. right. exists s1. exists g'. split. easy.
  specialize(guardG_more n x1 (Nat.max x1 x0) g'); intros. apply H4; try easy. apply max_l.
  apply Forall_forall; intros.
  inversion H1. subst. specialize(Forall_forall (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ guardG n x0 g)) x); intros.
  destruct H5. specialize(H5 H9). specialize(H5 x2 H4). destruct H5. left. easy.
  destruct H5 as (s3,(g3,(Hta,Htb))). subst. right. exists s3. exists g3.
  split. easy. 
  specialize(guardG_more n x0 (Nat.max x1 x0) g3); intros. apply H5; try easy. apply max_r.
  apply isgParts_xs; try easy.
  destruct H0. destruct H1. subst.
  destruct H4; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
  inversion H0. subst. split. destruct x; try easy. destruct H3.
  intros. destruct n. exists 0. constructor. specialize(H3 n). destruct H3. exists x.
  constructor. constructor; try easy. right. exists x1. exists x3. split. easy. easy.
  apply isgParts_x; try easy.
Qed.

Lemma _3_19_step : forall p q l G L1 L2 S T S' T',
  wfgC G ->
  projectionC G p (ltt_send q L1) -> 
  onth l L1 = Some(S, T) ->
  projectionC G q (ltt_recv p L2) -> 
  onth l L2 = Some(S', T') ->
  (isgPartsC p G /\ isgPartsC q G) /\ exists G', gttstepC G G' p q l. 
Proof.
  intros. 
  specialize(_a_29_s G p q L1 L2 S T S' T' l H H0 H1 H2 H3); intros.
  destruct H4. rename x into Gl.
  destruct H4. destruct H4. destruct H4. destruct H4. destruct H5. destruct H6. destruct H7. clear H8. rename x into ctxG.
  specialize(_3_19_ctx_loose H7); intros. clear H7.
  
  revert H H0 H1 H2 H3 H4 H5 H6 H8. clear x0 x1.
  revert p q l G L1 L2 S T S' T' ctxG.
  induction Gl using gtth_ind_ref; intros.
  - inversion H4. subst.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s'0, Gjk) /\
              projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG); intros.
    destruct H7. specialize(H7 H8). clear H8 H9.
    specialize(some_onth_implies_In n ctxG G H10); intros. 
    specialize(H7 (Some G) H8). destruct H7; try easy. destruct H7. destruct H7. destruct H7. destruct H9.
    destruct H11. destruct H11. destruct H11. destruct H11. destruct H11. destruct H12. inversion H7. subst.
    split.
    - split.
      apply triv_pt_p; try easy.
      apply triv_pt_q; try easy.
    - exists x2. 
      pinversion H0; try easy. subst.
      pinversion H2; try easy. subst.
      pfold. apply steq with (s := x1); try easy.
      apply proj_mon.
      apply proj_mon.
  - rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    inversion H5. subst.
    pinversion H1; try easy. subst. 
    assert False. apply H6. constructor. easy. subst.
    pinversion H3; try easy. subst.
    specialize(wfgC_after_step_all H12 H0); intros. rename H0 into Ht.
    specialize(proj_inv_lis p q l s s' ys L1 L2 S T S' T'); intros.
    assert(s = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
     s <> p /\
     s' <> q /\
     Forall
       (fun u : option (sort * gtt) =>
        u = None \/
        (exists
           (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
         (T T' : sort * ltt),
           u = Some (s, g) /\
           projectionC g p (ltt_send q LP') /\
           projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T'))
       ys).
    {
      apply H0; try easy. pfold. easy. pfold. easy.
    }
    destruct H10; try easy. destruct H10. destruct H11. clear H10 H11. clear H0 Ht.
    assert(List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\
        typ_gtth ctxG g g' /\
        (isgPartsC p g' /\ isgPartsC q g' /\ (exists G', gttstepC g' G' p q l))
    )) xs ys).
    {
      clear H27 H23 H22 H19 H18 H21 H17 H16 H13 H12 H14 H5 H4 H3 H2 H1.
      revert H24 H9 H15 H8 H H6 H7. clear H20 H26.
      clear ys0 ys1 S T S' T' L1 L2. 
      revert s s' p q l ctxG ys.
      induction xs; intros.
      - destruct ys; try easy.
      - destruct ys; try easy.
        inversion H. inversion H24. inversion H9. inversion H15. clear H H24 H9 H15. subst.
        assert (Forall2
         (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
          u = None /\ v = None \/
          (exists (s0 : sort) (g : gtth) (g' : gtt),
             u = Some (s0, g) /\
             v = Some (s0, g') /\
             typ_gtth ctxG g g' /\
             isgPartsC p g' /\ isgPartsC q g' /\ (exists G' : gtt, gttstepC g' G' p q l))) xs
         ys).
       {
        specialize(IHxs s s' p q l ctxG ys). apply IHxs; try easy.
        specialize(ishParts_hxs H6); try easy.
        specialize(ishParts_hxs H7); try easy.
       }
       constructor; try easy.
       clear H H22 H16 H11 H3 IHxs.
       destruct H20. left. easy.
       destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
       destruct H14; try easy. destruct H. destruct H. destruct H. inversion H. subst. clear H.
       destruct H10; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H.
       inversion H. subst. clear H.
       destruct H2; try easy. destruct H. destruct H. destruct H. inversion H. subst. clear H.
       rename x3 into Gl. rename x1 into G. rename x4 into LQ. rename x5 into LP. destruct x6. destruct x7.
       right. exists x2. exists Gl. exists G. split; try easy. split. easy. split. easy.
       specialize(H2 p q l G LQ LP s0 l0 s1 l1 ctxG). 
       assert((isgPartsC p G /\ isgPartsC q G) /\ (exists G' : gtt, gttstepC G G' p q l)).
       apply H2; try easy. 
       specialize(ishParts_x H6); try easy.
       specialize(ishParts_x H7); try easy.
       destruct H; try easy.
    }
    specialize(_3_19_step_helper2 xs ys p q l ctxG H0); intros. destruct H10.
    rename x into zs. destruct H10.
    specialize(_3_19_step_helper3 xs ys ctxG H14 H15); intros.
    specialize(_3_19_step_helper4 ys zs p q l H25 H11); intros.
    assert((exists G' : gtt, gttstepC (gtt_send s s' ys) G' p q l)).
    {
      exists (gtt_send s s' zs).
      pfold. apply stneq; try easy.
      specialize(_3_19_step_helper5 ys zs p q l H11); intros. easy.
    }
    split; try easy.
    apply proj_mon.
    apply proj_mon.
Qed.

Lemma _3_19_h_helper : forall L1 l S T,
    Forall2R
       (fun u v : option (sort * ltt) =>
        u = None \/
        (exists (s s' : sort) (t t' : ltt),
           u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t'))
       (extendLis l (Some (S, T))) L1 -> 
    exists ST, onth l L1 = Some ST.
Proof.
  intros L1 l. revert L1. induction l; intros.
  - destruct L1; try easy. inversion H. subst. 
    destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
    subst. exists (x0, x2). easy.
  - destruct L1; try easy.
    inversion H. subst. specialize(IHl L1 S T H5). destruct IHl. 
    exists x. easy.
Qed.


Lemma _3_19_h : forall p q l G L1 L2 S T xs y,
  wfgC G ->
  projectionC G p (ltt_send q L1) -> 
  subtypeC (ltt_send q (extendLis l (Datatypes.Some(S,T)))) (ltt_send q L1) ->
  projectionC G q (ltt_recv p L2) -> 
  onth l xs = Some y ->
  subtypeC (ltt_recv p xs) (ltt_recv p L2) -> 
  exists G', gttstepC G G' p q l.
Proof.
  intros.
  specialize(_3_19_step p q l G L1 L2); intros.
  specialize(subtype_send_inv q (extendLis l (Some (S, T))) L1 H1); intros.
  specialize(subtype_recv_inv p xs L2 H4); intros.
  specialize(projection_step_label_s G p q l L1 L2); intros.
  specialize(_3_19_h_helper L1 l S T H6); intros. destruct H9.
  specialize(H8 x). 
  assert(exists (LS' : sort) (LT' : ltt), onth l L2 = Some (LS', LT')). apply H8; try easy.
  destruct H10. destruct H10.
  destruct x. 
  specialize(H5 s l0 x0 x1).
  apply H5; try easy. 
Qed.

Lemma merge_same : forall ys ys0 ys1 p q l LP LQ S T S' T' ctxG SI s s' xs,
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) ys ys0 ->
      isMerge (ltt_send q LP) ys0 ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) ys ys1 ->
      Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s', Gjk) /\
              projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option sort) =>
              u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s))
             lsg SI)) ctxG ->
      isMerge (ltt_recv p LQ) ys1 ->
      onth l LP = Some (S, T) ->
      onth l LQ = Some (S', T') ->
      (ishParts p (gtth_send s s' xs) -> False) ->
      (ishParts q (gtth_send s s' xs) -> False) ->
      Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys ->
      Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys ->
      Forall (fun u => u = None \/ (exists s g LP' LQ', u = Some (s, g) /\
          projectionC g p (ltt_send q LP') /\ onth l LP' = Some (S, T) /\
          projectionC g q (ltt_recv p LQ') /\ onth l LQ' = Some (S', T'))) ys.
Proof.
  intros. rename H10 into Ht.
  apply Forall_forall; intros. 
  destruct x.
  - right.
    specialize(in_some_implies_onth p0 ys H10); intros. destruct H11. rename x into n.
    destruct p0.
    assert(exists LP LQ T T', onth n ys0 = Some (ltt_send q LP) /\ projectionC g p (ltt_send q LP) /\ onth n ys1 = Some (ltt_recv p LQ) /\ projectionC g q (ltt_recv p LQ) /\ onth l LP = Some T /\ onth l LQ = Some T' /\ wfgC g).
    {
      clear H10 H6 H5 H4 H1.
      specialize(_3_19_ctx_loose H3); intros. clear H3. clear SI S T S' T'. clear LP LQ.
      revert H1 H2 H0 H. revert H9 H8 H7 H11 Ht. revert ys ys0 ys1 p q l ctxG s g. revert s' s0 xs.
      induction n; intros; try easy.
      - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy. destruct xs; try easy.
        inversion H2. subst. inversion H0. subst. inversion H. subst. inversion H9. subst. inversion Ht. subst.
        clear H18 H13 H14 H12 H H0 H2 H9 Ht. simpl in H11. subst.
        destruct H5; try easy. destruct H. destruct H. destruct H. destruct H. destruct H.
        destruct H. destruct H. destruct H0. destruct H2. destruct H3. inversion H. subst.
        destruct H6; try easy. destruct H5. destruct H5. destruct H5. destruct H5. destruct H6.
        inversion H5. subst.
        destruct H10; try easy. destruct H6. destruct H6. destruct H6. destruct H6. destruct H10.
        inversion H6. subst.
        destruct H16; try easy. destruct H10. destruct H10. destruct H10. destruct H10. destruct H12.
        inversion H12. subst.
        destruct H15; try easy. destruct H10 as (st,(g,(Ha,Hb))). inversion Ha. subst.
        pclearbot. simpl. exists x1. exists x2. exists x3. exists x4.
        specialize(ishParts_x H8); intros.
        specialize(ishParts_x H7); intros.
        specialize(proj_inj Hb H0 H11); intros. subst.
        specialize(proj_inj Hb H2 H9); intros. subst. 
        easy.
      - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy. destruct xs; try easy.
        inversion H2. subst. inversion H0. subst. inversion H. subst. inversion H9. subst.
        specialize(IHn s' s0 xs ys ys0 ys1 p q l ctxG s g). apply IHn; try easy.
        specialize(ishParts_hxs H8); try easy.
        specialize(ishParts_hxs H7); try easy.
        inversion Ht; try easy.
    }
    destruct H12. destruct H12. destruct H12. destruct H12. destruct H12. destruct H13. destruct H14. destruct H15. destruct H16.
    exists s0. exists g. exists x. exists x0. destruct x1. destruct x2. split. easy. split. easy.
    destruct H17. 
    specialize(merge_label_recv_s ys1 LQ x0 (s2, l1) n l p H4 H14 H17); intros.
    specialize(merge_label_send_s ys0 LP x (s1, l0) n l q H1 H12 H16); intros.
    specialize(eq_trans (eq_sym H19) H6); intros. inversion H21. subst.
    specialize(eq_trans (eq_sym H20) H5); intros. inversion H22. subst.
    easy.
    left. easy.
Qed.

Lemma part_cont_false_all : forall ys2 s s' p,
      p <> s -> p <> s' ->
      wfgC (gtt_send s s' ys2) ->
      (isgPartsC p (gtt_send s s' ys2) -> False) ->
      List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ (isgPartsC p g -> False))) ys2.
Proof.
  intros.
  apply Forall_forall; intros.
  destruct x.
  - destruct p0. right. exists s0. exists g. split. easy.
    intros. apply H2.
    specialize(in_some_implies_onth (s0, g) ys2 H3); intros. destruct H5 as (n,H5).
    clear H3 H2.
    unfold wfgC in H1. destruct H1 as (Gl,(Ha,(Hb,(Hc,Hd)))).
    specialize(guard_breakG_s2 (gtt_send s s' ys2) Gl Hc Hb Ha); intros.
    clear Ha Hb Hc Hd. clear Gl.
    destruct H1 as (Gl,(Ha,(Hb,(Hc,Hd)))).
    destruct Ha. subst. pinversion Hd; try easy. apply gttT_mon.
    destruct H1 as (p1,(q1,(lis,He))). subst. pinversion Hd; try easy. subst.
    unfold isgPartsC in H4.
    destruct H4 as (G1,(He,(Hf,Hg))).
    unfold isgPartsC.
    exists (g_send s s' (overwrite_lis n (Some (s0, G1)) lis)).
    clear Hc Hd.
    specialize(guard_cont Hb); intros. clear Hb.
    revert H2 H1 H5 Hg Hf He H0 H. revert lis G1 g s0 s s' p ys2.
    induction n; intros; try easy.
    - destruct ys2; try easy. destruct lis; try easy.
      inversion H2. subst. clear H2. inversion H1. subst. clear H1.
      simpl in H5. subst. destruct H7; try easy. destruct H1 as (s1,(g1,(g2,(Hta,(Htb,Htc))))).
      inversion Htb. subst. destruct H4; try easy.
      destruct H1 as (s2,(g3,(Htd,Hte))). inversion Htd. subst.
      split. pfold. constructor; try easy. constructor; try easy.
      right. exists s2. exists G1. exists g2. split. easy. split. easy. left. easy.
      split. apply guard_cont_b. constructor; try easy. 
      right. exists s2. exists G1. easy.
      apply pa_sendr with (n := 0) (s := s2) (g := G1); try easy.
    - destruct ys2; try easy. destruct lis; try easy.
      inversion H2. subst. clear H2. inversion H1. subst. clear H1.
      specialize(IHn lis G1 g s0 s s' p ys2).
      assert(gttTC (g_send s s' (overwrite_lis n (Some (s0, G1)) lis)) (gtt_send s s' ys2) /\
      (forall n0 : fin, exists m : fin, guardG n0 m (g_send s s' (overwrite_lis n (Some (s0, G1)) lis))) /\
      isgParts p (g_send s s' (overwrite_lis n (Some (s0, G1)) lis))).
      apply IHn; try easy.
      destruct H1 as (Hta,(Htb,Htc)).
      clear H6 H9 IHn.
      pinversion Hta. subst. clear Hta.
      specialize(guard_cont Htb); intros. clear Htb.
      split.
      - pfold. constructor. constructor; try easy.
      - split. apply guard_cont_b. constructor; try easy.
      - inversion Htc. subst. easy. subst. easy.
        subst.
        apply pa_sendr with (n := S n0) (s := s1) (g := g0); try easy.
    apply gttT_mon.
    apply gttT_mon.
    left. easy.
Qed.

Lemma _3_19_12_helper : forall ys2 x p,
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys2 ->
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ (isgPartsC p g -> False))) ys2 -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt), u = Some (s, g) /\ v = Some t /\ projectionC g p t))
        ys2 x -> 
      Forall (fun u => u = None \/ u = Some ltt_end) x.
Proof.
  induction ys2; intros; try easy.
  - destruct x; try easy.
  - destruct x; try easy. inversion H. subst. clear H. inversion H0. subst. clear H0.
    inversion H1. subst. clear H1.
    specialize(IHys2 x p).
    assert(Forall (fun u : option ltt => u = None \/ u = Some ltt_end) x).
    apply IHys2; try easy. constructor; try easy.
    destruct H7. destruct H0. left. easy.
    destruct H0 as (s1,(g1,(t1,(Ha,(Hb,Hc))))). subst.
    destruct H3; try easy. destruct H0 as (s2,(g2,(Hd,He))). inversion Hd. subst.
    destruct H4; try easy. destruct H0 as (s3,(g3,(Hf,Hg))). inversion Hf. subst.
    pinversion Hc; try easy. right. easy.
    subst. specialize(He H1). easy.
    subst. specialize(He H1). easy.
    subst. specialize(He H3). easy.
    apply proj_mon.
Qed.


Lemma _3_19_1_helper : forall p q l G G' LP LQ S T S' T',
  wfgC G -> 
  wfgC G' -> 
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some(S, T) ->
  projectionC G q (ltt_recv p LQ) -> 
  onth l LQ = Some(S', T') ->
  gttstepC G G' p q l -> 
  projectionC G' p T.
Proof.
  intros. rename H0 into Htt. rename H1 into H0. rename H2 into H1. rename H3 into H2.
  rename H4 into H3. rename H5 into H4.
  specialize(_a_29_s G p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
  destruct H5. rename x into Gl. rename H into Ht.
  revert H0 H1 H2 H3 H4 H5 Ht Htt. revert p q l G G' LP LQ S S' T T'.
  induction Gl using gtth_ind_ref; intros.
  - destruct H5. destruct H. destruct H. destruct H. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9.
    rename x1 into Sn. rename x0 into SI. rename x into ctxG. 
    inversion H. subst.
    specialize(some_onth_implies_In n ctxG G H13); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s', Gjk) /\
              projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option sort) =>
              u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s))
             lsg SI)) ctxG); intros. destruct H12.
    specialize(H12 H7). clear H7 H14. 
    specialize(H12 (Some G) H11). destruct H12; try easy.
    destruct H7. destruct H7. destruct H7. destruct H12. destruct H14.
    destruct H14. destruct H14. destruct H14. destruct H14. destruct H14. destruct H16. destruct H17. destruct H18.
    subst. inversion H7. subst. clear H7.
    pinversion H4; try easy. subst. specialize(eq_trans H24 H14); intros. inversion H7. subst. easy.
    apply step_mon.
  - rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9. destruct H10.
    rename x into ctxG. rename x1 into Sn. rename x0 into SI. 
    inversion H5. subst. 
    pinversion H0; try easy. subst.
    assert False. apply H6. constructor. easy.
    pinversion H2; try easy. subst.
    pinversion H4; try easy. subst. 
    
    specialize(proj_inv_lis p q l s s' ys LP LQ S T S' T'); intros.
    assert (s = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
      s <> p /\
      s' <> q /\
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys).
    {
      pclearbot.
      apply H12; try easy. 
      specialize(_3_19_ctx_loose H8); try easy.
      pfold. easy. pfold. easy.
    }
    destruct H13; try easy. destruct H13. destruct H14.
    clear H15 H16 H19 H28 H29 H30 H13 H14 H12.
        
    assert (List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ projectionC g p T)) ys2).
    {
      clear H5 H4 H2 H0 H17.
      specialize(wfgC_after_step_all H22 Ht); intros. clear Ht. 
      specialize(wfgC_after_step_all H22 Htt); intros. clear Htt.
      specialize(merge_same ys ys0 ys1 p q l LP LQ S T S' T' ctxG SI s s' xs H33 H23 H24 H34 H8 H35 H1 H3 H6 H7 H18 H0); intros.
      clear H32 H27 H26 H25 H22 H21 H35 H31 H24 H20 H3 H1 H23 H34.
      clear ys0 ys1 LP LQ.
      revert H2 H0 H40 H18 H11 H10 H9 H8 H7 H6 H H4. clear H39 H33. 
      revert s s' p q l S S' T T' ys ys2 ctxG SI Sn.
      induction xs; intros; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
        inversion H0. subst. clear H0. inversion H40. subst. clear H40.
        inversion H18. subst. clear H18. inversion H. subst. clear H.
        inversion H2. subst. clear H2. inversion H4. subst. clear H4.
        specialize(IHxs s s' p q l S S' T T' ys ys2 ctxG SI Sn).
        assert (Forall
         (fun u : option (sort * gtt) =>
          u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ projectionC g p T)) ys2).
        {
          apply IHxs; try easy.
          - intros. apply H7.
            - case_eq (eqb q s); intros.
              assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb q s'); intros.
              assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (q <> s). apply eqb_neq; try easy. 
              assert (q <> s'). apply eqb_neq; try easy.
              inversion H; try easy. subst.
              apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
          - intros. apply H6.
            - case_eq (eqb p s); intros.
              assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb p s'); intros.
              assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (p <> s). apply eqb_neq; try easy. 
              assert (p <> s'). apply eqb_neq; try easy.
              inversion H; try easy. subst.
              apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
        }
        constructor; try easy.
        clear H H19 H18 H16 H17 H15 H12 IHxs.
        destruct H1. left. easy.
        destruct H as (s1,(g1,(Hla,Hlb))). subst.
        right. exists s1. exists g1. split. easy.
        destruct H13; try easy. destruct H as (s3,(g4,(g5,(Hi,(Hj,Hk))))). inversion Hj. subst.
        destruct H2; try easy. destruct H as (s2,(g3,(LP,(LQ,(Hd,(He,(Hf,(Hg,Hh)))))))). inversion Hd. subst.
        destruct H14; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Hb. subst.
        destruct H5; try easy. destruct H as (s4,(g6,(Hl,Hm))). inversion Hl. subst.
        destruct H3; try easy. destruct H as (s5,(g7,(Hn,Ho))). inversion Hn. subst.
        specialize(Ho p q l g6 g5 LP LQ S S' T T'). 
        pclearbot.
        apply Ho; try easy.
        exists ctxG. exists SI. exists Sn. split. easy.
        - split. intros. apply H6. 
          - case_eq (eqb p s); intros.
            assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb p s'); intros.
            assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (p <> s). apply eqb_neq; try easy. 
            assert (p <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := s5) (g := g7); try easy.
        - split; try easy. intros. apply H7.
          - case_eq (eqb q s); intros.
            assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb q s'); intros.
            assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (q <> s). apply eqb_neq; try easy. 
            assert (q <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := s5) (g := g7); try easy.
    }
    assert(exists ys3, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some t /\ projectionC g p t)) ys2 ys3 /\ isMerge T ys3).
    {
      specialize(wfgC_after_step_all H22 Htt); intros. clear Htt.
      clear H33 H39 H32 H26 H25 H22 H21 H35 H34 H31 H24 H23 Ht H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H1 H0 H.
      revert H12 H40 H18 H17. clear H27 H20. revert p T xs ys. clear s s' LP LQ S S' T' SI Sn ys0 ys1.
      revert ctxG q l. revert H13.
      
      induction ys2; intros; try easy.
      - destruct ys; try easy. destruct xs; try easy.
      - destruct ys; try easy. destruct xs; try easy.
        inversion H18. subst. inversion H12. subst. inversion H40. subst. clear H18 H12 H40.
        inversion H13. subst. clear H13.
        specialize(SList_f o0 xs H17); intros.
        destruct H.
        - assert (exists ys3, Forall2
            (fun (u : option (sort * gtt)) (v : option ltt) =>
             (u = None /\ v = None) \/
             (exists (s : sort) (g : gtt) (t : ltt), u = Some (s, g) /\ v = Some t /\ projectionC g p t))
            ys2 ys3 /\ isMerge T ys3).
          {
            apply IHys2 with (xs := xs) (q := q) (l := l) (ys := ys) (ctxG := ctxG); try easy.
          }
          destruct H0. clear IHys2.
          - destruct H6. destruct H6. subst. 
            exists (None :: x). split. constructor; try easy. left. easy.
            destruct H0.
            apply triv_merge2; try easy.
          - destruct H6 as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
            destruct H1; try easy. destruct H1 as (s2,(g3,(Hd,He))). inversion Hd. subst.
            exists (Some T :: x).
            split. constructor; try easy. right. exists s2. exists g3. exists T.
            easy.
            apply triv_merge3; try easy.
          - destruct H. destruct H0. subst.
            destruct ys; try easy. destruct ys2; try easy. clear H3 H8 H4 IHys2.
            destruct H2; try easy. 
            destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
            destruct H6; try easy. destruct H as (s2,(g3,(g4,(Hd,(He,Hf))))). inversion Hd. subst.
            destruct H1; try easy. destruct H as (s3,(g5,(Hg,Hh))). inversion Hg. subst.
            exists (Some T :: nil). split.
            constructor; try easy. right. exists s3. exists g5. exists T. easy.
            constructor; try easy.
    }
    destruct H13. destruct H13. pfold.
    specialize(decidable_isgPartsC (gtt_send s s' ys2) p Htt); intros.
    unfold Decidable.decidable in H15.
    destruct H15.
    - apply proj_cont with (ys := x); try easy.
      revert H13. apply Forall2_mono; intros. destruct H13. left. easy.
      right. destruct H13 as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
      subst. exists s1. exists g1. exists t1. split. easy. split. easy. left. easy.
    - unfold not in H15.
      specialize(part_cont_false_all ys2 s s' p); intros.
      assert(Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ (isgPartsC p g -> False))) ys2).
      apply H16; try easy. clear H16.
      specialize(wfgC_after_step_all H22 Htt); intros.
      specialize(_3_19_12_helper ys2 x p); intros.
      assert(Forall (fun u : option ltt => u = None \/ u = Some ltt_end) x).
      apply H28; try easy.
      specialize(merge_end_s x T H29 H14); intros. subst.
      apply proj_end; try easy.
    apply step_mon.
    apply proj_mon.
    apply proj_mon.
Qed.

Lemma _3_19_2_helper : forall p q l G G' LP LQ S T S' T',
  wfgC G -> 
  wfgC G' -> 
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some(S, T) ->
  projectionC G q (ltt_recv p LQ) -> 
  onth l LQ = Some(S', T') ->
  gttstepC G G' p q l -> 
  projectionC G' q T'.
Proof.
  intros. rename H0 into Htt. rename H1 into H0. rename H2 into H1. rename H3 into H2.
  rename H4 into H3. rename H5 into H4.
  specialize(_a_29_s G p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
  destruct H5. rename x into Gl. rename H into Ht.
  revert H0 H1 H2 H3 H4 H5 Ht Htt. revert p q l G G' LP LQ S S' T T'.
  induction Gl using gtth_ind_ref; intros.
  - destruct H5. destruct H. destruct H. destruct H. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9.
    rename x1 into Sn. rename x0 into SI. rename x into ctxG. 
    inversion H. subst.
    specialize(some_onth_implies_In n ctxG G H13); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s', Gjk) /\
              projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option sort) =>
              u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s))
             lsg SI)) ctxG); intros. destruct H12.
    specialize(H12 H7). clear H7 H14. 
    specialize(H12 (Some G) H11). destruct H12; try easy.
    destruct H7. destruct H7. destruct H7. destruct H12. destruct H14.
    destruct H14. destruct H14. destruct H14. destruct H14. destruct H14. destruct H16. destruct H17. destruct H18.
    subst. inversion H7. subst. clear H7.
    pinversion H4; try easy. subst. specialize(eq_trans H24 H14); intros. inversion H7. subst. easy.
    apply step_mon.
  - rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9. destruct H10.
    rename x into ctxG. rename x1 into Sn. rename x0 into SI. 
    inversion H5. subst. 
    pinversion H0; try easy. subst.
    assert False. apply H6. constructor. easy.
    pinversion H2; try easy. subst.
    pinversion H4; try easy. subst. 
    
    specialize(proj_inv_lis p q l s s' ys LP LQ S T S' T'); intros.
    assert (s = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
      s <> p /\
      s' <> q /\
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys).
    {
      pclearbot.
      apply H12; try easy. 
      specialize(_3_19_ctx_loose H8); try easy.
      pfold. easy. pfold. easy.
    }
    destruct H13; try easy. destruct H13. destruct H14.
    clear H15 H16 H19 H28 H29 H30 H13 H14 H12.
        
    assert (List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ projectionC g q T')) ys2).
    {
      clear H5 H4 H2 H0 H17.
      specialize(wfgC_after_step_all H22 Ht); intros. clear Ht. 
      specialize(wfgC_after_step_all H22 Htt); intros. clear Htt.
      specialize(merge_same ys ys0 ys1 p q l LP LQ S T S' T' ctxG SI s s' xs H33 H23 H24 H34 H8 H35 H1 H3 H6 H7 H18 H0); intros.
      clear H32 H27 H26 H25 H22 H21 H35 H31 H24 H20 H3 H1 H23 H34.
      clear ys0 ys1 LP LQ.
      revert H2 H0 H40 H18 H11 H10 H9 H8 H7 H6 H H4. clear H39 H33. 
      revert s s' p q l S S' T T' ys ys2 ctxG SI Sn.
      induction xs; intros; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
        inversion H0. subst. clear H0. inversion H40. subst. clear H40.
        inversion H18. subst. clear H18. inversion H. subst. clear H.
        inversion H2. subst. clear H2. inversion H4. subst. clear H4.
        specialize(IHxs s s' p q l S S' T T' ys ys2 ctxG SI Sn).
        assert (Forall
         (fun u : option (sort * gtt) =>
          u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ projectionC g q T')) ys2).
        {
          apply IHxs; try easy.
          - intros. apply H7.
            - case_eq (eqb q s); intros.
              assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb q s'); intros.
              assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (q <> s). apply eqb_neq; try easy. 
              assert (q <> s'). apply eqb_neq; try easy.
              inversion H; try easy. subst.
              apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
          - intros. apply H6.
            - case_eq (eqb p s); intros.
              assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb p s'); intros.
              assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (p <> s). apply eqb_neq; try easy. 
              assert (p <> s'). apply eqb_neq; try easy.
              inversion H; try easy. subst.
              apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
        }
        constructor; try easy.
        clear H H19 H18 H16 H17 H15 H12 IHxs.
        destruct H1. left. easy.
        destruct H as (s1,(g1,(Hla,Hlb))). subst.
        right. exists s1. exists g1. split. easy.
        destruct H13; try easy. destruct H as (s3,(g4,(g5,(Hi,(Hj,Hk))))). inversion Hj. subst.
        destruct H2; try easy. destruct H as (s2,(g3,(LP,(LQ,(Hd,(He,(Hf,(Hg,Hh)))))))). inversion Hd. subst.
        destruct H14; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Hb. subst.
        destruct H5; try easy. destruct H as (s4,(g6,(Hl,Hm))). inversion Hl. subst.
        destruct H3; try easy. destruct H as (s5,(g7,(Hn,Ho))). inversion Hn. subst.
        specialize(Ho p q l g6 g5 LP LQ S S' T T'). 
        pclearbot.
        apply Ho; try easy.
        exists ctxG. exists SI. exists Sn. split. easy.
        - split. intros. apply H6. 
          - case_eq (eqb p s); intros.
            assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb p s'); intros.
            assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (p <> s). apply eqb_neq; try easy. 
            assert (p <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := s5) (g := g7); try easy.
        - split; try easy. intros. apply H7.
          - case_eq (eqb q s); intros.
            assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb q s'); intros.
            assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (q <> s). apply eqb_neq; try easy. 
            assert (q <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := s5) (g := g7); try easy.
    }
    assert(exists ys3, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some t /\ projectionC g q t)) ys2 ys3 /\ isMerge T' ys3).
    {
      specialize(wfgC_after_step_all H22 Htt); intros. clear Htt.
      clear H33 H39 H32 H26 H25 H22 H21 H35 H34 H31 H24 H23 Ht H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H1 H0 H.
      revert H12 H40 H18 H17. clear H27 H20. revert p T' xs ys. clear s s' LP LQ S S' T SI Sn ys0 ys1.
      revert ctxG q l. revert H13.
      
      induction ys2; intros; try easy.
      - destruct ys; try easy. destruct xs; try easy.
      - destruct ys; try easy. destruct xs; try easy.
        inversion H18. subst. inversion H12. subst. inversion H40. subst. clear H18 H12 H40.
        inversion H13. subst. clear H13.
        specialize(SList_f o0 xs H17); intros.
        destruct H.
        - assert (exists ys3, Forall2
            (fun (u : option (sort * gtt)) (v : option ltt) =>
             (u = None /\ v = None) \/
             (exists (s : sort) (g : gtt) (t : ltt), u = Some (s, g) /\ v = Some t /\ projectionC g q t))
            ys2 ys3 /\ isMerge T' ys3).
          {
            apply IHys2 with (xs := xs) (p := p) (l := l) (ys := ys) (ctxG := ctxG); try easy.
          }
          destruct H0. clear IHys2.
          - destruct H6. destruct H6. subst. 
            exists (None :: x). split. constructor; try easy. left. easy.
            destruct H0.
            apply triv_merge2; try easy.
          - destruct H6 as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
            destruct H1; try easy. destruct H1 as (s2,(g3,(Hd,He))). inversion Hd. subst.
            exists (Some T' :: x).
            split. constructor; try easy. right. exists s2. exists g3. exists T'.
            easy.
            apply triv_merge3; try easy.
          - destruct H. destruct H0. subst.
            destruct ys; try easy. destruct ys2; try easy. clear H3 H8 H4 IHys2.
            destruct H2; try easy. 
            destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
            destruct H6; try easy. destruct H as (s2,(g3,(g4,(Hd,(He,Hf))))). inversion Hd. subst.
            destruct H1; try easy. destruct H as (s3,(g5,(Hg,Hh))). inversion Hg. subst.
            exists (Some T' :: nil). split.
            constructor; try easy. right. exists s3. exists g5. exists T'. easy.
            constructor; try easy.
    }
    destruct H13. destruct H13. pfold.
    specialize(decidable_isgPartsC (gtt_send s s' ys2) q Htt); intros.
    unfold Decidable.decidable in H15.
    destruct H15.
    - apply proj_cont with (ys := x); try easy.
      revert H13. apply Forall2_mono; intros. destruct H13. left. easy.
      right. destruct H13 as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
      subst. exists s1. exists g1. exists t1. split. easy. split. easy. left. easy.
    - unfold not in H15.
      specialize(part_cont_false_all ys2 s s' q); intros.
      assert(Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ (isgPartsC q g -> False))) ys2).
      apply H16; try easy. clear H16.
      specialize(wfgC_after_step_all H22 Htt); intros.
      specialize(_3_19_12_helper ys2 x q); intros.
      assert(Forall (fun u : option ltt => u = None \/ u = Some ltt_end) x).
      apply H28; try easy.
      specialize(merge_end_s x T' H29 H14); intros. subst.
      apply proj_end; try easy.
    apply step_mon.
    apply proj_mon.
    apply proj_mon.
Qed.

Lemma _3_19_1 : forall p q l G G' LP LQ S T S' T' xs,
  wfgC G ->
  wfgC G' -> 
  projectionC G p (ltt_send q LP) ->
  subtypeC (ltt_send q (extendLis l (Datatypes.Some (S, T)))) (ltt_send q LP) ->
  projectionC G q (ltt_recv p LQ) ->
  onth l xs = Some (S', T') ->
  subtypeC (ltt_recv p xs) (ltt_recv p LQ) ->
  gttstepC G G' p q l ->
  exists L, 
  projectionC G' p L /\ subtypeC T L. 
Proof.
  intros.
  specialize(_3_19_1_helper p q l G G' LP LQ); intros.
  specialize(subtype_send_inv q (extendLis l (Some (S, T))) LP H2); intros.
  specialize(subtype_recv_inv p xs LQ H5); intros.
  specialize(projection_step_label G G' p q l LP LQ H H1 H3 H6); intros.
  destruct H10. destruct H10. destruct H10. destruct H10. destruct H10.
  rename x into s. rename x0 into s'. rename x1 into t. rename x2 into t'.
  
  specialize(H7 s t s' t' H H0 H1 H10 H3 H11 H6).
  exists t. split; try easy.
  
  clear H11 H9 H7 H6 H5 H4 H3 H2 H1 H0 H. clear s' t' xs T' S' LQ G G' p q.
  revert H10 H8. revert LP S T t s.
  induction l; intros; try easy.
  - destruct LP; try easy. inversion H8. subst.
    destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0.
    destruct H1. inversion H. subst. simpl in H10. inversion H10. subst. easy.
  - destruct LP; try easy. inversion H8. subst. specialize(IHl LP S T t s). apply IHl; try easy.
Qed.


Lemma _3_19_2 : forall p q l G G' LP LQ S T S' T' xs,
  wfgC G ->
  wfgC G' ->
  projectionC G p (ltt_send q LP) ->
  subtypeC (ltt_send q (extendLis l (Datatypes.Some (S, T)))) (ltt_send q LP) ->
  projectionC G q (ltt_recv p LQ) ->
  onth l xs = Some (S', T') ->
  subtypeC (ltt_recv p xs) (ltt_recv p LQ) ->
  gttstepC G G' p q l ->
  exists L, 
  projectionC G' q L /\ subtypeC T' L. 
Proof.
  intros.
  specialize(_3_19_2_helper p q l G G' LP LQ); intros.
  specialize(subtype_send_inv q (extendLis l (Some (S, T))) LP H2); intros.
  specialize(subtype_recv_inv p xs LQ H5); intros.
  specialize(projection_step_label G G' p q l LP LQ H H1 H3 H6); intros.
  destruct H10. destruct H10. destruct H10. destruct H10. destruct H10.
  rename x into s. rename x0 into s'. rename x1 into t. rename x2 into t'.
  
  specialize(H7 s t s' t' H H0 H1 H10 H3 H11 H6).
  exists t'. split; try easy.
  
  clear H10 H8 H7 H6 H5 H3 H2 H1 H0 H. clear s t T LP G G' p q.
  revert H11 H9 H4. revert LQ T' t' s' xs S'. clear S.
  induction l; intros; try easy.
  - destruct LQ; try easy. destruct xs; try easy. inversion H9. subst.
    simpl in H11. subst.
    destruct H2; try easy.
    destruct H as (s1,(s2,(t1,(t2,(Ha,(Hb,(Hc,Hd))))))). inversion Ha. subst.
    simpl in H4. inversion H4. subst. easy.
  - destruct LQ; try easy. destruct xs; try easy. inversion H9. subst. specialize(IHl LQ T' t' s' xs S'). apply IHl; try easy.
Qed.

Lemma _3_19_3_helper_h1 : forall l lsg ys s' Gjk s,
      onth l lsg = Some (s', Gjk) -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g : gtt) (t : ltt),
            u = Some (s0, g) /\ v = Some t /\ upaco3 projection bot3 g s t)) lsg ys -> 
      exists t, onth l ys = Some t /\ projectionC Gjk s t.
Proof.
  induction l; intros.
  - destruct lsg; try easy. 
    inversion H0. subst. clear H0.
    simpl in H. subst. destruct H3; try easy. destruct H as (s0,(g,(t,(Ha,(Hb,Hc))))).
    subst. exists t. inversion Ha. subst. destruct Hc; try easy.
  - destruct lsg; try easy. 
    inversion H0. subst. clear H0. 
    specialize(IHl lsg l' s' Gjk s). apply IHl; try easy.
Qed.


Lemma _3_19_3_helper_h2 : forall [n ys s0 g xs ctxG],
        onth n ys = Some (s0, g) -> 
        Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys -> 
        exists g', onth n xs = Some (s0, g') /\ typ_gtth ctxG g' g.
Proof.
  induction n; intros.
  - destruct ys; try easy. destruct xs; try easy.
    inversion H0. subst. clear H0.
    simpl in H. subst. destruct H4; try easy. destruct H as (s,(g0,(g',(Ha,(Hb,Hc))))).
    inversion Hb. subst.
    exists g0. easy.
  - destruct ys; try easy. destruct xs; try easy.
    inversion H0. subst. clear H0.
    specialize(IHn ys s0 g xs ctxG). apply IHn; try easy.
Qed.

Lemma _3_19_3_helper_h3 : forall ys ys2 p q l,
    Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q l)) ys ys2 -> 
    (forall t : string,
      t <> p ->
      t <> q ->
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s' : sort) (g : gtt),
            u = Some (s', g) /\
            (forall (G' : gtt) (T : ltt),
             gttstepC g G' p q l ->
             projectionC g t T -> exists T' : ltt, projectionC G' t T' /\ T = T'))) ys) ->
    forall t, t <> p -> t <> q -> Forall2 (fun u v => (u = None /\ v = None) \/ (exists s' g g', u = Some(s', g) /\ v = Some(s', g') /\
      gttstepC g g' p q l /\ (forall T, projectionC g t T -> exists T', projectionC g' t T' /\ T = T'
    ))) ys ys2.
Proof.
  induction ys; intros; try easy.
  - destruct ys2; try easy.
  - destruct ys2; try easy.
    inversion H. subst. clear H.
    assert(forall t : string,
     t <> p ->
     t <> q ->
     Forall
       (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s' : sort) (g : gtt),
           u = Some (s', g) /\
           (forall (G' : gtt) (T : ltt),
            gttstepC g G' p q l ->
            projectionC g t T -> exists T' : ltt, projectionC G' t T' /\ T = T')))
       ys).
    {
      intros. specialize(H0 t0 H H3). inversion H0; try easy.
    }
    specialize(H0 t H1 H2). inversion H0. subst. clear H0.
    specialize(IHys ys2 p q l H8 H). constructor; try easy. clear H H7 IHys H8.
    destruct H6. left. easy.
    destruct H as (s1,(g,(g',(Ha,(Hb,Hc))))). subst.
    destruct H5; try easy. destruct H as (s2,(g2,(Hta,Htb))). inversion Hta. subst. clear Hta.
    right. exists s2. exists g2. exists g'. split. easy. split. easy.
    split. destruct Hc; try easy.
    intros. specialize(Htb g' T). apply Htb; try easy. destruct Hc; try easy.
    apply IHys; try easy.
Qed.

Lemma _3_19_3_helper_h4 : forall l lsg s' Gjk ys s T,
      onth l lsg = Some (s', Gjk) ->  
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g : gtt) (t : ltt),
            u = Some (s0, g) /\ v = Some t /\ upaco3 projection bot3 g s t)) lsg ys -> 
      isMerge T ys -> 
      projectionC Gjk s T.
Proof.
  induction l; intros; try easy.
  - destruct lsg; try easy. destruct ys; try easy. 
    inversion H0. subst. clear H0. simpl in H. subst.
    destruct H5; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
    pclearbot.
    inversion H1; try easy. 
  - destruct lsg; try easy. destruct ys; try easy. 
    inversion H0. subst. clear H0. simpl in H. subst.
    specialize(IHl lsg s' Gjk ys s T). apply IHl; try easy.
    inversion H1; try easy. subst. destruct lsg; try easy. destruct l; try easy.
Qed.

Lemma _3_19_3_helper_h5 : forall ys ys2 ys3 p q l r,
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s' : sort) (g g' : gtt),
            u = Some (s', g) /\
            v = Some (s', g') /\
            gttstepC g g' p q l /\
            (forall T : ltt, projectionC g r T -> exists T' : ltt, projectionC g' r T' /\ T = T'))) ys ys2 -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some (s, t) /\ upaco3 projection bot3 g r t)) ys ys3 -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g : gtt) (t : ltt),
            u = Some (s0, g) /\ v = Some (s0, t) /\ upaco3 projection bot3 g r t)) ys2 ys3.
Proof.
  induction ys; intros; try easy.
  - destruct ys2; try easy. destruct ys3; try easy.
  - destruct ys2; try easy.
    inversion H. subst. clear H. inversion H0. subst. clear H0.
    specialize(IHys ys2 ys3 p q l r).
    assert(Forall2
         (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
          u = None /\ v = None \/
          (exists (s0 : sort) (g : gtt) (t : ltt),
             u = Some (s0, g) /\ v = Some (s0, t) /\ upaco3 projection bot3 g r t)) ys2 ys3).
    apply IHys; try easy. constructor; try easy. clear H H7 H6 IHys.
    destruct H3. left. destruct H4. easy. 
    destruct H. subst. destruct H0 as (s1,(g1,(g2,(Ha,Hb)))). easy.
    destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). subst.
    destruct H4; try easy. destruct H as (s2,(g2,(g3,(Hd,(He,(Hf,Hg)))))). inversion Hd. subst.
    right. exists s2. exists g3. exists t1. 
    specialize(Hg t1).
    assert(exists T', projectionC g3 r T' /\ t1 = T'). apply Hg; try easy.
    destruct Hc; try easy.
    destruct H. subst. split. easy. split. easy. left. destruct H. subst. easy.
Qed.

Lemma _3_19_3_helper_h6 : forall ys ys2 ys3 p q l r,
        Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys3 -> 
        Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s' : sort) (g g' : gtt),
            u = Some (s', g) /\
            v = Some (s', g') /\
            gttstepC g g' p q l /\
            (forall T : ltt, projectionC g r T -> exists T' : ltt, projectionC g' r T' /\ T = T'))) ys ys2 ->
        Forall2
          (fun (u : option (sort * gtt)) (v : option ltt) =>
           u = None /\ v = None \/
           (exists (s0 : sort) (g : gtt) (t : ltt),
              u = Some (s0, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys2 ys3.
Proof.
  induction ys; intros; try easy.
  - destruct ys2; try easy.
  - destruct ys2; try easy. destruct ys3; try easy.
    inversion H. subst. clear H. inversion H0. subst. clear H0.
    specialize(IHys ys2 ys3 p q l r).
    assert(Forall2
         (fun (u : option (sort * gtt)) (v : option ltt) =>
          u = None /\ v = None \/
          (exists (s0 : sort) (g : gtt) (t : ltt),
             u = Some (s0, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys2 ys3).
    apply IHys; try easy.
    constructor; try easy.
    - destruct H3. destruct H0. subst. destruct H4. left. easy.
      destruct H0 as (s1,(g1,(t1,(Ha,Hb)))). easy.
    - destruct H0 as (s1,(g1,(g2,(Ha,(Hb,(Hc,Hd)))))). subst.
      destruct H4; try easy. destruct H0 as (s2,(g3,(t1,(He,(Hf,Hg))))). inversion He. subst.
      right. exists s2. exists g2. exists t1. split. easy. split. easy. left.
      specialize(Hd t1).
      assert(exists T' : ltt, projectionC g2 r T' /\ t1 = T'). apply Hd; try easy.
      destruct Hg; try easy.
      destruct H0. destruct H0. subst. easy.
Qed.

Lemma part_after_step_r_helper : forall n ys s1 g1 ys1 ys0 xs p q l r ctxG,
    onth n ys = Some (s1, g1) -> 
    Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys -> 
    Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys1 -> 
    Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q l)) ys ys0 ->
    Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys ->
    exists g2 g3 t,
    onth n ys0 = Some (s1, g2) /\ gttstepC g1 g2 p q l /\
    onth n xs = Some (s1, g3) /\ typ_gtth ctxG g3 g1 /\
    onth n ys1 = Some t /\ projectionC g1 r t /\ wfgC g1.
Proof.
  induction n; intros; try easy.
  - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy.
    destruct xs; try easy.
    inversion H3. subst. clear H3. inversion H2. subst. clear H2. 
    inversion H1. subst. clear H1. inversion H0. subst. clear H0.
    simpl in H. subst. clear H4 H11 H10 H9.
    destruct H7; try easy. destruct H as (s2,(g2,(g3,(Ha,(Hb,Hc))))). inversion Hb. subst.
    destruct H6; try easy. destruct H as (s3,(g4,(g5,(Hd,(He,Hf))))). inversion Hd. subst.
    destruct H5; try easy. destruct H as (s4,(g6,(t1,(Hg,(Hi,Hj))))). inversion Hg. subst.
    destruct H3; try easy. destruct H as (s5,(g7,(Hk,Hl))). inversion Hk. subst.
    simpl. exists g5. exists g2. exists t1. pclearbot. easy.
  - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy.
    destruct xs; try easy.
    inversion H3. subst. clear H3. inversion H2. subst. clear H2. 
    inversion H1. subst. clear H1. inversion H0. subst. clear H0.
    specialize(IHn ys s1 g1 ys1 ys0 xs p q l r ctxG). apply IHn; try easy.
Qed.

Lemma part_after_step_r : forall G r p q G' l T,
        wfgC G -> 
        wfgC G' ->
        r <> p -> r <> q ->
        isgPartsC r G -> 
        gttstepC G G' p q l -> 
        projectionC G r T ->
        isgPartsC r G'.
Proof.
  intros.
  rename H0 into Htt. rename H1 into H0. rename H2 into H1. rename H3 into H2.
  rename H4 into H3. rename H5 into H4.
  specialize(wfgC_step_part G G' p q l H H3); intros.
  specialize(balanced_to_tree G p H H5); intros. clear H5.
  destruct H6 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd.
  revert Hc Hb Ha H4 H3 H2 H1 H0 H Htt. revert ctxG T l G' r p q G.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha. subst.
    specialize(some_onth_implies_In n ctxG G H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : list (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
    destruct H6. specialize(H6 Hc). clear H8 Hc.
    specialize(H6 (Some G) H5). destruct H6; try easy.
    destruct H6 as (q1,(lsg,Hd)).
    - destruct Hd. inversion H6. subst. pinversion H3; try easy. subst.
      pinversion H4; try easy. subst. easy. subst. easy. subst.
      assert(exists t, onth l ys = Some t /\ projectionC G' r t).
      {
        clear H21 H17 H14 H13 H11 H12 H15 H5 H7 H H0 H1 H6 H2 H3 H4 Ha Hb Htt.
        revert H20 H16.
        revert G' r lsg s ys.
        induction l; intros; try easy.
        - destruct lsg; try easy. destruct ys; try easy.
          inversion H20. subst. clear H20.
          simpl in H16. subst. destruct H2; try easy. 
          destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
          exists t1. destruct Hc; try easy.
        - destruct lsg; try easy. destruct ys; try easy.
          inversion H20. subst. clear H20.
          specialize(IHl G' r lsg s ys). apply IHl; try easy.
      }
      destruct H8 as (t1,(He,Hf)).
      pinversion Hf; try easy. subst.
      specialize(merge_end_back l ys T He H21); intros. subst.
      assert(projectionC (gtt_send p q lsg) r ltt_end). pfold. easy.
      specialize(pmergeCR (gtt_send p q lsg) r); intros.
      assert(False). apply H10; try easy. easy.
    apply proj_mon. apply proj_mon. apply step_mon.
    - destruct H6. inversion H6. subst. pinversion H3; try easy. apply step_mon.
    - inversion H6. subst. pinversion H3; try easy. apply step_mon.
  - inversion Ha. subst.
    pinversion H3; try easy. subst. assert False. apply Hb. constructor. easy.
    subst. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    clear H21.
    - case_eq (eqb r s); intros.
      assert (r = s). apply eqb_eq; try easy. subst. apply triv_pt_p; try easy.
    - case_eq (eqb r s'); intros.
      assert (r = s'). apply eqb_eq; try easy. subst. apply triv_pt_q; try easy.
    - assert (r <> s). apply eqb_neq; try easy. 
      assert (r <> s'). apply eqb_neq; try easy.
      clear H6 H7.
    specialize(part_cont ys r s s' H2 H8 H17); intros.
    destruct H6 as (n,(s1,(g1,(Hta,Htb)))).
    pinversion H4; try easy. subst. easy. subst. easy. subst.
    specialize(wfgC_after_step_all H10 H5); intros.
    specialize(part_after_step_r_helper n ys s1 g1 ys1 ys0 xs p q l r ctxG); intros.
    assert(exists (g2 : gtt) (g3 : gtth) (t : ltt),
       onth n ys0 = Some (s1, g2) /\
       gttstepC g1 g2 p q l /\
       onth n xs = Some (s1, g3) /\
       typ_gtth ctxG g3 g1 /\ onth n ys1 = Some t /\ projectionC g1 r t /\ wfgC g1).
    {
      apply H7; try easy.
    }
    clear H7. destruct H18 as (g2,(g3,(t1,(Hsa,(Hsb,(Hsc,(Hsd,(Hse,(Hsf,Hsg))))))))).
    specialize(some_onth_implies_In n xs (s1, g3) Hsc); intros.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (ctxG : list (option gtt)) (T : ltt) (l : fin) (G' : gtt) (r p q : string) (G : gtt),
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (q0 : string) (lsg : list (option (sort * gtt))),
                 u0 = Some (gtt_send p q0 lsg) \/ u0 = Some (gtt_send q0 p lsg) \/ u0 = Some gtt_end))
             ctxG ->
           (ishParts p g -> False) ->
           typ_gtth ctxG g G ->
           projectionC G r T ->
           gttstepC G G' p q l -> isgPartsC r G -> r <> q -> r <> p -> wfgC G -> wfgC G' -> isgPartsC r G')))
      xs); intros.
    destruct H18. specialize(H18 H). clear H H24.
    specialize(H18 (Some (s1, g3)) H7). destruct H18; try easy.
    destruct H as (s3,(g4,(Hma,Hmb))). inversion Hma. subst.
    specialize(Hmb ctxG t1 l g2 r p q g1).
    assert(isgPartsC r g2).
    {
      apply Hmb; try easy.
      specialize(ishParts_n Hb Hsc); intros. apply H; try easy.
      specialize(wfgC_after_step_all H10 Htt); intros.
      specialize(Forall_forall (fun u : option (sort * gtt) =>
       u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys0); intros.
      destruct H18. specialize(H18 H). clear H24 H.
      specialize(some_onth_implies_In n ys0 (s3, g2) Hsa); intros.
      specialize(H18 (Some (s3, g2)) H). destruct H18; try easy.
      destruct H18 as (st1,(gt1,(Hmc,Hmd))). inversion Hmc. subst. easy.
    }
    apply part_cont_b with (n := n) (s := s3) (g := g2); try easy.
  apply proj_mon.
  apply step_mon.
Qed.


Lemma _3_19_3_helper : forall G G' p q s l L1 L2 LS LT LS' LT' T,
      wfgC G ->
      wfgC G' ->
      projectionC G p (ltt_send q L1) ->
      onth l L1 = Some (LS, LT) ->
      projectionC G q (ltt_recv p L2) ->
      onth l L2 = Some (LS', LT') ->
      gttstepC G G' p q l ->
      s <> q ->
      s <> p ->
      projectionC G s T -> 
      exists T', projectionC G' s T' /\ T = T'. 
Proof.
  intros.
  rename H0 into Htt. rename H1 into H0. rename H2 into H1.
  rename H3 into H2. rename H4 into H3. rename H5 into H4. rename H6 into H5.
  rename H7 into H6. rename H8 into H7.
  specialize(_a_29_s G p q L1 L2 LS LT LS' LT' l H H0 H1 H2 H3); intros. 
  destruct H8. rename x into Gl. rename H into Ht.
  destruct H8 as (ctxG,(SI,(Sn,(Ha,(Hb,(Hc,(Hd,He))))))).
  clear He.
  specialize(_3_19_ctx_loose Hd); intros. clear Hd.
  clear SI Sn.
  revert H0 H1 H2 H3 H4 H5 H6 H7 Ha Hb Hc H Ht Htt. revert p q l G G' L1 L2 LS LS' LT LT' s T ctxG.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha. subst.
    specialize(Forall_forall (fun u : option gtt =>
       u = None \/
       (exists (g : gtt) (lsg : list (option (sort * gtt))),
          u = Some g /\
          g = gtt_send p q lsg /\
          (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
             onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq)))
      ctxG); intros.
    destruct H8. specialize(H8 H). clear H9 H.
    specialize(some_onth_implies_In n ctxG G H10); intros.
    specialize(H8 (Some G) H). destruct H8; try easy.
    destruct H8 as (g,(lsg,(Hta,(Htb,Htc)))). inversion Hta. subst. clear Hta.
    destruct Htc as (s',(Gjk,(Tp,(Tq,(Hsa,(Hsb,Hsc)))))). 
    pinversion H4; try easy. subst.
    specialize(eq_trans H17 Hsa); intros. inversion H8. subst. clear H8 H14 H13 H17.
    pinversion H7; try easy. 
    - subst. exists ltt_end. split. 
      pfold. apply proj_end; try easy.
      specialize(part_after_step (gtt_send p q lsg) Gjk p q s l L1 L2); intros.
      apply H8. apply H9; try easy. pfold. easy.
      constructor. 
    - subst. easy.
    - subst. easy.
    - subst. exists T. split. pfold. 
      specialize(_3_19_3_helper_h4 l lsg s' Gjk ys s T); intros.
      assert(projectionC Gjk s T). apply H8; try easy.
      pinversion H9; try easy. apply proj_mon.
      easy.
    apply proj_mon.
    apply step_mon.
  - inversion Ha. subst.
    rename s into r. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    pinversion H0; try easy. subst.
    assert False. apply Hb. constructor. easy.
    subst.
    pinversion H2; try easy. subst.
    specialize(proj_inv_lis p q l s s' ys L1 L2 LS LT LS' LT'); intros.
    assert(s = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
     s <> p /\
     s' <> q /\
     Forall
       (fun u : option (sort * gtt) =>
        u = None \/
        (exists
           (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
         (T T' : sort * ltt),
           u = Some (s, g) /\
           projectionC g p (ltt_send q LP') /\
           projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T'))
       ys). apply H9; try easy. pfold. easy. pfold. easy.
    destruct H10. destruct H10. subst. easy.
    destruct H10 as (H10,(Hsa,Hsb)). clear H10 Hsa H9.
    pinversion H4; try easy. subst. clear H12 H13 H16 H18 H19 H22.
    
    
    
    
    (* 
    assert(forall t, t <> p -> t <> q -> List.Forall (fun u => u = None \/ (exists s' g, u = Some (s', g) /\ forall G' T, 
        gttstepC g G' p q l -> projectionC g t T -> exists T', projectionC G' t T' /\ T = T')) ys).
    {
      intros. apply Forall_forall; intros. rename H9 into Hka. rename H10 into Hkb. rename H11 into H9. destruct x.
      - right. specialize(in_some_implies_onth p0 ys H9); intros. destruct H10 as (n, H10).
        destruct p0. exists s0. exists g. split. easy.
        intros. 
        specialize(_3_19_3_helper_h2 H10 H15); intros. destruct H13 as (g', (H13, Hla)).
        specialize(some_onth_implies_In n xs (s0, g') H13); intros.
        specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (p q : string) (l : fin) (G G' : gtt) (L1 L2 : list (option (sort * ltt)))
             (LS LS' : sort) (LT LT' : ltt) (s0 : string) (T : ltt) (ctxG : list (option gtt)),
           projectionC G p (ltt_send q L1) ->
           onth l L1 = Some (LS, LT) ->
           projectionC G q (ltt_recv p L2) ->
           onth l L2 = Some (LS', LT') ->
           gttstepC G G' p q l ->
           s0 <> q ->
           s0 <> p ->
           projectionC G s0 T ->
           typ_gtth ctxG g G ->
           (ishParts p g -> False) ->
           (ishParts q g -> False) ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
                    onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG ->
           wfgC G -> wfgC G' -> exists T' : ltt, projectionC G' s0 T' /\ T = T'))) xs); intros.
        destruct H18. specialize(H18 H). clear H19 H.
        specialize(H18 (Some (s0, g')) H16). destruct H18; try easy. 
        specialize(Forall_forall (fun u : option (sort * gtt) =>
         u = None \/
         (exists
            (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T'))
        ys); intros. destruct H18. specialize(H18 Hsb). clear Hsb H19.
        specialize(H18 (Some (s0, g)) H9). destruct H18; try easy.
        destruct H18 as (s1,(g1,(LP',(LQ',(T1,(T1',(Hma,(Hmb,(Hmc,(Hmd,Hme)))))))))).
        inversion Hma. subst. clear Hma.
        destruct H as (s2,(g2,(Hta,Htb))). inversion Hta. subst.
        specialize(Htb p q l g1 G' LP' LQ').
        destruct T1. destruct T1'. 
        specialize(Htb s0 s1 l0 l1 t T0 ctxG). apply Htb; try easy.
        specialize(ishParts_n Hb H13); intros. apply H. easy.
        specialize(ishParts_n Hc H13); intros. apply H. easy.
        pfold. apply steq with (s := s2); try easy. 
        left. easy.
    }
    pose proof H9 as Hla.
    specialize(H9 s H28 H29).
    specialize(_3_19_3_helper_h3 ys ys2 p q l H37 Hla); intros. clear Hla H37.
    pinversion H7. subst.
    - exists ltt_end. split.
      pfold. apply proj_end. intros. apply H11.
      specialize(part_after_step (gtt_send s s' ys) (gtt_send s s' ys2) p q r l L1 L2); intros.
      apply H13; try easy. pfold. easy. pfold. easy. pfold. easy. constructor.
    - subst.
      specialize(wfgC_after_step_all H25 Ht); intros.
      exists (ltt_recv s ys3). split; try easy.
      pfold. constructor; try easy.
      specialize(wfgC_after_step (gtt_send s r ys) (gtt_send s r ys2) p q l); intros.
      apply triv_pt_q; try easy. apply H12; try easy. pfold. easy.
      specialize(H10 r H30 H31).
      specialize(_3_19_3_helper_h5 ys ys2 ys3 p q l r); intros. apply H12; try easy.
    - subst.
      specialize(wfgC_after_step_all H25 Ht); intros.
      exists (ltt_send s' ys3). split; try easy.
      pfold. constructor; try easy.
      specialize(wfgC_after_step (gtt_send r s' ys) (gtt_send r s' ys2) p q l); intros.
      apply triv_pt_p; try easy. apply H12; try easy. pfold. easy.
      specialize(H10 r H28 H29).
      specialize(_3_19_3_helper_h5 ys ys2 ys3 p q l r); intros. apply H12; try easy.
    - subst. exists T.
      split; try easy. 
      specialize(wfgC_after_step (gtt_send s s' ys) (gtt_send s s' ys2) p q l); intros.
      assert(wfgC (gtt_send s s' ys2)). apply H11; try easy. pfold. easy.
      specialize(decidable_isgPartsC (gtt_send s s' ys2) r H12); intros.
      unfold Decidable.decidable in H13. unfold not in H13.
      destruct H13.
      - pfold. apply proj_cont with (ys := ys3); try easy.
        specialize(H10 r).
        assert(Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s' : sort) (g g' : gtt),
            u = Some (s', g) /\
            v = Some (s', g') /\
            gttstepC g g' p q l /\
            (forall T : ltt, projectionC g r T -> exists T' : ltt, projectionC g' r T' /\ T = T'))) ys ys2). apply H10; try easy. clear H10.
        specialize(_3_19_3_helper_h6 ys ys2 ys3 p q l r); intros. apply H10; try easy.
      - specialize(part_after_step_r (gtt_send s s' ys) r p q (gtt_send s s' ys2) l T); intros.
        assert(isgPartsC r (gtt_send s s' ys2)). apply H32; try easy. pfold. easy. pfold. easy.
        specialize(H13 H33). easy.
      apply proj_mon. apply step_mon. apply proj_mon. apply proj_mon.
         *)
Admitted.




