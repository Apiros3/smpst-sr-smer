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



Lemma ishParts_x : forall [p s1 s2 o1 o2 xs0],
    (ishParts p (gtth_send s1 s2 (Some (o1,o2) :: xs0)) -> False) ->
    (ishParts p o2 -> False).
Proof.
  intros. apply H. 
  - case_eq (eqb p s1); intros.
    assert (p = s1). apply eqb_eq; try easy. subst. apply ha_sendp.
  - case_eq (eqb p s2); intros.
    assert (p = s2). apply eqb_eq; try easy. subst. apply ha_sendq.
  - assert (p <> s1). apply eqb_neq; try easy. 
    assert (p <> s2). apply eqb_neq; try easy.
    apply ha_sendr with (n := 0) (s := o1) (g := o2); try easy.
Qed.

Lemma isgParts_xs : forall [s s' x o p],
    isgParts p (g_send s s' x) ->
    isgParts p (g_send s s' (o :: x)).
Proof.
  intros. inversion H. subst. 
  constructor. 
  subst. constructor.
  subst. apply pa_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
Qed.

Lemma isgParts_x : forall [s s' x s0 g p],
    isgParts p g -> 
    isgParts p (g_send s s' (Some (s0, g) :: x)).
Proof.
    intros.
    - case_eq (eqb p s); intros.
      assert (p = s). apply eqb_eq; try easy. subst. apply pa_sendp.
    - case_eq (eqb p s'); intros.
      assert (p = s'). apply eqb_eq; try easy. subst. apply pa_sendq.
    - assert (p <> s). apply eqb_neq; try easy. 
      assert (p <> s'). apply eqb_neq; try easy.
      apply pa_sendr with (n := 0) (s := s0) (g := g); try easy.
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
    subst.
    pinversion H0; try easy. subst.
    rename p0 into p. rename q0 into q.
    specialize(wfgC_after_step_all H14 H1); intros. clear H1.
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
    apply H0; try easy. clear H0 H3 H22 H17 H15.
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
        subst. clear H4.
        pinversion Hf; try easy. subst. assert False. apply H1. apply triv_pt_p; try easy. easy.
        subst. clear H4.
        exists ys3. exists ys2.
        destruct H8 as (s2,(Gjk,(Tp,(Tq,(Hm,Ht))))). 
        assert(exists T T', onth l ys3 = Some T /\ onth l ys2 = Some T').
        {
          specialize(proj_inv_lis_helper3 Hm H20 H22); intros; try easy.
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
          specialize(merge_label_send ys3 LP' LP0' T n' l q H24 Htc Hsd); intros. destruct H3. exists x.
          specialize(merge_label_recv ys4 LQ' LQ0' T' n' l p H29 Hte Hse); intros. destruct H26. exists x0.
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
    clear H9 H13 H15 H14 H10 H8 H10 H7 H3 H0 H1 H2 H4 H H16. clear n x.
    revert H12 H17 H19. revert G' p q LP LQ x1 s.
    induction l; intros; try easy.
    - destruct x1; try easy.
      destruct LP; try easy. destruct LQ; try easy.
      inversion H19. subst. clear H19. inversion H12. subst. clear H12. 
      simpl in *. subst.
      destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H. subst.
      destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2.
      inversion H0. subst.
      exists x3. exists x3. exists x2. exists x5. easy.
    - destruct x1; try easy. destruct LP; try easy. destruct LQ; try easy.
      inversion H12. subst. inversion H19. subst.
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
      clear H2 H1 H0 H3 H4 H5 H6 H12 H10 H11 H14 H18 H22 H23 H24 H28 H8 H16 H19 H20 H21 H25 H26 H28 H33.
      clear LP LQ. clear s s0.
      revert H H27 H17 H13. revert H34. 
      revert xs p q ys ctxG ys0 ys1 x1 G. revert l ys2.
      induction n; intros; try easy.
      - destruct xs; try easy.
        destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H27. subst. inversion H13. subst. inversion H17. subst. inversion H34. subst. clear H27 H13 H17 H34.
        simpl in *. subst.
        destruct H4; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
        inversion H. subst. clear H. 
        destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        destruct H6; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        exists x3. exists x6. exists x5. exists x4. pclearbot. destruct H2; try easy.
      - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H27. subst. inversion H17. subst. inversion H13. subst. inversion H34. subst. apply IHn with (xs := xs); try easy.
    }
    destruct H7. destruct H7. destruct H7. destruct H7. destruct H7. destruct H9. destruct H15. destruct H29.
    destruct H30. destruct H31. destruct H32. 
    rename x into G0'. rename x2 into LP0. rename x3 into LQ0. rename x0 into G''.
    specialize(H8 G0' G'' p q l).
    specialize(merge_onth_recv n p LQ ys0 LP0 H18 H15); intros. destruct H36 as [LQ' H36].
    specialize(merge_onth_send n q LP ys1 LQ0 H28 H30); intros. destruct H37 as [LP' H37].
    subst.
    specialize(H8 LP' LQ' H31 H29 H35).
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
    destruct H36. destruct H36. destruct H36. destruct H36. destruct H36. 
    
    specialize(merge_label_send ys1 LP LP' (x, x2) n l q H28 H30 H36); intros.
    destruct H38. 
    specialize(merge_label_recv ys0 LQ LQ' (x0, x3) n l p H18 H15 H37); intros.
    destruct H39. destruct x4. destruct x5.
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
    clear H10 H14 H9 H11 H0 H7 H5 H2 H3 H H4. clear n x.
    revert H16 H13 H1. revert p q LP LQ ST x1.
    induction l; intros.
    - destruct LP; try easy. destruct x1; try easy. destruct LQ; try easy.
      inversion H16. inversion H13. subst. clear H16 H13.
      simpl in H1. subst.
      destruct H9; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H0. subst.
      destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H2.
      inversion H. subst. 
      exists x3. exists x5. easy.
    - destruct LP; try easy. destruct x1; try easy. destruct LQ; try easy.
      inversion H16. inversion H13. subst.
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
      clear H25 H21 H18 H17 H20 H16 H15 H14 H5 H1 H4 H8. clear ST LP LQ. clear s s'. clear l.
      revert H24 H19 H12 H7. revert xs p q ctxG ys s0 g ys0 ys1.
      induction n; intros.
      - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H24. inversion H19. inversion H12. subst. clear H24 H19 H12.
        simpl in H7. subst.
        destruct H16; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        destruct H9; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
        inversion H. subst. clear H.
        simpl. exists x1. exists x4. exists x5. pclearbot. easy.
      - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H24. inversion H19. inversion H12. subst. clear H24 H19 H12.
        specialize(IHn xs p q ctxG ys s0 g ys0 ys1). apply IHn; try easy.
    }
    destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H2. destruct H3. destruct H6.
    clear H24 H19 H12.
    rename x into g'. 
    specialize(merge_onth_recv n p LQ ys1 x1 H25 H6); intros. destruct H10. subst.
    specialize(merge_onth_send n q LP ys0 x0 H20 H2); intros. destruct H10. subst.
    rename x1 into LP'. rename x into LQ'.
    
    specialize(H8 g' p q l LP' LQ' ST).
    specialize(merge_label_sendb ys0 LP LP' ST n l q H20 H2 H1); intros. 
    assert (exists (LS' : sort) (LT' : ltt), onth l LQ' = Some (LS', LT')).
    {
      apply H8; try easy.
      exists ctxG. split; try easy. split; try easy.
      intros. apply H4. apply ha_sendr with (n := n) (s := s0) (g := g); try easy.
      
    }
    destruct H11. destruct H11.
    specialize(merge_label_recv ys1 LQ LQ' (x, x0) n l p H25 H6 H11); intros. destruct H12.
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
         (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts p g')) ys zs1 /\
    Forall2 
         (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts q g')) ys zs2.
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
            u = Some (s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts p g')) ys x ->
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

Lemma _3_19_step_helper8 : forall ys x s s' p,
      SList ys ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * global)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (g' : global),
            u = Some (s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts p g')) ys x ->
      isgParts p (g_send s s' x).
Proof.
  induction ys; intros; try easy.
  destruct x; try easy.
  inversion H0. subst. clear H0.
  specialize(SList_f a ys H); intros. destruct H0.
  specialize(IHys x s s' p). 
  specialize(IHys H0 H6). 
  apply isgParts_xs; try easy.
  destruct H0. destruct H1. subst.
  destruct H4; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
  inversion H0. subst.
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
    specialize(_3_19_step_helper s s' ys H0 H12); intros. rename H0 into Ht.
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
      clear H25 H24 H21 H18 H17 H20 H19 H16 H13 H12 H5 H4 H3 H2 H1. clear H14.
      revert H22 H9 H15 H8 H7 H6 H.
      clear ys0 ys1 S T S' T' L1 L2. 
      revert s s' p q l ctxG ys.
      induction xs; intros.
      - destruct ys; try easy.
      - destruct ys; try easy.
        inversion H. inversion H22. inversion H9. inversion H15. clear H H22 H9 H15. subst.
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
        specialize(ishParts_hxs H7); try easy.
        specialize(ishParts_hxs H6); try easy.
       }
       constructor; try easy.
       clear H H23 H16 H11 H3 IHxs.
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
    specialize(_3_19_step_helper4 ys zs p q l H23 H11); intros.
    assert((exists G' : gtt, gttstepC (gtt_send s s' ys) G' p q l)).
    {
      exists (gtt_send s s' zs).
      pfold. apply stneq; try easy.
      specialize(_3_19_step_helper5 ys zs p q l H11); intros. easy.
    }
    split; try easy. 
    specialize(_3_19_step_helper6 ys p q H10); intros. destruct H28. destruct H28. destruct H28.
    unfold isgPartsC in *.
    split.
    - exists (g_send s s' x).
      split. pfold. constructor.
      specialize(_3_19_step_helper7 ys x p H28); try easy.
      specialize(_3_19_step_helper8 ys x s s' p H23 H28); try easy.
    - exists (g_send s s' x0).
      split. pfold. constructor.
      specialize(_3_19_step_helper7 ys x0 q H29); try easy.
      specialize(_3_19_step_helper8 ys x0 s s' q H23 H29); try easy.
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


Lemma _3_19_1_helper : forall p q l G G' LP LQ S T S' T',
  wfgC G -> 
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some(S, T) ->
  projectionC G q (ltt_recv p LQ) -> 
  onth l LQ = Some(S', T') ->
  gttstepC G G' p q l -> 
  projectionC G' p T.
Proof.
  intros.
  specialize(_a_29_s G p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
  destruct H5. rename x into Gl. rename H into Ht.
  revert H0 H1 H2 H3 H4 H5 Ht. revert p q l G G' LP LQ S S' T T'.
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
    clear H15 H16 H19 H27 H28 H29 H20 H13 H14 H12.
        
    assert (List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ projectionC g p T)) ys2).
    {
      clear H5 H4 H2 H0 H17.
      specialize(wfgC_after_step_all H21 Ht); intros. clear Ht. 
      specialize(merge_same ys ys0 ys1 p q l LP LQ S T S' T' ctxG SI s s' xs H31 H22 H23 H32 H8 H33 H1 H3 H6 H7 H18 H0); intros.
      clear H32 H31 H22. rename H0 into Ht. rename H2 into H0.
      clear H23 H21 H24 H25 H26 H30 H3 H1. 
      revert H38 H18 H8 H7 H6 H H9 H10 H11 H0 Ht. clear H37 H33. clear ys0 ys1 LP LQ. 
      revert s s' p q l S S' T T' ys ys2 ctxG SI Sn.
      induction xs; intros; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
        inversion H0. subst. clear H0. inversion H38. subst. clear H38.
        inversion H18. subst. clear H18. inversion H. subst. clear H.
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
            inversion Ht; try easy.
        }
        clear H14 H15 H13 H4 IHxs.
        constructor; try easy.
        destruct H5. destruct H0. left. easy.
        destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. subst. right.
        exists x. exists x1. split; try easy.
        destruct H12; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
        inversion H1. subst. clear H1.
        destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
        destruct H1. destruct H3. destruct H12. inversion H0. subst. clear H0.
        destruct H2; try easy. destruct H0. destruct H0. destruct H0.
        inversion H0. subst.
        rename x4 into Gl. rename x0 into G. rename x1 into G'. rename x6 into LQ. rename x5 into LP.
        specialize(H2 p q l G G' LP LQ S S' T T').
        apply H2; try easy. destruct H4; try easy.
        exists ctxG. exists SI. exists Sn. split. easy.
        clear H2 H H4.
        - split. intros. apply H6. 
          - case_eq (eqb p s); intros.
            assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb p s'); intros.
            assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (p <> s). apply eqb_neq; try easy. 
            assert (p <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := x2) (g := Gl); try easy.
        - split; try easy. intros. apply H7.
          - case_eq (eqb q s); intros.
            assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb q s'); intros.
            assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (q <> s). apply eqb_neq; try easy. 
            assert (q <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := x2) (g := Gl); try easy.
       inversion Ht. subst. clear Ht.
       destruct H16; try easy. destruct H14 as (sta,(ga,(Hta,Htb))). inversion Hta. subst. easy.
    }
    clear Ht.
    assert(exists ys3, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some t /\ projectionC g p t)) ys2 ys3 /\ isMerge T ys3).
    {
      clear H33 H37 H31 H30 H26 H25 H24 H21 H33 H32 H23 H22 H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H1 H0 H.
      revert H17 H18 H12 H38.
      revert s s' xs p q l LP LQ S S' T T' ys ctxG SI Sn ys0 ys1.
      induction ys2; intros; try easy.
      - destruct ys; try easy. destruct xs; try easy.
      - destruct ys; try easy. destruct xs; try easy.
        inversion H18. subst. inversion H12. subst. inversion H38. subst. clear H18 H12 H38.
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
          - destruct H6. destruct H5. subst. 
            exists (None :: x). split. constructor; try easy. left. easy.
            destruct H0.
            apply triv_merge2; try easy.
          - destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. subst.
            destruct H2; try easy. destruct H2. destruct H2. destruct H2. destruct H2. destruct H5.
            inversion H5. subst. 
            destruct H1; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
            exists (Some T :: x). split.
            constructor; try easy. right. exists x0. exists x1. exists T. easy.
            apply triv_merge3; try easy.
          - destruct H. destruct H0. subst.
            destruct ys; try easy. destruct ys2; try easy. clear H3 H8 H4 IHys2.
            destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
            inversion H. subst.
            destruct H6; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H3.
            inversion H0. subst.
            destruct H1; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
            exists (Some T :: nil). split.
            constructor; try easy. right. exists x0. exists x2. exists T. easy.
            constructor.
    }
    destruct H13. destruct H13. pfold.
    apply proj_cont with (ys := x); try easy.
    clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H17 H18 H22 H23 H32 H33 H21 H24 H25 H26 H30 H31 H38 H37 H12 H14.
    clear s s' xs q l LP LQ S S' T T' ys ctxG SI Sn ys0 ys1.
    revert H13. revert p x.
    induction ys2; intros; try easy.
    - destruct x; try easy.
    - destruct x; try easy.
      inversion H13. subst. clear H13.
      specialize(IHys2 p x H4). constructor; try easy. clear IHys2 H4.
      destruct H2. left. easy. 
      destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
      right. exists x0. exists x1. exists x2. split. easy. split. easy. left. easy.
    apply step_mon.
    apply proj_mon.
    apply proj_mon.
Qed.

Lemma _3_19_2_helper : forall p q l G G' LP LQ S T S' T',
  wfgC G -> 
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some(S, T) ->
  projectionC G q (ltt_recv p LQ) -> 
  onth l LQ = Some(S', T') ->
  gttstepC G G' p q l -> 
  projectionC G' q T'.
Proof.
  intros.
  specialize(_a_29_s G p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
  destruct H5. rename x into Gl. rename H into Ht.
  revert H0 H1 H2 H3 H4 H5 Ht. revert p q l G G' LP LQ S S' T T'.
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
    clear H15 H16 H19 H27 H28 H29 H20 H13 H14 H12.
        
    assert (List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ projectionC g q T')) ys2).
    {
      clear H5 H4 H2 H0 H17.
      specialize(wfgC_after_step_all H21 Ht); intros. clear Ht. 
      specialize(merge_same ys ys0 ys1 p q l LP LQ S T S' T' ctxG SI s s' xs H31 H22 H23 H32 H8 H33 H1 H3 H6 H7 H18 H0); intros.
      clear H32 H31 H22. rename H0 into Ht. rename H2 into H0.
      clear H23 H21 H24 H25 H26 H30 H3 H1. 
      revert H38 H18 H8 H7 H6 H H9 H10 H11 H0 Ht. clear H37 H33. clear ys0 ys1 LP LQ. 
      revert s s' p q l S S' T T' ys ys2 ctxG SI Sn.
      induction xs; intros; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
        inversion H0. subst. clear H0. inversion H38. subst. clear H38.
        inversion H18. subst. clear H18. inversion H. subst. clear H.
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
            inversion Ht; try easy.
        }
        clear H14 H15 H13 H4 IHxs.
        constructor; try easy.
        destruct H5. destruct H0. left. easy.
        destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. subst. right.
        exists x. exists x1. split; try easy.
        destruct H12; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
        inversion H1. subst. clear H1.
        destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
        destruct H1. destruct H3. destruct H12. inversion H0. subst. clear H0.
        destruct H2; try easy. destruct H0. destruct H0. destruct H0.
        inversion H0. subst.
        rename x4 into Gl. rename x0 into G. rename x1 into G'. rename x6 into LQ. rename x5 into LP.
        specialize(H2 p q l G G' LP LQ S S' T T').
        apply H2; try easy. destruct H4; try easy.
        exists ctxG. exists SI. exists Sn. split. easy.
        clear H2 H H4.
        - split. intros. apply H6. 
          - case_eq (eqb p s); intros.
            assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb p s'); intros.
            assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (p <> s). apply eqb_neq; try easy. 
            assert (p <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := x2) (g := Gl); try easy.
        - split; try easy. intros. apply H7.
          - case_eq (eqb q s); intros.
            assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb q s'); intros.
            assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (q <> s). apply eqb_neq; try easy. 
            assert (q <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := x2) (g := Gl); try easy.
       inversion Ht. subst. clear Ht.
       destruct H16; try easy. destruct H14 as (sta,(ga,(Hta,Htb))). inversion Hta. subst. easy.
    }
    clear Ht.
    assert(exists ys3, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some t /\ projectionC g q t)) ys2 ys3 /\ isMerge T' ys3).
    {
      clear H33 H37 H31 H30 H26 H25 H24 H21 H33 H32 H23 H22 H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H1 H0 H.
      revert H17 H18 H12 H38.
      revert s s' xs p q l LP LQ S S' T T' ys ctxG SI Sn ys0 ys1.
      induction ys2; intros; try easy.
      - destruct ys; try easy. destruct xs; try easy.
      - destruct ys; try easy. destruct xs; try easy.
        inversion H18. subst. inversion H12. subst. inversion H38. subst. clear H18 H12 H38.
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
          - destruct H6. destruct H5. subst. 
            exists (None :: x). split. constructor; try easy. left. easy.
            destruct H0.
            apply triv_merge2; try easy.
          - destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. subst.
            destruct H2; try easy. destruct H2. destruct H2. destruct H2. destruct H2. destruct H5.
            inversion H5. subst. 
            destruct H1; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
            exists (Some T' :: x). split.
            constructor; try easy. right. exists x0. exists x1. exists T'. easy.
            apply triv_merge3; try easy.
          - destruct H. destruct H0. subst.
            destruct ys; try easy. destruct ys2; try easy. clear H3 H8 H4 IHys2.
            destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
            inversion H. subst.
            destruct H6; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H3.
            inversion H0. subst.
            destruct H1; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
            exists (Some T' :: nil). split.
            constructor; try easy. right. exists x0. exists x2. exists T'. easy.
            constructor.
    }
    destruct H13. destruct H13. pfold.
    apply proj_cont with (ys := x); try easy.
    clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H17 H18 H22 H23 H32 H33 H21 H24 H25 H26 H30 H31 H38 H37 H12 H14.
    revert H13. apply Forall2_mono; intros. destruct H. left. easy.
    destruct H as (sa,(ga,(ta,(Ha,(Hb,Hc))))). subst. right. exists sa. exists ga. exists ta.
    split. easy. split. easy. left. easy.
    apply step_mon.
    apply proj_mon.
    apply proj_mon.
Qed.

Lemma _3_19_1 : forall p q l G G' LP LQ S T S' T' xs,
  wfgC G ->
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
  specialize(subtype_send_inv q (extendLis l (Some (S, T))) LP H1); intros.
  specialize(subtype_recv_inv p xs LQ H4); intros.
  specialize(projection_step_label G G' p q l LP LQ H H0 H2 H5); intros.
  destruct H9. destruct H9. destruct H9. destruct H9. destruct H9.
  rename x into s. rename x0 into s'. rename x1 into t. rename x2 into t'.
  
  specialize(H6 s t s' t' H H0 H9 H2 H10 H5).
  exists t. split; try easy.
  
  clear H10 H8 H6 H5 H4 H3 H2 H1 H0 H. clear s' t' xs T' S' LQ G G' p q.
  revert H9 H7. revert LP S T t s.
  induction l; intros; try easy.
  - destruct LP; try easy. inversion H7. subst.
    destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0.
    destruct H1. inversion H. subst. simpl in H9. inversion H9. subst. easy.
  - destruct LP; try easy. inversion H7. subst. specialize(IHl LP S T t s). apply IHl; try easy.
Qed.


Lemma _3_19_2 : forall p q l G G' LP LQ S T S' T' xs,
  wfgC G ->
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
  specialize(subtype_send_inv q (extendLis l (Some (S, T))) LP H1); intros.
  specialize(subtype_recv_inv p xs LQ H4); intros.
  specialize(projection_step_label G G' p q l LP LQ H H0 H2 H5); intros.
  destruct H9. destruct H9. destruct H9. destruct H9. destruct H9.
  rename x into s. rename x0 into s'. rename x1 into t. rename x2 into t'.
  
  specialize(H6 s t s' t' H H0 H9 H2 H10 H5).
  exists t'. split; try easy.
  
  clear H9 H7 H6 H5 H4 H2 H1 H0 H.
  clear s t S T LP G G' p q.
  revert H3 H8 H10. revert LQ S' T' xs t' s'.
  induction l; intros.
  - destruct LQ; try easy. destruct xs; try easy.
    inversion H8. subst. simpl in *. subst.
    destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0.
    destruct H1. inversion H0. inversion H. subst. easy.
  - destruct LQ; try easy. destruct xs; try easy. 
    inversion H8. subst. simpl in *. 
    specialize(IHl LQ S' T' xs t' s'). apply IHl; try easy.
Qed.
(* 
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
             projectionC g t T -> exists T' : ltt, projectionC G' t T' /\ isMergable T' T))) ys) ->
    forall t, t <> p -> t <> q -> Forall2 (fun u v => (u = None /\ v = None) \/ (exists s' g g', u = Some(s', g) /\ v = Some(s', g') /\
      gttstepC g g' p q l /\ (forall T, projectionC g t T -> exists T', projectionC g' t T' /\ isMergable T' T
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
            projectionC g t T -> exists T' : ltt, projectionC G' t T' /\ isMergable T' T)))
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

(* Lemma projection_in_cont : forall n s s' ys s2 g1,
      wfgC (gtt_send s s' ys) ->
      (forall pt : string, exists T : ltt, projectionC (gtt_send s s' ys) pt T) -> 
      onth n ys = Some (s2, g1) ->
      (forall pt : string, exists T1 : ltt, projectionC g1 pt T1).
Proof.
  intros.
  pose proof H0 as Hs. pose proof Hs as Hs'.
  specialize(H0 pt). destruct H0 as (T,H0).
  pinversion H0. 
  - subst. exists ltt_end. pfold. constructor.
    specialize(part_after_step (gtt_send s s' ys) g1 s s' pt n); intros.
    
    
    
Admitted. *) *)

Lemma _3_19_3_helper : forall G G' p q s l L1 L2 LS LT LS' LT' T,
      wfgC G ->
      projectionC G p (ltt_send q L1) ->
      onth l L1 = Some (LS, LT) ->
      projectionC G q (ltt_recv p L2) ->
      onth l L2 = Some (LS', LT') ->
      gttstepC G G' p q l ->
      s <> q ->
      s <> p ->
      projectionC G s T -> 
      exists T', projectionC G' s T' /\ T' = T. 
Proof.
  (* intros.
  specialize(_a_29_s G p q L1 L2 LS LT LS' LT' l H H0 H1 H2 H3); intros. rename H8 into Hs.
  rename H9 into H8.
  destruct H8. rename x into Gl. rename H into Ht.
  destruct H8 as (ctxG,(SI,(Sn,(Ha,(Hb,(Hc,(Hd,He))))))).
  clear He.
  specialize(_3_19_ctx_loose Hd); intros. clear Hd.
  clear SI Sn.
  revert H0 H1 H2 H3 H4 H5 H6 H7 Ha Hb Hc H Ht Hs. revert p q l G G' L1 L2 LS LS' LT LT' s T ctxG.
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
    - subst.
      specialize(_3_19_3_helper_h1 l lsg ys s' Gjk s Hsa H18); intros.
      destruct H8 as (t,(Hta,Htb)). 
      exists t. split. easy.
      admit. (* easy *)
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
    pinversion H4; try easy. subst. clear H12 H13 H16 H17 H18 H21.
    assert(forall t, t <> p -> t <> q -> List.Forall (fun u => u = None \/ (exists s' g, u = Some (s', g) /\ forall G' T, 
        gttstepC g G' p q l -> projectionC g t T -> exists T', projectionC G' t T' /\ isMergable T' T)) ys).
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
             (LS LS' : sort) (LT LT' : ltt) (s0 : string) (T : ltt) 
             (ctxG : list (option gtt)),
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
                    onth l lsg = Some (s'0, Gjk) /\
                    projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG ->
           wfgC G ->
           (forall pt : string, isgPartsC pt G -> exists T0 : ltt, projectionC G pt T0) ->
           exists T' : ltt, projectionC G' s0 T' /\ isMergable T' T))) xs); intros.
        destruct H17. specialize(H17 H). clear H18 H.
        specialize(H17 (Some (s0, g')) H16). destruct H17; try easy. 
        specialize(Forall_forall (fun u : option (sort * gtt) =>
         u = None \/
         (exists
            (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T'))
        ys); intros. destruct H17. specialize(H17 Hsb). clear Hsb H18.
        specialize(H17 (Some (s0, g)) H9). destruct H17; try easy.
        destruct H17 as (s1,(g1,(LP',(LQ',(T1,(T1',(Hma,(Hmb,(Hmc,(Hmd,Hme)))))))))).
        inversion Hma. subst. clear Hma.
        destruct H as (s2,(g2,(Hta,Htb))). inversion Hta. subst.
        specialize(Htb p q l g1 G' LP' LQ').
        destruct T1. destruct T1'. 
        specialize(Htb s0 s1 l0 l1 t T0 ctxG). apply Htb; try easy.
        specialize(ishParts_n Hb H13); intros. apply H. easy.
        specialize(ishParts_n Hc H13); intros. apply H. easy.
        specialize(wfgC_after_step (gtt_send s s' ys) g1 s s' n); intros. apply H; try easy.
        pfold. apply steq with (s := s2); try easy. 
        admit.
        left. easy.
    }
    pose proof H9 as Hla.
    specialize(H9 s H26 H27).
    specialize(_3_19_3_helper_h3 ys ys2 p q l H35 Hla); intros. clear Hla H35.
    pinversion H7. subst.
    - exists ltt_end. split.
      pfold. apply proj_end. intros. apply H11.
      specialize(part_after_step (gtt_send s s' ys) (gtt_send s s' ys2) p q r l L1 L2); intros.
      apply H13; try easy. pfold. easy. pfold. easy. pfold. easy. constructor.
    - subst.
      specialize(wfgC_after_step_all H23 Ht); intros.
    
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some (s, t) /\ upaco3 projection bot3 g r t)) ys ys3 -> 
      (forall t : string,
      t <> p ->
      t <> q ->
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s' : sort) (g g' : gtt),
            u = Some (s', g) /\
            v = Some (s', g') /\
            gttstepC g g' p q l /\
            (forall T : ltt,
             projectionC g t T -> exists T' : ltt, projectionC g' t T' /\ isMergable T' T))) ys ys2) -> 
      Forall2 (fun u v => (u = None /\ v = None) \/ (exists s' g g', u = Some(s', g) /\ v = Some(s', g') /\
          gttstepC g g' p q l /\ (forall T, projectionC g r T -> projectionC g' r T))) ys ys2.
      
      assert().
      {
        
        
      }
      exists (ltt_recv s ys3). split.
      - pfold. constructor; try easy. *)
        
Admitted.




