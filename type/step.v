From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header type.global type.local type.isomorphism type.merge type.decidability type.global_tree_ctx type.projection.
Require Import List String Coq.Arith.PeanoNat Relations Coq.Logic.Decidable.
Import ListNotations. 

Variant gttstep (R: gtt -> gtt -> part -> part -> nat -> Prop): gtt -> gtt -> part -> part -> nat -> Prop :=
  | steq : forall p q xs s gc n,
                  p <> q ->
                  Datatypes.Some (s, gc) = onth n xs ->
                  gttstep R (gtt_send p q xs) gc p q n
  | stneq: forall p q r s xs ys n,
                  p <> q ->
                  r <> s ->
                  r <> p ->
                  r <> q ->
                  s <> p ->
                  s <> q ->
                  List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ isgPartsC p g /\ isgPartsC q g)) xs ->
                  List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ R g g' p q n)) xs ys ->
                  gttstep R (gtt_send r s xs) (gtt_send r s ys) p q n.

Definition gttstepC g1 g2 p q n := paco5 gttstep bot5 g1 g2 p q n. 

Lemma step_mon : monotone5 gttstep.
Proof. unfold monotone5.
       intros.
       induction IN; intros.
       - apply steq with (s := s). easy. easy.
       - constructor; try easy. 
         revert ys H6.
         induction xs; intros.
         + subst. inversion H6. constructor.
         + subst. inversion H6. constructor.
           subst.
           destruct H9 as [(H9a, H9b) | (s1,(g,(t,(Ht1,(Ht2,Ht3)))))].
           subst. left. easy.
           subst. right. exists s1. exists g. exists t.
           split. easy. split. easy. apply LE. easy.
           apply IHxs.
           rewrite Forall_forall.
           intros u Hu.
           subst. rewrite Forall_forall in H5.
           specialize(H5 u).
           assert(In u (a :: xs)) by (simpl; right; easy).
           apply H5 in H7.
           easy.
           easy.
Qed.

Lemma wfgC_step_part_helper : forall lis1 xs,
    SList lis1 -> 
    Forall2
       (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : global) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) lis1 xs -> 
    SList xs.
Proof.
  induction lis1; intros; try easy.
  destruct xs; try easy.
  specialize(SList_f a lis1 H); intros.
  inversion H0. clear H0. subst.
  destruct H1. apply SList_b. specialize(IHlis1 xs). apply IHlis1; try easy.
  destruct H0. destruct H1. subst. destruct xs; try easy.
  destruct H5; try easy. destruct H0 as (s0,(g0,(g1,(Ha,(Hb,Hc))))). inversion Ha. subst.
  easy.
Qed.

Lemma wfgC_step_part : forall G G' p q n,
    wfgC G ->
    gttstepC G G' p q n -> 
    isgPartsC p G.
Proof.
  intros.
  - pinversion H0. subst. 
    apply triv_pt_p; try easy.
  - subst.
    unfold wfgC in H.
    destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))). 
    specialize(guard_breakG_s2 (gtt_send r s xs) Gl Hc Hb Ha); intros.
    clear Ha Hb Hc. clear Gl. destruct H as (Gl,(Ha,(Hb,(Hc,He)))).
    destruct Ha. subst. pinversion He. apply gttT_mon.
    destruct H as (p1,(q1,(lis1,Ht))). subst. pinversion He. subst.
    inversion Hc. subst.
    specialize(wfgC_step_part_helper lis1 xs H12 H9); intros.
    clear H14 H13.
    unfold isgPartsC.
    specialize(slist_implies_some xs H); intros. destruct H10 as (k,(G,Hta)).
    specialize(some_onth_implies_In k xs G Hta); intros.
    specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ isgPartsC p g /\ isgPartsC q g)) xs); intros.
    destruct H11. specialize(H11 H7). clear H13 H7.
    specialize(H11 (Some G) H10). destruct H11; try easy. 
    destruct H7 as (s1,(g1,(Hsa,(Hsb,Hsc)))). inversion Hsa. subst.
    unfold isgPartsC in Hsb. destruct Hsb as (G1,(Hla,(Hlb,Hlc))).
    exists (g_send r s (overwrite_lis k (Some (s1, G1)) lis1)). 
    clear Hsc H10 Hsa H H12 He H8. clear H6 H4 H2 H1 Hd H0 Hc.
    revert Hlc Hlb Hla Hta H9 Hb H5 H3. revert G1 g1 s1 lis1 xs r s p. clear q n ys.
    induction k; intros; try easy.
    - destruct xs; try easy. destruct lis1; try easy. 
      inversion H9. subst. clear H9.
      simpl in Hta. subst.
      destruct H2; try easy. destruct H as (s2,(g2,(g3,(Hsa,(Hsb,Hsc))))).
      inversion Hsb. subst.
      split.
      - pfold. constructor. constructor; try easy.
        right. exists s2. exists G1. exists g3. split. easy. split. easy. left. easy.
      - split.
        apply guard_cont_b.
        specialize(guard_cont Hb); intros. inversion H. subst. clear H.
        constructor; try easy. right. exists s2. exists G1. easy.
      - apply pa_sendr with (n := 0) (s := s2) (g := G1); try easy.
    - destruct xs; try easy. destruct lis1; try easy. 
      inversion H9. subst. clear H9.
      specialize(IHk G1 g1 s1 lis1 xs).
      specialize(guard_cont Hb); intros. inversion H. subst. clear H.
      assert((forall n : fin, exists m : fin, guardG n m (g_send r s lis1))). apply guard_cont_b; try easy.
      assert(gttTC (g_send r s (overwrite_lis k (Some (s1, G1)) lis1)) (gtt_send r s xs) /\
      (forall n : fin, exists m : fin, guardG n m (g_send r s (overwrite_lis k (Some (s1, G1)) lis1))) /\
      isgParts p (g_send r s (overwrite_lis k (Some (s1, G1)) lis1))).
      {
        apply IHk; try easy.
      }
      destruct H0 as (Hma,(Hmb,Hmc)).
      - split. pfold. constructor.
        pinversion Hma; try easy. subst. constructor; try easy. apply gttT_mon.
      - split. apply guard_cont_b; try easy. simpl.
        specialize(guard_cont Hmb); intros.
        constructor; try easy.
      - apply pa_sendr with (n := S k) (s := s1) (g := G1); try easy.
        apply overwriteExtract; try easy.
      apply gttT_mon.
      apply step_mon.
Qed.


Lemma part_after_step_helper2 : forall l x0 q p x G' pt s,
    isgPartsC pt G' -> 
    Some (s, G') = onth l x0 -> 
    gttTC (g_send q p x) (gtt_send q p x0) -> 
    (forall n : fin, exists m : fin, guardG n m (g_send q p x)) ->
    exists G'0 : global, gttTC G'0 (gtt_send q p x0) /\ (forall n : fin, exists m : fin, guardG n m G'0) /\ isgParts pt G'0.
Proof.  
  intros.
  unfold isgPartsC in H. destruct H. destruct H. rename x1 into Gl.
  exists (g_send q p (overwrite_lis l (Some(s, Gl)) x)). 
  split.
  - pinversion H1; try easy. subst.
    pfold. constructor. destruct H3.
    clear H1 H2 H3 H4. revert H5 H0 H. clear q p pt. revert l x G' s Gl.
    induction x0; intros; try easy.
    - destruct l; try easy.
    - destruct x; try easy. inversion H5. subst. clear H5.
    - destruct l; try easy.
      - simpl in H0. subst. destruct H4; try easy.
      destruct H0 as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
      inversion Hb. subst.
        constructor; try easy. right. exists s1. exists Gl. exists g2. split. easy. split. easy. left. easy.
      - specialize(IHx0 l x G' s Gl H7 H0 H). constructor; try easy.
    apply gttT_mon.
    split.
    destruct H3. intros. destruct n. exists 0. constructor.
    specialize(H2 (S n)). specialize(H3 n). destruct H3. destruct H2.
    exists (Nat.max x1 x2). constructor. inversion H2. subst. clear H2 H1 H0 H4 H.
    revert H8 H3. revert n x s Gl x1 x2. clear x0 q p G' pt.
    induction l; intros; try easy.
    - destruct x; try easy. constructor; try easy. right. exists s. exists Gl.
      split. easy. specialize(guardG_more n x1 (Nat.max x1 x2) Gl); intros. apply H; try easy.
      apply max_l.
    - inversion H8. subst. clear H8. constructor; try easy. right.
      exists s. exists Gl. split. easy.
      specialize(guardG_more n x1 (Nat.max x1 x2) Gl); intros. apply H; try easy. apply max_l.
    - apply Forall_forall; intros.
      specialize(Forall_forall (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ guardG n x2 g)) x); intros.
      destruct H0. specialize(H0 H2). clear H4 H2. specialize(H0 x0 H). 
      destruct H0. left. easy. destruct H0 as (s1,(g,(Ha,Hb))). subst. right.
      exists s1. exists g. split. easy.
      specialize(guardG_more n x2 (Nat.max x1 x2) g); intros. apply H0; try easy. apply max_r.
    - destruct x; try easy.
      specialize(IHl n nil s Gl x1 x2 H8 H3). constructor; try easy.
      left. easy.
    - inversion H8. subst. clear H8. specialize(IHl n x s Gl x1 x2 H2 H3). constructor; try easy.
      destruct H1. left. easy.
      destruct H as (s1,(g1,(Ha,Hb))). subst. right. exists s1. exists g1. split. easy.
      specialize(guardG_more n x2 (Nat.max x1 x2) g1); intros. apply H; try easy.
      apply max_r.
  - case_eq (eqb pt p); intros.
      assert (pt = p). apply eqb_eq; try easy. subst. constructor.
    - case_eq (eqb pt q); intros.
      assert (pt = q). apply eqb_eq; try easy. subst. constructor.
    - assert (pt <> p). apply eqb_neq; try easy. 
      assert (pt <> q). apply eqb_neq; try easy.
      apply pa_sendr with (n := l) (s := s) (g := Gl); try easy.
      apply overwriteExtract; try easy.
Qed.

Lemma part_after_step_helper3 : forall n x1 ys2 ys ys0 ys1 xs p q l s g ctxG,
      onth n x1 = Some (s, g) -> 
      Forall2
        (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : global) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) x1 ys2 -> 
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' q p l)) ys ys2 -> 
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
      Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys -> 
      exists g' g'' t t' Gl,
      onth n ys2 = Some (s, g') /\ gttTC g g' /\
      onth n ys = Some (s, g'') /\ gttstepC g'' g' q p l /\
      onth n ys0 = Some t /\ projectionC g'' q t /\
      onth n ys1 = Some t' /\ projectionC g'' p t' /\
      onth n xs = Some (s, Gl) /\ typ_gtth ctxG Gl g''.
Proof.
  induction n; intros.
  - destruct x1; try easy. destruct ys2; try easy. destruct ys; try easy.
    destruct ys0; try easy. destruct ys1; try easy. destruct xs; try easy.
    inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. subst. 
    clear H0 H1 H2 H3 H4.
    simpl in H. subst. clear H34 H28 H22 H16 H10.
    destruct H8; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H. subst. clear H.
    destruct H14; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H0. subst. clear H0.
    destruct H32; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H0. subst. clear H0.
    destruct H26; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H. subst. clear H.
    destruct H20; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H. subst. clear H.
    destruct H1; try easy. destruct H2; try easy. destruct H4; try easy. destruct H5; try easy.
    simpl. exists x5. exists x6. exists x8. exists x7. exists x2. 
    easy.
  - destruct x1; try easy. destruct ys2; try easy. destruct ys; try easy.
    destruct ys0; try easy. destruct ys1; try easy. destruct xs; try easy.
    inversion H0. inversion H1. inversion H2. inversion H3. inversion H4. subst. 
    clear H0 H1 H2 H3 H4.
    specialize(IHn x1 ys2 ys ys0 ys1 xs p q l s g ctxG). apply IHn; try easy.
Qed.

Lemma part_after_step : forall G G' q p pt l LP LQ,
        wfgC G ->
        wfgC G' -> 
        gttstepC G G' q p l -> 
        projectionC G p (ltt_recv q LQ) ->
        projectionC G q (ltt_send p LP) ->
        isgPartsC pt G' -> 
        isgPartsC pt G.
Proof.
  intros.
  specialize(_a_29_11 G q p LP H H3); intros.
  destruct H5 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd.
  assert(Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send q p lsg)) ctxG).
  {
    apply Forall_forall; intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send q p lsg /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg LP)) ctxG); intros.
    destruct H6. specialize(H6 Hc). clear Hc H7.
    specialize(H6 x H5). destruct H6. left. easy.
    destruct H6 as (g,(lsg,(Hc,(Hd,He)))). right. exists g. exists lsg. easy.
  }
  clear Hc.
  revert H5 Hb Ha H4 H3 H2 H1 H0 H.
  revert G G' p q pt l LP LQ ctxG.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha. subst.
    specialize(some_onth_implies_In n ctxG G H8); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))), u = Some g /\ g = gtt_send q p lsg))
       ctxG); intros.
    destruct H7. specialize(H7 H5). clear H9 H5.
    specialize(H7 (Some G) H6). destruct H7; try easy.
    destruct H5 as (g1,(lsg,(Hc,Hd))). inversion Hc. subst.
    pinversion H1; try easy. subst.
    clear H11 H12.
    unfold wfgC in H. destruct H. destruct H. rename x into G1.
    unfold isgPartsC. destruct H5. destruct H7.
    specialize(part_after_step_helper G1 q p lsg H H7); intros.
    destruct H10. destruct H10.
    specialize(part_after_step_helper2 l lsg q p x G' pt s); intros. apply H12; try easy.
    apply step_mon.
  - inversion Ha. subst.
    unfold isgPartsC.
    pinversion H2; try easy.
    subst. assert False. apply Hb. constructor. easy.
    subst. pinversion H3; try easy. subst.
    pinversion H1; try easy. subst. clear H10 H11 H14 H16 H17 H20.
    specialize(part_break (gtt_send p q ys2) pt H0 H4); intros.
    destruct H7 as (Gl,(Hc,(Hd,(He,Hf)))).
    destruct Hf.
    - subst. pinversion Hc; try easy.
    - destruct H7 as (p1,(q1,(lis1,Hf))). subst.
      pinversion Hc; try easy. subst.
    clear Hc.
    - specialize(part_break (gtt_send p q ys) p); intros.
      assert(exists Gl : global,
       gttTC Gl (gtt_send p q ys) /\
       isgParts p Gl /\
       (forall n : fin, exists m : fin, guardG n m Gl) /\
       (Gl = g_end \/
        (exists (p q : string) (lis : seq.seq (option (sort * global))), Gl = g_send p q lis))).
      {
        apply H7; try easy.
        apply triv_pt_p; try easy.
      }
      destruct H9 as (Gl1,(Hta,(Htb,(Htc,Htd)))).
      destruct Htd. subst. pinversion Hta; try easy.
      destruct H9 as (p1,(q1,(lsg1,Htd))). subst.
      pinversion Hta. subst.
    - rename p into st. rename q into st'. rename p0 into p. rename q0 into q.
      clear H7 Hta.
      inversion Hd; try easy. 
      - subst. exists (g_send st st' lsg1). split. pfold. constructor. easy. split. easy. constructor.
      - subst. exists (g_send st st' lsg1). split. pfold. constructor. easy. split. easy. constructor.
      subst.
      clear Htb H21 H15 H12 H4 H1 Ha H2 H3.
      specialize(wfgC_after_step_all H23 H0); intros.
      specialize(wfgC_after_step_all H23 H6); intros.
      clear H0 H6 Hd H34.
      specialize(part_after_step_helper3 n lis1 ys2 ys ys1 ys0 xs p q l s g ctxG); intros.
      assert(exists (g' g'' : gtt) (t t' : ltt) (Gl : gtth),
       onth n ys2 = Some (s, g') /\
       gttTC g g' /\
       onth n ys = Some (s, g'') /\
       gttstepC g'' g' q p l /\
       onth n ys1 = Some t /\
       projectionC g'' q t /\
       onth n ys0 = Some t' /\
       projectionC g'' p t' /\ onth n xs = Some (s, Gl) /\ typ_gtth ctxG Gl g'').
      {
        apply H0; try easy.
      }
      clear H0.
      destruct H3 as (g1,(g2,(t1,(t2,(Gl,(Hta,(Htb,(Htk,(Htd,(Hte,(Htf,(Hth,(Hti,(Htj,Htl)))))))))))))).
      specialize(some_onth_implies_In n xs (s, Gl) Htj); intros.
      specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G G' : gtt) (p q pt : string) (l : fin) (LP LQ : seq.seq (option (sort * ltt)))
             (ctxG : seq.seq (option gtt)),
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some g0 /\ g0 = gtt_send q p lsg)) ctxG ->
           (ishParts q g -> False) ->
           typ_gtth ctxG g G ->
           isgPartsC pt G' ->
           projectionC G q (ltt_send p LP) ->
           projectionC G p (ltt_recv q LQ) ->
           gttstepC G G' q p l -> wfgC G' -> wfgC G -> isgPartsC pt G))) xs); intros.
      destruct H3. specialize(H3 H). clear H H4.
      specialize(H3 (Some (s, Gl)) H0). destruct H3; try easy. 
      destruct H as (s1,(g3,(Hma,Hmb))). inversion Hma. subst.
      clear Hma H0.
      specialize(Hmb g2 g1 p q pt l).
      specialize(merge_onth_send n p LP ys1 t1 H25 Hte); intros. destruct H. subst.
      specialize(merge_onth_recv n q LQ ys0 t2 H19 Hth); intros. destruct H. subst.
      specialize(Hmb x x0 ctxG H5).
      assert(isgPartsC pt g2).
      {
        apply Hmb; try easy.
        specialize(ishParts_n Hb Htj); try easy.
        unfold isgPartsC. exists g. split. easy. split; try easy.
        specialize(guard_cont He); intros.
        revert n0. specialize(Forall_prop n lis1 (s1, g) (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) H20 H); intro.
        simpl in H0. destruct H0; try easy. destruct H0 as (st1,(gt1,(Hsa,Hsb))). inversion Hsa; try easy.
        specialize(Forall_prop n ys2 (s1, g1) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) Hta H1); intro.
        simpl in H. destruct H; try easy. destruct H as (st1,(gt1,(Hsa,Hsb))). inversion Hsa; try easy.
        specialize(Forall_prop n ys (s1, g2) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) Htk H2); intro.
        simpl in H. destruct H; try easy. destruct H as (st1,(gt1,(Hsa,Hsb))). inversion Hsa; try easy.
      }
      
      clear Hmb H2 H1.
      specialize(part_after_step_helper2 n ys st st'); intros.
      specialize(H0 lsg1 g2 pt s1). apply H0; try easy. pfold. constructor. easy.
    apply gttT_mon.
    apply gttT_mon.
    apply step_mon.
    apply proj_mon.
    apply proj_mon. 
Qed.





