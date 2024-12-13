From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header type.global type.local type.isomorphism type.merge type.decidability type.global_tree_ctx.
Require Import List String Coq.Arith.PeanoNat Relations Coq.Logic.Decidable.
Import ListNotations. 

Variant projection (R: gtt -> part -> ltt -> Prop): gtt -> part -> ltt -> Prop :=
  | proj_end : forall g r, 
               (isgPartsC r g -> False) -> 
               projection R g r (ltt_end)
  | proj_in  : forall p r xs ys,
               p <> r ->
               (isgPartsC r (gtt_send p r xs)) ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some(s, t) /\ R g r t)) xs ys ->
               projection R (gtt_send p r xs) r (ltt_recv p ys)
  | proj_out : forall r q xs ys,
               r <> q ->
               (isgPartsC r (gtt_send r q xs)) ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some(s, t) /\ R g r t)) xs ys ->
               projection R (gtt_send r q xs) r (ltt_send q ys)
  | proj_cont: forall p q r xs ys t,
               p <> q ->
               q <> r ->
               p <> r ->
               (isgPartsC r (gtt_send p q xs)) ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some t /\ R g r t)) xs ys ->
               isMerge t ys ->
               projection R (gtt_send p q xs) r t.

Definition projectionC g r t := paco3 projection bot3 g r t.

Definition projectableA G := forall pt, exists T, projectionC G pt T.

Lemma proj_mon: monotone3 projection.
Proof. unfold monotone3.
       intros.
       induction IN; intros.
       - constructor. easy.
       - constructor; try easy. 
         revert ys H1. clear H0.
         induction xs; intros.
         + subst. inversion H1. constructor.
         + subst. inversion H1. constructor.
           destruct H3 as [(H3a, H3b) | (s,(g,(t,(Ht1,(Ht2,Ht3)))))].
           subst. left. easy.
           subst. right. exists s. exists g. exists t.
           split. easy. split. easy. apply LE. easy.
           apply IHxs. easy.
       - constructor. easy. easy.
         revert ys H1. clear H0.
         induction xs; intros.
         + subst. inversion H1. constructor.
         + subst. inversion H1. constructor.
           destruct H3 as [(H3a, H3b) | (s,(g,(t,(Ht1,(Ht2,Ht3)))))].
           subst. left. easy.
           subst. right. exists s. exists g. exists t.
           split. easy. split. easy. apply LE. easy.
           apply IHxs. easy.
       - apply proj_cont with (ys := ys); try easy.
         revert H3. apply Forall2_mono; intros.
         destruct H3. left. easy.
         destruct H3. destruct H3. destruct H3. destruct H3. destruct H5. subst.
         right. exists x0. exists x1. exists x2. split. easy. split. easy.
         apply LE; try easy.
Qed.


Lemma proj_forward : forall p q xs, 
  wfgC (gtt_send p q xs) ->
  projectableA (gtt_send p q xs) -> 
  List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ projectableA g)) xs.
Proof.
  intros.
  apply Forall_forall; intros.
  destruct x. 
  - destruct p0. right. exists s. exists g. split. easy.
    unfold projectableA in *.
    intros. specialize(H0 pt). destruct H0 as (T, H0).
    specialize(in_some_implies_onth (s, g) xs H1); intros.
    destruct H2 as (n, H2). clear H1.
    pinversion H0; try easy.
    - subst. 
      assert(p <> q).
      {
        unfold wfgC in H. 
        destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))).
        specialize(guard_breakG_s2 (gtt_send p q xs) Gl Hc Hb Ha); intros.
        destruct H as (Gl2,(Hta,(Htb,(Htc,Htd)))).
        destruct Hta. subst. pinversion Htd; try easy. apply gttT_mon.
        destruct H as (p1,(q1,(lis,Hte))). subst. pinversion Htd; try easy. subst.
        inversion Htc; try easy.
        apply gttT_mon.
      }
      specialize(wfgC_after_step_all H3 H); intros.
      specialize(some_onth_implies_In n xs (s, g) H2); intros.
      specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) xs); intros.
      destruct H6. specialize(H6 H4). clear H7 H4.
      specialize(H6 (Some (s, g)) H5). destruct H6; try easy.
      destruct H4 as (st,(g0,(Ha,Hb))). inversion Ha. subst. clear H5 Ha.
      specialize(decidable_isgPartsC g0 pt Hb); intros.
      unfold decidable in H4. unfold not in H4.
      destruct H4.
      - assert False. apply H1.
        - case_eq (eqb pt p); intros.
          assert (pt = p). apply eqb_eq; try easy. subst. apply triv_pt_p; try easy.
        - case_eq (eqb pt q); intros.
          assert (pt = q). apply eqb_eq; try easy. subst. apply triv_pt_q; try easy.
        - assert (pt <> p). apply eqb_neq; try easy. 
          assert (pt <> q). apply eqb_neq; try easy.
          apply part_cont_b with (n := n) (s := st) (g := g0); try easy. easy.
      - exists ltt_end. pfold. constructor; try easy.
    - subst.
      clear H8 H5 H0 H. revert H9 H2.
      revert xs pt ys s g. clear p.
      induction n; intros; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H9. subst. clear H9.
        simpl in H2. subst. destruct H3; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
        inversion Ha. subst. exists t1. destruct Hc; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H9. subst. clear H9.
        specialize(IHn xs pt ys s g). apply IHn; try easy.
    - subst.
      clear H8 H5 H0 H. revert H9 H2.
      revert xs pt ys s g. clear q.
      induction n; intros; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H9. subst. clear H9.
        simpl in H2. subst. destruct H3; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
        inversion Ha. subst. exists t1. destruct Hc; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H9. subst. clear H9.
        specialize(IHn xs pt ys s g). apply IHn; try easy.
    - subst. clear H12 H8 H7 H6 H5 H0 H.
      revert H2 H11.
      revert xs pt s g ys. clear p q T.
      induction n; intros; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H11. subst. clear H11.
        simpl in H2. subst. destruct H3; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
        inversion Ha. subst.
        exists t1. destruct Hc; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H11. subst. clear H11.
        specialize(IHn xs pt s g ys). apply IHn; try easy.
    apply proj_mon.
    left. easy.
Qed.




Lemma pmergeCR_helper : forall n ys ys0 xs r s g ctxG,
    Forall (fun u : option ltt => u = None \/ u = Some ltt_end) ys0 -> 
    Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys -> 
    Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys0 -> 
    Forall2
       (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys -> 
    onth n ys = Some (s, g) -> 
    exists g', wfgC g /\
    onth n ys0 = Some ltt_end /\ projectionC g r ltt_end /\
    onth n xs = Some(s, g') /\ typ_gtth ctxG g' g.
Proof.
  induction n; intros.
  - destruct ys; try easy. destruct xs; try easy. destruct ys0; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    simpl in H3. subst. inversion H. subst. clear H.
    destruct H8; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
    destruct H6; try easy. destruct H as (s2,(g2,(Hd,He))). inversion Hd. subst.
    destruct H5; try easy. destruct H as (s3,(g3,(g4,(Hf,(Hg,Hh))))). inversion Hg. subst.
    destruct H2; try easy. inversion H. subst.
    exists g3. destruct Hc; try easy.
  - destruct ys; try easy. destruct xs; try easy. destruct ys0; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    simpl in H3. subst. inversion H. subst. clear H.
    specialize(IHn ys ys0 xs r s g ctxG). apply IHn; try easy.
Qed.



Lemma pmergeCR: forall G r,
          wfgC G ->
          projectionC G r ltt_end ->
          (isgPartsC r G -> False).
Proof. intros.
  specialize(balanced_to_tree G r H H1); intros.
  destruct H2 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd.
  revert Hc Hb Ha. rename H1 into Ht.
  revert H0 H Ht. revert G r ctxG.
  induction Gl using gtth_ind_ref; intros; try easy.
  - inversion Ha. subst.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send r q lsg) \/ u = Some (gtt_send q r lsg) \/ u = Some gtt_end)) ctxG); intros.
    destruct H1. specialize(H1 Hc). clear Hc H2. 
    specialize(some_onth_implies_In n ctxG G H3); intros.
    specialize(H1 (Some G) H2). destruct H1; try easy.
    destruct H1 as (q,(lsg,Hd)).
    - destruct Hd. inversion H1. subst. pinversion H0; try easy.  
      apply proj_mon.
    - destruct H1. inversion H1. subst. pinversion H0; try easy.
      apply proj_mon.
    - inversion H1. subst.
      specialize(part_break gtt_end r H Ht); intros.
      destruct H4 as (Gl,(Hta,(Htb,(Htc,Htd)))).
      destruct Htd. subst. inversion Htb; try easy.
      destruct H4 as (p1,(q1,(lis1,Htd))). subst.
      pinversion Hta; try easy. apply gttT_mon. 
  - inversion Ha. subst.
    pinversion H0; try easy. subst.
    specialize(part_cont ys r p q); intros.
    assert(exists (n : fin) (s : sort) (g : gtt), onth n ys = Some (s, g) /\ isgPartsC r g).
    apply H2; try easy.
    destruct H3 as (n,(s,(g,(Hd,He)))). clear H2 H10.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G : gtt) (r : string) (ctxG : seq.seq (option gtt)),
           projectionC G r ltt_end ->
           wfgC G ->
           isgPartsC r G ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some (gtt_send r q lsg) \/ u0 = Some (gtt_send q r lsg) \/ u0 = Some gtt_end))
             ctxG -> (ishParts r g -> False) -> typ_gtth ctxG g G -> False))) xs); intros.
    destruct H2. specialize(H2 H). clear H H3.
    specialize(triv_merge_ltt_end ys0 H14); intros.
    specialize(wfgC_after_step_all H5 H1); intros.
    clear Ht H1 H0 Ha H7 H5 H6 H9.
    specialize(pmergeCR_helper n ys ys0 xs r s g ctxG); intros.
    assert(exists g' : gtth,
       wfgC g /\
       onth n ys0 = Some ltt_end /\
       projectionC g r ltt_end /\ onth n xs = Some (s, g') /\ typ_gtth ctxG g' g).
    apply H0; try easy. clear H0 H3 H H13 H8.
    destruct H1 as (g',(Hf,(Hg,(Hh,(Hi,Hj))))).
    specialize(some_onth_implies_In n xs (s, g') Hi); intros.
    specialize(H2 (Some (s, g')) H).
    destruct H2; try easy. destruct H0 as (s1,(g1,(Hk,Hl))). inversion Hk. subst.
    specialize(Hl g r ctxG).
    apply Hl; try easy.
    specialize(ishParts_n Hb Hi); intros. apply H0; try easy.
  apply proj_mon.
Qed.

Lemma pmergeCR_s : forall G r,
    projectionC G r ltt_end ->
    (isgPartsC r G -> False).
Proof.
  intros.
  unfold isgPartsC in H0.
  destruct H0 as (Gl,(Ha,(Hb,Hc))).
  specialize(isgParts_depth_exists r Gl Hc); intros. destruct H0 as (n, H0). clear Hc.
  revert H0 Hb Ha H. revert G r Gl.
  induction n; intros.
  - inversion H0. 
    subst. 
    pinversion Ha. subst. pinversion H; try easy. subst.
    apply H1. unfold isgPartsC. exists (g_send r q lis). split. pfold. easy. 
    split. easy. apply isgParts_depth_back with (n := 0); try easy.
    apply proj_mon.
    apply gttT_mon.
  - subst. 
    pinversion Ha. subst. pinversion H; try easy. subst.
    apply H1. unfold isgPartsC. exists (g_send p r lis). split. pfold. easy. 
    split. easy. apply isgParts_depth_back with (n := 0); try easy.
    apply proj_mon.
    apply gttT_mon.
  inversion H0.
  - subst.
    pinversion Ha. subst.
    specialize(subst_parts_depth 0 0 n r g g Q H3 H2); intros.
    specialize(IHn G r Q). apply IHn; try easy.
    intros. specialize(Hb n0). destruct Hb.
    inversion H5. subst. exists 0. constructor.
    - subst. specialize(subst_injG 0 0 (g_rec g) g Q Q0 H7 H3); intros. subst.
      exists m. easy.
      apply gttT_mon.
  - subst. pinversion H; try easy.
    - subst. apply H1. unfold isgPartsC. exists (g_send p q lis).
      split. easy. split. easy. apply isgParts_depth_back with (n := S n); try easy.
    - subst.
      specialize(triv_merge_ltt_end ys H10); intros.
      pinversion Ha. subst.
      specialize(guard_cont Hb); intros.
      specialize(Forall2_prop_r k lis xs (s, g) (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : global) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) H4 H13); intros.
       destruct H14 as (p1,(Hc,Hd)).
       destruct Hd; try easy. destruct H14 as (s1,(g1,(g2,(He,(Hf,Hg))))). inversion He. subst. clear H13.
       specialize(Forall2_prop_r k xs ys (s1, g2) (fun (u : option (sort * gtt)) (v : option ltt) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtt) (t : ltt),
           u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) Hf H9); intros.
       destruct H13 as (p1,(Hh,Hi)).
       destruct Hi; try easy. destruct H13 as (s2,(g3,(g4,(Hj,(Hk,Hl))))). inversion Hj. subst.
       clear H9.
       specialize(Forall_prop k lis (s2, g1) (fun u : option (sort * global) =>
         u = None \/
         (exists (s : sort) (g : global),
            u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) H4 H12); intros.
       destruct H9; try easy. destruct H9 as (s3,(g5,(Hm,Hn))). inversion Hm. subst. clear H12.
       specialize(Forall_prop k ys g4 (fun u : option ltt => u = None \/ u = Some ltt_end) Hk H11); intros.
       destruct H9; try easy. inversion H9. subst.
       pclearbot. destruct Hl; try easy.
       specialize(IHn g3 r g5). apply IHn; try easy.
     apply gttT_mon.
     apply proj_mon.
Qed.


Lemma proj_end_cont_end : forall s s' ys p,
        wfgC (gtt_send s s' ys) ->
        s <> s' ->
        projectionC (gtt_send s s' ys) p ltt_end -> 
        List.Forall (fun u => u = None \/ (exists st g, u = Some(st, g) /\ projectionC g p ltt_end)) ys.
Proof.
  intros. pinversion H1. subst.
  - assert(List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ (isgPartsC p g -> False))) ys).
    {
      specialize(wfgC_after_step_all H0 H); intros. clear H0 H1. rename H into Ht.
      apply Forall_forall; intros.
      specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys); intros.
      destruct H0. specialize(H0 H3). clear H3 H1.
      specialize(H0 x H). destruct H0. left. easy.
      destruct H0 as (st,(g,(Ha,Hb))). subst.
      right. exists st. exists g. split. easy.
      intros. apply H2. unfold isgPartsC.
      pose proof Ht as Ht2.
      unfold wfgC in Ht. destruct Ht as (Gl,(Hta,(Htb,(Htc,Htd)))).
      specialize(guard_breakG_s2 (gtt_send s s' ys) Gl Htc Htb Hta); intros. clear Hta Htb Htc. clear Gl.
      destruct H1 as (Gl,(Hta,(Htb,(Htc,Hte)))).
      destruct Hta.
      - subst. pinversion Hte. apply gttT_mon.
      - destruct H1 as (p1,(q1,(lis,Hsa))). subst.
        pinversion Hte; try easy. subst. 
        specialize(in_some_implies_onth (st,g) ys H); intros. destruct H1 as (n,Hsb).
        unfold isgPartsC in H0. destruct H0 as (G1,(Hla,Hlb)).
        exists (g_send s s' (overwrite_lis n (Some (st, G1)) lis)).
        split.
        pfold. constructor. revert Hsb H3 Hla.
        clear Htd H2 H Hb Hlb Hte Htc Htb Ht2. revert ys st g G1 lis. clear s s' p.
        induction n; intros; try easy.
        - destruct ys; try easy. destruct lis; try easy. inversion H3. subst. clear H3.
          constructor; try easy. right. exists st. exists G1. 
          simpl in Hsb. subst. destruct H2; try easy.
          exists g. split. easy. split. easy. left. easy.
        - destruct ys; try easy. destruct lis; try easy. inversion H3. subst. clear H3.
          specialize(IHn ys st g G1 lis Hsb H5 Hla).
          constructor; try easy.
            split. 
            - destruct Hlb. intros. destruct n0. exists 0. constructor.
              specialize(H0 n0). specialize(Htb (S n0)).
              destruct Htb. destruct H0. exists (Nat.max x0 x).
              constructor. inversion H4. subst.
              clear Hsb H3 H4 Htc Hte Ht2 H1 Hb H H2 Htd Hla. revert H8 H0.
              revert st G1 x0 lis x n0. clear s s' ys p g.
              induction n; intros; try easy. destruct lis; try easy.
              - constructor; try easy. right. exists st. exists G1. split. easy.
                specialize(guardG_more n0 x0 (Nat.max x0 x) G1); intros. apply H; try easy.
                apply max_l; try easy.
              - inversion H8. subst. constructor; try easy. right. exists st. exists G1.
                split. easy. specialize(guardG_more n0 x0 (Nat.max x0 x) G1); intros. apply H; try easy.
                apply max_l; try easy.
                apply Forall_forall; intros. 
                specialize(Forall_forall (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ guardG n0 x g)) lis); intros.
                destruct H1. specialize(H1 H3). clear H4 H3. specialize(H1 x1 H).
                destruct H1. left. easy. destruct H1 as (s1,(g1,(Ha,Hb))). subst.
                right. exists s1. exists g1. split. easy.
                specialize(guardG_more n0 x (Nat.max x0 x) g1); intros. apply H1; try easy.
                apply max_r; try easy.
              - destruct lis; try easy. constructor; try easy. left. easy.
                specialize(IHn st G1 x0 nil x n0 H8 H0). apply IHn; try easy.
                inversion H8. subst. clear H8.
                specialize(IHn st G1 x0 lis x n0 H3 H0). constructor; try easy.
                destruct H2. left. easy.
                destruct H as (s,(g,(Ha,Hb))). subst. right. exists s. exists g.
                split. easy.
                specialize(guardG_more n0 x (Nat.max x0 x) g); intros. apply H; try easy.
                apply max_r; try easy. 
          - case_eq (eqb p s); intros.
            assert (p = s). apply eqb_eq; try easy. subst. apply pa_sendp.
          - case_eq (eqb p s'); intros.
            assert (p = s'). apply eqb_eq; try easy. subst. apply pa_sendq.
          - assert (p <> s). apply eqb_neq; try easy. 
            assert (p <> s'). apply eqb_neq; try easy.
            apply pa_sendr with (n := n) (s := st) (g := G1); try easy. 
            apply overwriteExtract; try easy.
      apply gttT_mon.
    }
    apply Forall_forall; intros.
    specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ (isgPartsC p g -> False))) ys); intros.
    destruct H5. specialize(H5 H3). clear H6 H3. specialize(H5 x H4).
    destruct H5. left. easy. destruct H3 as (st,(g,(Ha,Hb))). subst.
    right. exists st. exists g. split. easy. pfold. apply proj_end; try easy.
  - subst.
    specialize(triv_merge_ltt_end ys0 H12); intros. clear H12 H7 H6 H5 H1 H.
    revert H11 H2. clear H0 H8. clear s s'. revert p ys0.
    induction ys; intros; try easy.
    - destruct ys0; try easy. inversion H2. subst. clear H2. inversion H11. subst. clear H11.
      specialize(IHys p ys0 H6 H3). constructor; try easy.
      clear IHys H6 H3. destruct H4. left. easy.
      destruct H as (s,(g,(t,(Ha,(Hb,Hc))))). subst.
      right. exists s. exists g. split. easy. destruct H1; try easy. inversion H. subst. 
      destruct Hc; try easy.
    apply proj_mon.
Qed.

Lemma proj_inj_list : forall lsg ys ys0 p r,
      (forall (t t' : ltt) (g : gtt),
      wfgC g -> projectionC g p t -> projectionC g p t' -> r t t') -> 
      Forall2
       (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtt) (t : ltt),
           u = Some (s, g) /\ v = Some (s, t) /\ upaco3 projection bot3 g p t)) lsg ys -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some (s, t) /\ upaco3 projection bot3 g p t)) lsg ys0 -> 
      Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) lsg -> 
      isoList (upaco2 lttIso r) ys ys0.
Proof.
  induction lsg; intros.
  - destruct ys; try easy. destruct ys0; try easy.
  - destruct ys; try easy. destruct ys0; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    specialize(IHlsg ys ys0 p r H H8 H9 H4). clear H4 H9 H8.
    
    destruct H6. destruct H0. subst. 
    destruct H5. destruct H0. subst. easy.
    destruct H0 as (s,(g,(t,(Ha,(Hb,Hc))))). easy.
    destruct H0 as (s,(g,(t,(Ha,(Hb,Hc))))). subst.
    destruct H3; try easy. destruct H0 as (s1,(g1,(Hd,He))). inversion Hd. subst.
    destruct H5; try easy. destruct H0 as (s2,(g2,(t',(Hg,(Hh,Hi))))). inversion Hg. subst.
    simpl. split. easy. split; try easy.
    right. pclearbot. specialize(H t t' g2). apply H; try easy.
Qed.

Lemma proj_end_inj_helper : forall n1 ys0 ys1 ys xs ctxG s1 g1 r,
      Forall (fun u : option ltt => u = None \/ u = Some ltt_end) ys0 -> 
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
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys0 -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys1 ->
      onth n1 ys = Some (s1, g1) -> 
      exists g2 t,
      onth n1 xs = Some(s1, g2) /\ typ_gtth ctxG g2 g1 /\
      onth n1 ys0 = Some ltt_end /\ projectionC g1 r ltt_end /\
      onth n1 ys1 = Some t /\ projectionC g1 r t /\ wfgC g1.
Proof.
  induction n1; intros; try easy.
  - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy.
    destruct xs; try easy.
    inversion H3. subst. clear H3. inversion H2. subst. clear H2.
    inversion H1. subst. clear H1. inversion H0. subst. clear H0.
    inversion H. subst. clear H.
    simpl in H4. subst.
    destruct H6; try easy. destruct H as (s2,(g2,(g3,(Ha,(Hb,Hc))))). inversion Hb. subst.
    destruct H3; try easy. destruct H as (s3,(g4,(Hd,He))). inversion Hd. subst.
    destruct H7; try easy. destruct H as (s4,(g5,(t1,(Hf,(Hg,Hh))))). inversion Hf. subst.
    destruct H8; try easy. destruct H as (s5,(g6,(t2,(Hi,(Hj,Hk))))). inversion Hi. subst.
    destruct H2; try easy. inversion H. subst.
    simpl. exists g2. exists t2. destruct Hh; try easy. destruct Hk; try easy.
  - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy.
    destruct xs; try easy.
    inversion H3. subst. clear H3. inversion H2. subst. clear H2.
    inversion H1. subst. clear H1. inversion H0. subst. clear H0.
    inversion H. subst. clear H.
    specialize(IHn1 ys0 ys1 ys xs ctxG s1 g1 r). apply IHn1; try easy.
Qed.


Lemma proj_end_inj : forall g t p,
          wfgC g -> 
          projectionC g p ltt_end -> 
          projectionC g p t -> 
          t = ltt_end.
Proof.
  intros.
  specialize(decidable_isgPartsC g p H); intros. unfold decidable in H2.
  destruct H2.
  - specialize(balanced_to_tree g p H H2); intros.
    destruct H3 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd. rename H2 into Ht.
    revert Hc Hb Ha H1 H0 H Ht. revert ctxG p t g.
    induction Gl using gtth_ind_ref; intros.
    - inversion Ha. subst.
      specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
      destruct H2. specialize(H2 Hc). clear Hc H3.
      specialize(some_onth_implies_In n ctxG g H4); intros.
      specialize(H2 (Some g) H3). destruct H2; try easy.
      destruct H2 as (q1,(lsg1,Hc)). 
      - destruct Hc. inversion H2. subst. pinversion H0; try easy. 
        apply proj_mon.
      - destruct H2. inversion H2. subst. pinversion H0; try easy.
        apply proj_mon.
      - inversion H2. subst. pinversion H1; try easy. apply proj_mon.
    - inversion Ha. subst.
      pinversion H0; try easy. subst.
      pinversion H1; try easy. subst. clear H17 H16 H13 H12. rename p0 into r.
      specialize(part_cont ys r p q H11); intros.
      assert(exists (n : fin) (s : sort) (g : gtt), onth n ys = Some (s, g) /\ isgPartsC r g).
      apply H3; try easy.
      clear H3. destruct H4 as (n1,(s1,(g1,(He,Hf)))).
      specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (ctxG : seq.seq (option gtt)) (p : string) (t : ltt) (g0 : gtt),
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some (gtt_send p q lsg) \/ u0 = Some (gtt_send q p lsg) \/ u0 = Some gtt_end))
             ctxG ->
           (ishParts p g -> False) ->
           typ_gtth ctxG g g0 ->
           projectionC g0 p t -> projectionC g0 p ltt_end -> wfgC g0 -> isgPartsC p g0 -> t = ltt_end)))
      xs); intros.
      destruct H3. specialize(H3 H). clear H H4.
      specialize(wfgC_after_step_all H6 H2); intros.
      specialize(triv_merge_ltt_end ys0 H15); intros.
      specialize(proj_end_inj_helper n1 ys0 ys1 ys xs ctxG s1 g1 r); intros.
      assert(exists (g2 : gtth) (t : ltt),
       onth n1 xs = Some (s1, g2) /\
       typ_gtth ctxG g2 g1 /\
       onth n1 ys0 = Some ltt_end /\
       projectionC g1 r ltt_end /\ onth n1 ys1 = Some t /\ projectionC g1 r t /\ wfgC g1).
      apply H5; try easy. clear H5 H4 H H20 H14 H9.
      destruct H12 as (g2,(t1,(Hta,(Htb,(Htc,(Htd,(Hte,Htf))))))).
      specialize(some_onth_implies_In n1 xs (s1, g2) Hta); intros.
      specialize(H3 (Some (s1, g2)) H). destruct H3; try easy.
      destruct H3 as (s2,(g3,(Hsa,Hsb))). inversion Hsa. subst.
      specialize(Hsb ctxG r t1 g1).
      assert(t1 = ltt_end). apply Hsb; try easy.
      specialize(ishParts_n Hb Hta); intros. apply H3; try easy. subst.
      specialize(merge_end_back n1 ys1 t); intros. apply H3; try easy.
      apply proj_mon. apply proj_mon.
  - unfold not in H2. pinversion H0; try easy.
    subst. pinversion H1; try easy.
    - subst. specialize(H2 H5). easy.
    - subst. specialize(H2 H5). easy.
    - subst. specialize(H2 H7). easy.
  apply proj_mon. 
  subst. specialize(H2 H6). easy. apply proj_mon.
Qed.

Theorem proj_inj : forall [g p t t'],
          wfgC g -> 
          projectionC g p t -> 
          projectionC g p t' -> 
          t = t'.
Proof.
  intros.
  apply lltExt. revert H H0 H1. revert t t' g. pcofix CIH; intros.
  specialize(decidable_isgPartsC g p H0); intros. unfold decidable in H.
  destruct H.
  pose proof H0 as Ht. unfold wfgC in H0. destruct H0 as (Gl,(Ha,(Hb,(Hc,Hd)))).
  specialize(balanced_to_tree g p Ht H); intros. clear Ha Hb Hc Hd. clear H. rename H0 into H.
  destruct H as (G,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd.
  revert H1 H2 Ht Ha Hb Hc CIH. revert t t' g. clear Gl.
  induction G using gtth_ind_ref; intros; try easy. 
  
  - inversion Ha. subst.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/
           u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
    destruct H. specialize(H Hc). clear Hc H0. 
    specialize(some_onth_implies_In n ctxG g H3); intros.
    specialize(H (Some g) H0). destruct H; try easy.
    destruct H as (q,(lsg,Hd)). 
    clear H0. destruct Hd.
    - inversion H. subst.
      pinversion H1; try easy. subst. 
      assert False. apply H0. apply triv_pt_p; try easy. easy.
      subst. 
      pinversion H2; try easy. subst.
      pfold. constructor.
      specialize(wfgC_after_step_all H8 Ht); intros.
      specialize(proj_inj_list lsg ys ys0 p r); intros. apply H4; try easy.
      apply proj_mon. apply proj_mon.
    destruct H.
    - inversion H. subst.
      pinversion H1; try easy. subst. 
      assert False. apply H0. apply triv_pt_q; try easy. easy.
      subst. 
      pinversion H2; try easy. subst.
      pfold. constructor.
      specialize(wfgC_after_step_all H8 Ht); intros.
      specialize(proj_inj_list lsg ys ys0 p r); intros. apply H4; try easy.
      apply proj_mon. apply proj_mon.
    - inversion H. subst.
      pinversion H2. subst. pinversion H1. subst. pfold. constructor.
      apply proj_mon. apply proj_mon.
  - inversion Ha. subst. 
    rename p0 into s. rename q into s'.
    pinversion H2. 
    - subst. 
      specialize(proj_end_inj (gtt_send s s' ys) t p); intros.
      assert(t = ltt_end).
      {
        apply H3; try easy. pfold. easy.
      }
      subst. pfold. constructor.
    - subst. assert False. apply Hb. constructor. easy. subst.
      pinversion H1; try easy. subst.
      pfold. constructor.
      specialize(proj_inj_list ys ys1 ys0 p r); intros.
      apply H0; try easy. 
      specialize(wfgC_after_step_all H6 Ht); try easy.
      apply proj_mon.
    - subst. 
      pinversion H1; try easy. subst.
      {
        assert (List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists t t', u = Some t /\ v = Some t' /\ paco2 lttIso r t t')) ys1 ys0).
        {
          specialize(wfgC_after_step_all H11 Ht); intros.
          clear H20 H16 H15 H12 H11 H14 H10 H9 H6 H5 H7 H1 H2 Ht Ha.
          revert H0 H19 H13 H8 CIH Hc Hb H.
          revert p r s s' xs ctxG ys1 ys0. clear t t'.
          induction ys; intros; try easy.
          - destruct ys0; try easy. destruct ys1; try easy.
          - destruct ys0; try easy. destruct ys1; try easy. destruct xs; try easy.
            inversion H0. subst. clear H0. inversion H19. subst. clear H19.
            inversion H13. subst. clear H13. inversion H8. subst. clear H8.
            inversion H. subst. clear H.
            specialize(IHys p r s s' xs ctxG ys1 ys0).
            assert(Forall2
               (fun u v : option ltt =>
                u = None /\ v = None \/
                (exists t t' : ltt, u = Some t /\ v = Some t' /\ paco2 lttIso r t t')) ys1 ys0).
            apply IHys; try easy. specialize(ishParts_hxs Hb); try easy.
            subst.
            constructor; try easy.
            {
              clear H8 H12 H10 H7 H4 IHys.
              destruct H5. 
              - destruct H0. subst. destruct H6. destruct H0. subst. left. easy.
                destruct H0 as (st,(g,(t,(Ha,(Hd,Hf))))). subst. easy. clear H.
              - destruct H0 as (s1,(g1,(t1,(Hd,(He,Hf))))).
                subst.
                destruct H3; try easy. destruct H as (s2,(g2,(Hg,Hh))). inversion Hg. subst.
                destruct H9; try easy. destruct H as (s3,(g3,(g4,(Hi,(Hj,Hk))))). inversion Hj. subst.
                destruct H6; try easy. destruct H as (s4,(g5,(t2,(Hl,(Hm,Hn))))). inversion Hl. subst.
                destruct H2; try easy. destruct H as (s5,(g6,(Ho,Hp))). inversion Ho. subst.
                clear Hl Hj Hg Ho.
                specialize(Hp t1 t2 g5).
                right. exists t1. exists t2.
                split. easy. split. easy. pclearbot. apply Hp; try easy.
                specialize(ishParts_x Hb); try easy.
            }
        }
        subst.
        specialize(isMerge_injw t t' r ys1 ys0 H0); intros. subst.
        apply H3; try easy.
      }
    apply proj_mon.
    apply proj_mon.
  - unfold not in *.
    pinversion H1; try easy. 
    - subst. pinversion H2; try easy. subst. pfold. constructor.
    - subst. specialize(H3 H5). easy.
    - subst. specialize(H3 H5). easy.
    - subst. specialize(H3 H7). easy.
    apply proj_mon.
  - subst. specialize(H H4). easy.
  - subst. specialize(H H4). easy.
  - subst. specialize(H H6). easy.
  apply proj_mon.
Qed.

Lemma non_triv_proj_part : forall [G p q x],
    projectionC G p (ltt_send q x) -> isgPartsC p G.
Proof.
  intros. pinversion H; try easy.
  apply proj_mon.
Qed.


Lemma ctx_merge2 : forall s s0 s1 g1 l p q x,
    p <> s -> p <> s0 ->
    (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
       typ_gtth ctxG G' g1 /\
       (ishParts p G' -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
             u = Some g /\
             g = gtt_send p q lsg /\
             Forall2
               (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                u0 = None /\ v = None \/
                (exists (s : sort) (t : ltt) (g' : gtt),
                   u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG /\
       usedCtx ctxG G') -> 
       (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
       typ_gtth ctxG G' (gtt_send s s0 l) /\
       (ishParts p G' -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
             u = Some g /\
             g = gtt_send p q lsg /\
             Forall2
               (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                u0 = None /\ v = None \/
                (exists (s : sort) (t : ltt) (g' : gtt),
                   u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG /\
       usedCtx ctxG G') -> 
       (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
  typ_gtth ctxG G' (gtt_send s s0 (Some (s1, g1) :: l)) /\
  (ishParts p G' -> False) /\
  Forall
    (fun u : option gtt =>
          u = None \/
          (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
             u = Some g /\
             g = gtt_send p q lsg /\
             Forall2
               (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                u0 = None /\ v = None \/
                (exists (s : sort) (t : ltt) (g' : gtt),
                   u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG /\
  usedCtx ctxG G').
Proof.
  intros.
  destruct H1 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))).
  destruct H2 as (Gl2,(ctxJ,(He,(Hf,(Hg,Hh))))).
  inversion He. subst.
  - specialize(some_onth_implies_In n ctxJ (gtt_send s s0 l) H1); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxJ); intros.
    destruct H3. specialize(H3 Hg). clear H4 Hg.
    specialize(H3 (Some (gtt_send s s0 l)) H2). destruct H3; try easy.
    destruct H3 as (g2,(lsg,(Hi,(Hj,Hk)))). inversion Hi. subst. inversion H4. subst. easy.
  - subst.
    assert(exists Gl', typ_gtth (noneLis (List.length ctxJ) ++ ctxG) Gl' g1 /\ usedCtx (noneLis (List.length ctxJ) ++ ctxG) Gl' /\ (ishParts p Gl' -> False)).
    {
      clear Hc Hf He Hg Hh H5 H7.
      clear H H0.
      revert Ha Hb Hd. revert g1 p Gl ctxG ctxJ. clear s s0 s1 l xs.
      apply shift_to; try easy.
    }
    destruct H1 as (Gl',(H1,(H2,Htm))).
    exists (gtth_send s s0 (Some (s1, Gl') :: xs)). exists (ctxJ ++ ctxG).
    - split.
      constructor; try easy. apply SList_b; try easy.
      constructor; try easy.
      - right. exists s1. exists Gl'. exists g1. split. easy. split. easy.
        apply typ_gtth_pad_l; try easy.
      - revert H7. apply Forall2_mono; intros.
        destruct H3. left. easy.
        right. destruct H3 as (s2,(g2,(g3,(Hta,(Htb,Htc))))). subst.
        exists s2. exists g2. exists g3. split. easy. split. easy.
        apply typ_gtth_pad_r with (ctxG := ctxG); try easy.
    - split.
      intros. inversion H3. subst. easy. subst. easy. subst.
      destruct n.
      - simpl in H12. inversion H12. subst. apply Hb. easy.
      - apply Hf. apply ha_sendr with (n := n) (s := s2) (g := g); try easy.
    - split.
      clear Htm H2 H1 H7 H5 Hh He Hf Hd Hb Ha H0 H. revert Hg Hc.
      revert p ctxG. clear s s0 s1 g1 l Gl xs Gl'.
      induction ctxJ; intros; try easy. inversion Hg. subst. clear Hg.
      specialize(IHctxJ p ctxG H2 Hc). constructor; try easy.
    - inversion Hh. subst.
      apply used_con with (ctxGLis := Some (noneLis (Datatypes.length ctxJ) ++ ctxG) :: ctxGLis); try easy.
      apply cmconss with (t := ctxJ); try easy.
      clear H10 H8 Htm H2 H1 H7 H5  Hh Hg He Hf Hd Hc Hb Ha H0 H.
      clear ctxGLis Gl' xs Gl p l g1 s1 s s0.
      induction ctxJ; intros; try easy. simpl. constructor.
      constructor; try easy. 
      destruct a. right. right. left. exists g. easy.
      left. easy.
    - constructor; try easy. right. exists (noneLis (Datatypes.length ctxJ) ++ ctxG).
      exists s1. exists Gl'. easy.
Qed.


Lemma _a_29_11 : forall G p q x,
    wfgC G ->
    projectionC G p (ltt_send q x) ->
    exists G' ctxJ, 
      typ_gtth ctxJ G' G /\ (ishParts p G' -> False) /\
      List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg /\
        List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t g', u = Some(s, g') /\ v = Some(s, t) /\
          projectionC g' p t
        )) lsg x 
      )) ctxJ /\ usedCtx ctxJ G'.
Proof.
    intros.
    specialize(non_triv_proj_part H0); intros Ht1.
    pose proof H as Ht. unfold wfgC in H. destruct H as (G',(Ha,(Hb,(Hc,Hd)))). clear Hc Hb Ha.
    specialize(balanced_to_tree G p Ht Ht1); intros. destruct H as (Gl,(ctxG,(Hta,(Htb,(Htc,Htd))))).
    
    clear Ht Hd Htd Ht1.
    clear G'.
    revert Htc Htb Hta H0. revert G p q x ctxG.
    induction Gl using gtth_ind_ref; intros; try easy.
    - inversion Hta. subst. exists (gtth_hol n).
      exists (extendLis n (Some G)).
      split. 
      constructor.
      specialize(extendExtract n (Some G)); try easy.
      split. easy.
      specialize(Forall_forall (fun u : option gtt =>
         u = None \/
         (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
            u = Some (gtt_send p q lsg) \/
            u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
      destruct H. specialize(H Htc). clear Htc H1. 
      specialize(some_onth_implies_In n ctxG G H2); intros.
      specialize(H (Some G) H1). destruct H; try easy.
      destruct H as (r,(lsg,Hsa)).
      
      destruct Hsa. inversion H. subst.
      - pinversion H0; try easy. subst. clear H7. clear H10.
        revert H11. clear H8 H1 H H2 H0 Hta Htb. clear ctxG. revert lsg x p q.
        induction n; intros; try easy. simpl. split.
        - constructor; try easy. right. exists (gtt_send p q lsg). exists lsg.
          split. easy. split. easy. revert H11.
          apply Forall2_mono; intros. destruct H. left. easy.
          right. destruct H as (s,(g,(t,(Ha,(Hb,Hc))))). subst. exists s. exists t. exists g. pclearbot. easy.
          specialize(used_hol 0 (gtt_send p q lsg)); intros. easy.
        - specialize(IHn lsg x p q H11). split. constructor; try easy. left. easy.
          constructor.
        apply proj_mon.
      - destruct H. inversion H. subst. pinversion H0; try easy. apply proj_mon.
      - inversion H. subst. pinversion H0; try easy. apply proj_mon.
    - inversion Hta. subst.
      rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
      - assert(List.Forall2 (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ 
           exists (G' : gtth) (ctxJ : seq.seq (option gtt)),
             typ_gtth ctxJ G' g' /\
             (ishParts p G' -> False) /\
             Forall
               (fun u0 : option gtt =>
                u0 = None \/
                (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                   u0 = Some g0 /\
                   g0 = gtt_send p q lsg /\
                   Forall2
                     (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                      u1 = None /\ v = None \/
                      (exists (s0 : sort) (t : ltt) (g' : gtt),
                         u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' p t)) lsg x)) ctxJ /\
             usedCtx ctxJ G')) xs ys).
        {
          clear H6 Hta.
          pinversion H0. subst. assert False. apply Htb. constructor. easy.
          subst. 
          clear H8 H6 H5 H4 H0.
          revert H12 H11 H7 Htb Htc H. revert xs p q x ys ctxG s s'.
          induction ys0; intros; try easy.
          destruct ys; try easy. destruct xs; try easy. 
          specialize(IHys0 xs p q x ys ctxG s s').
          inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion H. subst. clear H.
          inversion H12.
          - subst.
            destruct ys; try easy. destruct xs; try easy.
            clear H6 H8 H5 IHys0.
            constructor; try easy. destruct H4. left. easy.
            destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
            right. exists s1. exists g1. exists g2. split. easy. split. easy.
            destruct H3; try easy. destruct H as (s2,(g3,(t1,(Hd,(He,Hf))))). inversion Hd. subst.
            inversion He. subst. 
            destruct H2; try easy. destruct H as (s3,(g4,(Hg,Hh))). inversion Hg. subst.
            pclearbot.
            specialize(Hh g3 p q x ctxG). apply Hh; try easy.
            assert(onth 0 [Some (s3, g4)] = Some (s3, g4)). easy.
            specialize(ishParts_n Htb H); try easy.
          - subst.
            destruct H4. destruct H. subst.
            constructor; try easy. left. easy.
            apply IHys0; try easy.
            specialize(ishParts_hxs Htb); try easy.
            destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
            destruct H3; try easy. destruct H as (s2,(g3,(t1,(Hd,(He,Hf))))). easy.
          - subst.
            assert(Forall2
          (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
           u = None /\ v = None \/
           (exists (s : sort) (g : gtth) (g' : gtt),
              u = Some (s, g) /\
              v = Some (s, g') /\
              (exists (G' : gtth) (ctxJ : seq.seq (option gtt)),
                 typ_gtth ctxJ G' g' /\
                 (ishParts p G' -> False) /\
                 Forall
                   (fun u0 : option gtt =>
                    u0 = None \/
                    (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                       u0 = Some g0 /\
                       g0 = gtt_send p q lsg /\
                       Forall2
                         (fun (u1 : option (sort * gtt)) (v0 : option (sort * ltt)) =>
                          u1 = None /\ v0 = None \/
                          (exists (s0 : sort) (t : ltt) (g'0 : gtt),
                             u1 = Some (s0, g'0) /\ v0 = Some (s0, t) /\ projectionC g'0 p t)) lsg x))
                   ctxJ /\ usedCtx ctxJ G'))) xs ys).
            {
              apply IHys0; try easy.
              specialize(ishParts_hxs Htb); try easy.
            }
            constructor; try easy.
            clear H H1 H6 H8 H5 H12 IHys0.
            destruct H3; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Hb. subst.
            destruct H4; try easy. destruct H as (s2,(g2,(g3,(Hd,(He,Hf))))). inversion He. subst.
            destruct H2; try easy. destruct H as (s3,(g4,(Hg,Hh))). inversion Hg. subst.
            right. exists s3. exists g4. exists g3. split. easy. split. easy. pclearbot.
            specialize(Hh g3 p q x ctxG). apply Hh; try easy.
            specialize(ishParts_x Htb); try easy.
          apply proj_mon.
        }
        clear H7 Htb Htc H.
        - case_eq (eqb p s); intros.
          pinversion H0; try easy. subst.
          exists (gtth_hol 0). exists [Some (gtt_send p q ys)].
          - split. constructor. easy.
          - split. intros. inversion H2.
          - split. constructor; try easy. right. exists (gtt_send p q ys). exists ys.
            split. easy. split. easy.
            revert H11. apply Forall2_mono; intros; try easy.
            destruct H2. left. easy. right.
            destruct H2 as (s1,(g1,(t1,(Ha,(Hb,Hc))))). subst. exists s1. exists t1. exists g1.
            pclearbot. easy. 
          - assert(usedCtx (extendLis 0 (Some (gtt_send p q ys))) (gtth_hol 0)). constructor. simpl in H2. easy. subst.
            assert (p = s). apply eqb_eq; try easy. subst. easy.
            apply proj_mon.
        - case_eq (eqb p s'); intros.
          assert (p = s'). apply eqb_eq; try easy. subst.
          pinversion H0; try easy. apply proj_mon.
        - assert (p <> s). apply eqb_neq; try easy. 
          assert (p <> s'). apply eqb_neq; try easy.
      - clear H H2.
        clear H0 Hta.
        revert H3 H4 H1 H6. revert s s' p q x ys. clear ctxG.
        induction xs; intros; try easy.
        destruct ys; try easy. inversion H1. subst. clear H1.
        specialize(SList_f a xs H6); intros.
        specialize(IHxs s s' p q x ys H3 H4).
        destruct H.
        - assert(exists (G' : gtth) (ctxJ : seq.seq (option gtt)),
         typ_gtth ctxJ G' (gtt_send s s' ys) /\
         (ishParts p G' -> False) /\
         Forall
           (fun u : option gtt =>
            u = None \/
            (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
               u = Some g /\
               g = gtt_send p q lsg /\
               Forall2
                 (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                  u0 = None /\ v = None \/
                  (exists (s : sort) (t : ltt) (g' : gtt),
                     u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxJ /\
         usedCtx ctxJ G'). apply IHxs; try easy. clear IHxs H8 H6.
          destruct H5.
          - destruct H1. subst.
            destruct H0 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))).
            inversion Ha. subst. 
            - specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG); intros.
              destruct H1. specialize(H1 Hc). clear H2 Hc.
              specialize(some_onth_implies_In n ctxG (gtt_send s s' ys) H0); intros.
              specialize(H1 (Some (gtt_send s s' ys)) H2).
              destruct H1; try easy. destruct H1 as (g1,(lsg1,(He,(Hf,Hg)))). inversion He. subst.
              inversion H5. subst. easy.
            - subst. exists (gtth_send s s' (None :: xs0)). exists ctxG.
              - split. constructor. apply SList_b. easy.
                constructor; try easy. left. easy.
              - split. intros. apply Hb.
                inversion H0. subst. easy. subst. easy. subst.
                destruct n; try easy. apply ha_sendr with (n := n) (s := s0) (g := g); try easy.
              - split. easy.
              - inversion Hd. subst.
                apply used_con with (ctxGLis := None :: ctxGLis); try easy.
                constructor; try easy. constructor; try easy. left. easy.
          destruct H1 as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst. clear H.
          apply ctx_merge2; try easy.
        - destruct H as (H,(a0,Ht)). subst.
          destruct ys; try easy. clear H8 IHxs H6.
          destruct H5; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
          destruct Hc as (Gl,(ctxG,(Hc,(Hd,(He,Hf))))).
          exists (gtth_send s s' [Some (s1, Gl)]). exists ctxG.
          - split. constructor; try easy. constructor; try easy. 
            right. exists s1. exists Gl. exists g2. easy.
          - split. intros. apply Hd. inversion H. subst. easy. subst. easy. subst.
            destruct n; try easy. inversion H8. subst. easy.
            destruct n; try easy.
          - split. easy.
          - apply used_con with (ctxGLis := [Some ctxG]); try easy. constructor.
            constructor; try easy. right. exists ctxG. exists s1. exists Gl. easy.
Qed.

Lemma _a_29_part : forall ctxG G' G p q x ys,
    typ_gtth ctxG G' G -> 
    projectionC G p (ltt_send q x) ->
    projectionC G q (ltt_recv p ys) ->
    (ishParts p G' -> False) -> 
    (ishParts q G' -> False).
Proof.
    intros ctxG G'. revert ctxG.
    induction G' using gtth_ind_ref; intros; try easy.
    rename p into r. rename q into s. rename p0 into p. rename q0 into q.
    inversion H0. subst.
    inversion H4; try easy. 
    - subst.
      pinversion H2; try easy. subst.
      apply proj_mon.
    - subst. 
      pinversion H2; try easy. subst.
      apply H3. constructor.
      apply proj_mon.
    - subst.
      specialize(some_onth_implies_In n xs (s0, g) H13); intros.
      specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (ctxG : seq.seq (option gtt)) (G : gtt) (p q : string)
             (x ys : seq.seq (option (sort * ltt))),
           typ_gtth ctxG g G ->
           projectionC G p (ltt_send q x) ->
           projectionC G q (ltt_recv p ys) ->
           (ishParts p g -> False) -> ishParts q g -> False))) xs); intros.
    destruct H6. specialize(H6 H). clear H H7.
    specialize(H6 (Some (s0, g)) H5).
    destruct H6; try easy.
    destruct H. destruct H. destruct H.
    inversion H. subst. clear H.
    case_eq (eqb p s); intros; try easy.
    - assert (p = s). apply eqb_eq; easy. subst. apply H3. constructor.
    case_eq (eqb p r); intros; try easy.
    - assert (p = r). apply eqb_eq; easy. subst. apply H3. constructor.
    assert (p <> s). apply eqb_neq; try easy.
    assert (p <> r). apply eqb_neq; try easy.
    assert (ishParts p x1 -> False). 
    {
      intros. apply H3.
      apply ha_sendr with (n := n) (s := x0) (g := x1); try easy.
    }
    assert (exists g', typ_gtth ctxG x1 g' /\ onth n ys0 = Some (x0, g')).
    {
      clear H2 H1 H0 H3 H4 H10 H8 H12 H5 H14 H6 H H7 H9 H15 H16. clear p q r s.
      clear x ys.
      revert H11 H13. revert xs ctxG ys0 x0 x1.
      induction n; intros; try easy.
      - destruct xs; try easy. 
        destruct ys0; try easy.
        inversion H11. simpl in *. subst.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst.
        exists x3; try easy.
      - destruct xs; try easy.
        destruct ys0; try easy.
        apply IHn with (xs := xs) (ys0 := ys0) (x0 := x0); try easy.
        inversion H11. easy.
    }
    destruct H17. 
    specialize(H6 ctxG x2 p q).
    pinversion H2; try easy. subst.
    pinversion H1; try easy. subst. destruct H17.
    assert (exists t t', projectionC x2 p t /\ projectionC x2 q t' /\ onth n ys2 = Some t /\ onth n ys1 = Some t').
    {
      clear H2 H1 H0 H3 H4 H10 H8 H12 H5 H14 H13 H6 H H7 H9 H15 H16 H17 H21 H22 H23 H24. clear H29 H26 H25 H34 H11 H28 H30.
      clear r s x1 x ys xs ctxG.
      revert H18 H27 H33. revert p q x0 x2 ys0 ys1 ys2.
      induction n; intros; try easy.
      - destruct ys0; try easy.
        destruct ys1; try easy.
        destruct ys2; try easy.
        simpl in *.
        inversion H27. subst. inversion H33. subst. clear H27 H33.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. inversion H. subst.
        destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2. inversion H0. subst.
        pclearbot. exists x4. exists x3. easy.
      - destruct ys0; try easy.
        destruct ys1; try easy.
        destruct ys2; try easy.
        simpl in *.
        inversion H27. subst. inversion H33. subst. clear H27 H33.
        apply IHn with (x0 := x0) (ys0 := ys0) (ys1 := ys1) (ys2 := ys2); try easy.
    }
    destruct H19. destruct H19. destruct H19. destruct H20. destruct H31.
    specialize(_a_29_part_helper_recv n ys1 x4 p ys H32 H28); intros. destruct H35. subst.
    specialize(_a_29_part_helper_send n ys2 x3 q x H31 H34); intros. destruct H35. subst.
    specialize(H6 x4 x5). apply H6; try easy.
    apply proj_mon.
    apply proj_mon.
Qed.

    
Lemma _a_29_16 : forall G' ctxG G p q ys x, 
    projectionC G q (ltt_recv p ys) -> 
    Forall
          (fun u : option gtt =>
           u = None \/
           (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
              u = Some g /\
              g = gtt_send p q lsg /\
              Forall2
                (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                 u0 = None /\ v = None \/
                 (exists (s : sort) (t : ltt) (g' : gtt),
                    u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG ->
    usedCtx ctxG G' ->
    (ishParts p G' -> False) ->
    (ishParts q G' -> False) -> 
    typ_gtth ctxG G' G -> 
    Forall
          (fun u : option gtt =>
           u = None \/
           (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
              u = Some g /\
              g = gtt_send p q lsg /\
              Forall2
                (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                 u0 = None /\ v = None \/
                 (exists (s : sort) (t : ltt) (g' : gtt),
                    u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x /\
              Forall2
                (fun u v => (u = None /\ v = None) \/ 
                 (exists s t g', u = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg ys
              )) ctxG.
Proof.
  induction G' using gtth_ind_ref; intros; try easy.
  - inversion H4. subst.
    inversion H1. subst.
    clear H2 H3 H1 H4.
    revert H0 H7 H. revert G p q ys x G0.
    induction n; intros; try easy.
    - simpl in *. inversion H7. subst.
      inversion H0. subst. clear H0 H4.
      destruct H3; try easy. destruct H0 as (g,(lsg,(Ha,(Hb,Hc)))).
      inversion Ha. subst.
      pinversion H; try easy. subst. clear H4.
      constructor; try easy. right. exists (gtt_send p q lsg). exists lsg.
      split. easy. split. easy. split. easy.
      revert H8. apply Forall2_mono; intros.
      destruct H0. left. easy. 
      destruct H0 as (s,(g,(t,(Hd,(He,Hf))))). subst. right. exists s. exists t. exists g.
      destruct Hf; try easy.
    apply proj_mon.
    simpl in *. inversion H0. subst. clear H0.
    specialize(IHn G p q ys x G0 H4).
    constructor. left. easy. apply IHn; try easy.
  - inversion H5. subst. 
    pinversion H0. subst.
    - assert False. apply H3. constructor. easy.
    - subst. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
      clear H14.
      clear H12.
      specialize(ctx_back s s' xs ys0 ctxG H5 H2); intros.
      destruct H6 as (ctxGLis,(H6,H7)).
      assert(Forall (fun u => u = None \/ exists ctxGi, u = Some ctxGi /\
        Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' p t)) lsg x /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' q t)) lsg ys)) ctxGi
      ) ctxGLis).
      {
        apply Forall_forall; intros.
        destruct x0. right.
        specialize(in_some_implies_onth l ctxGLis H8); intros.
        destruct H12 as (n, H12). rename l into ctxGi. exists ctxGi. split. easy.
        clear H8. clear H11 H9 H10 H13 H5 H2.
        assert(exists s g1 g2 t, onth n xs = Some (s, g1) /\ onth n ys0 = Some (s, g2) /\ typ_gtth ctxGi g1 g2 /\ usedCtx ctxGi g1 /\ onth n ys1 = Some t /\ projectionC g2 q t).
        {
          revert H12 H6 H17.
          clear H7 H18 H4 H3 H1 H0 H.
          revert xs q ys0 ys1 ctxGLis ctxGi. clear s s' ctxG p ys x.
          induction n; intros.
          - destruct ctxGLis; try easy. destruct xs; try easy. destruct ys0; try easy.
            destruct ys1; try easy. inversion H6. subst. clear H6.
            inversion H17. subst. clear H17.
            simpl in H12. subst.
            destruct H3; try easy. destruct H as (ctxG,(s1,(g1,(g2,(Ha,(Hb,(Hc,(Hd,He)))))))).
            inversion Ha. subst.
            destruct H2; try easy. destruct H as (s2,(g3,(t1,(Hf,(Hg,Hh))))). inversion Hf. subst.
            simpl. exists s2. exists g1. exists g3. exists t1. destruct Hh; try easy.
          - destruct ctxGLis; try easy. destruct xs; try easy. destruct ys0; try easy.
            destruct ys1; try easy. inversion H6. subst. clear H6.
            inversion H17. subst. clear H17.
            specialize(IHn xs q ys0 ys1 ctxGLis ctxGi). apply IHn; try easy.
        }
        destruct H2 as (s1,(g1,(g2,(t1,(Hta,(Htb,(Htc,(Htd,(Hte,Htf))))))))).
        clear H6 H17.
        specialize(some_onth_implies_In n xs (s1, g1) Hta); intros.
        specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (ctxG : seq.seq (option gtt)) (G : gtt) (p q : string)
             (ys x : seq.seq (option (sort * ltt))),
           projectionC G q (ltt_recv p ys) ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' p t)) lsg x)) ctxG ->
           usedCtx ctxG g ->
           (ishParts p g -> False) ->
           (ishParts q g -> False) ->
           typ_gtth ctxG g G ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' p t)) lsg x /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' q t)) lsg ys)) ctxG)))
      xs); intros.
        destruct H5. specialize(H5 H). clear H H6.
        specialize(H5 (Some (s1, g1)) H2). destruct H5; try easy.
        destruct H as(s2,(g3,(Ha,Hb))). inversion Ha. subst.
        specialize(Hb ctxGi g2 p q ys x).
        apply Hb; try easy.
        - specialize(merge_inv_ss n (ltt_recv p ys) ys1 t1); intros.
          assert(t1 = ltt_recv p ys). apply H; try easy. subst. easy.
        - specialize(mergeCtx_sl n ctxGLis ctxGi ctxG); intros.
          assert(Forall2R (fun u v : option gtt => u = v \/ u = None) ctxGi ctxG). apply H; try easy.
          clear H. clear Hb H2 Htf Hte Hta Htc Htd Ha Htb H12 H7 H18 H4 H3 H0.
          revert H5 H1.
          revert ctxG p q x. clear s s' xs ys ys0 ys1 ctxGLis n g2 t1 s2 g3.
          induction ctxGi; intros; try easy.
          - destruct ctxG; try easy. inversion H1. subst. clear H1. inversion H5. subst. clear H5.
            specialize(IHctxGi ctxG p q x H7 H3). constructor; try easy. clear H7 H3 IHctxGi.
            destruct H4. subst. easy. left. easy.
        - specialize(ishParts_n H3 Hta); try easy.
        - specialize(ishParts_n H4 Hta); try easy.
        left. easy.
      }
      clear H6 H18 H17 H13 H10 H9 H11 H5 H4 H3 H2 H1 H0 H. 
      revert H8 H7. revert ctxG p q ys x. clear s s' xs ys0 ys1.
      induction ctxGLis; intros; try easy.
      - inversion H8. subst. clear H8.
        inversion H7; try easy.
        - subst.
          destruct H1; try easy. destruct H as (ct1,(Ha,Hb)). inversion Ha. subst. easy.
        - subst.
          specialize(IHctxGLis ctxG p q ys x). apply IHctxGLis; try easy.
        - subst.
          specialize(IHctxGLis t p q ys x H2 H5). clear H2 H5.
          clear H7. destruct H1; try easy.
          destruct H as (t1,(Ha,Hb)). inversion Ha. subst. clear Ha.
          revert H4 Hb IHctxGLis. clear ctxGLis. revert p q ys t t1 x. 
          induction ctxG; intros; try easy.
          - inversion H4.
            - subst. easy.
            - subst. easy.
            subst. clear H4. specialize(IHctxG p q ys xa xb x H6).
            inversion Hb. subst. clear Hb. inversion IHctxGLis. subst. clear IHctxGLis.
            specialize(IHctxG H2 H4). constructor; try easy.
            clear H4 H2 H6 IHctxG.
            - destruct H5. destruct H as (Ha,(Hb,Hc)). subst. easy.
            - destruct H. destruct H as (t,(Ha,(Hb,Hc))). subst. easy.
            - destruct H. destruct H as (t,(Ha,(Hb,Hc))). subst. easy.
            - destruct H as (t,(Ha,(Hb,Hc))). subst. easy.
  apply proj_mon.
Qed.


Lemma _a_29_s_helper {A B} : forall (ys : list (option (A * B))),
  exists SI, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g, u = Some s /\ v = Some (s, g))) SI ys.
Proof.
  induction ys; intros; try easy.
  exists nil. easy.
  destruct IHys. destruct a. destruct p. exists (Some a :: x). constructor; try easy.
  right. exists a. exists b. easy.
  exists (None :: x). constructor; try easy. left. easy.
Qed.

Lemma _a_29_s_helper2s : forall n s1 g1 xs ys ys0 ys1 ctxG p q,
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
    onth n xs = Some (s1, g1) -> 
    exists g2 t t',
    onth n ys = Some (s1, g2) /\ typ_gtth ctxG g1 g2 /\
    onth n ys0 = Some t /\ projectionC g2 q t /\
    onth n ys1 = Some t' /\ projectionC g2 p t'.
Proof.
  induction n; intros; try easy.
  - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
    inversion H. inversion H0. inversion H1. subst. clear H H0 H1.
    simpl in H2. subst.
    destruct H6; try easy. destruct H as (s2,(g2,(g3,(Ha,(Hb,Hc))))). inversion Ha. subst.
    destruct H12; try easy. destruct H as (s3,(g4,(t2,(Hd,(He,Hf))))). inversion Hd. subst.
    destruct H18; try easy. destruct H as (s4,(g5,(t3,(Hg,(Hh,Hi))))). inversion Hg. subst.
    pclearbot. simpl. exists g5. exists t2. exists t3. easy.
  - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
    inversion H. inversion H0. inversion H1. subst. clear H H0 H1.
    specialize(IHn s1 g1 xs ys ys0 ys1 ctxG). apply IHn; try easy.
Qed.

Lemma _a_29_s_helper2 : forall G' G p q PT QT ctxG,
  projectionC G p (ltt_send q PT) -> 
  projectionC G q (ltt_recv p QT) -> 
  typ_gtth ctxG G' G -> 
  (ishParts p G' -> False) -> 
  (ishParts q G' -> False) -> 
  Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg)) ctxG -> 
   wfgC G -> 
  List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g'))) PT QT.
Proof.
  induction G' using gtth_ind_ref; intros; try easy. rename H5 into Ht.
  - inversion H1. subst. clear H1.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))), u = Some g /\ g = gtt_send p q lsg))
       ctxG); intros.
    destruct H1. specialize(H1 H4). clear H4 H5.
    specialize(some_onth_implies_In n ctxG G H7); intros.
    specialize(H1 (Some G) H4). destruct H1; try easy.
    destruct H1 as (g,(lsg,(Ha,Hb))). inversion Ha. subst.
    pinversion H; try easy. subst. pinversion H0; try easy. subst.
    clear H13 H15 H14 H9 H11 H10 Ht H7 H3 H2 H H0 Ha H4. clear ctxG n.
    revert H16 H12. revert p q PT QT.
    induction lsg; intros; try easy.
    - destruct QT; try easy. destruct PT; try easy.
    - destruct QT; try easy. destruct PT; try easy.
      inversion H16. subst. clear H16. inversion H12. subst. clear H12.
      specialize(IHlsg p q PT QT H4 H6); intros. constructor; try easy.
      clear H6 H4 IHlsg.
      destruct H2. destruct H3. left. easy.
      destruct H. subst. destruct H0 as (s1,(g1,(t1,(Ha,Hb)))). easy.
      destruct H as (s,(g,(t,(Ha,(Hb,Hc))))). subst.
      destruct H3; try easy.
      destruct H as (s0,(g0,(t0,(Hd,(He,Hf))))). inversion Hd. subst.
      right. exists s0. exists t0. exists t. easy.
    apply proj_mon.
    apply proj_mon.
  - inversion H2. subst.
    rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    pinversion H1; try easy. subst. assert False. apply H3. constructor. easy.
    pinversion H0; try easy. subst.
    assert(List.Forall (fun u => u = None \/ (exists lis, u = Some (ltt_recv p lis))) ys0).
    {
      apply Forall_forall; intros.
      destruct x.
      specialize(in_some_implies_onth l ys0 H7); intros. destruct H8 as (n,H8).
      right.
      specialize(merge_onth_recv n p QT ys0 l H19 H8); intros. destruct H9. exists x. subst. easy.
      left. easy.
    }
    assert(List.Forall (fun u => u = None \/ (exists lis, u = Some (ltt_send q lis))) ys1).
    {
      apply Forall_forall; intros.
      destruct x.
      specialize(in_some_implies_onth l ys1 H8); intros. destruct H9 as (n,H9).
      right.
      specialize(merge_onth_send n q PT ys1 l H30 H9); intros. destruct H16. exists x. subst. easy.
      left. easy.
    }
    assert(List.Forall (fun u => u = None \/ 
      (exists s g PT QT, u = Some(s, g) /\ projectionC g p (ltt_send q PT) /\ projectionC g q (ltt_recv p QT) /\
        Forall2
             (fun u0 v : option (sort * ltt) =>
              u0 = None /\ v = None \/
              (exists (s0 : sort) (g0 g' : ltt), u0 = Some (s0, g0) /\ v = Some (s0, g'))) PT QT
      )) ys).
    {
      clear H30 H19 H12 H1 H0 H2.
      specialize(wfgC_after_step_all H10 H6); intros. clear H25 H24 H23 H14 H11 H10 H6.
      clear H26 H15.
      revert H0 H29 H18 H13 H5 H4 H3 H H7 H8.
      revert s s' xs p q ctxG ys0 ys1. clear PT QT.
      induction ys; intros; try easy.
      - destruct xs; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H0. subst. clear H0. inversion H29. subst. clear H29.
        inversion H18. subst. clear H18. inversion H13. subst. clear H13.
        inversion H. subst. clear H. inversion H7. subst. clear H7. inversion H8. subst. clear H8.
        specialize(IHys s s' xs p q ctxG ys0 ys1).
        assert(Forall
         (fun u : option (sort * gtt) =>
          u = None \/
          (exists (s : sort) (g : gtt) (PT QT : seq.seq (option (sort * ltt))),
             u = Some (s, g) /\
             projectionC g p (ltt_send q PT) /\
             projectionC g q (ltt_recv p QT) /\
             Forall2
               (fun u0 v : option (sort * ltt) =>
                u0 = None /\ v = None \/
                (exists (s0 : sort) (g0 g' : ltt), u0 = Some (s0, g0) /\ v = Some (s0, g'))) PT QT)) ys).
      {
        apply IHys; try easy.
        specialize(ishParts_hxs H4); try easy.
        specialize(ishParts_hxs H3); try easy.
      }
      constructor; try easy.
      clear H H18 H16 H13 H17 H15 H12 H9 IHys.
      destruct H11. left. easy. right.
      destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). subst.
      destruct H14; try easy. destruct H as (s2,(g2,(g3,(Hd,(He,Hf))))). inversion He. subst.
      destruct H6; try easy. destruct H as (s3,(g4,(Hg,Hi))). inversion Hg. subst.
      destruct H1; try easy. destruct H as (lis,Hj). inversion Hj. subst.
      destruct H10; try easy. destruct H as (s5,(g5,(t2,(Hk,(Hl,Hm))))). inversion Hk. subst.
      destruct H7; try easy. destruct H as (lis2,Hn). inversion Hn. subst.
      destruct H2; try easy.
      exists s5. exists g5. exists lis2. exists lis.
      destruct H as (s6,(g6,(Ho,Hp))). inversion Ho. subst. clear Hn Hk He Hg Ho.
      specialize(Hp g5 p q lis2 lis ctxG).
      split. easy. split. destruct Hm; try easy. split. destruct Hc; try easy.
      apply Hp; try easy. destruct Hm; try easy. destruct Hc; try easy.
      specialize(ishParts_x H3); try easy.
      specialize(ishParts_x H4); try easy.
    }
    specialize(wfgC_after_step_all H10 H6); intros.
    clear H25 H24 H23 H14 H11 H10 H13 H12 H6 H5 H4 H3 H0 H1 H2 H H15 H26. clear s s' ctxG.
    assert(List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists lis1 lis2, u = Some (ltt_recv p lis1) /\ v = Some (ltt_send q lis2) /\ 
      List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t'))) lis2 lis1
    )) ys0 ys1).
    {
      clear H30 H19.
      revert H16 H9 H8 H7 H29 H18. revert p q ys0 ys1. clear xs PT QT.
      induction ys; intros.
      - destruct ys0; try easy. destruct ys1; try easy.
      - destruct ys0; try easy. destruct ys1; try easy.
        inversion H16. subst. clear H16. inversion H9. subst. clear H9.
        inversion H8. subst. clear H8. inversion H7. subst. clear H7.
        inversion H29. subst. clear H29. inversion H18. subst. clear H18.
        specialize(IHys p q ys0 ys1).
        assert(Forall2
         (fun u v : option ltt =>
          u = None /\ v = None \/
          (exists lis1 lis2 : seq.seq (option (sort * ltt)),
             u = Some (ltt_recv p lis1) /\
             v = Some (ltt_send q lis2) /\
             Forall2
               (fun u0 v0 : option (sort * ltt) =>
                u0 = None /\ v0 = None \/
                (exists (s : sort) (t t' : ltt), u0 = Some (s, t) /\ v0 = Some (s, t'))) lis2 lis1)) ys0
         ys1).
      apply IHys; try easy. constructor; try easy.
      clear IHys H2 H4 H6 H9 H12 H14 H.
      - destruct H10. destruct H. subst.
        destruct H11. left. easy.
        destruct H as(s,(g,(t,(Ha,(Hb,Hc))))). easy.
      - destruct H as (s,(g,(t,(Ha,(Hb,Hc))))). subst.
        destruct H11; try easy. destruct H as (s1,(g1,(t1,(Hd,(He,Hf))))). inversion Hd. subst.
        destruct H5; try easy. destruct H as (lis,Hg). inversion Hg. subst.
        destruct H8; try easy. destruct H as (lis2,Hh). inversion Hh. subst.
        destruct H1; try easy. destruct H as (s2,(g2,(Hi,Hj))). inversion Hi. subst.
        destruct H3; try easy. destruct H as (s3,(g3,(PT,(QT,(Hk,(Hl,(Hm,Hn))))))). inversion Hk. subst.
        pclearbot.
        specialize(proj_inj Hj Hc Hl); intros. inversion H. subst.
        specialize(proj_inj Hj Hf Hm); intros. inversion H0. subst.
        clear Hg Hh Hc Hf H H0.
        right. exists QT. exists PT. split. easy. split. easy. easy.
    }
    clear H16 H9 H29 H18 H7 H8.
    clear ys.
    
    specialize(merge_sorts ys0 ys1 p q PT QT); intros. apply H0; try easy.
  apply proj_mon.
  apply proj_mon.
Qed.

Lemma _a_29_helper2 : forall lsg SI x p,
      Forall2
        (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
         u0 = None /\ v = None \/
         (exists (s : sort) (t : ltt) (g' : gtt),
            u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x ->
      Forall2
        (fun (u : option sort) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (t : ltt), u = Some s /\ v = Some (s, t))) SI x ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option sort) =>
         u = None /\ v = None \/
         (exists (s : sort) (g' : gtt), u = Some (s, g') /\ v = Some s)) lsg SI.
Proof.
  induction lsg; intros; try easy.
  - destruct x; try easy.
    destruct SI; try easy.
  - destruct x; try easy.
    destruct SI; try easy.
    inversion H0. subst. clear H0. inversion H. subst. clear H.
    constructor.
    - destruct H4. left. destruct H. subst. destruct H3; try easy. destruct H. destruct H. destruct H.
      destruct H. destruct H0. easy.
    - destruct H. destruct H. destruct H. subst.
      destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H0. subst. right.
      exists x2. exists x4. split; try easy.
  - apply IHlsg with (x := x) (p := p); try easy.
Qed.

Lemma _a_29_helper3 : forall n lsg x0 Sk ys q,
    onth n lsg = Some(Sk, x0) -> 
    Forall2
          (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
           u0 = None /\ v = None \/
           (exists (s : sort) (t : ltt) (g' : gtt),
              u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg ys ->
    exists Tq, onth n ys = Some(Sk, Tq) /\ projectionC x0 q Tq.
Proof.
  induction n; intros; try easy.
  - destruct lsg; try easy.
    destruct ys; try easy. simpl in *.
    inversion H0. subst. destruct H4; try easy. 
    destruct H. destruct H. destruct H. destruct H. destruct H1. inversion H. subst.
    exists x1. split; try easy.
  - destruct lsg; try easy.
    destruct ys; try easy. simpl in *.
    inversion H0. subst.
    apply IHn with (lsg := lsg); try easy.
Qed.


Lemma _a_29_s : forall G p q PT QT S T S' T' n, 
    wfgC G -> 
    projectionC G p (ltt_send q PT) -> 
    onth n PT = Some(S, T) ->
    projectionC G q (ltt_recv p QT) -> 
    onth n QT = Some (S', T') ->
    exists G' ctxG SI Sn, 
    typ_gtth ctxG G' G /\ (* 1 *)
    (ishParts p G' -> False) /\ (ishParts q G' -> False) /\ (* 2 *)
    List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg /\
      (exists s' Gjk Tp Tq, onth n lsg = Some (s', Gjk) /\ projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
      List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g', u = Some(s, g') /\ v = Some s)) lsg SI
    )) ctxG /\ (* 3 5 6 *)
    (onth n SI = Some Sn) /\ subsort S Sn /\ subsort Sn S'. (* 5 6 *)
Proof.
  intros.
  specialize(_a_29_11 G p q PT H H0); intros.
  destruct H4 as (G',(ctxG,(Ha,(Hb,(Hc,Hd))))). 
  exists G'. exists ctxG.
  specialize(_a_29_part ctxG G' G p q PT QT Ha H0 H2 Hb); intros.
  specialize(_a_29_16 G' ctxG G p q QT PT H2 Hc Hd Hb H4 Ha); intros. clear Hc.
  specialize(_a_29_s_helper PT); intros. destruct H6 as (SI, H6).
  exists SI. exists S. split. easy. split. easy. split. easy.
  specialize(_a_29_s_helper2 G' G p q PT QT ctxG); intros.
  assert(Forall2
       (fun u v : option (sort * ltt) =>
        u = None /\ v = None \/ (exists (s : sort) (g g' : ltt), u = Some (s, g) /\ v = Some (s, g')))
       PT QT).
  {
    apply H7; try easy.
    apply Forall_forall; intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg PT /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg QT)) ctxG); intros.
    destruct H9. specialize(H9 H5). clear H5 H10.
    specialize(H9 x H8). destruct H9. left. easy.
    destruct H5 as (g,(lsg,(Hta,(Htb,Htc)))). subst. right. exists (gtt_send p q lsg).
    exists lsg. easy.
  }
  clear H7.
  split.
  
  apply Forall_forall; intros.
  specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg PT /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg QT)) ctxG); intros.
  destruct H9. specialize(H9 H5). clear H5 H10. specialize(H9 x H7).
  destruct H9. left. easy. destruct H5 as (g,(lsg,(Hta,(Htb,(Htc,Htd))))).
  subst. right. exists (gtt_send p q lsg). exists lsg.
  split. easy. split. easy.
  split.
  {
    clear H7 H8 H6 H4 Hb Ha H2 H0 H Hd. 
    clear G G' ctxG SI. revert Htd Htc. revert lsg H3 H1. 
    revert p q PT QT S T S' T'.
    induction n; intros; try easy.
    - destruct PT; try easy. destruct QT; try easy. destruct lsg; try easy.
      inversion Htd. subst. clear Htd. inversion Htc. subst. clear Htc.
      simpl in *. subst.
      destruct H4; try easy. destruct H as (s1,(t1,(g1,(Ha,(Hb,Hc))))). inversion Hb. subst.
      destruct H5; try easy. destruct H as (s2,(t2,(g2,(Hd,(He,Hf))))). inversion Hd. inversion He. subst.
      exists s2. exists g2. exists t2. exists t1. easy.
    - destruct PT; try easy. destruct QT; try easy. destruct lsg; try easy.
      inversion Htd. subst. clear Htd. inversion Htc. subst. clear Htc.
      specialize(IHn p q PT QT S T S' T' lsg). apply IHn; try easy.
  }
  - specialize(_a_29_helper2 lsg SI PT p); intros. apply H5; try easy.
    clear H5 H4 Hb Ha H2 H0 Hd. clear G' H ctxG p q.
    revert H8 H6 H3 H1. revert SI T' S' T S PT QT G.
    induction n; intros; try easy.
    - destruct QT; try easy. destruct PT; try easy. destruct SI; try easy.
      inversion H6. subst. clear H6. inversion H8. subst. clear H8.
      simpl in H3. simpl in H1. subst.
      destruct H4; try easy. destruct H as (s1,(g1,(Ha,Hb))). inversion Hb. subst.
      destruct H5; try easy. destruct H as (s2,(g2,(g3,(Hc,Hd)))). inversion Hc. inversion Hd. subst.
      simpl. split. easy. split. apply srefl. apply srefl.
    - destruct QT; try easy. destruct PT; try easy. destruct SI; try easy.
      inversion H6. subst. clear H6. inversion H8. subst. clear H8.
      specialize(IHn SI T' S' T S PT QT). apply IHn; try easy.
Qed.

