From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header type.global type.local type.isomorphism type.merge type.decidability.
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


Inductive isMergeCtx : list (option gtt) -> list (option (list (option gtt))) -> Prop :=   
  | cmatm : forall t, isMergeCtx t (Some t :: nil)
  | cmconsn : forall t xs, isMergeCtx t xs -> isMergeCtx t (None :: xs) 
  | cmconss : forall t t' t'' xs, 
      Forall3S (fun u v w => 
        (u = None /\ v = None /\ w = None) \/
        (exists t, u = None /\ v = Some t /\ w = Some t) \/
        (exists t, u = Some t /\ v = None /\ w = Some t) \/
        (exists t, u = Some t /\ v = Some t /\ w = Some t)
      ) t t' t'' ->
      isMergeCtx t xs -> isMergeCtx t'' (Some t' :: xs). 


Inductive Forall3 {A B C} : (A -> B -> C -> Prop) -> list A -> list B -> list C -> Prop := 
  | Forall3_nil : forall P, Forall3 P nil nil nil
  | Forall3_cons : forall P a b c xa xb xc, P a b c -> Forall3 P xa xb xc -> Forall3 P (a :: xa) (b :: xb) (c :: xc).

Inductive usedCtx : (list (option gtt)) -> gtth -> Prop := 
  | used_hol : forall n G, usedCtx (extendLis n (Some G)) (gtth_hol n)
  | used_con : forall ctxG ctxGLis p q ys, isMergeCtx ctxG ctxGLis -> 
        List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists ctxGi s g, u = Some ctxGi /\ v = Some (s, g) /\ usedCtx ctxGi g)) ctxGLis ys -> usedCtx ctxG (gtth_send p q ys).

Lemma Forall3S_to_Forall2_r : forall ctxG0 ctxG1 ctxG,
    Forall3S
       (fun u v w : option gtt =>
        u = None /\ v = None /\ w = None \/
        (exists t : gtt, u = None /\ v = Some t /\ w = Some t) \/
        (exists t : gtt, u = Some t /\ v = None /\ w = Some t) \/
        (exists t : gtt, u = Some t /\ v = Some t /\ w = Some t)) ctxG0 ctxG1 ctxG -> 
    Forall2R 
        (fun u v => (u = None \/ u = v)) ctxG1 ctxG.
Proof.
  induction ctxG0; intros.
  inversion H. subst.
  - clear H. induction ctxG; intros; try easy. constructor; try easy. right. right. easy. easy.
  - subst. constructor.
  - inversion H.
    - subst. specialize(IHctxG0 nil ctxG0). constructor.
    - subst. clear H.
      specialize(IHctxG0 xb xc H6). constructor; try easy.
      clear H6 IHctxG0.
      destruct H3. destruct H as (Ha,(Hb,Hc)). subst. left. easy.
      destruct H. destruct H as (t,(Ha,(Hb,Hc))). subst. right. easy.
      destruct H. destruct H as (t,(Ha,(Hb,Hc))). subst. left. easy.
      destruct H as (t,(Ha,(Hb,Hc))). subst. right. easy.
Qed.

Lemma Forall3S_to_Forall2_l : forall ctxG0 ctxG1 ctxG,
    Forall3S
       (fun u v w : option gtt =>
        u = None /\ v = None /\ w = None \/
        (exists t : gtt, u = None /\ v = Some t /\ w = Some t) \/
        (exists t : gtt, u = Some t /\ v = None /\ w = Some t) \/
        (exists t : gtt, u = Some t /\ v = Some t /\ w = Some t)) ctxG0 ctxG1 ctxG -> 
    Forall2R 
        (fun u v => (u = None \/ u = v)) ctxG0 ctxG.
Proof.
  induction ctxG0; intros.
  inversion H. subst. constructor. constructor.
  - inversion H.
    - subst. constructor. right. easy. specialize(IHctxG0 nil ctxG0). apply IHctxG0. constructor.
    - subst. clear H.
      specialize(IHctxG0 xb xc H6). constructor; try easy.
      clear H6 IHctxG0.
      destruct H3. destruct H as (Ha,(Hb,Hc)). subst. left. easy.
      destruct H. destruct H as (t,(Ha,(Hb,Hc))). subst. left. easy.
      destruct H. destruct H as (t,(Ha,(Hb,Hc))). subst. right. easy.
      destruct H as (t,(Ha,(Hb,Hc))). subst. right. easy.
Qed.

Lemma mergeCtx_to_2R : forall ctxGLis ctxG,
    isMergeCtx ctxG ctxGLis -> 
    Forall (fun u => u = None \/ (exists ctxGi, u = Some ctxGi /\
      Forall2R (fun u v => (u = None \/ u = v)) ctxGi ctxG
    )) ctxGLis.
Proof.
  induction ctxGLis; intros; try easy.
  inversion H.
  - subst. constructor; try easy. right. exists ctxG.
    split. easy. clear H IHctxGLis. induction ctxG; intros.
    constructor. constructor; try easy. right. easy.
  - subst. specialize(IHctxGLis ctxG H2). constructor; try easy. left. easy.
  - subst.
    specialize(IHctxGLis t H4). clear H.
    constructor.
    - right. exists t'. split. easy.
      clear H4 IHctxGLis.
      apply Forall3S_to_Forall2_r with (ctxG0 := t); try easy.
      revert IHctxGLis. apply Forall_mono; intros.
      destruct H. left. easy.
      destruct H as (ctxGi,(Ha,Hb)). subst. right. exists ctxGi. split. easy.
      specialize(Forall3S_to_Forall2_l t t' ctxG H3); intros.
      clear H3 H4. clear ctxGLis t'.
      revert Hb H. revert t ctxG.
      induction ctxGi; intros; try easy.
      - constructor.
      - destruct t; try easy. destruct ctxG; try easy.
        inversion Hb. subst. clear Hb. inversion H. subst. clear H.
        specialize(IHctxGi t ctxG H5 H7). constructor; try easy.
        clear H5 H7.
        destruct H3. left. easy.
        subst. destruct H4. left. easy. subst. right. easy.
Qed.


Fixpoint noneLis {A} (n : fin) : list (option A) := 
  match n with 
    | 0 => nil 
    | S m => None :: noneLis m
  end.

Lemma typh_with_more : forall gl ctxJ ctxG g3,
            typ_gtth ctxJ gl g3 -> 
            Forall2R (fun u v : option gtt => u = None \/ u = v) ctxJ ctxG -> 
            typ_gtth ctxG gl g3.
Proof.
  induction gl using gtth_ind_ref; intros.
  - inversion H. subst. constructor.
    clear H. revert H3 H0. revert ctxG ctxJ. induction n; intros.
    - destruct ctxJ; try easy. destruct ctxG; try easy.
      inversion H0. subst. clear H0.
      simpl in H3. subst. destruct H4; try easy. 
    - destruct ctxJ; try easy. destruct ctxG; try easy.
      inversion H0. subst. clear H0.
      specialize(IHn ctxG ctxJ). apply IHn; try easy.
  - inversion H0. subst. constructor; try easy.
    clear H7 H0. revert H8 H1 H.
    revert xs ctxJ ctxG. clear p q.
    induction ys; intros.
    - destruct xs; try easy.
    - destruct xs; try easy. inversion H. subst. clear H. inversion H8. subst. clear H8.
      specialize(IHys xs ctxJ ctxG H7 H1 H4). constructor; try easy. clear H7 H4 IHys.
      destruct H5. left. easy.
      destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
      destruct H3; try easy. destruct H as (s2,(g3,(Hd,He))). inversion Hd. subst.
      right. exists s2. exists g3. exists g2. split. easy. split. easy.
      specialize(He ctxJ ctxG g2). apply He; try easy.
Qed.

Lemma typ_gtth_pad_l : forall Gl' g1 ctxJ ctxG,
    typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) Gl' g1 -> 
    typ_gtth (ctxJ ++ ctxG)%list Gl' g1.
Proof.
  intros.
  specialize(typh_with_more Gl' (noneLis (Datatypes.length ctxJ) ++ ctxG) (ctxJ ++ ctxG) g1); intros. apply H0; try easy.
  clear H0 H. induction ctxJ; intros; try easy.
  - simpl. induction ctxG; intros; try easy. constructor. constructor; try easy. right. easy.
  - constructor; try easy. left. easy.
Qed.

Lemma typ_gtth_pad_r : forall g2 g3 ctxJ ctxG,
        typ_gtth ctxJ g2 g3 -> 
        typ_gtth (ctxJ ++ ctxG)%list g2 g3.
Proof.
  intros.
  specialize(typh_with_more g2 ctxJ (ctxJ ++ ctxG) g3); intros.
  apply H0; try easy.
  clear H0 H. induction ctxJ; intros; try easy. constructor.
  constructor; try easy. right. easy.
Qed.

Lemma typh_with_less : forall ctxGi' ctxG g4 g3,
            typ_gtth ctxG g4 g3 -> 
            Forall2R (fun u v : option gtt => u = None \/ u = v) ctxGi' ctxG -> 
            usedCtx ctxGi' g4 -> 
            typ_gtth ctxGi' g4 g3.
Proof.
  intros. revert H H0 H1. revert g3 ctxGi' ctxG.
  induction g4 using gtth_ind_ref; intros.
  - inversion H. subst. constructor; try easy. 
    inversion H1. subst.
    clear H1 H. revert H4 H0. revert g3 ctxG G. induction n; intros; try easy.
    - destruct ctxG; try easy. simpl in H4. subst.
      inversion H0. subst. simpl. destruct H3; try easy.
    - destruct ctxG; try easy. inversion H0. subst. 
      apply IHn with (ctxG := ctxG); try easy.
  - inversion H0. subst.
    constructor; try easy. 
    inversion H2. subst.
    specialize(mergeCtx_to_2R ctxGLis ctxGi' H6); intros. clear H6 H8 H2 H0.
    revert H3 H10 H9 H1 H. revert ctxGi' ctxG ys ctxGLis. clear p q.
    induction xs; intros; try easy.
    - destruct ys; try easy.
    - destruct ys; try easy. destruct ctxGLis; try easy.
      inversion H. subst. clear H. inversion H9. subst. clear H9.
      inversion H3. subst. clear H3. inversion H10. subst. clear H10.
      specialize(IHxs ctxGi' ctxG ys ctxGLis).
      assert(Forall2
         (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
          u = None /\ v = None \/
          (exists (s : sort) (g : gtth) (g' : gtt),
             u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxGi' g g')) xs ys).
      apply IHxs; try easy. constructor; try easy.
      clear H H12 H7 H8 H5 IHxs.
      destruct H6. left. easy.
      destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
      destruct H4; try easy. destruct H as (s2,(g3,(Hd,He))). inversion Hd. subst.
      destruct H9; try easy. destruct H as (ct,(s3,(g4,(Hf,(Hg,Hh))))). inversion Hg. subst.
      destruct H2; try easy. destruct H as (ct2,(Hi,Hj)). inversion Hi. subst.
      right. exists s3. exists g4. exists g2.
      split. easy. split. easy.
      specialize(He g2 ct2 ctxG).
      assert(typ_gtth ct2 g4 g2).
      {
        apply He; try easy.
        clear Hh Hi Hc Hd He Hg. 
        revert Hj H1. revert ctxGi' ctxG.
        induction ct2; intros; try easy.
        - constructor.
        - destruct ctxGi'; try easy. destruct ctxG; try easy.
          inversion Hj. subst. clear Hj. inversion H1. subst. clear H1.
          specialize(IHct2 ctxGi' ctxG H5 H7). constructor; try easy.
          destruct H3. left. easy. subst. destruct H4. left. easy. subst. right. easy.
      }
      apply typh_with_more with (ctxJ := ct2); try easy.
Qed.

Lemma typh_with_more2 {A} : forall ctxGi' ctxG (ctxJ : list A) gl g3,
            typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxGi') gl g3 -> 
            Forall2R (fun u v : option gtt => u = None \/ u = v) ctxGi' ctxG -> 
            typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) gl g3.
Proof.
  intros.
  apply typh_with_more with (ctxJ := (noneLis (Datatypes.length ctxJ) ++ ctxGi')); try easy.
  clear H.
  induction ctxJ; intros; try easy.
  constructor; try easy. left. easy.
Qed.

Lemma ctx_back : forall s s' xs ys0 ctxG,
      typ_gtth ctxG (gtth_send s s' xs) (gtt_send s s' ys0) -> 
      usedCtx ctxG (gtth_send s s' xs) -> 
      exists ctxGLis, 
      Forall3 (fun u v w => (u = None /\ v = None /\ w = None) \/ (exists ct s g g', u = Some ct /\ v = Some(s, g) /\ w = Some(s, g') /\ typ_gtth ct g g' /\ usedCtx ct g)) ctxGLis xs ys0 /\
      isMergeCtx ctxG ctxGLis.
Proof.
  intros.
  inversion H. subst. clear H.
  inversion H0. subst. clear H0.
  clear H4. clear s s'.
  specialize(mergeCtx_to_2R ctxGLis ctxG H3); intros. 
  exists ctxGLis. split; try easy. clear H3.
  revert H7 H6 H. revert ys0 ctxG ctxGLis.
  induction xs; intros.
  - destruct ys0; try easy. destruct ctxGLis; try easy. constructor.
  - destruct ys0; try easy. destruct ctxGLis; try easy.
    inversion H7. subst. clear H7. inversion H6. subst. clear H6.
    inversion H. subst. clear H.
    specialize(IHxs ys0 ctxG ctxGLis H5 H8 H6). constructor; try easy.
    clear H6 H8 H5 IHxs.
    - destruct H4. destruct H. subst. destruct H3. destruct H. subst. left. easy.
      destruct H as (s1,(g1,(g2,Ha))). easy.
    - destruct H as (ct,(s1,(g1,(Ha,(Hb,Hc))))). subst.
      destruct H3; try easy. destruct H as (s2,(g2,(g3,(Hd,(He,Hf))))). inversion Hd. subst.
      destruct H2; try easy. destruct H as (ct2,(Hg,Hh)). inversion Hg. subst.
      right. exists ct2. exists s2. exists g2. exists g3.
      split. easy. split. easy. split. easy. split; try easy.
      apply typh_with_less with (ctxG := ctxG); try easy.
Qed.

Lemma mergeCtx_sl : forall n ctxGLis ctxGi ctxG,
        onth n ctxGLis = Some ctxGi -> 
        isMergeCtx ctxG ctxGLis -> 
        Forall2R (fun u v => u = v \/ u = None) ctxGi ctxG.
Proof.
  induction n; intros.
  - destruct ctxGLis; try easy. 
    simpl in H. subst.
    inversion H0. subst. 
    - clear H0. induction ctxGi; intros; try easy. constructor.
      constructor; try easy. left. easy.
    - subst.
      clear H4 H0. clear ctxGLis.
      revert H3. revert ctxG t. induction ctxGi; intros; try easy.
      - constructor.
      - inversion H3; try easy.
        - subst. clear H3 IHctxGi. constructor. left. easy. clear a.
          induction ctxGi; intros; try easy. constructor. constructor; try easy. left. easy.
        - subst. specialize(IHctxGi xc xa H6). constructor; try easy.
          clear H3 H6. 
          - destruct H4. destruct H as (Ha,(Hb,Hc)). subst. left. easy.
          - destruct H. destruct H as (t1,(Ha,(Hb,Hc))). subst. left. easy.
          - destruct H. destruct H as (t1,(Ha,(Hb,Hc))). subst. right. easy.
          - destruct H as (t1,(Ha,(Hb,Hc))). subst. left. easy.
  - destruct ctxGLis; try easy.
    inversion H0; try easy.
    - subst. destruct n; try easy.
    - subst. specialize(IHn ctxGLis ctxGi ctxG). apply IHn; try easy.
    - subst. specialize(IHn ctxGLis ctxGi t H H5).
      clear H0 H H5.
      clear ctxGLis n.
      revert H4 IHn. revert t ctxG t'.
      induction ctxGi; intros; try easy.
      - constructor.
      - inversion H4. 
        - subst. inversion IHn; try easy.
        - subst. destruct ctxG; try easy.
        - subst. clear H4.
          inversion IHn. subst. clear IHn.
          specialize(IHctxGi xa xc xb H0 H6). constructor; try easy.
          clear IHctxGi H0 H6.
          destruct H4. subst.
          - destruct H. destruct H as (Ha,(Hb,Hc)). subst. left. easy.
          - destruct H. destruct H as (t1,(Ha,(Hb,Hc))). subst. right. easy.
          - destruct H. destruct H as (t1,(Ha,(Hb,Hc))). subst. left. easy.
          - destruct H as (t1,(Ha,(Hb,Hc))). subst. left. easy.
          subst. right. easy.
Qed.


Lemma parts_to_word : forall p G, isgPartsC p G -> exists w r, (gttmap G w None (gnode_pq r p) \/ gttmap G w None (gnode_pq p r)).
Proof.
  intros.
  unfold isgPartsC in H.
  destruct H as (Gl,(Ha,(Hb,Hc))).
  specialize(isgParts_depth_exists p Gl Hc); intros.
  destruct H as (n, H).
  clear Hc Hb.
  revert H Ha. revert Gl G p.
  induction n; intros; try easy.
  - inversion H. subst.
    exists nil. exists q. right. pinversion Ha. subst. constructor.
    apply gttT_mon.
  - subst.
    exists nil. exists p0. left. pinversion Ha. subst. constructor.
    apply gttT_mon.
  - inversion H. subst.
    pinversion Ha. subst.
    specialize(subst_parts_depth 0 0 n p g g Q H2 H1); intros.
    specialize(IHn Q G p). apply IHn; try easy.
    apply gttT_mon.
  - subst.
    pinversion Ha. subst.
    assert(exists gl, onth k ys = Some(s, gl) /\ gttTC g gl).
    {
      clear H4 H2 H1 H Ha IHn.
      revert H8 H3. revert lis ys s g.
      induction k; intros; try easy.
      - destruct lis; try easy.
        destruct ys; try easy.
        inversion H8. subst. clear H8.
        simpl in H3. subst. 
        destruct H2; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
        exists g2. destruct Hc; try easy.
      - destruct lis; try easy.
        destruct ys; try easy.
        inversion H8. subst. clear H8.
        specialize(IHk lis ys s g). apply IHk; try easy.
    }
    destruct H0 as (gl,(Hb,Hc)).
    specialize(IHn g gl p H4 Hc).
    destruct IHn as (w,(r,Hd)).
    exists (k :: w). exists r.
    destruct Hd.
    - left. apply gmap_con with (st := s) (gk := gl); try easy.
    - right. apply gmap_con with (st := s) (gk := gl); try easy.
    apply gttT_mon.
Qed.


Lemma balanced_cont : forall [lsg p q],
    balancedG (gtt_send p q lsg) -> List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ balancedG g)) lsg.
Proof.
  intros. 
  apply Forall_forall; intros.
  destruct x.
  - right. destruct p0. exists s. exists g. split. easy.
    specialize(in_some_implies_onth (s, g) lsg H0); intros.
    destruct H1 as (n, H1). clear H0.
    unfold balancedG. 
    intros.
    unfold balancedG in H.
    specialize(H (n :: w) w' p0 q0 gn).
    assert(gttmap (gtt_send p q lsg) (n :: w) None gn).
    {
      apply gmap_con with (st := s) (gk := g); try easy.
    }
    assert(gttmap (gtt_send p q lsg) ((n :: w) ++ w') None (gnode_pq p0 q0) \/
    gttmap (gtt_send p q lsg) ((n :: w) ++ w') None (gnode_pq q0 p0)).
    {
      destruct H2. left.
      apply gmap_con with (st := s) (gk := g); try easy.
      right.
      apply gmap_con with (st := s) (gk := g); try easy.
    }
    specialize(H H3 H4).
    destruct H as (k, H). exists k.
    intros. specialize(H w'0).
    assert(gttmap (gtt_send p q lsg) ((n :: w) ++ w'0) None gnode_end \/
    Datatypes.length w'0 = k /\ (exists tc : gnode, gttmap (gtt_send p q lsg) ((n :: w) ++ w'0) None tc)).
    {
      destruct H5. left.
      apply gmap_con with (st := s) (gk := g); try easy.
      right.
      destruct H5. split. easy.
      destruct H6. exists x.
      apply gmap_con with (st := s) (gk := g); try easy.
    }
    specialize(H H6).
    destruct H as (w2,(w0,(H,Ha))).
    destruct Ha as (r,Ha).
    exists w2. exists w0. split. easy. exists r. 
    {
      destruct Ha. left.
      inversion H7; try easy. subst. 
      specialize(eq_trans (esym H1) H15); intros. inversion H. subst. easy.
      right.
      inversion H7; try easy. subst.
      specialize(eq_trans (esym H1) H15); intros. inversion H. subst. easy.
    }
    left. easy.
Qed.

Lemma Forall2_prop_r {A B} : forall l (xs : list (option A)) (ys : list (option B)) p P,
      onth l xs = Some p ->
      Forall2 P xs ys ->
      exists p', onth l ys = p' /\ P (Some p) p'.
Proof.
  induction l; intros.
  - destruct xs; try easy.
    destruct ys; try easy.
    inversion H0. subst. clear H0. 
    simpl in H. subst. exists o0. easy.
  - destruct xs; try easy.
    destruct ys; try easy.
    inversion H0. subst. clear H0. 
    specialize(IHl xs ys p P). apply IHl; try easy.
Qed.

Lemma Forall2_prop_l {A B} : forall l (xs : list (option A)) (ys : list (option B)) p P,
      onth l ys = Some p ->
      Forall2 P xs ys ->
      exists p', onth l xs = p' /\ P p' (Some p).
Proof.
  induction l; intros.
  - destruct xs; try easy.
    destruct ys; try easy.
    inversion H0. subst. clear H0. 
    simpl in H. subst. exists o. easy.
  - destruct xs; try easy.
    destruct ys; try easy.
    inversion H0. subst. clear H0. 
    specialize(IHl xs l' p P). apply IHl; try easy.
Qed.

Lemma Forall_prop {A} : forall l (xs : list (option A)) p P, 
      onth l xs = Some p ->
      Forall P xs -> 
      P (Some p).
Proof.
  intros.
  specialize(Forall_forall P xs); intros.
  destruct H1. specialize(H1 H0). 
  clear H2. specialize(some_onth_implies_In l xs p H); intros.
  specialize(H1 (Some p) H2); intros. easy.
Qed.

Lemma wfgC_after_step_all : forall [ys s s'],
    s <> s' -> wfgC (gtt_send s s' ys) -> List.Forall (fun u => u = None \/ (exists st g, u = Some(st, g) /\ wfgC g)) ys.
Proof.
  intros. apply Forall_forall; intros.
  destruct x. 
  - specialize(in_some_implies_onth p ys H1); intros.
    destruct H2. rename x into l. clear H1. 
    right. destruct p. exists s0. exists g. split. easy.
    unfold wfgC in *.
    destruct H0 as (Gl,(Ha,(Hb,(Hc,Hd)))).
    pinversion Ha; try easy.
    - subst.
      specialize(Forall2_prop_l l xs ys (s0, g) (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : global) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) H2 H3); intros.
      destruct H0 as (p',(He,Hf)). 
      destruct p'. destruct Hf; try easy.
      destruct H0 as (s1,(g1,(g2,(Hf,(Hg,Hh))))). inversion Hf. inversion Hg. subst.
      exists g1. pclearbot.
      - split. easy.
      - inversion Hb. subst.
        specialize(Forall_prop l xs (s1, g1) (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ wfG g)) He H7); intros.
        simpl in H0. destruct H0; try easy. destruct H0 as (s2,(g3,(Hi,Hj))).
        inversion Hi. subst.
        split. easy.
      - specialize(guard_cont Hc); intros.
        specialize(Forall_prop l xs (s2, g3) (fun u : option (sort * global) =>
        u = None \/
        (exists (s : sort) (g : global),
           u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) He H0); intros.
        simpl in H1. destruct H1; try easy. destruct H1 as (s3,(g4,(Hk,Hl))).
        inversion Hk. subst. split. easy.
      - specialize(balanced_cont Hd); intros.
        specialize(Forall_prop l ys (s3, g2) (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) H2 H1); intros.
        simpl in H4. destruct H4; try easy. destruct H4 as (s4,(g5,(Hm,Hn))).
        inversion Hm. subst. easy.
      - destruct Hf; try easy. destruct H0 as (s1,(g1,(g2,Hf))). easy.
    - subst.
      clear H0 H1. clear Q.
      specialize(guard_breakG G Hc); intros.
      destruct H0 as (T,(Hte,(Htf,Htg))).
      specialize(gttTC_after_subst (g_rec G) T (gtt_send s s' ys)); intros.
      assert(gttTC T (gtt_send s s' ys)). apply H0; try easy. pfold. easy.
      destruct Htg. subst. pinversion H1; try easy. apply gttT_mon.
      destruct H3 as (p1,(q1,(lis,Htg))). subst. 
      pinversion H1; try easy. subst. clear H0.
      specialize(wfG_after_beta (g_rec G) (g_send s s' lis) Hb Hte); intros.
      clear Hc Hb Ha Hte.
      specialize(Forall2_prop_l l lis ys (s0, g) (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : global) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) H2 H4); intros.
      destruct H3 as (p',(He,Hf)). 
      destruct p'. destruct Hf; try easy.
      destruct H3 as (s1,(g1,(g2,(Hf,(Hg,Hh))))). inversion Hf. inversion Hg. subst.
      exists g1. pclearbot.
      - split. easy.
      - inversion H0. subst.
        specialize(Forall_prop l lis (s1, g1) (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ wfG g)) He H9); intros.
        simpl in H3. destruct H3; try easy. destruct H3 as (s2,(g3,(Hi,Hj))).
        inversion Hi. subst.
        split. easy.
      - specialize(guard_cont Htf); intros.
        specialize(Forall_prop l lis (s2, g3) (fun u : option (sort * global) =>
        u = None \/
        (exists (s : sort) (g : global),
           u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) He H3); intros.
        simpl in H5. destruct H5; try easy. destruct H5 as (s3,(g4,(Hk,Hl))).
        inversion Hk. subst. split. easy.
      - specialize(balanced_cont Hd); intros.
        specialize(Forall_prop l ys (s3, g2) (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) H2 H5); intros.
        simpl in H6. destruct H6; try easy. destruct H6 as (s4,(g5,(Hm,Hn))).
        inversion Hm. subst. easy.
      - destruct Hf; try easy. destruct H3 as (s1,(g1,(g2,Hf))). easy.
    apply gttT_mon. apply gttT_mon.
  - left. easy.
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


Lemma wfgC_triv : forall s s0 l, wfgC (gtt_send s s0 l) -> s <> s0 /\ SList l.
Proof.
  intros.
  unfold wfgC in H.
  destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))).
  specialize(guard_breakG_s2 (gtt_send s s0 l) Gl Hc Hb Ha); intros.
  clear Ha Hb Hc Hd. clear Gl.
  destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))).
  destruct Ha.
  - subst. pinversion Hd; try easy. apply gttT_mon.
  - destruct H as (p1,(q1,(lis,Ha))). subst.
    pinversion Hd; try easy. subst. clear Hd Hb.
    inversion Hc. subst. split. easy.
    clear H4 H5 Hc.
    revert H3 H0. revert lis. clear s s0.
    induction l; intros; try easy.
    - destruct lis; try easy.
    - destruct lis; try easy.
      inversion H0. subst. clear H0.
      specialize(SList_f o lis H3); intros. clear H3.
      destruct H.
      - apply SList_b. specialize(IHl lis). apply IHl; try easy.
      - destruct H as (H,(a1,H1)). subst.
        destruct H4; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
        destruct l; try easy.
    apply gttT_mon.
Qed.



Lemma shift_to : forall (g1 : gtt) (p : string) (Gl : gtth) (ctxG ctxJ : seq.seq (option gtt)),
typ_gtth ctxG Gl g1 ->
(ishParts p Gl -> False) ->
usedCtx ctxG Gl ->
exists Gl' : gtth,
  typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) Gl' g1 /\
  usedCtx (noneLis (Datatypes.length ctxJ) ++ ctxG) Gl' /\ (ishParts p Gl' -> False).
Proof.
  intros g1 p Gl. revert g1 p.
  induction Gl using gtth_ind_ref; intros; try easy.
  - inversion H1. subst.
    exists (gtth_hol ((Datatypes.length ctxJ) + n)).
    assert(extendLis (Datatypes.length ctxJ + n) (Some G) =
     (noneLis (Datatypes.length ctxJ) ++ extendLis n (Some G))%SEQ).
      {
       clear H1 H0 H. clear g1 p. induction ctxJ; intros; try easy.
       simpl in *. replace (extendLis (Datatypes.length ctxJ + n)%Nrec (Some G))%SEQ with
          ((noneLis (Datatypes.length ctxJ) ++ extendLis n (Some G))%SEQ). easy. 
      }
      rename H2 into Ht.
    split.
    - inversion H. subst. 
      specialize(extendExtract n (Some G)); intros.
      specialize(eq_trans (esym H4) H2); intros. inversion H3. subst.
      clear H4 H3 H2.
      constructor. clear H1 H0 H Ht. clear p. revert G n.
      induction ctxJ; intros; try easy. simpl in *.
      apply extendExtract; try easy.
      specialize(IHctxJ G n). easy.
    - split.
      replace ((noneLis (Datatypes.length ctxJ) ++ extendLis n (Some G))%SEQ) with (extendLis (Datatypes.length ctxJ + n) (Some G)). constructor.
    - intros. inversion H2; try easy.
  - inversion H0. subst.
    inversion H2. subst.
    assert(
      exists zs,
      Forall2 (fun u v => (u = None /\ v = None) \/ exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) g g') zs ys /\
      List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists ctxGi s g, u = Some ctxGi /\ v = Some (s, g) /\ usedCtx (noneLis (Datatypes.length ctxJ) ++ ctxGi) g)) ctxGLis zs /\
      Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ (ishParts p0 g -> False))) zs 
    ). 
    {
      specialize(mergeCtx_to_2R ctxGLis ctxG H6); intros.
      clear H6 H8 H2 H0.
      revert H H1 H9 H10 H3.
      revert p q xs p0 ctxG ctxJ ctxGLis.
      induction ys; intros; try easy.
      - destruct xs; try easy. destruct ctxGLis; try easy.
        exists nil. easy.
      - destruct xs; try easy. destruct ctxGLis; try easy.
        inversion H9. subst. clear H9. inversion H10. subst. clear H10.
        inversion H3. subst. clear H3. inversion H. subst. clear H.
        assert(exists zs : seq.seq (option (sort * gtth)),
         Forall2
           (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
            u = None /\ v = None \/
            (exists (s : sort) (g : gtth) (g' : gtt),
               u = Some (s, g) /\
               v = Some (s, g') /\ typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) g g')) zs ys /\
         Forall2
           (fun (u : option (seq.seq (option gtt))) (v : option (sort * gtth)) =>
            u = None /\ v = None \/
            (exists (ctxGi : seq.seq (option gtt)) (s : sort) (g : gtth),
               u = Some ctxGi /\
               v = Some (s, g) /\ usedCtx (noneLis (Datatypes.length ctxJ) ++ ctxGi) g)) ctxGLis zs /\
         Forall
           (fun u : option (sort * gtth) =>
            u = None \/ (exists (s : sort) (g : gtth), u = Some (s, g) /\ (ishParts p0 g -> False))) zs).
        specialize(IHys p q xs p0 ctxG ctxJ ctxGLis). apply IHys; try easy.
        specialize(ishParts_hxs H1); try easy.
        clear IHys H10 H8 H9 H7.
        destruct H as (zs,(Ha,(Hb,Hc))).
        destruct H6.
        - destruct H. subst. destruct H5. destruct H. subst.
          exists (None :: zs).
          - split. constructor; try easy. left. easy.
          - split. constructor; try easy. left. easy.
          - constructor; try easy. left. easy.
          destruct H as (s1,(g1,(g2,Ht))). easy.
        - destruct H as (ctxGi,(s1,(g1,(Hd,(He,Hf))))). subst.
          destruct H5; try easy. destruct H as (s2,(g2,(g3,(Hg,(Hh,Hi))))). inversion Hg. subst.
          destruct H4; try easy. destruct H as (ctxGi',(Hj,Hk)). inversion Hj. subst.
          destruct H3; try easy. destruct H as (s3,(g4,(Hl,Hm))). inversion Hl. subst.
          specialize(Hm g3 p0 ctxGi' ctxJ).
          assert(exists Gl' : gtth,
       typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxGi') Gl' g3 /\
       usedCtx (noneLis (Datatypes.length ctxJ) ++ ctxGi') Gl' /\ (ishParts p0 Gl' -> False)).
          {
            apply Hm; try easy.
            - apply typh_with_less with (ctxG := ctxG); try easy.
            - specialize(ishParts_x H1); try easy.
          }
          destruct H as (gl,(Hd,(He,Hta))). exists (Some (s3, gl) :: zs).
          - split. constructor; try easy.
            right. exists s3. exists gl. exists g3. split. easy. split. easy.
            apply typh_with_more2 with (ctxGi' := ctxGi'); try easy.
          - split. constructor; try easy. right. exists ctxGi'. exists s3. exists gl. easy.
          - constructor; try easy. right. exists s3. exists gl. easy.
    } 
    destruct H3 as (zs,(Ha,(Hb,Hc))).
    exists (gtth_send p q zs).
    - split. constructor; try easy.
      clear H H0 H1 H2 H6 H10 Hb Hc. 
      revert Ha H9 H8. revert ctxG ctxJ ys zs. clear p q p0 ctxGLis.
      induction xs; intros; try easy.
      specialize(SList_f a xs H8); intros.
      destruct ys; try easy. destruct zs; try easy. inversion Ha. subst. clear Ha. 
      inversion H9. subst. clear H9.
      destruct H.
      - specialize(IHxs ctxG ctxJ ys zs). apply SList_b. apply IHxs; try easy.
      - destruct H as (H,(a0,Ha)). subst. 
        destruct ys; try easy. destruct zs; try easy. clear H7 H5 H8 IHxs.
        destruct H4; try easy.
        destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
        destruct H3; try easy. destruct H as (s2,(g3,(g4,(Hd,(He,Hf))))). subst. easy.
    - split.
      assert(exists ks, Forall2 (fun u v => (u = None /\ v = None) \/ (exists ctxGi ctxGi', u = Some ctxGi /\ v = Some ctxGi' /\ (noneLis (Datatypes.length ctxJ) ++ ctxGi) = ctxGi')) ctxGLis ks).
      {
        clear Hc Hb Ha H10 H6 H9 H8 H2 H1 H0 H.
        induction ctxGLis; intros; try easy.
        exists nil. easy.
        destruct IHctxGLis as (ks, H).
        destruct a.
        - exists (Some (noneLis (Datatypes.length ctxJ) ++ l) :: ks). constructor; try easy.
          right. exists l. exists (noneLis (Datatypes.length ctxJ) ++ l). easy.
        - exists (None :: ks). constructor; try easy. left. easy.
      }
      destruct H3 as (ks, H3).
      clear Hc Ha H10 H9 H8 H2 H1 H0 H.
      clear p0 ys. 
      apply used_con with (ctxGLis := ks); try easy.
      - clear Hb. revert H3 H6. 
        revert ctxG ctxJ ks. clear p q xs zs.
        induction ctxGLis; intros; try easy.
        destruct ks; try easy. inversion H3. subst. clear H3.
        inversion H6.
        - subst. destruct ks; try easy. destruct H2; try easy.
          destruct H as (ct1,(ct2,(Ha,(Hb,Hc)))). inversion Ha. subst. constructor.
        - subst. destruct H2. destruct H. subst.
          specialize(IHctxGLis ctxG ctxJ ks). 
          assert(isMergeCtx (noneLis (Datatypes.length ctxJ) ++ ctxG) ks). apply IHctxGLis; try easy.
          constructor. easy.
          destruct H as (ct1,(ct2,Ha)). easy.
        - subst. specialize(IHctxGLis t ctxJ ks H5 H4).
          destruct H2; try easy. destruct H as (ct1,(ct2,(Ha,(Hb,Hc)))). inversion Ha. subst.
          apply cmconss with (t := (noneLis (Datatypes.length ctxJ) ++ t)); try easy.
          clear H4 H5 Ha H6 IHctxGLis. induction ctxJ; intros; try easy.
          simpl. constructor; try easy. left. easy.
      - revert H3 Hb. clear H6.
        revert ctxJ zs ks. clear p q xs ctxG.
        induction ctxGLis; intros.
        - destruct ks; try easy. destruct zs; try easy.
        - destruct ks; try easy. destruct zs; try easy. 
          inversion H3. subst. clear H3. inversion Hb. subst. clear Hb.
          specialize(IHctxGLis ctxJ zs ks H5 H6). constructor; try easy.
          clear IHctxGLis H5 H6.
          - destruct H2. destruct H. subst. destruct H3. destruct H. subst. left. easy.
            destruct H as(ct,(s1,(g1,Ha))). easy.
          - destruct H as (ct1,(ct2,(Ha,(Hb,Hc)))). subst.
            destruct H3; try easy. destruct H as (ct2,(s2,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
            right. exists (noneLis (Datatypes.length ctxJ) ++ ct2). exists s2. exists g2. easy.
    - intros.
      inversion H3. 
      - subst. apply H1. constructor.
      - subst. apply H1. constructor.
      - subst. specialize(some_onth_implies_In n zs (s, g) H14); intros.
        specialize(Forall_forall (fun u : option (sort * gtth) =>
        u = None \/ (exists (s : sort) (g : gtth), u = Some (s, g) /\ (ishParts p0 g -> False))) zs); intros.
        destruct H5. specialize(H5 Hc). clear H7 Hc.
        specialize(H5 (Some(s, g)) H4). destruct H5; try easy.
        destruct H5 as (s1,(g1,(Hta,Htb))). inversion Hta. subst.
        apply Htb; try easy.
Qed.

Lemma ctx_merge : forall s s0 s1 g1 l p,
    p <> s -> p <> s0 ->
    (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
       typ_gtth ctxG G' g1 /\
       (ishParts p G' -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
             u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
       usedCtx ctxG G') -> 
       (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
       typ_gtth ctxG G' (gtt_send s s0 l) /\
       (ishParts p G' -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
             u = Some (gtt_send   p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
       usedCtx ctxG G') -> 
       (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
  typ_gtth ctxG G' (gtt_send s s0 (Some (s1, g1) :: l)) /\
  (ishParts p G' -> False) /\
  Forall
    (fun u : option gtt =>
     u = None \/
     (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
        u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
  usedCtx ctxG G').
Proof.
  intros.
  destruct H1 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))).
  destruct H2 as (Gl2,(ctxJ,(He,(Hf,(Hg,Hh))))).
  inversion He. subst.
  - specialize(some_onth_implies_In n ctxJ (gtt_send s s0 l) H1); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxJ); intros.
    destruct H3. specialize(H3 Hg). clear H4 Hg.
    specialize(H3 (Some (gtt_send s s0 l)) H2). destruct H3; try easy.
    destruct H3 as (q1,(lsg,H3)).
    - destruct H3. inversion H3. subst. easy.
    - destruct H3. inversion H3. subst. easy.
    - inversion H3.
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

Lemma balanced_to_tree : forall G p,
    wfgC G ->
    isgPartsC p G ->
    exists G' ctxG, 
       typ_gtth ctxG G' G /\ (ishParts p G' -> False) /\
       List.Forall (fun u => u = None \/ (exists q lsg, u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some (gtt_end))) ctxG /\ usedCtx ctxG G'.
Proof.
  intros.
  specialize(parts_to_word p G H0); intros.
  destruct H1 as (w,(r,Ha)). pose proof H as Htt.
  unfold wfgC in H. destruct H as (Gl,(Hb,(Hc,(Hd,He)))). clear Hb Hc Hd. clear Gl H0.
  pose proof He as Ht.
  unfold balancedG in He.
  specialize(He nil w p r).
  simpl in He.
  assert(exists gn, gttmap G nil None gn).
  {
    destruct G. exists gnode_end. constructor.
    exists (gnode_pq s s0). constructor.
  }
  destruct H as (gn, H). specialize(He gn H).
  assert(gttmap G w None (gnode_pq p r) \/ gttmap G w None (gnode_pq r p)).
  {
    destruct Ha. right. easy. left. easy.
  }
  specialize(He H0). clear H H0. destruct He as (k, H).
  clear Ha.
  revert H Ht Htt. revert G p. clear w r gn.
  induction k; intros.
  - specialize(H nil).
    assert(exists gn, gttmap G nil None gn).
    {
      destruct G. exists gnode_end. constructor.
      exists (gnode_pq s s0). constructor.
    }
    destruct H0 as (gn, H0). inversion H0; try easy. subst.
    - assert(exists w2 w0 : seq.seq fin,
        [] = w2 ++ w0 /\
        (exists r : string,
           gttmap gtt_end w2 None (gnode_pq p r) \/ gttmap gtt_end w2 None (gnode_pq r p))).
      {
        apply H. left. easy.
      }
      clear H. destruct H1 as (w2,(w0,(Ha,Hb))). destruct w2; try easy. simpl in Ha. subst.
      destruct Hb as (r, Hb).
      destruct Hb. inversion H. inversion H.
    - assert(exists w2 w0 : seq.seq fin,
      [] = w2 ++ w0 /\
      (exists r : string, gttmap G w2 None (gnode_pq p r) \/ gttmap G w2 None (gnode_pq r p))).
      apply H. right. split. easy. exists gn. easy.
      destruct H2 as (w2,(w0,(Ha,Hb))). destruct w2; try easy. simpl in Ha. subst.
      clear H.
      destruct Hb as (r, Hb).
      destruct Hb.
      - inversion H. subst.
        exists (gtth_hol 0). exists [Some (gtt_send p r xs)].
        split.
        - constructor; try easy.
        - split. intros. inversion H1.
        - split. constructor; try easy. right. exists r. exists xs. left. easy.
        - assert(usedCtx (extendLis 0 (Some (gtt_send p r xs))) (gtth_hol 0)). constructor.
          simpl in H1. easy.
      - inversion H. subst.
        exists (gtth_hol 0). exists [Some (gtt_send r p xs)].
        split.
        - constructor; try easy.
        - split. intros. inversion H1.
        - split. constructor; try easy. right. exists r. exists xs. right. left. easy.
        - assert(usedCtx (extendLis 0 (Some (gtt_send r p xs))) (gtth_hol 0)). constructor.
          simpl in H1. easy.
  - destruct G.
    - exists (gtth_hol 0). exists [Some gtt_end].
      split. constructor. easy.
      split. intros. inversion H0.
      split. constructor; try easy. right. exists p. exists nil. right. right. easy.
      assert(usedCtx (extendLis 0 (Some (gtt_end))) (gtth_hol 0)). constructor. simpl in H0. easy.
    - specialize(balanced_cont Ht); intros.
      - case_eq (eqb p s); intros.
        assert (p = s). apply eqb_eq; try easy. subst.
        exists (gtth_hol 0). exists [Some (gtt_send s s0 l)].
        - split. constructor. easy.
        - split. intros. inversion H2.
        - split. constructor; try easy. right. exists s0. exists l. left. easy.
        - assert(usedCtx (extendLis 0 (Some (gtt_send s s0 l))) (gtth_hol 0)). constructor. simpl in H2. easy.
      - case_eq (eqb p s0); intros.
        assert (p = s0). apply eqb_eq; try easy. subst.
        exists (gtth_hol 0). exists [Some (gtt_send s s0 l)].
        - split. constructor. easy.
        - split. intros. inversion H3.
        - split. constructor; try easy. right. exists s. exists l. right. left. easy.
        - assert(usedCtx (extendLis 0 (Some (gtt_send s s0 l))) (gtth_hol 0)). constructor. simpl in H2. easy.
      - assert (p <> s). apply eqb_neq; try easy. 
        assert (p <> s0). apply eqb_neq; try easy.
        clear H1 H2.
      assert(Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\
        (forall w' : seq.seq fin,
       gttmap g w' None gnode_end \/
       Datatypes.length w' = k /\ (exists tc : gnode, gttmap g w' None tc) ->
       exists w2 w0 : seq.seq fin,
         w' = w2 ++ w0 /\
         (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p)))
      )) l).
      {
        apply Forall_forall; intros.
        destruct x.
        - specialize(in_some_implies_onth p0 l H1); intros.
          destruct H2 as (n, H2). destruct p0.
          right. exists s1. exists g. split. easy.
          intros.
          specialize(H (n :: w')).
          assert(exists w2 w0 : seq.seq fin,
            (n :: w')%SEQ = w2 ++ w0 /\
            (exists r : string,
               gttmap (gtt_send s s0 l) w2 None (gnode_pq p r) \/
               gttmap (gtt_send s s0 l) w2 None (gnode_pq r p))).
          {
            apply H; try easy.
            destruct H5. left. apply gmap_con with (st := s1) (gk := g); try easy.
            right. destruct H5. split. simpl. apply eq_S. easy.
            destruct H6. exists x.
            apply gmap_con with (st := s1) (gk := g); try easy.
          }
          destruct H6 as (w2,(w0,(Ha,Hb))).
          destruct w2.
          - simpl in *. subst.
            destruct Hb as (r, Hb). destruct Hb. inversion H6. subst. easy.
            inversion H6. subst. easy.
          - inversion Ha. subst.
            exists w2. exists w0. split. easy.
            destruct Hb as (r, Hb). exists r.
            destruct Hb.
            - left. inversion H6. subst. specialize(eq_trans (esym H14) H2); intros.
              inversion H7. subst. easy.
            - right. inversion H6. subst. specialize(eq_trans (esym H14) H2); intros.
              inversion H7. subst. easy.
        - left. easy.
      }
      assert(Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\
        exists (G' : gtth) (ctxG : seq.seq (option gtt)),
        typ_gtth ctxG G' g /\
        (ishParts p G' -> False) /\
        Forall
          (fun u : option gtt =>
           u = None \/
           (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
              u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
        usedCtx ctxG G'
      )) l). 
      {
        clear H Ht.
        assert(s <> s0).
        {
          specialize(wfgC_triv s s0 l Htt); intros. easy.
        }
        specialize(wfgC_after_step_all H Htt); intros. clear H Htt.
        revert H0 IHk H1 H3 H4 H2. revert k s s0 p.
        induction l; intros; try easy.
        inversion H1. subst. clear H1. inversion H0. subst. clear H0. inversion H2. subst. clear H2.
        specialize(IHl k s s0 p).
        assert(Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt),
            u = Some (s, g) /\
            (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
               typ_gtth ctxG G' g /\
               (ishParts p G' -> False) /\
               Forall
                 (fun u0 : option gtt =>
                  u0 = None \/
                  (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
                     u0 = Some (gtt_send p q lsg) \/ u0 = Some (gtt_send q p lsg) \/ u0 = Some gtt_end))
                 ctxG /\ usedCtx ctxG G'))) l).
         apply IHl; try easy.
         constructor; try easy. clear H H9 H8 H7 IHl.
         destruct H5. left. easy.
         destruct H as (s1,(g1,(Ha,Hb))). subst. 
         destruct H1; try easy.
         destruct H as (s2,(g2,(Hc,Hd))). inversion Hc. subst.
         destruct H6; try easy. destruct H as (s3,(g3,(He,Hf))). inversion He. subst.
         specialize(IHk g3 p). right. exists s3. exists g3. split. easy. apply IHk; try easy.
      }
    clear H1 H0 Ht H IHk.
    assert(SList l).
    {
      specialize(wfgC_triv s s0 l Htt); intros. easy.
    }
    clear Htt.
    revert H H2 H3 H4. clear k. revert s s0 p.
    induction l; intros; try easy.
    specialize(SList_f a l H); intros. clear H.
    inversion H2. subst. clear H2.
    destruct H0.
    - specialize(IHl s s0 p).
      assert(exists (G' : gtth) (ctxG : seq.seq (option gtt)),
        typ_gtth ctxG G' (gtt_send s s0 l) /\
        (ishParts p G' -> False) /\
        Forall
          (fun u : option gtt =>
           u = None \/
           (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
              u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
        usedCtx ctxG G').
      {
        apply IHl; try easy.
      }
      clear H6 H IHl.
      destruct H5.
      - subst.
        destruct H0 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))).
        inversion Ha.
        - subst.
          specialize(some_onth_implies_In n ctxG (gtt_send s s0 l) H); intros.
          specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
          destruct H1. specialize(H1 Hc). clear H2 Hc.
          specialize(H1 (Some (gtt_send s s0 l)) H0). destruct H1; try easy.
          destruct H1 as (q1,(lsg,He)).
          - destruct He. inversion H1. subst. easy.
          - destruct H1. inversion H1. subst. easy.
          - inversion H1. 
        - subst.
          exists (gtth_send s s0 (None :: xs)). exists ctxG.
          - split. constructor; try easy.
            constructor; try easy. left. easy.
          - split. 
            intros. apply Hb. inversion H. subst. easy. subst. easy. subst.
            destruct n; try easy.
            apply ha_sendr with (n := n) (s := s1) (g := g); try easy.
          - split. easy.
          - inversion Hd. subst. apply used_con with (ctxGLis := (None :: ctxGLis)); try easy.
            constructor; try easy.
            constructor; try easy. left. easy.
      - destruct H as (s1,(g1,(Ha,Hb))). subst.
        specialize(ctx_merge s s0 s1 g1 l p); intros. apply H; try easy.
    destruct H as (H1,(a0,H2)). subst. clear H6 IHl.
    destruct H5; try easy.
    destruct H as (s1,(g1,(Ha,Hb))). inversion Ha. subst. clear Ha.
    destruct Hb as (Gl,(ctxG,(Hc,(Hd,(He,Hf))))).
    exists (gtth_send s s0 [Some (s1, Gl)]). exists ctxG.
    - split. constructor; try easy. constructor; try easy.
      right. exists s1. exists Gl. exists g1. easy.
    - split. intros. apply Hd. inversion H. subst. easy. subst. easy. 
      subst. destruct n; try easy.
      - simpl in H8. inversion H8. subst. easy.
      - simpl in H8. destruct n; try easy.
    - split. easy.
    - apply used_con with (ctxGLis := [Some ctxG]); try easy.
      - constructor.
      - constructor; try easy. right. exists ctxG. exists s1. exists Gl. easy.
Qed.

Lemma wfgC_after_step_helper : forall n0 s G' lsg lis1, 
      Some (s, G') = onth n0 lsg -> 
      Forall2
       (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : global) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) lis1 lsg -> 
      Forall
       (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ wfG g)) lis1 -> 
      Forall
      (fun u : option (sort * gtt) =>
       u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) lsg -> 
      Forall
       (fun u : option (sort * global) =>
        u = None \/
        (exists (s : sort) (g : global),
           u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) lis1 -> 
      exists G1, onth n0 lis1 = Some(s, G1) /\ gttTC G1 G' /\ wfG G1 /\ balancedG G' /\ (forall n, exists m, guardG n m G1).
Proof.
  induction n0; intros.
  - destruct lsg; try easy. destruct lis1; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    inversion H3. subst. clear H3. 
    simpl in H. subst.
    destruct H7; try easy. destruct H as (s0,(g1,(g2,(Ha,(Hb,Hc))))). inversion Hb. subst.
    destruct H5; try easy. destruct H as (s1,(g3,(Hd,He))). inversion Hd. subst.
    destruct H4; try easy. destruct H as (s2,(g4,(Hf,Hg))). inversion Hf. subst.
    destruct H2; try easy. destruct H as (s3,(g5,(Hh,Hi))). inversion Hh. subst.
    simpl. exists g5. pclearbot. easy.
  - destruct lsg; try easy. destruct lis1; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    inversion H3. subst. clear H3. 
    specialize(IHn0 s G' lsg lis1). apply IHn0; try easy.
Qed.

Lemma wfgC_after_step_helper2 : forall lis ys ys0 n p q,
    SList lis -> 
    Forall2
       (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : global) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) lis ys -> 
    Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q n))
        ys ys0 ->
    SList ys0.
Proof.
  induction lis; intros; try easy.
  specialize(SList_f a lis H); intros. destruct ys; try easy. destruct ys0; try easy.
  specialize(IHlis ys ys0 n p q). inversion H0. subst. clear H0. inversion H1. subst. clear H1.
  destruct H2. apply SList_b. apply IHlis; try easy.
  destruct H0. destruct H1. subst. destruct H6; try easy.
  destruct H0 as (s0,(g0,(g1,(Ha,(Hb,Hc))))). subst. destruct ys; try easy.
  destruct H5; try easy. destruct H0 as (s2,(g2,(g3,(Hta,(Htb,Htc))))). inversion Hta. subst.
  destruct ys0; try easy.
Qed.

Lemma wfgC_after_step_helper3 : forall ys0 xs,
      SList ys0 -> 
      Forall2
       (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : global) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ gttTC g g')) xs ys0 -> 
      SList xs.
Proof.
  induction ys0; intros; try easy.
  specialize(SList_f a ys0 H); intros. 
  destruct xs; try easy.
  specialize(IHys0 xs). inversion H0. subst. clear H0.
  destruct H1. apply SList_b. apply IHys0; try easy.
  destruct H0. destruct H1. subst.
  destruct H5; try easy. destruct H0 as (s,(g,(g',(Ha,(Hb,Hc))))). inversion Hb. subst.
  destruct xs; try easy.
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


(* hint : induction on balanced_to_tree *)
Lemma step_gtth : forall G G' p q l,
    wfgC G -> 
    gttstepC G G' p q l -> 
    exists ctxG ctxG2 Gl, typ_gtth ctxG Gl G /\ typ_gtth ctxG2 Gl G' /\
    (ishParts p Gl -> False) /\ (ishParts q Gl -> False) /\ 
    Forall2 (fun u v => (u = None /\ v = None) \/ (exists p q lis s g, u = Some (gtt_send p q lis) /\ onth l lis = Some(s, g) /\ v = Some g)) ctxG ctxG2.
Proof.
  intros.
  specialize(balanced_to_tree G p H); intros.
Admitted.



Lemma balanced_step : forall [G G' p q l],
    wfgC G -> 
    gttstepC G G' p q l -> 
    projectableA G ->
    balancedG G'.
Proof.
  intros.
  specialize(step_gtth G G' p q l H H0); intros.
  unfold wfgC in H. destruct H as (Gl,(Ha,(Hb,(Hc,H)))). clear Ha Hb Hc. clear Gl.
  destruct H2 as (ctxG,(ctxG2,(Gl,(Ha,(Hb,(Hc,(Hd,He))))))).
  
  
Admitted.

Lemma wfgC_after_step : forall G G' p q n, wfgC G -> gttstepC G G' p q n -> projectableA G -> wfgC G'. 
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

Lemma proj_inj : forall [g p t t'],
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

Lemma guard_contG : forall n st st' x1 s3 g,
        (forall n : fin, exists m : fin, guardG n m (g_send st st' x1)) -> 
        onth n x1 = Some (s3, g) -> 
        (forall n0 : fin, exists m : fin, guardG n0 m g).
Proof.
  intros. specialize(H (S n0)). destruct H. inversion H. subst. clear H.
  revert H4 H0. revert n0 x g s3 x1 st st'.
  induction n; intros; try easy.
  - destruct x1; try easy. simpl in H0. subst. exists x.
    inversion H4. subst.
    destruct H1; try easy. destruct H as (s1,(g1,(Hta,Htb))). inversion Hta. subst. easy.
  - destruct x1; try easy.
    inversion H4. subst. clear H4.
    specialize(IHn n0 x g s3 x1). apply IHn; try easy. 
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


















