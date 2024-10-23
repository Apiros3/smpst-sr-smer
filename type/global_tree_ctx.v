From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header type.global type.local type.isomorphism type.decidability.
Require Import List String Coq.Arith.PeanoNat Relations Coq.Logic.Decidable.
Import ListNotations. 
(* global trees with context holes *)
Inductive gtth: Type :=
  | gtth_hol    : fin -> gtth
  | gtth_send   : part -> part -> list (option (sort * gtth)) -> gtth.

Section gtth_ind_ref.
  Variable P : gtth -> Prop.
  Hypothesis P_hol : forall n, P (gtth_hol n).
  Hypothesis P_send : forall p q xs, List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ P g)) xs -> P (gtth_send p q xs).
  
  Fixpoint gtth_ind_ref p : P p.
  Proof.
    destruct p.
    - apply P_hol.
    - apply P_send.
      induction l; intros; try easy.
      constructor; try easy.
      destruct a. 
      - destruct p. right. exists s1. exists g. split. easy. apply gtth_ind_ref.
      - left. easy.
  Qed.

End gtth_ind_ref.

Inductive typ_gtth : list (option gtt) -> gtth -> gtt -> Prop := 
  | gt_hol : forall n ctx gc, onth n ctx = Some gc -> typ_gtth ctx (gtth_hol n) gc
  | gt_send : forall ctx p q xs ys, SList xs -> List.Forall2 (fun u v => (u = None /\ v = None) \/ 
                                                (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ typ_gtth ctx g g')) xs ys -> 
                                                typ_gtth ctx (gtth_send p q xs) (gtt_send p q ys).

Section typ_gtth_ind_ref.
  Variable P : list (option gtt) -> gtth -> gtt -> Prop.
  Hypothesis P_hol : forall n ctx gc, onth n ctx = Some gc -> P ctx (gtth_hol n ) gc.
  Hypothesis P_send : forall ctx p q xs ys, SList xs -> List.Forall2 (fun u v => (u = None /\ v = None) \/ 
                                                 (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ P ctx g g')) xs ys -> 
                                                 P ctx (gtth_send p q xs) (gtt_send p q ys).
  
  Fixpoint typ_gtth_ind_ref ctx G G' (a : typ_gtth ctx G G') {struct a} : P ctx G G'.
  Proof.
    refine (match a with 
      | gt_hol n ctx gc Ha => P_hol n ctx gc Ha
      | gt_send ctx p q xs ys Ha Hl => P_send ctx p q xs ys Ha _
    end); try easy.
    revert Hl. apply Forall2_mono.
    intros. 
    destruct H.
    - left. easy.
    - destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
      right. exists x0. exists x1. exists x2. split. easy. split. easy. 
      apply typ_gtth_ind_ref; try easy.
  Qed.

End typ_gtth_ind_ref.

Inductive ishParts : part -> gtth -> Prop := 
  | ha_sendp : forall p q l, ishParts p (gtth_send p q l)
  | ha_sendq : forall p q l, ishParts q (gtth_send p q l)
  | ha_sendr : forall p q r n s g lis, p <> r -> q <> r -> onth n lis = Some (s, g) -> ishParts r g -> ishParts r (gtth_send p q lis).

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


Lemma ishParts_hxs : forall [p s1 s2 o1 xs0],
    (ishParts p (gtth_send s1 s2 (o1 :: xs0)) -> False) ->
    (ishParts p (gtth_send s1 s2 xs0) -> False).
Proof.
  intros. apply H.
  inversion H0. subst. apply ha_sendp. apply ha_sendq.
  subst. apply ha_sendr with (n := Nat.succ n) (s := s) (g := g); try easy.
Qed.

Lemma ishParts_n : forall [n p s s' xs s0 g],
    (ishParts p (gtth_send s s' xs) -> False) ->
    onth n xs = Some(s0, g) -> 
    (ishParts p g -> False).
Proof.  
  induction n; intros; try easy.
  - apply H. destruct xs; try easy. simpl in *. subst.
    - case_eq (eqb p s); intros.
      assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
    - case_eq (eqb p s'); intros.
      assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
    - assert (p <> s). apply eqb_neq; try easy. 
      assert (p <> s'). apply eqb_neq; try easy.
      apply ha_sendr with (n := 0) (s := s0) (g := g); try easy.
  - destruct xs; try easy.
    specialize(ishParts_hxs H); intros.
    specialize(IHn p s s' xs s0 g). apply IHn; try easy.
Qed.

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



Inductive usedCtx : (list (option gtt)) -> gtth -> Prop := 
  | used_hol : forall n G, usedCtx (extendLis n (Some G)) (gtth_hol n)
  | used_con : forall ctxG ctxGLis p q ys, isMergeCtx ctxG ctxGLis -> 
        List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists ctxGi s g, u = Some ctxGi /\ v = Some (s, g) /\ usedCtx ctxGi g)) ctxGLis ys -> usedCtx ctxG (gtth_send p q ys).

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

