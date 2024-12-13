From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header src.global src.local src.merge src.global_tree_ctx src.projection src.step.
Require Import List String Coq.Arith.PeanoNat Relations Coq.Logic.Decidable.
Import ListNotations. 

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
