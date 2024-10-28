From SST Require Export src.expressions process.processes process.typecheck type.global type.local process.beta process.sessions process.inversion  type.isomorphism type.projection type.proj_part type.wfgC_after_step.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.


Inductive multiC : relation gtt := 
  | multiC_refl : forall G, multiC G G
  | multiC_step : forall G1 G2 G3 p q n, gttstepC G1 G2 p q n -> multiC G2 G3 -> multiC G1 G3.
  

Lemma _3_21_1_helper : forall l x1 xs x4 x5 y,
    onth l x1 = Some (x4, x5) ->
    onth l xs = Some y ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: nil) nil p t))
       xs x1 ->
    typ_proc (Some x4 :: nil) nil y x5.
Proof.
  induction l; intros; try easy.
  - destruct x1. try easy. destruct xs. try easy.
    simpl in *. subst.
    inversion H1. subst. destruct H3. destruct H. easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. inversion H. inversion H0. subst. easy.
  - destruct x1; try easy. destruct xs; try easy.
    simpl in *. apply IHl with (x1 := x1) (xs := xs); try easy.
    inversion H1; try easy.
Qed.

Lemma noin_cat_and {A} : forall pt (l1 l2 : list A), ~ In pt (l1 ++ l2) -> ~ (In pt l1 \/ In pt l2).
Proof.
  induction l1; intros; try easy.
  simpl in *. apply Classical_Prop.and_not_or. split; try easy.
  simpl in *. specialize(Classical_Prop.not_or_and (a = pt) (In pt (l1 ++ l2)) H); intros.
  destruct H0. 
  apply Classical_Prop.and_not_or.
  specialize(IHl1 l2 H1).
  specialize(Classical_Prop.not_or_and (In pt l1) (In pt l2) IHl1); intros. destruct H2.
  split; try easy. apply Classical_Prop.and_not_or. split; try easy.
Qed.

Lemma wfC_helper : forall l LQ SL' TL' lis,
    onth l LQ = Some (SL', TL') -> 
    Forall2
       (fun (u : option (sort * local)) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : local) (g' : ltt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco2 lttT bot2 g g')) lis LQ -> 
    exists T, onth l lis = Some(SL', T) /\ lttTC T TL'.
Proof.
  induction l; intros.
  - destruct LQ; try easy.
    inversion H0. subst. clear H0 H5. simpl in H.
    subst. destruct H4; try easy.
    destruct H as (s,(g,(g',(Ha,(Hb,Hc))))). subst. inversion Hb. subst.
    exists g. destruct Hc; try easy.
  - destruct LQ ;try easy.
    inversion H0. subst. clear H0. 
    specialize(IHl LQ SL' TL' l0). apply IHl; try easy.
Qed.

Lemma wfC_recv :  forall [l LQ SL' TL' q],
        wfC (ltt_recv q LQ) -> 
        onth l LQ = Some (SL', TL') -> 
        wfC TL'.
Proof.  
  intros.
  unfold wfC in *.
  destruct H as (T,(Ha,(Hb,Hc))).
  specialize(guard_breakL_s2 (ltt_recv q LQ) T Hc Hb Ha); intros.
  clear Ha Hb Hc. clear T.
  destruct H as (T,(Hb,(Hc,(Hd,He)))).
  destruct Hb.
  - subst. pinversion He; try easy. apply lttT_mon.
  - destruct H as (p0,(lis,Hf)).
    destruct Hf. subst. pinversion He. apply lttT_mon.
  - subst. pinversion He; try easy. subst.
    specialize(wfC_helper l LQ SL' TL' lis H0 H1); intros.
    destruct H as (T,(Hf,Hg)).
    exists T. split. easy. clear Hg H1 H0 He.
    clear TL' LQ.
    split.
    - inversion Hd. subst.
      clear H1 Hd Hc. revert Hf H2. revert lis. induction l; intros; try easy.
      - destruct lis; try easy. inversion H2. subst. clear H2 H3.
        simpl in *. subst. destruct H1; try easy.
        destruct H as (s,(g,(Ha,Hb))). inversion Ha. subst. easy.
      - destruct lis; try easy. inversion H2. subst. clear H2.
        specialize(IHl lis). apply IHl; try easy.
    - intros. specialize(Hc (S n)).
      destruct Hc. inversion H. subst. 
      clear Hd H. revert Hf H3. revert lis.
      induction l; intros; try easy.
      - destruct lis; try easy.
        inversion H3. subst. clear H3 H2. simpl in *. subst.
        destruct H1; try easy. destruct H as (s,(g,(Ha,Hb))). inversion Ha. subst.
        exists x. easy.
      - destruct lis; try easy.
        inversion H3. subst. clear H3.
        specialize(IHl lis). apply IHl; try easy.
    apply lttT_mon.
Qed.

Lemma wfC_send : forall [l LP SL TL p],
        wfC (ltt_send p LP) -> 
        onth l LP = Some (SL, TL) -> 
        wfC TL.
Proof.
  intros.
  unfold wfC in *.
  destruct H as (T,(Ha,(Hb,Hc))).
  specialize(guard_breakL_s2 (ltt_send p LP) T Hc Hb Ha); intros.
  clear Ha Hb Hc. clear T.
  destruct H as (T,(Hb,(Hc,(Hd,He)))).
  destruct Hb.
  - subst. pinversion He; try easy. apply lttT_mon.
  - destruct H as (p0,(lis,Hf)).
    destruct Hf. subst. pinversion He; try easy. subst.
    specialize(wfC_helper l LP SL TL lis H0 H1); intros.
    destruct H as (T,(Hf,Hg)).
    exists T. split. easy. clear Hg H1 H0 He.
    clear TL LP.
    split.
    - inversion Hd. subst.
      clear H1 Hd Hc. revert Hf H2. revert lis. induction l; intros; try easy.
      - destruct lis; try easy. inversion H2. subst. clear H2 H3.
        simpl in *. subst. destruct H1; try easy.
        destruct H as (s,(g,(Ha,Hb))). inversion Ha. subst. easy.
      - destruct lis; try easy. inversion H2. subst. clear H2.
        specialize(IHl lis). apply IHl; try easy.
    - intros. specialize(Hc (S n)).
      destruct Hc. inversion H. subst. 
      clear Hd H. revert Hf H3. revert lis.
      induction l; intros; try easy.
      - destruct lis; try easy.
        inversion H3. subst. clear H3 H2. simpl in *. subst.
        destruct H1; try easy. destruct H as (s,(g,(Ha,Hb))). inversion Ha. subst.
        exists x. easy.
      - destruct lis; try easy.
        inversion H3. subst. clear H3.
        specialize(IHl lis). apply IHl; try easy.
    apply lttT_mon.
  - subst. pinversion He; try easy. apply lttT_mon.
Qed.


Lemma _3_19_3_helper : forall M p q G G' l L1 L2 S T xs y,
    wfgC G ->
    wfgC G' ->
    projectionC G p (ltt_send q L1) -> 
    subtypeC (ltt_send q (extendLis l (Datatypes.Some(S, T)))) (ltt_send q L1) ->
    projectionC G q (ltt_recv p L2) -> 
    onth l xs = Some y ->
    ForallT
  (fun (u : string) (P : process) =>
   exists T : ltt,
     projectionC G u T /\ typ_proc nil nil P T /\ (forall n : fin, exists m : fin, guardP n m P)) M ->
    subtypeC (ltt_recv p xs) (ltt_recv p L2) -> 
    gttstepC G G' p q l ->
    ~ InT q M ->
    ~ InT p M ->
    ForallT
  (fun (u : string) (P : process) =>
   exists T : ltt,
     projectionC G' u T /\ typ_proc nil nil P T /\ (forall n : fin, exists m : fin, guardP n m P)) M.
Proof.
  intro M. induction M; intros; try easy.
  - unfold InT in *. simpl in H8. simpl in H9.
    specialize(Classical_Prop.not_or_and (s = q) False H8); intros. destruct H10.
    specialize(Classical_Prop.not_or_and (s = p0) False H9); intros. destruct H12.
    clear H8 H9 H11 H13.
    constructor.
    inversion H5. subst. destruct H9 as [T' H9]. destruct H9.
    specialize(projection_step_label G G' p0 q l L1 L2 H H1 H3 H7); intros.
    destruct H11. destruct H11. destruct H11. destruct H11. destruct H11.
    specialize(_3_19_3_helper G G' p0 q s l L1 L2 x x1 x0 x2 T'); intros.
    assert(exists T'0 : ltt, projectionC G' s T'0 /\ T' = T'0).
    apply H14; try easy.
    clear H14. destruct H15. exists x3. split; try easy. destruct H14. rename x3 into Tl. subst. easy. 
  - inversion H5. subst.
    specialize(noin_cat_and q (flattenT M1) (flattenT M2) H8); intros.
    specialize(noin_cat_and p (flattenT M1) (flattenT M2) H9); intros.
    specialize(Classical_Prop.not_or_and (In q (flattenT M1)) (In q (flattenT M2)) H10); intros.
    specialize(Classical_Prop.not_or_and (In p (flattenT M1)) (In p (flattenT M2)) H11); intros.
    destruct H14. destruct H15.
    unfold InT in *.
    specialize(IHM1 p q G G' l L1 L2 S T xs y H H0 H1 H2 H3 H4 H12 H6 H7 H14 H15).
    specialize(IHM2 p q G G' l L1 L2 S T xs y H H0 H1 H2 H3 H4 H13 H6 H7 H16 H17).
    constructor; try easy.
Qed.

Lemma _3_21_helper : forall l xs x1 y,
    onth l xs = Some y ->
    Forall2
        (fun (u : option process) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (p : process) (s : sort) (t : ltt),
            u = Some p /\
            v = Some (s, t) /\ typ_proc (Some s :: nil) nil p t)) xs x1 ->
    exists s t, onth l x1 = Some(s,t) /\ typ_proc (Some s :: nil) nil y t.
Proof.
  induction l; intros.
  - destruct xs; try easy.
    destruct x1; try easy.
    simpl in *.
    inversion H0. subst. destruct H4; try easy. destruct H. destruct H. destruct H. destruct H. destruct H1. 
    inversion H. subst.
    exists x0. exists x2. split; try easy.
  - destruct xs; try easy.
    destruct x1; try easy. 
    inversion H0. subst. apply IHl with (xs := xs); try easy.
Qed.

Lemma _3_21_helper_1 : forall [l LQ SL' TL' x x1 x0 q],
        onth l LQ = Some (SL', TL') -> 
        onth l x = Some (x0, x1) ->
        subtypeC (ltt_recv q x) (ltt_recv q LQ) ->
        subtypeC x1 TL' /\ subsort SL' x0.
Proof.
  intros.
  specialize(subtype_recv_inv q x LQ H1); intros.
  clear H1. revert H2 H0 H. revert q x0 x1 x TL' SL' LQ.
  induction l; intros.
  - destruct x; try easy. destruct LQ; try easy. simpl in *. subst.
    inversion H2. subst. destruct H3; try easy. destruct H. destruct H. destruct H.
    destruct H. destruct H. destruct H0. destruct H1. inversion H. inversion H0. subst. easy.
  - destruct LQ; try easy. destruct x; try easy. 
    inversion H2. subst.
    specialize(IHl q x0 x1 x TL' SL' LQ). apply IHl; try easy.
Qed.

Lemma _3_21_helper_2 : forall [l LP SL TL LT S p],
       subtypeC (ltt_send p (extendLis l (Some (S, LT)))) (ltt_send p LP) ->
       onth l LP = Some (SL, TL) -> 
       subtypeC LT TL /\ subsort S SL.
Proof.
  intros.
  specialize(subtype_send_inv p (extendLis l (Some (S, LT))) LP H); intros.
  clear H. revert H0 H1. revert LP SL TL LT S p.
  induction l; intros.
  - destruct LP; try easy. inversion H1. subst.
    destruct H4; try easy. destruct H. destruct H. destruct H. destruct H. destruct H.
    destruct H2. destruct H3. inversion H. simpl in H0. subst. inversion H2. subst.
    easy.
  - destruct LP; try easy. inversion H1. subst.
    specialize(IHl LP SL TL LT S p). apply IHl; try easy.
Qed. 

Lemma _3_21_helper_3 : forall M G pt,
        In pt (flattenT M) -> 
        ForallT
       (fun (u : string) (P : process) =>
        exists T : ltt,
          projectionC G u T /\ typ_proc nil nil P T /\ (forall n : fin, exists m : fin, guardP n m P))
       M -> 
       exists T : ltt, projectionC G pt T.
Proof.
  induction M; intros; try easy.
  - simpl in H. destruct H; try easy. subst.
    inversion H0. subst. destruct H1 as (T,(Ha,Hb)). exists T. easy.
  - inversion H0. subst.
    specialize(in_or (flattenT M1) (flattenT M2) pt H); intros.
    destruct H1.
    - specialize(IHM1 G pt H1 H3). apply IHM1; try easy.
    - specialize(IHM2 G pt H1 H4). apply IHM2; try easy.
Qed.

Lemma guardP_cont_recv_n : forall l xs y q, 
       (forall n : fin, exists m : fin, guardP n m (p_recv q xs)) -> 
        onth l xs = Some y -> 
        (forall n : fin, exists m : fin, guardP n m y).
Proof.
  induction l; intros; try easy.
  - destruct xs; try easy.
    simpl in H0. subst. specialize(H (Nat.succ n)).
    destruct H. inversion H. subst.
    inversion H3. subst. destruct H2; try easy.
    destruct H0 as (g,(Ha,Hb)). inversion Ha. subst. exists x. easy.
  - destruct xs; try easy.
    specialize(IHl xs y q). apply IHl; try easy.
    intros. specialize(H n0). destruct H.
    inversion H. subst. exists 0. constructor.
    subst. exists x. inversion H4. subst. constructor; try easy.
Qed. 

Inductive peq_w : process -> process -> Prop := 
  | peq_var : forall n, peq_w (p_var n) (p_var n)
  | peq_inact : peq_w p_inact p_inact
  | peq_send : forall pt lb e e' p1 p2, peq_w p1 p2 -> peq_w (p_send pt lb e p1) (p_send pt lb e' p2)
  | peq_recv : forall pt xs ys, Forall2 (fun u v => (u = None /\ v = None) \/ (exists p p', u = Some p /\ v = Some p' /\ peq_w p p')) xs ys -> peq_w (p_recv pt xs) (p_recv pt ys)
  | peq_ite  : forall e1 p1 q1 e2 p2 q2, peq_w p1 p2 -> peq_w q1 q2 -> peq_w (p_ite e1 p1 q1) (p_ite e2 p2 q2)
  | peq_rec : forall p1 p2, peq_w p1 p2 -> peq_w (p_rec p1) (p_rec p2).

Lemma peq_after_incr : forall g p0 m n k l,
        peq_w g p0 -> 
        peq_w (incr_free m n k l g) (incr_free m n k l p0).
Proof.
  induction g using process_ind_ref; intros; try easy.
  - inversion H. subst. constructor.
  - inversion H. subst. constructor.
  - inversion H. subst. constructor; try easy. apply IHg; try easy.
  - inversion H0. subst. constructor; try easy.
    revert H4 H. clear H0. revert llp m n k l.
    induction ys; intros; try easy.
    - destruct llp; try easy.
    - destruct llp; try easy.
      inversion H. subst. clear H. inversion H4. subst. clear H4.
      specialize(IHys llp m n k l H7 H3). constructor; try easy. clear IHys H3 H7.
      destruct H5.
      - destruct H. subst. left. easy.
      - destruct H as (p1,(p2,(Ha,(Hb,Hc)))). subst.
        right. exists (incr_free m (S n) k l p1). exists (incr_free m (S n) k l p2). split. easy.
        split. easy.
        apply H2; try easy.
  - inversion H. subst. constructor. apply IHg1; try easy. apply IHg2; try easy.
  - inversion H. subst. constructor. apply IHg; try easy.
Qed.

Lemma peq_after_subst : forall g1 g Q m n k p0 p1,
        substitutionP m n k g g1 Q -> 
        peq_w g p0 -> peq_w g1 p1 ->
        exists Q' : process, substitutionP m n k p0 p1 Q' /\ peq_w Q Q'.
Proof.
  induction g1 using process_ind_ref; intros.
  - inversion H1. subst.
    inversion H. subst.
    - exists (incr_free 0 0 n0 k p0). split. constructor. 
      apply peq_after_incr; try easy.
    - subst. exists (p_var 0). split. constructor. easy. constructor.
    - subst. exists (p_var y). split. constructor; try easy. constructor.
    - subst. exists (p_var (S y)). split. constructor; try easy. constructor.
  - inversion H1. subst. 
    inversion H. subst. exists p_inact. split. constructor. constructor.
  - inversion H1. subst.
    inversion H. subst.
    specialize(IHg1 g Q' m n k p0 p3 H12 H0 H7). destruct IHg1 as (q1,(Ha,Hb)).
    exists (p_send pt lb e' q1). split. constructor; try easy. constructor; try easy.
  - inversion H2. subst. inversion H0. subst.
    clear H2 H0.
    assert(exists ys3, Forall2 (fun u v => (u = None /\ v = None) \/ (exists p p', u = Some p /\ v = Some p' /\ substitutionP m n (S k) p0 p p')) ys ys3 /\ Forall2 (fun u v => (u = None /\ v = None) \/ (exists p p', u = Some p /\ v = Some p' /\ peq_w p p')) ys0 ys3).
    {
      revert H11 H6 H1 H.
      revert llp g m n k p0 ys0.
      induction ys; intros.
      - destruct llp; try easy. destruct ys0; try easy. exists nil. easy.
      - destruct llp; try easy. destruct ys0; try easy.
        inversion H11. subst. clear H11. inversion H6. subst. clear H6.
        inversion H. subst. clear H.
        specialize(IHys llp g m n k p0 ys0 H7 H9 H1 H6).
        clear H6 H9 H7.
        destruct IHys as (ys3,(Ha,Hb)).
        destruct H4.
        - destruct H. subst. destruct H5. destruct H. subst.
          exists (None :: ys3). split. constructor; try easy. left. easy. constructor; try easy. left. easy. 
          destruct H as (p1,(p2,Hc)). easy.
        - destruct H as (k1,(l1,(Hc,(Hd,He)))). subst.
          destruct H5; try easy. destruct H as (p1,(p2,(Hf,(Hg,Hh)))). inversion Hf. subst.
          specialize(H3 g l1 m n (S k) p0 p2 He H1 Hh).
          destruct H3 as (q1,(Hg,Hi)).
          exists (Some q1 :: ys3).
          - split. constructor; try easy. right. exists p2. exists q1. easy.
          - constructor; try easy. right. exists l1. exists q1. easy.
    }
    destruct H0 as (ys3,(Ha,Hb)). exists (p_recv pt ys3).
    split. constructor; try easy. constructor; try easy. 
  - inversion H1. subst. inversion H. subst.
    specialize(IHg1_1 g Q1 m n k p0 p3 H12 H0 H6). destruct IHg1_1 as (q1,(Ha,Hb)).
    specialize(IHg1_2 g Q2 m n k p0 q2 H13 H0 H7). destruct IHg1_2 as (q3,(Hc,Hd)).
    exists (p_ite e2 q1 q3). split. constructor; try easy. constructor; try easy.
  - inversion H1. subst. inversion H. subst.
    specialize(IHg1 g Q' (S m) (S n) k p0 p3 H8 H0 H3).
    destruct IHg1 as (q1,(Ha,Hb)). exists (p_rec q1).
    split. constructor; try easy.
    constructor; try easy.
Qed.

Lemma guardP_peq_w : forall p1 p2, 
      peq_w p1 p2 -> 
      (forall n : fin, exists m : fin, guardP n m p1) -> 
      (forall n : fin, exists m : fin, guardP n m p2).
Proof.
  intros.
  specialize(H0 n). destruct H0 as (m, H0). exists m.
  revert H0 H. revert p1 p2 m.
  induction n; intros; try easy.
  - constructor.
  - revert IHn H H0. revert n p1 p2.
    induction m; intros; try easy.
    inversion H0.
    - subst. inversion H. subst. constructor.
    - subst. inversion H. subst. constructor. apply IHn with (p1 := g); try easy.
    - subst. inversion H. subst.
      constructor. revert H5 H2 IHn. clear H0 H. revert ys. induction lis; intros; try easy.
      - destruct ys; try easy.
      - destruct ys; try easy. inversion H2. subst. clear H2. inversion H5. subst. clear H5.
        specialize(IHlis ys H7 H3 IHn). constructor; try easy.
        clear IHlis H3 H7.
        destruct H4. left. easy.
        destruct H as (p1,(p2,(Ha,(Hb,Hc)))). subst.
        destruct H1; try easy. destruct H as (g1,(Hd,He)). inversion Hd. subst.
        right. exists p2. split. easy. apply IHn with (p1 := g1); try easy.
    assert(forall (p1 p2 : process),
      peq_w p1 p2 -> guardP (S n) m p1 -> guardP (S n) m p2).
    {
      intros. specialize(IHm n p0 p3). apply IHm; try easy.
    }
    inversion H0. subst.
    - inversion H. constructor.
    - subst. inversion H. subst. constructor. apply IHn with (p1 := g); try easy.
    - subst. inversion H. subst. constructor.
      revert H6 H3. clear H0 H. revert ys.
      induction lis; intros.
      - destruct ys; try easy.
      - destruct ys; try easy. inversion H6. subst. clear H6. inversion H3. subst. clear H3.
        specialize(IHlis ys H7 H5). constructor; try easy.
        destruct H4. left. easy.
        destruct H as (p1,(p2,(Ha,(Hb,Hc)))). subst.
        destruct H2; try easy. destruct H as (g1,(Hd,He)). inversion Hd. subst.
        right. exists p2. split. easy.
        apply IHn with (p1 := g1); try easy.
    - subst. inversion H. subst.
      constructor. apply H1 with (p1 := P); try easy. apply H1 with (p1 := Q); try easy.
    - subst. inversion H. subst.
      assert(exists Q', substitutionP 0 0 0 (p_rec p0) p0 Q' /\ peq_w Q Q').
      {
        apply peq_after_subst with (g1 := g) (g := p_rec g); try easy.
      }
      destruct H2 as (Q1,(Ha,Hb)).
      apply gp_rec with (Q := Q1); try easy.
      apply H1 with (p1 := Q); try easy.
Qed.

Lemma guardP_subst_expr : forall y v j k,
    (forall n : fin, exists m : fin, guardP n m y) -> 
    (forall n : fin, exists m : fin, guardP n m (subst_expr_proc y v j k)).
Proof.
  intros.
  apply guardP_peq_w with (p1 := y); try easy.
  clear H n. revert v j k.
  induction y using process_ind_ref; intros; try easy.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. constructor. apply IHy; try easy.
  - simpl. constructor.
    revert H. revert pt v j k. induction llp; intros; try easy.
    - inversion H. subst. clear H. specialize(IHllp pt v j k H3). constructor; try easy.
      clear H3 IHllp.
      destruct a.
      - right. exists p. exists (subst_expr_proc p v (S j) (S k)). split. easy. split. easy.
        apply H2; try easy.
      - left. easy.
  - simpl. constructor.
    apply IHy1. apply IHy2.
  - simpl. constructor. apply IHy.
Qed.

Theorem _3_21 : forall M M' G, typ_sess M G -> betaP M M' -> exists G', typ_sess M' G' /\ multiC G G'.
Proof.
  intros. revert H. revert G.
  induction H0; intros; try easy.
  (* R-COMM *)
  inversion H1. subst.
  - inversion H5. subst. clear H5. inversion H8. subst. clear H8. 
    inversion H7. subst. clear H7. inversion H10. subst. clear H10. clear H1.
    destruct H6. destruct H1. destruct H7. destruct H6. rename x into T. rename x0 into T'.
    destruct H7 as (H7, Ht). destruct H5 as (H5, Htt).
    - specialize(_a23_a q xs (p_recv q xs) nil nil T H5 (eq_refl (p_recv q xs))); intros. 
      destruct H8. destruct H8. destruct H10. destruct H11.
    - specialize(_a23_bf p l e Q (p_send p l e Q) nil nil T' H7 (eq_refl (p_send p l e Q))); intros.
      destruct H13. destruct H13. destruct H13. destruct H14. rename x0 into S. rename x1 into LT.
    
    specialize(_3_19_h q p l); intros.
    specialize(subtype_recv T q x H10); intros. destruct H17. subst.
    specialize(subtype_send T' p (extendLis l (Some (S, LT))) H15); intros. destruct H17. subst.
    rename x0 into LQ. rename x1 into LP.
    specialize(H16 G LP LQ S LT).
    specialize(_3_21_helper l xs x y H H11); intros. destruct H17. destruct H17. destruct H17.
    specialize(H16 x (x0, x1)). 
    assert(exists G' : gtt, gttstepC G G' q p l).
    apply H16; try easy. destruct H19. subst. rename x2 into G'. 
    assert(multiC G G').
    specialize(multiC_step G G' G' q p l); intros. apply H20; try easy. constructor.
    exists G'. split; try easy. clear H20.
    clear H16.
    specialize(wfgC_after_step G G' q p l H2 H19); intros. 
    assert(wfgC G').
    intros. apply H16.
    unfold projectableA. intros.
    specialize(decidable_isgPartsC G pt H2); intros. unfold Decidable.decidable in H20.
    destruct H20.
    specialize(H3 pt H20).
    - unfold InT in H3. simpl in H3.
      - destruct H3. subst. exists (ltt_recv q LQ). easy.
      - destruct H3. subst. exists (ltt_send p LP). easy.
      - specialize(_3_21_helper_3 M G pt); intros. apply H21; try easy.
    - unfold not in H20. exists ltt_end. pfold. constructor; try easy.
    constructor; try easy.
    - intros.
      apply H3; try easy.
      - specialize(part_after_step G G' q p pt l LP LQ); intros. 
        apply H22; try easy.
    specialize(projection_step_label G G' q p l LP LQ); intros.
    assert(exists (LS LS' : sort) (LT LT' : ltt), onth l LP = Some (LS, LT) /\ onth l LQ = Some (LS', LT')).
    apply H21; try easy.
    destruct H22 as (SL,(SL',(TL,(TL',(H22,H23))))).
    
    specialize(_a_29_s G q p LP LQ SL TL SL' TL' l H2 H6 H22 H1 H23); intros.
    destruct H24 as (Gl,(ctxG,(SI,(Sn,(Ha,(Hb,(Hc,(Hd,(He,(Hf,Hg)))))))))).
    specialize(_3_21_helper_1 H23 H17 H10); intros.
    specialize(_3_21_helper_2 H15 H22); intros. 
    constructor. constructor.
    - constructor.
      specialize(_3_19_2_helper q p l G G' LP LQ SL TL SL' TL'); intros.
      assert(projectionC G' p TL'). apply H26; try easy. clear H26. 
      exists TL'. split; try easy.
      split.
      apply _a24 with (S := x0); try easy.
      - apply tc_sub with (t := x1); try easy.
        specialize(typable_implies_wfC H5); intros.
        specialize(wfC_recv H26 H23); try easy.
      - apply sc_sub with (s := S); try easy.
        apply expr_typ_step with (e := e); try easy.
        apply sstrans with (s2 := SL'); try easy.
        apply sstrans with (s2 := Sn); try easy. 
        apply sstrans with (s2 := SL); try easy.
      - specialize(guardP_cont_recv_n l xs y q Htt H); intros.
        specialize(guardP_subst_expr y (e_val v) 0 0); intros. apply H28; try easy.
    - constructor.
      specialize(_3_19_1_helper q p l G G' LP LQ SL TL SL' TL'); intros.
      assert(projectionC G' q TL). apply H26; try easy. clear H26.
      exists TL. split; try easy. split.
      - apply tc_sub with (t := LT); try easy.
        specialize(typable_implies_wfC H7); intros.
        specialize(wfC_send H26 H22); try easy.
      - intros. specialize(Ht (Nat.succ n)). destruct Ht. inversion H26.
        subst. exists x2. easy.
    - specialize(_3_19_3_helper M q p G G' l LP LQ S LT x (x0, x1)); intros.
      inversion H4. subst. inversion H30. subst.
      specialize(Classical_Prop.not_or_and (q = p) (In p (flattenT M)) H29); intros. destruct H27.
      apply H26; try easy.

  (* T-COND *)
  inversion H0. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
  destruct H5. destruct H4. destruct H5 as (H5, Ha).
  specialize(_a23_c (p_ite e P Q) e P Q x nil nil H5 (eq_refl (p_ite e P Q))); intros.
  destruct H6. destruct H6. destruct H6. destruct H7. destruct H9. destruct H10. 
  exists G. split.
  apply t_sess; try easy. apply ForallT_par; try easy.
  apply ForallT_mono; try easy. exists x.
  split; try easy. split.
  apply tc_sub with (t := x0); try easy.
  specialize(typable_implies_wfC H5); try easy.
  - intros. specialize(Ha n). destruct Ha. inversion H12. subst. exists 0. constructor.
    subst. exists m. easy.
  apply multiC_refl.
  
  (* F-COND *)
  inversion H0. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
  destruct H5. destruct H4. destruct H5 as (H5, Ha).
  specialize(_a23_c (p_ite e P Q) e P Q x nil nil H5 (eq_refl (p_ite e P Q))); intros.
  destruct H6. destruct H6. destruct H6. destruct H7. destruct H9. destruct H10. 
  exists G. split.
  apply t_sess; try easy. apply ForallT_par; try easy.
  apply ForallT_mono; try easy. exists x.
  split; try easy. split.
  apply tc_sub with (t := x1); try easy.
  specialize(typable_implies_wfC H5); try easy.
  - intros. specialize(Ha n). destruct Ha. inversion H12. subst. exists 0. constructor.
    subst. exists m. easy.
  apply multiC_refl.
  
  (* R-STRUCT *)
  specialize(_a22_2 M1 M1' G H2 H); intros.
  specialize(IHbetaP G H3); intros. destruct IHbetaP. exists x. 
  destruct H4. split; try easy.
  specialize(_a22_2 M2' M2 x H4 H0); intros. easy.
Qed.