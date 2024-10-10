From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header type.global type.local type.isomorphism type.merge.
Require Import List String Coq.Arith.PeanoNat Relations.
Import ListNotations. 

Inductive isgParts : part -> global -> Prop := 
  | pa_sendp : forall p q l, isgParts p (g_send p q l)
  | pa_sendq : forall p q l, isgParts q (g_send p q l)
  | pa_mu    : forall p g,   isgParts p g -> isgParts p (g_rec g)
  | pa_sendr : forall p q r n s g lis, p <> r -> q <> r -> onth n lis = Some (s, g) -> isgParts r g -> isgParts r (g_send p q lis).
  
Definition isgPartsC (pt : part) (G : gtt) : Prop := 
    exists G', gttTC G' G /\ isgParts pt G'.

Inductive ishParts : part -> gtth -> Prop := 
  | ha_sendp : forall p q l, ishParts p (gtth_send p q l)
  | ha_sendq : forall p q l, ishParts q (gtth_send p q l)
  | ha_sendr : forall p q r n s g lis, p <> r -> q <> r -> onth n lis = Some (s, g) -> ishParts r g -> ishParts r (gtth_send p q lis).


Variant projection (R: gtt -> part -> ltt -> Prop): gtt -> part -> ltt -> Prop :=
  | proj_end : forall g r, 
               (isgPartsC r g -> False) -> 
               projection R g r (ltt_end)
  | proj_in  : forall p r xs ys,
               p <> r ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some(s, t) /\ R g r t)) xs ys ->
               projection R (gtt_send p r xs) r (ltt_recv p ys)
  | proj_out : forall r q xs ys,
               r <> q ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some(s, t) /\ R g r t)) xs ys ->
               projection R (gtt_send r q xs) r (ltt_send q ys)
  | proj_cont: forall p q r xs ys t,
               p <> q ->
               q <> r ->
               p <> r ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some t /\ R g r t)) xs ys ->
               isMerge t ys ->
               projection R (gtt_send p q xs) r t.

Definition projectionC g r t := paco3 projection bot3 g r t.

Lemma proj_mon: monotone3 projection.
Proof. unfold monotone3.
       intros.
       induction IN; intros.
       - constructor. easy.
       - try easy.
Admitted.

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
Admitted.

Lemma gttTC_after_subst : forall G G' G1,
    multiS betaG G G' -> 
    gttTC G G1 ->
    gttTC G' G1.
Proof.
  intros. revert H0. revert G1. induction H; intros.
  - inversion H. subst.
    pinversion H0. subst.
    specialize(subst_injG 0 0 (g_rec G) G y Q H3 H1); intros. subst.
    easy.
    apply gttT_mon.
  - apply IHmultiS. inversion H. subst.
    pinversion H1. subst.
    specialize(subst_injG 0 0 (g_rec G) G y Q H4 H2); intros. subst.
    easy.
    apply gttT_mon.
Qed.

Lemma triv_pt_p : forall p q x0,
    wfgC (gtt_send p q x0) -> 
    isgPartsC p (gtt_send p q x0).
Proof.
  intros. unfold wfgC in H.
  destruct H. destruct H. destruct H0. destruct H1.
  unfold isgPartsC in *.
  pinversion H; try easy. 
  - subst. exists (g_send p q xs). split. pfold. easy. constructor.
  - subst. specialize(guard_breakG G H1); intros. 
    destruct H5. destruct H5. destruct H6.
   
    destruct H7.
    - subst. 
      specialize(gttTC_after_subst (g_rec G) g_end (gtt_send p q x0) H5); intros.
      assert(gttTC g_end (gtt_send p q x0)). 
      apply H7. pfold. easy. pinversion H8. 
      apply gttT_mon.
    destruct H7. destruct H7. destruct H7.
    - subst.
      specialize(gttTC_after_subst (g_rec G) (g_send x1 x2 x3) (gtt_send p q x0) H5); intros.
      assert(gttTC (g_send x1 x2 x3) (gtt_send p q x0)).
      apply H7. pfold. easy.
      pinversion H8. subst.
      exists (g_send p q x3). split; try easy. pfold. easy.
      constructor.
    apply gttT_mon.
    apply gttT_mon.
Qed.


Lemma triv_pt_q : forall p q x0,
    wfgC (gtt_send p q x0) -> 
    isgPartsC q (gtt_send p q x0).
Proof.
  intros. unfold wfgC in H.
  destruct H. destruct H. destruct H0. destruct H1.
  unfold isgPartsC in *.
  pinversion H; try easy. 
  - subst. exists (g_send p q xs). split. pfold. easy. constructor.
  - subst. specialize(guard_breakG G H1); intros. 
    destruct H5. destruct H5. destruct H6.
   
    destruct H7.
    - subst. 
      specialize(gttTC_after_subst (g_rec G) g_end (gtt_send p q x0) H5); intros.
      assert(gttTC g_end (gtt_send p q x0)). 
      apply H7. pfold. easy. pinversion H8. 
      apply gttT_mon.
    destruct H7. destruct H7. destruct H7.
    - subst.
      specialize(gttTC_after_subst (g_rec G) (g_send x1 x2 x3) (gtt_send p q x0) H5); intros.
      assert(gttTC (g_send x1 x2 x3) (gtt_send p q x0)).
      apply H7. pfold. easy.
      pinversion H8. subst.
      exists (g_send p q x3). split; try easy. pfold. easy.
      constructor.
    apply gttT_mon.
    apply gttT_mon.
Qed.


Lemma proj_inj_p [G p T T' ctxG q Gl] :  
  Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg))
       ctxG ->
  (ishParts p Gl -> False) ->
  typ_gtth ctxG Gl G ->
  projectionC G p T -> projectionC G p T' -> T = T'.
Admitted.

Lemma proj_inj_q [G p T T' ctxG q Gl] :  
  Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg))
       ctxG ->
  (ishParts q Gl -> False) -> 
  typ_gtth ctxG Gl G ->
  projectionC G q T -> projectionC G q T' -> T = T'.
Admitted.


Lemma _a_29_10 : forall G p q PT S T n,
    projectionC G p PT ->
    subtypeC (ltt_send q (extendLis n (Some (S, T)))) PT ->
    exists (xs : list (option (sort * ltt))) (Sk : sort) (Tk : ltt), projectionC G p (ltt_send q xs) /\ 
    onth n xs = Some(Sk, Tk) /\ subsort S Sk /\ subtypeC T Tk.
Proof.
  intros.
  specialize(subtype_send PT q (extendLis n (Some (S, T))) H0); intros.
  destruct H1. subst.
  specialize(subtype_send_inv q (extendLis n (Some (S,T))) x H0); intros.
  exists x.
  assert (exists Sk Tk, onth n x = Some (Sk, Tk) /\ subsort S Sk /\ subtypeC T Tk).
  {
    clear H0. clear H. revert G p q S T x H1.
    induction n; intros; try easy.
    - destruct x; try easy.
      simpl in *. inversion H1. subst. destruct H3; try easy.
      destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H2.
      inversion H. subst.
      exists x1. exists x3. try easy.
    - destruct x; try easy. apply IHn; try easy.
      inversion H1; try easy.
  }
  destruct H2. destruct H2. destruct H2. destruct H3.
  exists x0. exists x1. try easy.
Qed.

Lemma _a_29_11_helper : forall G p q x, 
    wfgC G -> 
    projectionC G p (ltt_send q x) -> 
    exists G' ctxJ,
      typ_gtth ctxJ G' G /\ (ishParts p G' -> False) /\
      List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg)) ctxJ.
Proof.
  intros.
  unfold wfgC in H. destruct H as [G' H1].
  destruct H1. destruct H1. destruct H2. 
  revert H H1 H2 H3 H0. revert G p q x.
  induction G' using global_ind_ref; intros; try easy.
  
Admitted.

Lemma _a_29_11 : forall G p q x,
    wfgC G ->
    projectionC G p (ltt_send q x) ->
    exists G' ctxJ, 
      typ_gtth ctxJ G' G /\ (ishParts p G' -> False) /\
      List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg /\
        List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t g', u = Some(s, g') /\ v = Some(s, t) /\
          projectionC g' p t
        )) lsg x 
      )) ctxJ.
Proof.
    intros.
Admitted.

Lemma some_onth_implies_In {A} : forall n (ctxG : list (option A)) G,
    onth n ctxG = Some G -> In (Some G) ctxG.
Proof.
  induction n; intros; try easy.
  - destruct ctxG; try easy. simpl in *.
    left. easy.
  - destruct ctxG; try easy. simpl in *.
    right. apply IHn; try easy.
Qed.

Lemma _a_29_1314 : forall G G' p q QT xs ctxG x,
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
                  u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x))
        ctxG -> 
  typ_gtth ctxG G' G ->
  (ishParts p G' -> False) ->
  projectionC G q QT ->
  subtypeC (ltt_recv p xs) QT -> 
  exists ys, projectionC G q (ltt_recv p ys) /\ List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t'))) ys x.
Proof.
  
Admitted.


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
      clear H2 H1 H0 H3 H4 H10 H8 H12 H5 H14 H13 H6 H H7 H9 H15 H16 H17 H21 H22 H23 H24. clear H27 H25 H28 H32 H11.
      clear r s x1 x ys xs ctxG.
      revert H18 H26 H31. revert p q x0 x2 ys0 ys1 ys2.
      induction n; intros; try easy.
      - destruct ys0; try easy.
        destruct ys1; try easy.
        destruct ys2; try easy.
        simpl in *.
        inversion H26. subst. inversion H31. subst. clear H26 H31.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. inversion H. subst.
        destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2. inversion H0. subst.
        pclearbot. exists x4. exists x3. easy.
      - destruct ys0; try easy.
        destruct ys1; try easy.
        destruct ys2; try easy.
        simpl in *.
        inversion H26. subst. inversion H31. subst. clear H26 H31.
        apply IHn with (x0 := x0) (ys0 := ys0) (ys1 := ys1) (ys2 := ys2); try easy.
    }
    destruct H19. destruct H19. destruct H19. destruct H20. destruct H29.
    specialize(_a_29_part_helper_recv n ys1 x4 p ys H30 H27); intros. destruct H33. subst.
    specialize(_a_29_part_helper_send n ys2 x3 q x H29 H32); intros. destruct H33. subst.
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
  
  
Admitted.

(* 
Lemma _a_29_helper : forall n x Sk Tk lsg p,
    onth n x = Some (Sk, Tk) ->
    Forall2 
        (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
         u0 = None /\ v = None \/
         (exists (s : sort) (t : ltt) (g' : gtt),
            u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x ->
    exists Glsg, onth n lsg = Some (Sk, Glsg) /\ projectionC Glsg p Tk.
Proof.
  induction n; intros; try easy.
  - destruct x; try easy.
    destruct lsg; try easy.
    simpl in *. subst.
    inversion H0. subst. destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H1. inversion H1. subst.
    exists x2. split; try easy.
  - destruct x; try easy. destruct lsg; try easy.
    inversion H0. subst.
    simpl in *. apply IHn with (x := x); try easy.
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

Lemma _a_29_helper4 : forall n xs ys S' Sk T' x1,
    onth n xs = Some (S', T') ->
    onth n ys = Some (Sk, x1) ->
    Forall2R
        (fun u v : option (sort * ltt) =>
         u = None \/
         (exists (s s' : sort) (t t' : ltt),
            u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) ys xs -> 
    subtypeC T' x1.
Proof.
  induction n; intros.
  - destruct xs; try easy. destruct ys; try easy.
    inversion H1. subst. simpl in *. subst.
    destruct H5; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H2.
    inversion H0. inversion H. subst. easy.
  - destruct xs; try easy. destruct ys; try easy.
    inversion H1. subst. specialize(IHn xs ys S' Sk). apply IHn; try easy.
Qed. *)
(* 
Lemma _a_29 : forall G p q PT QT S T S' T' xs n, 
    wfgC G -> 
    projectionC G p PT -> 
    subtypeC (ltt_send q (extendLis n (Some (S, T)))) PT ->
    projectionC G q QT -> 
    onth n xs = Some (S', T') ->
    subtypeC (ltt_recv p xs) QT -> 
    exists G' ctxG SI Sn, 
    typ_gtth ctxG G' G /\ (* 1 *)
    (ishParts p G' -> False) /\ (ishParts q G' -> False) /\ (* 2 *)
    List.Forall (fun u => u = None \/ (exists g lsg, u = Some g /\ g = gtt_send p q lsg /\
      (exists s' Gjk Tp Tq, onth n lsg = Some (s', Gjk) /\ projectionC Gjk p Tp /\ subtypeC T Tp /\ projectionC Gjk q Tq /\ subtypeC T' Tq) /\
      List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g', u = Some(s, g') /\ v = Some s)) lsg SI
    )) ctxG /\ (* 3 5 6 *)
    (onth n SI = Some Sn) /\ subsort S Sn /\ subsort Sn S'. (* 5 6 *)
Proof.
  intros.
  specialize(_a_29_10 G p q PT S T n H0 H1); intros.
  destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. destruct H7.
  rename x0 into Sk. rename x1 into Tk.
  assert (PT = (ltt_send q x)).
  {
(*    specialize(proj_inj H0 H5); intros. *)
    admit.
  } 
  subst. clear H5. (* _a_29_10 *)
  
  specialize(_a_29_11 G p q x H H0); intros.
  destruct H5. destruct H5. destruct H5. destruct H9.
  
  rename x1 into ctxG. rename x0 into G'.
  exists G'. exists ctxG.
  assert (exists (SI : seq.seq (option sort)),
    List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t, u = Some s /\ v = Some (s, t))) SI x).
  {
    clear H H1 H0 H2 H3 H4 H8 H5 H6 H7 H9 H10. 
    clear G p q QT S' T' T xs G' ctxG S n Sk Tk.
    induction x; intros; try easy.
    - exists []. easy.
    - destruct IHx; try easy. destruct a.
      - destruct p. exists (Some s :: x0). constructor; try easy.
        right. exists s. exists l. easy.
      - exists (None :: x0). constructor; try easy.
        left. easy.
  }
  destruct H11 as [SI H11]. exists SI.
  exists Sk. split. easy.
  split. easy.
  assert (onth n SI = Some Sk /\ subsort S Sk).
  {
    clear H1 H0 H10 H3.
    revert H11 H6 H7. revert n x SI. induction n; intros; try easy.
    - destruct SI; try easy. destruct x; try easy.
      destruct x; try easy. inversion H11. subst.
      simpl in H6. subst.
      destruct H10; try easy. destruct H0. destruct H0. destruct H0. inversion H1. subst. easy.
    - destruct SI; try easy. destruct x; try easy.
      destruct x; try easy.
      inversion H11. subst. simpl.
      apply IHn with (x := x); try easy. 
  }
  specialize(_a_29_1314 G G' p q QT xs ctxG x H10 H5 H9 H2 H4); intros; try easy.
  destruct H13. destruct H13. rename x0 into ys.
  
  assert (ltt_recv p ys = QT).
  {
    admit.
(*     specialize(proj_inj H13 H2); intros. *)
  } 
 
  subst. clear H13.
  clear H7.
  
  specialize(_a_29_part ctxG G' G p q x ys H5 H0 H2 H9); intros.
  split. easy.
  assert (subsort Sk S').
  {
    clear H7 H12 H10 H9 H5 H8 H2 H0 H1 H.
    specialize(subtype_recv_inv p xs ys H4); intros. clear H4.
    revert H11 H14 H H3 H6. clear G p q S T G' ctxG.
    revert S' T' xs x ys Sk Tk SI.
    induction n; intros; try easy.
    - destruct xs; try easy.
      destruct x; try easy. 
      destruct SI; try easy. destruct ys; try easy.
      simpl in *.
      subst.
      inversion H14. subst. clear H14. inversion H11. subst. clear H11.
      inversion H. subst. clear H.
      destruct H4; try easy. destruct H. destruct H. destruct H. inversion H0. subst.
      destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. inversion H1. subst.
      destruct H6; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H2. destruct H3. 
      inversion H. inversion H2. subst. easy.
    - destruct xs; try easy.
      destruct x; try easy.
      destruct SI; try easy. destruct ys; try easy.
      simpl in *. 
      inversion H14. subst. clear H14. inversion H11. subst. clear H11.
      inversion H. subst. clear H.
      specialize(IHn S' T' xs x ys Sk Tk SI). apply IHn; try easy.
  }
  split; try easy.
  
  specialize(subtype_recv_inv p xs ys H4); intros.
  specialize(subtype_send_inv q (extendLis n (Some (S, T))) x H1); intros.
  
  specialize(_a_29_16 G' ctxG G p q ys x H2 H10 H9 H7 H5); intros.
  
  specialize(Forall_forall (fun u : option gtt =>
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
              (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
               u0 = None /\ v = None \/
               (exists (s : sort) (t : ltt) (g' : gtt),
                  u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' q t)) lsg ys)) ctxG); intros.
  destruct H18. specialize(H18 H17). clear H17 H19 H10.
  
  apply Forall_forall; intros.
  specialize(H18 x0 H10). destruct H18. left. easy.
  destruct H17. destruct H17. destruct H17. destruct H18. destruct H19.
  right. exists (gtt_send p q x2). exists x2. subst.
  split. easy. split. easy. 
  rename x2 into lsg.
  specialize(_a_29_helper n x Sk Tk lsg p H6 H19); intros. 
  destruct H17. destruct H17.
  specialize(_a_29_helper2 lsg SI x p H19 H11); intros. 
  split; try easy. clear H21 H19.
  exists Sk. exists x0. exists Tk.
  specialize(_a_29_helper3 n lsg x0 Sk ys q H17 H20); intros.
  destruct H19. destruct H19. exists x1. split. easy.
  split. easy. split. easy. split. easy.
  specialize(_a_29_helper4 n xs ys S' Sk T' x1); intros. apply H22; try easy.
Admitted.
 *)

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
Admitted.


Lemma wfgC_after_step : forall G G' p q n, wfgC G -> gttstepC G G' p q n -> wfgC G'.
Proof.
Admitted.

Lemma ltt_after_betaL : forall G G' T,
  lttTC G T -> multiS betaL G G' -> lttTC G' T.
Proof.
  intros. revert H. revert T. induction H0; intros; try easy.
  inversion H. subst. pfold. 
  pinversion H0; try easy. subst.
  specialize(subst_injL 0 0 (l_rec G) G y Q H3 H1); intros. subst. easy.
  apply lttT_mon.
  apply IHmultiS.
  inversion H. subst. 
  pinversion H1. subst.
  specialize(subst_injL 0 0 (l_rec G) G y Q H4 H2); intros. subst. pfold. easy.
  apply lttT_mon.
Qed.

Lemma gtt_after_betaL : forall G G' T,
  gttTC G T -> multiS betaG G G' -> gttTC G' T.
Proof.
  intros. revert H. revert T. induction H0; intros; try easy.
  inversion H. subst. pfold. 
  pinversion H0; try easy. subst.
  specialize(subst_injG 0 0 (g_rec G) G y Q H3 H1); intros. subst. punfold H4.
  apply gttT_mon.
  apply gttT_mon.
  apply IHmultiS.
  inversion H. subst. 
  pinversion H1. subst.
  specialize(subst_injG 0 0 (g_rec G) G y Q H4 H2); intros. subst. pfold. punfold H5. 
  apply gttT_mon.
  apply gttT_mon.
Qed.

Lemma part_after_step_helper : forall G1 q p x0,
    gttTC G1 (gtt_send q p x0) -> 
    (forall n : fin, exists m : fin, guardG n m G1) -> 
    exists ys, gttTC (g_send q p ys) (gtt_send q p x0).
Proof.
  intros. pinversion H; try easy. subst.
  - exists xs. pfold. easy.
  - subst. specialize(guard_breakG G H0); intros.
    destruct H3. destruct H3. destruct H4.
    specialize(gtt_after_betaL (g_rec G) x (gtt_send q p x0)); intros.
    assert(gttTC x (gtt_send q p x0)). 
    apply H6; try easy. pfold. easy.
    destruct H5. pinversion H7; try easy. subst. easy. subst. easy.
    apply gttT_mon.
    destruct H5. destruct H5. destruct H5. subst.
    pinversion H7; try easy. subst. exists x3. pfold. easy.
    apply gttT_mon.
    apply gttT_mon.
Qed.

Lemma part_after_step : forall G G' q p pt l LP LQ,
        wfgC G ->
        gttstepC G G' q p l -> 
        projectionC G p (ltt_recv q LQ) ->
        projectionC G q (ltt_send p LP) ->
        isgPartsC pt G' -> 
        isgPartsC pt G.
Proof.
  intros.
  specialize(_a_29_11 G q p LP H H2); intros.
  destruct H4. destruct H4. rename x0 into ctxG. rename x into Gl.
  revert H4. revert H0 H1 H2 H3 H. revert ctxG LP LQ l p q pt G G'.
  induction Gl using gtth_ind_ref; intros.
  - destruct H4. destruct H5. 
    inversion H4. subst.
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
    destruct H7. specialize(H7 H6). clear H8 H6. 
    specialize(some_onth_implies_In n ctxG G H9); intros. 
    specialize(H7 (Some G) H6). destruct H7; try easy. destruct H7. destruct H7. destruct H7.
    destruct H8. inversion H7. subst.
    pinversion H0; try easy. subst. clear H14 H15.
    unfold wfgC in H. destruct H. destruct H. rename x into G1.
    unfold isgPartsC. destruct H8. destruct H11.
    specialize(part_after_step_helper G1 q p x0 H H11); intros.
    destruct H13.
    (* some notion of overwriting x with the unfolded pt item *)
    (* 
     exists (g_send q p x).
    - split; try easy.
      unfold isgPartsC in H3. destruct H3. destruct H3.
      clear H6 H10 H9 H5 H12 H11 H H8. clear G1.
      
    apply step_mon.
  - destruct H5. destruct H6. inversion H5. subst.
    rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
     *)
    
  
  
Admitted. (* probaly induction on Gl, base case ok, should be movable into everything later *)


Lemma in_some_implies_onth {A} : forall (x : A) xs,
    In (Some x) xs -> exists n, onth n xs = Some x.
Proof.
  intros. revert H. revert x. 
  induction xs; intros; try easy.
  simpl in *. destruct H. exists 0. easy.
  specialize(IHxs x H). destruct IHxs. exists (Nat.succ x0). easy.
Qed.


Lemma _3_19_step_helper : forall s s' ys,
    wfgC (gtt_send s s' ys) -> s <> s' -> List.Forall (fun u => u = None \/ exists s g, u = Some(s, g) /\ wfgC g) ys.
Proof.
  intros.
  apply Forall_forall; intros.
  destruct x.
  - right. 
    destruct p. exists s0. exists g. split; try easy.
    specialize(in_some_implies_onth (s0, g) ys H1); intros. destruct H2. rename x into n.
    assert(gttstepC (gtt_send s s' ys) g s s' n).
    {
      pfold. apply steq with (s := s0); try easy.
    }
    specialize(wfgC_after_step (gtt_send s s' ys) g s s' n H H3); intros. easy.
  - left. easy.
Qed.


Lemma wfG_after_beta : forall G G', 
      wfG G ->
      multiS betaG G G' -> 
      wfG G'.
Proof.
  intros. revert H. induction H0; intros; try easy.
  - inversion H. subst.
    specialize(wfG_after_subst y (g_rec G) G 0 0); intros.
    apply H2; try easy. inversion H0. easy.
  - apply IHmultiS. clear H0 IHmultiS.
    inversion H. subst.
    specialize(wfG_after_subst y (g_rec G) G 0 0); intros.
    apply H2; try easy. inversion H1. easy.
Qed.



Inductive isgParts_depth : fin -> part -> global -> Prop := 
  | dpth_p : forall p q lis, isgParts_depth 0 p (g_send p q lis)
  | dpth_q : forall p q lis, isgParts_depth 0 q (g_send p q lis)
  | dpth_mu : forall n pt g, isgParts_depth n pt g -> isgParts_depth (S n) pt (g_rec g)
  | dpth_c : forall p q pt s g lis n k, p <> pt -> q <> pt -> onth k lis = Some(s, g) -> isgParts_depth n pt g -> isgParts_depth (S n) pt (g_send p q lis).


Lemma isgParts_depth_exists : forall r Gl,
    isgParts r Gl -> exists n, isgParts_depth n r Gl.
Proof.
  induction Gl using global_ind_ref; intros; try easy.
  inversion H0.
  - subst. exists 0. constructor.
  - subst. exists 0. constructor.
  - subst. 
    specialize(some_onth_implies_In n lis (s, g) H7); intros.
    specialize(Forall_forall (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\
          (isgParts r g -> exists n : fin, isgParts_depth n r g))) lis); intros.
    destruct H2. specialize(H2 H). clear H H3.
    specialize(H2 (Some (s, g)) H1).
    destruct H2; try easy. destruct H. destruct H. destruct H. inversion H. subst. clear H.
    specialize(H2 H8). destruct H2.
    exists (S x1). apply dpth_c with (s := x) (g := x0) (k := n); try easy.
  - inversion H. subst. specialize(IHGl H2). destruct IHGl. exists (S x). constructor. easy.
Qed.

Lemma isgParts_depth_back : forall G n r,
      isgParts_depth n r G -> isgParts r G.
Proof.
  induction G using global_ind_ref; intros; try easy.
  inversion H0. 
  - subst. constructor.
  - subst. constructor.
  - subst. 
    specialize(some_onth_implies_In k lis (s, g) H8); intros.
    specialize(Forall_forall (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\
          (forall (n : fin) (r : string),
           isgParts_depth n r g -> isgParts r g))) lis); intros.
    destruct H2. specialize(H2 H). clear H H3.
    specialize(H2 (Some (s, g)) H1). destruct H2; try easy. destruct H. destruct H. destruct H.
    inversion H. subst.
    specialize(H2 n0 r H9). 
    apply pa_sendr with (n := k) (s := x) (g := x0); try easy.
  inversion H. subst.
  - specialize(IHG n0 r H3). constructor. easy.
Qed.
     

Lemma pmergeCR_helper : forall k lis s g ys,
      onth k lis = Some (s, g) -> 
      Forall2
        (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : global) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g'))
        lis ys -> 
      exists g', gttTC g g' /\ onth k ys = Some (s, g').
Proof.
  induction k; intros.
  - destruct lis; try easy.
    destruct ys; try easy. inversion H0. subst.
    simpl in H. subst. destruct H4; try easy. destruct H. destruct H. destruct H. destruct H. destruct H1. inversion H. subst.
    exists x1. split; try easy. destruct H2; try easy.
  - destruct lis; try easy. destruct ys; try easy.
    inversion H0. subst.
    specialize(IHk lis s g ys H H6).
    easy.
Qed.

Lemma pmergeCR_helper2 : forall k s ys g' ys0 r,
          onth k ys = Some (s, g') -> 
          Forall2
            (fun (u : option (sort * gtt)) (v : option ltt) =>
             u = None /\ v = None \/
             (exists (s : sort) (g : gtt) (t : ltt),
                u = Some (s, g) /\
                v = Some t /\ upaco3 projection bot3 g r t)) ys ys0 ->
          Forall (fun u : option ltt => u = None \/ u = Some ltt_end) ys0 -> 
          projectionC g' r ltt_end.
Proof.
  induction k; intros; try easy.
  - destruct ys; try easy. destruct ys0; try easy.
    inversion H0. inversion H1. subst. clear H0 H1 H7 H11.
    simpl in H. subst. destruct H5; try easy. 
    destruct H. destruct H. destruct H. destruct H. destruct H0. inversion H. subst. 
    destruct H10; try easy. inversion H0. subst. destruct H1; try easy.
  - destruct ys; try easy. destruct ys0; try easy.
    inversion H0. inversion H1. subst. clear H0 H1.
    specialize(IHk s ys g' ys0 r). apply IHk; try easy.
Qed.

Lemma subst_parts_depth : forall m n k r g g' Q,
      subst_global m n (g_rec g) g' Q -> 
      isgParts_depth k r g -> 
      isgParts_depth k r Q.
Proof.
  intros. revert H0. 
Admitted.

Lemma pmergeCR: forall G r,
          wfgC G ->
          projectionC G r ltt_end ->
          (isgPartsC r G -> False).
Proof. intros.
  
  unfold isgPartsC in H1. destruct H1. 
  destruct H1. rename x into Gl.
  specialize(isgParts_depth_exists r Gl H2); intros. destruct H3. rename x into n. 
  clear H2 H.
  revert H0 H1 H3. revert G r Gl.
  induction n; intros; try easy.
  - inversion H3. 
    - subst. pinversion H1; try easy.
      subst. pinversion H0; try easy. 
      subst. apply H. unfold isgPartsC. exists (g_send r q lis). split; try easy.
      pfold. easy. constructor.
      apply proj_mon.
      apply gttT_mon.
    - subst. pinversion H1; try easy.
      subst. pinversion H0; try easy. 
      subst. apply H. unfold isgPartsC. exists (g_send p r lis). split; try easy.
      pfold. easy. constructor.
      apply proj_mon.
      apply gttT_mon.
  - inversion H3. 
    - subst.
      pinversion H1; try easy. subst.
      specialize(IHn G r Q). apply IHn; try easy.
      specialize(subst_parts_depth 0 0 n r g g Q); intros. apply H; try easy.
      apply gttT_mon.
    - subst.
      pinversion H1; try easy. subst.
      - specialize(pmergeCR_helper k lis s g ys H5 H10); intros.
        destruct H. destruct H. rename x into g'.
        specialize(IHn g' r g). apply IHn; try easy.
        pinversion H0; try easy.
        - subst.
          assert False. apply H8. unfold isgPartsC. exists (g_send p q lis). split; try easy.
          - pfold. easy.
          - apply isgParts_depth_back with (n := S n); try easy. easy.
        - subst.
          specialize(triv_merge_ltt_end ys0 H18); intros.
          clear H18.
          specialize(pmergeCR_helper2 k s ys g' ys0 r); intros. apply H9; try easy.
      apply proj_mon.
      apply gttT_mon.
Qed.






