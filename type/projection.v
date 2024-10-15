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
       - constructor. easy. 
         revert ys H0.
         induction xs; intros.
         + subst. inversion H0. constructor.
         + subst. inversion H0. constructor.
           destruct H3 as [(H3a, H3b) | (s,(g,(t,(Ht1,(Ht2,Ht3)))))].
           subst. left. easy.
           subst. right. exists s. exists g. exists t.
           split. easy. split. easy. apply LE. easy.
           apply IHxs. easy.
       - constructor. easy.
         revert ys H0.
         induction xs; intros.
         + subst. inversion H0. constructor.
         + subst. inversion H0. constructor.
           destruct H3 as [(H3a, H3b) | (s,(g,(t,(Ht1,(Ht2,Ht3)))))].
           subst. left. easy.
           subst. right. exists s. exists g. exists t.
           split. easy. split. easy. apply LE. easy.
           apply IHxs. easy.
       - apply proj_cont with (ys := ys); try easy.
         revert H2. apply Forall2_mono; intros.
         destruct H2. left. easy.
         destruct H2. destruct H2. destruct H2. destruct H2. destruct H4. subst.
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


Inductive usedCtx : (list (option gtt)) -> gtth -> Prop := 
  | used_hol : forall n G, usedCtx (extendLis n (Some G)) (gtth_hol n)
  | used_con : forall p q s x xs ctxG0 ctxG1 ctxG2, Forall3S (fun u v w => 
                  (u = None /\ v = None /\ w = None) \/
                  (exists t, u = None /\ v = Some t /\ w = Some t) \/
                  (exists t, u = Some t /\ v = None /\ w = Some t) \/
                  (exists t, u = Some t /\ v = Some t /\ w = Some t)) ctxG0 ctxG1 ctxG2 ->
      usedCtx ctxG0 x -> usedCtx ctxG1 (gtth_send p q xs) -> usedCtx ctxG2 (gtth_send p q (Some (s, x) :: xs)).

Lemma balanced_to_tree : forall G p,
    balancedG G -> 
    exists G' ctxG, 
       typ_gtth ctxG G' G /\ (ishParts p G' -> False) /\
       List.Forall (fun u => u = None \/ (exists q lsg, u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some (gtt_end))) ctxG /\ usedCtx ctxG G'.
Admitted.

Lemma balanced_cont : forall [lsg p q],
    balancedG (gtt_send p q lsg) -> List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ balancedG g)) lsg.
Admitted.

Lemma balanced_cont_b : forall ys0 s s',
    Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g))
       ys0 -> 
    balancedG (gtt_send s s' ys0).
Admitted.

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

Lemma wfgC_after_step : forall G G' p q n, wfgC G -> gttstepC G G' p q n -> wfgC G'. 
Proof.
  intros. 
  unfold wfgC in *.
  destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))).
  specialize(balanced_to_tree G p Hd); intros.
  destruct H as (Gt,(ctxG,(Hta,(Htb,(Htc,Htd))))).
  clear Htd.
  revert Htc Htb Hta H0 Hd Hc Hb Ha.
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
      clear H14 H13 Hb Hc He H16 H11 H10 H9 H8 H5 H4 H6 Hta H0 Hd.
      apply Forall_forall; intros. 
      destruct x.
      - specialize(in_some_implies_onth p0 ys0 H0); intros. destruct H4 as (n0 ,H4). clear H0.
        right. destruct p0. exists s0. exists g. split. easy.
        revert H4 H3 H1 H15 H2 H17 H7 Htc H Htb.
        revert g s0 lis ys ys0 ctxG n p q xs s s'.
        induction n0; intros.
        - destruct ys0; try easy. destruct ys; try easy. destruct lis; try easy.
          destruct xs; try easy.
          inversion H3. subst. clear H3. inversion H1. subst. clear H1. inversion H15. subst. clear H15.
          inversion H2. subst. clear H2. inversion H17. subst. clear H17. inversion H7. subst. clear H7.
          inversion H. subst. clear H.
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
          specialize(Hq g9 g2 p q n g8 ctxG). unfold wfgC.
          apply Hq; try easy. 
          specialize(ishParts_x Htb); try easy.
          destruct Hc; try easy.
          destruct Hi; try easy.
        - destruct ys0; try easy. destruct ys; try easy. destruct lis; try easy.
          destruct xs; try easy.
          inversion H3. subst. clear H3. inversion H1. subst. clear H1. inversion H15. subst. clear H15.
          inversion H2. subst. clear H2. inversion H17. subst. clear H17. inversion H7. subst. clear H7.
          inversion H. subst. clear H.
          specialize(IHn0 g s0 lis ys ys0 ctxG n p q xs s s').
          apply IHn0; try easy.
          specialize(ishParts_hxs Htb); try easy.
        left. easy.
    }
    specialize(wfgC_after_step_helper2 lis ys ys0 n p q H13 H2 H17); intros.
    clear H3 H1 H15 H2 Hb Hc He H17 H16 H11 H10 H9 H8 H5 H4 H7 Hta H0 Hd Htb Htc H H6 H13.
    clear p q xs n ctxG ys lis. rename H14 into H. rename H12 into H1.
    assert(exists xs, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ gttTC g g')) xs ys0 /\ 
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ balancedG g)) ys0 /\
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfG g)) xs /\
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ (forall n, exists m, guardG n m g))) xs).
    {
      clear H. revert H1. clear H18. revert ys0. clear s s'.
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
    - apply balanced_cont_b; try easy.
    apply gttT_mon.
    apply step_mon.
Qed.


Lemma wfgC_after_step_all : forall [ys s s'],
    s <> s' -> wfgC (gtt_send s s' ys) -> List.Forall (fun u => u = None \/ (exists st g, u = Some(st, g) /\ wfgC g)) ys.
Proof.
  intros. apply Forall_forall; intros.
  destruct x. 
  - specialize(in_some_implies_onth p ys H1); intros.
    destruct H2. rename x into l. clear H1. 
    right. destruct p. exists s0. exists g. split. easy.
    specialize(wfgC_after_step (gtt_send s s' ys) g s s' l); intros. apply H1; try easy.
    pfold. apply steq with (s := s0); try easy.
  - left. easy.
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


Lemma subst_parts_helper : forall k0 xs s g0 r n0 lis m n g,
      onth k0 xs = Some (s, g0) -> 
      isgParts_depth n0 r g0 ->
      Forall2
       (fun u v : option (sort * global) =>
        u = None /\ v = None \/
        (exists (s : sort) (g0 g' : global),
           u = Some (s, g0) /\ v = Some (s, g') /\ subst_global m n (g_rec g) g0 g')) xs lis -> 
      Forall
      (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\
          (forall (m n k : fin) (r : string) (g0 g' : global),
           isgParts_depth k r g' -> subst_global m n (g_rec g0) g' g -> isgParts_depth k r g))) lis -> 
      exists g', onth k0 lis = Some (s, g') /\ isgParts_depth n0 r g'.
Proof.
  induction k0; intros; try easy.
  - destruct xs; try easy.
    simpl in H. subst. destruct lis; try easy. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    clear H4 H7. destruct H5; try easy. destruct H. destruct H. destruct H. destruct H.
    destruct H1. inversion H. subst.
    destruct H3; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
    specialize(H3 m n n0 r g x0 H0 H2).
    exists x3. split; try easy.
  - destruct xs; try easy. destruct lis; try easy. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    specialize(IHk0 xs s g0 r n0 lis m n g). apply IHk0; try easy.
Qed.

Lemma subst_parts_depth : forall m n k r g g' Q,
      subst_global m n (g_rec g) g' Q -> 
      isgParts_depth k r g' -> 
      isgParts_depth k r Q.
Proof.
  intros. revert H0 H. revert m n k r g g'.
  induction Q using global_ind_ref; intros; try easy.
  inversion H.
  - subst. inversion H0; try easy.
  - subst. inversion H0; try easy. 
  - subst. inversion H0; try easy.
  - inversion H. subst. inversion H0. 
  - inversion H1. subst.
    inversion H0. 
    - subst. constructor.
    - subst. constructor.
    - subst. 
      specialize(subst_parts_helper k0 xs s g0 r n0 lis m n g H10 H11 H7 H); intros. 
      destruct H2. destruct H2.
      apply dpth_c with (n := n0) (s := s) (g := x) (k := k0); try easy.
  - inversion H. subst. inversion H0. 
  - subst. inversion H0. subst.
    constructor. specialize(IHQ m.+1 n.+1 n0 r g P). apply IHQ; try easy.
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

Lemma part_break_s : forall G pt, 
    isgPartsC pt G -> 
    exists Gl, gttTC Gl G /\ isgParts pt Gl /\ (Gl = g_end \/ exists p q lis, Gl = g_send p q lis).
Proof.
  intros. pose proof H as H0.
  unfold isgPartsC in H0. destruct H0. destruct H0.
  rename x into Gl.
  specialize(isgParts_depth_exists pt Gl H1); intros. destruct H2. rename x into n.
  
  clear H.
  clear H1.
  revert H2 H0. revert G pt Gl.
  induction n; intros; try easy.
  - inversion H2. subst.
    exists (g_send pt q lis). split. easy. split. constructor. right. exists pt. exists q. exists lis. easy.
  - subst.
    exists (g_send p pt lis). split. easy. split. constructor. right. exists p. exists pt. exists lis. easy.
  - inversion H2. subst.
    pinversion H0. subst.
    specialize(subst_parts_depth 0 0 n pt g g Q H3 H1); intros.
    apply IHn with (Gl := Q); try easy.
    apply gttT_mon.
  - subst. 
    exists (g_send p q lis). split. easy.
    split.
    apply pa_sendr with (n := k) (s := s) (g := g); try easy.
    apply isgParts_depth_back with (n := n); try easy.
    right. exists p. exists q. exists lis. easy.
Qed.

Lemma part_break : forall G pt,
    wfgC G -> 
    isgPartsC pt G -> 
    exists Gl, gttTC Gl G /\ isgParts pt Gl /\ (Gl = g_end \/ exists p q lis, Gl = g_send p q lis).
Proof.
  intros. 
  unfold isgPartsC in H0. destruct H0. destruct H0.
  rename x into Gl.
  specialize(isgParts_depth_exists pt Gl H1); intros. destruct H2. rename x into n.
  
  clear H.
  clear H1.
  revert H2 H0. revert G pt Gl.
  induction n; intros; try easy.
  - inversion H2. subst.
    exists (g_send pt q lis). split. easy. split. constructor. right. exists pt. exists q. exists lis. easy.
  - subst.
    exists (g_send p pt lis). split. easy. split. constructor. right. exists p. exists pt. exists lis. easy.
  - inversion H2. subst.
    pinversion H0. subst.
    specialize(subst_parts_depth 0 0 n pt g g Q H3 H1); intros.
    apply IHn with (Gl := Q); try easy.
    apply gttT_mon.
  - subst. 
    exists (g_send p q lis). split. easy.
    split.
    apply pa_sendr with (n := k) (s := s) (g := g); try easy.
    apply isgParts_depth_back with (n := n); try easy.
    right. exists p. exists q. exists lis. easy.
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
    specialize(triv_merge_ltt_end ys0 H11); intros. clear H11 H7 H6 H5 H1 H.
    revert H10 H2. clear H0. clear s s'. revert p ys0.
    induction ys; intros; try easy.
    - destruct ys0; try easy. inversion H2. subst. clear H2. inversion H10. subst. clear H10.
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



Lemma proj_end_inj : forall g t p,
          wfgC g -> 
          projectionC g p ltt_end -> 
          projectionC g p t -> 
          t = ltt_end.
Proof.
  intros.
  pose proof H as Ht.
  unfold wfgC in H. destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))).
  clear Ha Hb Hc.
  specialize(balanced_to_tree g p Hd); intros.
  destruct H as (G,(ctxG,(Ha,(Hb,(Hc,He))))). clear He.
  revert Hc Hb Ha Ht H1 H0. clear Hd Gl.
  revert g t p ctxG.
  induction G using gtth_ind_ref; intros.
  - inversion Ha. subst.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/
           u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
    destruct H. specialize(H Hc). clear Hc H2.
    specialize(some_onth_implies_In n ctxG g H3); intros.
    specialize(H (Some g) H2). destruct H; try easy.
    destruct H as (q,(lsg,Hc)). clear H2.
    destruct Hc.
    - inversion H. subst. pinversion H0; try easy.
      assert False. apply H2. apply triv_pt_p; try easy.
      subst. easy.
      apply proj_mon.
    destruct H.
    - inversion H. subst. pinversion H0; try easy.
      assert False. apply H2. apply triv_pt_q; try easy.
      subst. easy.
      apply proj_mon.
    - inversion H. subst. pinversion H1; try easy.
      apply proj_mon.
  - inversion Ha. subst.
    rename p into s. rename q into s'. rename p0 into p.
    pinversion H1. easy. 
    - subst. assert False. apply Hb. constructor. easy.
    - subst. assert False. apply Hb. constructor. easy.
    subst.
    specialize(proj_end_cont_end s s' ys p Ht H5 H0); intros.
    specialize(wfgC_after_step_all H5 Ht); intros. 
    clear H9 H6 H5 H7 Ha Ht H1 H0.
    assert(List.Forall (fun u => u = None \/ u = Some ltt_end) ys0).
    {
      clear H13.
      revert H3 H2 H12 H8 Hb Hc H. clear t.
      revert s s' xs p ctxG ys.
      induction ys0; intros; try easy.
      - destruct ys; try easy. destruct xs; try easy. 
        inversion H. subst. clear H. inversion H3. subst. clear H3.
        inversion H2. subst. clear H2. inversion H12. subst. clear H12.
        inversion H8. subst. clear H8.
        specialize(IHys0 s s' xs p ctxG ys).
        assert(Forall (fun u : option ltt => u = None \/ u = Some ltt_end) ys0).
        {
          apply IHys0; try easy.
          specialize(ishParts_hxs Hb); try easy.
        }
        constructor; try easy. clear H H13 H11 H7 H6 H5 IHys0.
        destruct H9. left. easy.
        destruct H as (st,(g,(t,(Hta,(Htb,Htc))))). subst. right.
        destruct H3; try easy. destruct H as (s1,(g1,(Hd,He))). inversion Hd. subst.
        destruct H1; try easy. destruct H as (s2,(g2,(Hf,Hg))). inversion Hf. subst.
        destruct H10; try easy. destruct H as (s3,(g3,(g5,(Hi,(Hj,Hk))))). inversion Hj. subst.
        destruct H4; try easy. destruct H as (s4,(g4,(Hl,Hm))). inversion Hl. subst.
        clear Hj Hd Hf Hl.
        assert(t = ltt_end).
        {
          specialize(Hm g5 t p ctxG Hc). pclearbot.
          apply Hm; try easy.
          specialize(ishParts_x Hb); try easy.
        }
        subst. easy.
    }
    specialize(merge_end_back ys0 t H0 H13). easy.
    apply proj_mon.
Qed.

Lemma proj_inj : forall [g p t t'],
          wfgC g -> 
          projectionC g p t -> 
          projectionC g p t' -> 
          t = t'.
Proof.
  intros.
  apply lltExt. revert H H0 H1. revert t t' g. pcofix CIH; intros.
  pose proof H0 as Ht. unfold wfgC in H0. destruct H0 as (Gl,(Ha,(Hb,(Hc,Hd)))).
  specialize(balanced_to_tree g p Hd); intros. clear Ha Hb Hc Hd.
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
      assert False. apply H0. apply triv_pt_p; try easy. easy.
      subst. clear H6 H5 H11.
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
      assert False. apply H0. apply triv_pt_q; try easy. easy.
      subst. clear H6 H5 H11.
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
    - subst.
      pinversion H1; try easy. subst.
      specialize(proj_end_inj (gtt_send s p ys) (ltt_recv s ys0) p); intros.
      assert(ltt_recv s ys0 = ltt_end). apply H3; try easy. pfold. easy. pfold. easy. easy.
      subst. clear H4.
      pfold. constructor.
      specialize(proj_inj_list ys ys1 ys0 p r); intros.
      apply H0; try easy. 
      specialize(wfgC_after_step_all H9 Ht); try easy.
      apply proj_mon.
    - subst. 
      pinversion H1; try easy. subst.
      specialize(proj_end_inj (gtt_send p s' ys) (ltt_send s' ys0) p); intros.
      assert(ltt_send s' ys0 = ltt_end). apply H3; try easy. pfold. easy. pfold. easy. easy.
      subst. clear H4.
      pfold. constructor.
      specialize(proj_inj_list ys ys1 ys0 p r); intros.
      apply H0; try easy. 
      specialize(wfgC_after_step_all H9 Ht); try easy.
      apply proj_mon.
    - subst.
      pinversion H1. subst.
      - specialize(proj_end_inj (gtt_send s s' ys) t' p); intros.
        assert (t' = ltt_end).
        {
          apply H3; try easy. pfold. easy. pfold. easy.
        }
        subst. pfold. constructor.
      - subst. easy. subst. easy.
      - subst.
      {
        assert (List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists t t', u = Some t /\ v = Some t' /\ paco2 lttIso r t t')) ys1 ys0).
        {
          specialize(wfgC_after_step_all H10 Ht); intros.
          clear H18 H14 H11 H10 H13 H9 H6 H5 H7 H1 H2 Ht Ha.
          revert H0 H17 H12 H8 CIH Hc Hb H.
          revert p r s s' xs ctxG ys1 ys0. clear t t'.
          induction ys; intros; try easy.
          - destruct ys0; try easy. destruct ys1; try easy.
          - destruct ys0; try easy. destruct ys1; try easy. destruct xs; try easy.
            inversion H0. subst. clear H0. inversion H17. subst. clear H17.
            inversion H12. subst. clear H12. inversion H8. subst. clear H8.
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
    pose proof H as Ht. unfold wfgC in H. destruct H as (G',(Ha,(Hb,(Hc,Hd)))). clear Hc Hb Ha.
    specialize(balanced_to_tree G p Hd); intros. destruct H as (Gl,(ctxG,(Hta,(Htb,(Htc,Htd))))). exists Gl. 
    
    clear Ht Hd Htd.
    clear G'.
    revert Htc Htb Hta H0. revert G p q x ctxG.
    induction Gl using gtth_ind_ref; intros; try easy.
    - inversion Hta. subst.
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
      - pinversion H0; try easy. subst. clear H5.
        revert H10. clear H7 H1 H H2 H0 Hta Htb. clear ctxG. revert lsg x p q.
        induction n; intros; try easy. simpl. split.
        - constructor; try easy. right. exists (gtt_send p q lsg). exists lsg.
          split. easy. split. easy. revert H10.
          apply Forall2_mono; intros. destruct H. left. easy.
          right. destruct H as (s,(g,(t,(Ha,(Hb,Hc))))). subst. exists s. exists t. exists g. pclearbot. easy.
          specialize(used_hol 0 (gtt_send p q lsg)); intros. easy.
        - specialize(IHn lsg x p q H10). split. constructor; try easy. left. easy.
          constructor.
        apply proj_mon.
      - destruct H. inversion H. subst. pinversion H0; try easy. apply proj_mon.
      - inversion H. subst. pinversion H0; try easy. apply proj_mon.
    - inversion Hta. subst.
      assert(exists ctxJ : seq.seq (option gtt),
          typ_gtth ctxJ (gtth_send p q xs) (gtt_send p q ys) /\
          Forall
            (fun u : option gtt =>
             u = None \/
             (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
                u = Some g /\
                g = gtt_send p0 q0 lsg /\
                Forall2
                  (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
                   u0 = None /\ v = None \/
                   (exists (s : sort) (t : ltt) (g' : gtt),
                      u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p0 t)) lsg x))
            ctxJ /\ usedCtx ctxJ (gtth_send p q xs)
        ).
      {
        admit.
      }
      destruct H1. exists x0. easy.
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
  - 
  
Admitted.


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
  List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g'))) PT QT.
Proof.
  induction G' using gtth_ind_ref; intros; try easy.
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
    clear H8 H12 H6 H9 H7 H3 H2 H H0 Ha H4. clear ctxG n.
    revert H14 H11. revert p q PT QT.
    induction lsg; intros; try easy.
    - destruct QT; try easy. destruct PT; try easy.
    - destruct QT; try easy. destruct PT; try easy.
      inversion H14. subst. clear H14. inversion H11. subst. clear H11.
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
    (* specialize(slist_implies_some xs H11); intros. destruct H6 as (n,(G,Ha)).
    specialize(some_onth_implies_In n xs G Ha); intros.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G : gtt) (p q : string) (PT QT : seq.seq (option (sort * ltt)))
             (ctxG : seq.seq (option gtt)),
           projectionC G p (ltt_send q PT) ->
           projectionC G q (ltt_recv p QT) ->
           typ_gtth ctxG g G ->
           (ishParts p g -> False) ->
           (ishParts q g -> False) ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some g0 /\ g0 = gtt_send p q lsg)) ctxG ->
           Forall2
             (fun u0 v : option (sort * ltt) =>
              u0 = None /\ v = None \/
              (exists (s0 : sort) (g0 g' : ltt), u0 = Some (s0, g0) /\ v = Some (s0, g'))) PT QT))) xs); intros.
    destruct H7. specialize(H7 H). clear H H8.
    specialize(H7 (Some G) H6). destruct H7; try easy.
    destruct H as (s1,(g1,(Hb,Hc))). inversion Hb. subst. clear Hb H6.
    rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    pinversion H1; try easy.
    - subst. assert False. apply H3. constructor. easy.
    subst. pinversion H0; try easy. subst.
    specialize(_a_29_s_helper2s n s1 g1 xs ys ys0 ys1 ctxG p q H12 H15 H20 Ha); intros.
    destruct H as (g2,(t,(t',(Hta,(Htb,(Htc,(Htd,(Hte,Htf)))))))).
    specialize(merge_onth_recv n p QT ys0 t H16 Htc); intros. destruct H. subst.
    specialize(merge_onth_send n q PT ys1 t' H21 Hte); intros. destruct H. subst.
    specialize(Hc g2 p q x0 x ctxG). apply Hc; try easy. *)
Admitted.

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
    exists G'0 : global, gttTC G'0 (gtt_send q p x0) /\ isgParts pt G'0.
Proof.  
  intros.
  unfold isgPartsC in H. destruct H. destruct H. rename x1 into Gl.
  exists (g_send q p (overwrite_lis l (Some(s, Gl)) x)). 
  split.
  - pinversion H1; try easy. subst.
    pfold. constructor.
    clear H1 H2. revert H4 H0 H. clear q p pt. revert l x G' s Gl.
    induction x0; intros; try easy.
    - destruct l; try easy.
    - destruct x; try easy. inversion H4. subst. clear H4.
    - destruct l; try easy.
      - simpl in H0. subst. destruct H5; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. inversion H1. subst.
        constructor; try easy. right. exists x1. exists Gl. exists x3.
        split. easy. split. easy. left. easy.
      - specialize(IHx0 l x G' s Gl H7 H0 H). constructor; try easy.
    apply gttT_mon.
  - case_eq (eqb pt p); intros.
      assert (pt = p). apply eqb_eq; try easy. subst. constructor.
    - case_eq (eqb pt q); intros.
      assert (pt = q). apply eqb_eq; try easy. subst. constructor.
    - assert (pt <> p). apply eqb_neq; try easy. 
      assert (pt <> q). apply eqb_neq; try easy.
      apply pa_sendr with (n := l) (s := s) (g := Gl); try easy.
      clear H H0 H1 H2 H3 H4 H5 H6. clear x0 q p G' pt.
      revert Gl s x. induction l; intros; try easy.
      destruct x; try easy.
      destruct x; try easy. 
      specialize(IHl Gl s nil). easy. 
      specialize(IHl Gl s x). easy.
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
        gttstepC G G' q p l -> 
        projectionC G p (ltt_recv q LQ) ->
        projectionC G q (ltt_send p LP) ->
        isgPartsC pt G' -> 
        isgPartsC pt G.
Proof.
  intros.
  specialize(_a_29_11 G q p LP H H2); intros.
  destruct H4. destruct H4. rename x0 into ctxG. rename x into Gl.
  assert(typ_gtth ctxG Gl G /\
     (ishParts q Gl -> False) /\
     Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send q p lsg)) ctxG).
  {
    clear H H0 H1 H2 H3. destruct H4. destruct H0. destruct H1. clear H2.
    split; try easy. split; try easy.
    revert H1. clear H H0. induction ctxG; intros; try easy.
    inversion H1. subst. clear H1. specialize(IHctxG H3).
    constructor; try easy.
    clear IHctxG H3. destruct H2. left. easy. destruct H. destruct H. 
    right. exists x. exists x0. easy.
  }
  clear H4. rename H5 into H4.
  revert H4. revert H0 H1 H2 H3 H. revert ctxG LP LQ l p q pt G G'.
  induction Gl using gtth_ind_ref; intros.
  - destruct H4. destruct H5. 
    inversion H4. subst.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))), u = Some g /\ g = gtt_send q p lsg)) ctxG); intros.
    destruct H7. specialize(H7 H6). clear H8 H6. 
    specialize(some_onth_implies_In n ctxG G H9); intros. 
    specialize(H7 (Some G) H6). destruct H7; try easy. destruct H7. destruct H7. destruct H7.
    inversion H7. subst.
    pinversion H0; try easy. subst. clear H13 H14.
    unfold wfgC in H. destruct H. destruct H. rename x into G1.
    unfold isgPartsC. destruct H8. destruct H10.
    specialize(part_after_step_helper G1 q p x0 H H10); intros.
    destruct H12.
    specialize(part_after_step_helper2 l x0 q p x G' pt s); intros. apply H13; try easy.
    apply step_mon.
  - destruct H5. destruct H6. 
    inversion H5. subst.
    unfold isgPartsC.
    pinversion H2; try easy.
    subst. assert False. apply H6. constructor. easy.
    subst. pinversion H1; try easy. subst.
    pinversion H0; try easy. subst. clear H11 H12 H15 H16 H17 H20.
    specialize(part_break (gtt_send p q ys2) pt); intros.
    assert(exists Gl : global,
       gttTC Gl (gtt_send p q ys2) /\
       isgParts pt Gl /\
       (Gl = g_end \/
        (exists (p q : string) (lis : seq.seq (option (sort * global))), Gl = g_send p q lis))).
    {
      apply H8; try easy. 
      specialize(wfgC_after_step (gtt_send p q ys) (gtt_send p q ys2) q0 p0 l); intros.
      apply H9; try easy. pfold. easy.
    }
    destruct H9. destruct H9. destruct H10. rename x into Gl.
    destruct H11.
    - subst. pinversion H9; try easy.
    - destruct H11. destruct H11. destruct H11. subst.
      pinversion H9; try easy. subst.
    clear H8.
    inversion H10. subst.
    - specialize(part_break (gtt_send p q ys) p); intros.
      assert(exists Gl : global,
       gttTC Gl (gtt_send p q ys) /\
       isgParts p Gl /\
       (Gl = g_end \/
        (exists (p q : string) (lis : seq.seq (option (sort * global))), Gl = g_send p q lis))).
      {
        apply H8; try easy.
        apply triv_pt_p; try easy.
      }
      destruct H11. rename x into Gl'. destruct H11. destruct H15.
      destruct H16. subst. pinversion H11; try easy.
      destruct H16. destruct H16. destruct H16. subst. pinversion H11; try easy.
      subst. exists (g_send p q x2). split. pfold. easy. constructor. apply gttT_mon.
    - subst.
      specialize(part_break (gtt_send p q ys) q); intros.
      assert(exists Gl : global,
       gttTC Gl (gtt_send p q ys) /\
       isgParts q Gl /\
       (Gl = g_end \/
        (exists (p q : string) (lis : seq.seq (option (sort * global))), Gl = g_send p q lis))).
      {
        apply H8; try easy.
        apply triv_pt_q; try easy.
      }
      destruct H11. rename x into Gl'. destruct H11. destruct H15.
      destruct H16. subst. pinversion H11; try easy.
      destruct H16. destruct H16. destruct H16. subst. pinversion H11; try easy.
      subst. exists (g_send p q x2). split. pfold. easy. constructor. apply gttT_mon.
    - subst.
      
      rename p into st. rename q into st'. rename p0 into p. rename q0 into q.
      specialize(part_after_step_helper3 n x1 ys2 ys ys0 ys1 xs p q l s g ctxG); intros.
      assert(exists (g' g'' : gtt) (t t' : ltt) (Gl : gtth),
       onth n ys2 = Some (s, g') /\
       gttTC g g' /\
       onth n ys = Some (s, g'') /\
       gttstepC g'' g' q p l /\
       onth n ys0 = Some t /\
       projectionC g'' q t /\
       onth n ys1 = Some t' /\ projectionC g'' p t' /\ onth n xs = Some (s, Gl) /\ typ_gtth ctxG Gl g'').
      apply H8; try easy. clear H8.
      destruct H11. destruct H8. destruct H8. destruct H8. destruct H8.
      destruct H8. destruct H11. destruct H15. destruct H17. destruct H31. destruct H32. destruct H35.
      destruct H36. destruct H37.
      clear H12 H34 H23 H18 H14.
      specialize(some_onth_implies_In n xs (s, x4) H37); intros.
      specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (ctxG : seq.seq (option gtt)) (LP LQ : seq.seq (option (sort * ltt))) 
             (l : fin) (p q pt : string) (G G' : gtt),
           gttstepC G G' q p l ->
           projectionC G p (ltt_recv q LQ) ->
           projectionC G q (ltt_send p LP) ->
           isgPartsC pt G' ->
           wfgC G ->
           typ_gtth ctxG g G /\
           (ishParts q g -> False) /\
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some g0 /\ g0 = gtt_send q p lsg)) ctxG -> isgPartsC pt G))) xs); intros.
      destruct H14. specialize(H14 H). clear H H18.
      specialize(H14 (Some (s, x4)) H12). destruct H14; try easy.
      destruct H. destruct H. destruct H. inversion H. subst. clear H.
      rename x5 into s. rename x6 into Gl. rename x0 into G. rename x into G'.
      specialize(merge_onth_send n p LP ys0 x2 H19 H31); intros. destruct H. subst.
      specialize(merge_onth_recv n q LQ ys1 x3 H24 H35); intros. destruct H. subst.
      specialize(H14 ctxG x x0 l p q pt G G').
      assert(isgPartsC pt G).
      {
        apply H14; try easy. unfold isgPartsC. exists g. easy.
        specialize(wfgC_after_step (gtt_send st st' ys) G st st' n); intros.
        apply H; try easy. pfold. apply steq with (s := s); try easy.
        split; try easy. split; try easy.
        specialize(ishParts_n H6 H37); intros; try easy.
      }
      clear H14.
      unfold wfgC in H4. destruct H4. destruct H4. destruct H14. destruct H18.
      specialize(guard_breakG_s x2 (gtt_send st st' ys) H4 H18); intros.
      destruct H34. destruct H34. destruct H39. destruct H39.
      subst. pinversion H40. apply gttT_mon.
      destruct H39. destruct H39. destruct H39. subst.
      pinversion H40; try easy. subst.
      specialize(part_after_step_helper2 n ys st st' x6 G pt s); intros.
      apply H39; try easy. pfold. easy.
    apply gttT_mon.
    apply gttT_mon.
    apply step_mon.
    apply proj_mon.
    apply proj_mon.
Qed.


















