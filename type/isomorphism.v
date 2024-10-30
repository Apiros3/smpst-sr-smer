From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header type.global type.local.
Require Import List String Coq.Arith.PeanoNat Relations. 
Import ListNotations. 

Inductive gnode : Type := 
  | gnode_end : gnode
  | gnode_pq : part -> part -> gnode
  | gnode_s  : sort -> gnode.

(* gtt, labels to follow, sort if we want, where we reach *)
Inductive gttmap : gtt -> list fin -> option fin -> gnode -> Prop := 
  | gmap_end : gttmap gtt_end nil None gnode_end
  | gmap_pq  : forall p q xs, gttmap (gtt_send p q xs) nil None (gnode_pq p q)
  | gmap_con : forall n lis xs p q st gk s gn, onth n xs = Some (st, gk) -> gttmap gk lis s gn -> gttmap (gtt_send p q xs) (n :: lis) s gn
  | gmap_st  : forall n xs p q st gk, onth n xs = Some (st, gk) -> gttmap (gtt_send p q xs) nil (Some n) (gnode_s st). 

Inductive lnode : Type := 
  | lnode_end  : lnode 
  | lnode_send : part -> lnode 
  | lnode_recv : part -> lnode
  | lnode_s    : sort -> lnode.

(* tree to define on, labels to follow, sort if we want, where we reach *)
Inductive lttmap : ltt -> list fin -> option fin -> lnode -> Prop := 
  | lmap_end  : lttmap ltt_end nil None lnode_end 
  | lmap_send : forall p xs, lttmap (ltt_send p xs) nil None (lnode_send p)
  | lmap_recv : forall p xs, lttmap (ltt_recv p xs) nil None (lnode_recv p)
  | lmap_cons : forall n lis xs p st gk s gn, onth n xs = Some (st, gk) -> lttmap gk lis s gn -> lttmap (ltt_send p xs) (n :: lis) s gn
  | lmap_conr : forall n lis xs p st gk s gn, onth n xs = Some (st, gk) -> lttmap gk lis s gn -> lttmap (ltt_recv p xs) (n :: lis) s gn
  | lmap_sts  : forall n xs p st gk, onth n xs = Some(st, gk) -> lttmap (ltt_send p xs) nil (Some n) (lnode_s st)
  | lmap_str  : forall n xs p st gk, onth n xs = Some(st, gk) -> lttmap (ltt_recv p xs) nil (Some n) (lnode_s st).
 
Fixpoint isoList (R: ltt -> ltt -> Prop) (l1 l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | (Datatypes.None::xs, Datatypes.None::ys)               => isoList R xs ys
    | (Datatypes.Some (s,t)::xs, Datatypes.Some (s',t')::ys) => s = s' /\ R t t' /\ isoList R xs ys
    | (nil, nil)                                             => True
    | (_, _)                                                 => False
  end.

Inductive lttIso (R: ltt -> ltt -> Prop): ltt -> ltt -> Prop :=
  | i_end : lttIso R ltt_end ltt_end
  | i_recv: forall p xs ys, isoList R xs ys -> lttIso R (ltt_recv p xs) (ltt_recv p ys)
  | i_send: forall p xs ys, isoList R xs ys -> lttIso R (ltt_send p xs) (ltt_send p ys).

Definition lttIsoC L L' := paco2 lttIso bot2 L L'.

(* equivalent to functional extensionality *)
Axiom lltExt: forall L L', lttIsoC L L' -> L = L'.

Lemma lltExt_b : forall r L L', L = L' -> paco2 lttIso r L L'.
Proof.
  pcofix CIH; intros.
  subst.
  pfold. 
  destruct L'. constructor.
  constructor. induction l; intros; try easy.
  destruct a; try easy. destruct p; try easy. constructor; try easy. 
  split; try easy. right. apply CIH; try easy.
  constructor. induction l; intros; try easy.
  destruct a; try easy. destruct p; try easy. constructor; try easy. 
  split; try easy. right. apply CIH; try easy.
Qed.


Definition balancedG (G : gtt) := forall w w' p q gn,
  gttmap G w None gn -> (gttmap G (w ++ w') None (gnode_pq p q) \/ gttmap G (w ++ w') None (gnode_pq q p)) -> 
  (exists k, forall w', (gttmap G (w ++ w') None (gnode_end) \/ (List.length w' = k /\ exists tc, gttmap G (w ++ w') None tc)) -> 
                        exists w2 w0, w' = w2 ++ w0 /\ exists r, 
                        gttmap G (w ++ w2) None (gnode_pq p r) \/ gttmap G (w ++ w2) None (gnode_pq r p)).


Definition wfgC G := exists G', gttTC G' G /\ wfG G' /\ (forall n, exists m, guardG n m G') /\ balancedG G. 

Definition wfgCw G := exists G', gttTC G' G /\ wfG G' /\ (forall n, exists m, guardG n m G').

Definition wfC T := exists T', lttTC T' T /\ wfL T' /\ (forall n, exists m, guardL n m T').


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

Lemma wfL_after_beta : forall G G', 
      wfL G ->
      multiS betaL G G' -> 
      wfL G'.
Proof.
  intros. revert H. induction H0; intros; try easy.
  - inversion H. subst.
    specialize(wfL_after_subst y (l_rec G) G 0 0); intros.
    apply H2; try easy. inversion H0. easy.
  - apply IHmultiS. clear H0 IHmultiS.
    inversion H. subst.
    specialize(wfL_after_subst y (l_rec G) G 0 0); intros.
    apply H2; try easy. inversion H1. easy.
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

Lemma guard_breakL_s2 : forall G Gl, 
   (forall n : fin, exists m : fin, guardL n m Gl) ->
   wfL Gl ->
   lttTC Gl G -> 
   exists Gl', (Gl' = l_end \/ exists p lis, Gl' = l_send p lis \/ Gl' = l_recv p lis) /\
   (forall n : fin, exists m : fin, guardL n m Gl') /\
   wfL Gl' /\
   lttTC Gl' G.
Proof.
  intros.
  pinversion H1. 
  - subst. exists l_end. split; try easy. left. easy. split; try easy. split; try easy. pfold. easy.
  - subst. exists (l_send p xs). split. right. exists p. exists xs. left. easy.
    split. easy. split. easy. pfold. easy.
  - subst. exists (l_recv p xs). split. right. exists p. exists xs. right. easy.
    split. easy. split. easy. pfold. easy.
  - subst.
    specialize(guard_break G0 H); intros. clear H2 H3.
    destruct H4 as (Gl',(Ha,(Hb,Hc))). exists Gl'. split; try easy. split; try easy.
    split.
    specialize(wfL_after_beta (l_rec G0) Gl' H0 Ha). easy. 
    specialize(ltt_after_betaL (l_rec G0) Gl'); intros. apply H2; try easy. pfold. easy.
  apply lttT_mon.
Qed. 

Lemma guard_breakG_s2 : forall G Gl, 
   (forall n : fin, exists m : fin, guardG n m Gl) ->
   wfG Gl ->
   gttTC Gl G -> 
   exists Gl', (Gl' = g_end \/ exists p q lis, Gl' = g_send p q lis) /\
   (forall n : fin, exists m : fin, guardG n m Gl') /\
   wfG Gl' /\
   gttTC Gl' G.
Proof.
  intros.
  pinversion H1. 
  - subst. exists g_end. split; try easy. left. easy. split; try easy. split; try easy. pfold. easy.
  - subst. exists (g_send p q xs). split. right. exists p. exists q. exists xs. easy.
    split. easy. split. easy. pfold. easy.
  - subst.
    specialize(guard_breakG G0 H); intros. clear H2 H3.
    destruct H4 as (Gl',(Ha,(Hb,Hc))). exists Gl'. split; try easy. split; try easy.
    split.
    specialize(wfG_after_beta (g_rec G0) Gl' H0 Ha). easy. 
    specialize(gtt_after_betaL (g_rec G0) Gl'); intros. apply H2; try easy. pfold. easy.
  apply gttT_mon.
Qed. 

Lemma guard_cont : forall [lis1 p q],
    (forall n : fin, exists m : fin, guardG n m (g_send p q lis1)) -> 
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ 
      (forall n : fin, exists m : fin, guardG n m g)
    )) lis1.
Proof.
  induction lis1; intros; try easy.
  assert(Forall
           (fun u : option (sort * global) =>
            u = None \/
            (exists (s : sort) (g : global),
               u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g)))
           lis1).
  {
    specialize(IHlis1 p q). apply IHlis1; try easy.
    intros. specialize(H n). destruct H. exists x. 
    inversion H. subst. constructor.
    subst. constructor. inversion H3; try easy.
  }
  constructor; try easy.
  destruct a. 
  - right. destruct p0. exists s. exists g.
    split. easy. intros. specialize(H (n.+1)). destruct H. exists x.
    inversion H. subst. inversion H4. subst. destruct H3; try easy.
    destruct H1 as (s0,(g0,(Ha,Hb))). inversion Ha. subst. easy.
  - left. easy.
Qed.

Lemma guard_cont_b : forall [xs s s'],
    Forall
       (fun u : option (sort * global) =>
        u = None \/
        (exists (s : sort) (g : global),
           u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) xs -> 
    (forall n : fin, exists m : fin, guardG n m (g_send s s' xs)).
Proof.
  induction xs; intros; try easy. 
  - exists 0. destruct n; try easy. constructor. constructor. easy.
  - inversion H. subst.
    specialize(IHxs s s' H3).
    specialize(IHxs n). destruct IHxs as (m,H0).
    clear H H3.
    inversion H0. subst. exists 0. constructor.
    subst.
    destruct H2.
    - subst. exists m.
      constructor. constructor; try easy. left. easy.
    - destruct H as (s1,(g1,(Ha,Hb))). subst.
      specialize(Hb n0).
      destruct Hb as (m1, Hb). exists (Nat.max m m1).
      constructor; try easy. constructor.
      - right. exists s1. exists g1. split. easy.  
        apply guardG_more with (m := m1); try easy.
        apply max_r; try easy.
      - apply Forall_forall; intros.
        specialize(Forall_forall (fun u : option (sort * global) =>
        u = None \/
        (exists (s : sort) (g : global), u = Some (s, g) /\ guardG n0 m g)) xs); intros.
        destruct H1. specialize(H1 H4). clear H2 H4. specialize(H1 x H).
        destruct H1. left. easy.
        destruct H1 as (s0,(g0,(Hta,Htb))). subst. right.  
        exists s0. exists g0. split. easy. 
        apply guardG_more with (m := m); try easy.
        apply max_l; try easy.
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


Lemma wfgCw_after_step_all : forall [ys s s'],
    s <> s' -> wfgCw (gtt_send s s' ys) -> List.Forall (fun u => u = None \/ (exists st g, u = Some(st, g) /\ wfgCw g)) ys.
Proof.
  intros. apply Forall_forall; intros.
  destruct x. 
  - specialize(in_some_implies_onth p ys H1); intros.
    destruct H2. rename x into l. clear H1. 
    right. destruct p. exists s0. exists g. split. easy.
    unfold wfgC in *.
    destruct H0 as (Gl,(Ha,(Hb,Hc))).
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
        inversion Hk. subst. revert n. easy.
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
        inversion Hk. subst. revert n. easy.
      - destruct Hf; try easy. destruct H3 as (s1,(g1,(g2,Hf))). easy.
    apply gttT_mon. apply gttT_mon.
  - left. easy.
Qed.

Lemma wfgCw_triv : forall s s0 l, wfgCw (gtt_send s s0 l) -> s <> s0 /\ SList l.
Proof.
  intros.
  unfold wfgC in H.
  destruct H as (Gl,(Ha,(Hb,Hc))).
  specialize(guard_breakG_s2 (gtt_send s s0 l) Gl Hc Hb Ha); intros.
  clear Ha Hb Hc. clear Gl.
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

Lemma wfgC_triv : forall s s0 l, wfgC (gtt_send s s0 l) -> s <> s0 /\ SList l.
Proof.
  intros.
  unfold wfgC in H.
  apply wfgCw_triv. unfold wfgCw.
  destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))).
  exists Gl. easy.
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

