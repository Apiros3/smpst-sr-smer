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
 (* 
CoInductive EqGtt (G1 G2 : gtt) : Prop := 
  eqg_end : EqGtt gtt_end gtt_end 
   

Lemma fext_ltt : forall T T' lis sn x, lttmap T lis sn x -> lttmap T' lis sn x -> T = T'.
Proof.
   *)


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
  gttmap G w None gn -> gttmap G (w ++ w') None (gnode_pq p q) -> 
  (exists k, forall w', gttmap G (w ++ w') None (gnode_end) \/ 
                        (List.length w' = k /\ exists w2 w0, w' = w2 ++ w0 /\ exists r, 
                        gttmap G (w ++ w2) None (gnode_pq p r) \/ gttmap G (w ++ w2) None (gnode_pq r p))) /\
  (exists k, forall w', gttmap G (w ++ w') None (gnode_end) \/
                        (List.length w' = k /\ exists w2 w0, w' = w2 ++ w0 /\ exists r,
                        gttmap G (w ++ w2) None (gnode_pq q r) \/ gttmap G (w ++ w2) None (gnode_pq r q))).

Definition wfgC G := exists G', gttTC G' G /\ wfG G' /\ (forall n, exists m, guardG n m G') /\ balancedG G. 

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



