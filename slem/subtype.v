From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header src.local src.mono.
Require Import List String Coq.Arith.PeanoNat Morphisms Relations.
Import ListNotations. 

Lemma refl_recv: forall (l1:  list (option(sort*ltt))) (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop),
   Reflexive R1 -> Reflexive R2 ->
   wfrec R1 R2 l1 l1.
Proof. intro l1.
       induction l1; intros.
       - simpl. easy.
       - simpl. destruct a. destruct p.
         split. reflexivity.
         split. reflexivity.
         apply IHl1.
         easy. easy.
         apply IHl1.
         easy. easy.
Qed.

Lemma refl_send: forall (l1:  list (option(sort*ltt))) (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop),
   Reflexive R1 -> Reflexive R2 ->
   wfsend R1 R2 l1 l1.
Proof. intro l1.
       induction l1; intros.
       - simpl. easy.
       - simpl. destruct a. destruct p.
         split. reflexivity.
         split. reflexivity.
         apply IHl1.
         easy. easy.
         apply IHl1.
         easy. easy.
Qed.

Lemma stRefl: forall l, subtypeC l l.
Proof. pcofix CIH.
       intros.
       pfold.
       case_eq l; intros.
       constructor.
       constructor.
       apply refl_recv.
       constructor.

       repeat intro.
       unfold upaco2.
       right. apply CIH.

       constructor.
       apply refl_send.
       constructor.
       repeat intro.
       right. apply CIH.
Qed.

Lemma subtype_end : forall H, subtypeC ltt_end H -> H = ltt_end.
Proof.
  intros. punfold H0. inversion H0. easy. 
  apply subtype_monotone.
Qed.

Lemma subtype_recv_inv_helper : forall pt s s0 l l0 xs ys,
    subtypeC (ltt_recv pt (Some (s, l) :: xs)) (ltt_recv pt (Some (s0, l0) :: ys)) -> 
    subtypeC l l0.
Proof.
  intros. 
  pinversion H. subst.
  simpl in H1.
  destruct H1. destruct H1.
  pclearbot.
  unfold subtypeC. easy.
  apply subtype_monotone.
Qed.

Lemma subtype_recv_inv : forall pt xs ys, subtypeC (ltt_recv pt xs) (ltt_recv pt ys) -> Forall2R (fun u v => (u = None) \/ (exists s s' t t', u = Some(s,t) /\ v = Some (s',t') /\ subsort s s' /\ subtypeC t' t)) ys xs.
Proof.
  intros pt xs ys. revert pt xs.
  induction ys; intros. constructor.
  - destruct xs; try easy.
    pinversion H. subst. 
    simpl in H1. destruct a. destruct p. easy. easy.
    apply subtype_monotone.
  constructor.
  - destruct o. destruct a. destruct p0. destruct p. right.
    exists s. exists s0. exists l. exists l0. split; try easy. split; try easy.
    split. 
    pinversion H. subst. destruct H1. easy.
    apply subtype_monotone.
    specialize(subtype_recv_inv_helper pt s0 s l0 l xs ys H); intros. easy.
    left. easy.
    pinversion H. subst. 
    simpl in H1. destruct a; try easy.
    destruct p. easy.
    left. easy.
    apply subtype_monotone.
  - apply IHys with (pt := pt).
    pinversion H. subst. 
    pfold. constructor.
    simpl in H1. 
    destruct o. destruct p. destruct a. destruct p. destruct H1. destruct H1. easy. easy.
    destruct a. destruct p. easy. easy.
  - apply subtype_monotone.
Qed.

Lemma subtype_recv : forall H pt xs, subtypeC (ltt_recv pt xs) H -> (exists ys, 
                    H = ltt_recv pt ys).
Proof.
  induction xs; intros; try easy.
  - pinversion H0. subst. exists ys. easy.
    apply subtype_monotone.
  - destruct H.
    pinversion H0. apply subtype_monotone.
    pinversion H0. subst. exists l. easy. apply subtype_monotone.
    pinversion H0. apply subtype_monotone.
Qed.

Lemma subtype_send_inv_helper : forall pt s s0 l l0 xs ys,
    subtypeC (ltt_send pt (Some (s, l) :: xs)) (ltt_send pt (Some (s0, l0) :: ys)) -> 
    subtypeC l l0.
Proof.
  intros. 
  pinversion H. subst.
  simpl in H1.
  destruct H1. destruct H1.
  pclearbot.
  unfold subtypeC. easy.
  apply subtype_monotone.
Qed.

Lemma subtype_send_inv : forall pt xs ys, subtypeC (ltt_send pt xs) (ltt_send pt ys) -> Forall2R (fun u v => (u = None) \/ (exists s s' t t', u = Some(s,t) /\ v = Some (s',t') /\ subsort s s' /\ subtypeC t t')) xs ys.
Proof.
  induction xs; intros.
  - constructor.
  - destruct ys; try easy.
    pinversion H. subst. simpl in H1. destruct a. destruct p. easy. easy.
    apply subtype_monotone.
  constructor.
  - destruct a. right. destruct p. destruct o. destruct p.
    exists s. exists s0. exists l. exists l0. split; try easy. split; try easy.
    split.
    pinversion H. subst. simpl in H1. destruct H1. easy.
    apply subtype_monotone.
    specialize(subtype_send_inv_helper pt s s0 l l0 xs ys H); intros. easy.
    pinversion H. subst. simpl in H1. easy.
  - apply subtype_monotone.
    left. easy.
  - apply IHxs.
    pinversion H. subst. 
    pfold. constructor.
    simpl in H1. 
    destruct o. destruct p. destruct a. destruct p. destruct H1. destruct H1. easy. easy.
    destruct a. destruct p. easy. easy.
  - apply subtype_monotone.
Qed.

Lemma subtype_send : forall H pt xs, subtypeC (ltt_send pt xs) H -> (exists ys, 
                    H = ltt_send pt ys).
Proof.
  induction xs; intros; try easy.
  - pinversion H0. subst. exists ys. easy.
    apply subtype_monotone.
  - destruct H.
    pinversion H0. apply subtype_monotone.
    pinversion H0. apply subtype_monotone.
    pinversion H0. subst. exists l. easy. apply subtype_monotone.
Qed.

Lemma stTrans_helper_recv : forall x x0 l r,
      (forall l1 l2 l3 : ltt, subtypeC l1 l2 -> subtypeC l2 l3 -> r l1 l3) ->
      Forall2R
      (fun u v : option (sort * ltt) =>
       u = None \/
       (exists (s s' : sort) (t t' : ltt),
          u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) x0 x ->
      Forall2R
       (fun u v : option (sort * ltt) =>
        u = None \/
        (exists (s s' : sort) (t t' : ltt),
           u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) x l ->
      wfrec subsort (upaco2 subtype r) x0 l.
Proof.
  induction x; intros; try easy.
  destruct x0; try easy. 
  destruct l; try easy. destruct x0; try easy.
  inversion H0; subst. clear H0. inversion H1. subst. clear H1.
  simpl.
  destruct H5. 
  - subst. destruct o. destruct p. apply IHx; try easy. apply IHx; try easy.
  - destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
    subst.
    destruct H4; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H4.
    inversion H0.
    subst.
    split. apply sstrans with (s2 := x5); try easy.
    split. unfold upaco2. right. apply H with (l2 := x7); try easy. 
    apply IHx; try easy.
Qed. 

Lemma stTrans_helper_send : forall x x0 l r,
      (forall l1 l2 l3 : ltt, subtypeC l1 l2 -> subtypeC l2 l3 -> r l1 l3) ->
      Forall2R
      (fun u v : option (sort * ltt) =>
       u = None \/
       (exists (s s' : sort) (t t' : ltt),
          u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t')) x x0 -> 
      Forall2R
       (fun u v : option (sort * ltt) =>
        u = None \/
        (exists (s s' : sort) (t t' : ltt),
           u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t')) l x ->
      wfsend subsort (upaco2 subtype r) l x0.
Proof.
  induction x; intros; try easy.
  destruct l; try easy.
  destruct l; try easy. destruct x0; try easy.
  inversion H0; subst. clear H0. inversion H1. subst. clear H1.
  simpl.
  destruct H5. 
  - subst. destruct o. destruct p. destruct H4. easy. destruct H0. destruct H0. 
    destruct H0. destruct H0. destruct H0. destruct H1. easy.
    destruct o0. destruct p. apply IHx; try easy. apply IHx; try easy.
  - destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
    subst.
    destruct H4. subst. apply IHx; try easy. 
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H4.
    subst.
    inversion H1. subst.
    split. apply sstrans with (s2 := x6); try easy.
    split. unfold upaco2. right. apply H with (l2 := x8); try easy.
    apply IHx; try easy.
Qed. 

Lemma stTrans: forall l1 l2 l3, subtypeC l1 l2 -> subtypeC l2 l3 -> subtypeC l1 l3.
  Proof.
    pcofix CIH. intros.
    pfold. case_eq l1; intros.
    - subst. 
      specialize(subtype_end l2 H0); intros. subst.
      specialize(subtype_end l3 H1); intros. subst. apply sub_end.
    - subst.
      specialize(subtype_recv l2 s l H0); intros. destruct H. subst.
      specialize(subtype_recv l3 s x H1); intros. destruct H. subst.
      
      specialize(subtype_recv_inv s x x0 H1); intros.
      specialize(subtype_recv_inv s l x H0); intros.
      
      constructor.
      
      apply stTrans_helper_recv with (x := x); try easy.
      
    - subst.
      specialize(subtype_send l2 s l H0); intros. destruct H. subst.
      specialize(subtype_send l3 s x H1); intros. destruct H. subst.
      
      specialize(subtype_send_inv s x x0 H1); intros.
      specialize(subtype_send_inv s l x H0); intros.
      
      constructor.
      apply stTrans_helper_send with (x := x); try easy.
Qed.