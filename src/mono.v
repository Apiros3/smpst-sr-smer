From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations.
Import ListNotations. 
From SST Require Import src.header src.local src.global. 

Definition Forall_mono {X} {R T : X -> Prop} (HRT : forall x, R x -> T x) :
      forall l, Forall R l -> Forall T l.
Proof.
  induction l; intros; try easy.
  inversion H. subst. specialize(IHl H3). constructor; try easy.
  apply HRT; try easy.
Qed.

Definition Forall2_mono {X Y} {R T : X -> Y -> Prop} (HRT : forall x y, R x y -> T x y) :
      forall l m, Forall2 R l m -> Forall2 T l m :=
  fix loop l m h {struct h} :=
    match h with
    | Forall2_nil => Forall2_nil T
    | Forall2_cons _ _ _ _ h1 h2 => Forall2_cons _ _ (HRT _ _ h1) (loop _ _ h2)
    end.

Definition Forall2R_mono {X Y} {R T : X -> Y -> Prop} (HRT : forall x y, R x y -> T x y) :
      forall l m, Forall2R R l m -> Forall2R T l m :=
  fix loop l m h {struct h} :=
    match h with
    | Forall2R_nil xs => Forall2R_nil T xs
    | Forall2R_cons _ _ _ _ h1 h2 => Forall2R_cons _ _ _ _ _ (HRT _ _ h1) (loop _ _ h2)
    end.

Lemma subtype_monotone : monotone2 subtype.
Proof.
  unfold monotone2.
  intros. induction IN; intros.
  - constructor.
  - constructor.
    revert H. revert ys. 
    induction xs. destruct ys; try easy.
    intros. destruct ys; try easy. simpl.
    simpl in H. destruct o; try easy. destruct p0. destruct a; try easy. destruct p0.
    destruct H. destruct H0. split; try easy. split; try easy. apply LE; try easy. apply IHxs; try easy.
    destruct a; try easy. destruct p0. apply IHxs; try easy. apply IHxs; try easy. 
  - constructor.
    revert H. revert ys.
    induction xs. destruct ys; try easy.
    intros. destruct ys; try easy. simpl in *.
    destruct a; try easy. destruct p0. destruct o; try easy. destruct p0. 
    destruct H. destruct H0. split; try easy. split. apply LE; try easy. apply IHxs; try easy.
    destruct o; try easy. destruct p0. apply IHxs; try easy. apply IHxs; try easy.
Qed.

Lemma lttT_mon : monotone2 lttT.
Proof.
  unfold monotone2. intros. induction IN; intros; try easy.
  - apply lttT_end.
  - apply lttT_send; try easy.
    - revert H LE. revert r r' p ys.
      induction xs; intros; try easy.
      destruct ys; try easy.
      destruct ys; try easy.
      inversion H. subst.
      constructor.
      - destruct H3. left. easy.
        destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. subst. right.
        exists x. exists x0. exists x1. split; try easy. split; try easy.
        apply LE; try easy.
      - apply IHxs with (r := r); try easy.
  - apply lttT_recv; try easy.
    - revert H LE. revert r r' p ys.
      induction xs; intros; try easy.
      destruct ys; try easy.
      destruct ys; try easy.
      inversion H. subst.
      constructor.
      - destruct H3. left. easy.
        destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. subst. right.
        exists x. exists x0. exists x1. split; try easy. split; try easy.
        apply LE; try easy.
      - apply IHxs with (r := r); try easy.
  - apply lttT_rec with (Q := Q); try easy.

Qed.

Lemma gttT_mon : monotone2 gttT.
Proof.
  unfold monotone2. intros.
  induction IN; intros; try easy.
  - apply gttT_end.
  - apply gttT_send; try easy.
    - revert H LE. revert r r' p q ys.
      induction xs; intros; try easy.
      destruct ys; try easy.
      destruct ys; try easy.
      inversion H. subst.
      constructor.
      - destruct H3. left. easy.
        destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. subst. right.
        exists x. exists x0. exists x1. split; try easy. split; try easy.
        apply LE; try easy.
      - apply IHxs with (r := r); try easy.
  - apply gttT_rec with (Q := Q); try easy.
    apply LE; try easy.
Qed.

Lemma Iso_mon : monotone2 lttIso.
Proof.
  unfold monotone2; intros.
  induction IN; intros; try easy.
  - constructor.
  - constructor. revert H. revert xs ys.
    induction xs; intros; try easy. destruct ys; try easy.
    destruct a. destruct p0. destruct o; try easy. destruct p0.
    simpl in *. split. easy. split. apply LE; try easy.
    apply IHxs; try easy.
  - destruct o; try easy.
    apply IHxs; try easy.
  - constructor. revert H. revert xs ys.
    induction xs; intros; try easy. destruct ys; try easy.
    destruct a. destruct p0. destruct o; try easy. destruct p0.
    simpl in *. split. easy. split. apply LE; try easy.
    apply IHxs; try easy.
  - destruct o; try easy.
    apply IHxs; try easy.
Qed.

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