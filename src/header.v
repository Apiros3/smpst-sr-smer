From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations.
Import ListNotations. 

Notation fin := nat.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x 
  | multi_step : forall (x y z : X), R x y -> multi R y z -> multi R x z.
  
Lemma transitive_multi {X : Type} : forall (R : relation X) (x y z : X), multi R x y -> multi R y z -> multi R x z.
Proof.
  intros R x y z H.
  revert z.
  induction H; intros. easy.
  specialize(IHmulti z0 H1).
  specialize(@multi_step X R); intros.
  apply H2 with (y := y). easy. easy.
Qed.


Inductive Forall3S {A} : (A -> A -> A -> Prop) -> list A -> list A -> list A -> Prop := 
  | Forall3s_nil0 : forall P xs, Forall3S P nil xs xs
  | Forall3s_nil1 : forall P xs, Forall3S P xs nil xs
  | Forall3s_cons : forall P a xa b xb c xc, P a b c -> Forall3S P xa xb xc -> Forall3S P (a :: xa) (b :: xb) (c :: xc).

Fixpoint SList {A} (lis : list (option A)) : Prop := 
  match lis with 
    | Datatypes.Some x :: [] => True 
    | _ :: xs                => SList xs
    | []                     => False
  end.

Lemma SList_f {A} : forall x (xs : list (option A)), SList (x :: xs) -> SList xs \/ (xs = nil /\ exists a, x = Datatypes.Some a).
Proof.
  intros. unfold SList in H.
  destruct x. destruct xs. right. split. easy. exists a. easy. left. easy.
  left. easy.
Qed.

Lemma SList_b {A} : forall x (xs : list (option A)), SList xs -> SList (x :: xs).
Proof.
  intros. unfold SList.
  destruct x. destruct xs; try easy. easy.
Qed.

Fixpoint extendLis {A} (n : fin) (ST : option A) : list (option A) :=
  match n with 
    | S m  => None :: extendLis m ST
    | 0    => [ST]
  end.

Definition Forall2_mono {X Y} {R T : X -> Y -> Prop} (HRT : forall x y, R x y -> T x y) :
      forall l m, Forall2 R l m -> Forall2 T l m :=
  fix loop l m h {struct h} :=
    match h with
    | Forall2_nil => Forall2_nil T
    | Forall2_cons _ _ _ _ h1 h2 => Forall2_cons _ _ (HRT _ _ h1) (loop _ _ h2)
    end.

Definition Forall_mono {X} {R T : X -> Prop} (HRT : forall x, R x -> T x) :
      forall l, Forall R l -> Forall T l.
Proof.
  induction l; intros; try easy.
  inversion H. subst. specialize(IHl H3). constructor; try easy.
  apply HRT; try easy.
Qed.

Inductive Forall2R {X Y} (P : X -> Y -> Prop) : list X -> list Y -> Prop := 
  | Forall2R_nil : forall ys, Forall2R P nil ys
  | Forall2R_cons : forall x xs y ys, P x y -> Forall2R P xs ys -> Forall2R P (x :: xs) (y :: ys).

Definition Forall2R_mono {X Y} {R T : X -> Y -> Prop} (HRT : forall x y, R x y -> T x y) :
      forall l m, Forall2R R l m -> Forall2R T l m :=
  fix loop l m h {struct h} :=
    match h with
    | Forall2R_nil xs => Forall2R_nil T xs
    | Forall2R_cons _ _ _ _ h1 h2 => Forall2R_cons _ _ _ _ _ (HRT _ _ h1) (loop _ _ h2)
    end.

Inductive multiS {X : Type} (R : relation X) : relation X :=
  | multi_sing : forall (x y : X), R x y -> multiS R x y
  | multi_sstep : forall (x y z : X), R x y -> multiS R y z -> multiS R x z.
  
Fixpoint onth {A : Type} (n : fin) (lis : list (option A)) : option A :=
  match n with 
    | S m => 
      match lis with 
        | x::xs => onth m xs
        | []    => None 
      end
    | 0   =>
      match lis with 
        | x::xs => x 
        | []    => None
      end
  end.

Lemma slist_implies_some {A} : forall (lis : list (option A)), SList lis -> exists n G, 
  onth n lis = Some G.
Proof.
  induction lis; intros; try easy.
  specialize(SList_f a lis H); intros.
  destruct H0. specialize(IHlis H0). destruct IHlis. exists (S x). easy.
  destruct H0. destruct H1. subst. exists 0. exists x. easy.
Qed.

Lemma some_onth_implies_In {A} : forall n (ctxG : list (option A)) G,
    onth n ctxG = Some G -> In (Some G) ctxG.
Proof.
  induction n; intros; try easy.
  - destruct ctxG; try easy. simpl in *.
    left. easy.
  - destruct ctxG; try easy. simpl in *.
    right. apply IHn; try easy.
Qed.

Lemma in_some_implies_onth {A} : forall (x : A) xs,
    In (Some x) xs -> exists n, onth n xs = Some x.
Proof.
  intros. revert H. revert x. 
  induction xs; intros; try easy.
  simpl in *. destruct H. exists 0. easy.
  specialize(IHxs x H). destruct IHxs. exists (Nat.succ x0). easy.
Qed.

Lemma SList_to_In {A} : forall (xs : list (option A)),
    SList xs ->
    exists t, In (Some t) xs.
Proof.
  induction xs; intros; try easy.
  specialize(SList_f a xs H); intros.
  destruct H0.
  specialize(IHxs H0). destruct IHxs. exists x. right. easy.
  destruct H0. destruct H1. subst. exists x. left. easy.
Qed.

Lemma extendExtract {A} : forall n (ST : option A), onth n (extendLis n ST) = ST.
Proof.
  induction n; intros; try easy.
  apply IHn; try easy.
Qed.

Lemma triad_le :  forall m t',
                  is_true (ssrnat.leq m t') ->
                  is_true (ssrnat.leq (S t') m) -> False.
Proof.
  intros.
  specialize(leq_trans H0 H); intros. 
  clear H H0. clear m.
  induction t'; intros; try easy.
Qed.


Fixpoint overwrite_lis {A} (n : fin) (x : (option A)) (xs : list (option A)) : list (option A) := 
  match xs with 
    | y::xs => match n with 
        | 0 => x :: xs
        | S k => y :: overwrite_lis k x xs
      end
    | nil   => match n with 
        | 0 => [x]
        | S k => None :: overwrite_lis k x nil 
      end
  end.

Lemma overwriteExtract {A} : forall n (ST : option A) lis, onth n (overwrite_lis n ST lis) = ST.
Proof.
  induction n; intros.
  destruct lis; try easy.
  destruct lis; try easy.
  specialize(IHn ST nil). easy.
  specialize(IHn ST lis). easy.
Qed. 
 
Lemma max_l : forall m m1, m <= Nat.max m m1.
Proof.
  induction m; intros; try easy.
  revert IHm. revert m. induction m1; intros; try easy.
  apply IHm; try easy.
Qed.

Lemma max_r : forall m m1, m1 <= Nat.max m m1.
Proof.
  induction m; intros; try easy.
  revert IHm. revert m. induction m1; intros; try easy.
  apply IHm; try easy.
Qed.

Inductive Forall3 {A B C} : (A -> B -> C -> Prop) -> list A -> list B -> list C -> Prop := 
  | Forall3_nil : forall P, Forall3 P nil nil nil
  | Forall3_cons : forall P a b c xa xb xc, P a b c -> Forall3 P xa xb xc -> Forall3 P (a :: xa) (b :: xb) (c :: xc).

Fixpoint noneLis {A} (n : fin) : list (option A) := 
  match n with 
    | 0 => nil 
    | S m => None :: noneLis m
  end.


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
