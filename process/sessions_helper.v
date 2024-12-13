From SST Require Export src.expressions process.processes process.substitution process.inversion process.inversion_expr process.typecheck type.global type.local type.isomorphism type.projection.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes Coq.Logic.Classical_Prop.


Lemma noin_mid {A} : forall (l1 l2 : list A) a a0, ~ In a0 (l1 ++ a :: l2) -> ~ In a0 (l1 ++ l2) /\ a <> a0.
Proof.
  induction l1; intros; try easy.
  simpl in *.
  specialize(Classical_Prop.not_or_and (a = a0) (In a0 l2) H); intros.
  easy.
  simpl in *. 
  specialize(Classical_Prop.not_or_and (a = a1) (In a1 (l1 ++ a0 :: l2)) H); intros.
  destruct H0.
  specialize(IHl1 l2 a0 a1 H1). destruct IHl1.
  split; try easy.
  apply Classical_Prop.and_not_or. split; try easy.
Qed.

Lemma in_mid {A} : forall (l1 l2 : list A) a pt, In pt (l1 ++ a :: l2) -> (pt = a \/ In pt (l1 ++ l2)).
Proof.
  induction l1; intros; try easy.
  simpl in *. destruct H. left. easy. right. easy.
  simpl in H. destruct H. right. left. easy.
  specialize(IHl1 l2 a0 pt H); intros. destruct IHl1. left. easy.
  right. right. easy.
Qed.

Lemma in_or {A} : forall (l1 l2 : list A) pt, In pt (l1 ++ l2) -> In pt l1 \/ In pt l2.
Proof.
  induction l1; intros; try easy.
  right. easy.
  simpl in H.
  destruct H.
  - left. constructor. easy.
  - specialize(IHl1 l2 pt H). destruct IHl1.
    - left. right. easy.
    - right. easy.
Qed.

Lemma noin_swap {A} : forall (l1 l2 : list A) a, ~ In a (l1 ++ l2) -> ~ In a (l2 ++ l1).
Proof.
  induction l2; intros. simpl in *.
  specialize(app_nil_r l1); intros. replace (l1 ++ nil) with l1 in *. easy.
  specialize(noin_mid l1 l2 a a0 H); intros. destruct H0.
  simpl in *.
  apply Classical_Prop.and_not_or. split; try easy.
  apply IHl2; try easy. 
Qed.


Lemma nodup_swap {A} : forall (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup (l2 ++ l1).
Proof.
  induction l2; intros. simpl in *.
  specialize(app_nil_r l1); intros. replace (l1 ++ nil) with l1 in *. easy.
  specialize(NoDup_remove_1 l1 l2 a H); intros.
  specialize(NoDup_remove_2 l1 l2 a H); intros.
  specialize(IHl2 H0).
  constructor; try easy.
  apply noin_swap; try easy.
Qed.

Lemma in_swap {A} : forall (l1 l2 : list A) pt, In pt (l1 ++ l2) -> In pt (l2 ++ l1).
Proof.
  induction l2; intros. simpl in *.
  specialize(app_nil_r l1); intros. replace (l1 ++ nil) with l1 in *. easy.
  specialize(in_mid l1 l2 a pt H); intros.
  destruct H0. left. easy. right. apply IHl2; try easy.
Qed.

Lemma in_swap2 {A} : forall (l1 l2 l3 : list A) pt, In pt (l3 ++ l1 ++ l2) -> In pt (l3 ++ l2 ++ l1).
Proof.
  induction l3; intros. simpl in *.
  - apply in_swap. easy.
  - simpl in *. destruct H. left. easy.
    specialize(IHl3 pt H). right. easy.
Qed.

Lemma nodup_swap2 {A} : forall (l1 l2 l3 : list A), NoDup (l3 ++ l1 ++ l2) -> NoDup (l3 ++ l2 ++ l1).
Proof.
  induction l3; intros.
  - simpl in *. apply nodup_swap. easy.
  - inversion H. subst. specialize(IHl3 H3). constructor; try easy.
    unfold not in *.
    intros. apply H2.
    apply in_swap2. easy.
Qed.
