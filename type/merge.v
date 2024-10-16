From SST Require Export type.global type.local type.isomorphism.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.

Inductive merge2 : ltt -> ltt -> ltt -> Prop := 
  | mrg_id : forall x, merge2 x x x
  | mrg_bra : forall p xs ys IJ, 
                Forall3S (fun u v w => 
                  (u = None /\ v = None /\ w = None) \/
                  (exists t, u = None /\ v = Some t /\ w = Some t) \/
                  (exists t, u = Some t /\ v = None /\ w = Some t) \/
                  (exists t, u = Some t /\ v = Some t /\ w = Some t)) xs ys IJ -> 
                  SList xs -> SList ys ->
              merge2 (ltt_recv p xs) (ltt_recv p ys) (ltt_recv p IJ).

Inductive isMerge : ltt -> list (option ltt) -> Prop :=
  | matm : forall t, isMerge t (Some t :: nil)
  | mconsn : forall t xs, isMerge t xs -> isMerge t (None :: xs) 
  | mconss : forall t t' t'' xs, isMerge t xs -> merge2 t t' t'' -> isMerge t'' (Some t' :: xs). 


Lemma merge_end_back : forall ys0 t,
    Forall (fun u : option ltt => u = None \/ u = Some ltt_end) ys0 -> 
    isMerge t ys0 -> 
    t = ltt_end.
Admitted.

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

Lemma lttIso_inv : forall [r p xs q ys],
  (paco2 lttIso r (ltt_recv p xs) (ltt_recv q ys)) -> 
  p = q /\ List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t') /\ upaco2 lttIso r t t')) xs ys.
  intros.
  pinversion H; intros; try easy.
  subst. split. easy.
  clear H. revert H1. clear q.
  revert xs ys.
  induction xs; intros; try easy.
  - destruct ys; try easy. 
  - destruct ys; try easy. destruct a; try easy. destruct p; try easy.
    specialize(IHxs ys).
    - destruct a. destruct p. destruct o; try easy. destruct p; try easy.
      simpl in H1. destruct H1 as (Ha,(Hb,Hc)). specialize(IHxs Hc).
      constructor; try easy. right. subst. exists s0. exists l. exists l0.
      easy.
    - destruct o; try easy.
      specialize(IHxs H1). constructor; try easy. left. easy.
  apply Iso_mon.
Qed.

Lemma lttIso_inv_b : forall xs ys p r,
    List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t') /\ upaco2 lttIso r t t')) xs ys -> 
    paco2 lttIso r (ltt_recv p xs) (ltt_recv p ys).
Proof.
  intros. pfold. constructor. revert H. revert r ys. clear p.
  induction xs; intros. destruct ys; try easy.
  destruct ys; try easy. inversion H. subst. clear H.
  specialize(IHxs r ys H5). clear H5.
  destruct H3. destruct H. subst. easy.
  destruct H as (s,(t1,(t2,(Ha,(Hb,Hc))))). subst.
  simpl. easy.
Qed.

Lemma isMerge_injw : forall t t' r ys0 ys1,
    Forall2
       (fun u v : option ltt =>
        u = None /\ v = None \/
        (exists t t' : ltt, u = Some t /\ v = Some t' /\ paco2 lttIso r t t')) ys0 ys1 ->
    isMerge t ys0 -> isMerge t' ys1 -> paco2 lttIso r t t'.
Proof.
  intros t t' r ys0. revert t t' r.
  induction ys0; intros; try easy. destruct ys1; try easy.
  inversion H. subst. clear H.
  inversion H0. subst. destruct ys1; try easy.
  destruct H5; try easy. destruct H as (t1,(t2,(Ha,(Hb,Hc)))). inversion Ha. subst.
  inversion H1. subst. easy. subst. inversion H4; try easy.
  subst. destruct H5. destruct H. subst. inversion H1. subst.
  specialize(IHys0 t t' r ys1 H7 H3 H5). easy.
  destruct H as (t1,(t2,(Ha,(Hb,Hc)))). easy.
  subst.
  destruct H5; try easy. destruct H as (t1,(t2,(Ha,(Hb,Hc)))). inversion Ha. subst.
  inversion H1. subst. inversion H0. subst. inversion H4. 
  subst. destruct ys0; try easy. subst.
  specialize(IHys0 t0 t3 r ys1 H7 H4 H5). clear H0 H1 H4 H5 H7 Ha.
  
  inversion H6. subst. inversion H8; try easy. subst. easy.
  subst. pinversion IHys0; try easy. subst. 
  apply lttIso_inv_b; try easy.
  specialize(lttIso_inv Hc); intros. destruct H2. 
  
Admitted.

Lemma _a_29_part_helper_recv : forall n ys1 x4 p ys,
    onth n ys1 = Some x4 ->
    isMerge (ltt_recv p ys) ys1 -> 
    exists ys1', x4 = ltt_recv p ys1'.
Proof. intro n.
Admitted.

Lemma _a_29_part_helper_send : forall n ys2 x3 q x,
    onth n ys2 = Some x3 ->
    isMerge (ltt_send q x) ys2 ->
    exists ys2', x3 = ltt_send q ys2'.
Proof. intro n.
       induction n; intros.
       - inversion H0. subst. simpl in H. inversion H. subst.
         exists x. easy.
         subst. simpl in H. easy.
         subst. simpl in H. inversion H. subst. 
Admitted.

Lemma triv_merge : forall T T', isMerge T (Some T' :: nil) -> T = T'.
Proof. intros.
       inversion H. subst. easy. subst.
       easy.
Qed.

Lemma triv_merge2 : forall T xs, isMerge T xs -> isMerge T (None :: xs).
Proof. intros.
       inversion H. subst.
       constructor. easy.
       subst. constructor. easy.
       subst. constructor. easy.
Qed. 

Lemma triv_merge3 : forall T xs, isMerge T xs -> isMerge T (Some T :: xs).
Proof. intros.
       apply mconss with (t := T); try easy.
       constructor. 
Qed.

(* needed *)
Lemma merge_onth_recv : forall n p LQ ys1 gqT,
      isMerge (ltt_recv p LQ) ys1 ->
      onth n ys1 = Some gqT -> 
      exists LQ', gqT = ltt_recv p LQ'.
Proof. intros. eapply _a_29_part_helper_recv. eauto. eauto. Qed.

(* needed *)
Lemma merge_onth_send : forall n q LP ys0 gpT,
      isMerge (ltt_send q LP) ys0 ->
      onth n ys0 = Some gpT ->
      exists LP', gpT = (ltt_send q LP').
Proof. intros. eapply _a_29_part_helper_send. eauto. eauto. Qed.

(* needed *)
Lemma triv_merge_ltt_end : forall ys0,
    isMerge ltt_end ys0 -> List.Forall (fun u => u = None \/ u = Some ltt_end) ys0.
Proof.
  induction ys0; intros; try easy.
  inversion H.
  - subst. constructor; try easy. right. easy.
  - subst. specialize(IHys0 H2). constructor; try easy. left. easy.
  - subst. inversion H4. subst.
    specialize(IHys0 H3). constructor; try easy. right. easy.
Qed.

(* need *)
Lemma merge_label_recv : forall Mp LQ' LQ0' T k l p,
          isMerge (ltt_recv p LQ') Mp ->
          onth k Mp = Some (ltt_recv p LQ0') ->
          onth l LQ0' = Some T ->
          exists T', onth l LQ' = Some T'.
Proof. intros Mp.
Admitted.

(* need *)
Lemma merge_label_send : forall Mq LP' LP0' T k l q,
          isMerge (ltt_send q LP') Mq ->
          onth k Mq = Some (ltt_send q LP0') ->
          onth l LP0' = Some T ->
          exists T', onth l LP' = Some T'. 
Proof. intro Mq.
Admitted.

Lemma merge_label_sendb : forall ys0 LP LP' ST n l q,
      isMerge (ltt_send q LP) ys0 ->
      onth n ys0 = Some (ltt_send q LP') ->
      onth l LP = Some ST ->
      onth l LP' = Some ST.
Proof. intro ys0.
Admitted.

Lemma merge_constr : forall p LQ ys1 n,
          isMerge (ltt_recv p LQ) ys1 ->
          onth n ys1 = Some ltt_end ->
          False.
Proof. intros p LQ ys1 n.
Admitted.

Lemma merge_consts : forall q LP ys0 n,
          isMerge (ltt_send q LP) ys0 -> 
          onth n ys0 = Some ltt_end -> 
          False.
Proof. intros q LP ys0 n.
Admitted.


Lemma merge_slist : forall T ys, isMerge T ys -> SList ys.
Proof. intros.
       induction H; intros.
       simpl. easy.
       simpl. easy.
       simpl. destruct xs.
       easy. easy.
Qed.


Lemma merge_label_recv_s : forall Mp LQ' LQ0' T k l p,
          isMerge (ltt_recv p LQ') Mp ->
          onth k Mp = Some (ltt_recv p LQ0') ->
          onth l LQ0' = Some T ->
          onth l LQ' = Some T.
Admitted.

Lemma merge_label_send_s : forall Mq LP' LP0' T k l q,
          isMerge (ltt_send q LP') Mq ->
          onth k Mq = Some (ltt_send q LP0') ->
          onth l LP0' = Some T ->
          onth l LP' = Some T. 
Admitted.

Lemma merge_sorts : forall ys0 ys1 p q PT QT,
    Forall2
      (fun u v : option ltt =>
       u = None /\ v = None \/
       (exists lis1 lis2 : seq.seq (option (sort * ltt)),
          u = Some (ltt_recv p lis1) /\
          v = Some (ltt_send q lis2) /\
          Forall2
            (fun u0 v0 : option (sort * ltt) =>
             u0 = None /\ v0 = None \/
             (exists (s : sort) (t t' : ltt), u0 = Some (s, t) /\ v0 = Some (s, t'))) lis2 lis1)) ys0 ys1 -> 
    isMerge (ltt_recv p QT) ys0 -> 
    isMerge (ltt_send q PT) ys1 -> 
    Forall2
      (fun u v : option (sort * ltt) =>
       u = None /\ v = None \/ (exists (s : sort) (g g' : ltt), u = Some (s, g) /\ v = Some (s, g'))) PT QT.
Admitted.
 
 
 
 
 
 
 