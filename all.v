From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh src.step.
From SST Require Import lemma.inversion lemma.inversion_expr lemma.subtitution_helper lemma.substitution lemma.decidable_helper lemma.decidable  lemma.expr.

Inductive isMerge : ltt -> list (option ltt) -> Prop :=
  | matm : forall t, isMerge t (Some t :: nil)
  | mconsn : forall t xs, isMerge t xs -> isMerge t (None :: xs) 
  | mconss : forall t xs, isMerge t xs -> isMerge t (Some t :: xs). 

Lemma merge_end_back : forall n ys0 t,
    onth n ys0 = Some ltt_end -> 
    isMerge t ys0 -> 
    t = ltt_end.
Proof.
  induction n; intros; try easy.
  - destruct ys0; try easy. 
    simpl in H. subst. inversion H0. subst. easy. easy.
  - destruct ys0; try easy.
    inversion H0. subst. 
    - destruct n; try easy.
    - subst. specialize(IHn ys0 t). apply IHn; try easy.
    - subst. specialize(IHn ys0 t). apply IHn; try easy.
Qed.

Lemma merge_end_s : forall x T,
    Forall (fun u : option ltt => u = None \/ u = Some ltt_end) x -> 
    isMerge T x -> T = ltt_end.
Proof.
  induction x; intros; try easy.
  - inversion H. subst.
    inversion H0. subst. destruct H3; try easy. inversion H1; try easy.
    subst. specialize(IHx T). apply IHx; try easy.
    subst. specialize(IHx T). apply IHx; try easy.
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
  specialize(IHys0 t t' r ys1 H7).
  inversion H0. subst. inversion H1. subst.
  - destruct H5; try easy. destruct H as (t1,(t2,(Ha,(Hb,Hc)))). inversion Ha. inversion Hb. subst. easy.
  - subst. destruct H5; try easy.
    destruct H as (t1,(t2,(Ha,(Hb,Hc)))). easy.
  - subst. destruct H5; try easy. destruct H as (t1,(t2,(Ha,(Hb,Hc)))). inversion Ha. inversion Hb. subst. easy.
  - subst. inversion H1; try easy. subst. destruct H5; try easy.
    destruct H as (t1,(t2,(Ha,(Hb,Hc)))). easy.
  - subst. apply IHys0; try easy.
  - subst. destruct H5; try easy. destruct H as (t1,(t2,(Ha,(Hb,Hc)))). easy.
  - subst. destruct H5; try easy. destruct H as (t1,(t2,(Ha,(Hb,Hc)))). inversion Ha. subst. 
    inversion H1. subst. easy. subst. easy.
Qed.

Lemma canon_rep_part_helper_recv : forall n ys1 x4 p ys,
    onth n ys1 = Some x4 ->
    isMerge (ltt_recv p ys) ys1 -> 
    exists ys1', x4 = ltt_recv p ys1'.
Proof. 
  induction n; intros; try easy.
  - destruct ys1; try easy. simpl in *. subst. 
    inversion H0. subst. exists ys. easy.
    subst. exists ys. easy.
  - destruct ys1; try easy.
    specialize(IHn ys1 x4 p ys). apply IHn; try easy.
    inversion H0; try easy. subst. destruct n; try easy.
Qed.

Lemma canon_rep_part_helper_send : forall n ys2 x3 q x,
    onth n ys2 = Some x3 ->
    isMerge (ltt_send q x) ys2 ->
    exists ys2', x3 = ltt_send q ys2'.
Proof. intro n.
       induction n; intros.
       - inversion H0. subst. simpl in H. inversion H. subst.
         exists x. easy.
         subst. simpl in H. easy.
         subst. simpl in H. inversion H. subst.
       - exists x. easy.
       - destruct ys2; try easy.
         inversion H0. subst. destruct n; try easy.
         subst.
         specialize(IHn ys2 x3 q x). apply IHn; try easy.
         subst.
         specialize(IHn ys2 x3 q x). apply IHn; try easy.
Qed.

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
Qed.

Lemma merge_inv : forall T a xs, isMerge T (a :: xs) -> a = None \/ a = Some T.
Proof.
  intros. inversion H; subst; try easy. right. easy. left. easy. right. easy.
Qed.

Lemma merge_onth_recv : forall n p LQ ys1 gqT,
      isMerge (ltt_recv p LQ) ys1 ->
      onth n ys1 = Some gqT -> 
      exists LQ', gqT = ltt_recv p LQ'.
Proof. intros. eapply canon_rep_part_helper_recv. eauto. eauto. Qed.

Lemma merge_onth_send : forall n q LP ys0 gpT,
      isMerge (ltt_send q LP) ys0 ->
      onth n ys0 = Some gpT ->
      exists LP', gpT = (ltt_send q LP').
Proof. intros. eapply canon_rep_part_helper_send. eauto. eauto. Qed.

Lemma triv_merge_ltt_end : forall ys0,
    isMerge ltt_end ys0 -> List.Forall (fun u => u = None \/ u = Some ltt_end) ys0.
Proof.
  induction ys0; intros; try easy.
  inversion H.
  - subst. constructor; try easy. right. easy.
  - subst. specialize(IHys0 H2). constructor; try easy. left. easy.
  - subst. constructor; try easy. right. easy. 
    apply IHys0; try easy.
Qed.

Lemma merge_label_recv : forall Mp LQ' LQ0' T k l p,
          isMerge (ltt_recv p LQ') Mp ->
          onth k Mp = Some (ltt_recv p LQ0') ->
          onth l LQ0' = Some T ->
          exists T', onth l LQ' = Some T'.
Proof. intros Mp.
  induction Mp; intros; try easy.
  - inversion H. subst. 
    destruct k; try easy. simpl in H0. inversion H0. subst. exists T. easy.
  - simpl in H0. destruct k; try easy.
  - subst. destruct k; try easy.
    specialize(IHMp LQ' LQ0' T k l p). apply IHMp; try easy.
  - subst. destruct k; try easy. simpl in H0. inversion H0. subst. exists T. easy.
  - specialize(IHMp LQ' LQ0' T k l p). apply IHMp; try easy.
Qed.

Lemma merge_label_send : forall Mq LP' LP0' T k l q,
          isMerge (ltt_send q LP') Mq ->
          onth k Mq = Some (ltt_send q LP0') ->
          onth l LP0' = Some T ->
          exists T', onth l LP' = Some T'. 
Proof. intro Mq.
  induction Mq; intros; try easy.
  - inversion H. subst. 
    destruct k; try easy. simpl in H0. inversion H0. subst. exists T. easy.
  - simpl in H0. destruct k; try easy.
  - subst. destruct k; try easy.
    specialize(IHMq LP' LP0' T k l q). apply IHMq; try easy.
  - subst. destruct k; try easy. simpl in H0. inversion H0. subst. exists T. easy.
  - specialize(IHMq LP' LP0' T k l q). apply IHMq; try easy.
Qed.

Lemma merge_send_T : forall n T ys q lp,
        isMerge T ys -> 
        onth n ys = Some (ltt_send q lp) -> 
        exists lp', T = ltt_send q lp'.
Proof.
  induction n; intros; try easy.
  destruct ys; try easy. simpl in H0. subst.
  - inversion H. subst. exists lp. easy. 
  - subst. exists lp. easy.
  destruct ys; try easy. specialize(IHn T ys q lp).
  inversion H.
  - subst. destruct n; try easy.
  - subst. apply IHn; try easy.
  - subst. apply IHn; try easy.
Qed.

Lemma merge_recv_T : forall n T ys q lp,
        isMerge T ys -> 
        onth n ys = Some (ltt_recv q lp) -> 
        exists lp', T = ltt_recv q lp'.
Proof.
  induction n; intros; try easy.
  destruct ys; try easy. simpl in H0. subst.
  - inversion H. subst. exists lp. easy. 
  - subst. exists lp. easy.
  destruct ys; try easy. specialize(IHn T ys q lp).
  inversion H.
  - subst. destruct n; try easy.
  - subst. apply IHn; try easy.
  - subst. apply IHn; try easy.
Qed.
  
Lemma merge_label_sendb : forall ys0 LP LP' ST n l q,
      isMerge (ltt_send q LP) ys0 ->
      onth n ys0 = Some (ltt_send q LP') ->
      onth l LP = Some ST ->
      onth l LP' = Some ST.
Proof. intro ys0.
  induction ys0; intros; try easy.
  - destruct n; try easy. 
    - simpl in *. subst. 
      inversion H. subst.
      - easy.
      - subst. easy.
    - inversion H. subst.
      destruct n; try easy.
      subst. specialize(IHys0 LP LP' ST n l q). apply IHys0; try easy.
      subst. specialize(IHys0 LP LP' ST n l q). apply IHys0; try easy.
Qed.

Lemma merge_constr : forall p LQ ys1 n,
          isMerge (ltt_recv p LQ) ys1 ->
          onth n ys1 = Some ltt_end ->
          False.
Proof. intros p LQ ys1 n.
  revert ys1. induction n; intros; try easy.
  - destruct ys1; try easy. simpl in H0. subst. inversion H; try easy.
  - destruct ys1; try easy. 
    inversion H. subst. destruct n; try easy.
    - subst. specialize(IHn ys1). apply IHn; try easy.
    - subst. specialize(IHn ys1). apply IHn; try easy.
Qed.

Lemma merge_consts : forall q LP ys0 n,
          isMerge (ltt_send q LP) ys0 -> 
          onth n ys0 = Some ltt_end -> 
          False.
Proof. intros q LP ys0 n.
  revert ys0. induction n; intros; try easy.
  - destruct ys0; try easy. simpl in H0. subst. inversion H; try easy.
  - destruct ys0; try easy. 
    inversion H. subst. destruct n; try easy.
    - subst. specialize(IHn ys0). apply IHn; try easy.
    - subst. specialize(IHn ys0). apply IHn; try easy.
Qed.

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
Proof.
  induction Mp; intros; try easy.
  - destruct k; try easy. simpl in H0. subst.
    - inversion H. subst. easy. subst. easy.
    - inversion H. subst. destruct k; try easy.
      subst. specialize(IHMp LQ' LQ0' T k l p). apply IHMp; try easy.
      subst. specialize(IHMp LQ' LQ0' T k l p). apply IHMp; try easy.
Qed.

Lemma merge_label_send_s : forall Mq LP' LP0' T k l q,
          isMerge (ltt_send q LP') Mq ->
          onth k Mq = Some (ltt_send q LP0') ->
          onth l LP0' = Some T ->
          onth l LP' = Some T. 
Proof.
  induction Mq; intros; try easy.
  - destruct k; try easy. simpl in H0. subst.
    - inversion H. subst. easy. subst. easy.
    - inversion H. subst. destruct k; try easy.
      subst. specialize(IHMq LP' LP0' T k l q). apply IHMq; try easy.
      subst. specialize(IHMq LP' LP0' T k l q). apply IHMq; try easy.
Qed.

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
Proof.
  induction ys0; intros; try easy.
  destruct ys1; try easy. inversion H. subst. clear H.
  specialize(merge_inv (ltt_recv p QT) a ys0 H0); intros.
  specialize(merge_inv (ltt_send q PT) o ys1 H1); intros.
  
  destruct H.
  - subst. inversion H0. subst. 
    destruct H2. subst. inversion H1. subst.
    specialize(IHys0 ys1 p q PT QT). apply IHys0; try easy.
    subst. destruct H5; try easy. destruct H as (l1,(l2,(Ha,Hb))). easy.
  - subst.
    destruct H2. subst. destruct H5; try easy.
    destruct H as (l1,(l2,(Ha,Hb))). easy.
    subst. destruct H5; try easy.
    destruct H as (l1,(l2,(Ha,(Hb,Hc)))). inversion Ha. subst. inversion Hb. subst.
    easy.
Qed.
 
Lemma merge_inv_ss : forall n T ys1 t1,
        isMerge T ys1 -> 
        onth n ys1 = Some t1 -> 
        t1 = T.
Proof.
  induction n; intros.
  - destruct ys1; try easy. simpl in H0. subst.
    inversion H; try easy.
  - destruct ys1; try easy.
    specialize(IHn T ys1 t1).
    inversion H; try easy.
    - subst. destruct n; try easy.
    - subst. apply IHn; try easy.
    - subst. apply IHn; try easy.
Qed.
 
Variant projection (R: gtt -> part -> ltt -> Prop): gtt -> part -> ltt -> Prop :=
  | proj_end : forall g r, 
               (isgPartsC r g -> False) -> 
               projection R g r (ltt_end)
  | proj_in  : forall p r xs ys,
               p <> r ->
               (isgPartsC r (gtt_send p r xs)) ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some(s, t) /\ R g r t)) xs ys ->
               projection R (gtt_send p r xs) r (ltt_recv p ys)
  | proj_out : forall r q xs ys,
               r <> q ->
               (isgPartsC r (gtt_send r q xs)) ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some(s, t) /\ R g r t)) xs ys ->
               projection R (gtt_send r q xs) r (ltt_send q ys)
  | proj_cont: forall p q r xs ys t,
               p <> q ->
               q <> r ->
               p <> r ->
               (isgPartsC r (gtt_send p q xs)) ->
               List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some t /\ R g r t)) xs ys ->
               isMerge t ys ->
               projection R (gtt_send p q xs) r t.

Definition projectionC g r t := paco3 projection bot3 g r t.

Definition projectableA G := forall pt, exists T, projectionC G pt T.

Lemma proj_mon: monotone3 projection.
Proof. unfold monotone3.
       intros.
       induction IN; intros.
       - constructor. easy.
       - constructor; try easy. 
         revert ys H1. clear H0.
         induction xs; intros.
         + subst. inversion H1. constructor.
         + subst. inversion H1. constructor.
           destruct H3 as [(H3a, H3b) | (s,(g,(t,(Ht1,(Ht2,Ht3)))))].
           subst. left. easy.
           subst. right. exists s. exists g. exists t.
           split. easy. split. easy. apply LE. easy.
           apply IHxs. easy.
       - constructor. easy. easy.
         revert ys H1. clear H0.
         induction xs; intros.
         + subst. inversion H1. constructor.
         + subst. inversion H1. constructor.
           destruct H3 as [(H3a, H3b) | (s,(g,(t,(Ht1,(Ht2,Ht3)))))].
           subst. left. easy.
           subst. right. exists s. exists g. exists t.
           split. easy. split. easy. apply LE. easy.
           apply IHxs. easy.
       - apply proj_cont with (ys := ys); try easy.
         revert H3. apply Forall2_mono; intros.
         destruct H3. left. easy.
         destruct H3. destruct H3. destruct H3. destruct H3. destruct H5. subst.
         right. exists x0. exists x1. exists x2. split. easy. split. easy.
         apply LE; try easy.
Qed.

Lemma proj_forward : forall p q xs, 
  wfgC (gtt_send p q xs) ->
  projectableA (gtt_send p q xs) -> 
  List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ projectableA g)) xs.
Proof.
  intros.
  apply Forall_forall; intros.
  destruct x. 
  - destruct p0. right. exists s. exists g. split. easy.
    unfold projectableA in *.
    intros. specialize(H0 pt). destruct H0 as (T, H0).
    specialize(in_some_implies_onth (s, g) xs H1); intros.
    destruct H2 as (n, H2). clear H1.
    pinversion H0; try easy.
    - subst. 
      assert(p <> q).
      {
        unfold wfgC in H. 
        destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))).
        specialize(guard_breakG_s2 (gtt_send p q xs) Gl Hc Hb Ha); intros.
        destruct H as (Gl2,(Hta,(Htb,(Htc,Htd)))).
        destruct Hta. subst. pinversion Htd; try easy. apply gttT_mon.
        destruct H as (p1,(q1,(lis,Hte))). subst. pinversion Htd; try easy. subst.
        inversion Htc; try easy.
        apply gttT_mon.
      }
      specialize(wfgC_after_step_all H3 H); intros.
      specialize(some_onth_implies_In n xs (s, g) H2); intros.
      specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) xs); intros.
      destruct H6. specialize(H6 H4). clear H7 H4.
      specialize(H6 (Some (s, g)) H5). destruct H6; try easy.
      destruct H4 as (st,(g0,(Ha,Hb))). inversion Ha. subst. clear H5 Ha.
      specialize(decidable_isgPartsC g0 pt Hb); intros.
      unfold decidable in H4. unfold not in H4.
      destruct H4.
      - assert False. apply H1.
        - case_eq (eqb pt p); intros.
          assert (pt = p). apply eqb_eq; try easy. subst. apply triv_pt_p; try easy.
        - case_eq (eqb pt q); intros.
          assert (pt = q). apply eqb_eq; try easy. subst. apply triv_pt_q; try easy.
        - assert (pt <> p). apply eqb_neq; try easy. 
          assert (pt <> q). apply eqb_neq; try easy.
          apply part_cont_b with (n := n) (s := st) (g := g0); try easy. easy.
      - exists ltt_end. pfold. constructor; try easy.
    - subst.
      clear H8 H5 H0 H. revert H9 H2.
      revert xs pt ys s g. clear p.
      induction n; intros; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H9. subst. clear H9.
        simpl in H2. subst. destruct H3; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
        inversion Ha. subst. exists t1. destruct Hc; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H9. subst. clear H9.
        specialize(IHn xs pt ys s g). apply IHn; try easy.
    - subst.
      clear H8 H5 H0 H. revert H9 H2.
      revert xs pt ys s g. clear q.
      induction n; intros; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H9. subst. clear H9.
        simpl in H2. subst. destruct H3; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
        inversion Ha. subst. exists t1. destruct Hc; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H9. subst. clear H9.
        specialize(IHn xs pt ys s g). apply IHn; try easy.
    - subst. clear H12 H8 H7 H6 H5 H0 H.
      revert H2 H11.
      revert xs pt s g ys. clear p q T.
      induction n; intros; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H11. subst. clear H11.
        simpl in H2. subst. destruct H3; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
        inversion Ha. subst.
        exists t1. destruct Hc; try easy.
      - destruct xs; try easy. destruct ys; try easy.
        inversion H11. subst. clear H11.
        specialize(IHn xs pt s g ys). apply IHn; try easy.
    apply proj_mon.
    left. easy.
Qed.

Lemma pmergeCR_helper : forall n ys ys0 xs r s g ctxG,
    Forall (fun u : option ltt => u = None \/ u = Some ltt_end) ys0 -> 
    Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys -> 
    Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys0 -> 
    Forall2
       (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys -> 
    onth n ys = Some (s, g) -> 
    exists g', wfgC g /\
    onth n ys0 = Some ltt_end /\ projectionC g r ltt_end /\
    onth n xs = Some(s, g') /\ typ_gtth ctxG g' g.
Proof.
  induction n; intros.
  - destruct ys; try easy. destruct xs; try easy. destruct ys0; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    simpl in H3. subst. inversion H. subst. clear H.
    destruct H8; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
    destruct H6; try easy. destruct H as (s2,(g2,(Hd,He))). inversion Hd. subst.
    destruct H5; try easy. destruct H as (s3,(g3,(g4,(Hf,(Hg,Hh))))). inversion Hg. subst.
    destruct H2; try easy. inversion H. subst.
    exists g3. destruct Hc; try easy.
  - destruct ys; try easy. destruct xs; try easy. destruct ys0; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    simpl in H3. subst. inversion H. subst. clear H.
    specialize(IHn ys ys0 xs r s g ctxG). apply IHn; try easy.
Qed.

Lemma pmergeCR: forall G r,
          wfgC G ->
          projectionC G r ltt_end ->
          (isgPartsC r G -> False).
Proof. intros.
  specialize(balanced_to_tree G r H H1); intros.
  destruct H2 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd.
  revert Hc Hb Ha. rename H1 into Ht.
  revert H0 H Ht. revert G r ctxG.
  induction Gl using gtth_ind_ref; intros; try easy.
  - inversion Ha. subst.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send r q lsg) \/ u = Some (gtt_send q r lsg) \/ u = Some gtt_end)) ctxG); intros.
    destruct H1. specialize(H1 Hc). clear Hc H2. 
    specialize(some_onth_implies_In n ctxG G H3); intros.
    specialize(H1 (Some G) H2). destruct H1; try easy.
    destruct H1 as (q,(lsg,Hd)).
    - destruct Hd. inversion H1. subst. pinversion H0; try easy.  
      apply proj_mon.
    - destruct H1. inversion H1. subst. pinversion H0; try easy.
      apply proj_mon.
    - inversion H1. subst.
      specialize(part_break gtt_end r H Ht); intros.
      destruct H4 as (Gl,(Hta,(Htb,(Htc,Htd)))).
      destruct Htd. subst. inversion Htb; try easy.
      destruct H4 as (p1,(q1,(lis1,Htd))). subst.
      pinversion Hta; try easy. apply gttT_mon. 
  - inversion Ha. subst.
    pinversion H0; try easy. subst.
    specialize(part_cont ys r p q); intros.
    assert(exists (n : fin) (s : sort) (g : gtt), onth n ys = Some (s, g) /\ isgPartsC r g).
    apply H2; try easy.
    destruct H3 as (n,(s,(g,(Hd,He)))). clear H2 H10.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G : gtt) (r : string) (ctxG : seq.seq (option gtt)),
           projectionC G r ltt_end ->
           wfgC G ->
           isgPartsC r G ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some (gtt_send r q lsg) \/ u0 = Some (gtt_send q r lsg) \/ u0 = Some gtt_end))
             ctxG -> (ishParts r g -> False) -> typ_gtth ctxG g G -> False))) xs); intros.
    destruct H2. specialize(H2 H). clear H H3.
    specialize(triv_merge_ltt_end ys0 H14); intros.
    specialize(wfgC_after_step_all H5 H1); intros.
    clear Ht H1 H0 Ha H7 H5 H6 H9.
    specialize(pmergeCR_helper n ys ys0 xs r s g ctxG); intros.
    assert(exists g' : gtth,
       wfgC g /\
       onth n ys0 = Some ltt_end /\
       projectionC g r ltt_end /\ onth n xs = Some (s, g') /\ typ_gtth ctxG g' g).
    apply H0; try easy. clear H0 H3 H H13 H8.
    destruct H1 as (g',(Hf,(Hg,(Hh,(Hi,Hj))))).
    specialize(some_onth_implies_In n xs (s, g') Hi); intros.
    specialize(H2 (Some (s, g')) H).
    destruct H2; try easy. destruct H0 as (s1,(g1,(Hk,Hl))). inversion Hk. subst.
    specialize(Hl g r ctxG).
    apply Hl; try easy.
    specialize(ishParts_n Hb Hi); intros. apply H0; try easy.
  apply proj_mon.
Qed.

Lemma pmergeCR_s : forall G r,
    projectionC G r ltt_end ->
    (isgPartsC r G -> False).
Proof.
  intros.
  unfold isgPartsC in H0.
  destruct H0 as (Gl,(Ha,(Hb,Hc))).
  specialize(isgParts_depth_exists r Gl Hc); intros. destruct H0 as (n, H0). clear Hc.
  revert H0 Hb Ha H. revert G r Gl.
  induction n; intros.
  - inversion H0. 
    subst. 
    pinversion Ha. subst. pinversion H; try easy. subst.
    apply H1. unfold isgPartsC. exists (g_send r q lis). split. pfold. easy. 
    split. easy. apply isgParts_depth_back with (n := 0); try easy.
    apply proj_mon.
    apply gttT_mon.
  - subst. 
    pinversion Ha. subst. pinversion H; try easy. subst.
    apply H1. unfold isgPartsC. exists (g_send p r lis). split. pfold. easy. 
    split. easy. apply isgParts_depth_back with (n := 0); try easy.
    apply proj_mon.
    apply gttT_mon.
  inversion H0.
  - subst.
    pinversion Ha. subst.
    specialize(subst_parts_depth 0 0 n r g g Q H3 H2); intros.
    specialize(IHn G r Q). apply IHn; try easy.
    intros. specialize(Hb n0). destruct Hb.
    inversion H5. subst. exists 0. constructor.
    - subst. specialize(subst_injG 0 0 (g_rec g) g Q Q0 H7 H3); intros. subst.
      exists m. easy.
      apply gttT_mon.
  - subst. pinversion H; try easy.
    - subst. apply H1. unfold isgPartsC. exists (g_send p q lis).
      split. easy. split. easy. apply isgParts_depth_back with (n := S n); try easy.
    - subst.
      specialize(triv_merge_ltt_end ys H10); intros.
      pinversion Ha. subst.
      specialize(guard_cont Hb); intros.
      specialize(Forall2_prop_r k lis xs (s, g) (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : global) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) H4 H13); intros.
       destruct H14 as (p1,(Hc,Hd)).
       destruct Hd; try easy. destruct H14 as (s1,(g1,(g2,(He,(Hf,Hg))))). inversion He. subst. clear H13.
       specialize(Forall2_prop_r k xs ys (s1, g2) (fun (u : option (sort * gtt)) (v : option ltt) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtt) (t : ltt),
           u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) Hf H9); intros.
       destruct H13 as (p1,(Hh,Hi)).
       destruct Hi; try easy. destruct H13 as (s2,(g3,(g4,(Hj,(Hk,Hl))))). inversion Hj. subst.
       clear H9.
       specialize(Forall_prop k lis (s2, g1) (fun u : option (sort * global) =>
         u = None \/
         (exists (s : sort) (g : global),
            u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) H4 H12); intros.
       destruct H9; try easy. destruct H9 as (s3,(g5,(Hm,Hn))). inversion Hm. subst. clear H12.
       specialize(Forall_prop k ys g4 (fun u : option ltt => u = None \/ u = Some ltt_end) Hk H11); intros.
       destruct H9; try easy. inversion H9. subst.
       pclearbot. destruct Hl; try easy.
       specialize(IHn g3 r g5). apply IHn; try easy.
     apply gttT_mon.
     apply proj_mon.
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
            split. 
            - destruct Hlb. intros. destruct n0. exists 0. constructor.
              specialize(H0 n0). specialize(Htb (S n0)).
              destruct Htb. destruct H0. exists (Nat.max x0 x).
              constructor. inversion H4. subst.
              clear Hsb H3 H4 Htc Hte Ht2 H1 Hb H H2 Htd Hla. revert H8 H0.
              revert st G1 x0 lis x n0. clear s s' ys p g.
              induction n; intros; try easy. destruct lis; try easy.
              - constructor; try easy. right. exists st. exists G1. split. easy.
                specialize(guardG_more n0 x0 (Nat.max x0 x) G1); intros. apply H; try easy.
                apply max_l; try easy.
              - inversion H8. subst. constructor; try easy. right. exists st. exists G1.
                split. easy. specialize(guardG_more n0 x0 (Nat.max x0 x) G1); intros. apply H; try easy.
                apply max_l; try easy.
                apply Forall_forall; intros. 
                specialize(Forall_forall (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ guardG n0 x g)) lis); intros.
                destruct H1. specialize(H1 H3). clear H4 H3. specialize(H1 x1 H).
                destruct H1. left. easy. destruct H1 as (s1,(g1,(Ha,Hb))). subst.
                right. exists s1. exists g1. split. easy.
                specialize(guardG_more n0 x (Nat.max x0 x) g1); intros. apply H1; try easy.
                apply max_r; try easy.
              - destruct lis; try easy. constructor; try easy. left. easy.
                specialize(IHn st G1 x0 nil x n0 H8 H0). apply IHn; try easy.
                inversion H8. subst. clear H8.
                specialize(IHn st G1 x0 lis x n0 H3 H0). constructor; try easy.
                destruct H2. left. easy.
                destruct H as (s,(g,(Ha,Hb))). subst. right. exists s. exists g.
                split. easy.
                specialize(guardG_more n0 x (Nat.max x0 x) g); intros. apply H; try easy.
                apply max_r; try easy. 
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
    specialize(triv_merge_ltt_end ys0 H12); intros. clear H12 H7 H6 H5 H1 H.
    revert H11 H2. clear H0 H8. clear s s'. revert p ys0.
    induction ys; intros; try easy.
    - destruct ys0; try easy. inversion H2. subst. clear H2. inversion H11. subst. clear H11.
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

Lemma proj_end_inj_helper : forall n1 ys0 ys1 ys xs ctxG s1 g1 r,
      Forall (fun u : option ltt => u = None \/ u = Some ltt_end) ys0 -> 
      Forall
      (fun u : option (sort * gtt) =>
       u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys -> 
      Forall2
       (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys0 -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys1 ->
      onth n1 ys = Some (s1, g1) -> 
      exists g2 t,
      onth n1 xs = Some(s1, g2) /\ typ_gtth ctxG g2 g1 /\
      onth n1 ys0 = Some ltt_end /\ projectionC g1 r ltt_end /\
      onth n1 ys1 = Some t /\ projectionC g1 r t /\ wfgC g1.
Proof.
  induction n1; intros; try easy.
  - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy.
    destruct xs; try easy.
    inversion H3. subst. clear H3. inversion H2. subst. clear H2.
    inversion H1. subst. clear H1. inversion H0. subst. clear H0.
    inversion H. subst. clear H.
    simpl in H4. subst.
    destruct H6; try easy. destruct H as (s2,(g2,(g3,(Ha,(Hb,Hc))))). inversion Hb. subst.
    destruct H3; try easy. destruct H as (s3,(g4,(Hd,He))). inversion Hd. subst.
    destruct H7; try easy. destruct H as (s4,(g5,(t1,(Hf,(Hg,Hh))))). inversion Hf. subst.
    destruct H8; try easy. destruct H as (s5,(g6,(t2,(Hi,(Hj,Hk))))). inversion Hi. subst.
    destruct H2; try easy. inversion H. subst.
    simpl. exists g2. exists t2. destruct Hh; try easy. destruct Hk; try easy.
  - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy.
    destruct xs; try easy.
    inversion H3. subst. clear H3. inversion H2. subst. clear H2.
    inversion H1. subst. clear H1. inversion H0. subst. clear H0.
    inversion H. subst. clear H.
    specialize(IHn1 ys0 ys1 ys xs ctxG s1 g1 r). apply IHn1; try easy.
Qed.

Lemma proj_end_inj : forall g t p,
          wfgC g -> 
          projectionC g p ltt_end -> 
          projectionC g p t -> 
          t = ltt_end.
Proof.
  intros.
  specialize(decidable_isgPartsC g p H); intros. unfold decidable in H2.
  destruct H2.
  - specialize(balanced_to_tree g p H H2); intros.
    destruct H3 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd. rename H2 into Ht.
    revert Hc Hb Ha H1 H0 H Ht. revert ctxG p t g.
    induction Gl using gtth_ind_ref; intros.
    - inversion Ha. subst.
      specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
      destruct H2. specialize(H2 Hc). clear Hc H3.
      specialize(some_onth_implies_In n ctxG g H4); intros.
      specialize(H2 (Some g) H3). destruct H2; try easy.
      destruct H2 as (q1,(lsg1,Hc)). 
      - destruct Hc. inversion H2. subst. pinversion H0; try easy. 
        apply proj_mon.
      - destruct H2. inversion H2. subst. pinversion H0; try easy.
        apply proj_mon.
      - inversion H2. subst. pinversion H1; try easy. apply proj_mon.
    - inversion Ha. subst.
      pinversion H0; try easy. subst.
      pinversion H1; try easy. subst. clear H17 H16 H13 H12. rename p0 into r.
      specialize(part_cont ys r p q H11); intros.
      assert(exists (n : fin) (s : sort) (g : gtt), onth n ys = Some (s, g) /\ isgPartsC r g).
      apply H3; try easy.
      clear H3. destruct H4 as (n1,(s1,(g1,(He,Hf)))).
      specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (ctxG : seq.seq (option gtt)) (p : string) (t : ltt) (g0 : gtt),
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some (gtt_send p q lsg) \/ u0 = Some (gtt_send q p lsg) \/ u0 = Some gtt_end))
             ctxG ->
           (ishParts p g -> False) ->
           typ_gtth ctxG g g0 ->
           projectionC g0 p t -> projectionC g0 p ltt_end -> wfgC g0 -> isgPartsC p g0 -> t = ltt_end)))
      xs); intros.
      destruct H3. specialize(H3 H). clear H H4.
      specialize(wfgC_after_step_all H6 H2); intros.
      specialize(triv_merge_ltt_end ys0 H15); intros.
      specialize(proj_end_inj_helper n1 ys0 ys1 ys xs ctxG s1 g1 r); intros.
      assert(exists (g2 : gtth) (t : ltt),
       onth n1 xs = Some (s1, g2) /\
       typ_gtth ctxG g2 g1 /\
       onth n1 ys0 = Some ltt_end /\
       projectionC g1 r ltt_end /\ onth n1 ys1 = Some t /\ projectionC g1 r t /\ wfgC g1).
      apply H5; try easy. clear H5 H4 H H20 H14 H9.
      destruct H12 as (g2,(t1,(Hta,(Htb,(Htc,(Htd,(Hte,Htf))))))).
      specialize(some_onth_implies_In n1 xs (s1, g2) Hta); intros.
      specialize(H3 (Some (s1, g2)) H). destruct H3; try easy.
      destruct H3 as (s2,(g3,(Hsa,Hsb))). inversion Hsa. subst.
      specialize(Hsb ctxG r t1 g1).
      assert(t1 = ltt_end). apply Hsb; try easy.
      specialize(ishParts_n Hb Hta); intros. apply H3; try easy. subst.
      specialize(merge_end_back n1 ys1 t); intros. apply H3; try easy.
      apply proj_mon. apply proj_mon.
  - unfold not in H2. pinversion H0; try easy.
    subst. pinversion H1; try easy.
    - subst. specialize(H2 H5). easy.
    - subst. specialize(H2 H5). easy.
    - subst. specialize(H2 H7). easy.
  apply proj_mon. 
  subst. specialize(H2 H6). easy. apply proj_mon.
Qed.

Theorem proj_inj : forall [g p t t'],
          wfgC g -> 
          projectionC g p t -> 
          projectionC g p t' -> 
          t = t'.
Proof.
  intros.
  apply lltExt. revert H H0 H1. revert t t' g. pcofix CIH; intros.
  specialize(decidable_isgPartsC g p H0); intros. unfold decidable in H.
  destruct H.
  pose proof H0 as Ht. unfold wfgC in H0. destruct H0 as (Gl,(Ha,(Hb,(Hc,Hd)))).
  specialize(balanced_to_tree g p Ht H); intros. clear Ha Hb Hc Hd. clear H. rename H0 into H.
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
    - subst. assert False. apply Hb. constructor. easy. subst.
      pinversion H1; try easy. subst.
      pfold. constructor.
      specialize(proj_inj_list ys ys1 ys0 p r); intros.
      apply H0; try easy. 
      specialize(wfgC_after_step_all H6 Ht); try easy.
      apply proj_mon.
    - subst. 
      pinversion H1; try easy. subst.
      {
        assert (List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists t t', u = Some t /\ v = Some t' /\ paco2 lttIso r t t')) ys1 ys0).
        {
          specialize(wfgC_after_step_all H11 Ht); intros.
          clear H20 H16 H15 H12 H11 H14 H10 H9 H6 H5 H7 H1 H2 Ht Ha.
          revert H0 H19 H13 H8 CIH Hc Hb H.
          revert p r s s' xs ctxG ys1 ys0. clear t t'.
          induction ys; intros; try easy.
          - destruct ys0; try easy. destruct ys1; try easy.
          - destruct ys0; try easy. destruct ys1; try easy. destruct xs; try easy.
            inversion H0. subst. clear H0. inversion H19. subst. clear H19.
            inversion H13. subst. clear H13. inversion H8. subst. clear H8.
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
  - unfold not in *.
    pinversion H1; try easy. 
    - subst. pinversion H2; try easy. subst. pfold. constructor.
    - subst. specialize(H3 H5). easy.
    - subst. specialize(H3 H5). easy.
    - subst. specialize(H3 H7). easy.
    apply proj_mon.
  - subst. specialize(H H4). easy.
  - subst. specialize(H H4). easy.
  - subst. specialize(H H6). easy.
  apply proj_mon.
Qed.

Lemma non_triv_proj_part : forall [G p q x],
    projectionC G p (ltt_send q x) -> isgPartsC p G.
Proof.
  intros. pinversion H; try easy.
  apply proj_mon.
Qed.

Lemma ctx_merge2 : forall s s0 s1 g1 l p q x,
    p <> s -> p <> s0 ->
    (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
       typ_gtth ctxG G' g1 /\
       (ishParts p G' -> False) /\
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
                   u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG /\
       usedCtx ctxG G') -> 
       (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
       typ_gtth ctxG G' (gtt_send s s0 l) /\
       (ishParts p G' -> False) /\
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
                   u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG /\
       usedCtx ctxG G') -> 
       (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
  typ_gtth ctxG G' (gtt_send s s0 (Some (s1, g1) :: l)) /\
  (ishParts p G' -> False) /\
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
                   u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG /\
  usedCtx ctxG G').
Proof.
  intros.
  destruct H1 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))).
  destruct H2 as (Gl2,(ctxJ,(He,(Hf,(Hg,Hh))))).
  inversion He. subst.
  - specialize(some_onth_implies_In n ctxJ (gtt_send s s0 l) H1); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxJ); intros.
    destruct H3. specialize(H3 Hg). clear H4 Hg.
    specialize(H3 (Some (gtt_send s s0 l)) H2). destruct H3; try easy.
    destruct H3 as (g2,(lsg,(Hi,(Hj,Hk)))). inversion Hi. subst. inversion H4. subst. easy.
  - subst.
    assert(exists Gl', typ_gtth (noneLis (List.length ctxJ) ++ ctxG) Gl' g1 /\ usedCtx (noneLis (List.length ctxJ) ++ ctxG) Gl' /\ (ishParts p Gl' -> False)).
    {
      clear Hc Hf He Hg Hh H5 H7.
      clear H H0.
      revert Ha Hb Hd. revert g1 p Gl ctxG ctxJ. clear s s0 s1 l xs.
      apply shift_to; try easy.
    }
    destruct H1 as (Gl',(H1,(H2,Htm))).
    exists (gtth_send s s0 (Some (s1, Gl') :: xs)). exists (ctxJ ++ ctxG).
    - split.
      constructor; try easy. apply SList_b; try easy.
      constructor; try easy.
      - right. exists s1. exists Gl'. exists g1. split. easy. split. easy.
        apply typ_gtth_pad_l; try easy.
      - revert H7. apply Forall2_mono; intros.
        destruct H3. left. easy.
        right. destruct H3 as (s2,(g2,(g3,(Hta,(Htb,Htc))))). subst.
        exists s2. exists g2. exists g3. split. easy. split. easy.
        apply typ_gtth_pad_r with (ctxG := ctxG); try easy.
    - split.
      intros. inversion H3. subst. easy. subst. easy. subst.
      destruct n.
      - simpl in H12. inversion H12. subst. apply Hb. easy.
      - apply Hf. apply ha_sendr with (n := n) (s := s2) (g := g); try easy.
    - split.
      clear Htm H2 H1 H7 H5 Hh He Hf Hd Hb Ha H0 H. revert Hg Hc.
      revert p ctxG. clear s s0 s1 g1 l Gl xs Gl'.
      induction ctxJ; intros; try easy. inversion Hg. subst. clear Hg.
      specialize(IHctxJ p ctxG H2 Hc). constructor; try easy.
    - inversion Hh. subst.
      apply used_con with (ctxGLis := Some (noneLis (Datatypes.length ctxJ) ++ ctxG) :: ctxGLis); try easy.
      apply cmconss with (t := ctxJ); try easy.
      clear H10 H8 Htm H2 H1 H7 H5  Hh Hg He Hf Hd Hc Hb Ha H0 H.
      clear ctxGLis Gl' xs Gl p l g1 s1 s s0.
      induction ctxJ; intros; try easy. simpl. constructor.
      constructor; try easy. 
      destruct a. right. right. left. exists g. easy.
      left. easy.
    - constructor; try easy. right. exists (noneLis (Datatypes.length ctxJ) ++ ctxG).
      exists s1. exists Gl'. easy.
Qed.


Lemma canon_rep_11 : forall G p q x,
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
    specialize(non_triv_proj_part H0); intros Ht1.
    pose proof H as Ht. unfold wfgC in H. destruct H as (G',(Ha,(Hb,(Hc,Hd)))). clear Hc Hb Ha.
    specialize(balanced_to_tree G p Ht Ht1); intros. destruct H as (Gl,(ctxG,(Hta,(Htb,(Htc,Htd))))).
    
    clear Ht Hd Htd Ht1.
    clear G'.
    revert Htc Htb Hta H0. revert G p q x ctxG.
    induction Gl using gtth_ind_ref; intros; try easy.
    - inversion Hta. subst. exists (gtth_hol n).
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
      - pinversion H0; try easy. subst. clear H7. clear H10.
        revert H11. clear H8 H1 H H2 H0 Hta Htb. clear ctxG. revert lsg x p q.
        induction n; intros; try easy. simpl. split.
        - constructor; try easy. right. exists (gtt_send p q lsg). exists lsg.
          split. easy. split. easy. revert H11.
          apply Forall2_mono; intros. destruct H. left. easy.
          right. destruct H as (s,(g,(t,(Ha,(Hb,Hc))))). subst. exists s. exists t. exists g. pclearbot. easy.
          specialize(used_hol 0 (gtt_send p q lsg)); intros. easy.
        - specialize(IHn lsg x p q H11). split. constructor; try easy. left. easy.
          constructor.
        apply proj_mon.
      - destruct H. inversion H. subst. pinversion H0; try easy. apply proj_mon.
      - inversion H. subst. pinversion H0; try easy. apply proj_mon.
    - inversion Hta. subst.
      rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
      - assert(List.Forall2 (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ 
           exists (G' : gtth) (ctxJ : seq.seq (option gtt)),
             typ_gtth ctxJ G' g' /\
             (ishParts p G' -> False) /\
             Forall
               (fun u0 : option gtt =>
                u0 = None \/
                (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                   u0 = Some g0 /\
                   g0 = gtt_send p q lsg /\
                   Forall2
                     (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                      u1 = None /\ v = None \/
                      (exists (s0 : sort) (t : ltt) (g' : gtt),
                         u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' p t)) lsg x)) ctxJ /\
             usedCtx ctxJ G')) xs ys).
        {
          clear H6 Hta.
          pinversion H0. subst. assert False. apply Htb. constructor. easy.
          subst. 
          clear H8 H6 H5 H4 H0.
          revert H12 H11 H7 Htb Htc H. revert xs p q x ys ctxG s s'.
          induction ys0; intros; try easy.
          destruct ys; try easy. destruct xs; try easy. 
          specialize(IHys0 xs p q x ys ctxG s s').
          inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion H. subst. clear H.
          inversion H12.
          - subst.
            destruct ys; try easy. destruct xs; try easy.
            clear H6 H8 H5 IHys0.
            constructor; try easy. destruct H4. left. easy.
            destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
            right. exists s1. exists g1. exists g2. split. easy. split. easy.
            destruct H3; try easy. destruct H as (s2,(g3,(t1,(Hd,(He,Hf))))). inversion Hd. subst.
            inversion He. subst. 
            destruct H2; try easy. destruct H as (s3,(g4,(Hg,Hh))). inversion Hg. subst.
            pclearbot.
            specialize(Hh g3 p q x ctxG). apply Hh; try easy.
            assert(onth 0 [Some (s3, g4)] = Some (s3, g4)). easy.
            specialize(ishParts_n Htb H); try easy.
          - subst.
            destruct H4. destruct H. subst.
            constructor; try easy. left. easy.
            apply IHys0; try easy.
            specialize(ishParts_hxs Htb); try easy.
            destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
            destruct H3; try easy. destruct H as (s2,(g3,(t1,(Hd,(He,Hf))))). easy.
          - subst.
            assert(Forall2
          (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
           u = None /\ v = None \/
           (exists (s : sort) (g : gtth) (g' : gtt),
              u = Some (s, g) /\
              v = Some (s, g') /\
              (exists (G' : gtth) (ctxJ : seq.seq (option gtt)),
                 typ_gtth ctxJ G' g' /\
                 (ishParts p G' -> False) /\
                 Forall
                   (fun u0 : option gtt =>
                    u0 = None \/
                    (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                       u0 = Some g0 /\
                       g0 = gtt_send p q lsg /\
                       Forall2
                         (fun (u1 : option (sort * gtt)) (v0 : option (sort * ltt)) =>
                          u1 = None /\ v0 = None \/
                          (exists (s0 : sort) (t : ltt) (g'0 : gtt),
                             u1 = Some (s0, g'0) /\ v0 = Some (s0, t) /\ projectionC g'0 p t)) lsg x))
                   ctxJ /\ usedCtx ctxJ G'))) xs ys).
            {
              apply IHys0; try easy.
              specialize(ishParts_hxs Htb); try easy.
            }
            constructor; try easy.
            clear H H1 H6 H8 H5 H12 IHys0.
            destruct H3; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Hb. subst.
            destruct H4; try easy. destruct H as (s2,(g2,(g3,(Hd,(He,Hf))))). inversion He. subst.
            destruct H2; try easy. destruct H as (s3,(g4,(Hg,Hh))). inversion Hg. subst.
            right. exists s3. exists g4. exists g3. split. easy. split. easy. pclearbot.
            specialize(Hh g3 p q x ctxG). apply Hh; try easy.
            specialize(ishParts_x Htb); try easy.
          apply proj_mon.
        }
        clear H7 Htb Htc H.
        - case_eq (eqb p s); intros.
          pinversion H0; try easy. subst.
          exists (gtth_hol 0). exists [Some (gtt_send p q ys)].
          - split. constructor. easy.
          - split. intros. inversion H2.
          - split. constructor; try easy. right. exists (gtt_send p q ys). exists ys.
            split. easy. split. easy.
            revert H11. apply Forall2_mono; intros; try easy.
            destruct H2. left. easy. right.
            destruct H2 as (s1,(g1,(t1,(Ha,(Hb,Hc))))). subst. exists s1. exists t1. exists g1.
            pclearbot. easy. 
          - assert(usedCtx (extendLis 0 (Some (gtt_send p q ys))) (gtth_hol 0)). constructor. simpl in H2. easy. subst.
            assert (p = s). apply eqb_eq; try easy. subst. easy.
            apply proj_mon.
        - case_eq (eqb p s'); intros.
          assert (p = s'). apply eqb_eq; try easy. subst.
          pinversion H0; try easy. apply proj_mon.
        - assert (p <> s). apply eqb_neq; try easy. 
          assert (p <> s'). apply eqb_neq; try easy.
      - clear H H2.
        clear H0 Hta.
        revert H3 H4 H1 H6. revert s s' p q x ys. clear ctxG.
        induction xs; intros; try easy.
        destruct ys; try easy. inversion H1. subst. clear H1.
        specialize(SList_f a xs H6); intros.
        specialize(IHxs s s' p q x ys H3 H4).
        destruct H.
        - assert(exists (G' : gtth) (ctxJ : seq.seq (option gtt)),
         typ_gtth ctxJ G' (gtt_send s s' ys) /\
         (ishParts p G' -> False) /\
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
                     u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxJ /\
         usedCtx ctxJ G'). apply IHxs; try easy. clear IHxs H8 H6.
          destruct H5.
          - destruct H1. subst.
            destruct H0 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))).
            inversion Ha. subst. 
            - specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option (sort * ltt)) =>
              u0 = None /\ v = None \/
              (exists (s : sort) (t : ltt) (g' : gtt),
                 u0 = Some (s, g') /\ v = Some (s, t) /\ projectionC g' p t)) lsg x)) ctxG); intros.
              destruct H1. specialize(H1 Hc). clear H2 Hc.
              specialize(some_onth_implies_In n ctxG (gtt_send s s' ys) H0); intros.
              specialize(H1 (Some (gtt_send s s' ys)) H2).
              destruct H1; try easy. destruct H1 as (g1,(lsg1,(He,(Hf,Hg)))). inversion He. subst.
              inversion H5. subst. easy.
            - subst. exists (gtth_send s s' (None :: xs0)). exists ctxG.
              - split. constructor. apply SList_b. easy.
                constructor; try easy. left. easy.
              - split. intros. apply Hb.
                inversion H0. subst. easy. subst. easy. subst.
                destruct n; try easy. apply ha_sendr with (n := n) (s := s0) (g := g); try easy.
              - split. easy.
              - inversion Hd. subst.
                apply used_con with (ctxGLis := None :: ctxGLis); try easy.
                constructor; try easy. constructor; try easy. left. easy.
          destruct H1 as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst. clear H.
          apply ctx_merge2; try easy.
        - destruct H as (H,(a0,Ht)). subst.
          destruct ys; try easy. clear H8 IHxs H6.
          destruct H5; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
          destruct Hc as (Gl,(ctxG,(Hc,(Hd,(He,Hf))))).
          exists (gtth_send s s' [Some (s1, Gl)]). exists ctxG.
          - split. constructor; try easy. constructor; try easy. 
            right. exists s1. exists Gl. exists g2. easy.
          - split. intros. apply Hd. inversion H. subst. easy. subst. easy. subst.
            destruct n; try easy. inversion H8. subst. easy.
            destruct n; try easy.
          - split. easy.
          - apply used_con with (ctxGLis := [Some ctxG]); try easy. constructor.
            constructor; try easy. right. exists ctxG. exists s1. exists Gl. easy.
Qed.

Lemma canon_rep_part : forall ctxG G' G p q x ys,
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
      clear H2 H1 H0 H3 H4 H10 H8 H12 H5 H14 H13 H6 H H7 H9 H15 H16 H17 H21 H22 H23 H24. clear H29 H26 H25 H34 H11 H28 H30.
      clear r s x1 x ys xs ctxG.
      revert H18 H27 H33. revert p q x0 x2 ys0 ys1 ys2.
      induction n; intros; try easy.
      - destruct ys0; try easy.
        destruct ys1; try easy.
        destruct ys2; try easy.
        simpl in *.
        inversion H27. subst. inversion H33. subst. clear H27 H33.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. inversion H. subst.
        destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2. inversion H0. subst.
        pclearbot. exists x4. exists x3. easy.
      - destruct ys0; try easy.
        destruct ys1; try easy.
        destruct ys2; try easy.
        simpl in *.
        inversion H27. subst. inversion H33. subst. clear H27 H33.
        apply IHn with (x0 := x0) (ys0 := ys0) (ys1 := ys1) (ys2 := ys2); try easy.
    }
    destruct H19. destruct H19. destruct H19. destruct H20. destruct H31.
    specialize(canon_rep_part_helper_recv n ys1 x4 p ys H32 H28); intros. destruct H35. subst.
    specialize(canon_rep_part_helper_send n ys2 x3 q x H31 H34); intros. destruct H35. subst.
    specialize(H6 x4 x5). apply H6; try easy.
    apply proj_mon.
    apply proj_mon.
Qed.

    
Lemma canon_rep_16 : forall G' ctxG G p q ys x, 
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
  - inversion H4. subst.
    inversion H1. subst.
    clear H2 H3 H1 H4.
    revert H0 H7 H. revert G p q ys x G0.
    induction n; intros; try easy.
    - simpl in *. inversion H7. subst.
      inversion H0. subst. clear H0 H4.
      destruct H3; try easy. destruct H0 as (g,(lsg,(Ha,(Hb,Hc)))).
      inversion Ha. subst.
      pinversion H; try easy. subst. clear H4.
      constructor; try easy. right. exists (gtt_send p q lsg). exists lsg.
      split. easy. split. easy. split. easy.
      revert H8. apply Forall2_mono; intros.
      destruct H0. left. easy. 
      destruct H0 as (s,(g,(t,(Hd,(He,Hf))))). subst. right. exists s. exists t. exists g.
      destruct Hf; try easy.
    apply proj_mon.
    simpl in *. inversion H0. subst. clear H0.
    specialize(IHn G p q ys x G0 H4).
    constructor. left. easy. apply IHn; try easy.
  - inversion H5. subst. 
    pinversion H0. subst.
    - assert False. apply H3. constructor. easy.
    - subst. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
      clear H14.
      clear H12.
      specialize(ctx_back s s' xs ys0 ctxG H5 H2); intros.
      destruct H6 as (ctxGLis,(H6,H7)).
      assert(Forall (fun u => u = None \/ exists ctxGi, u = Some ctxGi /\
        Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' p t)) lsg x /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' q t)) lsg ys)) ctxGi
      ) ctxGLis).
      {
        apply Forall_forall; intros.
        destruct x0. right.
        specialize(in_some_implies_onth l ctxGLis H8); intros.
        destruct H12 as (n, H12). rename l into ctxGi. exists ctxGi. split. easy.
        clear H8. clear H11 H9 H10 H13 H5 H2.
        assert(exists s g1 g2 t, onth n xs = Some (s, g1) /\ onth n ys0 = Some (s, g2) /\ typ_gtth ctxGi g1 g2 /\ usedCtx ctxGi g1 /\ onth n ys1 = Some t /\ projectionC g2 q t).
        {
          revert H12 H6 H17.
          clear H7 H18 H4 H3 H1 H0 H.
          revert xs q ys0 ys1 ctxGLis ctxGi. clear s s' ctxG p ys x.
          induction n; intros.
          - destruct ctxGLis; try easy. destruct xs; try easy. destruct ys0; try easy.
            destruct ys1; try easy. inversion H6. subst. clear H6.
            inversion H17. subst. clear H17.
            simpl in H12. subst.
            destruct H3; try easy. destruct H as (ctxG,(s1,(g1,(g2,(Ha,(Hb,(Hc,(Hd,He)))))))).
            inversion Ha. subst.
            destruct H2; try easy. destruct H as (s2,(g3,(t1,(Hf,(Hg,Hh))))). inversion Hf. subst.
            simpl. exists s2. exists g1. exists g3. exists t1. destruct Hh; try easy.
          - destruct ctxGLis; try easy. destruct xs; try easy. destruct ys0; try easy.
            destruct ys1; try easy. inversion H6. subst. clear H6.
            inversion H17. subst. clear H17.
            specialize(IHn xs q ys0 ys1 ctxGLis ctxGi). apply IHn; try easy.
        }
        destruct H2 as (s1,(g1,(g2,(t1,(Hta,(Htb,(Htc,(Htd,(Hte,Htf))))))))).
        clear H6 H17.
        specialize(some_onth_implies_In n xs (s1, g1) Hta); intros.
        specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (ctxG : seq.seq (option gtt)) (G : gtt) (p q : string)
             (ys x : seq.seq (option (sort * ltt))),
           projectionC G q (ltt_recv p ys) ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' p t)) lsg x)) ctxG ->
           usedCtx ctxG g ->
           (ishParts p g -> False) ->
           (ishParts q g -> False) ->
           typ_gtth ctxG g G ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' p t)) lsg x /\
                 Forall2
                   (fun (u1 : option (sort * gtt)) (v : option (sort * ltt)) =>
                    u1 = None /\ v = None \/
                    (exists (s0 : sort) (t : ltt) (g' : gtt),
                       u1 = Some (s0, g') /\ v = Some (s0, t) /\ projectionC g' q t)) lsg ys)) ctxG)))
      xs); intros.
        destruct H5. specialize(H5 H). clear H H6.
        specialize(H5 (Some (s1, g1)) H2). destruct H5; try easy.
        destruct H as(s2,(g3,(Ha,Hb))). inversion Ha. subst.
        specialize(Hb ctxGi g2 p q ys x).
        apply Hb; try easy.
        - specialize(merge_inv_ss n (ltt_recv p ys) ys1 t1); intros.
          assert(t1 = ltt_recv p ys). apply H; try easy. subst. easy.
        - specialize(mergeCtx_sl n ctxGLis ctxGi ctxG); intros.
          assert(Forall2R (fun u v : option gtt => u = v \/ u = None) ctxGi ctxG). apply H; try easy.
          clear H. clear Hb H2 Htf Hte Hta Htc Htd Ha Htb H12 H7 H18 H4 H3 H0.
          revert H5 H1.
          revert ctxG p q x. clear s s' xs ys ys0 ys1 ctxGLis n g2 t1 s2 g3.
          induction ctxGi; intros; try easy.
          - destruct ctxG; try easy. inversion H1. subst. clear H1. inversion H5. subst. clear H5.
            specialize(IHctxGi ctxG p q x H7 H3). constructor; try easy. clear H7 H3 IHctxGi.
            destruct H4. subst. easy. left. easy.
        - specialize(ishParts_n H3 Hta); try easy.
        - specialize(ishParts_n H4 Hta); try easy.
        left. easy.
      }
      clear H6 H18 H17 H13 H10 H9 H11 H5 H4 H3 H2 H1 H0 H. 
      revert H8 H7. revert ctxG p q ys x. clear s s' xs ys0 ys1.
      induction ctxGLis; intros; try easy.
      - inversion H8. subst. clear H8.
        inversion H7; try easy.
        - subst.
          destruct H1; try easy. destruct H as (ct1,(Ha,Hb)). inversion Ha. subst. easy.
        - subst.
          specialize(IHctxGLis ctxG p q ys x). apply IHctxGLis; try easy.
        - subst.
          specialize(IHctxGLis t p q ys x H2 H5). clear H2 H5.
          clear H7. destruct H1; try easy.
          destruct H as (t1,(Ha,Hb)). inversion Ha. subst. clear Ha.
          revert H4 Hb IHctxGLis. clear ctxGLis. revert p q ys t t1 x. 
          induction ctxG; intros; try easy.
          - inversion H4.
            - subst. easy.
            - subst. easy.
            subst. clear H4. specialize(IHctxG p q ys xa xb x H6).
            inversion Hb. subst. clear Hb. inversion IHctxGLis. subst. clear IHctxGLis.
            specialize(IHctxG H2 H4). constructor; try easy.
            clear H4 H2 H6 IHctxG.
            - destruct H5. destruct H as (Ha,(Hb,Hc)). subst. easy.
            - destruct H. destruct H as (t,(Ha,(Hb,Hc))). subst. easy.
            - destruct H. destruct H as (t,(Ha,(Hb,Hc))). subst. easy.
            - destruct H as (t,(Ha,(Hb,Hc))). subst. easy.
  apply proj_mon.
Qed.


Lemma canon_rep_s_helper {A B} : forall (ys : list (option (A * B))),
  exists SI, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g, u = Some s /\ v = Some (s, g))) SI ys.
Proof.
  induction ys; intros; try easy.
  exists nil. easy.
  destruct IHys. destruct a. destruct p. exists (Some a :: x). constructor; try easy.
  right. exists a. exists b. easy.
  exists (None :: x). constructor; try easy. left. easy.
Qed.

Lemma canon_rep_s_helper2s : forall n s1 g1 xs ys ys0 ys1 ctxG p q,
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

Lemma canon_rep_s_helper2 : forall G' G p q PT QT ctxG,
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
   wfgC G -> 
  List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g'))) PT QT.
Proof.
  induction G' using gtth_ind_ref; intros; try easy. rename H5 into Ht.
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
    clear H13 H15 H14 H9 H11 H10 Ht H7 H3 H2 H H0 Ha H4. clear ctxG n.
    revert H16 H12. revert p q PT QT.
    induction lsg; intros; try easy.
    - destruct QT; try easy. destruct PT; try easy.
    - destruct QT; try easy. destruct PT; try easy.
      inversion H16. subst. clear H16. inversion H12. subst. clear H12.
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
    rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    pinversion H1; try easy. subst. assert False. apply H3. constructor. easy.
    pinversion H0; try easy. subst.
    assert(List.Forall (fun u => u = None \/ (exists lis, u = Some (ltt_recv p lis))) ys0).
    {
      apply Forall_forall; intros.
      destruct x.
      specialize(in_some_implies_onth l ys0 H7); intros. destruct H8 as (n,H8).
      right.
      specialize(merge_onth_recv n p QT ys0 l H19 H8); intros. destruct H9. exists x. subst. easy.
      left. easy.
    }
    assert(List.Forall (fun u => u = None \/ (exists lis, u = Some (ltt_send q lis))) ys1).
    {
      apply Forall_forall; intros.
      destruct x.
      specialize(in_some_implies_onth l ys1 H8); intros. destruct H9 as (n,H9).
      right.
      specialize(merge_onth_send n q PT ys1 l H30 H9); intros. destruct H16. exists x. subst. easy.
      left. easy.
    }
    assert(List.Forall (fun u => u = None \/ 
      (exists s g PT QT, u = Some(s, g) /\ projectionC g p (ltt_send q PT) /\ projectionC g q (ltt_recv p QT) /\
        Forall2
             (fun u0 v : option (sort * ltt) =>
              u0 = None /\ v = None \/
              (exists (s0 : sort) (g0 g' : ltt), u0 = Some (s0, g0) /\ v = Some (s0, g'))) PT QT
      )) ys).
    {
      clear H30 H19 H12 H1 H0 H2.
      specialize(wfgC_after_step_all H10 H6); intros. clear H25 H24 H23 H14 H11 H10 H6.
      clear H26 H15.
      revert H0 H29 H18 H13 H5 H4 H3 H H7 H8.
      revert s s' xs p q ctxG ys0 ys1. clear PT QT.
      induction ys; intros; try easy.
      - destruct xs; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H0. subst. clear H0. inversion H29. subst. clear H29.
        inversion H18. subst. clear H18. inversion H13. subst. clear H13.
        inversion H. subst. clear H. inversion H7. subst. clear H7. inversion H8. subst. clear H8.
        specialize(IHys s s' xs p q ctxG ys0 ys1).
        assert(Forall
         (fun u : option (sort * gtt) =>
          u = None \/
          (exists (s : sort) (g : gtt) (PT QT : seq.seq (option (sort * ltt))),
             u = Some (s, g) /\
             projectionC g p (ltt_send q PT) /\
             projectionC g q (ltt_recv p QT) /\
             Forall2
               (fun u0 v : option (sort * ltt) =>
                u0 = None /\ v = None \/
                (exists (s0 : sort) (g0 g' : ltt), u0 = Some (s0, g0) /\ v = Some (s0, g'))) PT QT)) ys).
      {
        apply IHys; try easy.
        specialize(ishParts_hxs H4); try easy.
        specialize(ishParts_hxs H3); try easy.
      }
      constructor; try easy.
      clear H H18 H16 H13 H17 H15 H12 H9 IHys.
      destruct H11. left. easy. right.
      destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). subst.
      destruct H14; try easy. destruct H as (s2,(g2,(g3,(Hd,(He,Hf))))). inversion He. subst.
      destruct H6; try easy. destruct H as (s3,(g4,(Hg,Hi))). inversion Hg. subst.
      destruct H1; try easy. destruct H as (lis,Hj). inversion Hj. subst.
      destruct H10; try easy. destruct H as (s5,(g5,(t2,(Hk,(Hl,Hm))))). inversion Hk. subst.
      destruct H7; try easy. destruct H as (lis2,Hn). inversion Hn. subst.
      destruct H2; try easy.
      exists s5. exists g5. exists lis2. exists lis.
      destruct H as (s6,(g6,(Ho,Hp))). inversion Ho. subst. clear Hn Hk He Hg Ho.
      specialize(Hp g5 p q lis2 lis ctxG).
      split. easy. split. destruct Hm; try easy. split. destruct Hc; try easy.
      apply Hp; try easy. destruct Hm; try easy. destruct Hc; try easy.
      specialize(ishParts_x H3); try easy.
      specialize(ishParts_x H4); try easy.
    }
    specialize(wfgC_after_step_all H10 H6); intros.
    clear H25 H24 H23 H14 H11 H10 H13 H12 H6 H5 H4 H3 H0 H1 H2 H H15 H26. clear s s' ctxG.
    assert(List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists lis1 lis2, u = Some (ltt_recv p lis1) /\ v = Some (ltt_send q lis2) /\ 
      List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t'))) lis2 lis1
    )) ys0 ys1).
    {
      clear H30 H19.
      revert H16 H9 H8 H7 H29 H18. revert p q ys0 ys1. clear xs PT QT.
      induction ys; intros.
      - destruct ys0; try easy. destruct ys1; try easy.
      - destruct ys0; try easy. destruct ys1; try easy.
        inversion H16. subst. clear H16. inversion H9. subst. clear H9.
        inversion H8. subst. clear H8. inversion H7. subst. clear H7.
        inversion H29. subst. clear H29. inversion H18. subst. clear H18.
        specialize(IHys p q ys0 ys1).
        assert(Forall2
         (fun u v : option ltt =>
          u = None /\ v = None \/
          (exists lis1 lis2 : seq.seq (option (sort * ltt)),
             u = Some (ltt_recv p lis1) /\
             v = Some (ltt_send q lis2) /\
             Forall2
               (fun u0 v0 : option (sort * ltt) =>
                u0 = None /\ v0 = None \/
                (exists (s : sort) (t t' : ltt), u0 = Some (s, t) /\ v0 = Some (s, t'))) lis2 lis1)) ys0
         ys1).
      apply IHys; try easy. constructor; try easy.
      clear IHys H2 H4 H6 H9 H12 H14 H.
      - destruct H10. destruct H. subst.
        destruct H11. left. easy.
        destruct H as(s,(g,(t,(Ha,(Hb,Hc))))). easy.
      - destruct H as (s,(g,(t,(Ha,(Hb,Hc))))). subst.
        destruct H11; try easy. destruct H as (s1,(g1,(t1,(Hd,(He,Hf))))). inversion Hd. subst.
        destruct H5; try easy. destruct H as (lis,Hg). inversion Hg. subst.
        destruct H8; try easy. destruct H as (lis2,Hh). inversion Hh. subst.
        destruct H1; try easy. destruct H as (s2,(g2,(Hi,Hj))). inversion Hi. subst.
        destruct H3; try easy. destruct H as (s3,(g3,(PT,(QT,(Hk,(Hl,(Hm,Hn))))))). inversion Hk. subst.
        pclearbot.
        specialize(proj_inj Hj Hc Hl); intros. inversion H. subst.
        specialize(proj_inj Hj Hf Hm); intros. inversion H0. subst.
        clear Hg Hh Hc Hf H H0.
        right. exists QT. exists PT. split. easy. split. easy. easy.
    }
    clear H16 H9 H29 H18 H7 H8.
    clear ys.
    
    specialize(merge_sorts ys0 ys1 p q PT QT); intros. apply H0; try easy.
  apply proj_mon.
  apply proj_mon.
Qed.

Lemma canon_rep_helper2 : forall lsg SI x p,
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

Lemma canon_rep_helper3 : forall n lsg x0 Sk ys q,
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


Lemma canon_rep_s : forall G p q PT QT S T S' T' n, 
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
  specialize(canon_rep_11 G p q PT H H0); intros.
  destruct H4 as (G',(ctxG,(Ha,(Hb,(Hc,Hd))))). 
  exists G'. exists ctxG.
  specialize(canon_rep_part ctxG G' G p q PT QT Ha H0 H2 Hb); intros.
  specialize(canon_rep_16 G' ctxG G p q QT PT H2 Hc Hd Hb H4 Ha); intros. clear Hc.
  specialize(canon_rep_s_helper PT); intros. destruct H6 as (SI, H6).
  exists SI. exists S. split. easy. split. easy. split. easy.
  specialize(canon_rep_s_helper2 G' G p q PT QT ctxG); intros.
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
  - specialize(canon_rep_helper2 lsg SI PT p); intros. apply H5; try easy.
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
    (forall n : fin, exists m : fin, guardG n m (g_send q p x)) ->
    exists G'0 : global, gttTC G'0 (gtt_send q p x0) /\ (forall n : fin, exists m : fin, guardG n m G'0) /\ isgParts pt G'0.
Proof.  
  intros.
  unfold isgPartsC in H. destruct H. destruct H. rename x1 into Gl.
  exists (g_send q p (overwrite_lis l (Some(s, Gl)) x)). 
  split.
  - pinversion H1; try easy. subst.
    pfold. constructor. destruct H3.
    clear H1 H2 H3 H4. revert H5 H0 H. clear q p pt. revert l x G' s Gl.
    induction x0; intros; try easy.
    - destruct l; try easy.
    - destruct x; try easy. inversion H5. subst. clear H5.
    - destruct l; try easy.
      - simpl in H0. subst. destruct H4; try easy.
      destruct H0 as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
      inversion Hb. subst.
        constructor; try easy. right. exists s1. exists Gl. exists g2. split. easy. split. easy. left. easy.
      - specialize(IHx0 l x G' s Gl H7 H0 H). constructor; try easy.
    apply gttT_mon.
    split.
    destruct H3. intros. destruct n. exists 0. constructor.
    specialize(H2 (S n)). specialize(H3 n). destruct H3. destruct H2.
    exists (Nat.max x1 x2). constructor. inversion H2. subst. clear H2 H1 H0 H4 H.
    revert H8 H3. revert n x s Gl x1 x2. clear x0 q p G' pt.
    induction l; intros; try easy.
    - destruct x; try easy. constructor; try easy. right. exists s. exists Gl.
      split. easy. specialize(guardG_more n x1 (Nat.max x1 x2) Gl); intros. apply H; try easy.
      apply max_l.
    - inversion H8. subst. clear H8. constructor; try easy. right.
      exists s. exists Gl. split. easy.
      specialize(guardG_more n x1 (Nat.max x1 x2) Gl); intros. apply H; try easy. apply max_l.
    - apply Forall_forall; intros.
      specialize(Forall_forall (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ guardG n x2 g)) x); intros.
      destruct H0. specialize(H0 H2). clear H4 H2. specialize(H0 x0 H). 
      destruct H0. left. easy. destruct H0 as (s1,(g,(Ha,Hb))). subst. right.
      exists s1. exists g. split. easy.
      specialize(guardG_more n x2 (Nat.max x1 x2) g); intros. apply H0; try easy. apply max_r.
    - destruct x; try easy.
      specialize(IHl n nil s Gl x1 x2 H8 H3). constructor; try easy.
      left. easy.
    - inversion H8. subst. clear H8. specialize(IHl n x s Gl x1 x2 H2 H3). constructor; try easy.
      destruct H1. left. easy.
      destruct H as (s1,(g1,(Ha,Hb))). subst. right. exists s1. exists g1. split. easy.
      specialize(guardG_more n x2 (Nat.max x1 x2) g1); intros. apply H; try easy.
      apply max_r.
  - case_eq (eqb pt p); intros.
      assert (pt = p). apply eqb_eq; try easy. subst. constructor.
    - case_eq (eqb pt q); intros.
      assert (pt = q). apply eqb_eq; try easy. subst. constructor.
    - assert (pt <> p). apply eqb_neq; try easy. 
      assert (pt <> q). apply eqb_neq; try easy.
      apply pa_sendr with (n := l) (s := s) (g := Gl); try easy.
      apply overwriteExtract; try easy.
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
        wfgC G' -> 
        gttstepC G G' q p l -> 
        projectionC G p (ltt_recv q LQ) ->
        projectionC G q (ltt_send p LP) ->
        isgPartsC pt G' -> 
        isgPartsC pt G.
Proof.
  intros.
  specialize(canon_rep_11 G q p LP H H3); intros.
  destruct H5 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd.
  assert(Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))),
           u = Some g /\
           g = gtt_send q p lsg)) ctxG).
  {
    apply Forall_forall; intros.
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
    destruct H6. specialize(H6 Hc). clear Hc H7.
    specialize(H6 x H5). destruct H6. left. easy.
    destruct H6 as (g,(lsg,(Hc,(Hd,He)))). right. exists g. exists lsg. easy.
  }
  clear Hc.
  revert H5 Hb Ha H4 H3 H2 H1 H0 H.
  revert G G' p q pt l LP LQ ctxG.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha. subst.
    specialize(some_onth_implies_In n ctxG G H8); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : seq.seq (option (sort * gtt))), u = Some g /\ g = gtt_send q p lsg))
       ctxG); intros.
    destruct H7. specialize(H7 H5). clear H9 H5.
    specialize(H7 (Some G) H6). destruct H7; try easy.
    destruct H5 as (g1,(lsg,(Hc,Hd))). inversion Hc. subst.
    pinversion H1; try easy. subst.
    clear H11 H12.
    unfold wfgC in H. destruct H. destruct H. rename x into G1.
    unfold isgPartsC. destruct H5. destruct H7.
    specialize(part_after_step_helper G1 q p lsg H H7); intros.
    destruct H10. destruct H10.
    specialize(part_after_step_helper2 l lsg q p x G' pt s); intros. apply H12; try easy.
    apply step_mon.
  - inversion Ha. subst.
    unfold isgPartsC.
    pinversion H2; try easy.
    subst. assert False. apply Hb. constructor. easy.
    subst. pinversion H3; try easy. subst.
    pinversion H1; try easy. subst. clear H10 H11 H14 H16 H17 H20.
    specialize(part_break (gtt_send p q ys2) pt H0 H4); intros.
    destruct H7 as (Gl,(Hc,(Hd,(He,Hf)))).
    destruct Hf.
    - subst. pinversion Hc; try easy.
    - destruct H7 as (p1,(q1,(lis1,Hf))). subst.
      pinversion Hc; try easy. subst.
    clear Hc.
    - specialize(part_break (gtt_send p q ys) p); intros.
      assert(exists Gl : global,
       gttTC Gl (gtt_send p q ys) /\
       isgParts p Gl /\
       (forall n : fin, exists m : fin, guardG n m Gl) /\
       (Gl = g_end \/
        (exists (p q : string) (lis : seq.seq (option (sort * global))), Gl = g_send p q lis))).
      {
        apply H7; try easy.
        apply triv_pt_p; try easy.
      }
      destruct H9 as (Gl1,(Hta,(Htb,(Htc,Htd)))).
      destruct Htd. subst. pinversion Hta; try easy.
      destruct H9 as (p1,(q1,(lsg1,Htd))). subst.
      pinversion Hta. subst.
    - rename p into st. rename q into st'. rename p0 into p. rename q0 into q.
      clear H7 Hta.
      inversion Hd; try easy. 
      - subst. exists (g_send st st' lsg1). split. pfold. constructor. easy. split. easy. constructor.
      - subst. exists (g_send st st' lsg1). split. pfold. constructor. easy. split. easy. constructor.
      subst.
      clear Htb H21 H15 H12 H4 H1 Ha H2 H3.
      specialize(wfgC_after_step_all H23 H0); intros.
      specialize(wfgC_after_step_all H23 H6); intros.
      clear H0 H6 Hd H34.
      specialize(part_after_step_helper3 n lis1 ys2 ys ys1 ys0 xs p q l s g ctxG); intros.
      assert(exists (g' g'' : gtt) (t t' : ltt) (Gl : gtth),
       onth n ys2 = Some (s, g') /\
       gttTC g g' /\
       onth n ys = Some (s, g'') /\
       gttstepC g'' g' q p l /\
       onth n ys1 = Some t /\
       projectionC g'' q t /\
       onth n ys0 = Some t' /\
       projectionC g'' p t' /\ onth n xs = Some (s, Gl) /\ typ_gtth ctxG Gl g'').
      {
        apply H0; try easy.
      }
      clear H0.
      destruct H3 as (g1,(g2,(t1,(t2,(Gl,(Hta,(Htb,(Htk,(Htd,(Hte,(Htf,(Hth,(Hti,(Htj,Htl)))))))))))))).
      specialize(some_onth_implies_In n xs (s, Gl) Htj); intros.
      specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G G' : gtt) (p q pt : string) (l : fin) (LP LQ : seq.seq (option (sort * ltt)))
             (ctxG : seq.seq (option gtt)),
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : seq.seq (option (sort * gtt))),
                 u0 = Some g0 /\ g0 = gtt_send q p lsg)) ctxG ->
           (ishParts q g -> False) ->
           typ_gtth ctxG g G ->
           isgPartsC pt G' ->
           projectionC G q (ltt_send p LP) ->
           projectionC G p (ltt_recv q LQ) ->
           gttstepC G G' q p l -> wfgC G' -> wfgC G -> isgPartsC pt G))) xs); intros.
      destruct H3. specialize(H3 H). clear H H4.
      specialize(H3 (Some (s, Gl)) H0). destruct H3; try easy. 
      destruct H as (s1,(g3,(Hma,Hmb))). inversion Hma. subst.
      clear Hma H0.
      specialize(Hmb g2 g1 p q pt l).
      specialize(merge_onth_send n p LP ys1 t1 H25 Hte); intros. destruct H. subst.
      specialize(merge_onth_recv n q LQ ys0 t2 H19 Hth); intros. destruct H. subst.
      specialize(Hmb x x0 ctxG H5).
      assert(isgPartsC pt g2).
      {
        apply Hmb; try easy.
        specialize(ishParts_n Hb Htj); try easy.
        unfold isgPartsC. exists g. split. easy. split; try easy.
        specialize(guard_cont He); intros.
        revert n0. specialize(Forall_prop n lis1 (s1, g) (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) H20 H); intro.
        simpl in H0. destruct H0; try easy. destruct H0 as (st1,(gt1,(Hsa,Hsb))). inversion Hsa; try easy.
        specialize(Forall_prop n ys2 (s1, g1) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) Hta H1); intro.
        simpl in H. destruct H; try easy. destruct H as (st1,(gt1,(Hsa,Hsb))). inversion Hsa; try easy.
        specialize(Forall_prop n ys (s1, g2) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) Htk H2); intro.
        simpl in H. destruct H; try easy. destruct H as (st1,(gt1,(Hsa,Hsb))). inversion Hsa; try easy.
      }
      
      clear Hmb H2 H1.
      specialize(part_after_step_helper2 n ys st st'); intros.
      specialize(H0 lsg1 g2 pt s1). apply H0; try easy. pfold. constructor. easy.
    apply gttT_mon.
    apply gttT_mon.
    apply step_mon.
    apply proj_mon.
    apply proj_mon. 
Qed.

Lemma typ_after_step_ctx_loose : forall [ctxG p q l T T' SI],
     Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s', Gjk) /\
              projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option sort) =>
              u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s))
             lsg SI)) ctxG ->
      Forall
        (fun u : option gtt =>
         u = None \/
         (exists (g : gtt) (lsg : list (option (sort * gtt))),
            u = Some g /\
            g = gtt_send p q lsg /\
            (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
               onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG.
Proof.
  intros.
  apply Forall_forall; intros.
  specialize(Forall_forall (fun u : option gtt =>
       u = None \/
       (exists (g : gtt) (lsg : list (option (sort * gtt))),
          u = Some g /\
          g = gtt_send p q lsg /\
          (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
             onth l lsg = Some (s', Gjk) /\
             projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
          Forall2
            (fun (u0 : option (sort * gtt)) (v : option sort) =>
             u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s)) lsg
            SI)) ctxG); intros.
  destruct H1. specialize(H1 H). clear H H2.
  destruct x. 
  specialize(H1 (Some g) H0). destruct H1; try easy.
  - destruct H. destruct H. destruct H. destruct H1. destruct H2.
    destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4. destruct H5. destruct H6.
    subst.
    inversion H. subst.
    right. exists (gtt_send p q x0). exists x0. split; try easy. split; try easy.
    exists x1. exists x2. exists x3. exists x4. easy.
  left. easy.
Qed.


Lemma proj_inv_lis_helper : forall n ys s0 g xs ys0 ys1 ctxG p q,
    onth n ys = Some (s0, g) -> 
    Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys ->
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
    exists g' t t',
    onth n xs = Some(s0, g') /\ typ_gtth ctxG g' g /\
    onth n ys0 = Some t /\ projectionC g q t /\
    onth n ys1 = Some t' /\ projectionC g p t' /\ wfgC g.
Proof.
  induction n; intros; try easy.
  - destruct ys; try easy. destruct xs; try easy. destruct ys0; try easy. destruct ys1; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1.
    inversion H2. subst. clear H2. inversion H3. subst. clear H3.
    simpl in H. subst.
    destruct H6; try easy. destruct H as (st,(g1,(Ha,Hb))). inversion Ha. subst. clear Ha.
    destruct H5; try easy. destruct H as (st1,(g2,(t1,(Hc,(Hd,He))))). inversion Hc. subst. clear Hc.
    destruct H4; try easy. destruct H as (st2,(g3,(t2,(Hf,(Hg,Hh))))). inversion Hf. subst. clear Hf.
    destruct H8; try easy. destruct H as (st3,(g4,(g5,(Hi,(Hj,Hk))))). inversion Hj. subst. clear Hj.
    simpl. exists g4. exists t1. exists t2. destruct He; try easy. destruct Hh; try easy.
  - destruct ys; try easy. destruct xs; try easy. destruct ys0; try easy. destruct ys1; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1.
    inversion H2. subst. clear H2. inversion H3. subst. clear H3.
    specialize(IHn ys s0 g xs ys0 ys1 ctxG p q). apply IHn; try easy.
Qed.

Lemma typ_after_step_step_helper3 : forall xs ys ctxG,
      SList xs ->
      Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys ->
      SList ys.
Proof.
  induction xs; intros; try easy.
  specialize(SList_f a xs H); intros.
  destruct ys; try easy. inversion H0.
  subst.
  destruct H1; try easy.
  - specialize(IHxs ys ctxG). apply SList_b. apply IHxs; try easy.
  - destruct H1. destruct H2. subst. destruct ys; try easy. destruct H5; try easy.
    destruct H1. destruct H1. destruct H1. destruct H1. destruct H2. subst. easy.
Qed.

Lemma proj_inv_lis_helper2 : forall ys2 ys3 ys4 p q,
          SList ys2 -> 
          Forall2
            (fun (u : option (sort * gtt)) (v : option ltt) =>
             u = None /\ v = None \/
             (exists (s : sort) (g : gtt) (t : ltt),
                u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) ys2 ys3 -> 
          Forall2
            (fun (u : option (sort * gtt)) (v : option ltt) =>
             u = None /\ v = None \/
             (exists (s : sort) (g : gtt) (t : ltt),
                u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) ys2 ys4 ->
          Forall
             (fun u : option (sort * gtt) =>
              u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys2 -> 
          exists n st g t t', 
          onth n ys2 = Some (st, g) /\ wfgC g /\
          onth n ys3 = Some t /\ projectionC g p t /\
          onth n ys4 = Some t' /\ projectionC g q t'.
Proof.
  induction ys2; intros; try easy.
  destruct ys3; try easy. destruct ys4; try easy.
  inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
  specialize(SList_f a ys2 H); intros.
  specialize(IHys2 ys3 ys4 p q).
  destruct H0. 
  assert (exists (n : fin) (st : sort) (g : gtt) (t t' : ltt),
          onth n ys2 = Some (st, g) /\
          wfgC g /\
          onth n ys3 = Some t /\ projectionC g p t /\ onth n ys4 = Some t' /\ projectionC g q t').
  apply IHys2; try easy. destruct H1. exists (S x). easy.
  destruct H0. destruct H1. subst. clear H4 H9 H8 IHys2 H. exists 0. simpl.
  destruct H6; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
  destruct H3; try easy. destruct H as (s2,(g2,(Hd,He))). inversion Hd. subst.
  destruct H5; try easy. destruct H as (s3,(g3,(t2,(Hf,(Hg,Hh))))).
  inversion Hf. subst.
  exists s3. exists g3. exists t1. exists t2. destruct Hc; try easy. destruct Hh; try easy.
Qed.

Lemma proj_inv_lis_helper3 : forall [l lsg s2 Gjk ys2 ys3 p q],
          onth l lsg = Some (s2, Gjk) ->
          Forall2
          (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
           u = None /\ v = None \/
           (exists (s : sort) (g : gtt) (t : ltt),
              u = Some (s, g) /\ v = Some (s, t) /\ upaco3 projection bot3 g q t)) lsg ys2 -> 
          Forall2
          (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
           u = None /\ v = None \/
           (exists (s : sort) (g : gtt) (t : ltt),
              u = Some (s, g) /\ v = Some (s, t) /\ upaco3 projection bot3 g p t)) lsg ys3 -> 
          exists T T' : sort * ltt, onth l ys3 = Some T /\ onth l ys2 = Some T'.
Proof.
  induction l; intros; try easy.
  - destruct lsg; try easy. destruct ys2; try easy. destruct ys3; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. simpl in H. subst.
    destruct H5; try easy. destruct H as (s,(g,(t,(Ha,(Hb,Hc))))). inversion Ha. subst.
    destruct H4; try easy. destruct H as (s1,(g1,(t1,(Hd,(He,Hf))))). inversion Hd. subst.
    simpl. exists (s1, t1). exists (s1, t). easy.
  - destruct lsg; try easy. destruct ys2; try easy. destruct ys3; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. simpl in H. subst.
    specialize(IHl lsg s2 Gjk ys2 ys3 p q). apply IHl; try easy.
Qed.

Lemma proj_inv_lis : forall p q l s s' ys LP LQ S T S' T',
    wfgC (gtt_send s s' ys) ->
    projectionC (gtt_send s s' ys) p (ltt_send q LP) -> 
    onth l LP = Some (S, T) ->
    projectionC (gtt_send s s' ys) q (ltt_recv p LQ) -> 
    onth l LQ = Some (S', T') ->
    (s = p /\ s' = q /\ exists Gk, onth l ys = Some Gk) \/
    (s <> p /\ s' <> q /\ List.Forall (fun u => u = None \/ 
        (exists s g LP' LQ' T T', u = Some(s, g) /\ projectionC g p (ltt_send q LP') /\ projectionC g q (ltt_recv p LQ') /\ 
          onth l LP' = Some T /\ onth l LQ' = Some T')) ys).
Proof.
  intros.
  specialize(canon_rep_s (gtt_send s s' ys) p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
  destruct H4. destruct H4. destruct H4. destruct H4. destruct H4. destruct H5. destruct H6.
  rename x0 into ctxG. rename x into Gl.
  destruct H7.
  specialize(typ_after_step_ctx_loose H7); intros. clear H7 H8 H3 H1.
  revert H9 H6 H5 H4 H2 H0 H.
  revert p q l s s' ys LP LQ ctxG. clear S T S' T' x1 x2.
  induction Gl using gtth_ind_ref; intros; try easy.
  - inversion H4. subst. 
    specialize(some_onth_implies_In n ctxG (gtt_send s s' ys) H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG); intros.
    destruct H3. specialize(H3 H9). clear H8 H9.
    specialize(H3 (Some (gtt_send s s' ys)) H1); intros.
    destruct H3; try easy. destruct H3. destruct H3. destruct H3. destruct H8. subst.
    inversion H3. subst. clear H3.
    destruct H9. destruct H3. destruct H3. destruct H3. destruct H3.
    left. split. easy. split. easy. exists (x, x1). easy.
  - inversion H4. subst.
    pinversion H2. subst. assert False. apply H6. constructor. easy.
    subst. clear H14. rename H18 into H14. rename H19 into H18. 
    pinversion H0; try easy. subst. clear H20. rename H23 into H20. rename H24 into H23.
    rename p0 into p. rename q0 into q.
    specialize(wfgC_after_step_all H11 H1); intros. clear H1.
    right. split. easy. split. easy.
    apply Forall_forall; intros. destruct x.
    right. destruct p0. exists s0. exists g.
    specialize(in_some_implies_onth (s0, g) ys H1); intros. destruct H7. rename x into n. clear H1.
    clear H2 H0 H4.
    specialize(proj_inv_lis_helper n ys s0 g xs ys0 ys1 ctxG p q); intros.
    assert(exists (g' : gtth) (t t' : ltt),
       onth n xs = Some (s0, g') /\
       typ_gtth ctxG g' g /\
       onth n ys0 = Some t /\ projectionC g q t /\ onth n ys1 = Some t' /\ projectionC g p t' /\ wfgC g).
    apply H0; try easy. clear H0 H3 H17 H15.
    destruct H1 as (g',(t,(t',(Ha,(Hb,(Hc,(Hd,(He,(Hf,Hg))))))))).
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (p q : string) (l : fin) (s0 s' : string) (ys : list (option (sort * gtt)))
             (LP LQ : list (option (sort * ltt))) (ctxG : list (option gtt)),
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
                    onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG ->
           (ishParts q g -> False) ->
           (ishParts p g -> False) ->
           typ_gtth ctxG g (gtt_send s0 s' ys) ->
           projectionC (gtt_send s0 s' ys) q (ltt_recv p LQ) ->
           projectionC (gtt_send s0 s' ys) p (ltt_send q LP) ->
           wfgC (gtt_send s0 s' ys) ->
           s0 = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
           s0 <> p /\
           s' <> q /\
           Forall
             (fun u0 : option (sort * gtt) =>
              u0 = None \/
              (exists (s1 : sort) (g0 : gtt) (LP' LQ' : list (option (sort * ltt))) 
               (T T' : sort * ltt),
                 u0 = Some (s1, g0) /\
                 projectionC g0 p (ltt_send q LP') /\
                 projectionC g0 q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys)))
      xs); intros. destruct H0. specialize(H0 H). clear H H1.
      specialize(some_onth_implies_In n xs (s0, g') Ha); intros.
      specialize(H0 (Some (s0, g')) H). clear H.
      destruct H0; try easy. destruct H as (s1,(g1,(H1,H2))).
      specialize(H2 p q l). inversion H1. subst. clear H1.
      
      inversion Hb.
      - subst.
        specialize(some_onth_implies_In n0 ctxG g H); intros.
        specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG); intros.
        destruct H1. specialize(H1 H9). clear H3 H9.
        specialize(H1 (Some g) H0). destruct H1; try easy.
        destruct H1 as (g2,(lsg,(H3,(H4,H8)))). subst. inversion H3. subst. clear H3.
        pinversion Hd; try easy. subst. assert False. apply H1. apply triv_pt_q; try easy. easy.
        subst. clear H15.
        pinversion Hf; try easy. subst. assert False. apply H1. apply triv_pt_p; try easy. easy.
        subst. clear H17.
        exists ys3. exists ys2.
        destruct H8 as (s2,(Gjk,(Tp,(Tq,(Hm,Ht))))). 
        assert(exists T T', onth l ys3 = Some T /\ onth l ys2 = Some T').
        {
          specialize(proj_inv_lis_helper3 Hm H22 H26); intros; try easy.
        }
        destruct H1 as (T,(T',(Ht1,Ht2))). exists T. exists T'. split. easy. split. pfold.
        easy. split. pfold. easy. easy.
      apply proj_mon.
      apply proj_mon.
      - subst. rename p0 into s0. rename q0 into s0'.
        specialize(H2 s0 s0' ys2).
        assert(exists LP' LQ', projectionC (gtt_send s0 s0' ys2) p (ltt_send q LP') /\ projectionC (gtt_send s0 s0' ys2) q (ltt_recv p LQ')).
        {
          specialize(merge_onth_recv n p LQ ys0 t H18 Hc); intros. destruct H1. subst.
          specialize(merge_onth_send n q LP ys1 t' H23 He); intros. destruct H1. subst. exists x0. exists x.
          easy.
        }
        destruct H1 as (LP',(LQ',(Ht1,Ht2))).
        specialize(H2 LP' LQ' ctxG).
        assert(s0 = p /\ s0' = q /\ (exists Gk : sort * gtt, onth l ys2 = Some Gk) \/
           s0 <> p /\
           s0' <> q /\
           Forall
             (fun u0 : option (sort * gtt) =>
              u0 = None \/
              (exists (s1 : sort) (g0 : gtt) (LP' LQ' : list (option (sort * ltt))) 
               (T T' : sort * ltt),
                 u0 = Some (s1, g0) /\
                 projectionC g0 p (ltt_send q LP') /\
                 projectionC g0 q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys2).
        {
          apply H2; try easy.
          - specialize(ishParts_n H6 Ha); intros. apply H1; try easy.
          - specialize(ishParts_n H5 Ha); intros. apply H1; try easy.
        }
        exists LP'. exists LQ'. 
        destruct H1.
        - destruct H1 as (Hs1,(Hs2,Hs3)). destruct Hs3. subst.
          assert False. apply H6. apply ha_sendr with (n := n) (s := s1) (g := gtth_send p q xs0); try easy.
          constructor. easy.
        - destruct H1 as (Hs1,(Hs2,Hs3)).
          specialize(typ_after_step_step_helper3 xs0 ys2 ctxG H H0); intros.
          clear H2.
          pinversion Ht1; try easy. subst.
          pinversion Ht2; try easy. subst.
          specialize(wfgC_after_step_all H8 Hg); intros.
          specialize(proj_inv_lis_helper2 ys2 ys3 ys4 p q); intros.
          assert(exists (n : fin) (st : sort) (g : gtt) (t t' : ltt),
       onth n ys2 = Some (st, g) /\
       wfgC g /\ onth n ys3 = Some t /\ projectionC g p t /\ onth n ys4 = Some t' /\ projectionC g q t').
          apply H3; try easy. clear H3.
          destruct H4 as (n',(st,(g3,(t1,(t2,(Hta,(Htb,(Htc,(Htd,(Hte,Htf)))))))))).
          specialize(Forall_forall (fun u0 : option (sort * gtt) =>
         u0 = None \/
         (exists (s1 : sort) (g0 : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u0 = Some (s1, g0) /\
            projectionC g0 p (ltt_send q LP') /\
            projectionC g0 q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys2); intros.
          destruct H3. specialize(H3 Hs3). clear Hs3 H4.
          specialize(some_onth_implies_In n' ys2 (st, g3) Hta); intros.
          specialize(H3 (Some (st, g3)) H4); intros. destruct H3; try easy.
          destruct H3 as (s3,(g0,(LP0',(LQ0',(T,(T',(Hsa,(Hsb,(Hsc,(Hsd,Hse)))))))))). inversion Hsa. subst.
          specialize(proj_inj Htb Htd Hsb); intros. subst. 
          specialize(proj_inj Htb Htf Hsc); intros. subst.
          specialize(merge_label_send ys3 LP' LP0' T n' l q H26 Htc Hsd); intros. destruct H3. exists x.
          specialize(merge_label_recv ys4 LQ' LQ0' T' n' l p H32 Hte Hse); intros. destruct H29. exists x0.
          split. easy. split. pfold. easy. split. pfold. easy. easy.
        apply proj_mon.
        apply proj_mon.
        left. easy.
      apply proj_mon.
      apply proj_mon.
Qed.

Lemma projection_step_label : forall G G' p q l LP LQ,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  projectionC G q (ltt_recv p LQ) ->
  gttstepC G G' p q l ->
  exists LS LS' LT LT', onth l LP = Some(LS, LT) /\ onth l LQ = Some(LS', LT').
Proof.
  intros.
  specialize(canon_rep_11 G p q LP H H0); intros.
  destruct H3. rename x into Gl.
  assert (exists ctxJ : list (option gtt),
       typ_gtth ctxJ Gl G /\
       (ishParts p Gl -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (g : gtt) (lsg : list (option (sort * gtt))),
             u = Some g /\
             g = gtt_send p q lsg)) ctxJ). 
  {
    destruct H3. exists x. destruct H3. destruct H4. split. easy. split. easy.
    clear H4 H3 H2 H1 H0 H. destruct H5 as (H5,H0). clear H0.  clear Gl LQ l. clear G G'.
    revert H5. revert LP p q. induction x; intros; try easy.
    inversion H5. subst. clear H5. specialize(IHx LP p q H2). constructor; try easy. clear H2 IHx.
    destruct H1. left. easy.
    destruct H. destruct H. destruct H. destruct H0. right. exists x0. exists x1. easy.
  } 
  clear H3. rename H4 into H3.
  revert H0 H1 H2 H3. clear H.
  revert G G' p q l LP LQ.
  induction Gl using gtth_ind_ref; intros; try easy.
  - destruct H3. destruct H. destruct H3. inversion H. subst. 
    specialize(some_onth_implies_In n x G H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg)) x); intros.
    destruct H6. specialize(H6 H4). clear H8. specialize(H6 (Some G) H5). clear H5 H4.
    destruct H6; try easy. destruct H4. destruct H4. destruct H4. inversion H4.
    subst.
    pinversion H1; try easy. subst.
    pinversion H2; try easy. subst.
    pinversion H0; try easy. subst.
    clear H16 H20 H19 H15 H14 H17 H10 H12 H11 H7 H3 H H0 H1 H2 H4. clear n x.
    revert H13 H18 H21. revert G' p q LP LQ x1 s.
    induction l; intros; try easy.
    - destruct x1; try easy.
      destruct LP; try easy. destruct LQ; try easy.
      inversion H21. subst. clear H21. inversion H13. subst. clear H13. 
      simpl in *. subst.
      destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H. subst.
      destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2.
      inversion H0. subst.
      exists x3. exists x3. exists x2. exists x5. easy.
    - destruct x1; try easy.
      destruct LP; try easy. destruct LQ; try easy.
      inversion H21. subst. clear H21. inversion H13. subst. clear H13. 
      specialize(IHl G' p q LP LQ x1 s). apply IHl; try easy.
    apply proj_mon.
    apply step_mon. 
    apply proj_mon.
  - destruct H3. destruct H3. destruct H4. 
    rename p into s. rename q into s0. rename p0 into p. rename q0 into q.
    specialize(canon_rep_part x (gtth_send s s0 xs) G p q LP LQ H3 H0 H1 H4); intros.
    inversion H3. subst.
    pinversion H1. subst.
    - assert False. apply H4. constructor. easy.
    pinversion H0; try easy. subst. 
    specialize(SList_to_In xs H12); intros. destruct H7.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G G' : gtt) (p q : string) (l : fin) (LP LQ : list (option (sort * ltt))),
           projectionC G p (ltt_send q LP) ->
           projectionC G q (ltt_recv p LQ) ->
           gttstepC G G' p q l ->
           (exists ctxJ : list (option gtt),
              typ_gtth ctxJ g G /\
              (ishParts p g -> False) /\
              Forall
                (fun u0 : option gtt =>
                 u0 = None \/
                 (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                    u0 = Some g0 /\
                    g0 = gtt_send p q lsg)) ctxJ) ->
           exists (LS LS' : sort) (LT LT' : ltt),
             onth l LP = Some (LS, LT) /\ onth l LQ = Some (LS', LT')))) xs); intros.
    destruct H8. specialize(H8 H). clear H H9.
    specialize(H8 (Some x0) H7). destruct H8; try easy. destruct H. destruct H.
    destruct H. inversion H. subst. clear H. rename x2 into G.
    specialize(in_some_implies_onth (x1, G) xs H7); intros. destruct H. clear H7. rename x0 into n.
    rename x into ctxG.
    pinversion H2; try easy. subst.
    assert(exists g g' t t', onth n ys = Some(x1, g) /\ typ_gtth ctxG G g /\ onth n ys0 = Some t /\ projectionC g q t /\
           onth n ys1 = Some t' /\ projectionC g p t' /\ onth n ys2 = Some (x1, g') /\ gttstepC g g' p q l).
    {
      clear H35 H28 H27 H22 H21 H20 H17 H8 H30 H26 H25 H24 H23 H19 H15 H14 H11 H10 H12 H6 H5 H3 H0 H1 H2 H4.
      clear LP LQ. clear s s0.
      revert H H36 H29 H18 H13. 
      revert xs p q ys ctxG ys0 ys1 x1 G. revert l ys2.
      induction n; intros; try easy.
      - destruct xs; try easy.
        destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H36. subst. inversion H29. subst. inversion H18. subst. inversion H13. subst.
        clear H36 H29 H18 H13.
        simpl in *. subst.
        destruct H8; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
        destruct H6; try easy. destruct H as (s2,(g3,(t1,(Hd,(He,Hf))))). inversion Hd. subst.
        destruct H2; try easy. destruct H as (s3,(g4,(g5,(Hg,(Hh,Hi))))). inversion Hg. subst.
        destruct H5; try easy. destruct H as (s4,(g6,(t2,(Hj,(Hk,Hl))))). inversion Hj. subst.
        exists g6. exists g5. exists t1. exists t2. pclearbot. easy.
      - destruct xs; try easy.
        destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H36. subst. inversion H29. subst. inversion H18. subst. inversion H13. subst. apply IHn with (xs := xs); try easy.
    }
    destruct H7. destruct H7. destruct H7. destruct H7. destruct H7. destruct H9. destruct H16. destruct H31.
    destruct H32. destruct H33. destruct H34. 
    rename x into G0'. rename x2 into LP0. rename x3 into LQ0. rename x0 into G''.
    specialize(H8 G0' G'' p q l).
    specialize(merge_onth_recv n p LQ ys0 LP0 H19 H16); intros. destruct H38 as [LQ' H38].
    specialize(merge_onth_send n q LP ys1 LQ0 H30 H32); intros. destruct H39 as [LP' H39].
    subst.
    specialize(H8 LP' LQ' H33 H31 H37).
    assert (exists (LS LS' : sort) (LT LT' : ltt), onth l LP' = Some (LS, LT) /\ onth l LQ' = Some (LS', LT')).
    {
      apply H8; try easy.
      exists ctxG. split. easy. split; try easy.
      intros. apply H4.
      - case_eq (eqb p s); intros.
        assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
      - case_eq (eqb p s0); intros.
        assert (p = s0). apply eqb_eq; try easy. subst. apply ha_sendq.
      - assert (p <> s). apply eqb_neq; try easy. 
        assert (p <> s0). apply eqb_neq; try easy.
        apply ha_sendr with (n := n) (s := x1) (g := G); try easy.
    }
    destruct H38. destruct H38. destruct H38. destruct H38. destruct H38. 
    
    specialize(merge_label_send ys1 LP LP' (x, x2) n l q H30 H32 H38); intros.
    destruct H40. 
    specialize(merge_label_recv ys0 LQ LQ' (x0, x3) n l p H19 H16 H39); intros.
    destruct H41. destruct x4. destruct x5.
    exists s1. exists s2. exists l0. exists l1. easy.
  apply step_mon.
  apply proj_mon.
  apply proj_mon.
Qed.

Lemma projection_step_label_s : forall G p q l LP LQ ST,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some ST -> 
  projectionC G q (ltt_recv p LQ) ->
  exists LS' LT', onth l LQ = Some(LS', LT').
Proof.
  intros.
  specialize(canon_rep_11 G p q LP H H0); intros.
  destruct H3. rename x into Gl.
  assert (exists ctxJ : list (option gtt),
       typ_gtth ctxJ Gl G /\
       (ishParts p Gl -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (g : gtt) (lsg : list (option (sort * gtt))),
             u = Some g /\
             g = gtt_send p q lsg)) ctxJ). 
  {
    destruct H3. exists x. destruct H3. destruct H4. split. easy. split. easy.
    clear H4 H3 H2 H1 H0 H. destruct H5 as (H5, H0). clear H0. clear Gl LQ l. clear G.
    revert H5. revert LP p q. induction x; intros; try easy.
    inversion H5. subst. clear H5. specialize(IHx LP p q H2). constructor; try easy. clear H2 IHx.
    destruct H1. left. easy.
    destruct H. destruct H. destruct H. destruct H0. right. exists x0. exists x1. easy.
  }
  clear H3. clear H.
  revert H4 H2 H1 H0. revert G p q l LP LQ ST.
  induction Gl using gtth_ind_ref; intros.
  - destruct H4. destruct H. destruct H3.
    inversion H. subst. 
    specialize(some_onth_implies_In n x G H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg)) x); intros.
    destruct H6. specialize(H6 H4 (Some G) H5). clear H4 H8.
    destruct H6; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst.
    pinversion H0; try easy. subst.
    pinversion H2; try easy. subst.
    clear H11 H15 H11 H12 H0 H7 H5 H2 H3 H H4. clear H17 H16 H13. clear n x.
    revert H18 H14 H1. revert p q LP LQ ST x1.
    induction l; intros.
    - destruct LP; try easy. destruct x1; try easy. destruct LQ; try easy.
      inversion H18. inversion H14. subst. clear H18 H14.
      simpl in H1. subst.
      destruct H9; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
      inversion H0. subst.
      destruct H3; try easy. destruct H. destruct H. destruct H. destruct H. destruct H2.
      inversion H. subst. 
      exists x3. exists x5. easy.
    - destruct LP; try easy. destruct x1; try easy. destruct LQ; try easy.
      inversion H18. inversion H14. subst. clear H18 H14.
      specialize(IHl p q LP LQ ST x1). apply IHl; try easy.
    apply proj_mon. 
    apply proj_mon.
  - destruct H4. destruct H3. destruct H4. 
    inversion H3. subst.
    specialize(SList_to_In xs H11); intros. destruct H6.
    specialize(in_some_implies_onth x0 xs H6); intros. destruct H7. rename x1 into n.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G : gtt) (p q : string) (l : fin) (LP LQ : list (option (sort * ltt)))
             (ST : sort * ltt),
           (exists ctxJ : list (option gtt),
              typ_gtth ctxJ g G /\
              (ishParts p g -> False) /\
              Forall
                (fun u0 : option gtt =>
                 u0 = None \/
                 (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                    u0 = Some g0 /\ g0 = gtt_send p q lsg)) ctxJ) ->
           projectionC G q (ltt_recv p LQ) ->
           onth l LP = Some ST ->
           projectionC G p (ltt_send q LP) ->
           exists (LS' : sort) (LT' : ltt), onth l LQ = Some (LS', LT')))) xs); intros.
    destruct H8. specialize(H8 H (Some x0) H6). clear H9 H. destruct H8; try easy.
    destruct H. destruct H. destruct H. inversion H. subst.
    pinversion H0. subst.
    assert False. apply H4. constructor. easy.
    subst.
    pinversion H2; try easy. subst.
    rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    rename x1 into s0. rename x2 into g. rename x into ctxG.
    clear H H6 H11 H2 H0 H3.
    assert(exists g' t t', onth n ys = Some (s0, g') /\ typ_gtth ctxG g g' /\ onth n ys0 = Some t /\ projectionC g' p t 
          /\ onth n ys1 = Some t' /\ projectionC g' q t').
    {
      clear H27 H23 H22 H19 H18 H21 H17 H16 H15 H14 H8 H1 H5 H4. 
      clear ST LP LQ. clear s s'. clear l.
      revert H26 H20 H12 H7. revert xs p q ctxG ys s0 g ys0 ys1.
      induction n; intros.
      - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H26. inversion H20. inversion H12. subst. clear H26 H20 H12.
        simpl in H7. subst.
        destruct H16; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        destruct H9; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
        inversion H. subst. clear H.
        destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. 
        inversion H. subst. clear H.
        simpl. exists x1. exists x4. exists x5. pclearbot. easy.
      - destruct xs; try easy. destruct ys; try easy. destruct ys0; try easy. destruct ys1; try easy.
        inversion H26. inversion H20. inversion H12. subst. clear H26 H20 H12.
        specialize(IHn xs p q ctxG ys s0 g ys0 ys1). apply IHn; try easy.
    }
    destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H2. destruct H3. destruct H6.
    rename x into g'. 
    specialize(merge_onth_recv n p LQ ys1 x1 H27 H6); intros. destruct H10. subst.
    specialize(merge_onth_send n q LP ys0 x0 H21 H2); intros. destruct H10. subst.
    rename x1 into LP'. rename x into LQ'.
    
    specialize(H8 g' p q l LP' LQ' ST).
    specialize(merge_label_sendb ys0 LP LP' ST n l q H21 H2 H1); intros. 
    assert (exists (LS' : sort) (LT' : ltt), onth l LQ' = Some (LS', LT')).
    {
      apply H8; try easy.
      exists ctxG. split; try easy. split; try easy.
      intros. apply H4. apply ha_sendr with (n := n) (s := s0) (g := g); try easy.
      
    }
    destruct H11. destruct H11.
    specialize(merge_label_recv ys1 LQ LQ' (x, x0) n l p H27 H6 H11); intros. destruct H13.
    destruct x1. exists s1. exists l0. easy.
  apply proj_mon.
  apply proj_mon.
Qed.

Lemma typ_after_step_step_helper2 : forall xs ys p q l ctxG,
    Forall2
       (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (g' : gtt),
           u = Some (s, g) /\
           v = Some (s, g') /\
           typ_gtth ctxG g g' /\
           isgPartsC p g' /\ isgPartsC q g' /\ (exists G' : gtt, gttstepC g' G' p q l))) xs
       ys -> 
    exists zs,
    Forall (fun u => (u = None) \/ (exists s g, u = Some(s, g) /\ isgPartsC p g /\ isgPartsC q g)) ys /\ 
    Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ gttstepC g g' p q l)) ys zs.
Proof.
  induction xs; intros; try easy.
  - destruct ys; try easy. exists nil. easy.
  - destruct ys; try easy. inversion H. subst. clear H.
    specialize(IHxs ys p q l ctxG H5). destruct IHxs. rename x into zs.
    clear H5. destruct H. destruct H3.
    - exists (None :: zs). destruct H1. subst.
      split. constructor; try easy. left. easy.
      constructor; try easy. left. easy.
    - destruct H1. destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. destruct H4. destruct H5.
      destruct H6. exists (Some (x, x2) :: zs). subst. split.
      constructor; try easy. right. exists x. exists x1. easy.
      constructor; try easy. right. exists x. exists x1. exists x2. easy.
Qed.

Lemma typ_after_step_step_helper4 : forall ys zs p q l,
      SList ys ->
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ gttstepC g g' p q l)) ys zs ->
      p <> q.
Proof.
  induction ys; intros; try easy.
  specialize(SList_f a ys H); intros. destruct zs; try easy.
  inversion H0. subst.
  destruct H1.
  specialize(IHys zs p q l H1 H7). easy. destruct H1. destruct H2. subst.
  destruct zs; try easy. clear IHys H7 H0.
  destruct H5; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
  inversion H0. subst.
  pinversion H2; try easy.
  apply step_mon.
Qed. 

Lemma typ_after_step_step_helper5 : forall ys zs p q l,
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt), u = Some (s, g) /\ v = Some (s, g') /\ gttstepC g g' p q l)) ys
        zs ->
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g g' : gtt),
            u = Some (s0, g) /\ v = Some (s0, g') /\ upaco5 gttstep bot5 g g' p q l)) ys zs.
Proof.
  induction ys; intros; try easy.
  - destruct zs; try easy.
  - destruct zs; try easy. inversion H. subst.
    specialize(IHys zs p q l H5).
    constructor; try easy.
    destruct H3. left. easy.
    right. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. subst.
    exists x. exists x0. exists x1. split. easy. split. easy. left. easy.
Qed.

Lemma typ_after_step_step_helper6 : forall ys p q,
    Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt), u = Some (s, g) /\ isgPartsC p g /\ isgPartsC q g)) ys ->
    exists zs1 zs2, 
    Forall2 
         (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts p g' /\ (forall n : fin, exists m : fin, guardG n m g'))) ys zs1 /\
    Forall2 
         (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts q g' /\ (forall n : fin, exists m : fin, guardG n m g'))) ys zs2.
Proof.
  induction ys; intros.
  - exists nil. exists nil. easy.
  - inversion H. subst. clear H.
    specialize(IHys p q H3). destruct IHys. destruct H. destruct H. rename x into zs1. rename x0 into zs2. clear H3.
    destruct H2.
    - exists (None :: zs1). exists (None :: zs2).
      subst. split. constructor; try easy. left. easy.
      constructor; try easy. left. easy.
    - destruct H1. destruct H1. destruct H1. destruct H2. subst.
      unfold isgPartsC in *. destruct H2. destruct H3.
      exists (Some (x, x1) :: zs1). exists (Some (x, x2) :: zs2).
      split. constructor; try easy. right. exists x. exists x0. exists x1. easy.
      constructor; try easy. right. exists x. exists x0. exists x2.
      easy.
Qed.

Lemma typ_after_step_step_helper7 : forall ys x p,
    Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * global)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (g' : global),
            u = Some (s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts p g' /\ (forall n : fin, exists m : fin, guardG n m g'))) ys x ->
      Forall2
        (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g : global) (g' : gtt),
            u = Some (s0, g) /\ v = Some (s0, g') /\ upaco2 gttT bot2 g g')) x ys.
Proof.
  induction ys; intros.
  - destruct x; try easy.
  - destruct x; try easy. inversion H.
    subst. specialize(IHys x p H5). clear H5 H. constructor; try easy.
    destruct H3. left. easy. destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H1.
    subst. right. exists x0. exists x2. exists x1. split. easy. split. easy. left. easy.
Qed.

Lemma typ_after_step_step_helper8 : forall ys x s s' p,
      SList ys ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * global)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (g' : global),
            u = Some (s, g) /\ v = Some (s, g') /\ gttTC g' g /\ isgParts p g' /\ (forall n : fin, exists m : fin, guardG n m g'))) ys x ->
      (forall n : fin, exists m : fin, guardG n m (g_send s s' x)) /\ isgParts p (g_send s s' x).
Proof.
  induction ys; intros; try easy.
  destruct x; try easy.
  inversion H0. subst. clear H0.
  specialize(SList_f a ys H); intros. destruct H0.
  specialize(IHys x s s' p). 
  specialize(IHys H0 H6). split. 
  destruct IHys. destruct H4. destruct H3. subst. intros. specialize(H1 n). destruct H1.
  exists x0. inversion H1. constructor. subst. constructor; try easy. constructor; try easy. left. easy.
  destruct H3 as (s1,(g,(g',(Ha,(Hb,(Hc,(Hd,He))))))). subst.
  intros. specialize(H1 n). destruct H1. destruct n. exists 0. constructor.
  specialize(He n). destruct He. exists (Nat.max x1 x0); intros.
  constructor. constructor; try easy. right. exists s1. exists g'. split. easy.
  specialize(guardG_more n x1 (Nat.max x1 x0) g'); intros. apply H4; try easy. apply max_l.
  apply Forall_forall; intros.
  inversion H1. subst. specialize(Forall_forall (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ guardG n x0 g)) x); intros.
  destruct H5. specialize(H5 H9). specialize(H5 x2 H4). destruct H5. left. easy.
  destruct H5 as (s3,(g3,(Hta,Htb))). subst. right. exists s3. exists g3.
  split. easy. 
  specialize(guardG_more n x0 (Nat.max x1 x0) g3); intros. apply H5; try easy. apply max_r.
  apply isgParts_xs; try easy.
  destruct H0. destruct H1. subst.
  destruct H4; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
  inversion H0. subst. split. destruct x; try easy. destruct H3.
  intros. destruct n. exists 0. constructor. specialize(H3 n). destruct H3. exists x.
  constructor. constructor; try easy. right. exists x1. exists x3. split. easy. easy.
  apply isgParts_x; try easy.
Qed.

Lemma typ_after_step_step : forall p q l G L1 L2 S T S' T',
  wfgC G ->
  projectionC G p (ltt_send q L1) -> 
  onth l L1 = Some(S, T) ->
  projectionC G q (ltt_recv p L2) -> 
  onth l L2 = Some(S', T') ->
  (isgPartsC p G /\ isgPartsC q G) /\ exists G', gttstepC G G' p q l. 
Proof.
  intros. 
  specialize(canon_rep_s G p q L1 L2 S T S' T' l H H0 H1 H2 H3); intros.
  destruct H4. rename x into Gl.
  destruct H4. destruct H4. destruct H4. destruct H4. destruct H5. destruct H6. destruct H7. clear H8. rename x into ctxG.
  specialize(typ_after_step_ctx_loose H7); intros. clear H7.
  
  revert H H0 H1 H2 H3 H4 H5 H6 H8. clear x0 x1.
  revert p q l G L1 L2 S T S' T' ctxG.
  induction Gl using gtth_ind_ref; intros.
  - inversion H4. subst.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s'0, Gjk) /\
              projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG); intros.
    destruct H7. specialize(H7 H8). clear H8 H9.
    specialize(some_onth_implies_In n ctxG G H10); intros. 
    specialize(H7 (Some G) H8). destruct H7; try easy. destruct H7. destruct H7. destruct H7. destruct H9.
    destruct H11. destruct H11. destruct H11. destruct H11. destruct H11. destruct H12. inversion H7. subst.
    split.
    - split.
      apply triv_pt_p; try easy.
      apply triv_pt_q; try easy.
    - exists x2. 
      pinversion H0; try easy. subst.
      pinversion H2; try easy. subst.
      pfold. apply steq with (s := x1); try easy.
      apply proj_mon.
      apply proj_mon.
  - rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    inversion H5. subst.
    pinversion H1; try easy. subst. 
    assert False. apply H6. constructor. easy. subst.
    pinversion H3; try easy. subst.
    specialize(wfgC_after_step_all H12 H0); intros. rename H0 into Ht.
    specialize(proj_inv_lis p q l s s' ys L1 L2 S T S' T'); intros.
    assert(s = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
     s <> p /\
     s' <> q /\
     Forall
       (fun u : option (sort * gtt) =>
        u = None \/
        (exists
           (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
         (T T' : sort * ltt),
           u = Some (s, g) /\
           projectionC g p (ltt_send q LP') /\
           projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T'))
       ys).
    {
      apply H0; try easy. pfold. easy. pfold. easy.
    }
    destruct H10; try easy. destruct H10. destruct H11. clear H10 H11. clear H0 Ht.
    assert(List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\
        typ_gtth ctxG g g' /\
        (isgPartsC p g' /\ isgPartsC q g' /\ (exists G', gttstepC g' G' p q l))
    )) xs ys).
    {
      clear H27 H23 H22 H19 H18 H21 H17 H16 H13 H12 H14 H5 H4 H3 H2 H1.
      revert H24 H9 H15 H8 H H6 H7. clear H20 H26.
      clear ys0 ys1 S T S' T' L1 L2. 
      revert s s' p q l ctxG ys.
      induction xs; intros.
      - destruct ys; try easy.
      - destruct ys; try easy.
        inversion H. inversion H24. inversion H9. inversion H15. clear H H24 H9 H15. subst.
        assert (Forall2
         (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
          u = None /\ v = None \/
          (exists (s0 : sort) (g : gtth) (g' : gtt),
             u = Some (s0, g) /\
             v = Some (s0, g') /\
             typ_gtth ctxG g g' /\
             isgPartsC p g' /\ isgPartsC q g' /\ (exists G' : gtt, gttstepC g' G' p q l))) xs
         ys).
       {
        specialize(IHxs s s' p q l ctxG ys). apply IHxs; try easy.
        specialize(ishParts_hxs H6); try easy.
        specialize(ishParts_hxs H7); try easy.
       }
       constructor; try easy.
       clear H H22 H16 H11 H3 IHxs.
       destruct H20. left. easy.
       destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
       destruct H14; try easy. destruct H. destruct H. destruct H. inversion H. subst. clear H.
       destruct H10; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H.
       inversion H. subst. clear H.
       destruct H2; try easy. destruct H. destruct H. destruct H. inversion H. subst. clear H.
       rename x3 into Gl. rename x1 into G. rename x4 into LQ. rename x5 into LP. destruct x6. destruct x7.
       right. exists x2. exists Gl. exists G. split; try easy. split. easy. split. easy.
       specialize(H2 p q l G LQ LP s0 l0 s1 l1 ctxG). 
       assert((isgPartsC p G /\ isgPartsC q G) /\ (exists G' : gtt, gttstepC G G' p q l)).
       apply H2; try easy. 
       specialize(ishParts_x H6); try easy.
       specialize(ishParts_x H7); try easy.
       destruct H; try easy.
    }
    specialize(typ_after_step_step_helper2 xs ys p q l ctxG H0); intros. destruct H10.
    rename x into zs. destruct H10.
    specialize(typ_after_step_step_helper3 xs ys ctxG H14 H15); intros.
    specialize(typ_after_step_step_helper4 ys zs p q l H25 H11); intros.
    assert((exists G' : gtt, gttstepC (gtt_send s s' ys) G' p q l)).
    {
      exists (gtt_send s s' zs).
      pfold. apply stneq; try easy.
      specialize(typ_after_step_step_helper5 ys zs p q l H11); intros. easy.
    }
    split; try easy.
    apply proj_mon.
    apply proj_mon.
Qed.

Lemma typ_after_step_h_helper : forall L1 l S T,
    Forall2R
       (fun u v : option (sort * ltt) =>
        u = None \/
        (exists (s s' : sort) (t t' : ltt),
           u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t'))
       (extendLis l (Some (S, T))) L1 -> 
    exists ST, onth l L1 = Some ST.
Proof.
  intros L1 l. revert L1. induction l; intros.
  - destruct L1; try easy. inversion H. subst. 
    destruct H3; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1.
    subst. exists (x0, x2). easy.
  - destruct L1; try easy.
    inversion H. subst. specialize(IHl L1 S T H5). destruct IHl. 
    exists x. easy.
Qed.

Lemma typ_after_step_h : forall p q l G L1 L2 S T xs y,
  wfgC G ->
  projectionC G p (ltt_send q L1) -> 
  subtypeC (ltt_send q (extendLis l (Datatypes.Some(S,T)))) (ltt_send q L1) ->
  projectionC G q (ltt_recv p L2) -> 
  onth l xs = Some y ->
  subtypeC (ltt_recv p xs) (ltt_recv p L2) -> 
  exists G', gttstepC G G' p q l.
Proof.
  intros.
  specialize(typ_after_step_step p q l G L1 L2); intros.
  specialize(subtype_send_inv q (extendLis l (Some (S, T))) L1 H1); intros.
  specialize(subtype_recv_inv p xs L2 H4); intros.
  specialize(projection_step_label_s G p q l L1 L2); intros.
  specialize(typ_after_step_h_helper L1 l S T H6); intros. destruct H9.
  specialize(H8 x). 
  assert(exists (LS' : sort) (LT' : ltt), onth l L2 = Some (LS', LT')). apply H8; try easy.
  destruct H10. destruct H10.
  destruct x. 
  specialize(H5 s l0 x0 x1).
  apply H5; try easy. 
Qed.

Lemma typ_after_step_12_helper : forall ys2 x p,
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgCw g)) ys2 ->
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ (isgPartsC p g -> False))) ys2 -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt), u = Some (s, g) /\ v = Some t /\ projectionC g p t))
        ys2 x -> 
      Forall (fun u => u = None \/ u = Some ltt_end) x.
Proof.
  induction ys2; intros; try easy.
  - destruct x; try easy.
  - destruct x; try easy. inversion H. subst. clear H. inversion H0. subst. clear H0.
    inversion H1. subst. clear H1.
    specialize(IHys2 x p).
    assert(Forall (fun u : option ltt => u = None \/ u = Some ltt_end) x).
    apply IHys2; try easy. constructor; try easy.
    destruct H7. destruct H0. left. easy.
    destruct H0 as (s1,(g1,(t1,(Ha,(Hb,Hc))))). subst.
    destruct H3; try easy. destruct H0 as (s2,(g2,(Hd,He))). inversion Hd. subst.
    destruct H4; try easy. destruct H0 as (s3,(g3,(Hf,Hg))). inversion Hf. subst.
    pinversion Hc; try easy. right. easy.
    subst. specialize(He H1). easy.
    subst. specialize(He H1). easy.
    subst. specialize(He H3). easy.
    apply proj_mon.
Qed.

Lemma merge_same : forall ys ys0 ys1 p q l LP LQ S T S' T' ctxG SI s s' xs,
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) ys ys0 ->
      isMerge (ltt_send q LP) ys0 ->
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) ys ys1 ->
      Forall
       (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s', Gjk) /\
              projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option sort) =>
              u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s))
             lsg SI)) ctxG ->
      isMerge (ltt_recv p LQ) ys1 ->
      onth l LP = Some (S, T) ->
      onth l LQ = Some (S', T') ->
      (ishParts p (gtth_send s s' xs) -> False) ->
      (ishParts q (gtth_send s s' xs) -> False) ->
      Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys ->
      Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys ->
      Forall (fun u => u = None \/ (exists s g LP' LQ', u = Some (s, g) /\
          projectionC g p (ltt_send q LP') /\ onth l LP' = Some (S, T) /\
          projectionC g q (ltt_recv p LQ') /\ onth l LQ' = Some (S', T'))) ys.
Proof.
  intros. rename H10 into Ht.
  apply Forall_forall; intros. 
  destruct x.
  - right.
    specialize(in_some_implies_onth p0 ys H10); intros. destruct H11. rename x into n.
    destruct p0.
    assert(exists LP LQ T T', onth n ys0 = Some (ltt_send q LP) /\ projectionC g p (ltt_send q LP) /\ onth n ys1 = Some (ltt_recv p LQ) /\ projectionC g q (ltt_recv p LQ) /\ onth l LP = Some T /\ onth l LQ = Some T' /\ wfgC g).
    {
      clear H10 H6 H5 H4 H1.
      specialize(typ_after_step_ctx_loose H3); intros. clear H3. clear SI S T S' T'. clear LP LQ.
      revert H1 H2 H0 H. revert H9 H8 H7 H11 Ht. revert ys ys0 ys1 p q l ctxG s g. revert s' s0 xs.
      induction n; intros; try easy.
      - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy. destruct xs; try easy.
        inversion H2. subst. inversion H0. subst. inversion H. subst. inversion H9. subst. inversion Ht. subst.
        clear H18 H13 H14 H12 H H0 H2 H9 Ht. simpl in H11. subst.
        destruct H5; try easy. destruct H. destruct H. destruct H. destruct H. destruct H.
        destruct H. destruct H. destruct H0. destruct H2. destruct H3. inversion H. subst.
        destruct H6; try easy. destruct H5. destruct H5. destruct H5. destruct H5. destruct H6.
        inversion H5. subst.
        destruct H10; try easy. destruct H6. destruct H6. destruct H6. destruct H6. destruct H10.
        inversion H6. subst.
        destruct H16; try easy. destruct H10. destruct H10. destruct H10. destruct H10. destruct H12.
        inversion H12. subst.
        destruct H15; try easy. destruct H10 as (st,(g,(Ha,Hb))). inversion Ha. subst.
        pclearbot. simpl. exists x1. exists x2. exists x3. exists x4.
        specialize(ishParts_x H8); intros.
        specialize(ishParts_x H7); intros.
        specialize(proj_inj Hb H0 H11); intros. subst.
        specialize(proj_inj Hb H2 H9); intros. subst. 
        easy.
      - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy. destruct xs; try easy.
        inversion H2. subst. inversion H0. subst. inversion H. subst. inversion H9. subst.
        specialize(IHn s' s0 xs ys ys0 ys1 p q l ctxG s g). apply IHn; try easy.
        specialize(ishParts_hxs H8); try easy.
        specialize(ishParts_hxs H7); try easy.
        inversion Ht; try easy.
    }
    destruct H12. destruct H12. destruct H12. destruct H12. destruct H12. destruct H13. destruct H14. destruct H15. destruct H16.
    exists s0. exists g. exists x. exists x0. destruct x1. destruct x2. split. easy. split. easy.
    destruct H17. 
    specialize(merge_label_recv_s ys1 LQ x0 (s2, l1) n l p H4 H14 H17); intros.
    specialize(merge_label_send_s ys0 LP x (s1, l0) n l q H1 H12 H16); intros.
    specialize(eq_trans (esym H19) H6); intros. inversion H21. subst.
    specialize(eq_trans (esym H20) H5); intros. inversion H22. subst.
    easy.
    left. easy.
Qed.

Lemma typ_after_step_1_helper : forall p q l G G' LP LQ S T S' T',
  wfgC G -> 
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some(S, T) ->
  projectionC G q (ltt_recv p LQ) -> 
  onth l LQ = Some(S', T') ->
  gttstepC G G' p q l -> 
  projectionC G' p T.
Proof.
  intros.
  specialize(canon_rep_s G p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
  destruct H5. rename x into Gl. rename H into Ht.
  revert H0 H1 H2 H3 H4 H5 Ht. revert p q l G G' LP LQ S S' T T'.
  induction Gl using gtth_ind_ref; intros.
  - destruct H5. destruct H. destruct H. destruct H. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9.
    rename x1 into Sn. rename x0 into SI. rename x into ctxG. 
    inversion H. subst.
    specialize(some_onth_implies_In n ctxG G H13); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s', Gjk) /\
              projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option sort) =>
              u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s))
             lsg SI)) ctxG); intros. destruct H12.
    specialize(H12 H7). clear H7 H14. 
    specialize(H12 (Some G) H11). destruct H12; try easy.
    destruct H7. destruct H7. destruct H7. destruct H12. destruct H14.
    destruct H14. destruct H14. destruct H14. destruct H14. destruct H14. destruct H16. destruct H17. destruct H18.
    subst. inversion H7. subst. clear H7.
    pinversion H4; try easy. subst. specialize(eq_trans H24 H14); intros. inversion H7. subst. easy.
    apply step_mon.
  - rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9. destruct H10.
    rename x into ctxG. rename x1 into Sn. rename x0 into SI. 
    inversion H5. subst. 
    pinversion H0; try easy. subst.
    assert False. apply H6. constructor. easy.
    pinversion H2; try easy. subst.
    pinversion H4; try easy. subst. 
    
    specialize(proj_inv_lis p q l s s' ys LP LQ S T S' T'); intros.
    assert (s = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
      s <> p /\
      s' <> q /\
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys).
    {
      pclearbot.
      apply H12; try easy. 
      specialize(typ_after_step_ctx_loose H8); try easy.
      pfold. easy. pfold. easy.
    }
    destruct H13; try easy. destruct H13. destruct H14.
    clear H15 H16 H19 H28 H29 H30 H13 H14 H12.
        
    assert (List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ projectionC g p T)) ys2).
    {
      clear H5 H4 H2 H0 H17.
      specialize(wfgC_after_step_all H22 Ht); intros. clear Ht. 
      specialize(merge_same ys ys0 ys1 p q l LP LQ S T S' T' ctxG SI s s' xs H33 H23 H24 H34 H8 H35 H1 H3 H6 H7 H18 H0); intros.
      clear H32 H27 H26 H25 H22 H21 H35 H31 H24 H20 H3 H1 H23 H34.
      clear ys0 ys1 LP LQ.
      revert H2 H0 H40 H18 H11 H10 H9 H8 H7 H6 H. clear H39 H33. 
      revert s s' p q l S S' T T' ys ys2 ctxG SI Sn.
      induction xs; intros; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
        inversion H0. subst. clear H0. inversion H40. subst. clear H40.
        inversion H18. subst. clear H18. inversion H. subst. clear H.
        inversion H2. subst. clear H2.
        specialize(IHxs s s' p q l S S' T T' ys ys2 ctxG SI Sn).
        assert (Forall
         (fun u : option (sort * gtt) =>
          u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ projectionC g p T)) ys2).
        {
          apply IHxs; try easy.
          - intros. apply H7.
            - case_eq (eqb q s); intros.
              assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb q s'); intros.
              assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (q <> s). apply eqb_neq; try easy. 
              assert (q <> s'). apply eqb_neq; try easy.
              inversion H; try easy. subst.
              apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
          - intros. apply H6.
            - case_eq (eqb p s); intros.
              assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb p s'); intros.
              assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (p <> s). apply eqb_neq; try easy. 
              assert (p <> s'). apply eqb_neq; try easy.
              inversion H; try easy. subst.
              apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
        }
        constructor; try easy.
        clear H H17 H15 H16 H14 H5 IHxs.
        destruct H12. destruct H. left. easy.
        destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
        destruct H1; try easy. destruct H as (s2,(g3,(LP,(LQ,(Hd,(He,(Hf,(Hg,Hh)))))))). inversion Hd. subst.
        destruct H13; try easy. destruct H as (s3,(g4,(g5,(Hi,(Hj,Hk))))). inversion Hj. subst.
        destruct H4; try easy. destruct H as (s4,(g6,(Hl,Hm))). inversion Hl. subst.
        destruct H3; try easy. destruct H as (s5,(g7,(Hn,Ho))). inversion Hn. subst.
        specialize(Ho p q l g6 g2 LP LQ S S' T T'). 
        right. exists s5. exists g2. split; try easy.
        apply Ho; try easy. destruct Hc; try easy.
        exists ctxG. exists SI. exists Sn. split. easy.
        - split. intros. apply H6. 
          - case_eq (eqb p s); intros.
            assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb p s'); intros.
            assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (p <> s). apply eqb_neq; try easy. 
            assert (p <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := s5) (g := g7); try easy.
        - split; try easy. intros. apply H7.
          - case_eq (eqb q s); intros.
            assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb q s'); intros.
            assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (q <> s). apply eqb_neq; try easy. 
            assert (q <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := s5) (g := g7); try easy.
    }
    assert(exists ys3, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some t /\ projectionC g p t)) ys2 ys3 /\ isMerge T ys3).
    {
      clear H33 H39 H32 H26 H25 H22 H21 H35 H34 H31 H24 H23 Ht H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H1 H0 H.
      revert H12 H40 H18 H17. clear H27 H20. revert p T xs ys. clear s s' LP LQ S S' T' SI Sn ys0 ys1.
      revert ctxG q l.
      
      induction ys2; intros; try easy.
      - destruct ys; try easy. destruct xs; try easy.
      - destruct ys; try easy. destruct xs; try easy.
        inversion H18. subst. inversion H12. subst. inversion H40. subst. clear H18 H12 H40.
        specialize(SList_f o0 xs H17); intros.
        destruct H.
        - assert (exists ys3, Forall2
            (fun (u : option (sort * gtt)) (v : option ltt) =>
             (u = None /\ v = None) \/
             (exists (s : sort) (g : gtt) (t : ltt), u = Some (s, g) /\ v = Some t /\ projectionC g p t))
            ys2 ys3 /\ isMerge T ys3).
          {
            apply IHys2 with (xs := xs) (q := q) (l := l) (ys := ys) (ctxG := ctxG); try easy.
          }
          destruct H0. clear IHys2.
          - destruct H6. destruct H5. subst. 
            exists (None :: x). split. constructor; try easy. left. easy.
            destruct H0.
            apply triv_merge2; try easy.
          - destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. subst.
            destruct H2; try easy. destruct H2. destruct H2. destruct H2. destruct H2. destruct H5.
            inversion H5. subst. 
            destruct H1; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
            exists (Some T :: x). split.
            constructor; try easy. right. exists x0. exists x1. exists T. easy.
            apply triv_merge3; try easy.
          - destruct H. destruct H0. subst.
            destruct ys; try easy. destruct ys2; try easy. clear H3 H8 H4 IHys2.
            destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
            inversion H. subst.
            destruct H6; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H3.
            inversion H0. subst.
            destruct H1; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
            exists (Some T :: nil). split.
            constructor; try easy. right. exists x0. exists x2. exists T. easy.
            constructor.
    }
    destruct H13. destruct H13. pfold.
    specialize(wfgCw_after_step (gtt_send s s' ys) (gtt_send s s' ys2) p q l); intros.
    assert(wfgCw (gtt_send s s' ys2)). apply H15; try easy. pfold. easy.
    clear H15.
    specialize(decidable_isgPartsC_s (gtt_send s s' ys2) p H16); intros.
    unfold Decidable.decidable in H15.
    destruct H15.
    - apply proj_cont with (ys := x); try easy.
      revert H13. apply Forall2_mono; intros. destruct H13. left. easy.
      right. destruct H13 as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
      subst. exists s1. exists g1. exists t1. split. easy. split. easy. left. easy.
    - unfold not in H15.
      specialize(part_cont_false_all_s ys2 s s' p); intros.
      assert(Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ (isgPartsC p g -> False))) ys2).
      apply H19; try easy. clear H19.

      specialize(typ_after_step_12_helper ys2 x p); intros.
      assert(Forall (fun u : option ltt => u = None \/ u = Some ltt_end) x).
      apply H19; try easy.
      specialize(wfgCw_after_step_all H22 H16); try easy.
      specialize(merge_end_s x T H29 H14); intros. subst.
      apply proj_end; try easy.
    apply step_mon.
    apply proj_mon.
    apply proj_mon.
Qed.

Lemma typ_after_step_2_helper : forall p q l G G' LP LQ S T S' T',
  wfgC G -> 
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some(S, T) ->
  projectionC G q (ltt_recv p LQ) -> 
  onth l LQ = Some(S', T') ->
  gttstepC G G' p q l -> 
  projectionC G' q T'.
Proof.
  intros.
  specialize(canon_rep_s G p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
  destruct H5. rename x into Gl. rename H into Ht.
  revert H0 H1 H2 H3 H4 H5 Ht. revert p q l G G' LP LQ S S' T T'.
  induction Gl using gtth_ind_ref; intros.
  - destruct H5. destruct H. destruct H. destruct H. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9.
    rename x1 into Sn. rename x0 into SI. rename x into ctxG. 
    inversion H. subst.
    specialize(some_onth_implies_In n ctxG G H13); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (g : gtt) (lsg : list (option (sort * gtt))),
           u = Some g /\
           g = gtt_send p q lsg /\
           (exists (s' : sort) (Gjk : gtt) (Tp Tq : ltt),
              onth l lsg = Some (s', Gjk) /\
              projectionC Gjk p Tp /\ T = Tp /\ projectionC Gjk q Tq /\ T' = Tq) /\
           Forall2
             (fun (u0 : option (sort * gtt)) (v : option sort) =>
              u0 = None /\ v = None \/ (exists (s : sort) (g' : gtt), u0 = Some (s, g') /\ v = Some s))
             lsg SI)) ctxG); intros. destruct H12.
    specialize(H12 H7). clear H7 H14. 
    specialize(H12 (Some G) H11). destruct H12; try easy.
    destruct H7. destruct H7. destruct H7. destruct H12. destruct H14.
    destruct H14. destruct H14. destruct H14. destruct H14. destruct H14. destruct H16. destruct H17. destruct H18.
    subst. inversion H7. subst. clear H7.
    pinversion H4; try easy. subst. specialize(eq_trans H24 H14); intros. inversion H7. subst. easy.
    apply step_mon.
  - rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. destruct H7. destruct H8. destruct H9. destruct H10.
    rename x into ctxG. rename x1 into Sn. rename x0 into SI. 
    inversion H5. subst. 
    pinversion H0; try easy. subst.
    assert False. apply H6. constructor. easy.
    pinversion H2; try easy. subst.
    pinversion H4; try easy. subst. 
    
    specialize(proj_inv_lis p q l s s' ys LP LQ S T S' T'); intros.
    assert (s = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
      s <> p /\
      s' <> q /\
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T')) ys).
    {
      pclearbot.
      apply H12; try easy. 
      specialize(typ_after_step_ctx_loose H8); try easy.
      pfold. easy. pfold. easy.
    }
    destruct H13; try easy. destruct H13. destruct H14.
    clear H15 H16 H19 H28 H29 H30 H13 H14 H12.
        
    assert (List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ projectionC g q T')) ys2).
    {
      clear H5 H4 H2 H0 H17.
      specialize(wfgC_after_step_all H22 Ht); intros. clear Ht. 
      specialize(merge_same ys ys0 ys1 p q l LP LQ S T S' T' ctxG SI s s' xs H33 H23 H24 H34 H8 H35 H1 H3 H6 H7 H18 H0); intros.
      clear H32 H27 H26 H25 H22 H21 H35 H31 H24 H20 H3 H1 H23 H34.
      clear ys0 ys1 LP LQ.
      revert H2 H0 H40 H18 H11 H10 H9 H8 H7 H6 H. clear H39 H33. 
      revert s s' p q l S S' T T' ys ys2 ctxG SI Sn.
      induction xs; intros; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
      - destruct ys; try easy. destruct ys2; try easy.
        inversion H0. subst. clear H0. inversion H40. subst. clear H40.
        inversion H18. subst. clear H18. inversion H. subst. clear H.
        inversion H2. subst. clear H2.
        specialize(IHxs s s' p q l S S' T T' ys ys2 ctxG SI Sn).
        assert (Forall
         (fun u : option (sort * gtt) =>
          u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ projectionC g q T')) ys2).
        {
          apply IHxs; try easy.
          - intros. apply H7.
            - case_eq (eqb q s); intros.
              assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb q s'); intros.
              assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (q <> s). apply eqb_neq; try easy. 
              assert (q <> s'). apply eqb_neq; try easy.
              inversion H; try easy. subst.
              apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
          - intros. apply H6.
            - case_eq (eqb p s); intros.
              assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
            - case_eq (eqb p s'); intros.
              assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
            - assert (p <> s). apply eqb_neq; try easy. 
              assert (p <> s'). apply eqb_neq; try easy.
              inversion H; try easy. subst.
              apply ha_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
        }
        constructor; try easy.
        clear H H17 H15 H16 H14 H5 IHxs.
        destruct H12. destruct H. left. easy.
        destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
        destruct H1; try easy. destruct H as (s2,(g3,(LP,(LQ,(Hd,(He,(Hf,(Hg,Hh)))))))). inversion Hd. subst.
        destruct H13; try easy. destruct H as (s3,(g4,(g5,(Hi,(Hj,Hk))))). inversion Hj. subst.
        destruct H4; try easy. destruct H as (s4,(g6,(Hl,Hm))). inversion Hl. subst.
        destruct H3; try easy. destruct H as (s5,(g7,(Hn,Ho))). inversion Hn. subst.
        specialize(Ho p q l g6 g2 LP LQ S S' T T'). 
        right. exists s5. exists g2. split; try easy.
        apply Ho; try easy. destruct Hc; try easy.
        exists ctxG. exists SI. exists Sn. split. easy.
        - split. intros. apply H6. 
          - case_eq (eqb p s); intros.
            assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb p s'); intros.
            assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (p <> s). apply eqb_neq; try easy. 
            assert (p <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := s5) (g := g7); try easy.
        - split; try easy. intros. apply H7.
          - case_eq (eqb q s); intros.
            assert (q = s). apply eqb_eq; try easy. subst. apply ha_sendp.
          - case_eq (eqb q s'); intros.
            assert (q = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
          - assert (q <> s). apply eqb_neq; try easy. 
            assert (q <> s'). apply eqb_neq; try easy.
            apply ha_sendr with (n := 0) (s := s5) (g := g7); try easy.
    }
    assert(exists ys3, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g t, u = Some(s, g) /\ v = Some t /\ projectionC g q t)) ys2 ys3 /\ isMerge T' ys3).
    {
      clear H33 H39 H32 H26 H25 H22 H21 H35 H34 H31 H24 H23 Ht H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H1 H0 H.
      revert H12 H40 H18 H17. clear H27 H20. revert p T' xs ys. clear s s' LP LQ S S' T SI Sn ys0 ys1.
      revert ctxG q l.
      
      induction ys2; intros; try easy.
      - destruct ys; try easy. destruct xs; try easy.
      - destruct ys; try easy. destruct xs; try easy.
        inversion H18. subst. inversion H12. subst. inversion H40. subst. clear H18 H12 H40.
        specialize(SList_f o0 xs H17); intros.
        destruct H.
        - assert (exists ys3, Forall2
            (fun (u : option (sort * gtt)) (v : option ltt) =>
             (u = None /\ v = None) \/
             (exists (s : sort) (g : gtt) (t : ltt), u = Some (s, g) /\ v = Some t /\ projectionC g q t))
            ys2 ys3 /\ isMerge T' ys3).
          {
            apply IHys2 with (xs := xs) (p := p) (l := l) (ys := ys) (ctxG := ctxG); try easy.
          }
          destruct H0. clear IHys2.
          - destruct H6. destruct H5. subst. 
            exists (None :: x). split. constructor; try easy. left. easy.
            destruct H0.
            apply triv_merge2; try easy.
          - destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. subst.
            destruct H2; try easy. destruct H2. destruct H2. destruct H2. destruct H2. destruct H5.
            inversion H5. subst. 
            destruct H1; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
            exists (Some T' :: x). split.
            constructor; try easy. right. exists x0. exists x1. exists T'. easy.
            apply triv_merge3; try easy.
          - destruct H. destruct H0. subst.
            destruct ys; try easy. destruct ys2; try easy. clear H3 H8 H4 IHys2.
            destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0.
            inversion H. subst.
            destruct H6; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H3.
            inversion H0. subst.
            destruct H1; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
            exists (Some T' :: nil). split.
            constructor; try easy. right. exists x0. exists x2. exists T'. easy.
            constructor.
    }
    destruct H13. destruct H13. pfold.
    specialize(wfgCw_after_step (gtt_send s s' ys) (gtt_send s s' ys2) p q l); intros.
    assert(wfgCw (gtt_send s s' ys2)). apply H15; try easy. pfold. easy.
    clear H15.
    specialize(decidable_isgPartsC_s (gtt_send s s' ys2) q H16); intros.
    unfold Decidable.decidable in H15.
    destruct H15.
    - apply proj_cont with (ys := x); try easy.
      revert H13. apply Forall2_mono; intros. destruct H13. left. easy.
      right. destruct H13 as (s1,(g1,(t1,(Ha,(Hb,Hc))))).
      subst. exists s1. exists g1. exists t1. split. easy. split. easy. left. easy.
    - unfold not in H15.
      specialize(part_cont_false_all_s ys2 s s' q); intros.
      assert(Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ (isgPartsC q g -> False))) ys2).
      apply H19; try easy. clear H19.

      specialize(typ_after_step_12_helper ys2 x q); intros.
      assert(Forall (fun u : option ltt => u = None \/ u = Some ltt_end) x).
      apply H19; try easy.
      specialize(wfgCw_after_step_all H22 H16); try easy.
      specialize(merge_end_s x T' H29 H14); intros. subst.
      apply proj_end; try easy.
    apply step_mon.
    apply proj_mon.
    apply proj_mon.
Qed.

Lemma typ_after_step_1 : forall p q l G G' LP LQ S T S' T' xs,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  subtypeC (ltt_send q (extendLis l (Datatypes.Some (S, T)))) (ltt_send q LP) ->
  projectionC G q (ltt_recv p LQ) ->
  onth l xs = Some (S', T') ->
  subtypeC (ltt_recv p xs) (ltt_recv p LQ) ->
  gttstepC G G' p q l ->
  exists L, 
  projectionC G' p L /\ subtypeC T L. 
Proof.
  intros.
  specialize(typ_after_step_1_helper p q l G G' LP LQ); intros.
  specialize(subtype_send_inv q (extendLis l (Some (S, T))) LP H1); intros.
  specialize(subtype_recv_inv p xs LQ H4); intros.
  specialize(projection_step_label G G' p q l LP LQ H H0 H2 H5); intros.
  destruct H9. destruct H9. destruct H9. destruct H9. destruct H9.
  rename x into s. rename x0 into s'. rename x1 into t. rename x2 into t'.
  
  specialize(H6 s t s' t' H H0 H9 H2 H10 H5).
  exists t. split; try easy.
  
  clear H10 H8 H6 H5 H4 H3 H2 H1 H0 H. clear s' t' xs T' S' LQ G G' p q.
  revert H9 H7. revert LP S T t s.
  induction l; intros; try easy.
  - destruct LP; try easy. inversion H7. subst.
    destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0.
    destruct H1. inversion H. subst. simpl in H9. inversion H9. subst. easy.
  - destruct LP; try easy. inversion H7. subst. specialize(IHl LP S T t s). apply IHl; try easy.
Qed.

Lemma typ_after_step_2 : forall p q l G G' LP LQ S T S' T' xs,
  wfgC G ->
  projectionC G p (ltt_send q LP) ->
  subtypeC (ltt_send q (extendLis l (Datatypes.Some (S, T)))) (ltt_send q LP) ->
  projectionC G q (ltt_recv p LQ) ->
  onth l xs = Some (S', T') ->
  subtypeC (ltt_recv p xs) (ltt_recv p LQ) ->
  gttstepC G G' p q l ->
  exists L, 
  projectionC G' q L /\ subtypeC T' L. 
Proof.
  intros.
  specialize(typ_after_step_2_helper p q l G G' LP LQ); intros.
  specialize(subtype_send_inv q (extendLis l (Some (S, T))) LP H1); intros.
  specialize(subtype_recv_inv p xs LQ H4); intros.
  specialize(projection_step_label G G' p q l LP LQ H H0 H2 H5); intros.
  destruct H9. destruct H9. destruct H9. destruct H9. destruct H9.
  rename x into s. rename x0 into s'. rename x1 into t. rename x2 into t'.
  
  specialize(H6 s t s' t' H H0 H9 H2 H10 H5).
  exists t'. split; try easy.
  
  clear H9 H7 H6 H5 H4 H2 H1 H0 H.
  clear s t S T LP G G' p q.
  revert H3 H8 H10. revert LQ S' T' xs t' s'.
  induction l; intros.
  - destruct LQ; try easy. destruct xs; try easy.
    inversion H8. subst. simpl in *. subst.
    destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H0.
    destruct H1. inversion H0. inversion H. subst. easy.
  - destruct LQ; try easy. destruct xs; try easy. 
    inversion H8. subst. simpl in *. 
    specialize(IHl LQ S' T' xs t' s'). apply IHl; try easy.
Qed.

Lemma typ_after_step_3_helper_h1 : forall l lsg ys s' Gjk s,
      onth l lsg = Some (s', Gjk) -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g : gtt) (t : ltt),
            u = Some (s0, g) /\ v = Some t /\ upaco3 projection bot3 g s t)) lsg ys -> 
      exists t, onth l ys = Some t /\ projectionC Gjk s t.
Proof.
  induction l; intros.
  - destruct lsg; try easy. 
    inversion H0. subst. clear H0.
    simpl in H. subst. destruct H3; try easy. destruct H as (s0,(g,(t,(Ha,(Hb,Hc))))).
    subst. exists t. inversion Ha. subst. destruct Hc; try easy.
  - destruct lsg; try easy. 
    inversion H0. subst. clear H0. 
    specialize(IHl lsg l' s' Gjk s). apply IHl; try easy.
Qed.


Lemma typ_after_step_3_helper_h2 : forall [n ys s0 g xs ctxG],
        onth n ys = Some (s0, g) -> 
        Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys -> 
        exists g', onth n xs = Some (s0, g') /\ typ_gtth ctxG g' g.
Proof.
  induction n; intros.
  - destruct ys; try easy. destruct xs; try easy.
    inversion H0. subst. clear H0.
    simpl in H. subst. destruct H4; try easy. destruct H as (s,(g0,(g',(Ha,(Hb,Hc))))).
    inversion Hb. subst.
    exists g0. easy.
  - destruct ys; try easy. destruct xs; try easy.
    inversion H0. subst. clear H0.
    specialize(IHn ys s0 g xs ctxG). apply IHn; try easy.
Qed.

Lemma typ_after_step_3_helper_h3 : forall ys ys2 p q l,
    Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q l)) ys ys2 -> 
    (forall t : string,
      t <> p ->
      t <> q ->
      Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s' : sort) (g : gtt),
            u = Some (s', g) /\
            (forall (G' : gtt) (T : ltt),
             gttstepC g G' p q l ->
             projectionC g t T -> wfgC G' -> exists T' : ltt, projectionC G' t T' /\ T = T'))) ys) ->
    Forall
        (fun u : option (sort * gtt) =>
         u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys2 ->
    forall t, t <> p -> t <> q -> Forall2 (fun u v => (u = None /\ v = None) \/ (exists s' g g', u = Some(s', g) /\ v = Some(s', g') /\
      gttstepC g g' p q l /\ (forall T, projectionC g t T -> exists T', projectionC g' t T' /\ T = T'
    ))) ys ys2.
Proof.
  induction ys; intros; try easy.
  - destruct ys2; try easy.
  - destruct ys2; try easy.
    inversion H. subst. clear H. inversion H1. subst. clear H1.
    assert(forall t : string,
     t <> p ->
     t <> q ->
     Forall
       (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s' : sort) (g : gtt),
           u = Some (s', g) /\
           (forall (G' : gtt) (T : ltt),
            gttstepC g G' p q l ->
            projectionC g t T -> wfgC G' -> exists T' : ltt, projectionC G' t T' /\ T = T'))) 
       ys).
    {
      intros. specialize(H0 t0 H H1). inversion H0; try easy.
    }
    specialize(H0 t H2 H3). inversion H0. subst. clear H0.
    specialize(IHys ys2 p q l H9 H H6 t H2 H3). constructor; try easy.
    clear H10 H6 H9 IHys H.
    destruct H7. left. easy.
    destruct H as (s1,(g,(g',(Ha,(Hb,Hc))))). subst.
    destruct H5; try easy. destruct H as (s2,(g2,(Hta,Htb))). inversion Hta. subst. clear Hta.
    destruct H8; try easy. destruct H as (s3,(g3,(Hd,He))). inversion Hd. subst. clear Hd.
    right. exists s3. exists g3. exists g2. split. easy. split. easy.
    split. destruct Hc; try easy.
    intros. specialize(He g2 T). apply He; try easy. destruct Hc; try easy.
Qed.

Lemma typ_after_step_3_helper_h4 : forall l lsg s' Gjk ys s T,
      onth l lsg = Some (s', Gjk) ->  
      Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g : gtt) (t : ltt),
            u = Some (s0, g) /\ v = Some t /\ upaco3 projection bot3 g s t)) lsg ys -> 
      isMerge T ys -> 
      projectionC Gjk s T.
Proof.
  induction l; intros; try easy.
  - destruct lsg; try easy. destruct ys; try easy. 
    inversion H0. subst. clear H0. simpl in H. subst.
    destruct H5; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
    pclearbot.
    inversion H1; try easy. 
  - destruct lsg; try easy. destruct ys; try easy. 
    inversion H0. subst. clear H0. simpl in H. subst.
    specialize(IHl lsg s' Gjk ys s T). apply IHl; try easy.
    inversion H1; try easy. subst. destruct lsg; try easy. destruct l; try easy.
Qed.

Lemma typ_after_step_3_helper_h5 : forall ys ys2 ys3 p q l r,
      Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s' : sort) (g g' : gtt),
            u = Some (s', g) /\
            v = Some (s', g') /\
            gttstepC g g' p q l /\
            (forall T : ltt, projectionC g r T -> exists T' : ltt, projectionC g' r T' /\ T = T'))) ys ys2 -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some (s, t) /\ upaco3 projection bot3 g r t)) ys ys3 -> 
      Forall2
        (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
         u = None /\ v = None \/
         (exists (s0 : sort) (g : gtt) (t : ltt),
            u = Some (s0, g) /\ v = Some (s0, t) /\ upaco3 projection bot3 g r t)) ys2 ys3.
Proof.
  induction ys; intros; try easy.
  - destruct ys2; try easy. destruct ys3; try easy.
  - destruct ys2; try easy.
    inversion H. subst. clear H. inversion H0. subst. clear H0.
    specialize(IHys ys2 ys3 p q l r).
    assert(Forall2
         (fun (u : option (sort * gtt)) (v : option (sort * ltt)) =>
          u = None /\ v = None \/
          (exists (s0 : sort) (g : gtt) (t : ltt),
             u = Some (s0, g) /\ v = Some (s0, t) /\ upaco3 projection bot3 g r t)) ys2 ys3).
    apply IHys; try easy. constructor; try easy. clear H H7 H6 IHys.
    destruct H3. left. destruct H4. easy. 
    destruct H. subst. destruct H0 as (s1,(g1,(g2,(Ha,Hb)))). easy.
    destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). subst.
    destruct H4; try easy. destruct H as (s2,(g2,(g3,(Hd,(He,(Hf,Hg)))))). inversion Hd. subst.
    right. exists s2. exists g3. exists t1. 
    specialize(Hg t1).
    assert(exists T', projectionC g3 r T' /\ t1 = T'). apply Hg; try easy.
    destruct Hc; try easy.
    destruct H. subst. split. easy. split. easy. left. destruct H. subst. easy.
Qed.

Lemma typ_after_step_3_helper_h6 : forall ys ys2 ys3 p q l r,
        Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys3 -> 
        Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s' : sort) (g g' : gtt),
            u = Some (s', g) /\
            v = Some (s', g') /\
            gttstepC g g' p q l /\
            (forall T : ltt, projectionC g r T -> exists T' : ltt, projectionC g' r T' /\ T = T'))) ys ys2 ->
        Forall2
          (fun (u : option (sort * gtt)) (v : option ltt) =>
           u = None /\ v = None \/
           (exists (s0 : sort) (g : gtt) (t : ltt),
              u = Some (s0, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys2 ys3.
Proof.
  induction ys; intros; try easy.
  - destruct ys2; try easy.
  - destruct ys2; try easy. destruct ys3; try easy.
    inversion H. subst. clear H. inversion H0. subst. clear H0.
    specialize(IHys ys2 ys3 p q l r).
    assert(Forall2
         (fun (u : option (sort * gtt)) (v : option ltt) =>
          u = None /\ v = None \/
          (exists (s0 : sort) (g : gtt) (t : ltt),
             u = Some (s0, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys2 ys3).
    apply IHys; try easy.
    constructor; try easy.
    - destruct H3. destruct H0. subst. destruct H4. left. easy.
      destruct H0 as (s1,(g1,(t1,(Ha,Hb)))). easy.
    - destruct H0 as (s1,(g1,(g2,(Ha,(Hb,(Hc,Hd)))))). subst.
      destruct H4; try easy. destruct H0 as (s2,(g3,(t1,(He,(Hf,Hg))))). inversion He. subst.
      right. exists s2. exists g2. exists t1. split. easy. split. easy. left.
      specialize(Hd t1).
      assert(exists T' : ltt, projectionC g2 r T' /\ t1 = T'). apply Hd; try easy.
      destruct Hg; try easy.
      destruct H0. destruct H0. subst. easy.
Qed.

Lemma part_after_step_r_helper : forall n ys s1 g1 ys1 ys0 xs p q l r ctxG,
    onth n ys = Some (s1, g1) -> 
    Forall
       (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys -> 
    Forall2
        (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g r t)) ys ys1 -> 
    Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q l)) ys ys0 ->
    Forall2
        (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtth) (g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxG g g')) xs ys ->
    exists g2 g3 t,
    onth n ys0 = Some (s1, g2) /\ gttstepC g1 g2 p q l /\
    onth n xs = Some (s1, g3) /\ typ_gtth ctxG g3 g1 /\
    onth n ys1 = Some t /\ projectionC g1 r t /\ wfgC g1.
Proof.
  induction n; intros; try easy.
  - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy.
    destruct xs; try easy.
    inversion H3. subst. clear H3. inversion H2. subst. clear H2. 
    inversion H1. subst. clear H1. inversion H0. subst. clear H0.
    simpl in H. subst. clear H4 H11 H10 H9.
    destruct H7; try easy. destruct H as (s2,(g2,(g3,(Ha,(Hb,Hc))))). inversion Hb. subst.
    destruct H6; try easy. destruct H as (s3,(g4,(g5,(Hd,(He,Hf))))). inversion Hd. subst.
    destruct H5; try easy. destruct H as (s4,(g6,(t1,(Hg,(Hi,Hj))))). inversion Hg. subst.
    destruct H3; try easy. destruct H as (s5,(g7,(Hk,Hl))). inversion Hk. subst.
    simpl. exists g5. exists g2. exists t1. pclearbot. easy.
  - destruct ys; try easy. destruct ys1; try easy. destruct ys0; try easy.
    destruct xs; try easy.
    inversion H3. subst. clear H3. inversion H2. subst. clear H2. 
    inversion H1. subst. clear H1. inversion H0. subst. clear H0.
    specialize(IHn ys s1 g1 ys1 ys0 xs p q l r ctxG). apply IHn; try easy.
Qed.

Lemma part_after_step_r : forall G r p q G' l T,
        wfgC G -> 
        wfgC G' ->
        r <> p -> r <> q ->
        isgPartsC r G -> 
        gttstepC G G' p q l -> 
        projectionC G r T ->
        isgPartsC r G'.
Proof.
  intros.
  rename H0 into Htt. rename H1 into H0. rename H2 into H1. rename H3 into H2.
  rename H4 into H3. rename H5 into H4.
  specialize(wfgC_step_part G G' p q l H H3); intros.
  specialize(balanced_to_tree G p H H5); intros. clear H5.
  destruct H6 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))). clear Hd.
  revert Hc Hb Ha H4 H3 H2 H1 H0 H Htt. revert ctxG T l G' r p q G.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha. subst.
    specialize(some_onth_implies_In n ctxG G H7); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : list (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
    destruct H6. specialize(H6 Hc). clear H8 Hc.
    specialize(H6 (Some G) H5). destruct H6; try easy.
    destruct H6 as (q1,(lsg,Hd)).
    - destruct Hd. inversion H6. subst. pinversion H3; try easy. subst.
      pinversion H4; try easy. subst. easy. subst. easy. subst.
      assert(exists t, onth l ys = Some t /\ projectionC G' r t).
      {
        clear H21 H17 H14 H13 H11 H12 H15 H5 H7 H H0 H1 H6 H2 H3 H4 Ha Hb Htt.
        revert H20 H16.
        revert G' r lsg s ys.
        induction l; intros; try easy.
        - destruct lsg; try easy. destruct ys; try easy.
          inversion H20. subst. clear H20.
          simpl in H16. subst. destruct H2; try easy. 
          destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
          exists t1. destruct Hc; try easy.
        - destruct lsg; try easy. destruct ys; try easy.
          inversion H20. subst. clear H20.
          specialize(IHl G' r lsg s ys). apply IHl; try easy.
      }
      destruct H8 as (t1,(He,Hf)).
      pinversion Hf; try easy. subst.
      specialize(merge_end_back l ys T He H21); intros. subst.
      assert(projectionC (gtt_send p q lsg) r ltt_end). pfold. easy.
      specialize(pmergeCR (gtt_send p q lsg) r); intros.
      assert(False). apply H10; try easy. easy.
    apply proj_mon. apply proj_mon. apply step_mon.
    - destruct H6. inversion H6. subst. pinversion H3; try easy. apply step_mon.
    - inversion H6. subst. pinversion H3; try easy. apply step_mon.
  - inversion Ha. subst.
    pinversion H3; try easy. subst. assert False. apply Hb. constructor. easy.
    subst. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    clear H21.
    - case_eq (eqb r s); intros.
      assert (r = s). apply eqb_eq; try easy. subst. apply triv_pt_p; try easy.
    - case_eq (eqb r s'); intros.
      assert (r = s'). apply eqb_eq; try easy. subst. apply triv_pt_q; try easy.
    - assert (r <> s). apply eqb_neq; try easy. 
      assert (r <> s'). apply eqb_neq; try easy.
      clear H6 H7.
    specialize(part_cont ys r s s' H2 H8 H17); intros.
    destruct H6 as (n,(s1,(g1,(Hta,Htb)))).
    pinversion H4; try easy. subst. easy. subst. easy. subst.
    specialize(wfgC_after_step_all H10 H5); intros.
    specialize(part_after_step_r_helper n ys s1 g1 ys1 ys0 xs p q l r ctxG); intros.
    assert(exists (g2 : gtt) (g3 : gtth) (t : ltt),
       onth n ys0 = Some (s1, g2) /\
       gttstepC g1 g2 p q l /\
       onth n xs = Some (s1, g3) /\
       typ_gtth ctxG g3 g1 /\ onth n ys1 = Some t /\ projectionC g1 r t /\ wfgC g1).
    {
      apply H7; try easy.
    }
    clear H7. destruct H18 as (g2,(g3,(t1,(Hsa,(Hsb,(Hsc,(Hsd,(Hse,(Hsf,Hsg))))))))).
    specialize(some_onth_implies_In n xs (s1, g3) Hsc); intros.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (ctxG : list (option gtt)) (T : ltt) (l : fin) (G' : gtt) (r p q : string) (G : gtt),
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (q0 : string) (lsg : list (option (sort * gtt))),
                 u0 = Some (gtt_send p q0 lsg) \/ u0 = Some (gtt_send q0 p lsg) \/ u0 = Some gtt_end))
             ctxG ->
           (ishParts p g -> False) ->
           typ_gtth ctxG g G ->
           projectionC G r T ->
           gttstepC G G' p q l -> isgPartsC r G -> r <> q -> r <> p -> wfgC G -> wfgC G' -> isgPartsC r G')))
      xs); intros.
    destruct H18. specialize(H18 H). clear H H24.
    specialize(H18 (Some (s1, g3)) H7). destruct H18; try easy.
    destruct H as (s3,(g4,(Hma,Hmb))). inversion Hma. subst.
    specialize(Hmb ctxG t1 l g2 r p q g1).
    assert(isgPartsC r g2).
    {
      apply Hmb; try easy.
      specialize(ishParts_n Hb Hsc); intros. apply H; try easy.
      specialize(wfgC_after_step_all H10 Htt); intros.
      specialize(Forall_forall (fun u : option (sort * gtt) =>
       u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) ys0); intros.
      destruct H18. specialize(H18 H). clear H24 H.
      specialize(some_onth_implies_In n ys0 (s3, g2) Hsa); intros.
      specialize(H18 (Some (s3, g2)) H). destruct H18; try easy.
      destruct H18 as (st1,(gt1,(Hmc,Hmd))). inversion Hmc. subst. easy.
    }
    apply part_cont_b with (n := n) (s := s3) (g := g2); try easy.
  apply proj_mon.
  apply step_mon.
Qed.

Lemma typ_after_step_3_helper : forall G G' p q s l L1 L2 LS LT LS' LT' T,
      wfgC G ->
      wfgC G' ->
      projectionC G p (ltt_send q L1) ->
      onth l L1 = Some (LS, LT) ->
      projectionC G q (ltt_recv p L2) ->
      onth l L2 = Some (LS', LT') ->
      gttstepC G G' p q l ->
      s <> q ->
      s <> p ->
      projectionC G s T -> 
      exists T', projectionC G' s T' /\ T = T'. 
Proof.
  intros.
  rename H0 into Htt. rename H1 into H0. rename H2 into H1.
  rename H3 into H2. rename H4 into H3. rename H5 into H4. rename H6 into H5.
  rename H7 into H6. rename H8 into H7.
  specialize(canon_rep_s G p q L1 L2 LS LT LS' LT' l H H0 H1 H2 H3); intros. 
  destruct H8. rename x into Gl. rename H into Ht.
  destruct H8 as (ctxG,(SI,(Sn,(Ha,(Hb,(Hc,(Hd,He))))))).
  clear He.
  specialize(typ_after_step_ctx_loose Hd); intros. clear Hd.
  clear SI Sn.
  revert H0 H1 H2 H3 H4 H5 H6 H7 Ha Hb Hc H Ht Htt. revert p q l G G' L1 L2 LS LS' LT LT' s T ctxG.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha. subst.
    specialize(Forall_forall (fun u : option gtt =>
       u = None \/
       (exists (g : gtt) (lsg : list (option (sort * gtt))),
          u = Some g /\
          g = gtt_send p q lsg /\
          (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
             onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq)))
      ctxG); intros.
    destruct H8. specialize(H8 H). clear H9 H.
    specialize(some_onth_implies_In n ctxG G H10); intros.
    specialize(H8 (Some G) H). destruct H8; try easy.
    destruct H8 as (g,(lsg,(Hta,(Htb,Htc)))). inversion Hta. subst. clear Hta.
    destruct Htc as (s',(Gjk,(Tp,(Tq,(Hsa,(Hsb,Hsc)))))). 
    pinversion H4; try easy. subst.
    specialize(eq_trans H17 Hsa); intros. inversion H8. subst. clear H8 H14 H13 H17.
    pinversion H7; try easy. 
    - subst. exists ltt_end. split. 
      pfold. apply proj_end; try easy.
      specialize(part_after_step (gtt_send p q lsg) Gjk p q s l L1 L2); intros.
      apply H8. apply H9; try easy. pfold. easy.
      constructor. 
    - subst. easy.
    - subst. easy.
    - subst. exists T. split. pfold. 
      specialize(typ_after_step_3_helper_h4 l lsg s' Gjk ys s T); intros.
      assert(projectionC Gjk s T). apply H8; try easy.
      pinversion H9; try easy. apply proj_mon.
      easy.
    apply proj_mon.
    apply step_mon.
  - inversion Ha. subst.
    rename s into r. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    pinversion H0; try easy. subst.
    assert False. apply Hb. constructor. easy.
    subst.
    pinversion H2; try easy. subst.
    specialize(proj_inv_lis p q l s s' ys L1 L2 LS LT LS' LT'); intros.
    assert(s = p /\ s' = q /\ (exists Gk : sort * gtt, onth l ys = Some Gk) \/
     s <> p /\
     s' <> q /\
     Forall
       (fun u : option (sort * gtt) =>
        u = None \/
        (exists
           (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
         (T T' : sort * ltt),
           u = Some (s, g) /\
           projectionC g p (ltt_send q LP') /\
           projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T'))
       ys). apply H9; try easy. pfold. easy. pfold. easy.
    destruct H10. destruct H10. subst. easy.
    destruct H10 as (H10,(Hsa,Hsb)). clear H10 Hsa H9.
    pinversion H4; try easy. subst. clear H12 H13 H16 H18 H19 H22.
    
    assert(forall t, t <> p -> t <> q -> List.Forall (fun u => u = None \/ (exists s' g, u = Some (s', g) /\ forall G' T, 
        gttstepC g G' p q l -> projectionC g t T -> wfgC G' -> exists T', projectionC G' t T' /\ T = T')) ys).
    {
      intros. apply Forall_forall; intros. rename H9 into Hka. rename H10 into Hkb. rename H11 into H9. destruct x.
      - right. specialize(in_some_implies_onth p0 ys H9); intros. destruct H10 as (n, H10).
        destruct p0. exists s0. exists g. split. easy.
        intros. rename H13 into Htl.
        specialize(typ_after_step_3_helper_h2 H10 H15); intros. destruct H13 as (g', (H13, Hla)).
        specialize(some_onth_implies_In n xs (s0, g') H13); intros.
        specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (p q : string) (l : fin) (G G' : gtt) (L1 L2 : list (option (sort * ltt)))
             (LS LS' : sort) (LT LT' : ltt) (s0 : string) (T : ltt) (ctxG : list (option gtt)),
           projectionC G p (ltt_send q L1) ->
           onth l L1 = Some (LS, LT) ->
           projectionC G q (ltt_recv p L2) ->
           onth l L2 = Some (LS', LT') ->
           gttstepC G G' p q l ->
           s0 <> q ->
           s0 <> p ->
           projectionC G s0 T ->
           typ_gtth ctxG g G ->
           (ishParts p g -> False) ->
           (ishParts q g -> False) ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (g0 : gtt) (lsg : list (option (sort * gtt))),
                 u0 = Some g0 /\
                 g0 = gtt_send p q lsg /\
                 (exists (s'0 : sort) (Gjk : gtt) (Tp Tq : ltt),
                    onth l lsg = Some (s'0, Gjk) /\ projectionC Gjk p Tp /\ projectionC Gjk q Tq))) ctxG ->
           wfgC G -> wfgC G' -> exists T' : ltt, projectionC G' s0 T' /\ T = T'))) xs); intros.
        destruct H18. specialize(H18 H). clear H19 H.
        specialize(H18 (Some (s0, g')) H16). destruct H18; try easy. 
        specialize(Forall_forall (fun u : option (sort * gtt) =>
         u = None \/
         (exists
            (s : sort) (g : gtt) (LP' LQ' : list (option (sort * ltt))) 
          (T T' : sort * ltt),
            u = Some (s, g) /\
            projectionC g p (ltt_send q LP') /\
            projectionC g q (ltt_recv p LQ') /\ onth l LP' = Some T /\ onth l LQ' = Some T'))
        ys); intros. destruct H18. specialize(H18 Hsb). clear Hsb H19.
        specialize(H18 (Some (s0, g)) H9). destruct H18; try easy.
        destruct H18 as (s1,(g1,(LP',(LQ',(T1,(T1',(Hma,(Hmb,(Hmc,(Hmd,Hme)))))))))).
        inversion Hma. subst. clear Hma.
        destruct H as (s2,(g2,(Hta,Htb))). inversion Hta. subst.
        specialize(Htb p q l g1 G' LP' LQ').
        destruct T1. destruct T1'. 
        specialize(Htb s0 s1 l0 l1 t T0 ctxG). apply Htb; try easy.
        specialize(ishParts_n Hb H13); intros. apply H. easy.
        specialize(ishParts_n Hc H13); intros. apply H. easy.
        specialize(wfgC_after_step_all H25 Ht); intros.
        specialize(Forall_prop n ys (s2, g1) (fun u : option (sort * gtt) =>
       u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) H10 H); intros.
        simpl in H18. destruct H18; try easy. destruct H18 as (st1,(gt1,(Hba,Hbb))). inversion Hba. subst. easy.
        left. easy.
    }
    pose proof H9 as Hla.
    specialize(H9 s H28 H29).
    specialize(wfgC_after_step_all H25 Htt); intros. rename H10 into Htk.
    specialize(typ_after_step_3_helper_h3 ys ys2 p q l H37 Hla Htk); intros. clear Hla H37.
    pinversion H7. subst.
    - exists ltt_end. split.
      pfold. apply proj_end. intros. apply H11.
      specialize(part_after_step (gtt_send s s' ys) (gtt_send s s' ys2) p q r l L1 L2); intros.
      apply H13; try easy. pfold. easy. pfold. easy. pfold. easy. constructor.
    - subst.
      specialize(wfgC_after_step_all H25 Ht); intros.
      exists (ltt_recv s ys3). split; try easy.
      pfold. constructor; try easy.
      apply triv_pt_q; try easy. 
      specialize(H10 r H30 H31).
      specialize(typ_after_step_3_helper_h5 ys ys2 ys3 p q l r); intros. apply H12; try easy.
    - subst.
      specialize(wfgC_after_step_all H25 Ht); intros.
      exists (ltt_send s' ys3). split; try easy.
      pfold. constructor; try easy.
      apply triv_pt_p; try easy. 
      specialize(H10 r H28 H29).
      specialize(typ_after_step_3_helper_h5 ys ys2 ys3 p q l r); intros. apply H12; try easy.
    - subst. exists T.
      split; try easy. 
      specialize(decidable_isgPartsC (gtt_send s s' ys2) r Htt); intros.
      unfold Decidable.decidable in H11. unfold not in H11.
      destruct H11.
      - pfold. apply proj_cont with (ys := ys3); try easy.
        specialize(H10 r).
        assert(Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s' : sort) (g g' : gtt),
            u = Some (s', g) /\
            v = Some (s', g') /\
            gttstepC g g' p q l /\
            (forall T : ltt, projectionC g r T -> exists T' : ltt, projectionC g' r T' /\ T = T'))) ys ys2). apply H10; try easy. clear H10.
        specialize(typ_after_step_3_helper_h6 ys ys2 ys3 p q l r); intros. apply H10; try easy.
      - specialize(part_after_step_r (gtt_send s s' ys) r p q (gtt_send s s' ys2) l T); intros.
        assert(isgPartsC r (gtt_send s s' ys2)). apply H12; try easy. pfold. easy. pfold. easy.
        specialize(H11 H13). easy.
      apply proj_mon. apply step_mon. apply proj_mon. apply proj_mon.
Qed.

Lemma proj_cont_pq_step : forall G G' p q l,
    wfgC G -> 
    gttstepC G G' p q l -> 
    projectableA G ->
    exists LP LQ S S' T T',
    projectionC G p (ltt_send q LP) /\ 
    projectionC G q (ltt_recv p LQ) /\
    onth l LP = Some(S, T) /\ onth l LQ = Some(S', T').
Proof.
  intros.
  specialize(wfgC_step_part G G' p q l H H0); intros.
  specialize(balanced_to_tree G p H H2); intros. clear H2.
  destruct H3 as (Gl,(ct,(Ha,(Hb,(Hc,Hd))))). clear Hd.
  revert H H0 H1 Ha Hb Hc. revert G G' p q l ct.
  induction Gl using gtth_ind_ref; intros.
  - inversion Ha. subst.
    specialize(some_onth_implies_In n ct G H4); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : list (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ct); intros.
    destruct H3. specialize(H3 Hc). clear Hc H5.
    specialize(H3 (Some G) H2). destruct H3; try easy.
    destruct H3 as (q1,(lsg,Hc)). clear H2.
    - destruct Hc. inversion H2. subst.  
      pinversion H0; try easy. subst.
      unfold projectableA in H1. pose proof H1 as Ht.
      specialize(H1 p). destruct H1. pinversion H1; try easy. subst.
      assert False. apply H3. apply triv_pt_p; try easy. easy.
      subst. specialize(Ht q). destruct Ht. pinversion H3; try easy. 
      subst. assert False. apply H5. apply triv_pt_q; try easy. easy. subst.
      exists ys. exists ys0.
      assert(exists (S S' : sort) (T T' : ltt),
        onth l ys = Some (S, T) /\ onth l ys0 = Some (S', T')).
      {
        clear H16 H18 H15 H9 H13 H7 H3 H8 H11 H4 Hb H2 Ha H1 H0 H.
        revert H19 H14 H12.
        revert G' p q lsg ys s ys0. clear n ct.
        induction l; intros.
        - destruct lsg; try easy. 
          destruct ys; try easy. destruct ys0; try easy.
          inversion H19. subst. clear H19. inversion H14. subst. clear H14.
          simpl in H12. subst.
          destruct H2; try easy. destruct H as (s1,(g1,(t1,(Ha,(Hb,Hc))))). inversion Ha. subst.
          destruct H3; try easy. destruct H as (s2,(g2,(t2,(Hd,(He,Hf))))). inversion Hd. subst.
          simpl. exists s2. exists s2. exists t2. exists t1. easy.
        - destruct lsg; try easy. 
          destruct ys; try easy. destruct ys0; try easy.
          inversion H19. subst. clear H19. inversion H14. subst. clear H14.
          specialize(IHl G' p q lsg ys s ys0). apply IHl; try easy.
      }
      destruct H5 as (s1,(s2,(t1,(t2,(Hl,Hk))))). exists s1. exists s2. exists t1. exists t2. 
      split. pfold. easy. split. pfold. easy. easy.
    apply proj_mon. apply proj_mon. apply step_mon.
    - destruct H2. inversion H2. subst. pinversion H0; try easy. apply step_mon.
    - inversion H2. subst. pinversion H0; try easy. apply step_mon.
  - inversion Ha. subst.
    clear Ha. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    specialize(proj_forward s s' ys H0 H2); intros. 
    pinversion H1; try easy. subst. assert False. apply Hb. constructor. easy.
    subst.
    specialize(wfgC_after_step_all H10 H0); intros. rename H1 into Htt.
    clear H19.
    unfold projectableA in H2. pose proof H2 as Ht.
    specialize(H2 p). destruct H2 as (T,H2). specialize(Ht q). destruct Ht as (T',Ht).
    specialize(slist_implies_some xs H8); intros.
    destruct H1 as (n,(gl,H1)). destruct gl.
    specialize(Forall2_prop_r n xs ys (s0, g) (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : gtth) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ct g g')) H1 H9); intros.
    destruct H5 as (p1,(Hd,He)). destruct He; try easy.
    destruct H5 as (s1,(g1,(g2,(Hf,(Hg,Hh))))). inversion Hf. subst. clear Hf.
    specialize(Forall_prop n ys (s1, g2) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) Hg H4); intros.
    destruct H5; try easy. destruct H5 as (s2,(g3,(Hi,Hj))). inversion Hi. subst. clear Hi.
    clear H9 H4 H8.
    specialize(Forall2_prop_r n ys ys0 (s2, g3) (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q l)) Hg H20); intros.
    destruct H4 as (p1,(Hi,Hk)). destruct Hk; try easy. destruct H4 as (s3,(g4,(g5,(Hl,(Hm,Hn))))).
    inversion Hl. subst. clear Hl H20.
    specialize(Forall_prop n ys (s3, g4) (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ projectableA g)) Hg H3); intros.
    destruct H4; try easy. destruct H4 as (s4,(g6,(Ho,Hp))). inversion Ho. subst. clear H3.
    specialize(some_onth_implies_In n xs (s4, g1) H1); intros.
    specialize(Forall_forall (fun u : option (sort * gtth) =>
       u = None \/
       (exists (s : sort) (g : gtth),
          u = Some (s, g) /\
          (forall (G G' : gtt) (p q : string) (l : fin) (ct : list (option gtt)),
           wfgC G ->
           gttstepC G G' p q l ->
           projectableA G ->
           typ_gtth ct g G ->
           (ishParts p g -> False) ->
           Forall
             (fun u0 : option gtt =>
              u0 = None \/
              (exists (q0 : string) (lsg : list (option (sort * gtt))),
                 u0 = Some (gtt_send p q0 lsg) \/ u0 = Some (gtt_send q0 p lsg) \/ u0 = Some gtt_end))
             ct ->
           exists (LP LQ : list (option (sort * ltt))) (S S' : sort) (T T' : ltt),
             projectionC G p (ltt_send q LP) /\
             projectionC G q (ltt_recv p LQ) /\ onth l LP = Some (S, T) /\ onth l LQ = Some (S', T')))) xs); intros. 
    destruct H4. specialize(H4 H). clear H H5.
    specialize(H4 (Some (s4, g1)) H3). destruct H4; try easy.
    destruct H as (s5,(g7,(Hq,Hr))). inversion Hq. subst.
    clear H3.
    specialize(Hr g6 g5 p q l ct).
    assert(exists (LP LQ : list (option (sort * ltt))) (S S' : sort) (T T' : ltt),
       projectionC g6 p (ltt_send q LP) /\
       projectionC g6 q (ltt_recv p LQ) /\ onth l LP = Some (S, T) /\ onth l LQ = Some (S', T')).
    {
      apply Hr; try easy.
      destruct Hn; try easy.
      specialize(ishParts_n Hb H1); intros. apply H; try easy.
    }
    clear Hr. 
    clear Hp Hn Hm Hj Hh Ho H1 Hq. clear g7 g5.
    destruct H as (lp,(lq,(s1,(s2,(t1,(t2,(Hta,(Htb,(Htc,Htd))))))))).
    clear Htt.
    assert(isgPartsC p g6). 
    {
      pinversion Hta; try easy.
      apply proj_mon.
    }
    assert(isgPartsC q g6).
    {
      pinversion Htb; try easy.
      apply proj_mon.
    }
    specialize(part_cont_b n ys s5 g6 p s s' Hg); intros.
    assert(isgPartsC p (gtt_send s s' ys)). apply H3; try easy.
    specialize(part_cont_b n ys s5 g6 q s s' Hg); intros.
    assert(isgPartsC q (gtt_send s s' ys)). apply H5; try easy.
    clear H3 H5.
    pinversion Ht; try easy. subst. pinversion H2; try easy. subst.
    clear H23 H22 H19 H18 H17 H16 H15 H6 H4 H1 H H14 H13 H12 H11 H10 H7 Hc Hb.
    specialize(Forall2_prop_r n ys ys1 (s5, g6) (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) Hg H20); intros.
    destruct H as (p1,(Ha,Hb)). destruct Hb; try easy. destruct H as (s3,(g1,(t3,(Hb,(Hc,Hd))))).
    inversion Hb. subst. clear Hb.
    specialize(Forall2_prop_r n ys ys2 (s3, g1) (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) Hg H26); intros.
    destruct H as (p2,(He,Hf)). destruct Hf; try easy. destruct H as (s4,(g2,(t4,(Hj,(Hh,Hi))))).
    inversion Hj. subst.
    pclearbot.
    specialize(wfgC_after_step_all H9 H0); intros.
    specialize(Forall_prop n ys (s4, g2) (fun u : option (sort * gtt) =>
       u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgC g)) Hg H); intros.
    destruct H1; try easy. destruct H1 as (s5,(g3,(Hk,Hl))). inversion Hk. subst.
    specialize(proj_inj Hl Hi Hta); intros. subst.
    specialize(proj_inj Hl Hd Htb); intros. subst.
    clear H H26 H20 Hi Hd.
    specialize(merge_send_T n T ys2 q lp H27 Hh); intros. destruct H as (lp',H). subst.
    specialize(merge_recv_T n T' ys1 p lq H21 Hc); intros. destruct H as (lq',H). subst.
    exists lp'. exists lq'. 
    specialize(merge_label_recv ys1 lq' lq (s2, t2) n l p H21 Hc Htd); intros. destruct H as (ta,H). 
    specialize(merge_label_send ys2 lp' lp (s1, t1) n l q H27 Hh Htc); intros. destruct H1 as (tb,H1).
    destruct ta. destruct tb.
    exists s3. exists s0. exists l1. exists l0.
    split. pfold. easy. split. pfold. easy. easy.
  apply proj_mon.
  apply proj_mon.
  apply step_mon.
Qed.

Lemma proj_cont_pq_step_full : forall G G' p q l,
    wfgC G -> 
    gttstepC G G' p q l -> 
    projectableA G ->
    exists (T T' : ltt), projectionC G' p T /\ projectionC G' q T'.
Proof.
  intros.
  specialize(proj_cont_pq_step G G' p q l H H0 H1); intros.
  destruct H2 as (l1,(l2,(s1,(s2,(t1,(t2,(Ha,(Hb,(Hc,Hd))))))))).
  specialize(typ_after_step_1_helper p q l G G' l1 l2 s1 t1 s2 t2); intros.
  exists t1.
  specialize(typ_after_step_2_helper p q l G G' l1 l2 s1 t1 s2 t2); intros.
  exists t2.
  split. apply H2; try easy. apply H3; try easy.
Qed.

Lemma balanced_step : forall [G G' p q l],
    wfgC G -> 
    gttstepC G G' p q l -> 
    projectableA G ->
    balancedG G'.
Proof.
  intros. pose proof H as Ht.
  unfold wfgC in H. destruct H as (Gl,(Ha,(Hb,(Hc,H)))). clear Ha Hb Hc. clear Gl.
  specialize(wfgC_step_part G G' p q l Ht H0); intros.
  specialize(balanced_to_tree G p Ht H2); intros.
  destruct H3 as (Gl,(ct,(Ha,(Hb,(Hc,Hd))))). clear Hd H2.
  revert Hc Hb Ha Ht H1 H0. clear H.
  revert G G' p q l ct.
  induction Gl using gtth_ind_ref; intros; try easy.
  - inversion Ha. subst.
    specialize(some_onth_implies_In n ct G H3); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : list (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ct); intros.
    destruct H2. specialize(H2 Hc). clear H4 Hc.
    specialize(H2 (Some G) H). destruct H2; try easy.
    destruct H2 as (q1,(lsg,Hc)).
    - destruct Hc. inversion H2. subst.
      pinversion H0; try easy. subst.
      unfold wfgC in Ht. destruct Ht as (G1,(Hta,(Htb,(Htc,Htd)))).
      specialize(balanced_cont Htd); intros.
      specialize(some_onth_implies_In l lsg (s, G') (esym H12)); intros.
      specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) lsg); intros. 
      destruct H6. specialize(H6 H4). clear H4 H7.
      specialize(H6 (Some (s, G')) H5). destruct H6; try easy.
      destruct H4 as (s1,(g1,(Hsa,Hsb))). inversion Hsa. subst. easy.
      apply step_mon.
    - destruct H2. inversion H2. subst. pinversion H0; try easy.
      apply step_mon.
    - inversion H2. subst. pinversion H0; try easy.
      apply step_mon.
  - inversion Ha. subst. 
    pinversion H0; try easy.
    - subst. assert False. apply Hb. constructor. easy.
    subst. rename p into s. rename q into s'. rename p0 into p. rename q0 into q.
    assert(Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ balancedG g)) ys0).
    {
      clear Ha H7. 
      specialize(wfgC_after_step_all H6 Ht); intros.
      specialize(proj_forward s s' ys Ht H1); intros. clear H1.
      clear H5 H6 H9 H10 H11 H12 Ht H0 H17.
      revert H3 H2 H18 H8 Hc H Hb. revert s s' xs p q l ct ys.
      induction ys0; intros; try easy.
      destruct ys; try easy. destruct xs; try easy.
      inversion H3. subst. clear H3. inversion H2. subst. clear H2.
      inversion H18. subst. clear H18. 
      inversion H8. subst. clear H8. inversion H. subst. clear H.
      specialize(IHys0 s s' xs p q l ct ys).
      assert(Forall
          (fun u : option (sort * gtt) =>
           u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) ys0).
      {
        apply IHys0; try easy.
        specialize(ishParts_hxs Hb); try easy.
      }
      constructor; try easy.
      clear H H8 H12 H10 H6 H5 IHys0.
      destruct H7. left. easy.
      destruct H as (s1,(g1,(g2,(Hd,(He,Hf))))). subst.
      destruct H3; try easy. destruct H as (s2,(g3,(Hg,Hh))). inversion Hg. subst.
      destruct H4; try easy. destruct H as (s3,(g4,(Hi,Hj))). inversion Hi. subst.
      destruct H9; try easy. destruct H as (s4,(g5,(g6,(Hk,(Hl,Hm))))). inversion Hl. subst.
      destruct H2; try easy. destruct H as (s5,(g7,(Hn,Ho))). inversion Hn. subst.
      right. exists s5. exists g2. split. easy.
      clear Hn Hl Hg Hi. destruct Hf; try easy. 
      specialize(Ho g6 g2 p q l ct). apply Ho; try easy.
      specialize(ishParts_x Hb); try easy.
    }
    clear H18 H17 H8 H7 H.
    unfold balancedG.
    intros.
    destruct w.
    - simpl.
      {
        simpl in *. 
        assert(exists Gl, Gl = (gtth_send s s' xs)). exists (gtth_send s s' xs). easy.
        destruct H4 as (Gl,H4). replace (gtth_send s s' xs) with Gl in *.
        assert(exists G, G = (gtt_send s s' ys)). exists (gtt_send s s' ys). easy.
        destruct H7 as (G,H7). replace (gtt_send s s' ys) with G in *.
        assert(exists G', G' = (gtt_send s s' ys0)). exists (gtt_send s s' ys0). easy.
        - case_eq (eqb p0 p); intros.
          assert (p0 = p). apply eqb_eq; try easy. subst. 
          {
            clear H4 Hc Hb Ha. 
            clear H8 H7 H13.
            assert(gttstepC G (gtt_send s s' ys0) p q l). pfold. easy. clear H0.
            specialize(proj_cont_pq_step_full G (gtt_send s s' ys0) p q l Ht H4 H1); intros.
            destruct H0 as (T,(T1,(Ha,Hb))). clear Hb. clear T1.
            
            specialize(wfgCw_after_step G (gtt_send s s' ys0) p q l Ht H4); intros. 
            
            assert(isgPartsC p (gtt_send s s' ys0)).
            {
              apply word_to_parts with (w' := w') (q0 := q0); try easy.
            }
            assert(Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ isgPartsC p g)) ys0).
            {
              apply Forall_forall; intros.
              destruct x.
              - right. destruct p0. exists s0. exists g. split. easy.
                pinversion Ha; try easy. subst.
                specialize(in_some_implies_onth (s0, g) ys0 H8); intros.
                destruct H13 as (n, H13).
                specialize(Forall2_prop_r n ys0 ys1 (s0, g) (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g p t)) H13 H22); intros.
                destruct H14 as (p1,(Hta,Htb)). destruct Htb; try easy.
                destruct H14 as (s1,(g1,(t1,(Htb,(Htc,Htd))))). inversion Htb. subst.
                destruct Htd; try easy.
                pinversion H14; try easy. subst.
                specialize(merge_end_back n ys1 T Htc H23); intros. subst.
                specialize(pmergeCR_s (gtt_send s s' ys0) p); intros.
                assert False. apply H20; try easy.
                pfold. easy. easy.
                apply proj_mon. apply proj_mon.
              - left. easy.
            }
            unfold balancedG in H2.
            assert((Forall (fun u : option (sort * gtt) =>
              u = None \/
              (exists (s : sort) (g : gtt),
                 u = Some (s, g) /\
                  exists k : fin,
                    forall w'0 : list fin,
                    gttmap g w'0 None gnode_end \/
                    length w'0 = k /\ (exists tc : gnode, gttmap g w'0 None tc) ->
                    exists w2 w0 : list fin,
                      w'0 = w2 ++ w0 /\
                      (exists r : string,
                         gttmap g w2 None (gnode_pq p r) \/
                         gttmap g w2 None (gnode_pq r p))))) ys0).
            {
              apply Forall_forall; intros.
              specialize(Forall_forall  (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall (w w' : list fin) (p q : string) (gn : gnode),
            gttmap g w None gn ->
            gttmap g (seq.cat w w') None (gnode_pq p q) \/ gttmap g (seq.cat w w') None (gnode_pq q p) ->
            exists k : fin,
              forall w'0 : list fin,
              gttmap g (seq.cat w w'0) None gnode_end \/
              length w'0 = k /\ (exists tc : gnode, gttmap g (seq.cat w w'0) None tc) ->
              exists w2 w0 : list fin,
                w'0 = w2 ++ w0 /\
                (exists r : string,
                   gttmap g (seq.cat w w2) None (gnode_pq p r) \/
                   gttmap g (seq.cat w w2) None (gnode_pq r p))))) ys0); intros.
              destruct H14. specialize(H14 H2). clear H15 H2.
              specialize(H14 x H13).
              specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ isgPartsC p g)) ys0); intros.
              destruct H2. specialize(H2 H8). clear H8 H15.
              specialize(H2 x H13).
              destruct H2. left. easy.
              destruct H2 as (s1,(g1,(Hb,Hc))). subst.
              destruct H14; try easy.
              destruct H2 as (s2,(g2,(Hd,He))). inversion Hd. subst.
              clear H13 Hd.
              right. exists s2. exists g2. split. easy.
              specialize(parts_to_word p g2 Hc); intros.
              destruct H2 as (w1,(r,Hd)).
              specialize(He nil w1 p r).
              specialize(nil_word g2); intros. destruct H2 as (tc,H2).
              specialize(He tc). apply He; try easy. simpl.
              destruct Hd. right. easy. left. easy.
            }
            clear H8 H7 Ha H4 H2.
            assert(exists K, 
                Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt),
            u = Some (s, g) /\
            (exists k : fin, k <= K /\
               forall w'0 : list fin,
               gttmap g w'0 None gnode_end \/
               length w'0 = k /\ (exists tc : gnode, gttmap g w'0 None tc) ->
               exists w2 w0 : list fin,
                 w'0 = w2 ++ w0 /\
                 (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p)))))
        ys0).
            {
              clear H0 H3 H H12 H11 H10 H9 H6 H5 H1 Ht.
              revert H13. revert p. clear s s' xs q l ct Gl ys G w' q0 gn T.
              induction ys0; intros; try easy.
              exists 0. constructor.
              inversion H13. subst. clear H13. specialize(IHys0 p H2).
              destruct IHys0 as (K, Ha). clear H2.
              destruct H1.
              - subst. exists K. constructor; try easy. left. easy.
              - destruct H as (s1,(g1,(Hb,(k,Hc)))). subst.
                exists (Nat.max k K).
                constructor; try easy.
                - right. exists s1. exists g1. split. easy.
                  exists k. split; try easy.
                  apply max_l.
                - revert Ha. clear Hc. clear g1 s1.
                  apply Forall_mono; intros.
                  destruct H. left. easy.
                  destruct H as (s1,(g1,(Ha,(k1,(Hb,Hc))))).
                  right. subst. exists s1. exists g1.
                  split. easy. exists k1. split; try easy.
                  apply leq_trans with (n := K); try easy.
                  apply max_r.
            }
            destruct H2 as (K, H2). clear H13.
            assert(Forall
             (fun u : option (sort * gtt) =>
              u = None \/
              (exists (s : sort) (g : gtt),
                 u = Some (s, g) /\
                    (forall w'0 : list fin,
                     gttmap g w'0 None gnode_end \/
                     length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
                     exists w2 w0 : list fin,
                       w'0 = w2 ++ w0 /\
                       (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p))))) ys0).
            {
              revert H2. apply Forall_mono; intros.
              destruct H2. left. easy.
              destruct H2 as (s1,(g1,(Ha,(k,(Hb,Hc))))).
              subst. right. exists s1. exists g1. split. easy.
              apply cut_further with (k := k); try easy.
            }
            clear H2.
            exists (S K).
            intros. clear H H3. clear gn w' ct Gl. clear ys xs H1 Ht.
            destruct H2.
            - inversion H. subst.
              specialize(Forall_prop n ys0 (st, gk) (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall w'0 : list fin,
            gttmap g w'0 None gnode_end \/ length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
            exists w2 w0 : list fin,
              w'0 = w2 ++ w0 /\
              (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p))))) H14 H4); intros.
               destruct H1; try easy. destruct H1 as (s1,(g1,(Ha,Hb))). inversion Ha. subst.
               specialize(Hb lis).
               assert(gttmap g1 lis None gnode_end \/ length lis = K /\ (exists tc : gnode, gttmap g1 lis None tc)). left. easy.
               specialize(Hb H1). clear H1.
               destruct Hb as (w2,(w0,(Hc,(r,Hd)))). subst.
               exists (n :: w2). exists w0. split. constructor.
               exists r.
               destruct Hd.
               - left. apply gmap_con with (st := s1) (gk := g1); try easy.
               - right. apply gmap_con with (st := s1) (gk := g1); try easy.
            - destruct H as (H,(tc,Ha)).
              inversion Ha; try easy. subst. easy.
              subst.
              specialize(Forall_prop n ys0 (st, gk) (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall w'0 : list fin,
            gttmap g w'0 None gnode_end \/ length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
            exists w2 w0 : list fin,
              w'0 = w2 ++ w0 /\
              (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p))))) H14 H4); intros.
              destruct H1; try easy. destruct H1 as (s1,(g1,(Hb,Hc))). inversion Hb. subst.
              specialize(Hc lis).
              assert(gttmap g1 lis None gnode_end \/ length lis = K /\ (exists tc : gnode, gttmap g1 lis None tc)). right. split. apply eq_add_S. easy. exists tc. easy.
              specialize(Hc H1). clear H1.
              destruct Hc as (w2,(w0,(Hc,(r,Hd)))). subst.
              exists (n :: w2). exists w0. split. constructor. exists r.
              destruct Hd.
               - left. apply gmap_con with (st := s1) (gk := g1); try easy.
               - right. apply gmap_con with (st := s1) (gk := g1); try easy.
          }
        - case_eq (eqb p0 q); intros.
          assert (p0 = q). apply eqb_eq; try easy. subst. 
          {
            simpl in *. 
            clear H4 Hc Hb Ha. 
            clear H8 H7 H13 H14.
            assert(gttstepC G (gtt_send s s' ys0) p q l). pfold. easy. clear H0.
            specialize(proj_cont_pq_step_full G (gtt_send s s' ys0) p q l Ht H4 H1); intros.
            destruct H0 as (T1,(T,(Hb,Ha))). clear Hb. clear T1.
            
            specialize(wfgCw_after_step G (gtt_send s s' ys0) p q l Ht H4); intros. 
            
            assert(isgPartsC q (gtt_send s s' ys0)).
            {
              apply word_to_parts with (w' := w') (q0 := q0); try easy.
            }
            assert(Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ isgPartsC q g)) ys0).
            {
              apply Forall_forall; intros.
              destruct x.
              - right. destruct p0. exists s0. exists g. split. easy.
                pinversion Ha; try easy. subst.
                specialize(in_some_implies_onth (s0, g) ys0 H8); intros.
                destruct H13 as (n, H13).
                specialize(Forall2_prop_r n ys0 ys1 (s0, g) (fun (u : option (sort * gtt)) (v : option ltt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g : gtt) (t : ltt),
            u = Some (s, g) /\ v = Some t /\ upaco3 projection bot3 g q t)) H13 H22); intros.
                destruct H14 as (p1,(Hta,Htb)). destruct Htb; try easy.
                destruct H14 as (s1,(g1,(t1,(Htb,(Htc,Htd))))). inversion Htb. subst.
                destruct Htd; try easy.
                pinversion H14; try easy. subst.
                specialize(merge_end_back n ys1 T Htc H23); intros. subst.
                specialize(pmergeCR_s (gtt_send s s' ys0) q); intros.
                assert False. apply H20; try easy.
                pfold. easy. easy.
                apply proj_mon. apply proj_mon.
              - left. easy.
            }
            unfold balancedG in H2.
            assert((Forall (fun u : option (sort * gtt) =>
              u = None \/
              (exists (s : sort) (g : gtt),
                 u = Some (s, g) /\
                  exists k : fin,
                    forall w'0 : list fin,
                    gttmap g w'0 None gnode_end \/
                    length w'0 = k /\ (exists tc : gnode, gttmap g w'0 None tc) ->
                    exists w2 w0 : list fin,
                      w'0 = w2 ++ w0 /\
                      (exists r : string,
                         gttmap g w2 None (gnode_pq q r) \/
                         gttmap g w2 None (gnode_pq r q))))) ys0).
            {
              apply Forall_forall; intros.
              specialize(Forall_forall  (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall (w w' : list fin) (p q : string) (gn : gnode),
            gttmap g w None gn ->
            gttmap g (seq.cat w w') None (gnode_pq p q) \/ gttmap g (seq.cat w w') None (gnode_pq q p) ->
            exists k : fin,
              forall w'0 : list fin,
              gttmap g (seq.cat w w'0) None gnode_end \/
              length w'0 = k /\ (exists tc : gnode, gttmap g (seq.cat w w'0) None tc) ->
              exists w2 w0 : list fin,
                w'0 = w2 ++ w0 /\
                (exists r : string,
                   gttmap g (seq.cat w w2) None (gnode_pq p r) \/
                   gttmap g (seq.cat w w2) None (gnode_pq r p))))) ys0); intros.
              destruct H14. specialize(H14 H2). clear H15 H2.
              specialize(H14 x H13).
              specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ isgPartsC q g)) ys0); intros.
              destruct H2. specialize(H2 H8). clear H8 H15.
              specialize(H2 x H13).
              destruct H2. left. easy.
              destruct H2 as (s1,(g1,(Hb,Hc))). subst.
              destruct H14; try easy.
              destruct H2 as (s2,(g2,(Hd,He))). inversion Hd. subst.
              clear H13 Hd.
              right. exists s2. exists g2. split. easy.
              specialize(parts_to_word q g2 Hc); intros.
              destruct H2 as (w1,(r,Hd)).
              specialize(He nil w1 q r).
              specialize(nil_word g2); intros. destruct H2 as (tc,H2).
              specialize(He tc). apply He; try easy. simpl.
              destruct Hd. right. easy. left. easy.
            }
            clear H8 H7 Ha H4 H2.
            assert(exists K, 
                Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt),
            u = Some (s, g) /\
            (exists k : fin, k <= K /\
               forall w'0 : list fin,
               gttmap g w'0 None gnode_end \/
               length w'0 = k /\ (exists tc : gnode, gttmap g w'0 None tc) ->
               exists w2 w0 : list fin,
                 w'0 = w2 ++ w0 /\
                 (exists r : string, gttmap g w2 None (gnode_pq q r) \/ gttmap g w2 None (gnode_pq r q)))))
        ys0).
            {
              clear H0 H3 H H12 H11 H10 H9 H6 H5 H1 Ht.
              revert H13. revert q. clear s s' xs p l ct Gl ys G w' q0 gn T.
              induction ys0; intros; try easy.
              exists 0. constructor.
              inversion H13. subst. clear H13. specialize(IHys0 q H2).
              destruct IHys0 as (K, Ha). clear H2.
              destruct H1.
              - subst. exists K. constructor; try easy. left. easy.
              - destruct H as (s1,(g1,(Hb,(k,Hc)))). subst.
                exists (Nat.max k K).
                constructor; try easy.
                - right. exists s1. exists g1. split. easy.
                  exists k. split; try easy.
                  apply max_l.
                - revert Ha. clear Hc. clear g1 s1.
                  apply Forall_mono; intros.
                  destruct H. left. easy.
                  destruct H as (s1,(g1,(Ha,(k1,(Hb,Hc))))).
                  right. subst. exists s1. exists g1.
                  split. easy. exists k1. split; try easy.
                  apply leq_trans with (n := K); try easy.
                  apply max_r.
            }
            destruct H2 as (K, H2). clear H13.
            assert(Forall
             (fun u : option (sort * gtt) =>
              u = None \/
              (exists (s : sort) (g : gtt),
                 u = Some (s, g) /\
                    (forall w'0 : list fin,
                     gttmap g w'0 None gnode_end \/
                     length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
                     exists w2 w0 : list fin,
                       w'0 = w2 ++ w0 /\
                       (exists r : string, gttmap g w2 None (gnode_pq q r) \/ gttmap g w2 None (gnode_pq r q))))) ys0).
            {
              revert H2. apply Forall_mono; intros.
              destruct H2. left. easy.
              destruct H2 as (s1,(g1,(Ha,(k,(Hb,Hc))))).
              subst. right. exists s1. exists g1. split. easy.
              apply cut_further with (k := k); try easy.
            }
            clear H2.
            exists (S K).
            intros. clear H H3. clear gn w' ct Gl. clear ys xs H1 Ht.
            destruct H2.
            - inversion H. subst.
              specialize(Forall_prop n ys0 (st, gk) (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall w'0 : list fin,
            gttmap g w'0 None gnode_end \/ length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
            exists w2 w0 : list fin,
              w'0 = w2 ++ w0 /\
              (exists r : string, gttmap g w2 None (gnode_pq q r) \/ gttmap g w2 None (gnode_pq r q))))) H14 H4); intros.
               destruct H1; try easy. destruct H1 as (s1,(g1,(Ha,Hb))). inversion Ha. subst.
               specialize(Hb lis).
               assert(gttmap g1 lis None gnode_end \/ length lis = K /\ (exists tc : gnode, gttmap g1 lis None tc)). left. easy.
               specialize(Hb H1). clear H1.
               destruct Hb as (w2,(w0,(Hc,(r,Hd)))). subst.
               exists (n :: w2). exists w0. split. constructor.
               exists r.
               destruct Hd.
               - left. apply gmap_con with (st := s1) (gk := g1); try easy.
               - right. apply gmap_con with (st := s1) (gk := g1); try easy.
            - destruct H as (H,(tc,Ha)).
              inversion Ha; try easy. subst. easy.
              subst.
              specialize(Forall_prop n ys0 (st, gk) (fun u : option (sort * gtt) =>
        u = None \/
        (exists (s : sort) (g : gtt),
           u = Some (s, g) /\
           (forall w'0 : list fin,
            gttmap g w'0 None gnode_end \/ length w'0 = K /\ (exists tc : gnode, gttmap g w'0 None tc) ->
            exists w2 w0 : list fin,
              w'0 = w2 ++ w0 /\
              (exists r : string, gttmap g w2 None (gnode_pq q r) \/ gttmap g w2 None (gnode_pq r q))))) H14 H4); intros.
              destruct H1; try easy. destruct H1 as (s1,(g1,(Hb,Hc))). inversion Hb. subst.
              specialize(Hc lis).
              assert(gttmap g1 lis None gnode_end \/ length lis = K /\ (exists tc : gnode, gttmap g1 lis None tc)). right. split. apply eq_add_S. easy. exists tc. easy.
              specialize(Hc H1). clear H1.
              destruct Hc as (w2,(w0,(Hc,(r,Hd)))). subst.
              exists (n :: w2). exists w0. split. constructor. exists r.
              destruct Hd.
               - left. apply gmap_con with (st := s1) (gk := g1); try easy.
               - right. apply gmap_con with (st := s1) (gk := g1); try easy.
          }
        - destruct H8 as (G',H8). replace (gtt_send s s' ys0) with G' in *. clear H4 H7 H8.
          assert (p0 <> p). apply eqb_neq; try easy. 
          assert (p0 <> q). apply eqb_neq; try easy.
          {
            pose proof Ht as Htt.
            unfold wfgC in Htt. destruct Htt as (G1,(Hf,(Hg,(Hd,He)))). clear Hf Hg Hd. clear G1.
            clear H13 H14 H H12 H11 H10 H9 H6 H5 Ht.
            assert(gttstepC G G' p q l). pfold. easy. clear H0 H1 H2. clear s s' xs ys ys0.
            unfold balancedG in He. specialize(He nil). simpl in He.
            
            assert(exists k : fin,
       forall w'0 : list fin,
       gttmap G w'0 None gnode_end \/ length w'0 = k /\ (exists tc : gnode, gttmap G w'0 None tc) ->
       exists w2 w0 : list fin,
         w'0 = w2 ++ w0 /\
         (exists r : string, gttmap G w2 None (gnode_pq p0 r) \/ gttmap G w2 None (gnode_pq r p0))).
            {
              specialize(nil_word G); intros.
              destruct H0 as (tc1,H0).
              destruct H3.
              - specialize(word_step_back_s H H1); intros.
                destruct H2. specialize(He w' p0 q0 tc1). apply He; try easy.
                left. easy.
              - destruct H2 as (w0,(w1,(Hd,Hf))). specialize(He (w0 ++ l :: w1) p0 q0 tc1).
                apply He; try easy.
                left. easy.
              - specialize(word_step_back_s H H1); intros.
                destruct H2. specialize(He w' p0 q0 tc1). apply He; try easy.
                right. easy.
              - destruct H2 as (w0,(w1,(Hd,Hf))). specialize(He (w0 ++ l :: w1) p0 q0 tc1).
                apply He; try easy.
                right. easy.
            }
            clear He H3.
            
            destruct H0 as (k, H0). exists k.
            intros.
            destruct H1.
            - specialize(word_step_back_ss H H1); intros.
              destruct H2.
              - specialize(H0 w'0).
                assert(gttmap G w'0 None gnode_end \/ length w'0 = k /\ (exists tc : gnode, gttmap G w'0 None tc)).
                {
                  left. specialize(H2 w'0 nil gnode_end). apply H2; try easy.
                  apply esym.
                  apply app_nil_r.
                }
                specialize(H0 H3). clear H3.
                destruct H0 as (w2,(w0,(Hta,(r,Htb)))).
                exists w2. exists w0. split. easy. exists r.
                destruct Htb.
                - specialize(H2 w2 w0 (gnode_pq p0 r)). left. apply H2; try easy.
                - specialize(H2 w2 w0 (gnode_pq r p0)). right. apply H2; try easy.
              - destruct H2 as (w0,(w1,(Hd,(He,(Hf,Hg))))). subst.
                pose proof Hf as Ht.
                specialize(Hf w1 nil gnode_end).
                assert(gttmap G (w0 ++ l :: w1) None gnode_end). apply Hf; try easy.
                apply esym. apply app_nil_r.
                specialize(H0 (w0 ++ l :: w1)).
                assert(gttmap G (w0 ++ l :: w1) None gnode_end \/
     length (w0 ++ l :: w1) = k /\ (exists tc : gnode, gttmap G (w0 ++ l :: w1) None tc)). left. easy.
                specialize(H0 H3). clear H3.
                destruct H0 as (w2,(w3,(Hh,(r,Hi)))).
                clear Hc Hb Ha H H1 H2 Hf.
                specialize(decon_word w2 l w0 w1 w3 Hh); intros.
                - destruct H.
                  subst. destruct Hi.
                  specialize(inj_gttmap Hg H); intros. inversion H0. subst. easy.
                  specialize(inj_gttmap Hg H); intros. inversion H0. subst. easy.
                - destruct H.
                  destruct H as (wi,(wj,Hta)). subst.
                  specialize(He w2 wi wj). exists w2. exists (wi ++ wj :: w1).
                  split.
                  apply stword.
                  exists r. destruct Hi.
                  specialize(He (gnode_pq p0 r)). left. apply He; try easy.
                  specialize(He (gnode_pq r p0)). right. apply He; try easy.
                - destruct H as (wi,(wj,(Hta,Htb))). subst.
                  specialize(Ht wi wj). exists (w0 ++ wi). exists wj. split. 
                  apply app_assoc. exists r.
                  destruct Hi.
                  - left. apply Ht; try easy.
                  - right. apply Ht; try easy.
          - destruct H1 as (H1,(tc,H2)).
            specialize(word_step_back_ss H H2); intros.
            clear Hc Hb Ha H. clear Gl ct. clear w' gn.
            destruct H3.
            - assert(gttmap G w'0 None gnode_end \/
     length w'0 = k /\ (exists tc : gnode, gttmap G w'0 None tc)).
              {
                right. split. easy. exists tc.
                specialize(H w'0 nil). apply H; try easy.
                apply esym. apply app_nil_r.
              }
              specialize(H0 w'0 H3). clear H3.
              destruct H0 as (w2,(w0,(Ha,(r,Hb)))).
              subst. exists w2. exists w0. split. easy. exists r.
              specialize(H w2 w0). destruct Hb.
              - left. apply H; try easy.
              - right. apply H; try easy.
            - destruct H as (w0,(w1,(Ha,(Hb,(Hc,Hd))))).
              assert(k <= S k). easy.
              specialize(cut_further k (S k) G p0 H H0); intros. clear H H0.
              assert(gttmap G (w0 ++ l :: w1) None tc).
              {
                specialize(Hc w1 nil tc). apply Hc; try easy.
                apply esym. apply app_nil_r; try easy. subst. easy.
              }
              specialize(H3 (w0 ++ l :: w1)).
              assert(gttmap G (w0 ++ l :: w1) None gnode_end \/
               length (w0 ++ l :: w1) = S k /\
               (exists tc : gnode, gttmap G (w0 ++ l :: w1) None tc)).
              {
                right. split. subst.
                clear H H3 Hd Hc Hb H2 H7 H4. clear p q G G' p0 q0 tc.
                revert w1 l. induction w0; intros; try easy.
                simpl in *. apply eq_S. apply IHw0; try easy.
                exists tc. easy.
              }
              specialize(H3 H0). clear H0.
              destruct H3 as (w2,(w3,(He,(r,Hf)))). subst.
              specialize(decon_word w2 l w0 w1 w3 He); intros.
              - destruct H0.
                subst.
                destruct Hf. 
                - specialize(inj_gttmap H0 Hd); intros. inversion H1. subst. easy.
                - specialize(inj_gttmap H0 Hd); intros. inversion H1. subst. easy.
              - destruct H0.
                destruct H0 as (wi,(wj,Hg)). subst.
                specialize(Hb w2 wi wj). exists w2. exists (wi ++ wj :: w1). 
                split. apply stword.
                exists r.
                destruct Hf.
                - left. apply Hb; try easy.
                - right. apply Hb; try easy.
              - destruct H0 as (wi,(wj,(Hg,Hh))). subst.
                specialize(Hc wi wj).
                exists (w0 ++ wi). exists wj. split. apply app_assoc.
                exists r.
                destruct Hf.
                - left. apply Hc; try easy.
                - right. apply Hc; try easy.
            }
      }
    - inversion H. subst.
      specialize(some_onth_implies_In n ys0 (st, gk) H17); intros.
      specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) ys0); intros.
      destruct H7. specialize(H7 H2). clear H8 H2.
      specialize(H7 (Some (st, gk)) H4). destruct H7; try easy.
      destruct H2 as (s1,(g1,(Hta,Htb))). inversion Hta. subst. clear H4 Hta.
      unfold balancedG in Htb.
      specialize(Htb w w' p0 q0 gn H18).
      assert(gttmap g1 (seq.cat w w') None (gnode_pq p0 q0) \/ gttmap g1 (seq.cat w w') None (gnode_pq q0 p0)).
      {
        destruct H3. left. inversion H2; try easy. subst. specialize(eq_trans (esym H16) H17); intros.
        inversion H3. subst. easy.
        right. inversion H2; try easy. subst. specialize(eq_trans (esym H16) H17); intros.
        inversion H3. subst. easy.
      }
      specialize(Htb H2). clear H2 H3.
      destruct Htb. exists x. intros.
      specialize(H2 w'0).
      assert(gttmap g1 (seq.cat w w'0) None gnode_end \/
     length w'0 = x /\ (exists tc : gnode, gttmap g1 (seq.cat w w'0) None tc)).
      {
        destruct H3. left.
        inversion H3. subst. specialize(eq_trans (esym H19) H17); intros. inversion H4. subst.
        easy.
        destruct H3. destruct H4 as (tc, H4).
        right. split; try easy.
        exists tc. inversion H4. subst.
        specialize(eq_trans (esym H20) H17); intros. inversion H3. subst.
        easy.
      }
      specialize(H2 H4).
      destruct H2 as (w2,(w0,(Hsa,Hsb))). exists w2. exists w0.
      split. easy. destruct Hsb as (r, Hsb). exists r.
      {
        destruct Hsb.
        left. apply gmap_con with (st := s1) (gk := g1); try easy.
        right. apply gmap_con with (st := s1) (gk := g1); try easy.
      }
    apply step_mon.
Qed.

Theorem wfgC_after_step : forall G G' p q n, wfgC G -> gttstepC G G' p q n -> projectableA G -> wfgC G'. 
Proof.
  intros. rename H1 into Htt. 
  pose proof H as Ht. unfold wfgC in H.
  destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))).
  specialize(wfgC_step_part G G' p q n Ht H0); intros.
  specialize(balanced_to_tree G p Ht H); intros. clear Ht H.
  destruct H1 as (Gt,(ctxG,(Hta,(Htb,(Htc,Htd))))).
  clear Htd.
  revert Htc Htb Hta H0 Hd Hc Hb Ha Htt.
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
    assert(wfgC (gtt_send p q ys)).
    {
      unfold wfgC. exists Gl. easy.
    }
    rename H1 into Ht.
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
      specialize(proj_forward s s' ys Ht Htt); intros. clear Ht Htt. rename H12 into Ht.
      clear H14 H13 Hb Hc He H16 H11 H10 H9 H8 H5 H4 H6 Hta H0 Hd.
      apply Forall_forall; intros. 
      destruct x.
      - specialize(in_some_implies_onth p0 ys0 H0); intros. destruct H4 as (n0 ,H4). clear H0.
        right. destruct p0. exists s0. exists g. split. easy.
        
        revert H4 H3 H1 H15 H2 H17 H7 Htc H Htb Ht.
        revert g s0 lis ys ys0 ctxG n p q xs s s'.
        induction n0; intros.
        - destruct ys0; try easy. destruct ys; try easy. destruct lis; try easy.
          destruct xs; try easy.
          inversion H3. subst. clear H3. inversion H1. subst. clear H1. inversion H15. subst. clear H15.
          inversion H2. subst. clear H2. inversion H17. subst. clear H17. inversion H7. subst. clear H7.
          inversion H. subst. clear H. inversion Ht. subst. clear Ht.
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
          destruct H1; try easy. destruct H as (s8,(g11,(Hr,Hs))). inversion Hr. subst.
          specialize(Hq g11 g2 p q n g8 ctxG). unfold wfgC.
          apply Hq; try easy. 
          specialize(ishParts_x Htb); try easy.
          destruct Hc; try easy.
          destruct Hi; try easy. 
        - destruct ys0; try easy. destruct ys; try easy. destruct lis; try easy.
          destruct xs; try easy.
          inversion H3. subst. clear H3. inversion H1. subst. clear H1. inversion H15. subst. clear H15.
          inversion H2. subst. clear H2. inversion H17. subst. clear H17. inversion H7. subst. clear H7.
          inversion H. subst. clear H. inversion Ht. subst. clear Ht.
          specialize(IHn0 g s0 lis ys ys0 ctxG n p q xs s s').
          apply IHn0; try easy.
          specialize(ishParts_hxs Htb); try easy.
        left. easy.
    }
    specialize(wfgC_after_step_helper2 lis ys ys0 n p q H13 H2 H17); intros.
    assert(wfgC (gtt_send s s' ys) /\ gttstepC (gtt_send s s' ys) (gtt_send s s' ys0) p q n). 
    {
      unfold wfgC. split. exists (g_send s s' lis). split. pfold. easy. easy.
      pfold. easy.
    }
    destruct H19.
    specialize(balanced_step H19 H20 Htt); intros. clear H19 H20 Htt Ht. rename H21 into Ht.
    clear H3 H1 H15 H2 Hb Hc He H17 H16 H11 H10 H9 H8 H5 H4 H7 Hta H0 Hd Htb Htc H H6 H13.
    clear p q xs n ctxG ys lis. rename H14 into H. rename H12 into H1.
    assert(exists xs, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ gttTC g g')) xs ys0 /\ 
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ balancedG g)) ys0 /\
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfG g)) xs /\
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ (forall n, exists m, guardG n m g))) xs).
    {
      clear H. revert H1. clear H18. clear Ht. revert ys0. clear s s'.
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
    - easy.
    apply gttT_mon.
    apply step_mon.
Qed.

Inductive session: Type :=
  | s_ind : part   -> process -> session
  | s_par : session -> session -> session.
  
Notation "p '<--' P"   :=  (s_ind p P) (at level 50, no associativity).
Notation "s1 '|||' s2" :=  (s_par s1 s2) (at level 50, no associativity).

Inductive ForallT (P : part -> process -> Prop) : session -> Prop := 
  | ForallT_mono : forall pt op, P pt op -> ForallT P (pt <-- op)
  | ForallT_par : forall (M1 M2 : session), ForallT P M1 -> ForallT P M2 -> ForallT P (M1 ||| M2). 
  
Fixpoint flattenT (M : session) : (list part) := 
  match M with 
    | p <-- _   => p :: nil
    | M1 ||| M2 => flattenT M1 ++ flattenT M2
  end.

Definition InT (pt : part) (M : session) : Prop :=
  In pt (flattenT M).

Inductive unfoldP : relation session := 
  | pc_sub   : forall p P Q M, substitutionP 0 0 0 (p_rec P) P Q -> unfoldP (p <-- (p_rec P) ||| M) (p <-- Q ||| M)
  | pc_subm  : forall p P Q, substitutionP 0 0 0 (p_rec P) P Q -> unfoldP (p <-- (p_rec P)) (p <-- Q)
  | pc_refl  : forall M, unfoldP M M
  | pc_trans : forall M M' M'', unfoldP M M' -> unfoldP M' M'' -> unfoldP M M''
  | pc_par1  : forall M M', unfoldP (M ||| M') (M' ||| M)
  | pc_par2  : forall M M' M'', unfoldP ((M ||| M') ||| M'') (M ||| (M' ||| M''))
  | pc_par1m : forall M M' M'', unfoldP ((M ||| M') ||| M'') ((M' ||| M) ||| M'')
  | pc_par2m : forall M M' M'' M''', unfoldP (((M ||| M') ||| M'') ||| M''') ((M ||| (M' ||| M'')) ||| M''').

Inductive typ_sess : session -> gtt -> Prop := 
  | t_sess : forall M G, wfgC G ->
                         (forall pt, isgPartsC pt G -> InT pt M) ->
                         NoDup (flattenT M) ->
                         ForallT (fun u P => exists T, projectionC G u T /\ typ_proc nil nil P T /\ (forall n, exists m, guardP n m P)) M ->
                         typ_sess M G.

Lemma typ_after_unfold : forall M M' G, typ_sess M G -> unfoldP M M' -> typ_sess M' G.
Proof.
  intros. revert H. revert G. induction H0; intros; try easy.
  - inversion H0. subst. 
    inversion H4. subst. clear H4. inversion H7. subst. clear H7. 
    apply t_sess; try easy. constructor; try easy. constructor; try easy.
    destruct H5. exists x. split; try easy. destruct H4. split.
    destruct H5 as (H5, H6).
    - specialize(inv_proc_rec (p_rec P) P x nil nil H5 (erefl (p_rec P))); intros.
      destruct H7 as (T,(Ha,Hb)).
      specialize(subst_proc_varf P (p_rec P) T T nil nil Q Ha H); intros.
      specialize(typable_implies_wfC H5); intros.
      apply tc_sub with (t := T); try easy.
      apply H7. apply tc_mu; try easy.
      destruct H5.
      intros. specialize(H6 n). destruct H6.
      inversion H6.
      - subst. exists 0. constructor.
      - subst. 
        specialize(inj_substP H9 H); intros. subst. exists m. easy.
  - inversion H0. subst. inversion H4. subst. clear H4. 
    destruct H6 as (T,(Ha,(Hb,Hc))).
    constructor; try easy.
    constructor; try easy.
    specialize(inv_proc_rec (p_rec P) P T nil nil Hb (erefl (p_rec P))); intros.
    destruct H4 as (T0,(Hd,He)).
    specialize(subst_proc_varf P (p_rec P) T0 T0 nil nil Q); intros. exists T. split. easy.
    split. specialize(typable_implies_wfC Hb); intros.
    apply tc_sub with (t := T0); try easy. apply H4; try easy.
    apply tc_mu; try easy.
    intros. specialize(Hc n). destruct Hc. inversion H5.
    - subst. exists 0. constructor.
    - subst. specialize(inj_substP H7 H); intros. subst. exists m. easy.
  - apply IHunfoldP2. apply IHunfoldP1. easy.
  - inversion H. subst. inversion H3. subst. clear H3.
    apply t_sess; try easy.
    - intros. specialize(H1 pt H3).
      unfold InT in *.
      simpl in *. apply in_swap; try easy.
      apply nodup_swap; try easy.
    - constructor; try easy.
  - inversion H. subst. inversion H3. subst. inversion H6. subst.
    apply t_sess; try easy.
    intros. specialize(H1 pt H4).
    unfold InT in *. 
    simpl in *.
    specialize(app_assoc (flattenT M) (flattenT M') (flattenT M'')); intros.
    replace (flattenT M ++ flattenT M' ++ flattenT M'') with ((flattenT M ++ flattenT M') ++ flattenT M'') in *.
    easy.
    simpl in *.
    specialize(app_assoc (flattenT M) (flattenT M') (flattenT M'')); intros.
    replace (flattenT M ++ flattenT M' ++ flattenT M'') with ((flattenT M ++ flattenT M') ++ flattenT M'') in *.
    easy.

    constructor. easy. constructor; try easy.
  - inversion H. subst. inversion H3. subst. clear H3. inversion H6. subst. clear H6.
    constructor; try easy.
    - intros. specialize(H1 pt H3). unfold InT in *. simpl in *.
      apply in_or_app. specialize(in_or ((flattenT M ++ flattenT M')) (flattenT M'') pt H1); intros.
      destruct H4. left. apply in_swap. easy. right. easy.
    - simpl in *.
      apply nodup_swap. specialize(nodup_swap ((flattenT M ++ flattenT M')) (flattenT M'') H2); intros.
      apply nodup_swap2. easy.
    - constructor. constructor. easy. easy. easy.
  - inversion H. subst. inversion H3. subst. clear H3. inversion H6. subst. clear H6.
    inversion H5. subst. clear H5.
    constructor; try easy.
    - intros. specialize(H1 pt H3).
      unfold InT in *. simpl in *.
      apply in_or_app.
      specialize(in_or (((flattenT M ++ flattenT M') ++ flattenT M'')) (flattenT M''') pt H1); intros.
      destruct H4.
      - left.
        specialize(app_assoc (flattenT M) (flattenT M') (flattenT M'')); intros.
        replace (flattenT M ++ flattenT M' ++ flattenT M'') with ((flattenT M ++ flattenT M') ++ flattenT M'') in *.
        easy.
      - right. easy.
    - simpl in *.
      specialize(app_assoc (flattenT M) (flattenT M') (flattenT M'')); intros.
      replace (flattenT M ++ flattenT M' ++ flattenT M'') with ((flattenT M ++ flattenT M') ++ flattenT M'') in *.
      easy.
    - constructor. constructor. easy. constructor. easy. easy. easy.
Qed.

Inductive betaP: relation session :=
  | r_comm  : forall p q xs y l e v Q M, 
              onth l xs = Some y -> stepE e (e_val v) -> 
              betaP ((p <-- (p_recv q xs)) ||| (q <-- (p_send p l e Q)) ||| M)
                    ((p <-- subst_expr_proc y (e_val v) 0 0) ||| (q <-- Q) ||| M)
  | rt_ite  : forall p e P Q M,
              stepE e (e_val (vbool true)) ->
              betaP ((p <-- (p_ite e P Q)) ||| M) ((p <-- P) ||| M)
  | rf_ite  : forall p e P Q M,
              stepE e (e_val (vbool false)) ->
              betaP ((p <-- (p_ite e P Q)) ||| M) ((p <-- Q) ||| M)
  | r_commu  : forall p q xs y l e v Q, 
              onth l xs = Some y -> stepE e (e_val v) -> 
              betaP ((p <-- (p_recv q xs)) ||| (q <-- (p_send p l e Q)))
                    ((p <-- subst_expr_proc y (e_val v) 0 0) ||| (q <-- Q))
  | rt_iteu  : forall p e P Q,
              stepE e (e_val (vbool true)) ->
              betaP ((p <-- (p_ite e P Q))) ((p <-- P))
  | rf_iteu  : forall p e P Q,
              stepE e (e_val (vbool false)) ->
              betaP ((p <-- (p_ite e P Q))) ((p <-- Q))
  | r_struct: forall M1 M1' M2 M2', unfoldP M1 M1' -> unfoldP M2' M2 -> betaP M1' M2' -> betaP M1 M2.

Definition beta_multistep := multi betaP.
    
Inductive multiC : relation gtt := 
  | multiC_refl : forall G, multiC G G
  | multiC_step : forall G1 G2 G3 p q n, gttstepC G1 G2 p q n -> multiC G2 G3 -> multiC G1 G3.

Lemma sub_red_1_helper : forall l x1 xs x4 x5 y,
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

Lemma typ_after_step_3_helper_s : forall M p q G G' l L1 L2 S T xs y,
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
    specialize(typ_after_step_3_helper G G' p0 q s l L1 L2 x x1 x0 x2 T'); intros.
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

Lemma sub_red_helper : forall l xs x1 y,
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

Lemma sub_red_helper_1 : forall [l LQ SL' TL' x x1 x0 q],
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

Lemma sub_red_helper_2 : forall [l LP SL TL LT S p],
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

Lemma sub_red_helper_3 : forall M G pt,
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

Theorem sub_red : forall M M' G, typ_sess M G -> betaP M M' -> exists G', typ_sess M' G' /\ multiC G G'.
Proof.
  intros. revert H. revert G.
  induction H0; intros; try easy.
  (* R-COMM *)
  inversion H1. subst.
  - inversion H5. subst. clear H5. inversion H8. subst. clear H8. 
    inversion H7. subst. clear H7. inversion H10. subst. clear H10. clear H1.
    destruct H6. destruct H1. destruct H7. destruct H6. rename x into T. rename x0 into T'.
    destruct H7 as (H7, Ht). destruct H5 as (H5, Htt).
    - specialize(inv_proc_recv q xs (p_recv q xs) nil nil T H5 (erefl (p_recv q xs))); intros. 
      destruct H8. destruct H8. destruct H10. destruct H11.
    - specialize(inv_proc_send p l e Q (p_send p l e Q) nil nil T' H7 (erefl (p_send p l e Q))); intros.
      destruct H13. destruct H13. destruct H13. destruct H14. rename x0 into S. rename x1 into LT.
    
    specialize(typ_after_step_h q p l); intros.
    specialize(subtype_recv T q x H10); intros. destruct H17. subst.
    specialize(subtype_send T' p (extendLis l (Some (S, LT))) H15); intros. destruct H17. subst.
    rename x0 into LQ. rename x1 into LP.
    specialize(H16 G LP LQ S LT).
    specialize(sub_red_helper l xs x y H H11); intros. destruct H17. destruct H17. destruct H17.
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
      - specialize(sub_red_helper_3 M G pt); intros. apply H21; try easy.
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
    
    specialize(canon_rep_s G q p LP LQ SL TL SL' TL' l H2 H6 H22 H1 H23); intros.
    destruct H24 as (Gl,(ctxG,(SI,(Sn,(Ha,(Hb,(Hc,(Hd,(He,(Hf,Hg)))))))))).
    specialize(sub_red_helper_1 H23 H17 H10); intros.
    specialize(sub_red_helper_2 H15 H22); intros. 
    constructor. constructor.
    - constructor.
      specialize(typ_after_step_2_helper q p l G G' LP LQ SL TL SL' TL'); intros.
      assert(projectionC G' p TL'). apply H26; try easy. clear H26. 
      exists TL'. split; try easy.
      split.
      apply _subst_expr_var with (S := x0); try easy.
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
      specialize(typ_after_step_1_helper q p l G G' LP LQ SL TL SL' TL'); intros.
      assert(projectionC G' q TL). apply H26; try easy. clear H26.
      exists TL. split; try easy. split.
      - apply tc_sub with (t := LT); try easy.
        specialize(typable_implies_wfC H7); intros.
        specialize(wfC_send H26 H22); try easy.
      - intros. specialize(Ht (Nat.succ n)). destruct Ht. inversion H26.
        subst. exists x2. easy.
    - specialize(typ_after_step_3_helper_s M q p G G' l LP LQ S LT x (x0, x1)); intros.
      inversion H4. subst. inversion H30. subst.
      specialize(Classical_Prop.not_or_and (q = p) (In p (flattenT M)) H29); intros. destruct H27.
      apply H26; try easy.

  (* T-COND *)
  inversion H0. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
  destruct H5. destruct H4. destruct H5 as (H5, Ha).
  specialize(inv_proc_ite (p_ite e P Q) e P Q x nil nil H5 (erefl (p_ite e P Q))); intros.
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
  specialize(inv_proc_ite (p_ite e P Q) e P Q x nil nil H5 (erefl (p_ite e P Q))); intros.
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
  
  (* R-COMM *)
  inversion H1. subst.
  - inversion H5. subst. clear H5. inversion H8. subst. clear H8. 
    inversion H9. subst. clear H9.
    destruct H6 as (T,(Ha,(Hb,Hc))). destruct H7 as (T1,(Hd,(He,Hf))).
    - specialize(inv_proc_recv q xs (p_recv q xs) nil nil T Hb (erefl (p_recv q xs))); intros. 
      destruct H5 as (STT,(Hg,(Hh,(Hi,Hj)))).
    - specialize(inv_proc_send p l e Q (p_send p l e Q) nil nil T1 He (erefl (p_send p l e Q))); intros.
      destruct H5 as (S,(T',(Hk,(Hl,Hm)))).
    
    specialize(typ_after_step_h q p l); intros.
    specialize(subtype_recv T q STT Hh); intros. destruct H6. subst.
    specialize(subtype_send T1 p (extendLis l (Some (S, T'))) Hm); intros. destruct H6. subst.
    rename x into LQ. rename x0 into LP.
    specialize(H5 G LP LQ S T').
    specialize(sub_red_helper l xs STT y H Hi); intros. destruct H6. destruct H6. destruct H6.
    specialize(H5 STT (x, x0)). 
    assert(exists G' : gtt, gttstepC G G' q p l).
    apply H5; try easy. destruct H8. subst. rename x1 into G'. 
    assert(multiC G G').
    specialize(multiC_step G G' G' q p l); intros. apply H9; try easy. constructor.
    exists G'. split; try easy.
    specialize(wfgC_after_step G G' q p l H2 H8); intros. 
    assert(wfgC G').
    intros. apply H10.
    unfold projectableA. intros.
    specialize(decidable_isgPartsC G pt H2); intros. unfold Decidable.decidable in H11.
    destruct H11.
    specialize(H3 pt H11).
    - unfold InT in H3. simpl in H3.
      - destruct H3. subst. exists (ltt_recv q LQ). easy.
      - destruct H3. subst. exists (ltt_send p LP). easy.
      - easy.
    - unfold not in H11. exists ltt_end. pfold. constructor; try easy.
    constructor; try easy.
    - intros.
      apply H3; try easy.
      - specialize(part_after_step G G' q p pt l LP LQ); intros. 
        apply H13; try easy.
    specialize(projection_step_label G G' q p l LP LQ); intros.
    assert(exists (LS LS' : sort) (LT LT' : ltt), onth l LP = Some (LS, LT) /\ onth l LQ = Some (LS', LT')).
    apply H12; try easy.
    destruct H13 as (SL,(SL',(TL,(TL',(H22,H23))))).
    
    specialize(canon_rep_s G q p LP LQ SL TL SL' TL' l H2 Hd H22 Ha H23); intros.
    destruct H13 as (Gl,(ctxG,(SI,(Sn,(Hta,(Htb,(Htc,(Htd,(Hte,(Htf,Htg)))))))))).
    specialize(sub_red_helper_1 H23 H6 Hh); intros.
    specialize(sub_red_helper_2 Hm H22); intros. 
    constructor. constructor.
    - specialize(typ_after_step_2_helper q p l G G' LP LQ SL TL SL' TL'); intros.
      assert(projectionC G' p TL'). apply H15; try easy. clear H15. 
      exists TL'. split; try easy.
      split.
      apply _subst_expr_var with (S := x); try easy.
      - apply tc_sub with (t := x0); try easy.
        specialize(typable_implies_wfC Hb); intros.
        specialize(wfC_recv H15 H23); try easy.
      - apply sc_sub with (s := S); try easy.
        apply expr_typ_step with (e := e); try easy.
        apply sstrans with (s2 := SL'); try easy.
        apply sstrans with (s2 := Sn); try easy. 
        apply sstrans with (s2 := SL); try easy.
      - specialize(guardP_cont_recv_n l xs y q Hc H); intros.
        specialize(guardP_subst_expr y (e_val v) 0 0); intros. apply H17; try easy.
    - constructor.
      specialize(typ_after_step_1_helper q p l G G' LP LQ SL TL SL' TL'); intros.
      assert(projectionC G' q TL). apply H15; try easy. clear H15.
      exists TL. split; try easy. split.
      - apply tc_sub with (t := T'); try easy.
        specialize(typable_implies_wfC He); intros.
        specialize(wfC_send H15 H22); try easy.
      - intros. specialize(Hf (Nat.succ n)). destruct Hf. inversion H15.
        subst. exists x1. easy.

  (* T-COND *)
  inversion H0. subst. inversion H4. subst. clear H4.
  destruct H6. destruct H4. destruct H5 as (H5, Ha).
  specialize(inv_proc_ite (p_ite e P Q) e P Q x nil nil H5 (erefl (p_ite e P Q))); intros.
  destruct H6. destruct H6. destruct H6. destruct H7. destruct H8. destruct H9. 
  exists G. split.
  apply t_sess; try easy. constructor. exists x.
  split; try easy. split.
  apply tc_sub with (t := x0); try easy.
  specialize(typable_implies_wfC H5); try easy.
  - intros. specialize(Ha n). destruct Ha. inversion H11. subst. exists 0. constructor.
    subst. exists m. easy.
  apply multiC_refl.
  
  (* F-COND *)
  inversion H0. subst. inversion H4. subst. clear H4.
  destruct H6. destruct H4. destruct H5 as (H5, Ha).
  specialize(inv_proc_ite (p_ite e P Q) e P Q x nil nil H5 (erefl (p_ite e P Q))); intros.
  destruct H6. destruct H6. destruct H6. destruct H7. destruct H8. destruct H9. 
  exists G. split.
  apply t_sess; try easy. constructor. exists x.
  split; try easy. split.
  apply tc_sub with (t := x1); try easy.
  specialize(typable_implies_wfC H5); try easy.
  - intros. specialize(Ha n). destruct Ha. inversion H11. subst. exists 0. constructor.
    subst. exists m. easy.
  apply multiC_refl.
  
  (* R-STRUCT *)
  specialize(typ_after_unfold M1 M1' G H2 H); intros.
  specialize(IHbetaP G H3); intros. destruct IHbetaP. exists x. 
  destruct H4. split; try easy.
  specialize(typ_after_unfold M2' M2 x H4 H0); intros. easy.
Qed.

Lemma pc_par5 : forall M M' M'', unfoldP (M ||| (M' ||| M'')) ((M ||| M') ||| M'').
Proof.
  intros.
  apply pc_trans with (M' := (M' ||| M'') ||| M). constructor.
  apply pc_trans with (M' := (M' ||| (M'' ||| M))). constructor.
  apply pc_trans with (M' := (M'' ||| M) ||| M'). constructor.
  apply pc_trans with (M' := M'' ||| (M ||| M')). constructor. constructor. 
Qed.

Lemma unf_cont_l : forall M1 M1' M2,
  unfoldP M1 M1' -> 
  unfoldP (M1 ||| M2) (M1' ||| M2).
Proof.
  intros. revert M2.
  induction H; intros.
  - {
      apply pc_trans with (M' := (p <-- p_rec P) ||| (M ||| M2)). apply pc_par2.
      apply pc_trans with (M' := (p <-- Q) ||| (M ||| M2)). constructor. easy.
      apply pc_par5. 
      
    }
  - constructor. easy.
  - apply pc_refl.
  - apply pc_trans with (M' := (M' ||| M2)). apply IHunfoldP1. apply IHunfoldP2.
  - constructor.
  - constructor.
  - {
      apply pc_trans with (M' := (M ||| M') ||| (M'' ||| M2)). constructor.
      apply pc_trans with (M' := (M' ||| M) ||| (M'' ||| M2)). constructor.
      apply pc_par5.
    }
  - {
      apply pc_trans with (M' := (((M ||| M') ||| M'') ||| (M''' ||| M2))). constructor.
      apply pc_trans with (M' := ((M ||| (M' ||| M'')) ||| (M''' ||| M2))). constructor.
      apply pc_par5.
    }
Qed.

Lemma unf_cont_r : forall M1 M2 M2', 
    unfoldP M2 M2' -> 
    unfoldP (M1 ||| M2) (M1 ||| M2').
Proof.
  intros.
  apply pc_trans with (M' := M2 ||| M1). constructor.
  apply pc_trans with (M' := M2' ||| M1). apply unf_cont_l. easy.
  constructor.
Qed.

Lemma unf_cont : forall M1 M1' M2 M2',
    unfoldP M1 M1' -> unfoldP M2 M2' -> 
    unfoldP (M1 ||| M2) (M1' ||| M2').
Proof.
  intros.
  apply pc_trans with (M' := (M1 ||| M2')). apply unf_cont_r. easy.
  apply unf_cont_l. easy.
Qed.

Lemma move_forward_h : forall M,
    forall p : string,
    InT p M ->
    (exists (P : process) (M' : session), unfoldP M ((p <-- P) ||| M')) \/
    (exists P : process, unfoldP M (p <-- P)).
Proof.
  induction M; intros.
  - rename H into H2. unfold InT in H2. simpl in H2. destruct H2; try easy.
    subst. right. exists p. constructor.
  - rename H into H2. unfold InT in *. simpl in *.
    specialize(in_or (flattenT M1) (flattenT M2) p H2); intros.
    destruct H.
    - specialize(IHM1 p H). 
      destruct IHM1.
      - destruct H0 as (P,(M',Ha)).
        left. exists P. exists (M' ||| M2).
        apply pc_trans with (M' := ((p <-- P) ||| M') ||| M2). apply unf_cont_l. easy. 
        constructor.
      - destruct H0 as (P,Ha).
        left. exists P. exists M2. apply unf_cont_l. easy.
    - specialize(IHM2 p H). clear IHM1 H2.
      destruct IHM2.
      - destruct H0 as (P,(M',Ha)).
        left. exists P. exists (M1 ||| M').
        apply pc_trans with (M' := M1 ||| ((p <-- P) ||| M')). apply unf_cont_r. easy.
        apply pc_trans with (M' := (M1 ||| (p <-- P)) ||| M'). apply pc_par5.
        apply pc_trans with (M' := ((p <-- P) ||| M1) ||| M'). constructor. constructor.
      - destruct H0 as (P,Ha).
        left. exists P. exists M1.
        apply pc_trans with (M' := M1 ||| (p <-- P)). apply unf_cont_r. easy.
        constructor.
Qed.

Lemma move_forward : forall p M G, 
    typ_sess M G -> 
    isgPartsC p G -> 
    (exists P M', unfoldP M (p <-- P ||| M')) \/ (exists P, unfoldP M (p <-- P)).
Proof.
  intros. inversion H. subst. clear H1 H3 H4 H.
  specialize(H2 p H0). clear H0.
  revert H2. revert p. clear G.
  apply move_forward_h.
Qed.

Lemma part_after_unf : forall M M' p,
    unfoldP M M' -> 
    InT p M ->
    InT p M'.
Proof.
  intros. revert H0. revert p.
  induction H; intros; try easy.
  - apply IHunfoldP2. apply IHunfoldP1. easy.
  - unfold InT in *.
    simpl in *. apply in_swap. easy.
  - unfold InT in *. simpl in *.
    specialize(app_assoc (flattenT M) (flattenT M') (flattenT M'')); intros.
    replace (flattenT M ++ flattenT M' ++ flattenT M'') with ((flattenT M ++ flattenT M') ++ flattenT M'') in *. easy.
  - unfold InT in *. simpl in *.
    apply in_or_app. specialize(in_or ((flattenT M ++ flattenT M')) (flattenT M'') p H0); intros.
    destruct H.
    - left. apply in_swap. easy. right. easy.
  - unfold InT in *. simpl in *.
    specialize(app_assoc (flattenT M) (flattenT M') (flattenT M'')); intros.
    replace (flattenT M ++ flattenT M' ++ flattenT M'') with ((flattenT M ++ flattenT M') ++ flattenT M'') in *. easy.
Qed.

Lemma canonical_glob_nt : forall M p q l,
    typ_sess M (gtt_send p q l) -> 
    (exists M' P Q, unfoldP M ((p <-- P) ||| (q <-- Q) ||| M')) \/ (exists P Q, unfoldP M ((p <-- P) ||| (q <-- Q))).
Proof.
  intros.
  inversion H. subst.
  assert(InT p M). apply H1. apply triv_pt_p. easy.
  assert(InT q M). apply H1. apply triv_pt_q. easy.
  specialize(move_forward_h M p H4); intros.
  specialize(wfgC_triv p q l H0); intros. destruct H7.
  destruct H6.
  - destruct H6 as (P,(M',Ha)). specialize(part_after_unf M ((p <-- P) ||| M') q Ha H5); intros.
    unfold InT in *.
    inversion H6. subst. easy. simpl in H9.
    specialize(move_forward_h M' q); intros.
    unfold InT in H10.
    specialize(H10 H9).
    destruct H10.
    - destruct H10 as (P1,(M'',Hb)). left.
      exists M''. exists P. exists P1.
      apply pc_trans with (M' := ((p <-- P) ||| M')); try easy.
      apply pc_trans with (M' := ((p <-- P) ||| ((q <-- P1) ||| M''))). apply unf_cont_r. easy.
      apply pc_par5.
    - destruct H10 as (P1,Hb).
      right. exists P. exists P1. 
      apply pc_trans with (M' := ((p <-- P) ||| M')); try easy.
      apply unf_cont_r. easy.
  - destruct H6 as (P,H6).
    specialize(part_after_unf M (p <-- P) q H6 H5); intros.
    inversion H9; try easy.
Qed.

Lemma sub_mon : monotone2 subtype.
Proof.
  unfold monotone2.
  intros.
  induction IN; intros.
  - constructor.
  - constructor.
    revert H. revert xs. induction ys; intros. constructor.
    destruct xs; try easy.
    simpl in *.
    - destruct a. destruct p0. destruct o; try easy.
      destruct p0. destruct H as (Ha,(Hb,Hc)). split. easy.
      split. apply LE. easy. apply IHys; try easy.
    - destruct o. destruct p0. apply IHys; try easy. 
      apply IHys; try easy.
  - constructor.
    revert H. revert ys.
    induction xs; intros.
    - constructor.
      destruct ys; try easy.
      simpl in *.
      destruct a. destruct p0. destruct o; try easy.
      destruct p0. destruct H as (Ha,(Hb,Hc)). split. easy. split. apply LE. easy.
      apply IHxs. easy.
      destruct o. destruct p0. apply IHxs. easy. apply IHxs. easy.
Qed.

Lemma canonical_glob_n : forall M,
    typ_sess M gtt_end -> 
    exists M', unfoldP M M' /\ ForallT (fun _ P => P = p_inact \/ (exists e p1 p2, P = p_ite e p1 p2 /\ typ_proc nil nil (p_ite e p1 p2) ltt_end)) M'.
Proof.
  intros.
  inversion H. subst.
  clear H H1 H2.
  revert H3.
  induction M; intros.
  - inversion H3. subst. clear H3.
    destruct H1 as (T,(Ha,(Hb,Hc))).
    specialize(Hc 1). destruct Hc as (m, Hc).
    revert Hc Hb Ha H0. revert s p T.
    induction m; intros. pinversion Ha. subst.
    - inversion Hc. subst. exists (s <-- p_inact). split.
      apply pc_refl.
      constructor. left. easy.
      subst.
      specialize(inv_proc_send pt l e g (p_send pt l e g) nil nil ltt_end Hb (erefl (p_send pt l e g))); intros.
      destruct H1 as (S1,(T1,(Hd,(He,Hf)))). pinversion Hf.
      apply sub_mon.
      subst.
      specialize(inv_proc_recv p0 lis (p_recv p0 lis) nil nil ltt_end Hb (erefl (p_recv p0 lis))); intros.
      destruct H1 as (STT,(Hd,(He,(Hf,Hg)))). pinversion He. apply sub_mon.
    apply proj_mon.
    pinversion Ha. subst.
    inversion Hc; try easy.
    - subst. exists (s <-- p_inact). split. apply pc_refl. constructor. left. easy.
    - subst.
      specialize(inv_proc_send pt l e g (p_send pt l e g) nil nil ltt_end Hb (erefl (p_send pt l e g))); intros. destruct H1 as (S1,(T1,(Hd,(He,Hf)))). pinversion Hf. apply sub_mon.
    - subst.
      specialize(inv_proc_recv p0 lis (p_recv p0 lis) nil nil ltt_end Hb (erefl (p_recv p0 lis))); intros.
      destruct H1 as (STT,(Hd,(He,(Hf,Hg)))). pinversion He. apply sub_mon.
    - subst.
      specialize(inv_proc_ite (p_ite e P Q) e P Q ltt_end nil nil Hb (erefl (p_ite e P Q))); intros.
      destruct H1 as (T1,(T2,(Hd,(He,(Hf,(Hg,Hh)))))).
      pinversion Hf. subst. pinversion Hg. subst.
      exists (s <-- p_ite e P Q). split. apply pc_refl.
      constructor. right. exists e. exists P. exists Q. easy.
      apply sub_mon. apply sub_mon.
    - subst.
      specialize(IHm s Q ltt_end).
      assert(exists M' : session,
        unfoldP (s <-- Q) M' /\
        ForallT
          (fun (_ : string) (P : process) =>
           P = p_inact \/
           (exists (e : expr) (p1 p2 : process),
              P = p_ite e p1 p2 /\ typ_proc nil nil (p_ite e p1 p2) ltt_end)) M').
      {
        apply IHm; try easy.
        - specialize(inv_proc_rec (p_rec g) g ltt_end nil nil Hb (erefl (p_rec g))); intros.
          destruct H1 as (T1,(Hd,He)). pinversion He. subst.
          specialize(subst_proc_varf g (p_rec g) ltt_end ltt_end nil nil Q); intros.
          apply H1; try easy. apply sub_mon.
        - pfold. easy.
      }
      destruct H1 as (M1,(Hd,He)). exists M1. split; try easy.
      apply pc_trans with (M' := (s <-- Q)); try easy.
      constructor. easy.
      apply proj_mon.
  - inversion H3. subst. clear H3.
    specialize(IHM1 H2). specialize(IHM2 H4). clear H2 H4.
    destruct IHM1 as (M1',(Ha,Hb)).
    destruct IHM2 as (M2',(Hc,Hd)). exists (M1' ||| M2'). 
    split. apply unf_cont; try easy.
    constructor; try easy.
Qed.

Lemma typ_proc_after_betaPr : forall P Q Gs Gt T, 
    multi betaPr P Q ->
    typ_proc Gs Gt P T -> typ_proc Gs Gt Q T.
Proof.
  intros. revert H0. revert T Gt Gs.
  induction H; intros.
  - easy.
  - apply IHmulti. clear IHmulti H0. clear z.
    inversion H. subst.
    specialize(inv_proc_rec (p_rec P) P T Gs Gt H1 (erefl (p_rec P))); intros.
    destruct H2 as (T0,(Ha,Hb)).
    specialize(subst_proc_varf P (p_rec P) T0 T0 Gs Gt y); intros.
    specialize(typable_implies_wfC H1); intros.
    apply tc_sub with (t := T0); try easy.
    apply H2; try easy. apply tc_mu. easy.
Qed.

Lemma betaPr_unfold_h : forall P Q1 Q Q2 p q,
          multi betaPr P Q1 -> 
          multi betaPr Q Q2 ->
          unfoldP (((p <-- P) ||| (q <-- Q))) (((p <-- Q1) ||| (q <-- Q2))).
Proof.
  intros.
  apply pc_trans with (M' := (p <-- Q1) ||| (q <-- Q)).
  - apply unf_cont_l. clear H0. clear Q Q2. 
    induction H; intros. constructor. apply pc_trans with (M' := (p <-- y)); try easy.
    clear IHmulti H0. inversion H. subst. constructor. easy.
  - apply unf_cont_r. clear H. clear P Q1.
    induction H0; intros. constructor. apply pc_trans with (M' := (q <-- y)); try easy.
    clear IHmulti H0. inversion H. subst. constructor. easy.
Qed.

Lemma betaPr_unfold : forall P Q1 Q Q2 p q M',
          multi betaPr P Q1 -> 
          multi betaPr Q Q2 ->
          unfoldP (((p <-- P) ||| (q <-- Q)) ||| M') (((p <-- Q1) ||| (q <-- Q2)) ||| M').
Proof.
  intros. apply unf_cont_l; try easy. apply betaPr_unfold_h; try easy.
Qed.

Theorem prog : forall M G, typ_sess M G -> (exists M', unfoldP M M' /\ (ForallT (fun _ P => P = p_inact) M')) \/ exists M', betaP M M'.
Proof.
  intros.
  destruct G.
  - specialize(canonical_glob_n M H); intros.
    destruct H0 as (M',(Ha,Hb)).
    assert(ForallT (fun _ P => P = p_inact) M' \/ (exists p e p1 p2, typ_proc nil nil (p_ite e p1 p2) ltt_end /\ ((exists M'', unfoldP M' ((p <-- p_ite e p1 p2) ||| M'')) \/ unfoldP M' (p <-- p_ite e p1 p2)))).
    {
      clear H Ha. clear M. revert Hb.
      induction M'; intros.
      - inversion Hb. subst. clear Hb. destruct H0.
        - subst. left. constructor. easy.
        - destruct H as (e,(p1,(p2,(Ha,Hb)))).
          right. exists s. exists e. exists p1. exists p2.  
          split. easy.
          right. subst. apply pc_refl.
      - inversion Hb. subst. clear Hb.
        specialize(IHM'1 H1). specialize(IHM'2 H2). clear H1 H2.
        destruct IHM'1.
        - destruct IHM'2. left. constructor; try easy.
        - destruct H0 as (p0,(e,(p1,(p2,(Ha,Hb))))).
          right. exists p0. exists e. exists p1. exists p2. split. easy.
          left. destruct Hb.
          - destruct H0 as (M1,Hc).
            exists (M1 ||| M'1).
            apply pc_trans with (M' := M'2 ||| M'1). constructor.
            apply pc_trans with (M' := ((p0 <-- p_ite e p1 p2) ||| M1) ||| M'1).
            apply unf_cont_l. easy. constructor.
          - exists M'1. 
            apply pc_trans with (M' := M'2 ||| M'1). constructor.
            apply unf_cont_l. easy.
        - destruct H as (p,(e,(p1,(p2,(Ha,Hb))))).
          destruct Hb.
          - destruct H as (M',H). 
            right. exists p. exists e. exists p1. exists p2. split. easy.
            left. exists (M' ||| M'2).
            apply pc_trans with (M' := ((p <-- p_ite e p1 p2 ||| M') ||| M'2)). apply unf_cont_l. easy.
            constructor.
          - right. exists p. exists e. exists p1. exists p2.
            split. easy.
            left. exists M'2. apply unf_cont_l. easy.
    }
    clear Hb. destruct H0.
    - left. exists M'. easy.
    - destruct H0 as (p,(e,(p1,(p2,(Hb,Hc))))). right.
      destruct Hc. 
      - destruct H0 as (M1,H0).
        assert(unfoldP M ((p <-- p_ite e p1 p2) ||| M1)). apply pc_trans with (M' := M'); try easy.
        clear H0 Ha.
        assert(exists M2, betaP ((p <-- p_ite e p1 p2) ||| M1) M2).
        {
          specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 ltt_end nil nil Hb (erefl (p_ite e p1 p2))); intros.
          destruct H0 as (T1,(T2,(Ha,(Hf,(Hc,(Hd,He)))))).
          specialize(expr_eval_b e He); intros.
          destruct H0.
          - exists ((p <-- p1) ||| M1). constructor. easy.
          - exists ((p <-- p2) ||| M1). constructor. easy.
        }
        destruct H0 as (M2,H0). exists M2.
        apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| M1)) (M2' := M2); try easy. 
        constructor.
      - assert(exists M2, betaP ((p <-- p_ite e p1 p2)) M2).
        { 
          specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 ltt_end nil nil Hb (erefl (p_ite e p1 p2))); intros.
          destruct H1 as (T1,(T2,(Hg,(Hf,(Hc,(Hd,He)))))).
          specialize(expr_eval_b e He); intros. destruct H1.
          - exists ((p <-- p1)). constructor. easy.
          - exists ((p <-- p2)). constructor. easy.
        }
        destruct H1 as (M2,H1). exists M2.
        apply r_struct with (M1' := (p <-- p_ite e p1 p2)) (M2' := M2); try easy.
        apply pc_trans with (M' := M'); try easy. constructor.
  - right.
    rename s into p. rename s0 into q.
    specialize(canonical_glob_nt M p q l H); intros.
    destruct H0.
    - destruct H0 as (M',(P,(Q,Ha))).
      specialize(typ_after_unfold M (((p <-- P) ||| (q <-- Q)) ||| M') (gtt_send p q l)); intros.
      assert(typ_sess (((p <-- P) ||| (q <-- Q)) ||| M') (gtt_send p q l)). apply H0; try easy.
      clear H0.
      assert(exists M1, betaP (((p <-- P) ||| (q <-- Q)) ||| M') M1).
      {
        inversion H1. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
        inversion H6. subst. clear H6. inversion H9. subst. clear H9.
        destruct H5 as (T,(Hd,(Hb,Hc))). destruct H6 as (T1,(He,(Hf,Hg))).
        clear Ha H2 H3 H8.
        specialize(guardP_break P Hc); intros.
        destruct H2 as (Q1,(Hh,Ho)).
        specialize(typ_proc_after_betaPr P Q1 nil nil T Hh Hb); intros.
        pinversion Hd. subst. assert False. apply H3. apply triv_pt_p; try easy. easy. subst. easy. subst. 
        - specialize(guardP_break Q Hg); intros.
          destruct H3 as (Q2,(Hj,Hl)).
          specialize(typ_proc_after_betaPr Q Q2 nil nil T1 Hj Hf); intros.
          clear H7 H9 Hg Hc H H1 Hd.
          pinversion He; try easy. subst. assert False. apply H. apply triv_pt_q; try easy. easy.
          subst. clear H7 H9 H5 He Hb Hf.
          assert(exists M1, betaP (((p <-- Q1) ||| (q <-- Q2)) ||| M') M1).
          {
            clear Hh Hj.
            destruct Ho.
            - subst. specialize(inv_proc_inact p_inact (ltt_send q ys) nil nil H2 (erefl (p_inact))); intros. 
              easy.
            - destruct H. destruct H as (e,(p1,(p2,Ha))). subst.
              specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 (ltt_send q ys) nil nil H2 (erefl (p_ite e p1 p2))); intros.
              destruct H as (T1,(T2,(Ha,(Hb,(Hc,(Hd,He)))))).
              specialize(expr_eval_b e He); intros. 
              destruct H.
              - exists ((p <-- p1) ||| ((q <-- Q2) ||| M')).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2) ||| M'))) (M2' := ((p <-- p1) ||| ((q <-- Q2) ||| M'))); try easy. constructor. constructor. constructor. easy.
              - exists ((p <-- p2) ||| ((q <-- Q2) ||| M')).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2) ||| M'))) (M2' := ((p <-- p2) ||| ((q <-- Q2) ||| M'))); try easy. constructor. constructor. constructor. easy.
            - destruct H.
              destruct H as (pt,(lb,(ex,(pr,Ha)))). subst.
              specialize(inv_proc_send pt lb ex pr (p_send pt lb ex pr) nil nil (ltt_send q ys) H2 (erefl ((p_send pt lb ex pr)))); intros. destruct H as (S,(T1,(Ht,Hb))). clear H2. rename T1 into Tl. rename Hb into Hta. clear M P Q.
              destruct Hl.
              - subst. specialize(inv_proc_inact p_inact (ltt_recv p ys0) nil nil H3 (erefl (p_inact))); intros. 
                easy.
              - destruct H. destruct H as (e,(p1,(p2,Ha))). subst. 
                specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 (ltt_recv p ys0) nil nil H3 (erefl (p_ite e p1 p2))); intros.
                destruct H as (T1,(T2,(Ha,(Hb,(Hc,(Hd,He)))))).
                specialize(expr_eval_b e He); intros. 
                destruct H.
                - exists ((q <-- p1) ||| ((p <-- p_send pt lb ex pr) ||| M')).
                  apply r_struct with (M1' := ((q <-- p_ite e p1 p2) ||| ((p <-- p_send pt lb ex pr) ||| M'))) (M2' := ((q <-- p1) ||| ((p <-- p_send pt lb ex pr) ||| M'))).
                  apply pc_trans with (M' := ((q <-- p_ite e p1 p2) ||| (p <-- p_send pt lb ex pr)) ||| M').
                  constructor. constructor. apply unf_cont_r. constructor.
                  constructor. easy.
                - exists ((q <-- p2) ||| ((p <-- p_send pt lb ex pr) ||| M')).
                  apply r_struct with (M1' := ((q <-- p_ite e p1 p2) ||| ((p <-- p_send pt lb ex pr) ||| M'))) (M2' := ((q <-- p2) ||| ((p <-- p_send pt lb ex pr) ||| M'))).
                  apply pc_trans with (M' := ((q <-- p_ite e p1 p2) ||| (p <-- p_send pt lb ex pr)) ||| M').
                  constructor. constructor. apply unf_cont_r. constructor.
                  constructor. easy.
              - destruct H. destruct H as (pt1,(lb1,(ex1,(pr1,Ha)))). subst.
                specialize(inv_proc_send pt1 lb1 ex1 pr1 (p_send pt1 lb1 ex1 pr1) nil nil (ltt_recv p ys0) H3 (erefl (p_send pt1 lb1 ex1 pr1))); intros.
                destruct H as (S1,(T1,(Ha,(Hb,Hc)))). pinversion Hc. apply sub_mon.
              - destruct H as (pt2,(llp,Ha)). subst.
                specialize(expr_eval_ss ex S Ht); intros. destruct H as (v, Ha).
                destruct Hta as (Hta,Htb).
                pinversion Htb. subst.
                specialize(inv_proc_recv pt2 llp (p_recv pt2 llp) nil nil (ltt_recv p ys0) H3 (erefl (p_recv pt2 llp))); intros.
                destruct H as (STT,(He,(Hb,(Hc,Hd)))).
                pinversion Hb. subst.
                assert(exists y, onth lb llp = Some y).
                {
                  specialize(subtype_send_inv q (extendLis lb (Some (S, Tl))) ys); intros.
                  assert(Forall2R
                    (fun u v : option (sort * ltt) =>
                     u = None \/
                     (exists (s s' : sort) (t t' : ltt),
                        u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t'))
                    (extendLis lb (Some (S, Tl))) ys). apply H; try easy.
                  pfold. easy.
                  
                  specialize(subtype_recv_inv p STT ys0); intros.
                  assert(Forall2R
                   (fun u v : option (sort * ltt) =>
                    u = None \/
                    (exists (s s' : sort) (t t' : ltt),
                       u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) ys0 STT). apply H5. pfold. easy.
                  clear H2 H5 Hd Hb He H H1 Ha Htb Hta Ht H3 H6 H0.
                  revert H7 Hc H4 H11 H10.
                  revert p q l ys ys0 llp S Tl STT. 
                  induction lb; intros.
                  - destruct ys; try easy. destruct l; try easy. destruct ys0; try easy. destruct STT; try easy. destruct llp; try easy.
                    inversion H10. subst. clear H10. inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion Hc. subst. clear Hc. inversion H4. subst. clear H4.
                    clear H13 H11 H10 H8 H5.
                    destruct H9; try easy. destruct H as (s1,(s2,(t1,(t2,(Ha,(Hb,(Hc,Hd))))))). subst.
                    destruct H2; try easy. destruct H as (s3,(g1,(t3,(He,(Hf,Hg))))). subst.
                    destruct H3; try easy. destruct H as (s4,(g2,(t4,(Hh,(Hi,Hj))))). subst.
                    destruct H6; try easy. destruct H as (s5,(s6,(t5,(t6,(Hk,(Hl,(Hm,Hn))))))). subst.
                    destruct H7; try easy. destruct H as (p1,(s7,(t7,(Ho,(Hp,Hq))))). subst.
                    exists p1. easy.
                  - destruct ys; try easy. destruct l; try easy. destruct ys0; try easy. destruct STT; try easy. destruct llp; try easy.
                    inversion H10. subst. clear H10. inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion Hc. subst. clear Hc. inversion H4. subst. clear H4.
                    specialize(IHlb p q l ys ys0 llp S Tl STT). apply IHlb; try easy.
                }
                destruct H as (y, H).
                exists ((q <-- subst_expr_proc y (e_val v) 0 0) ||| (p <-- pr) ||| M').
                apply r_struct with (M1' := (((q <-- p_recv p llp) ||| (p <-- p_send q lb ex pr)) ||| M')) (M2' := (((q <-- subst_expr_proc y (e_val v) 0 0) ||| (p <-- pr)) ||| M')); try easy.
                constructor. constructor. constructor. easy. easy.
                apply sub_mon. apply sub_mon.
            - destruct H as (pt,(llp,Ha)). subst.
              specialize(inv_proc_recv pt llp (p_recv pt llp) nil nil (ltt_send q ys) H2 (erefl (p_recv pt llp))); intros.
              destruct H as (STT,(Ha,(Hb,Hc))). pinversion Hb. apply sub_mon.
          }
          destruct H as (M1,Hta). exists M1.
          apply r_struct with (M1' := (((p <-- Q1) ||| (q <-- Q2)) ||| M')) (M2' := M1); try easy.
          apply betaPr_unfold; try easy.
          constructor.
          apply proj_mon.
        subst. easy.
        apply proj_mon.
      }
      destruct H0 as (M1,H0). exists M1.
      apply r_struct with (M1' := (((p <-- P) ||| (q <-- Q)) ||| M')) (M2' := M1); try easy. constructor.
    - destruct H0 as (P,(Q,Ha)).
      specialize(typ_after_unfold M (((p <-- P) ||| (q <-- Q))) (gtt_send p q l)); intros.
      assert(typ_sess ((p <-- P) ||| (q <-- Q)) (gtt_send p q l)). apply H0; try easy.
      clear H0.
      assert(exists M1, betaP (((p <-- P) ||| (q <-- Q))) M1).
      {
        inversion H1. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
        inversion H8. subst. clear H8.
        destruct H5 as (T,(Hd,(Hb,Hc))). destruct H6 as (T1,(He,(Hf,Hg))).
        clear Ha H2 H3.
        specialize(guardP_break P Hc); intros.
        destruct H2 as (Q1,(Hh,Ho)).
        specialize(typ_proc_after_betaPr P Q1 nil nil T Hh Hb); intros.
        pinversion Hd. subst. assert False. apply H3. apply triv_pt_p; try easy. easy. subst. easy. subst. 
        - specialize(guardP_break Q Hg); intros.
          destruct H3 as (Q2,(Hj,Hl)).
          specialize(typ_proc_after_betaPr Q Q2 nil nil T1 Hj Hf); intros.
          clear H7 H9 Hg Hc H H1 Hd.
          pinversion He; try easy. subst. assert False. apply H. apply triv_pt_q; try easy. easy.
          subst. clear H7 H9 H5 He Hb Hf.
          assert(exists M1, betaP (((p <-- Q1) ||| (q <-- Q2))) M1).
          {
            clear Hh Hj.
            destruct Ho.
            - subst. specialize(inv_proc_inact p_inact (ltt_send q ys) nil nil H2 (erefl (p_inact))); intros. 
              easy.
            - destruct H. destruct H as (e,(p1,(p2,Ha))). subst.
              specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 (ltt_send q ys) nil nil H2 (erefl (p_ite e p1 p2))); intros.
              destruct H as (T1,(T2,(Ha,(Hb,(Hc,(Hd,He)))))).
              specialize(expr_eval_b e He); intros. 
              destruct H.
              - exists ((p <-- p1) ||| ((q <-- Q2))).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2)))) (M2' := ((p <-- p1) ||| ((q <-- Q2)))); try easy. constructor. constructor. constructor. easy.
              - exists ((p <-- p2) ||| ((q <-- Q2))).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2)))) (M2' := ((p <-- p2) ||| ((q <-- Q2)))); try easy. constructor. constructor. constructor. easy.
            - destruct H.
              destruct H as (pt,(lb,(ex,(pr,Ha)))). subst.
              specialize(inv_proc_send pt lb ex pr (p_send pt lb ex pr) nil nil (ltt_send q ys) H2 (erefl ((p_send pt lb ex pr)))); intros. destruct H as (S,(T1,(Ht,Hb))). clear H2. rename T1 into Tl. rename Hb into Hta. clear M P Q.
              destruct Hl.
              - subst. specialize(inv_proc_inact p_inact (ltt_recv p ys0) nil nil H3 (erefl (p_inact))); intros. 
                easy.
              - destruct H. destruct H as (e,(p1,(p2,Ha))). subst. 
                specialize(inv_proc_ite (p_ite e p1 p2) e p1 p2 (ltt_recv p ys0) nil nil H3 (erefl (p_ite e p1 p2))); intros.
                destruct H as (T1,(T2,(Ha,(Hb,(Hc,(Hd,He)))))).
                specialize(expr_eval_b e He); intros. 
                destruct H.
                - exists ((q <-- p1) ||| ((p <-- p_send pt lb ex pr))).
                  apply r_struct with (M1' := ((q <-- p_ite e p1 p2) ||| ((p <-- p_send pt lb ex pr)))) (M2' := ((q <-- p1) ||| ((p <-- p_send pt lb ex pr)))).
                  apply pc_trans with (M' := ((q <-- p_ite e p1 p2) ||| (p <-- p_send pt lb ex pr))).
                  constructor. constructor. apply unf_cont_r. constructor.
                  constructor. easy.
                - exists ((q <-- p2) ||| ((p <-- p_send pt lb ex pr))).
                  apply r_struct with (M1' := ((q <-- p_ite e p1 p2) ||| ((p <-- p_send pt lb ex pr)))) (M2' := ((q <-- p2) ||| ((p <-- p_send pt lb ex pr)))).
                  apply pc_trans with (M' := ((q <-- p_ite e p1 p2) ||| (p <-- p_send pt lb ex pr))).
                  constructor. constructor. apply unf_cont_r. constructor.
                  constructor. easy.
              - destruct H. destruct H as (pt1,(lb1,(ex1,(pr1,Ha)))). subst.
                specialize(inv_proc_send pt1 lb1 ex1 pr1 (p_send pt1 lb1 ex1 pr1) nil nil (ltt_recv p ys0) H3 (erefl (p_send pt1 lb1 ex1 pr1))); intros.
                destruct H as (S1,(T1,(Ha,(Hb,Hc)))). pinversion Hc. apply sub_mon.
              - destruct H as (pt2,(llp,Ha)). subst.
                specialize(expr_eval_ss ex S Ht); intros. destruct H as (v, Ha).
                destruct Hta as (Hta,Htb).
                pinversion Htb. subst.
                specialize(inv_proc_recv pt2 llp (p_recv pt2 llp) nil nil (ltt_recv p ys0) H3 (erefl (p_recv pt2 llp))); intros.
                destruct H as (STT,(He,(Hb,(Hc,Hd)))).
                pinversion Hb. subst.
                assert(exists y, onth lb llp = Some y).
                {
                  specialize(subtype_send_inv q (extendLis lb (Some (S, Tl))) ys); intros.
                  assert(Forall2R
                    (fun u v : option (sort * ltt) =>
                     u = None \/
                     (exists (s s' : sort) (t t' : ltt),
                        u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t'))
                    (extendLis lb (Some (S, Tl))) ys). apply H; try easy.
                  pfold. easy.
                  
                  specialize(subtype_recv_inv p STT ys0); intros.
                  assert(Forall2R
                   (fun u v : option (sort * ltt) =>
                    u = None \/
                    (exists (s s' : sort) (t t' : ltt),
                       u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) ys0 STT). apply H5. pfold. easy.
                  clear H2 H5 Hd Hb He H H1 Ha Htb Hta Ht H3 H6 H0.
                  revert H7 Hc H4 H11 H10.
                  revert p q l ys ys0 llp S Tl STT. 
                  induction lb; intros.
                  - destruct ys; try easy. destruct l; try easy. destruct ys0; try easy. destruct STT; try easy. destruct llp; try easy.
                    inversion H10. subst. clear H10. inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion Hc. subst. clear Hc. inversion H4. subst. clear H4.
                    clear H13 H11 H10 H8 H5.
                    destruct H9; try easy. destruct H as (s1,(s2,(t1,(t2,(Ha,(Hb,(Hc,Hd))))))). subst.
                    destruct H2; try easy. destruct H as (s3,(g1,(t3,(He,(Hf,Hg))))). subst.
                    destruct H3; try easy. destruct H as (s4,(g2,(t4,(Hh,(Hi,Hj))))). subst.
                    destruct H6; try easy. destruct H as (s5,(s6,(t5,(t6,(Hk,(Hl,(Hm,Hn))))))). subst.
                    destruct H7; try easy. destruct H as (p1,(s7,(t7,(Ho,(Hp,Hq))))). subst.
                    exists p1. easy.
                  - destruct ys; try easy. destruct l; try easy. destruct ys0; try easy. destruct STT; try easy. destruct llp; try easy.
                    inversion H10. subst. clear H10. inversion H11. subst. clear H11. inversion H7. subst. clear H7. inversion Hc. subst. clear Hc. inversion H4. subst. clear H4.
                    specialize(IHlb p q l ys ys0 llp S Tl STT). apply IHlb; try easy.
                }
                destruct H as (y, H).
                exists ((q <-- subst_expr_proc y (e_val v) 0 0) ||| (p <-- pr)).
                apply r_struct with (M1' := (((q <-- p_recv p llp) ||| (p <-- p_send q lb ex pr)))) (M2' := (((q <-- subst_expr_proc y (e_val v) 0 0) ||| (p <-- pr)))); try easy.
                constructor. constructor. constructor. easy. easy.
                apply sub_mon. apply sub_mon.
            - destruct H as (pt,(llp,Ha)). subst.
              specialize(inv_proc_recv pt llp (p_recv pt llp) nil nil (ltt_send q ys) H2 (erefl (p_recv pt llp))); intros.
              destruct H as (STT,(Ha,(Hb,Hc))). pinversion Hb. apply sub_mon.
          }
          destruct H as (M1,Hta). exists M1.
          apply r_struct with (M1' := (((p <-- Q1) ||| (q <-- Q2)))) (M2' := M1); try easy.
          apply betaPr_unfold_h; try easy.
          constructor.
          apply proj_mon.
        subst. easy.
        apply proj_mon.
      }
      destruct H0 as (M1,H0). exists M1.
      apply r_struct with (M1' := (((p <-- P) ||| (q <-- Q)))) (M2' := M1); try easy. constructor.
Qed.


Definition stuck (M : session) := ((exists M', unfoldP M M' /\ ForallT (fun _ P => P = p_inact) M') -> False) /\ ((exists M', betaP M M') -> False).

Definition stuckM (M : session) := exists M', multi betaP M M' /\ stuck M'.

Theorem stuck_free : forall M G, typ_sess M G -> stuckM M -> False.
Proof.
  intros. 
  unfold stuckM in H0. destruct H0 as (M',(Ha,Hb)).
  revert Hb H. revert G.
  induction Ha; intros.
  - destruct Hb.
    specialize(prog x G H); intros. destruct H2. apply H0. easy. apply H1. easy.
  - specialize(sub_red x y G H0 H); intros.
    destruct H1 as (G',(Hc,Hd)).
    apply IHHa with (G := G'); try easy.
Qed.