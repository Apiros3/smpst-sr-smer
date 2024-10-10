From SST Require Export type.global type.local type.isomorphism.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.


Inductive Forall3S {A} : (A -> A -> A -> Prop) -> list A -> list A -> list A -> Prop := 
  | Forall3_nil0 : forall P xs, Forall3S P nil xs xs
  | Forall3_nil1 : forall P xs, Forall3S P xs nil xs
  | Forall3_cons : forall P a xa b xb c xc, P a b c -> Forall3S P xa xb xc -> Forall3S P (a :: xa) (b :: xb) (c :: xc).

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

Inductive isMergable : ltt -> ltt -> Prop :=
  | mrgba : forall x, isMergable x x
  | mrgb_bra : forall r xs ys, Forall2R (fun u v => u = None \/ u = v) xs ys -> (SList ys -> SList xs) ->
               isMergable (ltt_recv r xs) (ltt_recv r ys).
  
Inductive merges_at_n : fin -> ltt -> ltt -> Prop := 
  | merga0 : forall T T', isMergable T T' -> merges_at_n 0 T T'
  | mergan_recv : forall n p xs ys, Forall2R (fun u v => u = None \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t') /\ exists k, merges_at_n k t t' /\ k < n)) xs ys -> (SList ys -> SList xs) 
                  -> merges_at_n n (ltt_recv p xs) (ltt_recv p ys)
  | mergan_send : forall n p xs ys, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t') /\ exists k, merges_at_n k t t' /\ k < n)) xs ys 
                  -> merges_at_n n (ltt_send p xs) (ltt_send p ys).

Section merges_at_n_ind_ref.
  Variable P : fin -> ltt -> ltt -> Prop.
  Hypothesis P_merga0 : forall T T', isMergable T T' -> P 0 T T'.
  Hypothesis P_mergan_recv : forall n p xs ys, Forall2R (fun u v => u = None \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t') /\ exists k, P k t t' /\ k < n)) xs ys -> (SList ys -> SList xs) 
                  -> P n (ltt_recv p xs) (ltt_recv p ys).
  Hypothesis P_mergan_send : forall n p xs ys, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t') /\ exists k, P k t t' /\ k < n)) xs ys 
                  -> P n (ltt_send p xs) (ltt_send p ys).

  Fixpoint merges_at_n_ind_ref (n : fin) (T T' : ltt) (a : merges_at_n n T T') {struct a} : P n T T'.
  Proof. 
    refine (match a with 
      | merga0 t t' ha => P_merga0 t t' ha
      | mergan_recv n p xs ys Ha Hb => P_mergan_recv n p xs ys _ Hb
      | mergan_send n p xs ys Ha => P_mergan_send n p xs ys _
    end); try easy.
    - revert Ha. 
      apply Forall2R_mono; intros.
      destruct H. left. easy.
      destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H1. destruct H1. right.
      exists x0. exists x1. exists x2. split. easy. split. easy. exists x3. split; try easy.
      apply merges_at_n_ind_ref; try easy.
    - revert Ha. 
      apply Forall2_mono; intros.
      destruct H. left. easy.
      destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H1. destruct H1. right.
      exists x0. exists x1. exists x2. split. easy. split. easy. exists x3. split; try easy.
      apply merges_at_n_ind_ref; try easy.
  Qed.

End merges_at_n_ind_ref.

Lemma triv_merge_ltt_end : forall ys0,
    isMerge ltt_end ys0 -> List.Forall (fun u => u = None \/ u = Some ltt_end) ys0.
Admitted.

Lemma merge_inv_s : forall l ys T' T,
      onth l ys = Some T' -> 
      isMerge T ys -> 
      merges_at_n 0 T' T.
Admitted. 


Lemma merge_from_less : forall T ys3 x,
      isMerge T ys3 -> 
      Forall2
        (fun u v : option ltt =>
         u = None /\ v = None \/
         (exists t t' : ltt, u = Some t /\ v = Some t' /\ (exists n : fin, merges_at_n n t' t)))
        ys3 x -> 
      exists T', isMerge T' x. 
Proof.
  intros. revert H0. revert x.
  induction H; intros. 
  - destruct x; try easy. inversion H0. subst. clear H0. destruct x; try easy. destruct H3; try easy.
    destruct H. destruct H. destruct H. destruct H0. destruct H1. inversion H. subst. exists x0. 
    constructor.
  - destruct x; try easy. inversion H0. subst. clear H0. destruct H4; try easy. 
    destruct H0. subst. specialize(IHisMerge x H6). destruct IHisMerge. exists x0. constructor; try easy.
    destruct H0. destruct H0. destruct H0. easy.
  - destruct x; try easy. inversion H1. subst. clear H1.
    destruct H5; try easy. destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. inversion H1. subst.
    specialize(IHisMerge x H7). clear H7. destruct IHisMerge. clear H1.

Admitted.


Lemma merges_at_recv_inv : forall ys p T n,
    merges_at_n n (ltt_recv p ys) T -> 
    exists zs, T = ltt_recv p zs /\ Forall2R (fun u v => u = None \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t') /\ exists k, merges_at_n k t t' /\ k < n)) ys zs.
Admitted.

Lemma merges_at_recv_inv2 : forall xs x p n,
      merges_at_n n (ltt_recv p xs) (ltt_recv p x) -> 
      Forall2R (fun u v => u = None \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t') /\ exists k, merges_at_n k t t' /\ k < n)) xs x.
Admitted.

Lemma merges_at_recv_inv3 : forall xs p t n,
      merges_at_n n t (ltt_recv p xs) -> 
      exists zs, t = ltt_recv p zs /\ Forall2R (fun u v => u = None \/ (exists s t t', u = Some(s, t) /\ v = Some(s, t') /\ exists k, merges_at_n k t t' /\ k < n)) zs xs.
Admitted.

Lemma merge2_at_recv_inv : forall x x0 p T',
      merge2 (ltt_recv p x) (ltt_recv p x0) T' -> exists IJ, T' = ltt_recv p IJ /\ 
      Forall3S (fun u v w => 
                  (u = None /\ v = None /\ w = None) \/
                  (exists t, u = None /\ v = Some t /\ w = Some t) \/
                  (exists t, u = Some t /\ v = None /\ w = Some t) \/
                  (exists t, u = Some t /\ v = Some t /\ w = Some t)) x x0 IJ.
Admitted.


Lemma merge2I_fst: forall l T p xs ys zs,
  merge2 (ltt_recv p xs) (ltt_recv p ys) (ltt_recv p zs) ->
  onth l zs = Some T ->
  onth l xs = Some T \/ onth l xs = None.
Proof. intro l.
       (* induction l; intros.
       - inversion H. subst. left. easy.
       - subst. inversion H2. subst.
         left. easy.
         subst. simpl.
         destruct H1 as [H1 | [H1 | H1]].
         + right. easy.
         + destruct H1 as (t, (H1a,(H1b,H1c))).
           subst. simpl in H0. inversion H0. subst. right. easy.
           destruct H1 as [H1 | H1].
           ++ destruct H1 as (t, (H1a,(H1b,H1c))).
              subst. left. easy.
           ++ destruct H1 as (t, (H1a,(H1b,H1c))).
              subst. simpl in H0. inversion H0. subst. left. easy.
              case_eq xs; case_eq ys; case_eq zs; intros.
              * subst. simpl in H0. easy.
              * subst. simpl. right. easy.
              * subst. simpl in H0. easy.
              * subst. simpl in H0. simpl.
                inversion H. subst. inversion H2.
              * subst. simpl in H0. easy.
              * subst. inversion H. subst. inversion H2.
              * subst. simpl in H0. easy.
              * subst. simpl. simpl in H0.
                inversion H. subst. simpl in H0. left. easy. 
                subst.
                apply IHl with (p := p) (ys := l1) (zs := l0).
                inversion H2. subst.
                apply (mrg_bra p) in H10. easy. easy.
Qed. *)
Admitted.

Lemma merge2I_snd: forall l T p xs ys zs,
  merge2 (ltt_recv p xs) (ltt_recv p ys) (ltt_recv p zs) ->
  onth l zs = Some T ->
  onth l ys = Some T \/  onth l ys = None.
Proof. intro l.
       (* induction l; intros.
       - inversion H. subst. left. easy.
       - subst. inversion H2. subst. easy.
         subst. simpl.
         destruct H1 as [H1 | [H1 | H1]].
         + right. easy.
         + destruct H1 as (t, (H1a,(H1b,H1c))).
           subst. simpl in H0. inversion H0. subst. left. easy.
           destruct H1 as [H1 | H1].
           ++ destruct H1 as (t, (H1a,(H1b,H1c))).
              subst. right. easy.
           ++ destruct H1 as (t, (H1a,(H1b,H1c))).
              subst. simpl in H0. inversion H0. subst. left. easy.
              case_eq xs; case_eq ys; case_eq zs; intros.
              * subst. simpl in H0. easy.
              * subst. simpl. right. easy.
              * subst. simpl in H0. easy.
              * subst. simpl in H0. simpl.
                inversion H. subst. inversion H2.
              * subst. simpl in H0. easy.
              * subst. inversion H. subst. inversion H2.
              * subst. simpl in H0. easy.
              * subst. simpl. simpl in H0.
                inversion H. subst. simpl in H0. left. easy. 
                subst.
                apply IHl with (p := p) (xs := l2) (zs := l0).
                inversion H2. subst.
                apply (mrg_bra p) in H10. easy. easy.
Qed. *)
Admitted.

Lemma merge2_fst: forall l T p xs ys zs,
  merge2 (ltt_recv p xs) (ltt_recv p ys) (ltt_recv p zs) ->
  onth l xs = Some T ->
  onth l zs = Some T.
Proof. intro l.
       (* induction l; intros.
       - inversion H. subst. easy.
         subst. case_eq xs; case_eq ys; case_eq zs; intros.
         * subst. simpl in H0. easy.
         * subst. simpl in H0. easy.
         * subst. inversion H.  subst. inversion H3. subst. easy.
         * subst. simpl in H0. easy.
         * subst. inversion H.  subst. inversion H3. subst. easy.
         * subst. simpl in *. inversion H2. subst.
           destruct H6 as [H6 | [H6 | H6]]. 
           + easy.
           + destruct H6 as (t, (H6a,(H6b,H6c))). inversion H6b. subst. easy.
           + destruct H6 as [H6 | H6].
             * destruct H6 as (t, (H6a,(H6b,H6c))). inversion H6b. subst. easy.
             * destruct H6 as (t, (H6a,(H6b,H6c))). inversion H6b. subst. easy.
       - subst. case_eq xs; case_eq ys; case_eq zs; intros.
         * subst. simpl in H0. easy.
         * subst. simpl in H0. easy.
         * subst. simpl in *. inversion H. subst. inversion H2.
         * subst. simpl in *. inversion H. subst. inversion H2.
         * subst. simpl in *. inversion H. subst. inversion H2.
         * subst. simpl in *. inversion H. subst. inversion H2.
         * subst. simpl in *. inversion H. subst. inversion H2.
         * subst. simpl in *.
           inversion H. subst. easy. subst.
           apply IHl with (p := p) (xs := l2) (ys := l1).
           inversion H2. subst.
           apply (mrg_bra p) in H10. easy. easy. 
Qed. *)
Admitted.


Lemma merge2_snd: forall l T p xs ys zs,
  merge2 (ltt_recv p xs) (ltt_recv p ys) (ltt_recv p zs) ->
  onth l ys = Some T ->
  onth l zs = Some T.
Proof. intro l.
      (*  induction l; intros.
       - inversion H. subst. easy.
         subst. case_eq xs; case_eq ys; case_eq zs; intros.
         * subst. simpl in H0. easy.
         * subst. simpl in H0. easy.
         * subst. inversion H.  subst. inversion H3. subst. easy.
         * subst. simpl in H0. easy.
         * subst. inversion H.  subst. inversion H3. subst. easy.
         * subst. simpl in *. inversion H2. subst.
           destruct H6 as [H6 | [H6 | H6]]. 
           + easy.
           + destruct H6 as (t, (H6a,(H6b,H6c))). inversion H6b. subst. easy.
           + destruct H6 as [H6 | H6].
             * destruct H6 as (t, (H6a,(H6b,H6c))). easy.
             * destruct H6 as (t, (H6a,(H6b,H6c))). inversion H6b. subst. easy.
       - subst. case_eq xs; case_eq ys; case_eq zs; intros.
         * subst. simpl in H0. easy.
         * subst. simpl in H0. easy.
         * subst. simpl in *. inversion H. subst. inversion H2.
         * subst. simpl in *. inversion H. subst. inversion H2.
         * subst. simpl in *. inversion H. subst. inversion H2.
         * subst. simpl in *. inversion H. subst. inversion H2.
         * subst. simpl in *. inversion H. subst. inversion H2.
         * subst. simpl in *.
           inversion H. subst. easy. subst.
           apply IHl with (p := p) (xs := l2) (ys := l1).
           inversion H2. subst.
           apply (mrg_bra p) in H10. easy. easy. 
Qed.
 *)
Admitted.
 
Lemma _a_29_part_helper_recv : forall n ys1 x4 p ys,
    onth n ys1 = Some x4 ->
    isMerge (ltt_recv p ys) ys1 -> 
    exists ys1', x4 = ltt_recv p ys1'.
Proof. intro n.
       induction n; intros.
       - inversion H0. subst.
         simpl in H. inversion H. subst.
         exists ys. easy.
         subst. simpl in H. easy.
         subst. simpl in H.
         inversion H. subst.
         inversion H2. subst. exists ys. easy.
         subst. exists ys0. easy.
       - inversion H0. 
         subst. simpl in H. destruct n; try easy.
         subst. simpl in H.
         apply IHn with (ys1 := xs) (ys := ys). easy. easy.
         subst. simpl in H.
         inversion H2. subst.
         apply IHn with (ys1 := xs) (ys := ys). easy. easy.
         subst. 
         apply IHn with (ys1 := xs) (ys := xs0). easy. easy. 
Qed.

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
         inversion H2. subst. exists x. easy.
       - inversion H0. subst. simpl in H. destruct n; try easy.
         subst. simpl in H0.
         specialize(IHn xs x3 q x).
         simpl in H.
         apply IHn. easy. easy.
         inversion H2. subst. simpl in H.
         specialize(IHn xs x3 q x).
         apply IHn. easy. easy.
Qed.

Lemma triv_merge : forall T T', isMerge T (Some T' :: nil) -> T = T'.
Proof. intros.
       inversion H. subst. easy. subst.
       inversion H3.
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
       inversion H.
       subst. 
       apply mconss with (t := T). easy.
       constructor.
       subst.
       apply mconss with (t := T). easy.
       constructor.
       subst.
       apply mconss with (t := T). easy.
       constructor.
Qed.

Lemma merge_onth_recv : forall n p LQ ys1 gqT,
      isMerge (ltt_recv p LQ) ys1 ->
      onth n ys1 = Some gqT -> 
      exists LQ', gqT = ltt_recv p LQ'.
Proof. intros. eapply _a_29_part_helper_recv. eauto. eauto. Qed.

Lemma merge_onth_send : forall n q LP ys0 gpT,
      isMerge (ltt_send q LP) ys0 ->
      onth n ys0 = Some gpT ->
      exists LP', gpT = (ltt_send q LP').
Proof. intros. eapply _a_29_part_helper_send. eauto. eauto. Qed.

Lemma merge_label_recv : forall Mp LQ' LQ0' T k l p,
          isMerge (ltt_recv p LQ') Mp ->
          onth k Mp = Some (ltt_recv p LQ0') ->
          onth l LQ0' = Some T ->
          exists T', onth l LQ' = Some T'.
Proof. intros Mp.
       induction Mp; intros.
       - destruct k; try easy.
       - subst.
         inversion H. subst.
         case_eq k; intros. subst. simpl in H0. inversion H0. subst.
         exists T. easy.
         subst. simpl in H0. destruct n; try easy.
         subst. case_eq k; intros.
         + subst. simpl in H0. easy.
         + subst. simpl in H0.
           specialize(IHMp LQ' LQ0' T n l p). apply IHMp; try easy.
           subst. case_eq k; intros.
           ++ subst. simpl in H0. inversion H0. subst.
              inversion H6. subst. exists T. easy.
              subst.
              specialize(merge2_snd l T p xs LQ0' LQ' H6 H1); intro HF.
              exists T. easy.
           ++ subst. simpl in H0.
              inversion H6. subst.
              specialize(IHMp LQ' LQ0' T n l p). apply IHMp; try easy.
              subst. inversion H. subst.
              destruct n; try easy.
              subst.
              specialize(IHMp xs LQ0' T n l p H5 H0 H1).
              destruct IHMp as (u,IHu).
              exists u.
              specialize(merge2_fst l u p xs ys LQ' H6 IHu); intro HF.
              easy.
Qed.

Lemma merge_label_send : forall Mq LP' LP0' T k l q,
          isMerge (ltt_send q LP') Mq ->
          onth k Mq = Some (ltt_send q LP0') ->
          onth l LP0' = Some T ->
          exists T', onth l LP' = Some T'. 
Proof. intro Mq.
       induction Mq; intros.
       - destruct k; try easy. 
       - inversion H. subst. case_eq k; intros. subst. simpl in H0. inversion H0. subst.
         exists T. easy.
         subst. simpl in H0. destruct n; try easy. 
         subst. case_eq k; intros.
         + subst. simpl in H0. easy. subst. simpl in H0.
           specialize(IHMq LP' LP0' T n l q). apply IHMq; try easy.
           subst. inversion H6. case_eq k; intros. subst. simpl in H0. inversion H0. subst.
           inversion H6. subst. exists T. easy.
           subst. simpl in H0.
           apply IHMq with (LP0' := LP0') (T := T) (k := n) (q := q); easy.
Qed.

Lemma merge_label_sendb : forall ys0 LP LP' ST n l q,
      isMerge (ltt_send q LP) ys0 ->
      onth n ys0 = Some (ltt_send q LP') ->
      onth l LP = Some ST ->
      onth l LP' = Some ST.
Proof. intro ys0.
       induction ys0; intros.
       - destruct n; try easy. 
       - inversion H. subst. 
         case_eq n; intros. subst. simpl in H0. inversion H0. subst. easy.
         subst. simpl in H0. destruct n0; try easy.
         subst. case_eq n; intros. subst. simpl in H0. easy.
         subst. simpl in H0.
         apply IHys0 with (LP := LP) (n := n0) (q := q); easy.
         subst. inversion H6. subst.
         case_eq n; intros. subst. simpl in H0. inversion H0. subst. easy.
         subst. simpl in H0.
         apply IHys0 with (LP := LP) (n := n0) (q := q); easy.
Qed.

Lemma merge_constr : forall p LQ ys1 n,
          isMerge (ltt_recv p LQ) ys1 ->
          onth n ys1 = Some ltt_end ->
          False.
Proof. intros p LQ ys1 n.
       revert p LQ ys1.
       induction n; intros.
       - inversion H. subst. simpl in H0. easy.
         subst. simpl in H0. easy.
         subst. simpl in H0. inversion H0. subst.
         inversion H2.
       - inversion H. subst. simpl in H0.
         destruct n; try easy. 
         subst. simpl in H0.
         apply (IHn p LQ xs). easy. easy.
         subst. simpl in H0. 
         inversion H2. subst. 
         apply (IHn p LQ xs). easy. easy.
         subst.
         apply (IHn p xs0 xs). easy. easy.
Qed.

Lemma merge_consts : forall q LP ys0 n,
          isMerge (ltt_send q LP) ys0 -> 
          onth n ys0 = Some ltt_end -> 
          False.
Proof. intros q LP ys0 n.
       revert q LP ys0.
       induction n; intros.
       - inversion H. subst. simpl in H0. easy.
         subst. simpl in H0. easy.
         subst. simpl in H0. inversion H0. subst.
         inversion H2.
       - inversion H. subst. simpl in H0.
         destruct n; try easy. 
         subst. simpl in H0.
         apply (IHn q LP xs). easy. easy.
         subst. simpl in H0. 
         inversion H2. subst. 
         apply (IHn q LP xs). easy. easy.
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
Admitted.

Lemma merge_label_send_s : forall Mq LP' LP0' T k l q,
          isMerge (ltt_send q LP') Mq ->
          onth k Mq = Some (ltt_send q LP0') ->
          onth l LP0' = Some T ->
          onth l LP' = Some T. 
Admitted.

 