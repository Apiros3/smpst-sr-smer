From SST Require Import src.expressions process.processes process.inversion_helper process.typecheck type.global type.local type.isomorphism.
From mathcomp Require Import ssreflect.seq.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
Import ListNotations.
From Paco Require Import paco.

Lemma typable_implies_wfC [P : process] [Gs : ctxS] [Gt : ctxT] [T : ltt] :
  typ_proc Gs Gt P T -> wfC T.
Proof.
  intros. induction H using typ_proc_ind_ref; try easy.
  - unfold wfC. exists l_end. split. pfold. constructor. 
    split. apply wfl_end.
    intros. exists 0. apply gl_end.
  - apply typable_implies_wfC_helper_recv2 with (Pr := Pr); try easy.
  - unfold wfC.
    inversion IHtyp_proc. 
    destruct H0. destruct H1.
    exists (l_send p (extendLis l (Some (S, x)))).
    unfold wfC in IHtyp_proc. destruct IHtyp_proc. destruct H3. destruct H4.
    split.
    - unfold lttTC. pfold. constructor.
      induction l; intros; try easy.
      simpl in *.
      - constructor; try easy.
        right. exists S. exists x. exists T. split. easy. split. easy.
        unfold lttTC in H0. left. easy.
      - simpl. constructor; try easy.
        left. easy.
    split.
    - induction l; intros; try easy.
      simpl in *.
      - constructor; try easy.
      - constructor; try easy. right. exists S. exists x. split; try easy.
      - inversion IHl. subst.
        constructor; try easy.
        constructor; try easy. left. easy.
      - intros.
        destruct n; try easy.
        - exists 0. apply gl_nil.
        - specialize(H2 n). destruct H2.
          exists x1. apply gl_send; try easy.
          induction l; intros; try easy.
          - simpl in *. constructor; try easy.
            right. exists S. exists x. split; try easy.
          - simpl. constructor; try easy. left. easy.
Qed.

Lemma inv_proc_recv: forall p Q P Gs Gt T, 
  typ_proc Gs Gt P T ->
  P = (p_recv p Q) -> 
  (exists STT, length Q = length STT /\ subtypeC (ltt_recv p STT) T /\ 
  List.Forall2 (fun u v => (u = None /\ v = None) \/ 
                     (exists p s t, u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) Gt p t)) Q STT /\ SList Q).
Proof. intros.
       induction H; intros; try easy.
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc. destruct H3. destruct H4. 
       exists x.
       split; try easy. split; try easy.
       specialize(stTrans (ltt_recv p x) t t' H4 H1); intros.
       easy.
       inversion H0. subst. exists STT.
       split. easy. split. apply stRefl. easy.
Qed.

Lemma inv_proc_send: forall p l e Q P Gs Gt T, 
  typ_proc Gs Gt P T ->
  P = (p_send p l e Q) -> exists S T', typ_expr Gs e S /\ typ_proc Gs Gt Q T' /\  subtypeC (ltt_send p (extendLis l (Some (S,T')))) T.
Proof.
  intros. revert H0. induction H; intros; try easy.
  specialize(IHtyp_proc H2); intros. destruct IHtyp_proc. destruct H3. destruct H3. destruct H4.
  exists x. exists x0. split; try easy. split; try easy.
  specialize(stTrans (ltt_send p (extendLis l (Some (x, x0)))) t t' H5 H0); intros; try easy.
  inversion H1. subst.
  exists S. exists T. split; try easy. split; try easy. apply stRefl. 
Qed.

Lemma inv_proc_ite: forall P e Q1 Q2 T Gs Gt,
  typ_proc Gs Gt P T ->
  P = (p_ite e Q1 Q2) -> exists T1 T2, typ_proc Gs Gt Q1 T1 /\ typ_proc Gs Gt Q2 T2 /\ subtypeC T1 T /\ subtypeC T2 T /\ typ_expr Gs e sbool.
Proof. intros.
       induction H; intros; try easy.
       inversion H0.
       subst.
       exists T. exists T.
       split. easy. split. easy. split. apply stRefl. split. apply stRefl. easy.
       
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc as (T1,(T2,(Ha,(Hb,(Hc,Hd))))).
       exists T1. exists T2.
       split.
       specialize(tc_sub cs ct Q1 T1 T1); intro HTS.
       apply HTS. easy. apply stRefl. specialize(typable_implies_wfC Ha); easy.
       split. easy. split. 
       specialize(stTrans T1 t t' Hc H1); intro HT. easy.
       split. destruct Hd.
       specialize(stTrans T2 t t' H3 H1); intro HT. easy.
       destruct Hd. easy.
Qed.

Lemma inv_proc_rec: forall P Q T' Gs Gt,
  typ_proc Gs Gt P T' ->
  P = (p_rec Q)   -> exists T, (typ_proc Gs (Some T :: Gt) Q T /\ subtypeC T T').
Proof. intros.
       induction H; intros; try easy.
       inversion H0. subst.
       exists t. 
       split. easy. apply stRefl.
              
       specialize(IHtyp_proc H0).
       destruct IHtyp_proc. destruct H3.  
       exists x. 
       split. easy. 
       specialize(stTrans x t t' H4 H1); intros. easy.
Qed. 


Lemma inv_proc_var: forall P X T Gs Gt,
  typ_proc Gs Gt P T ->
  (P = (p_var X) -> exists T', onth X Gt = Some T' /\ subtypeC T' T /\ wfC T').
Proof. intros.
       induction H; intros; try easy.
       inversion H0. subst.
       exists t. split. easy. split. apply stRefl. easy.
       
       specialize(IHtyp_proc H0); intros. destruct IHtyp_proc.
       destruct H3.
       exists x. split. easy. split. destruct H4.
       specialize(stTrans x t t' H4 H1); intros; try easy. easy.
Qed.
       

Lemma inv_proc_inact: forall P T Gs Gt,
  typ_proc Gs Gt P T ->
  P = p_inact -> T = ltt_end.
Proof. intros.
       induction H; intros; try easy.
       subst. 
       specialize(IHtyp_proc eq_refl).
       subst.
       punfold H1. inversion H1. easy.
       apply subtype_monotone; try easy.
Qed.
