From SST Require Export src.expressions process.processes process.substitution process.inversion process.inversion_expr process.typecheck type.global type.local type.isomorphism type.projection.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes Coq.Logic.Classical_Prop.

Inductive session: Type :=
  | s_ind : part   -> process -> session
  | s_par : session -> session -> session.
  
Inductive guardP : fin -> fin -> process -> Prop :=  
  | gp_nil : forall m G, guardP 0 m G
  | gp_inact : forall n m, guardP n m p_inact
  | gp_send : forall n m pt l e g, guardP n m g -> guardP (S n) m (p_send pt l e g)
  | gp_recv : forall n m p lis, List.Forall (fun u => u = None \/ (exists g, u = Some g /\ guardP n m g)) lis -> guardP (S n) m (p_recv p lis)
  | gp_ite : forall n m P Q e, guardP n m P -> guardP n m Q -> guardP n (S m) (p_ite e P Q)
  | gp_rec : forall n m g Q, substitutionP 0 0 0 (p_rec g) g Q -> guardP n m Q -> guardP n (S m) (p_rec g).

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


Lemma _a22_2 : forall M M' G, typ_sess M G -> unfoldP M M' -> typ_sess M' G.
Proof.
  intros. revert H. revert G. induction H0; intros; try easy.
  - inversion H0. subst. 
    inversion H4. subst. clear H4. inversion H7. subst. clear H7. 
    apply t_sess; try easy. constructor; try easy. constructor; try easy.
    destruct H5. exists x. split; try easy. destruct H4. split.
    destruct H5 as (H5, H6).
    - specialize(_a23_d (p_rec P) P x nil nil H5 (eq_refl (p_rec P))); intros.
      destruct H7 as (T,(Ha,Hb)).
      specialize(_a21f P (p_rec P) T T nil nil Q Ha H); intros.
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
    specialize(_a23_d (p_rec P) P T nil nil Hb (eq_refl (p_rec P))); intros.
    destruct H4 as (T0,(Hd,He)).
    specialize(_a21f P (p_rec P) T0 T0 nil nil Q); intros. exists T. split. easy.
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
  - admit.
  - admit.
Admitted.


Inductive stepE : relation expr := 
  | ec_succ  : forall e n, stepE e (e_val (vnat n)) -> stepE (e_succ e) (e_val (vnat (n+1)))
  | ec_neg   : forall e n, stepE e (e_val (vint n)) -> stepE (e_neg e) (e_val (vint (-n)))
  | ec_t_f   : forall e,   stepE e (e_val (vbool true)) -> stepE (e_not e) (e_val (vbool false))
  | ec_f_t   : forall e,   stepE e (e_val (vbool false)) -> stepE (e_not e) (e_val (vbool true))
  | ec_gt_t  : forall e e' m n, Z.lt n m -> 
                           stepE e (e_val (vint m)) -> stepE e' (e_val (vint n)) ->
                           stepE (e_gt e e') (e_val (vbool true)) 
  | ec_gt_f  : forall e e' m n, Z.le m n -> 
                           stepE e (e_val (vint m)) -> stepE e' (e_val (vint n)) ->
                           stepE (e_gt e e') (e_val (vbool true)) 
  | ec_plus  : forall e e' m n, stepE e (e_val (vint n)) -> stepE e' (e_val (vint m)) -> 
                           stepE (e_plus e e') (e_val (vint (n + m)))
  | ec_detl  : forall m n v, stepE m v -> stepE (e_det m n) v
  | ec_detr  : forall m n v, stepE n v -> stepE (e_det m n) v
  | ec_refl  : forall e, stepE e e
  | ec_trans : forall e e' e'', stepE e e' -> stepE e' e'' -> stepE e e''.

   
Lemma expr_typ_step : forall Gs e e' S, typ_expr Gs e S -> stepE e e' -> typ_expr Gs e' S.
Proof.
  intros. revert H. revert S. induction H0; intros; try easy.
  - specialize(inv_expr_succ Gs (e_succ e) S e H (eq_refl (e_succ e))); intros.
    destruct H1. destruct H2; subst.
    apply sc_valn.
    apply sc_sub with (s := snat). apply sc_valn. apply sni.
  - specialize(inv_expr_neg Gs (e_neg e) S e H (eq_refl (e_neg e))); intros.
    destruct H1. subst. apply sc_vali.
  - specialize(inv_expr_not Gs (e_not e) S e H (eq_refl (e_not e))); intros.
    destruct H1. subst. apply sc_valb.
    specialize(inv_expr_not Gs (e_not e) S e H (eq_refl (e_not e))); intros.
    destruct H1. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (eq_refl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (eq_refl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_plus Gs (e_plus e e') S e e' H (eq_refl (e_plus e e'))); intros.
    destruct H0. destruct H1. subst. apply sc_vali.
  - specialize(inv_expr_det Gs (e_det m n) S m n H (eq_refl (e_det m n))); intros.
    destruct H1. destruct H1. destruct H2.
    apply sc_sub with (s := x); intros; try easy. apply IHstepE; try easy.
  - specialize(inv_expr_det Gs (e_det m n) S m n H (eq_refl (e_det m n))); intros.
    destruct H1. destruct H1. destruct H2.
    apply sc_sub with (s := x); intros; try easy. apply IHstepE; try easy.
  - specialize(IHstepE1 S H). specialize(IHstepE2 S). apply IHstepE2; try easy.
Qed.
