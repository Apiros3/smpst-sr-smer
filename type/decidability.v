From SST Require Export type.global type.local type.isomorphism type.projection type.merge.
Require Import List String Datatypes ZArith Relations PeanoNat. 
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes Coq.Logic.Decidable.

Lemma decidable_isgParts : forall G pt, decidable (isgParts pt G).
Proof.
  induction G using global_ind_ref; intros.
  - unfold decidable. right. easy.
  - unfold decidable. right. easy.
  - revert H. induction lis; intros; try easy.
    unfold decidable.
    - case_eq (eqb pt p); intros.
      assert (pt = p). apply eqb_eq; try easy. subst. left. constructor.
    - case_eq (eqb pt q); intros.
      assert (pt = q). apply eqb_eq; try easy. subst. left. constructor.
    - assert (pt <> p). apply eqb_neq; try easy. 
      assert (pt <> q). apply eqb_neq; try easy.
      right. unfold not. intros. inversion H4; try easy. subst. destruct n; try easy.
    inversion H. subst. specialize(IHlis H3). clear H3 H.
    unfold decidable in *.
    destruct IHlis. left. 
    - inversion H. subst. constructor. constructor. subst.
      apply pa_sendr with (n := S n) (s := s) (g := g); try easy.
    - unfold not in *. 
      destruct H2. subst. right. intros. apply H. inversion H0; try easy.
      constructor. constructor. subst.
      destruct n; try easy.
      apply pa_sendr with (n := n) (s := s) (g := g); try easy. 
    - destruct H0 as (s,(g,(Ha,Hb))). subst.
    - case_eq (eqb pt p); intros.
      assert (pt = p). apply eqb_eq; try easy. subst. left. constructor.
    - case_eq (eqb pt q); intros.
      assert (pt = q). apply eqb_eq; try easy. subst. left. constructor.
    - assert (pt <> p). apply eqb_neq; try easy. 
      assert (pt <> q). apply eqb_neq; try easy.
    - specialize(Hb pt). destruct Hb. left. 
      apply pa_sendr with (n := 0) (s := s) (g := g); try easy.
      right. intros. inversion H5; try easy. subst. 
      destruct n. simpl in H12. inversion H12. subst. apply H4. easy.
      apply H.
      apply pa_sendr with (n := n) (s := s0) (g := g0); try easy.
  - unfold decidable. specialize(IHG pt). destruct IHG. left. constructor. easy.
    right. unfold not in *. intros. apply H. inversion H0; try easy.
Qed.

Lemma part_betaG : forall G G' pt, multiS betaG G G' -> isgParts pt G -> isgParts pt G'.
Proof.
  intros.
  specialize(isgParts_depth_exists pt G H0); intros. destruct H1 as (n, H1). clear H0.
  revert H1. revert pt n.
  induction H; intros.
  - inversion H. subst.
    inversion H1. subst.
    specialize(subst_parts_depth 0 0 n0 pt G G y H0 H5); intros.
    specialize(isgParts_depth_back y n0 pt H2); intros. easy.
  - inversion H. subst.
    inversion H1. subst.
    specialize(subst_parts_depth 0 0 n0 pt G G y H2 H6); intros.
    specialize(isgParts_depth_back y n0 pt H3); intros.
    specialize(isgParts_depth_exists pt y H4); intros. destruct H5 as (n1, H5).
    specialize(IHmultiS pt n1). apply IHmultiS; try easy.
Qed.

Lemma subst_part_b : forall m n G G1 G2 pt,
    isgParts pt G2 -> 
    subst_global m n G G1 G2 -> 
    (isgParts pt G \/ isgParts pt G1).
    


Lemma part_betaG_b : forall G G' pt, multiS betaG G G' -> isgParts pt G' -> isgParts pt G.
Proof.
  intros.
  specialize(isgParts_depth_exists pt G' H0); intros. destruct H1 as (n, H1). clear H0.
  revert H1. revert pt n.
  induction H; intros.
  - inversion H. subst.
    specialize(subst_parts_depth 0 0 n pt G G y H0); intros.
    specialize(isgParts_depth_back y n0 pt H2); intros. easy.
  - inversion H. subst.
    inversion H1. subst.
    specialize(subst_parts_depth 0 0 n0 pt G G y H2 H6); intros.
    specialize(isgParts_depth_back y n0 pt H3); intros.
    specialize(isgParts_depth_exists pt y H4); intros. destruct H5 as (n1, H5).
    specialize(IHmultiS pt n1). apply IHmultiS; try easy.
Qed.

Lemma decidable_isgPartsC : forall G pt, wfgC G -> decidable (isgPartsC pt G).
Proof.
  intros. unfold decidable. pose proof H as Ht.
  unfold wfgC in H.
  destruct H as (G',(Ha,(Hb,(Hc,Hd)))). 
  specialize(decidable_isgParts G' pt); intros. unfold decidable in H.
  destruct H. left. unfold isgPartsC. exists G'. easy.
  right. unfold not in *. intros. apply H.
  clear H Ht.
  unfold isgPartsC in H0. destruct H0 as (Gl,(He,(Hf,Hg))).
  specialize(isgParts_depth_exists pt Gl Hg); intros. destruct H as (n, H). clear Hg.
  clear Hd Hb. revert Ha Hc He Hf H.
  revert G pt G' Gl.
  induction n; intros.
  - inversion H. subst. pinversion He; try easy. subst.
    - pinversion Ha. subst. constructor. subst. clear H0 H1.
      specialize(guard_breakG G Hc); intros. 
      destruct H0 as (T,(Hta,(Htb,Htc))).
      specialize(gttTC_after_subst (g_rec G) T (gtt_send pt q ys)); intros.
    - assert(gttTC T (gtt_send pt q ys)). apply H0; try easy. pfold. easy. clear H0.
      specialize(part_betaG (g_rec G) T pt); intros.
    
Admitted.
  
  
  
  
  
  