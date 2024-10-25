From mathcomp Require Import ssreflect.seq all_ssreflect.
From Paco Require Import paco pacotac.
From SST Require Export src.expressions src.header type.global type.local type.isomorphism.
Require Import List String Coq.Arith.PeanoNat Relations Coq.Logic.Decidable.
Import ListNotations. 

Inductive isgParts : part -> global -> Prop := 
  | pa_sendp : forall p q l, isgParts p (g_send p q l)
  | pa_sendq : forall p q l, isgParts q (g_send p q l)
  | pa_mu    : forall p g,   isgParts p g -> isgParts p (g_rec g)
  | pa_sendr : forall p q r n s g lis, p <> r -> q <> r -> onth n lis = Some (s, g) -> isgParts r g -> isgParts r (g_send p q lis).
  
Definition isgPartsC (pt : part) (G : gtt) : Prop := 
    exists G', gttTC G' G /\ (forall n, exists m, guardG n m G') /\ isgParts pt G'.


Lemma triv_pt_p : forall p q x0,
    wfgC (gtt_send p q x0) -> 
    isgPartsC p (gtt_send p q x0).
Proof.
  intros. unfold wfgC in H.
  destruct H. destruct H. destruct H0. destruct H1.
  unfold isgPartsC in *.
  pinversion H; try easy. 
  - subst. exists (g_send p q xs). split. pfold. easy. split. easy. constructor.
  - subst. specialize(guard_breakG G H1); intros. 
    destruct H5. destruct H5. destruct H6.
   
    destruct H7.
    - subst. 
      specialize(gttTC_after_subst (g_rec G) g_end (gtt_send p q x0) H5); intros.
      assert(gttTC g_end (gtt_send p q x0)). 
      apply H7. pfold. easy. pinversion H8. 
      apply gttT_mon.
    destruct H7. destruct H7. destruct H7.
    - subst.
      specialize(gttTC_after_subst (g_rec G) (g_send x1 x2 x3) (gtt_send p q x0) H5); intros.
      assert(gttTC (g_send x1 x2 x3) (gtt_send p q x0)).
      apply H7. pfold. easy.
      pinversion H8. subst.
      exists (g_send p q x3). split; try easy. pfold. easy. split. easy.
      constructor.
    apply gttT_mon.
    apply gttT_mon.
Qed.


Lemma triv_pt_q : forall p q x0,
    wfgC (gtt_send p q x0) -> 
    isgPartsC q (gtt_send p q x0).
Proof.
  intros. unfold wfgC in H.
  destruct H. destruct H. destruct H0. destruct H1.
  unfold isgPartsC in *.
  pinversion H; try easy. 
  - subst. exists (g_send p q xs). split. pfold. easy. constructor. easy. constructor.
  - subst. specialize(guard_breakG G H1); intros. 
    destruct H5. destruct H5. destruct H6.
   
    destruct H7.
    - subst. 
      specialize(gttTC_after_subst (g_rec G) g_end (gtt_send p q x0) H5); intros.
      assert(gttTC g_end (gtt_send p q x0)). 
      apply H7. pfold. easy. pinversion H8. 
      apply gttT_mon.
    destruct H7. destruct H7. destruct H7.
    - subst.
      specialize(gttTC_after_subst (g_rec G) (g_send x1 x2 x3) (gtt_send p q x0) H5); intros.
      assert(gttTC (g_send x1 x2 x3) (gtt_send p q x0)).
      apply H7. pfold. easy.
      pinversion H8. subst.
      exists (g_send p q x3). split; try easy. pfold. easy. 
      split. easy. constructor.
    apply gttT_mon.
    apply gttT_mon.
Qed.

Lemma isgParts_xs : forall [s s' x o p],
    isgParts p (g_send s s' x) ->
    isgParts p (g_send s s' (o :: x)).
Proof.
  intros. inversion H. subst. 
  constructor. 
  subst. constructor.
  subst. apply pa_sendr with (n := Nat.succ n) (s := s0) (g := g); try easy.
Qed.


Lemma isgParts_x : forall [s s' x s0 g p],
    isgParts p g -> 
    isgParts p (g_send s s' (Some (s0, g) :: x)).
Proof.
    intros.
    - case_eq (eqb p s); intros.
      assert (p = s). apply eqb_eq; try easy. subst. apply pa_sendp.
    - case_eq (eqb p s'); intros.
      assert (p = s'). apply eqb_eq; try easy. subst. apply pa_sendq.
    - assert (p <> s). apply eqb_neq; try easy. 
      assert (p <> s'). apply eqb_neq; try easy.
      apply pa_sendr with (n := 0) (s := s0) (g := g); try easy.
Qed.

Inductive isgParts_depth : fin -> part -> global -> Prop := 
  | dpth_p : forall p q lis, isgParts_depth 0 p (g_send p q lis)
  | dpth_q : forall p q lis, isgParts_depth 0 q (g_send p q lis)
  | dpth_mu : forall n pt g, isgParts_depth n pt g -> isgParts_depth (S n) pt (g_rec g)
  | dpth_c : forall p q pt s g lis n k, p <> pt -> q <> pt -> onth k lis = Some(s, g) -> isgParts_depth n pt g -> isgParts_depth (S n) pt (g_send p q lis).


Lemma isgParts_depth_exists : forall r Gl,
    isgParts r Gl -> exists n, isgParts_depth n r Gl.
Proof.
  induction Gl using global_ind_ref; intros; try easy.
  inversion H0.
  - subst. exists 0. constructor.
  - subst. exists 0. constructor.
  - subst. 
    specialize(some_onth_implies_In n lis (s, g) H7); intros.
    specialize(Forall_forall (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\
          (isgParts r g -> exists n : fin, isgParts_depth n r g))) lis); intros.
    destruct H2. specialize(H2 H). clear H H3.
    specialize(H2 (Some (s, g)) H1).
    destruct H2; try easy. destruct H. destruct H. destruct H. inversion H. subst. clear H.
    specialize(H2 H8). destruct H2.
    exists (S x1). apply dpth_c with (s := x) (g := x0) (k := n); try easy.
  - inversion H. subst. specialize(IHGl H2). destruct IHGl. exists (S x). constructor. easy.
Qed.

Lemma isgParts_depth_back : forall G n r,
      isgParts_depth n r G -> isgParts r G.
Proof.
  induction G using global_ind_ref; intros; try easy.
  inversion H0. 
  - subst. constructor.
  - subst. constructor.
  - subst. 
    specialize(some_onth_implies_In k lis (s, g) H8); intros.
    specialize(Forall_forall (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\
          (forall (n : fin) (r : string),
           isgParts_depth n r g -> isgParts r g))) lis); intros.
    destruct H2. specialize(H2 H). clear H H3.
    specialize(H2 (Some (s, g)) H1). destruct H2; try easy. destruct H. destruct H. destruct H.
    inversion H. subst.
    specialize(H2 n0 r H9). 
    apply pa_sendr with (n := k) (s := x) (g := x0); try easy.
  inversion H. subst.
  - specialize(IHG n0 r H3). constructor. easy.
Qed.


Lemma subst_parts_helper : forall k0 xs s g0 r n0 lis m n g,
      onth k0 xs = Some (s, g0) -> 
      isgParts_depth n0 r g0 ->
      Forall2
       (fun u v : option (sort * global) =>
        u = None /\ v = None \/
        (exists (s : sort) (g0 g' : global),
           u = Some (s, g0) /\ v = Some (s, g') /\ subst_global m n (g_rec g) g0 g')) xs lis -> 
      Forall
      (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\
          (forall (m n k : fin) (r : string) (g0 g' : global),
           isgParts_depth k r g' -> subst_global m n (g_rec g0) g' g -> isgParts_depth k r g))) lis -> 
      exists g', onth k0 lis = Some (s, g') /\ isgParts_depth n0 r g'.
Proof.
  induction k0; intros; try easy.
  - destruct xs; try easy.
    simpl in H. subst. destruct lis; try easy. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    clear H4 H7. destruct H5; try easy. destruct H. destruct H. destruct H. destruct H.
    destruct H1. inversion H. subst.
    destruct H3; try easy. destruct H1. destruct H1. destruct H1. inversion H1. subst.
    specialize(H3 m n n0 r g x0 H0 H2).
    exists x3. split; try easy.
  - destruct xs; try easy. destruct lis; try easy. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    specialize(IHk0 xs s g0 r n0 lis m n g). apply IHk0; try easy.
Qed.

Lemma subst_parts_depth : forall m n k r g g' Q,
      subst_global m n (g_rec g) g' Q -> 
      isgParts_depth k r g' -> 
      isgParts_depth k r Q.
Proof.
  intros. revert H0 H. revert m n k r g g'.
  induction Q using global_ind_ref; intros; try easy.
  inversion H.
  - subst. inversion H0; try easy.
  - subst. inversion H0; try easy. 
  - subst. inversion H0; try easy.
  - inversion H. subst. inversion H0. 
  - inversion H1. subst.
    inversion H0. 
    - subst. constructor.
    - subst. constructor.
    - subst. 
      specialize(subst_parts_helper k0 xs s g0 r n0 lis m n g H10 H11 H7 H); intros. 
      destruct H2. destruct H2.
      apply dpth_c with (n := n0) (s := s) (g := x) (k := k0); try easy.
  - inversion H. subst. inversion H0. 
  - subst. inversion H0. subst.
    constructor. specialize(IHQ m.+1 n.+1 n0 r g P). apply IHQ; try easy.
Qed.


Lemma part_after_step_helper : forall G1 q p x0,
    gttTC G1 (gtt_send q p x0) -> 
    (forall n : fin, exists m : fin, guardG n m G1) -> 
    exists ys, gttTC (g_send q p ys) (gtt_send q p x0) /\ (forall n : fin, exists m : fin, guardG n m (g_send q p ys)).
Proof.
  intros. pinversion H; try easy. subst.
  - exists xs. split. pfold. easy. easy.
  - subst. specialize(guard_breakG G H0); intros.
    destruct H3. destruct H3. destruct H4.
    specialize(gtt_after_betaL (g_rec G) x (gtt_send q p x0)); intros.
    assert(gttTC x (gtt_send q p x0)). 
    apply H6; try easy. pfold. easy.
    destruct H5. pinversion H7; try easy. subst. easy. subst. easy.
    apply gttT_mon.
    destruct H5. destruct H5. destruct H5. subst.
    pinversion H7; try easy. subst. exists x3. split. pfold. easy. easy.
    apply gttT_mon.
    apply gttT_mon.
Qed.

Lemma part_break_s : forall G pt, 
    isgPartsC pt G -> 
    exists Gl, gttTC Gl G /\ isgParts pt Gl /\ (Gl = g_end \/ exists p q lis, Gl = g_send p q lis).
Proof.
  intros. pose proof H as H0.
  unfold isgPartsC in H0. destruct H0. destruct H0.
  rename x into Gl. destruct H1.
  specialize(isgParts_depth_exists pt Gl H2); intros. destruct H3. rename x into n.
  
  clear H.
  clear H2.
  revert H3 H0 H1. revert G pt Gl.
  induction n; intros; try easy.
  - inversion H3. subst.
    exists (g_send pt q lis). split. easy. split. constructor. right. exists pt. exists q. exists lis. easy.
  - subst.
    exists (g_send p pt lis). split. easy. split. constructor. right. exists p. exists pt. exists lis. easy.
  - inversion H3. subst.
    pinversion H0. subst.
    specialize(subst_parts_depth 0 0 n pt g g Q H4 H2); intros.
    apply IHn with (Gl := Q); try easy.
    - intros. specialize(H1 n0). destruct H1. 
      inversion H1. exists 0. constructor.
      subst. exists m. specialize(subst_injG 0 0 (g_rec g) g Q Q0 H7 H4); intros. subst. easy.
    apply gttT_mon.
  - subst. 
    exists (g_send p q lis). split. easy.
    split.
    apply pa_sendr with (n := k) (s := s) (g := g); try easy.
    apply isgParts_depth_back with (n := n); try easy.
    right. exists p. exists q. exists lis. easy.
Qed.

Lemma part_break_s2 : forall G pt, 
    isgPartsC pt G -> 
    exists Gl, gttTC Gl G /\ isgParts pt Gl /\ (forall n : fin, exists m : fin, guardG n m Gl) /\ (Gl = g_end \/ exists p q lis, Gl = g_send p q lis).
Proof.
  intros. pose proof H as H0.
  unfold isgPartsC in H0. destruct H0. destruct H0.
  rename x into Gl. destruct H1.
  specialize(isgParts_depth_exists pt Gl H2); intros. destruct H3. rename x into n.
  
  clear H.
  clear H2.
  revert H3 H0 H1. revert G pt Gl.
  induction n; intros; try easy.
  - inversion H3. subst.
    exists (g_send pt q lis). split. easy. split. constructor. split. easy. right. exists pt. exists q. exists lis. easy.
  - subst.
    exists (g_send p pt lis). split. easy. split. constructor. split. easy. right. exists p. exists pt. exists lis. easy.
  - inversion H3. subst.
    pinversion H0. subst.
    specialize(subst_parts_depth 0 0 n pt g g Q H4 H2); intros.
    apply IHn with (Gl := Q); try easy.
    - intros. specialize(H1 n0). destruct H1. 
      inversion H1. exists 0. constructor.
      subst. exists m. specialize(subst_injG 0 0 (g_rec g) g Q Q0 H7 H4); intros. subst. easy.
    apply gttT_mon.
  - subst. 
    exists (g_send p q lis). split. easy.
    split.
    apply pa_sendr with (n := k) (s := s) (g := g); try easy.
    apply isgParts_depth_back with (n := n); try easy. split. easy.
    right. exists p. exists q. exists lis. easy.
Qed.

Lemma part_break : forall G pt,
    wfgC G -> 
    isgPartsC pt G -> 
    exists Gl, gttTC Gl G /\ isgParts pt Gl /\ (forall n : fin, exists m : fin, guardG n m Gl) /\ (Gl = g_end \/ exists p q lis, Gl = g_send p q lis).
Proof.
  intros. 
  unfold isgPartsC in H0. destruct H0. destruct H0.
  rename x into Gl. destruct H1.
  specialize(isgParts_depth_exists pt Gl H2); intros. destruct H3. rename x into n.
  
  clear H.
  clear H2.
  revert H3 H0 H1. revert G pt Gl.
  induction n; intros; try easy.
  - inversion H3. subst.
    exists (g_send pt q lis). split. easy. split. constructor. split. easy. right. exists pt. exists q. exists lis. easy.
  - subst.
    exists (g_send p pt lis). split. easy. split. constructor. split. easy. right. exists p. exists pt. exists lis. easy.
  - inversion H3. subst.
    pinversion H0. subst.
    specialize(subst_parts_depth 0 0 n pt g g Q H4 H2); intros.
    apply IHn with (Gl := Q); try easy.
    - intros. specialize(H1 n0). destruct H1. 
      inversion H1. exists 0. constructor.
      subst. exists m. specialize(subst_injG 0 0 (g_rec g) g Q Q0 H7 H4); intros. subst. easy.
    apply gttT_mon.
  - subst. 
    exists (g_send p q lis). split. easy.
    split.
    apply pa_sendr with (n := k) (s := s) (g := g); try easy.
    apply isgParts_depth_back with (n := n); try easy. split. easy.
    right. exists p. exists q. exists lis. easy.
Qed.


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

Lemma subst_after_incrG_b : forall G G' m n pt,
    isgParts pt G' -> incr_freeG m n G = G' -> isgParts pt G.
Proof.
  induction G using global_ind_ref; intros; try easy.
  - subst. inversion H; try easy.
  - subst. inversion H; try easy.
  - subst. 
    inversion H0; try easy. subst. constructor. subst. constructor.
    subst.
    assert(exists g', onth n0 lis = Some(s, g') /\ g = incr_freeG m n g').
    {
      clear H8 H6 H4 H0 H. revert H7. revert lis.
      induction n0; intros; try easy. destruct lis; try easy. simpl in H7.
      destruct o; try easy. destruct p0; try easy. inversion H7. subst.
      exists g0. easy.
      destruct lis; try easy. specialize(IHn0 lis H7). apply IHn0; try easy.
    }
    destruct H1 as (g1,(Ha,Hb)). 
    specialize(Forall_forall (fun u : option (sort * global) =>
       u = None \/
       (exists (s : sort) (g : global),
          u = Some (s, g) /\
          (forall (G' : global) (m n : fin) (pt : string),
           isgParts pt G' -> incr_freeG m n g = G' -> isgParts pt g))) lis); intros.
    destruct H1. specialize(H1 H). clear H2 H.
    specialize(some_onth_implies_In n0 lis (s, g1) Ha); intros.
    specialize(H1 (Some (s, g1)) H). destruct H1; try easy. 
    destruct H1 as (s0,(g2,(Hd,He))). inversion Hd. subst.
    specialize(He (incr_freeG m n g2) m n pt).
    apply pa_sendr with (n := n0) (s := s0) (g := g2); try easy. 
    apply He; try easy.
  - subst. inversion H. subst.
    specialize(IHG (incr_freeG m.+1 n G) (S m) n pt). 
    constructor. apply IHG; try easy.
Qed.

Lemma subst_part_b : forall m n G G1 G2 pt,
    isgParts pt G2 -> 
    subst_global m n G G1 G2 -> 
    (isgParts pt G \/ isgParts pt G1).
Proof.
  intros. revert H0 H. revert pt m n G G1.
  induction G2 using global_ind_ref; intros; try easy.
  - inversion H0.
    - subst. left.
      specialize(subst_after_incrG_b G (g_send p q lis) 0 n pt); intros.
      apply H2; try easy.
    - subst.
      inversion H1.
      - subst. right. constructor.
      - subst. right. constructor.
      subst.
      revert H10 H9 H8 H5 H7 H. clear H0 H1.
      revert p q lis pt m n G xs s g.
      induction n0; intros; try easy.
      - destruct lis; try easy. destruct xs; try easy. 
        inversion H7. subst. clear H7. inversion H. subst. clear H.
        simpl in H9. subst. 
        destruct H3; try easy. destruct H as (s0,(g1,(g2,(Ha,(Hb,Hc))))). inversion Hb. subst.
        destruct H2; try easy. destruct H as (s1,(g3,(Hd,He))). inversion Hd. subst.
        specialize(He pt m n G g1 Hc H10).
        destruct He. left. easy.
        right. apply pa_sendr with (n := 0) (s := s1) (g := g1); try easy.
      - destruct lis; try easy. destruct xs; try easy. 
        inversion H7. subst. clear H7. inversion H. subst. clear H.
        specialize(IHn0 p q lis pt m n G xs s g).
        assert(isgParts pt G \/ isgParts pt (g_send p q xs)). apply IHn0; try easy.
        destruct H. left. easy.
        right. inversion H; try easy. subst. easy. subst. easy.
        subst.
        apply pa_sendr with (n := S n1) (s := s0) (g := g0); try easy.
    - inversion H0. subst.
      - specialize(subst_after_incrG_b G (g_rec G2) 0 n pt); intros.
        left. apply H1; try easy.
      - subst. inversion H. subst.
        specialize(IHG2 pt (S m) (S n) G P H6 H3). 
        destruct IHG2. left. easy. right. constructor. easy.
Qed.


Lemma part_betaG_b : forall G G' pt, multiS betaG G G' -> isgParts pt G' -> isgParts pt G.
Proof.
  intros.
  specialize(isgParts_depth_exists pt G' H0); intros. destruct H1 as (n, H1). clear H0.
  revert H1. revert pt n.
  induction H; intros.
  - inversion H. subst.
    specialize(subst_parts_depth 0 0 n pt G G y H0); intros.
    specialize(subst_part_b 0 0 (g_rec G) G y pt); intros.
    specialize(isgParts_depth_back y n pt H1); intros.
    constructor.
    assert(isgParts pt (g_rec G) \/ isgParts pt G). apply H3; try easy.
    destruct H5; try easy. inversion H5; try easy.
  - inversion H. subst.
    specialize(IHmultiS pt n H1). clear H1 H0 H.
    specialize(subst_part_b 0 0 (g_rec G) G y pt); intros. 
    assert(isgParts pt (g_rec G) \/ isgParts pt G).
    apply H; try easy. destruct H0; try easy. constructor; try easy.
Qed.

Lemma guardG_betaG : forall G G1,
          (forall n : fin, exists m : fin, guardG n m G) -> 
          multiS betaG G G1 -> 
          (forall n : fin, exists m : fin, guardG n m G1).
Proof.  
  intros. revert n. revert H. 
  induction H0; intros; try easy.
  - inversion H. subst.
    specialize(H0 n). destruct H0. inversion H0. subst. exists 0. constructor.
    subst. specialize(subst_injG 0 0 (g_rec G) G y Q H3 H1); intros. subst. exists m. easy.
  - revert n. apply IHmultiS. clear IHmultiS H0.
    inversion H. subst. intros.
    specialize(H1 n). destruct H1. inversion H1. exists 0. constructor.
    subst. specialize(subst_injG 0 0 (g_rec G) G y Q H3 H0); intros. subst. exists m. easy.
Qed.

Lemma decidable_isgPartsC_helper : forall k lis s g ys xs,
          onth k lis = Some (s, g) -> 
          Forall2
           (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
            u = None /\ v = None \/
            (exists (s : sort) (g : global) (g' : gtt),
               u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) lis ys ->
          Forall
           (fun u : option (sort * global) =>
            u = None \/
            (exists (s : sort) (g : global),
               u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) lis ->
          Forall2
           (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
            u = None /\ v = None \/
            (exists (s : sort) (g : global) (g' : gtt),
               u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) xs ys ->
          Forall
           (fun u : option (sort * global) =>
            u = None \/
            (exists (s : sort) (g : global),
               u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) xs -> 
          exists g' g'', onth k ys = Some(s, g') /\ gttTC g g' /\
          (forall n : fin, exists m : fin, guardG n m g) /\
          onth k xs = Some(s, g'') /\ gttTC g'' g' /\ 
          (forall n : fin, exists m : fin, guardG n m g'').
Proof.
  induction k; intros; try easy.
  - destruct lis; try easy. destruct ys; try easy. destruct xs; try easy.
    inversion H0. subst. clear H0. inversion H2. subst. clear H2.
    inversion H1. subst. clear H1. inversion H3. subst. clear H3.
    simpl in H. subst.
    destruct H4; try easy. destruct H as (s1,(g1,(Ha,Hb))). inversion Ha. subst.
    destruct H7; try easy. destruct H as (s2,(g2,(g3,(Hc,(Hd,He))))). inversion Hc. subst.
    destruct H6; try easy. destruct H as (s3,(g4,(g5,(Hf,(Hg,Hh))))). inversion Hg. subst.
    destruct H2; try easy. destruct H as (s4,(g6,(Hi,Hj))). inversion Hi. subst.
    simpl. exists g5. exists g6. pclearbot. easy.
  - destruct lis; try easy. destruct ys; try easy. destruct xs; try easy.
    inversion H0. subst. clear H0. inversion H2. subst. clear H2.
    inversion H1. subst. clear H1. inversion H3. subst. clear H3.
    specialize(IHk lis s g ys xs). apply IHk; try easy.
Qed.

Lemma decidable_isgPartsC_s : forall G pt, wfgCw G -> decidable (isgPartsC pt G).
Proof.
  intros. unfold decidable. pose proof H as Ht.
  unfold wfgCw in H.
  destruct H as (G',(Ha,(Hb,Hc))). 
  specialize(decidable_isgParts G' pt); intros. unfold decidable in H.
  destruct H. left. unfold isgPartsC. exists G'. easy.
  right. unfold not in *. intros. apply H.
  clear H Ht.
  unfold isgPartsC in H0. destruct H0 as (Gl,(He,(Hf,Hg))).
  specialize(isgParts_depth_exists pt Gl Hg); intros. destruct H as (n, H). clear Hg.
  clear Hb. revert Ha Hc He Hf H.
  revert G pt G' Gl.
  induction n; intros.
  - inversion H. subst. pinversion He; try easy. subst.
    - pinversion Ha. subst. constructor. subst. clear H0 H1.
      specialize(guard_breakG G Hc); intros. 
      destruct H0 as (T,(Hta,(Htb,Htc))).
      specialize(gttTC_after_subst (g_rec G) T (gtt_send pt q ys)); intros.
    - assert(gttTC T (gtt_send pt q ys)). apply H0; try easy. pfold. easy. clear H0.
      specialize(part_betaG_b (g_rec G) T pt); intros. apply H0; try easy.
      destruct Htc. subst. pinversion H1; try easy. apply gttT_mon.
      destruct H2 as (p1,(q1,(lis1,Hl))). subst. pinversion H1; try easy. subst.
      constructor.
      apply gttT_mon. apply gttT_mon. apply gttT_mon.
    - subst. 
      pinversion He; try easy. subst.
      pinversion Ha. subst. constructor.
      subst. clear H0 H1.
      specialize(guard_breakG G Hc); intros.
      destruct H0 as (T1,(Hta,(Htb,Htc))).
      specialize(part_betaG_b (g_rec G) T1 pt); intros. apply H0; try easy.
      clear H0.
      specialize(gttTC_after_subst (g_rec G) T1 (gtt_send p pt ys)); intros.
      assert(gttTC T1 (gtt_send p pt ys)). apply H0; try easy. pfold. easy.
      clear H0. 
      destruct Htc. subst. pinversion H1; try easy. apply gttT_mon.
      destruct H0 as (p1,(q1,(lis1,Htc))). subst. pinversion H1; try easy. subst. 
      constructor.
      apply gttT_mon.
      apply gttT_mon. apply gttT_mon.
    - inversion H. 
      - subst.
        pinversion He; try easy. subst.
        specialize(subst_parts_depth 0 0 n pt g g Q H2 H1); intros.
        specialize(IHn G pt G' Q). apply IHn; try easy.
        intros. specialize(Hf n0). destruct Hf. 
        - inversion H4. subst. exists 0. constructor.
        - subst. specialize(subst_injG 0 0 (g_rec g) g Q Q0 H6 H2); intros. subst.
          exists m. easy.
        apply gttT_mon.
      - subst.
        pinversion He; try easy. subst.
        specialize(guard_cont Hf); intros.
        pinversion Ha; try easy.
        - subst.
          specialize(guard_cont Hc); intros.
          specialize(decidable_isgPartsC_helper k lis s g ys xs); intros.
          assert(exists (g' : gtt) (g'' : global),
       onth k ys = Some (s, g') /\
       gttTC g g' /\
       (forall n : fin, exists m : fin, guardG n m g) /\
       onth k xs = Some (s, g'') /\ gttTC g'' g' /\ (forall n : fin, exists m : fin, guardG n m g'')).
          apply H6; try easy. clear H6.
          clear H8 H0 H7 H5. destruct H9 as (g1,(g2,(Hg,(Hh,(Hi,(Hj,(Hk,Hl))))))).
          specialize(IHn g1 pt g2 g).
          assert(isgParts pt g2). apply IHn; try easy.
          apply pa_sendr with (n := k) (s := s) (g := g2); try easy.
        - subst. clear H5 H6. clear Q.
          specialize(guard_breakG G Hc); intros.
          destruct H5 as (T1,(Hta,(Htb,Htc))).
          specialize(gttTC_after_subst (g_rec G) T1 (gtt_send p q ys)); intros.
          assert(gttTC T1 (gtt_send p q ys)). apply H5; try easy. pfold. easy.
          clear H5. destruct Htc. subst. pinversion H6. apply gttT_mon.
          destruct H5 as (p1,(q1,(lis1,Htc))). subst. pinversion H6. subst.
          specialize(part_betaG_b (g_rec G) (g_send p q lis1) pt); intros. apply H5; try easy.
          clear H5 Htb.
          specialize(guardG_betaG (g_rec G) (g_send p q lis1)); intros.
          assert(forall n : fin, exists m : fin, guardG n m (g_send p q lis1)). apply H5; try easy.
          clear H5.
          specialize(guard_cont H9); intros.
          specialize(decidable_isgPartsC_helper k lis s g ys lis1); intros.
          assert(exists (g' : gtt) (g'' : global),
        onth k ys = Some (s, g') /\
        gttTC g g' /\
        (forall n : fin, exists m : fin, guardG n m g) /\
        onth k lis1 = Some (s, g'') /\ gttTC g'' g' /\ (forall n : fin, exists m : fin, guardG n m g'')).
          apply H10; try easy. clear H10.
          destruct H11 as (g1,(g2,(Hg,(Hh,(Hi,(Hj,(Hk,Hl))))))).
          specialize(IHn g1 pt g2 g).
          assert(isgParts pt g2). apply IHn; try easy.
          apply pa_sendr with (n := k) (s := s) (g := g2); try easy.
      apply gttT_mon.
      apply gttT_mon. 
      apply gttT_mon.
Qed.

Lemma decidable_isgPartsC : forall G pt, wfgC G -> decidable (isgPartsC pt G).
Proof.
  intros.
  apply decidable_isgPartsC_s; try easy.
  unfold wfgC in *. unfold wfgCw. 
  destruct H. exists x. easy.
Qed.



Lemma part_cont : forall ys r p q,
    isgPartsC r (gtt_send p q ys) -> 
    r <> p -> r <> q ->
    exists n s g, onth n ys = Some(s, g) /\ isgPartsC r g.
Proof.
  induction ys; intros; try easy.
  - specialize(part_break_s (gtt_send p q []) r H); intros.
    destruct H2 as (Gl,(Ha,(Hb,Hc))). 
    destruct Hc. subst. pinversion Ha; try easy. 
    destruct H2 as (p1,(q1,(lis,Hc))). subst. pinversion Ha; try easy. subst. destruct lis; try easy.
    inversion Hb.
    - subst. easy. 
    - subst. easy.
    - destruct n; try easy.
    apply gttT_mon.
  - specialize(part_break_s2 (gtt_send p q (a :: ys)) r H); intros.
    destruct H2 as (Gl,(Ha,(Hb,(Hc,Hd)))). 
    destruct Hd. subst. pinversion Ha; try easy. 
    destruct H2 as (p1,(q1,(lis,He))). subst. pinversion Ha; try easy. subst. destruct lis; try easy.
    inversion H3. subst. clear H3.
    inversion Hb; try easy. subst.
    destruct n.
    - simpl in H10. subst.
      destruct H6; try easy. destruct H2 as (s1,(g1,(g2,(Hsa,(Hsb,Hsc))))). inversion Hsa. subst.
      exists 0. exists s1. exists g2. split; try easy.
      unfold isgPartsC. exists g1. destruct Hsc; try easy. 
      specialize(guard_cont Hc); intros. inversion H3. subst.
      destruct H7; try easy. destruct H4 as (s2,(g3,(Hma,Hmb))). inversion Hma. subst.
      easy.
    - specialize(IHys r p q).
      assert(exists (n : fin) (s : sort) (g : gtt), onth n ys = Some (s, g) /\ isgPartsC r g).
      {
        apply IHys; try easy.
        unfold isgPartsC. exists (g_send p q lis).
        split. pfold. constructor; try easy.
        split. 
        apply guard_cont_b. specialize(guard_cont Hc); intros. inversion H2; try easy.
        apply pa_sendr with (n := n) (s := s) (g := g); try easy.
      }
      destruct H2. exists (S x). easy.
    apply gttT_mon.
Qed.
  

Lemma part_cont_b : forall n ys s g r p q,
    onth n ys = Some(s, g) ->
    isgPartsC r g ->
    r <> p -> r <> q -> 
    wfgC (gtt_send p q ys) -> 
    isgPartsC r (gtt_send p q ys).
Proof.
  intros.
  unfold wfgC in H3.
  destruct H3 as (Gl,(Ha,(Hb,(Hc,Hd)))).
  unfold isgPartsC in *. destruct H0 as (G1,(He,(Hf,Hg))).
  pinversion Ha; try easy.
  - subst.
    exists (g_send p q (overwrite_lis n (Some (s, G1)) xs)).
    specialize(guard_cont Hc); intros. clear Hc Ha Hb Hd.
    revert H0 H4 Hg Hf He H H1 H2. revert xs G1 r p q g s ys.
    induction n; intros; try easy.
    - destruct ys; try easy. destruct xs; try easy.
      inversion H0. subst. clear H0. inversion H4. subst. clear H4.
      simpl in H. subst. destruct H8; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
      inversion Hb. subst.
      destruct H6; try easy. destruct H as (s2,(g3,(Hi,Hh))). inversion Hi. subst.
      pclearbot.
      - split. pfold. constructor; try easy. constructor; try easy.
        right. exists s2. exists G1. exists g2.
        split. easy. split. easy. left. easy.
      - split. apply guard_cont_b. constructor; try easy. right.
        exists s2. exists G1. easy.
      - apply pa_sendr with (n := 0) (s := s2) (g := G1); try easy.
    - destruct ys; try easy. destruct xs; try easy.
      inversion H0. subst. clear H0. inversion H4. subst. clear H4.
      assert(gttTC (g_send p q (overwrite_lis n (Some (s, G1)) xs)) (gtt_send p q ys) /\
      (forall n0 : fin, exists m : fin, guardG n0 m (g_send p q (overwrite_lis n (Some (s, G1)) xs))) /\
      isgParts r (g_send p q (overwrite_lis n (Some (s, G1)) xs))).
      specialize(IHn xs G1 r p q g s ys). apply IHn; try easy. clear IHn.
      destruct H0 as (Hta,(Htb,Htc)).
      - split. pfold. constructor. 
        pinversion Hta; try easy. subst. constructor; try easy. apply gttT_mon.
      - split. apply guard_cont_b. specialize(guard_cont Htb); intros.
        constructor; try easy.
      - inversion Htc; try easy. subst.
        apply pa_sendr with (n := S n0) (s := s0) (g := g0); try easy.
  - subst.
    clear H0 H3.
    specialize(guard_breakG G Hc); intros.
    destruct H0 as (Gl,(Hh,(Hi,Hj))).
    specialize(gttTC_after_subst (g_rec G) Gl (gtt_send p q ys)); intros.
    assert(gttTC Gl (gtt_send p q ys)). apply H0; try easy. pfold. easy.
    clear H0. destruct Hj. subst. pinversion H3. apply gttT_mon.
    destruct H0 as (p1,(q1,(lis,Hj))). subst. pinversion H3; try easy. subst.
    specialize(guardG_betaG (g_rec G) (g_send p q lis)); intros.
    exists (g_send p q (overwrite_lis n (Some (s, G1)) lis)).
    clear H0 H3 Hh Hd Ha Hb Hc.
    specialize(guard_cont Hi); intros. clear Hi.
    revert H0 H4 H2 H1 Hg Hf He H.
    revert ys s g r p q G1 lis. clear G Q.
    induction n; intros; try easy.
    - destruct ys; try easy. destruct lis; try easy.
      inversion H0. subst. clear H0. inversion H4. subst. clear H4.
      simpl in H. subst. destruct H8; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))).
      inversion Hb. subst.
      destruct H6; try easy. destruct H as (s2,(g3,(Hi,Hh))). inversion Hi. subst.
      pclearbot.
      - split. pfold. constructor; try easy. constructor; try easy.
        right. exists s2. exists G1. exists g2.
        split. easy. split. easy. left. easy.
      - split. apply guard_cont_b. constructor; try easy. right.
        exists s2. exists G1. easy.
      - apply pa_sendr with (n := 0) (s := s2) (g := G1); try easy.
    - destruct ys; try easy. destruct lis; try easy.
      inversion H0. subst. clear H0. inversion H4. subst. clear H4.
      assert(gttTC (g_send p q (overwrite_lis n (Some (s, G1)) lis)) (gtt_send p q ys) /\
      (forall n0 : fin, exists m : fin, guardG n0 m (g_send p q (overwrite_lis n (Some (s, G1)) lis))) /\
      isgParts r (g_send p q (overwrite_lis n (Some (s, G1)) lis))).
      specialize(IHn ys s g r p q G1 lis). apply IHn; try easy. clear IHn.
      destruct H0 as (Hta,(Htb,Htc)).
      - split. pfold. constructor. 
        pinversion Hta; try easy. subst. constructor; try easy. apply gttT_mon.
      - split. apply guard_cont_b. specialize(guard_cont Htb); intros.
        constructor; try easy.
      - inversion Htc; try easy. subst.
        apply pa_sendr with (n := S n0) (s := s0) (g := g0); try easy.
    apply gttT_mon.
    apply gttT_mon.
Qed.
  
Lemma parts_to_word : forall p G, isgPartsC p G -> exists w r, (gttmap G w None (gnode_pq r p) \/ gttmap G w None (gnode_pq p r)).
Proof.
  intros.
  unfold isgPartsC in H.
  destruct H as (Gl,(Ha,(Hb,Hc))).
  specialize(isgParts_depth_exists p Gl Hc); intros.
  destruct H as (n, H).
  clear Hc Hb.
  revert H Ha. revert Gl G p.
  induction n; intros; try easy.
  - inversion H. subst.
    exists nil. exists q. right. pinversion Ha. subst. constructor.
    apply gttT_mon.
  - subst.
    exists nil. exists p0. left. pinversion Ha. subst. constructor.
    apply gttT_mon.
  - inversion H. subst.
    pinversion Ha. subst.
    specialize(subst_parts_depth 0 0 n p g g Q H2 H1); intros.
    specialize(IHn Q G p). apply IHn; try easy.
    apply gttT_mon.
  - subst.
    pinversion Ha. subst.
    assert(exists gl, onth k ys = Some(s, gl) /\ gttTC g gl).
    {
      clear H4 H2 H1 H Ha IHn.
      revert H8 H3. revert lis ys s g.
      induction k; intros; try easy.
      - destruct lis; try easy.
        destruct ys; try easy.
        inversion H8. subst. clear H8.
        simpl in H3. subst. 
        destruct H2; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
        exists g2. destruct Hc; try easy.
      - destruct lis; try easy.
        destruct ys; try easy.
        inversion H8. subst. clear H8.
        specialize(IHk lis ys s g). apply IHk; try easy.
    }
    destruct H0 as (gl,(Hb,Hc)).
    specialize(IHn g gl p H4 Hc).
    destruct IHn as (w,(r,Hd)).
    exists (k :: w). exists r.
    destruct Hd.
    - left. apply gmap_con with (st := s) (gk := gl); try easy.
    - right. apply gmap_con with (st := s) (gk := gl); try easy.
    apply gttT_mon.
Qed.




  