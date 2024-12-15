From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 

Notation fin := nat.
Notation part := string (only parsing).
Notation label := nat (only parsing).

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


Variant value: Type :=
  | vint : Z    -> value
  | vbool: bool -> value
  | vnat : nat -> value.


Inductive sort: Type :=
  | sbool: sort
  | sint : sort
  | snat : sort.

Inductive subsort: sort -> sort -> Prop :=
  | sni  : subsort snat sint
  | srefl: forall s, subsort s s.

Lemma sstrans: forall s1 s2 s3, subsort s1 s2 -> subsort s2 s3 -> subsort s1 s3.
Proof. intros.
       induction H.
       inversion H0. subst. constructor.
       easy.
Qed.

Section expr.
Inductive expr  : Type :=
  | e_var : ( fin ) -> expr 
  | e_val : ( value   ) -> expr 
  | e_succ : ( expr   ) -> expr 
  | e_neg : ( expr   ) -> expr 
  | e_not : ( expr   ) -> expr 
  | e_gt : ( expr   ) -> ( expr   ) -> expr
  | e_plus: ( expr   ) -> ( expr   ) -> expr
  | e_det : expr -> expr -> expr.


End expr.

Section process.

Inductive process : Type := 
  | p_var : fin -> process
  | p_inact : process
  | p_send : part -> label -> expr -> process -> process
  | p_recv : part -> list (option process) -> process 
  | p_ite : expr -> process -> process -> process 
  | p_rec : process -> process.

Section process_ind_ref.
  Variable P : process -> Prop.
  Hypothesis P_var : forall n, P (p_var n).
  Hypothesis P_inact : P (p_inact).
  Hypothesis P_send : forall pt lb ex pr, P pr -> P (p_send pt lb ex pr).
  Hypothesis P_recv : forall pt llp, Forall (fun u => 
      match u with 
        | Some k => P k 
        | None   => True 
      end) llp -> P (p_recv pt llp).
  Hypothesis P_ite : forall e P1 P2, P P1 -> P P2 -> P (p_ite e P1 P2).
  Hypothesis P_rec : forall pr, P pr -> P (p_rec pr).
  
  Fixpoint process_ind_ref p : P p.
  Proof.
    destruct p.
    - apply (P_var n).
    - apply (P_inact).
    - apply (P_send s n e p (process_ind_ref p)).
    - apply (P_recv).
      induction l as [ | c l IH].
      clear process_ind_ref. 
      - easy.
      - apply (Forall_cons); intros. destruct c. 
        - generalize (process_ind_ref p); intros. easy. easy.
        - apply IH.
    - apply (P_ite e p1 p2 (process_ind_ref p1) (process_ind_ref p2)).
    - apply (P_rec p (process_ind_ref p)). 
  Qed.
End process_ind_ref.

Inductive wtyped : process -> Prop := 
  | wp_var : forall n, wtyped (p_var n)
  | wp_inact : wtyped p_inact
  | wp_send: forall pt lb ex pr, wtyped pr -> wtyped (p_send pt lb ex pr)
  | wp_recv : forall pt llp, SList llp -> List.Forall (fun u => (u = None) \/ (exists k, u = Some k /\ wtyped k)) llp -> wtyped (p_recv pt llp)
  | wp_ite : forall e P1 P2, wtyped P1 -> wtyped P2 -> wtyped (p_ite e P1 P2)
  | wp_rec : forall pr, wtyped pr -> wtyped (p_rec pr).

Lemma list_fst_snd_len {A B: Type} : forall (lis : list (A*B)), length (List.map fst lis) = length (List.map snd lis).
Proof.
  intros.
  induction lis.
  easy.
  simpl. 
  replace (length (List.map fst lis)) with (length (List.map snd lis)).
  easy.
Qed.

Lemma unzip_zip {A B : Type} : forall (lis : list (A*B)), lis = zip (List.map fst lis) (List.map snd lis).
Proof.
  intros.
  induction lis.
  - easy.
  - simpl. replace lis with (zip (List.map fst lis) (List.map snd lis)) at 1.
    specialize(surjective_pairing a); intros. 
    replace a with (a.1,a.2). easy.
Qed.

Fixpoint incr_freeE (fv m : fin) (e : expr) :=
  match e with
    | e_var n    => e_var (if fv <= n then (n + m)%coq_nat else n)
    | e_val v    => e_val v 
    | e_succ n   => e_succ (incr_freeE fv m n)
    | e_neg n    => e_neg (incr_freeE fv m n)
    | e_not n    => e_not (incr_freeE fv m n)
    | e_gt u v   => e_gt (incr_freeE fv m u) (incr_freeE fv m v)
    | e_plus u v => e_plus (incr_freeE fv m u) (incr_freeE fv m v) 
    | e_det u v  => e_det (incr_freeE fv m u) (incr_freeE fv m v)
  end. 

Fixpoint incr_free (fvP fvE m k : fin) (P : process) : process :=
  match P with 
    | p_var n          => p_var (if fvP <= n then ((n + m)%coq_nat) else n)
    | p_inact          => p_inact
    | p_send p l e P'  => p_send p l (incr_freeE fvE k e) (incr_free fvP fvE m k P')
    | p_recv p llp     => p_recv p (List.map (
        fun u => match u with 
          | Some p' => Some (incr_free fvP (S fvE) m k p')
          | None    => None
        end) llp)
    | p_ite e P1 P2    => p_ite (incr_freeE fvE k e) (incr_free fvP fvE m k P1) (incr_free fvP fvE m k P2)
    | p_rec P'         => p_rec (incr_free (S fvP) fvE m k P')
  end.

Section substitution.

Definition subst_relation (A : Type) : Type := fin -> fin -> fin -> A -> A -> A -> Prop.

(* relation of sub_from, sub_to, proc_before_sub, proc_after_sub, rec case, ensures is fresh in both x and P *)
Inductive substitutionP : subst_relation process :=
  | sub_var_is   : forall P x m n,              substitutionP x m n P (p_var x) (incr_free 0 0 m n P)
  | sub_var_notz : forall P x m n, x <> 0 ->    substitutionP x m n P (p_var 0) (p_var 0)
  | sub_var_not1 : forall P x y m n, x <> S y -> x <= y -> substitutionP x m n P (p_var (S y)) (p_var y)
  | sub_var_not2 : forall P x y m n, x <> S y -> y < x  -> substitutionP x m n P (p_var (S y)) (p_var (S y))
  | sub_inact    : forall P x m n,              substitutionP x m n P (p_inact) (p_inact)
  | sub_send     : forall P x m n pt l e P' Q', substitutionP x m n P P' Q' -> substitutionP x m n P (p_send pt l e P') (p_send pt l e Q')
  | sub_recv     : forall P x m n pt xs ys, 
  List.Forall2 (fun u v => 
    (u = None /\ v = None) \/
    (exists k l, u = Some k /\ v = Some l /\ substitutionP x m (S n) P k l)  
  ) xs ys -> substitutionP x m n P (p_recv pt xs) (p_recv pt ys)
  | sub_ite       : forall P x m n e P1 P2 Q1 Q2, substitutionP x m n P P1 Q1 -> substitutionP x m n P P2 Q2 -> substitutionP x m n P (p_ite e P1 P2) (p_ite e Q1 Q2)
  | sub_rec       : forall P x m n P' Q', substitutionP (S x) (S m) n P P' Q' -> substitutionP x m n P (p_rec P') (p_rec Q').



End substitution.

End process.

Section ltt.

CoInductive ltt: Type :=
  | ltt_end : ltt
  | ltt_recv: part -> list (option(sort*ltt)) -> ltt
  | ltt_send: part -> list (option(sort*ltt)) -> ltt.

Definition ltt_id (s: ltt): ltt :=
  match s with
    | ltt_end      => ltt_end
    | ltt_recv p l => ltt_recv p l 
    | ltt_send p l => ltt_send p l
  end.
  
Lemma ltt_eq: forall s, s = ltt_id s.
Proof. intro s; destruct s; easy. Defined.

Inductive local  : Type :=
  | l_var : fin -> local 
  | l_end : local 
  | l_send : part -> list (option (sort * local)) -> local 
  | l_recv : part -> list (option (sort * local)) -> local 
  | l_rec : local -> local .
  
Section local_ind_ref.
  Variable P : local -> Prop.
  Hypothesis P_var : forall n, P (l_var n).
  Hypothesis P_end : P (l_end).
  Hypothesis P_send : forall p lis, List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ P g)) lis -> P (l_send p lis).
  Hypothesis P_recv : forall p lis, List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ P g)) lis -> P (l_recv p lis).
  Hypothesis P_rec : forall g, P g -> P (l_rec g).

  Fixpoint local_ind_ref p : P p.
  Proof.
    destruct p.
    - apply P_var.
    - apply P_end.
    - apply P_send.
      induction l; try easy.
      constructor; try easy.
      destruct a. right. destruct p. exists s0. exists l0. split; try easy.
      left. easy.
    - apply P_recv.
      induction l; try easy.
      constructor; try easy.
      destruct a. right. destruct p. exists s0. exists l0. split; try easy.
      left. easy.
    - apply P_rec; easy.
  Qed.
End local_ind_ref.


Fixpoint incr_freeL (fv m : fin) (T : local) := 
  match T with 
    | l_var n        => l_var (if fv <= n then (n + m) else n)
    | l_end          => l_end 
    | l_send p lis => l_send p (List.map (fun u => 
          match u with 
            | Some (s, g) => Some (s, incr_freeL fv m g)
            | None        => None
          end) lis)
    | l_recv p lis => l_recv p (List.map (fun u => 
          match u with 
            | Some (s, g) => Some (s, incr_freeL fv m g)
            | None        => None
          end) lis)
    | l_rec g        => l_rec (incr_freeL (S fv) m g)
  end.

Inductive subst_local : fin -> fin -> local -> local -> local -> Prop := 
  | subl_var_is   : forall G t m,                            subst_local t m G (l_var t) (incr_freeL 0 m G)
  | subl_var_notz : forall G t m, t <> 0 ->                  subst_local t m G (l_var 0) (l_var 0)
  | subl_var_not1 : forall G t t' m, t <> S t' -> t <= t' -> subst_local t m G (l_var (S t')) (l_var (t'))
  | subl_var_not2 : forall G t t' m, t <> S t' -> t' < t  -> subst_local t m G (l_var (S t')) (l_var (S t'))
  | subl_end      : forall G t m,                            subst_local t m G l_end l_end
  | subl_send     : forall G t m p xs ys, List.Forall2 (fun u v => 
                           (u = None /\ v = None) \/
                           (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ subst_local t m G g g')
                                                  ) xs ys -> subst_local t m G (l_send p xs) (l_send p ys)
  | subl_recv     : forall G t m p xs ys, List.Forall2 (fun u v => 
                           (u = None /\ v = None) \/
                           (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ subst_local t m G g g')
                                                  ) xs ys -> subst_local t m G (l_recv p xs) (l_recv p ys)
  | subl_rec      : forall G t m P Q, subst_local (S t) (S m) G P Q -> subst_local t m G (l_rec P) (l_rec Q). 

Inductive betaL : relation local := 
  | lttS : forall G G', subst_local 0 0 (l_rec G) G G' -> betaL (l_rec G) G'.

Inductive lttT (R : local -> ltt -> Prop) : local -> ltt -> Prop := 
  | lttT_end  : lttT R l_end ltt_end
  | lttT_send : forall p xs ys, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ R g g')) xs ys -> lttT R (l_send p xs) (ltt_send p ys)
  | lttT_recv : forall p xs ys, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ R g g')) xs ys -> lttT R (l_recv p xs) (ltt_recv p ys)
  | lttT_rec  : forall G Q G', subst_local 0 0 (l_rec G) G Q -> lttT R Q G' -> lttT R (l_rec G) G'.

Definition lttTC G G' := paco2 lttT bot2 G G'.

Inductive wfL : local -> Prop :=
  | wfl_var : forall n, wfL (l_var n)
  | wfl_end : wfL l_end
  | wfl_send : forall p lis, SList lis -> List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfL g)) lis -> wfL (l_send p lis)
  | wfl_recv : forall p lis, SList lis -> List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfL g)) lis -> wfL (l_recv p lis)
  | wfl_rec  : forall g, wfL g -> wfL (l_rec g).

Inductive guardL : fin -> fin -> local -> Prop := 
  | gl_nil  : forall m T, guardL 0 m T
  | gl_end  : forall n m, guardL n m l_end
  | gl_send : forall n m p lis, List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ guardL n m g)) lis -> guardL (S n) m (l_send p lis)
  | gl_recv : forall n m p lis, List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ guardL n m g)) lis -> guardL (S n) m (l_recv p lis)
  | gl_rec  : forall n m g Q, subst_local 0 0 (l_rec g) g Q -> guardL n m Q -> guardL n (S m) (l_rec g).


Lemma guardL_more : forall n m k T, guardL n m T -> m <= k -> guardL n k T.
Proof.
  induction n; intros; try easy.
  - apply gl_nil.
  - revert IHn H H0. revert n k T. induction m; intros; try easy.
    inversion H. subst. 
    - apply gl_end.
    - subst. apply gl_send; try easy.
      clear H. revert IHn H0 H2. revert n k p.
      induction lis; intros; try easy.
      inversion H2. subst. clear H2.
      constructor.
      - destruct H3. subst. left. easy.
        right. destruct H. destruct H. destruct H. subst. exists x. exists x0.
        split; try easy. apply IHn with (m := 0); try easy.
      - apply IHlis; try easy.
    - subst. apply gl_recv; try easy.
      clear H. revert IHn H0 H2. revert n k p.
      induction lis; intros; try easy.
      inversion H2. subst. clear H2.
      constructor.
      - destruct H3. subst. left. easy.
        right. destruct H. destruct H. destruct H. subst. exists x. exists x0.
        split; try easy. apply IHn with (m := 0); try easy.
      - apply IHlis; try easy.
    - destruct T.
      - inversion H.
      - apply gl_end.
      - apply gl_send.
        inversion H. subst.
        revert IHm IHn H H0 H4. revert m n k s.
        induction l; intros; try easy.
        inversion H4. subst.
        constructor.
        - destruct H3. subst. left. easy.
          destruct H1. destruct H1. destruct H1. subst. right.
          exists x. exists x0. split; try easy.
          apply IHn with (m := m.+1); try easy.
        - apply IHl with (m := m) (s := s); try easy.
        apply gl_send. easy.
      - apply gl_recv.
        inversion H. subst.
        revert IHm IHn H H0 H4. revert m n k s.
        induction l; intros; try easy.
        inversion H4. subst.
        constructor.
        - destruct H3. subst. left. easy.
          destruct H1. destruct H1. destruct H1. subst. right.
          exists x. exists x0. split; try easy.
          apply IHn with (m := m.+1); try easy.
        - apply IHl with (m := m) (s := s); try easy.
        apply gl_recv. easy.
      - inversion H. subst.
        destruct k; try easy.
        apply gl_rec with (Q := Q); try easy.
        apply IHm; try easy.
Qed.

Fixpoint wfrec (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop) (l1 l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | (Datatypes.None::xs, Datatypes.None::ys)               => wfrec R1 R2 xs ys
    | (Datatypes.Some (s',t')::xs, Datatypes.Some (s,t)::ys) => R1 s' s /\ R2 t t' /\ wfrec R1 R2 xs ys
    | (Datatypes.None::xs, Datatypes.Some(s,t)::ys)          => wfrec R1 R2 xs ys
    | (nil, _)                                               => True
    | _                                                      => False
  end.

Fixpoint wfsend (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop) (l1 l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | (Datatypes.None::xs, Datatypes.None::ys)               => wfsend R1 R2 xs ys
    | (Datatypes.Some (s,t)::xs, Datatypes.Some (s',t')::ys) => R1 s s' /\ R2 t t' /\ wfsend R1 R2 xs ys
    | (Datatypes.None::xs, Datatypes.Some(s',t')::ys)        => wfsend R1 R2 xs ys
    | (nil, _)                                               => True
    | _                                                      => False
  end.

Inductive subtype (R: ltt -> ltt -> Prop): ltt -> ltt -> Prop :=
  | sub_end: subtype R ltt_end ltt_end
  | sub_in : forall p xs ys,
                    wfrec subsort R ys xs ->
                    subtype R (ltt_recv p xs) (ltt_recv p ys)
  | sub_out : forall p xs ys,
                     wfsend subsort R xs ys ->
                     subtype R (ltt_send p xs) (ltt_send p ys).

Definition subtypeC l1 l2 := paco2 subtype bot2 l1 l2.


Lemma refl_recv: forall (l1:  list (option(sort*ltt))) (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop),
   Reflexive R1 -> Reflexive R2 ->
   wfrec R1 R2 l1 l1.
Proof. intro l1.
       induction l1; intros.
       - simpl. easy.
       - simpl. destruct a. destruct p.
         split. reflexivity.
         split. reflexivity.
         apply IHl1.
         easy. easy.
         apply IHl1.
         easy. easy.
Qed.

Lemma refl_send: forall (l1:  list (option(sort*ltt))) (R1: sort -> sort -> Prop) (R2: ltt -> ltt -> Prop),
   Reflexive R1 -> Reflexive R2 ->
   wfsend R1 R2 l1 l1.
Proof. intro l1.
       induction l1; intros.
       - simpl. easy.
       - simpl. destruct a. destruct p.
         split. reflexivity.
         split. reflexivity.
         apply IHl1.
         easy. easy.
         apply IHl1.
         easy. easy.
Qed.

Lemma stRefl: forall l, subtypeC l l.
Proof. pcofix CIH.
       intros.
       pfold.
       case_eq l; intros.
       constructor.
       constructor.
       apply refl_recv.
       constructor.

       repeat intro.
       unfold upaco2.
       right. apply CIH.

       constructor.
       apply refl_send.
       constructor.
       repeat intro.
       right. apply CIH.
Qed.


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


Lemma subtype_end : forall H, subtypeC ltt_end H -> H = ltt_end.
Proof.
  intros. punfold H0. inversion H0. easy. 
  apply subtype_monotone.
Qed.

Lemma subtype_recv_inv_helper : forall pt s s0 l l0 xs ys,
    subtypeC (ltt_recv pt (Some (s, l) :: xs)) (ltt_recv pt (Some (s0, l0) :: ys)) -> 
    subtypeC l l0.
Proof.
  intros. 
  pinversion H. subst.
  simpl in H1.
  destruct H1. destruct H1.
  pclearbot.
  unfold subtypeC. easy.
  apply subtype_monotone.
Qed.

Lemma subtype_recv_inv : forall pt xs ys, subtypeC (ltt_recv pt xs) (ltt_recv pt ys) -> Forall2R (fun u v => (u = None) \/ (exists s s' t t', u = Some(s,t) /\ v = Some (s',t') /\ subsort s s' /\ subtypeC t' t)) ys xs.
Proof.
  intros pt xs ys. revert pt xs.
  induction ys; intros. constructor.
  - destruct xs; try easy.
    pinversion H. subst. 
    simpl in H1. destruct a. destruct p. easy. easy.
    apply subtype_monotone.
  constructor.
  - destruct o. destruct a. destruct p0. destruct p. right.
    exists s. exists s0. exists l. exists l0. split; try easy. split; try easy.
    split. 
    pinversion H. subst. destruct H1. easy.
    apply subtype_monotone.
    specialize(subtype_recv_inv_helper pt s0 s l0 l xs ys H); intros. easy.
    left. easy.
    pinversion H. subst. 
    simpl in H1. destruct a; try easy.
    destruct p. easy.
    left. easy.
    apply subtype_monotone.
  - apply IHys with (pt := pt).
    pinversion H. subst. 
    pfold. constructor.
    simpl in H1. 
    destruct o. destruct p. destruct a. destruct p. destruct H1. destruct H1. easy. easy.
    destruct a. destruct p. easy. easy.
  - apply subtype_monotone.
Qed.

Lemma subtype_recv : forall H pt xs, subtypeC (ltt_recv pt xs) H -> (exists ys, 
                    H = ltt_recv pt ys).
Proof.
  induction xs; intros; try easy.
  - pinversion H0. subst. exists ys. easy.
    apply subtype_monotone.
  - destruct H.
    pinversion H0. apply subtype_monotone.
    pinversion H0. subst. exists l. easy. apply subtype_monotone.
    pinversion H0. apply subtype_monotone.
Qed.

Lemma subtype_send_inv_helper : forall pt s s0 l l0 xs ys,
    subtypeC (ltt_send pt (Some (s, l) :: xs)) (ltt_send pt (Some (s0, l0) :: ys)) -> 
    subtypeC l l0.
Proof.
  intros. 
  pinversion H. subst.
  simpl in H1.
  destruct H1. destruct H1.
  pclearbot.
  unfold subtypeC. easy.
  apply subtype_monotone.
Qed.

Lemma subtype_send_inv : forall pt xs ys, subtypeC (ltt_send pt xs) (ltt_send pt ys) -> Forall2R (fun u v => (u = None) \/ (exists s s' t t', u = Some(s,t) /\ v = Some (s',t') /\ subsort s s' /\ subtypeC t t')) xs ys.
Proof.
  induction xs; intros.
  - constructor.
  - destruct ys; try easy.
    pinversion H. subst. simpl in H1. destruct a. destruct p. easy. easy.
    apply subtype_monotone.
  constructor.
  - destruct a. right. destruct p. destruct o. destruct p.
    exists s. exists s0. exists l. exists l0. split; try easy. split; try easy.
    split.
    pinversion H. subst. simpl in H1. destruct H1. easy.
    apply subtype_monotone.
    specialize(subtype_send_inv_helper pt s s0 l l0 xs ys H); intros. easy.
    pinversion H. subst. simpl in H1. easy.
  - apply subtype_monotone.
    left. easy.
  - apply IHxs.
    pinversion H. subst. 
    pfold. constructor.
    simpl in H1. 
    destruct o. destruct p. destruct a. destruct p. destruct H1. destruct H1. easy. easy.
    destruct a. destruct p. easy. easy.
  - apply subtype_monotone.
Qed.

Lemma subtype_send : forall H pt xs, subtypeC (ltt_send pt xs) H -> (exists ys, 
                    H = ltt_send pt ys).
Proof.
  induction xs; intros; try easy.
  - pinversion H0. subst. exists ys. easy.
    apply subtype_monotone.
  - destruct H.
    pinversion H0. apply subtype_monotone.
    pinversion H0. apply subtype_monotone.
    pinversion H0. subst. exists l. easy. apply subtype_monotone.
Qed.

Lemma stTrans_helper_recv : forall x x0 l r,
      (forall l1 l2 l3 : ltt, subtypeC l1 l2 -> subtypeC l2 l3 -> r l1 l3) ->
      Forall2R
      (fun u v : option (sort * ltt) =>
       u = None \/
       (exists (s s' : sort) (t t' : ltt),
          u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) x0 x ->
      Forall2R
       (fun u v : option (sort * ltt) =>
        u = None \/
        (exists (s s' : sort) (t t' : ltt),
           u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t' t)) x l ->
      wfrec subsort (upaco2 subtype r) x0 l.
Proof.
  induction x; intros; try easy.
  destruct x0; try easy. 
  destruct l; try easy. destruct x0; try easy.
  inversion H0; subst. clear H0. inversion H1. subst. clear H1.
  simpl.
  destruct H5. 
  - subst. destruct o. destruct p. apply IHx; try easy. apply IHx; try easy.
  - destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
    subst.
    destruct H4; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H4.
    inversion H0.
    subst.
    split. apply sstrans with (s2 := x5); try easy.
    split. unfold upaco2. right. apply H with (l2 := x7); try easy. 
    apply IHx; try easy.
Qed. 

Lemma stTrans_helper_send : forall x x0 l r,
      (forall l1 l2 l3 : ltt, subtypeC l1 l2 -> subtypeC l2 l3 -> r l1 l3) ->
      Forall2R
      (fun u v : option (sort * ltt) =>
       u = None \/
       (exists (s s' : sort) (t t' : ltt),
          u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t')) x x0 -> 
      Forall2R
       (fun u v : option (sort * ltt) =>
        u = None \/
        (exists (s s' : sort) (t t' : ltt),
           u = Some (s, t) /\ v = Some (s', t') /\ subsort s s' /\ subtypeC t t')) l x ->
      wfsend subsort (upaco2 subtype r) l x0.
Proof.
  induction x; intros; try easy.
  destruct l; try easy.
  destruct l; try easy. destruct x0; try easy.
  inversion H0; subst. clear H0. inversion H1. subst. clear H1.
  simpl.
  destruct H5. 
  - subst. destruct o. destruct p. destruct H4. easy. destruct H0. destruct H0. 
    destruct H0. destruct H0. destruct H0. destruct H1. easy.
    destruct o0. destruct p. apply IHx; try easy. apply IHx; try easy.
  - destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H2.
    subst.
    destruct H4. subst. apply IHx; try easy. 
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. destruct H4.
    subst.
    inversion H1. subst.
    split. apply sstrans with (s2 := x6); try easy.
    split. unfold upaco2. right. apply H with (l2 := x8); try easy.
    apply IHx; try easy.
Qed. 

Lemma stTrans: forall l1 l2 l3, subtypeC l1 l2 -> subtypeC l2 l3 -> subtypeC l1 l3.
  Proof.
    pcofix CIH. intros.
    pfold. case_eq l1; intros.
    - subst. 
      specialize(subtype_end l2 H0); intros. subst.
      specialize(subtype_end l3 H1); intros. subst. apply sub_end.
    - subst.
      specialize(subtype_recv l2 s l H0); intros. destruct H. subst.
      specialize(subtype_recv l3 s x H1); intros. destruct H. subst.
      
      specialize(subtype_recv_inv s x x0 H1); intros.
      specialize(subtype_recv_inv s l x H0); intros.
      
      constructor.
      
      apply stTrans_helper_recv with (x := x); try easy.
      
    - subst.
      specialize(subtype_send l2 s l H0); intros. destruct H. subst.
      specialize(subtype_send l3 s x H1); intros. destruct H. subst.
      
      specialize(subtype_send_inv s x x0 H1); intros.
      specialize(subtype_send_inv s l x H0); intros.
      
      constructor.
      apply stTrans_helper_send with (x := x); try easy.
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


Lemma subst_injL : forall m n G G1 Q Q0, subst_local m n G G1 Q0 -> subst_local m n G G1 Q -> Q = Q0.
Proof.
  intros m n G G1.
  revert m n G. induction G1 using local_ind_ref; intros; try easy.
  inversion H. subst. 
  - inversion H0; try easy. 
  - subst. inversion H0; try easy.
  - subst. inversion H0; try easy.
    subst. specialize(triad_le m t' H6 H8); try easy.
  - subst. inversion H0; try easy. 
    subst. specialize(triad_le m t' H8 H6); try easy.
  
  inversion H. subst. inversion H0. subst. easy.
  
  inversion H0. subst. inversion H1. subst.
  assert (ys0 = ys). {
    clear H0 H1. revert H H8 H9. revert p m n G ys ys0.
    induction lis; intros; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    inversion H. subst. clear H.
    inversion H8. subst. clear H8.
    inversion H9. subst. clear H9.
    specialize(IHlis p m n G ys ys0 H3 H6 H8). subst.
    clear H3 H6 H8.
    destruct H4. destruct H. subst.
    destruct H5. destruct H. subst. easy.
    destruct H. destruct H. destruct H. easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
    destruct H5; try easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H. subst. 
    destruct H2; try easy. destruct H0. destruct H0. destruct H0. 
    inversion H0. subst.
    specialize(H2 m n G x1 x4 H3 H1). subst. easy.
  }
  subst. easy.
  
  inversion H0. subst. inversion H1. subst.
  assert (ys0 = ys). {
    clear H0 H1. revert H H8 H9. revert p m n G ys ys0.
    induction lis; intros; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    inversion H. subst. clear H.
    inversion H8. subst. clear H8.
    inversion H9. subst. clear H9.
    specialize(IHlis p m n G ys ys0 H3 H6 H8). subst.
    clear H3 H6 H8.
    destruct H4. destruct H. subst.
    destruct H5. destruct H. subst. easy.
    destruct H. destruct H. destruct H. easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
    destruct H5; try easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H. subst. 
    destruct H2; try easy. destruct H0. destruct H0. destruct H0. 
    inversion H0. subst.
    specialize(H2 m n G x1 x4 H3 H1). subst. easy.
  }
  subst. easy.
  
  inversion H. subst. inversion H0. subst.
  specialize(IHG1 (S m) (S n) G Q1 Q0 H6 H5). subst. easy.
Qed.

Lemma wfL_after_incr : forall G1 m n,
     wfL G1 -> wfL (incr_freeL m n G1).
Proof.
  induction G1 using local_ind_ref; intros; try easy.
  - simpl in *.
    constructor.
  - revert m n H0 H. revert p.
    induction lis; intros; try easy.
    - inversion H. subst. clear H.
      inversion H0. subst. inversion H5. subst.
      specialize(SList_f a lis H2); intros.
      destruct H.
      - assert (wfL (incr_freeL m n (l_send p lis))).
        {
          apply IHlis; try easy.
          inversion H0. subst. inversion H5. subst.
          constructor; try easy.
        }
        destruct H6. subst.
        - constructor. 
          {
            simpl. clear IHlis H3 H0 H4 H5 H2 H7 H1. 
            revert m n p H. induction lis; intros; try easy.
            specialize(SList_f a lis H); intros.
            destruct H0.
            - apply SList_b. apply IHlis; try easy.
            - destruct H0. destruct H1. subst. 
            simpl. destruct x; try easy.
          }
          constructor; try easy. left. easy.
          {
            clear IHlis H3 H0 H5 H2 H H1. clear p.
            revert H4. revert m n. induction lis; intros; try easy. 
            inversion H4. inversion H7. subst. clear H4 H7.
            constructor. 
            - destruct H1. subst. left. easy.
            - destruct H. destruct H. destruct H. subst. right.
              exists x. exists (incr_freeL m n x0). split; try easy. apply H0.
              destruct H6; try easy. destruct H. destruct H. destruct H. inversion H. subst. easy.
            - apply IHlis; try easy.
          }
        - destruct H6. destruct H6. destruct H6. subst. 
          constructor; try easy.
          {
             apply SList_b.
             clear IHlis H3 H0 H4 H5 H2 H8 H7 H1. clear x x0 p.
             revert m n H.
             induction lis; intros; try easy.
             specialize(SList_f a lis H); intros.
             destruct H0. apply SList_b. apply IHlis; try easy.
             destruct H0. destruct H1. subst. destruct x. easy.
          }
          constructor. right. exists x. exists (incr_freeL m n x0).
          split; try easy.
          destruct H3; try easy. destruct H3. destruct H3. destruct H3. inversion H3. subst. 
          apply H6; try easy.
          {
            clear IHlis H3 H0 H5 H2 H H1. clear p.
            revert H4. revert m n. induction lis; intros; try easy. 
            inversion H4. inversion H7. subst. clear H4 H7.
            constructor. 
            - destruct H1. subst. left. easy.
            - destruct H. destruct H. destruct H. subst. right.
              exists x1. exists (incr_freeL m n x2). split; try easy. apply H0.
              destruct H6; try easy. destruct H. destruct H. destruct H. inversion H. subst. easy.
            - apply IHlis; try easy.
          }
        - destruct H. destruct H1. subst.
          destruct H6; try easy. destruct H. destruct H. destruct H. subst.
          destruct H3; try easy. destruct H3. destruct H3. destruct H3. 
          replace (Some x) with (Some (x2, x3)) in *. inversion H. subst. clear H H3 H4 H7 H5.
          constructor; try easy. constructor; try easy.
          right. exists x0. exists (incr_freeL m n x1).
          split; try easy. apply H6; try easy.
  - revert m n H0 H. revert p.
    induction lis; intros; try easy.
    - inversion H. subst. clear H.
      inversion H0. subst. inversion H5. subst.
      specialize(SList_f a lis H2); intros.
      destruct H.
      - assert (wfL (incr_freeL m n (l_recv p lis))).
        {
          apply IHlis; try easy.
          inversion H0. subst. inversion H5. subst.
          constructor; try easy.
        }
        destruct H6. subst.
        - constructor. 
          {
            simpl. clear IHlis H3 H0 H4 H5 H2 H7 H1. 
            revert m n p H. induction lis; intros; try easy.
            specialize(SList_f a lis H); intros.
            destruct H0.
            - apply SList_b. apply IHlis; try easy.
            - destruct H0. destruct H1. subst. 
            simpl. destruct x; try easy.
          }
          constructor; try easy. left. easy.
          {
            clear IHlis H3 H0 H5 H2 H H1. clear p.
            revert H4. revert m n. induction lis; intros; try easy. 
            inversion H4. inversion H7. subst. clear H4 H7.
            constructor. 
            - destruct H1. subst. left. easy.
            - destruct H. destruct H. destruct H. subst. right.
              exists x. exists (incr_freeL m n x0). split; try easy. apply H0.
              destruct H6; try easy. destruct H. destruct H. destruct H. inversion H. subst. easy.
            - apply IHlis; try easy.
          }
        - destruct H6. destruct H6. destruct H6. subst. 
          constructor; try easy.
          {
             apply SList_b.
             clear IHlis H3 H0 H4 H5 H2 H8 H7 H1. clear x x0 p.
             revert m n H.
             induction lis; intros; try easy.
             specialize(SList_f a lis H); intros.
             destruct H0. apply SList_b. apply IHlis; try easy.
             destruct H0. destruct H1. subst. destruct x. easy.
          }
          constructor. right. exists x. exists (incr_freeL m n x0).
          split; try easy.
          destruct H3; try easy. destruct H3. destruct H3. destruct H3. inversion H3. subst. 
          apply H6; try easy.
          {
            clear IHlis H3 H0 H5 H2 H H1. clear p.
            revert H4. revert m n. induction lis; intros; try easy. 
            inversion H4. inversion H7. subst. clear H4 H7.
            constructor. 
            - destruct H1. subst. left. easy.
            - destruct H. destruct H. destruct H. subst. right.
              exists x1. exists (incr_freeL m n x2). split; try easy. apply H0.
              destruct H6; try easy. destruct H. destruct H. destruct H. inversion H. subst. easy.
            - apply IHlis; try easy.
          }
        - destruct H. destruct H1. subst.
          destruct H6; try easy. destruct H. destruct H. destruct H. subst.
          destruct H3; try easy. destruct H3. destruct H3. destruct H3. 
          replace (Some x) with (Some (x2, x3)) in *. inversion H. subst. clear H H3 H4 H7 H5.
          constructor; try easy. constructor; try easy.
          right. exists x0. exists (incr_freeL m n x1).
          split; try easy. apply H6; try easy.
  - inversion H. subst.
    constructor; try easy. apply IHG1; try easy.
Qed.
        
  
Lemma wfL_after_subst : forall Q G1 G2 m n,
    wfL G1 -> wfL G2 -> subst_local m n G1 G2 Q -> wfL Q.
Proof.
  induction Q using local_ind_ref; intros; try easy.
  - apply wfl_var.
  - apply wfl_end.
  - inversion H2; try easy. 
    - subst.
      apply wfL_after_incr. easy.
    - subst.
      inversion H1. subst.
      revert H H0 H1 H2 H8 H5 H6.
      revert p G1 m n xs.
      induction lis; intros; try easy. 
      - destruct xs; try easy.
      - destruct xs; try easy.
        specialize(SList_f o xs H5); intros. clear H5.
        inversion H8. subst. clear H8. inversion H6. subst. clear H6.
        destruct H3.
        - constructor; try easy. apply SList_b.
          {
            clear IHlis H H0 H1 H2 H9 H7 H8. revert H11 H3. revert xs.
            induction lis; intros; try easy.
            destruct xs; try easy.
            inversion H11. subst.
            specialize(SList_f x l H3); intros. destruct H. 
            - apply SList_b. apply IHlis with (xs := l); try easy.
            - destruct H. destruct H0. subst. destruct lis; try easy.
              destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. subst. easy.
          } 
        - inversion H. subst. clear H.
          assert (wfL (l_send p lis)). 
          {
            apply IHlis with (G1 := G1) (m := m) (n := n) (xs := xs); try easy.
            inversion H1. subst. inversion H12. subst. clear H12.
            constructor; try easy.
            inversion H2. subst. inversion H13. subst. clear H13.
            constructor; try easy.
          }
          inversion H. subst. constructor; try easy.
          clear H11 H8 H10 H12 H13 IHlis.
          destruct H6.
          - left. easy.
          - right. destruct H4. destruct H4. destruct H4. subst.
            destruct H9; try easy. destruct H4. destruct H4. destruct H4. destruct H4. destruct H6. inversion H6. subst.
            exists x1. exists x3. split; try easy.
            destruct H7; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst. 
            specialize(H5 G1 x0 m n). apply H5; try easy.
        - destruct H3. destruct H4. subst.
          destruct H9; try easy. destruct H3. destruct H3. destruct H3. destruct H3. destruct H4. inversion H3. subst.
          destruct H7; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst. 
          destruct lis; try easy.
          constructor; try easy. constructor; try easy. right.
          exists x. exists x2. split; try easy.
          inversion H. subst. clear H. destruct H10; try easy. destruct H. destruct H. destruct H. inversion H. subst.
          specialize(H7 G1 x3 m n). apply H7; try easy.
  - inversion H2; try easy. 
    - subst.
      apply wfL_after_incr. easy.
    - subst.
      inversion H1. subst.
      revert H H0 H1 H2 H8 H5 H6.
      revert p G1 m n xs.
      induction lis; intros; try easy. 
      - destruct xs; try easy.
      - destruct xs; try easy.
        specialize(SList_f o xs H5); intros. clear H5.
        inversion H8. subst. clear H8. inversion H6. subst. clear H6.
        destruct H3.
        - constructor; try easy. apply SList_b.
          {
            clear IHlis H H0 H1 H2 H9 H7 H8. revert H11 H3. revert xs.
            induction lis; intros; try easy.
            destruct xs; try easy.
            inversion H11. subst.
            specialize(SList_f x l H3); intros. destruct H. 
            - apply SList_b. apply IHlis with (xs := l); try easy.
            - destruct H. destruct H0. subst. destruct lis; try easy.
              destruct H2; try easy. destruct H. destruct H. destruct H. destruct H. destruct H0. subst. easy.
          } 
        - inversion H. subst. clear H.
          assert (wfL (l_recv p lis)). 
          {
            apply IHlis with (G1 := G1) (m := m) (n := n) (xs := xs); try easy.
            inversion H1. subst. inversion H12. subst. clear H12.
            constructor; try easy.
            inversion H2. subst. inversion H13. subst. clear H13.
            constructor; try easy.
          }
          inversion H. subst. constructor; try easy.
          clear H11 H8 H10 H12 H13 IHlis.
          destruct H6.
          - left. easy.
          - right. destruct H4. destruct H4. destruct H4. subst.
            destruct H9; try easy. destruct H4. destruct H4. destruct H4. destruct H4. destruct H6. inversion H6. subst.
            exists x1. exists x3. split; try easy.
            destruct H7; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst. 
            specialize(H5 G1 x0 m n). apply H5; try easy.
        - destruct H3. destruct H4. subst.
          destruct H9; try easy. destruct H3. destruct H3. destruct H3. destruct H3. destruct H4. inversion H3. subst.
          destruct H7; try easy. destruct H4. destruct H4. destruct H4. inversion H4. subst. 
          destruct lis; try easy.
          constructor; try easy. constructor; try easy. right.
          exists x. exists x2. split; try easy.
          inversion H. subst. clear H. destruct H10; try easy. destruct H. destruct H. destruct H. inversion H. subst.
          specialize(H7 G1 x3 m n). apply H7; try easy.
  - inversion H1. subst.
    apply wfL_after_incr; try easy.
    subst.
    specialize(IHQ G1 P (S m) (S n)). 
    constructor. apply IHQ; try easy.
    inversion H0. easy.
Qed.
  
Lemma guard_break : forall x, (forall n, exists m, guardL n m (l_rec x)) -> exists T, multiS betaL (l_rec x) T /\  (forall n, exists m, guardL n m T) /\ (T = l_end \/ (exists p lis, T = l_send p lis \/ T = l_recv p lis)).
Proof.
  intros.
  pose proof H as H1.
  specialize(H1 1). destruct H1.
  assert (exists T, multiS betaL (l_rec x) T /\
  (T = l_end \/
   (exists
      (p : string) (lis : seq.seq (option (sort * local))),
      T = l_send p lis \/ T = l_recv p lis))).
  {
    clear H. revert H0. revert x. induction x0; intros; try easy.
    inversion H0. subst.
    destruct Q; try easy.
    - exists l_end.
      split. apply multi_sing. constructor; try easy.
      left. easy.
    - exists (l_send s l).
      split. apply multi_sing. constructor; try easy.
      right. exists s. exists l. left. easy.
    - exists (l_recv s l).
      split. apply multi_sing. constructor; try easy.
      right. exists s. exists l. right. easy.
    - specialize(IHx0 Q H4). 
      destruct IHx0. destruct H. exists x1. split; try easy.
      apply multi_sstep with (y := (l_rec Q)).
      constructor; try easy.
      easy.
  }
  destruct H1. destruct H1. exists x1.
  split; try easy. split; try easy.
  clear H0 H2. clear x0.
  revert H. induction H1; intros; try easy.
  - inversion H. subst.
    specialize(H0 n). destruct H0. 
    inversion H0. subst.
    - exists 0. apply gl_nil.
    - subst. exists m.
      specialize(subst_injL 0 0 (l_rec G) G y Q H3 H1); intros. subst. easy.
  - inversion H. subst.
    apply IHmultiS; try easy.
    intros. specialize(H0 n0). destruct H0.
    inversion H0. subst. exists 0. apply gl_nil.
    subst. exists m.
    specialize(subst_injL 0 0 (l_rec G) G y Q H4 H2); intros. subst. easy.
Qed.




End ltt.



Section gtt.

(* global session trees *)
CoInductive gtt: Type :=
  | gtt_end    : gtt
  | gtt_send   : part -> part -> list (option (sort*gtt)) -> gtt.

Definition gtt_id (s: gtt): gtt :=
  match s with
    | gtt_end        => gtt_end
    | gtt_send p q l => gtt_send p q l
  end.

Lemma gtt_eq: forall s, s = gtt_id s.
Proof. intro s; destruct s; easy. Defined.


Inductive global  : Type :=
  | g_var : fin -> global 
  | g_end : global 
  | g_send : part -> part -> list (option (sort * global)) -> global 
  | g_rec : global -> global.
  
Section global_ind_ref.
  Variable P : global -> Prop.
  Hypothesis P_var : forall n, P (g_var n).
  Hypothesis P_end : P (g_end).
  Hypothesis P_send : forall p q lis, List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ P g)) lis -> P (g_send p q lis).
  Hypothesis P_rec : forall g, P g -> P (g_rec g).
  
  Fixpoint global_ind_ref p : P p.
  Proof.
    destruct p.
    - apply P_var.
    - apply P_end.
    - apply P_send.
      induction l; try easy.
      constructor; try easy.
      destruct a. right. destruct p. exists s1. exists g. split; try easy.
      left. easy.
    - apply P_rec. easy.
  Qed.
End global_ind_ref.


Fixpoint incr_freeG (fv m : fin) (G : global) := 
  match G with 
    | g_var n        => g_var (if fv <= n then (n + m) else n)
    | g_end          => g_end 
    | g_send p q lis => g_send p q (map (fun u => 
          match u with 
            | Some (s, g) => Some (s, incr_freeG fv m g)
            | None        => None
          end) lis)
    | g_rec g        => g_rec (incr_freeG (S fv) m g)
  end.

Inductive subst_global : fin -> fin -> global -> global -> global -> Prop := 
  | subg_var_is   : forall G t m,                            subst_global t m G (g_var t) (incr_freeG 0 m G)
  | subg_var_notz : forall G t m, t <> 0 ->                  subst_global t m G (g_var 0) (g_var 0)
  | subg_var_not1 : forall G t t' m, t <> S t' -> t <= t' -> subst_global t m G (g_var (S t')) (g_var (t'))
  | subg_var_not2 : forall G t t' m, t <> S t' -> t' < t  -> subst_global t m G (g_var (S t')) (g_var (S t'))
  | subg_end      : forall G t m,                            subst_global t m G g_end g_end
  | subg_send     : forall G t m p q xs ys, List.Forall2 (fun u v => 
                           (u = None /\ v = None) \/
                           (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ subst_global t m G g g')
                                                  ) xs ys -> subst_global t m G (g_send p q xs) (g_send p q ys)
  | subg_rec      : forall G t m P Q, subst_global (S t) (S m) G P Q -> subst_global t m G (g_rec P) (g_rec Q). 


Inductive betaG : relation global := 
  | gttS : forall G G', subst_global 0 0 (g_rec G) G G' -> betaG (g_rec G) G'.

Inductive gttT (R : global -> gtt -> Prop) : global -> gtt -> Prop := 
  | gttT_end  : gttT R g_end gtt_end
  | gttT_send : forall p q xs ys, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ R g g')) xs ys -> gttT R (g_send p q xs) (gtt_send p q ys)
  | gttT_rec  : forall G Q G', subst_global 0 0 (g_rec G) G Q -> R Q G' -> gttT R (g_rec G) G'.

Definition gttTC G G' := paco2 gttT bot2 G G'.

Inductive wfG : global -> Prop := 
  | wfg_var : forall n, wfG (g_var n)
  | wfg_end : wfG g_end
  | wfg_send : forall p q lis, SList lis -> p <> q -> List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfG g)) lis -> wfG (g_send p q lis)
  | wfg_rec : forall g, wfG g -> wfG (g_rec g).

Inductive guardG : fin -> fin -> global -> Prop :=  
  | gg_nil : forall m G, guardG 0 m G
  | gg_end : forall n m, guardG n m g_end
  | gg_send : forall n m p q lis, List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ guardG n m g)) lis -> guardG (S n) m (g_send p q lis)
  | gg_rec : forall n m g Q, subst_global 0 0 (g_rec g) g Q -> guardG n m Q -> guardG n (S m) (g_rec g).

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

Lemma guardG_more : forall n m k G, guardG n m G -> m <= k -> guardG n k G.
Proof.
  induction n; intros; try easy.
  - apply gg_nil.
  - revert IHn H H0. revert n k G. induction m; intros; try easy.
    inversion H. subst. 
    - apply gg_end.
    - subst. apply gg_send; try easy.
      clear H. revert IHn H0 H2. revert n k p.
      induction lis; intros; try easy.
      inversion H2. subst. clear H2.
      constructor.
      - destruct H3. subst. left. easy.
        right. destruct H. destruct H. destruct H. subst. exists x. exists x0.
        split; try easy. apply IHn with (m := 0); try easy.
      - apply IHlis; try easy.
    - destruct G.
      - inversion H.
      - apply gg_end.
      - apply gg_send.
        inversion H. subst.
        revert IHm IHn H H0 H4. revert m n k s.
        induction l; intros; try easy.
        inversion H4. subst.
        constructor.
        - destruct H3. subst. left. easy.
          destruct H1. destruct H1. destruct H1. subst. right.
          exists x. exists x0. split; try easy.
          apply IHn with (m := m.+1); try easy.
        - apply IHl with (m := m) (s := s); try easy.
        apply gg_send. easy.
      - inversion H. subst.
        destruct k; try easy.
        apply gg_rec with (Q := Q); try easy.
        apply IHm; try easy.
Qed.

 
Lemma subst_injG : forall m n G G1 Q Q0, subst_global m n G G1 Q0 -> subst_global m n G G1 Q -> Q = Q0.
Proof.
  intros m n G G1. revert m n G.
  induction G1 using global_ind_ref; intros; try easy.
  inversion H. subst. 
  - inversion H0; try easy. 
  - subst. inversion H0; try easy.
  - subst. inversion H0; try easy.
    subst. specialize(triad_le m t' H6 H8); try easy.
  - subst. inversion H0; try easy. 
    subst. specialize(triad_le m t' H8 H6); try easy.
  
  inversion H. subst. inversion H0. subst. easy.
  
  inversion H0. subst. inversion H1. subst.
  assert (ys0 = ys). {
    clear H0 H1. revert H H9 H10. revert p m n G ys ys0.
    induction lis; intros; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    destruct ys; try easy. destruct ys0; try easy.
    inversion H. subst. clear H.
    inversion H9. subst. clear H9.
    inversion H10. subst. clear H10.
    specialize(IHlis p m n G ys ys0 H3 H6 H8). subst.
    clear H3 H6 H8.
    destruct H4. destruct H. subst.
    destruct H5. destruct H. subst. easy.
    destruct H. destruct H. destruct H. easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
    destruct H5; try easy.
    destruct H. destruct H. destruct H. destruct H. destruct H0. 
    inversion H. subst. 
    destruct H2; try easy. destruct H0. destruct H0. destruct H0. 
    inversion H0. subst.
    specialize(H2 m n G x1 x4 H3 H1). subst. easy.
  }
  subst. easy.
  
  inversion H. subst. inversion H0. subst.
  specialize(IHG1 (S m) (S n) G Q1 Q0 H6 H5). subst. easy.
Qed.

Lemma wfG_after_incr : forall G1 m n,
     wfG G1 -> wfG (incr_freeG m n G1).
Proof.
  induction G1 using global_ind_ref; intros; try easy.
  - simpl in *.
    constructor.
  - revert m n H0 H. revert p.
    induction lis; intros; try easy.
    - inversion H. subst. clear H.
      inversion H0. subst. inversion H7. subst. clear H7.
      specialize(SList_f a lis H5); intros.
      destruct H.
      - assert (wfG (incr_freeG m n (g_send p q lis))).
        {
          apply IHlis; try easy.
          inversion H0. subst.
          constructor; try easy.
        }
        destruct H2. subst.
        - constructor. 
          {
            simpl. clear IHlis H3 H0 H4 H5 H6 H1. 
            revert m n p H. induction lis; intros; try easy.
            specialize(SList_f a lis H); intros.
            destruct H0.
            - apply SList_b. apply IHlis; try easy. inversion H8. easy.
            - destruct H0. destruct H1. subst. 
            simpl. destruct x; try easy.
          }
          easy.
          {
            clear IHlis H3 H0 H5 H1 H6. 
            revert H H4 H8. revert m n. clear q p.
            induction lis; intros; try easy. constructor. left. easy.
            - specialize(SList_f a lis H); intros.
              inversion H4. subst. clear H4. inversion H8. subst. clear H8.
              destruct H0. specialize(IHlis m n H0 H5 H6). inversion IHlis. subst. clear IHlis.
              constructor; try easy. clear H8. clear H7 H6 H5.
              destruct H3. subst. left. easy.
              destruct H1. destruct H1. destruct H1. subst. right.
              exists x. exists (incr_freeG m n x0). split; try easy.
              destruct H4; try easy. apply H2; try easy.
              destruct H1. destruct H1. destruct H1. inversion H1. subst. easy.
              
            - destruct H0. destruct H1. subst. constructor; try easy.
              right. destruct x. exists s. 
              destruct H3; try easy. destruct H0. destruct H0. destruct H0. inversion H0. subst.
              destruct H4; try easy. destruct H2. destruct H2. destruct H2. inversion H2. subst.
              exists (incr_freeG m n x2). split; try easy. apply H1; try easy.
          }
        - destruct H2. destruct H2. destruct H2. subst. 
          constructor; try easy.
          {
             apply SList_b.
             clear IHlis H3 H0 H4 H5 H6 H7 H8 H1. clear x x0 p q.
             revert m n H.
             induction lis; intros; try easy.
             specialize(SList_f a lis H); intros.
             destruct H0. apply SList_b. apply IHlis; try easy.
             destruct H0. destruct H1. subst. destruct x. easy.
          }
          constructor. right. exists x. exists (incr_freeG m n x0).
          split; try easy.
          destruct H3; try easy. destruct H2. destruct H2. destruct H2. inversion H2. subst. 
          apply H3; try easy.
          {
            clear IHlis H3 H0 H5 H6 H7 H1 H. clear p q.
            revert H4 H8. revert m n. clear x x0. induction lis; intros; try easy. 
            inversion H4. inversion H8. subst. clear H4 H8.
            specialize(IHlis m n H2 H7). constructor; try easy. clear IHlis H2 H7.
            - destruct H1. subst. left. easy.
            - destruct H. destruct H. destruct H. subst. right.
              exists x. exists (incr_freeG m n x0). split; try easy.
              apply H0.
              destruct H6; try easy. destruct H. destruct H. destruct H. inversion H. subst. easy.
          }
        - destruct H. destruct H1. subst.
          destruct H2; try easy. destruct H. destruct H. destruct H. inversion H. subst.
          destruct H3; try easy. destruct H2. destruct H2. destruct H2. inversion H2. subst. 
          constructor; try easy. constructor; try easy.
          right. exists x. exists (incr_freeG m n x2).
          split; try easy. apply H3; try easy.
  - inversion H. subst.
    constructor; try easy. apply IHG1; try easy.
Qed.
  
Lemma wfG_after_subst : forall Q G1 G2 m n,
    wfG G1 -> wfG G2 -> subst_global m n G1 G2 Q -> wfG Q.
Proof.
  induction Q using global_ind_ref; intros; try easy.
  - apply wfg_var.
  - apply wfg_end.
  - inversion H2; try easy. 
    - subst.
      apply wfG_after_incr. easy.
    - subst. 
      inversion H1. subst. clear H1 H2.
      revert H H0 H8 H6 H7 H9.
      revert p G1 m n xs q.
      induction lis; intros; try easy. 
      - destruct xs; try easy.
      - destruct xs; try easy.
        specialize(SList_f o xs H6); intros. clear H6.
        inversion H8. subst. clear H8.
        inversion H. subst. clear H. inversion H9. subst. clear H9.
        destruct H1.
        specialize(IHlis p G1 m n xs q H6 H0 H10 H H7 H8).
        inversion IHlis; subst.
        constructor; try easy. apply SList_b. easy.
        constructor; try easy.
        clear H12 H11 H8 H6 H10 H H7. 
        destruct H4. left. easy.
        destruct H. destruct H. destruct H. subst.
        destruct H5; try easy. destruct H. destruct H. destruct H. destruct H. destruct H2.
        inversion H2. subst. right. exists x1. exists x3. split; try easy. 
        destruct H3; try easy. destruct H. destruct H. destruct H. inversion H. subst.
        specialize(H1 G1 x0 m n). apply H1;try easy.
      - destruct H. destruct H1. subst.
        destruct lis; try easy. clear IHlis H10 H6 H8.
        destruct H3; try easy. destruct H. destruct H. destruct H. inversion H. subst.
        destruct H5; try easy. destruct H2. destruct H2. destruct H2. destruct H2. destruct H3.
        inversion H2. subst.
        destruct H4; try easy. destruct H3. destruct H3. destruct H3. inversion H3. subst.
        constructor; try easy. constructor; try easy. right.
        exists x0. exists x1. specialize(H4 G1 x2 m n). split; try easy. apply H4; try easy.
  - inversion H1. subst.
    apply wfG_after_incr; try easy.
    subst.
    specialize(IHQ G1 P (S m) (S n)). 
    constructor. apply IHQ; try easy.
    inversion H0. easy.
Qed.
  
Lemma guard_breakG : forall x, (forall n, exists m, guardG n m (g_rec x)) -> exists T, multiS betaG (g_rec x) T /\  (forall n, exists m, guardG n m T) /\ (T = g_end \/ (exists p q lis, T = g_send p q lis)).
Proof.
  intros.
  pose proof H as H1.
  specialize(H1 1). destruct H1.
  assert (exists T, multiS betaG (g_rec x) T /\
  (T = g_end \/
   (exists
      (p q : string) (lis : seq.seq (option (sort * global))),
      T = g_send p q lis))).
  {
    clear H. revert H0. revert x. induction x0; intros; try easy.
    inversion H0. subst.
    destruct Q; try easy.
    - exists g_end.
      split. apply multi_sing. constructor; try easy.
      left. easy.
    - exists (g_send s s0 l).
      split. apply multi_sing. constructor; try easy.
      right. exists s. exists s0. exists l. easy.
    - specialize(IHx0 Q H4). 
      destruct IHx0. destruct H. exists x1. split; try easy.
      apply multi_sstep with (y := (g_rec Q)).
      constructor; try easy.
      easy.
  }
  destruct H1. destruct H1. exists x1.
  split; try easy. split; try easy.
  clear H0 H2. clear x0.
  revert H. induction H1; intros; try easy.
  - inversion H. subst.
    specialize(H0 n). destruct H0. 
    inversion H0. subst.
    - exists 0. apply gg_nil.
    - subst. exists m.
      specialize(subst_injG 0 0 (g_rec G) G y Q H3 H1); intros. subst. easy.
  - inversion H. subst.
    apply IHmultiS; try easy.
    intros. specialize(H0 n0). destruct H0.
    inversion H0. subst. exists 0. apply gg_nil.
    subst. exists m.
    specialize(subst_injG 0 0 (g_rec G) G y Q H4 H2); intros. subst. easy.
Qed.


Lemma gttTC_after_subst : forall G G' G1,
    multiS betaG G G' -> 
    gttTC G G1 ->
    gttTC G' G1.
Proof.
  intros. revert H0. revert G1. induction H; intros.
  - inversion H. subst.
    pinversion H0. subst.
    specialize(subst_injG 0 0 (g_rec G) G y Q H3 H1); intros. subst.
    easy.
    apply gttT_mon.
  - apply IHmultiS. inversion H. subst.
    pinversion H1. subst.
    specialize(subst_injG 0 0 (g_rec G) G y Q H4 H2); intros. subst.
    easy.
    apply gttT_mon.
Qed.

Lemma guard_breakG_s : forall Gl G,
      gttTC Gl G -> 
      (forall n : fin, exists m : fin, guardG n m Gl) -> 
      exists T : global,
        (forall n : fin, exists m : fin, guardG n m T) /\
        (T = g_end \/
         (exists (p q : string) (lis : seq.seq (option (sort * global))), T = g_send p q lis)) /\
         gttTC T G.
Proof.
  intros. pinversion H; try easy.
  - subst. exists g_end. split; try easy. split; try easy. left. easy. pfold. constructor.
  - subst. exists (g_send p q xs). split; try easy. split.
    right. exists p. exists q. exists xs. easy. pfold. easy.
  - subst.
    specialize(guard_breakG G0 H0); intros. destruct H3.
    exists x. destruct H3. destruct H4. split; try easy.
    split; try easy.
    specialize(gttTC_after_subst (g_rec G0) x G); intros. apply H6; try easy. pfold. easy.
  apply gttT_mon.
Qed.

End gtt.



Inductive gnode : Type := 
  | gnode_end : gnode
  | gnode_pq : part -> part -> gnode
  | gnode_s  : sort -> gnode.

(* gtt, labels to follow, sort if we want, where we reach *)
Inductive gttmap : gtt -> list fin -> option fin -> gnode -> Prop := 
  | gmap_end : gttmap gtt_end nil None gnode_end
  | gmap_pq  : forall p q xs, gttmap (gtt_send p q xs) nil None (gnode_pq p q)
  | gmap_con : forall n lis xs p q st gk s gn, onth n xs = Some (st, gk) -> gttmap gk lis s gn -> gttmap (gtt_send p q xs) (n :: lis) s gn
  | gmap_st  : forall n xs p q st gk, onth n xs = Some (st, gk) -> gttmap (gtt_send p q xs) nil (Some n) (gnode_s st). 

Inductive lnode : Type := 
  | lnode_end  : lnode 
  | lnode_send : part -> lnode 
  | lnode_recv : part -> lnode
  | lnode_s    : sort -> lnode.

(* tree to define on, labels to follow, sort if we want, where we reach *)
Inductive lttmap : ltt -> list fin -> option fin -> lnode -> Prop := 
  | lmap_end  : lttmap ltt_end nil None lnode_end 
  | lmap_send : forall p xs, lttmap (ltt_send p xs) nil None (lnode_send p)
  | lmap_recv : forall p xs, lttmap (ltt_recv p xs) nil None (lnode_recv p)
  | lmap_cons : forall n lis xs p st gk s gn, onth n xs = Some (st, gk) -> lttmap gk lis s gn -> lttmap (ltt_send p xs) (n :: lis) s gn
  | lmap_conr : forall n lis xs p st gk s gn, onth n xs = Some (st, gk) -> lttmap gk lis s gn -> lttmap (ltt_recv p xs) (n :: lis) s gn
  | lmap_sts  : forall n xs p st gk, onth n xs = Some(st, gk) -> lttmap (ltt_send p xs) nil (Some n) (lnode_s st)
  | lmap_str  : forall n xs p st gk, onth n xs = Some(st, gk) -> lttmap (ltt_recv p xs) nil (Some n) (lnode_s st).
 
Fixpoint isoList (R: ltt -> ltt -> Prop) (l1 l2: list (option(sort*ltt))): Prop :=
  match (l1,l2) with
    | (Datatypes.None::xs, Datatypes.None::ys)               => isoList R xs ys
    | (Datatypes.Some (s,t)::xs, Datatypes.Some (s',t')::ys) => s = s' /\ R t t' /\ isoList R xs ys
    | (nil, nil)                                             => True
    | (_, _)                                                 => False
  end.

Inductive lttIso (R: ltt -> ltt -> Prop): ltt -> ltt -> Prop :=
  | i_end : lttIso R ltt_end ltt_end
  | i_recv: forall p xs ys, isoList R xs ys -> lttIso R (ltt_recv p xs) (ltt_recv p ys)
  | i_send: forall p xs ys, isoList R xs ys -> lttIso R (ltt_send p xs) (ltt_send p ys).

Definition lttIsoC L L' := paco2 lttIso bot2 L L'.

(* equivalent to functional extensionality *)
Axiom lltExt: forall L L', lttIsoC L L' -> L = L'.

Lemma lltExt_b : forall r L L', L = L' -> paco2 lttIso r L L'.
Proof.
  pcofix CIH; intros.
  subst.
  pfold. 
  destruct L'. constructor.
  constructor. induction l; intros; try easy.
  destruct a; try easy. destruct p; try easy. constructor; try easy. 
  split; try easy. right. apply CIH; try easy.
  constructor. induction l; intros; try easy.
  destruct a; try easy. destruct p; try easy. constructor; try easy. 
  split; try easy. right. apply CIH; try easy.
Qed.


Definition balancedG (G : gtt) := forall w w' p q gn,
  gttmap G w None gn -> (gttmap G (w ++ w') None (gnode_pq p q) \/ gttmap G (w ++ w') None (gnode_pq q p)) -> 
  (exists k, forall w', (gttmap G (w ++ w') None (gnode_end) \/ (List.length w' = k /\ exists tc, gttmap G (w ++ w') None tc)) -> 
                        exists w2 w0, w' = w2 ++ w0 /\ exists r, 
                        gttmap G (w ++ w2) None (gnode_pq p r) \/ gttmap G (w ++ w2) None (gnode_pq r p)).


Definition wfgC G := exists G', gttTC G' G /\ wfG G' /\ (forall n, exists m, guardG n m G') /\ balancedG G. 

Definition wfgCw G := exists G', gttTC G' G /\ wfG G' /\ (forall n, exists m, guardG n m G').

Definition wfC T := exists T', lttTC T' T /\ wfL T' /\ (forall n, exists m, guardL n m T').


Lemma ltt_after_betaL : forall G G' T,
  lttTC G T -> multiS betaL G G' -> lttTC G' T.
Proof.
  intros. revert H. revert T. induction H0; intros; try easy.
  inversion H. subst. pfold. 
  pinversion H0; try easy. subst.
  specialize(subst_injL 0 0 (l_rec G) G y Q H3 H1); intros. subst. easy.
  apply lttT_mon.
  apply IHmultiS.
  inversion H. subst. 
  pinversion H1. subst.
  specialize(subst_injL 0 0 (l_rec G) G y Q H4 H2); intros. subst. pfold. easy.
  apply lttT_mon.
Qed.

Lemma gtt_after_betaL : forall G G' T,
  gttTC G T -> multiS betaG G G' -> gttTC G' T.
Proof.
  intros. revert H. revert T. induction H0; intros; try easy.
  inversion H. subst. pfold. 
  pinversion H0; try easy. subst.
  specialize(subst_injG 0 0 (g_rec G) G y Q H3 H1); intros. subst. punfold H4.
  apply gttT_mon.
  apply gttT_mon.
  apply IHmultiS.
  inversion H. subst. 
  pinversion H1. subst.
  specialize(subst_injG 0 0 (g_rec G) G y Q H4 H2); intros. subst. pfold. punfold H5. 
  apply gttT_mon.
  apply gttT_mon.
Qed.

Lemma wfL_after_beta : forall G G', 
      wfL G ->
      multiS betaL G G' -> 
      wfL G'.
Proof.
  intros. revert H. induction H0; intros; try easy.
  - inversion H. subst.
    specialize(wfL_after_subst y (l_rec G) G 0 0); intros.
    apply H2; try easy. inversion H0. easy.
  - apply IHmultiS. clear H0 IHmultiS.
    inversion H. subst.
    specialize(wfL_after_subst y (l_rec G) G 0 0); intros.
    apply H2; try easy. inversion H1. easy.
Qed.

Lemma wfG_after_beta : forall G G', 
      wfG G ->
      multiS betaG G G' -> 
      wfG G'.
Proof.
  intros. revert H. induction H0; intros; try easy.
  - inversion H. subst.
    specialize(wfG_after_subst y (g_rec G) G 0 0); intros.
    apply H2; try easy. inversion H0. easy.
  - apply IHmultiS. clear H0 IHmultiS.
    inversion H. subst.
    specialize(wfG_after_subst y (g_rec G) G 0 0); intros.
    apply H2; try easy. inversion H1. easy.
Qed.

Lemma guard_breakL_s2 : forall G Gl, 
   (forall n : fin, exists m : fin, guardL n m Gl) ->
   wfL Gl ->
   lttTC Gl G -> 
   exists Gl', (Gl' = l_end \/ exists p lis, Gl' = l_send p lis \/ Gl' = l_recv p lis) /\
   (forall n : fin, exists m : fin, guardL n m Gl') /\
   wfL Gl' /\
   lttTC Gl' G.
Proof.
  intros.
  pinversion H1. 
  - subst. exists l_end. split; try easy. left. easy. split; try easy. split; try easy. pfold. easy.
  - subst. exists (l_send p xs). split. right. exists p. exists xs. left. easy.
    split. easy. split. easy. pfold. easy.
  - subst. exists (l_recv p xs). split. right. exists p. exists xs. right. easy.
    split. easy. split. easy. pfold. easy.
  - subst.
    specialize(guard_break G0 H); intros. clear H2 H3.
    destruct H4 as (Gl',(Ha,(Hb,Hc))). exists Gl'. split; try easy. split; try easy.
    split.
    specialize(wfL_after_beta (l_rec G0) Gl' H0 Ha). easy. 
    specialize(ltt_after_betaL (l_rec G0) Gl'); intros. apply H2; try easy. pfold. easy.
  apply lttT_mon.
Qed. 

Lemma guard_breakG_s2 : forall G Gl, 
   (forall n : fin, exists m : fin, guardG n m Gl) ->
   wfG Gl ->
   gttTC Gl G -> 
   exists Gl', (Gl' = g_end \/ exists p q lis, Gl' = g_send p q lis) /\
   (forall n : fin, exists m : fin, guardG n m Gl') /\
   wfG Gl' /\
   gttTC Gl' G.
Proof.
  intros.
  pinversion H1. 
  - subst. exists g_end. split; try easy. left. easy. split; try easy. split; try easy. pfold. easy.
  - subst. exists (g_send p q xs). split. right. exists p. exists q. exists xs. easy.
    split. easy. split. easy. pfold. easy.
  - subst.
    specialize(guard_breakG G0 H); intros. clear H2 H3.
    destruct H4 as (Gl',(Ha,(Hb,Hc))). exists Gl'. split; try easy. split; try easy.
    split.
    specialize(wfG_after_beta (g_rec G0) Gl' H0 Ha). easy. 
    specialize(gtt_after_betaL (g_rec G0) Gl'); intros. apply H2; try easy. pfold. easy.
  apply gttT_mon.
Qed. 

Lemma guard_cont : forall [lis1 p q],
    (forall n : fin, exists m : fin, guardG n m (g_send p q lis1)) -> 
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ 
      (forall n : fin, exists m : fin, guardG n m g)
    )) lis1.
Proof.
  induction lis1; intros; try easy.
  assert(Forall
           (fun u : option (sort * global) =>
            u = None \/
            (exists (s : sort) (g : global),
               u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g)))
           lis1).
  {
    specialize(IHlis1 p q). apply IHlis1; try easy.
    intros. specialize(H n). destruct H. exists x. 
    inversion H. subst. constructor.
    subst. constructor. inversion H3; try easy.
  }
  constructor; try easy.
  destruct a. 
  - right. destruct p0. exists s. exists g.
    split. easy. intros. specialize(H (n.+1)). destruct H. exists x.
    inversion H. subst. inversion H4. subst. destruct H3; try easy.
    destruct H1 as (s0,(g0,(Ha,Hb))). inversion Ha. subst. easy.
  - left. easy.
Qed.

Lemma guard_cont_b : forall [xs s s'],
    Forall
       (fun u : option (sort * global) =>
        u = None \/
        (exists (s : sort) (g : global),
           u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) xs -> 
    (forall n : fin, exists m : fin, guardG n m (g_send s s' xs)).
Proof.
  induction xs; intros; try easy. 
  - exists 0. destruct n; try easy. constructor. constructor. easy.
  - inversion H. subst.
    specialize(IHxs s s' H3).
    specialize(IHxs n). destruct IHxs as (m,H0).
    clear H H3.
    inversion H0. subst. exists 0. constructor.
    subst.
    destruct H2.
    - subst. exists m.
      constructor. constructor; try easy. left. easy.
    - destruct H as (s1,(g1,(Ha,Hb))). subst.
      specialize(Hb n0).
      destruct Hb as (m1, Hb). exists (Nat.max m m1).
      constructor; try easy. constructor.
      - right. exists s1. exists g1. split. easy.  
        apply guardG_more with (m := m1); try easy.
        apply max_r; try easy.
      - apply Forall_forall; intros.
        specialize(Forall_forall (fun u : option (sort * global) =>
        u = None \/
        (exists (s : sort) (g : global), u = Some (s, g) /\ guardG n0 m g)) xs); intros.
        destruct H1. specialize(H1 H4). clear H2 H4. specialize(H1 x H).
        destruct H1. left. easy.
        destruct H1 as (s0,(g0,(Hta,Htb))). subst. right.  
        exists s0. exists g0. split. easy. 
        apply guardG_more with (m := m); try easy.
        apply max_l; try easy.
Qed.


Lemma balanced_cont : forall [lsg p q],
    balancedG (gtt_send p q lsg) -> List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ balancedG g)) lsg.
Proof.
  intros. 
  apply Forall_forall; intros.
  destruct x.
  - right. destruct p0. exists s. exists g. split. easy.
    specialize(in_some_implies_onth (s, g) lsg H0); intros.
    destruct H1 as (n, H1). clear H0.
    unfold balancedG. 
    intros.
    unfold balancedG in H.
    specialize(H (n :: w) w' p0 q0 gn).
    assert(gttmap (gtt_send p q lsg) (n :: w) None gn).
    {
      apply gmap_con with (st := s) (gk := g); try easy.
    }
    assert(gttmap (gtt_send p q lsg) ((n :: w) ++ w') None (gnode_pq p0 q0) \/
    gttmap (gtt_send p q lsg) ((n :: w) ++ w') None (gnode_pq q0 p0)).
    {
      destruct H2. left.
      apply gmap_con with (st := s) (gk := g); try easy.
      right.
      apply gmap_con with (st := s) (gk := g); try easy.
    }
    specialize(H H3 H4).
    destruct H as (k, H). exists k.
    intros. specialize(H w'0).
    assert(gttmap (gtt_send p q lsg) ((n :: w) ++ w'0) None gnode_end \/
    Datatypes.length w'0 = k /\ (exists tc : gnode, gttmap (gtt_send p q lsg) ((n :: w) ++ w'0) None tc)).
    {
      destruct H5. left.
      apply gmap_con with (st := s) (gk := g); try easy.
      right.
      destruct H5. split. easy.
      destruct H6. exists x.
      apply gmap_con with (st := s) (gk := g); try easy.
    }
    specialize(H H6).
    destruct H as (w2,(w0,(H,Ha))).
    destruct Ha as (r,Ha).
    exists w2. exists w0. split. easy. exists r. 
    {
      destruct Ha. left.
      inversion H7; try easy. subst. 
      specialize(eq_trans (esym H1) H15); intros. inversion H. subst. easy.
      right.
      inversion H7; try easy. subst.
      specialize(eq_trans (esym H1) H15); intros. inversion H. subst. easy.
    }
    left. easy.
Qed.


Lemma wfgC_after_step_all : forall [ys s s'],
    s <> s' -> wfgC (gtt_send s s' ys) -> List.Forall (fun u => u = None \/ (exists st g, u = Some(st, g) /\ wfgC g)) ys.
Proof.
  intros. apply Forall_forall; intros.
  destruct x. 
  - specialize(in_some_implies_onth p ys H1); intros.
    destruct H2. rename x into l. clear H1. 
    right. destruct p. exists s0. exists g. split. easy.
    unfold wfgC in *.
    destruct H0 as (Gl,(Ha,(Hb,(Hc,Hd)))).
    pinversion Ha; try easy.
    - subst.
      specialize(Forall2_prop_l l xs ys (s0, g) (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : global) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) H2 H3); intros.
      destruct H0 as (p',(He,Hf)). 
      destruct p'. destruct Hf; try easy.
      destruct H0 as (s1,(g1,(g2,(Hf,(Hg,Hh))))). inversion Hf. inversion Hg. subst.
      exists g1. pclearbot.
      - split. easy.
      - inversion Hb. subst.
        specialize(Forall_prop l xs (s1, g1) (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ wfG g)) He H7); intros.
        simpl in H0. destruct H0; try easy. destruct H0 as (s2,(g3,(Hi,Hj))).
        inversion Hi. subst.
        split. easy.
      - specialize(guard_cont Hc); intros.
        specialize(Forall_prop l xs (s2, g3) (fun u : option (sort * global) =>
        u = None \/
        (exists (s : sort) (g : global),
           u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) He H0); intros.
        simpl in H1. destruct H1; try easy. destruct H1 as (s3,(g4,(Hk,Hl))).
        inversion Hk. subst. split. easy.
      - specialize(balanced_cont Hd); intros.
        specialize(Forall_prop l ys (s3, g2) (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) H2 H1); intros.
        simpl in H4. destruct H4; try easy. destruct H4 as (s4,(g5,(Hm,Hn))).
        inversion Hm. subst. easy.
      - destruct Hf; try easy. destruct H0 as (s1,(g1,(g2,Hf))). easy.
    - subst.
      clear H0 H1. clear Q.
      specialize(guard_breakG G Hc); intros.
      destruct H0 as (T,(Hte,(Htf,Htg))).
      specialize(gttTC_after_subst (g_rec G) T (gtt_send s s' ys)); intros.
      assert(gttTC T (gtt_send s s' ys)). apply H0; try easy. pfold. easy.
      destruct Htg. subst. pinversion H1; try easy. apply gttT_mon.
      destruct H3 as (p1,(q1,(lis,Htg))). subst. 
      pinversion H1; try easy. subst. clear H0.
      specialize(wfG_after_beta (g_rec G) (g_send s s' lis) Hb Hte); intros.
      clear Hc Hb Ha Hte.
      specialize(Forall2_prop_l l lis ys (s0, g) (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : global) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) H2 H4); intros.
      destruct H3 as (p',(He,Hf)). 
      destruct p'. destruct Hf; try easy.
      destruct H3 as (s1,(g1,(g2,(Hf,(Hg,Hh))))). inversion Hf. inversion Hg. subst.
      exists g1. pclearbot.
      - split. easy.
      - inversion H0. subst.
        specialize(Forall_prop l lis (s1, g1) (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ wfG g)) He H9); intros.
        simpl in H3. destruct H3; try easy. destruct H3 as (s2,(g3,(Hi,Hj))).
        inversion Hi. subst.
        split. easy.
      - specialize(guard_cont Htf); intros.
        specialize(Forall_prop l lis (s2, g3) (fun u : option (sort * global) =>
        u = None \/
        (exists (s : sort) (g : global),
           u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) He H3); intros.
        simpl in H5. destruct H5; try easy. destruct H5 as (s3,(g4,(Hk,Hl))).
        inversion Hk. subst. split. easy.
      - specialize(balanced_cont Hd); intros.
        specialize(Forall_prop l ys (s3, g2) (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) H2 H5); intros.
        simpl in H6. destruct H6; try easy. destruct H6 as (s4,(g5,(Hm,Hn))).
        inversion Hm. subst. easy.
      - destruct Hf; try easy. destruct H3 as (s1,(g1,(g2,Hf))). easy.
    apply gttT_mon. apply gttT_mon.
  - left. easy.
Qed.


Lemma wfgCw_after_step_all : forall [ys s s'],
    s <> s' -> wfgCw (gtt_send s s' ys) -> List.Forall (fun u => u = None \/ (exists st g, u = Some(st, g) /\ wfgCw g)) ys.
Proof.
  intros. apply Forall_forall; intros.
  destruct x. 
  - specialize(in_some_implies_onth p ys H1); intros.
    destruct H2. rename x into l. clear H1. 
    right. destruct p. exists s0. exists g. split. easy.
    unfold wfgC in *.
    destruct H0 as (Gl,(Ha,(Hb,Hc))).
    pinversion Ha; try easy.
    - subst.
      specialize(Forall2_prop_l l xs ys (s0, g) (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : global) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) H2 H3); intros.
      destruct H0 as (p',(He,Hf)). 
      destruct p'. destruct Hf; try easy.
      destruct H0 as (s1,(g1,(g2,(Hf,(Hg,Hh))))). inversion Hf. inversion Hg. subst.
      exists g1. pclearbot.
      - split. easy.
      - inversion Hb. subst.
        specialize(Forall_prop l xs (s1, g1) (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ wfG g)) He H7); intros.
        simpl in H0. destruct H0; try easy. destruct H0 as (s2,(g3,(Hi,Hj))).
        inversion Hi. subst.
        split. easy.
      - specialize(guard_cont Hc); intros.
        specialize(Forall_prop l xs (s2, g3) (fun u : option (sort * global) =>
        u = None \/
        (exists (s : sort) (g : global),
           u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) He H0); intros.
        simpl in H1. destruct H1; try easy. destruct H1 as (s3,(g4,(Hk,Hl))).
        inversion Hk. subst. revert n. easy.
      - destruct Hf; try easy. destruct H0 as (s1,(g1,(g2,Hf))). easy.
    - subst.
      clear H0 H1. clear Q.
      specialize(guard_breakG G Hc); intros.
      destruct H0 as (T,(Hte,(Htf,Htg))).
      specialize(gttTC_after_subst (g_rec G) T (gtt_send s s' ys)); intros.
      assert(gttTC T (gtt_send s s' ys)). apply H0; try easy. pfold. easy.
      destruct Htg. subst. pinversion H1; try easy. apply gttT_mon.
      destruct H3 as (p1,(q1,(lis,Htg))). subst. 
      pinversion H1; try easy. subst. clear H0.
      specialize(wfG_after_beta (g_rec G) (g_send s s' lis) Hb Hte); intros.
      clear Hc Hb Ha Hte.
      specialize(Forall2_prop_l l lis ys (s0, g) (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : global) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) H2 H4); intros.
      destruct H3 as (p',(He,Hf)). 
      destruct p'. destruct Hf; try easy.
      destruct H3 as (s1,(g1,(g2,(Hf,(Hg,Hh))))). inversion Hf. inversion Hg. subst.
      exists g1. pclearbot.
      - split. easy.
      - inversion H0. subst.
        specialize(Forall_prop l lis (s1, g1) (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ wfG g)) He H9); intros.
        simpl in H3. destruct H3; try easy. destruct H3 as (s2,(g3,(Hi,Hj))).
        inversion Hi. subst.
        split. easy.
      - specialize(guard_cont Htf); intros.
        specialize(Forall_prop l lis (s2, g3) (fun u : option (sort * global) =>
        u = None \/
        (exists (s : sort) (g : global),
           u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) He H3); intros.
        simpl in H5. destruct H5; try easy. destruct H5 as (s3,(g4,(Hk,Hl))).
        inversion Hk. subst. revert n. easy.
      - destruct Hf; try easy. destruct H3 as (s1,(g1,(g2,Hf))). easy.
    apply gttT_mon. apply gttT_mon.
  - left. easy.
Qed.

Lemma wfgCw_triv : forall s s0 l, wfgCw (gtt_send s s0 l) -> s <> s0 /\ SList l.
Proof.
  intros.
  unfold wfgC in H.
  destruct H as (Gl,(Ha,(Hb,Hc))).
  specialize(guard_breakG_s2 (gtt_send s s0 l) Gl Hc Hb Ha); intros.
  clear Ha Hb Hc. clear Gl.
  destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))).
  destruct Ha.
  - subst. pinversion Hd; try easy. apply gttT_mon.
  - destruct H as (p1,(q1,(lis,Ha))). subst.
    pinversion Hd; try easy. subst. clear Hd Hb.
    inversion Hc. subst. split. easy.
    clear H4 H5 Hc.
    revert H3 H0. revert lis. clear s s0.
    induction l; intros; try easy.
    - destruct lis; try easy.
    - destruct lis; try easy.
      inversion H0. subst. clear H0.
      specialize(SList_f o lis H3); intros. clear H3.
      destruct H.
      - apply SList_b. specialize(IHl lis). apply IHl; try easy.
      - destruct H as (H,(a1,H1)). subst.
        destruct H4; try easy. destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
        destruct l; try easy.
    apply gttT_mon.
Qed.

Lemma wfgC_triv : forall s s0 l, wfgC (gtt_send s s0 l) -> s <> s0 /\ SList l.
Proof.
  intros.
  unfold wfgC in H.
  apply wfgCw_triv. unfold wfgCw.
  destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))).
  exists Gl. easy.
Qed.

Lemma guard_contG : forall n st st' x1 s3 g,
        (forall n : fin, exists m : fin, guardG n m (g_send st st' x1)) -> 
        onth n x1 = Some (s3, g) -> 
        (forall n0 : fin, exists m : fin, guardG n0 m g).
Proof.
  intros. specialize(H (S n0)). destruct H. inversion H. subst. clear H.
  revert H4 H0. revert n0 x g s3 x1 st st'.
  induction n; intros; try easy.
  - destruct x1; try easy. simpl in H0. subst. exists x.
    inversion H4. subst.
    destruct H1; try easy. destruct H as (s1,(g1,(Hta,Htb))). inversion Hta. subst. easy.
  - destruct x1; try easy.
    inversion H4. subst. clear H4.
    specialize(IHn n0 x g s3 x1). apply IHn; try easy. 
Qed.










Definition ctxS := list (option sort).
Definition ctxT := list (option ltt).


Inductive typ_expr: ctxS -> expr -> sort -> Prop :=
  | sc_var : forall c s t, Some t = onth s c -> typ_expr c (e_var s) t
  | sc_vali: forall c i, typ_expr c (e_val (vint i)) sint
  | sc_valn: forall c i, typ_expr c (e_val (vnat i)) snat
  | sc_valb: forall c b, typ_expr c (e_val (vbool b)) sbool
  | sc_succ: forall c e, typ_expr c e snat ->
                         typ_expr c (e_succ e) snat
  | sc_neg : forall c e, typ_expr c e sint ->
                         typ_expr c (e_neg e) sint
  | sc_sub : forall c e s s', typ_expr c e s ->
                                 subsort s s' ->
                                 typ_expr c e s'
  | sc_not : forall c e, typ_expr c e sbool ->
                         typ_expr c (e_not e) sbool
  | sc_gt  : forall c e1 e2, typ_expr c e1 sint ->
                             typ_expr c e2 sint ->
                             typ_expr c (e_gt e1 e2) sbool
  | sc_plus: forall c e1 e2, typ_expr c e1 sint ->
                             typ_expr c e2 sint ->
                             typ_expr c (e_plus e1 e2) sint
  | sc_det  : forall c e1 e2 s, typ_expr c e1 s -> typ_expr c e2 s -> typ_expr c (e_det e1 e2) s.


(*  depth *)
Inductive typ_proc: ctxS -> ctxT -> process -> ltt -> Prop :=
  | tc_inact: forall cs ct,     typ_proc cs ct (p_inact) (ltt_end)
  | tc_var  : forall cs ct s t, Some t = onth s ct -> wfC t ->
                                typ_proc cs ct (p_var s) t
  | tc_mu   : forall cs ct p t,       typ_proc cs (Some t :: ct) p t ->
                                      typ_proc cs ct (p_rec p) t
  | tc_ite  : forall cs ct e p1 p2 T, typ_expr cs e sbool ->
                                      typ_proc cs ct p1 T ->
                                      typ_proc cs ct p2 T ->
                                      typ_proc cs ct (p_ite e p1 p2) T
  | tc_sub  : forall cs ct p t t',    typ_proc cs ct p t ->
                                      subtypeC t t' -> wfC t' ->
                                      typ_proc cs ct p t'
  | tc_recv : forall cs ct p STT P,
                     length P = length STT -> SList P ->
                     Forall2 (fun u v => (u = None /\ v = None) \/ 
                     (exists p s t, u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: cs) ct p t)) P STT ->
                     typ_proc cs ct (p_recv p P) (ltt_recv p STT)
  | tc_send : forall cs ct p l e P S T, typ_expr cs e S ->
                                        typ_proc cs ct P T ->
                                        typ_proc cs ct (p_send p l e P) (ltt_send p (extendLis l (Some (S,T)))).

Section typ_proc_ind_ref.
  Variable P : ctxS -> ctxT -> process -> ltt -> Prop.
  Hypothesis P_inact : forall cs ct, P cs ct p_inact ltt_end.
  Hypothesis P_var   : forall cs ct s t, Some t = onth s ct -> wfC t -> P cs ct (p_var s) t.
  Hypothesis P_mu    : forall cs ct p t, P cs (Some t :: ct) p t -> P cs ct (p_rec p) t.
  Hypothesis P_ite   : forall cs ct e p1 p2 T, typ_expr cs e sbool -> P cs ct p1 T -> P cs ct p2 T -> P cs ct (p_ite e p1 p2) T.
  Hypothesis P_sub   : forall cs ct p t t', P cs ct p t -> subtypeC t t' -> wfC t' -> P cs ct p t'.
  Hypothesis P_recv  : forall cs ct p STT Pr, length Pr = length STT -> SList Pr ->
                     Forall2 (fun u v => (u = None /\ v = None) \/ 
                     (exists p s t, u = Some p /\ v = Some (s, t) /\ P (Some s :: cs) ct p t)) Pr STT ->
                     P cs ct (p_recv p Pr) (ltt_recv p STT).
  Hypothesis P_send  : forall cs ct p l e Pr S T, typ_expr cs e S -> P cs ct Pr T -> P cs ct (p_send p l e Pr) (ltt_send p (extendLis l (Some (S,T)))).
  
  Fixpoint typ_proc_ind_ref (cs : ctxS) (ct : ctxT) (p : process) (T : ltt) (a : typ_proc cs ct p T) {struct a} : P cs ct p T.
  Proof.
    refine (match a with
      | tc_inact s t => P_inact s t 
      | tc_var s t s1 t1 Hsl Hwf => P_var s t s1 t1 Hsl Hwf
      | tc_mu sc tc pr t Ht => P_mu sc tc pr t (typ_proc_ind_ref sc (Some t :: tc) pr t Ht)
      | tc_ite sc tc ex p1 p2 t He Hp1 Hp2 => P_ite sc tc ex p1 p2 t He (typ_proc_ind_ref sc tc p1 t Hp1) (typ_proc_ind_ref sc tc p2 t Hp2)
      | tc_sub sc tc pr t t' Ht Hst Hwf => P_sub sc tc pr t t' (typ_proc_ind_ref sc tc pr t Ht) Hst Hwf
      | tc_recv sc st p STT Pr HST HSl Hm => P_recv sc st p STT Pr HST HSl _
      | tc_send sc tc p l ex Pr Sr Tr He HT => P_send sc tc p l ex Pr Sr Tr He (typ_proc_ind_ref sc tc Pr Tr HT)
    end); try easy.
    revert Hm.
    apply Forall2_mono. intros.
    destruct H. left. easy. destruct H. destruct H. destruct H. right. exists x0, x1, x2.
    destruct H. destruct H0. split. easy. split. easy.
    apply typ_proc_ind_ref. easy.
  Qed.

End typ_proc_ind_ref.

Lemma natb_to_prop : forall a b, (a =? b)%nat = true -> a = b.
Proof. 
    intros a b.
    specialize(Nat.eqb_eq a b); intro H1.
    destruct H1.
    easy.
Qed.

Lemma natb_to_propf : forall a b, (a =? b)%nat = false -> a <> b.
Proof.
    intros a b.
    specialize(Nat.eqb_neq a b); intro H1.
    destruct H1.
    easy.
Qed.

Lemma typable_implies_wfC_helper_p2 : forall x T',
      lttTC (l_rec x) T' ->
      wfL (l_rec x) -> 
      (forall n, exists m, guardL n m (l_rec x)) ->
      exists T, lttTC T T' /\ wfL T /\ (forall n, exists m, guardL n m T) /\ (T = l_end \/ (exists p lis, T = l_send p lis \/ T = l_recv p lis)).
Proof.
      intros.
      specialize(guard_break x H1); intros.
      destruct H2. exists x0. destruct H2.
      split.
      - clear H0 H1 H3.
        revert H. revert T'. induction H2; intros; try easy.
        inversion H. subst. 
        pinversion H0. subst. 
        specialize(subst_injL 0 0 (l_rec G) G Q y H1 H3); intros. subst.
        unfold lttTC. pfold. easy.
        apply lttT_mon.
      - apply IHmultiS; try easy.
        inversion H. subst.
        pinversion H0. subst. 
        specialize(subst_injL 0 0 (l_rec G) G Q y H1 H4); intros. subst.
        unfold lttTC. pfold. easy.
        apply lttT_mon.
      split; try easy.
      - clear H H1 H3.
        revert H0. revert T'. induction H2; intros; try easy.
        inversion H. subst.
        inversion H0. subst.
        specialize(wfL_after_subst y (l_rec G) G 0 0); intros. apply H2; try easy.
      - apply IHmultiS; try easy.
         inversion H. subst.
        inversion H0. subst.
        specialize(wfL_after_subst y (l_rec G) G 0 0); intros. apply H3; try easy.
Qed.

Lemma typable_implies_wfC_helper_recv : forall x p STT,
      lttTC x (ltt_recv p STT) ->
      wfL x -> 
      (forall n, exists m, guardL n m x) ->
      exists T, lttTC (l_recv p T) (ltt_recv p STT) /\ wfL (l_recv p T) /\ (forall n, exists m, guardL n m (l_recv p T)).
Proof.
  induction x using local_ind_ref; intros; try easy.
  - pinversion H.
    apply lttT_mon.
  - pinversion H.
    apply lttT_mon.
  - exists lis. 
    pinversion H0. subst. 
    apply lttT_mon.
  - exists lis.
    pinversion H0. subst.
    split.
    pfold. easy. easy.
    apply lttT_mon.
  - pinversion H. subst.
    
    specialize(typable_implies_wfC_helper_p2 x (ltt_recv p STT)); intros.
    unfold lttTC in H2 at 1. 
    assert (exists T : local,
       lttTC T (ltt_recv p STT) /\
       wfL T /\
       (forall n : fin, exists m : fin, guardL n m T) /\
       (T = l_end \/
        (exists
           (p : string) (lis : seq.seq (option (sort * local))),
           T = l_send p lis \/ T = l_recv p lis))).
    {
      apply H2; try easy.
      pfold. easy.
    }
    clear H2. destruct H5. destruct H2. destruct H5. destruct H6.
    pinversion H2. subst.
    - destruct H7; try easy. destruct H7. destruct H7. destruct H7. easy.
      inversion H7. subst. exists x1. unfold lttTC. split. pfold. easy. easy.
    - subst. destruct H7; try easy. destruct H7. destruct H7. destruct H7; try easy.
    apply lttT_mon.
    apply lttT_mon.
Qed.


Lemma typable_implies_wfC_helper_recv2 : forall STT Pr p,
    SList Pr ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt), u = Some p /\ v = Some (s, t) /\ wfC t)) Pr STT ->
    wfC (ltt_recv p STT).
Proof.
  induction STT; intros; try easy.
  - destruct Pr; try easy.
  - destruct Pr; try easy.
    inversion H0. subst.
    unfold wfC. destruct H4.
    - destruct H1. subst. 
      specialize(IHSTT Pr p H H6).
      unfold wfC in IHSTT. destruct IHSTT. destruct H1. destruct H2.
      specialize(typable_implies_wfC_helper_recv x p STT H1 H2 H3); intros.
      destruct H4. destruct H4. destruct H5. 
      exists (l_recv p (None :: x0)).
      split.
      - pinversion H4. subst.
        unfold lttTC. pfold. constructor. constructor; try easy. left. easy.
        apply lttT_mon.
      split; try easy.
      - inversion H5. subst. constructor; try easy. constructor; try easy.
        left. easy. 
        intros. specialize(H7 n). destruct H7. inversion H7. subst. exists 0. apply gl_nil.
        subst. exists x1. constructor; try easy. constructor; try easy. left. easy.
    - destruct H1. destruct H1. destruct H1. destruct H1. destruct H2. subst. clear H0.
      unfold wfC in H3. destruct H3. destruct H0. destruct H1.
      specialize(SList_f (Some x) Pr H); intros. destruct H3.
      - specialize(IHSTT Pr p H3 H6). 
        unfold wfC in IHSTT. destruct IHSTT. destruct H4. destruct H5.
        specialize(typable_implies_wfC_helper_recv x3 p STT H4 H5 H7); intros.
        destruct H8. destruct H8. destruct H9.
        exists (l_recv p (Some (x0, x2) :: x4)).
        split.
        - pfold. constructor.
          pinversion H8. subst. constructor; try easy.
          right. exists x0. exists x2. exists x1. split. easy. split. easy.
          left. easy.
          apply lttT_mon.
        split.
        - constructor; try easy.
          specialize(SList_f (Some x) Pr H); intros.
          {
            clear H4 H5 H7 H H0 H1 H2 H3 H9 H10.
            destruct H11.
            apply SList_b. pinversion H8. subst. clear H8. clear p x3 x x0 x1 x2. 
            revert H6 H1 H. revert Pr x4. induction STT; intros; try easy.
            - destruct Pr; try easy.
            - destruct Pr; try easy.
              destruct x4; try easy.
              inversion H6. subst. clear H6. inversion H1. subst. clear H1.
              specialize(SList_f o Pr H); intros. destruct H0.
              - apply SList_b. apply IHSTT with (Pr := Pr); try easy.
              - destruct H0. destruct H1. subst.
                destruct STT; try easy. destruct x4; try easy.
                destruct H4; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. inversion H0. subst.
                destruct H5; try easy. destruct H1. destruct H1. destruct H1. destruct H1. destruct H3. inversion H3. subst. easy.
                apply lttT_mon.
            - destruct H. subst. destruct STT; try easy.
              pinversion H8. subst. destruct x4; try easy.
              apply lttT_mon.
          }
        - pinversion H8. subst. constructor.
          right. exists x0. exists x2. split; try easy.
          inversion H9. subst. easy.
          apply lttT_mon.
        - clear H4 H5 H7 H H0 H1 H6 H3 H8 H9.
          clear STT x3 Pr x x1.
          intros.
          destruct n. exists 0. apply gl_nil.
          specialize(H2 n). specialize(H10 (S n)). destruct H2. destruct H10.
          exists (ssrnat.maxn x1 x). apply gl_recv.
          constructor.
          - right. exists x0. exists x2. split; try easy.
            specialize(guardL_more n x); intros. apply H1; try easy.
            specialize(ssrnat.leq_maxr x1 x); intros. easy.
          - inversion H0. subst. clear H0 H. clear p x0 x2. revert H4. revert n x x1.
            induction x4; intros; try easy.
            inversion H4. subst.
            constructor; try easy.
            destruct H1.
            - left. easy.
            - right. destruct H. destruct H. destruct H. subst. exists x0. exists x2.
              split; try easy.
              specialize(guardL_more n x1 (ssrnat.maxn x1 x) x2 H0); intros.
              apply H.
              specialize(ssrnat.leq_maxl x1 x); intros. easy.
            apply IHx4; try easy.
      - destruct H3. destruct H4. subst.
        destruct STT; try easy. inversion H4. subst.
        exists (l_recv p [Some (x0, x2)]).
        split.
        - unfold lttTC. pfold. constructor.
          constructor. right. exists x0. exists x2. exists x1.
          split. easy. split. easy.
          left. easy.
        - easy.
        split.
        - constructor. easy.
          constructor. right. exists x0. exists x2. split; try easy.
        - easy.
        - intro. 
          destruct n. exists 0. apply gl_nil.
          specialize(H2 n). destruct H2.
          exists x. apply gl_recv. constructor; try easy.
          right. exists x0. exists x2. split. easy. easy.
Qed.
  
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

Lemma _a23_a: forall p Q P Gs Gt T, 
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
(* 
Lemma _a23_b: forall p l e Q P Gs Gt T, 
  typ_proc Gs Gt P T ->
  P = (p_send p l e Q) -> exists S S' T', typ_expr Gs e S /\ typ_proc Gs Gt Q T' /\ subsort S' S /\ subtypeC (ltt_send p [(l,(S',T'))]) T.
Proof. intros p l e Q P Gs Gt T H.
       induction H; intros; try easy.
       specialize(IHtyp_proc H1).
       destruct IHtyp_proc as (S,(S',(T',Ha))).
       exists S. exists S'. exists T'.
       split.
       specialize(sc_sub cs e S S); intro HSS.
       apply HSS. easy. apply srefl. 
       split.
       specialize(tc_sub cs ct Q T' T'); intro HTS.
       apply HTS. easy.
       apply stRefl. split. easy.
       destruct Ha as (Ha,(Hb,(Hc,Hd))).
       specialize(stTrans (ltt_send p [(l, (S', T'))]) t t' Hd H0); intro HT.
       apply HT.
       exists S. exists S. exists T.
       inversion H1. subst.
       split. easy. split. easy.
       split. apply srefl.
       apply stRefl. 
Qed.
 *)
Lemma _a23_bf: forall p l e Q P Gs Gt T, 
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
(* 
Lemma _a23_bs: forall p l e Q P Gs Gt T, 
  typ_proc Gs Gt P T ->
  P = (p_send p l e Q) -> forall S T', subtypeC (ltt_send p [(l,(S,T'))]) T -> 
  typ_expr Gs e S /\ typ_proc Gs Gt Q T'.
Proof.
  intros. revert H0. induction H; intros; try easy.
  specialize(IHtyp_proc H1); intros. 
  specialize(stTrans (ltt_send p [(l, (S, T'))]) t t' IHtyp_proc H0); intros; try easy.
  inversion H3. subst.
  exists S. exists T. split; try easy. 
Qed.
 *)
Lemma _a23_c: forall P e Q1 Q2 T Gs Gt,
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

Lemma _a23_d: forall P Q T' Gs Gt,
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


Lemma _a23_e: forall P X T Gs Gt,
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
       

Lemma _a23_f: forall P T Gs Gt,
  typ_proc Gs Gt P T ->
  P = p_inact -> T = ltt_end.
Proof. intros.
       induction H; intros; try easy.
       subst. 
       specialize(IHtyp_proc (erefl p_inact)). 
       subst.
       punfold H1. inversion H1. easy.
       apply subtype_monotone; try easy.
Qed.


Lemma inv_expr_var : forall ex n Gs S,
  typ_expr Gs ex S -> ex = (e_var n) -> 
  exists S', onth n Gs = Some S' /\ subsort S' S.
Proof.
  intros. induction H; intros; try easy.
  - inversion H0. subst. exists t. split. easy. apply srefl.
  - specialize(IHtyp_expr H0); intros. destruct IHtyp_expr. destruct H2.
    exists x. split. easy. specialize(sstrans x s s' H3 H1); easy.
Qed.

Lemma inv_expr_vali : forall Gs ex S n,
  typ_expr Gs ex S -> ex = (e_val n) -> ((exists k, S = sint /\ n = vint k) \/ (exists k, subsort snat S /\ n = vnat k) \/ (exists k, S = sbool /\ n = vbool k)).
Proof.
  intros. induction H; intros; try easy. inversion H0. subst.
  - left. exists i. easy. 
  - inversion H0. subst. right. left. exists i. split. apply srefl. easy.
  - inversion H0. subst. right. right. exists b. easy.
  specialize(IHtyp_expr H0); intros. 
  destruct IHtyp_expr. 
  - destruct H2. destruct H2. subst. 
    inversion H1. subst.
    left. exists x. easy.
  - subst. inversion H2. destruct H0. destruct H0. subst. inversion H0. subst.
    inversion H1. subst. right. left. exists x.
    split. apply sni. easy.
  - subst. inversion H1. subst. right. left. exists x. split. apply sni. easy.
    subst. right. left. exists x. easy.
  - inversion H0. destruct H3. subst.
    inversion H1. subst. right. right. exists x. easy.
Qed.
  
Lemma inv_expr_succ : forall Gs ex S n,
  typ_expr Gs ex S -> ex = (e_succ n) -> typ_expr Gs n snat /\ (S = snat \/ S = sint). 
Proof.
  intros. induction H; intros; try easy. 
  - inversion H0. subst. split. easy. left. easy.
  - specialize(IHtyp_expr H0); intros.
    destruct IHtyp_expr. destruct H3.
    split. easy. inversion H1. subst. right. easy. subst. left. easy.
  - split. easy. subst. inversion H1. subst. right. easy.
Qed. 

Lemma inv_expr_neg : forall Gs ex S n,
  typ_expr Gs ex S -> ex = (e_neg n) -> S = sint /\ typ_expr Gs n sint.
Proof.
  intros. induction H; try easy. 
  inversion H0. subst. easy.
  inversion H1. subst. 
  - specialize(IHtyp_expr (erefl (e_neg n))). destruct IHtyp_expr. easy.
  - subst. apply IHtyp_expr. easy.
Qed.

Lemma inv_expr_not : forall Gs ex S n,
  typ_expr Gs ex S -> ex = (e_not n) -> S = sbool /\ typ_expr Gs n sbool.
Proof.
  intros. induction H; try easy.
  inversion H1. subst. 
  specialize(IHtyp_expr (erefl (e_not n))); easy.
  subst. apply IHtyp_expr. easy.
  inversion H0. subst. easy.
Qed.

Lemma inv_expr_gt : forall Gs ex S m n,
  typ_expr Gs ex S -> ex = (e_gt m n) -> S = sbool /\ typ_expr Gs m sint /\ typ_expr Gs n sint.
Proof.
  intros. induction H; try easy.
  - inversion H1; try easy. subst.
    specialize(IHtyp_expr (erefl (e_gt m n))); try easy.
    subst. apply IHtyp_expr; try easy.
  - inversion H0. subst. easy. 
Qed.

Lemma inv_expr_plus : forall Gs ex S m n,
  typ_expr Gs ex S -> ex = (e_plus m n) -> S = sint /\ typ_expr Gs m sint /\ typ_expr Gs n sint.
Proof.
  intros. induction H; try easy.
  - inversion H1; try easy. subst.
    specialize(IHtyp_expr (erefl (e_plus m n ))); try easy.
    subst. apply IHtyp_expr; try easy.
  - inversion H0. subst. try easy.
Qed.

Lemma inv_expr_det : forall Gs ex S m n,
  typ_expr Gs ex S -> ex = (e_det m n) -> exists k, typ_expr Gs m k /\ typ_expr Gs n k /\ subsort k S.
Proof.
  intros. induction H; try easy.
  specialize(IHtyp_expr H0). destruct IHtyp_expr. destruct H2. destruct H3.
  exists x. split; try easy. split; try easy.
  apply sstrans with (s2 := s); intros; try easy.
  exists s. inversion H0. subst. split; try easy. split. easy.
  apply srefl.
Qed.








Fixpoint RemoveT (n : fin) (Gt : ctxT) : ctxT :=
  match Gt with 
    | x::xs =>
      match n with 
        | S m => x :: RemoveT m xs
        | 0   => None :: xs 
      end
    | [] => []
  end.

Fixpoint extendT (n : fin) (T : ltt) (Gt : ctxT) : ctxT :=
  match Gt with 
    | x::xs =>
      match n with 
        | S m => x :: extendT m T xs
        | 0   => Some T :: xs 
      end 
    | [] =>
      match n with 
        | S m => None :: extendT m T [] 
        | 0   => [Some T]
      end 
  end.
  
Lemma onth_nil : forall n, @onth ltt n [] = None.
Proof.
  intros. induction n. easy. easy.
Qed.

Lemma remove_var : forall X n T Gt x, X <> n -> onth n (extendT X T Gt) = Some x -> onth n Gt = Some x.
Proof.
  intros X n T Gt. revert X T Gt. induction n; intros; try easy.
  destruct X; try easy. destruct Gt. easy. simpl in H0. simpl. easy.
  destruct X. destruct Gt; try easy. simpl in H0. simpl. 
  specialize(onth_nil n); intros.
  specialize(eq_trans (ssrfun.esym H1) H0); intros. easy.
  specialize(Nat.succ_inj_wd_neg X n); intros. destruct H1. 
  specialize(H1 H); intros. clear H2.
  destruct Gt. 
  - simpl in H0.
    specialize(IHn X T [] x H1 H0); intros.
    specialize(onth_nil n); intros.
    specialize(eq_trans (ssrfun.esym H2) IHn); intros. easy.
  - simpl in *. 
    apply IHn with (X := X) (T := T); try easy.
Qed.

Lemma extend_extract : forall n (T : ltt) Gt, onth n (extendT n T Gt) = Some T.
Proof.
  intro n. induction n.
  intros t gt. revert t. induction gt.
  - intros. easy. intros. easy.
  - destruct Gt; try easy. simpl.
    - apply IHn.
    - simpl. apply IHn.
Qed.


Lemma typable_implies_wtyped_helper : forall Pr STT,
  Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt), u = Some p /\ v = Some (s, t) /\ wtyped p)) Pr STT ->
  Forall (fun u : option process => u = None \/ (exists k : process, u = Some k /\ wtyped k)) Pr.
Proof.
  intro Pr. induction Pr; intros; try easy.
  destruct STT; try easy.
  specialize(Forall2_cons_iff (fun (u : option process) (v : option (sort * ltt)) =>
       u = None /\ v = None \/
       (exists (p : process) (s : sort) (t : ltt), u = Some p /\ v = Some (s, t) /\ wtyped p)) a o Pr STT); intros.
  destruct H0. specialize(H0 H). clear H H1. destruct H0.
  apply Forall_cons; try easy.
  destruct H.
  - destruct H. subst. left. easy.
  - destruct H. destruct H. destruct H. destruct H. destruct H1. subst.
    right. exists x. easy.
  apply IHPr with (STT := STT); try easy.
Qed.

Lemma typable_implies_wtyped [Gs : ctxS] [Gt : ctxT] [P : process] [T : ltt] : typ_proc Gs Gt P T -> wtyped P.
Proof.
  intros. induction H using typ_proc_ind_ref.
  apply wp_inact.
  apply wp_var.
  apply wp_rec. easy.
  apply wp_ite; try easy. easy.
  apply wp_recv; try easy. 
  - apply typable_implies_wtyped_helper with (STT := STT); try easy.
  apply wp_send. easy.
Qed.

Lemma onth_exact {X} : forall (GtA GtB : list (option X)) T, onth (length GtA) (GtA ++ (T :: GtB)) = T.
Proof.
  intro GtA. induction GtA; intros; try easy.
  simpl. apply IHGtA.
Qed.

Lemma onth_more {X} : forall (GtA GtB : list (option X)) y T, length GtA <= y -> onth y.+1 (GtA ++ (T :: GtB)) = onth y (GtA ++ GtB).
Proof.
  intro GtA. induction GtA; intros; try easy.
  destruct y; try easy. apply IHGtA. easy.
Qed.

Lemma onth_less {X} : forall (GtA GtB : list (option X)) y T, y < length GtA -> length GtA <> y.+1 -> onth y.+1 (GtA ++ (T :: GtB)) = onth y.+1 (GtA ++ GtB). 
Proof.
  intro GtA. induction GtA; intros; try easy.
  destruct y; try easy. destruct GtA; try easy. 
  apply IHGtA; try easy. simpl in H0.
  specialize(Nat.succ_inj_wd_neg (length GtA) y.+1); intros. destruct H1. apply H1; try easy. 
Qed.

Lemma onth_morec {A} : forall l Gtl Gtr n X x (tm : option A),
      (l <= n) = true ->
      length Gtl = l ->
      onth (n + X)%coq_nat (Gtl ++ Gtr) = Some x ->
      Some x = onth (n + X.+1)%coq_nat (Gtl ++ tm :: Gtr).
Proof.
  intro l. induction l; intros; try easy.
  - specialize(length_zero_iff_nil Gtl); intros. destruct H2. specialize(H2 H0); intros. clear H3. subst.
    simpl.
    specialize(Nat.add_succ_r n X); intros. replace ((n + X.+1)%coq_nat) with ((n + X)%coq_nat.+1). simpl.
    simpl in H1. easy.
  - destruct n. easy.
    destruct Gtl; try easy.
    simpl in *.
    apply IHl; try easy.
    apply Nat.succ_inj. easy.
Qed.

Lemma onth_lessc {A} : forall l Gtl Gtr n x (tm : option A),
      (l <= n) = false ->
      length Gtl = l ->
      onth n (Gtl ++ Gtr) = Some x ->
      Some x = onth n (Gtl ++ tm :: Gtr).
Proof.
  intro l. induction l; intros; try easy.
  destruct Gtl; try easy.
  destruct n; try easy.
  simpl in *.
  apply IHl; try easy.
  apply Nat.succ_inj. easy.
Qed.

Lemma SList_map {A} : forall (f : A -> A) lis,  
  SList (map (fun u => match u with
    | Some x => Some (f x)
    | None   => None
  end) lis) -> SList lis.
Proof.
  intros f lis. induction lis; intros; try easy. 
  destruct a; try easy.
  destruct lis; try easy.  
  apply SList_b. apply IHlis. 
  simpl in H.
  specialize(SList_f (Some (f a)) (map (fun u : option A => match u with
                                     | Some x => Some (f x)
                                     | None => None
                                     end) (o :: lis)) H); intros.
  destruct H0; try easy. 
  
  apply SList_b. apply IHlis.
  simpl in H.
  easy.
Qed.

Lemma SList_map2 {A} : forall (f : A -> A) lis, SList lis -> 
  SList (map (fun u => match u with
    | Some x => Some (f x)
    | None   => None
  end) lis).
Proof.
  intros f lis. induction lis; intros; try easy.
  destruct a; try easy.
  destruct lis; try easy.
  apply SList_b. apply IHlis.
  easy.
  apply SList_b. apply IHlis. easy.
Qed.

Lemma slideT_helper : forall llp Gs Gtl tm Gtr l X m k x,
    length Gtl = l ->
    Forall
      (fun u : option process =>
       match u with
       | Some k =>
           forall (X m l k0 : fin) (tm : option ltt) (Gs : ctxS) (Gtl Gtr : list (option ltt)) (T : ltt),
           typ_proc Gs (Gtl ++ Gtr) (incr_free l k0 X m k) T ->
           length Gtl = l -> typ_proc Gs (Gtl ++ tm :: Gtr) (incr_free l k0 X.+1 m k) T
       | None => True
       end) llp ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (Gtl ++ Gtr) p t))
       (map
          (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp) x ->
    Forall2
      (fun (u : option process) (v : option (sort * ltt)) =>
       u = None /\ v = None \/
       (exists (p : process) (s : sort) (t : ltt),
          u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (Gtl ++ tm :: Gtr) p t))
      (map
         (fun u : option process =>
          match u with
          | Some p' => Some (incr_free l k.+1 X.+1 m p')
          | None => None
          end) llp) x.
Proof.
  intro llp. induction llp; intros; try easy.
  - destruct x; try easy.
  - destruct x; try easy.
    simpl in *.
    specialize(Forall2_cons_iff (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (Gtl ++ Gtr) p t)) (match a with
        | Some p' => Some (incr_free l k.+1 X m p')
        | None => None
        end) o (map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp) x); intros. destruct H2. clear H3. specialize(H2 H1). clear H1.
    destruct H2.
    specialize(Forall_cons_iff (fun u : option process =>
        match u with
        | Some k =>
            forall (X m l k0 : fin) (tm : option ltt) (Gs : ctxS) (Gtl Gtr : list (option ltt)) (T : ltt),
            typ_proc Gs (Gtl ++ Gtr) (incr_free l k0 X m k) T ->
            length Gtl = l -> typ_proc Gs (Gtl ++ tm :: Gtr) (incr_free l k0 X.+1 m k) T
        | None => True
        end) a llp); intros. destruct H3. clear H4. specialize(H3 H0). clear H0. destruct H3.
    apply Forall2_cons; try easy.
    - destruct a; try easy. destruct H1. easy.
      destruct H1. destruct H1. destruct H1. destruct H1. destruct H4. subst.
      right. exists (incr_free (length Gtl) k.+1 X.+1 m p), x1, x2. split. easy. split. easy. 
      inversion H1. subst. apply H0; try easy.
    - destruct H1. destruct H1. subst. left. easy.
      destruct H1. destruct H1. destruct H1. destruct H1. easy.
    apply IHllp; try easy.
Qed.

Lemma slideTp : forall Q X m l k tm Gs Gtl Gtr T,
typ_proc Gs (Gtl ++ Gtr) (incr_free l k X m Q) T -> length Gtl = l -> typ_proc Gs (Gtl ++ [tm] ++ Gtr) (incr_free l k X.+1 m Q) T.
Proof.
  intro Q.
  induction Q using process_ind_ref; intros; try easy.
  - simpl in *. 
    specialize(_a23_e (p_var (if l <= n then (n + X)%coq_nat else n)) (if l <= n then (n + X)%coq_nat else n) T Gs (Gtl ++ Gtr) H (erefl (p_var (if l <= n then (n + X)%coq_nat else n)))); intros.
    destruct H1. destruct H1.
    case_eq (l <= n); intros.
    - replace (l <= n) with true in H, H1.
      apply tc_sub with (t := x); try easy. 
      apply tc_var; try easy.
      apply onth_morec with (l := l); try easy.
      specialize(typable_implies_wfC H); intros; try easy.
    - replace (l <= n) with false in H, H1.
      apply tc_sub with (t := x); try easy.
      apply tc_var; try easy.
      apply onth_lessc with (l := l); try easy.
      specialize(typable_implies_wfC H); intros; try easy.
  - simpl in *. 
    specialize(_a23_f p_inact T Gs (Gtl++Gtr) H (erefl p_inact)); intros. subst. 
    apply tc_inact.
  - simpl in *.
    specialize(_a23_bf pt lb (incr_freeE k m ex) (incr_free l k X m Q) (p_send pt lb (incr_freeE k m ex) (incr_free l k X m Q)) Gs (Gtl ++ Gtr) T H (erefl (p_send pt lb (incr_freeE k m ex) (incr_free l k X m Q)))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2.
    apply tc_sub with (t := (ltt_send pt (extendLis lb (Some (x, x0))))); try easy.
    apply tc_send; try easy.
    apply IHQ. easy. easy.
    specialize(typable_implies_wfC H); intros; try easy.
  - simpl in *.
    specialize(_a23_a pt (map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp) (p_recv pt
          (map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp)) Gs (Gtl ++ Gtr) T H0 (erefl (p_recv pt
          (map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp)))); intros.
    destruct H2. destruct H2. destruct H3. destruct H4. 
    apply tc_sub with (t := (ltt_recv pt x)); try easy. constructor.
    specialize(Forall2_length H4); intros.
    specialize(map_length (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp); intros.
    specialize(eq_trans (esym H6) H7); intros. clear H6 H7.
    apply eq_trans with (y := length llp); try easy. 
    apply map_length; try easy.
    apply SList_map2 with (f := (incr_free l k.+1 X.+1 m)); try easy.
    specialize(SList_map (incr_free l k.+1 X m) llp H5); intros. easy.
    apply slideT_helper; try easy.
    specialize(typable_implies_wfC H0); intros; try easy.
  - simpl in *.
    specialize(_a23_c (p_ite (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2)) (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2) T Gs (Gtl ++ Gtr) H (erefl (p_ite (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2)))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. destruct H4.
    apply tc_ite; try easy.
    apply tc_sub with (t := x); try easy.
    apply IHQ1; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
    apply tc_sub with (t := x0); try easy.
    apply IHQ2; try easy.
    specialize(typable_implies_wfC H); intros; try easy. 
  - simpl in *. 
    specialize(_a23_d (p_rec (incr_free l.+1 k X m Q)) (incr_free l.+1 k X m Q) T Gs (Gtl++Gtr) H (erefl (p_rec (incr_free l.+1 k X m Q)))); intros.
    destruct H1. destruct H1. 
    specialize(IHQ X m l.+1 k tm Gs (Some x :: Gtl) Gtr x); intros.
    specialize(cat_cons (Some x) Gtl Gtr); intros.
    replace ((Some x :: Gtl) ++ Gtr) with (Some x :: Gtl ++ Gtr) in IHQ.
    specialize(IHQ H1); intros. simpl in IHQ.
    specialize(eq_S (length Gtl) l H0); intros.
    specialize(IHQ H4). clear H0 H4.
    apply tc_sub with (t := x); try easy.
    apply tc_mu; try easy.
    specialize(typable_implies_wfC H1); intros; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
Qed.

Lemma slideT : forall Q X m tm Gs Gt T,
typ_proc Gs Gt (incr_free 0 0 X m Q) T -> typ_proc Gs (tm :: Gt) (incr_free 0 0 X.+1 m Q) T.
Proof.
  intros.
  specialize(slideTp Q X m 0 0 tm Gs [] Gt T H); intros. simpl in H0.
  apply H0; try easy.
Qed.

Lemma slideSp_e : forall k m ex x Gsl Gsr tm,
  typ_expr (Gsl ++ Gsr) (incr_freeE k m ex) x ->
  length Gsl = k ->
  typ_expr (Gsl ++ tm :: Gsr) (incr_freeE k m.+1 ex) x.
Proof. 
  intros k m ex. revert k m. induction ex; intros; try easy.
  - simpl in *. 
    specialize(inv_expr_var (e_var (if k <= n then (n + m)%coq_nat else n)) (if k <= n then (n + m)%coq_nat else n) (Gsl ++ Gsr) x H (erefl (e_var (if k <= n then (n + m)%coq_nat else n)))); intros.
    destruct H1. destruct H1.
    apply sc_sub with (s := x0); try easy.
    apply sc_var.
    case_eq (k <= n); intros.
    - replace (k <= n) with true in H1. subst.
      apply onth_morec with (l := length Gsl); try easy.
    - replace (k <= n) with false in H1. subst.
      apply onth_lessc with (l := length Gsl); try easy.
  - simpl in *. 
    specialize(inv_expr_vali (Gsl ++ Gsr) (e_val v) x v H (erefl (e_val v))); intros.
    destruct H1.
    - subst. destruct H1. destruct H0. subst. apply sc_vali.
    - subst. destruct H1. destruct H0. destruct H0. subst.
      inversion H0. subst. apply sc_sub with (s := snat); try easy. apply sc_valn.
      subst. apply sc_valn.
    - subst. destruct H0. destruct H0. subst. apply sc_valb.
  - simpl in *.
    specialize(inv_expr_succ (Gsl ++ Gsr) (e_succ (incr_freeE k m ex)) x (incr_freeE k m ex) H (erefl (e_succ (incr_freeE k m ex)))); intros.
    destruct H1. destruct H2.
    - subst. apply sc_succ; try easy. apply IHex; try easy.
    - subst. apply sc_sub with (s := snat); try easy. apply sc_succ; try easy. apply IHex; try easy.
      apply sni.
  - simpl in *.
    specialize(inv_expr_neg (Gsl ++ Gsr) (e_neg (incr_freeE k m ex)) x (incr_freeE k m ex) H (erefl (e_neg (incr_freeE k m ex)))); intros.
    destruct H1. subst. apply sc_neg. apply IHex; try easy.
  - simpl in *.
    specialize(inv_expr_not (Gsl ++ Gsr) (e_not (incr_freeE k m ex)) x (incr_freeE k m ex) H (erefl (e_not (incr_freeE k m ex)))); intros. 
    destruct H1. subst. apply sc_not. apply IHex; try easy.
  - simpl in *.
    specialize(inv_expr_gt (Gsl ++ Gsr) (e_gt (incr_freeE k m ex1) (incr_freeE k m ex2)) x (incr_freeE k m ex1) (incr_freeE k m ex2) H (erefl (e_gt (incr_freeE k m ex1) (incr_freeE k m ex2)))); intros.
    destruct H1. destruct H2.
    subst. apply sc_gt. apply IHex1; try easy. apply IHex2; try easy.
  - simpl in *.
    specialize(inv_expr_plus (Gsl ++ Gsr) (e_plus (incr_freeE k m ex1) (incr_freeE k m ex2)) x (incr_freeE k m ex1) (incr_freeE k m ex2) H (erefl (e_plus (incr_freeE k m ex1) (incr_freeE k m ex2)))); intros.
    destruct H1. destruct H2.
    subst. apply sc_plus. apply IHex1; try easy. apply IHex2; try easy.
  - simpl in *.
    specialize(inv_expr_det (Gsl ++ Gsr) (e_det (incr_freeE k m ex1) (incr_freeE k m ex2)) x (incr_freeE k m ex1) (incr_freeE k m ex2) H (erefl (e_det (incr_freeE k m ex1) (incr_freeE k m ex2)))); intros.
    destruct H1. destruct H1. destruct H2.
    constructor; try easy.
    apply IHex1; try easy.
    apply sc_sub with (s := x0); intros; try easy.
    apply IHex2; try easy.
    apply sc_sub with (s := x0); intros; try easy.
Qed.

Lemma slideS_helper : forall llp l k X m x Gsl Gsr Gt tm,
    length Gsl = k ->
    Forall
      (fun u : option process =>
       match u with
       | Some k =>
           forall (X m l k0 : fin) (tm : option sort) (Gsl Gsr : list (option sort)) 
             (Gt : ctxT) (T : ltt),
           typ_proc (Gsl ++ Gsr) Gt (incr_free l k0 X m k) T ->
           length Gsl = k0 -> typ_proc (Gsl ++ tm :: Gsr) Gt (incr_free l k0 X m.+1 k) T
       | None => True
       end) llp ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gsl ++ Gsr) Gt p t))
       (map
          (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp) x ->
    Forall2
      (fun (u : option process) (v : option (sort * ltt)) =>
       u = None /\ v = None \/
       (exists (p : process) (s : sort) (t : ltt),
          u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gsl ++ tm :: Gsr) Gt p t))
      (map
         (fun u : option process =>
          match u with
          | Some p' => Some (incr_free l k.+1 X m.+1 p')
          | None => None
          end) llp) x.
Proof.
  intro llp. induction llp; intros; try easy.
  - destruct x; try easy.
  - destruct x; try easy.
    specialize(Forall_cons_iff (fun u : option process =>
        match u with
        | Some k =>
            forall (X m l k0 : fin) (tm : option sort) (Gsl Gsr : list (option sort)) 
              (Gt : ctxT) (T : ltt),
            typ_proc (Gsl ++ Gsr) Gt (incr_free l k0 X m k) T ->
            length Gsl = k0 -> typ_proc (Gsl ++ tm :: Gsr) Gt (incr_free l k0 X m.+1 k) T
        | None => True
        end) a llp); intros. destruct H2. specialize(H2 H0). clear H0 H3. destruct H2.
    simpl in *.
    specialize(Forall2_cons_iff (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gsl ++ Gsr) Gt p t)) (match a with
        | Some p' => Some (incr_free l k.+1 X m p')
        | None => None
        end) o (map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp) x); intros.
    destruct H3. specialize(H3 H1). clear H1 H4. destruct H3.
    apply Forall2_cons; try easy.
    - destruct a; try easy. destruct H1. easy.
      destruct H1. destruct H1. destruct H1. destruct H1. inversion H1. subst.
      right. destruct H4. subst. exists (incr_free l (length Gsl).+1 X m.+1 p), x1, x2.
      split. easy. split. easy. 
      specialize(H0 X m l (length Gsl).+1 tm (Some x1 :: Gsl) Gsr Gt x2 H4).
      simpl in H0. apply H0. easy.
    - destruct H1. destruct H1. subst. left; easy.
      destruct H1. destruct H1. destruct H1. destruct H1. easy.
    apply IHllp; try easy.
Qed.

Lemma slideSp : forall Q X m l k tm Gsl Gsr Gt T,
typ_proc (Gsl ++ Gsr) Gt (incr_free l k X m Q) T -> length Gsl = k -> typ_proc (Gsl ++ [tm] ++ Gsr) Gt (incr_free l k X m.+1 Q) T.
Proof.
  intro Q.
  induction Q using process_ind_ref; intros; try easy.
  - simpl in *. 
    specialize(_a23_e (p_var (if l <= n then (n + X)%coq_nat else n)) (if l <= n then (n + X)%coq_nat else n) T (Gsl ++ Gsr) Gt H (erefl (p_var (if l <= n then (n + X)%coq_nat else n)))); intros.
    destruct H1. destruct H1.
    apply tc_sub with (t := x); try easy. 
    apply tc_var; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
  - simpl in *.
    specialize(_a23_f p_inact T (Gsl ++ Gsr) Gt H (erefl p_inact)); intros. subst.
    apply tc_inact.
  - simpl in *.
    specialize(_a23_bf pt lb (incr_freeE k m ex) (incr_free l k X m Q) (p_send pt lb (incr_freeE k m ex) (incr_free l k X m Q)) (Gsl ++ Gsr) Gt T H (erefl (p_send pt lb (incr_freeE k m ex) (incr_free l k X m Q) ))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2.
    apply tc_sub with (t := (ltt_send pt (extendLis lb (Some (x, x0))))); try easy.
    apply tc_send; try easy.
    apply slideSp_e; try easy.
    apply IHQ; try easy.
    specialize(typable_implies_wfC H); intros; try easy. 
  - simpl in *.
    specialize(_a23_a pt (map
             (fun u : option process =>
              match u with
              | Some p' => Some (incr_free l k.+1 X m p')
              | None => None
              end) llp) (p_recv pt
       (map
          (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp)) (Gsl ++ Gsr) Gt T H0 (erefl (p_recv pt
       (map
          (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp)))); intros. 
    destruct H2. destruct H2. destruct H3. destruct H4. 
    apply tc_sub with (t := (ltt_recv pt x)); try easy. 
    constructor.
    specialize(Forall2_length H4); intros. 
    specialize(map_length (fun u : option process =>
           match u with
           | Some p' => Some (incr_free l k.+1 X m p')
           | None => None
           end) llp); intros. 
    specialize(eq_trans (esym H6) H7); intros.
    apply eq_trans with (y := length llp); try easy. apply map_length. clear H2.
    apply SList_map2; try easy.
    specialize(SList_map (incr_free l k.+1 X m) llp H5); intros; try easy.
    apply slideS_helper; try easy.
    specialize(typable_implies_wfC H0); intros; try easy.
  - simpl in *.
    specialize(_a23_c (p_ite (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2)) (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2) T (Gsl ++ Gsr) Gt H (erefl (p_ite (incr_freeE k m e) (incr_free l k X m Q1) (incr_free l k X m Q2)))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. destruct H4.
    apply tc_ite; try easy.
    apply slideSp_e; try easy.
    apply tc_sub with (t := x); try easy. apply IHQ1; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
    apply tc_sub with (t := x0); try easy. apply IHQ2; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
  - simpl in *.
    specialize(_a23_d (p_rec (incr_free l.+1 k X m Q)) (incr_free l.+1 k X m Q) T (Gsl ++ Gsr) Gt H (erefl (p_rec (incr_free l.+1 k X m Q)))); intros.
    destruct H1. destruct H1. 
    apply tc_sub with (t := x); try easy.
    apply tc_mu. try easy.
    apply IHQ; try easy.
    specialize(typable_implies_wfC H1); intros; try easy.
    specialize(typable_implies_wfC H); intros; try easy.
Qed.

Lemma slideS : forall Q X m tm Gs Gt T,
typ_proc Gs Gt (incr_free 0 0 X m Q) T -> typ_proc (tm :: Gs) Gt (incr_free 0 0 X m.+1 Q) T.
Proof.
  intros.
  specialize(slideSp Q X m 0 0 tm [] Gs Gt T H); intros. simpl in H0.
  apply H0; try easy.
Qed.

Lemma _a21_helper_1 : forall llp ys (GtA : list (option ltt)) m n Q,
      SList llp ->      
      Forall2
        (fun u v : option process =>
         u = None /\ v = None \/
         (exists k l : process, u = Some k /\ v = Some l /\ substitutionP (length GtA) m n.+1 Q k l))
        llp ys -> 
      SList ys.
Proof.
  intro llp. induction llp; intros; try easy.
  inversion H0. subst. clear H0.
  destruct H3. destruct H0. subst. apply SList_b. 
  - apply IHllp with (GtA := GtA) (m := m) (n := n) (Q := Q); try easy.
  - destruct H0. destruct H0. destruct H0. destruct H1. subst.
    specialize(SList_f (Some x) llp H); intros.
    destruct H0. apply SList_b. apply IHllp with (GtA := GtA) (m := m) (n := n) (Q := Q); try easy.
    destruct H0. subst. inversion H5. subst. easy.
Qed.

Lemma _a21_recv_helper : forall llp Q Gs GtA GtB m n T ys x,
  wtyped Q ->
  typ_proc Gs (GtA ++ GtB) (incr_free 0 0 m n Q) T ->
  Forall
      (fun u : option process =>
       match u with
       | Some k =>
           forall (Q : process) (T T' : ltt) (Gs : ctxS) (GtA GtB : list (option ltt)) 
             (X : fin) (Q' : process) (m n : fin),
           wtyped Q ->
           typ_proc Gs (GtA ++ Some T :: GtB) k T' ->
           length GtA = X ->
           substitutionP X m n Q k Q' ->
           typ_proc Gs (GtA ++ GtB) (incr_free 0 0 m n Q) T -> typ_proc Gs (GtA ++ GtB) Q' T'
       | None => True
       end) llp ->
  Forall2
        (fun u v : option process =>
         u = None /\ v = None \/
         (exists k l : process, u = Some k /\ v = Some l /\ substitutionP (length GtA) m n.+1 Q k l))
        llp ys ->
  Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (GtA ++ Some T :: GtB) p t)) llp x ->
  Forall2
  (fun (u : option process) (v : option (sort * ltt)) =>
   u = None /\ v = None \/
   (exists (p : process) (s : sort) (t : ltt),
      u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gs) (GtA ++ GtB) p t)) ys x.
Proof.
  intro llp. induction llp; intros; try easy.
  inversion H2. subst. inversion H3. subst. easy.
  inversion H2. subst. inversion H3. subst. clear H2 H3.
  constructor; try easy.
  - destruct H6. destruct H2. subst.
    left. destruct H7; try easy. destruct H2. destruct H2. destruct H2. easy.
    destruct H2. destruct H2. destruct H2. destruct H3. subst.
    destruct H7; try easy. destruct H2. destruct H2. destruct H2. destruct H2. destruct H3. inversion H2. subst.
    right. exists x0. exists x2. exists x3. split; try easy. split; try easy.
    inversion H1. subst. 
    specialize(H7 Q T x3 (Some x2 :: Gs) GtA GtB (length GtA) x0 m n.+1). 
    apply H7; try easy.
    apply slideS; try easy.
  - inversion H1. subst. clear H1 H6 H7 H4.
    apply IHllp with (Q := Q) (m := m) (n := n) (T := T); try easy.
Qed.

Lemma _a21 : forall P Q T T' Gs GtA GtB X Q' m n, wtyped Q
  -> typ_proc Gs (GtA ++ (Some T :: GtB)) P T' -> length GtA = X
  -> substitutionP X m n Q P Q' -> typ_proc Gs (GtA ++ GtB) (incr_free 0 0 m n Q) T
  -> typ_proc Gs (GtA ++ GtB) Q' T'.
Proof.
  intros P. induction P using process_ind_ref.
  
  (* p_var *)
  intros. inversion H2; subst. 
  - specialize(_a23_e (p_var (length GtA)) (length GtA) T' Gs (GtA ++ Some T :: GtB) H0 (erefl (p_var (length GtA)))); intros.
    destruct H1. destruct H1. destruct H4.
    specialize(onth_exact GtA GtB (Some T)); intros.
    apply tc_sub with (t := x); try easy.
    specialize(eq_trans (esym H1) H6); intros. inversion H7. subst. easy.
    apply typable_implies_wfC with (P := (p_var (length GtA))) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)).
    easy.
  - specialize(_a23_e (p_var 0) 0 T' Gs (GtA ++ Some T :: GtB) H0 (erefl (p_var 0))); intros.
    destruct H1. destruct H1. destruct H4. destruct GtA; try easy.
    simpl in H1. subst.
    apply tc_sub with (t := x); try easy.
    apply tc_var; try easy.
    apply typable_implies_wfC with (P := p_var 0) (Gs := Gs) (Gt := ((Some x :: GtA) ++ Some T :: GtB)). easy.
  - specialize(_a23_e (p_var y.+1) y.+1 T' Gs (GtA ++ Some T :: GtB) H0 (erefl (p_var y.+1))); intros.
    destruct H1. destruct H1. destruct H4.
    apply tc_sub with (t := x); intros; try easy.
    apply tc_var; try easy.
    specialize(onth_more GtA GtB y (Some T) H10); intros.
    apply eq_trans with (y := (onth y.+1 (GtA ++ Some T :: GtB))); try easy.
    apply typable_implies_wfC with (P := p_var y.+1) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)). easy.
  - specialize(_a23_e (p_var y.+1) y.+1 T' Gs (GtA ++ Some T :: GtB) H0 (erefl (p_var y.+1))); intros.
    destruct H1. destruct H1. destruct H4.
    apply tc_sub with (t := x); intros; try easy.
    apply tc_var; try easy.
    specialize(onth_less GtA GtB y (Some T) H10 H5); intros.
    apply eq_trans with (y := onth y.+1 (GtA ++ Some T :: GtB)); try easy.
    apply typable_implies_wfC with (P := (p_var y.+1)) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)). easy.
  
  (* p_inact *)
  intros. inversion H2. subst.
  specialize(_a23_f p_inact T' Gs (GtA ++ Some T :: GtB) H0 (erefl p_inact)); intros. subst. 
  constructor.
  
  (* p_send *)
  intros. inversion H2. subst.
  specialize(_a23_bf pt lb ex P (p_send pt lb ex P) Gs (GtA ++ Some T :: GtB) T' H0 (erefl (p_send pt lb ex P))); intros.
  destruct H1. destruct H1. destruct H1. destruct H4.
  apply tc_sub with (t := (ltt_send pt (extendLis lb (Some (x, x0))))); try easy.
  constructor; try easy.
  apply IHP with (Q := Q) (T := T) (X := length GtA) (m := m) (n := n); try easy.
  apply typable_implies_wfC with (P := (p_send pt lb ex P)) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)). easy.
  
  (* p_recv *)
  intros. inversion H3. subst.
  specialize(_a23_a pt llp (p_recv pt llp) Gs (GtA ++ Some T :: GtB) T' H1 (erefl (p_recv pt llp))); intros.
  destruct H2. destruct H2. destruct H5. destruct H6.
  apply tc_sub with (t := ltt_recv pt x); try easy.
  constructor; try easy.
  specialize(Forall2_length H12); intros.
  apply eq_trans with (y := length llp); try easy. 
  apply _a21_helper_1 with (llp := llp) (GtA := GtA) (m := m) (n := n) (Q := Q); try easy.
  apply _a21_recv_helper with (llp := llp) (Q := Q) (m := m) (n := n) (T := T); try easy.
  apply typable_implies_wfC with (P := (p_recv pt llp)) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)). easy.
  
  (* p_ite *)
  intros. inversion H2. subst.
  specialize(_a23_c (p_ite e P1 P2) e P1 P2 T' Gs (GtA ++ Some T :: GtB) H0 (erefl (p_ite e P1 P2))); intros.
  destruct H1. destruct H1. destruct H1. destruct H4. destruct H5. destruct H6.
  apply tc_ite; try easy.
  - apply tc_sub with (t := x); try easy. 
    apply IHP1 with (Q := Q) (T := T) (X := length GtA) (m := m) (n := n); try easy.
    apply typable_implies_wfC with (P := p_ite e P1 P2) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)). easy.
  - apply tc_sub with (t := x0); try easy.
    apply IHP2 with (Q := Q) (T := T) (X := length GtA) (m := m) (n := n); try easy.
    apply typable_implies_wfC with (P := p_ite e P1 P2) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)). easy.
  
  (* p_rec *)
  intros. inversion H2. subst.
  specialize(_a23_d (p_rec P) P T' Gs (GtA ++ Some T :: GtB) H0 (erefl (p_rec P))); intros.
  destruct H1. destruct H1.
  apply tc_sub with (t := x); try easy.
  apply tc_mu.
  specialize(IHP Q T x Gs (Some x :: GtA) GtB (length (Some x :: GtA)) Q'0 m.+1 n H); intros.
  apply IHP; try easy.
  apply slideT; try easy.
  apply typable_implies_wfC with (P := p_rec P) (Gs := Gs) (Gt := (GtA ++ Some T :: GtB)). easy.
Qed.

Lemma trivial_incrE : forall n ex, (incr_freeE n 0 ex) = ex.
Proof.
  intros n ex. induction ex; intros; try easy.
  - simpl. destruct (n <= n0); try easy.
    specialize(Nat.add_0_r n0); intros. replace (n0 + 0)%coq_nat with n0. easy.
  - simpl. replace (incr_freeE n 0 ex) with ex. easy.
  - simpl. replace (incr_freeE n 0 ex) with ex. easy.
  - simpl. replace (incr_freeE n 0 ex) with ex. easy.
  - simpl. replace (incr_freeE n 0 ex1) with ex1. replace (incr_freeE n 0 ex2) with ex2. easy.
  - simpl. replace (incr_freeE n 0 ex1) with ex1. replace (incr_freeE n 0 ex2) with ex2. easy.
  - simpl. replace (incr_freeE n 0 ex1) with ex1. replace (incr_freeE n 0 ex2) with ex2. easy.
Qed.

Lemma trivial_incr : forall m n Q, (incr_free m n 0 0 Q) = Q.
Proof.
  intros. revert m n. induction Q using process_ind_ref; intros; simpl; try easy. 
  - destruct (m <= n); try easy.
    specialize(Nat.add_0_r n); intros. replace (n + 0)%coq_nat with n; easy.
  - specialize(trivial_incrE n ex); intros.
    specialize(IHQ m n); intros.
    replace (incr_freeE n 0 ex) with ex. replace (incr_free m n 0 0 Q) with Q. easy.
  - assert (map (fun u => match u with 
        | Some u => Some (incr_free m n.+1 0 0 u)
        | None   => None
      end) llp = llp).
    {
      induction llp. easy. simpl in *.
      specialize(Forall_cons_iff (fun u : option process =>
       match u with
       | Some k => forall m n : fin, incr_free m n 0 0 k = k
       | None => True
       end) a llp); intros.
      destruct H0. specialize(H0 H); intros. clear H1 H. destruct H0.
      specialize(IHllp H0); intros.
      simpl.
      destruct a; try easy. 
      specialize(H m n.+1). replace (incr_free m n.+1 0 0 p) with p. 
      replace (map
     (fun u : option process =>
      match u with
      | Some u0 => Some (incr_free m n.+1 0 0 u0)
      | None => None
      end) llp) with llp. easy.
      replace (map
     (fun u : option process =>
      match u with
      | Some u0 => Some (incr_free m n.+1 0 0 u0)
      | None => None
      end) llp) with llp. easy.
    }
    replace (List.map (fun u : option process =>
        match u with
        | Some p' => Some (incr_free m n.+1 0 0 p')
        | None => None
        end) llp) with llp. easy.
  - specialize(trivial_incrE n e); intros. 
    specialize(IHQ1 m n); intros. specialize(IHQ2 m n); intros.
    replace (incr_freeE n 0 e) with e.
    replace (incr_free m n 0 0 Q1) with Q1. 
    replace (incr_free m n 0 0 Q2) with Q2.
    easy.
  - specialize(IHQ m.+1 n); intros. 
    replace (incr_free m.+1 n 0 0 Q) with Q. easy.
Qed.

Lemma _a21f : forall P Q T T' Gs Gt Q',
     typ_proc Gs (Some T :: Gt) P T' 
  -> substitutionP 0 0 0 Q P Q' -> typ_proc Gs Gt Q T
  -> typ_proc Gs Gt Q' T'.
Proof.
  intros.
  specialize(_a21 P Q T T' Gs nil Gt 0 Q' 0 0); intros.
  simpl in H2. apply H2; try easy.
  apply typable_implies_wtyped with (Gs := Gs) (Gt := Gt) (T := T). easy.
  specialize(trivial_incr 0 0 Q); intros.
  replace (incr_free 0 0 0 0 Q) with Q. easy.
Qed.

Lemma inj_substP : forall [P' m n k P Q Q0], 
    substitutionP m n k P P' Q -> 
    substitutionP m n k P P' Q0 -> 
    Q = Q0.
Proof.
  induction P' using process_ind_ref; intros.
  - inversion H; try easy.
    subst. 
    inversion H0; try easy.
    subst.
    inversion H0; try easy.
    subst.
    inversion H0; try easy. subst.
    specialize(triad_le m y H7 H9); intros. easy.
    subst. inversion H0; try easy.
    subst.
    destruct m; try easy.
    specialize(triad_le y m H7 H9); intros. easy.
  - inversion H. subst. inversion H0. subst. easy.
  - inversion H. subst.
    inversion H0. subst.
    specialize(IHP' m n k P Q' Q'0 H10 H11). subst. easy.
  - inversion H0. subst. inversion H1. subst.
    assert(ys = ys0).
    {
      clear H0 H1. revert H10 H9 H. revert m n k P ys ys0. clear pt.
      induction llp; intros.
      - destruct ys0; try easy. destruct ys; try easy.
      - destruct ys0; try easy. destruct ys; try easy.
        inversion H10. subst. clear H10. inversion H9. subst. clear H9.
        inversion H. subst. clear H.
        specialize(IHllp m n k P ys ys0 H5 H7 H6); intros. subst. clear H6 H7 H5.
        destruct H3. 
        - destruct H. subst. destruct H4. destruct H. subst. easy.
          destruct H as (k1,(l1,Ha)). easy.
        - destruct H as (k1,(l1,(Ha,(Hb,Hc)))). subst.
          destruct H4; try easy. destruct H as (k2,(l2,(Hf,(Hd,He)))). inversion Hf. subst.
          specialize(H2 m n (S k) P l1 l2 Hc He). subst. easy.
    }
    subst. easy.
  - inversion H. subst. inversion H0. subst.
    specialize(IHP'1 m n k P Q1 Q3 H9 H11); intros. subst. 
    specialize(IHP'2 m n k P Q2 Q4 H10 H12); intros. subst. easy.
  - inversion H. subst. inversion H0. subst.
    specialize(IHP' (S m) (S n) k P Q' Q'0 H6 H7). subst. easy. 
Qed.



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


Lemma triv_pt_p_s : forall p q x0,
    wfgCw (gtt_send p q x0) -> 
    isgPartsC p (gtt_send p q x0).
Proof.
  intros. unfold wfgC in H.
  destruct H. destruct H. destruct H0. pose proof H1 as H2.
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


Lemma triv_pt_q_s : forall p q x0,
    wfgCw (gtt_send p q x0) -> 
    isgPartsC q (gtt_send p q x0).
Proof.
  intros. unfold wfgC in H.
  destruct H. destruct H. destruct H0. pose proof H1 as H2.
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

Lemma part_cont_b_s : forall n ys s g r p q,
    onth n ys = Some(s, g) ->
    isgPartsC r g ->
    r <> p -> r <> q -> 
    wfgCw (gtt_send p q ys) -> 
    isgPartsC r (gtt_send p q ys).
Proof.
  intros.
  unfold wfgC in H3.
  destruct H3 as (Gl,(Ha,(Hb,Hc))).
  unfold isgPartsC in *. destruct H0 as (G1,(He,(Hf,Hg))).
  pinversion Ha; try easy.
  - subst.
    exists (g_send p q (overwrite_lis n (Some (s, G1)) xs)).
    specialize(guard_cont Hc); intros. clear Hc Ha Hb.
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
    clear H0 H3 Hh Ha Hb Hc.
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


(* global trees with context holes *)
Inductive gtth: Type :=
  | gtth_hol    : fin -> gtth
  | gtth_send   : part -> part -> list (option (sort * gtth)) -> gtth.

Section gtth_ind_ref.
  Variable P : gtth -> Prop.
  Hypothesis P_hol : forall n, P (gtth_hol n).
  Hypothesis P_send : forall p q xs, List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ P g)) xs -> P (gtth_send p q xs).
  
  Fixpoint gtth_ind_ref p : P p.
  Proof.
    destruct p.
    - apply P_hol.
    - apply P_send.
      induction l; intros; try easy.
      constructor; try easy.
      destruct a. 
      - destruct p. right. exists s1. exists g. split. easy. apply gtth_ind_ref.
      - left. easy.
  Qed.

End gtth_ind_ref.

Inductive typ_gtth : list (option gtt) -> gtth -> gtt -> Prop := 
  | gt_hol : forall n ctx gc, onth n ctx = Some gc -> typ_gtth ctx (gtth_hol n) gc
  | gt_send : forall ctx p q xs ys, SList xs -> List.Forall2 (fun u v => (u = None /\ v = None) \/ 
                                                (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ typ_gtth ctx g g')) xs ys -> 
                                                typ_gtth ctx (gtth_send p q xs) (gtt_send p q ys).

Section typ_gtth_ind_ref.
  Variable P : list (option gtt) -> gtth -> gtt -> Prop.
  Hypothesis P_hol : forall n ctx gc, onth n ctx = Some gc -> P ctx (gtth_hol n ) gc.
  Hypothesis P_send : forall ctx p q xs ys, SList xs -> List.Forall2 (fun u v => (u = None /\ v = None) \/ 
                                                 (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ P ctx g g')) xs ys -> 
                                                 P ctx (gtth_send p q xs) (gtt_send p q ys).
  
  Fixpoint typ_gtth_ind_ref ctx G G' (a : typ_gtth ctx G G') {struct a} : P ctx G G'.
  Proof.
    refine (match a with 
      | gt_hol n ctx gc Ha => P_hol n ctx gc Ha
      | gt_send ctx p q xs ys Ha Hl => P_send ctx p q xs ys Ha _
    end); try easy.
    revert Hl. apply Forall2_mono.
    intros. 
    destruct H.
    - left. easy.
    - destruct H. destruct H. destruct H. destruct H. destruct H0. subst.
      right. exists x0. exists x1. exists x2. split. easy. split. easy. 
      apply typ_gtth_ind_ref; try easy.
  Qed.

End typ_gtth_ind_ref.

Inductive ishParts : part -> gtth -> Prop := 
  | ha_sendp : forall p q l, ishParts p (gtth_send p q l)
  | ha_sendq : forall p q l, ishParts q (gtth_send p q l)
  | ha_sendr : forall p q r n s g lis, p <> r -> q <> r -> onth n lis = Some (s, g) -> ishParts r g -> ishParts r (gtth_send p q lis).

Lemma ishParts_x : forall [p s1 s2 o1 o2 xs0],
    (ishParts p (gtth_send s1 s2 (Some (o1,o2) :: xs0)) -> False) ->
    (ishParts p o2 -> False).
Proof.
  intros. apply H. 
  - case_eq (eqb p s1); intros.
    assert (p = s1). apply eqb_eq; try easy. subst. apply ha_sendp.
  - case_eq (eqb p s2); intros.
    assert (p = s2). apply eqb_eq; try easy. subst. apply ha_sendq.
  - assert (p <> s1). apply eqb_neq; try easy. 
    assert (p <> s2). apply eqb_neq; try easy.
    apply ha_sendr with (n := 0) (s := o1) (g := o2); try easy.
Qed.


Lemma ishParts_hxs : forall [p s1 s2 o1 xs0],
    (ishParts p (gtth_send s1 s2 (o1 :: xs0)) -> False) ->
    (ishParts p (gtth_send s1 s2 xs0) -> False).
Proof.
  intros. apply H.
  inversion H0. subst. apply ha_sendp. apply ha_sendq.
  subst. apply ha_sendr with (n := Nat.succ n) (s := s) (g := g); try easy.
Qed.

Lemma ishParts_n : forall [n p s s' xs s0 g],
    (ishParts p (gtth_send s s' xs) -> False) ->
    onth n xs = Some(s0, g) -> 
    (ishParts p g -> False).
Proof.  
  induction n; intros; try easy.
  - apply H. destruct xs; try easy. simpl in *. subst.
    - case_eq (eqb p s); intros.
      assert (p = s). apply eqb_eq; try easy. subst. apply ha_sendp.
    - case_eq (eqb p s'); intros.
      assert (p = s'). apply eqb_eq; try easy. subst. apply ha_sendq.
    - assert (p <> s). apply eqb_neq; try easy. 
      assert (p <> s'). apply eqb_neq; try easy.
      apply ha_sendr with (n := 0) (s := s0) (g := g); try easy.
  - destruct xs; try easy.
    specialize(ishParts_hxs H); intros.
    specialize(IHn p s s' xs s0 g). apply IHn; try easy.
Qed.

Lemma Forall3S_to_Forall2_r : forall ctxG0 ctxG1 ctxG,
    Forall3S
       (fun u v w : option gtt =>
        u = None /\ v = None /\ w = None \/
        (exists t : gtt, u = None /\ v = Some t /\ w = Some t) \/
        (exists t : gtt, u = Some t /\ v = None /\ w = Some t) \/
        (exists t : gtt, u = Some t /\ v = Some t /\ w = Some t)) ctxG0 ctxG1 ctxG -> 
    Forall2R 
        (fun u v => (u = None \/ u = v)) ctxG1 ctxG.
Proof.
  induction ctxG0; intros.
  inversion H. subst.
  - clear H. induction ctxG; intros; try easy. constructor; try easy. right. right. easy. easy.
  - subst. constructor.
  - inversion H.
    - subst. specialize(IHctxG0 nil ctxG0). constructor.
    - subst. clear H.
      specialize(IHctxG0 xb xc H6). constructor; try easy.
      clear H6 IHctxG0.
      destruct H3. destruct H as (Ha,(Hb,Hc)). subst. left. easy.
      destruct H. destruct H as (t,(Ha,(Hb,Hc))). subst. right. easy.
      destruct H. destruct H as (t,(Ha,(Hb,Hc))). subst. left. easy.
      destruct H as (t,(Ha,(Hb,Hc))). subst. right. easy.
Qed.

Lemma Forall3S_to_Forall2_l : forall ctxG0 ctxG1 ctxG,
    Forall3S
       (fun u v w : option gtt =>
        u = None /\ v = None /\ w = None \/
        (exists t : gtt, u = None /\ v = Some t /\ w = Some t) \/
        (exists t : gtt, u = Some t /\ v = None /\ w = Some t) \/
        (exists t : gtt, u = Some t /\ v = Some t /\ w = Some t)) ctxG0 ctxG1 ctxG -> 
    Forall2R 
        (fun u v => (u = None \/ u = v)) ctxG0 ctxG.
Proof.
  induction ctxG0; intros.
  inversion H. subst. constructor. constructor.
  - inversion H.
    - subst. constructor. right. easy. specialize(IHctxG0 nil ctxG0). apply IHctxG0. constructor.
    - subst. clear H.
      specialize(IHctxG0 xb xc H6). constructor; try easy.
      clear H6 IHctxG0.
      destruct H3. destruct H as (Ha,(Hb,Hc)). subst. left. easy.
      destruct H. destruct H as (t,(Ha,(Hb,Hc))). subst. left. easy.
      destruct H. destruct H as (t,(Ha,(Hb,Hc))). subst. right. easy.
      destruct H as (t,(Ha,(Hb,Hc))). subst. right. easy.
Qed.

Inductive isMergeCtx : list (option gtt) -> list (option (list (option gtt))) -> Prop :=   
  | cmatm : forall t, isMergeCtx t (Some t :: nil)
  | cmconsn : forall t xs, isMergeCtx t xs -> isMergeCtx t (None :: xs) 
  | cmconss : forall t t' t'' xs, 
      Forall3S (fun u v w => 
        (u = None /\ v = None /\ w = None) \/
        (exists t, u = None /\ v = Some t /\ w = Some t) \/
        (exists t, u = Some t /\ v = None /\ w = Some t) \/
        (exists t, u = Some t /\ v = Some t /\ w = Some t)
      ) t t' t'' ->
      isMergeCtx t xs -> isMergeCtx t'' (Some t' :: xs). 



Inductive usedCtx : (list (option gtt)) -> gtth -> Prop := 
  | used_hol : forall n G, usedCtx (extendLis n (Some G)) (gtth_hol n)
  | used_con : forall ctxG ctxGLis p q ys, isMergeCtx ctxG ctxGLis -> 
        List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists ctxGi s g, u = Some ctxGi /\ v = Some (s, g) /\ usedCtx ctxGi g)) ctxGLis ys -> usedCtx ctxG (gtth_send p q ys).

Lemma mergeCtx_to_2R : forall ctxGLis ctxG,
    isMergeCtx ctxG ctxGLis -> 
    Forall (fun u => u = None \/ (exists ctxGi, u = Some ctxGi /\
      Forall2R (fun u v => (u = None \/ u = v)) ctxGi ctxG
    )) ctxGLis.
Proof.
  induction ctxGLis; intros; try easy.
  inversion H.
  - subst. constructor; try easy. right. exists ctxG.
    split. easy. clear H IHctxGLis. induction ctxG; intros.
    constructor. constructor; try easy. right. easy.
  - subst. specialize(IHctxGLis ctxG H2). constructor; try easy. left. easy.
  - subst.
    specialize(IHctxGLis t H4). clear H.
    constructor.
    - right. exists t'. split. easy.
      clear H4 IHctxGLis.
      apply Forall3S_to_Forall2_r with (ctxG0 := t); try easy.
      revert IHctxGLis. apply Forall_mono; intros.
      destruct H. left. easy.
      destruct H as (ctxGi,(Ha,Hb)). subst. right. exists ctxGi. split. easy.
      specialize(Forall3S_to_Forall2_l t t' ctxG H3); intros.
      clear H3 H4. clear ctxGLis t'.
      revert Hb H. revert t ctxG.
      induction ctxGi; intros; try easy.
      - constructor.
      - destruct t; try easy. destruct ctxG; try easy.
        inversion Hb. subst. clear Hb. inversion H. subst. clear H.
        specialize(IHctxGi t ctxG H5 H7). constructor; try easy.
        clear H5 H7.
        destruct H3. left. easy.
        subst. destruct H4. left. easy. subst. right. easy.
Qed.

Lemma typh_with_more : forall gl ctxJ ctxG g3,
            typ_gtth ctxJ gl g3 -> 
            Forall2R (fun u v : option gtt => u = None \/ u = v) ctxJ ctxG -> 
            typ_gtth ctxG gl g3.
Proof.
  induction gl using gtth_ind_ref; intros.
  - inversion H. subst. constructor.
    clear H. revert H3 H0. revert ctxG ctxJ. induction n; intros.
    - destruct ctxJ; try easy. destruct ctxG; try easy.
      inversion H0. subst. clear H0.
      simpl in H3. subst. destruct H4; try easy. 
    - destruct ctxJ; try easy. destruct ctxG; try easy.
      inversion H0. subst. clear H0.
      specialize(IHn ctxG ctxJ). apply IHn; try easy.
  - inversion H0. subst. constructor; try easy.
    clear H7 H0. revert H8 H1 H.
    revert xs ctxJ ctxG. clear p q.
    induction ys; intros.
    - destruct xs; try easy.
    - destruct xs; try easy. inversion H. subst. clear H. inversion H8. subst. clear H8.
      specialize(IHys xs ctxJ ctxG H7 H1 H4). constructor; try easy. clear H7 H4 IHys.
      destruct H5. left. easy.
      destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
      destruct H3; try easy. destruct H as (s2,(g3,(Hd,He))). inversion Hd. subst.
      right. exists s2. exists g3. exists g2. split. easy. split. easy.
      specialize(He ctxJ ctxG g2). apply He; try easy.
Qed.

Lemma typ_gtth_pad_l : forall Gl' g1 ctxJ ctxG,
    typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) Gl' g1 -> 
    typ_gtth (ctxJ ++ ctxG)%list Gl' g1.
Proof.
  intros.
  specialize(typh_with_more Gl' (noneLis (Datatypes.length ctxJ) ++ ctxG) (ctxJ ++ ctxG) g1); intros. apply H0; try easy.
  clear H0 H. induction ctxJ; intros; try easy.
  - simpl. induction ctxG; intros; try easy. constructor. constructor; try easy. right. easy.
  - constructor; try easy. left. easy.
Qed.

Lemma typ_gtth_pad_r : forall g2 g3 ctxJ ctxG,
        typ_gtth ctxJ g2 g3 -> 
        typ_gtth (ctxJ ++ ctxG)%list g2 g3.
Proof.
  intros.
  specialize(typh_with_more g2 ctxJ (ctxJ ++ ctxG) g3); intros.
  apply H0; try easy.
  clear H0 H. induction ctxJ; intros; try easy. constructor.
  constructor; try easy. right. easy.
Qed.

Lemma typh_with_less : forall ctxGi' ctxG g4 g3,
            typ_gtth ctxG g4 g3 -> 
            Forall2R (fun u v : option gtt => u = None \/ u = v) ctxGi' ctxG -> 
            usedCtx ctxGi' g4 -> 
            typ_gtth ctxGi' g4 g3.
Proof.
  intros. revert H H0 H1. revert g3 ctxGi' ctxG.
  induction g4 using gtth_ind_ref; intros.
  - inversion H. subst. constructor; try easy. 
    inversion H1. subst.
    clear H1 H. revert H4 H0. revert g3 ctxG G. induction n; intros; try easy.
    - destruct ctxG; try easy. simpl in H4. subst.
      inversion H0. subst. simpl. destruct H3; try easy.
    - destruct ctxG; try easy. inversion H0. subst. 
      apply IHn with (ctxG := ctxG); try easy.
  - inversion H0. subst.
    constructor; try easy. 
    inversion H2. subst.
    specialize(mergeCtx_to_2R ctxGLis ctxGi' H6); intros. clear H6 H8 H2 H0.
    revert H3 H10 H9 H1 H. revert ctxGi' ctxG ys ctxGLis. clear p q.
    induction xs; intros; try easy.
    - destruct ys; try easy.
    - destruct ys; try easy. destruct ctxGLis; try easy.
      inversion H. subst. clear H. inversion H9. subst. clear H9.
      inversion H3. subst. clear H3. inversion H10. subst. clear H10.
      specialize(IHxs ctxGi' ctxG ys ctxGLis).
      assert(Forall2
         (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
          u = None /\ v = None \/
          (exists (s : sort) (g : gtth) (g' : gtt),
             u = Some (s, g) /\ v = Some (s, g') /\ typ_gtth ctxGi' g g')) xs ys).
      apply IHxs; try easy. constructor; try easy.
      clear H H12 H7 H8 H5 IHxs.
      destruct H6. left. easy.
      destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
      destruct H4; try easy. destruct H as (s2,(g3,(Hd,He))). inversion Hd. subst.
      destruct H9; try easy. destruct H as (ct,(s3,(g4,(Hf,(Hg,Hh))))). inversion Hg. subst.
      destruct H2; try easy. destruct H as (ct2,(Hi,Hj)). inversion Hi. subst.
      right. exists s3. exists g4. exists g2.
      split. easy. split. easy.
      specialize(He g2 ct2 ctxG).
      assert(typ_gtth ct2 g4 g2).
      {
        apply He; try easy.
        clear Hh Hi Hc Hd He Hg. 
        revert Hj H1. revert ctxGi' ctxG.
        induction ct2; intros; try easy.
        - constructor.
        - destruct ctxGi'; try easy. destruct ctxG; try easy.
          inversion Hj. subst. clear Hj. inversion H1. subst. clear H1.
          specialize(IHct2 ctxGi' ctxG H5 H7). constructor; try easy.
          destruct H3. left. easy. subst. destruct H4. left. easy. subst. right. easy.
      }
      apply typh_with_more with (ctxJ := ct2); try easy.
Qed.

Lemma typh_with_more2 {A} : forall ctxGi' ctxG (ctxJ : list A) gl g3,
            typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxGi') gl g3 -> 
            Forall2R (fun u v : option gtt => u = None \/ u = v) ctxGi' ctxG -> 
            typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) gl g3.
Proof.
  intros.
  apply typh_with_more with (ctxJ := (noneLis (Datatypes.length ctxJ) ++ ctxGi')); try easy.
  clear H.
  induction ctxJ; intros; try easy.
  constructor; try easy. left. easy.
Qed.

Lemma ctx_back : forall s s' xs ys0 ctxG,
      typ_gtth ctxG (gtth_send s s' xs) (gtt_send s s' ys0) -> 
      usedCtx ctxG (gtth_send s s' xs) -> 
      exists ctxGLis, 
      Forall3 (fun u v w => (u = None /\ v = None /\ w = None) \/ (exists ct s g g', u = Some ct /\ v = Some(s, g) /\ w = Some(s, g') /\ typ_gtth ct g g' /\ usedCtx ct g)) ctxGLis xs ys0 /\
      isMergeCtx ctxG ctxGLis.
Proof.
  intros.
  inversion H. subst. clear H.
  inversion H0. subst. clear H0.
  clear H4. clear s s'.
  specialize(mergeCtx_to_2R ctxGLis ctxG H3); intros. 
  exists ctxGLis. split; try easy. clear H3.
  revert H7 H6 H. revert ys0 ctxG ctxGLis.
  induction xs; intros.
  - destruct ys0; try easy. destruct ctxGLis; try easy. constructor.
  - destruct ys0; try easy. destruct ctxGLis; try easy.
    inversion H7. subst. clear H7. inversion H6. subst. clear H6.
    inversion H. subst. clear H.
    specialize(IHxs ys0 ctxG ctxGLis H5 H8 H6). constructor; try easy.
    clear H6 H8 H5 IHxs.
    - destruct H4. destruct H. subst. destruct H3. destruct H. subst. left. easy.
      destruct H as (s1,(g1,(g2,Ha))). easy.
    - destruct H as (ct,(s1,(g1,(Ha,(Hb,Hc))))). subst.
      destruct H3; try easy. destruct H as (s2,(g2,(g3,(Hd,(He,Hf))))). inversion Hd. subst.
      destruct H2; try easy. destruct H as (ct2,(Hg,Hh)). inversion Hg. subst.
      right. exists ct2. exists s2. exists g2. exists g3.
      split. easy. split. easy. split. easy. split; try easy.
      apply typh_with_less with (ctxG := ctxG); try easy.
Qed.

Lemma mergeCtx_sl : forall n ctxGLis ctxGi ctxG,
        onth n ctxGLis = Some ctxGi -> 
        isMergeCtx ctxG ctxGLis -> 
        Forall2R (fun u v => u = v \/ u = None) ctxGi ctxG.
Proof.
  induction n; intros.
  - destruct ctxGLis; try easy. 
    simpl in H. subst.
    inversion H0. subst. 
    - clear H0. induction ctxGi; intros; try easy. constructor.
      constructor; try easy. left. easy.
    - subst.
      clear H4 H0. clear ctxGLis.
      revert H3. revert ctxG t. induction ctxGi; intros; try easy.
      - constructor.
      - inversion H3; try easy.
        - subst. clear H3 IHctxGi. constructor. left. easy. clear a.
          induction ctxGi; intros; try easy. constructor. constructor; try easy. left. easy.
        - subst. specialize(IHctxGi xc xa H6). constructor; try easy.
          clear H3 H6. 
          - destruct H4. destruct H as (Ha,(Hb,Hc)). subst. left. easy.
          - destruct H. destruct H as (t1,(Ha,(Hb,Hc))). subst. left. easy.
          - destruct H. destruct H as (t1,(Ha,(Hb,Hc))). subst. right. easy.
          - destruct H as (t1,(Ha,(Hb,Hc))). subst. left. easy.
  - destruct ctxGLis; try easy.
    inversion H0; try easy.
    - subst. destruct n; try easy.
    - subst. specialize(IHn ctxGLis ctxGi ctxG). apply IHn; try easy.
    - subst. specialize(IHn ctxGLis ctxGi t H H5).
      clear H0 H H5.
      clear ctxGLis n.
      revert H4 IHn. revert t ctxG t'.
      induction ctxGi; intros; try easy.
      - constructor.
      - inversion H4. 
        - subst. inversion IHn; try easy.
        - subst. destruct ctxG; try easy.
        - subst. clear H4.
          inversion IHn. subst. clear IHn.
          specialize(IHctxGi xa xc xb H0 H6). constructor; try easy.
          clear IHctxGi H0 H6.
          destruct H4. subst.
          - destruct H. destruct H as (Ha,(Hb,Hc)). subst. left. easy.
          - destruct H. destruct H as (t1,(Ha,(Hb,Hc))). subst. right. easy.
          - destruct H. destruct H as (t1,(Ha,(Hb,Hc))). subst. left. easy.
          - destruct H as (t1,(Ha,(Hb,Hc))). subst. left. easy.
          subst. right. easy.
Qed.


Lemma shift_to : forall (g1 : gtt) (p : string) (Gl : gtth) (ctxG ctxJ : seq.seq (option gtt)),
typ_gtth ctxG Gl g1 ->
(ishParts p Gl -> False) ->
usedCtx ctxG Gl ->
exists Gl' : gtth,
  typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) Gl' g1 /\
  usedCtx (noneLis (Datatypes.length ctxJ) ++ ctxG) Gl' /\ (ishParts p Gl' -> False).
Proof.
  intros g1 p Gl. revert g1 p.
  induction Gl using gtth_ind_ref; intros; try easy.
  - inversion H1. subst.
    exists (gtth_hol ((Datatypes.length ctxJ) + n)).
    assert(extendLis (Datatypes.length ctxJ + n) (Some G) =
     (noneLis (Datatypes.length ctxJ) ++ extendLis n (Some G))%SEQ).
      {
       clear H1 H0 H. clear g1 p. induction ctxJ; intros; try easy.
       simpl in *. replace (extendLis (Datatypes.length ctxJ + n)%Nrec (Some G))%SEQ with
          ((noneLis (Datatypes.length ctxJ) ++ extendLis n (Some G))%SEQ). easy. 
      }
      rename H2 into Ht.
    split.
    - inversion H. subst. 
      specialize(extendExtract n (Some G)); intros.
      specialize(eq_trans (esym H4) H2); intros. inversion H3. subst.
      clear H4 H3 H2.
      constructor. clear H1 H0 H Ht. clear p. revert G n.
      induction ctxJ; intros; try easy. simpl in *.
      apply extendExtract; try easy.
      specialize(IHctxJ G n). easy.
    - split.
      replace ((noneLis (Datatypes.length ctxJ) ++ extendLis n (Some G))) with (extendLis (Datatypes.length ctxJ + n) (Some G)). constructor.
    - intros. inversion H2; try easy.
  - inversion H0. subst.
    inversion H2. subst.
    assert(
      exists zs,
      Forall2 (fun u v => (u = None /\ v = None) \/ exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) g g') zs ys /\
      List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists ctxGi s g, u = Some ctxGi /\ v = Some (s, g) /\ usedCtx (noneLis (Datatypes.length ctxJ) ++ ctxGi) g)) ctxGLis zs /\
      Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ (ishParts p0 g -> False))) zs 
    ). 
    {
      specialize(mergeCtx_to_2R ctxGLis ctxG H6); intros.
      clear H6 H8 H2 H0.
      revert H H1 H9 H10 H3.
      revert p q xs p0 ctxG ctxJ ctxGLis.
      induction ys; intros; try easy.
      - destruct xs; try easy. destruct ctxGLis; try easy.
        exists nil. easy.
      - destruct xs; try easy. destruct ctxGLis; try easy.
        inversion H9. subst. clear H9. inversion H10. subst. clear H10.
        inversion H3. subst. clear H3. inversion H. subst. clear H.
        assert(exists zs : seq.seq (option (sort * gtth)),
         Forall2
           (fun (u : option (sort * gtth)) (v : option (sort * gtt)) =>
            u = None /\ v = None \/
            (exists (s : sort) (g : gtth) (g' : gtt),
               u = Some (s, g) /\
               v = Some (s, g') /\ typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxG) g g')) zs ys /\
         Forall2
           (fun (u : option (seq.seq (option gtt))) (v : option (sort * gtth)) =>
            u = None /\ v = None \/
            (exists (ctxGi : seq.seq (option gtt)) (s : sort) (g : gtth),
               u = Some ctxGi /\
               v = Some (s, g) /\ usedCtx (noneLis (Datatypes.length ctxJ) ++ ctxGi) g)) ctxGLis zs /\
         Forall
           (fun u : option (sort * gtth) =>
            u = None \/ (exists (s : sort) (g : gtth), u = Some (s, g) /\ (ishParts p0 g -> False))) zs).
        specialize(IHys p q xs p0 ctxG ctxJ ctxGLis). apply IHys; try easy.
        specialize(ishParts_hxs H1); try easy.
        clear IHys H10 H8 H9 H7.
        destruct H as (zs,(Ha,(Hb,Hc))).
        destruct H6.
        - destruct H. subst. destruct H5. destruct H. subst.
          exists (None :: zs).
          - split. constructor; try easy. left. easy.
          - split. constructor; try easy. left. easy.
          - constructor; try easy. left. easy.
          destruct H as (s1,(g1,(g2,Ht))). easy.
        - destruct H as (ctxGi,(s1,(g1,(Hd,(He,Hf))))). subst.
          destruct H5; try easy. destruct H as (s2,(g2,(g3,(Hg,(Hh,Hi))))). inversion Hg. subst.
          destruct H4; try easy. destruct H as (ctxGi',(Hj,Hk)). inversion Hj. subst.
          destruct H3; try easy. destruct H as (s3,(g4,(Hl,Hm))). inversion Hl. subst.
          specialize(Hm g3 p0 ctxGi' ctxJ).
          assert(exists Gl' : gtth,
       typ_gtth (noneLis (Datatypes.length ctxJ) ++ ctxGi') Gl' g3 /\
       usedCtx (noneLis (Datatypes.length ctxJ) ++ ctxGi') Gl' /\ (ishParts p0 Gl' -> False)).
          {
            apply Hm; try easy.
            - apply typh_with_less with (ctxG := ctxG); try easy.
            - specialize(ishParts_x H1); try easy.
          }
          destruct H as (gl,(Hd,(He,Hta))). exists (Some (s3, gl) :: zs).
          - split. constructor; try easy.
            right. exists s3. exists gl. exists g3. split. easy. split. easy.
            apply typh_with_more2 with (ctxGi' := ctxGi'); try easy.
          - split. constructor; try easy. right. exists ctxGi'. exists s3. exists gl. easy.
          - constructor; try easy. right. exists s3. exists gl. easy.
    } 
    destruct H3 as (zs,(Ha,(Hb,Hc))).
    exists (gtth_send p q zs).
    - split. constructor; try easy.
      clear H H0 H1 H2 H6 H10 Hb Hc. 
      revert Ha H9 H8. revert ctxG ctxJ ys zs. clear p q p0 ctxGLis.
      induction xs; intros; try easy.
      specialize(SList_f a xs H8); intros.
      destruct ys; try easy. destruct zs; try easy. inversion Ha. subst. clear Ha. 
      inversion H9. subst. clear H9.
      destruct H.
      - specialize(IHxs ctxG ctxJ ys zs). apply SList_b. apply IHxs; try easy.
      - destruct H as (H,(a0,Ha)). subst. 
        destruct ys; try easy. destruct zs; try easy. clear H7 H5 H8 IHxs.
        destruct H4; try easy.
        destruct H as (s1,(g1,(g2,(Ha,(Hb,Hc))))). subst.
        destruct H3; try easy. destruct H as (s2,(g3,(g4,(Hd,(He,Hf))))). subst. easy.
    - split.
      assert(exists ks, Forall2 (fun u v => (u = None /\ v = None) \/ (exists ctxGi ctxGi', u = Some ctxGi /\ v = Some ctxGi' /\ (noneLis (Datatypes.length ctxJ) ++ ctxGi) = ctxGi')) ctxGLis ks).
      {
        clear Hc Hb Ha H10 H6 H9 H8 H2 H1 H0 H.
        induction ctxGLis; intros; try easy.
        exists nil. easy.
        destruct IHctxGLis as (ks, H).
        destruct a.
        - exists (Some (noneLis (Datatypes.length ctxJ) ++ l) :: ks). constructor; try easy.
          right. exists l. exists (noneLis (Datatypes.length ctxJ) ++ l). easy.
        - exists (None :: ks). constructor; try easy. left. easy.
      }
      destruct H3 as (ks, H3).
      clear Hc Ha H10 H9 H8 H2 H1 H0 H.
      clear p0 ys. 
      apply used_con with (ctxGLis := ks); try easy.
      - clear Hb. revert H3 H6. 
        revert ctxG ctxJ ks. clear p q xs zs.
        induction ctxGLis; intros; try easy.
        destruct ks; try easy. inversion H3. subst. clear H3.
        inversion H6.
        - subst. destruct ks; try easy. destruct H2; try easy.
          destruct H as (ct1,(ct2,(Ha,(Hb,Hc)))). inversion Ha. subst. constructor.
        - subst. destruct H2. destruct H. subst.
          specialize(IHctxGLis ctxG ctxJ ks). 
          assert(isMergeCtx (noneLis (Datatypes.length ctxJ) ++ ctxG) ks). apply IHctxGLis; try easy.
          constructor. easy.
          destruct H as (ct1,(ct2,Ha)). easy.
        - subst. specialize(IHctxGLis t ctxJ ks H5 H4).
          destruct H2; try easy. destruct H as (ct1,(ct2,(Ha,(Hb,Hc)))). inversion Ha. subst.
          apply cmconss with (t := (noneLis (Datatypes.length ctxJ) ++ t)); try easy.
          clear H4 H5 Ha H6 IHctxGLis. induction ctxJ; intros; try easy.
          simpl. constructor; try easy. left. easy.
      - revert H3 Hb. clear H6.
        revert ctxJ zs ks. clear p q xs ctxG.
        induction ctxGLis; intros.
        - destruct ks; try easy. destruct zs; try easy.
        - destruct ks; try easy. destruct zs; try easy. 
          inversion H3. subst. clear H3. inversion Hb. subst. clear Hb.
          specialize(IHctxGLis ctxJ zs ks H5 H6). constructor; try easy.
          clear IHctxGLis H5 H6.
          - destruct H2. destruct H. subst. destruct H3. destruct H. subst. left. easy.
            destruct H as(ct,(s1,(g1,Ha))). easy.
          - destruct H as (ct1,(ct2,(Ha,(Hb,Hc)))). subst.
            destruct H3; try easy. destruct H as (ct2,(s2,(g2,(Ha,(Hb,Hc))))). inversion Ha. subst.
            right. exists (noneLis (Datatypes.length ctxJ) ++ ct2). exists s2. exists g2. easy.
    - intros.
      inversion H3. 
      - subst. apply H1. constructor.
      - subst. apply H1. constructor.
      - subst. specialize(some_onth_implies_In n zs (s, g) H14); intros.
        specialize(Forall_forall (fun u : option (sort * gtth) =>
        u = None \/ (exists (s : sort) (g : gtth), u = Some (s, g) /\ (ishParts p0 g -> False))) zs); intros.
        destruct H5. specialize(H5 Hc). clear H7 Hc.
        specialize(H5 (Some(s, g)) H4). destruct H5; try easy.
        destruct H5 as (s1,(g1,(Hta,Htb))). inversion Hta. subst.
        apply Htb; try easy.
Qed.

Lemma ctx_merge : forall s s0 s1 g1 l p,
    p <> s -> p <> s0 ->
    (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
       typ_gtth ctxG G' g1 /\
       (ishParts p G' -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
             u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
       usedCtx ctxG G') -> 
       (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
       typ_gtth ctxG G' (gtt_send s s0 l) /\
       (ishParts p G' -> False) /\
       Forall
         (fun u : option gtt =>
          u = None \/
          (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
             u = Some (gtt_send   p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
       usedCtx ctxG G') -> 
       (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
  typ_gtth ctxG G' (gtt_send s s0 (Some (s1, g1) :: l)) /\
  (ishParts p G' -> False) /\
  Forall
    (fun u : option gtt =>
     u = None \/
     (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
        u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
  usedCtx ctxG G').
Proof.
  intros.
  destruct H1 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))).
  destruct H2 as (Gl2,(ctxJ,(He,(Hf,(Hg,Hh))))).
  inversion He. subst.
  - specialize(some_onth_implies_In n ctxJ (gtt_send s s0 l) H1); intros.
    specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxJ); intros.
    destruct H3. specialize(H3 Hg). clear H4 Hg.
    specialize(H3 (Some (gtt_send s s0 l)) H2). destruct H3; try easy.
    destruct H3 as (q1,(lsg,H3)).
    - destruct H3. inversion H3. subst. easy.
    - destruct H3. inversion H3. subst. easy.
    - inversion H3.
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



Lemma balanced_to_tree : forall G p,
    wfgC G ->
    isgPartsC p G ->
    exists G' ctxG, 
       typ_gtth ctxG G' G /\ (ishParts p G' -> False) /\
       List.Forall (fun u => u = None \/ (exists q lsg, u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some (gtt_end))) ctxG /\ usedCtx ctxG G'.
Proof.
  intros.
  specialize(parts_to_word p G H0); intros.
  destruct H1 as (w,(r,Ha)). pose proof H as Htt.
  unfold wfgC in H. destruct H as (Gl,(Hb,(Hc,(Hd,He)))). clear Hb Hc Hd. clear Gl H0.
  pose proof He as Ht.
  unfold balancedG in He.
  specialize(He nil w p r).
  simpl in He.
  assert(exists gn, gttmap G nil None gn).
  {
    destruct G. exists gnode_end. constructor.
    exists (gnode_pq s s0). constructor.
  }
  destruct H as (gn, H). specialize(He gn H).
  assert(gttmap G w None (gnode_pq p r) \/ gttmap G w None (gnode_pq r p)).
  {
    destruct Ha. right. easy. left. easy.
  }
  specialize(He H0). clear H H0. destruct He as (k, H).
  clear Ha.
  revert H Ht Htt. revert G p. clear w r gn.
  induction k; intros.
  - specialize(H nil).
    assert(exists gn, gttmap G nil None gn).
    {
      destruct G. exists gnode_end. constructor.
      exists (gnode_pq s s0). constructor.
    }
    destruct H0 as (gn, H0). inversion H0; try easy. subst.
    - assert(exists w2 w0 : seq.seq fin,
        [] = w2 ++ w0 /\
        (exists r : string,
           gttmap gtt_end w2 None (gnode_pq p r) \/ gttmap gtt_end w2 None (gnode_pq r p))).
      {
        apply H. left. easy.
      }
      clear H. destruct H1 as (w2,(w0,(Ha,Hb))). destruct w2; try easy. simpl in Ha. subst.
      destruct Hb as (r, Hb).
      destruct Hb. inversion H. inversion H.
    - assert(exists w2 w0 : seq.seq fin,
      [] = w2 ++ w0 /\
      (exists r : string, gttmap G w2 None (gnode_pq p r) \/ gttmap G w2 None (gnode_pq r p))).
      apply H. right. split. easy. exists gn. easy.
      destruct H2 as (w2,(w0,(Ha,Hb))). destruct w2; try easy. simpl in Ha. subst.
      clear H.
      destruct Hb as (r, Hb).
      destruct Hb.
      - inversion H. subst.
        exists (gtth_hol 0). exists [Some (gtt_send p r xs)].
        split.
        - constructor; try easy.
        - split. intros. inversion H1.
        - split. constructor; try easy. right. exists r. exists xs. left. easy.
        - assert(usedCtx (extendLis 0 (Some (gtt_send p r xs))) (gtth_hol 0)). constructor.
          simpl in H1. easy.
      - inversion H. subst.
        exists (gtth_hol 0). exists [Some (gtt_send r p xs)].
        split.
        - constructor; try easy.
        - split. intros. inversion H1.
        - split. constructor; try easy. right. exists r. exists xs. right. left. easy.
        - assert(usedCtx (extendLis 0 (Some (gtt_send r p xs))) (gtth_hol 0)). constructor.
          simpl in H1. easy.
  - destruct G.
    - exists (gtth_hol 0). exists [Some gtt_end].
      split. constructor. easy.
      split. intros. inversion H0.
      split. constructor; try easy. right. exists p. exists nil. right. right. easy.
      assert(usedCtx (extendLis 0 (Some (gtt_end))) (gtth_hol 0)). constructor. simpl in H0. easy.
    - specialize(balanced_cont Ht); intros.
      - case_eq (eqb p s); intros.
        assert (p = s). apply eqb_eq; try easy. subst.
        exists (gtth_hol 0). exists [Some (gtt_send s s0 l)].
        - split. constructor. easy.
        - split. intros. inversion H2.
        - split. constructor; try easy. right. exists s0. exists l. left. easy.
        - assert(usedCtx (extendLis 0 (Some (gtt_send s s0 l))) (gtth_hol 0)). constructor. simpl in H2. easy.
      - case_eq (eqb p s0); intros.
        assert (p = s0). apply eqb_eq; try easy. subst.
        exists (gtth_hol 0). exists [Some (gtt_send s s0 l)].
        - split. constructor. easy.
        - split. intros. inversion H3.
        - split. constructor; try easy. right. exists s. exists l. right. left. easy.
        - assert(usedCtx (extendLis 0 (Some (gtt_send s s0 l))) (gtth_hol 0)). constructor. simpl in H2. easy.
      - assert (p <> s). apply eqb_neq; try easy. 
        assert (p <> s0). apply eqb_neq; try easy.
        clear H1 H2.
      assert(Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\
        (forall w' : seq.seq fin,
       gttmap g w' None gnode_end \/
       Datatypes.length w' = k /\ (exists tc : gnode, gttmap g w' None tc) ->
       exists w2 w0 : seq.seq fin,
         w' = w2 ++ w0 /\
         (exists r : string, gttmap g w2 None (gnode_pq p r) \/ gttmap g w2 None (gnode_pq r p)))
      )) l).
      {
        apply Forall_forall; intros.
        destruct x.
        - specialize(in_some_implies_onth p0 l H1); intros.
          destruct H2 as (n, H2). destruct p0.
          right. exists s1. exists g. split. easy.
          intros.
          specialize(H (n :: w')).
          assert(exists w2 w0 : seq.seq fin,
            (n :: w')%SEQ = w2 ++ w0 /\
            (exists r : string,
               gttmap (gtt_send s s0 l) w2 None (gnode_pq p r) \/
               gttmap (gtt_send s s0 l) w2 None (gnode_pq r p))).
          {
            apply H; try easy.
            destruct H5. left. apply gmap_con with (st := s1) (gk := g); try easy.
            right. destruct H5. split. simpl. apply eq_S. easy.
            destruct H6. exists x.
            apply gmap_con with (st := s1) (gk := g); try easy.
          }
          destruct H6 as (w2,(w0,(Ha,Hb))).
          destruct w2.
          - simpl in *. subst.
            destruct Hb as (r, Hb). destruct Hb. inversion H6. subst. easy.
            inversion H6. subst. easy.
          - inversion Ha. subst.
            exists w2. exists w0. split. easy.
            destruct Hb as (r, Hb). exists r.
            destruct Hb.
            - left. inversion H6. subst. specialize(eq_trans (esym H14) H2); intros.
              inversion H7. subst. easy.
            - right. inversion H6. subst. specialize(eq_trans (esym H14) H2); intros.
              inversion H7. subst. easy.
        - left. easy.
      }
      assert(Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\
        exists (G' : gtth) (ctxG : seq.seq (option gtt)),
        typ_gtth ctxG G' g /\
        (ishParts p G' -> False) /\
        Forall
          (fun u : option gtt =>
           u = None \/
           (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
              u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
        usedCtx ctxG G'
      )) l). 
      {
        clear H Ht.
        assert(s <> s0).
        {
          specialize(wfgC_triv s s0 l Htt); intros. easy.
        }
        specialize(wfgC_after_step_all H Htt); intros. clear H Htt.
        revert H0 IHk H1 H3 H4 H2. revert k s s0 p.
        induction l; intros; try easy.
        inversion H1. subst. clear H1. inversion H0. subst. clear H0. inversion H2. subst. clear H2.
        specialize(IHl k s s0 p).
        assert(Forall
        (fun u : option (sort * gtt) =>
         u = None \/
         (exists (s : sort) (g : gtt),
            u = Some (s, g) /\
            (exists (G' : gtth) (ctxG : seq.seq (option gtt)),
               typ_gtth ctxG G' g /\
               (ishParts p G' -> False) /\
               Forall
                 (fun u0 : option gtt =>
                  u0 = None \/
                  (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
                     u0 = Some (gtt_send p q lsg) \/ u0 = Some (gtt_send q p lsg) \/ u0 = Some gtt_end))
                 ctxG /\ usedCtx ctxG G'))) l).
         apply IHl; try easy.
         constructor; try easy. clear H H9 H8 H7 IHl.
         destruct H5. left. easy.
         destruct H as (s1,(g1,(Ha,Hb))). subst. 
         destruct H1; try easy.
         destruct H as (s2,(g2,(Hc,Hd))). inversion Hc. subst.
         destruct H6; try easy. destruct H as (s3,(g3,(He,Hf))). inversion He. subst.
         specialize(IHk g3 p). right. exists s3. exists g3. split. easy. apply IHk; try easy.
      }
    clear H1 H0 Ht H IHk.
    assert(SList l).
    {
      specialize(wfgC_triv s s0 l Htt); intros. easy.
    }
    clear Htt.
    revert H H2 H3 H4. clear k. revert s s0 p.
    induction l; intros; try easy.
    specialize(SList_f a l H); intros. clear H.
    inversion H2. subst. clear H2.
    destruct H0.
    - specialize(IHl s s0 p).
      assert(exists (G' : gtth) (ctxG : seq.seq (option gtt)),
        typ_gtth ctxG G' (gtt_send s s0 l) /\
        (ishParts p G' -> False) /\
        Forall
          (fun u : option gtt =>
           u = None \/
           (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
              u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG /\
        usedCtx ctxG G').
      {
        apply IHl; try easy.
      }
      clear H6 H IHl.
      destruct H5.
      - subst.
        destruct H0 as (Gl,(ctxG,(Ha,(Hb,(Hc,Hd))))).
        inversion Ha.
        - subst.
          specialize(some_onth_implies_In n ctxG (gtt_send s s0 l) H); intros.
          specialize(Forall_forall (fun u : option gtt =>
        u = None \/
        (exists (q : string) (lsg : seq.seq (option (sort * gtt))),
           u = Some (gtt_send p q lsg) \/ u = Some (gtt_send q p lsg) \/ u = Some gtt_end)) ctxG); intros.
          destruct H1. specialize(H1 Hc). clear H2 Hc.
          specialize(H1 (Some (gtt_send s s0 l)) H0). destruct H1; try easy.
          destruct H1 as (q1,(lsg,He)).
          - destruct He. inversion H1. subst. easy.
          - destruct H1. inversion H1. subst. easy.
          - inversion H1. 
        - subst.
          exists (gtth_send s s0 (None :: xs)). exists ctxG.
          - split. constructor; try easy.
            constructor; try easy. left. easy.
          - split. 
            intros. apply Hb. inversion H. subst. easy. subst. easy. subst.
            destruct n; try easy.
            apply ha_sendr with (n := n) (s := s1) (g := g); try easy.
          - split. easy.
          - inversion Hd. subst. apply used_con with (ctxGLis := (None :: ctxGLis)); try easy.
            constructor; try easy.
            constructor; try easy. left. easy.
      - destruct H as (s1,(g1,(Ha,Hb))). subst.
        specialize(ctx_merge s s0 s1 g1 l p); intros. apply H; try easy.
    destruct H as (H1,(a0,H2)). subst. clear H6 IHl.
    destruct H5; try easy.
    destruct H as (s1,(g1,(Ha,Hb))). inversion Ha. subst. clear Ha.
    destruct Hb as (Gl,(ctxG,(Hc,(Hd,(He,Hf))))).
    exists (gtth_send s s0 [Some (s1, Gl)]). exists ctxG.
    - split. constructor; try easy. constructor; try easy.
      right. exists s1. exists Gl. exists g1. easy.
    - split. intros. apply Hd. inversion H. subst. easy. subst. easy. 
      subst. destruct n; try easy.
      - simpl in H8. inversion H8. subst. easy.
      - simpl in H8. destruct n; try easy.
    - split. easy.
    - apply used_con with (ctxGLis := [Some ctxG]); try easy.
      - constructor.
      - constructor; try easy. right. exists ctxG. exists s1. exists Gl. easy.
Qed.



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

Lemma _a_29_part_helper_recv : forall n ys1 x4 p ys,
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
  - subst. constructor; try easy. right. easy. 
    apply IHys0; try easy.
Qed.


(* need *)
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

(* need *)
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


Lemma _a_29_11 : forall G p q x,
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

Lemma _a_29_part : forall ctxG G' G p q x ys,
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
    specialize(_a_29_part_helper_recv n ys1 x4 p ys H32 H28); intros. destruct H35. subst.
    specialize(_a_29_part_helper_send n ys2 x3 q x H31 H34); intros. destruct H35. subst.
    specialize(H6 x4 x5). apply H6; try easy.
    apply proj_mon.
    apply proj_mon.
Qed.

    
Lemma _a_29_16 : forall G' ctxG G p q ys x, 
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


Lemma _a_29_s_helper {A B} : forall (ys : list (option (A * B))),
  exists SI, Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g, u = Some s /\ v = Some (s, g))) SI ys.
Proof.
  induction ys; intros; try easy.
  exists nil. easy.
  destruct IHys. destruct a. destruct p. exists (Some a :: x). constructor; try easy.
  right. exists a. exists b. easy.
  exists (None :: x). constructor; try easy. left. easy.
Qed.

Lemma _a_29_s_helper2s : forall n s1 g1 xs ys ys0 ys1 ctxG p q,
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

Lemma _a_29_s_helper2 : forall G' G p q PT QT ctxG,
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

Lemma _a_29_helper2 : forall lsg SI x p,
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

Lemma _a_29_helper3 : forall n lsg x0 Sk ys q,
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


Lemma _a_29_s : forall G p q PT QT S T S' T' n, 
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
  specialize(_a_29_11 G p q PT H H0); intros.
  destruct H4 as (G',(ctxG,(Ha,(Hb,(Hc,Hd))))). 
  exists G'. exists ctxG.
  specialize(_a_29_part ctxG G' G p q PT QT Ha H0 H2 Hb); intros.
  specialize(_a_29_16 G' ctxG G p q QT PT H2 Hc Hd Hb H4 Ha); intros. clear Hc.
  specialize(_a_29_s_helper PT); intros. destruct H6 as (SI, H6).
  exists SI. exists S. split. easy. split. easy. split. easy.
  specialize(_a_29_s_helper2 G' G p q PT QT ctxG); intros.
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
  - specialize(_a_29_helper2 lsg SI PT p); intros. apply H5; try easy.
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




Variant gttstep (R: gtt -> gtt -> part -> part -> nat -> Prop): gtt -> gtt -> part -> part -> nat -> Prop :=
  | steq : forall p q xs s gc n,
                  p <> q ->
                  Datatypes.Some (s, gc) = onth n xs ->
                  gttstep R (gtt_send p q xs) gc p q n
  | stneq: forall p q r s xs ys n,
                  p <> q ->
                  r <> s ->
                  r <> p ->
                  r <> q ->
                  s <> p ->
                  s <> q ->
                  List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ isgPartsC p g /\ isgPartsC q g)) xs ->
                  List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ R g g' p q n)) xs ys ->
                  gttstep R (gtt_send r s xs) (gtt_send r s ys) p q n.

Definition gttstepC g1 g2 p q n := paco5 gttstep bot5 g1 g2 p q n. 

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

Lemma wfgC_step_part_helper : forall lis1 xs,
    SList lis1 -> 
    Forall2
       (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : global) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) lis1 xs -> 
    SList xs.
Proof.
  induction lis1; intros; try easy.
  destruct xs; try easy.
  specialize(SList_f a lis1 H); intros.
  inversion H0. clear H0. subst.
  destruct H1. apply SList_b. specialize(IHlis1 xs). apply IHlis1; try easy.
  destruct H0. destruct H1. subst. destruct xs; try easy.
  destruct H5; try easy. destruct H0 as (s0,(g0,(g1,(Ha,(Hb,Hc))))). inversion Ha. subst.
  easy.
Qed.

Lemma wfgC_step_part : forall G G' p q n,
    wfgC G ->
    gttstepC G G' p q n -> 
    isgPartsC p G.
Proof.
  intros.
  - pinversion H0. subst. 
    apply triv_pt_p; try easy.
  - subst.
    unfold wfgC in H.
    destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))). 
    specialize(guard_breakG_s2 (gtt_send r s xs) Gl Hc Hb Ha); intros.
    clear Ha Hb Hc. clear Gl. destruct H as (Gl,(Ha,(Hb,(Hc,He)))).
    destruct Ha. subst. pinversion He. apply gttT_mon.
    destruct H as (p1,(q1,(lis1,Ht))). subst. pinversion He. subst.
    inversion Hc. subst.
    specialize(wfgC_step_part_helper lis1 xs H12 H9); intros.
    clear H14 H13.
    unfold isgPartsC.
    specialize(slist_implies_some xs H); intros. destruct H10 as (k,(G,Hta)).
    specialize(some_onth_implies_In k xs G Hta); intros.
    specialize(Forall_forall (fun u : option (sort * gtt) =>
        u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ isgPartsC p g /\ isgPartsC q g)) xs); intros.
    destruct H11. specialize(H11 H7). clear H13 H7.
    specialize(H11 (Some G) H10). destruct H11; try easy. 
    destruct H7 as (s1,(g1,(Hsa,(Hsb,Hsc)))). inversion Hsa. subst.
    unfold isgPartsC in Hsb. destruct Hsb as (G1,(Hla,(Hlb,Hlc))).
    exists (g_send r s (overwrite_lis k (Some (s1, G1)) lis1)). 
    clear Hsc H10 Hsa H H12 He H8. clear H6 H4 H2 H1 Hd H0 Hc.
    revert Hlc Hlb Hla Hta H9 Hb H5 H3. revert G1 g1 s1 lis1 xs r s p. clear q n ys.
    induction k; intros; try easy.
    - destruct xs; try easy. destruct lis1; try easy. 
      inversion H9. subst. clear H9.
      simpl in Hta. subst.
      destruct H2; try easy. destruct H as (s2,(g2,(g3,(Hsa,(Hsb,Hsc))))).
      inversion Hsb. subst.
      split.
      - pfold. constructor. constructor; try easy.
        right. exists s2. exists G1. exists g3. split. easy. split. easy. left. easy.
      - split.
        apply guard_cont_b.
        specialize(guard_cont Hb); intros. inversion H. subst. clear H.
        constructor; try easy. right. exists s2. exists G1. easy.
      - apply pa_sendr with (n := 0) (s := s2) (g := G1); try easy.
    - destruct xs; try easy. destruct lis1; try easy. 
      inversion H9. subst. clear H9.
      specialize(IHk G1 g1 s1 lis1 xs).
      specialize(guard_cont Hb); intros. inversion H. subst. clear H.
      assert((forall n : fin, exists m : fin, guardG n m (g_send r s lis1))). apply guard_cont_b; try easy.
      assert(gttTC (g_send r s (overwrite_lis k (Some (s1, G1)) lis1)) (gtt_send r s xs) /\
      (forall n : fin, exists m : fin, guardG n m (g_send r s (overwrite_lis k (Some (s1, G1)) lis1))) /\
      isgParts p (g_send r s (overwrite_lis k (Some (s1, G1)) lis1))).
      {
        apply IHk; try easy.
      }
      destruct H0 as (Hma,(Hmb,Hmc)).
      - split. pfold. constructor.
        pinversion Hma; try easy. subst. constructor; try easy. apply gttT_mon.
      - split. apply guard_cont_b; try easy. simpl.
        specialize(guard_cont Hmb); intros.
        constructor; try easy.
      - apply pa_sendr with (n := S k) (s := s1) (g := G1); try easy.
        apply overwriteExtract; try easy.
      apply gttT_mon.
      apply step_mon.
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
  specialize(_a_29_11 G q p LP H H3); intros.
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


Lemma wfgC_after_step_helper : forall n0 s G' lsg lis1, 
      Some (s, G') = onth n0 lsg -> 
      Forall2
       (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : global) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) lis1 lsg -> 
      Forall
       (fun u : option (sort * global) =>
        u = None \/ (exists (s : sort) (g : global), u = Some (s, g) /\ wfG g)) lis1 -> 
      Forall
      (fun u : option (sort * gtt) =>
       u = None \/ (exists (s : sort) (g : gtt), u = Some (s, g) /\ balancedG g)) lsg -> 
      Forall
       (fun u : option (sort * global) =>
        u = None \/
        (exists (s : sort) (g : global),
           u = Some (s, g) /\ (forall n : fin, exists m : fin, guardG n m g))) lis1 -> 
      exists G1, onth n0 lis1 = Some(s, G1) /\ gttTC G1 G' /\ wfG G1 /\ balancedG G' /\ (forall n, exists m, guardG n m G1).
Proof.
  induction n0; intros.
  - destruct lsg; try easy. destruct lis1; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    inversion H3. subst. clear H3. 
    simpl in H. subst.
    destruct H7; try easy. destruct H as (s0,(g1,(g2,(Ha,(Hb,Hc))))). inversion Hb. subst.
    destruct H5; try easy. destruct H as (s1,(g3,(Hd,He))). inversion Hd. subst.
    destruct H4; try easy. destruct H as (s2,(g4,(Hf,Hg))). inversion Hf. subst.
    destruct H2; try easy. destruct H as (s3,(g5,(Hh,Hi))). inversion Hh. subst.
    simpl. exists g5. pclearbot. easy.
  - destruct lsg; try easy. destruct lis1; try easy.
    inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst. clear H2.
    inversion H3. subst. clear H3. 
    specialize(IHn0 s G' lsg lis1). apply IHn0; try easy.
Qed.

Lemma wfgC_after_step_helper2 : forall lis ys ys0 n p q,
    SList lis -> 
    Forall2
       (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : global) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco2 gttT bot2 g g')) lis ys -> 
    Forall2
        (fun u v : option (sort * gtt) =>
         u = None /\ v = None \/
         (exists (s : sort) (g g' : gtt),
            u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q n))
        ys ys0 ->
    SList ys0.
Proof.
  induction lis; intros; try easy.
  specialize(SList_f a lis H); intros. destruct ys; try easy. destruct ys0; try easy.
  specialize(IHlis ys ys0 n p q). inversion H0. subst. clear H0. inversion H1. subst. clear H1.
  destruct H2. apply SList_b. apply IHlis; try easy.
  destruct H0. destruct H1. subst. destruct H6; try easy.
  destruct H0 as (s0,(g0,(g1,(Ha,(Hb,Hc))))). subst. destruct ys; try easy.
  destruct H5; try easy. destruct H0 as (s2,(g2,(g3,(Hta,(Htb,Htc))))). inversion Hta. subst.
  destruct ys0; try easy.
Qed.

Lemma wfgC_after_step_helper3 : forall ys0 xs,
      SList ys0 -> 
      Forall2
       (fun (u : option (sort * global)) (v : option (sort * gtt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : global) (g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ gttTC g g')) xs ys0 -> 
      SList xs.
Proof.
  induction ys0; intros; try easy.
  specialize(SList_f a ys0 H); intros. 
  destruct xs; try easy.
  specialize(IHys0 xs). inversion H0. subst. clear H0.
  destruct H1. apply SList_b. apply IHys0; try easy.
  destruct H0. destruct H1. subst.
  destruct H5; try easy. destruct H0 as (s,(g,(g',(Ha,(Hb,Hc))))). inversion Hb. subst.
  destruct xs; try easy.
Qed.


Theorem wfgCw_after_step : forall G G' p q n, wfgC G -> gttstepC G G' p q n -> wfgCw G'. 
Proof.
  intros. 
  pose proof H as Ht. unfold wfgC in H.
  destruct H as (Gl,(Ha,(Hb,(Hc,Hd)))).
  specialize(wfgC_step_part G G' p q n Ht H0); intros.
  specialize(balanced_to_tree G p Ht H); intros. clear Ht H.
  destruct H1 as (Gt,(ctxG,(Hta,(Htb,(Htc,Htd))))).
  clear Htd.
  revert Htc Htb Hta H0 Hd Hc Hb Ha.
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
    assert(List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ wfgCw g)) ys0).
    {
      clear H14 H13 Hb Hc He H16 H11 H10 H9 H8 H5 H4 H6 Hta H0 Hd.
      apply Forall_forall; intros. 
      destruct x.
      - specialize(in_some_implies_onth p0 ys0 H0); intros. destruct H4 as (n0 ,H4). clear H0.
        right. destruct p0. exists s0. exists g. split. easy.
        clear Ht.
        revert H4 H3 H1 H15 H2 H17 H7 Htc H Htb.
        revert g s0 lis ys ys0 ctxG n p q xs s s'.
        induction n0; intros.
        - destruct ys0; try easy. destruct ys; try easy. destruct lis; try easy.
          destruct xs; try easy.
          inversion H3. subst. clear H3. inversion H1. subst. clear H1. inversion H15. subst. clear H15.
          inversion H2. subst. clear H2. inversion H17. subst. clear H17. inversion H7. subst. clear H7.
          inversion H. subst. clear H.
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
          specialize(Hq g9 g2 p q n g8 ctxG).
          apply Hq; try easy. 
          specialize(ishParts_x Htb); try easy.
          destruct Hc; try easy.
          destruct Hi; try easy. 
        - destruct ys0; try easy. destruct ys; try easy. destruct lis; try easy.
          destruct xs; try easy.
          inversion H3. subst. clear H3. inversion H1. subst. clear H1. inversion H15. subst. clear H15.
          inversion H2. subst. clear H2. inversion H17. subst. clear H17. inversion H7. subst. clear H7.
          inversion H. subst. clear H. 
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
    clear H3 H1 H15 H2 Hb Hc He H17 H16 H11 H10 H9 H8 H5 H4 H7 Hta H0 Hd Htb Htc H H6 H13. clear Ht H19 H20.
    clear p q xs n ctxG ys lis. rename H14 into H. rename H12 into H1.
    assert(exists xs, List.Forall2 (fun u v => (u = None /\ v = None) \/ (exists s g g', u = Some(s, g) /\ v = Some(s, g') /\ gttTC g g')) xs ys0 /\ 
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ wfG g)) xs /\
    List.Forall (fun u => u = None \/ (exists s g, u = Some(s, g) /\ (forall n, exists m, guardG n m g))) xs).
    {
      clear H. revert H1. clear H18. revert ys0. clear s s'.
      induction ys0; intros; try easy.
      - exists nil. easy.
      - inversion H1. subst. clear H1.
        specialize(IHys0 H3). destruct IHys0 as (xs,H).
        destruct H2. 
        - subst. exists (None :: xs).
          split. constructor; try easy. left. easy.
          split. constructor; try easy. left. easy.
          constructor; try easy. left. easy.
        - destruct H0 as (s,(g,(Ha,Hb))). subst.
          unfold wfgC in Hb. destruct Hb.
          exists (Some(s, x) :: xs).
          split. constructor; try easy. right. exists s. exists x. exists g. easy.
          split. constructor; try easy. right. exists s. exists x. easy.
          constructor; try easy. right. exists s. exists x. easy.
    }
    destruct H0 as (xs,(Ha,(Hb,Hc))).
    exists (g_send s s' xs).
    - split. pfold. constructor; try easy.
      revert Ha. apply Forall2_mono; intros; try easy. destruct H0. left. easy.
      destruct H0 as (s0,(g0,(g1,(Hta,(Htb,Htc))))). subst. right. exists s0. exists g0. exists g1. 
      split. easy. split. easy. left. easy.
    - split. constructor; try easy.
      specialize(wfgC_after_step_helper3 ys0 xs H18 Ha); try easy.
    - apply guard_cont_b; try easy.
    apply gttT_mon.
    apply step_mon.
Qed.


Lemma _3_19_ctx_loose : forall [ctxG p q l T T' SI],
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

Lemma _3_19_step_helper3 : forall xs ys ctxG,
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
  specialize(_a_29_s (gtt_send s s' ys) p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
  destruct H4. destruct H4. destruct H4. destruct H4. destruct H4. destruct H5. destruct H6.
  rename x0 into ctxG. rename x into Gl.
  destruct H7.
  specialize(_3_19_ctx_loose H7); intros. clear H7 H8 H3 H1.
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
          specialize(_3_19_step_helper3 xs0 ys2 ctxG H H0); intros.
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
  specialize(_a_29_11 G p q LP H H0); intros.
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
    specialize(_a_29_part x (gtth_send s s0 xs) G p q LP LQ H3 H0 H1 H4); intros.
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
  specialize(_a_29_11 G p q LP H H0); intros.
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


Lemma _3_19_step_helper2 : forall xs ys p q l ctxG,
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



Lemma _3_19_step_helper4 : forall ys zs p q l,
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


Lemma _3_19_step_helper5 : forall ys zs p q l,
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

Lemma _3_19_step_helper6 : forall ys p q,
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

Lemma _3_19_step_helper7 : forall ys x p,
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

Lemma guardG_xs : forall [x s s' o],
    (forall n : fin, exists m : fin, guardG n m (g_send s s' (o :: x))) ->
    (forall n : fin, exists m : fin, guardG n m (g_send s s' x)). 
Proof.
  intros.
  specialize(H n). destruct H. exists x0.
  inversion H. constructor. subst.
  constructor. inversion H3; try easy.
Qed.

Lemma _3_19_step_helper8 : forall ys x s s' p,
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

Lemma _3_19_step : forall p q l G L1 L2 S T S' T',
  wfgC G ->
  projectionC G p (ltt_send q L1) -> 
  onth l L1 = Some(S, T) ->
  projectionC G q (ltt_recv p L2) -> 
  onth l L2 = Some(S', T') ->
  (isgPartsC p G /\ isgPartsC q G) /\ exists G', gttstepC G G' p q l. 
Proof.
  intros. 
  specialize(_a_29_s G p q L1 L2 S T S' T' l H H0 H1 H2 H3); intros.
  destruct H4. rename x into Gl.
  destruct H4. destruct H4. destruct H4. destruct H4. destruct H5. destruct H6. destruct H7. clear H8. rename x into ctxG.
  specialize(_3_19_ctx_loose H7); intros. clear H7.
  
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
    specialize(_3_19_step_helper2 xs ys p q l ctxG H0); intros. destruct H10.
    rename x into zs. destruct H10.
    specialize(_3_19_step_helper3 xs ys ctxG H14 H15); intros.
    specialize(_3_19_step_helper4 ys zs p q l H25 H11); intros.
    assert((exists G' : gtt, gttstepC (gtt_send s s' ys) G' p q l)).
    {
      exists (gtt_send s s' zs).
      pfold. apply stneq; try easy.
      specialize(_3_19_step_helper5 ys zs p q l H11); intros. easy.
    }
    split; try easy.
    apply proj_mon.
    apply proj_mon.
Qed.

Lemma _3_19_h_helper : forall L1 l S T,
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


Lemma _3_19_h : forall p q l G L1 L2 S T xs y,
  wfgC G ->
  projectionC G p (ltt_send q L1) -> 
  subtypeC (ltt_send q (extendLis l (Datatypes.Some(S,T)))) (ltt_send q L1) ->
  projectionC G q (ltt_recv p L2) -> 
  onth l xs = Some y ->
  subtypeC (ltt_recv p xs) (ltt_recv p L2) -> 
  exists G', gttstepC G G' p q l.
Proof.
  intros.
  specialize(_3_19_step p q l G L1 L2); intros.
  specialize(subtype_send_inv q (extendLis l (Some (S, T))) L1 H1); intros.
  specialize(subtype_recv_inv p xs L2 H4); intros.
  specialize(projection_step_label_s G p q l L1 L2); intros.
  specialize(_3_19_h_helper L1 l S T H6); intros. destruct H9.
  specialize(H8 x). 
  assert(exists (LS' : sort) (LT' : ltt), onth l L2 = Some (LS', LT')). apply H8; try easy.
  destruct H10. destruct H10.
  destruct x. 
  specialize(H5 s l0 x0 x1).
  apply H5; try easy. 
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
      specialize(_3_19_ctx_loose H3); intros. clear H3. clear SI S T S' T'. clear LP LQ.
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

Lemma part_cont_false_all_s : forall ys2 s s' p,
      p <> s -> p <> s' ->
      wfgCw (gtt_send s s' ys2) ->
      (isgPartsC p (gtt_send s s' ys2) -> False) ->
      List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ (isgPartsC p g -> False))) ys2.
Proof.
  intros.
  apply Forall_forall; intros.
  destruct x.
  - destruct p0. right. exists s0. exists g. split. easy.
    intros. apply H2.
    specialize(in_some_implies_onth (s0, g) ys2 H3); intros. destruct H5 as (n,H5).
    clear H3 H2.
    unfold wfgCw in H1. destruct H1 as (Gl,(Ha,(Hb,Hc))).
    specialize(guard_breakG_s2 (gtt_send s s' ys2) Gl Hc Hb Ha); intros.
    clear Ha Hb Hc. clear Gl.
    destruct H1 as (Gl,(Ha,(Hb,(Hc,Hd)))).
    destruct Ha. subst. pinversion Hd; try easy. apply gttT_mon.
    destruct H1 as (p1,(q1,(lis,He))). subst. pinversion Hd; try easy. subst.
    unfold isgPartsC in H4.
    destruct H4 as (G1,(He,(Hf,Hg))).
    unfold isgPartsC.
    exists (g_send s s' (overwrite_lis n (Some (s0, G1)) lis)).
    clear Hc Hd.
    specialize(guard_cont Hb); intros. clear Hb.
    revert H2 H1 H5 Hg Hf He H0 H. revert lis G1 g s0 s s' p ys2.
    induction n; intros; try easy.
    - destruct ys2; try easy. destruct lis; try easy.
      inversion H2. subst. clear H2. inversion H1. subst. clear H1.
      simpl in H5. subst. destruct H7; try easy. destruct H1 as (s1,(g1,(g2,(Hta,(Htb,Htc))))).
      inversion Htb. subst. destruct H4; try easy.
      destruct H1 as (s2,(g3,(Htd,Hte))). inversion Htd. subst.
      split. pfold. constructor; try easy. constructor; try easy.
      right. exists s2. exists G1. exists g2. split. easy. split. easy. left. easy.
      split. apply guard_cont_b. constructor; try easy. 
      right. exists s2. exists G1. easy.
      apply pa_sendr with (n := 0) (s := s2) (g := G1); try easy.
    - destruct ys2; try easy. destruct lis; try easy.
      inversion H2. subst. clear H2. inversion H1. subst. clear H1.
      specialize(IHn lis G1 g s0 s s' p ys2).
      assert(gttTC (g_send s s' (overwrite_lis n (Some (s0, G1)) lis)) (gtt_send s s' ys2) /\
      (forall n0 : fin, exists m : fin, guardG n0 m (g_send s s' (overwrite_lis n (Some (s0, G1)) lis))) /\
      isgParts p (g_send s s' (overwrite_lis n (Some (s0, G1)) lis))).
      apply IHn; try easy.
      destruct H1 as (Hta,(Htb,Htc)).
      clear H6 H9 IHn.
      pinversion Hta. subst. clear Hta.
      specialize(guard_cont Htb); intros. clear Htb.
      split.
      - pfold. constructor. constructor; try easy.
      - split. apply guard_cont_b. constructor; try easy.
      - inversion Htc. subst. easy. subst. easy.
        subst.
        apply pa_sendr with (n := S n0) (s := s1) (g := g0); try easy.
    apply gttT_mon.
    apply gttT_mon.
    left. easy.
Qed.

Lemma part_cont_false_all : forall ys2 s s' p,
      p <> s -> p <> s' ->
      wfgC (gtt_send s s' ys2) ->
      (isgPartsC p (gtt_send s s' ys2) -> False) ->
      List.Forall (fun u => u = None \/ (exists s g, u = Some (s, g) /\ (isgPartsC p g -> False))) ys2.
Proof.
  intros. apply part_cont_false_all_s with (s := s) (s' := s'); try easy.
  unfold wfgC in *. unfold wfgCw.
  destruct H1. exists x. easy.
Qed.

Lemma _3_19_12_helper : forall ys2 x p,
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


Lemma _3_19_1_helper : forall p q l G G' LP LQ S T S' T',
  wfgC G -> 
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some(S, T) ->
  projectionC G q (ltt_recv p LQ) -> 
  onth l LQ = Some(S', T') ->
  gttstepC G G' p q l -> 
  projectionC G' p T.
Proof.
  intros.
  specialize(_a_29_s G p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
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
      specialize(_3_19_ctx_loose H8); try easy.
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

      specialize(_3_19_12_helper ys2 x p); intros.
      assert(Forall (fun u : option ltt => u = None \/ u = Some ltt_end) x).
      apply H19; try easy.
      specialize(wfgCw_after_step_all H22 H16); try easy.
      specialize(merge_end_s x T H29 H14); intros. subst.
      apply proj_end; try easy.
    apply step_mon.
    apply proj_mon.
    apply proj_mon.
Qed.

Lemma _3_19_2_helper : forall p q l G G' LP LQ S T S' T',
  wfgC G -> 
  projectionC G p (ltt_send q LP) ->
  onth l LP = Some(S, T) ->
  projectionC G q (ltt_recv p LQ) -> 
  onth l LQ = Some(S', T') ->
  gttstepC G G' p q l -> 
  projectionC G' q T'.
Proof.
  intros.
  specialize(_a_29_s G p q LP LQ S T S' T' l H H0 H1 H2 H3); intros.
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
      specialize(_3_19_ctx_loose H8); try easy.
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

      specialize(_3_19_12_helper ys2 x q); intros.
      assert(Forall (fun u : option ltt => u = None \/ u = Some ltt_end) x).
      apply H19; try easy.
      specialize(wfgCw_after_step_all H22 H16); try easy.
      specialize(merge_end_s x T' H29 H14); intros. subst.
      apply proj_end; try easy.
    apply step_mon.
    apply proj_mon.
    apply proj_mon.
Qed.

Lemma _3_19_1 : forall p q l G G' LP LQ S T S' T' xs,
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
  specialize(_3_19_1_helper p q l G G' LP LQ); intros.
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


Lemma _3_19_2 : forall p q l G G' LP LQ S T S' T' xs,
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
  specialize(_3_19_2_helper p q l G G' LP LQ); intros.
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


Lemma _3_19_3_helper_h1 : forall l lsg ys s' Gjk s,
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


Lemma _3_19_3_helper_h2 : forall [n ys s0 g xs ctxG],
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

Lemma _3_19_3_helper_h3 : forall ys ys2 p q l,
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

Lemma _3_19_3_helper_h4 : forall l lsg s' Gjk ys s T,
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

Lemma _3_19_3_helper_h5 : forall ys ys2 ys3 p q l r,
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

Lemma _3_19_3_helper_h6 : forall ys ys2 ys3 p q l r,
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


Lemma _3_19_3_helper : forall G G' p q s l L1 L2 LS LT LS' LT' T,
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
  specialize(_a_29_s G p q L1 L2 LS LT LS' LT' l H H0 H1 H2 H3); intros. 
  destruct H8. rename x into Gl. rename H into Ht.
  destruct H8 as (ctxG,(SI,(Sn,(Ha,(Hb,(Hc,(Hd,He))))))).
  clear He.
  specialize(_3_19_ctx_loose Hd); intros. clear Hd.
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
      specialize(_3_19_3_helper_h4 l lsg s' Gjk ys s T); intros.
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
        specialize(_3_19_3_helper_h2 H10 H15); intros. destruct H13 as (g', (H13, Hla)).
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
    specialize(_3_19_3_helper_h3 ys ys2 p q l H37 Hla Htk); intros. clear Hla H37.
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
      specialize(_3_19_3_helper_h5 ys ys2 ys3 p q l r); intros. apply H12; try easy.
    - subst.
      specialize(wfgC_after_step_all H25 Ht); intros.
      exists (ltt_send s' ys3). split; try easy.
      pfold. constructor; try easy.
      apply triv_pt_p; try easy. 
      specialize(H10 r H28 H29).
      specialize(_3_19_3_helper_h5 ys ys2 ys3 p q l r); intros. apply H12; try easy.
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
        specialize(_3_19_3_helper_h6 ys ys2 ys3 p q l r); intros. apply H10; try easy.
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
  specialize(_3_19_1_helper p q l G G' l1 l2 s1 t1 s2 t2); intros.
  exists t1.
  specialize(_3_19_2_helper p q l G G' l1 l2 s1 t1 s2 t2); intros.
  exists t2.
  split. apply H2; try easy. apply H3; try easy.
Qed.

Lemma nil_word : forall G, exists tc, gttmap G nil None tc.
Proof.
  intros.
  destruct G.
  exists gnode_end. constructor.
  exists (gnode_pq s s0). constructor.
Qed.

Lemma word_step_back_s : forall [w G G' tc p q l], 
    gttstepC G G' p q l ->
    gttmap G' w None tc ->
    gttmap G w None tc \/ (exists w0 w1, w = (w0 ++ w1) /\ gttmap G (w0 ++ l :: w1) None tc /\ gttmap G w0 None (gnode_pq p q)).
Proof.
  induction w; intros.
  - pinversion H.
    - subst. right. exists nil. exists nil. split. easy.
      simpl. split. apply gmap_con with (st := s) (gk := G'); try easy.
      constructor.
    - subst. left. inversion H0; try easy. subst. constructor.
    apply step_mon.
  - pinversion H.
    - subst. right. exists nil. exists (a :: w).
      split. easy. split. apply gmap_con with (st := s) (gk := G'); try easy.
      constructor.
    - subst.
      inversion H0. subst. clear H7.
      specialize(Forall2_prop_l a xs ys (st, gk) (fun u v : option (sort * gtt) =>
        u = None /\ v = None \/
        (exists (s : sort) (g g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q l)) H16 H8); intros.
      destruct H7 as (p1,(Ha,Hb)). destruct Hb; try easy.
      destruct H7 as (s1,(g1,(g2,(Hb,(Hc,Hd))))). inversion Hc. subst.
      destruct Hd; try easy.
      specialize(IHw g1 g2 tc p q l H7 H17).
      destruct IHw.
      - left. apply gmap_con with (st := s1) (gk := g1); try easy.
      - right.
        destruct H9 as (w0,(w1,(Hd,He))). subst.
        exists (a :: w0). exists w1. split. easy.
        split.
        apply gmap_con with (st := s1) (gk := g1); try easy.
        apply gmap_con with (st := s1) (gk := g1); try easy.
      apply step_mon.
Qed.


Lemma word_step_back_ss : forall [w G G' tc p q l], 
    gttstepC G G' p q l ->
    gttmap G' w None tc ->
    (forall w0 w1 tc1, w = w0 ++ w1 -> (gttmap G' w0 None tc1 <-> gttmap G w0 None tc1)) \/ 
    (exists w0 w1, w = (w0 ++ w1) /\ 
    (forall s1 s2 s3 tc1, w0 = s1 ++ s2 ++ (s3 :: nil) -> (gttmap G' s1 None tc1 <-> gttmap G s1 None tc1)) /\
    (forall s1 s2 tc1, w1 = s1 ++ s2 -> (gttmap G' (w0 ++ s1) None tc1 <-> gttmap G (w0 ++ l :: s1) None tc1)) 
     /\ gttmap G w0 None (gnode_pq p q)).
Proof.
  induction w; intros.
  - pinversion H.
    - subst. right. exists nil. exists nil. split. easy.
      - split. intros. destruct s1; try easy. destruct s2; try easy.
      - split. intros. destruct s1; try easy. simpl in *.
        split.
        - intros.
          apply gmap_con with (st := s) (gk := G'); try easy.
        - intros. inversion H4. subst.
          specialize(eq_trans H2 H12); intros. inversion H3. subst. easy.
      - constructor. 
    - subst. left. inversion H0; try easy. subst.
      intros. split.
      - intros. destruct w0; try easy. inversion H10; try easy. subst. constructor.
      - intros. destruct w0; try easy. inversion H10; try easy. 
    apply step_mon.
  - pinversion H.
    - subst. right. exists nil. exists (a :: w).
      split. easy.
      - split. intros. destruct s1; try easy. destruct s2; try easy.
      - split. intros.
        split.
        - intros. apply gmap_con with (st := s) (gk := G'); try easy.
        - intros. inversion H4. subst.
          specialize(eq_trans H2 H12); intros. inversion H5. subst. easy.
      - constructor.
    - subst.
      inversion H0. subst. clear H7.
      specialize(Forall2_prop_l a xs ys (st, gk) (fun u v : option (sort * gtt) =>
        u = None /\ v = None \/
        (exists (s : sort) (g g' : gtt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco5 gttstep bot5 g g' p q l)) H16 H8); intros.
      destruct H7 as (p1,(Ha,Hb)). destruct Hb; try easy.
      destruct H7 as (s1,(g1,(g2,(Hb,(Hc,Hd))))). inversion Hc. subst.
      destruct Hd; try easy.
      specialize(IHw g1 g2 tc p q l H7 H17).
      destruct IHw.
      - left.
        intros. split. intros. destruct w0. 
        - inversion H11. subst. constructor.
        - inversion H10. subst.
          inversion H11. subst.
          specialize(eq_trans (esym H21) H16); intros. inversion H12. subst.
          specialize(H9 w0 w1 tc1).
          assert(gttmap g1 w0 None tc1). apply H9; try easy.
          apply gmap_con with (st := s1) (gk := g1); try easy.
        intros. destruct w0.
        - inversion H11. subst. constructor.
        - inversion H10. subst.
          inversion H11. subst.
          specialize(eq_trans (esym H21) Hb); intros. inversion H12. subst.
          specialize(H9 w0 w1 tc1).
          assert(gttmap g2 w0 None tc1). apply H9; try easy.
          apply gmap_con with (st := s1) (gk := g2); try easy.
      - right.
        destruct H9 as (w0,(w1,(Hd,He))). subst.
        exists (a :: w0). exists w1. split. easy.
        destruct He as (He,(Hf,Hg)).
        - split. intros. 
          destruct s0. split. intros.
          - inversion H10. subst. constructor.
          - intros. inversion H10. subst. constructor.
          - inversion H9. subst.
          split. intros. inversion H10. subst. 
            specialize(eq_trans (esym H20) H16); intros. inversion H11. subst.
            specialize(He s0 s2 s3 tc1).
            assert(gttmap g1 s0 None tc1). apply He; try easy.
            apply gmap_con with (st := s1) (gk := g1); try easy.
          - intros. inversion H10. subst.
            specialize(eq_trans (esym H20) Hb); intros. inversion H11. subst.
            specialize(He s0 s2 s3 tc1).
            assert(gttmap g2 s0 None tc1). apply He; try easy.
            apply gmap_con with (st := s1) (gk := g2); try easy.
        - split. intros.
          specialize(Hf s0 s2 tc1).
          split. intros.
            inversion H10. subst. specialize(eq_trans (esym H20) H16); intros. inversion H9. subst.
            assert(gttmap g1 (w0 ++ l :: s0) None tc1). apply Hf; try easy.
            apply gmap_con with (st := s1) (gk := g1); try easy.
          - intros.
            inversion H10. subst. specialize(eq_trans (esym H20) Hb); intros. inversion H9. subst.
            assert(gttmap g2 (w0 ++ s0) None tc1). apply Hf; try easy.
            apply gmap_con with (st := s1) (gk := g2); try easy.
          - apply gmap_con with (st := s1) (gk := g1); try easy.
      apply step_mon.
Qed.

Lemma decon_word {A} : forall (w2 : list A) l w0 w1 w3,
    w0 ++ l :: w1 = w2 ++ w3 -> 
    w0 = w2 \/ (exists wi wj, w0 = w2 ++ wi ++ (wj :: nil)) \/ (exists wi wj, w1 = wi ++ wj /\ w2 = w0 ++ l :: wi).
Proof.
  induction w2; intros.
  - destruct w0. left. easy.
    right. simpl. left. 
    clear H. revert a. induction w0; intros. exists nil. exists a. easy.
    specialize(IHw0 a). destruct IHw0 as (wi,(wj,Ha)). exists (a0 :: wi). exists wj. 
    replace (a :: w0) with (wi ++ wj :: nil) in *. constructor.
  - destruct w0.
    simpl. right. right. inversion H. subst. exists w2. exists w3. easy.
    inversion H. subst. clear H.
    specialize(IHw2 l w0 w1 w3 H2).
    destruct IHw2. left. subst. easy.
    destruct H.
    - destruct H as (wi,(wj,Ha)). right. left. exists wi. exists wj. subst. easy.
    - destruct H as (wi,(wj,Ha)). right. right. destruct Ha. subst.
      exists wi. exists wj. easy.
Qed.

Lemma inj_gttmap : forall [w G tc1 tc2], gttmap G w None tc1 -> gttmap G w None tc2 -> tc1 = tc2.
Proof.
  induction w; intros.
  - inversion H. subst. inversion H0. subst. easy.
    subst. inversion H0. subst. easy.
  - inversion H. subst.
    inversion H0. subst.
    specialize(eq_trans (esym H4) H10); intros. inversion H1. subst.
    specialize(IHw gk0 tc1 tc2 H7 H11). subst. easy.
Qed.

Lemma stword {A} : forall w2 wi (wj : A) w1,
    (w2 ++ wi ++ wj :: nil) ++ w1 = w2 ++ wi ++ wj :: w1.
Proof.
  intros.
  specialize(app_assoc w2 wi (wj :: w1)); intros.
  apply eq_trans with (y := (w2 ++ wi) ++ wj :: w1); try easy. clear H.
  specialize(app_assoc w2 wi (wj :: nil)); intros.
  replace (w2 ++ wi ++ wj :: nil) with ((w2 ++ wi) ++ wj :: nil) in *. clear H.
  specialize(app_assoc (w2 ++ wi) (wj :: nil) w1); intros.
  replace (((w2 ++ wi) ++ wj :: nil) ++ w1) with ((w2 ++ wi) ++ (wj :: nil) ++ w1) in *. clear H.
  constructor.
Qed.

Lemma cut_word {A} : forall (w : list A) k k',
    k <= k' -> 
    length w = k' ->
    exists w' w2, length w' = k /\ w = w' ++ w2.
Proof.
  induction w; intros.
  - destruct k'; try easy. 
    destruct k; try easy. exists nil. exists nil. easy.
  - destruct k'; try easy.
    destruct k.
    - exists nil. exists (a :: w). easy.
    - specialize(IHw k k').
      assert(exists w' w2 : list A, length w' = k /\ w = w' ++ w2).
      {
        apply IHw; try easy. 
        apply eq_add_S; try easy.
      }
      destruct H1 as (w1,(w2,(Ha,Hb))).
      exists (a :: w1). exists w2. subst. easy.
Qed.

Lemma map_back_word : forall [w0 G w1 tc],
    gttmap G (w0 ++ w1) None tc -> 
    exists tc, gttmap G w0 None tc.
Proof.
  induction w0; intros.
  - destruct G.
    - exists gnode_end. constructor.
    - exists (gnode_pq s s0). constructor.
  - inversion H. subst.
    specialize(IHw0 gk w1 tc H6). destruct IHw0 as (tc1,H1).
    exists tc1.
    apply gmap_con with (st := st) (gk := gk); try easy.
Qed.

Lemma cut_further : forall k k' G p0,
    k <= k' -> 
    (forall w'0 : list fin,
     gttmap G w'0 None gnode_end \/
     length w'0 = k /\ (exists tc : gnode, gttmap G w'0 None tc) ->
     exists w2 w0 : list fin,
       w'0 = w2 ++ w0 /\
       (exists r : string,
          gttmap G w2 None (gnode_pq p0 r) \/ gttmap G w2 None (gnode_pq r p0))) ->
    (forall w'0 : list fin,
     gttmap G w'0 None gnode_end \/
     length w'0 = k' /\ (exists tc : gnode, gttmap G w'0 None tc) ->
     exists w2 w0 : list fin,
       w'0 = w2 ++ w0 /\
       (exists r : string,
          gttmap G w2 None (gnode_pq p0 r) \/ gttmap G w2 None (gnode_pq r p0))).
Proof.
  intros.
  destruct H1.
  - specialize(H0 w'0). apply H0. left. easy.
  - destruct H1 as (H1,(tc,H2)). rename w'0 into w.
    specialize(cut_word w k k' H H1); intros.
    destruct H3 as (w0,(w1,(Ha,Hb))).
    specialize(H0 w0). subst.
    assert(gttmap G w0 None gnode_end \/
     length w0 = length w0 /\ (exists tc : gnode, gttmap G w0 None tc)).
    {
      right. split. easy.
      apply map_back_word with (w1 := w1) (tc := tc); try easy.
    }
    specialize(H0 H1). clear H1.
    destruct H0 as (w2,(w3,(Ha,(r,Hb)))). subst.
    exists w2. exists (w3 ++ w1). split. apply esym. apply app_assoc.
    exists r. easy.
Qed.

Lemma word_to_parts : forall G w' p q0,
             gttmap G w' None (gnode_pq p q0) \/
             gttmap G w' None (gnode_pq q0 p) -> 
             wfgCw G -> 
             isgPartsC p G.
Proof.
  intros G w'. revert G.
  induction w'; intros.
  - destruct H.
    inversion H. subst. apply triv_pt_p_s; try easy.
    inversion H. subst. apply triv_pt_q_s; try easy.
  - destruct H.
    - inversion H. subst.
      specialize(wfgCw_after_step_all); intros.
      specialize(wfgCw_triv p0 q xs H0); intros. destruct H2.
      specialize(H1 xs p0 q H2 H0); intros.
      clear H2 H3.
      specialize(Forall_prop a xs (st, gk) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgCw g)) H4 H1); intros.
      destruct H2; try easy. destruct H2 as (s1,(g1,(Ha,Hb))). inversion Ha. subst.
      specialize(IHw' g1 p q0).
      assert(isgPartsC p g1). apply IHw'; try easy.
      left. easy.
      - case_eq (eqb p p0); intros.
        assert (p = p0). apply eqb_eq; try easy. subst. apply triv_pt_p_s; try easy.
      - case_eq (eqb p q); intros.
        assert (p = q). apply eqb_eq; try easy. subst. apply triv_pt_q_s; try easy.
      - assert (p <> p0). apply eqb_neq; try easy.
        assert (p <> q). apply eqb_neq; try easy.
        apply part_cont_b_s with (n := a) (s := s1) (g := g1); try easy.
    - inversion H. subst.
      specialize(wfgCw_after_step_all); intros.
      specialize(wfgCw_triv p0 q xs H0); intros. destruct H2.
      specialize(H1 xs p0 q H2 H0); intros.
      clear H2 H3.
      specialize(Forall_prop a xs (st, gk) (fun u : option (sort * gtt) =>
        u = None \/ (exists (st : sort) (g : gtt), u = Some (st, g) /\ wfgCw g)) H4 H1); intros.
      destruct H2; try easy. destruct H2 as (s1,(g1,(Ha,Hb))). inversion Ha. subst.
      specialize(IHw' g1 p q0).
      assert(isgPartsC p g1). apply IHw'; try easy.
      right. easy.
      - case_eq (eqb p p0); intros.
        assert (p = p0). apply eqb_eq; try easy. subst. apply triv_pt_p_s; try easy.
      - case_eq (eqb p q); intros.
        assert (p = q). apply eqb_eq; try easy. subst. apply triv_pt_q_s; try easy.
      - assert (p <> p0). apply eqb_neq; try easy.
        assert (p <> q). apply eqb_neq; try easy.
        apply part_cont_b_s with (n := a) (s := s1) (g := g1); try easy.
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

Lemma _a22_2 : forall M M' G, typ_sess M G -> unfoldP M M' -> typ_sess M' G.
Proof.
  intros. revert H. revert G. induction H0; intros; try easy.
  - inversion H0. subst. 
    inversion H4. subst. clear H4. inversion H7. subst. clear H7. 
    apply t_sess; try easy. constructor; try easy. constructor; try easy.
    destruct H5. exists x. split; try easy. destruct H4. split.
    destruct H5 as (H5, H6).
    - specialize(_a23_d (p_rec P) P x nil nil H5 (erefl (p_rec P))); intros.
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
    specialize(_a23_d (p_rec P) P T nil nil Hb (erefl (p_rec P))); intros.
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


Inductive stepE : relation expr := 
  | ec_succ  : forall e n, stepE e (e_val (vnat n)) -> stepE (e_succ e) (e_val (vnat (n+1)))
  | ec_neg   : forall e n, stepE e (e_val (vint n)) -> stepE (e_neg e) (e_val (vint (-n)))
  | ec_neg2  : forall e n, stepE e (e_val (vnat n)) -> stepE (e_neg e) (e_val (vint (-(Z.of_nat n)))) 
  | ec_t_f   : forall e,   stepE e (e_val (vbool true)) -> stepE (e_not e) (e_val (vbool false))
  | ec_f_t   : forall e,   stepE e (e_val (vbool false)) -> stepE (e_not e) (e_val (vbool true))
  | ec_gt_t0 : forall e e' m n, Z.lt (Z.of_nat n) (Z.of_nat m) -> 
                           stepE e (e_val (vnat m)) -> stepE e' (e_val (vnat n)) ->
                           stepE (e_gt e e') (e_val (vbool true)) 
  | ec_gt_t1 : forall e e' m n, Z.lt n (Z.of_nat m) -> 
                           stepE e (e_val (vnat m)) -> stepE e' (e_val (vint n)) ->
                           stepE (e_gt e e') (e_val (vbool true)) 
  | ec_gt_t2 : forall e e' m n, Z.lt (Z.of_nat n) m -> 
                           stepE e (e_val (vint m)) -> stepE e' (e_val (vnat n)) ->
                           stepE (e_gt e e') (e_val (vbool true)) 
  | ec_gt_t3 : forall e e' m n, Z.lt n m -> 
                           stepE e (e_val (vint m)) -> stepE e' (e_val (vint n)) ->
                           stepE (e_gt e e') (e_val (vbool true)) 
  | ec_gt_f0 : forall e e' m n, Z.le (Z.of_nat m) (Z.of_nat n) -> 
                           stepE e (e_val (vnat m)) -> stepE e' (e_val (vnat n)) ->
                           stepE (e_gt e e') (e_val (vbool false)) 
  | ec_gt_f1 : forall e e' m n, Z.le (Z.of_nat m) n -> 
                           stepE e (e_val (vnat m)) -> stepE e' (e_val (vint n)) ->
                           stepE (e_gt e e') (e_val (vbool false)) 
  | ec_gt_f2 : forall e e' m n, Z.le m (Z.of_nat n) -> 
                           stepE e (e_val (vint m)) -> stepE e' (e_val (vnat n)) ->
                           stepE (e_gt e e') (e_val (vbool false)) 
  | ec_gt_f3 : forall e e' m n, Z.le m n -> 
                           stepE e (e_val (vint m)) -> stepE e' (e_val (vint n)) ->
                           stepE (e_gt e e') (e_val (vbool false)) 
  | ec_plus0 : forall e e' m n, stepE e (e_val (vnat n)) -> stepE e' (e_val (vnat m)) -> 
                           stepE (e_plus e e') (e_val (vint ((Z.of_nat n) + (Z.of_nat m))))
  | ec_plus1 : forall e e' m n, stepE e (e_val (vnat n)) -> stepE e' (e_val (vint m)) -> 
                           stepE (e_plus e e') (e_val (vint ((Z.of_nat n) + m)))
  | ec_plus2 : forall e e' m n, stepE e (e_val (vint n)) -> stepE e' (e_val (vnat m)) -> 
                           stepE (e_plus e e') (e_val (vint (n + (Z.of_nat m))))
  | ec_plus3 : forall e e' m n, stepE e (e_val (vint n)) -> stepE e' (e_val (vint m)) -> 
                           stepE (e_plus e e') (e_val (vint (n + m)))
  | ec_detl  : forall m n v, stepE m v -> stepE (e_det m n) v
  | ec_detr  : forall m n v, stepE n v -> stepE (e_det m n) v
  | ec_refl  : forall e, stepE e e
  | ec_trans : forall e e' e'', stepE e e' -> stepE e' e'' -> stepE e e''.

   
Lemma expr_typ_step : forall Gs e e' S, typ_expr Gs e S -> stepE e e' -> typ_expr Gs e' S.
Proof.
  intros. revert H. revert S. induction H0; intros; try easy.
  - specialize(inv_expr_succ Gs (e_succ e) S e H (erefl (e_succ e))); intros.
    destruct H1. destruct H2; subst.
    apply sc_valn.
    apply sc_sub with (s := snat). apply sc_valn. apply sni.
  - specialize(inv_expr_neg Gs (e_neg e) S e H (erefl (e_neg e))); intros.
    destruct H1. subst. apply sc_vali.
  - specialize(inv_expr_neg Gs (e_neg e) S e H (erefl (e_neg e))); intros.
    destruct H1. subst. apply sc_vali.
  - specialize(inv_expr_not Gs (e_not e) S e H (erefl (e_not e))); intros.
    destruct H1. subst. apply sc_valb.
  - specialize(inv_expr_not Gs (e_not e) S e H (erefl (e_not e))); intros.
    destruct H1. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_gt Gs (e_gt e e') S e e' H0 (erefl (e_gt e e'))); intros.
    destruct H1. destruct H2. subst. apply sc_valb.
  - specialize(inv_expr_plus Gs (e_plus e e') S e e' H (erefl (e_plus e e'))); intros.
    destruct H0. destruct H1. subst. apply sc_vali.
  - specialize(inv_expr_plus Gs (e_plus e e') S e e' H (erefl (e_plus e e'))); intros.
    destruct H0. destruct H1. subst. apply sc_vali.
  - specialize(inv_expr_plus Gs (e_plus e e') S e e' H (erefl (e_plus e e'))); intros.
    destruct H0. destruct H1. subst. apply sc_vali.
  - specialize(inv_expr_plus Gs (e_plus e e') S e e' H (erefl (e_plus e e'))); intros.
    destruct H0. destruct H1. subst. apply sc_vali.
  - specialize(inv_expr_det Gs (e_det m n) S m n H (erefl (e_det m n))); intros.
    destruct H1. destruct H1. destruct H2.
    apply sc_sub with (s := x); intros; try easy. apply IHstepE; try easy.
  - specialize(inv_expr_det Gs (e_det m n) S m n H (erefl (e_det m n))); intros.
    destruct H1. destruct H1. destruct H2.
    apply sc_sub with (s := x); intros; try easy. apply IHstepE; try easy.
  - specialize(IHstepE1 S H). specialize(IHstepE2 S). apply IHstepE2; try easy.
Qed.


(* substitute e into e_var n of e1, depth d *)
Fixpoint subst_expr (n d : fin) (e : expr) (e1 : expr) : expr :=
  match e1 with 
    | e_var 0     => if Nat.eqb n 0 then (incr_freeE 0 d e) else e_var 0
    | e_var (S m) => if Nat.eqb (S m) n then (incr_freeE 0 d e) else 
                     if Nat.ltb (S m) n then e_var (S m) else e_var m 
    | e_succ e' => e_succ (subst_expr n d e e')
    | e_neg e' => e_neg (subst_expr n d e e')
    | e_not e' => e_not (subst_expr n d e e')
    | e_gt e' e'' => e_gt (subst_expr n d e e') (subst_expr n d e e'')
    | e_plus e' e'' => e_plus (subst_expr n d e e') (subst_expr n d e e'')
    | e_det e' e'' => e_det (subst_expr n d e e') (subst_expr n d e e'')
    | _ => e1
  end.
  
(* For a choice function, substitutes expr to e_var n (decr vars above n), d keeps track of depth of recv return process continuation
 *)
 
Fixpoint subst_expr_proc (p : process) (e : expr) (n d : fin) : process :=
  match p with 
    | p_send pt l e' P => p_send pt l (subst_expr n d e e') (subst_expr_proc P e n d)
    | p_ite e' P Q     => p_ite (subst_expr n d e e') (subst_expr_proc P e n d) (subst_expr_proc Q e n d)
    | p_recv pt lst    => p_recv pt (map (fun x => match x with
                                                | None => None
                                                | Some y => Some (subst_expr_proc y e (S n) (S d))
                                               end) lst)
    | p_rec P          => p_rec (subst_expr_proc P e n d)
    | _ => p
  end.


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

Lemma onth_sless {X} : forall n (Gsl Gsr : list (option X)) x0 S,
      n < length Gsl ->
      onth n (Gsl ++ Some S :: Gsr) = Some x0 ->
      onth n (Gsl ++ Gsr) = Some x0.
Proof.
  intro n. induction n; intros; try easy.
  - destruct Gsl; try easy.
  - destruct Gsl; try easy. apply IHn with (S := S); try easy.
Qed.

Lemma onth_smore {X} : forall n (Gsl Gsr : list (option X)) x0 o S,
      n <> length Gsl ->
      length Gsl <= n ->
      Some x0 = onth n (Gsl ++ Some S :: Gsr) ->
      Some x0 = onth n (o :: Gsl ++ Gsr).
Proof.
  intro n. induction n; intros; try easy.
  destruct Gsl; try easy.
  simpl in *. destruct Gsl; try easy.
  apply IHn with (S := S); try easy. simpl in *.
  specialize(Nat.succ_inj_wd_neg n (length Gsl)); intros. destruct H2. specialize(H2 H). easy.
Qed.

Lemma coq_nat_to_nat : forall a b, (a < b)%coq_nat -> a < b.
Proof.
  induction a; intros.
  - destruct b; try easy.
  - destruct b; try easy.
    specialize(PeanoNat.lt_S_n a b H); intros.
    specialize(IHa b H0). clear H H0.
    revert IHa. revert b.
    induction a; intros.
    - destruct b; try easy.
    - destruct b; try easy.
Qed.


Lemma coq_nat_to_nat_le : forall a b,
  (a <= b)%coq_nat -> 
  a <= b.
Proof.
  induction a; intros.
  - destruct b; try easy.
  - destruct b; try easy.
    specialize(le_S_n a b H); intros.
    specialize(IHa b H0). clear H H0.
    revert IHa. revert b.
    induction a; intros.
    - destruct b; try easy.
    - destruct b; try easy.
Qed.

Lemma expr_subst : forall v ex x d Gsl Gsr S,
        typ_expr (Gsl ++ Gsr) (incr_freeE 0 d v) S ->
        typ_expr (Gsl ++ Some S :: Gsr) ex x ->
        typ_expr (Gsl ++ Gsr) (subst_expr (length Gsl) d v ex) x.
Proof.
  intros v ex. revert v.
  induction ex; intros; try easy.
  - simpl in *.
    specialize(inv_expr_var (e_var n) n (Gsl ++ Some S :: Gsr) x H0 (erefl (e_var n))); intros.
    destruct H1. destruct H1. 
    apply sc_sub with (s := x0); try easy.
    - destruct n; try easy.
      case_eq (Nat.eqb (length Gsl) 0); intros; try easy.
      destruct Gsl; try easy. simpl in *. inversion H1. subst. easy.
    - destruct Gsl; try easy. constructor; try easy.
    destruct Gsl.
    - simpl in *. constructor; try easy.
    - simpl in *.
      case_eq (Nat.eqb n (length Gsl)); intros.
      - specialize(onth_exact Gsl Gsr (Some S)); intros.
        specialize(natb_to_prop n (length Gsl) H3); intros. subst.
        specialize(eq_trans (esym H1) H4); intros. inversion H5. subst. easy.
      case_eq (Datatypes.S n <? Datatypes.S (length Gsl))%nat; intros.
      - specialize(Nat.ltb_lt (Datatypes.S n) (Datatypes.S (length Gsl))); intros.
        destruct H5. specialize(H5 H4). clear H4 H6.
        constructor.
        apply esym. apply onth_sless with (S := S); try easy.
        specialize(PeanoNat.lt_S_n n (length Gsl) H5); intros. 
        apply coq_nat_to_nat. easy.
      - specialize(Nat.ltb_ge(Datatypes.S n) (Datatypes.S (length Gsl))); intros.
        destruct H5. specialize(H5 H4). clear H4 H6.
        constructor.
        apply onth_smore with (S := S); try easy.
        apply natb_to_propf. easy.
        Search((S ?a <= S ?b)%coq_nat).
        specialize(le_S_n (length Gsl) n H5); intros. 
        apply coq_nat_to_nat_le. easy.
  - simpl in *.
    specialize(inv_expr_vali (Gsl ++ Some S :: Gsr) (e_val v) x v H0 (erefl (e_val v))); intros.
    destruct H1.
    - destruct H1. destruct H1. subst. apply sc_vali.
    - destruct H1. destruct H1. destruct H1. subst. apply sc_sub with (s := snat); try easy. apply sc_valn.
    - destruct H1. destruct H1. subst. apply sc_valb.
  - simpl in *.
    specialize(inv_expr_succ (Gsl ++ Some S :: Gsr) (e_succ ex) x ex H0 (erefl (e_succ ex))); intros.
    destruct H1. destruct H2.
    - subst. apply sc_succ. apply IHex with (S := S); try easy.
    - subst. apply sc_sub with (s := snat); try easy. apply sc_succ. apply IHex with (S := S); try easy.
      apply sni.
  - simpl in *.
    specialize(inv_expr_neg (Gsl ++ Some S :: Gsr) (e_neg ex) x ex H0 (erefl (e_neg ex))); intros.
    destruct H1. subst. constructor. apply IHex with (S := S); try easy.
  - simpl in *.
    specialize(inv_expr_not (Gsl ++ Some S :: Gsr) (e_not ex) x ex H0 (erefl (e_not ex))); intros.
    destruct H1. subst. constructor. apply IHex with (S := S); try easy.
  - simpl in *.
    specialize(inv_expr_gt (Gsl ++ Some S :: Gsr) (e_gt ex1 ex2) x ex1 ex2 H0 (erefl (e_gt ex1 ex2))); intros.
    destruct H1. destruct H2. subst.
    constructor. apply IHex1 with (S := S); try easy. apply IHex2 with (S := S); try easy.
  - simpl in *.
    specialize(inv_expr_plus (Gsl ++ Some S :: Gsr) (e_plus ex1 ex2) x ex1 ex2 H0 (erefl (e_plus ex1 ex2))); intros.
    destruct H1. destruct H2. subst.
    constructor. apply IHex1 with (S := S); try easy. apply IHex2 with (S := S); try easy.
  - simpl in *.
    specialize(inv_expr_det (Gsl ++ Some S :: Gsr) (e_det ex1 ex2) x ex1 ex2 H0 (erefl (e_det ex1 ex2))); intros.
    destruct H1. destruct H1. destruct H2.
    apply sc_sub with (s := x0); try easy.
    constructor. apply IHex1 with (S := S); try easy. apply IHex2 with (S := S); try easy.
Qed.

Lemma SList_map_a24 {A} : forall (llp : list (option process)) v d (Gsl : list A),
  SList llp ->
  SList
  (map
     (fun x0 : option process =>
      match x0 with
      | Some y =>
          Some
            (subst_expr_proc y v (Datatypes.S (length Gsl)) (Datatypes.S d))
      | None => None
      end) llp).
Proof.
  intro llp. induction llp; intros; try easy.
  specialize(SList_f a llp H); intros. destruct H0; subst; try easy.
  apply SList_b. apply IHllp; try easy.
  destruct H0. destruct H1. subst. easy.
Qed.

Lemma slideE : forall v Gs d S x0,
               typ_expr Gs (incr_freeE 0 d v) S ->
               typ_expr (Some x0 ::Gs) (incr_freeE 0 (Datatypes.S d) v) S.
Proof.
  intro v. induction v; intros; try easy.
  - simpl in H.
    specialize(inv_expr_var (e_var (n + d)) (n + d) Gs S H (erefl (e_var (n + d)))); intros.
    destruct H0. destruct H0. apply sc_sub with (s := x); try easy.
    constructor. simpl.
    specialize(Nat.add_succ_r n d); intros.
    replace (n + d.+1)%coq_nat with ((n + d)%coq_nat.+1). simpl. easy.
  - simpl in *.
    specialize(inv_expr_vali Gs (e_val v) S v H (erefl (e_val v))); intros.
    - destruct H0. destruct H0. destruct H0. subst. apply sc_vali.
    - destruct H0. destruct H0. destruct H0. subst. apply sc_sub with (s := snat); try easy. apply sc_valn.
    - destruct H0. destruct H0. subst. apply sc_valb.
  - simpl in *.
    specialize(inv_expr_succ Gs (e_succ (incr_freeE 0 d v)) S (incr_freeE 0 d v) H (erefl (e_succ (incr_freeE 0 d v)))); intros.
    destruct H0. destruct H1. subst. constructor. apply IHv; try easy.
    subst. apply sc_sub with (s := snat). constructor. apply IHv; try easy. apply sni.
  - simpl in *.
    specialize(inv_expr_neg Gs (e_neg (incr_freeE 0 d v)) S (incr_freeE 0 d v) H (erefl (e_neg (incr_freeE 0 d v)))); intros.
    destruct H0. subst. constructor. apply IHv; try easy.
  - simpl in *.
    specialize(inv_expr_not Gs (e_not (incr_freeE 0 d v)) S (incr_freeE 0 d v) H (erefl (e_not (incr_freeE 0 d v)))); intros.
    destruct H0. subst. constructor. apply IHv; try easy.
  - simpl in *.
    specialize(inv_expr_gt Gs (e_gt (incr_freeE 0 d v1) (incr_freeE 0 d v2)) S (incr_freeE 0 d v1) (incr_freeE 0 d v2) H (erefl (e_gt (incr_freeE 0 d v1) (incr_freeE 0 d v2)))); intros.
    destruct H0. subst. constructor. apply IHv1; try easy. apply IHv2; try easy.
  - simpl in *.
    specialize(inv_expr_plus Gs (e_plus (incr_freeE 0 d v1) (incr_freeE 0 d v2)) S (incr_freeE 0 d v1) (incr_freeE 0 d v2) H (erefl (e_plus (incr_freeE 0 d v1) (incr_freeE 0 d v2)))); intros.
    destruct H0. subst. constructor. apply IHv1; try easy. apply IHv2; try easy.
  - simpl in *.
    specialize(inv_expr_det Gs (e_det (incr_freeE 0 d v1) (incr_freeE 0 d v2)) S (incr_freeE 0 d v1) (incr_freeE 0 d v2) H (erefl (e_det (incr_freeE 0 d v1) (incr_freeE 0 d v2)))); intros.
    destruct H0. destruct H0. destruct H1.
    apply sc_sub with (s := x); try easy. constructor. apply IHv1; try easy. apply IHv2; try easy.
Qed.


Lemma _a24_helper_recv : forall llp Gsl Gsr Gt d v x S,
    typ_expr (Gsl ++ Gsr) (incr_freeE 0 d v) S ->
    Forall
      (fun u : option process =>
       match u with
       | Some k =>
           forall (v : expr) (d : fin) (Gsl Gsr : list (option sort)) (Gt : ctxT) (S : sort) (T : ltt),
           typ_proc (Gsl ++ Some S :: Gsr) Gt k T ->
           typ_expr (Gsl ++ Gsr) (incr_freeE 0 d v) S ->
           typ_proc (Gsl ++ Gsr) Gt (subst_expr_proc k v (length Gsl) d) T
       | None => True
       end) llp ->
    Forall2
       (fun (u : option process) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (p : process) (s : sort) (t : ltt),
           u = Some p /\ v = Some (s, t) /\ typ_proc (Some s :: Gsl ++ Some S :: Gsr) Gt p t)) llp x ->
    Forall2
        (fun (u : option process) (v0 : option (sort * ltt)) =>
         u = None /\ v0 = None \/
         (exists (p : process) (s : sort) (t : ltt),
            u = Some p /\ v0 = Some (s, t) /\ typ_proc (Some s :: Gsl ++ Gsr) Gt p t))
        (map
           (fun x0 : option process =>
            match x0 with
            | Some y =>
                Some
                  (subst_expr_proc y v (Datatypes.S (length Gsl)) (Datatypes.S d))
            | None => None
            end) llp) x.
Proof.
  intro llp.
  induction llp; intros; try easy.
  inversion H1; subst. easy.
  inversion H1; subst. clear H1. 
  constructor. 
  destruct a; try easy.
  - right. destruct H4; try easy. destruct H1. destruct H1. destruct H1. destruct H1. destruct H2. 
    inversion H1. subst.
    exists (subst_expr_proc x v (Datatypes.S (length Gsl)) (Datatypes.S d)).
    exists x0. exists x1. split; try easy. split; try easy. clear H1.
    inversion H0; subst. clear H0.
    specialize(H4 v (Datatypes.S d) (Some x0 :: Gsl) Gsr Gt S x1).
    apply H4; try easy.
    apply slideE; try easy.
  - left. split; try easy.
    destruct H4; try easy. destruct H1. destruct H1. destruct H1. easy.
  - apply IHllp with (S := S); try easy.
    inversion H0; subst. easy.
Qed.

Lemma _a24_helper : forall v d P Gsl Gsr Gt S T, 
        typ_proc (Gsl ++ Some S :: Gsr) Gt P T -> 
        typ_expr (Gsl ++ Gsr) (incr_freeE 0 d v) S -> 
        typ_proc (Gsl ++ Gsr) Gt (subst_expr_proc P v (length Gsl) d) T.
Proof.
  intros v d P. revert v d.
  induction P using process_ind_ref; intros; try easy.
  - specialize(_a23_e (p_var n) n T (Gsl ++ Some S :: Gsr) Gt H (erefl (p_var n))); intros.
    destruct H1. destruct H1. destruct H2.
    simpl. apply tc_sub with (t := x); intros; try easy.
    constructor; try easy.
    specialize(typable_implies_wfC H); easy.
  - specialize(_a23_f p_inact T (Gsl ++ Some S :: Gsr) Gt H (erefl (p_inact))); intros.
    subst. simpl. constructor.
  - simpl.
    specialize(_a23_bf pt lb ex P (p_send pt lb ex P) (Gsl ++ Some S :: Gsr) Gt T H (erefl (p_send pt lb ex P))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2. 
    apply tc_sub with (t := (ltt_send pt (extendLis lb (Some (x, x0))))); intros; try easy.
    constructor; try easy.
    apply expr_subst with (S := S); try easy.
    apply IHP with (S := S); try easy.
    specialize(typable_implies_wfC H); try easy.
  - specialize(_a23_a pt llp (p_recv pt llp) (Gsl ++ Some S :: Gsr) Gt T H0 (erefl (p_recv pt llp))); intros.
    destruct H2. destruct H2. destruct H3. destruct H4.
    apply tc_sub with (t := ltt_recv pt x); intros; try easy. 
    constructor; try easy.
    apply eq_trans with (y := length llp); try easy.
    apply map_length; try easy. 
    apply SList_map_a24; try easy.
    apply _a24_helper_recv with (S := S); try easy.
    specialize(typable_implies_wfC H0); try easy.
  - specialize(_a23_c (p_ite e P1 P2) e P1 P2 T (Gsl ++ Some S :: Gsr) Gt H (erefl (p_ite e P1 P2))); intros.
    destruct H1. destruct H1. destruct H1. destruct H2. destruct H3. destruct H4.
    specialize(typable_implies_wfC H); intros.
    constructor.
    apply expr_subst with (S := S); try easy.
    apply IHP1 with (S := S); try easy.
    apply tc_sub with (t := x); try easy.
    apply IHP2 with (S := S); try easy.
    apply tc_sub with (t := x0); try easy.
  - specialize(_a23_d (p_rec P) P T (Gsl ++ Some S :: Gsr) Gt H (erefl (p_rec P))); intros.
    destruct H1. destruct H1.
    apply tc_sub with (t := x); try easy.
    simpl in *. constructor. apply IHP with (S := S); try easy.
    specialize(typable_implies_wfC H); try easy. 
Qed.

Lemma _a24 : forall v Gs Gt P S T,
        typ_proc (Some S :: Gs) Gt P T -> 
        typ_expr Gs v S -> 
        typ_proc Gs Gt (subst_expr_proc P v 0 0) T.
Proof.
  intros. 
  specialize(_a24_helper v 0 P nil Gs Gt S T); intros. simpl in H1. apply H1; try easy.
  specialize(trivial_incrE 0 v); intros. replace (incr_freeE 0 0 v) with v. easy.
Qed.
    

Inductive multiC : relation gtt := 
  | multiC_refl : forall G, multiC G G
  | multiC_step : forall G1 G2 G3 p q n, gttstepC G1 G2 p q n -> multiC G2 G3 -> multiC G1 G3.
  

Lemma _3_21_1_helper : forall l x1 xs x4 x5 y,
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

Lemma noin_cat_and {A} : forall pt (l1 l2 : list A), ~ In pt (l1 ++ l2) -> ~ (In pt l1 \/ In pt l2).
Proof.
  induction l1; intros; try easy.
  simpl in *. apply Classical_Prop.and_not_or. split; try easy.
  simpl in *. specialize(Classical_Prop.not_or_and (a = pt) (In pt (l1 ++ l2)) H); intros.
  destruct H0. 
  apply Classical_Prop.and_not_or.
  specialize(IHl1 l2 H1).
  specialize(Classical_Prop.not_or_and (In pt l1) (In pt l2) IHl1); intros. destruct H2.
  split; try easy. apply Classical_Prop.and_not_or. split; try easy.
Qed.

Lemma wfC_helper : forall l LQ SL' TL' lis,
    onth l LQ = Some (SL', TL') -> 
    Forall2
       (fun (u : option (sort * local)) (v : option (sort * ltt)) =>
        u = None /\ v = None \/
        (exists (s : sort) (g : local) (g' : ltt),
           u = Some (s, g) /\ v = Some (s, g') /\ upaco2 lttT bot2 g g')) lis LQ -> 
    exists T, onth l lis = Some(SL', T) /\ lttTC T TL'.
Proof.
  induction l; intros.
  - destruct LQ; try easy.
    inversion H0. subst. clear H0 H5. simpl in H.
    subst. destruct H4; try easy.
    destruct H as (s,(g,(g',(Ha,(Hb,Hc))))). subst. inversion Hb. subst.
    exists g. destruct Hc; try easy.
  - destruct LQ ;try easy.
    inversion H0. subst. clear H0. 
    specialize(IHl LQ SL' TL' l0). apply IHl; try easy.
Qed.

Lemma wfC_recv :  forall [l LQ SL' TL' q],
        wfC (ltt_recv q LQ) -> 
        onth l LQ = Some (SL', TL') -> 
        wfC TL'.
Proof.  
  intros.
  unfold wfC in *.
  destruct H as (T,(Ha,(Hb,Hc))).
  specialize(guard_breakL_s2 (ltt_recv q LQ) T Hc Hb Ha); intros.
  clear Ha Hb Hc. clear T.
  destruct H as (T,(Hb,(Hc,(Hd,He)))).
  destruct Hb.
  - subst. pinversion He; try easy. apply lttT_mon.
  - destruct H as (p0,(lis,Hf)).
    destruct Hf. subst. pinversion He. apply lttT_mon.
  - subst. pinversion He; try easy. subst.
    specialize(wfC_helper l LQ SL' TL' lis H0 H1); intros.
    destruct H as (T,(Hf,Hg)).
    exists T. split. easy. clear Hg H1 H0 He.
    clear TL' LQ.
    split.
    - inversion Hd. subst.
      clear H1 Hd Hc. revert Hf H2. revert lis. induction l; intros; try easy.
      - destruct lis; try easy. inversion H2. subst. clear H2 H3.
        simpl in *. subst. destruct H1; try easy.
        destruct H as (s,(g,(Ha,Hb))). inversion Ha. subst. easy.
      - destruct lis; try easy. inversion H2. subst. clear H2.
        specialize(IHl lis). apply IHl; try easy.
    - intros. specialize(Hc (S n)).
      destruct Hc. inversion H. subst. 
      clear Hd H. revert Hf H3. revert lis.
      induction l; intros; try easy.
      - destruct lis; try easy.
        inversion H3. subst. clear H3 H2. simpl in *. subst.
        destruct H1; try easy. destruct H as (s,(g,(Ha,Hb))). inversion Ha. subst.
        exists x. easy.
      - destruct lis; try easy.
        inversion H3. subst. clear H3.
        specialize(IHl lis). apply IHl; try easy.
    apply lttT_mon.
Qed.

Lemma wfC_send : forall [l LP SL TL p],
        wfC (ltt_send p LP) -> 
        onth l LP = Some (SL, TL) -> 
        wfC TL.
Proof.
  intros.
  unfold wfC in *.
  destruct H as (T,(Ha,(Hb,Hc))).
  specialize(guard_breakL_s2 (ltt_send p LP) T Hc Hb Ha); intros.
  clear Ha Hb Hc. clear T.
  destruct H as (T,(Hb,(Hc,(Hd,He)))).
  destruct Hb.
  - subst. pinversion He; try easy. apply lttT_mon.
  - destruct H as (p0,(lis,Hf)).
    destruct Hf. subst. pinversion He; try easy. subst.
    specialize(wfC_helper l LP SL TL lis H0 H1); intros.
    destruct H as (T,(Hf,Hg)).
    exists T. split. easy. clear Hg H1 H0 He.
    clear TL LP.
    split.
    - inversion Hd. subst.
      clear H1 Hd Hc. revert Hf H2. revert lis. induction l; intros; try easy.
      - destruct lis; try easy. inversion H2. subst. clear H2 H3.
        simpl in *. subst. destruct H1; try easy.
        destruct H as (s,(g,(Ha,Hb))). inversion Ha. subst. easy.
      - destruct lis; try easy. inversion H2. subst. clear H2.
        specialize(IHl lis). apply IHl; try easy.
    - intros. specialize(Hc (S n)).
      destruct Hc. inversion H. subst. 
      clear Hd H. revert Hf H3. revert lis.
      induction l; intros; try easy.
      - destruct lis; try easy.
        inversion H3. subst. clear H3 H2. simpl in *. subst.
        destruct H1; try easy. destruct H as (s,(g,(Ha,Hb))). inversion Ha. subst.
        exists x. easy.
      - destruct lis; try easy.
        inversion H3. subst. clear H3.
        specialize(IHl lis). apply IHl; try easy.
    apply lttT_mon.
  - subst. pinversion He; try easy. apply lttT_mon.
Qed.


Lemma _3_19_3_helper_s : forall M p q G G' l L1 L2 S T xs y,
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
    specialize(_3_19_3_helper G G' p0 q s l L1 L2 x x1 x0 x2 T'); intros.
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

Lemma _3_21_helper : forall l xs x1 y,
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

Lemma _3_21_helper_1 : forall [l LQ SL' TL' x x1 x0 q],
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

Lemma _3_21_helper_2 : forall [l LP SL TL LT S p],
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

Lemma _3_21_helper_3 : forall M G pt,
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

Lemma guardP_cont_recv_n : forall l xs y q, 
       (forall n : fin, exists m : fin, guardP n m (p_recv q xs)) -> 
        onth l xs = Some y -> 
        (forall n : fin, exists m : fin, guardP n m y).
Proof.
  induction l; intros; try easy.
  - destruct xs; try easy.
    simpl in H0. subst. specialize(H (Nat.succ n)).
    destruct H. inversion H. subst.
    inversion H3. subst. destruct H2; try easy.
    destruct H0 as (g,(Ha,Hb)). inversion Ha. subst. exists x. easy.
  - destruct xs; try easy.
    specialize(IHl xs y q). apply IHl; try easy.
    intros. specialize(H n0). destruct H.
    inversion H. subst. exists 0. constructor.
    subst. exists x. inversion H4. subst. constructor; try easy.
Qed. 

Inductive peq_w : process -> process -> Prop := 
  | peq_var : forall n, peq_w (p_var n) (p_var n)
  | peq_inact : peq_w p_inact p_inact
  | peq_send : forall pt lb e e' p1 p2, peq_w p1 p2 -> peq_w (p_send pt lb e p1) (p_send pt lb e' p2)
  | peq_recv : forall pt xs ys, Forall2 (fun u v => (u = None /\ v = None) \/ (exists p p', u = Some p /\ v = Some p' /\ peq_w p p')) xs ys -> peq_w (p_recv pt xs) (p_recv pt ys)
  | peq_ite  : forall e1 p1 q1 e2 p2 q2, peq_w p1 p2 -> peq_w q1 q2 -> peq_w (p_ite e1 p1 q1) (p_ite e2 p2 q2)
  | peq_rec : forall p1 p2, peq_w p1 p2 -> peq_w (p_rec p1) (p_rec p2).

Lemma peq_after_incr : forall g p0 m n k l,
        peq_w g p0 -> 
        peq_w (incr_free m n k l g) (incr_free m n k l p0).
Proof.
  induction g using process_ind_ref; intros; try easy.
  - inversion H. subst. constructor.
  - inversion H. subst. constructor.
  - inversion H. subst. constructor; try easy. apply IHg; try easy.
  - inversion H0. subst. constructor; try easy.
    revert H4 H. clear H0. revert llp m n k l.
    induction ys; intros; try easy.
    - destruct llp; try easy.
    - destruct llp; try easy.
      inversion H. subst. clear H. inversion H4. subst. clear H4.
      specialize(IHys llp m n k l H7 H3). constructor; try easy. clear IHys H3 H7.
      destruct H5.
      - destruct H. subst. left. easy.
      - destruct H as (p1,(p2,(Ha,(Hb,Hc)))). subst.
        right. exists (incr_free m (S n) k l p1). exists (incr_free m (S n) k l p2). split. easy.
        split. easy.
        apply H2; try easy.
  - inversion H. subst. constructor. apply IHg1; try easy. apply IHg2; try easy.
  - inversion H. subst. constructor. apply IHg; try easy.
Qed.

Lemma peq_after_subst : forall g1 g Q m n k p0 p1,
        substitutionP m n k g g1 Q -> 
        peq_w g p0 -> peq_w g1 p1 ->
        exists Q' : process, substitutionP m n k p0 p1 Q' /\ peq_w Q Q'.
Proof.
  induction g1 using process_ind_ref; intros.
  - inversion H1. subst.
    inversion H. subst.
    - exists (incr_free 0 0 n0 k p0). split. constructor. 
      apply peq_after_incr; try easy.
    - subst. exists (p_var 0). split. constructor. easy. constructor.
    - subst. exists (p_var y). split. constructor; try easy. constructor.
    - subst. exists (p_var (S y)). split. constructor; try easy. constructor.
  - inversion H1. subst. 
    inversion H. subst. exists p_inact. split. constructor. constructor.
  - inversion H1. subst.
    inversion H. subst.
    specialize(IHg1 g Q' m n k p0 p3 H12 H0 H7). destruct IHg1 as (q1,(Ha,Hb)).
    exists (p_send pt lb e' q1). split. constructor; try easy. constructor; try easy.
  - inversion H2. subst. inversion H0. subst.
    clear H2 H0.
    assert(exists ys3, Forall2 (fun u v => (u = None /\ v = None) \/ (exists p p', u = Some p /\ v = Some p' /\ substitutionP m n (S k) p0 p p')) ys ys3 /\ Forall2 (fun u v => (u = None /\ v = None) \/ (exists p p', u = Some p /\ v = Some p' /\ peq_w p p')) ys0 ys3).
    {
      revert H11 H6 H1 H.
      revert llp g m n k p0 ys0.
      induction ys; intros.
      - destruct llp; try easy. destruct ys0; try easy. exists nil. easy.
      - destruct llp; try easy. destruct ys0; try easy.
        inversion H11. subst. clear H11. inversion H6. subst. clear H6.
        inversion H. subst. clear H.
        specialize(IHys llp g m n k p0 ys0 H7 H9 H1 H6).
        clear H6 H9 H7.
        destruct IHys as (ys3,(Ha,Hb)).
        destruct H4.
        - destruct H. subst. destruct H5. destruct H. subst.
          exists (None :: ys3). split. constructor; try easy. left. easy. constructor; try easy. left. easy. 
          destruct H as (p1,(p2,Hc)). easy.
        - destruct H as (k1,(l1,(Hc,(Hd,He)))). subst.
          destruct H5; try easy. destruct H as (p1,(p2,(Hf,(Hg,Hh)))). inversion Hf. subst.
          specialize(H3 g l1 m n (S k) p0 p2 He H1 Hh).
          destruct H3 as (q1,(Hg,Hi)).
          exists (Some q1 :: ys3).
          - split. constructor; try easy. right. exists p2. exists q1. easy.
          - constructor; try easy. right. exists l1. exists q1. easy.
    }
    destruct H0 as (ys3,(Ha,Hb)). exists (p_recv pt ys3).
    split. constructor; try easy. constructor; try easy. 
  - inversion H1. subst. inversion H. subst.
    specialize(IHg1_1 g Q1 m n k p0 p3 H12 H0 H6). destruct IHg1_1 as (q1,(Ha,Hb)).
    specialize(IHg1_2 g Q2 m n k p0 q2 H13 H0 H7). destruct IHg1_2 as (q3,(Hc,Hd)).
    exists (p_ite e2 q1 q3). split. constructor; try easy. constructor; try easy.
  - inversion H1. subst. inversion H. subst.
    specialize(IHg1 g Q' (S m) (S n) k p0 p3 H8 H0 H3).
    destruct IHg1 as (q1,(Ha,Hb)). exists (p_rec q1).
    split. constructor; try easy.
    constructor; try easy.
Qed.

Lemma guardP_peq_w : forall p1 p2, 
      peq_w p1 p2 -> 
      (forall n : fin, exists m : fin, guardP n m p1) -> 
      (forall n : fin, exists m : fin, guardP n m p2).
Proof.
  intros.
  specialize(H0 n). destruct H0 as (m, H0). exists m.
  revert H0 H. revert p1 p2 m.
  induction n; intros; try easy.
  - constructor.
  - revert IHn H H0. revert n p1 p2.
    induction m; intros; try easy.
    inversion H0.
    - subst. inversion H. subst. constructor.
    - subst. inversion H. subst. constructor. apply IHn with (p1 := g); try easy.
    - subst. inversion H. subst.
      constructor. revert H5 H2 IHn. clear H0 H. revert ys. induction lis; intros; try easy.
      - destruct ys; try easy.
      - destruct ys; try easy. inversion H2. subst. clear H2. inversion H5. subst. clear H5.
        specialize(IHlis ys H7 H3 IHn). constructor; try easy.
        clear IHlis H3 H7.
        destruct H4. left. easy.
        destruct H as (p1,(p2,(Ha,(Hb,Hc)))). subst.
        destruct H1; try easy. destruct H as (g1,(Hd,He)). inversion Hd. subst.
        right. exists p2. split. easy. apply IHn with (p1 := g1); try easy.
    assert(forall (p1 p2 : process),
      peq_w p1 p2 -> guardP (S n) m p1 -> guardP (S n) m p2).
    {
      intros. specialize(IHm n p0 p3). apply IHm; try easy.
    }
    inversion H0. subst.
    - inversion H. constructor.
    - subst. inversion H. subst. constructor. apply IHn with (p1 := g); try easy.
    - subst. inversion H. subst. constructor.
      revert H6 H3. clear H0 H. revert ys.
      induction lis; intros.
      - destruct ys; try easy.
      - destruct ys; try easy. inversion H6. subst. clear H6. inversion H3. subst. clear H3.
        specialize(IHlis ys H7 H5). constructor; try easy.
        destruct H4. left. easy.
        destruct H as (p1,(p2,(Ha,(Hb,Hc)))). subst.
        destruct H2; try easy. destruct H as (g1,(Hd,He)). inversion Hd. subst.
        right. exists p2. split. easy.
        apply IHn with (p1 := g1); try easy.
    - subst. inversion H. subst.
      constructor. apply H1 with (p1 := P); try easy. apply H1 with (p1 := Q); try easy.
    - subst. inversion H. subst.
      assert(exists Q', substitutionP 0 0 0 (p_rec p0) p0 Q' /\ peq_w Q Q').
      {
        apply peq_after_subst with (g1 := g) (g := p_rec g); try easy.
      }
      destruct H2 as (Q1,(Ha,Hb)).
      apply gp_rec with (Q := Q1); try easy.
      apply H1 with (p1 := Q); try easy.
Qed.

Lemma guardP_subst_expr : forall y v j k,
    (forall n : fin, exists m : fin, guardP n m y) -> 
    (forall n : fin, exists m : fin, guardP n m (subst_expr_proc y v j k)).
Proof.
  intros.
  apply guardP_peq_w with (p1 := y); try easy.
  clear H n. revert v j k.
  induction y using process_ind_ref; intros; try easy.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. constructor. apply IHy; try easy.
  - simpl. constructor.
    revert H. revert pt v j k. induction llp; intros; try easy.
    - inversion H. subst. clear H. specialize(IHllp pt v j k H3). constructor; try easy.
      clear H3 IHllp.
      destruct a.
      - right. exists p. exists (subst_expr_proc p v (S j) (S k)). split. easy. split. easy.
        apply H2; try easy.
      - left. easy.
  - simpl. constructor.
    apply IHy1. apply IHy2.
  - simpl. constructor. apply IHy.
Qed.

Theorem _3_21 : forall M M' G, typ_sess M G -> betaP M M' -> exists G', typ_sess M' G' /\ multiC G G'.
Proof.
  intros. revert H. revert G.
  induction H0; intros; try easy.
  (* R-COMM *)
  inversion H1. subst.
  - inversion H5. subst. clear H5. inversion H8. subst. clear H8. 
    inversion H7. subst. clear H7. inversion H10. subst. clear H10. clear H1.
    destruct H6. destruct H1. destruct H7. destruct H6. rename x into T. rename x0 into T'.
    destruct H7 as (H7, Ht). destruct H5 as (H5, Htt).
    - specialize(_a23_a q xs (p_recv q xs) nil nil T H5 (erefl (p_recv q xs))); intros. 
      destruct H8. destruct H8. destruct H10. destruct H11.
    - specialize(_a23_bf p l e Q (p_send p l e Q) nil nil T' H7 (erefl (p_send p l e Q))); intros.
      destruct H13. destruct H13. destruct H13. destruct H14. rename x0 into S. rename x1 into LT.
    
    specialize(_3_19_h q p l); intros.
    specialize(subtype_recv T q x H10); intros. destruct H17. subst.
    specialize(subtype_send T' p (extendLis l (Some (S, LT))) H15); intros. destruct H17. subst.
    rename x0 into LQ. rename x1 into LP.
    specialize(H16 G LP LQ S LT).
    specialize(_3_21_helper l xs x y H H11); intros. destruct H17. destruct H17. destruct H17.
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
      - specialize(_3_21_helper_3 M G pt); intros. apply H21; try easy.
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
    
    specialize(_a_29_s G q p LP LQ SL TL SL' TL' l H2 H6 H22 H1 H23); intros.
    destruct H24 as (Gl,(ctxG,(SI,(Sn,(Ha,(Hb,(Hc,(Hd,(He,(Hf,Hg)))))))))).
    specialize(_3_21_helper_1 H23 H17 H10); intros.
    specialize(_3_21_helper_2 H15 H22); intros. 
    constructor. constructor.
    - constructor.
      specialize(_3_19_2_helper q p l G G' LP LQ SL TL SL' TL'); intros.
      assert(projectionC G' p TL'). apply H26; try easy. clear H26. 
      exists TL'. split; try easy.
      split.
      apply _a24 with (S := x0); try easy.
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
      specialize(_3_19_1_helper q p l G G' LP LQ SL TL SL' TL'); intros.
      assert(projectionC G' q TL). apply H26; try easy. clear H26.
      exists TL. split; try easy. split.
      - apply tc_sub with (t := LT); try easy.
        specialize(typable_implies_wfC H7); intros.
        specialize(wfC_send H26 H22); try easy.
      - intros. specialize(Ht (Nat.succ n)). destruct Ht. inversion H26.
        subst. exists x2. easy.
    - specialize(_3_19_3_helper_s M q p G G' l LP LQ S LT x (x0, x1)); intros.
      inversion H4. subst. inversion H30. subst.
      specialize(Classical_Prop.not_or_and (q = p) (In p (flattenT M)) H29); intros. destruct H27.
      apply H26; try easy.

  (* T-COND *)
  inversion H0. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
  destruct H5. destruct H4. destruct H5 as (H5, Ha).
  specialize(_a23_c (p_ite e P Q) e P Q x nil nil H5 (erefl (p_ite e P Q))); intros.
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
  specialize(_a23_c (p_ite e P Q) e P Q x nil nil H5 (erefl (p_ite e P Q))); intros.
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
    - specialize(_a23_a q xs (p_recv q xs) nil nil T Hb (erefl (p_recv q xs))); intros. 
      destruct H5 as (STT,(Hg,(Hh,(Hi,Hj)))).
    - specialize(_a23_bf p l e Q (p_send p l e Q) nil nil T1 He (erefl (p_send p l e Q))); intros.
      destruct H5 as (S,(T',(Hk,(Hl,Hm)))).
    
    specialize(_3_19_h q p l); intros.
    specialize(subtype_recv T q STT Hh); intros. destruct H6. subst.
    specialize(subtype_send T1 p (extendLis l (Some (S, T'))) Hm); intros. destruct H6. subst.
    rename x into LQ. rename x0 into LP.
    specialize(H5 G LP LQ S T').
    specialize(_3_21_helper l xs STT y H Hi); intros. destruct H6. destruct H6. destruct H6.
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
    
    specialize(_a_29_s G q p LP LQ SL TL SL' TL' l H2 Hd H22 Ha H23); intros.
    destruct H13 as (Gl,(ctxG,(SI,(Sn,(Hta,(Htb,(Htc,(Htd,(Hte,(Htf,Htg)))))))))).
    specialize(_3_21_helper_1 H23 H6 Hh); intros.
    specialize(_3_21_helper_2 Hm H22); intros. 
    constructor. constructor.
    - specialize(_3_19_2_helper q p l G G' LP LQ SL TL SL' TL'); intros.
      assert(projectionC G' p TL'). apply H15; try easy. clear H15. 
      exists TL'. split; try easy.
      split.
      apply _a24 with (S := x); try easy.
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
      specialize(_3_19_1_helper q p l G G' LP LQ SL TL SL' TL'); intros.
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
  specialize(_a23_c (p_ite e P Q) e P Q x nil nil H5 (erefl (p_ite e P Q))); intros.
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
  specialize(_a23_c (p_ite e P Q) e P Q x nil nil H5 (erefl (p_ite e P Q))); intros.
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
  specialize(_a22_2 M1 M1' G H2 H); intros.
  specialize(IHbetaP G H3); intros. destruct IHbetaP. exists x. 
  destruct H4. split; try easy.
  specialize(_a22_2 M2' M2 x H4 H0); intros. easy.
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
      specialize(_a23_bf pt l e g (p_send pt l e g) nil nil ltt_end Hb (erefl (p_send pt l e g))); intros.
      destruct H1 as (S1,(T1,(Hd,(He,Hf)))). pinversion Hf.
      apply sub_mon.
      subst.
      specialize(_a23_a p0 lis (p_recv p0 lis) nil nil ltt_end Hb (erefl (p_recv p0 lis))); intros.
      destruct H1 as (STT,(Hd,(He,(Hf,Hg)))). pinversion He. apply sub_mon.
    apply proj_mon.
    pinversion Ha. subst.
    inversion Hc; try easy.
    - subst. exists (s <-- p_inact). split. apply pc_refl. constructor. left. easy.
    - subst.
      specialize(_a23_bf pt l e g (p_send pt l e g) nil nil ltt_end Hb (erefl (p_send pt l e g))); intros. destruct H1 as (S1,(T1,(Hd,(He,Hf)))). pinversion Hf. apply sub_mon.
    - subst.
      specialize(_a23_a p0 lis (p_recv p0 lis) nil nil ltt_end Hb (erefl (p_recv p0 lis))); intros.
      destruct H1 as (STT,(Hd,(He,(Hf,Hg)))). pinversion He. apply sub_mon.
    - subst.
      specialize(_a23_c (p_ite e P Q) e P Q ltt_end nil nil Hb (erefl (p_ite e P Q))); intros.
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
        - specialize(_a23_d (p_rec g) g ltt_end nil nil Hb (erefl (p_rec g))); intros.
          destruct H1 as (T1,(Hd,He)). pinversion He. subst.
          specialize(_a21f g (p_rec g) ltt_end ltt_end nil nil Q); intros.
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

Lemma expr_eval_n : forall e, typ_expr nil e snat -> (exists k, stepE e (e_val (vnat k))).
Proof.
  induction e; intros; try easy.
  - specialize(inv_expr_var (e_var n) n nil snat H (erefl (e_var n))); intros.
    destruct H0 as (S',(Ha,Hb)). destruct n; try easy.
  - specialize(inv_expr_vali nil (e_val v) snat v H (erefl (e_val v))); intros.
    destruct H0.
    - destruct H0 as (k,(Ha,Hb)). subst. easy.
    - destruct H0. destruct H0 as (k,(Ha,Hb)). subst. exists k. constructor.
    - destruct H0 as (k,(Ha,Hb)). subst. easy.
  - specialize(inv_expr_succ nil (e_succ e) snat e H (erefl (e_succ e))); intros.
    destruct H0 as (H0,H1). destruct H1. specialize(IHe H0). destruct IHe as (k,Ha). exists (k+1). constructor. easy. easy.
  - specialize(inv_expr_neg nil (e_neg e) snat e H (erefl (e_neg e))); intros.
    easy.
  - specialize(inv_expr_not nil (e_not e) snat e H (erefl (e_not e))); intros.
    destruct H0. easy.
  - specialize(inv_expr_gt nil (e_gt e1 e2) snat e1 e2 H (erefl (e_gt e1 e2))); intros.
    destruct H0 as (Ha,(Hb,Hc)). easy.
  - specialize(inv_expr_plus nil (e_plus e1 e2) snat e1 e2 H (erefl (e_plus e1 e2))); intros.
    easy.
  - specialize(inv_expr_det nil (e_det e1 e2) snat e1 e2 H (erefl (e_det e1 e2))); intros.
    destruct H0 as (k,(Ha,(Hb,Hc))). inversion Hc. subst.
    specialize(IHe1 Ha). destruct IHe1. exists x. constructor. easy.
Qed.

Lemma expr_eval_i : forall e, typ_expr nil e sint -> (exists k, stepE e (e_val (vint k))) \/ (exists k, stepE e (e_val (vnat k))).
Proof.
  induction e; intros; try easy.
  - specialize(inv_expr_var (e_var n) n nil sint H (erefl (e_var n))); intros.
    destruct H0 as (S',(Ha,Hb)). destruct n; try easy.
  - specialize(inv_expr_vali nil (e_val v) sint v H (erefl (e_val v))); intros.
    destruct H0.
    - destruct H0 as (k,(Ha,Hb)). subst. left. exists k. constructor.
    - destruct H0. destruct H0 as (k,(Ha,Hb)). subst. right. exists k. constructor.
    - destruct H0 as (k,(Ha,Hb)). subst. easy.
  - specialize(inv_expr_succ nil (e_succ e) sint e H (erefl (e_succ e))); intros.
    destruct H0 as (H0,H1). destruct H1. right. easy.
    specialize(expr_eval_n e H0); intros. destruct H2 as (k,H2). 
    right. exists (k+1). constructor. easy.
  - specialize(inv_expr_neg nil (e_neg e) sint e H (erefl (e_neg e))); intros.
    destruct H0. specialize(IHe H1).
    destruct IHe.
    - destruct H2 as (k,Ha). left. exists (Z.opp k). constructor. easy.
    - destruct H2 as (k,Ha). left. exists (Z.opp (Z.of_nat k)). apply ec_neg2. easy.
  - specialize(inv_expr_not nil (e_not e) sint e H (erefl (e_not e))); intros.
    destruct H0. easy.
  - specialize(inv_expr_gt nil (e_gt e1 e2) sint e1 e2 H (erefl (e_gt e1 e2))); intros.
    destruct H0 as (Ha,(Hb,Hc)). easy.
  - specialize(inv_expr_plus nil (e_plus e1 e2) sint e1 e2 H (erefl (e_plus e1 e2))); intros.
    destruct H0 as (Ha,(Hb,Hc)). specialize(IHe1 Hb). specialize(IHe2 Hc).
    left.
    - destruct IHe1.
      destruct H0 as (k,H0).
      destruct IHe2.
      - destruct H1 as (k1,H1). exists (Z.add k k1). constructor; try easy.
      - destruct H1 as (k1,H1). exists (Z.add k (Z.of_nat k1)). constructor; try easy.
    - destruct H0 as (k,H0).
      destruct IHe2.
      - destruct H1 as (k1,H1). exists (Z.add (Z.of_nat k) k1). constructor; try easy.
      - destruct H1 as (k1,H1). exists (Z.add (Z.of_nat k) (Z.of_nat k1)). constructor; try easy.
  - specialize(inv_expr_det nil (e_det e1 e2) sint e1 e2 H (erefl (e_det e1 e2))); intros.
    destruct H0 as (k,(Ha,(Hb,Hc))). inversion Hc. subst.
    - specialize(expr_eval_n e1 Ha); intros. destruct H0 as (k,Hd). right. exists k. constructor. easy.
    - subst.
      specialize(IHe1 Ha). destruct IHe1.
      destruct H0. left. exists x. constructor. easy.
      destruct H0. right. exists x. constructor. easy.
Qed.

Lemma expr_eval_b : forall e, typ_expr nil e sbool -> (stepE e (e_val (vbool true)) \/ stepE e (e_val (vbool false))).
Proof.
  induction e; intros; try easy.
  - specialize(inv_expr_var (e_var n) n nil sbool H (erefl (e_var n))); intros.
    destruct H0 as (S',(Ha,Hb)). destruct n; try easy.
  - specialize(inv_expr_vali nil (e_val v) sbool v H (erefl (e_val v))); intros.
    destruct H0.
    - destruct H0 as (k,(Ha,Hb)). easy.
    - destruct H0. destruct H0 as (k,(Ha,Hb)). subst. inversion Ha.
    - destruct H0 as (k,(Ha,Hb)). subst. destruct k. left. apply ec_refl. right. apply ec_refl. 
  - specialize(inv_expr_succ nil (e_succ e) sbool e H (erefl (e_succ e))); intros.
    destruct H0 as (H0,H1). destruct H1. right. easy. easy.
  - specialize(inv_expr_neg nil (e_neg e) sbool e H (erefl (e_neg e))); intros.
    easy.
  - specialize(inv_expr_not nil (e_not e) sbool e H (erefl (e_not e))); intros.
    destruct H0.
    specialize(IHe H1).
    destruct IHe. right. constructor; try easy.
    left. constructor; try easy.
  - specialize(inv_expr_gt nil (e_gt e1 e2) sbool e1 e2 H (erefl (e_gt e1 e2))); intros.
    destruct H0 as (Ha,(Hb,Hc)).
    specialize(expr_eval_i e1 Hb); intros. 
    specialize(expr_eval_i e2 Hc); intros.
    clear Ha H IHe1 IHe2.
    destruct H0.
    - destruct H as (k,H).
      destruct H1.
      - destruct H0 as (k1,H0). 
        specialize(Zle_or_lt k k1); intros. destruct H1. 
        right. apply ec_gt_f3 with (m := k) (n := k1); try easy.
        left. apply ec_gt_t3 with (m := k) (n := k1); try easy.
      - destruct H0 as (k1,H0).
        specialize(Zle_or_lt k (Z.of_nat k1)); intros. destruct H1. 
        right. apply ec_gt_f2 with (m := k) (n := k1); try easy.
        left. apply ec_gt_t2 with (m := k) (n := k1); try easy.
    - destruct H as (k,H).
      destruct H1.
      - destruct H0 as (k1,H0).
        specialize(Zle_or_lt (Z.of_nat k) k1); intros. destruct H1. 
        right. apply ec_gt_f1 with (m := k) (n := k1); try easy.
        left. apply ec_gt_t1 with (m := k) (n := k1); try easy.
      - destruct H0 as (k1,H0).
        specialize(Zle_or_lt (Z.of_nat k) (Z.of_nat k1)); intros. destruct H1. 
        right. apply ec_gt_f0 with (m := k) (n := k1); try easy.
        left. apply ec_gt_t0 with (m := k) (n := k1); try easy.
  - specialize(inv_expr_plus nil (e_plus e1 e2) sbool e1 e2 H (erefl (e_plus e1 e2))); intros.
    easy.
  - specialize(inv_expr_det nil (e_det e1 e2) sbool e1 e2 H (erefl (e_det e1 e2))); intros.
    destruct H0 as (k,(Ha,(Hb,Hc))). inversion Hc. subst.
    specialize(IHe1 Ha). destruct IHe1. left. constructor. easy. right. constructor. easy.
Qed.

Lemma expr_eval_ss : forall ex S, typ_expr nil ex S -> exists v, stepE ex (e_val v).
Proof.
  intros.
  destruct S. 
  - specialize(expr_eval_b ex H); intros. destruct H0. exists (vbool true). easy. exists (vbool false). easy.
  - specialize(expr_eval_i ex H); intros. destruct H0. destruct H0. exists (vint x). easy. destruct H0. exists (vnat x). easy.
  - specialize(expr_eval_n ex H); intros. destruct H0. exists (vnat x). easy.
Qed.

Inductive betaPr : relation process := 
  | betaPr_sin : forall P Q, substitutionP 0 0 0 (p_rec P) P Q -> betaPr (p_rec P) Q.

Lemma guardP_break : forall P,
    (forall n : fin, exists m : fin, guardP n m P) -> 
    exists Q, multi betaPr P Q /\ (Q = p_inact \/ (exists e p1 p2, Q = p_ite e p1 p2) \/ (exists pt lb ex pr, Q = p_send pt lb ex pr) \/ (exists pt llp, Q = p_recv pt llp)).
Proof.
  intros.
  specialize(H 1). destruct H as (m, H).
  revert H. revert P.
  induction m; intros.
  - inversion H.
    - subst. exists p_inact. split. constructor. left. easy.
    - subst. exists (p_send pt l e g). split. constructor. right. right. left. exists pt. exists l. exists e. exists g. easy.
    - subst. exists (p_recv p lis). split. constructor. right. right. right. exists p. exists lis. easy.
  - inversion H. 
    - subst. exists p_inact. split. constructor. left. easy.
    - subst. exists (p_send pt l e g). split. constructor. right. right. left. exists pt. exists l. exists e. exists g. easy.
    - subst. exists (p_recv p lis). split. constructor. right. right. right. exists p. exists lis. easy.
    - subst. exists (p_ite e P0 Q). split. constructor.
      right. left. exists e. exists P0. exists Q. easy.
    - subst. specialize(IHm Q H3).
      destruct IHm as (Q1,(Ha,Hb)). exists Q1. split; try easy.
      apply multi_step with (y := Q); try easy. 
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
    specialize(_a23_d (p_rec P) P T Gs Gt H1 (erefl (p_rec P))); intros.
    destruct H2 as (T0,(Ha,Hb)).
    specialize(_a21f P (p_rec P) T0 T0 Gs Gt y); intros.
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

Theorem _3_23 : forall M G, typ_sess M G -> (exists M', unfoldP M M' /\ (ForallT (fun _ P => P = p_inact) M')) \/ exists M', betaP M M'.
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
          specialize(_a23_c (p_ite e p1 p2) e p1 p2 ltt_end nil nil Hb (erefl (p_ite e p1 p2))); intros.
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
          specialize(_a23_c (p_ite e p1 p2) e p1 p2 ltt_end nil nil Hb (erefl (p_ite e p1 p2))); intros.
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
      specialize(_a22_2 M (((p <-- P) ||| (q <-- Q)) ||| M') (gtt_send p q l)); intros.
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
            - subst. specialize(_a23_f p_inact (ltt_send q ys) nil nil H2 (erefl (p_inact))); intros. 
              easy.
            - destruct H. destruct H as (e,(p1,(p2,Ha))). subst.
              specialize(_a23_c (p_ite e p1 p2) e p1 p2 (ltt_send q ys) nil nil H2 (erefl (p_ite e p1 p2))); intros.
              destruct H as (T1,(T2,(Ha,(Hb,(Hc,(Hd,He)))))).
              specialize(expr_eval_b e He); intros. 
              destruct H.
              - exists ((p <-- p1) ||| ((q <-- Q2) ||| M')).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2) ||| M'))) (M2' := ((p <-- p1) ||| ((q <-- Q2) ||| M'))); try easy. constructor. constructor. constructor. easy.
              - exists ((p <-- p2) ||| ((q <-- Q2) ||| M')).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2) ||| M'))) (M2' := ((p <-- p2) ||| ((q <-- Q2) ||| M'))); try easy. constructor. constructor. constructor. easy.
            - destruct H.
              destruct H as (pt,(lb,(ex,(pr,Ha)))). subst.
              specialize(_a23_bf pt lb ex pr (p_send pt lb ex pr) nil nil (ltt_send q ys) H2 (erefl ((p_send pt lb ex pr)))); intros. destruct H as (S,(T1,(Ht,Hb))). clear H2. rename T1 into Tl. rename Hb into Hta. clear M P Q.
              destruct Hl.
              - subst. specialize(_a23_f p_inact (ltt_recv p ys0) nil nil H3 (erefl (p_inact))); intros. 
                easy.
              - destruct H. destruct H as (e,(p1,(p2,Ha))). subst. 
                specialize(_a23_c (p_ite e p1 p2) e p1 p2 (ltt_recv p ys0) nil nil H3 (erefl (p_ite e p1 p2))); intros.
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
                specialize(_a23_bf pt1 lb1 ex1 pr1 (p_send pt1 lb1 ex1 pr1) nil nil (ltt_recv p ys0) H3 (erefl (p_send pt1 lb1 ex1 pr1))); intros.
                destruct H as (S1,(T1,(Ha,(Hb,Hc)))). pinversion Hc. apply sub_mon.
              - destruct H as (pt2,(llp,Ha)). subst.
                specialize(expr_eval_ss ex S Ht); intros. destruct H as (v, Ha).
                destruct Hta as (Hta,Htb).
                pinversion Htb. subst.
                specialize(_a23_a pt2 llp (p_recv pt2 llp) nil nil (ltt_recv p ys0) H3 (erefl (p_recv pt2 llp))); intros.
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
              specialize(_a23_a pt llp (p_recv pt llp) nil nil (ltt_send q ys) H2 (erefl (p_recv pt llp))); intros.
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
      specialize(_a22_2 M (((p <-- P) ||| (q <-- Q))) (gtt_send p q l)); intros.
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
            - subst. specialize(_a23_f p_inact (ltt_send q ys) nil nil H2 (erefl (p_inact))); intros. 
              easy.
            - destruct H. destruct H as (e,(p1,(p2,Ha))). subst.
              specialize(_a23_c (p_ite e p1 p2) e p1 p2 (ltt_send q ys) nil nil H2 (erefl (p_ite e p1 p2))); intros.
              destruct H as (T1,(T2,(Ha,(Hb,(Hc,(Hd,He)))))).
              specialize(expr_eval_b e He); intros. 
              destruct H.
              - exists ((p <-- p1) ||| ((q <-- Q2))).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2)))) (M2' := ((p <-- p1) ||| ((q <-- Q2)))); try easy. constructor. constructor. constructor. easy.
              - exists ((p <-- p2) ||| ((q <-- Q2))).
                apply r_struct with (M1' := ((p <-- p_ite e p1 p2) ||| ((q <-- Q2)))) (M2' := ((p <-- p2) ||| ((q <-- Q2)))); try easy. constructor. constructor. constructor. easy.
            - destruct H.
              destruct H as (pt,(lb,(ex,(pr,Ha)))). subst.
              specialize(_a23_bf pt lb ex pr (p_send pt lb ex pr) nil nil (ltt_send q ys) H2 (erefl ((p_send pt lb ex pr)))); intros. destruct H as (S,(T1,(Ht,Hb))). clear H2. rename T1 into Tl. rename Hb into Hta. clear M P Q.
              destruct Hl.
              - subst. specialize(_a23_f p_inact (ltt_recv p ys0) nil nil H3 (erefl (p_inact))); intros. 
                easy.
              - destruct H. destruct H as (e,(p1,(p2,Ha))). subst. 
                specialize(_a23_c (p_ite e p1 p2) e p1 p2 (ltt_recv p ys0) nil nil H3 (erefl (p_ite e p1 p2))); intros.
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
                specialize(_a23_bf pt1 lb1 ex1 pr1 (p_send pt1 lb1 ex1 pr1) nil nil (ltt_recv p ys0) H3 (erefl (p_send pt1 lb1 ex1 pr1))); intros.
                destruct H as (S1,(T1,(Ha,(Hb,Hc)))). pinversion Hc. apply sub_mon.
              - destruct H as (pt2,(llp,Ha)). subst.
                specialize(expr_eval_ss ex S Ht); intros. destruct H as (v, Ha).
                destruct Hta as (Hta,Htb).
                pinversion Htb. subst.
                specialize(_a23_a pt2 llp (p_recv pt2 llp) nil nil (ltt_recv p ys0) H3 (erefl (p_recv pt2 llp))); intros.
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
              specialize(_a23_a pt llp (p_recv pt llp) nil nil (ltt_send q ys) H2 (erefl (p_recv pt llp))); intros.
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

Theorem _3_24 : forall M G, typ_sess M G -> stuckM M -> False.
Proof.
  intros. 
  unfold stuckM in H0. destruct H0 as (M',(Ha,Hb)).
  revert Hb H. revert G.
  induction Ha; intros.
  - destruct Hb.
    specialize(_3_23 x G H); intros. destruct H2. apply H0. easy. apply H1. easy.
  - specialize(_3_21 x y G H0 H); intros.
    destruct H1 as (G',(Hc,Hd)).
    apply IHHa with (G := G'); try easy.
Qed.















