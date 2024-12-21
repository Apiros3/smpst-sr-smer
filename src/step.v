From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh.

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