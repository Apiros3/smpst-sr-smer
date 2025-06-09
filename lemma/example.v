From mathcomp Require Import ssreflect.seq all_ssreflect.
Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes Coq.Logic.Classical_Prop.
Import ListNotations. 
Open Scope list_scope.
From Paco Require Import paco.
Import ListNotations. 
From SST Require Import src.header src.sim src.expr src.process src.local src.global src.balanced src.typecheck src.part src.gttreeh src.step src.merge src.projection src.session.  
From SST Require Import lemma.inversion lemma.inversion_expr lemma.substitution_helper lemma.substitution lemma.decidable_helper lemma.decidable lemma.expr lemma.part lemma.step
lemma.projection_helper lemma.projection lemma.main_helper lemma.main.

Definition G := gtt_send "Alice" "Bob" [
  Some (snat, gtt_send "Bob" "Carol" [Some(snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])] );
  Some (snat, gtt_send "Bob" "Carol" [Some(snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])] )
  ].

Definition TAlice := ltt_send "Bob" [Some (snat, ltt_recv "Carol" [Some (snat, ltt_end)])].

Definition T'Alice := ltt_send "Bob" [
  Some (snat, ltt_recv "Carol" [Some (snat, ltt_end)]);
  Some (snat, ltt_recv "Carol" [Some (snat, ltt_end)])
  ].

Definition TCarol := ltt_recv "Bob" [Some (snat, ltt_send "Alice" [Some (snat, ltt_end)])].

Definition TBob := ltt_recv "Alice" [
  Some(snat, ltt_send "Carol" [Some(snat, ltt_end)]);
  Some(snat, ltt_send "Carol" [Some(snat, ltt_end)])
  ].

Lemma no_part_end: forall p,
  isgPartsC p (gtt_end) -> False.
Proof. intros.
       specialize(part_break_s gtt_end p H); intro HH.
       destruct HH as (g, (Ha,(Hb,[Hc | (r,(s,(xs,Hxs)))]))).
       subst. inversion Hb.
       subst.
       pinversion Ha.
       apply gttT_mon.
Qed. 

Lemma no_part_send: forall p q r,
  p <> r ->
  q <> r ->
  isgPartsC r (gtt_send p q [Some (snat, gtt_end)]) -> False.
Proof. intros.
       apply part_cont in H1; try easy.
       destruct H1 as (n,(s,(g,(Hg1,Hg2)))).
       destruct n. simpl in Hg1.
       inversion Hg1. subst.
       apply no_part_end in Hg2. easy.
       simpl in Hg1.
       destruct n. simpl in Hg1. easy. simpl in Hg1. easy.
Qed.

Lemma no_part_send_send: forall pt p q r s,
  pt <> p ->
  pt <> q ->
  pt <> r ->
  pt <> s ->
  isgPartsC pt (gtt_send p q [Some (snat, gtt_send r s [Some (snat, gtt_end)])]) -> False.
Proof. intros.
       apply part_cont in H3; try easy.
       destruct H3 as (n1,(s1,(g1,(Hg1,Hg2)))).
       destruct n1. simpl in Hg1.
       inversion Hg1. subst.
       apply no_part_send in Hg2; try easy.
       simpl in Hg1.
       destruct n1. simpl in Hg1. easy. simpl in Hg1. easy.
Qed.


Lemma GPAlice: projectionC G "Alice" T'Alice.
Proof. unfold G, T'Alice.
       pfold.
       constructor. easy.

       unfold isgPartsC.
       exists(
       (g_send "Alice" "Bob"
       [Some (snat, g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]);
        Some (snat, g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])])])
       ).
       split.
       pfold.
       constructor.
       constructor. right.
       exists snat. exists(g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       exists(gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left.
       pfold. constructor.
       constructor.
       right. exists snat. exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       exists(gtt_send "Carol" "Alice" [Some (snat, gtt_end)]). split. easy.
       split. easy.
       left.
       pfold. constructor.
       constructor. right.
       exists snat. exists g_end. exists gtt_end. split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       constructor.
       right. 
       exists snat. exists(g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       exists(gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left.
       pfold. constructor.
       constructor.
       right. exists snat. exists (g_send "Carol" "Alice" [Some (snat, g_end)]).
       exists (gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat. exists g_end. exists gtt_end. split. easy. split. easy.
       left.
       pfold. constructor.
       constructor.
       constructor.
       constructor.
       split.
       intro n.
       induction n; intros.
       exists 0.
       constructor.
       destruct IHn as (m, IHn).
       exists m.
       constructor.
       constructor.
       right.
       exists snat. exists (g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       split. easy.
       case_eq n; intros.
       constructor.
       constructor. constructor.
       right.
       exists snat. exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. easy.
       case_eq n0; intros.
       constructor.
       constructor. constructor.
       right. exists snat. exists g_end.
       split. easy. constructor. constructor. constructor.
       constructor.
       right.
       exists snat. exists (g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       split. easy.
       case_eq n; intros.
       constructor.
       constructor. constructor.
       right.
       exists snat. exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. easy.
       case_eq n0; intros.
       constructor.
       constructor. constructor.
       right. exists snat. exists g_end.
       split. easy. constructor. constructor. constructor.
       constructor.
       constructor.
       
       constructor.
       right.
       
       exists snat. 
       exists(gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
       exists( ltt_recv "Carol" [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold.
       apply proj_cont with (ys := [Some (ltt_recv "Carol" [Some (snat, ltt_end)])]).
       easy. easy. easy.
       unfold isgPartsC. 
       exists(g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       split. pfold. constructor. constructor.
       right. exists snat. exists( g_send "Carol" "Alice" [Some (snat, g_end)]).
       exists(gtt_send "Carol" "Alice" [Some (snat, gtt_end)]). split. easy. split. easy.
       left. pfold. constructor. constructor. right.
       exists snat. exists g_end. exists gtt_end. split. easy. split. easy.
       left. pfold. constructor.
       constructor. constructor.
       split.
       intro n.
       case_eq n; intros.
       exists 0. constructor.
       exists 0. constructor. 
       constructor.
       right. exists snat. exists( g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. easy.
       case_eq n0; intros.
       constructor.
       constructor.
       constructor.
       right. exists snat. exists g_end. split. easy. constructor.
       constructor. constructor.
       apply pa_sendr with (n := 0) (s := snat) (g := g_send "Carol" "Alice" [Some (snat, g_end)]). easy. easy.
       simpl. easy.
       constructor.
       
       constructor.
       right. exists snat. exists (gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       exists((ltt_recv "Carol" [Some (snat, ltt_end)])). split. easy.
       split. easy.
       left. pfold. constructor. easy.
       
       unfold isgPartsC.
       exists((g_send "Carol" "Alice" [Some (snat, g_end)])).
       split. pfold. constructor.
       constructor.
       right. exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy. left. pfold. constructor. constructor.
       split.
       intro n.
       exists 0.
       destruct n; constructor.
       constructor. right. exists snat. exists g_end. split. easy. constructor.
       constructor.
       constructor.

       constructor.
       right.
       exists snat. exists gtt_end. exists ltt_end. split. easy. split. easy.
       left. pfold. constructor.
       apply no_part_end.
       constructor.
       constructor. constructor.
      
       constructor.
       right.
       exists snat. exists(gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
       exists(ltt_recv "Carol" [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold.
       apply proj_cont with (ys := [Some (ltt_recv "Carol" [Some (snat, ltt_end)])]).
       easy. easy. easy.
       unfold isgPartsC.
       
       exists((g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])])).
       split. pfold. constructor.
       constructor. right.
       exists snat. exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       exists(gtt_send "Carol" "Alice" [Some (snat, gtt_end)]). split. easy. split. easy.
       left.  pfold. constructor. constructor.
       right. exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy. left. pfold. constructor. constructor. constructor.
       split.
       intro n.
       exists 0.
       case_eq n; constructor.
       constructor. right.
       exists snat. exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. easy. 
       case_eq n0; constructor. constructor.
       right. exists snat. exists g_end. split. easy. constructor. constructor. constructor.
       apply pa_sendr with (n := 0) (s := snat) (g := g_send "Carol" "Alice" [Some (snat, g_end)]). easy. easy.
       simpl. easy. constructor.

       constructor.
       right. exists snat.
       exists(gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       exists (ltt_recv "Carol" [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       easy.
       
       unfold isgPartsC.
       exists( (g_send "Carol" "Alice" [Some (snat, g_end)])).
       split. pfold. constructor.
       constructor. right.
       exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       split.
       intro n.
       exists 0.
       case_eq n; constructor.
       constructor. right.
       exists snat. exists g_end. split. constructor.
       constructor. constructor.
       constructor.

       constructor. right.
       exists snat. exists gtt_end. exists ltt_end.
       split. easy. split. easy. left. pfold. constructor.
       apply no_part_end.
       constructor.
       constructor.
       constructor.
       constructor.
Qed.

Lemma GPBob: projectionC G "Bob" TBob.
Proof. unfold G, TBob.
       pfold. constructor.
       easy.
       (**)
       unfold isgPartsC.
       exists((g_send "Alice" "Bob"
         [Some (snat, g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]);
          Some (snat, g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])])])).
       split.
       pfold. constructor.
       constructor. right.
       exists snat.
       exists(g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       exists(gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       exists( gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       constructor.
       right.
       exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       constructor.
       right.
       exists snat.
       exists( g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       exists(gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left. pfold. 
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       exists( gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       constructor.
       right.
       exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       constructor.
       
       split.
       intro n.
       exists 0.
       destruct n; constructor.
       constructor.
       right.
       exists snat.
       exists( g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       split. easy.
       destruct n; constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor.
       right.
       exists snat.
       exists(g_end). split. easy. constructor.
       constructor. constructor. 
       constructor.
       right.
       exists snat.
       exists( g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       split. easy.
       destruct n; constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor.
       right.
       exists snat.
       exists(g_end). split. easy. constructor.
       constructor. constructor. 
       constructor.
       constructor.
       (**)
       constructor.
       right.
       exists snat.
       exists(gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
       exists(ltt_send "Carol" [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       easy.
       
       unfold isgPartsC.
       exists((g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]) ).
       split.
       pfold. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       exists(gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat.
       exists g_end.
       exists gtt_end.
       split. easy. split. easy. left. pfold. constructor.
       constructor. constructor.
       split.
       intro n.
       exists 0.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists(g_end).
       split. easy. constructor.
       constructor. constructor.
       constructor.
       (**)

       constructor.
       right.
       exists snat.
       exists (gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       exists ltt_end.
       split. easy. split. easy.
       left. pfold.
       constructor.
       apply no_part_send; easy.
       constructor.
       
       constructor.
       right.
       exists snat.
       exists( gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
       exists(ltt_send "Carol" [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       easy.
       
       (**)
       unfold isgPartsC.
       exists(g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       split.
       pfold. constructor.
       constructor. right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       exists(gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat.
       exists g_end.
       exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       split.
       intro n.
       exists 0.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists(g_end).
       split. easy. constructor.
       constructor. constructor.
       constructor.

       constructor.
       right.
       exists snat.
       exists( gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       exists(ltt_end). split. easy. split. easy.
       left. pfold.
       constructor.
       apply no_part_send; easy.
       constructor.
       constructor.
Qed.

Lemma GPCarol: projectionC G "Carol" TCarol.
Proof. unfold G, TCarol.
       pfold.
       apply proj_cont with (ys := [Some (ltt_recv "Bob" [Some (snat, ltt_send "Alice" [Some (snat, ltt_end)])]); Some (ltt_recv "Bob" [Some (snat, ltt_send "Alice" [Some (snat, ltt_end)])])]).
       easy. easy. easy.
       unfold isgPartsC.
       exists((g_send "Alice" "Bob"
         [Some (snat, g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]);
          Some (snat, g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])])])). 
       split.
       pfold. constructor.
       constructor. right.
       exists snat.
       exists(g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       exists(gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       exists(gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor. right.
       exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy. left. pfold. constructor.
       constructor. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       exists(gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       exists( gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor. constructor. constructor.
       split.
       intro n.
       exists 0.
       case_eq n; constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       split. easy.
       case_eq n0; constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]). split. easy.
       case_eq n1; constructor.
       constructor.
       right. exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       split. easy.
       case_eq n0; constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]). split. easy.
       case_eq n1; constructor.
       constructor.
       right. exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       apply pa_sendr with (n := 0) (s := snat) (g := g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]). easy. easy.
       simpl. easy.
       constructor.
       (**)
       constructor.
       right.
       exists snat.
       exists(gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
       exists(ltt_recv "Bob" [Some (snat, ltt_send "Alice" [Some (snat, ltt_end)])]).
       split. easy. split. easy.
       left. pfold. constructor.
       easy.
       
       unfold isgPartsC.
       exists((g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])])).
       split.
       pfold. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       exists( gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       split.
       intro n. exists 0.
       destruct n; constructor.
       constructor. right.
       exists snat. exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor.
       right.
       exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       (**)
       constructor.
       right.
       exists snat.
       exists( gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       exists(ltt_send "Alice" [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold. constructor. easy.
       
       unfold isgPartsC.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. pfold. constructor.
       constructor.
       right. exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       split.
       intro n. exists 0.
       destruct n; constructor.
       constructor.
       right. exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.

       constructor.
       right.
       exists snat. exists gtt_end. exists ltt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       apply no_part_end.
       constructor. constructor.
       constructor.
       right.
       exists snat.
       exists(gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
       exists(ltt_recv "Bob" [Some (snat, ltt_send "Alice" [Some (snat, ltt_end)])]).
       split. easy. split. easy.
       left. pfold. constructor.
       easy.

       unfold isgPartsC.
       exists((g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])])).
       split.
       pfold. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       exists( gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       right.
       exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       split.
       intro n. exists 0.
       destruct n; constructor.
       constructor. right.
       exists snat. exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor.
       right.
       exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.

       constructor.
       right.
       exists snat.
       exists( gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       exists(ltt_send "Alice" [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold. constructor. easy.

       unfold isgPartsC.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. pfold. constructor.
       constructor.
       right. exists snat. exists g_end. exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       split.
       intro n. exists 0.
       destruct n; constructor.
       constructor.
       right. exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.

       constructor.
       right.
       exists snat. exists gtt_end. exists ltt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       apply no_part_end.
       constructor. constructor.
       constructor.
       constructor.
       constructor.
Qed.

(*subtype*)

Lemma stAlice: subtypeC TAlice T'Alice.
Proof. unfold TAlice, T'Alice.
       pfold.
       constructor.
       simpl. split. constructor.
       split. left.
       pfold. constructor.
       simpl. split. constructor.
       split. left.
       pfold. constructor.
       easy.
       easy.
Qed.

(*typing*)

Definition PAlice := p_send "Bob" 0 (e_val (vnat 50)) (p_recv "Carol" [Some (p_inact)] ).

Lemma TypAlice: typ_proc nil nil PAlice TAlice.
Proof. unfold PAlice, TAlice.
       specialize(tc_send nil nil "Bob" 0 (e_val (vnat 50)) (p_recv "Carol" [Some p_inact])
       snat
       ( ltt_recv "Carol" [Some (snat, ltt_end)])
       ); intro HP.
       simpl in HP.
       apply HP.
       constructor.
       constructor. simpl. easy.
       simpl. easy.
       constructor.
       right.
       exists p_inact. exists snat. exists ltt_end.
       split. easy. split. easy.
       constructor.
       constructor.
Qed.

Definition PBob := p_recv "Alice" [
  Some(p_send "Carol" 0 (e_val (vnat 100)) (p_inact));
  Some(p_send "Carol" 0 (e_val (vnat 2)) (p_inact))
  ].

Lemma TypBob: typ_proc nil nil PBob TBob.
Proof. unfold PBob, TBob.
       constructor.
       simpl. easy.
       simpl. easy.
       constructor.
       right.
       exists(p_send "Carol" 0 (e_val (vnat 100)) p_inact).
       exists snat.
       exists(ltt_send "Carol" [Some (snat, ltt_end)]).
       split. easy. split. easy.
       specialize(tc_send [Some snat] nil "Carol" 0 (e_val (vnat 100)) p_inact
       snat ltt_end
       ); intro HP.
       simpl in HP.
       apply HP.
       constructor.
       constructor.
       
       constructor.
       right.
       exists(p_send "Carol" 0 (e_val (vnat 2)) p_inact).
       exists snat.
       exists(ltt_send "Carol" [Some (snat, ltt_end)]).
       split. easy. split. easy.
       specialize(tc_send [Some snat] nil "Carol" 0 (e_val (vnat 2)) p_inact
       snat ltt_end
       ); intro HP.
       simpl in HP.
       apply HP.
       constructor.
       constructor.
       constructor.
Qed.

Definition PCarol := p_recv "Bob" [Some (p_send "Alice" 0 (e_succ (e_var 0)) p_inact)].

Lemma TypCarol: typ_proc nil nil PCarol TCarol.
Proof. unfold PCarol, TCarol.
       constructor.
       simpl. easy. easy.
       constructor.
       right.
       exists((p_send "Alice" 0 (e_succ (e_var 0)) p_inact) ).
       exists snat.
       exists(ltt_send "Alice" [Some (snat, ltt_end)]).
       split. easy. split. easy.
       specialize(tc_send [Some snat] nil "Alice" 0 (e_succ (e_var 0)) p_inact
       snat ltt_end
       ); intro HP.
       simpl in HP.
       apply HP. 
       constructor.
       constructor. simpl. easy.
       constructor.
       constructor.
Qed.

Definition M := s_par (s_par (s_ind "Alice" PAlice) (s_ind "Bob" PBob)) (s_ind "Carol" PCarol).

Lemma pwf: forall pt : string, isgPartsC pt G -> InT pt M.
Proof. intros.
       case_eq (eqb pt "Alice"); intros.
       rewrite String.eqb_eq in H0. subst.
       unfold M.
       unfold InT. simpl. left. easy.
       rewrite String.eqb_neq in H0.
       case_eq (eqb pt "Bob"); intros.
       rewrite String.eqb_eq in H1. subst.
       unfold InT. simpl. right. left. easy.
       rewrite String.eqb_neq in H1.
       case_eq (eqb pt "Carol"); intros.
       rewrite String.eqb_eq in H2. subst.
       unfold InT. simpl. right. right. left. easy.
       rewrite String.eqb_neq in H2.
       apply part_cont in H; try easy.
       destruct H as (n,(s,(g,(Ha,Hb)))).
       revert pt H0 H1 H2 Hb. revert s g Ha.
       induction n; intros.
       - simpl in Ha.
         inversion Ha. subst. apply no_part_send_send in Hb; try easy.
         simpl in Ha.
       - destruct n. simpl in Ha. inversion Ha.
         subst. apply no_part_send_send in Hb; try easy.
         simpl in Ha.
         destruct n. simpl in Ha. easy. simpl in Ha. easy.
Qed.


Lemma endP: forall w, gttmap G w None gnode_end ->
  w = [0;0;0] \/ w = [1;0;0].
Proof. intros.
       inversion H. subst.
       case_eq n; intros.
       - subst. simpl in H6.
         inversion H6. subst.
         inversion H7. subst.
         case_eq n; intros.
         + subst. simpl in H8.
           inversion H8. subst.
           inversion H9. subst.
           case_eq n; intros.
           ++ subst. simpl in H10. inversion H10. subst.
              inversion H11. subst. left. easy.
           ++ subst. simpl in H10. 
              destruct n0; simpl in H10; easy.
         + subst. simpl in H8.
           destruct n0; simpl in H8; easy.
      - subst. simpl in H6.
        case_eq n0; intros.
        + subst. simpl in H6. 
          inversion H6. subst.
          inversion H7. subst.
          case_eq n; intros.
          ++ subst. simpl in H8.
             inversion H8. subst.
             inversion H9. subst.
             case_eq n; intros.
             * subst. simpl in H10.
               inversion H10. subst. 
               inversion H11. subst. right. easy.
             * subst. simpl in H10.
               destruct n0; simpl in H10; easy.
          ++ subst. simpl in H8.
             destruct n0; simpl in H8; easy.
        + subst. simpl in H6.
          destruct n; simpl in H6; easy.
Qed.

Lemma spq: forall w p q, gttmap G w None (gnode_pq p q) ->
  (w = [] /\ p = "Alice"%string /\ q = "Bob"%string) \/ 
  (w = [0] /\ p = "Bob"%string /\ q = "Carol"%string) \/ 
  (w = [1] /\ p = "Bob"%string /\ q = "Carol"%string) \/
  (w = [0;0] /\ p = "Carol"%string /\ q = "Alice"%string) \/ 
  (w = [1;0] /\ p = "Carol"%string /\ q = "Alice"%string).
Proof. intros.
       inversion H.
       - subst. left. easy.
       - subst. 
         case_eq n; intros.
         + subst. simpl in H6.
           inversion H6. subst.
           inversion H7. subst.
           right. left. easy.
           subst.
           case_eq n; intros.
           ++ subst. simpl in H8.
              inversion H8. subst. 
              inversion H9. subst. 
              right. right. right. left. easy.
              subst.
              case_eq n; intros.
              * subst. simpl in H10. inversion H10. subst.
                inversion H11.
              * subst. simpl in H10.
                destruct n0; simpl in H10; easy.
           ++ subst. simpl in H8.
              destruct n0; simpl in H8; easy.
         + subst.
           simpl in H6.
           case_eq n0; intros.
           ++ subst. simpl in H6.
              inversion H6. subst.
              inversion H7. subst.
              right. right. left. easy.
              subst.
              case_eq n; intros.
              * subst. simpl in H8.
                inversion H8. subst. 
                inversion H9. subst.
                right. right. right. right. easy.
              * subst.
                case_eq n; intros.
                ** subst. simpl in H10. inversion H10. subst.
                   inversion H11.
                ** subst. simpl in H10.
                   destruct n0; simpl in H10; easy.
           ++ subst. simpl in H8.
              destruct n0; simpl in H8; easy.
         + subst. simpl in H6.
           destruct n; simpl in H7; easy.
Qed.

Lemma spqn: forall n l p q, gttmap G (n :: l) None (gnode_pq p q) -> 
  (n = 0 /\ ((l = [] /\ p = "Bob"%string /\ q = "Carol"%string) \/ (l = [0] /\ p = "Carol"%string /\ q = "Alice"%string))) \/
  (n = 1 /\ ((l = [] /\ p = "Bob"%string /\ q = "Carol"%string) \/ (l = [0] /\ p = "Carol"%string /\ q = "Alice"%string))).
Proof. intros.
       case_eq n; intros.
       - subst. left.
         inversion H. subst.
         simpl in H7. inversion H7.
         subst. split. easy.
         inversion H8. subst. left. easy.
         subst. 
         case_eq n; intros.
         + subst. simpl in H6. inversion H6. subst.
           inversion H9. subst.
           right. easy.
           subst.
           case_eq n; intros.
           ++ subst. simpl in H10. inversion H10. subst.
              inversion H11.
           ++ subst. simpl in H10.
              destruct n0; simpl in H10; easy.
        + subst. simpl in H6.
          destruct n0; simpl in H6; easy.
       - subst. simpl. right.
         case_eq n0; intros.
         + subst. split. easy.
           inversion H. subst.
           simpl in H7. inversion H7. subst.
           inversion H8. subst. left. easy.
           subst. 
           case_eq n; intros.
           ++ right. subst. simpl in H6.
              inversion H6. subst.
              inversion H9. subst. easy.
              subst. 
              case_eq n; intros.
              * subst. simpl in H10. inversion H10. subst.
                inversion H11.
              * subst. simpl in H10.
                destruct n0; simpl in H10; easy.
            ++ subst. simpl in H6. 
               destruct n0; simpl in H6; easy.
        - subst. inversion H.
          subst.
          case_eq n; subst; simpl in H7.
          destruct n; easy.
          destruct n; easy.
Qed.

Lemma blen1: forall w t, length w = 1 -> gttmap G w None t ->
  (w = [0] /\ t = gnode_pq "Bob"%string "Carol"%string) \/
  (w = [1] /\ t = gnode_pq "Bob"%string "Carol"%string).
Proof. intros.
       inversion H0.
       subst. easy.
       subst.
       case_eq n; intros.
       + subst. simpl in H7. inversion H7. subst.
         inversion H8. subst. left. easy.
       + subst.
         case_eq n; intros.
         ++ subst. simpl in H9. inversion H9. subst.
            easy.
         ++ easy.
       subst. simpl in H7.
       case_eq n0; intros.
       + subst. simpl in H7.
         inversion H7. subst.
         inversion H8. subst.
         right. easy.
       + subst. easy.
       subst.
       simpl in H7.
       destruct n; simpl in H7; easy.
Qed.

Lemma blen2: forall w t, length w = 2 -> gttmap G w None t ->
  (w = [0;0] /\ t = gnode_pq "Carol"%string "Alice"%string) \/
  (w = [1;0] /\ t = gnode_pq "Carol"%string "Alice"%string).
Proof. intros.
       inversion H0.
       subst. easy.
       subst.
       case_eq n; intros.
       + subst. simpl in H7. inversion H7. subst.
         inversion H8. subst. left. easy.
       + subst.
         case_eq n; intros.
         ++ subst. simpl in H9. inversion H9. subst.
            inversion H10. subst.
            left. easy.
            subst. easy.
         ++ subst. simpl in H9.
            destruct n0; simpl in H9; easy.
         subst. simpl in H7.
         right.
       case_eq n0; intros.
       + subst. simpl in H7.
         inversion H7. subst.
         inversion H8. subst. easy.
         subst. 
         case_eq n; intros.
         ++ subst. simpl in H9. inversion H9. subst.
            inversion H10. subst. easy.
            subst. 
            case_eq n; intros.
            +++ subst. simpl in H11. inversion H11. subst.
                easy.
            +++ subst. easy.
          ++ subst. simpl in H9. 
             destruct n0 in H9; easy.
             subst.
             simpl in H7.
             destruct n; easy.
Qed.

Lemma bnil: forall {A: Type} (w1 w2: list A), w1 ++ w2 = [] -> w1 = [] /\ w2 = [].
Proof. intros A w1.
       induction w1; intros.
       - simpl in H. subst. easy.
       - simpl in H. easy.
Qed.

Lemma onenil: forall {A: Type} w1 w2 (a: A), w1 ++ w2 = [a] -> (w1 = [a] /\ w2 = []) \/ (w1 = [] /\ w2 = [a]).
Proof. intros a w1.
       induction w1; intros.
       - simpl in H. simpl. right. easy.
       - simpl in H.
         inversion H. subst.
         apply bnil in H2.
         destruct H2 as (H2a,H2b). subst.
         simpl. left. easy.
Qed.

Lemma balG: balancedG G.
Proof. unfold balancedG.
       intros.
       inversion H.
       - subst. simpl in H0. simpl.
         destruct H0 as [H0 | H0].
         + apply spq in H0.
           destruct H0 as [(Ha1,(Ha2,Ha3)) | [(Ha1,(Ha2,Ha3)) | [(Ha1,(Ha2,Ha3))| [(Ha1,(Ha2,Ha3)) | (Ha1,(Ha2,Ha3))]]]].
           ++ subst.
              exists 0.
              intros.
              destruct H0 as [H0 | H0].
              * apply endP in H0.
                destruct H0 as [H0 | H0].
                ** subst. exists []. exists [0;0;0].
                   simpl. split. easy.
                   exists "Bob"%string.
                   left. easy.
                ** subst. exists []. exists [1;0;0].
                   simpl. split. easy.
                   exists "Bob"%string.
                   left. easy.
                destruct H0 as (Ha,(t,Hb)).
                assert (w' = []).
                { apply length_zero_iff_nil. easy. } 
                subst.
                exists []. exists []. 
                split. easy. 
                exists "Bob"%string.
                left. easy.
           ++ exists 1.
              intros.
              destruct H0 as [H0 | H0].
              * apply endP in H0.
                destruct H0 as [H0 | H0].
                ** rewrite H0. exists [0]. exists [0;0].
                   simpl. split. easy.
                   exists "Carol"%string.
                   left. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                   simpl. easy.
                   rewrite Ha2.
                   constructor.
                ** exists [1]. exists [0;0].
                   simpl. split. easy.
                   exists "Carol"%string.
                   left. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                   simpl. easy.
                   rewrite Ha2.
                   constructor.
                   destruct H0 as (Ha,(t,Hb)).
                   specialize(blen1 w'0 t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   *** subst. exists [0]. exists [].
                       split. easy. exists "Carol"%string. 
                       left. easy.
                   *** subst.  exists [1]. exists [].
                       split. easy. exists "Carol"%string. 
                       left. easy.
           ++ subst.
              exists 1.
              intros.
              destruct H0 as [H0 | H0].
              * apply endP in H0.
                destruct H0 as [H0 | H0].
                ** rewrite H0. exists [0]. exists [0;0].
                   simpl. split. easy.
                   exists "Carol"%string.
                   left. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                   simpl. easy.
                   constructor.
                ** exists [1]. exists [0;0].
                   simpl. split. easy.
                   exists "Carol"%string.
                   left. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                   simpl. easy.
                   constructor.
                   destruct H0 as (Ha,(t,Hb)).
                   specialize(blen1 w' t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   *** subst. exists [0]. exists [].
                       split. easy. exists "Carol"%string. 
                       left. easy.
                   *** subst.  exists [1]. exists [].
                       split. easy. exists "Carol"%string. 
                       left. easy.
             ++ subst.
                exists 1.
                intros.
                destruct H0 as [H0 | H0].
                * apply endP in H0.
                  destruct H0 as [H0 | H0].
                  ** exists [0;0]. exists [0].
                     simpl. split. easy.
                     exists "Alice"%string.
                     left. 
                     unfold G.
                     apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                  ** exists [1;0]. exists [0].
                     simpl. split. easy.
                     exists "Alice"%string.
                     left. 
                     unfold G.
                     apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                * destruct H0 as (Ha,(t,Hb)).
                   specialize(blen1 w' t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   *** subst. exists [0]. exists [].
                       split. easy. exists "Bob"%string. 
                       right. easy.
                   *** subst.  exists [1]. exists [].
                       split. easy. exists "Bob"%string. 
                       right. easy.
             ++ exists 2. subst.
                intros.
                destruct H0 as [H0 | H0].
                * apply endP in H0.
                  destruct H0 as [H0 | H0].
                  ** exists [0;0]. exists [0].
                     simpl. split. easy.
                     exists "Alice"%string.
                     left.
                     apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                  ** exists [1;0]. exists [0].
                     simpl. split. easy.
                     exists "Alice"%string.
                     left. 
                     unfold G.
                     apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                 * destruct H0 as (Ha,(t,Hb)).
                   specialize(blen2 w' t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   ** subst. exists [0;0]. exists [].
                      simpl. split. easy.
                      exists "Alice"%string. left. easy.
                   ** subst. exists [1;0]. exists [].
                      simpl. split. easy.
                      exists "Alice"%string. left. easy.
         + apply spq in H0.
           destruct H0 as [(Ha1,(Ha2,Ha3)) | [(Ha1,(Ha2,Ha3)) | [(Ha1,(Ha2,Ha3))| [(Ha1,(Ha2,Ha3)) | (Ha1,(Ha2,Ha3))]]]].
           ++ subst.
              exists 0.
              intros.
              destruct H0 as [H0 | H0].
              * apply endP in H0.
                destruct H0 as [H0 | H0].
                ** subst. exists []. exists [0;0;0].
                   simpl. split. easy.
                   exists "Alice"%string.
                   right. easy.
                ** subst. exists []. exists [1;0;0].
                   simpl. split. easy.
                   exists "Alice"%string.
                   right. easy.
                destruct H0 as (Ha,(t,Hb)).
                assert (w' = []).
                { apply length_zero_iff_nil. easy. } 
                subst.
                exists []. exists []. 
                split. easy. 
                exists "Alice"%string.
                right. easy.
           ++ exists 1.
              intros.
              destruct H0 as [H0 | H0].
              * apply endP in H0.
                destruct H0 as [H0 | H0].
                ** rewrite H0. exists [0]. exists [0;0].
                   simpl. split. easy.
                   exists "Bob"%string.
                   right. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                   simpl. easy.
                   subst.
                   constructor.
                ** exists [1]. exists [0;0].
                   simpl. split. easy.
                   exists "Bob"%string.
                   right. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                   simpl. easy.
                   subst.
                   constructor.
                   destruct H0 as (Ha,(t,Hb)).
                   specialize(blen1 w'0 t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   *** subst. exists [0]. exists [].
                       split. easy. exists "Bob"%string. 
                       right. easy.
                   *** subst.  exists [1]. exists [].
                       split. easy. exists "Bob"%string. 
                       right. easy.
           ++ subst.
              exists 1.
              intros.
              destruct H0 as [H0 | H0].
              * apply endP in H0.
                destruct H0 as [H0 | H0].
                ** rewrite H0. exists [0]. exists [0;0].
                   simpl. split. easy.
                   exists "Bob"%string.
                   right. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                   simpl. easy.
                   constructor.
                ** exists [1]. exists [0;0].
                   simpl. split. easy.
                   exists "Bob"%string.
                   right. unfold G.
                   apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                   simpl. easy.
                   constructor.
                   destruct H0 as (Ha,(t,Hb)).
                   specialize(blen1 w' t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   *** subst. exists [0]. exists [].
                       split. easy. exists "Bob"%string. 
                       right. easy.
                   *** subst.  exists [1]. exists [].
                       split. easy. exists "Bob"%string. 
                       right. easy.
             ++ subst.
                exists 1.
                intros.
                destruct H0 as [H0 | H0].
                * apply endP in H0.
                  destruct H0 as [H0 | H0].
                  ** exists [0;0]. exists [0].
                     simpl. split. easy.
                     exists "Carol"%string.
                     right. 
                     unfold G.
                     apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                  ** exists [1;0]. exists [0].
                     simpl. split. easy.
                     exists "Carol"%string.
                     right. 
                     unfold G.
                     apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                * destruct H0 as (Ha,(t,Hb)).
                   specialize(blen1 w' t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   *** subst. exists []. exists [0].
                       split. easy. exists "Bob"%string. 
                       left. easy.
                   *** subst.  exists []. exists [1].
                       split. easy. exists "Bob"%string. 
                       left. easy.
             ++ exists 2. subst.
                intros.
                destruct H0 as [H0 | H0].
                * apply endP in H0.
                  destruct H0 as [H0 | H0].
                  ** exists [0;0]. exists [0].
                     simpl. split. easy.
                     exists "Carol"%string.
                     right.
                     apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                  ** exists [1;0]. exists [0].
                     simpl. split. easy.
                     exists "Carol"%string.
                     right. 
                     unfold G.
                     apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                     simpl. easy.
                     apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                     simpl. easy.
                     constructor.
                 * destruct H0 as (Ha,(t,Hb)).
                   specialize(blen2 w' t Ha Hb); intro HH.
                   destruct HH as [(HHa,HHb) | (HHa,HHb)].
                   ** subst. exists [0;0]. exists [].
                      simpl. split. easy.
                      exists "Carol"%string. right. easy.
                   ** subst. exists [1;0]. exists [].
                      simpl. split. easy.
                      exists "Carol"%string. right. easy. 
             ++ subst.
                destruct H0 as [H0 | H0].
                * assert(((n :: lis) ++ w') = n :: (lis++w')).
                  { simpl. easy. }
                  rewrite H1 in H0.
                  apply spqn in H0.
                  destruct H0 as [H0 | H0].
                  ** destruct H0 as (Ha, Hb).
                     subst. simpl in H7.
                     destruct Hb as [Hb | Hb].
                     *** destruct Hb as (Hb1,(Hb2,Hb3)).
                         subst.
                         assert(lis = [] /\ w' = []).
                         { apply bnil. easy. }
                         destruct H0 as (H0a,H0b).
                         subst. simpl.
                         inversion H7. subst.
                         exists 0.
                         intros.
                         destruct H0 as [H0 | H0].
                         **** apply endP in H0. 
                              destruct H0 as [H0 | H0].
                              +++ inversion H0. subst.
                                  exists []. exists [0;0].
                                  simpl. split. easy.
                                  exists "Carol"%string.
                                  left. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                                  easy.
                              +++ destruct H0 as (H0a,H0b).
                                  assert(w' = []).
                                  { apply length_zero_iff_nil. easy. } 
                                  subst.
                                  exists []. exists []. split. easy.
                                  exists "Carol"%string.
                                  left. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                         **** destruct Hb as (Hb1,(Hb2,Hb3)).
                              subst.
                              apply onenil in Hb1.
                              destruct Hb1 as [(Hb1,Hb2) | (Hb1,Hb2)].
                              +++ subst.
                                  exists 0.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       **** inversion H0. subst.
                                            exists []. exists [0]. split. easy.
                                            exists "Alice"%string.
                                            simpl. left.
                                            apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                                            easy.
                                       **** destruct H0 as (H0a,H0b).
                                            assert(w' = []).
                                            { apply length_zero_iff_nil. easy. } 
                                            subst.
                                            exists []. exists []. split. easy.
                                            exists "Alice"%string.
                                            left.
                                            apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                              +++ subst. 
                                  exists 0.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       inversion H0. subst.
                                       exists [0]. exists [0].
                                       simpl. split. easy.
                                       exists "Alice"%string.
                                       simpl. left.
                                       apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                       simpl. easy.
                                       apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                                       simpl. easy.
                                       constructor.
                                       easy.
                                       destruct H0 as (Ha,(t,Hb)).
                                       assert(w' = []).
                                       { apply length_zero_iff_nil. easy. } 
                                       subst. simpl in Hb.
                                       exists []. exists []. split. easy. simpl.
                                       exists "Bob"%string.
                                       right.
                                       apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                       simpl. easy.
                                       constructor.
                  ++ destruct H0 as (Ha, Hb).
                     subst.
                     simpl in H7.
                     destruct Hb as [Hb | Hb].
                     *** destruct Hb as (Hb1,(Hb2,Hb3)).
                         subst.
                         assert(lis = [] /\ w' = []).
                         { apply bnil. easy. }
                         destruct H0 as (H0a,H0b).
                         subst. simpl.
                         inversion H7. subst.
                         exists 0.
                         intros.
                         destruct H0 as [H0 | H0].
                         **** apply endP in H0. 
                              destruct H0 as [H0 | H0].
                              +++ easy.
                                  inversion H0. subst.
                                  exists []. exists [0;0].
                                  simpl. split. easy.
                                  exists "Carol"%string.
                                  left. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                              +++ destruct H0 as (H0a,H0b).
                                  assert(w' = []).
                                  { apply length_zero_iff_nil. easy. } 
                                  subst.
                                  exists []. exists []. split. easy.
                                  exists "Carol"%string.
                                  left. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                         **** destruct Hb as (Hb1,(Hb2,Hb3)).
                              subst.
                              apply onenil in Hb1.
                              destruct Hb1 as [(Hb1,Hb2) | (Hb1,Hb2)].
                              +++ subst.
                                  exists 0.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       **** easy.
                                            inversion H0. subst.
                                            exists []. exists [0]. split. easy.
                                            exists "Alice"%string.
                                            simpl. left.
                                            apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                                       **** destruct H0 as (H0a,H0b).
                                            assert(w' = []).
                                            { apply length_zero_iff_nil. easy. } 
                                            subst.
                                            exists []. exists []. split. easy.
                                            exists "Alice"%string.
                                            left.
                                            apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                              +++ subst. 
                                  exists 0.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       easy.
                                       inversion H0. subst.
                                       exists [0]. exists [0].
                                       simpl. split. easy.
                                       exists "Alice"%string.
                                       simpl. left.
                                       apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                       simpl. easy.
                                       apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                                       simpl. easy.
                                       constructor.
                                       destruct H0 as (Ha,(t,Hb)).
                                       assert(w' = []).
                                       { apply length_zero_iff_nil. easy. } 
                                       subst. simpl in Hb.
                                       exists []. exists []. split. easy. simpl.
                                       exists "Bob"%string.
                                       right.
                                       apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                       simpl. easy.
                                       constructor.
               ++ assert(((n :: lis) ++ w') = n :: (lis++w')).
                  { simpl. easy. }
                  rewrite H1 in H0.
                  apply spqn in H0.
                  destruct H0 as [H0 | H0].
                  ** destruct H0 as (Ha, Hb).
                     subst. simpl in H7.
                     destruct Hb as [Hb | Hb].
                     *** destruct Hb as (Hb1,(Hb2,Hb3)).
                         subst.
                         assert(lis = [] /\ w' = []).
                         { apply bnil. easy. }
                         destruct H0 as (H0a,H0b).
                         subst. simpl.
                         inversion H7. subst.
                         exists 0.
                         intros.
                         destruct H0 as [H0 | H0].
                         **** apply endP in H0. 
                              destruct H0 as [H0 | H0].
                              +++ inversion H0. subst.
                                  exists []. exists [0;0].
                                  simpl. split. easy.
                                  exists "Bob"%string.
                                  right. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                                  easy.
                              +++ destruct H0 as (H0a,H0b).
                                  assert(w' = []).
                                  { apply length_zero_iff_nil. easy. } 
                                  subst.
                                  exists []. exists []. split. easy.
                                  exists "Bob"%string.
                                  right. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                         **** destruct Hb as (Hb1,(Hb2,Hb3)).
                              subst.
                              apply onenil in Hb1.
                              destruct Hb1 as [(Hb1,Hb2) | (Hb1,Hb2)].
                              +++ subst.
                                  exists 0.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       **** inversion H0. subst.
                                            exists []. exists [0]. split. easy.
                                            exists "Carol"%string.
                                            simpl. right.
                                            apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                                            easy.
                                       **** destruct H0 as (H0a,H0b).
                                            assert(w' = []).
                                            { apply length_zero_iff_nil. easy. } 
                                            subst.
                                            exists []. exists []. split. easy.
                                            exists "Carol"%string.
                                            right.
                                            apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                              +++ subst.
                                  exists 1.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       inversion H0. subst.
                                       exists [0]. exists [0].
                                       simpl. split. easy.
                                       exists "Carol"%string.
                                       simpl. right.
                                       apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                       simpl. easy.
                                       apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                                       simpl. easy.
                                       constructor.
                                       easy.
                                       destruct H0 as (Ha,(t,Hb)).
                                       simpl in Hb.
                                       inversion Hb.
                                       subst. simpl in H10. inversion H10. subst.
                                       inversion H11. subst.
                                       easy.
                                       subst.
                                       case_eq n; intros.
                                       **** subst. simpl in H9. inversion H9. subst.
                                            inversion H12. subst. 
                                            exists [0]. exists []. 
                                            split. easy.
                                            exists "Carol"%string.
                                            simpl. right.
                                            apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                                            subst.
                                            easy.
                                      **** subst. simpl in H9. 
                                           destruct n0; easy.
                  ++ destruct H0 as (Ha, Hb).
                     subst.
                     simpl in H7.
                     destruct Hb as [Hb | Hb].
                     *** destruct Hb as (Hb1,(Hb2,Hb3)).
                         subst.
                         assert(lis = [] /\ w' = []).
                         { apply bnil. easy. }
                         destruct H0 as (H0a,H0b).
                         subst. simpl.
                         inversion H7. subst.
                         exists 0.
                         intros.
                         destruct H0 as [H0 | H0].
                         **** apply endP in H0. 
                              destruct H0 as [H0 | H0].
                              +++ easy.
                                  inversion H0. subst.
                                  exists []. exists [0;0].
                                  simpl. split. easy.
                                  exists "Bob"%string.
                                  right. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                              +++ destruct H0 as (H0a,H0b).
                                  assert(w' = []).
                                  { apply length_zero_iff_nil. easy. } 
                                  subst.
                                  exists []. exists []. split. easy.
                                  exists "Bob"%string.
                                  right. unfold G.
                                  apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                  simpl. easy.
                                  constructor.
                         **** destruct Hb as (Hb1,(Hb2,Hb3)).
                              subst.
                              apply onenil in Hb1.
                              destruct Hb1 as [(Hb1,Hb2) | (Hb1,Hb2)].
                              +++ subst.
                                  exists 0.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       **** easy.
                                            inversion H0. subst.
                                            exists []. exists [0]. split. easy.
                                            exists "Carol"%string.
                                            simpl. right.
                                            apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                                       **** destruct H0 as (H0a,H0b).
                                            assert(w' = []).
                                            { apply length_zero_iff_nil. easy. } 
                                            subst.
                                            exists []. exists []. split. easy.
                                            exists "Carol"%string.
                                            right.
                                            apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                              +++ subst. 
                                  exists 1.
                                  intros.
                                  destruct H0 as [H0 | H0].
                                  ++++ apply endP in H0.
                                       destruct H0 as [H0 | H0].
                                       easy.
                                       inversion H0. subst.
                                       exists [0]. exists [0].
                                       simpl. split. easy.
                                       exists "Carol"%string.
                                       simpl. right.
                                       apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                       simpl. easy.
                                       apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                                       simpl. easy.
                                       constructor.
                                       destruct H0 as (Ha,(t,Hb)).
                                       inversion Hb. subst.
                                       simpl in H10. inversion H10. subst.
                                       inversion H11. subst. easy.
                                       subst. 
                                       case_eq n; intros.
                                       **** subst. simpl in H9.
                                            inversion H9. subst.
                                            inversion H12. subst.
                                            exists [0]. exists [].
                                            simpl. split. easy.
                                            exists "Carol"%string.
                                            right.
                                            apply gmap_con with (st := snat) (gk := gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
                                            simpl. easy.
                                            apply gmap_con with (st := snat) (gk :=  gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
                                            simpl. easy.
                                            constructor.
                                            subst.
                                            case_eq n; intros.
                                            ++++ subst. simpl in H13. inversion H13. subst. easy.
                                            ++++ subst. easy.
                                            subst. simpl in H9.
                                            destruct n0; easy.
Qed.

Lemma wfgCG: wfgC G.
Proof. unfold wfgC.
       unfold G.
       exists((g_send "Alice" "Bob"
         [Some (snat, g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]);
          Some (snat, g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])])])).
       split.
       pfold. constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       exists(gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       exists(gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. 
       constructor.
       constructor.
       right. exists snat.
       exists g_end.
       exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       exists(gtt_send "Bob" "Carol" [Some (snat, gtt_send "Carol" "Alice" [Some (snat, gtt_end)])]).
       split. easy. split. easy.
       left. pfold.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       exists(gtt_send "Carol" "Alice" [Some (snat, gtt_end)]).
       split. easy. split. easy.
       left. pfold. 
       constructor.
       constructor.
       right. exists snat.
       exists g_end.
       exists gtt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       constructor.
       split.
       constructor. simpl. easy. easy.
       constructor. right.
       exists snat.
       exists( g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       split. easy.
       constructor.
       simpl. easy. easy.
       constructor. right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. easy.
       constructor. easy. easy.
       constructor. right.
       exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       right. 
       exists snat.
       exists( g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       split. easy.
       constructor.
       simpl. easy. easy.
       constructor. right.
       exists snat.
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. easy.
       constructor. easy. easy.
       constructor. right.
       exists snat. exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       split.
       intro n. exists 0.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists(g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       split. easy.
       destruct n; constructor.
       constructor.
       right. exists snat. 
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       right.
       exists snat.
       exists(g_send "Bob" "Carol" [Some (snat, g_send "Carol" "Alice" [Some (snat, g_end)])]).
       split. easy.
       destruct n; constructor.
       constructor.
       right. exists snat. 
       exists(g_send "Carol" "Alice" [Some (snat, g_end)]).
       split. easy.
       destruct n; constructor.
       constructor. right.
       exists snat.
       exists g_end.
       split. easy. constructor.
       constructor.
       constructor.
       constructor.
       
       apply balG.
Qed.

Lemma TypM: typ_sess M G.
Proof. constructor.
       apply wfgCG.
       apply pwf.
       
       unfold M.
       simpl.
       constructor.
       intro H.
       inversion H. easy. inversion H0. easy. easy.
       constructor.
       intro H.
       inversion H. easy. easy.
       constructor.
       intro H. inversion H. constructor.
     
       
       unfold G, M.
       constructor.
       constructor.
       constructor.
       exists T'Alice.
       split.
       apply GPAlice.
       split.
       apply tc_sub with (t := TAlice).
       apply TypAlice.
       apply stAlice.
       
       unfold T'Alice.
       unfold wfC.
       exists(l_send "Bob"
         [Some (snat, l_recv "Carol" [Some (snat, l_end)]);
          Some (snat, l_recv "Carol" [Some (snat, l_end)])]) .
       split.
       pfold.
       constructor.
       constructor.
       right.
       exists snat.
       exists(l_recv "Carol" [Some (snat, l_end)]).
       exists(ltt_recv "Carol" [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold. 
       constructor.
       constructor.
       right.
       exists snat. exists l_end. exists ltt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       right.
       exists snat.
       exists(l_recv "Carol" [Some (snat, l_end)]).
       exists(ltt_recv "Carol" [Some (snat, ltt_end)]).
       split. easy. split. easy.
       left. pfold. 
       constructor.
       constructor.
       right.
       exists snat. exists l_end. exists ltt_end.
       split. easy. split. easy.
       left. pfold. constructor.
       constructor.
       constructor.
       
       split.
       constructor. simpl. easy.
       constructor.
       right.
       exists snat.
       exists(l_recv "Carol" [Some (snat, l_end)]).
       split. easy.
       constructor. easy. constructor.
       right. exists snat. exists l_end. split. easy. constructor.
       constructor.
       constructor.
       right. 
       exists snat.
       exists(l_recv "Carol" [Some (snat, l_end)]).
       split. easy.
       constructor. easy. constructor.
       right. exists snat. exists l_end. split. easy. constructor.
       constructor.
       constructor.
       
       intro n.
       exists 0.
       destruct n; constructor.
       constructor.
       right. 
       exists snat.
       exists(l_recv "Carol" [Some (snat, l_end)]).
       split. easy.
       destruct n; constructor.
       constructor.
       right. exists snat. exists l_end. split. easy. constructor.
       constructor.
       constructor.
       right.
       exists snat.
       exists(l_recv "Carol" [Some (snat, l_end)]).
       split. easy.
       destruct n; constructor.
       constructor.
       right. exists snat. exists l_end. split. easy. constructor.
       constructor.
       constructor.
       
       intro n.
       unfold PAlice.
       exists 0.
       destruct n; constructor.
       destruct n; constructor.
       constructor.
       right. exists p_inact. split. easy. constructor.
       constructor.
         
       constructor.
       exists TBob.
       split.
       apply GPBob.
       split.
       apply TypBob.
       
       intro n.
       exists 0. unfold PBob.
       destruct n; constructor.
       constructor.
       right.
       exists((p_send "Carol" 0 (e_val (vnat 100)) p_inact) ).
       split. easy.
       destruct n; constructor.
       constructor.
       constructor.
       right.
       exists((p_send "Carol" 0 (e_val (vnat 2)) p_inact) ).
       split. easy.
       destruct n; constructor.
       constructor.
       constructor.
       
       constructor.
       exists TCarol.
       split.
       apply GPCarol.
       split.
       apply TypCarol.
       
       intro n.
       unfold PCarol.
       exists 0.
       destruct n; constructor.
       constructor.
       right.
       exists((p_send "Alice" 0 (e_succ (e_var 0)) p_inact) ).
       split. easy.
       destruct n; constructor.
       constructor.
       constructor.
Qed.

Definition P'Alice := p_recv "Carol" [Some (p_inact)].

Definition P'Bob := p_send "Carol" 0 (e_val (vnat 100)) (p_inact).

Definition M' := s_par (s_par (s_ind "Alice" P'Alice) (s_ind "Bob" P'Bob)) (s_ind "Carol" PCarol).

Lemma redM: betaP M M'.
Proof. unfold M, M', PAlice, P'Alice, PBob, P'Bob.
       specialize(r_struct
       M
       (s_par (s_par (s_ind "Bob" PBob) (s_ind "Alice" PAlice)) (s_ind "Carol" PCarol))
       M'
       (s_par (s_par (s_ind "Bob" P'Bob) (s_ind "Alice" P'Alice)) (s_ind "Carol" PCarol))
       ); intro HR.
       apply HR.
       unfold M.
       apply pc_par1m.
       unfold M.
       apply pc_par1m.

       unfold M, M', PAlice, P'Alice, PBob, P'Bob.
       specialize(r_comm "Bob" "Alice"
         ([Some (p_send "Carol" 0 (e_val (vnat 100)) p_inact); Some (p_send "Carol" 0 (e_val (vnat 2)) p_inact)])
         (p_send "Carol" 0 (e_val (vnat 100)) p_inact)
         0 (e_val (vnat 50)) (vnat 50)
         (p_recv "Carol" [Some p_inact])
          ("Carol" <-- PCarol)
       ); intro HC.
       simpl in HC.
       apply HC.
       easy.
       constructor.
Qed.

Lemma SRExa: exists G', typ_sess M' G' /\ multiC G G'.
Proof. apply sub_red with (M := M).
       apply TypM.
       apply redM.
Qed.

