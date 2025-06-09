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
       Print isgParts.
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

Print session.

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

Lemma balG: balancedG G.
Proof. Admitted.

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

