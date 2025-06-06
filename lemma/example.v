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

Lemma no_part_ed: forall p,
  isgPartsC p (gtt_end) -> False.
Proof. intros.
       specialize(part_break_s gtt_end p H); intro HH.
       destruct HH as (g, (Ha,(Hb,[Hc | (r,(s,(xs,Hxs)))]))).
       subst. inversion Hb.
       subst.
       pinversion Ha.
       apply gttT_mon.
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
       apply no_part_ed.
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
       apply no_part_ed.
       constructor.
       constructor.
       constructor.
       constructor.
Qed.
       
       