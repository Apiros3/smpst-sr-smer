From SST Require Export src.expressions  type.global type.local  type.isomorphism type.projection.
Require Import String List Datatypes ZArith Relations PeanoNat.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.
Open Scope list_scope.
Import ListNotations.

CoFixpoint Ga : gtt := gtt_send "Alice" "Bob" [Some (snat, Ga); Some(snat, gtt_send "p" "q" [Some (sbool, gtt_end)])].

Example Gaexp : projectionC Ga "p" (ltt_send "q" [Some(sbool, ltt_end)]).
Proof.
  pcofix CIH.
  specialize(gtt_eq Ga); intros. 
  replace Ga with (gtt_id Ga). unfold gtt_id. simpl.
  pfold. apply proj_cont with (ys := [Some (ltt_send "q" [Some(sbool, ltt_end)]); Some (ltt_send "q" [Some(sbool, ltt_end)])]); try easy.
  constructor.
  - right. exists snat. exists Ga. exists (ltt_send "q" [Some (sbool, ltt_end)]). split. easy. split. easy.
    right. easy.
  constructor; try easy.
  - right. exists snat. exists (gtt_send "p" "q" [Some (sbool, gtt_end)]). exists (ltt_send "q" [Some (sbool, ltt_end)]).
    split. easy. split. easy. left.
    pfold. constructor; try easy. constructor; try easy.
    right. exists sbool. exists gtt_end. exists ltt_end. split. easy. split. easy. left. pfold. constructor.
    intros. unfold isgPartsC in H0. destruct H0 as (Gl,(Ha,(Hb,Hc))). 
    admit.
  admit.
Admitted.


Definition G1 : gtt := gtt_send "r" "s" [Some(snat, gtt_send "p" "q" [Some(snat, gtt_send "q" "r" [Some(sbool, gtt_end)]); Some(snat, gtt_send "q" "r" [None; Some(sbool, gtt_end)])])].

Definition G3 : gtt := gtt_send "r" "s" [Some(snat, gtt_send "q" "r" [Some(sbool, gtt_end); Some(sbool, gtt_end)])].

Definition G2 : gtt := gtt_send "p" "q" [Some(snat, G3); Some(snat, G3)].

Definition G : gtt := gtt_send "s" "s'" [Some(snat, G1); Some(snat, G2)].

Example Gexr : projectionC G "r" (ltt_send "s" [Some(snat, ltt_recv "q" [Some(sbool, ltt_end); Some(sbool, ltt_end)])]).
Proof.
  pfold. apply proj_cont with (ys := [Some (ltt_send "s" [Some(snat, ltt_recv "q" [Some(sbool, ltt_end); Some(sbool, ltt_end)])]); Some (ltt_send "s" [Some(snat, ltt_recv "q" [Some(sbool, ltt_end); Some(sbool, ltt_end)])])]); try easy.
  constructor; try easy.
  - right. exists snat. exists G1. exists (ltt_send "s" [Some (snat, ltt_recv "q" [Some (sbool, ltt_end); Some (sbool, ltt_end)])]).
    split. easy. split. easy. left.
    pfold. constructor; try easy. constructor; try easy. right.
    exists snat. exists (gtt_send "p" "q"
       [Some (snat, gtt_send "q" "r" [Some (sbool, gtt_end)]);
        Some (snat, gtt_send "q" "r" [None; Some (sbool, gtt_end)])]).
    exists (ltt_recv "q" [Some (sbool, ltt_end); Some (sbool, ltt_end)]). 
    split. easy. split. easy. left. pfold.
    apply proj_cont with (ys := [Some (ltt_recv "q" [Some (sbool, ltt_end)]); Some (ltt_recv "q" [None; Some (sbool, ltt_end)])]); try easy. 
    constructor; try easy. right. exists snat. exists (gtt_send "q" "r" [Some (sbool, gtt_end)]).
    exists (ltt_recv "q" [Some (sbool, ltt_end)]). split. easy. split. easy. left.
    pfold. constructor; try easy.
    constructor; try easy. right. exists sbool. exists gtt_end. exists ltt_end. 
    split. easy. split. easy. left. pfold. constructor. 
    - admit.
    constructor; try easy. right. exists snat. exists (gtt_send "q" "r" [None; Some (sbool, gtt_end)]).
    exists (ltt_recv "q" [None; Some (sbool, ltt_end)]). split. easy. split. easy.
    left. pfold. apply proj_in; try easy. constructor. left. easy.
    constructor; try easy. right. exists sbool. exists gtt_end. exists ltt_end. 
    split. easy. split. easy. left. pfold. constructor. 
    - admit.
    - admit.
  - constructor; try easy.
    right. exists snat. exists G2. exists (ltt_send "s" [Some (snat, ltt_recv "q" [Some (sbool, ltt_end); Some (sbool, ltt_end)])]).
    split. easy. split. easy. left. pfold. unfold G2. 
    apply proj_cont with (ys := [Some (ltt_send "s" [Some (snat, ltt_recv "q" [Some (sbool, ltt_end); Some (sbool, ltt_end)])]); Some (ltt_send "s" [Some (snat, ltt_recv "q" [Some (sbool, ltt_end); Some (sbool, ltt_end)])])]); try easy.
    assert(Some (snat, G3) = None /\
Some (ltt_send "s" [Some (snat, ltt_recv "q" [Some (sbool, ltt_end); Some (sbool, ltt_end)])]) = None \/
(exists (s : sort) (g : gtt) (t : ltt),
   Some (snat, G3) = Some (s, g) /\
   Some (ltt_send "s" [Some (snat, ltt_recv "q" [Some (sbool, ltt_end); Some (sbool, ltt_end)])]) =
   Some t /\ upaco3 projection bot3 g "r"%string t)).
    {
      right. exists snat. exists G3. exists (ltt_send "s" [Some (snat, ltt_recv "q" [Some (sbool, ltt_end); Some (sbool, ltt_end)])]).
      split. easy. split. easy.
      left. pfold. unfold G3. constructor; try easy. 
    }
    constructor; try easy. constructor; try easy.
    admit.
    admit.
Admitted.

Example Gex2 : gttstepC G (gtt_send "s" "s'" [Some(snat, gtt_send "r" "s" [Some(snat, gtt_send "s" "r" [Some(sbool, gtt_end)])]); Some(snat, G3)]) "p" "q" 0.
Proof.
  pfold. constructor; try easy.
  - constructor; try easy. right. exists snat. exists G1. split. easy. 
    split. 
    - unfold isgPartsC. unfold G1. 
      exists (g_send "r" "s"
       [Some
          (snat,
           g_send "p" "q"
             [Some (snat, g_send "s" "r" [Some (sbool, g_end)]);
              Some (snat, g_send "s" "r" [None; Some (sbool, g_end)])])]).
      split. pfold. constructor. constructor; try easy.
      right. exists snat. exists (g_send "p" "q"
       [Some (snat, g_send "s" "r" [Some (sbool, g_end)]);
        Some (snat, g_send "s" "r" [None; Some (sbool, g_end)])]). exists (gtt_send "p" "q"
       [Some (snat, gtt_send "s" "r" [Some (sbool, gtt_end)]);
        Some (snat, gtt_send "s" "r" [None; Some (sbool, gtt_end)])]).
       split. easy. split. easy. left.
       pfold. constructor. constructor; try easy. 
       right. exists snat. exists (g_send "s" "r" [Some (sbool, g_end)]). exists (gtt_send "s" "r" [Some (sbool, gtt_end)]).
       split. easy. split. easy. left. pfold. constructor. constructor; try easy.
       right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
       left. pfold. constructor. constructor.
       right. exists snat. exists (g_send "s" "r" [None; Some (sbool, g_end)]). exists (gtt_send "s" "r" [None; Some (sbool, gtt_end)]).
       split. easy. split. easy. left. pfold. constructor. constructor; try easy. left. easy. constructor; try easy.
       right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
       left. pfold. constructor. constructor.
       apply pa_sendr with (n := 0) (s := snat) (g := g_send "p" "q"
           [Some (snat, g_send "s" "r" [Some (sbool, g_end)]);
            Some (snat, g_send "s" "r" [None; Some (sbool, g_end)])]); try easy.
       constructor.
    - unfold isgPartsC. unfold G1. 
      exists (g_send "r" "s"
       [Some
          (snat,
           g_send "p" "q"
             [Some (snat, g_send "s" "r" [Some (sbool, g_end)]);
              Some (snat, g_send "s" "r" [None; Some (sbool, g_end)])])]).
      split. pfold. constructor. constructor; try easy.
      right. exists snat. exists (g_send "p" "q"
       [Some (snat, g_send "s" "r" [Some (sbool, g_end)]);
        Some (snat, g_send "s" "r" [None; Some (sbool, g_end)])]). exists (gtt_send "p" "q"
       [Some (snat, gtt_send "s" "r" [Some (sbool, gtt_end)]);
        Some (snat, gtt_send "s" "r" [None; Some (sbool, gtt_end)])]).
       split. easy. split. easy. left.
       pfold. constructor. constructor; try easy. 
       right. exists snat. exists (g_send "s" "r" [Some (sbool, g_end)]). exists (gtt_send "s" "r" [Some (sbool, gtt_end)]).
       split. easy. split. easy. left. pfold. constructor. constructor; try easy.
       right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
       left. pfold. constructor. constructor.
       right. exists snat. exists (g_send "s" "r" [None; Some (sbool, g_end)]). exists (gtt_send "s" "r" [None; Some (sbool, gtt_end)]).
       split. easy. split. easy. left. pfold. constructor. constructor; try easy. left. easy. constructor; try easy.
       right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
       left. pfold. constructor. constructor.
       apply pa_sendr with (n := 0) (s := snat) (g := g_send "p" "q"
           [Some (snat, g_send "s" "r" [Some (sbool, g_end)]);
            Some (snat, g_send "s" "r" [None; Some (sbool, g_end)])]); try easy.
       constructor.
  - constructor; try easy. right. exists snat. exists G2. split. easy.
    unfold G2. unfold G3. unfold isgPartsC. split. 
    - exists (g_send "p" "q"
       [Some
          (snat,
           g_send "r" "s"
             [Some
                (snat,
                 g_send "s" "r"
                   [Some (sbool, g_end); Some (sbool, g_end)])]);
        Some
          (snat,
           g_send "r" "s"
             [Some
                (snat,
                 g_send "s" "r"
                   [Some (sbool, g_end); Some (sbool, g_end)])])]). split.
      pfold. constructor. constructor; try easy. right.
      exists snat. exists (g_send "r" "s"
       [Some
          (snat, g_send "s" "r" [Some (sbool, g_end); Some (sbool, g_end)])]). exists (gtt_send "r" "s"
       [Some
          (snat,
           gtt_send "s" "r" [Some (sbool, gtt_end); Some (sbool, gtt_end)])]).
      split. easy. split. easy.
      left. pfold. constructor. constructor; try easy. right. exists snat. exists (g_send "s" "r" [Some (sbool, g_end); Some (sbool, g_end)]).
      exists (gtt_send "s" "r" [Some (sbool, gtt_end); Some (sbool, gtt_end)]). split. easy. split. easy.
      left. pfold. constructor; try easy. constructor; try easy.
      right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
      left. pfold. constructor. constructor.
      right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
      left. pfold. constructor. constructor.
      constructor; try easy. right.
      exists snat. exists (g_send "r" "s"
       [Some
          (snat, g_send "s" "r" [Some (sbool, g_end); Some (sbool, g_end)])]). exists (gtt_send "r" "s"
     [Some
        (snat,
         gtt_send "s" "r" [Some (sbool, gtt_end); Some (sbool, gtt_end)])]).
       split. easy. split. easy. left. pfold. constructor. constructor; try easy.
       right. exists snat. exists (g_send "s" "r" [Some (sbool, g_end); Some (sbool, g_end)]). exists (gtt_send "s" "r" [Some (sbool, gtt_end); Some (sbool, gtt_end)]).
      split. easy. split. easy. 
      left. pfold. constructor. constructor; try easy.
      right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
      left. pfold. constructor. constructor.
      right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
      left. pfold. constructor. constructor.
      constructor.
    - exists (g_send "p" "q"
       [Some
          (snat,
           g_send "r" "s"
             [Some
                (snat,
                 g_send "s" "r"
                   [Some (sbool, g_end); Some (sbool, g_end)])]);
        Some
          (snat,
           g_send "r" "s"
             [Some
                (snat,
                 g_send "s" "r"
                   [Some (sbool, g_end); Some (sbool, g_end)])])]). split.
      pfold. constructor. constructor; try easy. right.
      exists snat. exists (g_send "r" "s"
       [Some
          (snat, g_send "s" "r" [Some (sbool, g_end); Some (sbool, g_end)])]). exists (gtt_send "r" "s"
       [Some
          (snat,
           gtt_send "s" "r" [Some (sbool, gtt_end); Some (sbool, gtt_end)])]).
      split. easy. split. easy.
      left. pfold. constructor. constructor; try easy. right. exists snat. exists (g_send "s" "r" [Some (sbool, g_end); Some (sbool, g_end)]).
      exists (gtt_send "s" "r" [Some (sbool, gtt_end); Some (sbool, gtt_end)]). split. easy. split. easy.
      left. pfold. constructor; try easy. constructor; try easy.
      right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
      left. pfold. constructor. constructor.
      right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
      left. pfold. constructor. constructor.
      constructor; try easy. right.
      exists snat. exists (g_send "r" "s"
       [Some
          (snat, g_send "s" "r" [Some (sbool, g_end); Some (sbool, g_end)])]). exists (gtt_send "r" "s"
     [Some
        (snat,
         gtt_send "s" "r" [Some (sbool, gtt_end); Some (sbool, gtt_end)])]).
       split. easy. split. easy. left. pfold. constructor. constructor; try easy.
       right. exists snat. exists (g_send "s" "r" [Some (sbool, g_end); Some (sbool, g_end)]). exists (gtt_send "s" "r" [Some (sbool, gtt_end); Some (sbool, gtt_end)]).
      split. easy. split. easy. 
      left. pfold. constructor. constructor; try easy.
      right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
      left. pfold. constructor. constructor.
      right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
      left. pfold. constructor. constructor.
      constructor.
  - constructor; try easy. right. exists snat. exists G1. exists (gtt_send "r" "s"
       [Some (snat, gtt_send "s" "r" [Some (sbool, gtt_end)])]). split. easy. split. easy.
    left. pfold. constructor; try easy.
    - constructor; try easy. right. exists snat. exists (gtt_send "p" "q"
       [Some (snat, gtt_send "s" "r" [Some (sbool, gtt_end)]);
        Some (snat, gtt_send "s" "r" [None; Some (sbool, gtt_end)])]). 
      split. easy.
      unfold isgPartsC.
      split.
      - exists (g_send "p" "q"
       [Some (snat, g_send "s" "r" [Some (sbool, g_end)]);
        Some (snat, g_send "s" "r" [None; Some (sbool, g_end)])]).
        split. pfold. constructor. constructor; try easy.
        right. exists snat. exists (g_send "s" "r" [Some (sbool, g_end)]). exists (gtt_send "s" "r" [Some (sbool, gtt_end)]).
        split. easy. split. easy. left. pfold. constructor. constructor; try easy.
      right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy. left. pfold. constructor. 
       constructor; try easy. right. exists snat. exists (g_send "s" "r" [None; Some (sbool, g_end)]). exists (gtt_send "s" "r" [None; Some (sbool, gtt_end)]). split. easy. split. easy. left. pfold. constructor. constructor. left. easy.
       constructor; try easy.
       right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy. left. pfold. constructor. 
       constructor.
     - exists (g_send "p" "q"
       [Some (snat, g_send "s" "r" [Some (sbool, g_end)]);
        Some (snat, g_send "s" "r" [None; Some (sbool, g_end)])]).
        split. pfold. constructor. constructor; try easy.
        right. exists snat. exists (g_send "s" "r" [Some (sbool, g_end)]). exists (gtt_send "s" "r" [Some (sbool, gtt_end)]).
        split. easy. split. easy. left. pfold. constructor. constructor; try easy.
      right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy. left. pfold. constructor. 
       constructor; try easy. right. exists snat. exists (g_send "s" "r" [None; Some (sbool, g_end)]). exists (gtt_send "s" "r" [None; Some (sbool, gtt_end)]). split. easy. split. easy. left. pfold. constructor. constructor. left. easy.
       constructor; try easy.
       right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy. left. pfold. constructor. 
       constructor.
    - constructor; try easy. right. exists snat. exists (gtt_send "p" "q"
       [Some (snat, gtt_send "s" "r" [Some (sbool, gtt_end)]);
        Some (snat, gtt_send "s" "r" [None; Some (sbool, gtt_end)])]). 
      exists (gtt_send "s" "r" [Some (sbool, gtt_end)]). split. easy. split. easy.
      left. pfold. apply steq with (s := snat); try easy.
    - constructor; try easy. right. exists snat. exists G2. exists G3. split. easy. split. easy.
      unfold G2. unfold G3.
      left. pfold. apply steq with (s := snat); try easy.
Qed.

Example Gex3 : forall T, projectionC (gtt_send "s" "s'" [Some(snat, gtt_send "r" "s" [Some(snat, gtt_send "s" "r" [Some(sbool, gtt_end)])]); Some(snat, G3)]) "r" T -> False.
Proof.
  intros.
  pinversion H; try easy. subst. apply H0. clear H0.
    unfold G3.
    unfold isgPartsC.
    exists (g_send "s" "s'"
     [Some
        (snat,
         g_send "r" "s"
           [Some (snat, g_send "s" "r" [Some (sbool, g_end)])]);
      Some
        (snat,
         g_send "r" "s"
           [Some
              (snat,
               g_send "s" "r"
                 [Some (sbool, g_end); Some (sbool, g_end)])])]).
    split. pfold. constructor; try easy. constructor; try easy.
    - right. exists snat. exists (g_send "r" "s" [Some (snat, g_send "s" "r" [Some (sbool, g_end)])]). exists (gtt_send "r" "s"
       [Some (snat, gtt_send "s" "r" [Some (sbool, gtt_end)])]).
      split. easy. split. easy. left. pfold. constructor; try easy. constructor; try easy.
      right. exists snat. exists (g_send "s" "r" [Some (sbool, g_end)]). exists (gtt_send "s" "r" [Some (sbool, gtt_end)]).
      split. easy. split. easy. left. pfold. constructor. constructor; try easy.
      right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
      left. pfold. constructor. constructor.
    - right. exists snat. exists (g_send "r" "s"
       [Some
          (snat, g_send "s" "r" [Some (sbool, g_end); Some (sbool, g_end)])]). exists (gtt_send "r" "s"
       [Some
          (snat,
           gtt_send "s" "r" [Some (sbool, gtt_end); Some (sbool, gtt_end)])]).
      split. easy. split. easy. left. pfold. constructor; try easy. constructor; try easy.
      right. exists snat. exists (g_send "s" "r" [Some (sbool, g_end); Some (sbool, g_end)]). exists (gtt_send "s" "r" [Some (sbool, gtt_end); Some (sbool, gtt_end)]).
      split. easy. split. easy. 
      left. pfold. constructor. constructor; try easy.
      right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
      left. pfold. constructor. constructor.
      right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
      left. pfold. constructor. constructor.
      easy.
      apply pa_sendr with (n := 0) (s := snat) (g := g_send "r" "s" [Some (snat, g_send "s" "r" [Some (sbool, g_end)])]); intros; try easy.
      constructor.
  - subst. destruct ys; try easy.
    inversion H8. subst. clear H8. destruct ys; try easy. inversion H10. subst. clear H10. destruct ys; try easy. clear H11.
    clear H3 H4 H5.
    destruct H6; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. inversion H0. subst.
    clear H0.
    destruct H7; try easy. destruct H0. destruct H0. destruct H0. destruct H0. destruct H1. inversion H0. subst.
    clear H0.
    destruct H2; try easy. destruct H3; try easy.
    unfold G3 in H1.
    
    pinversion H0; try easy. subst.
    - apply H2.
      unfold isgPartsC.
      exists (g_send "r" "s" [Some (snat, g_send "s" "r" [Some (sbool, g_end)])]).
      split. pfold. constructor; try easy. constructor; try easy.
      right. exists snat. exists (g_send "s" "r" [Some (sbool, g_end)]). exists (gtt_send "s" "r" [Some (sbool, gtt_end)]).
      split. easy. split. easy. left. pfold. constructor; try easy.
      constructor; try easy. right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
      left. pfold. constructor. constructor.
    - subst. clear H4.
      destruct ys; try easy. inversion H7. subst. destruct ys; try easy. clear H8 H7.
      destruct H5; try easy. destruct H2. destruct H2. destruct H2. destruct H2. destruct H3.
      inversion H2. subst. clear H2.
      destruct H4; try easy.
      pinversion H2; try easy. subst.
      apply H3.
      - unfold isgPartsC.
        exists (g_send "s" "r" [Some (sbool, g_end)]). split.
        - pfold. constructor; try easy. constructor; try easy. right. exists sbool. exists g_end. exists gtt_end.
          split. easy. split. easy. left. pfold. constructor.
        - constructor; try easy.
      - subst. clear H5. destruct ys; try easy. inversion H8. subst. clear H8. destruct ys; try easy. clear H10.
        destruct H6; try easy. destruct H3. destruct H3. destruct H3. destruct H3. destruct H4. inversion H3. subst.
        clear H3.
        destruct H5; try easy.
        pinversion H3; try easy. subst. clear H4.
      pinversion H1; try easy. subst. 
      apply H4.
      - unfold isgPartsC.
        exists (g_send "r" "s"
       [Some
          (snat,
           g_send "s" "r" [Some (sbool, g_end); Some (sbool, g_end)])]).
           split.
           - pfold. constructor. constructor; try easy. right. exists snat. exists (g_send "s" "r" [Some (sbool, g_end); Some (sbool, g_end)]).
             exists (gtt_send "s" "r" [Some (sbool, gtt_end); Some (sbool, gtt_end)]).
             split. easy. split. easy. 
             left. pfold. constructor; try easy. constructor; try easy.
             right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy. left. pfold. constructor.
             constructor; try easy.
             right. exists sbool. exists g_end. exists gtt_end. split. easy. split. easy.
             left. pfold. constructor.
           - constructor; try easy.
      subst. destruct ys; try easy. inversion H10. subst. clear H10. destruct ys; try easy. clear H12.
      destruct H8; try easy. destruct H4. destruct H4. destruct H4. destruct H4. destruct H5. inversion H4. subst. clear H4.
      destruct H7; try easy. clear H6.
      pinversion H4; try easy. subst.
      apply H5.
      - unfold isgPartsC.
        exists (g_send "s" "r" [Some (sbool, g_end); Some (sbool, g_end)]). split.
        - pfold. constructor. constructor; try easy. right. exists sbool. exists g_end. exists gtt_end. split. easy.
          split. easy. left. pfold. constructor.
          constructor; try easy. right. exists sbool. exists g_end. exists gtt_end.
          split. easy. split. easy. left. pfold. constructor.
        - constructor.
      subst.
      destruct ys; try easy. inversion H11. subst. clear H11. destruct ys; try easy. inversion H13. subst. clear H13.
      destruct ys; try easy. clear H14.
      destruct H10; try easy. destruct H5. destruct H5. destruct H5. destruct H5. destruct H6. inversion H5. subst.
      destruct H11; try easy. destruct H6. destruct H6. destruct H6. destruct H6. destruct H10. inversion H6. subst.
      clear H6 H5. destruct H8; try easy. destruct H11; try easy.
      pinversion H5; try easy. subst.
      pinversion H6; try easy. subst. clear H8 H10.
      inversion H9; try easy. subst.
      inversion H12; try easy. subst. clear H12.
      inversion H13; try easy.
    apply proj_mon. apply proj_mon. apply proj_mon. apply proj_mon.
    apply proj_mon. apply proj_mon. apply proj_mon. apply proj_mon.
Qed.
      
Lemma merge_bad : exists G G' T r p q l, projectionC G r T /\ gttstepC G G' p q l /\ (forall T', projectionC G' r T' -> False).
Proof.
  exists G. exists (gtt_send "s" "s'" [Some(snat, gtt_send "r" "s" [Some(snat, gtt_send "s" "r" [Some(sbool, gtt_end)])]); Some(snat, G3)]).
  exists (ltt_send "s" [Some(snat, ltt_recv "s" [Some(sbool, ltt_end); Some(sbool, ltt_end)])]).  
  exists "r"%string. exists "p"%string. exists "q"%string. exists 0.
  split. apply Gex1. split. apply Gex2. apply Gex3.
Qed.


CoFixpoint Ga : gtt := gtt_send "Alice" "Bob" [Some (snat, Ga)].

Example Grec : gttTC (g_rec (g_send "Alice" "Bob" [Some (snat, g_var 0)])) Ga.
Proof.
  pcofix CIH.
  pfold. apply gttT_rec with (Q := g_send "Alice" "Bob" [(Some (snat, (g_rec (g_send "Alice" "Bob" [Some (snat, g_var 0)]))))]).
  constructor. constructor. right.
  exists snat. exists (g_var 0). exists (g_rec (g_send "Alice" "Bob" [Some (snat, g_var 0)])).
  split; try easy. split; try easy. constructor. easy.
  
  rewrite (gtt_eq Ga). simpl.
  left. pfold.
  constructor. constructor. right. exists snat. exists (g_rec (g_send "Alice" "Bob" [Some (snat, g_var 0)])). exists Ga.
  split; try easy. split; try easy.
  right. easy. easy.
Qed.
