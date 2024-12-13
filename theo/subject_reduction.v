From SST Require Export src.expressions process.processes process.typecheck type.global type.local process.beta process.sessions process.inversion type.isomorphism type.projection type.proj_part type.wfgC_after_step process.subject_reduction_helper.
Require Import List String Datatypes ZArith Relations PeanoNat.
Open Scope list_scope.
From Paco Require Import paco pacotac.
Require Import Setoid Morphisms Coq.Program.Basics.
Require Import Coq.Init.Datatypes.

Inductive multiC : relation gtt := 
  | multiC_refl : forall G, multiC G G
  | multiC_step : forall G1 G2 G3 p q n, gttstepC G1 G2 p q n -> multiC G2 G3 -> multiC G1 G3.

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
    - specialize(inv_proc_recv q xs (p_recv q xs) nil nil T H5 (eq_refl (p_recv q xs))); intros. 
      destruct H8. destruct H8. destruct H10. destruct H11.
    - specialize(inv_proc_send p l e Q (p_send p l e Q) nil nil T' H7 (eq_refl (p_send p l e Q))); intros.
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
    - specialize(_3_19_3_helper M q p G G' l LP LQ S LT x (x0, x1)); intros.
      inversion H4. subst. inversion H30. subst.
      specialize(Classical_Prop.not_or_and (q = p) (In p (flattenT M)) H29); intros. destruct H27.
      apply H26; try easy.

  (* T-COND *)
  inversion H0. subst. inversion H4. subst. clear H4. inversion H7. subst. clear H7.
  destruct H5. destruct H4. destruct H5 as (H5, Ha).
  specialize(inv_proc_ite (p_ite e P Q) e P Q x nil nil H5 (eq_refl (p_ite e P Q))); intros.
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
  specialize(inv_proc_ite (p_ite e P Q) e P Q x nil nil H5 (eq_refl (p_ite e P Q))); intros.
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
    - specialize(inv_proc_recv q xs (p_recv q xs) nil nil T Hb (eq_refl (p_recv q xs))); intros. 
      destruct H5 as (STT,(Hg,(Hh,(Hi,Hj)))).
    - specialize(inv_proc_send p l e Q (p_send p l e Q) nil nil T1 He (eq_refl (p_send p l e Q))); intros.
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
  specialize(inv_proc_ite (p_ite e P Q) e P Q x nil nil H5 (eq_refl (p_ite e P Q))); intros.
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
  specialize(inv_proc_ite (p_ite e P Q) e P Q x nil nil H5 (eq_refl (p_ite e P Q))); intros.
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