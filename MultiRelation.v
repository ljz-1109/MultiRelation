Require PropExtensionality FunctionalExtensionality.

Section Specification.
  Definition MultiRelationSpec (IT : Type) (OT : Type) := IT -> (OT -> Prop) -> Prop.
  Definition RelationSpec (IT : Type) (OT : Type) := IT -> OT -> Prop.

  Definition extensionality {IT OT} (R : MultiRelationSpec IT OT) : forall s P Q, (forall t, P t <-> Q t) -> R s P -> R s Q.
  Proof.
    intros.
    erewrite FunctionalExtensionality.functional_extensionality; try eassumption.
    intros. symmetry. eapply PropExtensionality.propositional_extensionality. eauto.
  Qed.

  Section MultiRelation.
    Context {IT OT : Type}.

    Section Properties.
      Section Unary.
        Context (R : MultiRelationSpec IT OT).

        Definition extensional : Prop := forall s P Q, (forall t, P t <-> Q t) -> R s P -> R s Q.
        Definition upclosed : Prop := forall s P Q, (forall t, P t -> Q t) -> R s P -> R s Q.
        Definition proper : Prop := forall s, exists P, R s P.
        Definition total : Prop := forall s P, R s P -> exists t, P t.

        Definition multiplicative : Prop := forall s MP, (exists P, MP P) -> (forall P, MP P -> R s P) -> R s (fun t => forall P, MP P -> P t). 
        Definition additive : Prop := forall s MP, (exists P, MP P) -> R s (fun t => exists P, MP P /\ P t) -> exists P, MP P /\ R s P. 

        Definition angelic : Prop := upclosed /\ additive /\ total.
        Definition demonic : Prop := upclosed /\ multiplicative /\ proper.
        Definition totalic : Prop := upclosed /\ multiplicative /\ total.

        Definition multiplicative2 := forall s P Q, R s P -> R s Q -> R s (fun x => P x /\ Q x).

      End Unary.

      Section Binary.
        Context (R Q : MultiRelationSpec IT OT).
        Context (Equiv : forall s P, R s P <-> Q s P).

        Definition upclosed_extensionality : upclosed R -> upclosed Q.
        Proof. cbv; firstorder. eapply Equiv. eapply H; try eassumption. firstorder. Qed.

        Definition proper_extensionality : proper R -> proper Q.
        Proof. cbv; firstorder. specialize (H s). firstorder. Qed.
        
        Definition total_extensionality : total R -> total Q.
        Proof. cbv; firstorder. Qed.

        Definition multiplicative_extensionality : multiplicative R -> multiplicative Q.
        Proof. cbv; firstorder. eapply Equiv. eapply H; firstorder. Qed.

        Definition additive_extensionality : additive R -> additive Q.
        Proof. cbv; firstorder. eapply Equiv in H1. specialize (H s MP (ex_intro _ _ H0) H1). firstorder. Qed.

        Local Hint Resolve upclosed_extensionality proper_extensionality total_extensionality multiplicative_extensionality additive_extensionality : extensionality.

        Definition angelic_extensionality : angelic R -> angelic Q.
        Proof. cbv [angelic]. intros [? [? ?]]. repeat split; eauto with extensionality. Qed.

        Definition demonic_extensionality : demonic R -> demonic Q.
        Proof. cbv [demonic]. intros [? [? ?]]. repeat split; eauto with extensionality. Qed.

        Definition totalic_extensionality : totalic R -> totalic Q.
        Proof. cbv [totalic]. intros [? [? ?]]. repeat split; eauto with extensionality. Qed.

      End Binary.

      Lemma multiplicative3 MR : upclosed MR -> multiplicative MR -> multiplicative2 MR.
      Proof.
        cbv. intros.
        assert (forall MR' P, MR' s P -> (forall Q, MR' s Q -> MR s Q) -> MR s P ).
        firstorder.
        eapply H3.
        instantiate (1 := (fun s P => forall t, (forall Q, MR s Q -> Q t) -> P t) ).
        firstorder. cbn. intros. eapply H. eapply H4. eapply H0; firstorder.
      Qed.

      
    End Properties.

    (* family of total additive up-closed binary multirelations *)
    Section AngelicNondeterminism.

      Definition toAngelic (R : RelationSpec IT OT) : MultiRelationSpec IT OT :=
        fun input P => (exists output, R input output /\ P output).

      Lemma toAngelicIsAngelic r : angelic (toAngelic r).
      Proof. firstorder. Qed.

      Definition AngelicEquivalence (R : RelationSpec IT OT) (mr : MultiRelationSpec IT OT) : Prop := 
        forall input P, mr input P <-> (exists output, R input output /\ P output). 

      Definition ofAngelic (r : MultiRelationSpec IT OT) : RelationSpec IT OT :=
        (* fun input output => ((forall P, r input P -> (P output -> False)) -> False). *)
        (* fun input output => ((forall P, ((r input P) -> False) -> (P output -> False) )). *)
        fun input output => forall P, P output -> (r input P).
        (* fun input output => ((exists P, ((r input P) -> False) /\ (P output)) -> False). *)
        (* fun input output => ((forall P, ((r input (fun x => P x -> False))) \/ (P output))). *)

      Lemma toAngelic_ofAngelic (R : RelationSpec IT OT) : forall input output, 
        ofAngelic (toAngelic R) input output <-> R input output.
      Proof. intros. firstorder. cbv in *. specialize (H (fun x => x = output) eq_refl). firstorder. subst; eauto. Qed.

      Lemma ofAngelic_toAngelic (R : MultiRelationSpec IT OT) : forall input P, 
        angelic R -> 
        (toAngelic (ofAngelic R) input P <-> R input P).
      Proof. 
        intros. firstorder. cbv. 
        cbv [additive upclosed] in *.
        
        specialize (H0 input (fun Q => exists x, P x /\ (forall y, Q y <-> y = x))). cbn in H0. 
        eapply H in H2. eapply H0 in H2. firstorder. cbn. pose proof (H1 _ _ H3). destruct H5 as [t H5]. eapply H4 in H5; subst. eexists x0. cbn. firstorder. 
        eapply H; try eassumption. intros. eapply H4 in H6. subst. eauto. 
        eapply H1 in H2. firstorder.
        intros. cbn. eexists (fun x' => x' = t). firstorder.
      Qed.

    End AngelicNondeterminism.

    (* family of proper multiplicative up-closed binary multirelations *)
    Section DemonicNondeterminism.

      Definition toDemonic (r : RelationSpec IT OT) : MultiRelationSpec IT OT :=
        fun input P => (forall output, r input output -> P output).

      Lemma toDemonicIsDemonic r : demonic (toDemonic r).
      Proof. repeat split; try firstorder. cbv. intros.  eexists (fun _ => True). eauto. Qed.

      Definition DemonicEquivalence (r : RelationSpec IT OT) (mr : MultiRelationSpec IT OT) : Prop := 
        forall input P, mr input P <-> (forall output, r input output -> P output).

      Definition ofDemonic (r : MultiRelationSpec IT OT) : RelationSpec IT OT :=
        fun input output => (forall P, r input P -> P output).

      Lemma toDenomic_ofDenomic (R : RelationSpec IT OT) : forall input output, 
        ofDemonic (toDemonic R) input output <-> R input output.
      Proof. intros. firstorder. cbv in *. specialize (H (fun x => R input x) ). firstorder. Qed.

      Lemma ofDenomic_toDenomic (R : MultiRelationSpec IT OT) : forall input P, 
        demonic R -> 
        (toDemonic (ofDemonic R) input P <-> R input P).
      Proof. intros. firstorder. cbv in *. eapply H. eapply H2. firstorder. Qed.
      
    End DemonicNondeterminism.

    (* family of total multiplicative up-closed binary multirelations *)
    Section TotalNondeterminism.

      Definition toTotal (r : RelationSpec IT OT) : MultiRelationSpec IT OT :=
        fun input P => (forall output, r input output -> P output) /\ (exists output, r input output).

      Lemma toTotalIsTotal r : totalic (toTotal r).
      Proof. repeat split; try firstorder. Qed.

      Definition TotalicEquivalence (r : RelationSpec IT OT) (mr : MultiRelationSpec IT OT) : Prop := 
        forall input P, mr input P <-> ((forall output, r input output -> P output) /\ (exists output, r input output)).

      Definition ofTotal (r : MultiRelationSpec IT OT) : RelationSpec IT OT :=
        fun input output => (forall P, r input P -> P output) /\ (exists P, r input P).

      Lemma toTotal_ofTotal (R : RelationSpec IT OT) : forall input output, 
        ofTotal (toTotal R) input output <-> R input output.
      Proof. intros. cbv. firstorder.   specialize (H (fun x => R input x ) ). cbn in *. eapply H. firstorder. 
        exists (fun x => R input x). firstorder.
      Qed.

      Lemma ofTotal_toTotal (R : MultiRelationSpec IT OT) : forall input P, 
        totalic R -> 
        (toTotal (ofTotal R) input P <-> R input P).
      Proof. intros. firstorder; pose proof (multiplicative3 _ H H0). cbv in *. 
        eapply H.
        eapply H2.
        assert (R input (fun output : OT => (forall P0 : OT -> Prop, R input P0 -> P0 output))).
        { 
          eapply H0; firstorder.
        }
        assert (R input (fun output : OT => (exists P0 : OT -> Prop, R input P0))).
        {
          eapply H; try eassumption. cbn; intros. firstorder. 
        }
        eapply H5; firstorder.

        assert (R input (fun output : OT => (forall P0 : OT -> Prop, R input P0 -> P0 output))).
        { 
          eapply H0; firstorder.
        }
        assert (R input (fun output : OT => (exists P0 : OT -> Prop, R input P0))).
        {
          eapply H; try eassumption. cbn; intros. firstorder. 
        }
        cbv in *. 
        eapply H1 with (s := input).
        eapply H3; firstorder.
      Qed.

    End TotalNondeterminism.

  End MultiRelation.

  Section Identity.

    Context {T : Type}.
    Definition identity : MultiRelationSpec T T := fun s P => P s.

    Lemma identity_upclosed : upclosed identity.
    Proof. cbv; firstorder. Qed.

    Lemma identity_proper : proper identity.
    Proof. cbv; firstorder. eexists (fun _ => True). eauto. Qed.

    Lemma identity_total : total identity.
    Proof. cbv; firstorder. Qed.

    Lemma identity_multiplicative : multiplicative identity.
    Proof. cbv; firstorder. Qed.

    Lemma identity_additive : additive identity.
    Proof. cbv; firstorder. Qed.

    Local Hint Resolve identity_upclosed identity_proper identity_total identity_multiplicative identity_additive : identity.

    Lemma identity_angelic : angelic identity.
    Proof. repeat split; eauto with identity. Qed.

    Lemma identity_demonic : demonic identity.
    Proof. repeat split; eauto with identity. Qed.

    Lemma identity_totalic : totalic identity.
    Proof. repeat split; eauto with identity. Qed.

  End Identity.

  Section Bounds.

    Context {IT OT : Type}.
    
    Definition top : MultiRelationSpec IT OT := fun s P => True.

    Lemma top_upclosed : upclosed top.
    Proof. cbv; firstorder. Qed.

    Lemma top_proper : proper top.
    Proof. cbv; firstorder. refine (fun _ => True). Qed.

    (* Lemma top_total : total top.
    Proof. cbv; firstorder. eexists () Qed. *)

    Lemma top_multiplicative : multiplicative top.
    Proof. cbv; firstorder. Qed.

    Lemma top_additive : additive top.
    Proof. cbv; firstorder. Qed.

    Definition bot : MultiRelationSpec IT OT := fun s P => False.

    Lemma bot_upclosed : upclosed bot.
    Proof. cbv; firstorder. Qed.

    (* Lemma bot_proper : proper bot.
    Proof. cbv; firstorder. refine (fun _ => True). Qed. *)

    Lemma bot_total : total bot.
    Proof. cbv; firstorder. Qed.

    Lemma bot_multiplicative : multiplicative bot.
    Proof. cbv; firstorder. Qed.

    Lemma bot_additive : additive bot.
    Proof. cbv; firstorder. Qed.

    (* Local Hint Resolve identity_upclosed identity_proper identity_total identity_multiplicative identity_additive : identity.

    Lemma identity_angelic : angelic identity.
    Proof. repeat split; eauto with identity. Qed.

    Lemma identity_demonic : demonic identity.
    Proof. repeat split; eauto with identity. Qed.

    Lemma identity_totalic : totalic identity.
    Proof. repeat split; eauto with identity. Qed. *)

  End Bounds.

  Section Composition.
    Context {IT MT OT : Type}.
    Context (R : MultiRelationSpec IT MT).
    Context (Q : MultiRelationSpec MT OT).

    Definition composition : MultiRelationSpec IT OT := fun it ot => R it (fun mt => Q mt ot).
    Definition strong_composition : MultiRelationSpec IT OT := fun it ot => exists T, R it T /\ (forall mt, T mt <-> Q mt ot).
    Definition weak_composition : MultiRelationSpec IT OT := fun it ot => exists T, R it T /\ (forall mt, T mt -> Q mt ot).

    Definition composition_equivalence `{upclosed R} {it P} : composition it P <-> weak_composition it P.
    Proof.
      cbv; split; firstorder.
    Qed.

    Definition composition_upclosed `{upclosed_R : upclosed R} `{upclosed_Q : upclosed Q} : upclosed composition.
    Proof.
      cbv in *; firstorder. eapply upclosed_R; try eassumption. cbn; intros. eauto.
    Qed.

    Definition composition_proper `{upclosed_R : upclosed R} `{upclosed_Q : upclosed Q} `{proper_R : proper R} `{proper_Q : proper Q} : proper composition.
    Proof.
      cbv in *; firstorder. 
      specialize (proper_R s). destruct proper_R.
      eexists (fun _ => True). eapply upclosed_R; try eassumption. intros.
      specialize (proper_Q t). destruct proper_Q. eauto. 
    Qed.

    Definition composition_total `{total_R : total R} `{total_Q : total Q} : total composition.
    Proof. cbv in *; firstorder. Qed.

    Definition composition_multiplicative `{upclosed_R : upclosed R} `{upclosed_Q : upclosed Q} `{multiplicative_R : multiplicative R} `{multiplicative_Q : multiplicative Q} : multiplicative composition.
    Proof. 
      cbv in *; firstorder.
      eapply upclosed_R.
      2:{
        eapply multiplicative_R with (MP := R s). specialize (H0 x H). eexists; eassumption. eauto.
      } 
      cbn; intros. 
      eapply upclosed_Q.
      2:{
        eapply multiplicative_Q with (MP := Q t). eapply H1 in H0; eauto.  eauto.
      }
      cbn; intros. firstorder.
    Qed.

    Definition composition_additive `{upclosed_R : upclosed R} `{additive_R : additive R} `{additive_Q : additive Q} : additive composition.
    Proof. 
      cbv in *; firstorder.
      eapply upclosed_R with (Q := fun s => exists P : MT -> Prop, (fun P' => exists P'' : OT -> Prop, MP P'' /\ (forall t, P' t -> Q t P'') ) P /\ P s) in H0; eauto.
      eapply additive_R in H0; firstorder. eexists (fun t => Q t x). firstorder.
      intros. eapply additive_Q in H1; firstorder.
      eexists (fun t => Q t x0). split; eauto.
    Qed.

    Local Hint Resolve composition_upclosed composition_proper composition_total composition_multiplicative composition_additive : composition.
    
    Definition composition_angelic `{angelic_R : angelic R} `{angelic_Q : angelic Q} : angelic composition.
    Proof.
      cbv [angelic] in *. destruct angelic_R as [? [? ?]]. destruct angelic_Q as [? [? ?]].
      repeat split; eauto with composition.
    Qed.

    Definition composition_demonic `{demonic_R : demonic R} `{demonic_Q : demonic Q} : demonic composition.
    Proof.
      cbv [demonic] in *. destruct demonic_R as [? [? ?]]. destruct demonic_Q as [? [? ?]].
      repeat split; eauto with composition.
    Qed.

    Definition composition_totalic `{totalic_R : totalic R} `{totalic_Q : totalic Q} : totalic composition.
    Proof.
      cbv [totalic] in *. destruct totalic_R as [? [? ?]]. destruct totalic_Q as [? [? ?]].
      repeat split; eauto with composition.
    Qed.

  End Composition.

  Section Composition.
    Context {IT MT OT : Type}.
    Context (f : IT -> MT).
    Context (R : MultiRelationSpec MT OT).

    Definition fcomposition : MultiRelationSpec IT OT := fun it ot => R (f it) ot.

    Definition fcomposition_upclosed `{upclosed_R : upclosed R} : upclosed fcomposition.
    Proof. cbv in *; firstorder. Qed.

    Definition fcomposition_proper  `{proper_R : proper R} : proper fcomposition.
    Proof. cbv in *; firstorder. Qed.

    Definition fcomposition_total `{total_R : total R} : total fcomposition.
    Proof. cbv in *; firstorder. Qed.

    Definition fcomposition_multiplicative `{multiplicative_R : multiplicative R} : multiplicative fcomposition.
    Proof. cbv in *; firstorder. Qed.

    Definition fcomposition_additive `{additive_R : additive R} : additive fcomposition.
    Proof. cbv in *; firstorder. Qed.

    Local Hint Resolve fcomposition_upclosed fcomposition_proper fcomposition_total fcomposition_multiplicative fcomposition_additive : fcomposition.

    Definition fcomposition_angelic `{angelic_R : angelic R} : angelic fcomposition.
    Proof. cbv [angelic] in *. destruct angelic_R as [? [? ?]]. repeat split; eauto with fcomposition. Qed.

    Definition fcomposition_demonic `{demonic_R : demonic R} : demonic fcomposition.
    Proof. cbv [demonic] in *. destruct demonic_R as [? [? ?]]. repeat split; eauto with fcomposition. Qed.

    Definition fcomposition_totalic `{totalic_R : totalic R} : totalic fcomposition.
    Proof. cbv [totalic] in *. destruct totalic_R as [? [? ?]]. repeat split; eauto with fcomposition. Qed.
    
  End Composition.

  Section Composition.
    Context {IT MT OT : Type}.
    Context (g : MT -> OT).
    Context (R : MultiRelationSpec IT MT).

    Definition gcomposition : MultiRelationSpec IT OT := fun it ot => R it (fun mt => ot (g mt)).

    Definition gcomposition_upclosed `{upclosed_R : upclosed R} : upclosed gcomposition.
    Proof. cbv in *; firstorder. Qed.

    Definition gcomposition_proper `{upclosed_R : upclosed R} `{proper_R : proper R} : proper gcomposition.
    Proof.
      cbv in *; firstorder. specialize (proper_R s). destruct proper_R.  
      eexists (fun _ => True). firstorder. 
    Qed.

    Definition gcomposition_total `{total_R : total R} : total gcomposition.
    Proof. cbv in *. firstorder. Qed.
    
    Definition gcomposition_multiplicative `{upclosed_R : upclosed R} `{multiplicative_R : multiplicative R} : multiplicative gcomposition.
    Proof.
      cbv in *; firstorder. 
      specialize (multiplicative_R s (fun P => exists Q, MP Q /\ (forall t, Q (g t) -> P t))).
      eapply upclosed_R. 2:{ 
        eapply multiplicative_R; firstorder. 
        eexists (fun m => x (g m)). firstorder. 
      }
      firstorder. cbn in *. eapply H1.  firstorder.
    Qed.

    Definition gcomposition_additive `{upclosed_R : upclosed R} `{additive_R : additive R} : additive gcomposition.
    Proof.
      cbv in *. intros; firstorder.
      specialize (additive_R s (fun P => exists Q, MP Q /\ (forall t,  P t -> Q (g t) ) )).
      match type of additive_R with 
      | ?H -> _ => let H' := fresh "H" in assert (H) as H'; [ | specialize (additive_R H'); clear H' ]
      end.
      eexists (fun t => x (g t)). firstorder.
      match type of additive_R with 
      | (R s ?t) -> _ => eapply upclosed_R with ( Q := t) in H0
      end.
      firstorder.
      firstorder. 
      eexists (fun t => x0 (g t)). firstorder.
    Qed.

    Local Hint Resolve gcomposition_upclosed gcomposition_proper gcomposition_total gcomposition_multiplicative gcomposition_additive : gcomposition.

    Definition gcomposition_angelic `{angelic_R : angelic R} : angelic gcomposition.
    Proof. cbv [angelic] in *. destruct angelic_R as [? [? ?]]. repeat split; eauto with gcomposition. Qed.

    Definition gcomposition_demonic `{demonic_R : demonic R} : demonic gcomposition.
    Proof. cbv [demonic] in *. destruct demonic_R as [? [? ?]]. repeat split; eauto with gcomposition. Qed.

    Definition gcomposition_totalic `{totalic_R : totalic R} : totalic gcomposition.
    Proof. cbv [totalic] in *. destruct totalic_R as [? [? ?]]. repeat split; eauto with gcomposition. Qed.

  End Composition.

  Section Composition.
    Context {IT NT MT OT : Type}.
    Context (h : IT -> (NT * MT)).
    Context (R : NT -> MultiRelationSpec MT OT).

    Definition hcomposition : MultiRelationSpec IT OT := fun it ot => R (fst (h it)) (snd (h it)) ot.

    Definition hcomposition_upclosed `{upclosed_R : forall t, upclosed (R t)} : upclosed hcomposition.
    Proof. cbv in *; firstorder. Qed.

    Definition hcomposition_proper  `{proper_R : forall t, proper (R t)} : proper hcomposition.
    Proof. cbv in *; firstorder. Qed.

    Definition hcomposition_total `{total_R : forall t, total (R t)} : total hcomposition.
    Proof. cbv in *; firstorder. Qed.

    Definition hcomposition_multiplicative `{multiplicative_R : forall t, multiplicative (R t)} : multiplicative hcomposition.
    Proof. cbv in *; firstorder. eapply multiplicative_R; firstorder. Qed.

    Definition hcomposition_additive `{additive_R : forall t, additive (R t)} : additive hcomposition.
    Proof. cbv in *; firstorder. eapply additive_R; firstorder. Qed.

    Local Hint Resolve hcomposition_upclosed hcomposition_proper hcomposition_total hcomposition_multiplicative hcomposition_additive : hcomposition.

    Local Definition universal_conjunction_commutative {A : Type} (P Q : A -> Prop) :
      (forall x, P x /\ Q x) <-> ((forall x, P x) /\ (forall x, Q x)).
    Proof. firstorder. Qed.

    Definition hcomposition_angelic `{angelic_R : forall t, angelic (R t)} : angelic hcomposition.
    Proof. cbv [angelic] in *. do 2 (erewrite universal_conjunction_commutative in angelic_R; destruct angelic_R as [? angelic_R]). repeat split; eauto with hcomposition. Qed.

    Definition hcomposition_demonic `{demonic_R : forall t, demonic (R t)} : demonic hcomposition.
    Proof. cbv [demonic] in *. do 2 (erewrite universal_conjunction_commutative in demonic_R; destruct demonic_R as [? demonic_R]). repeat split; eauto with hcomposition. Qed.

    Definition hcomposition_totalic `{totalic_R : forall t, totalic (R t)} : totalic hcomposition.
    Proof. cbv [totalic] in *. do 2 (erewrite universal_conjunction_commutative in totalic_R; destruct totalic_R as [? totalic_R]). repeat split; eauto with hcomposition. Qed.
    
  End Composition.

  (* Section Composition.
    Context {IT MT OT : Type}.
    Context (h : IT -> MT).
    Context (R : MT -> MultiRelationSpec IT OT).

    Definition hcomposition : MultiRelationSpec IT OT := fun it ot => R (h it) it ot.

    Definition hcomposition_upclosed `{upclosed_R : forall t, upclosed (R t)} : upclosed hcomposition.
    Proof. cbv in *; firstorder. Qed.

    Definition hcomposition_proper  `{proper_R : forall t, proper (R t)} : proper hcomposition.
    Proof. cbv in *; firstorder. Qed.

    Definition hcomposition_total `{total_R : forall t, total (R t)} : total hcomposition.
    Proof. cbv in *; firstorder. Qed.

    Definition hcomposition_multiplicative `{multiplicative_R : forall t, multiplicative (R t)} : multiplicative hcomposition.
    Proof. cbv in *; firstorder. eapply multiplicative_R; firstorder. Qed.

    Definition hcomposition_additive `{additive_R : forall t, additive (R t)} : additive hcomposition.
    Proof. cbv in *; firstorder. eapply additive_R; firstorder. Qed.

    Local Hint Resolve hcomposition_upclosed hcomposition_proper hcomposition_total hcomposition_multiplicative hcomposition_additive : hcomposition.

    Local Definition universal_conjunction_commutative {A : Type} (P Q : A -> Prop) :
      (forall x, P x /\ Q x) <-> ((forall x, P x) /\ (forall x, Q x)).
    Proof. firstorder. Qed.

    Definition hcomposition_angelic `{angelic_R : forall t, angelic (R t)} : angelic hcomposition.
    Proof. cbv [angelic] in *. do 2 (erewrite universal_conjunction_commutative in angelic_R; destruct angelic_R as [? angelic_R]). repeat split; eauto with hcomposition. Qed.

    Definition hcomposition_demonic `{demonic_R : forall t, demonic (R t)} : demonic hcomposition.
    Proof. cbv [demonic] in *. do 2 (erewrite universal_conjunction_commutative in demonic_R; destruct demonic_R as [? demonic_R]). repeat split; eauto with hcomposition. Qed.

    Definition hcomposition_totalic `{totalic_R : forall t, totalic (R t)} : totalic hcomposition.
    Proof. cbv [totalic] in *. do 2 (erewrite universal_conjunction_commutative in totalic_R; destruct totalic_R as [? totalic_R]). repeat split; eauto with hcomposition. Qed.
    
  End Composition. *)

  (* ------------------------ Left identity composition ----------------------- *)
  Section Composition.
    Context {IT OT : Type}.
    Context (R : MultiRelationSpec IT OT).

    Lemma left_identity_composition {s P} : 
      R s P <-> (composition identity R) s P.
    Proof. firstorder. Qed.

    Lemma right_identity_composition {s P} : 
      R s P <-> (composition R identity) s P.
    Proof. firstorder. Qed.

  End Composition.

  Section Composition.
    Context {IT MT NT OT : Type}.
    Context (R : MultiRelationSpec IT MT).
    Context (P : MultiRelationSpec MT NT).
    Context (Q : MultiRelationSpec NT OT).

    Lemma composition_associative {s T} : 
      (composition (composition R P) Q) s T <-> (composition R (composition P Q)) s T.
    Proof. firstorder. Qed.

  End Composition.
(* 
  Section Composition.
    Context {IT MT NT OT : Type}.
    Context (R : MultiRelationSpec MT NT).
    Context (f : IT -> MT).
    Context (g : MT -> NT -> OT).

    CONT

    (* Lemma composition_associative {s P} : 
      R s P <-> (composition identity R) s P.
    Proof. firstorder. Qed. *)


    Lemma composition_commutitive {s P} : 
      fcomposition (gcomposition R g) f s P <-> gcomposition (fcomposition R f) g s P.

    Lemma right_identity_composition {s P} : 
      R s P <-> (composition R identity) s P.
    Proof. firstorder. Qed.

  End Composition. *)

End Specification.

Global Hint Resolve 
  identity_upclosed
  composition_upclosed
  fcomposition_upclosed
  gcomposition_upclosed
  hcomposition_upclosed
  : upclosed.

Global Hint Resolve 
  identity_angelic
  composition_angelic
  fcomposition_angelic
  gcomposition_angelic
  hcomposition_angelic
  : angelic.

Global Hint Resolve 
  identity_demonic
  composition_demonic
  fcomposition_demonic
  gcomposition_demonic
  hcomposition_demonic
  : demonic.

Global Hint Resolve 
  identity_totalic
  composition_totalic
  fcomposition_totalic
  gcomposition_totalic
  hcomposition_totalic
  : totalic.
