Require Import HoTT.

(* perhaps too much is imported here *)
From GCTT
     Require Import equiv_lemmas sigma_lemmas quotients finite_types finite.permutations monoidal_1type.
From GCTT Require Import fintype_monoidal group_complete_category.

(** Would have been better to define this stuff before fintype_monoidal, but but.*)
Require Import monoidal_category.
Section Iso_Fin.
  Definition iso_fin : PreCategory.
  Proof.
    srapply (Build_PreCategory (fun A B : FinType => A <~> B)).
    - intros. cbn. reflexivity.
    - intros A B C. cbn. intros f g.
      exact (f oE g).
    - intros A B C D. cbn. intros f g h.
      apply ecompose_ee_e.
    - intros A B. cbn. intro f.
      apply ecompose_1e.
    - intros A B. cbn. intro f.
      apply ecompose_e1.
  Defined.

  Definition isgroupoid_isofin {A B : iso_fin} (f : morphism iso_fin A B)
    : IsIsomorphism f.
  Proof.
    simpl in f.
    apply (Build_IsIsomorphism _ A B  f (equiv_inverse f)); apply path_equiv; apply path_arrow.
    - apply (eissect f).
    - apply (eisretr f).
  Defined.


  Definition iso_fin_to_pg_fin : Functor iso_fin (Core.groupoid_category FinType).
  Proof.
    srapply (Build_Functor iso_fin (Core.groupoid_category FinType) idmap).
    - intros A B. cbn. apply path_FinType.
    - intros A B C. intros f g. hnf.
      apply path_FinType_compose.
    - intro A. hnf. apply path_FinType_1.
  Defined.

  Definition isfullyfaithful_iso_to_pgfin : forall (A B : iso_fin),
      IsEquiv (morphism_of iso_fin_to_pg_fin (s := A) (d := B)).
  Proof.
    simpl. intros A B. exact _.
  Defined.

  Definition iso_fin_sum : Functor (iso_fin * iso_fin) iso_fin.
  Proof.
    srapply @Build_Functor.
    - intros [A B]. exact (sum_FinType A B).
    - intros [A1 B1] [A2 B2]. simpl.
      intros [alpha betta]. exact (alpha +E betta).
    - cbn. intros [A1 B1] [A2 B2] [A3 B3]. cbn.
      intros [alpha1 betta1] [alpha2 betta2]. cbn.
      apply path_equiv. apply path_arrow. intros [i | j]; reflexivity.
    - cbn. intros [A B]. simpl. unfold reflexive_equiv.
      apply path_equiv. apply path_arrow. intros [i | j]; reflexivity.
  Defined.

  Definition moncat_isofin : Symmetric_Monoidal_Category.
  Proof.
    srefine (Build_Symmetric_Monoidal_Category
               (Build_Cat_Magma _ iso_fin_sum) FinType_id
               (fun A B C => equiv_sum_assoc A B C)
               _ _
               (fun A => sum_empty_l A)
               _ _
               (fun A => sum_empty_r A)
               _ _
               (fun A B => equiv_sum_symm A B ) _ _ _ _ _ _ _); cbn.
    - intros. apply isgroupoid_isofin.
    - intros A B C A' B' C'. intros f g h.
      apply path_equiv; apply path_arrow.
      intro x. destruct x as [[i | j] | k]; reflexivity.
    - intro A. apply isgroupoid_isofin.
    - intros A B f.
      apply path_equiv; apply path_arrow.
      intro x. destruct x as [[] | i]. reflexivity.
    - intro A. apply isgroupoid_isofin.
    - intros A B f.
      apply path_equiv; apply path_arrow.
      intro x. destruct x as [i | []]. reflexivity.
    - intros. apply isgroupoid_isofin.
    - intros A B A' B' f g.
      apply path_equiv; apply path_arrow.
      intro x. destruct x as [i | i]; reflexivity.
    - intros A B.
      apply path_equiv; apply path_arrow.
      intro x. destruct x as [i | i]; reflexivity.
    - intros A B.
      apply path_equiv; apply path_arrow.
      intro x. destruct x as [[[] | i] | i]; reflexivity.
    - intros A B.
      apply path_equiv; apply path_arrow.
      intro x. destruct x as [[i | []] | i]; reflexivity.
    - intros A B C D.
      apply path_equiv; apply path_arrow.
      intro x. destruct x as [[[i | i] | i] | i]; reflexivity.
    - intros A B C. 
      apply path_equiv; apply path_arrow.
      intro x. destruct x as [[i | i] | i]; reflexivity.
  Defined.
  
End Iso_Fin.


Section Group_Complete_Iso_Fin.
  Definition group_complete_isofin := group_completion_moncat moncat_isofin.

  Definition sum_group_complete_isofin :
    Functor (group_complete_isofin * group_complete_isofin) group_complete_isofin.
  Proof.
    srapply @Build_Functor; cbn.
    - intros [[A1 B1] [A2 B2]].
      exact ((sum_FinType A1 A2, sum_FinType B1 B2)).
    - intros [[A1 B1] [A2 B2]] [[A3 B3] [A4 B4]]. simpl.
      intros [f1 f2]. revert f1 f2. simpl.
      srapply @set_quotient_rec2'.
      + intros f1 f2. simpl. apply class_of.
        apply (sum_group_completion_1' moncat_isofin f1 f2).
      + simpl. intros f f' g H.
        apply related_classes_eq.
        apply (welldef_sum_group_completion_1 moncat_isofin f f' g g H).
        apply refl_monact_relation.
      + simpl. intros f g g' H.
        apply related_classes_eq.
        srefine (welldef_sum_group_completion_1 moncat_isofin f f g g' _ H).
        apply refl_monact_relation.
    - simpl. intros [[a1 a2] [b1 b2]] [[c1 c2] [d1 d2]] [[e1 e2] [f1 f2]].
      simpl. intros [alpha betta] [gamma dela]. simpl.
      revert alpha.
      apply set_quotient_ind_prop.
      { intro alpha. exact _. }
      intro alpha. revert betta.
      apply set_quotient_ind_prop.
      { intro betta. exact _. }
      intro betta. revert gamma.
      apply set_quotient_ind_prop.
      { intro gamma. exact _. }
      intro gamma. revert dela.
      apply set_quotient_ind_prop.
      { intro dela. exact _. }
      intro dela. simpl.
      apply related_classes_eq.
      destruct alpha as [s alpha].
      destruct betta as [t betta].
      destruct gamma as [u gamma].
      destruct dela as [v dela].
      srapply @exist.
      { simpl. apply (Build_Isomorphic (isiso_twist_middle moncat_isofin _ _ _ _ )). }
      cbn.
      destruct alpha as [alpha1 alpha2]. destruct betta as [betta1 betta2].
      destruct gamma as [gamma1 gamma2]. destruct dela as [delta1 delta2]. simpl in *.
      simpl.
      apply path_prod; simpl.
      (** Here comes the coherence  *)
      { apply path_equiv. apply path_arrow. intro x.
        destruct x as [[[i|i] | [i|i]] | [i|i]]; reflexivity. }
      { apply path_equiv. apply path_arrow. intro x.
        destruct x as [[[i|i] | [i|i]] | [i|i]]; reflexivity. }
    - intros [[A1 A2] [B1 B2]]. simpl.
      apply related_classes_eq.
      unfold monact_relation. srapply @exist.
      { simpl.
        apply (Build_Isomorphic (isiso_moncat_lid moncat_isofin FinType_id)). }
      simpl.
      apply path_prod; simpl.
      (** This is probably not difficult to show from naturality and coherence triangles, but we use the hamme*)
      { apply path_equiv; apply path_arrow. intro x.
        destruct x as [[[] | []] | [i | i]]; reflexivity. }
      { apply path_equiv; apply path_arrow. intro x.
        destruct x as [[[] | []] | [i | i]]; reflexivity. }
  Defined.

  Definition FinFin_to_GrpCompl : Functor (iso_fin * iso_fin) group_complete_isofin.
  Proof.
    apply cat_to_actcat.
  Defined.

  Definition assoc_group_complete_isofin (A1 A2 A3 : group_complete_isofin)
    : morphism _ (sum_group_complete_isofin (sum_group_complete_isofin (A1, A2), A3))
               (sum_group_complete_isofin (A1, sum_group_complete_isofin (A2, A3))).
  Proof.
    srefine (FinFin_to_GrpCompl _1 _). cbn.
    (* simpl. apply class_of. *)
    (* exists (moncat_id _). *)
    simpl. (* destruct A1 as [A1 B1]. destruct A2 as [A2 B2]. destruct A3 as [A3 B3]. simpl. *)
    exact (equiv_sum_assoc _ _ _ , equiv_sum_assoc _ _ _ ).
  Defined.

  Definition lid_group_complete_isofin (A : group_complete_isofin)
    : morphism _ (sum_group_complete_isofin ((FinType_id, FinType_id), A)) A.
  Proof.
    srefine (FinFin_to_GrpCompl _1 _). cbn.
    exact (sum_empty_l _ , sum_empty_l _).
  Defined.

  Definition rid_group_complete_isofin (A : group_complete_isofin)
    : morphism _ (sum_group_complete_isofin (A, (FinType_id, FinType_id))) A.
  Proof.
    srefine (FinFin_to_GrpCompl _1 _). cbn.
    exact (sum_empty_r _ , sum_empty_r _).
  Defined.

  Definition sym_group_complete_isofin (A B : group_complete_isofin)
    : morphism _ (sum_group_complete_isofin (A, B)) (sum_group_complete_isofin (B, A)).
  Proof.
    srefine (FinFin_to_GrpCompl _1 _). cbn.
    exact (equiv_sum_symm _ _, equiv_sum_symm _ _).
  Defined.


  (* Move result to other place *)
  (** The symmetric monoidal structure of the category of finite types and isomorphisms.  *)
  (** Should ideally restructure somewhat since now this takes a LONG time...  *)
  Definition moncat_group_complete_isofin : Symmetric_Monoidal_Category.
  Proof.
    srefine (Build_Symmetric_Monoidal_Category
               (Build_Cat_Magma _ sum_group_complete_isofin) (FinType_id ,FinType_id)
               assoc_group_complete_isofin _ _
               lid_group_complete_isofin _ _
               rid_group_complete_isofin _ _ 
               sym_group_complete_isofin _ _
               _ _(* (fun A => sum_empty_r A) *)
               _ _
               _ ).
    - intros A B C. unfold assoc_group_complete_isofin.
      apply (iso_functor FinFin_to_GrpCompl).
      apply prod_isisomorphism; apply isgroupoid_isofin.
    - intros A B C A' B' C'. simpl in A, B, C, A', B', C'.
      intros f g h. revert f.
      apply set_quotient_ind_prop.
      { intro x. exact _. }    
      intro f.
      revert g.
      apply set_quotient_ind_prop.
      { intro x. exact _. }
      intro g. revert h.
      apply set_quotient_ind_prop.
      { intro x. exact _. }
      intro h.
      destruct f as [s f]. destruct g as [t g]. destruct h as [u h]. simpl in *.
      apply related_classes_eq.
      srapply @exist.
      { simpl.
        (* Cheat a little since all morphisms in iso_fin are isomorphisms *)
        srefine (Build_Isomorphic (isgroupoid_isofin _)).
        refine (moncat_sym (moncat_isofin) FinType_id (sum_FinType s (sum_FinType t u)) o _).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        srefine (identity _ +^ _). apply moncat_assoc. }
      hnf. destruct f as [f1 f2]. destruct g as [g1 g2]. destruct h as [h1 h2]. hnf.
      destruct A as [A1 A2]. destruct B as [B1 B2]. destruct C as [C1 C2].
      destruct A' as [A1' A2']. destruct B' as [B1' B2']. destruct C' as [C1' C2'].
      unfold monoidal_action_cat_compose'. simpl.
      apply path_prod; cbn.
      (* here comes the coherence *)
      { apply path_equiv. apply path_arrow.
        intro x. destruct x as [[[] | i] | i]; repeat destruct i as [i | i]; reflexivity. }
      { apply path_equiv. apply path_arrow.
        intro x. destruct x as [[[] | i] | i]; repeat destruct i as [i | i]; reflexivity. }
    - intro A. unfold lid_group_complete_isofin.
      apply (iso_functor FinFin_to_GrpCompl).
      apply prod_isisomorphism; apply isgroupoid_isofin.
    - intros A A'. simpl in A, A'.
      apply set_quotient_ind_prop.
      {intro x. exact _. }
      intro f. destruct f as [s [f1 f2]]. simpl in f1, f2.
      destruct A as [A1 A2]. destruct A' as [A1' A2']. simpl.
      apply related_classes_eq.
      srapply @exist.
      { simpl.
        (* Cheat a little since all morphisms in iso_fin are isomorphisms *)
        srefine (Build_Isomorphic (isgroupoid_isofin _)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        srefine (_ o moncat_lid moncat_isofin _).
        apply moncat_sym. }
      hnf. unfold monoidal_action_cat_compose'. simpl.
      (* coherence: *)
      apply path_prod; simpl;
        apply path_equiv; apply path_arrow; intro i;
          repeat try destruct i as [i | i]; try destruct i as []; reflexivity.
    - intro A. 
      apply (iso_functor FinFin_to_GrpCompl).
      apply prod_isisomorphism; apply isgroupoid_isofin.
    - intros A A'. simpl in A, A'.
      apply set_quotient_ind_prop.
      { intro x. exact _. }
      intros [s [f1 f2]]. simpl in f1, f2.
      destruct A as [A1 A2]. destruct A' as [A1' A2']. simpl in *.
      apply related_classes_eq.
      srapply @exist.
      { simpl.
        srefine (Build_Isomorphic (isgroupoid_isofin _)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        srefine (moncat_lid moncat_isofin _). }
      (* coherence *)
      apply path_prod; simpl;
        apply path_equiv; apply path_arrow; intro i;
          repeat try destruct i as [i | i]; try destruct i as []; reflexivity.
    - intros A B. 
      apply (iso_functor FinFin_to_GrpCompl).
      apply prod_isisomorphism; apply isgroupoid_isofin.
    - intros [A1 A2] [B1 B2] [A1' A2'] [B1' B2'].
      intros f g. revert f.
      apply set_quotient_ind_prop.
      { intro x. exact _. } intro f.
      revert g.
      apply set_quotient_ind_prop.
      { intro x. exact _. } intro g.
      destruct f as [s f]. destruct g as [t g]. simpl in *.
      apply related_classes_eq.
      srapply @exist.
      { simpl. srefine (Build_Isomorphic (isgroupoid_isofin _)). 
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        srefine (moncat_sym moncat_isofin _ _ o _).
        srefine (1 +^ _). apply moncat_sym. }
      (* coherence *)
      apply path_prod; simpl;
        apply path_equiv; apply path_arrow; intro i;
          repeat try destruct i as [i | i]; try destruct i as []; reflexivity.
    - intros [A1 A2] [B1 B2]. simpl.
      apply related_classes_eq.
      srapply @exist.
      { simpl. srefine (Build_Isomorphic (isgroupoid_isofin _)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        apply (moncat_lid moncat_isofin). }
      (* coherence *)
      apply path_prod; simpl;
        apply path_equiv; apply path_arrow; intro i;
          repeat try destruct i as [i | i]; try destruct i as []; reflexivity.
    - intros [A1 A2] [B1 B2]. simpl.
      apply related_classes_eq.
      srapply @exist.
      { reflexivity. } 
      (* coherence *)
      apply path_prod; simpl;
        apply path_equiv; apply path_arrow; intro i;
          repeat try destruct i as [i | i]; try destruct i as []; reflexivity.
    - intros [A1 A2] [B1 B2]. simpl.
      apply related_classes_eq.
      srapply @exist.
      { simpl.
        srefine (Build_Isomorphic (isgroupoid_isofin _)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        apply (moncat_rid moncat_isofin). }
      (* coherence *)
      apply path_prod; simpl;
        apply path_equiv; apply path_arrow; intro i;
          repeat try destruct i as [i | i]; try destruct i as []; reflexivity.
    - intros [A1 A2] [B1 B2] [C1 C2] [D1 D2]. simpl.
      apply related_classes_eq.
      srapply @exist.
      { simpl.  apply symmetry.
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        srefine (Build_Isomorphic (isgroupoid_isofin _)).      
        srefine (_ +^ (moncat_lid moncat_isofin FinType_id) ).
        srefine (_ o moncat_rid moncat_isofin _ ).
        srefine (moncat_rid moncat_isofin _ ). }
      (* coherence *)
      apply path_prod; simpl;
        apply path_equiv; apply path_arrow; intro i;
          repeat try destruct i as [i | i]; try destruct i as []; reflexivity.
    - intros [A1 A2] [B1 B2] [C1 C2]. simpl.
      apply related_classes_eq.
      srapply @exist.
      { simpl. apply symmetry.
        srefine (Build_Isomorphic (isgroupoid_isofin _)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        change (sum_FinType ?a ?b) with (@binary_op moncat_isofin (a, b)).
        srefine (_ +^ (moncat_lid moncat_isofin FinType_id) ).
        exact ((moncat_lid moncat_isofin FinType_id) +^ 1). }
      (* coherence *)
      apply path_prod; simpl;
        apply path_equiv; apply path_arrow; intro i;
          repeat try destruct i as [i | i]; try destruct i as []; reflexivity.
  Defined.

  
End Group_Complete_Iso_Fin.