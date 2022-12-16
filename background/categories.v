Require Import HoTT.

Require Import Categories.Functor Category.Morphisms.
Require Import Category.Core.
Require Import FunextAxiom.

From GCTT Require Import quotients.
(* Require Import finite_lemmas. *)

(** Easier to redefine isomorphisms of categories than to using the library *)
Section Category_Isomorphism.
  Definition IsFullyFaithful {C D : PreCategory} (F : Functor C D)
    := forall (c c' : C), IsEquiv (@morphism_of _ _ F c c').
  Definition IsIso_Functor {C D : PreCategory} (F : Functor C D)
    := (IsEquiv (object_of F)) * (IsFullyFaithful F).
  Definition Cat_Isomorphic (C D : PreCategory)
    := {F : Functor C D & IsIso_Functor F}.
  
  Definition cat_isomorphic_compose {C D E : PreCategory}
             (G : Cat_Isomorphic D E) (F : Cat_Isomorphic C D)
  : Cat_Isomorphic C E.
  Proof.
    destruct G as [G iso_G]. destruct F as [F iso_F].
    exists (G o F)%functor.
    destruct iso_G as [ff_G equiv_G].
    destruct iso_F as [ff_F equiv_F].
    srefine (isequiv_compose, _).
    unfold IsFullyFaithful in *.
    intros s d. 
    unfold Functor.Composition.Core.compose. simpl.
    apply isequiv_compose.
  Defined.
End Category_Isomorphism.

Definition idtohom {C : PreCategory} {c d : C}
  : c = d -> morphism C c d.
Proof.
  intro p. destruct p.
  apply identity.
Defined.

Global Instance isisomorphism_idtohom {C : PreCategory} {c d : C} (p : c = d)
  : IsIsomorphism (idtohom p).
Proof.
  apply (Build_IsIsomorphism C c d _ (idtohom p^));
    destruct p; apply identity_identity.
Defined.

Section Path_Functor.
  (** We describe the path types of functors (using function extensionality).   *)
  (** Again, something like it is done in the HoTT library, but we found it easier to redefine. *)
  Definition issig_functor {C D : PreCategory}
  : Functor C D <~>
            {F : {F0 : C -> D &
                   forall s d : C, morphism C s d -> morphism D (F0 s) (F0 d)} &
                   (forall (s d d' : C) (m1 : morphism C s d) (m2 : morphism C d d'),
                     (pr2 F) s d' (m2 o m1)%morphism =
                     ((pr2 F) d d' m2 o (pr2 F) s d m1)%morphism) *
                   (forall x : C, (pr2 F) x x 1%morphism = 1%morphism)}.
  Proof.
    srapply @equiv_adjointify.
    - intro F.
      srapply @exist.
      { exists (object_of F). apply (morphism_of F). }
      simpl.
      exact (composition_of F, identity_of F).
    - intros [[F0 F1] [comp id]].
      exact (Build_Functor _ _ F0 F1 comp id).
    - intros [[F0 F1] [comp id]].
      simpl. reflexivity.
    - intros [F0 F1 comp id]. reflexivity.
  Defined.

  Definition equiv_path_forall_3 {X Y : Type} {Z : X -> Y -> Type}
             {P : forall (x : X) (y : Y), Z x y -> Type}
             (f g : forall (x : X) (y : Y) (z : Z x y), P x y z)
    : (forall (x : X) (y : Y) (z : Z x y), f x y z = g x y z) <~> f = g.
  Proof.
    refine (equiv_path_forall _ _ oE _).
    apply (equiv_functor_forall' equiv_idmap). simpl. intro x.
    refine (equiv_path_forall _ _ oE _).
    apply (equiv_functor_forall' equiv_idmap). simpl. intro y.
    apply equiv_path_forall.
  Defined.

  Definition inv_path_functor  {C D : PreCategory} (F G : Functor C D)
    : F = G -> {p0 : forall c : C, F c = G c &
                          forall (c d : C) (f : morphism C c d),
                            (idtohom (p0 d) o morphism_of F f  o (idtohom (p0 c))^-1=
                             morphism_of G f )%morphism }.
  Proof.
    intro p. destruct p.
    exists (fun _ => idpath).
    intros c d f .
    refine (right_identity _ _ _ _ @ _).
    refine (left_identity _ _ _ _ ).
  Defined.
    

  Definition equiv_path_functor {C D : PreCategory} (F G : Functor C D)
    : {p0 : forall c : C, F c = G c &
                          forall (c d : C) (f : morphism C c d),
                            (idtohom (p0 d) o morphism_of F f  o (idtohom (p0 c))^-1=
                             morphism_of G f )%morphism } <~> F = G.
  Proof.
    srefine ((equiv_ap (@issig_functor C D) F G)^-1 oE _).
    refine (equiv_path_sigma_hprop _ _ oE _).
    refine (equiv_path_sigma _ _ _ oE _).
    simpl.
    srapply @equiv_functor_sigma'.
    - apply equiv_path_forall.
    - intro p0.  simpl. 
      refine (equiv_path_forall _ _ oE _).  
      apply (equiv_functor_forall' equiv_idmap). simpl. intro s.
      refine (equiv_path_forall _ _ oE _).  
      apply (equiv_functor_forall' equiv_idmap). simpl. intro d.
      refine (equiv_path_forall _ _ oE _).  
      apply (equiv_functor_forall' equiv_idmap). simpl. intro f.
      apply equiv_concat_l.
      transitivity (idtohom ((ap10 (path_forall _ _ p0)) d) o (morphism_of F) s d f o
                            idtohom ((ap10 (path_forall _ _ p0)) s)^)%morphism.
      { destruct (path_forall _ _ p0). simpl.
        apply inverse.
        refine (right_identity _ _ _ _ @ _).
        refine (left_identity _ _ _ _ ). }
      apply (ap (fun x => (idtohom (x d) o (morphism_of F) s d f o idtohom (x s)^)%morphism)).
      refine (eissect (equiv_path_forall _ _) p0).
  Defined.    

  Definition path_functor' {C D : PreCategory} (F G : Functor C D)
             (p0 : forall c : C, F c = G c)
             (p1 : forall (c d : C) (f : morphism C c d),
                 (idtohom (p0 d) o morphism_of F f  o (idtohom (p0 c))^-1=
                  morphism_of G f )%morphism)
  : F = G := equiv_path_functor F G (p0; p1).

  Definition path_functor_id {C D : PreCategory} (F : Functor C D)
    : equiv_inverse (equiv_path_functor F F) (idpath F) = inv_path_functor F F (idpath F).
  Proof.
    apply path_sigma_hprop.
    simpl. reflexivity.
  Defined.

  Lemma isequiv_inv_path_functor {C D : PreCategory} (F G: Functor C D)
    : IsEquiv (inv_path_functor F G).
  Proof.
    cut (inv_path_functor F G = equiv_inverse (equiv_path_functor F G)).
    { intro p. rewrite p.
      apply equiv_isequiv. }
    apply path_arrow. intro p. destruct p.
    apply inverse. apply path_functor_id.
  Defined.
    
             
End Path_Functor.


Section Pi_0.
  (** The set truncation of a category  *)
  Definition pi0_cat (C : PreCategory) : Type
    := set_quotient (morphism C).

  Definition class_of_pi0cat {C : PreCategory} : C -> pi0_cat C :=
    class_of (morphism C).

  Definition path_pi0_cat {C : PreCategory} {c d : C} (f : morphism C c d)
    : class_of_pi0cat c = class_of_pi0cat d.
  Proof.
    apply related_classes_eq. exact f.
  Defined.  
End Pi_0.

Section Cat_sum.
  (** Given a family of categories [C : X -> Cat], we define the sum of [C] over [X] *)
  Definition cat_sum_obj (X : Type) (C : X -> PreCategory) :=
    {x : X & object (C x)}.

  Definition morphism_over {X : Type} (C : X -> PreCategory)
             {x0 x1 : X} (p : x0 = x1) (c0 : C x0) (c1 : C x1) : Type.
  Proof.
    destruct p.
    exact (morphism (C x0) c0 c1).
  Defined.

  Global Instance isset_morphism_over {X : Type} (C : X -> PreCategory)
         {x0 x1 : X} (p : x0 = x1) (c0 : C x0) (c1 : C x1)
    : IsHSet (morphism_over C p c0 c1).
  Proof.
    destruct p. simpl. exact _.
  Defined.

  Definition morphism_over_compose {X : Type} (C : X -> PreCategory)
             {x0 x1 x2 : X} {p1 : x0 = x1} {p2 : x1 = x2}
             {c0 : C x0} {c1 : C x1} {c2 : C x2}
    : morphism_over C p2 c1 c2 ->  morphism_over C p1 c0 c1
      -> morphism_over C (p1 @ p2) c0 c2.
  Proof.
    intros f g.
    destruct p2. destruct p1.
    simpl. exact (f o g)%morphism.
  Defined.

  Definition cat_sum_morph (X : Type) (C : X -> PreCategory)
    : cat_sum_obj X C -> cat_sum_obj X C -> Type.
  Proof.
    intros [x a] [y b].
    exact {p : x = y & morphism_over C p a b}.
  Defined.

  Definition cat_sum (X : Type) {istrunc_X : IsTrunc 1 X}
             (C : X -> PreCategory) : PreCategory.
  Proof.
    srapply (Build_PreCategory (cat_sum_morph X C)).
    (* identity *)
    - intros [x a]. exists idpath. apply identity.
    - intros [x a] [y b] [z c].
      intros [p f] [q g].
      exists (q @ p).
      apply (morphism_over_compose C f g).
    - intros [x a] [y b] [z c] [w d].
      intros [p f] [q g] [r h].
      destruct r. destruct q. destruct p. simpl in *.
      srapply (@path_sigma).
      { reflexivity. } apply associativity.
    - intros [x a] [y b]. intros [p f].
      destruct p.
      srapply (@path_sigma).
      { reflexivity. } simpl.
      apply left_identity.
    - intros [x a] [y b]. intros [p f].
      destruct p.
      srapply (@path_sigma).
      { reflexivity. } simpl.
      apply right_identity.
  Defined.

  Definition include_summand (X : Type) {istrunc_X : IsTrunc 1 X}
             (C : X -> PreCategory) (x : X)
    : Functor (C x) (cat_sum X C).
  Proof.
    srapply @Build_Functor.
    - intro c. exact (x; c).
    - intros s d f. simpl.
      exists idpath. exact f.
    - intros a b c f g. simpl. reflexivity.
    - reflexivity.
  Defined.

  Definition isequiv_restrict_to_comp_catsum (X : Type) {istrunc_X : IsTrunc 1 X}
             (C : X -> PreCategory) (D : PreCategory)
    : IsEquiv (fun F : Functor (cat_sum X C) D => (fun x : X => (F o include_summand X C x)%functor)).
  Proof.
    srapply @isequiv_adjointify.
    - intro F.
      srapply @Build_Functor.
      + intros [x c]. exact (F x c).
      + intros [x1 c1] [x2 c2]. simpl.
        intros [p f]. simpl. destruct p. simpl in *.
        apply (morphism_of (F x1)). exact f.
      + intros [x1 c1] [x2 c2] [x3 c3].
        intros [p f] [q g]. simpl.
        destruct q. destruct p. simpl.
        apply composition_of.
      + simpl. intro x.
        apply identity_of.
    - simpl. intro F. apply path_forall.
      intro x. srapply @path_functor'.
      + simpl. reflexivity.
      + simpl. intros.
        rewrite left_identity. rewrite right_identity.
        reflexivity.
    - simpl. intro F.
      srapply @path_functor'.
      + simpl. intros [x c]. reflexivity.
      + simpl. intros [x1 c1] [x2 c2] [p f].
        destruct p.
        rewrite left_identity. rewrite right_identity.
        reflexivity.
  Defined.
    

  Definition univ_cat_sum (X : Type) {istrunc_X : IsTrunc 1 X}
             (C : X -> PreCategory) (D : PreCategory)
    :  Functor (cat_sum X C) D <~> (forall x : X, Functor (C x) D)
    := BuildEquiv _ _ _ (isequiv_restrict_to_comp_catsum X C D).

  Definition cat_sum_to_groupoid (X : Type) (Y : X -> Type)
             {istrunc_X : IsTrunc 1 X} {istrunc_Y : forall x : X, IsTrunc 1 (Y x)}
    : Functor (cat_sum X (fun x => Core.groupoid_category (Y x)))
              (Core.groupoid_category {x : X & Y x}).
  Proof.
    srapply @Build_Functor.
    - exact idmap.
    - intros [x1 y1] [x2 y2]. simpl.
      intros [p f]. destruct p. simpl in f. destruct f. reflexivity.
    - intros [x1 y1] [x2 y2] [x3 y3]. simpl.
      intros [p1 f1] [p2 f2]. destruct p2. destruct p1. simpl.
      destruct f2. destruct f1. reflexivity.
    - simpl. reflexivity.
  Defined.

  (** The sum commutes with the path groupoid *)
  Definition sum_to_catsum (X : Type) (Y : X -> Type)
             {istrunc_X : IsTrunc 1 X} {istrunc_Y : forall x : X, IsTrunc 1 (Y x)}
    : Functor (Core.groupoid_category {x : X & Y x})
              (cat_sum X (fun x => Core.groupoid_category (Y x))).
  Proof.
    srapply @Build_Functor.
    - simpl. exact idmap.
    - simpl. intros a b p.
      unfold cat_sum_morph. destruct p.
      exists idpath. reflexivity.
    - simpl. intros a b c p q. destruct q. destruct p. simpl.
      reflexivity.
    - simpl. reflexivity.
  Defined.

  Definition isiso_sum_to_catsum (X : Type) (Y : X -> Type)
             {istrunc_X : IsTrunc 1 X} {istrunc_Y : forall x : X, IsTrunc 1 (Y x)}
    : IsIso_Functor (sum_to_catsum X Y).
  Proof.
    apply Datatypes.pair.
    - simpl. exact _.
    - intros a b. simpl.
      srapply @isequiv_adjointify.
      + intros [p f]. destruct a as [x1 y1]. destruct b as [x2 y2].
        destruct p. simpl in f. destruct f. reflexivity.
      + intros [p f].
        destruct a as [x1 y1]. destruct b as [x2 y2].
        destruct p. simpl in f. destruct f. reflexivity.
      + simpl. intro p. destruct p. reflexivity.      
  Defined.
  
  Definition iso_path_groupoid_cat_sum (X : Type) (Y : X -> Type)
             {istrunc_X : IsTrunc 1 X} {istrunc_Y : forall x : X, IsTrunc 1 (Y x)}
    : Cat_Isomorphic (Core.groupoid_category {x : X & Y x})
                     (cat_sum X (fun x => Core.groupoid_category (Y x)))
    := (sum_to_catsum X Y; isiso_sum_to_catsum X Y).
End Cat_sum.    

Section Component.
  (** Defining the components of a category.  *)

  (** First we define the components of a type.  *)
  Definition component (X : Type) (x0 : Trunc 0 X) :=
    {x : X & tr x = x0}.

  (* full subcategory given by a family of propositions on the type of objects *)
  Definition full_subcategory
             (C : PreCategory) (P : C -> Type) : PreCategory.
  Proof.
    srapply (Build_PreCategory
               (object := {c : C & P c})
               (fun c d => morphism C (c.1) (d.1))).
    - intros. simpl.
      apply identity.
    - simpl. intros a b c f g.
      apply (compose f g).
    - simpl. intros a b c d. intros f g h.
      apply (associativity).
    - simpl. intros a b f.
      apply left_identity.
    - simpl. intros a b f.
      apply right_identity.
  Defined.

  Definition include_full_subcategory (C : PreCategory) (P : C -> Type)
    : Functor (full_subcategory C P) C.
  Proof.
    srapply @Build_Functor.
    - exact pr1.
    - intros [c1 p1] [c2 p2]. exact idmap.
    - intros [c1 p1] [c2 p2] [c3 p3]. reflexivity.
    - simpl. reflexivity.
  Defined. 

  
  Definition component_cat (C : PreCategory) (c0 : pi0_cat C) :=
    full_subcategory C (fun c => class_of _ c = c0).

  Definition include_component_cat (C : PreCategory) (c0 : pi0_cat C)
    : Functor (component_cat C c0) C.
  Proof.
    apply include_full_subcategory.
  Defined.

End Component.

Section Decompose_cat.
  (** A category may be decomposed into its components.  *)

  Definition transport_morph_component {C : PreCategory} {c d : C}
             (f : morphism C c d) :
    transport (component_cat C) (path_pi0_cat f) (c; idpath) =
    (c; path_pi0_cat f).
  Proof.
    destruct (path_pi0_cat f). reflexivity.
  Defined.

  Definition decompose_cat_obj {C : PreCategory}
    : C -> cat_sum (pi0_cat C) (component_cat C).
  Proof.
    intro c. exists (class_of_pi0cat c).
    exists c. reflexivity.
  Defined.

  Definition morphism_over_decomp {C : PreCategory} {c1 c2 : C}
             {x1 x2 : pi0_cat C}
             (p1 : class_of_pi0cat c1 = x1)
             (p2 : class_of_pi0cat c2 = x2)
             (q : x1 = x2)
    : morphism (component_cat C x2) (c1; p1 @ q) (c2 ; p2) ->
      morphism_over (component_cat C) q (c1; p1) (c2; p2).
  Proof.
    destruct q. simpl. exact idmap.
  Defined.

  Definition morphism_to_morphism_over_comp {C : PreCategory} {c1 c2 c3 : C}
             {x1 x2 x3 : pi0_cat C}
             (p1 : class_of_pi0cat c1 = x1)
             (p2 : class_of_pi0cat c2 = x2)
             (p3 : class_of_pi0cat c3 = x3)
             (q1 : x1 = x2) (q2 : x2 = x3)
             (f : morphism C c2 c3) (g : morphism C c1 c2)
    : morphism_over_compose _
                            (morphism_over_decomp p2 p3 q2 f) (morphism_over_decomp p1 p2 q1 g) =
      morphism_over_decomp p1 p3 (q1 @ q2) (f o g)%morphism.
  Proof.
    destruct q2. destruct q1. reflexivity.
  Defined.

  Definition decompose_cat (C : PreCategory)
    : Cat_Isomorphic C (cat_sum (pi0_cat C) (component_cat C)).
  Proof.
    refine
      (cat_isomorphic_compose
         (D := full_subcategory C (fun c => {x : pi0_cat C & class_of_pi0cat c = x}))
         _ _).
    - srapply @exist.
      + srapply @Build_Functor.
        * intros [c [x p]].
          exact (x; (c; p)).
        * intros [c1 [x1 p1]] [c2 [x2 p2]].
          simpl. intro f.
          srapply @exist.
          { simpl. exact (p1^ @ (path_pi0_cat f) @ p2). }
          simpl.

          apply morphism_over_decomp. simpl.
          exact f.
        * intros [c1 [x1 p1]] [c2 [x2 p2]] [c3 [x3 p3]].
          destruct p3. destruct p2. destruct p1.
          intros f1 f2. simpl in f1. simpl in f2.
          simpl. rewrite morphism_to_morphism_over_comp.
          repeat rewrite concat_1p. repeat rewrite concat_p1.
          simpl. unfold morphism_over_decomp.
          assert (p : path_pi0_cat (f2 o f1) =
                      path_pi0_cat f1 @ path_pi0_cat f2).
          { apply set_quotient_set. }
          
          destruct p. reflexivity.
        * simpl.
          intros [c [x p]]. destruct p.
          unfold morphism_over_decomp.
          rewrite concat_1p. rewrite concat_p1. 
          assert (p :path_pi0_cat (identity c) = idpath).
          { apply set_quotient_set. } rewrite p.
          reflexivity.
      + simpl. unfold IsIso_Functor.
        unfold IsFullyFaithful. simpl.
        apply Datatypes.pair.
        { srapply @isequiv_adjointify.
          - intros [x [c p]].
            exact (c; (x; p)).
          - intros [x [c p]]. reflexivity.
          - intros [c [x p]]. reflexivity. }
        { intros [c1 [x1 p1]] [c2 [x2 p2]].
          srapply @isequiv_adjointify.
          - simpl.
            intros [p f]. destruct p. simpl in f. exact f.
          - intros [p f].          
            destruct p. simpl. simpl in f.
            assert (p : (p1^ @ path_pi0_cat f) @ p2 = idpath).
            { apply set_quotient_set. }
            rewrite p.
            reflexivity.
          - intro f. simpl in f.
            generalize ((p1^ @ path_pi0_cat f) @ p2).
            intro p. destruct p. reflexivity. }        
    - srapply @exist.
      + srapply @Build_Functor.
        * intro c. exists c. exists (class_of_pi0cat c). reflexivity.
        * intros s d f. simpl. exact f.
        * intros a b c f g. simpl. reflexivity.
        * reflexivity.
      + simpl. apply Datatypes.pair.
        * simpl.
          srapply @isequiv_adjointify.
          { apply pr1. }
          { intros [c [x p]]. simpl.
            destruct p. reflexivity. }
          intro c. reflexivity.
        * intros c d. simpl. exact _.        
  Defined.

End Decompose_cat.




