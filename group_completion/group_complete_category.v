Require Import HoTT.
Require Import HoTT.Categories Category.
From A_BPQ Require Import categories sigma_lemmas path_lemmas quotients monoidal_category.
(* From A_BPQ Require Export monoidal_1type. *)
(* Change this once monoidal_category is in _CoqProject *)

(*These notations are defined elsewhere, but I do not know how to import it.*)
Local Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
Notation "F '_0' x" := (Functor.Core.object_of F x) (at level 10, no associativity, only parsing) : object_scope.
Notation "F '_1' m" := (Functor.Core.morphism_of F m) (at level 10, no associativity) : morphism_scope.
Open Scope category_scope.
Open Scope morphism_scope.



Section Localize.
  (* Definition Relation (A : Type) := (A -> A -> Type)%type. *)

  (** TODO: Update comments *)
  (** if we have a monoidal action with left_cancellation, we can build a category with objects X and
       arrows  [{m : M & m ⊗ x = m ⊗ y}] *)
  Definition monact_relation {S : Symmetric_Monoidal_Category} {X : PreCategory}
             (a : Monoidal_Action S X) (x y : X)
    : relation ({s : S & a (s, x) --> y}).
  intros [s g] [t h]. 
  exact {sigma : Isomorphic s t & h o (a _1 (pair_1 sigma 1)) = g  }.
  Defined.

  (* This is an equivalence relation, here is a proof of reflexivity *)
  Lemma refl_monact_relation {S : Symmetric_Monoidal_Category} {X : PreCategory}
             (a : Monoidal_Action S X) {x y : X}
             (f : {s : S & a (s, x) --> y})
    : monact_relation a x y f f.
  Proof.
    srapply @exist.
    { apply isomorphic_refl. }
    simpl. rewrite identity_of. apply right_identity.
  Qed.
    
  
  Definition monoidal_action_morphism (S : Symmetric_Monoidal_Category) (X : PreCategory)
             (a : Monoidal_Action S X) :
    (X -> X -> Type)
    := fun x y => set_quotient (monact_relation a x y).

  (* Definition left_faithful {C D : PreCategory} (m : Functor (A*B) B) := *)
  (* forall (s t : A) (f g : s --> t) (b : B), *)
  (*   m _1 (pair_1 f (identity b)) = m _1 (pair_1 f (identity b)) *)
  (*   ap (fun x => m x b) p = ap (fun x => m x b) q -> p = q. *)

  Definition functor_isomorphic {C D : PreCategory} (F : Functor C D)
             {c1 c2 : C} (e : Isomorphic c1 c2)
    : Isomorphic (F c1) (F c2).
  Proof.
    srefine (@Build_Isomorphic D _ _ (F _1 e) _).
  Defined.

  Definition prod_isomorphic {C D : PreCategory} {c1 c2 : C} {d1 d2 : D}
             (f : Isomorphic c1 c2) (g : Isomorphic d1 d2)
    : Isomorphic (C := C * D) (c1, d1) (c2, d2).
  Proof.
    srefine (@Build_Isomorphic
               (C*D) (c1,d1) (c2,d2)
               (morphism_isomorphic (Isomorphic := f), morphism_isomorphic (Isomorphic := g)) _).
    srapply @Build_IsIsomorphism.
    - exact (f^-1, g^-1).
    - apply path_prod; apply left_inverse.
    - apply path_prod; apply right_inverse.
  Defined.
    
  Definition monoidal_action_cat_compose' {S : Symmetric_Monoidal_Category} {X : PreCategory}
             (a : Monoidal_Action S X) {x y z : X}
    : {s : S & (a _0 (s, y))%object --> z} ->
      {s : S & (a _0 (s, x))%object --> y} -> {s : S & (a _0 (s, x))%object --> z}.
  Proof.
    intros [s1 f1] [s2 f2]. 
    exists (s1 +' s2).
    refine (f1 o (a _1 _ o mon_action_mult _ _ _ s1 s2 x)).
    exact (1, f2).
  Defined.

  Proposition welldef_monoidal_action_cat_compose
             {S : Symmetric_Monoidal_Category} {X : PreCategory}
             (a : Monoidal_Action S X) (x y z : X)
             (f f' : {s : S & (a _0 (s, y))%object --> z})
             (g g' : {s : S & (a _0 (s, x))%object --> y})
             (H1 : monact_relation a y z f f')
             (H2 : monact_relation a x y g g')
    : monact_relation a x z (monoidal_action_cat_compose' a f g)
                      (monoidal_action_cat_compose' a f' g').
  Proof.
    unfold monact_relation.
    destruct H1 as [sigma1 p1].
    destruct H2 as [sigma2 p2].
    simpl.
    srapply @exist.
    - apply (functor_isomorphic (binary_op)).
      srefine (prod_isomorphic sigma1 sigma2).
    - simpl.
      destruct f as [s f]. destruct p1.
      destruct g as [t g]. destruct p2.
      repeat rewrite associativity.
      apply (ap (fun h => f'.2 o h)).
      rewrite natl_mon_action_mult.
      repeat rewrite <- associativity.
      apply (ap (fun h => h o mon_action_mult S X a s t x)).
      rewrite <- composition_of. rewrite <- composition_of.
      simpl.  rewrite left_identity. rewrite left_identity.
      rewrite right_identity. reflexivity.
  Qed.
      
      
    
             
    
    
  
  Definition monoidal_action_cat (S : Symmetric_Monoidal_Category) (X : PreCategory)
             (a : Monoidal_Action S X)
    : PreCategory.
  Proof.
    srefine (Build_PreCategory (monoidal_action_morphism S X a) _ _ _ _ _ _).
    (* identity *)
    - intro x. apply class_of. exists (moncat_id _). apply mon_action_id.
    (* composition *)
    - intros x y z. unfold monoidal_action_morphism.
      srefine (set_quotient_rec2' (monact_relation a y z) _ _ _); simpl.
      + intros f1 f2. apply class_of.
        apply (monoidal_action_cat_compose' _ f1 f2).
      + simpl. intros f f' g.  intro H.
        apply related_classes_eq.
        apply (welldef_monoidal_action_cat_compose _ _ _ _ _ _ _ _ H).
        apply refl_monact_relation.
      + simpl. intros f g g'. intro H.
        apply related_classes_eq.
        refine (welldef_monoidal_action_cat_compose _ _ _ _ _ _ _ _ _ H).
        apply refl_monact_relation.
    (* associativity *)
    - intros x1 x2 x3 x4.
      srapply @set_quotient_ind_prop.
      intros [s f].
      srapply @set_quotient_ind_prop.
      intros [t g].
      srapply @set_quotient_ind_prop.
      intros [u h].
      simpl.
      apply related_classes_eq.
      exists (iso_moncat_assoc S u t s).
      simpl.
      repeat rewrite associativity.
      apply (ap (fun v => h o v)).
      transitivity
        (a _1 (pair_1 1 g) o (mon_action_mult S X a u t x2 o (a _1 (pair_1 (1 +^ 1) f))) o
           mon_action_mult S X a (u +' t) s x1).
      { rewrite natl_mon_action_mult.
        repeat rewrite associativity.
        rewrite action_coh_pent.
        repeat rewrite <- associativity.
        apply (ap (fun v => v o _)).
        apply (ap (fun v => v o _)).
        rewrite <- composition_of.
        rewrite <- composition_of.
        simpl.  rewrite left_identity. rewrite left_identity. reflexivity. }
      rewrite identity_of. simpl.
      repeat rewrite <- associativity. reflexivity.
    (* left identity *)
    - simpl.
      intros x1 x2.
      srapply @set_quotient_ind_prop.
      intros [s f]. simpl.
      apply related_classes_eq.
      exists (iso_moncat_lid S s).
      simpl. repeat rewrite <- associativity.
      rewrite natl_mon_action_id.
      rewrite <- action_coh_tri1.
      repeat rewrite associativity. reflexivity.
    (* right identity *)
    - simpl.
      intros x1 x2.
      srapply @set_quotient_ind_prop.
      intros [s f]. simpl.
      apply related_classes_eq.
      exists (iso_moncat_rid S s).
      simpl. repeat rewrite <- associativity.
      rewrite <- action_coh_tri2.
      repeat rewrite associativity.
      reflexivity.
  Defined.

  Definition cat_to_actcat {S : Symmetric_Monoidal_Category} {X : PreCategory}
             (act : Monoidal_Action S X)
             (* (left_cancel : left_faithful act) *)
    : Functor X (monoidal_action_cat S X act).
  Proof.
    srapply @Build_Functor.
    - exact idmap.
    - intros x y. simpl.
      intro f. apply class_of.
      exists (moncat_id _).
      exact (f o (mon_action_id _ _ act x)).
    - intros x y z f g. simpl.
      apply inverse.
      apply related_classes_eq. unfold monact_relation. simpl.
      exists (iso_moncat_rid S (moncat_id S)).
      simpl.
      repeat rewrite associativity.
      apply (ap (fun v => g o v)).
      refine (_ @ (associativity _ _ _ _ _ _ _ _)).
      rewrite natl_mon_action_id.
      refine (_ @ (associativity _ _ _ _ _ _ _ _)^).
      refine (_ @ (associativity _ _ _ _ _ _ _ _)^).
      apply (ap (fun v => f o v)).
      refine (_ @ (associativity _ _ _ _ _ _ _ _)).
      rewrite <- (natl_mon_action_id _ _ act _ _ (mon_action_id S X act x)).
      rewrite <- action_coh_tri2. repeat rewrite associativity.
      reflexivity.
    - intro x. simpl. apply (ap (class_of _)).
      rewrite left_identity. reflexivity.
  Defined.
  
  Definition include_in_monoidal_action_cat {S : Symmetric_Monoidal_Category} {X : PreCategory}
             (act : Monoidal_Action S X)
             (* (left_cancel : left_faithful act) *)
             (F : Functor S X)

    : Functor S (monoidal_action_cat S X act)
    := cat_to_actcat act o F.

  Definition triv_act_morphism {S : Symmetric_Monoidal_Category} {X : PreCategory}
             (act : Monoidal_Action S X)
             (s : S) (x : X)
    : morphism (monoidal_action_cat S X act) x (act (s,x))
    := class_of (monact_relation act _ _) (s ; (Category.identity (act (s, x)))). 

  Lemma decompose_actcat {S : Symmetric_Monoidal_Category} {X : PreCategory}
             (act : Monoidal_Action S X)
             (x y : X)
             (s : S) (f : act (s, x) --> y)
    : class_of (monact_relation act x y ) (s; f) =
      (cat_to_actcat act) _1 f o triv_act_morphism act s x. 
  Proof.
    simpl.  apply inverse. apply related_classes_eq.
    unfold monact_relation. simpl.
    exists (iso_moncat_lid S s).
    simpl.
    rewrite <- action_coh_tri1.
    rewrite identity_of.  rewrite left_identity.
    repeat rewrite associativity. reflexivity.
  Qed.

  Lemma natl_cat_to_actcat {S : Symmetric_Monoidal_Category} {X : PreCategory}
             (act : Monoidal_Action S X)
             (s : S) {x y : X} (f : x --> y)
    : (cat_to_actcat act) _1 (act _1 (pair_1 1 f)) o triv_act_morphism act s x
      = triv_act_morphism act s y o ((cat_to_actcat act) _1 f).
  Proof.
    rewrite <- decompose_actcat. simpl.
    apply inverse.
    apply related_classes_eq.
    unfold monact_relation. simpl.
    exists (iso_moncat_rid S s).
    simpl.
    rewrite <- action_coh_tri2. rewrite left_identity.
    repeat rewrite <- associativity.
    rewrite <- composition_of.
    simpl. rewrite left_identity. reflexivity.
  Qed.

End Localize.

Section Group_Completion.
  Definition diag_act_obj (S : Symmetric_Monoidal_Category) : S * (S * S) -> S * S.
  Proof.
    intros [s [x1 x2]].
    exact (s +' x1, s +' x2).
  Defined.

  Definition diag_act_fun (S : Symmetric_Monoidal_Category) : Functor (S * (S * S)) (S * S).
  Proof.
    srapply (Build_Functor (S * (S * S)) (S * S) (diag_act_obj S)).
    - intros [s [x1 x2]] [t [y1 y2]]. simpl.
      intros [f [g1 g2]].
      exact (f +^ g1, f +^ g2).
    - intros. 
      simpl.  rewrite <- composition_of. rewrite <- composition_of. simpl. reflexivity.
    - intros.  simpl. rewrite <- identity_of. rewrite <- identity_of. reflexivity.
  Defined.

  (* Definition diag_act_mult (S : Symmetric_Monoidal_Category) (s t: S) (x : S * S) *)
  (*   : diag_act_fun S (s +' t, x) --> diag_act_fun S (s, (diag_act_fun S (t,x))). *)
  (* Proof. *)
  (*   simpl. refine (moncat_assoc S _ _ _ , moncat_assoc S _ _ _). *)
  (* Defined. *)

  Definition prod_isisomorphism (C D : PreCategory) {c c' : C} {d d' : D}
             (f : c --> c') (g : d --> d')
    : IsIsomorphism f -> IsIsomorphism g
      -> IsIsomorphism (C := C*D) (s := (_,_)) (d := (_,_)) (f,g).
  Proof.
    intros isiso_f isiso_g.
    srapply @Build_IsIsomorphism.
    - exact (f^-1, g^-1).
    - apply path_prod; apply left_inverse.
    - apply path_prod; apply right_inverse.
  Defined.


  Definition diag_act (S : Symmetric_Monoidal_Category) : Monoidal_Action S (S * S).
  Proof.
    srefine (Build_Monoidal_Action S (S * S) (diag_act_fun S)
                                 (fun _ _ _ => (moncat_assoc S _ _ _,moncat_assoc S _ _ _)) _ _
                                 (fun _ => (moncat_lid S _, moncat_lid S _)) _ _
                                 _ _ _
            ); intros; simpl.
    - apply prod_isisomorphism; apply isiso_moncat_assoc.
    - apply path_prod; apply natural_moncat_assoc.
    - apply prod_isisomorphism; apply isiso_moncat_lid.
    - apply path_prod; apply natural_moncat_lid.
    - apply path_prod; apply moncat_coh_tri1.
    - apply path_prod; apply moncat_coh_tri2.
    - apply path_prod; apply moncat_coh_pent.
  Defined.

  Definition group_completion_moncat (S : Symmetric_Monoidal_Category)
    := monoidal_action_cat _ _ (diag_act S).

  
  Definition include_in_gcl (S : Symmetric_Monoidal_Category)
    : Functor S (group_completion_moncat S).
  Proof.
    apply include_in_monoidal_action_cat.
    srapply @Build_Functor.
    - intro a. exact (a,a).
    - intros a b f.
      exact (f,f).
    - reflexivity.
    - reflexivity.
  Defined.

  Definition functor_group_completion_1' (S T : Symmetric_Monoidal_Category)
             (F : Monoidal_Functor S T)
             {x1 x2 y1 y2 : S}
             (f : {s : S & diag_act S (s, (x1, x2)) --> (y1, y2)})
    : {t : T & diag_act T (t, (F x1, F x2)) --> (F y1, F y2)}.
  Proof.
    destruct f as [s [f1 f2]]. simpl in f1, f2.
    exists (F s).
    simpl.
    srefine (((F _1 f1) o (mon_fun_sum _ _ F _ _)^-1) ,((F _1 f2) o (mon_fun_sum _ _ F _ _)^-1));
      apply isiso_mon_fun_sum.
  Defined.

  Lemma welldef_functor_group_completion_1 (S T : Symmetric_Monoidal_Category)
             (F : Monoidal_Functor S T)
             {x1 x2 y1 y2 : S}
             (f g : {s : S & diag_act S (s, (x1, x2)) --> (y1, y2)})
    : monact_relation (diag_act S) _ _ f g
      -> monact_relation (diag_act T) _ _ (functor_group_completion_1' _ _ F f)
                         (functor_group_completion_1' _ _ _ g).
  Proof.
    destruct f as [s f].
    destruct g as [t [g1 g2]]. simpl in *.
    intros [sigma p].
    exists (functor_isomorphic F (sigma)). simpl.
    simpl in p. destruct p. simpl.
    rewrite composition_of. rewrite composition_of.
    apply path_prod; simpl;
      apply  iso_moveL_pV; repeat rewrite associativity;
        rewrite <- (identity_of F);
        rewrite <- natl_mon_fun_sum; simpl;
          rewrite iso_compose_V_pp; reflexivity.
  Defined.

  Definition functor_group_completion (S T : Symmetric_Monoidal_Category)
             (F : Monoidal_Functor S T)
    : Functor (group_completion_moncat S) (group_completion_moncat T).
  Proof.
    srapply @Build_Functor.
    - intros [a b]. exact (F a, F b).
    - intros [x1 x2] [y1 y2].
      srapply @set_quotient_rec.
      { intro f. apply class_of.
        apply functor_group_completion_1'. exact f. }
      intros f g. simpl. intro H.
      apply related_classes_eq.
      apply welldef_functor_group_completion_1. exact H.
    - simpl. intros [x1 x2] [y1 y2] [z1 z2].
      srapply @set_quotient_ind_prop.
      intros [s f].
      srapply @set_quotient_ind_prop.
      intros [t g].
      simpl. apply related_classes_eq.
      exists (iso_mon_fun_sum F t s).
      simpl. destruct f as [f1 f2]. destruct g as [g1 g2]. simpl in *.
      rewrite composition_of. rewrite composition_of. rewrite composition_of. rewrite composition_of.
      repeat rewrite associativity.
      apply path_prod; simpl.
      + apply (ap (fun v => F _1 g1 o v)).
        apply iso_moveR_Vp.
        repeat rewrite <- associativity.
        rewrite natl_mon_fun_sum. apply iso_moveL_pV.
        rewrite associativity.
        rewrite associativity.
        rewrite <- (associativity _ _ _ _ _ (mon_fun_sum S T F (t +' s) x1)).
        rewrite mon_fun_assoc.
        repeat rewrite <- associativity.
        rewrite <- composition_of. simpl. rewrite left_identity.
        rewrite iso_compose_pV_p. rewrite identity_of.
        reflexivity.
      + apply (ap (fun v => F _1 g2 o v)).
        apply iso_moveR_Vp.
        repeat rewrite <- associativity.
        rewrite natl_mon_fun_sum. apply iso_moveL_pV.
        rewrite associativity.
        rewrite associativity.
        rewrite <- (associativity _ _ _ _ _ (mon_fun_sum S T F (t +' s) x2)).
        rewrite mon_fun_assoc.
        repeat rewrite <- associativity.
        rewrite <- composition_of. simpl. rewrite left_identity.
        rewrite iso_compose_pV_p. rewrite identity_of.
        reflexivity.
    - simpl. intros [x1 x2].
      apply related_classes_eq.
      exists (iso_mon_fun_id F).
      simpl. rewrite mon_fun_lid. rewrite mon_fun_lid. simpl.
      rewrite iso_compose_pp_V. rewrite iso_compose_pp_V.
      reflexivity.
  Defined.

  (* move *)
  (* Sum of iso is iso *)
  Definition sum_iso {M : Cat_Magma} {a b c d : M}
             (f : Isomorphic a b) (g : Isomorphic c d)
    : Isomorphic (a +' c) (b +' d).
  Proof.
    apply (functor_isomorphic (binary_op)).
    apply prod_isomorphic.
    - exact f. - exact g.
  Defined.    


  Definition iso_moncat_sum_aa_aa (S : Symmetric_Monoidal_Category)
             (a b c d : S)
    : Isomorphic (a +' (b +' c) +' d) ((a +' b) +' (c +' d)) .
  Proof.
    refine (isomorphic_trans _ (iso_moncat_assoc S _ _ _)).
    refine (sum_iso _ (isomorphic_refl S d)).
    apply isomorphic_sym.
    apply iso_moncat_assoc.
  Defined.


  Definition iso_twist_middle (S : Symmetric_Monoidal_Category)
             (a b c d : S)
    : Isomorphic ((a +' b) +' (c +' d))  ((a +' c) +' (b +' d)).
  Proof.
    refine (isomorphic_trans _ (iso_moncat_sum_aa_aa S _ _ _ _ )).
    refine (isomorphic_trans (isomorphic_sym (iso_moncat_sum_aa_aa S _ _ _ _ )) _ ).
    refine (sum_iso _ (isomorphic_refl S d)).
    refine (sum_iso (isomorphic_refl S a) _).
    apply iso_moncat_sym.
  Defined.

  Definition twist_middle (S : Symmetric_Monoidal_Category)
             (a b c d : S)
    : ((a +' b) +' (c +' d)) --> ((a +' c) +' (b +' d))
    := iso_twist_middle S a b c d.

  Instance isiso_twist_middle (S : Symmetric_Monoidal_Category)
             (a b c d : S)
    : IsIsomorphism (twist_middle S a b c d) := _.
  Arguments twist_middle : simpl never.

  (* Definition coh_twist_middle (S : Symmetric_Monoidal_Category)(a b c d e : S) *)
  (*   : twist_middle S a b (d +' c) e = *)
  (*     (moncat_assoc S a d c +^ 1) o (iso_moncat_assoc S (a +' d) c (b +' e))^-1 o *)
  (*     (1 +^ moncat_assoc S c b e) o (1 +^ (moncat_sym S b c +^ 1)) o *)
  (*     (1 +^ (iso_moncat_assoc S b c e)^-1) o twist_middle S a b d (c +' e) o *)
  (*     (1 +^ moncat_assoc S d c e). *)
  (* Proof. *)
  (*   unfold twist_middle. unfold iso_twist_middle. simpl. *)
  (*   change (binary_op _1 (?f, ?g)) with (f +^ g). *)
  (*   change (binary_op _1 (?f, ?g)) with (f +^ g). *)
  (*   assert (p : moncat_sym S b (d +' c) = *)
  (*           (iso_moncat_assoc S d c b)^-1 o (1 +^ moncat_sym S b c) o *)
  (*             (moncat_assoc S d b c) o (moncat_sym S b d +^ 1) o *)
  (*             (iso_moncat_assoc S b d c)^-1). *)
  (*   { apply iso_moveL_pV. repeat rewrite associativity. *)
  (*     apply iso_moveL_Vp. repeat rewrite <- associativity. *)
  (*     apply moncat_coh_hex. } *)
  (*   rewrite p. clear p. repeat rewrite compose_sum_r. repeat rewrite compose_sum_l. *)
  (*   repeat rewrite <- sum_idmap. *)
  (*   repeat rewrite associativity. *)
  (*   assert (p : forall x y z w : S, *)
  (*              moncat_assoc S x y (z +' w) = *)
  (*              (1 +^ moncat_assoc S y z w) o (moncat_assoc S x (y +' z) w) o *)
  (*               (moncat_assoc S x y z +^ 1) o (iso_moncat_assoc S (x +' y) z w)^-1). *)
  (*   { intros. apply iso_moveL_pV. apply moncat_coh_pent. } *)
  (*   rewrite p. rewrite p. *)
  (*   repeat rewrite compose_sum_r. repeat rewrite compose_sum_l. *)
  (*   repeat rewrite associativity. *)
    

  (*   moncat_coh_pent *)
  (*   asser (moncat_sym S b c +^1 = *)
  (*          (iso_moncat_assoc S c b e)^-1 o (1 +^ moncat_sym S b c) *)
    


  (*   (1 +^ moncat_assoc S x y) = *)
    
    
    
  (*   refine ((associativity _ _ _ _ _ _ _ _)^ @ _). *)
  (*   refine ((associativity _ _ _ _ _ _ _ _)^ @ _). *)
    
    

      
  (*          ) *)

  (*             (moncat_coh_hex S b d c) *)

  (* Definition coh_twist_middle (S : Symmetric_Monoidal_Category)(a b c d e : S) *)
  (*   : twist_middle S a (b +' c) d e = *)
  (*     1 +^ (iso_moncat_assoc S b c e)^-1 o (iso_moncat_assoc S a d (b +' (c +' e)))^-1 o *)
  (*       (1 +^ moncat_assoc S d b (c +' e)) o (1 +^ (moncat_sym S b d +^ 1)) o *)
  (*       (1 +^ twist_middle S b c d e) o (moncat_assoc S a (b +' c) (d +' e)). *)
  (* Proof. *)
    
    
    
    

  (*   change (binary_op _1 (?f, ?g)) with (f +^ g). *)
    
  (*   moncat_coh_hex *)
             

  Lemma natural_moncat_assoc_inv (S : Symmetric_Monoidal_Category) {a b c a' b' c' : S}
               (f : a --> a') (g : b --> b') (h : c --> c')
      : (iso_moncat_assoc S a' b' c')^-1 o (f +^ (g +^ h)) =
        ((f +^ g) +^ h) o (iso_moncat_assoc S a b c)^-1.
  Proof.
    apply iso_moveL_pV.
    rewrite associativity.
    apply iso_moveR_Vp.
    apply inverse. apply natural_moncat_assoc.
  Qed.    
  
  Definition natural_twist_middle (S : Symmetric_Monoidal_Category)
             {a b c d a' b' c' d': S}
             (f : a --> a') (g : b --> b') (h : c --> c') (i : d --> d')
    : (twist_middle S a' b' c' d') o ((f +^ g) +^ (h +^ i)) =
      ((f +^ h) +^ (g +^ i)) o (twist_middle S a b c d).
  Proof.
    simpl. repeat rewrite associativity.
    rewrite natural_moncat_assoc_inv. simpl.
    repeat rewrite <- associativity.
    apply (ap (fun v => v o _)).
    repeat rewrite associativity.
    repeat rewrite <- composition_of. simpl.
    repeat rewrite left_identity. simpl.
    repeat rewrite <- associativity.
    rewrite <- natural_moncat_assoc. simpl.
    repeat rewrite associativity.
    apply (ap (fun v => _ o v)). rewrite <- composition_of. simpl. rewrite right_identity.
    apply (ap (fun v => binary_op _1 v)).
    rewrite natural_moncat_assoc.
    apply (ap (fun v => (v, i))).
    repeat rewrite <- associativity.
    apply (ap (fun v => v o _)).
    rewrite <- natural_moncat_assoc_inv. simpl.
    repeat rewrite associativity. apply (ap (fun v => _ o v)).
    rewrite <- composition_of. simpl. rewrite left_identity.
    rewrite natural_moncat_sym. simpl.
    rewrite <- composition_of. simpl. rewrite right_identity.
    reflexivity.
  Qed.    
  
  Definition sum_group_completion_1' (S : Symmetric_Monoidal_Category)
             {x1 x2 y1 y2 z1 z2 w1 w2 : S}
    :   {s : S & ((diag_act S) _0 (s, (x1, x2)))%object --> (z1, z2)} ->
        {s : S & ((diag_act S) _0 (s, (y1, y2)))%object --> (w1, w2)} ->
        {s : S & ((s +' (x1 +' y1) --> z1 +' w1) * (s +' (x2 +' y2) --> z2 +' w2))%type}.
  Proof.
    intros [s [f1 f2]] [t [g1 g2]]. simpl in *.
    exists (s +' t).            (* perhaps other way? *)
    refine (_ , _).
    - refine (f1 +^ g1 o _). 
      apply twist_middle.
    - refine (f2 +^ g2 o _).
      apply twist_middle.
  Defined.

  Lemma welldef_sum_group_completion_1 (S : Symmetric_Monoidal_Category)
             {x1 x2 y1 y2 z1 z2 w1 w2 : S}
             (f f' : {s : S & ((diag_act S) _0 (s, (x1, x2)))%object --> (z1, z2)})
             (g g' : {s : S & ((diag_act S) _0 (s, (y1, y2)))%object --> (w1, w2)})
    : monact_relation (diag_act S) _ _ f f' ->
      monact_relation (diag_act S) _ _  g g' ->
      monact_relation (diag_act S) (_,_) (_,_)
                      (sum_group_completion_1' S f g)
                      (sum_group_completion_1' S f' g').
  Proof.
    intros [sigma p]. intros [tau q].
    destruct f as [s f]. destruct p.
    destruct g as [t g]. destruct q. simpl in *.
    exists (sum_iso sigma tau).
    destruct f' as [s' [f1 f2]]. destruct g' as [g' [g1 g2]].
    cbn. apply path_prod; simpl.
    - rewrite <- sum_idmap. rewrite associativity.
      rewrite natural_twist_middle. rewrite <- associativity.
      apply (ap (fun v => v o _)).
      refine ((composition_of _ _ _ _ _ _)^ ).
    - rewrite <- sum_idmap. rewrite associativity.
      rewrite natural_twist_middle. rewrite <- associativity.
      apply (ap (fun v => v o _)).
      refine ((composition_of _ _ _ _ _ _)^ ).
  Qed.

  (* (* probably needs left cancellation *) *)
  (* Definition sum_group_completion (S : Symmetric_Monoidal_Category) *)
  (*   : Functor ((group_completion_moncat S) * (group_completion_moncat S)) *)
  (*             (group_completion_moncat S). *)
  (* Proof. *)
  (*   srapply @Build_Functor. *)
  (*   - simpl. intros [[x1  x2] [y1 y2]]. *)
  (*     exact (x1 +' y1, x2 +' y2). *)
  (*   - simpl. intros [[x1 x2] [y1 y2]] [[z1 z2] [w1 w2]]. simpl. *)
  (*     intros [f g]. *)
  (*     revert f g. *)
  (*     srapply @set_quotient_rec2'. *)
  (*     + intros f g. apply class_of. simpl. *)
  (*       apply (sum_group_completion_1' S f g). *)
      (* + simpl. intros f f' g H. *)
      (*   apply related_classes_eq. *)
      (*   apply (welldef_sum_group_completion_1 S f f' g g H). *)
      (*   apply refl_monact_relation. *)
      (* + simpl. intros f g g' H. *)
      (*   apply related_classes_eq. *)
      (*   srefine (welldef_sum_group_completion_1 S f f g g' _ H). *)
      (*   apply refl_monact_relation. *)
  (*   - simpl. intros [[a1 a2] [b1 b2]] [[c1 c2] [d1 d2]] [[e1 e2] [f1 f2]]. *)
  (*     simpl. intros [alpha betta] [gamma dela]. simpl. *)
  (*     revert alpha.  *)
  (*     apply set_quotient_ind_prop. *)
  (*     { intro alpha. exact _. } *)
  (*     intro alpha. revert betta. *)
  (*     apply set_quotient_ind_prop. *)
  (*     { intro betta. exact _. } *)
  (*     intro betta. revert gamma. *)
  (*     apply set_quotient_ind_prop. *)
  (*     { intro gamma. exact _. } *)
  (*     intro gamma. revert dela. *)
  (*     apply set_quotient_ind_prop. *)
  (*     { intro dela. exact _. } *)
  (*     intro dela. simpl. *)
  (*     apply related_classes_eq. *)
  (*     destruct alpha as [s alpha]. *)
  (*     destruct betta as [t betta]. *)
  (*     destruct gamma as [u gamma]. *)
  (*     destruct dela as [v dela]. *)
  (*     srapply @exist. *)
  (*     { simpl. apply (Build_Isomorphic (isiso_twist_middle S _ _ _ _ )). } *)
  (*     cbn. *)
  (*     destruct alpha as [alpha1 alpha2]. destruct betta as [betta1 betta2]. *)
  (*     destruct gamma as [gamma1 gamma2]. destruct dela as [delta1 delta2]. simpl in *. *)
  (*     rewrite compose_sum_r. rewrite compose_sum_r. *)
  (*     rewrite (composition_of binary_op (_,_) (_,_) (_,_) (_,_) (gamma1, delta1)) . *)
  (*     rewrite (composition_of binary_op (_,_) (_,_) (_,_) (_,_) (gamma2, delta2)) . *)
  (*     rewrite (composition_of binary_op (_,_) (_,_) (_,_) (_,_) (_, _)). *)
  (*     rewrite (composition_of binary_op (_,_) (_,_) (_,_) (_,_) (_, _)). *)
  (*     admit. *)
  (*   - admit. *)
  (* Abort. *)
      
        


      
  

End Group_Completion.
    

(* Definition functor_monoidal_action_cat (M N : Monoidal_1Type) (X Y : 1-Type) *)
(*              (act1 : monoidal_action M X) (left_cancel1 : left_faithful act1) *)
(*              (act2 : monoidal_action N Y) (left_cancel2 : left_faithful act2) *)
(*              (f : Monoidal_Map M N) *)
(*              (g : X -> Y) *)
(*              (act_mult : forall (a : M) (x : X), *)
(*                  g (act1 a x) = act2 (f a) (g x)) *)
(*              (act_mult_assoc : forall (a b : M) (x : X), *)
(*                  ap g (montype_act_mult act1 a b x) = *)
(*                  act_mult _ x @ ap011 act2 (montype_map_mult f a b) idpath *)
(*                           @ montype_act_mult act2 (f a) (f b) (g x) *)
(*                           @ (ap011 act2 idpath (act_mult b x))^ *)
(*                           @ (act_mult a _)^) *)
(*              (act_mult_lid : forall (x : X), *)
(*                  ap g (montype_act_id act1 x) = *)
(*                  act_mult montype_id x *)
(*                           @ ap011 act2 (montype_map_id f) idpath *)
(*                           @ montype_act_id act2 (g x)) *)
(*     : Functor (monoidal_action_cat M X act1 left_cancel1) *)
(*               (monoidal_action_cat N Y act2 left_cancel2). *)
(*   Proof. *)
(*     srapply @Build_Functor. *)
(*     - exact g. *)
(*     - simpl. intros x y. *)
(*       intros [s p]. *)
(*       exists (f s). *)
(*       refine (_ @ ap g p). *)
(*       apply inverse. apply act_mult. *)
(*     - intros x y z. *)
(*       intros [s p] [t q]. simpl. *)
(*       destruct q. destruct p. simpl. *)
(*       repeat rewrite concat_p1. *)
(*       apply (path_sigma _ (_;_) (_;_) (montype_map_mult f t s)). *)
(*       simpl. *)
(*       refine (transport_paths_Fl (montype_map_mult f t s) _ @ _). *)
(*       rewrite act_mult_assoc. *)
(*       repeat rewrite concat_p_pp. apply whiskerR. *)
(*       rewrite ap_V. apply whiskerR. *)
(*       apply moveR_pM. rewrite concat_pV. *)
(*       apply moveR_pM. rewrite concat_1p. *)
(*       apply moveR_pM. apply whiskerR. destruct (montype_map_mult f t s). *)
(*       reflexivity. *)
(*     - simpl. intro x. *)
(*       apply (path_sigma _ (_;_) (_;_) (montype_map_id f)). *)
(*       refine (transport_paths_Fl (montype_map_id f) _ @ _). *)
(*       rewrite act_mult_lid. simpl. *)
(*       repeat rewrite concat_pp_p. apply moveR_Vp. apply moveR_Vp. *)
(*       apply whiskerL. apply whiskerR. *)
(*       generalize (montype_map_id f). intro p. destruct p. *)
(*       reflexivity. *)
(*   Defined. *)
              

(*   Definition left_cancel_localize (M : Monoidal_1Type) (X : 1-Type) (act : monoidal_action M X) *)
(*              (left_cancel : left_faithful (@montype_mult M)) *)
(*     : left_faithful (act_on_prod M M X (act_on_self M) act). *)
(*   Proof. *)
(*     unfold left_faithful. *)
(*     intros s t p q [a x]. *)
(*     intro H. apply (left_cancel s t p q a).  *)
(*     refine ((ap_fst_path_prod (z := (s ⊗ a, act s x )) (z' := (t ⊗ a, act t x )) *)
(*                 (ap (fun m : M => m ⊗ a) p) (ap (fun m : M => act m x) p))^ @ _ @ *)
(*              ap_fst_path_prod (z := (s ⊗ a, act s x )) (z' := (t ⊗ a, act t x )) *)
(*                 (ap (fun m : M => m ⊗ a) q) (ap (fun m : M => act m x) q)).  *)
(*     apply (ap (ap fst)). *)
(*     refine (_ @ H @ _). *)
(*     - destruct p. reflexivity. *)
(*     - destruct q. reflexivity. *)
(*   Defined. *)
    

(*   Definition localize_action (M : Monoidal_1Type) (X : 1-Type) (act : monoidal_action M X) *)
(*              (left_cancel : left_faithful (@montype_mult M)) *)
(*     : PreCategory. *)
(*   Proof. *)
(*     apply (monoidal_action_cat M (BuildTruncType 1 (M*X)) (act_on_prod M M X (act_on_self M) act)). *)
(*     apply left_cancel_localize. apply left_cancel. *)
(*   Defined. *)

  

(*   Definition include_in_localize_action (M : Monoidal_1Type) (X : 1-Type) (act : monoidal_action M X) *)
(*              (left_cancel : left_faithful (@montype_mult M)) *)
(*              (x0 : X) *)
(*     : Functor (groupoid_category M) (localize_action M X act left_cancel). *)
(*   Proof. *)
(*     apply include_in_monoidal_action_cat. *)
(*     intro a. exact (a,x0). *)
(*   Defined. *)

(*   (** The group completion of a monoidal category. *) *)
(*   Definition group_completion_moncat (M : Monoidal_1Type) *)
(*              (left_cancel : left_faithful (@montype_mult M)) *)
(*     : PreCategory := *)
(*     localize_action M M (act_on_self M) left_cancel. *)

(*   Definition contr_self_category (M : Monoidal_1Type) *)
(*              (left_cancel : left_faithful (@montype_mult M)) *)
(*              (* (left_cancel : forall (s t : M) (p q : s = t) (a : M), *) *)
(*              (*     ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q) *) *)
(*     : forall x : object (monoidal_action_cat M M (act_on_self M) left_cancel), *)
(*       Contr (morphism (monoidal_action_cat M M (act_on_self M) left_cancel) montype_id x). *)
(*   Proof. *)
(*     simpl. intro a. unfold monoidal_action_morphism. unfold act_on_self. simpl. *)
(*     apply (contr_equiv' {s : M & s = a}). *)
(*     - srapply @equiv_functor_sigma'. *)
(*       { exact equiv_idmap. } *)
(*       intro m. simpl. *)
(*       apply equiv_concat_l. apply montype_moncat_rid. *)
(*     - apply contr_basedpaths'. *)
(*   Defined. *)


(*   (** Given a : M, get an endofunctor +a on the group completion  *) *)
(*   Definition act_on_grp_compl (M : Monoidal_1Type) *)
(*              (left_cancel : left_faithful (@montype_mult M)) *)
(*     : M -> Functor (group_completion_moncat M left_cancel) (group_completion_moncat M left_cancel). *)
(*   Proof. *)
(*     intro a. *)
(*     srapply @Build_Functor. *)
(*     - intros [x1 x2]. exact (montype_mult x1 a, x2). *)
(*     - intros [x1 x2] y. *)
(*       intros [s p]. *)
(*       exists s. *)
(*       apply (path_prod); simpl. *)
(*       + refine (_ @ ap (fun m => montype_mult m a) (ap fst p)). *)
(*         apply inverse. apply montype_assoc. *)
(*       + apply (ap snd p). *)
(*     - intros [x1 x2] y z. *)
(*       intros [s p]. intros [t q]. destruct q. destruct p. *)
(*       simpl. repeat rewrite concat_p1. *)
(*       srapply @path_sigma. *)
(*       { reflexivity. } *)
(*       simpl. *)
(*       rewrite ap_fst_path_prod. rewrite ap_snd_path_prod. *)
(*       rewrite ap_functor_prod. *)
(*       rewrite <- path_prod_pp. rewrite <- path_prod_pp. *)
(*       rewrite concat_p1. simpl. rewrite concat_p1. *)
(*       apply (ap (fun p => path_prod _ _ p _)). *)
(*       rewrite montype_pentagon. *)
(*       repeat rewrite concat_p_pp. *)
(*       apply whiskerR. rewrite ap_V. apply whiskerR. rewrite concat_Vp. *)
(*       apply concat_1p. *)
(*     - intros [x1 x2]. simpl. *)
(*       srapply @path_sigma. *)
(*       { reflexivity. } simpl. *)
(*       rewrite ap_fst_path_prod. rewrite ap_snd_path_prod. *)
(*       apply (ap (fun p => path_prod _ _ p _)). *)
(*       rewrite montype_triangle1. *)
(*       destruct (montype_lid (x1 ⊗ a)). rewrite concat_p1. *)
(*       apply concat_Vp. *)
(*   Defined. *)

(*   (** The action preserves the monoid multiplication.  *) *)
(*   Definition act_on_grp_compl_mult (M : Monoidal_1Type) *)
(*              (left_cancel : left_faithful (@montype_mult M)) *)
(*              (a b : M) (x : M * M) *)
(*     : act_on_grp_compl M left_cancel (montype_mult a b) x = *)
(*       ((act_on_grp_compl M left_cancel b) ((act_on_grp_compl M left_cancel a) x)). *)
(*   Proof. *)
(*     destruct x as [x1 x2]. simpl. *)
(*     apply path_prod; simpl. *)
(*     + apply inverse. apply montype_assoc. *)
(*     + reflexivity. *)
(*   Defined. *)

(*   (** The following results implies that the action is an equivalence after taking the 1-type completion.  *) *)
(*   Definition act_on_grp_compl_inv (M : Monoidal_1Type) *)
(*              (left_cancel : left_faithful (@montype_mult M)) *)
(*     : M -> Functor (group_completion_moncat M left_cancel) (group_completion_moncat M left_cancel). *)
(*   Proof. *)
(*     intro a. *)
(*     srapply @Build_Functor. *)
(*     - intros [x1 x2]. exact (x1, montype_mult x2 a). *)
(*     - intros [x1 x2] y. *)
(*       intros [s p]. *)
(*       exists s. *)
(*       apply (path_prod); simpl. *)
(*       + apply (ap fst p). *)
(*       + refine (_ @ ap (fun m => montype_mult m a) (ap snd p)). *)
(*         apply inverse. apply montype_assoc. *)
(*     - intros [x1 x2] y z. *)
(*       intros [s p]. intros [t q]. destruct q. destruct p. *)
(*       simpl. repeat rewrite concat_p1. *)
(*       srapply @path_sigma. *)
(*       { reflexivity. } *)
(*       simpl. *)
(*       rewrite ap_fst_path_prod. rewrite ap_snd_path_prod. *)
(*       rewrite ap_functor_prod. *)
(*       rewrite <- path_prod_pp. rewrite <- path_prod_pp. *)
(*       rewrite concat_p1. simpl. rewrite concat_p1. *)
(*       apply (ap (fun p => path_prod _ _ _ p)). *)
(*       rewrite montype_pentagon. *)
(*       repeat rewrite concat_p_pp. *)
(*       apply whiskerR. rewrite ap_V. apply whiskerR. rewrite concat_Vp. *)
(*       apply concat_1p. *)
(*     - intros [x1 x2]. simpl. *)
(*       srapply @path_sigma. *)
(*       { reflexivity. } simpl. *)
(*       rewrite ap_fst_path_prod. rewrite ap_snd_path_prod. *)
(*       apply (ap (fun p => path_prod _ _ _ p)). *)
(*       rewrite montype_triangle1. *)
(*       destruct (montype_lid (x2 ⊗ a)). rewrite concat_p1. *)
(*       apply concat_Vp. *)
(*   Defined. *)


(*   Definition act_on_grp_compl_is_sect (M : Symmetric_Monoidal_1Type) *)
(*              (left_cancel : left_faithful (@montype_mult M)) (a : M): *)
(*     NaturalTransformation *)
(*       1%functor *)
(*       ((act_on_grp_compl_inv M left_cancel a) o (act_on_grp_compl M left_cancel a))%functor. *)
(*   Proof. *)
(*     srapply @Build_NaturalTransformation. *)
(*     - intros [x1 x2]. simpl. *)
(*       exists a. *)
(*       apply path_prod; *)
(*         apply smontype_sym. *)
(*     - intros [x1 x2] y. intros [s p]. *)
(*       simpl. destruct p. simpl. *)
(*       rewrite concat_p1. rewrite concat_p1. *)
(*       srapply @path_sigma. *)
(*       { apply smontype_sym. } *)
(*       refine (transport_paths_Fl (smontype_sym a s) _ @ _). simpl. *)
(*       rewrite ap_functor_prod. *)
(*       rewrite <- path_prod_pp. *)
(*       rewrite <- path_prod_pp. *)
(*       rewrite <- path_prod_pp. *)
(*       rewrite ap_fst_path_prod. rewrite ap_snd_path_prod. simpl. rewrite concat_p1. *)
(*       apply moveR_pM. *)
(*       rewrite <- path_prod_VV. *)
(*       rewrite <- path_prod_pp. unfold functor_prod. simpl. *)
(*       transitivity (path_prod (_,_) (_,_) *)
(*                               (ap (fun x : M => smontype_mult x x1) (smontype_sym a s)) *)
(*                               (ap (fun x : M => smontype_mult x x2) (smontype_sym a s)))^. *)
(*       { destruct (smontype_sym a s). reflexivity. } *)
(*       apply (equiv_inj inverse). rewrite inv_V. *)
(*       rewrite <- path_prod_VV. *)
(*       rewrite inv_pV. rewrite inv_pV. *)
(*       rewrite inv_pV. rewrite inv_pV. *)
(*       rewrite smontype_hexagon. rewrite smontype_hexagon. *)
(*       rewrite inv_pp. rewrite inv_pp. *)
(*       repeat rewrite concat_p_pp. *)
(*       reflexivity. *)
(*   Defined. *)

(*   Definition act_on_grp_compl_is_retr (M : Symmetric_Monoidal_1Type) *)
(*              (left_cancel : left_faithful (@montype_mult M)) (a : M): *)
(*     NaturalTransformation *)
(*       1%functor *)
(*       ((act_on_grp_compl M left_cancel a) o (act_on_grp_compl_inv M left_cancel a))%functor. *)
(*   Proof. *)
(*     srapply @Build_NaturalTransformation. *)
(*     - intros [x1 x2]. simpl. *)
(*       exists a. *)
(*       apply path_prod; *)
(*         apply smontype_sym. *)
(*     - intros [x1 x2] y. intros [s p]. *)
(*       simpl. destruct p. simpl. *)
(*       rewrite concat_p1. rewrite concat_p1. *)
(*       srapply @path_sigma. *)
(*       { apply smontype_sym. } *)
(*       refine (transport_paths_Fl (smontype_sym a s) _ @ _). simpl. *)
(*       rewrite ap_functor_prod. *)
(*       rewrite <- path_prod_pp. *)
(*       rewrite <- path_prod_pp. *)
(*       rewrite <- path_prod_pp. *)
(*       rewrite ap_fst_path_prod. rewrite ap_snd_path_prod. simpl. rewrite concat_p1. *)
(*       apply moveR_pM. *)
(*       rewrite <- path_prod_VV. *)
(*       rewrite <- path_prod_pp. unfold functor_prod. simpl. *)
(*       transitivity (path_prod (_,_) (_,_) *)
(*                               (ap (fun x : M => smontype_mult x x1) (smontype_sym a s)) *)
(*                               (ap (fun x : M => smontype_mult x x2) (smontype_sym a s)))^. *)
(*       { destruct (smontype_sym a s). reflexivity. } *)
(*       apply (equiv_inj inverse). rewrite inv_V. *)
(*       rewrite <- path_prod_VV. *)
(*       rewrite inv_pV. rewrite inv_pV. *)
(*       rewrite inv_pV. rewrite inv_pV. *)
(*       rewrite smontype_hexagon. rewrite smontype_hexagon. *)
(*       rewrite inv_pp. rewrite inv_pp. *)
(*       repeat rewrite concat_p_pp. *)
(*       reflexivity. *)
(*   Defined. *)

  
(*   Definition to_groupcompletion (S : Monoidal_1Type) *)
(*              (left_cancel : left_faithful (@montype_mult S)) *)
(*              : Functor (groupoid_category S) (group_completion_moncat S left_cancel). *)
(*   Proof. *)
(*     apply include_in_monoidal_action_cat. *)
(*     simpl. intro a. exact (a, montype_id). *)
(*   Defined. *)

(* End Localize. *)
  
(* Section Univalent_GroupGompletion. *)
(*   (** We show when the group completion is a univalent category.  *) *)
(*   Context (M : Monoidal_1Type) (X : 1-Type) (act : monoidal_action M X) *)
(*           (left_cancel_act : left_faithful act). *)


(*   Lemma idtoiso_is_concat (x y : monoidal_action_cat M X act left_cancel_act) : *)
(*     forall (p : x = y), *)
(*       (@idtoiso _ x y p) = *)
(*       (montype_id; montype_act_id _ x @ p) :> morphism _ x y. *)
(*   Proof. *)
(*     intros []. simpl. *)
(*     srapply @path_sigma. { reflexivity. } *)
(*     simpl. apply (concat_p1 _)^. *)
(*   Defined. *)

(*   Definition equiv_path_isomorphic {C : PreCategory} (x y : C) (f g : (x <~=~> y)%category) : *)
(*     (f = g :> morphism C x y) <~> f = g *)
(*     := BuildEquiv _ _ (path_isomorphic f g) _. *)

(*   Lemma fiber_idtoiso (x y : monoidal_action_cat M X act left_cancel_act) (f : (x <~=~> y) %category) : *)
(*     hfiber (@idtoiso _ x y) f <~> *)
(*            ((morphism_isomorphic (Isomorphic := f)).1 = montype_id). *)
(*   Proof. *)
(*     unfold hfiber. *)
(*     transitivity {p : x = y & (montype_id; montype_act_id _ x @ p) = f :> morphism _ x y}. *)
(*     - apply equiv_functor_sigma_id. *)
(*       intro p. *)
(*       refine (_ oE (equiv_path_isomorphic *)
(*                       x y *)
(*                       _ *)
(*                       f)^-1).       *)
(*       apply equiv_concat_l. *)
(*       apply inverse. apply idtoiso_is_concat. *)
(*     - destruct f as [[s q] isiso]. simpl. *)
(*       transitivity {p : x = y & *)
(*                         {r : montype_id = s & *)
(*                              (montype_act_id act x)^ @ ap (fun a : M => act a x) r @ q = p}}. *)
(*       { apply equiv_functor_sigma_id. intro p. *)
(*         refine (_ oE (equiv_path_sigma _ _ _ )). simpl. *)
(*         apply equiv_functor_sigma_id. intro r. *)
(*         destruct r. simpl. destruct p.  *)
(*         refine (_ oE equiv_moveL_Vp _ _ _). *)
(*         refine (equiv_path_inverse _ _ oE _). *)
(*         apply equiv_concat_r. apply whiskerR. apply inverse. apply concat_p1. } *)
(*       transitivity {r : montype_id = s & *)
(*                         {p : x = y & *)
(*                              ((montype_act_id act x)^ @ ap (fun a : M => act a x) r) @ q = p}}. *)
(*       { srapply @equiv_adjointify. *)
(*         - intros [p [r h]]. exact (r; (p; h)). *)
(*         - intros [r [p h]]. exact (p; (r; h)). *)
(*         - intros [r [p h]]. reflexivity. *)
(*         - intros [p [r h]]. reflexivity. } *)
(*       refine (equiv_path_inverse _ _ oE _). *)
(*       apply equiv_sigma_contr. intro r. *)
(*       apply contr_basedpaths. *)
(*   Defined. *)
    

(*   Context (unit_is_id : forall s t: M, montype_mult s t = montype_id -> s = montype_id) *)
(*           (contr_component_id : forall (a : M), IsHProp (montype_id = a)). *)

(*   Definition univalent_monactcat (x y : monoidal_action_cat M X act left_cancel_act) : *)
(*     IsEquiv (@Category.idtoiso _ x y). *)
(*   Proof. *)
(*     apply isequiv_fcontr. intro f. *)
(*     srefine (contr_equiv' _ (equiv_inverse (fiber_idtoiso x y f))). *)
(*     destruct f as [[s p] isiso]. simpl. *)
(*     apply (contr_equiv' (montype_id = s)). *)
(*     { apply equiv_path_inverse. } *)
(*     apply contr_inhabited_hprop. *)
(*     { apply contr_component_id. } *)
(*     apply inverse. *)
(*     destruct isiso as [[t q] ]. simpl in *. *)
(*     apply (unit_is_id s t). *)
(*     apply ((equiv_path_sigma _ _ _) right_inverse). *)
(*   Defined. *)
(* End Univalent_GroupGompletion. *)
     









