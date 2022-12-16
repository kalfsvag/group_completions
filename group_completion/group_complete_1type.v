Require Import HoTT.
Require Import HoTT.Categories Category.
From GCTT Require Import categories sigma_lemmas path_lemmas.
From GCTT Require Export monoidal_1type.


Section Localize.

  (** if we have a monoidal action with left_cancellation, we can build a category with objects X and
       arrows  [{m : M & m ⊗ x = m ⊗ y}] *)
  Definition monoidal_action_morphism (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X) :
    (X -> X -> Type) := fun x y => {s : M & a s x = y}.

  Instance isset_mon_morphism (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X) (x1 x2 : X)
           (left_cancel : left_faithful a)
    : IsHSet (monoidal_action_morphism M X a x1 x2).
  Proof.
    unfold monoidal_action_morphism.
    intros [s1 p1] [s2 p2].
    apply (trunc_equiv' {q : s1 = s2 & transport (fun s => a s x1 = x2) q p1 = p2}).
    { apply equiv_inverse.
      apply (equiv_path_sigma (fun s : M => a s x1 = x2) (s1; p1) (s2; p2) ). }
    (* apply (trunc_equiv' {q : s1 = s2 & p1 = (ap (fun s => a s x1) q) @ p2}). *)
    apply (trunc_equiv' {q : s1 = s2 & p1 = action_on_path a x1 q @ p2}).
    { apply equiv_functor_sigma_id. intro q. destruct q. simpl. destruct p2. apply equiv_idmap. }
    apply trunc_sigma'.
    + intro p. exact _.
    + simpl.
      intros [q1 r1] [q2 r2]. simpl.
      apply contr_inhabited_hprop. { exact _. }
      apply (left_cancel _ _ q1 q2 x1).
      transitivity (p1 @ p2^).
      { apply moveL_pV. apply r1^. }
      { apply moveR_pV. apply r2. }
  Defined.

  Definition monoidal_action_cat (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X)
             (left_cancel : left_faithful a)
    : PreCategory.
  Proof.
    srefine (Build_PreCategory (monoidal_action_morphism M X a) _ _ _ _ _ (fun x1 x2 => isset_mon_morphism M X a x1 x2 left_cancel)).
    (* identity *)
    - intro x. exists montype_id. apply montype_act_id.
    (* composition *)
    - intros x y z.
      intros [s1 p1] [s2 p2].
      exists (s1 ⊗ s2).
      exact (montype_act_mult a s1 s2 x @ ap (a s1) p2 @ p1).
    (* associativity *)
    - intros x1 x2 x3 x4 [s1 []] [s2 []] [s3 []]. repeat rewrite ap_1. repeat rewrite concat_p1.
      srapply @path_sigma.
      { apply montype_assoc. }
      cbn.
      refine (transport_paths_Fl (montype_assoc s3 s2 s1) _ @ _).
      rewrite montype_act_pentagon. repeat rewrite inv_pp. repeat rewrite inv_V.
      apply moveR_pM.
      repeat rewrite concat_pp_p. apply whiskerL. apply whiskerL.
      apply inverse. apply inv_pp.
    (* left identity *)
    - simpl.
      intros x1 x2 [s []]. simpl. rewrite concat_p1.
      srapply @path_sigma.
      { apply montype_lid. }
      simpl. 
      refine (transport_paths_Fl (montype_lid s) _ @ _).
      apply moveR_Vp. refine (_ @ (concat_p1 _)^). apply inverse.
      apply montype_act_triangle1.
    (* right identity *)
    - simpl.
      intros x1 x2 [s []]. simpl. rewrite concat_p1.
      srapply @path_sigma.
      { apply montype_rid. } simpl. 
      refine (transport_paths_Fl (montype_rid s) _ @ _).
      apply moveR_Vp. refine (_ @ (concat_p1 _)^). apply inverse.
      apply montype_act_triangle2.
  Defined.
  
  Definition include_in_monoidal_action_cat (M : Monoidal_1Type) (X : 1-Type)
             (act : monoidal_action M X)
             (left_cancel : left_faithful act)
             (f : M -> X)

    : Functor (groupoid_category M) (monoidal_action_cat M X act left_cancel).
  Proof.
    srapply @Build_Functor.
    - simpl. exact f.
    - intros a b. simpl.
      intros []. apply (identity (C := monoidal_action_cat M X act left_cancel)).
    - intros a b c. intros p q. destruct q. destruct p.
      apply inverse. apply identity_identity.
    - reflexivity.
  Defined.

  Definition functor_monoidal_action_cat (M N : Monoidal_1Type) (X Y : 1-Type)
             (act1 : monoidal_action M X) (left_cancel1 : left_faithful act1)
             (act2 : monoidal_action N Y) (left_cancel2 : left_faithful act2)
             (f : Monoidal_Map M N)
             (g : X -> Y)
             (act_mult : forall (a : M) (x : X),
                 g (act1 a x) = act2 (f a) (g x))
             (act_mult_assoc : forall (a b : M) (x : X),
                 ap g (montype_act_mult act1 a b x) =
                 act_mult _ x @ ap011 act2 (montype_map_mult f a b) idpath
                          @ montype_act_mult act2 (f a) (f b) (g x)
                          @ (ap011 act2 idpath (act_mult b x))^
                          @ (act_mult a _)^)
             (act_mult_lid : forall (x : X),
                 ap g (montype_act_id act1 x) =
                 act_mult montype_id x
                          @ ap011 act2 (montype_map_id f) idpath
                          @ montype_act_id act2 (g x))
    : Functor (monoidal_action_cat M X act1 left_cancel1)
              (monoidal_action_cat N Y act2 left_cancel2).
  Proof.
    srapply @Build_Functor.
    - exact g.
    - simpl. intros x y.
      intros [s p].
      exists (f s).
      refine (_ @ ap g p).
      apply inverse. apply act_mult.
    - intros x y z.
      intros [s p] [t q]. simpl.
      destruct q. destruct p. simpl.
      repeat rewrite concat_p1.
      apply (path_sigma _ (_;_) (_;_) (montype_map_mult f t s)).
      simpl.
      refine (transport_paths_Fl (montype_map_mult f t s) _ @ _).
      rewrite act_mult_assoc.
      repeat rewrite concat_p_pp. apply whiskerR.
      rewrite ap_V. apply whiskerR.
      apply moveR_pM. rewrite concat_pV.
      apply moveR_pM. rewrite concat_1p.
      apply moveR_pM. apply whiskerR. destruct (montype_map_mult f t s).
      reflexivity.
    - simpl. intro x.
      apply (path_sigma _ (_;_) (_;_) (montype_map_id f)).
      refine (transport_paths_Fl (montype_map_id f) _ @ _).
      rewrite act_mult_lid. simpl.
      repeat rewrite concat_pp_p. apply moveR_Vp. apply moveR_Vp.
      apply whiskerL. apply whiskerR.
      generalize (montype_map_id f). intro p. destruct p.
      reflexivity.
  Defined.
              

  Definition left_cancel_localize (M : Monoidal_1Type) (X : 1-Type) (act : monoidal_action M X)
             (left_cancel : left_faithful (@montype_mult M))
    : left_faithful (act_on_prod M M X (act_on_self M) act).
  Proof.
    unfold left_faithful.
    intros s t p q [a x].
    intro H. apply (left_cancel s t p q a). 
    refine ((ap_fst_path_prod (z := (s ⊗ a, act s x )) (z' := (t ⊗ a, act t x ))
                (ap (fun m : M => m ⊗ a) p) (ap (fun m : M => act m x) p))^ @ _ @
             ap_fst_path_prod (z := (s ⊗ a, act s x )) (z' := (t ⊗ a, act t x ))
                (ap (fun m : M => m ⊗ a) q) (ap (fun m : M => act m x) q)). 
    apply (ap (ap fst)).
    refine (_ @ H @ _).
    - destruct p. reflexivity.
    - destruct q. reflexivity.
  Defined.
    

  Definition localize_action (M : Monoidal_1Type) (X : 1-Type) (act : monoidal_action M X)
             (left_cancel : left_faithful (@montype_mult M))
    : PreCategory.
  Proof.
    apply (monoidal_action_cat M (BuildTruncType 1 (M*X)) (act_on_prod M M X (act_on_self M) act)).
    apply left_cancel_localize. apply left_cancel.
  Defined.

  

  Definition include_in_localize_action (M : Monoidal_1Type) (X : 1-Type) (act : monoidal_action M X)
             (left_cancel : left_faithful (@montype_mult M))
             (x0 : X)
    : Functor (groupoid_category M) (localize_action M X act left_cancel).
  Proof.
    apply include_in_monoidal_action_cat.
    intro a. exact (a,x0).
  Defined.

  (** The group completion of a monoidal category. *)
  Definition group_completion_moncat (M : Monoidal_1Type)
             (left_cancel : left_faithful (@montype_mult M))
    : PreCategory :=
    localize_action M M (act_on_self M) left_cancel.

  Definition contr_self_category (M : Monoidal_1Type)
             (left_cancel : left_faithful (@montype_mult M))
             (* (left_cancel : forall (s t : M) (p q : s = t) (a : M), *)
             (*     ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q) *)
    : forall x : object (monoidal_action_cat M M (act_on_self M) left_cancel),
      Contr (morphism (monoidal_action_cat M M (act_on_self M) left_cancel) montype_id x).
  Proof.
    simpl. intro a. unfold monoidal_action_morphism. unfold act_on_self. simpl.
    apply (contr_equiv' {s : M & s = a}).
    - srapply @equiv_functor_sigma'.
      { exact equiv_idmap. }
      intro m. simpl.
      apply equiv_concat_l. apply montype_rid.
    - apply contr_basedpaths'.
  Defined.


  (** Given a : M, get an endofunctor +a on the group completion  *)
  Definition act_on_grp_compl (M : Monoidal_1Type)
             (left_cancel : left_faithful (@montype_mult M))
    : M -> Functor (group_completion_moncat M left_cancel) (group_completion_moncat M left_cancel).
  Proof.
    intro a.
    srapply @Build_Functor.
    - intros [x1 x2]. exact (montype_mult x1 a, x2).
    - intros [x1 x2] y.
      intros [s p].
      exists s.
      apply (path_prod); simpl.
      + refine (_ @ ap (fun m => montype_mult m a) (ap fst p)).
        apply inverse. apply montype_assoc.
      + apply (ap snd p).
    - intros [x1 x2] y z.
      intros [s p]. intros [t q]. destruct q. destruct p.
      simpl. repeat rewrite concat_p1.
      srapply @path_sigma.
      { reflexivity. }
      simpl.
      rewrite ap_fst_path_prod. rewrite ap_snd_path_prod.
      rewrite ap_functor_prod.
      rewrite <- path_prod_pp. rewrite <- path_prod_pp.
      rewrite concat_p1. simpl. rewrite concat_p1.
      apply (ap (fun p => path_prod _ _ p _)).
      rewrite montype_pentagon.
      repeat rewrite concat_p_pp.
      apply whiskerR. rewrite ap_V. apply whiskerR. rewrite concat_Vp.
      apply concat_1p.
    - intros [x1 x2]. simpl.
      srapply @path_sigma.
      { reflexivity. } simpl.
      rewrite ap_fst_path_prod. rewrite ap_snd_path_prod.
      apply (ap (fun p => path_prod _ _ p _)).
      rewrite montype_triangle1.
      destruct (montype_lid (x1 ⊗ a)). rewrite concat_p1.
      apply concat_Vp.
  Defined.

  (** The action preserves the monoid multiplication.  *)
  Definition act_on_grp_compl_mult (M : Monoidal_1Type)
             (left_cancel : left_faithful (@montype_mult M))
             (a b : M) (x : M * M)
    : act_on_grp_compl M left_cancel (montype_mult a b) x =
      ((act_on_grp_compl M left_cancel b) ((act_on_grp_compl M left_cancel a) x)).
  Proof.
    destruct x as [x1 x2]. simpl.
    apply path_prod; simpl.
    + apply inverse. apply montype_assoc.
    + reflexivity.
  Defined.

  (** The following results implies that the action is an equivalence after taking the 1-type completion.  *)
  Definition act_on_grp_compl_inv (M : Monoidal_1Type)
             (left_cancel : left_faithful (@montype_mult M))
    : M -> Functor (group_completion_moncat M left_cancel) (group_completion_moncat M left_cancel).
  Proof.
    intro a.
    srapply @Build_Functor.
    - intros [x1 x2]. exact (x1, montype_mult x2 a).
    - intros [x1 x2] y.
      intros [s p].
      exists s.
      apply (path_prod); simpl.
      + apply (ap fst p).
      + refine (_ @ ap (fun m => montype_mult m a) (ap snd p)).
        apply inverse. apply montype_assoc.
    - intros [x1 x2] y z.
      intros [s p]. intros [t q]. destruct q. destruct p.
      simpl. repeat rewrite concat_p1.
      srapply @path_sigma.
      { reflexivity. }
      simpl.
      rewrite ap_fst_path_prod. rewrite ap_snd_path_prod.
      rewrite ap_functor_prod.
      rewrite <- path_prod_pp. rewrite <- path_prod_pp.
      rewrite concat_p1. simpl. rewrite concat_p1.
      apply (ap (fun p => path_prod _ _ _ p)).
      rewrite montype_pentagon.
      repeat rewrite concat_p_pp.
      apply whiskerR. rewrite ap_V. apply whiskerR. rewrite concat_Vp.
      apply concat_1p.
    - intros [x1 x2]. simpl.
      srapply @path_sigma.
      { reflexivity. } simpl.
      rewrite ap_fst_path_prod. rewrite ap_snd_path_prod.
      apply (ap (fun p => path_prod _ _ _ p)).
      rewrite montype_triangle1.
      destruct (montype_lid (x2 ⊗ a)). rewrite concat_p1.
      apply concat_Vp.
  Defined.


  Definition act_on_grp_compl_is_sect (M : Symmetric_Monoidal_1Type)
             (left_cancel : left_faithful (@montype_mult M)) (a : M):
    NaturalTransformation
      1%functor
      ((act_on_grp_compl_inv M left_cancel a) o (act_on_grp_compl M left_cancel a))%functor.
  Proof.
    srapply @Build_NaturalTransformation.
    - intros [x1 x2]. simpl.
      exists a.
      apply path_prod;
        apply smontype_sym.
    - intros [x1 x2] y. intros [s p].
      simpl. destruct p. simpl.
      rewrite concat_p1. rewrite concat_p1.
      srapply @path_sigma.
      { apply smontype_sym. }
      refine (transport_paths_Fl (smontype_sym a s) _ @ _). simpl.
      rewrite ap_functor_prod.
      rewrite <- path_prod_pp.
      rewrite <- path_prod_pp.
      rewrite <- path_prod_pp.
      rewrite ap_fst_path_prod. rewrite ap_snd_path_prod. simpl. rewrite concat_p1.
      apply moveR_pM.
      rewrite <- path_prod_VV.
      rewrite <- path_prod_pp. unfold functor_prod. simpl.
      transitivity (path_prod (_,_) (_,_)
                              (ap (fun x : M => smontype_mult x x1) (smontype_sym a s))
                              (ap (fun x : M => smontype_mult x x2) (smontype_sym a s)))^.
      { destruct (smontype_sym a s). reflexivity. }
      apply (equiv_inj inverse). rewrite inv_V.
      rewrite <- path_prod_VV.
      rewrite inv_pV. rewrite inv_pV.
      rewrite inv_pV. rewrite inv_pV.
      rewrite smontype_hexagon. rewrite smontype_hexagon.
      rewrite inv_pp. rewrite inv_pp.
      repeat rewrite concat_p_pp.
      reflexivity.
  Defined.

  Definition act_on_grp_compl_is_retr (M : Symmetric_Monoidal_1Type)
             (left_cancel : left_faithful (@montype_mult M)) (a : M):
    NaturalTransformation
      1%functor
      ((act_on_grp_compl M left_cancel a) o (act_on_grp_compl_inv M left_cancel a))%functor.
  Proof.
    srapply @Build_NaturalTransformation.
    - intros [x1 x2]. simpl.
      exists a.
      apply path_prod;
        apply smontype_sym.
    - intros [x1 x2] y. intros [s p].
      simpl. destruct p. simpl.
      rewrite concat_p1. rewrite concat_p1.
      srapply @path_sigma.
      { apply smontype_sym. }
      refine (transport_paths_Fl (smontype_sym a s) _ @ _). simpl.
      rewrite ap_functor_prod.
      rewrite <- path_prod_pp.
      rewrite <- path_prod_pp.
      rewrite <- path_prod_pp.
      rewrite ap_fst_path_prod. rewrite ap_snd_path_prod. simpl. rewrite concat_p1.
      apply moveR_pM.
      rewrite <- path_prod_VV.
      rewrite <- path_prod_pp. unfold functor_prod. simpl.
      transitivity (path_prod (_,_) (_,_)
                              (ap (fun x : M => smontype_mult x x1) (smontype_sym a s))
                              (ap (fun x : M => smontype_mult x x2) (smontype_sym a s)))^.
      { destruct (smontype_sym a s). reflexivity. }
      apply (equiv_inj inverse). rewrite inv_V.
      rewrite <- path_prod_VV.
      rewrite inv_pV. rewrite inv_pV.
      rewrite inv_pV. rewrite inv_pV.
      rewrite smontype_hexagon. rewrite smontype_hexagon.
      rewrite inv_pp. rewrite inv_pp.
      repeat rewrite concat_p_pp.
      reflexivity.
  Defined.

  
  Definition to_groupcompletion (S : Monoidal_1Type)
             (left_cancel : left_faithful (@montype_mult S))
             : Functor (groupoid_category S) (group_completion_moncat S left_cancel).
  Proof.
    apply include_in_monoidal_action_cat.
    simpl. intro a. exact (a, montype_id).
  Defined.

End Localize.
  
Section Univalent_GroupGompletion.
  (** We show when the group completion is a univalent category.  *)
  Context (M : Monoidal_1Type) (X : 1-Type) (act : monoidal_action M X)
          (left_cancel_act : left_faithful act).


  Lemma idtoiso_is_concat (x y : monoidal_action_cat M X act left_cancel_act) :
    forall (p : x = y),
      (@idtoiso _ x y p) =
      (montype_id; montype_act_id _ x @ p) :> morphism _ x y.
  Proof.
    intros []. simpl.
    srapply @path_sigma. { reflexivity. }
    simpl. apply (concat_p1 _)^.
  Defined.

  Definition equiv_path_isomorphic {C : PreCategory} (x y : C) (f g : (x <~=~> y)%category) :
    (f = g :> morphism C x y) <~> f = g
    := BuildEquiv _ _ (path_isomorphic f g) _.

  Lemma fiber_idtoiso (x y : monoidal_action_cat M X act left_cancel_act) (f : (x <~=~> y) %category) :
    hfiber (@idtoiso _ x y) f <~>
           ((morphism_isomorphic (Isomorphic := f)).1 = montype_id).
  Proof.
    unfold hfiber.
    transitivity {p : x = y & (montype_id; montype_act_id _ x @ p) = f :> morphism _ x y}.
    - apply equiv_functor_sigma_id.
      intro p.
      refine (_ oE (equiv_path_isomorphic
                      x y
                      _
                      f)^-1).      
      apply equiv_concat_l.
      apply inverse. apply idtoiso_is_concat.
    - destruct f as [[s q] isiso]. simpl.
      transitivity {p : x = y &
                        {r : montype_id = s &
                             (montype_act_id act x)^ @ ap (fun a : M => act a x) r @ q = p}}.
      { apply equiv_functor_sigma_id. intro p.
        refine (_ oE (equiv_path_sigma _ _ _ )). simpl.
        apply equiv_functor_sigma_id. intro r.
        destruct r. simpl. destruct p. 
        refine (_ oE equiv_moveL_Vp _ _ _).
        refine (equiv_path_inverse _ _ oE _).
        apply equiv_concat_r. apply whiskerR. apply inverse. apply concat_p1. }
      transitivity {r : montype_id = s &
                        {p : x = y &
                             ((montype_act_id act x)^ @ ap (fun a : M => act a x) r) @ q = p}}.
      { srapply @equiv_adjointify.
        - intros [p [r h]]. exact (r; (p; h)).
        - intros [r [p h]]. exact (p; (r; h)).
        - intros [r [p h]]. reflexivity.
        - intros [p [r h]]. reflexivity. }
      refine (equiv_path_inverse _ _ oE _).
      apply equiv_sigma_contr. intro r.
      apply contr_basedpaths.
  Defined.
    

  Context (unit_is_id : forall s t: M, montype_mult s t = montype_id -> s = montype_id)
          (contr_component_id : forall (a : M), IsHProp (montype_id = a)).

  Definition univalent_monactcat (x y : monoidal_action_cat M X act left_cancel_act) :
    IsEquiv (@Category.idtoiso _ x y).
  Proof.
    apply isequiv_fcontr. intro f.
    srefine (contr_equiv' _ (equiv_inverse (fiber_idtoiso x y f))).
    destruct f as [[s p] isiso]. simpl.
    apply (contr_equiv' (montype_id = s)).
    { apply equiv_path_inverse. }
    apply contr_inhabited_hprop.
    { apply contr_component_id. }
    apply inverse.
    destruct isiso as [[t q] ]. simpl in *.
    apply (unit_is_id s t).
    apply ((equiv_path_sigma _ _ _) right_inverse).
  Defined.
End Univalent_GroupGompletion.
     
