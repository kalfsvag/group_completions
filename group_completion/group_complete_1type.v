Require Import HoTT.
Require Import HoTT.Categories Category.
From A_BPQ Require Import categories sigma_lemmas.
From A_BPQ Require Export monoidal_1type.


Section Localize.

  (* if we have a monoidal action with left_cancellation, we can build a category with objects X and arrows*)
  (* {m : M & m ⊗ x = m ⊗ y} *)
  Definition monoidal_action_morphism (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X) :
    (X -> X -> Type) := fun x y => {s : M & a s x = y}.

  Instance isset_mon_morphism (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X) (x1 x2 : X)
           (left_cancel : left_faithful a)
    (* (left_cancel : forall (s t : M) (p q : s = t) (x : X), *)
    (*              action_on_path a x p = action_on_path a x q -> p = q)  *):
    IsHSet (monoidal_action_morphism M X a x1 x2).
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
             (* (left_cancel : forall (s t : M) (p q : s = t) (x : X), *)
             (*     action_on_path a x p = action_on_path a x q -> p = q) *)
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

  (* Definition include_in_monoidal_action_cat (M : Monoidal_1Type) (X : 1-Type) *)
  (*            (act : monoidal_action M X) *)
  (*            (left_cancel : left_faithful act) *)
             
  (*   : Functor (groupoid_category X) (monoidal_action_cat M X act left_cancel). *)
  (* Proof. *)
  (*   srapply @Build_Functor. *)
  (*   - simpl. exact idmap. *)
  (*   - intros a b. simpl. *)
  (*     intros []. apply (identity (C := monoidal_action_cat M X act left_cancel)). *)
  (*   - intros a b c. intros p q. destruct q. destruct p. *)
  (*     apply inverse. apply identity_identity. *)
  (*   - reflexivity. *)
  (* Defined. *)

  
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
              

  (* Definition monoidal_action_fun_obj (M : Symmetric_Monoidal_1Type) (X : 1-Type) *)
  (*            (act : monoidal_action M X) (a : M) *)
  (*   : X -> X. *)
  (* Proof. *)
  (*   simpl. apply act. exact a. *)
  (* Defined. *)

  (* Definition monoidal_action_fun_morphism (M : Symmetric_Monoidal_1Type) (X : 1-Type) *)
  (*            (act : monoidal_action M X) (left_cancel : left_faithful act) (a : M) (x y : X) *)
  (*   : morphism (monoidal_action_cat M X act left_cancel) x y -> *)
  (*     morphism (monoidal_action_cat M X act left_cancel) (act a x) (act a y). *)
  (* Proof. *)
  (*   intros [s p]. *)
  (*   exists s. *)
  (*   refine ((montype_act_mult _ _ _ _)^ @ _). *)
  (*   refine (ap10 (ap act (smontype_sym _ _ )^) x @ _). *)
  (*   refine (montype_act_mult _ _ _ _ @ _). *)
  (*   apply (ap (act a) p). *)
  (* Defined. *)

  (* Definition monoidal_action_fun_compose (M : Symmetric_Monoidal_1Type) (X : 1-Type) *)
  (*            (act : monoidal_action M X) (left_cancel : left_faithful act) (a : M) (x y z: X) *)
  (*            (f : morphism (monoidal_action_cat M X act left_cancel) x y) *)
  (*            (g : morphism (monoidal_action_cat M X act left_cancel) y z) *)
  (*   : monoidal_action_fun_morphism M X act left_cancel a x z (g o f)%morphism = *)
  (*     (monoidal_action_fun_morphism M X act left_cancel a y z g o *)
  (*      monoidal_action_fun_morphism M X act left_cancel a x y f)%morphism. *)
  (* Proof. *)
  (*   destruct f as [s p]. destruct g as [t q]. simpl. *)
  (*   destruct p. destruct q. *)
  (*   srapply @path_sigma. *)
  (*   { reflexivity. } *)
  (*   simpl. repeat rewrite concat_p1. *)

  (*   apply inverse. apply moveR_Mp. apply moveR_Vp. apply moveR_pM. *)
  (*   transitivity ((montype_act_mult act _ _ x)^ @ *)
  (*                                                 (ap10 (ap act (ap (fun m => smontype_mult m s) (smontype_sym a t))^) x) *)
  (*                                                 @ (montype_act_mult act _ _ x)). *)
  (*   { destruct (smontype_sym a t). simpl. *)
  (*     rewrite concat_p1. rewrite concat_Vp. reflexivity. } *)
  (*   apply moveR_pM. apply moveR_Vp. *)
  (*   rewrite smontype_hexagon. *)
  (*   assert (H : forall (n1 n2: M) (p: n1 = n2), ap10 (ap act p) x = ap (fun m => act m x) p). *)
  (*   { intros m n. intros []. reflexivity. } *)
  (*   rewrite H. rewrite H. rewrite H. clear H. *)
  (*   rewrite ap_V. repeat rewrite ap_pp. *)
  (*   repeat rewrite ap_V.  *)
    
  (*   rewrite montype_act_pentagon.  rewrite montype_act_pentagon.  rewrite montype_act_pentagon. *)
  (*   repeat rewrite inv_pp. repeat rewrite inv_V. *)
  (*   repeat rewrite concat_p_pp. *)
  (*   repeat apply whiskerR. *)
  (*   repeat rewrite concat_pp_p. repeat apply whiskerL. *)
  (*   cut (forall (n1 n2 : M) (p : n1 = n2), *)
  (*           (montype_act_mult act t n1 x)^ @ *)
  (*                                            (ap (fun m : M => act m x) (ap (smontype_mult t) p) @ *)
  (*                                                montype_act_mult act t n2 x) = ap (act t) (ap (fun m : M => act m x) p)). *)
  (*   { intro H. apply H. } *)
  (*   intros n1 n2. intros []. simpl. rewrite concat_1p. apply concat_Vp. *)
  (* Qed. *)

  (* Definition monoidal_action_fun_id (M : Symmetric_Monoidal_1Type) (X : 1-Type) *)
  (*            (act : monoidal_action M X) (left_cancel : left_faithful act) (a : M) (x : X) *)
  (*   : monoidal_action_fun_morphism M X act left_cancel a x x 1%morphism = *)
  (*     1%morphism. *)
  (* Proof. *)
  (*   rewrite <- (identity_identity (monoidal_action_cat M X act left_cancel) x). *)
  (*   rewrite monoidal_action_fun_compose. *)
  (*   simpl. *)
  (*   srapply @path_sigma. *)
  (*   - simpl. apply smontype_lid. *)
  (*   - simpl. refine (transport_paths_FlFr (smontype_lid smontype_id) _ @ _). *)
      
      

  (* Definition monoidal_action_fun (M : Symmetric_Monoidal_1Type) (X : 1-Type) (act : monoidal_action M X) *)
  (*            (left_cancel : left_faithful act) (a : M) *)
  (*   : Functor (monoidal_action_cat M X act left_cancel) (monoidal_action_cat M X act left_cancel). *)
  (* Proof. *)
  (*   srapply @Build_Functor. *)
  (*   - simpl. apply act. exact a. *)
  (*   - simpl. intros x y. *)
  (*     intros [s p]. *)
  (*     exists s. *)
  (*     refine ((montype_act_mult _ _ _ _)^ @ _). *)
  (*     refine (ap10 (ap act (smontype_sym _ _ )^) x @ _). *)
  (*     refine (montype_act_mult _ _ _ _ @ _). *)
  (*     apply (ap (act a) p). *)
  (*   - simpl. intros x y z. *)
  (*     simpl. *)
  (*     intros [s p] [t q]. *)
  (*     destruct p. destruct q. *)
  (*     srapply @path_sigma. *)
  (*     { reflexivity. } *)
  (*     simpl. repeat rewrite concat_p1. *)

  (*     apply inverse. apply moveR_Mp. apply moveR_Vp. apply moveR_pM. *)
  (*     transitivity ((montype_act_mult act _ _ x)^ @ *)
  (*                   (ap10 (ap act (ap (fun m => smontype_mult m s) (smontype_sym a t))^) x) *)
  (*                    @ (montype_act_mult act _ _ x)). *)
  (*     { destruct (smontype_sym a t). simpl. *)
  (*       rewrite concat_p1. rewrite concat_Vp. reflexivity. } *)
  (*     apply moveR_pM. apply moveR_Vp. *)
  (*     rewrite smontype_hexagon. *)
  (*     assert (H : forall (n1 n2: M) (p: n1 = n2), ap10 (ap act p) x = ap (fun m => act m x) p). *)
  (*     { intros m n. intros []. reflexivity. } *)
  (*     rewrite H. rewrite H. rewrite H. clear H. *)
  (*     rewrite ap_V. repeat rewrite ap_pp. *)
  (*     repeat rewrite ap_V.  *)
      
  (*     rewrite montype_act_pentagon.  rewrite montype_act_pentagon.  rewrite montype_act_pentagon. *)
  (*     repeat rewrite inv_pp. repeat rewrite inv_V. *)
  (*     repeat rewrite concat_p_pp. *)
  (*     repeat apply whiskerR. *)
  (*     repeat rewrite concat_pp_p. repeat apply whiskerL. *)
  (*     cut (forall (n1 n2 : M) (p : n1 = n2), *)
  (*             (montype_act_mult act t n1 x)^ @ *)
  (*                    (ap (fun m : M => act m x) (ap (smontype_mult t) p) @ *)
  (*                        montype_act_mult act t n2 x) = ap (act t) (ap (fun m : M => act m x) p)). *)
  (*     { intro H. apply H. } *)
  (*     intros n1 n2. intros []. simpl. rewrite concat_1p. apply concat_Vp. *)
  (*   - intro x. simpl. *)
  (*     srapply @path_sigma. *)
  (*     { reflexivity. } *)
  (*     simpl. *)
      
  (*     apply moveR_Vp. *)
      
      
      
                           
      

  (* (* Some initial checking whether this category is univalent *) *)
  (* Definition iso_to_id {M : Monoidal_1Type} {X : 1-Type} (a : monoidal_action M X) *)
  (*            {lc : left_faithful a} (x y : monoidal_action_cat M X a lc) : *)
  (*   Isomorphic x y -> x = y. *)
  (* Proof. *)
  (*   intros [[s1 p1] [[s2 p2] H1' H2']]. simpl in *. *)
  (*   destruct ((path_sigma_uncurried (fun s0 : M => a s0 x = x) *)
  (*                                  (s2 ⊗ s1; (montype_act_mult a s2 s1 x @ ap (a s2) p1) @ p2) *)
  (*                                  (montype_id; montype_act_id a x))^-1 H1') as [q1 H1]. simpl in *. *)
  (*   clear H1'. *)
  (*   destruct ((path_sigma_uncurried (fun s0 : M => a s0 y = y) *)
  (*                                  (s1 ⊗ s2; (montype_act_mult a s1 s2 y @ ap (a s1) p2) @ p1) *)
  (*                                  (montype_id; montype_act_id a y))^-1 H2') as [q2 H2]. simpl in *. *)
  (*   clear H2'. *)
  (*   refine (_ @ p1). *)
  (*   refine ((montype_act_id a x)^  @ _). *)
  (*   apply (ap (fun s => a s x)). *)
  (*   unfold left_faithful in lc. *)
  (*   refine (_ @ ap (a s1) p2). *)


  (*   refine (p2^ @ _ @ p1). *)
  (*   refine (ap (a s2) p1^ @ _ @ ap (a s1) p2). *)

                                   
    
  (*   destruct q. destruct p. *)
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
             (* (left_cancel : forall (s t : M) (p q : s = t) (a : M), *)
             (*     ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q)  *): PreCategory.
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

  Definition group_completion (M : Monoidal_1Type)
             (left_cancel : left_faithful (@montype_mult M))
             (* (left_cancel : forall (s t : M) (p q : s = t) (a : M), *)
             (*     ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q) *) : PreCategory :=
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


  Definition act_on_grp_compl (M : Monoidal_1Type)
             (left_cancel : left_faithful (@montype_mult M))
    : M -> Functor (group_completion M left_cancel) (group_completion M left_cancel).
  Proof.
    intro a.
    (* srapply @functor_monoidal_action_cat. *)
    (* - apply monoidal_map_id. *)
    (* - intros [x1 x2]. exact (montype_mult x1 a, x2). *)
    (* - simpl. intros s [x1 x2]. unfold functor_prod. *)
    (*   simpl. apply path_prod; simpl. *)
    (*   + apply montype_assoc. *)
    (*   + reflexivity. *)
    (* - intros s t [x1 x2]. simpl. *)
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

  (* (* Some auxiliary stuff  *) *)
  (* Definition double_transport {A B : Type} (P : A -> B -> Type) *)
  (*            {a a' : A} {b b' : B} *)
  (*            (p : a = a') (q : b = b') : *)
  (*   P a b -> P a' b'. *)
  (* Proof. *)
  (*   destruct p. destruct q. exact idmap. *)
  (* Defined. *)
  (* Definition double_transport_compose {A B : Type} (P : A -> B -> Type) *)
  (*            {a a' a'' : A} {b b' b'' : B} *)
  (*            (p : a = a') (p' : a' = a'') *)
  (*            (q : b = b') (q' : b' = b'') *)
  (*   : double_transport P (p @ p') (q @ q') == *)
  (*     double_transport P p' q' o double_transport P p q. *)
  (* Proof. *)
  (*   intro x. *)
  (*   destruct q'. destruct q. *)
  (*   destruct p'. destruct p. reflexivity. *)
  (* Defined. *)

  (* Definition path_functor'' {C D : PreCategory} (F G : Functor C D) *)
  (*            (p0 : forall c : C, F c = G c) *)
  (*            (p1 : forall (c d : C) (f : morphism C c d), *)
  (*                double_transport (morphism D) (p0 c) (p0 d) (morphism_of F f ) *)
  (*                = morphism_of G f) *)
  (*   : F = G. *)
  (* Proof. *)
  (*   srapply @Paths.path_functor. *)
  (*   - apply path_forall. exact p0. *)
  (*   - apply path_forall. intro s. apply path_forall. intro d. *)
  (*     apply path_arrow. intro f. *)
  (*     refine (_ @ p1 _ _ f). *)
  (*     rewrite <- (apD10_path_forall (object_of F) (object_of G) p0 s). *)
  (*     rewrite <- (apD10_path_forall (object_of F) (object_of G) p0 d). *)
  (*     change (path_forall (Core.object_of F) (Core.object_of G) p0) with *)
  (*     (path_forall F G p0). *)
  (*     destruct (path_forall F G p0). simpl. *)
  (*     reflexivity. *)
  (* Defined. *)

  (* Definition double_transport_monoidal_action_cat *)
  (*            (M : Monoidal_1Type) (X : 1-Type) (act : monoidal_action M X) *)
  (*            (left_cancel : left_faithful act) *)
  (*            {x x' y y' : monoidal_action_cat M X act left_cancel} *)
  (*            (q1 : x = x') (q2 : y = y') *)
  (*            (s : M) (p : act s x = y) *)
  (*   : double_transport (morphism (monoidal_action_cat M X act left_cancel)) *)
  (*                      q1 q2 *)
  (*                      (s; p) *)
  (*     = (s; (ap (act s) q1^ @ p @ q2)). *)
  (* Proof. *)
  (*   destruct q2. destruct q1. simpl. *)
  (*   rewrite concat_1p. rewrite concat_p1. reflexivity. *)
  (* Qed. *)

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
    (* srapply @path_functor''. *)
    (* - intros [x1 x2]. simpl. *)
    (*   apply path_prod; simpl. *)
    (*   + apply inverse. apply montype_assoc. *)
    (*   + reflexivity. *)
    (* - intros [x1 x2] y. intros [s p]. destruct p. *)
      (* change (act_on_prod M M M (act_on_self M) (act_on_self M) s (x1, x2)) with *)
      (* (montype_mult s x1 , montype_mult s x2). *)
      (* change (fst (s ⊗ x1, s ⊗ x2)) with (montype_mult s x1). *)
      
      (* simpl.  *)
      
      (* assert (forall (C : Core.PreCategory) (c d : C) (p : c = d), *)
      (*            idtohom p *)
                 
      (* change (fst (montype_mult s x1, montype_mult s x2)) with (montype_mult s x1). *)
      
      (* change (fst (?y1, ?y2)) with y1. *)
        
      (* unfold act_on_prod. *)
      (* cbn. *)

      (* simpl. *)
      (* simpl. rewrite ap_fst_path_prod. rewrite ap_snd_path_prod. *)
  (*     rewrite concat_p1. rewrite concat_p1. simpl. *)
  (*     unfold path_prod. *)
  (*     srefine (double_transport_monoidal_action_cat M _ _ _ _ _ _ _ @ _). *)
  (*     { apply left_cancel_localize. apply left_cancel. } *)
  (*     srapply @path_sigma. *)
  (*     { reflexivity. } *)
  (*     simpl.  *)
  (*     repeat rewrite <- path_prod_VV. rewrite inv_V. simpl. *)
  (*     rewrite ap_functor_prod. *)
  (*     rewrite <- path_prod_pp. rewrite <- path_prod_pp. *)
  (*     repeat rewrite concat_p1. simpl. *)
  (*     unfold functor_prod. simpl. *)
  (*     apply (ap (fun p => path_prod (s ⊗ ((x1 ⊗ a) ⊗ b), s ⊗ x2) (((s ⊗ x1) ⊗ a) ⊗ b, s ⊗ x2) *)
  (*                                   p idpath)). *)
  (*     rewrite ap_V.  *)
  (*     apply moveL_Vp. apply (equiv_inj inverse). rewrite inv_V. *)
  (*     rewrite inv_pp. rewrite inv_pV. rewrite inv_pV. apply inverse. *)
  (*     refine (montype_pentagon M _ _ _ _ @ _). *)
  (*     repeat rewrite concat_p_pp. reflexivity. *)
  (* Defined. *)

  (* Definition act_on_grp_compl_id (M : Monoidal_1Type) *)
  (*            (left_cancel : left_faithful (@montype_mult M)) *)
  (*   : act_on_grp_compl M left_cancel montype_id = 1%functor. *)
  (* Proof. *)
  (*   srapply @path_functor'. *)
  (*   - intros [x1 x2]. simpl. *)
  (*     apply path_prod; simpl. *)
  (*     + apply montype_rid. *)
  (*     + reflexivity. *)
  (*   - intros [x1 x2] y. *)
  (*     intros [s p]. destruct p. simpl. *)
  (*     rewrite concat_p1. *)
  (*     srefine (double_transport_monoidal_action_cat M _ _ _ _ _ _ _ @ _). *)
  (*     { apply left_cancel_localize. apply left_cancel. } *)
  (*     srapply @path_sigma. *)
  (*     { reflexivity. } *)
  (*     simpl. *)
  (*     rewrite ap_V. rewrite ap_functor_prod. *)
  (*     apply moveR_Mp. rewrite concat_p1. *)
  (*     rewrite inv_Vp. simpl. *)
  (*     apply moveL_Vp. rewrite <- path_prod_pp. simpl. unfold functor_prod. simpl. *)
  (*     apply (ap (fun p => path_prod (s ⊗ (x1 ⊗ montype_id), s ⊗ x2) (s ⊗ x1, s ⊗ x2) p idpath)). *)
  (*     rewrite montype_triangle2. *)

    

  Definition act_on_grp_compl_inv (M : Monoidal_1Type)
             (left_cancel : left_faithful (@montype_mult M))
    : M -> Functor (group_completion M left_cancel) (group_completion M left_cancel).
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

      
                              
      
      
  (* Proof. *)
  (*   simpl. intros x y. *)
  (*   apply isequiv_fcontr. *)
  (*   intros [[s p] [[t q] h1 h2]]. simpl in *. *)
  (*   assert (isid_s : montype_id = s). *)
  (*     { apply inverse. apply (unital_is_unit s t (ap pr1 h2)). } *)

  (*   assert (isid_t : montype_id = t). *)
  (*     { apply inverse. apply (unital_is_unit t s (ap pr1 h1)). } *)
  (*     destruct isid_s. destruct isid_t. *)
  (*     destruct q. *)
      
    
  (*   srapply @BuildContr. *)
  (*   - exists (montype_act_id _ y). *)
  (*     apply Category.path_isomorphic. *)
  (*     unfold Category.morphism_isomorphic. *)
  (*     clear h2 h1.  *)
  (*     srapply @path_sigma.       *)
  (*     + simpl. *)
  (*       destruct (montype_act_id act y). *)
  (*        simpl. reflexivity. *)
  (*     + simpl. *)
  (*       refine (transport_paths_Fl (match *)
  (*     montype_act_id act y as p0 in (_ = y0) *)
  (*     return *)
  (*       ((let (morphism_isomorphic, _) := *)
  (*           Category.Morphisms.idtoiso (monoidal_action_cat M X act left_cancel) p0 in *)
  (*         morphism_isomorphic).1 = montype_id) *)
  (*   with *)
  (*   | 1 => 1 *)
  (*   end) _ @ _). *)
  (*       simpl. *)
  (*       apply moveR_Vp. *)
        

        
  (*       clear h2 h1. clear q. *)

  (*     simpl. *)

    
  (*   srapply @isequiv_adjointify. *)
  (*   - intros [[s p] [[t q] h1 h2]]. simpl in *. *)
  (*     refine (_ @ p). apply inverse. *)
  (*     refine (_ @ montype_act_id act x). *)
  (*     apply (ap (fun var => act var x)). *)
  (*     apply (unital_is_unit s t). *)
  (*     apply (ap pr1 h2). *)
  (*   - unfold Sect. *)
  (*     intros [[s p] [[t q] h1 h2]]. simpl in *. *)
  (*     destruct p. apply Category.path_isomorphic. simpl. *)
  (*     unfold Category.morphism_isomorphic. *)
  (*     srapply @path_sigma. simpl.        *)
      

      
      
  (*     destruct q. simpl. *)
  (*     intro  *)

    
  (* should be moved *)
  Definition ap_homotopy_idmap {A : Type} (f : A -> A) (h : f == idmap) (a : A):
    ap f (h a) = h (f a).
  Proof.
    cut (forall p : f a = a,
              ap f p = h (f a) @ p @ (h a)^).
    - intro H. refine (H (h a) @ _).
      refine (concat_pp_p _ _ _ @ _). 
      refine (whiskerL _ (concat_pV _) @ _). apply concat_p1.
    - intros []. destruct (h (f a)). reflexivity.
  Defined.    
  
  (* Definition ap_homotopic_idmap {A : Type} (f : A -> A) (h : f == idmap) {a b : A} (p : a = b) : *)
  (*   ap f p = (h a) @ p @ (h b)^. *)
  (* Proof. *)
  (*   destruct p. destruct (h a). reflexivity. *)
  (* Defined. *)
  
  (* Definition prod_to_groupcompletion (S : Monoidal_1Type) *)
  (*            (left_cancel : left_faithful (@montype_mult S)) *)
  (*            (* (left_cancel : forall (s t : S) (p q : s = t) (a : S), *) *)
  (*            (*     ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q) *): *)
  (*   Functor ((groupoid_category S)*(groupoid_category S))%category (group_completion S left_cancel). *)
  (* Proof. *)
  (*   srapply @Build_Functor; simpl. { exact idmap. } *)
  (*   - intros a b [p q]. *)
  (*     unfold monoidal_action_morphism. *)
  (*     exists montype_id. apply path_prod. *)
  (*     { apply (montype_lid _ @ p). } *)
  (*     apply (montype_lid _ @ q). *)
  (*   - intros [a1 a2] [b1 b2] [c1 c2] [p1 p2] [q1 q2]. simpl in *. *)
  (*     destruct q2, q1, p2, p1. simpl. repeat rewrite concat_p1. *)
  (*     srapply @path_sigma;simpl. *)
  (*     { apply inverse. apply montype_lid. } *)
  (*     refine (transport_paths_Fl (montype_lid montype_id)^ *)
  (*             (path_prod (functor_prod (montype_mult montype_id) (montype_mult montype_id) (a1, a2)) (a1, a2) (montype_lid a1) (montype_lid a2)) @ _). *)
  (*     rewrite ap_V. rewrite inv_V. *)
  (*     apply whiskerR. *)
  (*     transitivity (path_prod ((montype_id ⊗ montype_id) ⊗ a1, (montype_id ⊗ montype_id) ⊗ a2) (_,_) *)

  (*                             (ap (fun x : S => montype_mult x a1) (montype_lid montype_id)) (ap (fun x : S => montype_mult x a2) (montype_lid montype_id))). *)
  (*     { destruct (montype_lid montype_id). reflexivity. } *)
  (*     rewrite ap_functor_prod. *)
  (*     rewrite <- path_prod_pp. *)
  (*     apply (ap011 (path_prod _ _)); *)
  (*     refine (montype_triangle1 S montype_id _ @ _); apply whiskerL; *)
  (*     apply inverse; simpl; apply ap_homotopy_idmap. *)
  (*   - intro x. simpl. rewrite concat_p1. rewrite concat_p1. reflexivity. *)
  (* Defined. *)

  (* Definition to_prod (C : PreCategory) : *)
  (*   Functor C (C*C)%category. *)
  (* Proof. *)
  (*   apply Functor.prod; apply Functor.identity. *)
  (* Defined. *)
  
  Definition to_groupcompletion (S : Monoidal_1Type)
             (left_cancel : left_faithful (@montype_mult S))
           (* (left_cancel : forall (s t : S) (p q : s = t) (a : S), *)
           (*       ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q) *):
    Functor (groupoid_category S) (group_completion S left_cancel).
  Proof.
    apply include_in_monoidal_action_cat.
    simpl. intro a. exact (a, montype_id).
  (* := *)
  (*   Functor.compose (prod_to_groupcompletion S left_cancel) (to_prod _). *)
  Defined.

End Localize.
  
Section Univalent_GroupGompletion.
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
    (* destruct f as [f isiso]. simpl. *)
    (* destruct f as [s q]. simpl. *)
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
          
  
  (* Definition isiso_monactcat : *)
  (*   forall (x y : monoidal_action_cat M X act left_cancel_act) (f : morphism _ x y), *)
  (*     Category.IsIsomorphism f <~> (montype_id = pr1 f). *)
  (* Proof. *)
  (*   intros. destruct f as [s p].  *)
  (*   apply equiv_iff_hprop. *)
  (*   - intros [[t q] h1 h2]. simpl. apply inverse. *)
  (*     apply (unit_is_id s t). apply (ap pr1 h2). *)
  (*   - simpl. destruct p. intro q. destruct q.  *)
  (*     srapply @Category.Build_IsIsomorphism. *)
  (*     + simpl. unfold monoidal_action_morphism. *)
  (*       exists montype_id.      (* from here *) *)
  (*       refine ((montype_act_mult act _ _ _)^ @ _). *)
  (*       refine (_ @ montype_act_id act x). *)
  (*       apply (ap (fun m => act m x) (montype_lid montype_id)). *)
  (*     + simpl. rewrite concat_p1. *)
  (*       srapply @path_sigma. *)
  (*       * apply montype_lid. *)
  (*       * simpl. *)
  (*         refine (transport_paths_Fl (montype_lid montype_id) _ @ _). *)
  (*         hott_simpl. *)
  (*     + simpl. rewrite concat_p1. *)
  (*       srapply @path_sigma. *)
  (*       * apply montype_lid. *)
  (*       * simpl. *)
  (*         refine (transport_paths_Fl (montype_lid montype_id) _ @ _). *)
  (*         rewrite (montype_act_triangle1 M X act). *)
  (*         rewrite (montype_act_triangle1 M X act). *)
  (*         hott_simpl. *)
  (*         rewrite (ap_to_conjp (fun x : X =>  (montype_act_id act x)^)). *)
  (*         unfold conjp. rewrite inv_pp. hott_simpl. *)
  (* Qed. *)

  (* Definition isomorphic_monactcat_1 (x y : monoidal_action_cat M X act left_cancel_act) : *)
  (*   Category.Isomorphic x y <~> {f : morphism _ x y &  montype_id = f.1} := *)
  (*  (equiv_functor_sigma_id (isiso_monactcat x y)) oE (Category.issig_isomorphic _ x y)^-1. *)

  (* Definition isomorphic_monactcat_2 (x y : monoidal_action_cat M X act left_cancel_act) : *)
  (*   {f : morphism _ x y &  montype_id = f.1} <~> (act montype_id x = y).                           *)
  (* Proof. *)
  (*   srapply @equiv_adjointify. *)
  (*   - intros [[s p] q]. simpl in q. destruct q. exact p. *)
  (*   - intros []. *)
  (*     srapply @exist. *)
  (*     + exists montype_id. reflexivity. *)
  (*     + reflexivity. *)
  (*   - intros []. reflexivity. *)
  (*   - intros [[s p] q]. simpl in q. destruct q. destruct p. reflexivity. *)
  (* Defined. *)

  (* Lemma factorize_idtoiso_1 (x y : monoidal_action_cat M X act left_cancel_act) : *)
  (*   (isomorphic_monactcat_1 x y) o (Category.idtoiso _ (x := x) (y := y)) == *)
  (*   (fun p : x = y => *)
  (*      match p with *)
  (*        idpath => ((montype_id; montype_act_id _ x); idpath) *)
  (*      end).     *)
  (* Proof. *)
  (*   intro p. apply path_sigma_hprop. destruct p. reflexivity. *)
  (* Qed. *)

  (* Lemma factorize_idtoiso_2 (x y : monoidal_action_cat M X act left_cancel_act) : *)
  (*   (isomorphic_monactcat_2 x y) o (fun p : x = y => *)
  (*                                     match p with *)
  (*                                       idpath => ((montype_id; montype_act_id _ x); idpath) *)
  (*                                     end) *)
  (*   == *)
  (*   (concat (montype_act_id _ x)). *)
  (* Proof. *)
  (*   intros []. simpl. apply inverse. apply concat_p1. *)
  (* Defined. *)

  (* Lemma factorize_idtoiso (x y : monoidal_action_cat M X act left_cancel_act) : *)
  (*   (isomorphic_monactcat_2 x y) o (isomorphic_monactcat_1 x y) o (@Category.idtoiso _ x y) == *)
  (*   concat (montype_act_id _ x). *)
  (* Proof. *)
  (*   intro p. *)
  (*   refine (_ @ factorize_idtoiso_2 x y p). *)
  (*   apply (ap (isomorphic_monactcat_2 x y)). *)
  (*   apply factorize_idtoiso_1. *)
  (* Qed. *)
  (* Require Import Morphisms. *)
  (* Require Import Categories. *)
  (* Definition isiso_frompath (x y : monoidal_action_cat M X act left_cancel_act) (p : x = y): *)
  (*   Category.IsIsomorphism *)
  (*     (C := monoidal_action_cat M X act left_cancel_act) *)
  (*     (s := x) (d := y) *)
  (*     (montype_id; montype_act_id _ x @ p). *)
  (* Proof. *)
  (*   srapply @Category.Build_IsIsomorphism. *)
  (*   - hnf. exists montype_id. *)
  (*     exact (montype_act_id _ y @ p^). *)
  (*   - simpl. *)
    
  (*   intro p. *)
  (*   srapply (@Category.Build_Isomorphic _ x y). *)
  (*   srefine ( *)
  (*            (morphism_isomorphic := _) _). *)
    

  (* Check Morphisms.Isomorphic. *)
End Univalent_GroupGompletion.
     
