Require Import HoTT.
Require Import UnivalenceAxiom.

From A_BPQ Require Import sigma_lemmas monoids_and_groups quotients.


Section Monoid_action.
  (** Defining sets with a monoid action (see MacLane, p5) *)
  Open Scope monoid_scope.
  Record Monoid_Action (M : Monoid) (X : hSet)
    := {function_of : M -> (X -> X);
        assoc_function_of : forall (m1 m2 : M) (x : X),
            function_of (m1 + m2) x = function_of m1 (function_of m2 x);
        preserve_id_function_of : forall x : X,
            function_of (mon_id) x = x
       }.
  Global Arguments function_of {M} {X} _ _ _.

  (** If M acts on X, we define the localization of the action to be )
  the quotient X/~, where x ~ y if there is an [s : S] such that [s + x = y] *)
  Definition grp_compl_relation {M : Monoid} (X : hSet) (a : Monoid_Action M X) : relation X
    := (fun x y => {m : M | function_of a m x = y}).

  Lemma relation_is_mere {M : Monoid} (X : hSet)
           (a : Monoid_Action M X)
           (isfree_a : forall (m1 m2 : M) (x : X), (function_of a m1 x = function_of a m2 x -> m1 = m2))
    : is_mere_relation X (grp_compl_relation X a).
  Proof.
    intros.
    unfold grp_compl_relation.
    apply (trunc_sigma' _).
    - intros [m1 p1] [m2 p2]. simpl.
      apply (contr_inhabited_hprop _).
      exact (isfree_a m1 m2 x (p1 @ p2^)).
  Qed.

End Monoid_action.

Section Set_Group_Completion.
  Open Scope monoid_scope.
  Variable M : Symmetric_Monoid.
  Variable right_cancellation_M : forall l m n : M, m + l = n + l -> m = n.
  
  Definition product_action : Monoid_Action M (BuildhSet (M*M)).
  Proof.
    srapply (@Build_Monoid_Action).
    (* The action *)
    - intro m.
      intros [a b].
      exact (m + a, m + b).
    - intros m1 m2 [x1 x2].
      apply path_prod; apply mon_assoc.
    - intros [x1 x2]. apply path_prod; apply mon_lid.
  Defined.
  
  Definition right_cancel_action : forall (m1 m2 : M) (x : M*M),
      function_of product_action m1 x = function_of product_action m2 x -> m1 = m2.
  Proof.
    intros m1 m2 [x1 x2]. simpl.
    intro p.
    apply (right_cancellation_M x1).
    exact (ap fst p).
  Defined.

  Instance product_action_is_mere
    : is_mere_relation (M*M) (grp_compl_relation (BuildhSet (M*M)) product_action) :=
    relation_is_mere (BuildhSet (M*M)) (product_action) right_cancel_action.

  (** The group completion of a monoid.  *)
  Definition set_group_completion  :=
    set_quotient (grp_compl_relation (BuildhSet (M*M)) product_action).

  Definition set_group_completion_rec (Y : Type) {isset_Y : IsTrunc 0 Y}
             (f : M -> M -> Y)
             (cancel_f : forall (s : M) (a b : M),
                 f a b = f (s + a) (s + b))
    : set_group_completion -> Y.
  Proof.
    srapply @set_quotient_rec.
    - intros [a b]. exact (f a b).
    - intros [a1 b1] [a2 b2].
      unfold grp_compl_relation. intros [s p].
      set (pa := (fst ((equiv_path_prod (_,_) (_,_))^-1 p))). simpl in pa. destruct pa.
      set (pb := (snd ((equiv_path_prod (_,_) (_,_))^-1 p))). simpl in pb. destruct pb. clear p.
      apply cancel_f.
  Defined.

  Definition to_groupcompletion' : M -> M -> set_group_completion.
  Proof.
    intros m n. apply class_of.
    exact (m, n).
  Defined.
  
  Definition lcancel_to_groupcompletion (s a b : M)
    : to_groupcompletion' a b =
      to_groupcompletion' (mon_mult s a) (mon_mult s b).
  Proof.
    unfold to_groupcompletion'.
    apply related_classes_eq. simpl.
    unfold grp_compl_relation. exists s. simpl.
    reflexivity.
  Defined.

  Definition set_group_completion_ind_prop
             (P : set_group_completion -> Type)
             {isprop_P : forall z : set_group_completion, IsHProp (P z)}
             (f : forall (a b : M), P (to_groupcompletion' a b))
    : forall z : set_group_completion, P z.
  Proof.
    apply (@set_quotient_ind_prop _ _ P isprop_P).
    intros [a b]. exact (f a b).
  Defined.


  (** Now we prove that the group completion is a group  *)
  Definition grp_compl_mult : set_group_completion -> set_group_completion -> set_group_completion.
  Proof.
    srapply @set_quotient_rec2; simpl.
    - intros [a1 a2] [b1 b2].
      exact (to_groupcompletion' (a1 + b1) (a2 + b2)).
      (* apply class_of. *)
      (* exact (a1 + b1, a2 + b2).  *)
    - intros [a1 a2] [b1 b2] [c1 c2].
      intros [s p]. simpl in p.
      apply related_classes_eq. red.
      exists s. simpl.
      apply path_prod; simpl; refine (mon_assoc^ @ _).
      + apply (ap (fun x => x + c1)). apply (ap fst p).
      + apply (ap (fun x => x + c2)). apply (ap snd p).
    - intros [a1 a2] [b1 b2] [c1 c2].
      intros [s p]. simpl in p.
      apply related_classes_eq. red.
      exists s. simpl.
      apply path_prod; simpl;
      refine (mon_assoc^ @ _).
      + refine (ap (fun x => x + b1) mon_sym @ _).
        refine (mon_assoc @ _).
        apply (ap (mon_mult a1)). apply (ap fst p).
      + refine (ap (fun x => x + b2) mon_sym @ _).
        refine (mon_assoc @ _).
        apply (ap (mon_mult a2)). apply (ap snd p).
  Defined.

  Definition grp_compl_inv : set_group_completion -> set_group_completion.
  Proof.
    srapply set_group_completion_rec.
    - intros a b. exact (to_groupcompletion' b a).
    - intros s a b. simpl.
      apply lcancel_to_groupcompletion.
  Defined.
    
  Definition grp_compl_linv :
    forall x : set_group_completion,
      grp_compl_mult (grp_compl_inv x) x = to_groupcompletion' mon_id mon_id.
  Proof.
    apply set_group_completion_ind_prop.
    - intro x.
      srefine (set_quotient_set (grp_compl_relation (BuildhSet (M * M)) product_action) _ _).
    - intros a b. simpl.
      apply inverse.
      refine (lcancel_to_groupcompletion (a + b) _ _ @ _).
      apply (ap011 to_groupcompletion');
        refine (mon_rid _ @ _).
      +  apply mon_sym. + reflexivity.
  Defined.
    
  Definition grp_compl_rinv :
    forall x : set_group_completion,
      grp_compl_mult x (grp_compl_inv x) = to_groupcompletion' mon_id mon_id.
      (* class_of _ (mon_id,  mon_id). *)
  Proof.
    apply set_group_completion_ind_prop.
    - intro x.
      srefine (set_quotient_set (grp_compl_relation (BuildhSet (M * M)) product_action) _ _).
    - intros a b. simpl.
      apply inverse.
      refine (lcancel_to_groupcompletion (a + b) _ _ @ _).
      apply (ap011 to_groupcompletion');
        refine (mon_rid _ @ _).
      + reflexivity.
      + apply mon_sym. 
  Defined.

  Definition set_group_completion_group : Group.
  Proof.
    srapply @Build_Group.
    { srapply @Build_Monoid.
      - exact (BuildTruncType 0 set_group_completion).
      - simpl.
        apply grp_compl_mult.
      - simpl.
        exact (to_groupcompletion' mon_id mon_id).
        (* apply class_of. *)
        (* exact (mon_id, mon_id). *)
      - unfold associative. simpl.
        apply (set_group_completion_ind_prop
                 (fun a : set_group_completion  => forall b c : set_group_completion,
                      grp_compl_mult (grp_compl_mult a b) c = grp_compl_mult a (grp_compl_mult b c))).
        intros a1 b1.
        apply (set_group_completion_ind_prop
                 (fun b : set_group_completion => forall c : set_group_completion,
                      grp_compl_mult (grp_compl_mult (to_groupcompletion' a1 b1) b) c =
                      grp_compl_mult (to_groupcompletion' a1 b1) (grp_compl_mult b c))).
        intros a2 b2.
        apply (set_group_completion_ind_prop _).
        intros a3 b3. simpl.
        apply (ap011 to_groupcompletion'); apply mon_assoc.
      - unfold left_identity.
        apply (set_group_completion_ind_prop _).
        intros a b. simpl.
        apply (ap011 to_groupcompletion'); apply mon_lid.
      - unfold right_identity.
        apply (set_group_completion_ind_prop _).
        intros a b. simpl.
        apply (ap011 to_groupcompletion'); apply mon_rid. }
    - simpl.
      apply grp_compl_inv.
    - unfold left_inverse. simpl.
      apply grp_compl_linv.
    - unfold right_inverse. simpl.
      apply grp_compl_rinv.
  Defined.

  (** The inclusion of a monoid into a group.  *)
  Definition to_groupcompletion : Hom M (set_group_completion_group).
  Proof.
    srapply @Build_Homomorphism.
    - intro a. apply (to_groupcompletion' a mon_id).
    - simpl. reflexivity.
    - simpl. intros a b.
      apply (ap (to_groupcompletion' (a + b))).
      apply inverse. apply mon_lid.      
  Defined.


  Definition inverse_precompose_groupcompletion (G : Abelian_Group) :
    Hom M G -> Hom set_group_completion_group G.
  Proof.
    intro g.
    srapply @Build_Homomorphism.
    { srapply @set_group_completion_rec.
      - intros a b.
        exact (g a - g b).
      - intros s a b. simpl.
        rewrite preserve_mult. rewrite preserve_mult.
        rewrite grp_inv_distr.
        rewrite (grp_sym (a := g s) (b := g a)).
        rewrite (grp_sym (a := - g b) (b := - g s)).
        refine (_ @ mon_assoc^).
        refine (_ @ (ap (fun x => g a + x) mon_assoc)).
        rewrite grp_rinv. rewrite mon_lid.
        reflexivity. }
    + simpl.
      apply grp_rinv.
    + intro a. 
      apply (set_group_completion_ind_prop _). intros a2 b2.
      revert a.
      apply (set_group_completion_ind_prop _). intros a1 b1. simpl.
      rewrite preserve_mult. rewrite preserve_mult.
      refine (mon_assoc @ _ @ mon_assoc^).
      apply (ap (fun x => g a1 + x)).
      rewrite grp_inv_distr.
      refine (mon_assoc^ @ _ @ mon_assoc).
      refine (grp_sym @ _).
      apply (mon_assoc^).
  Defined.  

  Definition universal_groupcompletion (G : Abelian_Group) :
    IsEquiv (fun f : Hom set_group_completion_group G => compose_hom f to_groupcompletion).
  Proof.
    srapply @isequiv_adjointify.
    - apply inverse_precompose_groupcompletion.
    - unfold Sect. intro f.
      apply path_hom. apply path_arrow. intro x. simpl.
      rewrite preserve_id.
      rewrite inv_id.
      apply mon_rid.
    - unfold Sect.
      intro g. apply path_hom. apply path_arrow. intro x.  revert x.
      apply (set_group_completion_ind_prop _). intros a b. simpl.
      rewrite <- preserve_inv.
      rewrite <- preserve_mult. simpl.
      rewrite mon_rid. rewrite mon_lid. reflexivity.
  Defined.
      
    
  (** This is more in line with the proof in the thesis *)
  Definition universal_groupcompletion' (G : Abelian_Group) :
    IsEquiv (fun f : Hom set_group_completion_group G => compose_hom f to_groupcompletion).
  Proof.
    apply (isequiv_isepi_ismono
             (BuildhSet (Hom set_group_completion_group G))
             (BuildhSet (Hom M G))).
    - apply issurj_isepi.
      apply BuildIsSurjection. intro f.
      apply tr. unfold hfiber.
      exists (inverse_precompose_groupcompletion G f).
      apply path_hom. apply path_arrow.
      intro x. simpl.
      rewrite preserve_id. rewrite inv_id. apply mon_rid.
    - apply isinj_ismono.      
      unfold isinj.
      intros f g.
      intro H.
      apply path_hom. apply path_arrow.
      intro x. revert x.
      apply (set_group_completion_ind_prop _).
      intros a b.
      cut (f (to_groupcompletion' a mon_id) - f (to_groupcompletion' b mon_id) =
           g (to_groupcompletion' a mon_id) - g (to_groupcompletion' b mon_id)).
      { intro p. refine (_ @ p @ _);
                   rewrite <- preserve_inv;
                   rewrite <- preserve_mult;
                   apply (ap011 (fun x y => _ (to_groupcompletion' x y))).
           - apply inverse. apply mon_rid.
           - apply inverse. apply mon_lid.
           - apply mon_rid.
           - apply mon_lid. }
      apply (ap011 (@mon_mult G)).
      + apply
          (ap10 (equiv_inverse (path_hom (f oH to_groupcompletion) (g oH to_groupcompletion)) H) a).
      + apply (ap grp_inv).
        apply
          (ap10 (equiv_inverse (path_hom (f oH to_groupcompletion) (g oH to_groupcompletion)) H) b).
  Defined.

End Set_Group_Completion.

Section Integers.
  (** We define the integers to be the group completion of the natural numbers.  *)
  Definition Integers : Group.
  Proof.
    srapply set_group_completion_group.
    - apply (Build_Symmetric_Monoid (nat_monoid)).
      intros a b. simpl.
      apply nat_plus_comm.
  Defined.

  Definition nat_to_integer : nat -> Integers.
  Proof.
    intro a.
    apply to_groupcompletion.
    exact a.
  Defined.

  Definition integer_to_nat : Integers -> nat.
  Proof.
    srapply set_group_completion_rec.
    - simpl. intros a b.
      apply (nat_minus b a).
    - simpl.
      intros s a b. induction s; try reflexivity.
      apply IHs.
  Defined.

  Definition issect_to_groupcompletion (a : nat)
    : integer_to_nat (nat_to_integer a) = a.
  Proof.
    reflexivity.
  Defined.

  Definition natnat_to_integer : nat -> nat -> Integers.
  Proof.
    intros a b.
    unfold Integers. unfold set_group_completion_group. simpl.
    apply (to_groupcompletion').
    - exact a.
    - exact b.
  Defined.

  Definition rcancel_integers (s a b : nat) :
    natnat_to_integer a b = natnat_to_integer (s + a) (s + b).
  Proof.
    apply lcancel_to_groupcompletion.
  Defined.

  (** The function from nat to the integers is injective.  *)
  Definition inj_nat_to_integer (a b : nat) (p : nat_to_integer a = nat_to_integer b) : a = b.
  Proof.
    refine ((issect_to_groupcompletion a)^ @ _ @ issect_to_groupcompletion b).
    apply (ap integer_to_nat p).
  Defined.

  Definition diff_zero (a b : nat) (p : natnat_to_integer a b = nat_to_integer 0) : a = b.
  Proof.
    apply inj_nat_to_integer. apply inverse.
    apply grp_moveL_M1. refine (_ @ p).
    apply (ap011 natnat_to_integer); simpl.
    - reflexivity.
    - apply inverse. apply nat_plus_n_O.
  Defined.

  (** Now we prove that this definition of integers is equivalent to the one in the HoTT library *)
  (* The function +1 from nat to the positives *)
  Definition succ_nat_to_pos : nat -> Pos.
  Proof.
    intro a. induction a.
    - exact Int.one.
    - exact (succ_pos IHa).
  Defined.

  (* the inclution nat to int *)
  Definition nat_to_int : nat -> Int.
  Proof.
    intro a.
    destruct a.
    - exact Int.zero.
    - exact (pos (succ_nat_to_pos a)).
  Defined.

  (* the function - on Int *)
  Definition int_neg : Int -> Int.
  Proof.
    intros [n | | p].
    - exact (pos n).
    - exact Int.zero.
    - exact (neg p).
  Defined.

  (* the function a-b *)
  Fixpoint nat_int_minus (a b : nat) : Int.
  Proof.
    destruct b.
    (* a-0 = a *)
    - exact (nat_to_int a).
    - destruct a.
      (* 0-(b+1) = -b+1 *)
      + apply int_neg.
        exact (nat_to_int b.+1).
      (* (a+1) - (b+1) = a - b *)
      + exact (nat_int_minus a b).
  Defined.

  Definition integers_to_int : Integers -> Int.
  Proof.
    srapply (set_group_completion_rec); simpl.
    - intros a b. exact (nat_int_minus a b).
    - intros s a b. simpl.
      induction s; try reflexivity. apply IHs.
  Defined.

  (* the function -1 from pos to nat *)
  Definition pred_pos_to_nat : Pos -> nat.
  Proof.
    intro p. induction p.
    - exact 0.
    - exact (IHp.+1).
  Defined.
    
  (* The inclusion of positives in the natural numbers *)
  Definition pos_to_nat (p : Pos) : nat
    := (pred_pos_to_nat p).+1.
  (* Proof. *)
  (*   destruct p as [ | p]. *)
  (*   - exact 1. *)
  (*   - exact (pos_to_nat p).+1. *)
  (* Defined. *)

  Definition int_to_natnat : Int -> nat * nat.
  Proof.
    intros [n | | p].
    - exact (0, pos_to_nat n).
    - exact (0,0).
    - exact (pos_to_nat p, 0).
  Defined.


  Definition int_to_integers : Int -> Integers.
  Proof.
    intro z.
    apply natnat_to_integer.
    - exact (fst (int_to_natnat z)).
    - exact (snd (int_to_natnat z)).
  Defined.

  (*   destruct z as [neg | | pos]. *)
  (*   - apply grp_inv. apply nat_to_integers. *)
  (*     exact (pos_to_nat neg). *)
  (*   - exact (nat_to_integers 0). *)
  (*   - apply nat_to_integers. *)
  (*     exact (pos_to_nat pos). *)
  (* Defined. *)

  Definition succ_pred_nat_pos (p : Pos)
    : succ_nat_to_pos (pred_pos_to_nat p) = p.
  Proof.
    induction p; try reflexivity.
    exact (ap (succ_pos) IHp).
  Defined.

  Definition pred_succ_nat_pos (a : nat)
    : pred_pos_to_nat (succ_nat_to_pos a) = a.
  Proof.
    induction a; try reflexivity.
    apply (ap S IHa).
  Defined.

  Fixpoint retr_int_natnat (a b : nat) :
    natnat_to_integer
      (fst (int_to_natnat (nat_int_minus a b)))
      (snd (int_to_natnat (nat_int_minus a b))) =
    natnat_to_integer a b.
  Proof.
    destruct a, b; try reflexivity; simpl; unfold pos_to_nat.
    - rewrite pred_succ_nat_pos. reflexivity.
    - rewrite pred_succ_nat_pos. reflexivity.
    - refine (retr_int_natnat _ _ @ _).
      apply (rcancel_integers 1).
  Defined.
    

  Definition equiv_integers :
    Integers <~> Int.
  Proof.
    apply (equiv_adjointify integers_to_int int_to_integers).
    - intro z. simpl. 
      destruct z as [n | | p]; try reflexivity.
      + destruct n; try reflexivity.
        simpl. apply (ap neg).
        apply (ap succ_pos). apply succ_pred_nat_pos.
      + simpl.
        apply (ap pos).
        apply succ_pred_nat_pos.
    - intro z. revert z.
      apply (set_group_completion_ind_prop _ _).
      simpl. intros a b.
      unfold int_to_integers.
      apply retr_int_natnat.
  Defined.

  Definition nat_to_int_commute 
    : equiv_integers o nat_to_integer == nat_to_int.
  Proof.
    intro a. simpl.
    destruct a; reflexivity.
  Defined.

  (** We end by noting that the function from [nat] to [Integers] is injective.  *)
  Definition inj_nat_to_int (a b : nat) (p : nat_to_int a = nat_to_int b) : a = b.
  Proof.
    destruct a, b; try reflexivity.
    - apply Empty_rec.
      apply (pos_neq_zero p^).
    - apply Empty_rec.
      apply (pos_neq_zero p).
    - apply (ap S).
      refine ((pred_succ_nat_pos _)^ @ _ @ pred_succ_nat_pos _).
      apply (ap pred_pos_to_nat). apply pos_injective. exact p.
  Defined.

End Integers.






