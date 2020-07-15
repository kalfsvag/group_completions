Require Import HoTT.

(* Example test ( A : Type) (H : Decidable A) : ~ ~ A -> A. *)
(* intros. unfold not in X. *)
(* destruct (dec A). *)
(* exact a. *)
(* destruct (X n). *)
From A_BPQ Require Import finite_types permutations.




Section Sign.
  
  (* Arguments equiv_sum_assoc : simpl nomatch. *)


  Lemma swap_fix_last {n : nat} (e : fintype n.+1 <~> fintype n.+1) :
    (swap_last e oE e) (inr tt) = inr tt.
  Proof.
    apply fin_transpose_last_with_with.
  Qed.

  (* First sign of transpositions with the last element *)
  Definition sgn_transpose {n : nat} (i : fintype n.+1) : (fintype 2 <~> fintype 2).
  Proof.
    destruct i as [i | []].
    (* i is a nontrivial transposition, and has sign τ *)
    - exact twist2.
    (* i is the trivial transposition and has sign ι *)
    - exact equiv_idmap.
  Defined.
    
  Fixpoint sign (n : nat) :
    (fintype n <~> fintype n) -> (fintype 2 <~> fintype 2).
  Proof.
    intro e.
    (* For n = 0, the sign is trivial *)
    destruct n. { exact equiv_idmap. }
    exact (sgn_transpose (e (inr tt)) oE sign n (transpose_and_restrict e)).
  Defined.

  Lemma sgn_transpose_notlast {n : nat} (i : fintype n.+1) :
        (i <> inr tt) -> sgn_transpose i = twist2.
  Proof.
    intro nlast.
    destruct i as [i | []].
    - reflexivity.
    - destruct (nlast idpath).
  Qed.

  Definition sgn_id (m : nat) :
    sign m (equiv_idmap) = equiv_idmap.
  Proof.
    induction m.
    - reflexivity.
    - simpl. refine (_ @ IHm).
      refine (ecompose_1e _ @ _).
      apply (ap (sign m)).
      apply path_equiv. apply path_arrow.
      apply transpose_and_restrict_id.
  Qed.

 
  Lemma sgn2_is_id : sign 2 == idmap.
  Proof.
    intro e.
    unfold sign.
    assert (h : (transpose_and_restrict e) (inr tt) = inr tt).
    { recall ((transpose_and_restrict e) (inr tt)) as x eqn:p. rewrite p.
      destruct x as [[] | []]; reflexivity. }
    rewrite h. clear h.
    rewrite (ecompose_e1).
    recall (e (inr tt)) as x eqn:p. rewrite p. simpl.
    destruct x as [ [[] | []] | []]; apply inverse; apply path_equiv; apply path_arrow.
    - apply (sigma2_notfixlast e p). 
    - apply (sigma2_fixlast e p).
  Qed.
      
  Definition sgn_beta_transpose (m : nat) (x y : fintype m) :
    (x <> y) -> sign m (fin_transpose x y) = twist2.
  Proof.
    intro neq.
    induction m.
    - destruct x.
    - change (sign m.+1 (fin_transpose x y))
             with
             (sgn_transpose (fin_transpose x y (inr tt)) oE
              sign m (transpose_and_restrict (fin_transpose x y))).
      destruct y as [y | []].
      + destruct x as [x | []].
        * rewrite
            (path_equiv (path_arrow _ _ (transpose_and_restrict_transpose_fixlast x y))).
          simpl. 
          refine (ecompose_1e _ @ _).
          apply IHm. revert neq. apply functor_not.
          apply (ap inl).
        * rewrite (fin_transpose_beta_l).
          change (sgn_transpose (inl y)) with twist2.
          rewrite (path_equiv (path_arrow _ _
                      (fin_transpose_sym (n := m.+1) (inr tt) (inl y)))).
          rewrite (path_equiv (path_arrow _ _
                      (transpose_and_restrict_transpose_nfx (inl y)))).
          rewrite sgn_id. apply ecompose_e1.
      + rewrite (fin_transpose_beta_r).
        rewrite (path_equiv (path_arrow _ _
                      (transpose_and_restrict_transpose_nfx x))).
        rewrite (sgn_id). refine (ecompose_e1 _ @ _).
        destruct x as [x | []].
        * reflexivity.
        * destruct (neq idpath).
  Qed.    
      
  
  (* Definition Decidable_fixlast {n : nat} (e : fintype n.+1 <~> fintype n.+1) : Type:= *)
  (*   (e (inr tt) = inr tt) + {x : fintype n & e (inr tt) = inl x}. *)
  
  (* Definition decidable_fixlast {n : nat} (e : fintype n.+1 <~> fintype n.+1) : *)
  (*   (e (inr tt) = inr tt) + {x : fintype n & e (inr tt) = inl x}. *)
  (* Proof. *)
  (*   recall (e (inr tt)) as x eqn:p. *)
  (*   destruct x as [x | []]. *)
  (*   - exact (inr (x; p)). *)
  (*   - exact (inl p). *)
  (* Defined. *)

  (* Definition decidable_fixlast_blocksum {m n : nat} *)
  (*            (e1 : fintype m.+1 <~> fintype m.+1) (e2 : fintype n <~> fintype n) : *)
  (*   Decidable_fixlast e1 -> Decidable_fixlast (block_sum m.+1 n e1 e2). *)
  (* Proof. *)
  (*   apply functor_sum. *)
  (*   - apply (block_sum_fixlast m n e1 e2)^-1. *)
  (*   - srapply @functor_sigma. *)
  (*     + intro i. *)
  (*       apply (equiv_finsum m n)^-1. exact (inr i). *)
  (*     + intro i. simpl. *)
  (*       intro p. *)
  (*       rewrite p. reflexivity. *)
  (* Defined. *)

  (* Definition decidable_fixlast_blocksum_is_decidable_fixlast {m n : nat} *)
  (*            (e1 : fintype m.+1 <~> fintype m.+1) (e2 : fintype n <~> fintype n) : *)
  (*   decidable_fixlast_blocksum e1 e2 (decidable_fixlast e1) = *)
  (*   decidable_fixlast (block_sum m.+1 n e1 e2). *)
  (* Proof. *)
  (*   destruct (decidable_fixlast e1). *)
  (*   - simpl. *)
      

  (*     destruct (decidable_fixlast (block_sum m.+1 n e1 e2)). *)
  (*     + apply (ap inl). *)
  (*       apply (istrunc_trunctype_type (BuildTruncType 0 (fintype (m.+1 + n)))). *)
  (*     + simpl in p. *)
  (*     apply path_sum.  *)
  (*   -  *)
    
      
      
  (*   decidable_fixlast (block_sum m.+1 n e1 e2) = *)
  (*   functor_sum (block_sum_fixlast m.+1 n e1 e2)^-1 *)
  (*               ( *)

  (* Fixpoint sign (n : nat) : *)
  (*   (fintype n <~> fintype n) -> group_2. *)
  (* Proof. *)
  (*   intro e. *)
  (*   (* For n = 0, the sign is trivial *) *)
  (*   destruct n. { exact ι. } *)
  (*   destruct (decidable_fixlast e) as [p | [x p]]. *)
  (*   - exact (sign n (equiv_restrict e p)). *)
  (*   - exact (τ + sign n (transpose_and_restrict e)). *)
  (*   (* recall (e (inr tt)) as x eqn:p. *) *)
  (*   (* destruct x as [x | []]. *) *)
  (*   (* (* e does not preserve the last point *) *) *)
  (*   (* - exact (τ + sign n (transpose_and_restrict e)). *) *)
  (*   (* (* e preserves the last point *) *) *)
  (*   (* - exact (sign n (equiv_restrict e p)). *) *)
  (* Defined. *)

  (* Definition sgn_plus_1 {n : nat} (e : fintype n <~> fintype n) : *)
  (*   sign (n := n.+1) (e +E 1) = sign e. *)
  (* Proof. *)
  (*   simpl. (* refine (id_2_is_id _ @ _). *)
    apply (ap (sign (n := n))). *)
  (*   apply path_equiv. apply path_arrow. *)
  (*   apply equiv_restrict_plus1. *)
  (* Defined. *)

  (* Arguments block_sum : simpl never. *)

  Definition sgn_block_sum {m n : nat} (e1 : fintype m <~> fintype m) (e2 : fintype n <~> fintype n) :
    sign (n+m) (block_sum e1 e2) = sign n e2 oE sign m e1.
  Proof.
    induction n.
    - simpl.
      refine (_ @ (ecompose_1e _)^).
      apply (ap (sign m)).
      apply path_equiv. apply path_arrow. intro.
      apply (block_sum_beta_finl e1 e2 x).
    - simpl. 
      (* change (finsum m n.+1 (functor_sum e1 e2 (_^-1 (inr tt)))) *)
      (*        with *)
      (*        (block_sum e1 e2 (inr tt)). *)
      
      (* rewrite (block_sum_beta_finr e1 e2 (inr tt)). *)
      rewrite (path_equiv (path_forall _ _ (transpose_and_restrict_block_sum e1 e2))).
      rewrite (IHn (transpose_and_restrict e2)).
      refine (ecompose_e_ee _ _ _ @ _).
      apply (ap (fun g =>
                   g oE sign n (transpose_and_restrict e2) oE
                     sign m e1)).
      cut (forall x : fintype n.+1,
              sgn_transpose (functor_sum (finr m n) idmap x) = sgn_transpose x).
      { intro H. apply H. }
      intros [x | x]; reflexivity.
  Qed.
  
  (* Fixpoint block_sum_lid (m : nat) (n : nat) (e : fintype n <~> fintype n) : *)
  (*   fintype (m + n) <~> fintype (m + n). *)
  (* Proof. *)
  (*   induction m; simpl. *)
  (*   - exact e. *)
  (*   - exact (equiv_functor_sum' (block_sum_lid m n e) 1). *)
  (* Defined. *)

  (* Definition block_sum_lid_1 (m : nat) {n : nat} (e : fintype n <~> fintype n) : *)
  (*   block_sum_lid m.+1 e = (block_sum_lid m e) +E 1 := idpath.     *)



  Lemma functor_sum_compose {A1 A2 A3 B1 B2 B3 : Type}
        (f1 : A1 -> A2) (f2 : A2 -> A3)
        (g1 : B1 -> B2) (g2 : B2 -> B3) :
    functor_sum (f2 o f1) (g2 o g1) == (functor_sum f2 g2) o (functor_sum f1 g1). 
  Proof.
    intros [a | a]; reflexivity.
  Defined.

  Definition transpose_and_restrict_fixlast {n : nat}
             (e : fintype n.+1 <~> fintype n.+1)
             (fixlast : e (inr tt) = inr tt) :
    transpose_and_restrict e == equiv_restrict e fixlast.
  Proof.
    apply inj_equiv_plus1.
    intro x.
    refine (transpose_and_restrict_eta _ x @ _ @ (equiv_restrict_eta _ _ x)^).
    ev_equiv. unfold swap_last. rewrite fixlast.
    apply (fin_transpose_same_is_id (n := n.+1) (inr tt) (e x)).
  Defined.

  Lemma transpose_and_restrict_fixlast1 {n : nat}
             (e1 e2 : fintype n.+1 <~> fintype n.+1)
             (fixlast_1: e1 (inr tt) = inr tt) :
    transpose_and_restrict (e2 oE e1) ==
    (transpose_and_restrict e2) oE (transpose_and_restrict e1).
  Proof.
    apply inj_equiv_plus1.
    intro x.
    refine (transpose_and_restrict_eta _ x @ _).
    unfold swap_last. ev_equiv. rewrite fixlast_1.
    transitivity (((transpose_and_restrict e2 +E 1) oE (transpose_and_restrict e1 +E 1)) x).
    - ev_equiv.
      apply inverse.
      refine (transpose_and_restrict_eta e2 _ @ _). ev_equiv.
      apply (ap (swap_last e2)). apply (ap e2).
      refine (transpose_and_restrict_eta e1 _ @ _). ev_equiv.
      unfold swap_last. rewrite fixlast_1.
      apply (fin_transpose_same_is_id (n := n.+1)).
    - destruct x as [x | []]; reflexivity.
  Qed.

  Lemma transpose_and_restrict_fixlast2 {n : nat}
             (e1 e2 : fintype n.+1 <~> fintype n.+1)
             (fixlast_2 : e2 (inr tt) = inr tt) :
    transpose_and_restrict (e2 oE e1) ==
    (transpose_and_restrict e2) oE (transpose_and_restrict e1).
  Proof.
    apply inj_equiv_plus1.
    intro x.    
    refine (transpose_and_restrict_eta _ _ @ _).
    refine (_ @ (functor_sum_compose _ _ idmap idmap x)^).
    refine (_ @ (transpose_and_restrict_eta e2 _)^).
    refine (_ @ (ap ((swap_last e2) o e2) (transpose_and_restrict_eta e1 x)^)).
    unfold swap_last. ev_equiv. rewrite fixlast_2.
    refine (_ @ (fin_transpose_same_is_id (n := n.+1) _ _ )^).
    apply inverse.
    refine (natural_fin_transpose (e1 (inr tt)) (inr tt) e2  _ @ _).
    rewrite fixlast_2. reflexivity.
  Qed.

  Lemma transpose_and_restrict_fixlast12 {n : nat}
             (e1 e2 : fintype n.+1 <~> fintype n.+1)
             (fixlast_12 : e2 (e1 (inr tt)) = inr tt) :
    transpose_and_restrict (e2 oE e1) ==
    (transpose_and_restrict e2) oE (transpose_and_restrict e1).
  Proof.
    apply inj_equiv_plus1.
    intro x.    
    refine (transpose_and_restrict_eta _ _ @ _).
    refine (_ @ (functor_sum_compose _ _ idmap idmap x)^).
    refine (_ @ (transpose_and_restrict_eta e2 _)^).
    refine (_ @ (ap (swap_last e2 oE e2) (transpose_and_restrict_eta e1 x)^)).
    ev_equiv.
    refine (_ @ (ap (swap_last e2) (natural_fin_transpose (e1 (inr tt)) (inr tt) e2 (e1 x))^)).
    unfold swap_last. ev_equiv. rewrite fixlast_12.
    refine (fin_transpose_same_is_id (n := n.+1) (inr tt) _ @ _).
    rewrite (fin_transpose_sym (e2 (inr tt)) (inr tt)).
    refine ((fin_transpose_invol (n := n.+1) (inr tt) (e2 (inr tt)) _)^).
  Qed.


  Lemma transpose_and_restrict_nfx {n : nat}
        (e1 e2 : fintype n.+1 <~> fintype n.+1)
        (x2 x12: fintype n)
        (* (p1 : e1 (inr tt) = inl x1) *)
        (p2 : e2 (inr tt) = inl x2)
        (p12 : e2 (e1 (inr tt)) = inl x12) :
    transpose_and_restrict (e2 oE e1) ==
    (fin_transpose x2 x12)
      oE (transpose_and_restrict e2) oE (transpose_and_restrict e1).
  Proof.
    apply inj_equiv_plus1.
    intro x.    
    refine (transpose_and_restrict_eta _ _ @ _).
    refine (_ @ (functor_sum_compose _ _ idmap idmap x)^).
    rewrite (functor_sum_compose (transpose_and_restrict e2) (fin_transpose x2 x12) idmap idmap).
    refine (_ @ ap ((functor_sum (fin_transpose x2 x12) idmap)
                      o (functor_sum (transpose_and_restrict e2) idmap))
              (transpose_and_restrict_eta e1 x)^).
    refine (_ @ ap (functor_sum (fin_transpose x2 x12) idmap)
              (transpose_and_restrict_eta e2 _)^).
    ev_equiv.
    assert (h : fin_transpose (e2 (inr tt)) (e2 (e1 (inr tt))) ==
            functor_sum (B := Unit) (fin_transpose x2 x12) idmap ).
    { rewrite p2.  rewrite p12. intro i. reflexivity. }
    refine (_ @ h _). clear h.
    unfold swap_last.  ev_equiv.

    rewrite (natural_fin_transpose (e1 (inr tt)) (inr tt) e2 (e1 x)).
    generalize (e2 (e1 x)). clear x. intro x.
    (* four cases: x = n+1, e2 (e1 (n+1)) = x, e2 (n+1) = x, and everything else *)
    destruct x as [x | []].
    - rewrite p12. rewrite p2.
      destruct (decidablepaths_fin n x12 x).
      + rewrite p.
        repeat rewrite fin_transpose_beta_l.
        apply inverse.
        apply fin_transpose_other; apply inr_ne_inl.
      + transitivity (inl Unit x).
        { apply fin_transpose_other.
          - revert n0. apply functor_not.
            intro p. exact (path_sum_inl Unit p^).
          - apply inl_ne_inr. }
        destruct (decidablepaths_fin n x2 x).
        * rewrite p.
          rewrite fin_transpose_beta_r.
          assert (h : fin_transpose (n := n.+1) (inl x) (inr tt) (inl x12) = inl x12).
          { apply fin_transpose_other; try (apply inl_ne_inr).
            revert n0. apply functor_not. apply path_sum_inl. }
          rewrite h. clear h.
          apply inverse.
          apply fin_transpose_beta_r.
        * assert (h : fin_transpose (n := n.+1) (inl x12) (inl x2) (inl x) = inl x).
          { apply fin_transpose_other;
              apply (functor_not (path_sum_inl Unit));
              apply (functor_not inverse).
            - exact n0. - exact n1. }
          rewrite h. clear h.
          assert (h : fin_transpose (n := n.+1) (inl x2) (inr tt) (inl x) = inl x).
          { apply fin_transpose_other; try (apply inl_ne_inr).
            apply (functor_not (path_sum_inl Unit)).
            apply (functor_not (inverse) n1). }
          rewrite h. clear h.
          apply inverse.
          apply fin_transpose_other;
            apply (functor_not (path_sum_inl Unit));
            apply (functor_not inverse).
          { exact n1. } { exact n0. }
    - rewrite fin_transpose_beta_r.
      rewrite p12.  rewrite p2.
      rewrite (fin_transpose_other (n := n.+1) (inl x12) (inl x2) (inr tt)
                                   (inr_ne_inl _ _) (inr_ne_inl _ _)).
      rewrite fin_transpose_beta_r. rewrite fin_transpose_beta_l.
      reflexivity.
  Qed.
          

  
  Definition sgn_compose (n : nat) (e1 e2 : fintype n <~> fintype n) :
    sign n (e2 oE e1) = (sign n e2) oE (sign n e1).
  Proof.
    induction n. { reflexivity. }
    simpl. rewrite ecompose_e_ee.
    rewrite (ecompose_ee_e _ (sign n (transpose_and_restrict e2)) _).
    rewrite (symm_sigma2 (sign n (transpose_and_restrict e2)) _).
    rewrite (ecompose_ee_e _ _ (sgn_transpose (e2 (inr tt)))).
    rewrite (ecompose_ee_e _ _ (sgn_transpose (e1 (inr tt)))).
    rewrite (ecompose_e_ee _ _ (sgn_transpose (e2 (inr tt)))).
    rewrite <- (IHn (transpose_and_restrict e1) (transpose_and_restrict e2)).
    (* recall (e1 (inr tt)) as x1 eqn:p1. *)
    (* destruct x1 as [x1 | []]. *)
    recall (e1 (inr tt)) as x1 eqn:p1.
    destruct x1 as [x1 | []].
    - recall (e2 (e1 (inr tt))) as x12 eqn:p12.
         destruct x12 as [x12 | []].
      +  recall (e2 (inr tt)) as x2 eqn:p2.
         destruct x2 as [x2 | []].
         * rewrite (path_equiv (path_forall _ _
                                            (transpose_and_restrict_nfx e1 e2 x2 x12 p2 p12))).
           (* rewrite p12. rewrite p2. *)
           rewrite ecompose_ee_e.
           rewrite (IHn
                      (transpose_and_restrict e2 oE transpose_and_restrict e1) (fin_transpose x2 x12)).
           rewrite (ecompose_ee_e).
           rewrite p12. rewrite p2. simpl.
           apply (ap (fun g => twist2 oE g)).
           apply (ap
                    (fun g => g oE
                              sign n (transpose_and_restrict e2 oE transpose_and_restrict e1))).
           rewrite p1.
           apply (sgn_beta_transpose).
           apply (functor_not (ap (fun x => (inl Unit x)))).
           rewrite <- p12. rewrite <- p2.
           apply (functor_not (equiv_inj e2)). rewrite p1.
           apply inr_ne_inl.
        * (* rewrite p1. refine (_ @ sgn_id n). *)
          (* apply (ap (sign n)). *)
          (* assert (h : x2 = x12). *)
          (* { apply (path_sum_inl Unit). *)
          (*   rewrite <- p2. rewrite <- p12.  rewrite p1.  reflexivity. } *)
          (* rewrite h. clear h. *)
          (* apply path_equiv. apply path_arrow. apply fin_transpose_same_is_id. *)
          rewrite
            (path_equiv (path_arrow _ _ (transpose_and_restrict_fixlast2 e1 e2 p2))).
          apply (ap (fun g =>
                       g oE sign n (transpose_and_restrict e2 oE transpose_and_restrict e1))).
          rewrite p2. rewrite p1.
          simpl. rewrite ecompose_1e.
          apply sgn_transpose_notlast.
          rewrite <- p2.
          apply (functor_not (equiv_inj e2)).
          apply inl_ne_inr. 
      + rewrite (path_equiv (path_arrow _ _
                     (transpose_and_restrict_fixlast12 e1 e2 p12))).
        apply (ap (fun g =>
                       g oE sign n (transpose_and_restrict e2 oE transpose_and_restrict e1))).
        rewrite p12. rewrite p1. simpl.
        apply emoveL_eM. rewrite ecompose_1e.
        simpl. 
        apply inverse. rewrite twist2_inv.
        apply sgn_transpose_notlast.
        intro false.
        rewrite p1 in p12. apply (inl_ne_inr  x1 tt).
        apply (equiv_inj e2).
        exact (p12 @ false^).
    - rewrite (path_equiv (path_arrow _ _ (transpose_and_restrict_fixlast1 e1 e2 p1))).
      apply (ap (fun g =>
                       g oE sign n (transpose_and_restrict e2 oE transpose_and_restrict e1))).
      rewrite p1. simpl.
      refine (ecompose_e1 _)^.
  Qed.

End Sign.

(* I think the following is in finite_lemmas...*)


(* (* Comparing not_leq to gt *) *)
(* Section Inequalities. *)
  
(*   (* For two natural numbers, one is either less than or equal the other, or it is greater. *) *)
(*   Definition leq_or_gt (i j : nat) : (i <= j) + (i > j). *)
(*   Proof. *)
(*     revert j. induction i; intro j. *)
(*     (* 0 <= j *) *)
(*     - exact (inl tt). *)
(*     - destruct j. *)
(*       (* 0 < i+1 *) *)
(*       + exact (inr tt). *)
(*       (* (i < j+1) + (j.+1 < i + 1) <-> (i <= j) + (j < i) *) *)
(*       + apply IHi. *)
(*   Defined. *)
 

(*   Definition leq_succ (n : nat) : n <= n.+1. *)
(*   Proof. *)
(*     induction n. reflexivity. apply IHn. *)
(*   Defined. *)

(*   (* Lemma leq_refl_code (i j : nat) : i =n j -> i <= j. *) *)
(*   (* Proof. *) *)
(*   (*   intro H. *) *)
(*   (*   destruct (path_nat H). apply leq_refl. *) *)
(*   (* Qed. *) *)
  
(*   Definition neq_succ (n : nat) : not (n =n n.+1). *)
(*   Proof. *)
(*     induction n. *)
(*     - exact idmap. *)
(*     - exact IHn. *)
(*   Defined. *)

(*   Definition leq0 {n : nat} : n <= 0 -> n =n 0. *)
(*   Proof. *)
(*     induction n; exact idmap. *)
(*   Defined. *)

(*     (*  *) *)
(*   Definition leq_geq_to_eq (i j : nat) : (i <= j) * (j <= i) -> i =n j. *)
(*   Proof. *)
(*     intros [i_lt_j  j_lt_i]. *)
(*     revert j_lt_i. revert i_lt_j. revert i. *)
(*     induction j. *)
(*     - intros. exact (leq0 i_lt_j). *)
(*     - destruct i. *)
(*       + intros. destruct j_lt_i. *)
(*       + simpl. intros. *)
(*         apply (IHj _ i_lt_j j_lt_i). *)
(*   Defined. *)

(*   (* Definition leq_to_lt_plus_eq (i j : nat) : i <= j -> (i < j) + (i = j). *) *)
(*   (* Proof. *) *)
(*   (*   intro i_leq_j. *) *)
(*   (*   destruct (dec (i = j)). *) *)
(*   (*   - exact (inr p). *) *)
(*   (*   - apply inl. *) *)
(*   (*     induction j. *) *)
(*   (*     + simpl. rewrite (path_nat (leq0 i i_leq_j)) in n. apply n. reflexivity. *) *)
(*   (*     + destruct i. exact tt. *) *)
(*   (*       srapply (@leq_transd i.+2 j j.+1). *) *)
(*   (*       * apply IHj. *) *)
(*   (*         admit. *) *)
           
        
(*   (*       simpl. *) *)

        
(*   (*       i. *) *)
(*   (*     + simpl. *) *)
    
(*   (*   destruct j. *) *)
(*   (*   apply inr. apply path_nat. apply (leq0  i (i_leq_j)). *) *)
(*   (*   destruct i. *) *)
(*   (*   - simpl. *) *)
    
(*   (*   apply inl. change (i < j.+1) with (i <= j). *) *)
(*   (*   apply (leq_transd *) *)
    
    

(*   (* Definition nlt_n0 (n : nat) : ~(n < 0) := idmap. *) *)
  
(*   Definition gt_to_notleq (i j : nat) : j > i -> ~(j <= i). *)
(*   Proof. *)
(*     intro i_lt_j. *)
(*     intro j_leq_i. *)
(*     apply (neq_succ i). *)
(*     apply (leq_antisymd (leq_succ i)). *)
(*     apply (leq_transd i_lt_j j_leq_i). *)
(*     (* set (Si_leq_i := leq_transd i_lt_j j_leq_i). *) *)
(*     (* set (Si_eq_i := leq_antisymd (leq_succ i) Si_leq_i). *) *)
(*     (* apply (neq_succ i Si_eq_i). *) *)
(*     (* induction i. *) *)
(*     (* exact Si_eq_i. *) *)
(*   Defined. *)

(*   (* Lemma notleq_to_gt (i j : nat) : ~(j <= i) -> j > i. *) *)
(*   (* Proof. *) *)
(*   (*   intro j_nleq_i. *) *)
(*   (*   induction j. *) *)
(*   (*   - apply j_nleq_i. *) *)
(*   (*     apply leq0n. *) *)
(*   (*   - change (i < j.+1) with (i <= j). *) *)
(*   (*     destruct (dec (i =n j)). *) *)
(*   (*     (* i = j *) *) *)
(*   (*     + destruct (path_nat t). apply leq_refl. *) *)
(*   (*     +  *) *)

(*   (*     induction i. *) *)
(*   (*     + exact tt. *) *)
(*   (*     +  *) *)
    
(*   (*   induction i, j. *) *)
(*   (*   - apply j_nleq_i. exact tt. *) *)
(*   (*   - exact tt. *) *)
(*   (*   - simpl. simpl in IHi. simpl in j_nleq_i. apply IHi. exact j_nleq_i. *) *)
(*   (*   - change (i.+1 < j.+1) with (i < j). *) *)
(*   (*     change (j < i.+1) with (j <= i) in j_nleq_i. *) *)
(*   (*     change (i < j.+1) with (i <= j) in IHi. *) *)
      
    
(*   (*   destruct (dec (~ (j <= i))). *) *)
(*   (*   - set (f := j_nleq_i t). destruct f. *) *)
(*   (*   -  *) *)
  
(*   (* If i <= j, then j is the sum of i and some natural number *) *)
(*   Definition leq_to_sum {i j : nat} : i <= j -> {k : nat | j = i + k}%nat. *)
(*   Proof. *)
(*     revert j. induction i; intro j. *)
(*     - intro.  *)
(*       exists j. reflexivity. *)
(*     - destruct j. intros []. *)
(*       simpl. change (i < j.+1) with (i <= j). *)
(*       intro i_leq_j. *)
(*       apply (functor_sigma (A := nat) idmap (fun _ => ap S)). *)
(*       apply (IHi j i_leq_j). *)
(*       (* exists (IHi j i_leq_j).1. *) *)
(*       (* apply (ap S). *) *)
(*       (* apply (IHi j i_leq_j).2. *) *)
(*   Defined. *)

(*   (* If j > i, then j is a successor *) *)
(*   Definition gt_is_succ {i j : nat} : i < j -> {k : nat | j = k.+1}. *)
(*   Proof. *)
(*     intro i_lt_j. *)
(*     destruct (leq_to_sum i_lt_j) as [k H]. *)
(*     exact (i+k; H)%nat. *)
(*   Defined. *)
    
(* End Inequalities. *)

(* Notation "[ n ]" := {m : nat | m <= n}. *)
(* Section Cosimplicial_maps. *)
  
(*   (* Definition pfintype (n : nat) := { m : nat | m <= n }. *) *)
(*   (* Definition pFin_include {n : nat} : pfintype n -> nat := pr1. *) *)
(*   (* Coercion pFin_include : pfintype >-> nat. *) *)

(*   (* The i'th coface *) *)
(*   Definition coface {n : nat} (i : nat) (i_leq_n : i <= n) : [n] -> [n.+1]. *)
(*   Proof. *)
(*     intros [j j_leq_n]. *)
(*     destruct (leq_or_gt i j).   (* destruct (dec (i <= j)).      *) *)
(*     (* i <= j *) *)
(*     - exists j. *)
(*       apply (leq_trans _ n _ j_leq_n). apply leq_succ. *)
(*     (* j > i *) *)
(*     - exists j.+1. *)
(*       apply j_leq_n. *)
(*   Defined. *)

(*   (* The i'th codegeneracy *) *)
(*   (* s_i j = *)
(*           j, if j <= i *)
(*           j-1, if j > i  *) *)
(*   Definition codegen {n : nat} (i : nat) (i_leq_n : i <= n) : [n.+1] -> [n]. *)
(*   Proof. *)
(*     intros [j j_leq_Sn]. *)
(*     destruct (leq_or_gt j i). *)
(*     (* j <= i *) *)
(*     - exists j. *)
(*       apply (leq_trans _ i _ t i_leq_n). *)
(*     (* j > i *) *)
(*     - destruct (gt_is_succ t) as [k H]. (* j is a successor *) *)
(*       exists k. *)
(*       change (k <= n) with (k.+1 <= n.+1). *)
(*       apply (@leq_transd k.+1 j n.+1)%nat. *)
(*       rewrite H. apply leq_refl. *)
(*       apply j_leq_Sn. *)
(*   Defined. *)

(* End Cosimplicial_maps. *)


    





    
  
  