Require Import HoTT.
From A_BPQ
     Require Import path_lemmas finite_types conn_ptype delooping monoids_and_groups
          group_completion_monoid fintype_monoidal permutations sign Bsgn path_over
          grp_complete_fintype.

(** Introduce some shorthand notations  *)
Local Definition pft {m : nat}
  := path_finite_types m.

Local Definition pft_inv {m : nat} {A B}
  := inv_path_finite_types m A B.

Local Definition pbs_inv {A B : FinType} 
  := equiv_inverse (equiv_path_FinType A B).
  


(** This file is admittedly rather messy. Ideally we would have had a proof of [equiv_Z0_fin2] modeled on the proof in the thesis, but this one will have to do.  *)


Section GrpCompl_To_Fin2.

  Definition sgn_sasb (s a b : nat)
             (sigma : SymGrp s) (alpha : SymGrp a) (betta : SymGrp b) :
    sign ((b+s)+(a+s)) (block_sum (block_sum sigma alpha) (block_sum sigma betta))
    = sign (b+a) (block_sum alpha betta).
  Proof.
    refine (sgn_block_sum _ _ @ _).
    refine (ap011 equiv_compose' (sgn_block_sum _ _) (sgn_block_sum _ _) @ _).
    refine (ecompose_ee_e _ _ _ @ _).
    refine (_ @ (sgn_block_sum _ _)^).
    apply (ap (equiv_compose' (sign b betta))).
    refine (ap (equiv_compose' (sign s sigma))
               (symm_sigma2 _ _) @ _).               
    refine (ecompose_e_ee _ _ _ @ _).
    refine (_ @ ecompose_1e _).
    apply (ap (fun f => f oE sign a alpha)).
    apply invol_SymGrp2.
  Qed.

  (* make these their own lemmas because they don't need to get unfolded later *)
  (* Definition BSgn_sum_sum (s a1 a2 : nat) *)
  (*   : BSgn _ (sum_finite_types (sum_finite_types (canon s) (canon a1)) *)
  (*                              (sum_finite_types (canon s) (canon a2))) *)
  (*     = BSgn _ (sum_finite_types (canon (a1 + s)) (canon (a2 + s))) *)
  (*   := ap (BSgn _) (ap011 sum_finite_types *)
  (*                         (sum_finite_types_canon) *)
  (*                         (sum_finite_types_canon)). *)

  Definition sum_FinType_uncurry : FinType * FinType -> FinType
    := fun AB =>
         match AB with
           (A,B) => sum_FinType A B
         end.

  Definition canonsum_FinType (a b : nat)
    : sum_FinType (canon_FinType a) (canon_FinType b) = canon_FinType (b+a)
    :=
      path_FinType
        (sum_FinType (canon_FinType a) (canon_FinType b))
        (canon_FinType (b+a))
        (equiv_finsum a b).
                                                     

  Definition Bsign_sum2 (s a b : nat)
    : Bsign _ (sum_finite_types
              (sum_finite_types (canon s) (canon a))
              (sum_finite_types (canon s) (canon b))) =
      Bsign _ (sum_finite_types (canon (a + s)) (canon (b + s))).

  (*     Bsign_uncurry *)
  (*       (fin_to_FinType *)
  (*          (sum_finite_types *)
  (*             (sum_finite_types (canon s) (canon a)) *)
  (*             (sum_finite_types (canon s) (canon b)))) = *)
  (*     Bsign_uncurry (fin_to_FinType (sum_finite_types (canon (a + s)) (canon (b + s)))). *)
  (* Proof. *)
  (*   apply (ap (Bsign_uncurry)). *)
  (*   exact (ap011 sum_FinType (canonsum_FinType s a) (canonsum_FinType s b)). *)
  (* Defined. *)
    apply (ap (Bsign _)).
    apply (ap011 sum_finite_types);
      apply sum_finite_types_canon.
  Defined.

  Definition Bsign_sum_canon2 (a1 a2 : nat)
    : Bsign _ (sum_finite_types (canon a1) (canon a2)) = canon 2
    := ap (Bsign _) sum_finite_types_canon @ deloop_fin_canon (a2 + a1) 2 (sgnhom _).
             
  (*   : Bsign_uncurry (fin_to_FinType (sum_finite_types (canon a1) (canon a2))) = canon 2. *)
  (* Proof. *)
  (*   refine (_ @ deloop_fin_canon (a2 + a1) 2 (sgnhom _)). *)
  (*   (* change (Bsign ?m ?x) with (Bsign_uncurry (m; x)). *) *)
  (*   change (deloop_fin ?m 2 (sgnhom ?m) ?x) with (Bsign_uncurry (fin_to_FinType x)). *)
  (*   apply (ap Bsign_uncurry). *)
  (*   apply (canonsum_FinType a1 a2). *)
  (* Defined. *)


  Definition Bsign_SASB_canon (s a1 a2 : nat) :
    (* Bsign_uncurry (fin_to_FinType (sum_finite_types (canon a1) (canon a2))) = *)
    (* Bsign_uncurry (fin_to_FinType (sum_finite_types *)
    (*                                  (sum_finite_types (canon s) (canon a1)) *)
    (*                                  (sum_finite_types (canon s) (canon a2)))) *)
                 
    Bsign (a2 + a1) (sum_finite_types (canon a1) (canon a2)) =
    Bsign (a2 + s + (a1 + s))
         (sum_finite_types
            (sum_finite_types (canon s) (canon a1))
            (sum_finite_types (canon s) (canon a2)))
  := 
    Bsign_sum_canon2 a1 a2 @ (Bsign_sum_canon2 (a1+s) (a2 + s))^ @ (Bsign_sum2 s a1 a2)^.


  Lemma blocksum_is_ap011 (a b : nat) (alpha : canon a = canon a) (betta : canon b = canon b)
    : block_sum (pft_inv alpha) (pft_inv betta) =
      pft_inv (sum_finite_types_canon^
               @ (ap011 sum_finite_types alpha betta @ sum_finite_types_canon)).
  Proof.
    intros. unfold block_sum.
    unfold sum_finite_types_canon.
    change (path_finite_types ?m ?A ?B) with (pft A B).
    assert (pft_inv_pp
            : forall (m : nat) (A B C : Finite_Types m) (x : A = B) (y : B = C),
               pft_inv (x @ y) = pft_inv y oE pft_inv x).
    { intros m A B C [] []. simpl. apply inverse. apply ecompose_e1. }
    rewrite pft_inv_pp. rewrite pft_inv_pp. clear pft_inv_pp.
    assert (pft_sect : forall (m : nat) (A B : Finite_Types m) (e : A <~> B),
               pft_inv (pft A B e)
              = e).
    { intros. exact (eissect (equiv_path_finite_types _ A B) e). }
    rewrite pft_sect. 
    rewrite <- path_finite_types_V. rewrite pft_sect.
    apply (ap (fun f => f oE (equiv_finsum a b)^-1)).
    apply (ap (fun f => equiv_finsum a b oE f)).
    cut (forall (A : Finite_Types a) (B : Finite_Types b)
                (alpha' : canon a = A) (betta' : canon b = B),
            pft_inv alpha' +E pft_inv betta' = pft_inv (ap011 sum_finite_types alpha' betta')).
    { intro H. apply (H _ _ alpha betta). }
    intros A B [] []. apply path_equiv. apply path_arrow. intros [x | x]; reflexivity.
  Qed.

        (* change Bsign to use equiv_functor_deloop' ? *)
  Definition loops_functor_uncurried {X Y : pType} (f : X -> Y) (p : f (point X) = point Y)
    : loops X -> loops Y.
  Proof.
    apply (@loops_functor X Y).
    exact (Build_pMap X Y f p).
  Defined.

    
  (* If two maps agree on the loop space, they are equal *)
  (* move? Make variant with f g : pMap X Y, and phomotopy?*)
  Definition deloop_eq (X: Conn_pType) (Y : pType) {istrunc_y : IsTrunc 1 Y}
             (f g : X -> Y) (pt_f : f (point X) = point Y) (pt_g : g (point X) = point Y)
    : loops_functor_uncurried f pt_f == loops_functor_uncurried g pt_g ->
      f == g.
  Proof.
    intro H.
    intro x.
    revert x.
    srapply (deloop_ind_set X); simpl.
    - exact (pt_f @ pt_g^).
    - intro.
      unfold loops_functor_uncurried in H. unfold loops_functor in H. simpl in H.
      refine (transport_paths_FlFr _ _ @ _).
      apply moveL_pV. refine (concat_pp_p _ _ _ @ _).
      refine (concat_pp_p _ _ _ @ _). apply moveR_Vp.
      refine (concat_pp_p _ _ _ @ _). apply moveR_Mp.
      apply inverse.
      apply H.
  Defined.

  Definition SAB (s a b : nat) := (conn_ptype_prod (pFin s) (conn_ptype_prod (pFin a) (pFin b))).

  Definition pmap_BsignAB (s a b : nat) : pMap (SAB s a b) (pFin 2).
  Proof.
    srapply @Build_pMap.
    - intros [S [A B]].
      exact (Bsign _ (sum_finite_types A B)).
    - unfold point. apply (Bsign_sum_canon2 a b).
  Defined.

  Definition pmap_Bsign_SASB (s a b : nat) : pMap (SAB s a b) (pFin 2).
  Proof.
    srapply @Build_pMap.
    - intros [S [A B]].
      exact (Bsign _ (sum_finite_types (sum_finite_types S A) (sum_finite_types S B))).
    - unfold point. refine (_ @ Bsign_sum_canon2 (s +' a) (s +' b)).
      apply (ap (Bsign _)). apply (ap011 sum_finite_types);
      apply sum_finite_types_canon.
  Defined.

  (* Definition Bsign_SASB' (s a b : nat) *)
  (*   : pHomotopy (pmap_BsignAB s a b) (pmap_Bsign_SASB s a b). *)
  (* Proof. *)
  (*   srapply @Build_pHomotopy. *)
  (*   - srapply (deloop_eq (SAB s a b) (pFin 2)). *)
  (*     + apply (point_eq). + apply point_eq. *)
  (*     + unfold loops_functor_uncurried. *)
  (*       intro x.  *)
  (*       simpl. *)
      

  
  Definition Bsign_SASB (s a1 a2 : nat)
             (S : Finite_Types s) (A1 : Finite_Types a1) (A2 : Finite_Types a2)
  : Bsign (a2 + a1) (sum_finite_types A1 A2) =
    Bsign (a2 + s + (a1 + s)) (sum_finite_types (sum_finite_types S A1) (sum_finite_types S A2)).
  Proof.
    revert S A1 A2.
    cut (forall SA : (Finite_Types s) * ((Finite_Types a1) * (Finite_Types a2)),
            Bsign_uncurry (fin_to_FinType (sum_finite_types (fst (snd SA)) (snd (snd SA)))) =
            Bsign_uncurry
              (fin_to_FinType (sum_finite_types (sum_finite_types (fst SA) (fst (snd SA)))
                                               (sum_finite_types (fst SA) (snd (snd SA)))))).
    { intros H S A1 A2. exact (H (S, (A1, A2))). }

    (* srapply (deloop_eq (conn_ptype_prod (pFin s) (conn_ptype_prod (pFin a1) (pFin a2))) (pFin 2)). *)
    (* - simpl. unfold point. unfold Bsign_uncurry. *)
      
    (*   apply Bsign_SASB_canon. *)
    (*        . *)
    
    
    srapply (@deloop_ind_set
               (conn_ptype_prod (pFin s) (conn_ptype_prod (pFin a1) (pFin a2)))
            ).
    + simpl. unfold point.
      apply Bsign_SASB_canon.
    + simpl. unfold point. intro.
      refine (transport_paths_FlFr ω _ @ _).
      (* revert ω. *)
      (* apply (equiv_functor_forall_pf *)
      (*          (equiv_inverse (equiv_path_prod (_,_) (_,_)))). *)
      (* simpl. intros [sigma p]. revert p. *)
      (* apply (equiv_functor_forall_pf *)
      (*          (equiv_inverse (equiv_path_prod (_,_) (_,_)))). simpl. *)
      (* intros [alpha betta]. *)
      
      assert (
          p : forall (x : Finite_Types s * (Finite_Types a1 * Finite_Types a2))
                     (q : (canon s, (canon a1, canon a2)) = x),
            (ap
               (fun x : Finite_Types s * (Finite_Types a1 * Finite_Types a2) =>
                  Bsign (a2 + a1) (sum_finite_types (fst (snd x)) (snd (snd x)))) q)
            =
            
            (* ap (Bsign_uncurry) (ap (fin_to_FinType) *)
            (*                       (ap011 sum_finite_types *)
            (*                              (ap fst (ap snd q)) *)
            (*                              (ap snd (ap snd q))))). *)
            
            ap (Bsign (a2 + a1))
               (ap011 sum_finite_types
                      (ap fst (ap snd q))
                      (ap snd (ap snd q)))).
      { intros x []. reflexivity. }
      rewrite (p _ ω). clear p. 
      assert (
          p : forall (x : Finite_Types s * (Finite_Types a1 * Finite_Types a2))
                     (q : (canon s, (canon a1, canon a2)) = x),
            ap (fun x : Finite_Types s * (Finite_Types a1 * Finite_Types a2) =>
                  Bsign (a2 + s + (a1 + s))
                       (sum_finite_types (sum_finite_types (fst x) (fst (snd x)))
                                         (sum_finite_types (fst x) (snd (snd x))))) q
            =
            (* ap (Bsign_uncurry) *)
            (*    (ap (fin_to_FinType) *)
            (*        (ap011 *)
            (*           sum_finite_types *)
            (*           (ap011 sum_finite_types ((ap fst q)) *)
            (*                  ((ap fst (ap snd q)))) *)
            (*           (ap011 sum_finite_types ((ap fst q)) *)
            (*                  ((ap snd (ap snd q))))))). *)
            ap (Bsign _)
               (ap011
                  sum_finite_types
                  (ap011 sum_finite_types ((ap fst q))
                         ((ap fst (ap snd q))))
                  (ap011 sum_finite_types ((ap fst q))
                         ((ap snd (ap snd q)))))).
      { intros x []. reflexivity. }
      rewrite (p _ ω). clear p.
      revert ω.
      apply (equiv_functor_forall_pb
               (equiv_path_triple_prod (canon s, (canon a1, canon a2)) 
                                       (canon s, (canon a1, canon a2)))).
      intros [p [q r]].
      simpl in p. simpl in q. simpl in r. 
      change
        (equiv_path_triple_prod ?a ?b ?c) with
      (path_triple_prod a b c).  unfold path_triple_prod.
      rewrite ap_fst_path_prod. rewrite ap_snd_path_prod. rewrite ap_snd_path_prod.

      
      rewrite ap_fst_path_prod. unfold Bsign_SASB_canon.
      unfold Bsign_sum_canon2. unfold Bsign_sum2.
      apply moveL_pV. apply moveL_pV.
      repeat rewrite concat_pp_p.
      apply moveR_Vp. apply moveR_Mp. apply moveR_Mp.
      rewrite inv_pp.
      rewrite <- ap_V.
      rewrite <- ap_V.
      rewrite <- (ap_V (Bsign (a2 + a1)%nat) sum_finite_types_canon).
      repeat refine (_ @ concat_pp_p _ _ _).
      apply moveL_pM.
      repeat refine (_ @ concat_p_pp _ _ _).
      rewrite <- (ap_pp (Bsign (a2 + a1)%nat)).
      rewrite <- (ap_pp (Bsign (a2 + a1)%nat)).
      apply moveR_pV.
      repeat refine (concat_p_pp _ _ _ @ _).
      apply moveR_pM.
      repeat refine (concat_pp_p _ _ _ @ _).
      rewrite <- (ap_pp (Bsign (_ + _)%nat)).
      rewrite <- (ap_pp (Bsign (_ + _)%nat)).
      rewrite <- (ap_pp (Bsign (_ + _)%nat)).
      rewrite <- (ap_pp (Bsign (_ + _)%nat)).
      apply moveL_pV. refine (_ @ concat_p_pp _ _ _).
      refine (_ @ (deloop_fin_loop _ _ _ _)^).
      refine (concat_pp_p _ _ _ @ _).
      refine (deloop_fin_loop _ _ _ _ @ _). simpl.
      apply (ap (path_finite_types 2 _ _)).
      refine (_ @ ((sgn_sasb _ _ _ (pft_inv p) (pft_inv q) (pft_inv r))) @ _);
        apply (ap (sign _)).
      - apply inverse.
        refine (_ @ blocksum_is_ap011
                  (a1 + s) (a2 + s)
                  (pft (canon _) (canon _)
                       (block_sum (pft_inv p) (pft_inv q)))
                  (pft (canon _) (canon _) (block_sum (pft_inv p) (pft_inv r))) @ _ ).
        { apply (ap011 block_sum).
          - apply inverse.
            exact (eissect
                     (equiv_path_finite_types (a1 + s) (canon (a1 + s)) (canon (a1 + s)))
                     (block_sum (pft_inv p) (pft_inv q))
                  ).
          - apply inverse.
            exact (eissect
                     (equiv_path_finite_types (a2 + s) (canon (a2 + s)) (canon (a2 + s)))
                     (block_sum (pft_inv p) (pft_inv r))
                  ). }
        apply (ap (inv_path_finite_types (a2 + s + (a1 + s)) (canon (a2 + s + (a1 + s))) 
                                             (canon (a2 + s + (a1 + s))))).
        apply whiskerL.
        repeat refine (_ @ concat_pp_p _ _ _). apply whiskerR.
        rewrite blocksum_is_ap011.  rewrite blocksum_is_ap011.
        rewrite ap011_VV.
        rewrite <- ap011_pp_pp. rewrite <- ap011_pp_pp.
        apply (ap011 (ap011 sum_finite_types)).
        * refine (eisretr
                   (equiv_path_finite_types (a1 + s) (canon (a1 + s)) (canon (a1 + s)))
                   (sum_finite_types_canon^ @ (ap011 sum_finite_types p q @ sum_finite_types_canon))
                   @ _ ).
          apply concat_p_pp.
        * refine (eisretr
                   (equiv_path_finite_types (a2 + s) (canon (a2 + s)) (canon (a2 + s)))
                   (sum_finite_types_canon^ @ (ap011 sum_finite_types p r @ sum_finite_types_canon))
                   @ _ ).
          apply concat_p_pp.
      - refine (blocksum_is_ap011 _ _ q r ).
  Defined.
    
  Definition Bsign_SASB_canon_id (s a1 a2 : nat)
    : Bsign_SASB s a1 a2 (canon s) (canon a1) (canon a2) = Bsign_SASB_canon s a1 a2.
  Proof.
    refine
      (deloop_ind_beta_pt
         (conn_ptype_prod (pFin s) (conn_ptype_prod (pFin a1) (pFin a2))) _
         (Bsign_SASB_canon s a1 a2)
         _ _
      ).
  Qed.

  Definition ap011_Bsign_canon {m1 m2 n1 n2 : nat} (p1 : m1 = n1) (p2 : m2 = n2)
    : Bsign (m2 + m1) (sum_finite_types (canon m1) (canon m2))
      = Bsign (n2 + n1) (sum_finite_types (canon n1) (canon n2)).
  Proof.
    (* change (Bsign (m2 + m1) (sum_finite_types (canon m1) (canon m2))) *)
    (*        with (sum_FinType (canon_FinType m1) (canon_FinType m2)). *)
    change (Bsign ?m ?A) with (Bsign_uncurry (fin_to_FinType A)).
    apply (ap Bsign_uncurry).
    
    (* change (sum_finite_types (canon m1) (canon m2)) with (sum_FinType (canon_FinType m1) *)
    (*                                                                  (canon_FinType m2)). *)

    change (sum_finite_types (canon ?m) (canon ?n)) with (sum_finite_types (canon_FinType m)
                                                                           (canon_FinType n)).
    change (fin_to_FinType
              (sum_finite_types (canon_FinType ?m) (canon_FinType ?n))) with
    (sum_FinType (canon_FinType m) (canon_FinType n)).
    apply (ap011 sum_FinType); apply (ap canon_FinType).
    - exact p1. - exact p2.
        
    (* apply (ap011 (fun a b => fin_to_FinType (sum_finite_types (canon a) (canon b))) p1 p2). *)
  Defined.
  
  Definition grpcompl_to_fin2 : Z -> Finite_Types 2.
  Proof.
    srapply @grp_compl_FinType_rec.
    - simpl.
      intros A B. apply (Bsign_uncurry). exact (sum_FinType A B).
      (* intros [a1 A1] [a2 A2]. *)
      (* exact (Bsign (a2 + a1) (sum_finite_types A1 A2)). *)
    - simpl. intros [s S] [a1 A1] [a2 A2].
      apply Bsign_SASB.
    - intros [s S] [t T] [a1 A1] [a2 A2]. 
      
      change {| card_FinType := ?m; fintype_of_FinType := ?A |} with (fin_to_FinType A).
      revert A1.
      apply (deloop_ind_prop (pFin a1)).
      revert A2.
      apply (deloop_ind_prop (pFin a2)).
      revert T.
      apply (deloop_ind_prop (pFin t)).
      revert S.
      apply (deloop_ind_prop (pFin s)).
      hnf.
      change (point (pFin ?n)) with (canon n).

      (* unfold sum_FinType. *)
      change (fin_to_FinType (canon ?m)) with
      (canon_FinType m). 
      
      assert (H : forall (x m n : nat)
                       (S S': Finite_Types x) (A : Finite_Types m) (B : Finite_Types n)
                       (p : S = S'),
                 Bsign_SASB _ _ _ S A B =
                 Bsign_SASB _ _ _ S' A B
                           @ (ap (Bsign _)
                                 (ap011 sum_finite_types
                                        (ap011 sum_finite_types p idpath)
                                        (ap011 sum_finite_types p idpath)))^).
                                 (* (ap (fun x => sum_finite_types (sum_finite_types x A) *)
                                 (*                                (sum_finite_types x B)) p))^). *)
      { intros. destruct p. refine (concat_p1 _)^. }
      rewrite (H _ _ _ _ _ _ _ (finsum_id_fix t s)). clear H.
      assert (H :
                forall (x m n : nat)
                       (S S': Finite_Types x) (A A' : Finite_Types m) (B B' : Finite_Types n)
                       (p : S = S') (q : A = A') (r : B = B'),
                  Bsign_SASB _ _ _ S A B =
                  (ap (Bsign _) (ap011 sum_finite_types q r))
                    @ Bsign_SASB _ _ _ S' A' B' @
                    (ap (Bsign _) (ap011 sum_finite_types
                                        (ap011 sum_finite_types p q)
                                        (ap011 sum_finite_types p r)))^).
      { intros. destruct p. destruct q. destruct r.
        refine (_ @ (concat_p1 _)^).
        refine (concat_1p _)^. }
      rewrite (H _ _ _ _ _ _ _ _ _
                 idpath (finsum_id_fix s a1) (finsum_id_fix s a2)).
      (* rewrite (H _ _ _ _ _ _ _ _ _ *)
      (*            (finsum_id t s) idpath idpath). *)
      clear H.
      (* rewrite (Bsign_SASB_canon_id s a1 a2). *)
      rewrite Bsign_SASB_canon_id.
      rewrite Bsign_SASB_canon_id.
      rewrite Bsign_SASB_canon_id.
      unfold Bsign_SASB_canon.
      change (ap (Bsign (a2 + s + (a1 + s)))
                 (ap011 sum_finite_types (finsum_id_fix s a1) (finsum_id_fix s a2)))
      with (Bsign_sum2 s a1 a2).
      repeat rewrite (concat_pp_p (Bsign_sum_canon2 a1 a2)). apply whiskerL.
      (* rewrite <- (inv_V (Bsign_sum_canon2 a1 a2)). *)
      
      (* destruct ((Bsign_sum_canon2 a1 a2)^). rewrite concat_1p. rewrite concat_1p. *)
      rewrite <- (inv_pp (Bsign_sum2 s a1 a2) (Bsign_sum_canon2 (a1 + s) (a2 + s)) ).
      rewrite (concat_pp_p (Bsign_sum_canon2 (a1 + s) (a2 + s))).
      rewrite (concat_p_pp (Bsign_sum2 s a1 a2)).
      rewrite (concat_pp_p (Bsign_sum2 s a1 a2 @ Bsign_sum_canon2 (a1 + s) (a2 + s))).
      rewrite concat_V_pp.
      assert (H : forall (m1 m2 n1 n2 : nat) (p1 : m1 = n1) (p2 : m2 = n2),
                 (Bsign_sum_canon2 n1 n2)^
                 = (Bsign_sum_canon2 m1 m2)^ @ (ap011_Bsign_canon p1 p2)).
      { intros. destruct p1. destruct p2. apply inverse. apply concat_p1.  }
      
      rewrite (H _ _ _ _ (nat_plus_assoc a1 s t)^ (nat_plus_assoc a2 s t)^).
      clear H. repeat rewrite concat_pp_p. apply whiskerL.
      apply moveR_Vp.
      unfold Bsign_sum2.
      apply moveR_Vp.
      repeat rewrite concat_p_pp.
      apply moveL_pV. apply moveL_pV.
      rewrite <- (ap_pp (Bsign (a2 + (s + t) + (a1 + (s + t))))).
      rewrite <- ap011_pp_pp.
      rewrite concat_pp_p.
      rewrite <- (ap_pp (Bsign (a2 + s + t + (a1 + s + t)))).
      rewrite <- ap011_pp_pp.
      assert (H : forall (X1 X2 Y1 Y2 : FinType) (p : X1 = X2) (q : Y1 = Y2),
                 ap011 (fun A B : FinType => Bsign_uncurry (sum_FinType A B)) p q =
                 ap Bsign_uncurry (ap011 sum_FinType p q)).
      { intros. destruct p. destruct q. reflexivity. }
      rewrite H. clear H. unfold ap011_Bsign_canon.
      assert (H : forall (m : nat) (A B : Finite_Types m) (p : A = B),
                 ap (Bsign m) p =
                 ap Bsign_uncurry (ap fin_to_FinType p)).
      { intros. destruct p. reflexivity. }
      rewrite H. rewrite H. clear H.
      
      refine (_ @ ap_pp Bsign_uncurry (ap fin_to_FinType _)
                                     (ap011 sum_FinType
                                            (ap canon_FinType _) (ap canon_FinType _))).
                
                                     (* (ap011 (fun a b : nat => *)
                                     (*           fin_to_FinType (sum_finite_types (canon a) (canon b))) *)
                                     (*        _ _)). *)
      refine ((ap_pp Bsign_uncurry
                     (ap011 sum_FinType
                            (FinType_assoc (canon_FinType t) (canon_FinType s) (canon_FinType a1))
                            (FinType_assoc (canon_FinType t) (canon_FinType s) (canon_FinType a2)))
                     _)^ @ _).
      apply (ap (ap Bsign_uncurry)).
      assert (H : forall (m n : nat) (A1 A2 : Finite_Types m) (B1 B2 : Finite_Types n)
                         (p1 : A1 = A2) (p2 : B1 = B2),
                 ap fin_to_FinType (ap011 sum_finite_types p1 p2) =
                 ap011 sum_FinType (ap fin_to_FinType p1) (ap fin_to_FinType p2)).
      { intros. destruct p1. destruct p2. reflexivity. }
      rewrite H. rewrite H. clear H.
      rewrite <- ap011_pp_pp.
      refine (_ @ ap011_pp_pp sum_FinType _ _ _ _).
      cut (forall (a : nat),
              FinType_assoc (canon_FinType t) (canon_FinType s) (canon_FinType a) @
                           ap fin_to_FinType (ap011 sum_finite_types 1 (finsum_id_fix s a) @
                                                   sum_finite_types_canon) =
              ap fin_to_FinType (ap011 sum_finite_types (finsum_id_fix t s) 1 @
                                       sum_finite_types_canon) @
                  ap canon_FinType (nat_plus_assoc a s t)^).
      { intro H.
        apply (ap011 (ap011 sum_FinType)); apply H. }
      intro a.
      apply moveL_Mp. (* hei *)
      refine (_ @ eq_canon_FinType_assoc _ _ _).
      unfold canon_FinType_assoc.
      unfold canon_assoc.
      (* move? *)
      assert (path_finite_types_nat_l : forall (m n: nat)
                                               (A1 A2 : Finite_Types m)
                                               (B : Finite_Types n)
                                               (e : A1 <~> A2),
                 ap011 sum_finite_types
                       (path_finite_types _ A1 A2 e)
                       (idpath B) =
                 path_finite_types _ (sum_finite_types A1 B) (sum_finite_types A2 B) 
                                   (equiv_functor_sum_r e )).
      { intros.
        refine (_ @ ap
                  (fun f =>
                     path_finite_types (n + m)
                                       (sum_finite_types A1 B)
                                       (sum_finite_types A2 B)
                                       (equiv_functor_sum_r f))
                  (eissect (equiv_path_finite_types _ _ _) e)).
        simpl.
        destruct (path_finite_types m A1 A2 e).
        apply inverse.
        refine (_ @ path_finite_types_id _ _).
        apply (ap (path_finite_types _ _ _)). simpl.
        apply path_equiv. apply path_arrow. intros [x | x]; reflexivity. }

      assert (path_finite_types_nat_r : forall (m n: nat)
                                               (A : Finite_Types m)
                                               (B1 B2 : Finite_Types n)
                                               (e : B1 <~> B2),
                 ap011 sum_finite_types
                       (idpath A)
                       (path_finite_types _ B1 B2 e) =
                 path_finite_types _ (sum_finite_types A B1) (sum_finite_types A B2) 
                                   (equiv_functor_sum_l e )).
      { intros.
        refine (_ @ ap
                  (fun f =>
                     path_finite_types (n + m)
                                       (sum_finite_types _ _)
                                       (sum_finite_types _ _)
                                       (equiv_functor_sum_l f))
                  (eissect (equiv_path_finite_types _ _ _) e)).
        simpl.
        destruct (path_finite_types _ _ _ e).
        apply inverse.
        refine (_ @ path_finite_types_id _ _).
        apply (ap (path_finite_types _ _ _)). simpl.
        apply path_equiv. apply path_arrow. intros [x | x]; reflexivity. }

      
      
      (* assert (path_finite_types_nat : forall (m1 m2 : nat) *)
      (*                                        (A1 B1 : Finite_Types m1) *)
      (*                                        (A2 B2 : Finite_Types m2) *)
      (*                                        (e1 : A1 <~> B1) *)
      (*                                        (e2 : A2 <~> B2), *)
      (*            ap011 sum_finite_types *)
      (*                  (path_finite_types _ A1 B1 e1) *)
      (*                  (path_finite_types _ A2 B2 e2) = *)
      (*            path_finite_types _ (sum_finite_types A1 A2) (sum_finite_types B1 B2) *)
      (*                              (equiv_functor_sum' e1 e2)). *)
      (* { intros. *)
      (*   refine (_ @ ap011 *)
      (*             (fun f g => *)
      (*                path_finite_types (m2 + m1) *)
      (*                                  (sum_finite_types A1 A2) (sum_finite_types B1 B2) (f +E g)) *)
      (*             (eissect (equiv_path_finite_types _ _ _) e1) *)
      (*             (eissect (equiv_path_finite_types _ _ _) e2)). *)
      (*   simpl. *)
      (*   destruct (path_finite_types m1 A1 B1 e1). *)
      (*   destruct (path_finite_types m2 A2 B2 e2). *)
      (*   apply inverse. *)
      (*   refine (_ @ path_finite_types_id _ _). *)
      (*   apply (ap (path_finite_types _ _ _)). simpl. *)
      (*   apply path_equiv. apply path_arrow. intros [x | x]; reflexivity. } *)

      rewrite path_finite_types_nat_l. clear path_finite_types_nat_l.
      rewrite path_finite_types_nat_r. clear path_finite_types_nat_r.
      change (ap fin_to_FinType ?p) with (pft_to_pbs p).
      unfold FinType_assoc.
      unfold sum_FinType.  unfold canon_FinType.
      (* change sum_FinType . . . with fin_to_FinType . . . *)
      
      (* refine (whiskerR (ap inverse *)
      (*                      (@path_FinType_fix *)
      (*            (a + (s + t))%nat *)
      (*            (sum_finite_types (sum_finite_types (canon t) (canon s)) (canon a)) *)
      (*   (sum_finite_types (canon (s + t)) (canon a)) (equiv_functor_sum_r (equiv_finsum t s)) *)
      (*         )) _ @ _). *)
      (* Arguments pft_to_pbs : clear implicits. *)
      unfold sum_finite_types_canon.
      rewrite <- path_finite_types_compose.
      rewrite <- path_finite_types_compose.
      rewrite path_FinType_fix.
      rewrite path_FinType_fix.
      apply moveR_Vp.
      rewrite <- path_FinType_compose.
      rewrite <- path_FinType_compose.

      apply (ap
               (fun e =>
                  path_FinType
                    (fin_to_FinType
                       (sum_finite_types
                          (fin_to_FinType
                             (sum_finite_types (fin_to_FinType (canon t)) (fin_to_FinType (canon s))))
                          (fin_to_FinType (canon a))))
                    (fin_to_FinType (canon (a + s + t))) e)).
      simpl.
      repeat rewrite ecompose_ee_e.
      rewrite ecompose_V_ee.
      rewrite ecompose_Ve. rewrite ecompose_e1.
      reflexivity.
  Defined.


End GrpCompl_To_Fin2.
  (* Declare Scope nat2_scope. *)



Section IsEquiv_GrpCompl_To_Fin2.
  (* For reasons, it is easier to work with addition on natural numbers defined by induction  *)
  (* on the right hand element *)
  (* Open Scope nat2_scope. *)
  
    (* move? *)
  Definition transpose_last_two_is_block_sum (a : nat)
    : fin_transpose_last_two a = (block_sum equiv_idmap twist2).
  Proof.
    apply path_equiv. apply path_arrow.
    intros [[x | []] | []]; reflexivity.
  Defined.

  Definition block_sum_is_id (m n : nat)
    : equiv_idmap (Fin (m +' n)) = block_sum (equiv_idmap (Fin m)) (equiv_idmap (Fin n)).
  Proof.
    unfold block_sum. unfold fin_equiv_sum.
    assert (p : equiv_idmap (Fin m) +E equiv_idmap (Fin n) = equiv_idmap ((Fin m) + (Fin n))).
    { apply path_equiv. apply path_arrow. intros [x | x]; reflexivity. }
    rewrite p.     
    rewrite ecompose_e1. apply inverse. apply ecompose_eV.
  Qed.

  
  (* We want to show that the map above induces and equivalence on the component of cardinality 0 *)
  (* First we connect all the canonical points in this component *)


  (* move. Necessary? *)
  Definition block_sum_0 {a : nat} (alpha : Fin a <~> Fin a) (sigma : Fin 0 <~> Fin 0)
    : block_sum alpha sigma = alpha.
  Proof.
    unfold block_sum. unfold fin_equiv_sum.
    simpl. apply emoveR_eV.
    apply path_equiv. apply path_arrow.
    intros [x | []]. reflexivity.
  Defined.
    
  Definition path_base_0 (A : FinType)
    : FinType_to_Z (canon_FinType 0) (canon_FinType 0) =
      FinType_to_Z A A.
  Proof.
    apply (path_Z A);
      apply (path_FinType); apply sum_empty_r.
  Defined.

  Definition path_base_2 (A : FinType)
    : FinType_to_Z A A = FinType_to_Z (canon_FinType 2) (canon_FinType 2) :=
    (path_base_0 A)^ @ (path_base_0 (canon_FinType 2)).  

  (* := *)
  (*   (lcancel_canon a 0 0). *)

  (* (* necessary? *) *)
  (* Definition unit_FinType : FinType. *)
  (* Proof. *)
  (*   apply (Build_FinType 1). *)
  (*   exists Unit. apply tr. *)
  (*   apply equiv_inverse. *)
  (*   apply equiv_contr_unit. *)
  (* Defined. *)
  
  Definition path_succ (a b : nat)
    : FinType_to_Z (canon_FinType a) (canon_FinType b) =
      FinType_to_Z (canon_FinType a.+1) (canon_FinType b.+1).
  Proof.
    apply (path_Z (canon_FinType 1));
      exact (FinType_symmetric _ _ @ finsum_id _ _).
  Defined.

  Definition path_succ_cancel_path {a b : nat}
             (alpha : canon_FinType a <~> canon_FinType a)
             (betta : canon_FinType b <~> canon_FinType b)
    : (path_succ a b) @
         ap011 FinType_to_Z (path_FinType (canon_FinType a.+1) (canon_FinType a.+1) (alpha +E equiv_idmap))
                           (path_FinType (canon_FinType b.+1) (canon_FinType b.+1) (betta +E equiv_idmap))
      @ (path_succ a b)^
      =
      ap011 FinType_to_Z (path_FinType _ _ alpha) (path_FinType _ _ betta).
  Proof.
    apply moveR_pV.
    unfold path_succ.
    rewrite <- path_Z_pp_r.
    rewrite <- path_Z_pp_l.
    rewrite <- path_FinType_compose. rewrite <- path_FinType_compose.
    rewrite <- path_FinType_1.
    rewrite <- path_FinType_sum. rewrite <- path_FinType_sum.
    rewrite <- path_FinType_compose. rewrite <- path_FinType_compose.
    rewrite <- path_FinType_compose. rewrite <- path_FinType_compose.
    apply (ap011 (path_Z (canon_FinType 1))); apply (ap (path_FinType _ _));
      apply path_equiv; apply path_arrow;
        intro x; repeat destruct x as [x | x]; try destruct x; reflexivity.
  Defined.

  (* (* necessary? *) *)
  (*   Definition lcancel_Z_path {S A B S' A' B': FinType} *)
  (*            (sigma : S <~> S') (alpha : A <~> A') (betta : B <~> B')  *)
  (*   : ap011 FinType_to_Z (path_FinType _ _ alpha) (path_FinType _ _ betta) = *)

  (*     (lcancel_Z S A B) @ *)
  (*                       ap011 FinType_to_Z *)
  (*                       (path_FinType (sum_FinType S A) (sum_FinType S' A') (sigma +E alpha)) *)
  (*                       (path_FinType (sum_FinType S B) (sum_FinType S' B') (sigma +E betta)) @ *)
  (*                       (lcancel_Z S' A' B')^. *)
  (* Proof. *)
  (*   rewrite path_FinType_sum. rewrite path_FinType_sum. *)
  (*   destruct (path_FinType A A' alpha). *)
  (*   destruct (path_FinType B B' betta). *)
  (*   destruct (path_FinType S S' sigma). *)
  (*   rewrite concat_p1. *)
  (*   apply inverse. apply concat_pV. *)
  (* Defined. *)

  (* (* necessary? *) *)
  (* Definition path_base_2_compose (A B  : FinType) : *)
  (*   (lcancel_Z A B B ) @ path_base_2 (sum_FinType A B) = *)
  (*   path_base_2 B. *)
  (* Proof. *)
  (*   unfold path_base_2. destruct (path_base_0 (canon_FinType 2)). *)
  (*   rewrite concat_p1. rewrite concat_p1. *)
  (*   unfold path_base_0. apply moveR_pV. apply moveL_Vp. *)
  (*   unfold lcancel_Z. rewrite path_Z_compose. rewrite concat_p1. *)
  (*   rewrite <- path_FinType_1. rewrite <- path_FinType_sum. *)
  (*   rewrite <- path_FinType_compose. *)
  (*   apply (ap011 (path_Z _)); apply (ap (path_FinType _ _)); *)
  (*     apply path_equiv; apply path_arrow; intro x; *)
  (*       repeat destruct x as [x | x]; try destruct x; reflexivity. *)
  (* Defined. *)


  Definition path_base_2_succ (a : nat)
    : path_base_2 (canon_FinType a.+1) =
      (path_succ a a)^ @ path_base_2 (canon_FinType a).
  Proof.
    unfold path_base_2. refine (_ @ concat_pp_p _ _ _). apply whiskerR.
    rewrite <- inv_pp. apply (ap inverse).
    assert (forall (A B : FinType) (p : A = B),
               path_base_0 B = path_base_0 A @ ap011 FinType_to_Z p p).
    { intros A B []. rewrite concat_p1. reflexivity. }
    rewrite (X _ _ (FinType_symmetric (canon_FinType 1) (canon_FinType a) @ finsum_id a 1)).
    clear X.
    unfold path_succ.
    rewrite <- path_Z_pp_r. unfold path_base_0.
    rewrite path_Z_compose.
    rewrite <- path_FinType_compose. rewrite <- path_FinType_compose.
    rewrite <- path_FinType_1. rewrite <- path_FinType_sum.
    rewrite <- path_FinType_compose. rewrite <- path_FinType_compose.
    apply (ap011 (path_Z _)); apply (ap (path_FinType _ _));
      apply path_equiv; apply path_arrow; intro x;
        repeat destruct x as [x | x]; try destruct x; reflexivity.
  Defined.
    
      

  (* Definition path_base_0_sum (a b : nat) *)
  (*   : path_base_0 (canon_FinType (a +' b)) = *)
  (*     path_base_0 (canon_FinType a) @ lcancel_canon_fr b a a. *)
  (* Proof. *)
  (*   unfold path_base_0. unfold lcancel_canon_fr. *)
  (*   rewrite path_Z_fr_compose. *)
  (*   rewrite (path_Z_fr_100 _ _ (finsum_id a b)). *)
  (*   rewrite path_FinType_V. *)
  (*   rewrite <- path_FinType_1. rewrite <- path_FinType_1.  *)
  (*   rewrite <- path_FinType_sum. rewrite <- path_FinType_sum. *)
  (*   unfold finsum_id. *)
  (*   repeat rewrite <- path_FinType_compose. *)
  (*   apply (ap011 (path_Z_fr _)); apply (ap (path_FinType _ _)); *)
  (*     apply path_equiv; apply path_arrow; intro x; *)
  (*       repeat destruct x as [x | x]; try destruct x; reflexivity. *)
  (* Defined. *)

  (* Definition path_base_0_succ (a : nat) *)
  (*   : path_base_0 (canon_FinType a.+1) = *)
  (*     path_base_0 (canon_FinType a) @ lcancel_canon_fr 1 a a *)
  (*   := path_base_0_sum a 1.     *)

  
  (* Definition path_base_2 (a : nat) *)
  (*   : FinType_to_Z (canon_FinType 2) (canon_FinType 2) = *)
  (*     FinType_to_Z (canon_FinType a) (canon_FinType a) := *)
  (*   (path_base_0 _)^ @ path_base_0 _. *)

  (* Definition path_base_2 (a : nat) *)
  (*   : FinType_to_Z (canon_FinType 2) (canon_FinType 2) = *)
  (*     (* FinType_to_Z (canon_FinType (2 +' a)) (canon_FinType (2 +' a)) *) *)
  (*     FinType_to_Z (canon_FinType (2 +' a)) (canon_FinType (2 +' a)) *)
  (*   := lcancel_canon_fr a _ _. *)
  (* .       *)
  (* Proof. *)
  (*   apply (path_Z_fr (canon_FinType a)); *)
  (*     apply finsum_id. *)
  (* Defined. *)
    

  Definition path_base_2_is_lcancel (a : nat)
    : path_base_2 (canon_FinType (a +' 2)) = (lcancel_canon a 2 2)^.
      (* (path_base_0 _)^ @ path_base_0 _. *)
  Proof.
    unfold path_base_2. apply moveR_Vp.
    apply moveL_pV.
    unfold lcancel_canon. unfold lcancel_Z.
    rewrite <- path_Z_pp_r. rewrite concat_1p.
    unfold path_base_0.
    rewrite (path_Z_100 _ _ (finsum_id a 2)).
    rewrite path_Z_compose.
    rewrite <- path_FinType_1. rewrite <- path_FinType_1.
    rewrite <- path_FinType_sum. rewrite <- path_FinType_sum.
    repeat rewrite <- path_FinType_compose.
    apply (ap011 (path_Z _)); apply (ap (path_FinType _ _));
      apply path_equiv; apply path_arrow; intro x;
        repeat destruct x as [x | x]; try destruct x; reflexivity.
  Defined.
      

  (*   : FinType_to_Z (canon_FinType 2) (canon_FinType 0) = *)
  (*     FinType_to_Z (canon_FinType (2 +' a)) (canon_FinType a). *)
  (* Proof. *)
    
  (*   refine (lcancel_canon_fr a _ _ @ _). *)
  (*   (* apply (ap011 FinType_to_Z); apply (ap canon_FinType); apply nat_plus_comm. *) *)
  (*   apply (ap011 FinType_to_Z idpath). *)
  (*   refine ((finsum_id 0 a)^ @ _). *)
  (*   apply path_FinType. apply sum_empty_l. *)
    (* apply (ap011 FinType_to_Z idpath). apply (ap canon_FinType). *)
    (* apply inverse. *)
    (* apply nat_plus_n_O. *)
    
    (* refine (lcancel_Z_fr _ _ (canon_FinType a) @ _). *)
    (* (* refine (lcancel_Z (canon_FinType a) _ _ @ _). *) *)
    (* apply (ap011 FinType_to_Z). *)
    (* - apply finsum_id. *)
    (* - apply path_FinType. *)
    (*   apply sum_empty_l. *)
  (* Defined. *)


  (*   refine (lcancel_iter a 2 0 @ _). *)
  (*   apply (ap011 FinType_to_Z idpath). *)
    

  (* Defined. *)
    
    
  (*   induction a. *)
  (*   - reflexivity. *)
  (*   - refine (IHa @ _). apply lcancel_succ. *)
  Definition lcancel_Z_fr_100 {A B S S'} (p : S' = S)
    : lcancel_Z_fr A B S =
      lcancel_Z_fr A B S' @ ap011 FinType_to_Z
                                  (ap011 sum_FinType idpath p)
                                  (ap011 sum_FinType idpath p).
  Proof.
    destruct p. apply inverse.
    apply concat_p1.
  Defined.
                   
  (* Definition natural_path_Z_fr {A1 B1 A2 B2 A3 B3} *)

  (*            ap011 FinType_to_Z p1 q1 @ path_Z A2 B2 A3 B3 p2 q2 = *)
             
  (* Definition path_base_2_sum (a b : nat) *)
  (*   : path_base_2 (a +' b) = *)
  (*     path_base_2 a @ (lcancel_canon_fr b _ _). *)
  (* Proof. *)
  (*   unfold path_base_2. *)
  (*   rewrite path_base_0_sum. apply concat_p_pp. *)
  (* Defined. *)


  (* Definition path_base_2_succ (a : nat) *)
  (*   : path_base_2 (a.+1) = *)
  (*     path_base_2 a @ (lcancel_canon_fr 1 _ _) *)
  (*   := path_base_2_sum a 1. *)

    
    
    (* unfold path_base_2. *)
    (* rewrite (lcancel_Z_fr_100 (finsum_id a 1)). *)
    (* refine (concat_pp_p _ _ _ @ _). *)
    (* rewrite <- ap011_pp_pp. *)
    (* rewrite lcancel_Z_fr_compose. *)
    (* refine (concat_pp_p _ _ _ @ _). *)
    (* refine (concat_pp_p _ _ _ @ _). *)
    (* refine (_ @ concat_p_pp _ _ _). apply whiskerL. *)
    (* unfold lcancel_canon_fr. *)

    (* unfold path_base_2. *)
  (*   refine (_ @ concat_p_pp _ _ _). *)
    
    
  (*   assert (forall (m n n': nat) (p : n' = n), *)
  (*              ap011 FinType_to_Z idpath (ap canon_FinType p) @ lcancel_canon_fr 1 m n = *)
  (*              lcancel_canon_fr 1 m n' @ ap011 FinType_to_Z 1 (ap canon_FinType (ap S p))). *)
  (*   { intros. destruct p. rewrite concat_1p. rewrite concat_p1. *)
  (*     reflexivity. } *)
  (*   rewrite X. clear X. refine (_ @ concat_pp_p _ _ _). *)
  (*   rewrite (lcancel_canon_fr_compose _ _ a 1 ). *)
  (*   assert (canon_FinType_assoc 1 a 2 = idpath). *)
  (*   { refine (_ @ path_FinType_1 _). *)
  (*     apply (ap (path_FinType _ _)). *)
  (*     unfold canon_assoc. *)
  (*     apply emoveR_eV. apply emoveR_eV. *)
  (*     apply path_equiv. apply path_arrow. intro x. *)
  (*     repeat destruct x as [x | x]; try destruct x; reflexivity. } *)
  (*   rewrite X. clear X. *)
  (*   assert (canon_FinType_assoc 1 a 0 = idpath). *)
  (*   { refine (_ @ path_FinType_1 _). *)
  (*     apply (ap (path_FinType _ _)). *)
  (*     unfold canon_assoc. *)
  (*     apply emoveR_eV. apply emoveR_eV. *)
  (*     apply path_equiv. apply path_arrow. intro x. *)
  (*     repeat destruct x as [x | x]; try destruct x; reflexivity. } *)
  (*   rewrite X. clear X. rewrite concat_p1. *)
  (*   apply whiskerL. rewrite (ap_V S). *)
  (*   apply (ap (fun p => ap011 FinType_to_Z 1 (ap canon_FinType p^))). *)
  (*   apply hset_nat. *)
  (* Defined. *)
    
    
  (*   unfold path_base_2. unfold lcancel_canon_fr. *)
  (*   unfold lcancel_Z_fr. *)
  (*   rewrite <- path_Z_fr_pp. *)
  (*   rewrite <- path_Z_fr_pp. *)
  (*   rewrite <- path_Z_fr_pp. repeat rewrite concat_1p. *)
  (*   rewrite <- path_Z_fr_pp. rewrite <- path_Z_fr_pp. *)
  (*   rewrite path_Z_fr_compose. *)
  (*   rewrite (path_Z_fr_100 _ _ (finsum_id a 1)). *)
  (*   repeat rewrite concat_1p. repeat rewrite concat_p1. *)
  (*   rewrite concat_p_Vp. *)
  (*   rewrite concat_p_Vp. *)
  (*   rewrite path_FinType_V. rewrite path_FinType_V. *)
  (*   rewrite <- path_FinType_1. rewrite <- path_FinType_1.  rewrite <- path_FinType_1. *)
  (*   rewrite <- path_FinType_sum. rewrite <- path_FinType_sum. rewrite <- path_FinType_sum. *)
  (*   rewrite <- path_FinType_sum. *)
  (*   repeat rewrite <- path_FinType_compose. *)
  (*   apply (ap011 (path_Z_fr (sum_FinType (canon_FinType a) (canon_FinType 1)))); *)
  (*     apply (ap (path_FinType _ _)); apply path_equiv; apply path_arrow; intro x; *)
  (*       repeat destruct x as [x | x]; try destruct x; reflexivity. *)
  (*   (* would be more elegant to use lcancel_fr_compose, but. . . *) *)
  (* Defined. *)
    
    
    
  (*   repeat rewrite concat_pp_p. *)
      
    (* := lcancel_canon a _ _. *)

  (* Definition twist_first_two (a b c : nat) *)
  (*   : Fin (a +' (b +' c)) <~> Fin ((b +' a) +' c). *)
  (* Proof. *)
  (*   refine (_ oE (canon_assoc _ _ _ )^-1). *)
  (*   apply fin_equiv_sum. *)
  (*   apply equiv_functor_sum_r. *)
  (*   apply fin_equiv_sum. *)
  (*   apply equiv_sum_symm. *)
  (* Defined. *)

    
  (* Definition twist_last_two (a b c : nat) *)
  (*   : Fin ((a +' b) +' c) <~> Fin (a +' (c +' b)). *)
  (* Proof. *)
  (*   refine (_ oE canon_assoc _ _ _). *)
  (*   apply fin_equiv_sum. *)
  (*   apply equiv_functor_sum_l. *)
  (*   apply fin_equiv_sum. *)
  (*   apply equiv_sum_symm. *)
  (* Defined. *)
  

(*   Definition transpose_twist (a : nat) (i : Fin (a.+1))  *)
(*     : fin_transpose_last_with (a.+2) (inl (inl i)) = *)
(*       (twist_first_two 1 a 2) oE (block_sum *)
(*                                        (equiv_idmap (Fin 1)) *)
(*                                        (fin_transpose_last_with (a.+1) (inl i)) *)
                                           
(*                                            ) *)
(*                              oE (twist_first_two 1 a 2)^-1. *)
(*   Proof. *)
(*     apply emoveL_eV. *)
(*     unfold block_sum. unfold fin_equiv_sum. *)
(*     refine (_ @ ecompose_ee_e _ _ _). apply emoveL_eV. *)
(*     unfold twist_first_two. unfold canon_assoc. *)
(*     rewrite einv_eV. rewrite einv_eV. *)
(*     rewrite einv_ee. rewrite einv_ee. *)
(*     apply path_equiv. apply path_arrow. *)
(*     intro x. ev_equiv. rewrite eissect. rewrite eissect. *)
(*     destruct x as [[[] | []] | x]. *)
(*     - assert ((fin_equiv_sum (equiv_functor_sum_r (fin_equiv_sum (equiv_sum_symm (Fin 1) (Fin a)))) *)
(*        (equiv_finsum (1 +' a) 2 *)
(*           (equiv_functor_sum_r (equiv_finsum 1 a) *)
(*              ((equiv_sum_assoc' (Fin 1) (Fin a) (Fin 2))^-1 *)
(*                 ((equiv_functor_sum_l (equiv_finsum a 2))^-1 (inl (inr tt))))))) = *)
(*               (inl (inr tt))). *)
(*       { simpl. change (finl ?m ?n ?x) with (equiv_finsum m n (inl x)). *)
(*         change (finsum_inv ?m ?n ?x) with ((equiv_finsum m n)^-1 x). *)
(*         rewrite eissect. simpl. *)

(*         rewrite (eissect (equiv_finsum 1 a) (inr tt)). *)

(*       change ((?f +E ?g) (?x)) with (functor_sum f g x).       *)
(*       change (functor_sum (B' := ?B) ?f ?g (inl ?x)) with (inl B (f x)). *)
(*       change (equiv_idmap _ ?x) with x. *)
      
(*       unfold equiv_functor_sum_l. *)
(*       assert (forall (A B C : Type) (f : A <~> B), *)
(*                  ((equiv_idmap C) +E f)^-1 = ((equiv_idmap C) +E f^-1)). *)
(*       { intros. reflexivity. } *)
(*       (* then why doesn't this work. *) *)
(*       (* change (((equiv_idmap (Fin 1)) +E equiv_finsum a 2)^-1) with *) *)
(*       (* ((equiv_idmap (Fin 1)) +E (equiv_finsum a 2)^-1). *) *)
(*       rewrite X. *)
(*       change ((?f +E ?g) (?x)) with (functor_sum f g x).       *)
(*       change (functor_sum (B' := ?B) ?f ?g (inl ?x)) with (inl B (f x)). *)
      
(*       simpl. *)

(*       unfold equiv_inv. *)
(*       change (equiv_functor_sum_l (A := ?A) ?f)^-1 with (functor_sum (fun a : A => A) (f^-1)). *)
(*       change ((equiv_functor_sum_l (A := ?A) ?f)^-1 (inl ?x)) with (inl (f^-1 x)). *)
      
(*       change (equiv_finsum ?m ?n (inl ?x)) with (finl m n x). *)
(*       (* change (equiv_finsum 1 a.+2 (inl (inr tt))) with (finl 1 (a.+2) (inr tt)). *) *)
(*       (* change ((finl ?m ?n.+2) ?x) with (inl Unit (inl Unit (finl m n x))). *) *)
(*       (* change ((finl 1 a.+2) (inr tt)) with (inl Unit (inl Unit (finl 1 a (inr tt)))). *) *)
(*       change ((equiv_sum_assoc' ?A ?B ?C)^-1 (inl (inl ?x))) with (inl x). *)
      
      
      
(* simpl. *)
      

      
(* (*       change ((?f +E ?g) (inl (?x))) with (inl (f x)).
simpl. *) *)
    
(* (* repeat ; try destruct x; simpl. *) *)
    
(* simpl. *)

    
(*     destruct i as [i | []]; simpl. *)
  

  (* Definition path_base_diff (a : nat) *)
  (*   : FinType_to_Z (canon_FinType (a.+2)) (canon_FinType a) = *)
  (*     FinType_to_Z (canon_FinType ((a.+1).+2)) (canon_FinType a.+1). *)
  (* Proof. *)
  (*   lcancel_canon 1 _ _ @ _). *)
  (*   change (a.+3) with (2 + (1 + a))%nat. *)
  (*   change (canon_FinType (a.+1)) with (canon_FinType (0 + (1 + a))%nat). *)
  (*   change (canon_FinType (a + 1)) with (canon_FinType (0 + (a + 1))). *)
  (*   change (a.+2) with (2 + a)%nat. *)
  (*   apply (ap011 FinType_to_Z). *)
  (*   - apply (path_FinType). apply twist_last_two. *)
  (*   - apply (path_FinType). apply (twist_last_two 0 a 1). *)


  (*   (* ; apply (ap canon_FinType); simpl. *) *)
  (*   (* - apply (nat_plus_comm a.+2). *) *)
  (*   (* - apply (nat_plus_comm a). *) *)
  (*   (* apply (ap (fun x => FinType_to_Z (canon_FinType (2 + x)) (canon_FinType (x)))). *) *)
  (*   (* (* apply (ap011 FinType_to_Z); apply (ap canon_FinType); *) *) *)
  (*   (* apply nat_plus_comm. *) *)
  (* Defined. *)


  (* Definition path_base_succ (a : nat) *)
  (*   : path_base_2 (a.+1) = *)
  (*     path_base_2 a @ path_base_diff a. *)
  (* Proof. *)
  (*   unfold path_base_diff. *)
  (*   unfold path_base_2. unfold lcancel_canon. *)
    
  (*   assert (H : forall (m n : nat) (p : m = n), *)
  (*              lcancel_canon n 2 0 = *)
  (*              lcancel_canon m 2 0 @ *)
  (*                   ap (fun x => FinType_to_Z (canon_FinType (2 + x)) (canon_FinType (0 + x))) p). *)
  (*   { intros m n []. apply inverse. apply concat_p1. } *)
  (*   rewrite (H _ _ (nat_plus_comm a 1)). clear H. *)
  (*   refine (_ @ concat_pp_p _ _ _). *)
  (*   apply whiskerR. *)
  (*   refine (lcancel_canon_compose _ _ _ _ @ _). (* simpler proof to just prove this here? *) *)
  (*   apply moveR_pV. refine ((concat_p1 _)^ @ _). apply whiskerL. *)
  (*   change idpath with (ap011 FinType_to_Z *)
  (*                             (idpath (canon_FinType (2 + (a + 1)))) *)
  (*                             (idpath (canon_FinType ((a + 1))))). *)
  (*   rewrite <- path_FinType_1.  rewrite <- path_FinType_1.  *)
  (*   unfold canon_FinType_assoc. simpl. *)
  (*   apply (ap011 (fun f g => ap011 FinType_to_Z (path_FinType _ _ f) (path_FinType _ _ g))). *)
  (*   +  unfold canon_assoc. *)
  (*      apply emoveL_eV. apply emoveL_eV. *)
  (*      apply path_equiv. apply path_arrow. *)
  (*      intros [[x | x] | [[[]|x] | x]]; reflexivity. *)
  (*   + unfold canon_assoc. *)
  (*     apply emoveL_eV. apply emoveL_eV. *)
  (*     apply path_equiv. apply path_arrow. *)
  (*     intros [[x | x] | []]; reflexivity. *)
  (* Defined. *)

  (* Definition path_base_2_SS (a : nat) *)
  (*   : FinType_to_Z (canon_FinType 2) (canon_FinType 2) *)
  (*     = FinType_to_Z (canon_FinType a.+2) (canon_FinType a.+2) *)
  (*   := (lcancel_canon _ _ a). *)
  (* Proof. *)
  (*   (* induction a. *) *)
  (*   (* - exact idpath. *) *)
  (*   (* - refine (IHa @ _). *) *)
  (*   (*   refine (lcancel_Z (canon_FinType 1) _ _ @ _). *) *)
  (*   (*   apply (ap011 FinType_to_Z); *) *)
  (*   (*     refine (FinType_symmetric _ _ @ _); apply finsum_id.         *) *)
  (*   apply (path_Z (canon_FinType a)); apply finsum_id. *)
  (* Defined. *)
    
    (* refine (lcancel_Z (canon_FinType a) _ _ @ _). *)
    (* apply (ap011 FinType_to_Z); apply finsum_id. *)
  

  (* Definition path_succ ( a : nat ) *)
  (*   : FinType_to_Z (canon_FinType a) (canon_FinType a) = *)
  (*     FinType_to_Z (canon_FinType a.+1) (canon_FinType a.+1). *)
  (* Proof. *)
  (*   refine (lcancel_canon _ _ 1 @ _). *)
  (*   apply (ap011 FinType_to_Z); apply (ap canon_FinType); apply nat_plus_comm. *)
  (*   (* apply (ap011 (fun x y => FinType_to_Z (canon_FinType x) (canon_FinType y))); *) *)
  (*   (*   apply nat_plus_comm. *) *)
  (* Defined. *)
    (* refine (lcancel_Z (canon_FinType 1) _ _ @ _). *)
    (* apply (path_Z (canon_FinType 1)); *)
    (*   refine ((finsum_id 1 a) @ _); apply (ap canon_FinType); apply nat_plus_comm. *)
  (*     (* refine (FinType_symmetric _ _ @ _); apply finsum_id. *) *)
  (*   (* apply ccleq. *) *)
  (*   (* exists (canon_FinType 1). simpl. *) *)
  (*   (* apply path_prod; *) *)
  (* Defined. *)

(*   Definition path_Z_bc {S S' : FinType} {A1 B1 A2 B2 : FinType} *)
(*              (p : sum_FinType S A1 = A2) (q : sum_FinType S B1 = B2) *)
(*              (h : S' = S) *)
(*     : path_Z S p q = path_Z S' (ap011 sum_FinType h idpath @ p) *)
(*                                (ap011 sum_FinType h idpath @ q). *)
(*   Proof. *)
(*     destruct h. *)
(*     rewrite concat_1p. rewrite concat_1p. *)
(*     reflexivity. *)
(*   Defined. *)

(*   Definition path_base_2_succ (a : nat) *)
(*     : path_base_2_SS a.+1 = *)
(*       path_base_2_SS a @ (path_succ _). *)
(*   Proof.     *)
(*     unfold path_base_2_SS. unfold path_succ. *)
(*     unfold lcancel_canon. (* refine (_ @ concat_pp_p _ _ _). *) *)
(*     (* refine (_ @ whiskerR (path_Z_compose _ _ _ _ _ _)^ _). *) *)
(*     refine (_ @ (path_Z_compose _ _ _ _ _ _)^). *)
    
(*     refine (path_Z_bc _ _ (* (FinType_symmetric _ _ @ finsum_id a 1 ) @ _). *) *)
(*                       (* (finsum_id 1 a @ (ap canon_FinType (nat_plus_comm _ _))) @ _). *) *)
(*                       ((ap canon_FinType (nat_plus_comm a 1))) @ _). *)
    
(*     refine (_ @ (path_Z_compose _ _ _ _ _ _)^). *)
(*     unfold path_Z. *)
(*     apply (ap (ccleq group_completion_FinType)). *)
(*     apply (ap (fun x => (_ ; x))). *)
(*     simpl. unfold functor_prod. simpl. *)
(*     assert (forall (A B : Type) (a a' : A) (b b' : B) (p : a = a') (q : b = b'), *)
(*         path_prod (a,b) (a', b') p q = ap011 pair p q). *)
(*     { intros. destruct p. destruct q. reflexivity. } *)
(*     rewrite X. rewrite X. clear X. *)
    
(*     unfold FinType_symmetric. unfold finsum_id. *)
(*     repeat rewrite <- path_FinType_compose. *)
(*     rewrite <- path_FinType_1. rewrite <- path_FinType_1.  *)
(*     rewrite <- path_FinType_sum. rewrite <- path_FinType_sum.  *)
(*     rewrite <- path_FinType_compose. *)
(*     rewrite <- path_FinType_compose. *)
(*     rewrite <- path_FinType_compose.     *)
(*     apply (ap011 (ap011 pair)); apply (ap (path_FinType _ _)); *)
(*       apply path_equiv; apply path_arrow. *)
(*     - intro x. *)
(*     intros [[[[] | []] | x] | x]; try reflexivity; simpl. *)
    
(*     apply (ap (path_prod (sum_FinType (sum_FinType (canon_FinType 1) (canon_FinType a)) (canon_FinType 2), *)
(*                           sum_FinType (sum_FinType (canon_FinType 1) (canon_FinType a)) (canon_FinType 2)) *)
(*                          (canon_FinType a.+3, canon_FinType a.+3))). *)
    
(*     apply (ap (path_Z (sum_FinType (canon_FinType 1) (canon_FinType a)))). *)

    
(*     transitivity (path_Z (sum_FinType (canon_FinType a) (canon_FinType 1)) _)     *)
    
    

(* rewrite <- path_FinType_compose. *)
    
(*     unfold path_Z. *)
    
(*     refine (_ @ cconcat _ _ _). simpl. *)
(*     apply (ap (ccleq _)). *)
(*     apply inverse. *)
(*     srapply @path_sigma. *)
(*     { simpl. apply (FinType_symmetric _ _ @ finsum_id a 1). } *)
(*     simpl. *)
                         
(*     apply (path_sigma _ _ _ (finsum_id _ _)). *)

    
(*     apply inverse. *)
    
(*     refine ( *)
      
(*       lcancel_Z (canon_FinType a) _ _ @ (ap011 FinType_to_Z (finsum_id _ _) (finsum_id _ _)). *)
(*   Proof. *)
(*     induction a. *)
(*     { simpl. *)
      
(*       unfold lcancel_Z. *)
(*       rewrite <- (ce group_completion_FinType). *)
(*       refine ((concat_p1 _)^ @ _). *)
(*       apply concat2. *)
(*       unfold finsum_id. simpl. *)
      

(*   Definition path_base_2 (a : nat) *)
(*     : FinType_to_Z (canon_FinType 2) (canon_FinType 2) = FinType_to_Z (canon_FinType a) (canon_FinType a). *)
(*   Proof. *)
(*     destruct a as [ | a]. *)
(*     { apply inverse. *)
(*       refine (lcancel_Z (canon_FinType 2) _ _ @ _). *)
(*       apply (ap011 (FinType_to_Z)); apply finsum_id. } *)
(*     destruct a as [ | a]. *)
(*     { apply inverse. *)
(*       refine (lcancel_Z (canon_FinType 1) _ _ @ _). *)
(*       apply (ap011 (FinType_to_Z)); apply finsum_id. } *)
(*     apply path_base_2_SS. *)
(*   Defined. *)
  
    (* := (path_base_0 _)^ @ (path_base_0 _). *)    

    Definition twist2_Z : FinType_to_Z (canon_FinType 2) (canon_FinType 2) =
                          FinType_to_Z (canon_FinType 2) (canon_FinType 2).
  Proof.
    apply (ap011 FinType_to_Z).
    - exact (path_FinType (canon_FinType 2) (canon_FinType 2) twist2).
    - exact idpath.
  Defined.

  (* Definition transpose_first_two_is_twist_Z (a : nat) *)
  (*   : ap011 FinType_to_Z (path_FinType (canon_FinType (2 +' a)) (canon_FinType (2 +' a)) *)
  (*                                    (block_sum twist2 equiv_idmap)) *)
  (*                       idpath = *)
  (*         ((path_base_2 _)^ @ twist2_Z) @ path_base_2 _.       *)
  (* Proof. *)
  (*   refine (_ @ lcancel_canon_path_fr a 2 0 equiv_idmap twist2 equiv_idmap @ _). *)
    
  (*   rewrite <- path_FinType_1. *)
  (*   rewrite (ap (path_FinType _ _) (block_sum_is_id a 0)). *)
  (*   lcancel_canon_path_fr *)
  (*   unfold twist2_Z. *)
  (*   rewrite path_FinType_blocksum. *)
  (*   unfold path_base_2. *)

    
      
      
            

  Definition transpose_Z (a : nat) (i : Fin (a.+1))
    : FinType_to_Z (canon_FinType (a.+1)) (canon_FinType (a.+1)) =
      FinType_to_Z (canon_FinType (a.+1)) (canon_FinType (a.+1)).
    apply (ap011 FinType_to_Z).
    - apply path_FinType.
      apply (fin_transpose_last_with (a) i).
    - exact idpath.
  Defined.

    

  (* Definition tranpose_Z_is_transpose_last_two (a : nat) (i : Fin a.+1) *)
  (*   : transpose_Z a i = transpose_Z a (inr tt). *)
  (* Proof. *)
  (*   induction a. *)
  (*   - destruct i as [[] | []]. reflexivity. *)
  (*   - simpl. unfold transpose_Z in *. simpl.  *)

  Definition transpose_last_two_is_twist_Z (a : nat)
        : ap011
            FinType_to_Z
            (path_FinType (canon_FinType a.+2) (canon_FinType a.+2) (fin_transpose_last_two a)) 1 =
          (* transpose_Z a (inr tt) = *)
          ((path_base_2 _) @ twist2_Z) @ (path_base_2 _)^.
  Proof.
    rewrite path_base_2_is_lcancel.
    rewrite inv_V.
    refine (_ @ lcancel_canon_path a 2 2 equiv_idmap twist2 equiv_idmap @ _).
    - rewrite transpose_last_two_is_block_sum.
      apply (ap (fun x =>
                ap011 FinType_to_Z
                      (path_FinType (canon_FinType a.+2) (canon_FinType a.+2) (block_sum 1 twist2)) x)).
      rewrite <- block_sum_is_id.
      apply inverse. apply path_FinType_1.
    - rewrite path_FinType_1. reflexivity.
  Defined.


  (* Definition move_fst_to_mid (a : nat) : *)
  (*   sum_FinType (canon_FinType 1) (canon_FinType (a.+1)) = canon_FinType (a.+2). *)
  (* Proof. *)
  (*   apply path_FinType. *)
  (*   refine (fin_transpose_last_two a oE _). *)
  (*   refine (_ oE equiv_sum_symm _ _). *)
  (*   apply equiv_finsum. *)
  (*   (* refine (_ @ path_FinType (canon_FinType a.+2) (canon_FinType a.+2) (fin_transpose_last_two a)). *) *)
  (*   (* refine (FinType_symmetric _ _ @ _). *) *)
  (*   (* apply finsum_id. *) *)
  (* Defined. *)

  Lemma path_succ_cancel_path_l (a b : nat) (alpha : canon_FinType a <~> canon_FinType a)
    : (path_succ a b @
        ap011 FinType_to_Z (path_FinType (canon_FinType a.+1) (canon_FinType a.+1) (alpha +E 1)) idpath)
        @ (path_succ a b)^ =
      ap011 FinType_to_Z (path_FinType (canon_FinType a) (canon_FinType a) alpha) idpath.
  Proof.
    refine (_ @ path_succ_cancel_path alpha equiv_idmap @ _).
    - apply whiskerR. apply whiskerL.
      refine (ap011 (ap011 FinType_to_Z) idpath _).
      apply inverse. refine (_ @ path_FinType_1 _).
      apply (ap (path_FinType _ _)).
      apply path_equiv. apply path_arrow. intros [x | x]; reflexivity.
    - rewrite path_FinType_1. reflexivity.
  Defined.  
    
  (* all nontrivial transpositions are above the transposition in canon 2 *)
  Definition transpose_Z_is_twist2 (a : nat) (i : Fin a)
    : (path_base_2 _)^ @ (transpose_Z a (inl i) @ path_base_2 _) = twist2_Z.
  Proof.    
    induction a.
    { destruct i. }
    destruct i as [i | []].
    - refine (_ @ IHa i). clear IHa.
      assert (H : forall (A B : FinType) (p : B = A),
                 path_base_2 A =
                 (ap011 FinType_to_Z p p)^ @ path_base_2 B).
      { intros A B []. rewrite concat_1p. reflexivity. }
      rewrite (H _ _ (path_FinType (canon_FinType a.+2) (canon_FinType a.+2)
                                  (fin_transpose_last_two a))).
      rewrite (path_base_2_succ (a.+1)).
      refine (concat_p_pp _ _ _ @ _). refine (concat_p_pp _ _ _ @ _). refine (concat_p_pp _ _ _ @ _).
      refine (_ @ concat_pp_p _ _ _). apply whiskerR.
      rewrite inv_Vp. rewrite inv_Vp.
      refine (concat_pp_p _ _ _ @ _). refine (concat_pp_p _ _ _ @ _). refine (concat_pp_p _ _ _ @ _).
      refine (concat_pp_p _ _ _ @ _). apply whiskerL.
      refine (_ @ path_succ_cancel_path_l _ _ _).
      refine (_ @ concat_p_pp _ _ _). apply whiskerL.
      refine (concat_p_pp _ _ _ @ _). refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      rewrite ap011_VV. 
      rewrite <- ap011_pp_pp. 
      rewrite <- ap011_pp_pp. rewrite concat_p1.
      rewrite concat_pV.
      rewrite path_FinType_V.
      rewrite <- path_FinType_compose.
      rewrite <- path_FinType_compose.
      refine (ap011 (ap011 FinType_to_Z) _ idpath).
      apply (ap (path_FinType _ _)).
      apply emoveR_Ve.
      apply path_equiv. apply path_arrow.
      intro x. repeat destruct x as [x | x]; reflexivity.
    - apply moveR_Vp. apply moveR_pM.
      apply transpose_last_two_is_twist_Z.
  Defined.

  (* Then we have control over all transpositions *)
  Lemma sgn_transpose_Z (a : nat) (i : Fin a.+1)
    : (path_base_2 _)^ @ (transpose_Z a i @ path_base_2 _) =
      ap011 FinType_to_Z (path_FinType (canon_FinType 2) (canon_FinType 2) (sgn_transpose i)) idpath.
  Proof.
    destruct i as [i | []].
    { apply transpose_Z_is_twist2. }
    simpl. apply moveR_Vp.
    rewrite path_FinType_1.
    refine (_ @ (concat_p1 _)^).
    apply moveR_pM. refine (_ @ (concat_pV _)^).
    unfold transpose_Z.
    
    assert (fin_transpose_last_with a (inr tt) = equiv_idmap).
    { apply path_equiv. apply path_arrow. intro x.
      apply (fin_transpose_last_with_last_other a x). }
    rewrite X. rewrite path_FinType_1. reflexivity.
  Defined.

  (*     rewrite (H _ _ (move_fst_to_mid a)). clear H. *)
  (*     rewrite inv_Vp.        *)
  (*     rewrite <- (path_base_2_compose (canon_FinType 1) (canon_FinType a.+1)). *)
  (*     rewrite inv_pp. *)
  (*     refine (_ @ concat_pp_p _ _ _). refine (_ @ concat_pp_p _ _ _). *)
  (*     refine (concat_p_pp _ _ _ @ _). refine (concat_p_pp _ _ _ @ _). apply whiskerR. *)
  (*     refine (_ @ concat_p_pp _ _ _). refine (_ @ concat_p_pp _ _ _). *)
  (*     refine (concat_pp_p _ _ _ @ _). refine (concat_pp_p _ _ _ @ _). apply whiskerL. *)
  (*     apply moveL_Vp. apply moveL_pM. unfold transpose_Z at 2. *)
  (*     rewrite <- (path_FinType_1 (canon_FinType a.+1)). *)
  (*     refine (_ @ (lcancel_Z_path (equiv_idmap (canon_FinType 1)) _ _)^). *)
  (*     apply whiskerR. apply whiskerL. *)
  (*     apply moveR_Mp. apply moveR_pV. *)
  (*     rewrite ap011_VV. *)
  (*     rewrite <- ap011_pp_pp. rewrite <- ap011_pp_pp. *)
  (*     assert (path_FinType (sum_FinType (canon_FinType 1) (canon_FinType a.+1)) *)
  (*                         (sum_FinType (canon_FinType 1) (canon_FinType a.+1)) (1 +E 1) = idpath). *)
  (*     { refine (_ @ path_FinType_1 _). *)
  (*       apply (ap (path_FinType _ _)). *)
  (*       apply path_equiv. apply path_arrow. intros [x | x]; reflexivity. } *)
  (*     rewrite X. clear X. *)
  (*      rewrite concat_p1. rewrite concat_Vp.       *)
  (*     rewrite path_FinType_V. *)
  (*     rewrite <- path_FinType_compose. rewrite <- path_FinType_compose. *)
  (*     refine (ap011 (ap011 FinType_to_Z) _ idpath). apply (ap (path_FinType _ _ )). *)
  (*       apply path_equiv; apply path_arrow; intro x; *)
  (*         repeat destruct x as [x | x]; try destruct x; try reflexivity. *)
  (*   - apply moveR_Vp. apply moveR_pM. *)
  (*     apply transpose_last_two_is_twist_Z. *)
  (* Defined. *)


  (* Definition path_succ (a b : nat) : *)
  (*   FinType_to_Z (canon_FinType a.+1) (canon_FinType b.+1) = *)
  (*   FinType_to_Z (canon_FinType a) (canon_FinType b). *)

  Definition path_is_sgn (a : nat) (alpha : canon_FinType a <~> canon_FinType a)
    : (path_base_2 _)^ @ ap011 FinType_to_Z (path_FinType _ _ alpha) idpath @ path_base_2 _
      = ap011 FinType_to_Z (path_FinType (canon_FinType 2) (canon_FinType 2) (sign a alpha)) idpath.
  Proof.
    induction a.
    (* base case is simple *)
    - simpl.
      assert (alpha = equiv_idmap _).
      { apply path_equiv. apply path_arrow. intros []. }
      rewrite X. clear X. rewrite path_FinType_1.
      rewrite concat_p1. rewrite concat_Vp.
      rewrite path_FinType_1. reflexivity.
    (* for induction step, we factorize alpha into a transposition and something that *)
    (* fixes the endpoint. The transposition is taken care of by sgn_transpose_Z, *)
    (* while the part fixing the endpoint follows from the induction hypothesis *)
    - simpl.
      rewrite (path_FinType_compose (B := (canon_FinType 2))).
      rewrite (ap011_pp_pp FinType_to_Z _ _ idpath idpath).
      rewrite <- sgn_transpose_Z.
      rewrite <- (IHa (transpose_and_restrict alpha)).
      rewrite (path_base_2_succ).
      (* cancelling out stuff: *)
      rewrite <- (path_succ_cancel_path_l _ _ (transpose_and_restrict alpha)).
      rewrite inv_Vp.
      refine (_ @ concat_pp_p _ _ _). refine (_ @ concat_pp_p _ _ _). refine (_ @ concat_pp_p _ _ _).
      refine (concat_p_pp _ _ _ @ _). apply whiskerR. apply whiskerR.
      refine (_ @ concat_p_pp _ _ _). refine (_ @ concat_p_pp _ _ _). refine (_ @ concat_p_pp _ _ _).
      refine (concat_pp_p _ _ _ @ _). apply whiskerL.
      refine (_ @ concat_p_pp _ _ _). refine (_ @ concat_p_pp _ _ _). apply whiskerL.
      rewrite (concat_pp_p (path_base_2 (canon_FinType a))^).
      rewrite concat_p_Vp. rewrite concat_V_pp.
      
      refine (_ @ ap011_pp_pp FinType_to_Z _ _ _ _ ).
      rewrite <- path_FinType_compose. simpl.
      refine (ap011 (ap011 FinType_to_Z) _ idpath).
      apply (ap (path_FinType _ _)).
      apply (factorize_permutation alpha).
  Defined.

  (* The inverse map in the equivalence: *)
  Definition fin2_to_grpcompl : Finite_Types 2 -> Z.
  Proof.
    intro x.
    refine (FinType_to_Z _ (canon_FinType 2)).
    apply (Build_FinType 2 x).
  Defined.

    (* If two maps agree on the loop space, they are equal *)
  (* move? Make variant with f g : pMap X Y, and phomotopy?*)
  Definition pt_deloop_eq (X: Conn_pType) (Y : pType) {istrunc_y : IsTrunc 1 Y}
             (f g : pMap X Y) 
    : (loops_functor f) == (loops_functor g) ->
      pHomotopy f g.
  Proof.
    intro H. srapply @Build_pHomotopy.
    - 
      srapply (deloop_ind_set X); simpl.
      + exact (point_eq f @ (point_eq g)^).
      +  intro. refine (transport_paths_FlFr _ _ @ _).
         apply moveL_pV. refine (concat_pp_p _ _ _ @ _).
         refine (concat_pp_p _ _ _ @ _). apply moveR_Vp.
         refine (concat_pp_p _ _ _ @ _). apply moveR_Mp.
         apply inverse. apply H.
         (* apply (pointed_htpy H). *)
    - simpl. apply moveR_pM.
      refine (deloop_ind_beta_pt X (fun x : X => f x = g x) (point_eq f @ (point_eq g)^) _ _ ).
  Defined.


  (* move, and perhaps generalize *)
  (* Definition deloop_fin_compose {l m n : nat} *)
  (*            (f : Homomorphism (SymGrp l) (SymGrp m)) *)
  (*            (g : Homomorphism (SymGrp m) (SymGrp n)) *)
  (*   : pHomotopy (deloop_fin _ _ (g oH f)) (deloop_fin _ _ g o* deloop_fin _ _ f). *)
  (* Proof. *)
  (*   apply (pt_deloop_eq (pFin l) (pFin n)). *)
    
  (*   transitivity ( *)
  (*   loops_functor_compose *)
    
    
    
    

  (*   srapply (deloop_ind_set (pFin l)). *)
  (*   - simpl. *)
  (*     refine (deloop_fin_canon _ _ _ @ _). *)
  (*     apply inverse. *)
  (*     refine (ap (deloop_fin m n g) (deloop_fin_canon _ _ f) @ _). *)
  (*     apply deloop_fin_canon. *)
  (*   - intro. *)
  (*     refine (transport_paths_FlFr _ _ @ _). *)
  (*     apply moveL_pV. *)
  (*     refine (concat_pp_p _ _ _ @ _). refine (concat_pp_p _ _ _ @ _). *)
  (*     apply moveR_Vp. refine (concat_pp_p _ _ _ @ _). *)
  (*     apply moveR_Mp. *)
  (*     refine (_ @ concat_pp_p _ _ _). *)
  (*     refine (_ @ (deloop_fin_loop _ _ (g oH f) ω)^). simpl. *)
  (*     rewrite inv_pp. *)
  (*     rewrite (ap_compose (deloop_fin l m f) (deloop_fin m n g)). *)
  (*     rewrite (concat_pp_p (deloop_fin_canon m n g)^). *)
  (*     rewrite (concat_p_pp (ap (deloop_fin m n g) (ap (deloop_fin l m f) ω))). *)
  (*     rewrite <- ap_pp. rewrite <- ap_V. *)
  (*     rewrite (concat_p_pp (ap (deloop_fin m n g) (deloop_fin_canon l m f)^)). *)
  (*     rewrite <- ap_pp. rewrite (concat_p_pp (deloop_fin_canon l m f)^). *)
  (*     rewrite (deloop_fin_loop _ _ f). simpl. *)
  (*     refine (concat_p_pp _ _ _ @ _). *)
  (*     refine (deloop_fin_loop _ _ g _ @ _). simpl. *)
      
  (*     generalize (f (inv_path_finite_types l (canon l) (canon l) ω)). clear ω. *)
  (*     intro ω. *)
  (*     apply (ap (path_finite_types n (canon n) (canon n))). apply (ap g). *)
  (*     change (inv_path_finite_types m (canon m) (canon m) ?x) with *)
  (*     ((equiv_path_finite_types m (canon m) (canon m))^-1 x). *)
  (*     apply (eissect (equiv_path_finite_types m (canon m) (canon m)) (ω)). *)
  (* Defined. *)

  Definition blocksum_hom (a b : nat) 
    : Homomorphism (SymGrp a) (SymGrp (a +' b)).
  Proof.
    srapply @Build_GrpHom.
    - intro alpha. exact (block_sum alpha equiv_idmap).
    - intros alpha1 alpha2. simpl.
      refine (_ @ block_sum_compose _ _ _ _). rewrite ecompose_e1.
      reflexivity.
  Defined.

  Definition pmap_sum_canon (a b : nat)
    : pMap (pFin a) (pFin (a +' b)).
  Proof.
    srapply @Build_pMap.
    - simpl. intro x.
      exact (sum_finite_types x (canon b)).
    - simpl.
      apply path_finite_types. apply (equiv_finsum).
  Defined.

  Definition pmap_Bsign (a : nat)
    : pMap (pFin a) (pFin 2).
  Proof.
    srapply @Build_pMap.
    - exact (Bsign a).
    - unfold Bsign.
      apply deloop_fin_canon.
  Defined.

  (* Definition deloop_blocksum_is_sum_finite_types (a b : nat) *)
  (*   : deloop_fin a _ (blocksum_hom a b) == *)
  (*     fun x => sum_finite_types x (canon b). *)
  (* Proof. *)
  (*   intro x. revert x. *)
  (*   srapply (deloop_ind (pFin a)). *)
  (*   - simpl. unfold point. *)
  (*     refine (deloop_fin_canon _ _ _ @ _). *)
  (*     apply inverse. apply (path_finite_types (a +' b)).  apply (equiv_finsum a b). *)
  (*   - intro. *)
  (*     refine (transport_paths_FlFr _ _ @ _). *)

      

  Definition isretr_toZ :
      grpcompl_to_fin2 o fin2_to_grpcompl == idmap.
  Proof.
    unfold fin2_to_grpcompl.
    change (grpcompl_to_fin2 (FinType_to_Z ?A ?B)) with (Bsign_uncurry (sum_FinType A B)).
    unfold Bsign_uncurry.
    cut (pHomotopy (pmap_compose (Bsign 4) (pmap_sum_canon 2 2)) pmap_idmap).
    { intro H. apply (pointed_htpy H). }
    apply (pt_deloop_eq (pFin 2) (pFin 2)).
    transitivity (pmap_compose (loops_functor (Bsign 4))  (loops_functor (pmap_sum_canon 2 2))).
    { apply loops_functor_compose. }
    (* assert (loops_functor (Bsign 4) == equiv_functor_hom_fin 4 2 (sgnhom 4)). *)
    (* { apply (functor_deloop_loop (pFin 4) (pFin 2)). } *)
    unfold Bsign. intro alpha.
    refine (functor_deloop_loop (pFin 4) (pFin 2) (equiv_functor_hom_fin 4 2 (sgnhom 4)) _ @ _).
    assert (loops_functor (pmap_sum_canon 2 2) alpha =
            (equiv_functor_hom_fin 2 4 (blocksum_hom 2 2)) alpha).
    { unfold equiv_functor_hom_fin. unfold equiv_functor_hom'. unfold equiv_functor_hom.
      simpl.
      refine (_ @
                ap (path_finite_types 4 (canon 4) (canon 4)) (blocksum_is_ap011 2 2 alpha idpath)^).
      refine (_ @ (eisretr (equiv_path_finite_types 4 (canon 4) (canon 4))
                (sum_finite_types_canon^ @ (ap011 sum_finite_types alpha (idpath (canon 2)) @ sum_finite_types_canon)))^).
      apply whiskerL. apply whiskerR.
      cut (forall (X : pFin 2) (p : canon 2 = X),
              ap (fun x : Finite_Types 2 => sum_finite_types x (canon 2)) p =
              ap011 sum_finite_types p idpath).
      { intro H. apply H. }
      intros X []. reflexivity. } rewrite X. clear X.
    apply inverse.
    refine ((pointed_htpy (loops_functor_idmap (pFin 2)) _ @ _)).
    change (pmap_idmap alpha) with alpha.
    assert (equiv_functor_hom_fin_compose :
              forall (a b c : nat)
                     (f : Homomorphism (SymGrp a) (SymGrp b))
                     (g : Homomorphism (SymGrp b) (SymGrp c)),
                equiv_functor_hom_fin _ _ (g oH f) ==
                (equiv_functor_hom_fin _ _ g) oH (equiv_functor_hom_fin _ _ f)).
    { intros.
      intro sigma. simpl.
      apply (ap (path_finite_types _ _ _)). apply (ap g).
      generalize (f (inv_path_finite_types a (canon a) (canon a) sigma)). clear sigma. intro sigma.
      apply inverse.
      refine (eissect (equiv_path_finite_types b (canon b) (canon b)) sigma). }
    refine (_ @ equiv_functor_hom_fin_compose _ _ _ (blocksum_hom 2 2) (sgnhom 4) alpha).
    transitivity (equiv_functor_hom_fin 2 2 idhom alpha).
    { unfold equiv_functor_hom_fin. unfold equiv_functor_hom'.
      simpl. apply inverse.
      refine (eisretr (equiv_path_finite_types 2 (canon 2) (canon 2)) alpha). }
    apply (ap (fun x => equiv_functor_hom_fin 2 2 x alpha)).
    apply inverse. apply path_hom.  apply path_arrow. intro x.
    unfold sgnhom. unfold blocksum_hom.
    change ((?f oH ?g) x) with (f (g x)).
    change (Build_GrpHom ?f _ ?x) with (f x).
    change (Build_GrpHom ?f _ ?x) with (f x).
    hnf.
    refine (@sgn_block_sum 2 2 x (equiv_idmap) @ _).
    apply path_equiv. apply path_arrow. intro y. ev_equiv.
    rewrite sgn2_is_id. rewrite sgn2_is_id.  reflexivity. 
  Defined.


  


    


    


  (* Definition inj_pred_pos_to_nat (a b : nat) (p : pred_pos_to_nat a = pred_pos_to_nat b) *)
  (*   : a = b. *)


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

    
  

  (* Definition inj_nat_to_int (a b : nat) *)
  (*   : nat_to_int a = nat_to_int b -> a = b. *)
  (* Proof. *)
  (*   intro p. *)
  (*   Check (classes_eq_related p). *)
  (*   induction a. *)
  (*   induction a, b. *)
  (*   - reflexivity. *)
  (*   - simpl.  *)
    
   
      
  Definition card_Z : Z -> Integers.
  Proof.
    srefine (grp_compl_FinType_rec (BuildTruncType 1 Integers) _ _ _).
    - intros [a A] [b B]. exact (natnat_to_integer a b).
    - intros [s S] [a A] [b B]. simpl.
      srefine (lcancel_to_groupcompletion _ _ _ _ @ _).
      { exact s. }
      simpl. apply (ap011 natnat_to_integer);
               apply nat_plus_comm.
    - intros. apply quotients.set_quotient_path2.
  Defined.

  Definition grp_compl_FinType_rec_set (P : Type) {isset_P : IsHSet P}
             (f : nat -> nat -> P)
             (act_add : forall s a b : nat, f a b = f (s +' a) (s+' b))
    : Z -> P.
  Proof.
    srapply @grp_compl_FinType_ind_set.
    - exact f.
    - simpl. intros.
      apply path_to_double_pathover.
      refine
        (transport_const (path_prod (canon a, canon b) (canon a, canon b) alpha betta) (f a b)).
      (* unfold uncurry.  *)
      (* apply (ap (transport *)
      (*              (fun _ : Finite_Types a * Finite_Types b => P) *)
      (*              (path_prod (canon a, canon b) (canon a, canon b) alpha betta))). *)
    - intros. apply path_to_path_over.
      refine (transport_const (lcancel_canon s m n) (f m n) @ act_add s m n).
  Defined.

  Definition grp_compl_FinType_ind_set_beta_pt (P : Z -> Type) {isprop_P : forall z : Z, IsHSet (P z)}
             (f : forall (m n : nat),
                 P (Fin_to_Z (canon m) (canon n)))
             (base_change
              : forall (a b : nat) (alpha : canon a = canon a) (betta : canon b = canon b),
                 double_pathover (fun (x : Finite_Types a) (y : Finite_Types b) => P (Fin_to_Z x y))

                                 alpha betta (f a b) (f a b))
             (act_add :
                (forall (m n : nat) (s : nat),
                    path_over P (lcancel_canon s m n) (f m n) (f (m+s)%nat (n+s)%nat)))
             (m n : nat)
    : grp_compl_FinType_ind_set P f base_change act_add
                               (FinType_to_Z (canon_FinType m) (canon_FinType n)) = f m n.
  Proof.
    simpl.
    refine (deloop_double_ind_set_beta_pt' (pFin m) (pFin n) _ _ _ ).
  Defined.             

  (* removable? *)
  Definition in_component_0 : Z -> hProp.
  Proof.
    srefine (@grp_compl_FinType_rec_set hProp _ _ _).
    - intros a b.
      exact (BuildTruncType -1 (a = b)).
    - intros. simpl.
      apply path_trunctype. simpl.
      apply equiv_iff_hprop.
      + apply (ap (fun x => s +' x)).
      + intro p.
        apply (nat_plus_cancelL s).
        refine (_ @ p @ _);
          apply nat_plus_comm.
  Defined.

  Definition in_component_0_canon (a b : nat)
    : in_component_0 (FinType_to_Z (canon_FinType a) (canon_FinType b)) <~> a = b.
  Proof.
    change (?X <~> a = b) with (X <~> BuildhProp (a = b)).
    apply ((path_trunctype (n := -1))^-1). 
    refine (grp_compl_FinType_ind_set_beta_pt _ _ _ _ a b).
  Defined.
    

  Definition Z0_card (z : Z)
    : in_component_0 z <~> (card_Z z = nat_to_integer 0).
  Proof.
    revert z. srapply @grp_compl_FinType_ind_hprop.
    intros. hnf.
    refine (_ oE (in_component_0_canon m n)).
    apply equiv_iff_hprop.
    + simpl. intros [].
      apply inverse.
      refine (rcancel_integers m 0 0 @ _).
      apply (ap011 natnat_to_integer);
        apply (nat_plus_n_O m)^.
    + apply diff_zero.
  Defined.
    

  (* Definition Z0 := {z : Z & merely (z = FinType_to_Z (canon_FinType 2) (canon_FinType 2))}. *)
  Definition Z0 := {z : Z & card_Z z = nat_to_integer 0}.
  (* Definition Z0 := {z : Z & in_component_0 z}. *)
  
  Definition cancel_zero (a : nat) : natnat_to_integer a a = nat_to_integer 0.
  Proof.
    apply inverse.
    refine (rcancel_integers a _ _ @ _). simpl.
    apply (ap011 natnat_to_integer);
      apply inverse; apply (nat_plus_n_O a).
  Defined.

  Definition FinFin_to_Z0 {a : nat} : Finite_Types a -> Finite_Types a -> Z0.
  Proof.
    intros x y.
    exists (Fin_to_Z x y).    
    (* refine (equiv_inverse (Z0_card (Fin_to_Z x y)) _). simpl. *)
    apply cancel_zero.
  Defined.             

  Definition canon_Z0 (a : nat) : Z0
    := FinFin_to_Z0 (canon a) (canon a).

  Definition lcancel_canon_Z0 (s a : nat)
    : canon_Z0 a = canon_Z0 (s +' a).
  Proof.
    apply path_sigma_hprop. simpl.
    apply (lcancel_canon s a a).
  Defined.

  (* move *)
  Definition equiv_diff_zero (a b : nat) : (natnat_to_integer a b = nat_to_integer 0) <~> a = b.
  Proof.
    apply equiv_iff_hprop.
    - apply diff_zero.
    - intros [].
      apply cancel_zero.
  Defined.

  Definition Z0_forall_canon (P : Z0 -> Type) (a : nat)
    : P (canon_Z0 a) ->
      (forall (b : nat)
              (p : card_Z (FinType_to_Z (canon_FinType a) (canon_FinType b)) = nat_to_integer 0),
          P (Fin_to_Z (canon a) (canon b); p)).
  Proof.
    intros f b p.
    refine (transport P _ (f)).
    apply path_sigma_hprop. simpl.
    apply (ap (fun x => Fin_to_Z (canon a) (canon x))). apply diff_zero. exact p.
  Defined.

  (* Definition Z0_forall_canon_retr (P : Z0 -> Type) (a b : nat)  *)
  (*            (p : card_Z (FinType_to_Z (canon_FinType a) (canon_FinType b)) = nat_to_integer 0) *)
  (*            (f : forall a : nat, P (canon_Z0 a)) *)
  (*   : Z0_forall_canon P a (f a) b p = f a. *)

  Instance isequiv_Z0_forall_canon (P : Z0 -> Type) (a : nat)
    : IsEquiv (Z0_forall_canon P a).
  Proof.
    srapply @isequiv_adjointify.
    - intro f. apply f.
    - intro f.
      apply path_forall. intro b. apply path_forall. intro p.
      unfold Z0_forall_canon.
      destruct (diff_zero a b p). simpl.
      refine (_ @ transport_1 P _).
      assert (h : cancel_zero a = p).
      { apply (istrunc_trunctype_type (n := 0)). }
      destruct h. simpl. 
      rewrite (path_sigma_hprop_1 (FinFin_to_Z0 (canon a) (canon a))).
      reflexivity.
    - intro f. 
      refine (_ @ transport_1 P _).
      apply (ap (fun x => transport P x (f))).
      assert (h : diff_zero a a (cancel_zero (card_FinType (fin_to_FinType (canon a)))) = idpath).
      { apply hset_nat. }
      rewrite h. simpl.
      apply path_sigma_hprop_1.
  Defined.

  (* move *)
  Definition pathover_sigma_hprop {A : Type} {B : A -> Type} {isprop_B : (forall a : A, IsHProp (B a))}
             (C : forall a : A, B a -> Type)
             {a1 a2 : A} (p : a1 = a2)
             (c1 : forall b : B a1, C a1 b) (c2 : forall b : B a2, C a2 b)
    : 
      (forall (b1 : B a1)       (*(b2 : B a2) *),  (* transport B p b1*)
          path_over (fun ab : {a : A & B a} => C (pr1 ab) (pr2 ab))
                    (path_sigma_hprop (a1; b1) (a2; transport B p b1) p)
                    (c1 b1) (c2 (transport B p b1))) ->
      path_over (fun a : A => forall b : B a, C a b) p c1 c2.
  Proof.
    destruct p. simpl. 
    intro q. apply (path_over_single_fiber^-1).
    apply path_forall. intro b.
    set (q' := q b).
    rewrite path_sigma_hprop_1 in q'.
    exact (path_over_single_fiber q').
  Defined.

  Definition pathover_sigma_hprop' {A : Type} {B : A -> Type} {isprop_B : (forall a : A, IsHProp (B a))}
             (C : {a : A &  B a} -> Type)
             {a1 a2 : A} (p : a1 = a2)
             (c1 : forall b : B a1, C (a1; b)) (c2 : forall b : B a2, C (a2; b))
    : 
      (forall (b1 : B a1)       (*(b2 : B a2) *),  (* transport B p b1*)
          path_over C
                    (path_sigma_hprop (a1; b1) (a2; transport B p b1) p)
                    (c1 b1) (c2 (transport B p b1))) ->
      path_over (fun a : A => forall b : B a, C (a; b)) p c1 c2.
  Proof.
    destruct p. simpl. 
    intro q. apply (path_over_single_fiber^-1).
    apply path_forall. intro b.
    set (q' := q b).
    rewrite path_sigma_hprop_1 in q'.
    exact (path_over_single_fiber q').
  Defined.

  (* not needed? *)
  Definition pathover_forall {A B : Type} (C : A -> B -> Type)
             {a1 a2 : A} (p : a1 = a2)
             (c1 : forall b : B, C a1 b) (c2 : forall b : B, C a2 b)
    : (forall b : B, path_over (fun a : A => C a b) p (c1 b) (c2 b)) ->
      path_over (fun a : A => forall b : B, C a b) p c1 c2.
  Proof.
    destruct p. intro q.
    apply path_over_single_fiber^-1.
    apply path_forall. intro b.
    apply (path_over_single_fiber (q b)).
  Defined.             

  Definition double_pathover_forall
             {A B C : Type}
             (D :  A -> B -> C -> Type)
             {a a' : A} (p : a = a')
             {b b' : B} (q : b = b')
             (d : forall (c : C), D a b c)
             (d' : forall (c : C), D a' b' c)
    : (forall (c : C), double_pathover (fun a b => D a b c) p q (d c) (d' c))
      ->
      double_pathover (fun a b => (forall c : C, D a b c)) p q d d'.
  Proof.
    intro h. destruct p. destruct q. simpl. simpl in h.
    apply path_forall. intro c. apply h.
  Defined.

  Definition path_over_arrow' {A : Type} (B C : A -> Type)
             {a1 a2 : A} (p : a1 = a2)
             (f1 : B a1 -> C a1) (f2 : B a2 -> C a2)
    : (forall b : B a1,
          path_over C p (f1 b) (f2 (transport B p b))) ->
      path_over (fun a => B a -> C a) p f1 f2.
  Proof.
    destruct p.  simpl.
    intro h.
    apply (path_over_single_fiber^-1). apply path_arrow.
    intro b. exact (path_over_single_fiber (h b)).
  Defined.
                           
  
  Definition Z0_ind_set (P : forall z : Z, Type) {isset_P : forall z : Z, IsHSet (P z)}
             (f : forall (a : nat), P (Fin_to_Z (canon a) (canon a)))
             (base_change :
                forall (a : nat) (alpha : canon a = canon a) (betta : canon a = canon a),
                  double_pathover (fun (x : Finite_Types a) (y : Finite_Types a) =>
                                     P (Fin_to_Z x y))
                                  alpha betta (f a) (f a))
             (act_add :
                forall s a : nat, path_over P (lcancel_canon s a a) (f a) (f (s +' a)))
    : forall (z : Z), (card_Z z = nat_to_integer 0) -> P z.
  Proof.
    srapply (grp_compl_FinType_ind_set).
    - hnf. intros a b p.
      refine (transport P _ (f a)).
      apply (ap (fun x => Fin_to_Z (canon a) (canon x))).
      apply (diff_zero _ _ p).
    - intros. simpl.
      apply double_pathover_forall.
      intro p. revert p.
      apply (equiv_functor_forall_pf (equiv_diff_zero a b)). intro p.
      (* change (diff_zero a b ?x) with (equiv_diff_zero a b x). *)
      (* rewrite (eisretr (equiv_diff_zero a b) p). *)
      simpl. destruct p.
      assert (h : (diff_zero a a (cancel_zero a)) = idpath).
      { apply hset_nat. } rewrite h. simpl.
      apply base_change.
    - intros a b s. simpl.
      apply path_over_arrow'.
      simpl. intro p.      
      assert (diff_zero
                (s +' a) (s +' b)
                (transport (fun a0 : Z => card_Z a0 = nat_to_integer 0) (lcancel_canon s a b) p) =
              ap (fun x => s +' x)
                 (diff_zero a b p)).
      { apply hset_nat. } rewrite X. clear X.
      destruct (diff_zero a b p). simpl.
      exact (act_add s a).
  Defined.
                      
             

  Definition Z0_ind_set' (P : Z0 -> Type) {isset_P : forall z : Z0, IsHSet (P z)}
             (f : forall (a : nat), P (canon_Z0 a))
             (base_change:
                forall (a : nat) (alpha : canon a = canon a) (betta : canon a = canon a),
                  double_pathover (fun (x : Finite_Types a) (y : Finite_Types a) =>
                                     P (FinFin_to_Z0 x y))
                                  alpha betta (f a) (f a))
             (act_add :
                forall s a : nat, path_over P (lcancel_canon_Z0 s a) (f a) (f (s +' a)))
    : forall z : Z0, P z.
  Proof.
    intros [z p]. revert z p.
    srapply (grp_compl_FinType_ind_set).
    - hnf. intros a b p.
      refine (transport P _ (f a)).
      apply path_sigma_hprop. simpl.
      apply (ap (fun x => Fin_to_Z (canon a) (canon x))).
      apply (diff_zero _ _ p).
    - intros. simpl.
      apply double_pathover_forall.
      intro p. revert p.
      apply (equiv_functor_forall_pf (equiv_diff_zero a b)). intro p.
      (* change (diff_zero a b ?x) with (equiv_diff_zero a b x). *)
      (* rewrite (eisretr (equiv_diff_zero a b) p). *)
      simpl. destruct p.
      assert (h : (diff_zero a a (cancel_zero a)) = idpath).
      { apply hset_nat. } rewrite h. rewrite path_sigma_hprop_1. clear h.
      simpl. apply base_change.
    - intros a b s. simpl.
      
      apply pathover_sigma_hprop'. intro p. simpl in p.
      (* assert ((path_sigma_hprop (FinType_to_Z (canon_FinType a) (canon_FinType b); p) *)
      (*  (FinType_to_Z (canon_FinType (s +' a)) (canon_FinType (s +' b)); *)
      (*  transport (fun a0 : Z => card_Z a0 = nat_to_integer 0) (lcancel_canon s a b) p) *)
      (*  (lcancel_canon s a b)) = (lcancel_canon_Z0 s a) *)
      (* revert p. *)
      
      (* assert ((fun ab : {a0 : Z & card_Z a0 = nat_to_integer 0} => P (ab.1; ab.2)) = P). *)
      (* { apply path_arrow.  intros [a' b']. reflexivity. } *)
      (* rewrite X. *)
      
      assert (diff_zero (s +' a) (s +' b)
                        (transport (fun a0 : Z => card_Z a0 = nat_to_integer 0) (lcancel_canon s a b)
                                   p) =
              ap (fun x => s +' x) (diff_zero a b p)).
      { apply hset_nat. } rewrite X. clear X.
      
      generalize (diff_zero a b p). intro q.
      assert ((equiv_diff_zero a b)^-1 q = p).
      { apply (istrunc_trunctype_type (n := 0)). }
      destruct X. destruct q. simpl.
      unfold lcancel_canon_Z0 in act_add. unfold canon_Z0 in act_add.
      assert
        (transport (fun a0 : Z => card_Z a0 = nat_to_integer 0) (lcancel_canon s a a) (cancel_zero a)
                   = cancel_zero (s +' a)).
      { apply (istrunc_trunctype_type (n := 0)). } rewrite X. clear X.
      rewrite path_sigma_hprop_1. rewrite path_sigma_hprop_1. simpl.
      apply act_add.
  Defined.


  Definition component_card (z : Z) :
    merely (z = FinType_to_Z (canon_FinType 2) (canon_FinType 2)) <~>
           card_Z z = nat_to_integer 0.
  Proof.
    apply equiv_iff_hprop.
    - intro p. strip_truncations. simpl in p.
      refine (ap card_Z p @ _). simpl.
      apply inverse.
      apply (rcancel_integers 2).
    - revert z.
      srapply (grp_compl_FinType_ind_hprop).
      simpl. intros a b p. simpl.
      rewrite <- (diff_zero a b p). apply tr.
      apply path_base_2.
  Defined.
  
  Definition Z0_to_fin2 : Z0 -> Finite_Types 2.
  Proof.
    intros [z  p]. exact (grpcompl_to_fin2 z).
  Defined.  

  Definition fin2_to_Z0 : Finite_Types 2 -> Z0.
  Proof.
    intro x.
    exists (fin2_to_grpcompl x). simpl.
    apply inverse.
    apply (rcancel_integers 2).
  Defined.

  Definition double_pathover_path {A B C: Type} 
             (f g : A -> B -> C)
             {a a' : A} (alpha : a = a')
             {b b' : B} (betta : b = b')
             (p : f a b = g a b) (q : f a' b' = g a' b')
    : (ap011 f alpha betta)^ @ p @ (ap011 g alpha betta) =  q ->
      double_pathover (fun a b => f a b = g a b) alpha betta p q.
  Proof.
    destruct alpha. destruct betta. simpl.
    intro h. refine (_ @ h).
    apply inverse.
    refine (concat_p1 _ @ _).
    apply concat_1p.
  Defined.

  Definition loops_functor_uncurried' {A B : Type} {a0 : A} {b0 : B} (f : A -> B)
    : (f a0 = b0) -> (a0 = a0) -> (b0 = b0).
  Proof.
    intro p.
    intro q.
    exact (p^ @ (ap f q @ p)).
  Defined.

  Definition ispointed_compose {A B C : Type} {a0 : A} {b0 : B} {c0 : C}
             (g : B -> C) (pt_g : g b0 = c0)
             (f : A -> B) (pt_f : f a0 = b0)
    : g (f a0) = c0.
  Proof.
    exact (ap g (pt_f) @ pt_g).
  Defined.

  Definition loops_functor_uncurried_compose {A B C : Type} {a0 : A} {b0 : B} {c0 : C}
             (f : A -> B) (pt_f : f a0 = b0)
             (g : B -> C) (pt_g : g b0 = c0)
    : loops_functor_uncurried' (g o f) (ispointed_compose g pt_g f pt_f) ==
      loops_functor_uncurried' g pt_g o loops_functor_uncurried' f pt_f.
  Proof.
    intro p. unfold loops_functor_uncurried'.
    unfold ispointed_compose. destruct pt_g. destruct pt_f. 
    simpl. destruct p. reflexivity.
  Defined.
  

  
  Definition isidmap_Z0 (f : Z -> Z)
             (* unecessary? *)
             (f_comp0 : forall (z : Z), card_Z z = nat_to_integer 0 -> card_Z (f z) = nat_to_integer 0)
             (f_canon : forall a : nat,
                 f (Fin_to_Z (canon a) (canon a)) = (Fin_to_Z (canon a) (canon a)))
             (f_bc : forall (a : nat) (alpha betta : canon a = canon a),
                 loops_functor_uncurried' f (f_canon a) ((ap011 Fin_to_Z alpha betta))= 
                 (* (f_canon a)^ @ (ap f (ap011 Fin_to_Z alpha betta) @ f_canon a) = *)
                 ap011 Fin_to_Z alpha betta)  
             (f_add : forall (s a : nat),
                 (f_canon a)^ @ (ap f (lcancel_canon s a a) @ f_canon (s +' a))=
                 lcancel_canon s a a)

             (* (f_canon : forall a : nat, *)
             (*     (Fin_to_Z (canon a) (canon a)) = f (Fin_to_Z (canon a) (canon a))) *)
             (* (f_bc : forall (a : nat) (alpha betta : canon a = canon a), *)
             (*     (ap011 Fin_to_Z alpha betta)^ @ f_canon a @ *)
             (*      ap011 (fun x y : Finite_Types a => f (Fin_to_Z x y)) alpha betta = f_canon a) *)

             (* (f_add : forall (s a : nat), *)
             (*     (lcancel_canon s a a)^ @ f_canon a @ ap f (lcancel_canon s a a) = *)
             (*     f_canon (s +' a)) *)
             
    : forall (z : Z), (card_Z z = nat_to_integer 0) -> f z = z.
  Proof.
    srapply Z0_ind_set.
    - intro a. (* apply inverse. *) apply f_canon.
    - intros. 
      apply double_pathover_path. simpl.
      refine (concat_pp_p _ _ _ @ _).
      apply moveR_Vp. apply moveR_Mp. apply inverse.
      refine (_ @ f_bc a alpha betta).
      apply whiskerL. apply whiskerR.
      destruct alpha. destruct betta. reflexivity.
    - intros s a.
      apply path_to_path_over.
      refine (transport_paths_FlFr (lcancel_canon s a a) (f_canon a) @ _).
      rewrite ap_idmap.
      apply moveR_Mp. apply inverse.
      refine (_ @ f_add s a).
      rewrite inv_Vp.
      refine (concat_pp_p _ _ _ ).
  Defined.

  (* move *)
  Definition loops_Bsign (a : nat) (alpha : canon a = canon a)
    : loops_functor (Bsign a) alpha =
      path_finite_types 2 (canon 2) (canon 2)
                        (sign a (pft_inv alpha)).
  Proof.
    unfold Bsign.
    refine (deloop_fin_loop a 2 _ _ ).
  Defined.

  Definition loops_Bsign' (a : nat) (alpha : Fin a <~> Fin a)
    : loops_functor (Bsign a) (equiv_path_finite_types a (canon a) (canon a) alpha) =
      path_finite_types 2 (canon 2) (canon 2) (sign a alpha).
  Proof.
    refine (loops_Bsign a _ @ _).
    apply (ap (path_finite_types _ _ _ )). apply (ap (sign a)).
    srefine (eissect (equiv_path_finite_types a (canon a) (canon a)) alpha).
  Defined.

  Definition path_Z_alpha_alpha (a : nat) (alpha : canon a = canon a)
    : ap011 Fin_to_Z alpha alpha = idpath.
  Proof.
    transitivity (ap011 FinType_to_Z (ap (fin_to_FinType) alpha) (ap (fin_to_FinType) alpha)).
    { destruct alpha. reflexivity. }
    refine (_ @ concat_Vp (path_base_0 (canon_FinType a))).
    cut (forall (x : FinType) (p : fin_to_FinType (canon a) = x),
            ap011 FinType_to_Z p p = ((path_base_0 (canon_FinType a))^) @ path_base_0 x).
    { intro H. apply H. }
    intro x. destruct p. rewrite concat_Vp. reflexivity.
  Defined.

  Definition grpcompl_to_fin2_pt (a : nat)
    : grpcompl_to_fin2 (Fin_to_Z (canon a) (canon a)) = canon 2.
  Proof.
    change (grpcompl_to_fin2 (Fin_to_Z ?A ?B)) with
    (Bsign _ ((sum_finite_types A B))).
    apply Bsign_sum_canon2.
  Defined.

  Definition issect_toZ_canon (a : nat)
    : fin2_to_grpcompl (grpcompl_to_fin2 (Fin_to_Z (canon a) (canon a))) =
      Fin_to_Z (canon a) (canon a).
  Proof.
    srefine (ispointed_compose fin2_to_grpcompl (b0 := canon 2) _ _ _).
      + apply inverse. apply path_base_2.
      + apply grpcompl_to_fin2_pt.
  Defined.

  (* Definition grp_compl_FinType_rec_beta_lcancel_Z (P : 1 -Type) (f : FinType -> FinType -> P) *)
  (*            (act_add : forall S A1 A2 : FinType, f A1 A2 = f (sum_FinType S A1) (sum_FinType S A2)) *)
  (*            (act_add_compose : forall (S T A1 A2 : FinType), *)
  (*              act_add (sum_FinType T S) A1 A2 *)
  (*                      @ (ap011 f (FinType_assoc T S A1) (FinType_assoc T S A2)) *)
  (*              = act_add S A1 A2 @ act_add T (sum_FinType S A1) (sum_FinType S A2)) *)
  (*            (S A B : FinType) *)
  (*   : ap (grp_compl_FinType_rec P f act_add act_add_compose) (lcancel_Z S A B) = *)
  (*     act_add S A B. *)
  (* Proof. *)
  (*   unfold lcancel_Z. unfold path_Z. *)
  (*   refine (cquot_rec_beta_ccleq group_completion_FinType P _ _ _ _ _ _ _ _ @ _). *)
  (*   simpl. apply concat_p1. *)
  (* Defined. *)
  
  Definition issect_toZ (z : Z) (p : card_Z z = nat_to_integer 0)
    : fin2_to_grpcompl (grpcompl_to_fin2 z) = z.
  Proof.
    revert z p.
    srapply isidmap_Z0.
    - intros z p. simpl.
      exact (rcancel_integers 2 0 0)^.
    - hnf. intro a.
      apply issect_toZ_canon.
    - intros.  hnf.
      rewrite (loops_functor_uncurried_compose ).
      assert (loops_functor_uncurried' (a0 := Fin_to_Z (canon a) (canon a))
                                       grpcompl_to_fin2 (Bsign_sum_canon2 a a)
                                       (ap011 Fin_to_Z alpha betta) =
              loops_functor_uncurried' (Bsign (a +' a)) (Bsign_sum_canon2 a a)
                                       (ap011 sum_finite_types alpha betta)).
      { unfold loops_functor_uncurried'. apply whiskerL. apply whiskerR.
        destruct alpha. destruct betta. reflexivity. }
      rewrite X. clear X.
      assert (loops_functor_uncurried' (Bsign (a +' a)) (Bsign_sum_canon2 a a)
                                       (ap011 sum_finite_types alpha betta) =
              path_finite_types 2 (canon 2) (canon 2)
                                (sign _ (block_sum (pft_inv alpha) (pft_inv betta)))).
      { unfold loops_functor_uncurried'.
        rewrite blocksum_is_ap011.
        refine (_ @ loops_Bsign (a +' a)  _).
        unfold Bsign_sum_canon2. rewrite inv_pp.
        change (loops_functor (Bsign ?m) ?x)
        with ((point_eq (Bsign m))^ @ (ap (Bsign m) x @ (point_eq (Bsign m)))).
        change (point_eq (Bsign ?m)) with (deloop_fin_canon m 2 (sgnhom m)).
        refine (concat_pp_p _ _ _ @ _). apply whiskerL.
        refine (concat_p_pp _ _ _ @ _). refine (concat_p_pp _ _ _ @ _).
        apply whiskerR.
        rewrite ap_pp. rewrite ap_pp. rewrite ap_V. 
        repeat rewrite concat_p_pp. reflexivity.
      }
      rewrite X. clear X. unfold loops_functor_uncurried'.
      rewrite inv_V. apply moveR_Mp. apply moveR_pV.
      refine (_ @ concat_p_pp _ _ _).
      apply moveL_Vp. apply moveL_pM. apply inverse.
      transitivity (ap011 Fin_to_Z alpha idpath @ ap011 Fin_to_Z idpath betta).
      { destruct alpha. destruct betta. reflexivity. }
      assert (ap011 Fin_to_Z idpath betta = ap011 Fin_to_Z betta^ idpath).
      { refine (_ @ (concat_p1 _)).
        rewrite <- (ap011_VV Fin_to_Z betta idpath).
        apply moveL_Vp.
        refine (_ @ path_Z_alpha_alpha _ betta).
        destruct betta. reflexivity. }
      rewrite X. clear X.
      apply moveL_pV. apply moveL_Mp.
      rewrite sgn_block_sum.
      
      rewrite (path_finite_types_compose 2 (canon 2) (canon 2) (canon 2)).
      rewrite ap_pp.
      assert (sgn_inv : forall (sigma : Fin a <~> Fin a),
                 sign a sigma = sign a (sigma^-1)).
      { intro sigma.
        transitivity (equiv_inverse (sign a sigma)).
        { refine (_ @ ecompose_e1 _).
          apply emoveL_Ve. apply invol_SymGrp2. }
        refine ((ecompose_e1 _)^ @ _).
        apply emoveR_Ve.
        refine (_ @ sgn_compose _ _ _). apply inverse.
        rewrite ecompose_eV. apply sgn_id. }
      rewrite (sgn_inv (pft_inv betta)).
      refine (_ @ 
                concat2 (path_is_sgn _ (pft_inv alpha)) (path_is_sgn _ (pft_inv betta)^-1) @ _).
      + change (fin_to_FinType (canon a)) with (canon_FinType a).
        refine (_ @ concat_p_pp _ _ _). refine (_ @ concat_p_pp _ _ _). apply whiskerL.
        refine (_ @ concat_pp_p _ _ _). refine (_ @ concat_pp_p _ _ _).
        apply whiskerR.
        refine (_ @ concat_pp_p _ _ _). rewrite concat_pp_V.
        assert (equiv_inverse (pft_inv betta) = pft_inv betta^).
        { destruct betta. simpl. apply path_equiv. reflexivity. }
        rewrite X. clear X.
        assert
          (forall (x : Finite_Types a) (p : canon a = x),
              ap011 Fin_to_Z p (idpath (canon a)) =
              ap011 FinType_to_Z (path_FinType (canon_FinType a) (fin_to_FinType x) (pft_inv p)) idpath).
        { intro x. destruct p. simpl.
          rewrite path_FinType_1. reflexivity. }
        apply concat2; apply X.
      + rewrite <- path_FinType_fix. rewrite <- path_FinType_fix.
        assert (forall (x : Finite_Types 2) (p : canon 2 = x),
                   ap011 FinType_to_Z (pft_to_pbs p) idpath =
                   ap fin2_to_grpcompl p).
        { intros x []. reflexivity. }
        apply concat2; apply X.
    - intros. hnf. unfold ispointed_compose.
      assert (lcancel_canon s a a =
              path_base_2 _ @ (path_base_2 _)^).
      { apply moveL_pV.
        unfold path_base_2. destruct (path_base_0 (canon_FinType 2)).
        rewrite concat_p1. rewrite concat_p1. apply moveR_pV. apply moveL_Vp.
        unfold path_base_0. unfold lcancel_canon. unfold lcancel_Z.
        destruct (finsum_id s a). simpl. rewrite concat_p1.
        rewrite path_Z_compose. rewrite concat_p1.
        rewrite <- path_FinType_1.
        rewrite <- path_FinType_sum.
        rewrite <- path_FinType_compose.        
        apply (ap011 (path_Z _)); apply (ap (path_FinType _ _));
          apply path_equiv; apply path_arrow; intro x;
            repeat destruct x as [x | x]; try destruct x; reflexivity. }
      refine (_ @ X^).
      clear X.
      unfold issect_toZ_canon. unfold ispointed_compose.
      rewrite inv_pV.
      refine (concat_pp_p _ _ _ @ _). apply whiskerL.
      refine (concat_p_pp _ _ _ @ _). refine (concat_p_pp _ _ _ @ _).
      refine (_ @ concat_1p _). apply whiskerR.
      refine (_ @ ap_1 _ fin2_to_grpcompl).
      rewrite (ap_compose grpcompl_to_fin2 fin2_to_grpcompl).
      rewrite <- ap_V. rewrite <- ap_pp. rewrite <- ap_pp.
      apply (ap (ap fin2_to_grpcompl)).
      unfold grpcompl_to_fin2_pt.
      apply moveR_pM. rewrite concat_1p. 
      apply moveR_Vp.
      unfold lcancel_canon. rewrite ap_pp.
      apply moveR_pM.
      (* rewrite grp_compl_FinType_rec_beta_path_Z. *)
      refine (grp_compl_FinType_rec_beta_lcancel_Z
                _
                (fun A B : FinType => Bsign_uncurry (sum_FinType A B)) _ _
                (canon_FinType s) (canon_FinType a) (canon_FinType a)
                @ _).
      refine (Bsign_SASB_canon_id s a a @ _). unfold Bsign_SASB_canon.
      apply whiskerL. unfold Bsign_sum2.
      apply (ap inverse).
      apply inverse .
      assert (forall (A B : FinType) (p : A = B),
                 ap grpcompl_to_fin2 (ap011 FinType_to_Z p p) =
                 ap Bsign_uncurry (ap011 sum_FinType p p)).
      { intros A B []. reflexivity. }
      refine (X _ _ (finsum_id s a) @ _).  clear X.
      unfold finsum_id. rewrite <- path_FinType_fix.
      unfold sum_finite_types_canon.
      unfold canon_FinType. unfold fin_to_FinType.
      destruct (path_finite_types (s +' a) (sum_finite_types (canon s) (canon a)) 
                                  (canon (s +' a)) (equiv_finsum s a)).
      reflexivity.
  Defined.


  (** TODO: Explain notational difference from book  *)
  Definition equiv_Z0_fin2 : Z0 <~> Finite_Types 2.
  Proof.
    apply (equiv_adjointify Z0_to_fin2 fin2_to_Z0).
    - intro x.
      unfold fin2_to_Z0. unfold Z0_to_fin2.
      apply isretr_toZ.
    - intros [z p].
      unfold Z0_to_fin2. unfold fin2_to_Z0.
      apply path_sigma_hprop. simpl.
      apply issect_toZ. exact p.
  Defined.
  
  
End IsEquiv_GrpCompl_To_Fin2.