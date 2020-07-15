Require Import HoTT.

From A_BPQ Require Import 
     conn_ptype path_lemmas finite_types delooping permutations fintype_monoidal
     group_complete_1type onetype_completion.

Definition group_completion_FinType := group_completion FinType_smoncat FinType_lcancel.
Section Univalent_Group_Completion_FinType.
  
  Lemma sum_empty_is_empty (A B : Type) :
    A + B <~> Empty -> A <~> Empty.
  Proof.
    intro e.
    apply (BuildEquiv A Empty (fun a => e (inl a)) ). apply all_to_empty_isequiv.
  Defined.    

  Definition univalent_group_completion_FinType :
    Categories.IsCategory group_completion_FinType.
  Proof.
    apply univalent_monactcat; simpl.
    - intros A B.
      intro p.
      apply path_FinType. simpl.
      apply (sum_empty_is_empty A B).
      apply ((path_FinType _ _)^-1 p).
    - intro A.
      apply (trunc_equiv' (Empty <~> A)).
      + apply (equiv_path_FinType (canon_FinType 0)).
      + apply (trunc_equiv' (A <~> Empty)).
        * apply equiv_equiv_inverse.
        * exact _.
  Qed.
End Univalent_Group_Completion_FinType.

Definition Z := cquot (group_completion_FinType).


Definition ccleq_concat_Z (S A1 B1 : FinType) (A2 A3 : FinType * FinType)
           (p : (sum_FinType S A1, sum_FinType S B1) = A2)
           (q : A2 = A3)
  : ccleq group_completion_FinType (a₁ := (A1, B1)) (S; p @ q) =
    ccleq group_completion_FinType (a₁ := (A1, B1)) (S; p) @ ap (ccl group_completion_FinType) q.
Proof.
  destruct q. rewrite concat_p1. rewrite concat_p1. reflexivity.
Qed.


Definition FinType_to_Z : FinType -> FinType -> Z.
Proof.
  intros A B.  apply ccl.
  exact (A, B).
Defined.

Definition Fin_to_Z {a b : nat}
  : Finite_Types a -> Finite_Types b -> Z.
  intros A B. apply FinType_to_Z.
  - exact (fin_to_FinType A).
  - exact (fin_to_FinType B).
Defined.



Section N1_FinType_set_ind.
  
  Definition canon_grpclFinType_sum (m1 m2 n1 n2 : nat) :
    FinType_to_Z (sum_FinType (canon_FinType m1) (canon_FinType n1))
                 (sum_FinType (canon_FinType m2) (canon_FinType n2)) =
    FinType_to_Z (canon_FinType (n1 + m1)) (canon_FinType (n2 + m2)).
  Proof.
    apply (ap011 FinType_to_Z); apply finsum_id.
  Defined.
  
  (* ccl (group_completion_FinType) *)
  (*     (functor_prod (sum_FinType (canon_FinType m1)) (sum_FinType (canon_FinType m2)) (canon_FinType n1, canon_FinType n2)) = *)
  (* ccl (group_completion_FinType) *)
  (*     (canon_FinType (n1+m1), (canon_FinType (n2+m2))). *)
  (* Proof. *)
  (*   apply (ap (ccl group_completion_FinType)). unfold sum_FinType. simpl. *)
  (*   unfold functor_prod. simpl. unfold canon_FinType. *)
  (*   exact (ap (fun x : Finite_Types (n1 + m1) * Finite_Types (n2+m2) => *)
  (*                (fin_to_FinType (fst x), (fin_to_FinType (snd x)))) *)
  (*         (path_prod (_,_) (_,_) (finsum_id m1 n1) (finsum_id m2 n2)))%nat. *)
  (* Defined. *)


  Definition path_Z {A1 B1 A2 B2 : FinType} (S : FinType)
    : (sum_FinType S A1 = A2) -> (sum_FinType S B1 = B2)
      -> FinType_to_Z A1 B1 = FinType_to_Z A2 B2.
  Proof.
    intros p q.
    apply ccleq. exists S.
    apply path_prod.
    - exact p. - exact q.
  Defined.

  Definition path_Z_fr {A1 B1 A2 B2 : FinType} (S : FinType)
    : (sum_FinType A1 S = A2) -> (sum_FinType B1 S = B2)
      -> FinType_to_Z A1 B1 = FinType_to_Z A2 B2.
  Proof.
    intros p q.
    apply ccleq. exists S. simpl.
    apply path_prod; simpl.
    - exact (FinType_symmetric _ _ @ p).
    - exact (FinType_symmetric _ _ @ q).
  Defined.
  
  (* {s a b : nat} (S : Finite_Types s) (A : Finite_Types a) (B : Finite_Types b) *)
  Definition lcancel_Z (S A B : FinType)
    : FinType_to_Z A B = FinType_to_Z (sum_FinType S A) (sum_FinType S B) :=
    path_Z S idpath idpath.

  Definition lcancel_Z_fr (A B S : FinType)
    : FinType_to_Z A B = FinType_to_Z (sum_FinType A S) (sum_FinType B S) :=
    path_Z_fr S idpath idpath.
  (* Proof. *)
  (*   apply (path_Z S); apply FinType_symmetric. *)
  (*   (* refine (lcancel_Z S A B @ _); *) *)
  (*   (* apply (ap011 FinType_to_Z); apply FinType_symmetric. *) *)
  (* Defined. *)

  Definition path_Z_pp_r {A1 B1 A2 B2 A2' B2'} (S : FinType)
             (p1 : sum_FinType S A1 = A2) (p2 : sum_FinType S B1 = B2)
             (q1 : A2 = A2') (q2 : B2 = B2')
    : path_Z S (p1 @ q1) (p2 @ q2) =
      path_Z S p1 p2 @ (ap011 FinType_to_Z q1 q2).
  Proof.
    destruct q1. destruct q2. destruct p1. destruct p2. simpl.
    rewrite concat_p1. reflexivity.
  Defined.

  Definition path_Z_pp_l {A1 B1 A1' B1' A2 B2 S}
             (p1 : A1 = A1') (p2 : B1 = B1')
             (q1 : sum_FinType S A1' = A2)
             (q2 : sum_FinType S B1'= B2)
    : path_Z S (ap011 sum_FinType idpath p1 @ q1) (ap011 sum_FinType idpath p2 @ q2) =
      ap011 FinType_to_Z p1 p2 @ path_Z S q1 q2.
  Proof.
    destruct q1. destruct q2. destruct p1. destruct p2.
    simpl. 
    rewrite concat_1p. reflexivity.
  Defined.

  Definition path_Z_fr_pp_r {A1 B1 A2 B2 A2' B2'} (S : FinType)
             (p1 : sum_FinType A1 S = A2) (p2 : sum_FinType B1 S = B2)
             (q1 : A2 = A2') (q2 : B2 = B2')
    : path_Z_fr S (p1 @ q1) (p2 @ q2) =
      path_Z_fr S p1 p2 @ (ap011 FinType_to_Z q1 q2).
  Proof.
    destruct q1. destruct q2. destruct p1. destruct p2. simpl.
    rewrite concat_p1. reflexivity.
  Defined.

  Definition path_Z_fr_pp_l {A1 B1 A1' B1' A2 B2 S}
             (p1 : A1 = A1') (p2 : B1 = B1')
             (q1 : sum_FinType A1' S = A2)
             (q2 : sum_FinType B1' S = B2)
    : path_Z_fr S (ap011 sum_FinType p1 idpath @ q1) (ap011 sum_FinType p2 idpath @ q2) =
      ap011 FinType_to_Z p1 p2 @ path_Z_fr S q1 q2.
  Proof.
    destruct p1. destruct p2.
    rewrite concat_1p. rewrite concat_1p. rewrite concat_1p.
    reflexivity.
  Defined.


  Definition path_Z_100 {A1 B1 A2 B2} (S S' : FinType) (p : S' = S)
             (q1 : sum_FinType S A1 = A2)
             (q2 : sum_FinType S B1 = B2)
    : path_Z S q1 q2 =
      path_Z S' (ap011 sum_FinType p idpath @ q1)
             (ap011 sum_FinType p idpath @ q2).
  Proof.
    destruct p.
    rewrite concat_1p. rewrite concat_1p.
    reflexivity.
  Defined.

  Definition path_Z_fr_100 {A1 B1 A2 B2} (S S' : FinType) (p : S' = S)
             (q1 : sum_FinType A1 S = A2)
             (q2 : sum_FinType B1 S = B2)
    : path_Z_fr S q1 q2 =
      path_Z_fr S' (ap011 sum_FinType idpath p @ q1)
                (ap011 sum_FinType idpath p @ q2).
  Proof.
    destruct p.
    rewrite concat_1p. rewrite concat_1p.
    reflexivity.
  Defined.

  Definition path_is_lcancel {A1 B1 A2 B2} (S : FinType)
             (p : sum_FinType S A1 = A2) (q : sum_FinType S B1 = B2)
    : path_Z S p q = lcancel_Z S A1 B1 @ ap011 FinType_to_Z p q.
  Proof.
    unfold lcancel_Z.
    refine (_ @ path_Z_pp_r S idpath idpath p q).
    rewrite concat_1p. rewrite concat_1p.
    reflexivity.
  Defined.

  Definition path_fr_is_lcancel {A1 B1 A2 B2} (S : FinType)
             (p : sum_FinType A1 S = A2) (q : sum_FinType B1 S = B2)
    : path_Z_fr S p q = lcancel_Z_fr A1 B1 S @ ap011 FinType_to_Z p q.
  Proof.
    unfold lcancel_Z_fr.
    refine (_ @ path_Z_fr_pp_r S idpath idpath p q).
    rewrite concat_1p. rewrite concat_1p.
    reflexivity.
  Defined.


  Definition path_Z_compose {A1 B1 A2 B2 A3 B3: FinType} (S T: FinType)
             (p1 : sum_FinType S A1 = A2) (q1 : sum_FinType S B1 = B2)
             (p2 : sum_FinType T A2 = A3) (q2 : sum_FinType T B2 = B3) : 
    (path_Z S p1 q1) @ (path_Z T p2 q2) = 
    @path_Z  A1 B1 A3 B3  (sum_FinType T S)
             (FinType_assoc T S A1 @ ap011 sum_FinType idpath p1 @ p2)
             (FinType_assoc T S B1 @ ap011 sum_FinType idpath q1 @ q2).
  Proof.
    unfold path_Z.
    apply inverse.
    refine (_ @ cconcat _ _ _). simpl.
    apply (ap (ccleq group_completion_FinType)).
    apply (ap (fun x => (sum_FinType T S; x))).
    rewrite ap_functor_prod.
    rewrite <- path_prod_pp. rewrite <- path_prod_pp. reflexivity.
  Qed.

  Definition path_Z_fr_compose {A1 B1 A2 B2 A3 B3: FinType} (S T: FinType)
             (p1 : sum_FinType A1 S = A2) (q1 : sum_FinType B1 S = B2)
             (p2 : sum_FinType A2 T = A3) (q2 : sum_FinType B2 T = B3) :
    (path_Z_fr S p1 q1) @ (path_Z_fr T p2 q2) = 
    @path_Z_fr  A1 B1 A3 B3  (sum_FinType S T)
                ((FinType_assoc A1 S T)^ @ ap011 sum_FinType p1 idpath @ p2)
                ((FinType_assoc B1 S T)^ @ ap011 sum_FinType q1 idpath @ q2).
  Proof.
    rewrite (path_Z_fr_100 _ _ (FinType_symmetric T S)).
    unfold path_Z_fr.
    apply inverse.
    refine (_ @ cconcat _ _ _). 
    apply (ap (ccleq group_completion_FinType)). simpl.
    apply (ap (fun x => (sum_FinType T S; x))).
    rewrite ap_functor_prod.
    rewrite <- path_prod_pp. rewrite <- path_prod_pp.
    destruct q2. destruct p2. destruct q1. destruct p1.
    repeat rewrite concat_p1.
    rewrite <- path_FinType_1.
    rewrite <- path_FinType_sum.
    rewrite <- path_FinType_1.
    rewrite <- path_FinType_sum.
    rewrite path_FinType_V.
    rewrite path_FinType_V.
    rewrite natural_path_FinType_r.
    rewrite natural_path_FinType_r.
    repeat rewrite <- path_FinType_compose.
    apply (ap011 (path_prod _ _)); apply (ap (path_FinType _ _));
      apply path_equiv; apply path_arrow; intro x;
        repeat destruct x as [x | x]; reflexivity.
  Qed.

  Definition lcancel_Z_compose (S T A B : FinType)
    (* {s t a b : nat} *)
    (* (S : Finite_Types s) (T : Finite_Types t) (A : Finite_Types a) (B : Finite_Types b) *)
    : lcancel_Z (sum_FinType T S) A B  =
      lcancel_Z S A B @ lcancel_Z T (sum_FinType S A) (sum_FinType S B)
                @ (ap011 FinType_to_Z (FinType_assoc T S A) (FinType_assoc T S B))^.
  Proof.
    unfold lcancel_Z. apply moveL_pV.
    refine (_ @ (path_Z_compose S T _ _ _ _)^). simpl.
    repeat rewrite concat_p1. destruct (FinType_assoc T S A). destruct (FinType_assoc T S B).
    apply concat_p1.
  Defined.

  Definition lcancel_Z_fr_compose (A B S T: FinType) 
    : lcancel_Z_fr A B (sum_FinType T S) =
      lcancel_Z_fr A B T @ (lcancel_Z_fr _ _ S) @
                   (ap011 FinType_to_Z (FinType_assoc A T S) (FinType_assoc B T S)).
  Proof.
    unfold lcancel_Z_fr.
    apply moveL_pM.
    refine (_ @ (path_Z_fr_compose T S _ _ _ _)^).
    repeat rewrite concat_p1. simpl.
    transitivity (path_Z_fr (sum_FinType T S) 1 1 @
                            (ap011 FinType_to_Z (FinType_assoc A T S)^ (FinType_assoc B T S)^)).
    { apply whiskerL. destruct (FinType_assoc A T S). destruct (FinType_assoc B T S).
      reflexivity. }
    destruct (FinType_assoc A T S)^.
    destruct (FinType_assoc B T S)^.
    apply concat_p1.
  Defined.               
  

  Definition lcancel_canon (s m n : nat) :
    FinType_to_Z (canon_FinType m) (canon_FinType n) =
    FinType_to_Z (canon_FinType (m + s)) (canon_FinType (n + s)).
  Proof.
    refine (lcancel_Z (canon_FinType s) _ _ @ _).
    apply (ap011 FinType_to_Z); apply finsum_id.
    (* apply (path_Z (canon_FinType s)); *)
    (*   apply finsum_id. *)
  Defined.

  Definition lcancel_canon_fr (s m n : nat)
    : FinType_to_Z (canon_FinType m) (canon_FinType n) =
      FinType_to_Z (canon_FinType (m +' s)) (canon_FinType (n +' s)).
  Proof.
    apply (path_Z_fr (canon_FinType s)); apply finsum_id.
    (* refine (lcancel_Z_fr _ _ (canon_FinType s) @ _). *)
    (* apply (ap011 FinType_to_Z); apply finsum_id. *)
  Defined.

  Definition lcancel_canon_path_fr (s a b : nat)
             (sigma : fintype s <~> fintype s)
             (alpha : fintype a <~> fintype a) (betta : fintype b <~> fintype b)
    : ap011 FinType_to_Z
            (path_FinType (canon_FinType (a +' s)) (canon_FinType (a +' s)) (block_sum alpha sigma))
            (path_FinType (canon_FinType (b +' s)) (canon_FinType (b +' s)) (block_sum betta sigma)) =
      (lcancel_canon_fr s a b)^ @
                                  ap011 FinType_to_Z (path_FinType (canon_FinType a) (canon_FinType a) alpha)
                                  (path_FinType (canon_FinType b) (canon_FinType b) betta)
                                  @ lcancel_canon_fr s a b.
  Proof.
    rewrite path_FinType_blocksum.
    rewrite path_FinType_blocksum.
    repeat refine (_ @ concat_p_pp _ _ _).
    apply moveL_Vp.
    unfold lcancel_canon_fr.
    unfold lcancel_Z_fr.
    rewrite <- path_Z_fr_pp_r.
    (* rewrite <- path_Z_fr_pp_r. *)
    repeat rewrite concat_1p.
    rewrite concat_p_Vp. rewrite concat_p_Vp.
    destruct (finsum_id a s). destruct (finsum_id b s).
    rewrite concat_p1. rewrite concat_p1.
    destruct (path_FinType (canon_FinType a) (canon_FinType a) alpha).
    destruct (path_FinType (canon_FinType b) (canon_FinType b) betta).
    destruct (path_FinType (canon_FinType s) (canon_FinType s) sigma). 
    rewrite concat_1p. reflexivity.
  Defined.  

  Definition lcancel_canon_path (s a b : nat)
             (sigma : fintype s <~> fintype s)
             (alpha : fintype a <~> fintype a) (betta : fintype b <~> fintype b) 
    : ap011 FinType_to_Z
            (path_FinType (canon_FinType (a + s)) (canon_FinType (a + s)) (block_sum sigma alpha))
            (path_FinType (canon_FinType (b + s)) (canon_FinType (b + s)) (block_sum sigma betta)) =
      (lcancel_canon s a b)^ @
                               ap011 FinType_to_Z (path_FinType (canon_FinType a) (canon_FinType a) alpha)
                               (path_FinType (canon_FinType b) (canon_FinType b) betta)
                               @ lcancel_canon s a b.
  Proof.
    rewrite path_FinType_blocksum.
    rewrite path_FinType_blocksum.
    repeat refine (_ @ concat_p_pp _ _ _).
    apply moveL_Vp.
    unfold lcancel_canon.
    unfold lcancel_Z.
    rewrite <- path_Z_pp_r.
    rewrite <- path_Z_pp_r.
    repeat rewrite concat_1p.
    rewrite concat_p_Vp. rewrite concat_p_Vp.
    destruct (finsum_id s a). destruct (finsum_id s b).
    rewrite concat_p1. rewrite concat_p1.
    destruct (path_FinType (canon_FinType a) (canon_FinType a) alpha).
    destruct (path_FinType (canon_FinType b) (canon_FinType b) betta).
    destruct (path_FinType (canon_FinType s) (canon_FinType s) sigma). 
    rewrite concat_1p. reflexivity.
  Defined.            
  
  



  (* Definition plus_assoc_Z (a1 b1 c1 a2 b2 c2 : nat) *)
  (*   : FinType_to_Z (canon_FinType ((a1 + b1) + c1)) (canon_FinType ((a2 + b2) + c2)) = *)
  (*     FinType_to_Z (canon_FinType (a1 + (b1 + c1))) (canon_FinType (a2 + (b2 + c2))). *)
  (* Proof. *)
  (*   apply (ap011 FinType_to_Z); *)
  (*     apply (ap canon_FinType); apply nat_lemmas.plus_assoc. *)
  (* Defined. *)

  Definition lcancel_canon_fr_compose (a b s t : nat)
    : lcancel_canon_fr (s +' t) a b =
      lcancel_canon_fr s a b @ lcancel_canon_fr t (a +' s) (b +' s) @
                       (ap011 FinType_to_Z (canon_FinType_assoc _ _ _) (canon_FinType_assoc _ _ _)).
  Proof.
    unfold lcancel_canon_fr. unfold lcancel_Z_fr.
    (* rewrite <- path_Z_fr_pp_r. *) (* rewrite <- path_Z_fr_pp_r. rewrite <- path_Z_fr_pp_r. *)
    repeat rewrite concat_1p.
    rewrite path_Z_fr_compose. rewrite <- path_Z_fr_pp_r.
    rewrite (path_Z_fr_100 _ _ (finsum_id s t)). 
    
    rewrite <- path_FinType_1. rewrite <- path_FinType_sum.
    rewrite <- path_FinType_1. rewrite <- path_FinType_sum.
    rewrite path_FinType_V. rewrite path_FinType_V.
    rewrite <- path_FinType_compose. rewrite <- path_FinType_compose.
    rewrite <- path_FinType_1. rewrite <- path_FinType_sum.
    rewrite <- path_FinType_compose. rewrite <- path_FinType_compose.
    rewrite <- path_FinType_compose.
    rewrite <- path_FinType_sum.
    rewrite <- path_FinType_compose.
    rewrite <- path_FinType_compose. rewrite <- path_FinType_compose.

    assert (finsum_inv_l : forall (m n : nat),
               finsum_inv m n o (finl m n) == inl).
    { intros m n. intro x.
      exact (eissect (equiv_finsum m n) (inl x)). }
    assert (finsum_inv_r : forall (m n : nat),
               finsum_inv m n o (finr m n) == inr).
    { intros m n. intro x.
      exact (eissect (equiv_finsum m n) (inr x)). }
    
    apply (ap011 (path_Z_fr _)); (apply (ap (path_FinType _ _)));
      apply path_equiv; apply path_arrow; intro x; 
        repeat destruct x as [x | x]; simpl.
    - rewrite finsum_inv_l. change (functor_sum (B' := ?B) ?f ?g (inl ?y)) with (inl B (f y)).
      rewrite finsum_inv_l. reflexivity.
    - rewrite finsum_inv_l. change (functor_sum (B' := ?B) ?f ?g (inl ?y)) with (inl B (f y)).
      rewrite finsum_inv_r. reflexivity.
    - rewrite finsum_inv_r. reflexivity.
    - rewrite finsum_inv_l. change (functor_sum (B' := ?B) ?f ?g (inl ?y)) with (inl B (f y)).
      rewrite finsum_inv_l. reflexivity.
    - rewrite finsum_inv_l. change (functor_sum (B' := ?B) ?f ?g (inl ?y)) with (inl B (f y)).
      rewrite finsum_inv_r. reflexivity.
    - rewrite finsum_inv_r. reflexivity.
  Defined.



  Definition lcancel_canon_compose (m n s t : nat)
    : lcancel_canon (s + t) m n  =
      lcancel_canon s m n @ lcancel_canon t (m + s) (n + s)
                    @ (ap011 FinType_to_Z (canon_FinType_assoc _ _ _) (canon_FinType_assoc _ _ _))^.
  Proof.
    unfold lcancel_canon.
    assert (H : lcancel_Z  (canon_FinType (s + t)) (canon_FinType m) (canon_FinType n)  =
                lcancel_Z  (sum_FinType (canon_FinType t) (canon_FinType s))
                           (canon_FinType m) (canon_FinType n)
                           @ (ap011 FinType_to_Z
                                    (ap011 sum_FinType (finsum_id _ _) idpath)
                                    (ap011 sum_FinType (finsum_id _ _) idpath))).
    { destruct (finsum_id t s). apply inverse. apply concat_p1. }
    rewrite H. clear H.
    rewrite lcancel_Z_compose.
    repeat refine (_ @ concat_p_pp _ _ _).
    repeat refine (concat_pp_p _ _ _ @ _). apply whiskerL.
    (* refine (concat_p_pp _ _ _ @ _). *)
    refine (_ @ (whiskerL _ (concat_p_pp _ _ _ ))).
    refine (_ @ concat_pp_p _ _ _).
    assert (H :lcancel_Z (canon_FinType t)
                         (sum_FinType (canon_FinType s) (canon_FinType m))
                         (sum_FinType (canon_FinType s) (canon_FinType n))
               = (ap011 FinType_to_Z (finsum_id s m) (finsum_id s n) @
                        lcancel_Z (canon_FinType t) (canon_FinType (m + s)) (canon_FinType (n + s)))
                   @ (ap011 FinType_to_Z
                            (ap011 sum_FinType idpath (finsum_id s m))
                            (ap011 sum_FinType idpath (finsum_id s n)))^).
    { destruct (finsum_id s m). destruct (finsum_id s n).
      rewrite concat_1p. rewrite concat_p1. reflexivity. }
    rewrite H. clear H.
    refine (concat_pp_p _ _ _ @ _). apply whiskerL.
    apply moveR_Vp. apply moveR_Vp.
    refine (_ @ concat_pp_p _ _ _).
    refine (_ @ concat_pp_p _ _ _).
    apply moveL_pV.
    apply moveR_Mp.
    (* assert (ap011_pp_pp : forall {A B C : Type} (f : A -> B -> C) {x x' x'' : A} {y y' y'' : B} *)
    (*                              (p : x = x') (p' : x' = x'') (q : y = y') (q' : y' = y''), *)
    (*            ap011 f (p @ p') (q @ q') = ap011 f p q @ ap011 f p' q'). *)
    (* { intros. destruct p'. destruct p. destruct q'. destruct q. reflexivity. } *)
    rewrite <- ap011_pp_pp. rewrite <- ap011_pp_pp. rewrite <- ap011_pp_pp.
    rewrite ap011_VV. rewrite <- ap011_pp_pp.
    assert (H : forall (A B C : FinType) (e : A <~> B),
               ap011 sum_FinType (path_FinType A B e) (idpath C)
               = path_FinType (sum_FinType A C) (sum_FinType B C)
                              (equiv_functor_sum_r e)).
    { intros. refine (_ @ natural_path_FinType_l e).
      destruct (path_FinType A B e). reflexivity. }
    rewrite H. rewrite H. clear H.
    assert (H : forall (A B C : FinType) (e : B <~> C),
               ap011 sum_FinType (idpath A) (path_FinType B C e)
               = path_FinType (sum_FinType A B) (sum_FinType A C)
                              (equiv_functor_sum_l e)).
    { intros. refine (_ @ natural_path_FinType_r e).
      destruct (path_FinType B C e). reflexivity. }
    rewrite H. rewrite H. clear H.
    rewrite <- path_FinType_compose. rewrite <- path_FinType_compose.
    rewrite <- path_FinType_compose. rewrite <- path_FinType_compose.
    rewrite <- path_FinType_compose. rewrite <- path_FinType_compose.
    rewrite path_FinType_V. rewrite path_FinType_V.
    rewrite <- path_FinType_compose. rewrite <- path_FinType_compose.
    (* now they are basically the same *)
    apply (ap011 (ap011 FinType_to_Z));
      apply (ap (path_FinType _ _)); unfold canon_assoc;
        rewrite einv_ee; repeat rewrite ecompose_e_ee;
          reflexivity.
  Defined.

  (* removable? *)
  (* Definition uncurry_forall {A B : Type} (P : A -> B -> Type) : *)
  (*   (forall (a : A) (b : B), P a b) -> (forall ab : A*B, P (fst ab) (snd ab)). *)
  (* Proof. *)
  (*   intro f. *)
  (*   intros [a b]. exact (f a b). *)
  (* Defined. *)

  (* Local Open Scope nat_scope. *)

  Definition grp_compl_FinType_rec
             (P : 1-Type)
             (f : FinType -> FinType -> P)
             (act_add : forall (S A1 A2:  FinType),
                 f A1 A2 = f (sum_FinType S A1) (sum_FinType S A2))
             (act_add_compose : forall (S T A1 A2 : FinType),
                 act_add (sum_FinType T S) A1 A2
                         @ (ap011 f (FinType_assoc T S A1) (FinType_assoc T S A2))
                 = act_add S A1 A2 @ act_add T (sum_FinType S A1) (sum_FinType S A2))
    : Z -> P.
  Proof.
    (* set (uncurry_f := *)
    (*        fun x : FinType * FinType => *)
    (*          match x with *)
    (*            (A1, A2) => f A1 A2 end). *)
    srapply @cquot_rec'.
    - simpl. intros [A1 A2]. exact (f A1 A2).
    - simpl. intros [A1 A2]. intro B.
      unfold monoidal_action_morphism.
      intros [S p]. simpl in p.
      refine (act_add S _ _ @ _).
      apply (ap (uncurry f) p).
    - intros [A1 A2]. intros B C.
      intros [S p]. intros [T q]. 
      destruct q. destruct p. simpl. repeat rewrite concat_p1.
      refine (_ @ act_add_compose _ _ _ _).
      apply whiskerL.
      generalize (FinType_assoc T S A2) as q. 
      generalize (FinType_assoc T S A1) as p.
      cut (forall (B1 B2 : FinType)
                  (p : sum_FinType (sum_FinType T S) A1 = B1)
                  (q : sum_FinType (sum_FinType T S) A2 = B2),
              ap (uncurry f)
                 (path_prod
                    (functor_prod
                       (sum_FinType (sum_FinType T S)) (sum_FinType (sum_FinType T S)) (A1, A2))
                    (B1, B2) p q)
              = ap011 f p q).
      { intro H. apply H. }
      intros B1 B2. intros [] []. reflexivity.
  Defined.

  Definition grp_compl_FinType_rec_beta_lcancel_Z (P : 1 -Type) (f : FinType -> FinType -> P)
             (act_add : forall S A1 A2 : FinType, f A1 A2 = f (sum_FinType S A1) (sum_FinType S A2))
             (act_add_compose : forall (S T A1 A2 : FinType),
                 act_add (sum_FinType T S) A1 A2
                         @ (ap011 f (FinType_assoc T S A1) (FinType_assoc T S A2))
                 = act_add S A1 A2 @ act_add T (sum_FinType S A1) (sum_FinType S A2))
             (S A B : FinType)
    : ap (grp_compl_FinType_rec P f act_add act_add_compose) (lcancel_Z S A B) =
      act_add S A B.
  Proof.
    unfold lcancel_Z. unfold path_Z.
    refine (cquot_rec_beta_ccleq group_completion_FinType P _ _ _ _ _ _ _ _ @ _).
    simpl. apply concat_p1.
  Defined.


  (* Auxillary stuff for the next result *)
  Local Definition grp_compl_FinType_ind_set_fintype {a b : nat}
        (P : Z -> Type) {isset_P : forall z : Z, IsHSet (P z)}
        (f : forall (m n : nat),
            P (Fin_to_Z (canon m) (canon n)))
        (* P (ccl (group_completion_FinType) ((canon_FinType m), (canon_FinType n)))} *)
        (base_change
         : forall (a b : nat) (alpha : canon a = canon a) (betta : canon b = canon b),
            double_pathover (fun (x : Finite_Types a) (y : Finite_Types b) =>  P (Fin_to_Z x y))
                            alpha betta (f a b) (f a b))
    : forall (x : Finite_Types a) (y : Finite_Types b),
      P (Fin_to_Z x y).
  (* (ccl group_completion_FinType (fin_to_FinType x, fin_to_FinType y)). *)
  Proof.
    apply (deloop_double_ind_set'
             (pFin a) (pFin b)
             (fun x y => BuildTruncType 0 (P (Fin_to_Z x y))) (f a b)).
    intros alpha betta.
    apply (double_pathover_to_path
             (fun (x : pFin a) (y : pFin b) =>
                P (Fin_to_Z x y))
             alpha betta (f a b) (f a b)).
    apply base_change.
  Defined.

  (* Set induction for the group completion of FinType *)
  Definition grp_compl_FinType_ind_set
             (P : Z -> Type) {isset_P : forall z : Z, IsHSet (P z)}
             (f : forall (m n : nat),
                 P (Fin_to_Z (canon m) (canon n)))
             (base_change
              : forall (a b : nat) (alpha : canon a = canon a) (betta : canon b = canon b),
                 double_pathover (fun (x : Finite_Types a) (y : Finite_Types b) => P (Fin_to_Z x y))

                                 alpha betta (f a b) (f a b))
             (* transport *)
             (*   (fun p : Finite_Types a * Finite_Types b => *)
             (*      uncurry *)
             (*        (fun (x : Finite_Types a) (y : Finite_Types b) => *)
             (*           P (ccl group_completion_FinType (fin_to_FinType x, fin_to_FinType y))) p) *)
             (*   (path_prod (canon a, canon b) (canon a, canon b) alpha betta) *)
             (*   (f a b) = f a b) *)
             (act_add :
                (forall (m n : nat) (s : nat),
                    path_over P (lcancel_canon s m n) (f m n) (f (m+s)%nat (n+s)%nat)))
    : forall z : Z, P z.
  Proof.
    srapply @cquot_ind_set.
    - simpl.
      intros [[a x] [b y]]. 
      change (ccl group_completion_FinType
                  ({| card_FinType := a; fintype_of_FinType := x |},
                   {| card_FinType := b; fintype_of_FinType := y |}))
      with (Fin_to_Z x y).
      revert x y.
      (* change {| card_FinType := ?a; fintype_of_FinType := ?A |} with (fin_to_FinType A). *)
      apply (@grp_compl_FinType_ind_set_fintype a b P _ f base_change).
    - simpl. unfold monoidal_action_morphism.
      intros [[a A] [b B]] C [S p].  destruct p. simpl.
      revert B.
      srefine (deloop_ind_prop
                 (pFin b) 
                 _ _).
      revert A.
      srefine (deloop_ind_prop
                 (pFin a)
                 _ _).
      destruct S as [s S]. revert S.
      srefine (deloop_ind_prop
                 (pFin s)
                 _ _).
      simpl.
      change (@ccleq group_completion_FinType (?A, ?B) _
                     ({| card_FinType := s; fintype_of_FinType := point (Finite_Types s) |}; idpath))
      with
      (lcancel_Z (canon_FinType s) A B).
      change {| card_FinType := ?x; fintype_of_FinType := point (Finite_Types ?x) |}
      with (canon_FinType x).
      
      assert (H : (lcancel_Z (canon_FinType s) (canon_FinType a) (canon_FinType b)) =
                  (lcancel_canon s a b) @ (canon_grpclFinType_sum s s a b)^).
      { unfold lcancel_canon. unfold canon_grpclFinType_sum.
        destruct (ap011 FinType_to_Z (finsum_id s a) (finsum_id s b)).
        rewrite concat_p1.  rewrite concat_p1. reflexivity.

        (* unfold path_Z. *)
        (* unfold canon_grpclFinType_sum. (* unfold lcancel_Z. *) *)
        (* destruct (finsum_id s a). destruct (finsum_id s b). *)
        (* simpl. rewrite concat_p1. *)
        (* rewrite (path_is_lcancel  *)
      (* reflexivity. *) }
      (* destruct (canon_grpclFinType_sum s s a b). repeat rewrite concat_p1. reflexivity. } *)
      rewrite H. clear H.
      
      srapply @path_over_concat; simpl.
      + apply (grp_compl_FinType_ind_set_fintype P f base_change).
      (* apply f. *)
      + (* apply path_to_path_over. *)
        unfold grp_compl_FinType_ind_set_fintype.
        rewrite (deloop_double_ind_set_beta_pt').
        rewrite (deloop_double_ind_set_beta_pt').        
        apply act_add.
      + unfold canon_grpclFinType_sum.
        change (point (Finite_Types ?a)) with (canon a).
        unfold finsum_id.
        rewrite <- (path_FinType_fix (sum_finite_types (canon s) (canon _)) (canon (_ + s))
                                     (equiv_finsum s _)).
        rewrite <- (path_FinType_fix (sum_finite_types (canon s) (canon _)) (canon (_ + s))
                                     (equiv_finsum s _)).
        simpl.
        cut (forall (A : Finite_Types (a + s)) (B : Finite_Types (b + s))
                    (p : sum_finite_types (canon s) (canon a) = A)
                    (q : sum_finite_types (canon s) (canon b) = B),
                path_over
                  P (ap011 FinType_to_Z (pft_to_pbs p) (pft_to_pbs q))^
                (grp_compl_FinType_ind_set_fintype P f base_change A B)
                  (grp_compl_FinType_ind_set_fintype P f base_change (sum_finite_types (canon s) (canon a))
                                                     (sum_finite_types (canon s) (canon b)))).
        { intro H. apply H. }
        intros A B [] []. apply path_over_id.
        (* apply path_over_inv. *)
        (* change (grp_compl_FinType_ind_set_fintype (base_change := base_change) ?x ?y) with *)
        (* (uncurry_forall _ (grp_compl_FinType_ind_set_fintype (base_change := base_change)) (x,y)). *)
        (* apply *)
        (*   (apd_po *)
        (*      (uncurry_forall (fun (x : Finite_Types (a + s)) (y : Finite_Types (b + s)) => *)
        (*                         P (ccl group_completion_FinType (fin_to_FinType x, fin_to_FinType y))) *)
        (*                      (grp_compl_FinType_ind_set_fintype (base_change := base_change))) *)
        (*      (a₁ := (sum_finite_types (canon s) (canon a), sum_finite_types (canon s) (canon b))) *)
        (*      (a₂ := (canon (a + s), canon (b + s)))). *)
        
        (* generalize to some version of apd: *)
        (* cut (forall (A A' : Finite_Types (a + s)) (B B' : Finite_Types (b + s)) *)
        (*             (p : A = A') (q : B = B'), *)
        (*         path_over *)
        (*           P *)
        (*           (ap (ccl group_completion_FinType) *)
        (*               (ap *)
        (*                  (fun x : Finite_Types (a + s) * Finite_Types (b + s) => *)
        (*                     (fin_to_FinType (fst x), fin_to_FinType (snd x))) *)
        (*   (path_prod (A, B) (A', B') p q))) *)
        (*           (grp_compl_FinType_ind_set_fintype (base_change := base_change) A B) *)
        (*           (grp_compl_FinType_ind_set_fintype (base_change := base_change) A' B')). *)
        (* { intro H. apply H. } *)
        (* intros. destruct p. destruct q. simpl. apply path_over_id. *)
  Defined.


  Definition grp_compl_FinType_ind_hprop
             (P : Z -> Type) {hprop_P : forall z : Z, IsHProp (P z)}
             (f : forall (m n : nat),
                 P (Fin_to_Z (canon m) (canon n)))
    : forall z : Z, P z.
  Proof.
    srefine (grp_compl_FinType_ind_set P f _ _).
    - intros. apply path_to_double_pathover.
      apply hprop_P.
    - intros. apply path_to_path_over.
      apply hprop_P.
  Defined.
  

  (* (* change to only one act? *) *)
  (* Definition grp_compl_FinType_ind_set *)
  (*            (P : Z -> hSet) *)
  (*            (f : forall (m n : nat), *)
  (*                P (ccl (group_completion_FinType) ((canon_FinType m), (canon_FinType n)))) *)
  (*            (act_r : *)
  (*               forall (m n : nat) (σ : canon n = canon n), *)
  (*                 transport *)
  (*                   (fun x : (Finite_Types n) => *)
  (*                      P (ccl (group_completion_FinType) *)
  (*                             ((canon_FinType m), (fin_to_FinType x)))) σ (f m n) = (f m n)) *)
  (*            (act_l : *)
  (*               forall (m n : nat) (σ : canon m = canon m), *)
  (*                 transport *)
  (*                   (fun x : (Finite_Types m) => *)
  (*                      P (ccl (group_completion_FinType) ((fin_to_FinType x), (canon_FinType n)))) σ (f m n) = (f m n)) *)
  
  (*            (act_add : *)
  (*               (forall (m n : nat) (s : nat), *)
  (*                 transport P (ccleq_canon m n s) (f m n) = f (m+s)%nat (n+s)%nat)) *)
  (*            : forall z : Z, P z. *)

End N1_FinType_set_ind.





