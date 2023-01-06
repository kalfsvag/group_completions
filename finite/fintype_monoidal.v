Require Import HoTT.

From GCTT
     Require Import equiv_lemmas sigma_lemmas finite_types finite.permutations monoidal_1type.

(** Defining the monoidal 1-type of finite sets*)
Section FinType.
    
  (** This type is equivalent to the path groupoid of the category BSym
of finite sets and isomorphisms*)
  Record FinType :=
    {card_FinType : nat ; fintype_of_FinType :> Finite_Types card_FinType}.
    (* {m : nat & Finite_Types m}. *)
    (* { S : Type & Finite S}. *)

  Definition issig_FinType :
    FinType <~> {A : Type & Finite A}.
  Proof.
    srapply @equiv_adjointify.
    - intros [n A]. exists A. exact _.
    - intros [A [n e]]. exact (Build_FinType n (A; e)).
    - intros [A [n e]]. simpl.
      apply path_sigma_hprop. reflexivity.
    - intros [n A]. simpl. reflexivity.
  Defined.

  Global Instance istrunc_FinType : IsTrunc 1 FinType.
  Proof.
    apply (trunc_equiv' {S : Type & Finite S}).
    - apply equiv_inverse. apply issig_FinType.
    - apply trunc_sigma'.
      +  intro A. exact _.
      +  intros A B.
         srapply @istrunc_paths_Type. 
         apply isset_Finite. exact B.2.
  Defined.

  Definition fin_to_FinType {n : nat}
    : Finite_Types n -> FinType
    := Build_FinType n.

  (** Canonical objects in FinType*)
  Definition canon_FinType (n : nat) : FinType := fin_to_FinType (canon n).

  Lemma finite_types_eqcard {m n : nat} (A : Finite_Types m) (B : Finite_Types n) :
    A <~> B -> m = n.
  Proof.
    destruct A as [A fA]. destruct B as [B fB]. simpl. intro e.
    strip_truncations.
    apply nat_eq_fin_equiv.
    exact (fB oE e oE (equiv_inverse fA)).
  Qed.

  (** Describing the path types in FinType.  *)
  Definition inv_path_FinType {A B : FinType}
    : A = B -> A <~> B.
  Proof.
    intros []. exact equiv_idmap.
  Defined.

  Definition equiv_path_FinType (A B : FinType) :
    (A <~> B) <~> A = B.
  Proof.
    refine ((equiv_ap issig_FinType A B)^-1 oE _).
    exact (equiv_path_finite_types' (issig_FinType A) (issig_FinType B) ).
  Defined.


  Definition inv_equiv_path_FinType (A B : FinType) : 
    (equiv_inverse (equiv_path_FinType A B)) == inv_path_FinType.
  Proof.
    intros []. reflexivity.
  Defined.

  Definition path_FinType (A B : FinType) : A <~> B -> A = B
    := equiv_path_FinType A B.

  Definition path_FinType_1 (A : FinType) :
    path_FinType _ _ (equiv_idmap A) = idpath.
  Proof.
    unfold path_FinType. unfold equiv_path_FinType. ev_equiv.
    apply moveR_equiv_V. unfold equiv_path_finite_types'. ev_equiv.
    apply moveR_equiv_M. simpl.
    apply (moveR_equiv_M (f := equiv_path_universe _ _)). reflexivity.
  Defined.

  Definition path_FinType_V {A B : FinType} (e : A <~> B)
    : (path_FinType _ _ e)^ = path_FinType _ _ (equiv_inverse e).
  Proof.
    refine (_ @ ap (fun g => path_FinType B A (equiv_inverse g)) (eissect (@path_FinType A B) e)).
    generalize (path_FinType A B e).  intros [].
    simpl. apply inverse.
    refine (_ @ path_FinType_1 A).
    apply (ap (path_FinType _ _)).
    apply path_equiv. simpl.  reflexivity.
  Defined.

  Definition pft_to_pbs {m : nat} {A B : Finite_Types m}
    : A = B -> (fin_to_FinType A) = (fin_to_FinType B) 
    := ap (fin_to_FinType).

  Definition path_FinType_fix {m : nat} (A B : Finite_Types m) (e : A <~> B)
    : pft_to_pbs (path_finite_types m A B e)
      = @path_FinType (fin_to_FinType A) (fin_to_FinType B) e.
  Proof.
    refine (_ @ ap (@path_FinType
                      (fin_to_FinType _)
                      (fin_to_FinType _))
              (eissect (path_finite_types m A B) e)).
    generalize (path_finite_types m A B e).
    intros []. simpl.
    refine ((path_FinType_1 _)^).
  Defined.

  Global Instance isequiv_pft_to_pbs {m : nat} {A B : Finite_Types m}
    : IsEquiv (@pft_to_pbs m A B).
  Proof.
    assert (H : @pft_to_pbs m A B
            = equiv_path_FinType
                (fin_to_FinType A) (fin_to_FinType B)
                oE (equiv_path_finite_types m A B)^-1).
    { apply path_arrow. intros []. ev_equiv.
      apply inverse.
      refine (path_FinType_1 _). }
    rewrite H.
    apply equiv_isequiv.
  Qed.

  (** path_FinType respects composition *)  
  Definition path_FinType_compose {A B C : FinType} (e1 : A <~> B) (e2 : B <~> C) :
    path_FinType _ _ (e2 oE e1) = path_FinType _ _ e1 @ path_FinType _ _ e2.
  Proof.
    refine
      (ap011 (fun g1 g2 => path_FinType A C (g2 oE g1))
             (eissect (path_FinType A B) e1)^ (eissect (path_FinType B C) e2)^ @ _).
    generalize (path_FinType _ _ e2). intros []. 
    generalize (path_FinType _ _ e1). intros []. simpl.
    refine (path_FinType_1 A).
  Qed.
    

  Definition sum_FinType : FinType -> FinType -> FinType.
  Proof.
    intros [m A] [n B].
    exact (fin_to_FinType (sum_finite_types A B)).
  Defined.

  Definition FinType_id : FinType := canon_FinType 0.

  Local Notation "S1 ⊕ S2" := (sum_FinType S1 S2) (at level 50, no associativity).


  (** path_FinType behaves well with respect to sum *)
  Lemma path_FinType_sum (A1 A2 B1 B2 : FinType)
        (e1 : A1 <~> B1) (e2  : A2 <~> B2)
    : path_FinType (sum_FinType A1 A2) (sum_FinType B1 B2) (e1 +E e2)
      = ap011 sum_FinType (path_FinType _ _ e1) (path_FinType _ _ e2).
  Proof.
    rewrite (ap011 equiv_functor_sum'
                   (eissect (equiv_path_FinType A1 B1) e1)^ (eissect (equiv_path_FinType A2 B2) e2)^).
    change ((equiv_path_FinType ?A ?B) ?e) with (path_FinType A B e).
    destruct (path_FinType A1 B1 e1). destruct (path_FinType A2 B2 e2).
    simpl.
    refine (_ @ path_FinType_1 _).
    apply (ap (path_FinType _ _)).
    apply path_equiv. apply path_arrow.
    intros [a | a]; reflexivity.
  Defined.
  
  
  Definition finsum_id (m n : nat) :
    sum_FinType (canon_FinType m) (canon_FinType n) = canon_FinType (n+m)
    :=  path_FinType (sum_FinType (canon_FinType m) (canon_FinType n)) (canon_FinType (n+m))
                     (equiv_finsum m n).

  Definition finsum_id_fix (m n : nat)
    : sum_finite_types (canon m) (canon n) = canon (n + m)
    := path_finite_types _ (sum_finite_types (canon m) (canon n)) (canon (n+m)) (equiv_finsum m n).



  Definition path_FinType_blocksum {a b : nat}
             (alpha : canon_FinType a <~> canon_FinType a)
             (betta : canon_FinType b <~> canon_FinType b)
    : path_FinType (canon_FinType (a +' b)) (canon_FinType (a +' b)) (block_sum alpha betta) =
      (finsum_id a b)^ @ (ap011 sum_FinType (path_FinType _ _ alpha) (path_FinType _ _ betta) @
                                finsum_id a b).
  Proof.
    unfold finsum_id.
    rewrite <- path_FinType_sum.
    rewrite path_FinType_V.
    rewrite <- path_FinType_compose. rewrite <- path_FinType_compose.
    reflexivity.
  Defined.

  Definition natural_path_FinType_l {S1 S2 S3: FinType} (e : S1 <~> S2)
    : ap (fun x : FinType => x ⊕ S3) (path_FinType _ _ e)
    = path_FinType (S1 ⊕ S3) (S2 ⊕ S3) (equiv_functor_sum_r (B := S3) e).
  Proof.    
    refine (_ @ ap (fun e' => @path_FinType (S1⊕ S3) (S2 ⊕ S3) (equiv_functor_sum_r e'))
              (eissect (@path_FinType S1 S2) e)).
    generalize (path_FinType _ _ e). intros [].
    simpl. apply inverse.
    refine (_ @ path_FinType_1 (S1 ⊕ S3)).
    apply (ap (path_FinType _ _)).
    apply path_equiv. apply path_arrow. intros [s1 | s3]; reflexivity.
  Qed.

  Definition natural_path_FinType_r {S1 S2 S3: FinType} (e : S2 <~> S3)
    : ap (fun x : FinType => S1 ⊕ x) (path_FinType _ _ e)
      = path_FinType (S1 ⊕ S2) (S1 ⊕ S3) (equiv_functor_sum_l (A := S1) e).
  Proof.
    refine (_ @ ap (fun e' => @path_FinType (S1 ⊕ S2) (S1 ⊕ S3) (equiv_functor_sum_l e'))
              (eissect (@path_FinType S2 S3) e)).
    generalize (path_FinType _ _ e). intros [].
    simpl. apply inverse.
    refine (_ @ path_FinType_1 (S1 ⊕ S2)).
    apply (ap (path_FinType _ _)).
    apply path_equiv. apply path_arrow. intros [s1 | s2]; reflexivity.
  Qed.

  
  (** The monoidal structure on FinType*)
  Definition FinType_assoc : associative sum_FinType.
  Proof.
    intros S1 S2 S3.
    apply path_FinType.
    apply equiv_sum_assoc'. 
  Defined.

  Definition FinType_lid : left_identity_mult sum_FinType (canon_FinType 0).
  Proof.
    intro S. apply path_FinType.
    apply sum_empty_l.
  Defined.
  
  Definition FinType_rid : right_identity_mult sum_FinType (canon_FinType 0).
  Proof.
    intro S. apply path_FinType.
    apply sum_empty_r.
  Defined.

  Definition FinType_symmetric : symmetric sum_FinType. 
  Proof.
    intros S1 S2. apply path_FinType. apply equiv_sum_symm.
  Defined.

  Definition FinType_symsym : forall (a b : FinType), FinType_symmetric a b = (FinType_symmetric b a)^.
  Proof.
    intros A B.
    unfold FinType_symmetric.
    rewrite path_FinType_V.
    apply (ap (path_FinType _ _)).
    apply path_equiv. apply path_arrow.
    intros [a | b]; reflexivity.
  Qed.    
  
  Definition FinType_triangle1 : coherence_triangle1 FinType_assoc FinType_lid.
  Proof.
    intros S1 S2.
    unfold FinType_lid.
    refine (natural_path_FinType_l _ @ _).
    unfold FinType_assoc.
    refine (_ @ (path_FinType_compose _ _)).
    apply (ap (path_FinType _ _)).
    apply path_equiv. apply path_arrow.
    intros [[[] | s1] | s2]; reflexivity.
  Qed.

  Definition FinType_triangle2 : coherence_triangle2 FinType_assoc FinType_lid FinType_rid.
  Proof.
    intros S1 S2. unfold FinType_rid. unfold FinType_assoc. unfold FinType_lid. simpl.
    refine (natural_path_FinType_l _ @ _).
    refine (_ @ whiskerL _ (natural_path_FinType_r _)^).
    refine (_ @ (path_FinType_compose  _ _)).
    apply (ap (path_FinType _ _)).
    apply path_equiv. apply path_arrow.
    intros [[s1 | []] | s2]; reflexivity.
  Qed.
  
  Definition FinType_pentagon : coherence_pentagon FinType_assoc.
  Proof.
    intros S1 S2 S3 S4.
    refine (natural_path_FinType_l _  @ _).
    apply moveL_pV.
    refine ((path_FinType_compose _ _)^ @ _).
    apply moveL_pV.
    refine (whiskerL _ (natural_path_FinType_r _) @ _).
    refine ((path_FinType_compose _ _)^ @ _).
    refine (_ @ (path_FinType_compose _ _)).
    apply (ap (path_FinType _ _)).
    apply path_equiv. apply path_arrow.
    intros [[[s1 | s2]| s3] | s4]; reflexivity.
  Defined.

  Definition FinType_hexagon : coherence_hexagon FinType_assoc FinType_symmetric.
  Proof.
    intros A B C.
    refine (natural_path_FinType_l _  @ _).
    apply moveL_pV. apply moveL_pV.
    refine (whiskerL _ (natural_path_FinType_r _) @ _).
    rewrite <- path_FinType_compose.
    rewrite <- path_FinType_compose.
    rewrite <- path_FinType_compose.
    rewrite <- path_FinType_compose.
    apply (ap (path_FinType _ _)).
    apply path_equiv. apply path_arrow.
    intros [[a | b] | c]; reflexivity.
  Defined.


  (** A couple auxiliary lemmas. *)
  Definition isinj_functor_sum {A1 A2 B1 B2 : Type} (f1 f1' : A1 -> B1) (f2 f2': A2 -> B2) :
    functor_sum f1 f2 = functor_sum f1' f2' -> (f1 = f1') * (f2 = f2').
  Proof.
    intro p.
    set (p' := ap10 p).
    apply pair.
    - apply path_arrow. intro a.
      apply (path_sum_inl B2). exact (p' (inl a)).
    - apply path_arrow. intro a.
      apply (path_sum_inr B1). exact (p' (inr a)).
  Defined.

  Definition isinj_equiv_functor_sum_r {A1 A2 B : Type} (e1 e2 : A1 <~> A2) :
    equiv_functor_sum_r (B := B) e1 = equiv_functor_sum_r e2 -> e1 = e2.
  Proof.
    intro p. apply path_equiv.
    refine (fst ((isinj_functor_sum e1 e2 idmap idmap) _)).
    apply (path_equiv^-1 p).
  Defined.    

  (** FinType has left cancellation  *)
  Definition FinType_lcancel (S1 S2 : FinType) (p q : S1 = S2) (T : FinType) :
    ap (fun x => x ⊕ T) p = ap (fun x => x ⊕ T) q -> p = q.
  Proof.
    intro h.
    apply (equiv_inj (@path_FinType S1 S2)^-1).
    apply (isinj_equiv_functor_sum_r (B:=T)
                                     ((equiv_path_FinType _ _)^-1 p) ((equiv_path_FinType _ _)^-1 q)) .
    apply (equiv_inj (@path_FinType (S1 ⊕ T) (S2 ⊕ T))).
    refine ((natural_path_FinType_l _)^ @ _ @ natural_path_FinType_l _).
    refine (_ @ h @ _);
      apply (ap (ap (fun x : FinType => x ⊕ T))).
      - apply eisretr.
      - apply inverse. apply eisretr.
  Defined.

  (** FinType is a symmetric monoidal category  *)
  Definition FinType_smoncat : Symmetric_Monoidal_1Type :=
    Build_Symmetric_Monoidal_1Type
      (BuildTruncType 1 FinType) sum_FinType (canon_FinType 0) FinType_assoc
      FinType_lid FinType_rid FinType_symmetric FinType_symsym
      FinType_triangle1 FinType_triangle2 FinType_pentagon FinType_hexagon.
End FinType.

From GCTT Require Import monoids_and_groups.
Section Assoc_Nat_to_Assoc_FinType.
  (** Now we prove that associativity of sum_FinType on canonical finite types correspond to
   associativity of natural numbers. *)

  Definition equiv_sum_assoc_Fin (j k l : nat)
    : (Fin l + Fin k) + Fin j <~>
       Fin l + (Fin k + Fin j).
  Proof.
    induction j.
    - refine (_ oE sum_empty_r _).
      apply (equiv_functor_sum_l (sum_empty_r _)^-1).
    - simpl.
      refine (_ oE (equiv_functor_sum' IHj (equiv_idmap Unit)) oE _).
      + refine (_ oE equiv_sum_assoc _ _ _).
        apply equiv_functor_sum_l. apply equiv_sum_assoc.
      + 
        refine (_ oE (equiv_sum_assoc _ _ _)^-1 ). apply equiv_idmap.
  Defined.

  Definition id_equiv_sum_assoc_Fin (j k l : nat)
    : equiv_sum_assoc (Fin l) (Fin k) (Fin j) = equiv_sum_assoc_Fin j k l.
  Proof.
    induction j.
    - simpl. apply path_equiv. apply path_arrow.
      intros [[x | x] | []]; reflexivity.
    - simpl. rewrite <- IHj.
      apply path_equiv. apply path_arrow.
      intros [[x | x] | [x | []]]; reflexivity.
  Defined.
  
  Definition sum_canon_FinType (j k : nat) :
    sum_FinType (canon_FinType j) (canon_FinType k) = canon_FinType (k + j)%nat.
  Proof.
    srapply @path_FinType. apply equiv_finsum.
  Defined.

  Definition canon_assoc (a b c : nat)
    : Fin (a + (b + c)) <~> Fin ((a + b) + c ).
  Proof.
    refine (_ oE (equiv_finsum _ _)^-1).
    refine (_ oE (equiv_functor_sum_r (equiv_finsum _ _))^-1).
    refine (_ oE ((equiv_sum_assoc' _ _ _))).
    refine (equiv_finsum _ _ oE _).
    apply (equiv_functor_sum_l (equiv_finsum _ _)).
  Defined.

  Definition equiv_functor_sum_r_compose
    : forall (A A1 A2 B : Type)
             (e1 : A <~> A1)
             (e2 : A1 <~> A2),
      equiv_functor_sum_r (B := B) (e2 oE e1)
      = equiv_functor_sum_r (B:= B) e2 oE equiv_functor_sum_r (B := B) e1.
  Proof.
    intros. apply path_equiv. apply path_arrow.
    intros [x | x]; reflexivity.
  Defined.

  Definition equiv_finsum_succ (a b : nat)
    : equiv_finsum a (b.+1) = equiv_functor_sum_r (equiv_finsum a b) oE (equiv_sum_assoc' _ _ _)^-1.
  Proof.
    apply path_equiv. apply path_arrow.
    intro x. simpl. apply finsum_succ.
  Defined.

  (** More auxiliary results  *)
  Definition functor_sum_assoc {A B C A' B' C' : Type} (f : A -> A') (g : B -> B') (h : C -> C')
    : functor_sum (functor_sum f g) h  o (sum_assoc_inv _ _ _) ==
      sum_assoc_inv _ _ _  o (functor_sum f (functor_sum g h)).
  Proof.
    intros [a | [b | c]]; reflexivity.
  Defined.

  Definition functor_sum_idmap (A B: Type)
    : @functor_sum A A B B idmap idmap == idmap.
  Proof.
    intros [a | b]; reflexivity.
  Defined.

  Definition functor_sum_compose {A A1 A2 B B1 B2 : Type}
             (f1 : A -> A1) (f2 : A1 -> A2)
             (g1 : B -> B1) (g2 : B1 -> B2)
    : functor_sum (f2 o f1) (g2 o g1) == functor_sum f2 g2 o functor_sum f1 g1.
  Proof.
    intros [a | b]; reflexivity.
  Defined.

    Definition equiv_functor_sum_r_V (A A' B : Type) (e : A <~> A')
    : equiv_functor_sum_r (B := B) (e^-1) = equiv_inverse (equiv_functor_sum_r e).
  Proof.
    apply path_equiv. reflexivity.
  Defined.

  Definition canon_assoc_succ (a b c : nat)
    : canon_assoc (a.+1) b c
      = equiv_functor_sum_r (canon_assoc a b c).
  Proof.    
    unfold canon_assoc. simpl.
    apply emoveR_eV. apply emoveR_eV.
    rewrite equiv_finsum_succ. rewrite equiv_finsum_succ.
    rewrite equiv_finsum_succ.
    repeat rewrite equiv_functor_sum_r_compose.
    repeat rewrite equiv_functor_sum_r_V.
    apply path_equiv. apply path_arrow. intro x. ev_equiv. simpl.
    apply (ap (equiv_functor_sum_r (equiv_finsum c (a + b)))).
    rewrite <- (functor_sum_compose (finsum (b + c) a) (finsum_inv (b + c) a) idmap idmap).
    change (finsum_inv ?x ?y) with ((equiv_finsum x y)^-1).
    change (finsum ?x ?y ?z) with (equiv_finsum x y z).
    rewrite (path_arrow _ _ (eissect (equiv_finsum (b + c) a))).
    rewrite functor_sum_idmap.  simpl.
    rewrite functor_sum_assoc.
    rewrite <- (functor_sum_compose (finsum c b) (finsum_inv c b) idmap (functor_sum idmap idmap)).
    change (finsum_inv c b) with ((equiv_finsum c b)^-1).
    change (finsum c b ?x) with (equiv_finsum c b x).
    rewrite (path_arrow _ _ (eissect (equiv_finsum c b))).    
    destruct x as [[x | x] | [x | x]]; reflexivity.
  Defined.
      
  Definition canon_FinType_assoc (a b c : nat) :
    canon_FinType (a + (b + c))%nat = canon_FinType ((a + b) + c)%nat.
  Proof.
    apply path_FinType. exact (canon_assoc a b c).
  Defined.
    
  (** Associativity in nat and FinType correspond  *)
  Definition eq_canon_FinType_assoc (a b c : nat)
    : canon_FinType_assoc a b c = ap canon_FinType (nat_plus_assoc a b c)^.
  Proof.
    unfold canon_FinType_assoc.
    induction a.
    - simpl. unfold canon_assoc.
      refine (_ @ path_FinType_1 _).
      apply (ap (path_FinType _ _)).
      apply emoveR_eV.
      refine (_ @ (ecompose_1e _)^).
      apply emoveR_eV.
      apply path_equiv. apply path_arrow.
      intros [[x | x] | []]; reflexivity.
    - rewrite canon_assoc_succ.
      simpl.
      assert (H : forall (m n : nat) (p : m = n),
                 ap canon_FinType (ap S p)
                 = @path_FinType (canon_FinType (m.+1)) (canon_FinType (n.+1))
                     (equiv_functor_sum_r
                        (B := Unit)
                        ((equiv_path_FinType (canon_FinType (m)) (canon_FinType (n)))^-1
                                      (ap canon_FinType p)))).
      { intros m n []. simpl.
        apply inverse. refine (_ @ path_FinType_1 _).
        apply (ap (path_FinType _ _)). apply path_equiv. simpl. apply path_arrow.
        intros [x|x]; reflexivity. }
      rewrite <- ap_V.
      rewrite H. clear H.
      apply (ap (path_FinType _ _)). apply (ap equiv_functor_sum_r).
      apply moveL_equiv_V.
      apply IHa.
  Qed.
End Assoc_Nat_to_Assoc_FinType.  

(** Would have been better to define this stuff before doing all the above, but but.*)
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
    


From GCTT Require Import  quotients group_complete_category.

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
  : morphism _ (sum_group_complete_isofin (sum_group_complete_isofin (A1, A2), A3) )
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

  









