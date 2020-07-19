Require Import HoTT.

From A_BPQ Require Import sigma_lemmas equiv_lemmas conn_ptype categories.
Require Import UnivalenceAxiom.


(** Reverse the notation of plus so that n.+1 = n+1 by definition. *)
Notation "a +' b" := (Peano.plus b a) (at level 50).
(** Change notation since "Fin" is something else in the thesis. *)
Notation "'fintype'" := Fin. 

Definition equiv_fin2_bool : fintype 2 <~> Bool.
Proof.
  srapply @equiv_adjointify.
  { intros [[[] | []] | []].
    - exact true.
    - exact false. }
  { intros  [ | ].
    - exact (inl (inr tt)).
    - exact (inr tt). }
  - intros [ | ] ;reflexivity.
  - intros [[[] | []] | []]; reflexivity.
Defined.


(** The type of decidable propositions is finite *)
Global Instance finite_dprop : Finite DProp.
Proof.
  refine (finite_equiv' (fintype 2) _ _).
  refine (_ oE equiv_fin2_bool).
  apply equiv_inverse. apply equiv_dprop_to_bool.
Qed.


(** Finite types are sets *)
Definition isset_fintype (n : nat) : IsHSet (fintype n).
Proof.
  induction n.
  - exact _.
  - apply hset_sum.
Defined.

Definition isset_Finite `{Funext} (A : Type) :
  Finite A -> IsHSet A.
Proof.
  intros [m finA]. strip_truncations.
  apply (trunc_equiv' (fintype m) finA^-1).
Defined.

Lemma finite_eq_fcard (A B : Type) {fA : Finite A} {fB : Finite B} :
  fcard A = fcard B -> merely (A <~> B).
Proof.
  destruct fA as [m eA]. destruct fB as [n eB].
  strip_truncations. intro p. apply tr. simpl in p. destruct p.
  exact (eB^-1 oE eA).
Qed.

Section Equiv_Finsum.
  (** [fintype] preserves sum  *)
  Definition finl (m n : nat) : fintype m -> fintype (n + m).
  Proof.
    induction n.
    - exact idmap.
    - simpl.
      exact (inl o IHn).
  Defined.

  Definition finr (m n : nat) : fintype n -> fintype (n + m).
  Proof.
    induction n.
    - apply Empty_rec.
    - simpl.
      exact (functor_sum IHn idmap).
  Defined.

  Definition finsum (m n : nat) : fintype m + fintype n -> fintype (n+m).
  Proof.
    intros [i | j].
    - exact (finl _ _ i).
    - exact (finr _ _ j).
  Defined.
  
  Definition finsum_succ (m n : nat)
    : finsum m n.+1 == (functor_sum (finsum m n) idmap) o (sum_assoc_inv _ _ _).
  Proof.
    intros [i | [i | []]]; reflexivity.
  Defined.

  Definition finsum_inv (m n : nat) : fintype (n+m) -> fintype m + fintype n.
  Proof.
    induction n;simpl.
    - exact inl.
    - refine (equiv_sum_assoc' _ _ _ o _).
      exact (functor_sum IHn idmap).
  Defined.

  Global Instance isequiv_finsum {m n : nat} : IsEquiv (finsum m n).
  Proof.
    apply (isequiv_adjointify (finsum m n) (finsum_inv m n)).
    - intro x.
      induction n; try reflexivity. simpl. rewrite finsum_succ.
      refine (ap (functor_sum (finsum m n) idmap) 
                 (eissect
                    (equiv_sum_assoc' (fintype m) (fintype n) Unit)
                    (functor_sum (finsum_inv m n) idmap x)) @ _).
      destruct x as [x | x]; try reflexivity. simpl.
      exact (ap inl (IHn x)).
    - intro x. 
      induction n.
      { simpl. destruct x as [x | []]. reflexivity. }
      refine (_ @ eisretr (equiv_sum_assoc' (fintype m) (fintype n) Unit) x).
      simpl. 
      apply (ap (equiv_sum_assoc _ _ _)). rewrite finsum_succ.
      generalize ((sum_assoc_inv (fintype m) (fintype n) Unit x)). clear x. intro x.
      destruct x as [x | x]; try reflexivity.
      simpl. exact (ap inl (IHn x)).
  Defined.


  Definition equiv_finsum (m n : nat) : (fintype m) + (fintype n) <~> fintype (n + m) :=
    BuildEquiv _ _ (finsum m n) isequiv_finsum.

  Lemma inj_finl {m n : nat} (i j : fintype m) :
    finl m n i = finl m n j -> i = j.
  Proof.
    intro p. apply (path_sum_inl (fintype n)).
    apply (equiv_inj (finsum m n)).  exact p.
  Qed.
  
  Lemma inj_finr {m n : nat} (i j : fintype n) :
    finr m n i = finr m n j -> i = j.
  Proof.
    intro p. apply (path_sum_inr (fintype m)).
    apply (equiv_inj (finsum m n)).  exact p.
  Qed.
End Equiv_Finsum.

Section Finite_Types.
  (** The type of finite types of cardinality n  *)
  Definition Finite_Types  (n : nat) :=
    {A : Type & merely (A <~> fintype n)}.


  Definition type_of {n : nat} (A : Finite_Types n) := pr1 A.
  Global Coercion type_of : Finite_Types >-> Sortclass.
  Global Instance finite_finite_type {n : nat} (A : Finite_Types n) : Finite A := 
    Build_Finite A.1 n A.2.


  (** Canonical finite types *)
  Global Instance canon (n : nat) : IsPointed (Finite_Types n) := (fintype n; tr equiv_idmap).    

  (** A detachable subset of a finite set has smaller cardinal *)
  Definition leq_card_subset {n : nat} (A : Finite_Types n) (P : A -> Type)
             (isprop_P : forall a : A, IsHProp (P a)) (isdec_P : forall a : A, Decidable (P a)) :
    (fcard {a : A & P a} <= fcard A)%nat.
  Proof.  
    destruct A as [A eA]. simpl in P, isprop_P, isdec_P. 
    apply (leq_inj_finite pr1).
    unfold IsEmbedding. simpl. intro a.
    apply (trunc_equiv' (P a) ).
    - apply hfiber_fibration.
    - apply isprop_P.
  Qed.

  (*( Plus one for finite types *)
  Definition add_one {n : nat} : Finite_Types n -> Finite_Types n.+1.
  Proof.
    intros [A H].
    exists (A + Unit).
    (* apply (Build_Finite_Types (A + Unit)). *)
    strip_truncations.
    apply tr. (* apply path_universe_uncurried. *)
    (* exact (equiv_functor_sum' ((equiv_path_universe A (fintype n))^-1 H) equiv_idmap). *)
    exact (equiv_functor_sum' H equiv_idmap).
  Defined.

  Definition sum_finite_types {m n : nat} (A : Finite_Types m) (B : Finite_Types n) :
    Finite_Types (n + m).
  Proof.
    exists (A + B).
    destruct A as [A fA]. destruct B as [B fB]. strip_truncations.
    apply tr. simpl.
    refine (_ oE equiv_functor_sum' fA fB).
    apply equiv_finsum.
  Defined.
End Finite_Types.

Section Path_Finite_Types.
  (** Describing path types in [Finite_Types]   *)
  Definition path_finite_types (n : nat) (s t : Finite_Types n)
    : (s <~> t) -> s = t
    :=  path_sigma_hprop _ _ o path_universe_uncurried.

  Lemma path_finite_types_id (m : nat) (A : Finite_Types m) :
    path_finite_types m A A equiv_idmap = idpath.
  Proof.
    unfold path_finite_types. apply moveR_equiv_M.
    simpl. unfold path_universe_uncurried.
    apply moveR_equiv_V.
    apply path_equiv. reflexivity.
  Defined.
  

  Definition inv_path_finite_types (n : nat) (s t : Finite_Types n)
    : (s = t) -> (s <~> t).
  Proof.
    intros []. exact equiv_idmap.
  Defined.

  Global Instance isequiv_path_finite_types (n : nat) (s t : Finite_Types n)
    : IsEquiv (path_finite_types n s t).
  Proof.
    srapply @isequiv_adjointify.
    - apply inv_path_finite_types.
    - intros []. apply path_finite_types_id.
    - unfold Sect. simpl.
      intro f. unfold path_finite_types.
      assert (h : inv_path_finite_types n s t  ==
                  (equiv_inverse (equiv_path_universe s t))
                    o  ((equiv_inverse (equiv_path_sigma_hprop s t)) )).
      { intros []. reflexivity. }
      refine (h ((path_sigma_hprop s t (path_universe_uncurried f))) @ _).
      refine (ap (equiv_path_universe s t)^-1
                 (eissect (path_sigma_hprop s t) (path_universe_uncurried f)) @ _).
      apply eissect.
  Defined.

  Definition equiv_path_finite_types (n : nat) (s t : Finite_Types n)
    : (s <~> t) <~> (s = t)
    := BuildEquiv _ _ (path_finite_types n s t) (isequiv_path_finite_types n s t).

  Definition equiv_path_finite_types' (s t : {A : Type & Finite A}) :
    (s.1 <~> t.1) <~> s = t :=
    equiv_path_sigma_hprop _ _ oE equiv_path_universe _ _.

  Lemma path_finite_types_sum {a1 a2 : nat}
        (A1 : Finite_Types a1) (A2 : Finite_Types a2)
        (B1 : Finite_Types a1) (B2 : Finite_Types a2)
        (e1 : A1 <~> B1) (e2 : A2 <~> B2)
    : path_finite_types _ (sum_finite_types A1 A2) (sum_finite_types B1 B2)
                        (e1 +E e2)
      = ap011 sum_finite_types
              (path_finite_types _ _ _ e1)
              (path_finite_types _ _ _ e2).
  Proof.
    revert e1.
    apply (equiv_functor_forall_pf (equiv_path_finite_types _ A1 B1)).
    intro p. revert e2.
    apply (equiv_functor_forall_pf (equiv_path_finite_types _ A2 B2)).
    intro q.
    destruct p. destruct q.
    simpl.
    refine (_ @ path_finite_types_id (a2 + a1) (sum_finite_types A1 A2) @ _).
    - apply (ap (path_finite_types (a2 + a1) (sum_finite_types A1 A2) (sum_finite_types A1 A2))).
      apply path_equiv. apply path_arrow. intros [x | y]; reflexivity.
    - apply inverse.
      apply (ap011 (ap011 sum_finite_types)
                   (path_finite_types_id a1 A1)
                   (path_finite_types_id a2 A2)).
  Defined.

  
  Definition transport_exp_finite_fix (n : nat) {X : Type} {A B : Finite_Types n}
             (e : A <~> B) (x : A -> X)
    : transport (fun I : Finite_Types n => I -> X) (path_finite_types n A B e) x = x o e^-1.
  Proof.
    refine (ap10 (transport_pr1_path_sigma_uncurried (pr1^-1 (path_universe_uncurried e))
                                                     (fun A : Type => A -> X)) x @ _).
    exact (transport_exp X A B e x).
  Defined.


  Definition path_finite_types_V {m : nat} (A B : Finite_Types m) (e : A <~> B)
    : path_finite_types m B A (equiv_inverse e) = (path_finite_types m A B e)^.
  Proof.
    unfold path_finite_types.
    refine (ap (path_sigma_hprop B A)
               (path_universe_V_uncurried e) @ _).
    apply path_sigma_hprop_V.
  Defined.



  Definition transport_exp_finite_sum {X : Type} {A B : {A : Type & Finite A}}
             (e : A.1 <~> B.1) (x : A.1 -> X)
    : transport (fun I : {A : Type & Finite A} => I.1 -> X)
                (equiv_path_finite_types' A B e) x = x o e^-1.
  Proof.
    refine (ap10 (transport_pr1_path_sigma_uncurried (pr1^-1 (path_universe_uncurried e))
                                                     (fun A : Type => A -> X)) x @ _).
    exact (transport_exp X A.1 B.1 e x).
  Defined.
  
  Lemma path_finite_types_compose (m : nat) (A B C : Finite_Types m)
        (e1 : A <~> B) (e2 : B <~> C) :
    path_finite_types m _ _ (e2 oE e1) =
    (path_finite_types m _ _ e1) @ (path_finite_types m _ _ e2).
  Proof.
    unfold path_finite_types. simpl.    
    refine (ap (path_sigma_hprop A C) (path_universe_compose e1 e2) @ _).
    apply path_sigma_hprop_compose.
  Defined.

End Path_Finite_Types.

Global Instance istrunc_finite_types {m : nat} : IsTrunc 1 (Finite_Types m).
Proof.
  intros x y.
  change (IsTrunc_internal 0) with IsHSet.
  apply (trunc_equiv' (x <~> y)).
  - apply equiv_path_finite_types.
  - apply istrunc_equiv.
Qed.

Definition sum_finite_types_canon {m n : nat} :
  sum_finite_types (canon m) (canon n) = canon (n + m).
Proof.
  apply path_finite_types. simpl.
  apply equiv_finsum.
Defined.

Lemma isconn_finite_types (m : nat) :
  forall x : Finite_Types m,
    merely (canon m = x).
Proof.
  intros [A fA]. strip_truncations.
  apply tr. apply inverse. apply path_finite_types.
  exact fA.
Qed.

Definition pFin (m : nat) : Conn_pType.
Proof.
  apply (Build_Conn_pType (Build_pType (Finite_Types m) _)).
  intro x.
  apply (isconn_finite_types m x).
Defined.











