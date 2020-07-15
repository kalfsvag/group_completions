Require Import HoTT.

From A_BPQ Require Import
     conn_ptype finite_types monoids_and_groups delooping permutations sign fintype_monoidal.

(** First we name a few results we already have proven. *)
Definition iso_path_finite_types (m : nat)
  : Isomorphism (SymGrp m) (loopGroup (Finite_Types m) (canon m)).
Proof.
  srapply Build_Grp_Iso'.
  - simpl. apply (equiv_path_finite_types m (canon m) (canon m)).
  - intros alpha beta. simpl.
    apply (path_finite_types_compose m (canon m) (canon m) (canon m) alpha beta).
Defined.

Definition equiv_functor_hom_fin (m n : nat)
  : Homomorphism (SymGrp m) (SymGrp n) <~> Homomorphism (loopGroup (pFin m) (canon m))
                                                        (loopGroup (pFin n) (canon n)).
Proof.
  apply equiv_functor_hom'; apply iso_path_finite_types.
Defined.  

Definition deloop_fin (m n : nat)
  : Homomorphism (SymGrp m) (SymGrp n) -> pMap(pFin m) (pFin n).
Proof.
  intro f. apply (functor_deloop (pFin m) (pFin n)).
  apply (equiv_functor_hom_fin m n). exact f.
Defined.

Definition deloop_fin_canon (m n : nat) (f : Homomorphism (SymGrp m) (SymGrp n))
  : deloop_fin m n f (canon m) = canon n.
Proof.
  apply (point_eq (deloop_fin m n f)).
Defined.

Definition deloop_fin_loop (m n : nat) (f : Homomorphism (SymGrp m) (SymGrp n))
           (ω : canon m = canon m)
  : loops_functor (deloop_fin m n f) ω
    = (functor_hom
         (iso_inv (iso_path_finite_types m))
         (iso_path_finite_types n) f) ω.
Proof.  
  apply functor_deloop_loop.
Defined.


Definition sgnhom (m : nat) : Homomorphism (SymGrp m) (SymGrp 2).
Proof.
  srapply @Build_GrpHom.
  + apply sign.
  + apply sgn_compose.
Defined.

Definition Bsign (m : nat) :=
  deloop_fin m 2 (sgnhom m).

Definition Bsign_uncurry : FinType -> Finite_Types 2.
Proof.
  intros [a A]. exact (Bsign a A).
Defined.




