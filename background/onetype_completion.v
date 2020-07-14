Require Import HoTT.
Require Import Categories.Functor Category.Morphisms.
Require Import Category.Core.
From A_BPQ Require Import quotients categories.
From A_BPQ Require Import cquot cquot_principles.

(* The definition of the 1type-completion is in the folder cquot *)

(** The functor given by the constructors of cquot *)
Definition include_in_cquot (C : PreCategory)
  : Functor C (Core.groupoid_category (cquot C)).
Proof.
  srapply @Build_Functor.
  - apply ccl.
  - apply ccleq.
  - apply cconcat.
  - apply ce.
Defined.

Definition functor_groupoid_category
           (X Y : Type) {istrunc_X : IsTrunc 1 X} {istrunc_Y : IsTrunc 1 Y}
  : (X -> Y) -> Functor (Core.groupoid_category X) (Core.groupoid_category Y).
Proof.
  intro f.
  srapply @Build_Functor.
  + exact f.
  + intros x1 x2. simpl. exact (ap f).
  + intros x1 x2 x3 p1 p2. simpl in *.
    apply ap_pp.
  + reflexivity.
Defined.

(** The universal principle of the 1-type completion *)
Definition univ_cquot (C : PreCategory) (Y : Type) {istrunc_Y : IsTrunc 1 Y}
  : (cquot C -> Y) <~> Functor C (Core.groupoid_category Y).
Proof.
  srapply @equiv_adjointify.
  - intro f.
    refine (_ o (include_in_cquot C))%functor.
    apply functor_groupoid_category. exact f.
  - intro F.
    srapply @cquot_rec.
    + exact (object_of F).
    + apply (morphism_of F). 
    + apply (identity_of F).
    + apply (composition_of F).
  - intro F.
    srapply @path_functor'.
    + reflexivity.
    + cbn.  
      intros a b f. rewrite concat_p1. rewrite concat_1p.
      apply cquot_rec_beta_ccleq.
  - intro F. apply path_arrow. intro x. revert x.
    srapply @cquot_ind_set.
    + intro c. simpl. reflexivity.
    + intros c1 c2 f. simpl.
      apply path_to_path_over.
      refine (transport_paths_FlFr _ _ @ _).
      simpl. rewrite concat_p1.
      apply moveR_Vp. rewrite concat_p1.
      apply inverse.
      refine (cquot_rec_beta_ccleq _ _ _ _ _ _ _ _ _ _).
Defined.


Definition functor_cquot {C D : PreCategory}
  : Functor C D -> (cquot C -> cquot D).
Proof.
  intro F.
  apply (univ_cquot _ _)^-1.
  refine (include_in_cquot _ o F)%functor.
  (* srapply @cquot_rec. *)
  (* - intro c. apply ccl. exact (F c). *)
  (* - intros c1 c2 f. simpl. *)
  (*   apply ccleq. apply (morphism_of F). exact f. *)
  (* - intro c. simpl. *)
  (*   rewrite identity_of. apply ce. *)
  (* - intros c1 c2 c3 f g. simpl. *)
  (*   rewrite composition_of. apply cconcat. *)
Defined.

(** Computational rules  *)
Definition univ_cquot_beta_ccleq {C : PreCategory}
           (Y : Type) {istrunc_Y : IsTrunc 1 Y}
           (F : Functor C (Core.groupoid_category Y))
           {c1 c2 : C} (f : morphism C c1 c2)             
  : ap ((univ_cquot C Y)^-1 F) (ccleq C f) = (morphism_of F f).
Proof.
  unfold univ_cquot. simpl.
  apply cquot_rec_beta_ccleq.
Defined.             

Definition functor_cquot_beta_ccleq {C D : PreCategory}
           (F : Functor C D)
           {c1 c2 : C} (f : morphism C c1 c2)
  : ap (functor_cquot F) (ccleq C f) =
    ccleq D (morphism_of F f).
Proof.
  unfold functor_cquot.
  apply univ_cquot_beta_ccleq.
Defined.


(** The 1-type completion preserves set truncation.  *)
Definition pi0_cat_cquot (C : PreCategory) :
  pi0_cat C <~> Trunc 0 (cquot C).
Proof.
  srapply @equiv_adjointify.
  - srapply @set_quotient_rec.
    + intro c. apply tr. apply (ccl C c).
    + simpl. intros x y f.
      apply (ap tr).
      apply ccleq. exact f.
  - srapply @Trunc_rec.
    srapply @cquot_rec.
    + apply class_of.
    + intros c d f.
      apply related_classes_eq. exact f.
    + simpl. intro c.
      apply set_quotient_set.
    + simpl. intros.
      apply set_quotient_set.
  - intro x. revert x.
    srefine (Trunc_ind _ _).
    srefine (cquot_ind_prop _ _ _).
    simpl. reflexivity.
  - intro x. revert x.
    srefine (set_quotient_ind_prop _ _ _).
    simpl. reflexivity.
Defined.