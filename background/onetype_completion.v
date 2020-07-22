Require Import HoTT.
Require Import Categories.Functor Category.Morphisms.
Require Import Category.Core.
From A_BPQ Require Import quotients categories.
From A_BPQ Require Export cquot cquot_principles.

(** The definition of the 1type-completion is in the folder cquot. We change the notation here so that it matches the thesis. *)
Notation "'N1'" := cquot.
Notation "'N1_rec'" := cquot_rec.
Notation "'N1_ind'" := cquot_ind.
Notation "'N1_ind_set'" := cquot_ind_set.

(** A simplified version of N1_rec where we don't need to specify that identities are preserved  *)
Definition N1_rec' {C : PreCategory} (Y : Type)
             (cclY : C -> Y)
             (ccleqY : forall {a₁ a₂ : C},
                 C a₁ a₂ -> cclY a₁ = cclY a₂)
             (* (ceY : forall (a : C), ccleqY (identity a) = idpath) *)
             (cconcatY : forall (a₁ a₂ a₃: C) (c₁: C a₁ a₂) (c₂: C a₂ a₃),
                 ccleqY (c₂ o c₁)%morphism = ccleqY c₁ @ ccleqY c₂)
             {truncY : IsTrunc 1 Y}
  : N1 C -> Y.
  Proof.
    refine (N1_rec Y cclY ccleqY _ cconcatY).
    intro c.
    apply (cancelL (ccleqY c c 1%morphism)).
    refine ((cconcatY c c c _ _)^ @ _).
    refine (ap (ccleqY c c) (left_identity C c c _) @ _).
    apply inverse. apply concat_p1.
  Defined.


(** The functor given by the constructors of N1 *)
Definition include_in_N1 (C : PreCategory)
  : Functor C (Core.groupoid_category (N1 C)).
Proof.
  srapply @Build_Functor.
  - apply ccl.
  - apply ccleq.
  - apply cconcat.
  - apply ce.
Defined.

(** N1 is functorial *)
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
Definition univ_N1 (C : PreCategory) (Y : Type) {istrunc_Y : IsTrunc 1 Y}
  : (N1 C -> Y) <~> Functor C (Core.groupoid_category Y).
Proof.
  srapply @equiv_adjointify.
  - intro f.
    refine (_ o (include_in_N1 C))%functor.
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


Definition functor_N1 {C D : PreCategory}
  : Functor C D -> (N1 C -> N1 D).
Proof.
  intro F.
  apply (univ_N1 _ _)^-1.
  refine (include_in_N1 _ o F)%functor.
Defined.

(** Computational rules  *)
Definition univ_N1_beta_ccleq {C : PreCategory}
           (Y : Type) {istrunc_Y : IsTrunc 1 Y}
           (F : Functor C (Core.groupoid_category Y))
           {c1 c2 : C} (f : morphism C c1 c2)             
  : ap ((univ_N1 C Y)^-1 F) (ccleq C f) = (morphism_of F f).
Proof.
  unfold univ_N1. simpl.
  apply cquot_rec_beta_ccleq.
Defined.             

Definition functor_N1_beta_ccleq {C D : PreCategory}
           (F : Functor C D)
           {c1 c2 : C} (f : morphism C c1 c2)
  : ap (functor_N1 F) (ccleq C f) =
    ccleq D (morphism_of F f).
Proof.
  unfold functor_N1.
  apply univ_N1_beta_ccleq.
Defined.


(** The 1-type completion preserves set truncation.  *)
Definition pi0_cat_N1 (C : PreCategory) :
  pi0_cat C <~> Trunc 0 (N1 C).
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
