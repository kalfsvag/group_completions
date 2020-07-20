(** This file was originally written by Niels van der Weide and Dan Frumin, with only minor changes here. Namely, that we generalize the construction for all categories, and not only for groupoids.*)

Require Import HoTT.
From A_BPQ Require Import
     general.
From A_BPQ.cquot.basics Require Export
     globe_over path_over square.
Require Import cquot.

From HoTT.Categories Require Import
     Functor GroupoidCategory Category  .

Section cquot_rec.
  Variable (C : PreCategory)
           (Y : Type)
           (cclY : C -> Y)
           (ccleqY : forall {a₁ a₂ : C},
               C a₁ a₂ -> cclY a₁ = cclY a₂)
           (ceY : forall (a : C), ccleqY (identity a) = idpath)
           (cconcatY : forall (a₁ a₂ a₃: C) (c₁: C a₁ a₂) (c₂: C a₂ a₃),
               ccleqY (c₂ o c₁) = ccleqY c₁ @ ccleqY c₂)
           (truncY : IsTrunc 1 Y).

  Definition cquot_rec : cquot C -> Y.
  Proof.
    simple refine (cquot_ind (fun _ => Y)
                             cclY
                             (fun a₁ a₂ c => const_path_over (@ccleqY a₁ a₂ c))
                             (fun a => const_globe_over
                                         (path_to_globe (ce C a))
                                         (@ccleqY a a (identity a))
                                         idpath
                                         (path_to_globe (ceY a)))
                             _ _) ; cbn.
    intros a₁ a₂ a₃ c₁ c₂.
    simple refine (globe_over_whisker
                     (fun _ => Y)
                     _
                     idpath
                     (const_path_over_concat _ _)
                     (const_globe_over
                        (path_to_globe (cconcat C c₁ c₂))
                        (@ccleqY a₁ a₃ (c₂ o c₁))
                        (@ccleqY a₁ a₂ c₁ @ (@ccleqY a₂ a₃ c₂))
                        (path_to_globe (cconcatY a₁ a₂ a₃ c₁ c₂))
                     )
                  ).
  Defined.

  Definition cquot_rec_beta_ccleq (a₁ a₂ : C) (c : C a₁ a₂)
    : ap cquot_rec (ccleq C c) = @ccleqY a₁ a₂ c.
  Proof.
    apply (const_path_over_inj (ccleq C c)).
    refine ((apd_po_const _ _)^ @ _).
    apply cquot_ind_beta_ccleq.
  Qed.
End cquot_rec.

Arguments cquot_rec {C} Y cclY ccleqY ceY cconcatY {truncY}.

(** If the we have a family of sets, then we can simplify the induction principle. *)
Section cquot_ind_set.
  Variable (C : PreCategory)
           (Y : cquot C -> Type)
           (cclY : forall (a : C), Y(ccl C a))
           (ccleqY : forall (a₁ a₂ : C) (c : C a₁ a₂),
               path_over Y (ccleq C c) (cclY a₁) (cclY a₂))
           (truncY : forall (x : cquot C), IsHSet (Y x)).

  Definition cquot_ind_set : forall (c : cquot C), Y c.
  Proof.
    simple refine (cquot_ind Y cclY ccleqY _ _ _)
    ; intros ; apply path_globe_over_hset ; apply _.
  Defined.

  Definition cquot_ind_set_beta_ccl (a : C)
    : cquot_ind_set (ccl C a) = cclY a
    := idpath.

  Definition cquot_ind_set_beta_ccleq : forall (a₁ a₂ : C) (c : C a₁ a₂),
      apd_po cquot_ind_set (ccleq C c)
      =
      ccleqY a₁ a₂ c.
  Proof.
    apply cquot_ind_beta_ccleq.
  Qed.
End cquot_ind_set.

Arguments cquot_ind_set {C} Y cclY ccleqY truncY.

(** If the we have a family of propositions, then we can simplify the induction principle. *)
Section cquot_ind_prop.
  Variable (C : PreCategory)
           (Y : cquot C -> Type)
           (cclY : forall (a : C), Y(ccl C a)).
  Context `{forall (x : cquot C), IsHProp (Y x)}.

  Definition cquot_ind_prop : forall (c : cquot C), Y c.
  Proof.
    simple refine (cquot_ind_set Y cclY _ _).
    intros ; apply path_over_path_hprop ; apply _.
  Qed.
End cquot_ind_prop.

Arguments cquot_ind_prop {C} Y cclY.

(** The double recursion principle.
    We use [cquot_rec], [cquot_ind_set] and [cquot_ind_prop] to define it.
 *)
Section cquot_double_rec.
  Variable (C₁ C₂ : PreCategory)
           (Y : Type).
  Context `{IsTrunc 1 Y}
          `{Funext}.

  Variable (f : C₁ -> C₂ -> Y)
           (fr : forall (a : C₁) (b₁ b₂ : C₂),
               C₂ b₁ b₂ -> f a b₁ = f a b₂)
           (fre : forall (a : C₁) (b : C₂),
               fr a b b (identity b) = idpath)
           (frc : forall (a : C₁) (b₁ b₂ b₃ : C₂)
                         (c₁ : C₂ b₁ b₂) (c₂ : C₂ b₂ b₃),
               fr a b₁ b₃ (c₂ o c₁)
               =
               (fr a b₁ b₂ c₁) @ (fr a b₂ b₃ c₂))
           (fl : forall (a₁ a₂ : C₁) (b : C₂),
               morphism C₁ a₁ a₂ -> f a₁ b = f a₂ b)
           (fle : forall (a : C₁) (b : C₂),
               fl a a b (identity a) = idpath)
           (flc : forall (a₁ a₂ a₃ : C₁) (b : C₂)
                         (c₁ : C₁ a₁ a₂) (c₂ : C₁ a₂ a₃),
               fl a₁ a₃ b (c₂ o c₁)
               =
               (fl a₁ a₂ b c₁) @ (fl a₂ a₃ b c₂))
           (fp : forall (a₁ a₂ : C₁) (b₁ b₂ : C₂)
                        (c₁ : C₁ a₁ a₂) (c₂ : C₂ b₁ b₂),
               square (fl a₁ a₂ b₂ c₁)
                      (fr a₁ b₁ b₂ c₂)
                      (fr a₂ b₁ b₂ c₂)
                      (fl a₁ a₂ b₁ c₁)).

  Definition cquot_double_rec' : cquot C₁ -> cquot C₂ -> Y.
  Proof.
    intros x y.
    simple refine (cquot_rec _ _ _ _ _ x).
    - exact (fun a => cquot_rec Y (f a) (fr a) (fre a) (frc a) y).
    - intros a₁ a₂ c₁ ; simpl.
      simple refine (cquot_ind_set (fun z => _) _ _ _ y).
      + exact (fun b => fl a₁ a₂ b c₁).
      + intros b₁ b₂ c₂.
        apply map_path_over.
        refine (whisker_square idpath _ _ idpath _).
        * symmetry.
          apply cquot_rec_beta_ccleq.
        * symmetry.
          apply cquot_rec_beta_ccleq.
        * exact (fp a₁ a₂ b₁ b₂ c₁ c₂).
    - intros a.
      simple refine (cquot_ind_prop (fun z => _) _ _ y).
      exact (fun b => fle a b).
    - intros a₁ a₂ a₃ c.
      simple refine (cquot_ind_prop (fun z => _) _ _ y).
      exact (fun b => flc a₁ a₂ a₃ b c).
  Defined.

  Definition cquot_double_rec'_beta_l_ccleq
             {a₁ a₂ : C₁} (b : C₂) (c : C₁ a₁ a₂)
    : ap (fun z => cquot_double_rec' z (ccl C₂ b)) (ccleq C₁ c)
      =
      fl a₁ a₂ b c.
  Proof.
    apply cquot_rec_beta_ccleq.
  Qed.

  Definition cquot_double_rec'_beta_r_ccleq
             (a : C₁) {b₁ b₂ : C₂} (c : C₂ b₁ b₂)
    : ap (cquot_double_rec' (ccl C₁ a)) (ccleq C₂ c)
      =
      fr a b₁ b₂ c.
  Proof.
    apply (cquot_rec_beta_ccleq C₂).
  Qed.

  Definition cquot_double_rec : cquot C₁ * cquot C₂ -> Y
    := uncurry cquot_double_rec'.

  Definition cquot_double_rec_point (a : C₁) (b : C₂)
    : cquot_double_rec (ccl C₁ a, ccl C₂ b) = f a b
    := idpath.

  Definition cquot_double_rec_beta_ccleq
             {a₁ a₂ : C₁} {b₁ b₂ : C₂}
             (c₁ : C₁ a₁ a₂) (c₂ : C₂ b₁ b₂)
    : ap cquot_double_rec (path_prod' (ccleq C₁ c₁) (ccleq C₂ c₂))
      =
      fl a₁ a₂ b₁ c₁ @ fr a₂ b₁ b₂ c₂.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    refine (ap (fun p => p @ _) (cquot_rec_beta_ccleq C₁ _ _ _ _ _ _ _ _ _) @ _).
    exact (ap (fun p => _ @ p) (cquot_rec_beta_ccleq C₂ _ _ _ _ _ _ _ _ _)).
  Qed.

  Definition cquot_double_rec_beta_l_ccleq
             {a₁ a₂ : C₁} (b : C₂) (c : C₁ a₁ a₂)
    : ap cquot_double_rec (path_prod' (ccleq C₁ c) (idpath : ccl C₂ b = _))
      =
      fl a₁ a₂ b c.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    refine (ap (fun p => p @ _) (cquot_rec_beta_ccleq C₁ _ _ _ _ _ _ _ _ _) @ _).
    apply concat_p1.
  Qed.
  
  Definition cquot_double_rec_beta_r_ccleq
             (a : C₁) {b₁ b₂ : C₂} (c : C₂ b₁ b₂)
    : ap cquot_double_rec (path_prod' (idpath  : ccl C₁ a = _) (ccleq C₂ c))
      =
      fr a b₁ b₂ c.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    refine (ap (fun p => _ @ p) (cquot_rec_beta_ccleq C₂ _ _ _ _ _ _ _ _ _) @ _).
    apply concat_1p.
  Qed.
End cquot_double_rec.

Arguments cquot_double_rec {C₁ C₂} Y {_ _}.
Arguments cquot_double_rec' {C₁ C₂} Y {_ _}.
Arguments cquot_double_rec_beta_ccleq {C₁ C₂} Y {_ _}.

(** Double induction over a family of sets.
    We use the same trick as for double recursion.
 *)
Section cquot_double_ind_set.
  Variable (C₁ C₂ : PreCategory)
           (Y : cquot C₁ -> cquot C₂ -> Type).
  Context `{forall (a : cquot C₁) (b : cquot C₂), IsHSet (Y a b)}
          `{Funext}.
  
  Variable (f : forall (a : C₁) (b : C₂), Y (ccl C₁ a) (ccl C₂ b))
           (fr : forall (a : C₁) (b₁ b₂ : C₂) (c : C₂ b₁ b₂),
               path_over (Y (ccl C₁ a)) (ccleq C₂ c) (f a b₁) (f a b₂))
           (fl : forall (a₁ a₂ : C₁) (b : C₂) (c : C₁ a₁ a₂),
               path_over (fun z : cquot C₁ => Y z (ccl C₂ b))
                         (ccleq C₁ c)
                         (f a₁ b)
                         (f a₂ b)).
  
  Definition cquot_double_ind_set : forall (a : cquot C₁) (b : cquot C₂), Y a b.
  Proof.
    intros x y.
    simple refine (cquot_ind_set (fun z => _) _ _ _ x).
    - exact (fun a => cquot_ind_set (fun z => _) (f a) (fr a) _ y).
    - intros a₁ a₂ c ; simpl.
      simple refine (cquot_ind_prop (fun z => _) _ _ y).
      exact (fun b => fl a₁ a₂ b c).
  Defined.
End cquot_double_ind_set.

Arguments cquot_double_ind_set {C₁ C₂} Y {_ _}.

(** Double induction over a family of propositions.
    We use the same trick as before.
 *)
Section cquot_double_ind_prop.
  Variable (C₁ C₂ : PreCategory)
           (Y : cquot C₁ -> cquot C₂ -> Type).
  Context `{forall (a : cquot C₁) (b : cquot C₂), IsHProp (Y a b)}
          `{Funext}.
  
  Variable (f : forall (a : C₁) (b : C₂), Y (ccl C₁ a) (ccl C₂ b)).
  
  Definition cquot_double_ind_prop : forall (a : cquot C₁) (b : cquot C₂), Y a b.
  Proof.
    intros x y.
    simple refine (cquot_ind_prop (fun z => _) _ _ x).
    exact (fun a => cquot_ind_prop (fun z => _) (f a) _ y).
  Defined.
End cquot_double_ind_prop.

Arguments cquot_double_ind_prop {C₁ C₂} Y.

(** A special instance of double recursion for defining set-relations.
    This requires univalence, because we need to give equalities in [hSet].
    These equalities are made with [path_hset] and two functions need to be given.
    For the higher coherencies, these functions need to satisfy some laws.
 *)
Section cquot_relation.
  Variable (C₁ C₂ : PreCategory)
           (R : C₁ -> C₂ -> hSet)
           (fl : forall (a₁ a₂ : C₁) (b : C₂), C₁ a₁ a₂ -> R a₁ b -> R a₂ b)
           (fr : forall (a : C₁) (b₁ b₂ : C₂), C₂ b₁ b₂ -> R a b₁ -> R a b₂).
  
  Context `{forall (a₁ a₂ : C₁) (b : C₂) (c : C₁ a₁ a₂), IsEquiv (fl a₁ a₂ b c)}
          `{forall (a : C₁) (b₁ b₂ : C₂) (c : C₂ b₁ b₂), IsEquiv (fr a b₁ b₂ c)}.
  Context `{Univalence}.

  Variable (fl_id : forall (a : C₁) (b : C₂), fl a a b (identity a) == idmap)
           (fl_comp : forall (a₁ a₂ a₃ : C₁) (b : C₂)
                             (c₁ : C₁ a₁ a₂) (c₂ : C₁ a₂ a₃),
               fl a₁ a₃ b (c₂ o c₁) == fl a₂ a₃ b c₂ o (fl a₁ a₂ b c₁))
           (fr_id : forall (a : C₁) (b : C₂), fr a b b (identity b) == idmap)
           (fr_comp : forall (a : C₁) (b₁ b₂ b₃ : C₂)
                             (c₁ : C₂ b₁ b₂) (c₂ : C₂ b₂ b₃),
               fr a b₁ b₃ (c₂ o c₁) == fr a b₂ b₃ c₂ o (fr a b₁ b₂ c₁))
           (fc : forall (a₁ a₂ : C₁) (b₁ b₂ : C₂)
                        (c₁ : morphism C₁ a₁ a₂) (c₂ : morphism C₂ b₁ b₂),
               fl a₁ a₂ b₂ c₁ o fr a₁ b₁ b₂ c₂
               ==
               fr a₂ b₁ b₂ c₂ o fl a₁ a₂ b₁ c₁
           ).

  Definition path_hset_fr_refl
             (a : C₁) (b : C₂)
    : path_hset (BuildEquiv _ _ (fr a b b (identity b)) _) = idpath.
  Proof.
    refine (_ @ path_trunctype_1).
    apply path_trunctype_eq ; cbn.
    apply fr_id.
  Qed.

  Definition path_hset_fr_trans
             (a : C₁) (b₁ b₂ b₃ : C₂)
             (c₁ : C₂ b₂ b₃) (c₂ : C₂ b₁ b₂)
    : path_hset (BuildEquiv _ _ (fr a b₁ b₃ (c₁ o c₂)) _)
      =
      (path_hset (BuildEquiv _ _ (fr a b₁ b₂ c₂) _))
        @
        path_hset (BuildEquiv _ _ (fr a b₂ b₃ c₁) _).
  Proof.
    refine (_ @ path_trunctype_pp _ _).
    apply path_trunctype_eq ; cbn.
    apply fr_comp.
  Qed.

  Definition path_hset_fl_refl
             (a : C₁) (b : C₂)
    : path_hset (BuildEquiv _ _ (fl a a b (identity a)) _) = idpath.
  Proof.
    refine (_ @ path_trunctype_1).
    apply path_trunctype_eq ; cbn.
    apply fl_id.
  Qed.
  
  Definition path_hset_fl_trans
             (a₁ a₂ a₃ : C₁) (b : C₂)
             (c₁ : C₁ a₂ a₃) (c₂ : C₁ a₁ a₂)
    : path_hset (BuildEquiv _ _ (fl a₁ a₃ b (c₁ o c₂)) _)
      =
      (path_hset (BuildEquiv _ _ (fl a₁ a₂ b c₂) _))
        @
        path_hset (BuildEquiv _ _ (fl a₂ a₃ b c₁) _).
  Proof.
    refine (_ @ path_trunctype_pp _ _).
    apply path_trunctype_eq ; cbn.
    apply fl_comp.
  Qed.

  Definition path_hset_fl_fr
             (a₁ a₂ : C₁) (b₁ b₂ : C₂)
             (c₁ : C₁ a₁ a₂)
             (c₂ : C₂ b₁ b₂)
    : (path_hset (BuildEquiv _ _ (fr a₁ b₁ b₂ c₂) _))
        @
        path_hset (BuildEquiv _ _ (fl a₁ a₂ b₂ c₁) _)
      =
      (path_hset (BuildEquiv _ _ (fl a₁ a₂ b₁ c₁) _))
        @
        path_hset (BuildEquiv _ _ (fr a₂ b₁ b₂ c₂) _).
  Proof.
    refine ((path_trunctype_pp _ _)^ @ _ @ path_trunctype_pp _ _).
    apply path_trunctype_eq ; cbn.
    apply fc.
  Qed.

  Definition cquot_relation : cquot C₁ -> cquot C₂ -> hSet.
  Proof.
    simple refine (cquot_double_rec' _ _ _ _ _ _ _ _ _).
    - exact R.
    - exact (fun a b₁ b₂ c => path_hset (BuildEquiv _ _ (fr a b₁ b₂ c) _)).
    - exact path_hset_fr_refl.
    - intros.
      apply path_hset_fr_trans.
    - exact (fun a₁ a₂ b c => path_hset (BuildEquiv _ _ (fl a₁ a₂ b c) _)).
    - exact path_hset_fl_refl.
    - intros.
      apply path_hset_fl_trans.
    - intros a₁ a₂ b₁ b₂ c₁ c₂.
      apply path_to_square.
      apply path_hset_fl_fr.
  Defined.

  Definition cquot_relation_ccl_ccl (a : C₁) (b : C₂)
    : cquot_relation (ccl C₁ a) (ccl C₂ b) = R a b
    := idpath.

  Definition cquot_relation_beta_l_ccleq
             {a₁ a₂ : C₁} (b : C₂) (c : C₁ a₁ a₂)
    : ap (fun z => cquot_relation z (ccl C₂ b)) (ccleq C₁ c)
      =
      path_hset (BuildEquiv _ _ (fl a₁ a₂ b c) _).
  Proof.
    exact (cquot_double_rec'_beta_l_ccleq C₁ C₂ hSet R _ _ _ _ _ _ _ b c).
  Qed.

  Definition cquot_relation_beta_r_ccleq
             (a : C₁) {b₁ b₂ : C₂} (c : C₂ b₁ b₂)
    : ap (cquot_relation (ccl C₁ a)) (ccleq C₂ c)
      =
      path_hset (BuildEquiv _ _ (fr a b₁ b₂ c) _).
  Proof.
    exact (cquot_double_rec'_beta_r_ccleq C₁ C₂ hSet R _ _ _ _ _ _ _ a c).
  Qed.
End cquot_relation.