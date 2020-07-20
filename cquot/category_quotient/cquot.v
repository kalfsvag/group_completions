(** This file defines a 1-type completion of a category as a HIT and derives some recursion/induction principles for it.
 This file was originally written by Niels van der Weide and Dan Frumin, with only minor changes here. Namely, that we generalize the construction for all categories, and not only for groupoids.*)

Require Import HoTT.
From A_BPQ Require Import
     general.
From A_BPQ.cquot.basics Require Export
     globe_over path_over square.

From HoTT.Categories Require Import
     Category.

(** * The 1-type completion of a category  *)
(** Given a type [A] and a category [C], we construct a type [cquot C] such that
    we have [A -> cquot A C] and the equality of [cquot A C] is described by [C].
    We use the standard method to define the HIT
    <<
    HIT gquot C :=
     | ccl : A -> cquot C
     | ccleq : Π(a₁ a₂ : A), hom C a₁ a₂ -> gcl a₁ = gcl a₂
     | ce : Π(a : A), ccleq (e a) = idpath
     | cconcat : Π(a₁ a₂ a₃ : A) (g₁ : hom C a₁ a₂) (g₂ : hom C a₂ a₃),
               ccleq (g₁ × g₂) = ccleq g₁ @ ccleq g₂
     | ctrunc : Is-1-Type (cquot C)
    >>

*)

Module Export cquot.
  Private Inductive cquot (C : PreCategory) :=
  | ccl : C -> cquot C.

  Coercion morphism : PreCategory >-> Funclass.

  Axiom ccleq
    : forall (C : PreCategory) {a₁ a₂ : C} (g : C a₁ a₂),
      ccl C a₁ = ccl C a₂.

  Axiom ce
    : forall (C : PreCategory) (a : C),
      ccleq C (identity a) = idpath.

  Axiom cconcat
    : forall (C : PreCategory)
             {a₁ a₂ a₃ : C}
             (g₁ : C a₁ a₂) (g₂ : C a₂ a₃),
      ccleq C (g₂ o g₁) = ccleq C g₁ @ ccleq C g₂.

  Axiom ctrunc
    : forall (C : PreCategory), IsTrunc 1 (cquot C).

  Instance cquot_istrunct C : IsTrunc 1 (cquot C).
  Proof.
    apply ctrunc.
  Defined.

  Section cquot_ind.
    Variable (C : PreCategory)
             (Y : cquot C -> Type)
             (cclY : forall (a : C), Y(ccl C a))
             (ccleqY : forall (a₁ a₂ : C) (g : C a₁ a₂),
                 path_over Y (ccleq C g) (cclY a₁) (cclY a₂))
             (ceY : forall (a : C), globe_over Y
                                                (path_to_globe (ce C a))
                                                (ccleqY a a (identity a))
                                                (path_over_id (cclY a)))
             (cconcatY : forall (a₁ a₂ a₃ : C)
                                (g₁ : C a₁ a₂) (g₂ : C a₂ a₃),
                 globe_over Y
                            (path_to_globe (cconcat C g₁ g₂))
                            (ccleqY a₁ a₃ (g₂ o g₁))
                            (path_over_concat (ccleqY a₁ a₂ g₁)
                                              (ccleqY a₂ a₃ g₂)))
             (truncY : forall (x : cquot C), IsTrunc 1 (Y x)).

    Fixpoint cquot_ind (g : cquot C) : Y g
      := (match g with
         | ccl a => fun _ _ _ _ => cclY a
          end) ccleqY ceY cconcatY truncY.

    Axiom cquot_ind_beta_ccleq : forall (a₁ a₂ : C) (g : C a₁ a₂),
        apd_po cquot_ind (ccleq C g)
        =
        ccleqY a₁ a₂ g.
  End cquot_ind.
End cquot.

Arguments cquot_ind {C} Y cclY ccleqY ceY cconcatY truncY.















