(** This file defines a groupoid quotient HIT and derives some recursion/induction principles for it. *)
Require Import HoTT.
From A_BPQ Require Import
     general.
From A_BPQ.cquot.basics Require Export
     globe_over path_over square.
(* From A_BPQ.cquot Require Import *)
(*      grpd_bicategory. *)

From HoTT.Categories Require Import
     Category.

(** * The groupoid quotient over a type. *)
(** Given a type [A] and a groupoid [G], we construct a type [gquot G] such that
    we have [A -> gquot A G] and the equality of [gquot A G] is described by [G].
    We use the standard method to define the HIT
    <<
    HIT gquot G :=
     | gcl : A -> gquot G
     | gcleq : Π(a₁ a₂ : A), hom G a₁ a₂ -> gcl a₁ = gcl a₂
     | ge : Π(a : A), gcleq (e a) = idpath
     | ginv : Π(a₁ a₂ : A) (g : hom G a₁ a₂), gcleq g⁻¹ = (gcleq g)^
     | gconcat : Π(a₁ a₂ a₃ : A) (g₁ : hom G a₁ a₂) (g₂ : hom G a₂ a₃),
               gcleq (g₁ × g₂) = gcleq g₁ @ gcleq g₂
     | gtrunc : Is-1-Type (gquot G)
    >>
*)

(* modifying this to make a groupoid truncation of any precategory *)

Module Export cquot.
  Private Inductive cquot (C : PreCategory) :=
  | ccl : C -> cquot C.

  (*   (** The homsets. *) *)
  (* Definition hom (G : groupoid) : G -> G -> hSet *)
  (*   := fun x y => BuildhSet (morphism G.1 x y)%morphism. *)

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

  (* Definition cinv *)
  (*   : forall (G : groupoid) {a₁ a₂ : G} (g : G a₁ a₂), *)
  (*     ccleq G.1 (inv g) = (ccleq G.1 g)^. *)
  (* Proof. *)
  (*   intros G a₁ a₂ g. *)
  (*   apply moveL_V1. *)
  (*   rewrite <- cconcat, grpd_right_inverse. , ce. *)
  (*   reflexivity. *)
  (* Qed. *)
  
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















