(** This file was originally written by Niels van der Weide and Dan Frumin.  *)
Require Import HoTT.
From GCTT Require Import heterogeneous_equality.

(** The type of paths over path defined as an inductive type.
    The goal is to represent paths in dependent families.
 *)
Inductive path_over {A : Type} (C : A -> Type)
  : forall {a₁ a₂ : A} (p : a₁ = a₂) (c₁ : C a₁) (c₂ : C a₂), Type
  := path_over_id : forall {a : A} (c : C a), path_over C idpath c c.

Arguments path_over_id {A C a} c.

(** Alternatively, we can define it using path induction. *)
Definition path_over_pi
           {A : Type} (C : A -> Type)
           {a₁ a₂ : A} (p : a₁ = a₂)
  : forall (c₁ : C a₁) (c₂ : C a₂), Type
  := match p with
     | idpath => fun c₁ c₂ => c₁ = c₂
     end.

Section equivalences.
  (** Paths in dependent families are equivalent to heterogeneous equalities. *)
  Definition path_over_to_heq
             {A : Type} {C : A -> Type}
             {a₁ a₂ : A} {p : a₁ = a₂}
             {c₁ : C a₁} {c₂ : C a₂}
             (q : path_over C p c₁ c₂)
    : heq (ap C p) c₁ c₂
    := match q with
       | path_over_id _ _ => heq_refl _
       end.

  Definition heq_to_path_over
             {A : Type} {C : A -> Type}
             {a₁ a₂ : A} {p : a₁ = a₂}
    : forall {c₁ : C a₁} {c₂ : C a₂} (q : heq (ap C p) c₁ c₂),
      path_over C p c₁ c₂
    := match p with
       | idpath =>
         fun c₁ c₂ q =>
           transport (path_over C idpath c₁) (heq_to_heq_pi q) (path_over_id _)
       end.

  Global Instance path_over_to_heq_isequiv
         {A : Type} {C : A -> Type}
         {a₁ a₂ : A} {p : a₁ = a₂}
         {c₁ : C a₁} {c₂ : C a₂}
    : IsEquiv (@path_over_to_heq A C a₁ a₂ p c₁ c₂).
  Proof.
    
    simple refine (isequiv_adjointify _ _ _ _).
    - apply heq_to_path_over.
    - intros x ; induction p ; cbn in *.
      refine (_ @ eissect heq_to_heq_pi x).
      induction (heq_to_heq_pi x).
      reflexivity.
    - intros x ; induction x.
      reflexivity.
  Defined.

  (** Also, paths in path families are equivalent to paths in both [C a₁]. *)
  Definition path_over_to_path
             {A : Type} {C : A -> Type}
             {a₁ a₂ : A} {p : a₁ = a₂}
             {c₁ : C a₁} {c₂ : C a₂}
             (q : path_over C p c₁ c₂)
    : transport C p c₁ = c₂
    := match q with
       | path_over_id _ _ => idpath
       end.

  Definition path_to_path_over
             {A : Type} {C : A -> Type}
             {a₁ a₂ : A} {p : a₁ = a₂}
    : forall {c₁ : C a₁} {c₂ : C a₂} (q : transport C p c₁ = c₂),
      path_over C p c₁ c₂
    := match p with
       | idpath =>
         fun c₁ c₂ q => transport (path_over C idpath c₁) q (path_over_id _)
       end.

  Global Instance path_over_to_path_is_equiv
         {A : Type} {C : A -> Type}
         {a₁ a₂ : A} {p : a₁ = a₂}
         {c₁ : C a₁} {c₂ : C a₂}
    : IsEquiv (@path_over_to_path A C a₁ a₂ p c₁ c₂).
  Proof.
    simple refine (isequiv_adjointify _ (@path_to_path_over A C a₁ a₂ p c₁ c₂) _ _).
    - intros q ; induction p, q ; cbn in *.
      reflexivity.
    - intros x ; induction x.
      reflexivity.
  Defined.

  (** Also, paths in path families are equivalent to paths in both [C a₂]. *)
  Definition path_over_to_path_V
             {A : Type} {C : A -> Type}
             {a₁ a₂ : A} {p : a₁ = a₂}
             {c₁ : C a₁} {c₂ : C a₂}
             (q : path_over C p c₁ c₂)
    : c₁ = transport C p^ c₂
    := match q with
       | path_over_id _ _ => idpath
       end.

  Definition path_V_to_path_over
             {A : Type} {C : A -> Type}
             {a₁ a₂ : A} {p : a₁ = a₂}
    : forall {c₁ : C a₁} {c₂ : C a₂} (q : c₁ = transport C p^ c₂),
      path_over C p c₁ c₂
    := match p with
       | idpath =>
         fun c₁ c₂ q => transport (path_over C idpath c₁) q (path_over_id _)
       end.

  Global Instance path_over_to_path_V_is_equiv
         {A : Type} {C : A -> Type}
         {a₁ a₂ : A} {p : a₁ = a₂}
         {c₁ : C a₁} {c₂ : C a₂}
    : IsEquiv (@path_over_to_path_V A C a₁ a₂ p c₁ c₂).
  Proof.
    simple refine (isequiv_adjointify _ (@path_V_to_path_over A C a₁ a₂ p c₁ c₂) _ _).
    - intros q ; induction p ; cbn in * ; induction q.
      reflexivity.
    - intros x ; induction x.
      reflexivity.
  Defined.

  (** The definitions of paths in dependent families using inductive types and path induction, are equivalent. *)
  Definition path_over_to_path_over_pi
             {A : Type} {C : A -> Type}
             {a₁ a₂ : A} {p : a₁ = a₂}
             {c₁ : C a₁} {c₂ : C a₂}
             (q : path_over C p c₁ c₂)
    : path_over_pi C p c₁ c₂
    := match q with
       | path_over_id _ _ => idpath
       end.

  Definition path_over_pi_to_path_over
             {A : Type} {C : A -> Type}
             {a₁ a₂ : A} {p : a₁ = a₂}
    : forall {c₁ : C a₁} {c₂ : C a₂} (q : path_over_pi C p c₁ c₂),
      path_over C p c₁ c₂
    := match p with
       | idpath =>
         fun c₁ c₂ q => transport (path_over C 1 c₁) q (path_over_id _)
       end.

  Global Instance path_over_to_path_over_pi_is_equiv
         {A : Type} {C : A -> Type}
         {a₁ a₂ : A} {p : a₁ = a₂}
         {c₁ : C a₁} {c₂ : C a₂}
    : IsEquiv (@path_over_to_path_over_pi A C a₁ a₂ p c₁ c₂).
  Proof.
    simple refine (isequiv_adjointify _ (@path_over_pi_to_path_over A C a₁ a₂ p c₁ c₂) _ _).
    - intros x.
      induction p, x.
      reflexivity.
    - intros x ; induction x.
      reflexivity.
  Defined.
End equivalences.

Section operations.
  (** Dependent maps can be applied to paths.
      This gives a path in a dependent family.
   *)
  Definition apd_po
             {A : Type} {C : A -> Type}
             (f : forall (a : A), C a)
             {a₁ a₂ : A} (p : a₁ = a₂)
    : path_over C p (f a₁) (f a₂)
    := match p with
       | idpath => path_over_id _
       end.

  (** A path in a dependent family gives a path in a sigma type. *)
  Definition path_prod_po
             {A : Type} {C : A -> Type}
             {a₁ a₂ : A} (p : a₁ = a₂)
             {c₁ : C a₁} {c₂ : C a₂}
             (q : path_over C p c₁ c₂)
    : (a₁;c₁) = (a₂;c₂)
    := match q with
       | path_over_id _ _ => idpath
       end.

  (** If we look at a path over the identity path, then it is just a path in a certain fiber. *)
  Definition path_over_single_fiber
             {A : Type} {C : A -> Type}
             {a : A}
             {c₁ : C a} {c₂ : C a}
             (q : path_over C idpath c₁ c₂)
    : c₁ = c₂
    := path_over_to_path q.

  Global Instance path_over_single_fiber_is_equiv
         {A : Type} {C : A -> Type}
         {a : A}
         {c₁ : C a} {c₂ : C a}
    : IsEquiv (@path_over_single_fiber A C a c₁ c₂)
    := _.

  (** If the fiber is constant, then it is just a path in that fiber. *)
  Definition path_over_const
             {A C : Type}
             {a₁ a₂ : A} {p : a₁ = a₂}
             {c₁ c₂ : C}
             (q : path_over (fun _ => C) p c₁ c₂)
    : c₁ = c₂
    := match q with
       | path_over_id _ _ => idpath
       end.

  Definition const_path_over
             {A C : Type}
             {a₁ a₂ : A} {p : a₁ = a₂}
             {c₁ c₂ : C}
             (q : c₁ = c₂)
    : path_over (fun _ => C) p c₁ c₂
    := match p, q with
       | idpath, idpath => path_over_id _
       end.

  Global Instance path_over_const_isequiv
         {A C : Type}
         {a₁ a₂ : A} {p : a₁ = a₂}
         {c₁ c₂ : C}
    : IsEquiv (@const_path_over A C a₁ a₂ p c₁ c₂).
  Proof.
    simple refine (isequiv_adjointify _ path_over_const _ _).
    - intros q ; induction q.
      reflexivity.
    - intros q ; induction p, q.
      reflexivity.
  Defined.

  (** Composing the fibration with a map [f] gives a path over [ap f p]. *)
  Definition path_over_compose
             {A B : Type} {C : B -> Type} (f : A -> B)
             {a₁ a₂ : A} {p : a₁ = a₂}
             {c₁ : C (f a₁)} {c₂ : C (f a₂)}
             (q : path_over (C o f) p c₁ c₂)
    : path_over C (ap f p) c₁ c₂
    := match q with
       | path_over_id _ _ => path_over_id _
       end.

  Definition compose_path_over
             {A B : Type} {C : B -> Type} (f : A -> B)
             {a₁ a₂ : A} {p : a₁ = a₂}
    : forall {c₁ : C (f a₁)} {c₂ : C (f a₂)} (q : path_over C (ap f p) c₁ c₂),
      path_over (C o f) p c₁ c₂
    := match p with
       | idpath =>
         fun c₁ c₂ q => transport (path_over _ idpath c₁)
                                  (path_over_to_path q)
                                  (path_over_id c₁)
       end.

  Global Instance path_over_compose_isequiv
         {A B : Type} {C : B -> Type} (f : A -> B)
         {a₁ a₂ : A} {p : a₁ = a₂}
         {c₁ : C (f a₁)} {c₂ : C (f a₂)}
    : IsEquiv (@path_over_compose A B C f a₁ a₂ p c₁ c₂).
  Proof.
    simple refine (isequiv_adjointify _ (@compose_path_over A B C f a₁ a₂ p c₁ c₂) _ _).
    - intros x ; induction p ; cbn in *.
      refine (_ @ eissect path_over_to_path x).
      induction (path_over_to_path x).
      reflexivity.
    - intros q ; induction q.
      reflexivity.
  Defined.
End operations.

(* Groupoid operations for `path_over`. *)
Section groupoid.
  Variable (A : Type)
           (C : A -> Type).

  (* The inverse. *)
  Definition path_over_inv
             {a₁ a₂ : A}
             {p : a₁ = a₂}
             {c₁ : C a₁} {c₂ : C a₂}
             (q : path_over C p c₁ c₂)
    : path_over C p^ c₂ c₁
    := match q with
       | path_over_id _ _ => path_over_id _
       end.

  (* Concatenation. *)
  Definition path_over_concat
             {a₁ a₂ a₃ : A}
             {p₁ : a₁ = a₂} {p₂ : a₂ = a₃}
             {c₁ : C a₁} {c₂ : C a₂} {c₃ : C a₃}
             (q₁ : path_over C p₁ c₁ c₂) (q₂ : path_over C p₂ c₂ c₃)
    : path_over C (p₁ @ p₂) c₁ c₃.
  Proof.
    induction q₁, q₂.
    exact (path_over_id _).
  Defined.
End groupoid.

Arguments path_over_inv {A C a₁ a₂ p c₁ c₂} q.
Arguments path_over_concat {A C a₁ a₂ a₃ p₁ p₂ c₁ c₂ c₃} q₁ q₂.

(** `const_path_over` applied to an inverse, gives the inverse in `path_over`.*)
Definition const_path_over_inv
           {A C : Type}
           {a₁ a₂ : A} {p : a₁ = a₂}
           {c₁ c₂ : C}
           (q : c₁ = c₂)
  : (const_path_over q^ : path_over (fun _ => C) p^ c₂ c₁)
    =
    path_over_inv (const_path_over q)
  := match q, p with
     | idpath, idpath => idpath
     end.

(** `const_path_over` applied to a concatanation, gives the concatanation in `path_over`. *)
Definition const_path_over_concat
           {A C : Type}
           {a₁ a₂ a₃ : A}
           {p₁ : a₁ = a₂} {p₂ : a₂ = a₃}
           {c₁ c₂ c₃ : C}
           (q₁ : c₁ = c₂) (q₂ : c₂ = c₃)
  : (const_path_over (q₁ @ q₂) : path_over (fun _ => C) (p₁ @ p₂) c₁ c₃)
    =
    path_over_concat (const_path_over q₁) (const_path_over q₂).
Proof.
  induction p₁, p₂, q₁, q₂.
  reflexivity.
Defined.

(** `apd` on a section of a constant fibration. *)
Definition apd_po_const
           {A C : Type}
           (f : A -> C)
           {a₁ a₂ : A} (p : a₁ = a₂)
  : apd_po f p = const_path_over (ap f p)
  := match p with
     | idpath => idpath
     end.

(** `const_path_over` is injective. *)
Definition const_path_over_inj
           {A C : Type}
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           {c₁ c₂ : C}
           (q₁ q₂ : c₁ = c₂)
           (h : (const_path_over q₁ : path_over (fun _ => C) p c₁ c₂)
                = const_path_over q₂)
  : q₁ = q₂.
Proof.
  pose (ap const_path_over^-1 h) as s.
  rewrite !eissect in s.
  exact s.
Defined.

(** `path_over` in a family of sets. *)
Global Instance path_over_hprop
       {A : Type}
       (Y : A -> Type)
       `{forall (a : A), IsHSet (Y a)}
       {a₁ a₂ : A}
       (p : a₁ = a₂)
       (c₁ : Y a₁) (c₂ : Y a₂)
  : IsHProp (path_over Y p c₁ c₂).
Proof.
  apply hprop_allpath.
  intros x y.
  refine ((eissect path_over_to_path x)^ @ _ @ eissect path_over_to_path y).
  apply (ap path_to_path_over).
  apply path_ishprop.
Defined.

(** `path_over` in a family of propositions. *)
Definition path_over_path_hprop
       {A : Type}
       (Y : A -> Type)
       `{forall (a : A), IsHProp (Y a)}
       {a₁ a₂ : A}
       (p : a₁ = a₂)
       (c₁ : Y a₁) (c₂ : Y a₂)
  : path_over Y p c₁ c₂.
Proof.
  apply path_to_path_over.
  apply path_ishprop.
Defined.

(** `path_over` in a family of arrows. *)
Definition path_over_arrow
           {A : Type}
           (Y₁ Y₂ : A -> Type)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (f₁ : Y₁ a₁ -> Y₂ a₁) (f₂ : Y₁ a₂ -> Y₂ a₂)
           (q : forall (x : Y₁ a₂), path_over Y₂ p (f₁ (p^ # x)) (f₂ x))
           `{Funext}
  : path_over (fun a => Y₁ a -> Y₂ a) p f₁ f₂.
Proof.
  apply path_to_path_over.
  funext x.
  refine (transport_arrow _ _ _ @ _).
  apply path_over_to_path.
  apply q.
Defined.
