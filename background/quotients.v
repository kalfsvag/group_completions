(**
  This file is copied from the HoTT library, with only minor changes: Namely that we do not require R to be a mere relation in the definition.
 *)


(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics.
Require Import Types.Universe Types.Arrow Types.Sigma.
Require Import HSet HProp UnivalenceImpliesFunext TruncType.
Require Import HIT.epi HIT.Truncations HIT.Connectedness.

Local Open Scope path_scope.



(** * Quotient of a Type by an hprop-valued relation

We aim to model:
<<
Inductive quotient : Type :=
   | class_of : A -> quotient
   | related_classes_eq : forall x y, (R x y), class_of x = class_of y
   | quotient_set : IsHSet quotient
>>
*)


Module Export Set_Quotient.

  Section Domain.

    Context {A : Type}.

    Private Inductive set_quotient (R : relation A): Type :=
    | class_of : A -> set_quotient R.

    (** The path constructors. *)
    Axiom related_classes_eq
    : forall {R : relation A} {x y : A}, R x y ->
                        class_of R x = class_of R y.

    Context (R : relation A).

    Axiom set_quotient_set : IsHSet (set_quotient R).
    Global Existing Instance set_quotient_set.

    Definition set_quotient_ind (P : (set_quotient R) -> Type) {sP : forall x, IsHSet (P x)}
               (dclass : forall x, P (class_of R x))
               (dequiv : (forall x y (H : R x y), (related_classes_eq H) # (dclass x) = dclass y))
    : forall q, P q
      := fun q => match q with class_of a => fun _ _ => dclass a end sP dequiv.

    Definition set_quotient_ind_compute {P sP} dclass dequiv x
    : @set_quotient_ind P sP dclass dequiv (class_of R x) = dclass x.
    Proof.
      reflexivity.
    Defined.

    (** Again equality of paths needs to be postulated *)
    Axiom set_quotient_ind_compute_path
    : forall P sP dclass dequiv,
      forall x y (H : R x y),
        apD (@set_quotient_ind P sP dclass dequiv) (related_classes_eq H)
        = dequiv x y H.

  End Domain.

End Set_Quotient.

Section rec.
  Context `{Univalence}.
  
  Context {A : Type} (R : relation A) .
  Definition set_quotient_rec {B : Type} {sB : IsHSet B}
             (dclass : (forall x : A, B))
             (dequiv : (forall x y, R x y -> dclass x = dclass y))
  : set_quotient R -> B.
  Proof.
    apply (set_quotient_ind R (fun _ : set_quotient _ => B)) with dclass.
    intros ?? H'. destruct (related_classes_eq H'). by apply dequiv.
  Defined.

  Definition set_quotient_rec2 {B : hSet} {dclass : (A -> A -> B)} : 
             (forall x x' y, R x x' -> dclass x y = dclass x' y) ->
             (forall x y y', R y y' -> dclass x y = dclass x y') -> 
      set_quotient R -> set_quotient R -> B.
  Proof.
    intros dequiv1 dequiv0.
    (* assert (dequiv0 : forall x x0 y : A, R x0 y -> dclass x x0 = dclass x y) *)
    (*   by (intros ? ? ? Hx; apply dequiv;[apply Hrefl|done]). *)
    refine (set_quotient_rec
              (fun x => set_quotient_rec (dclass x) (dequiv0 x)) _).
    intros x x' Hx.
    assert (h : dclass x = dclass x').
    { exact (path_arrow (dclass x) (dclass x') (fun y => dequiv1 x x' y Hx)). }
        
    apply path_forall. red.
    (* assert (dequiv1 : forall y : A, *)
    (*                     set_quotient_rec (dclass x) (dequiv0 x) (class_of _ y) = *)
    (*                     set_quotient_rec (dclass x') (dequiv0 x') (class_of _ y)) *)
    (*   by (intros; by apply dequiv). *)
    srapply (set_quotient_ind R).
    - intro a. simpl. apply (dequiv1 _ _ _ Hx).
    - intros. apply path_ishprop.
  Defined.


End rec.


  (* Double induction on two different quotients *)
  Definition set_quotient_rec2' `{Univalence} {A B : Type} (R : relation A) (S : relation B)
           {C : hSet} {dclass : (A -> B -> C)} : 
             (forall x x' y, R x x' -> dclass x y = dclass x' y) ->
             (forall x y y', S y y' -> dclass x y = dclass x y') -> 
      set_quotient R -> set_quotient S -> C.
  Proof.
    intros dequiv1 dequiv0.
    (* assert (dequiv0 : forall x x0 y : A, R x0 y -> dclass x x0 = dclass x y) *)
    (*   by (intros ? ? ? Hx; apply dequiv;[apply Hrefl|done]). *)
    (* srapply @set_quotient_rec. *)
    (* - intro x. *)
    (*   srapply @set_quotient_rec. *)
    (*   + exact (dclass x). *)
    refine (set_quotient_rec _
              (fun x => set_quotient_rec _ (dclass x) (dequiv0 x)) _).
    intros x x' Hx.
    assert (h : dclass x = dclass x').
    { exact (path_arrow (dclass x) (dclass x') (fun y => dequiv1 x x' y Hx)). }
        
    apply path_forall. red.
    (* assert (dequiv1 : forall y : A, *)
    (*                     set_quotient_rec (dclass x) (dequiv0 x) (class_of _ y) = *)
    (*                     set_quotient_rec (dclass x') (dequiv0 x') (class_of _ y)) *)
    (*   by (intros; by apply dequiv). *)
    srapply (set_quotient_ind S).
    - intro a. simpl. apply (dequiv1 _ _ _ Hx).
    - intros. apply path_ishprop.
  Defined.


Section Equiv.

  Context `{Univalence}.

  Context {A : Type} (R : relation A) 
          {Htrans : Transitive R} {Hsymm : Symmetric R}.

  Lemma set_quotient_path2 : forall {x y : set_quotient R} (p q : x=y), p=q.
  Proof.
    apply @set_path2. apply _.
  Defined.

  Definition in_class {sR: is_mere_relation _ R} : set_quotient R -> A -> hProp.
  Proof.
    refine (set_quotient_ind R (fun _ => A -> hProp) (fun a b => BuildhProp (R a b)) _).
    intros. eapply concat;[apply transport_const|].
    apply path_forall. intro z. apply path_hprop; simpl.
    apply @equiv_iff_hprop; eauto.
  Defined.

  Context {Hrefl : Reflexive R}.

  Lemma in_class_pr {sR: is_mere_relation _ R} : forall x y, (in_class (class_of R x) y : Type) = R x y.
  Proof.
    reflexivity.
  Defined.

  Lemma set_quotient_ind_prop (P : set_quotient R -> Type)
        `{forall x, IsHProp (P x)} :
    forall dclass : forall x, P (class_of R x),
    forall q, P q.
  Proof.
    intros. apply (set_quotient_ind R P dclass).
    intros. apply path_ishprop.
  Defined.

  Global Instance decidable_in_class `{forall x y, Decidable (R x y)} {sR: is_mere_relation _ R}
  : forall x a, Decidable (in_class x a).
  Proof.
    refine (set_quotient_ind_prop _ _).
    intros a b; exact (transport Decidable (in_class_pr a b) _).
  Defined.

  Lemma class_of_repr {sR: is_mere_relation _ R}: forall q x, in_class q x -> q = class_of R x.
  Proof.
    apply (set_quotient_ind R
                        (fun q : set_quotient R => forall x, in_class q x -> q = class_of _ x)
                        (fun x y H => related_classes_eq H)).
    intros.
    apply path_forall. intro z.
    apply path_forall;intro H'.
    apply set_quotient_path2.
  Defined.

  Lemma classes_eq_related {sR: is_mere_relation _ R} : forall x y,
                               class_of R x = class_of R y -> R x y.
  Proof.
    intros x y H'.
    pattern (R x y).
    eapply transport.
    - apply in_class_pr.
    - pattern (class_of R x). apply (transport _ (H'^)).
      apply Hrefl.
  Defined.

  (** Thm 10.1.8 *)
  Theorem sets_exact {sR: is_mere_relation _ R} : forall x y, (class_of R x = class_of R y) <~> R x y.
    intros ??. apply equiv_iff_hprop.
    - apply classes_eq_related.
    - apply related_classes_eq.
  Defined.


  Definition set_quotient_ind_prop' : forall P : set_quotient R -> Type,
                                  forall (Hprop' : forall x, IsHProp (P (class_of _ x))),
                                    (forall x, P (class_of _ x)) -> forall y, P y.
  Proof.
    intros ? ? dclass. apply set_quotient_ind with dclass.
    - simple refine (set_quotient_ind R (fun x => IsHSet (P x)) _ _); cbn beta; try exact _.
      intros; apply path_ishprop.
    - intros. apply Hprop'.
  Defined.

  (** From Ch6 *)
  Theorem set_quotient_surjective: IsSurjection (class_of R).
  Proof.
    apply BuildIsSurjection.
    apply (set_quotient_ind_prop (fun y => merely (hfiber (class_of R) y))); try exact _.
    intro x. apply tr. by exists x.
  Defined.

  (** From Ch10 *)
  Definition set_quotient_ump' (B:hSet): (set_quotient R -> B) ->
                                     (sigT (fun f : A-> B => (forall a a0:A, R a a0 -> f a =f a0))).
    intro f. exists (compose f (class_of R) ).
    intros. f_ap. by apply related_classes_eq.
  Defined.

  (* Definition set_quotient_ump'' (B:hSet): (sigT (fun f : A-> B => (forall a a0:A, R a a0 -> f a =f a0))) *)
  (*                                     -> set_quotient R -> B. *)
  (*   intros [f H']. *)
  (*   apply (set_quotient_rec _ H'). *)
  (* Defined. *)

  (* Theorem set_quotient_ump (B:hSet): (set_quotient R -> B) <~> *)
  (*                                                  (sigT (fun f : A-> B => (forall a a0:A, R a a0 -> f a =f a0))). *)
  (* Proof. *)
  (*   refine (equiv_adjointify (set_quotient_ump' B) (set_quotient_ump'' B) _ _). *)
  (*   intros [f Hf]. *)
  (*   - by apply equiv_path_sigma_hprop. *)
  (*   - intros f. *)
  (*     apply path_forall. *)
  (*     red. apply set_quotient_ind_prop';[apply _|reflexivity]. *)
  (* Defined. *)

  (** Missing

  The equivalence with VVset_quotient [A//R].

  This should lead to the unnamed theorem:

  10.1.10. Equivalence relations are effective and there is an equivalence [A/R<~>A//R]. *)

  (**
  The theory of canonical quotients is developed by C.Cohen:
  http://perso.crans.org/cohen/work/quotients/
 *)

End Equiv.

Section Functoriality.

  Definition set_quotient_functor
             {A : Type} (R : relation A) {sR: is_mere_relation _ R}
             {B : Type} (S : relation B) {sS: is_mere_relation _ S}
             (f : A -> B) (fresp : forall x y, R x y -> S (f x) (f y))
  : set_quotient R -> set_quotient S.
  Proof.
    refine (set_quotient_rec R (class_of S o f) _).
    intros x y r.
    apply related_classes_eq, fresp, r.
  Defined.

  Context {A : Type} (R : relation A) {sR: is_mere_relation _ R}
          {B : Type} (S : relation B) {sS: is_mere_relation _ S}.

  Global Instance set_quotient_functor_isequiv
             (f : A -> B) (fresp : forall x y, R x y <-> S (f x) (f y))
             `{IsEquiv _ _ f}
  : IsEquiv (set_quotient_functor R S f (fun x y => fst (fresp x y))).
  Proof.
    simple refine (isequiv_adjointify _ (set_quotient_functor S R f^-1 _)
                               _ _).
    - intros u v s.
      apply (snd (fresp _ _)).
      abstract (do 2 rewrite eisretr; apply s).
    - intros x; revert x; simple refine (set_quotient_ind S _ _ _).
      + intros b; simpl. apply ap, eisretr.
      + intros; apply path_ishprop.
    - intros x; revert x; simple refine (set_quotient_ind R _ _ _).
      + intros a; simpl. apply ap, eissect.
      + intros; apply path_ishprop.
  Defined.

  Definition set_quotient_functor_equiv
             (f : A -> B) (fresp : forall x y, R x y <-> S (f x) (f y))
             `{IsEquiv _ _ f}
  : set_quotient R <~> set_quotient S
    := BuildEquiv _ _
         (set_quotient_functor R S f (fun x y => fst (fresp x y))) _.

  Definition set_quotient_functor_equiv'
             (f : A <~> B) (fresp : forall x y, R x y <-> S (f x) (f y))
  : set_quotient R <~> set_quotient S
    := set_quotient_functor_equiv f fresp.

End Functoriality.

Section Kernel.

  (** ** Quotients of kernels of maps to sets give a surjection/mono factorization. *)

  Context {fs : Funext}.

  (** A function we want to factor. *)
  Context {A B : Type} `{IsHSet B} (f : A -> B).

  (** A mere relation equivalent to its kernel. *)
  Context (R : relation A) {sR : is_mere_relation _ R}.
  Context (is_ker : forall x y, f x = f y <~> R x y).

  Theorem set_quotient_kernel_factor
  : exists (C : Type) (e : A -> C) (m : C -> B),
      IsHSet C * IsSurjection e * IsEmbedding m * (f = m o e).
  Proof.
    pose (C := set_quotient R).
    (* We put this explicitly in the context so that typeclass resolution will pick it up. *)
    assert (IsHSet C) by (unfold C; apply _).
    exists C.
    pose (e := class_of R).
    exists e.
    transparent assert (m : (C -> B)).
    { apply set_quotient_ind with f; try exact _.
      intros x y H. transitivity (f x).
      - apply transport_const.
      - exact ((is_ker x y) ^-1 H). }
    exists m.
    split.
    { split.
      { split.
        - assumption.
        - apply set_quotient_surjective. }
      intro u.
      apply hprop_allpath.
      assert (H : forall (x y : C) (p : m x = u) (p' : m y = u), x = y).
      { simple refine (set_quotient_ind R _ _ _).
        { intro a.
          simple refine (set_quotient_ind R _ _ _).
          { intros a' p p'; fold e in p, p'.
            apply related_classes_eq.
            refine (is_ker a a' _).
            change (m (e a) = m (e a')).
            exact (p @ p'^). }
          intros; apply path_ishprop. }
        intros; apply path_ishprop. }
      intros [x p] [y p'].
      apply path_sigma_hprop; simpl.
      exact (H x y p p'). }
    reflexivity.
  Defined.

End Kernel.
