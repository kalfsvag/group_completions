From GCTT Require Import quotients.
Require Import HoTT.Basics.
Require Import Types.Universe Types.Arrow Types.Sigma.
Require Import HSet HProp UnivalenceImpliesFunext TruncType.
Require Import HIT.epi HIT.Truncations HIT.Connectedness.


Definition iswelldef {A: Type} (R : relation A) {B : Type} (f : A -> B)
  := forall a a' : A, R a a' -> f a = f a'.

Definition wd (A : Type) (R : relation A) (B : Type)
  := {f : A -> B & iswelldef R f}.

Definition set_quotient_rec_uncurried (A : Type) (R : relation A) (B : Type) {isset_B : IsHSet B}
  : wd A R B -> (set_quotient R -> B).
Proof.
  intros [f iwd].
  exact (set_quotient_rec R f iwd).
Defined.

Lemma isequiv_set_quotient_rec_uncurried `{Funext} (A : Type) (R : relation A) (B : Type) {isset_B : IsHSet B}
  : IsEquiv (set_quotient_rec_uncurried A R B).
Proof.
  srapply @isequiv_adjointify.
  - intro g.
    exists (g o class_of R).
    unfold iswelldef.
    intros a a' r.
    apply (ap g).
    apply related_classes_eq. exact r.
  - intro g.
    apply path_arrow.
    intro a.
    revert a.
    srapply @set_quotient_ind_prop; reflexivity.
  - intro f. simpl.
    srapply @path_sigma_hprop. reflexivity.
Defined.

Definition double_set_quotient_rec_uncurried `{Funext} (A B : Type) (R : relation A) (S: relation B)
           (C : Type) {isset_C : IsHSet C}
  : {f : A * B -> C & (forall a : A, iswelldef S (fun b => f (a,b))) *
                      (forall b : B, iswelldef R (fun a => f(a,b)))}
      -> (set_quotient R) * (set_quotient S) -> C.
Proof.
  intros [f [wd_S wd_R]].
  intros [a b].
  revert b. revert a.  
  srapply @set_quotient_rec_uncurried.
  srapply @exist.
  - intro a.
    srapply @set_quotient_rec_uncurried.
    srapply @exist.
    + exact (fun b => f(a,b)).
    + simpl. intros b b' s.
      apply wd_S. exact s.
  - intros a a' r. simpl.
    apply (ap (set_quotient_rec_uncurried B S C)).
    apply path_sigma_hprop. simpl.
    apply path_arrow. intro b.
    apply wd_R. exact r.
Defined.

Definition isequiv_double_set_quotient_rec_uncurried `{Funext}
           (A B : Type) (R : relation A) (S: relation B) (C : Type) {isset_C : IsHSet C}
  : IsEquiv (double_set_quotient_rec_uncurried A B R S C).
Proof.
  srapply @isequiv_adjointify.
  - intro g.
    exists (g o (Prod.functor_prod (class_of R) (class_of S))).
    srapply @pair.
    + intro a.
      unfold iswelldef. intros b b' s.
      unfold Prod.functor_prod. simpl.
      apply (ap (fun x => g (class_of R a, x))).
      apply related_classes_eq. exact s.
    + intro b.
      unfold iswelldef. intros a a' r.
      apply (ap (fun x => g (x, class_of S b))).
      apply related_classes_eq. exact r.
  - intro g. simpl.
    apply path_arrow.
    intros [a b].
    revert b.
    srapply @set_quotient_ind_prop.
    revert a.
    srapply @set_quotient_ind_prop.
    intro a. simpl.
    intro b.
    reflexivity.
  - intros [f [wd_S wd_R]]. simpl.
    apply path_sigma_hprop. simpl.
    reflexivity.
Defined.

                  
      
    