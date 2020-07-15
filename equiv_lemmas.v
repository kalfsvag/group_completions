Require Import HoTT.

Definition equiv_emoveR_fV `{Funext} {A B C : Type} (e : A <~> B) (f : B -> C) (g : A -> C) : 
  g = f o e <~> g o e^-1 = f.
Proof.
  transitivity (g == f o e).
  { apply equiv_inverse.
    apply equiv_path_arrow. }
  transitivity (g o e^-1 == f).
  { unfold pointwise_paths.
    apply equiv_inverse.
    apply (equiv_functor_forall' e).
    intro b.
    apply (equiv_concat_l).
    apply (ap g).
    change (e^-1 (e b)) with ((e^-1 o e) b).
    apply (ap10 (f:= idmap)).
    apply path_arrow.
    intro x. apply inverse. apply (eissect e). }
    apply equiv_path_arrow.
Defined.

Definition sum_assoc (A B C : Type)
  : A + B + C -> A + (B + C).
Proof.
  intros [[a | b] | c].
  - exact (inl a).
  - exact (inr (inl b)).
  - exact (inr (inr c)).
Defined.

Definition sum_assoc_inv (A B C : Type)
  : A + (B + C) -> (A + B) + C.
Proof.
  intros [a | [b | c]].
  - exact (inl (inl a)).
  - exact (inl (inr b)).
  - exact (inr c).
Defined.

Definition equiv_sum_assoc' (A B C : Type)
  : (A + B) + C <~> A + (B + C).
Proof.
  apply (equiv_adjointify (sum_assoc A B C) (sum_assoc_inv A B C)).
  - intros [a | [b | c]]; reflexivity.
  - intros [[a | b] | c]; reflexivity.
Defined.


(* Definition equiv_emoveL `{Funext} {A B C : Type} (e : A <~> B) (f : B -> C) (g : A -> C) :  *)
(*   g = f o e <~> g o e^-1 = e f. *)
(* Proof. *)
(*   transitivity (g == f o e). *)
(*   apply equiv_inverse. *)
(*   apply equiv_path_arrow. *)
(*   transitivity (g o e^-1 == f). *)
(*   unfold pointwise_paths. *)
(*   apply equiv_inverse. *)
(*   apply (equiv_functor_forall' e). *)
(*   intro b. *)
(*   apply (equiv_concat_l). *)
(*   apply (ap g). *)
(*   change (e^-1 (e b)) with ((e^-1 o e) b). *)
(*   apply (ap10 (f:= idmap)). *)
(*   apply path_arrow. *)
(*   intro x. apply inverse. apply (eissect e). *)
(*   apply equiv_path_arrow. *)
(* Defined. *)

Lemma equiv_is_embedding `{Funext} {A B : Type} (f : A -> B) {isequiv_f : IsEquiv f}
  : IsEmbedding f.
Proof.
  unfold IsEmbedding. intro b.
  srapply @trunc_succ.
  apply fcontr_isequiv. exact isequiv_f.
Defined.

Definition ecancelL `{Funext} {A B C : Type} (f : A -> B) {isequiv_f : IsEquiv f} (g h : B -> C) :
  g o f = h o f -> g = h.
Proof.
  intro p.
  apply path_arrow.
  intro b.
  refine (ap g (eisretr f b)^ @ _ @ ap h (eisretr f b)).
  exact (ap10 p (f^-1 b)).
Defined.

Definition ecancelR `{Funext} {A B C : Type} (f g : A -> B) (h : B -> C) {isequiv_h : IsEquiv h} :
  h o f = h o g -> f = g.
Proof.
  intro p.
  apply path_arrow.
  intro a.
  refine ((eissect h (f a))^ @ _ @ (eissect h (g a))).
  exact (ap (h^-1) (ap10 p a)).
Defined.

Definition equiv_functor_sum_1 `{Funext} {A B : Type} : @equiv_idmap A +E @equiv_idmap B = equiv_idmap.
Proof.
  apply path_equiv. apply path_arrow. intros [a | b]; reflexivity.
Defined.

