Require Import HoTT.

(** A few lemmas regarding sigma types that we did not find in the HoTT library  *)


Definition distributivity `{Funext} (A : Type) (B : A -> Type) (C : forall a : A, B a -> Type) :
  (forall a : A, {b : B a & C a b}) <~> {b : forall a : A, B a & forall a : A, C a (b a)}.
Proof.
  srapply @equiv_adjointify.
  - intro x.
    exists (fun a : A => (x a).1). exact (fun a : A => (x a).2).
  - intro x.
    intro a.
    exists (x.1 a). exact (x.2 a).
  - intros [b c]. simpl. reflexivity.
  - intro. simpl. apply path_forall. intro a.
    srapply @path_sigma; reflexivity.
Defined.
  
Lemma path_sigma_hprop_compose {A : Type} {P : A -> Type} {isprop : forall a : A, IsHProp (P a)}
      (x y z: { a : A & P a}) (p : x.1 = y.1) (q : y.1 = z.1) :
  path_sigma_hprop _ _ (p @ q) = (path_sigma_hprop _ _ p) @ (path_sigma_hprop _ _ q).
Proof.
  destruct x as [x1 x2]. destruct y as [y1 y2]. destruct z as [z1 z2]. simpl in p,q.
  destruct q. destruct p. cbn.
  destruct (center _ (isprop x1 x2 z2)).
  destruct (center _ (isprop x1 x2 y2)).    
  refine (path_sigma_hprop_1 _ @ _).
  apply inverse.
  apply (concat2 (path_sigma_hprop_1 (x1; x2)) (path_sigma_hprop_1 (x1; x2))).
Defined.

(** A more general version of trunc_sigma that only requires A to be "locally truncated" wherever there is a [b : B(a)] *)
Definition trunc_sigma' {A : Type} {B : A -> Type} {n : trunc_index} :
           (forall a : A, IsTrunc (n.+1) (B a)) ->
           (forall p q : {a : A & B a}, IsTrunc n (p.1 = q.1)) ->
           IsTrunc (n.+1) {a : A & B a}.
Proof.
  intros H_B H_pq.
  intros ab ab'.
  cut (IsTrunc n ({p : ab.1 = ab'.1 & p# ab.2 = ab'.2})).
  { apply trunc_equiv'.
    exact (BuildEquiv _ _ (path_sigma_uncurried B ab ab') _). }
  apply trunc_sigma.
Defined.


Lemma equiv_sigma_sum' (A : Type) (B C : A -> Type) :
   {a : A & B a} + {a : A & C a} <~> {a : A & B a + C a}.
Proof.
  srapply @equiv_adjointify.
  - intros [[a b] | [a c]].
    + exact (a; inl b).
    + exact (a; inr c).
  - intros [a [b | c]].
    + exact (inl (a; b)).
    + exact (inr (a; c)).
  - intros [a [b | c]]; reflexivity.
  - intros [[a b] | [a c]]; reflexivity.
Defined.


(*The section corresponding to a dependent function:*)
Definition section_of {A : Type} {B : A -> Type} (f : forall a : A, B a) :
  A -> {a : A & B a} := fun a => (a ; f a).

Definition ap_section {A : Type} {B : A -> Type} (f : forall a : A, B a) {a a' : A} (p : a = a'):
  ap (section_of f) p = path_sigma B (a; f a) (a'; f a') p (apD f p).
Proof.
  destruct p. reflexivity.
Defined.

Definition refl_sigma {A : Type} {B : A -> Type} (a : A) (b : B a) : (a ; b) = (a ; b) :=
  path_sigma B _ _ idpath idpath.
  

Definition section_to_depfun {A : Type} {B : A -> Type} :
  {f : A -> {a : A & B a} | (pr1 o f == idmap)} -> (forall a : A, B a).
Proof.
  intros [f sect].
  exact (fun a => transport B (sect a) (f a).2).
Defined.

Definition equiv_path_sigma {A : Type} (P : A -> Type) (u v : {a : A & P a}) :
  u = v <~> {p : u.1 = v.1 & transport P p u.2 = v.2}.
Proof.
  srapply @equiv_adjointify.
  - intro p. destruct p. exact (idpath; idpath).
  - intros [p q].
    exact (path_sigma P u v p q).
  - intros [p q].
    destruct u as [u1 u2].
    destruct v as [v1 v2]. simpl in p.
    destruct p. simpl in q. destruct q. reflexivity.
  - intro p. destruct p. reflexivity.
Defined.

Definition path2_sigma {A : Type} (P : A -> Type) (u v : {a : A & P a})
           (p p' : u.1 = v.1)
           (q : transport P p u.2 = v.2)
           (q' : transport P p' u.2 = v.2)
           (h1 : p = p')
           (h2 : transport (fun p0 : u.1=v.1 => (transport P p0 u.2 = v.2)) h1 q = q')
  : path_sigma P u v p q = path_sigma P u v p' q'.
Proof.
  destruct u as [u1 u2].
  destruct v as [v1 v2].
  simpl in p. simpl in p'. destruct h1.
  simpl in q. simpl in q'.
  simpl in h2. destruct h2.
  destruct p. destruct q.
  reflexivity.
Defined.
  

Definition path_sigma_V {A : Type} (P : A -> Type) (u v : {a : A & P a})
           (p : u.1 = v.1) (q : transport P p u.2 = v.2)
           :
             (path_sigma P u v p q)^ =
             path_sigma P v u p^ (ap (transport P p^) q^ @ transport_Vp P p u.2).
Proof.
  destruct u as [u1 u2].
  destruct v as [v1 v2].
  simpl in p. destruct p.
  simpl in q. destruct q.
  reflexivity.
Defined.

           
  
