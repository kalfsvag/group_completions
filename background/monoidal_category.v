Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import Functor Category.
(* From A_BPQ Require Import path_lemmas. *)
(*These notations are defined elsewhere, but I do not know how to import it.*)
Local Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
Notation "F '_0' x" := (Functor.Core.object_of F x) (at level 10, no associativity, only parsing) : object_scope.
Notation "F '_1' m" := (Functor.Core.morphism_of F m) (at level 10, no associativity) : morphism_scope.
Open Scope category_scope.
Open Scope morphism_scope.

Record Magma : Type :=
  { magma_cat :> PreCategory; binary_op : Functor (magma_cat*magma_cat) magma_cat }.
Arguments binary_op {m}.

Definition binary_op_0 {M : Magma} : ((object M) * (object M) -> object M )%type :=
  object_of binary_op.


(* Local Notation "a + b" := (Core.object_of binary_op (a, b)). (* Just for printing. *) *)
Local Notation "a +' b" := (binary_op (a, b)) (at level 40).

(* Definition binary_op_1 {M : Magma} {s1 s2 d1 d2 : object M} : *)
(*   ((s1 --> d1) * (s2 --> d2))%type -> ((s1 + s2) --> (d1 + d2)). *)
(* Proof. *)
(*   intro m. apply (morphism_of binary_op). exact m. *)
(* Defined. *)

Definition pair_1 {C D : PreCategory} {c c' : C} {d d' : D} (f : c --> c') (g : d --> d') :
  morphism (C*D) (c, d) (c', d') := (f,g).

(* Local Notation "f +^ g" := (binary_op _1 (f, g)) (at level 40). (* This is just for printing *) *)
Local Notation "f +^ g" := (binary_op _1 (pair_1 f g)) (at level 40).



(* Sum of idmaps is the idmap *)
Definition sum_idmap {M : Magma} {m n : M} : (identity m +^ identity n) = identity (m +' n) :=
  identity_of binary_op (m, n).

(* Translation from right *)
Definition translate_fr {M : Magma} (a : M) : Functor M M.
Proof.
  refine (Functor.compose (D := M*M) binary_op _).
  srapply @Build_Functor.
  (* Objects *)
  - exact (fun m => (m, a)).
  (* Morphisms *)
  - intros m n f. exact (f,identity a).
  (* Respect composition *)
  - intros l m n.
    intros f g.
    apply path_prod.
    + exact idpath.
    + apply inverse. apply left_identity.
  (* Respect identity *)
  - exact (fun _ => idpath).
Defined.

(* Translation from left *)
Definition translate_fl {M : Magma} (a : M) : Functor M M.
Proof.
  refine (Functor.compose (D := M*M) binary_op _).
  srapply @Build_Functor.
  (* Objects *)
  - exact (fun m => (a, m)).
  (* Morphisms *)
  - intros m n f. exact (identity a, f).
  (* Respect composition *)
  - intros l m n.
    intros f g.
    apply path_prod.
    + apply inverse.
      apply left_identity.
    + exact idpath. 
  (* Respect identity *)
  - exact (fun _ => idpath).
Defined.

(* Check (forall (A : Magma) (a b : A), a + b). *)

(* Record Monoidal_Category : Type := *)
(*   {moncat_cat : PreCategory ; *)
(*    moncat_prod : Functor (moncat_cat * moncat_cat) (moncat_cat) ; *)
(*    moncat_id : moncat_cat ; *)
(*    moncat_assoc : forall a b c : moncat_cat, *)
(*        moncat_prod ((moncat_prod (a, b)), c) --> moncat_prod (a, (moncat_prod (b, c))) ; *)

Record Symmetric_Monoidal_Category : Type :=
  {smon_magma :> Magma ;
   (* isgroupoid_smon_magma : forall (a b : smon_magma) (f : a --> b), IsIsomorphism f; *)
   moncat_id : smon_magma ;
   moncat_assoc : forall a b c : smon_magma, (a +' b) +' c --> a +' (b +' c);
   iso_moncat_assoc : forall a b c : smon_magma, IsIsomorphism (moncat_assoc a b c);
   natural_moncat_assoc : forall (a b c a' b' c': smon_magma)
                                 (f : a-->a') (g : b --> b') (h : c --> c'),
       moncat_assoc a' b' c' o ((f +^ g) +^ h) = (f +^ (g +^ h)) o moncat_assoc a b c;
   lid : forall a : smon_magma, moncat_id +' a --> a;
   iso_lid : forall a : smon_magma, IsIsomorphism (lid a);
   natural_lid : forall (a a' : smon_magma) (f : a --> a'),
       lid a' o (1 +^ f) = f o lid a;
   rid : forall a : smon_magma, a +' moncat_id --> a;
   iso_rid : forall a : smon_magma, IsIsomorphism (rid a);
   natural_rid : forall (a a' : smon_magma) (f : a --> a'),
       rid a' o (f +^ 1) = f o rid a;
   symm : forall a b : smon_magma, a +' b -->  b +' a;
   natural_sym : forall (a b a' b' : smon_magma) (f : a --> a') (g : b --> b'),
       symm a' b' o (f +^ g) = (g +^ f) o symm a b;
   symm_inv : forall a b : smon_magma, symm a b o symm b a = 1;
   coh_tri1 : forall a b : smon_magma,
       (lid (a +' b)) o (moncat_assoc moncat_id a b) = (lid a +^ 1) ;
   coh_tri2 : forall a b : smon_magma,
       (1 +^ lid b) o (moncat_assoc a moncat_id b) = (rid a +^ 1) ;
   coh_pent : forall a b c d : smon_magma,
       (moncat_assoc a b (c +' d)) o (moncat_assoc (a +' b) c d)  =
       (1 +^ moncat_assoc b c d) o (moncat_assoc a (b +' c) d) o (moncat_assoc a b c +^ 1);
   coh_hex : forall a b c : smon_magma,
       (moncat_assoc b c a) o (symm a (b +' c)) o (moncat_assoc a b c) =
       (1 +^ symm a c) o (moncat_assoc b a c) o (symm a b +^ 1)
                       
                       (* (moncat_assoc c a b) o (symm (a+b) c) o moncat_assoc a b c = *)
                       (* (symm a c +^ 1) o (moncat_assoc a c b) o (1 +^ symm b c); (*I am guessing that this is correct*) *)
                       (* cancellation : forall (s t a : smon_magma) (f g : s --> t), (f +^ identity a) = (g +^ identity a) -> f = g *)
  }.

(* We define monoidal action in parallel to monoidal category *)

Record Monoidal_Action (S : Symmetric_Monoidal_Category) (X : PreCategory) :=
  { mon_action :> Functor (S * X) X;
    mon_action_mult : forall (a b : S) (x : X),
        mon_action ((a +' b), x) --> mon_action (a, mon_action (b, x)) ;
    iso_mon_action_mult : forall (a b : S) (x : X),
        IsIsomorphism (mon_action_mult a b x) ;
    natl_mon_action_mult : forall (a b a' b' : S) (x x' : X)
                                  (f : a --> a') (g : b --> b') (h : x --> x'),
        mon_action_mult a' b' x' o mon_action _1 (pair_1 (f +^ g) h)  =
        mon_action _1 (pair_1 f (mon_action _1 (pair_1 g h))) o mon_action_mult a b x ;
    mon_action_id : forall x : X,
        mon_action (moncat_id S, x) --> x ;
    iso_mon_action_id : forall x : X, IsIsomorphism (mon_action_id x) ;
    natl_mon_action_id : forall (x x' : X) (h : x --> x'),
        mon_action_id x' o mon_action _1 (pair_1 (identity _) h) =
        h o mon_action_id x;
    action_coh_tri1 : forall (a : S) (x : X),
        (mon_action_id (mon_action (a, x)) o (mon_action_mult (moncat_id _) a x) =
         (mon_action _1 (pair_1 (lid S a) 1))) ;
    action_coh_tri2 : forall (a : S) (x : X),
        (mon_action _1 (pair_1 1 (mon_action_id x)) o mon_action_mult a (moncat_id _) x =
        (mon_action _1 (pair_1 (rid S a) 1))) ;
    action_coh_pent : forall (a b c : S) (x : X),
        (mon_action_mult a b (mon_action (c, x))) o (mon_action_mult (a +' b) c x)  =
        (mon_action _1 (pair_1 1 (mon_action_mult b c x))) o (mon_action_mult a (b +' c) x) o
                                             (mon_action _1 (pair_1 (moncat_assoc _ a b c) 1));
  }.



Definition uncurry_action {S : Symmetric_Monoidal_Category} {X : PreCategory}
           (a : Monoidal_Action S X)
  : S -> X -> X.
Proof.
  intros s x.
  exact (a (s,x)).
Defined.

Local Notation "a +'' x" := (uncurry_action a x) (at level 40).
Local Notation "g +^^ h" := (mon_action _1 (pair_1 g h)) (at level 40).

