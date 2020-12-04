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

Lemma compose_sum_l {M: Magma} {a1 a2 a3 b : M} (f1 : a1 --> a2) (f2 : a2 --> a3)
  : (f2 o f1) +^ (identity b) = (f2 +^ 1) o (f1 +^ 1).
Proof.
  rewrite <- composition_of. simpl.
  rewrite left_identity. reflexivity.
Qed.

Lemma compose_sum_r {M: Magma} {a b1 b2 b3 : M} (f1 : b1 --> b2) (f2 : b2 --> b3)
  : (identity a) +^ (f2 o f1) = (1 +^ f2) o (1 +^ f1).
Proof.
  rewrite <- composition_of. simpl.
  rewrite left_identity. reflexivity.
Qed.


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
   isiso_moncat_assoc : forall a b c : smon_magma, IsIsomorphism (moncat_assoc a b c);
   natural_moncat_assoc : forall (a b c a' b' c': smon_magma)
                                 (f : a-->a') (g : b --> b') (h : c --> c'),
       moncat_assoc a' b' c' o ((f +^ g) +^ h) = (f +^ (g +^ h)) o moncat_assoc a b c;
   moncat_lid : forall a : smon_magma, moncat_id +' a --> a;
   isiso_moncat_lid : forall a : smon_magma, IsIsomorphism (moncat_lid a);
   natural_moncat_lid : forall (a a' : smon_magma) (f : a --> a'),
       moncat_lid a' o (1 +^ f) = f o moncat_lid a;
   moncat_rid : forall a : smon_magma, a +' moncat_id --> a;
   isiso_moncat_rid : forall a : smon_magma, IsIsomorphism (moncat_rid a);
   natural_moncat_rid : forall (a a' : smon_magma) (f : a --> a'),
       moncat_rid a' o (f +^ 1) = f o moncat_rid a;
   moncat_sym : forall a b : smon_magma, a +' b -->  b +' a;
   isiso_moncat_sym : forall a b : smon_magma, IsIsomorphism (moncat_sym a b);
   natural_moncat_sym : forall (a b a' b' : smon_magma) (f : a --> a') (g : b --> b'),
       moncat_sym a' b' o (f +^ g) = (g +^ f) o moncat_sym a b;
   moncat_sym_inv : forall a b : smon_magma, moncat_sym a b o moncat_sym b a = 1;
   moncat_coh_tri1 : forall a b : smon_magma,
       (moncat_lid (a +' b)) o (moncat_assoc moncat_id a b) = (moncat_lid a +^ 1) ;
   moncat_coh_tri2 : forall a b : smon_magma,
       (1 +^ moncat_lid b) o (moncat_assoc a moncat_id b) = (moncat_rid a +^ 1) ;
   moncat_coh_pent : forall a b c d : smon_magma,
       (moncat_assoc a b (c +' d)) o (moncat_assoc (a +' b) c d)  =
       (1 +^ moncat_assoc b c d) o (moncat_assoc a (b +' c) d) o (moncat_assoc a b c +^ 1);
   moncat_coh_hex : forall a b c : smon_magma,
       (moncat_assoc b c a) o (moncat_sym a (b +' c)) o (moncat_assoc a b c) =
       (1 +^ moncat_sym a c) o (moncat_assoc b a c) o (moncat_sym a b +^ 1)
                       
                       (* (moncat_assoc c a b) o (symm (a+b) c) o moncat_assoc a b c = *)
                       (* (symm a c +^ 1) o (moncat_assoc a c b) o (1 +^ symm b c); (*I am guessing that this is correct*) *)
                       (* cancellation : forall (s t a : smon_magma) (f g : s --> t), (f +^ identity a) = (g +^ identity a) -> f = g *)
  }.

Definition iso_moncat_assoc (S : Symmetric_Monoidal_Category) (a b c : S)
  := Build_Isomorphic (isiso_moncat_assoc S a b c).

Definition iso_moncat_lid (S : Symmetric_Monoidal_Category) (a : S)
  := Build_Isomorphic (isiso_moncat_lid S a).

Definition iso_moncat_rid (S : Symmetric_Monoidal_Category) (a : S)
  := Build_Isomorphic (isiso_moncat_rid S a).

Definition iso_moncat_sym (S : Symmetric_Monoidal_Category) (a b : S)
  := Build_Isomorphic (isiso_moncat_sym S a b).

(* We define monoidal action in parallel to monoidal category *)

Record Monoidal_Action (S : Symmetric_Monoidal_Category) (X : PreCategory) :=
  { mon_action :> Functor (S * X) X;
    mon_action_mult : forall (a b : S) (x : X),
        mon_action ((a +' b), x) --> mon_action (a, mon_action (b, x)) ;
    isiso_mon_action_mult : forall (a b : S) (x : X),
        IsIsomorphism (mon_action_mult a b x) ;
    natl_mon_action_mult : forall (a b a' b' : S) (x x' : X)
                                  (f : a --> a') (g : b --> b') (h : x --> x'),
        mon_action_mult a' b' x' o mon_action _1 (pair_1 (f +^ g) h)  =
        mon_action _1 (pair_1 f (mon_action _1 (pair_1 g h))) o mon_action_mult a b x ;
    mon_action_id : forall x : X,
        mon_action (moncat_id S, x) --> x ;
    isiso_mon_action_id : forall x : X, IsIsomorphism (mon_action_id x) ;
    natl_mon_action_id : forall (x x' : X) (h : x --> x'),
        mon_action_id x' o mon_action _1 (pair_1 (identity _) h) =
        h o mon_action_id x;
    action_coh_tri1 : forall (a : S) (x : X),
        (mon_action_id (mon_action (a, x)) o (mon_action_mult (moncat_id _) a x) =
         (mon_action _1 (pair_1 (moncat_lid S a) 1))) ;
    action_coh_tri2 : forall (a : S) (x : X),
        (mon_action _1 (pair_1 1 (mon_action_id x)) o mon_action_mult a (moncat_id _) x =
        (mon_action _1 (pair_1 (moncat_rid S a) 1))) ;
    action_coh_pent : forall (a b c : S) (x : X),
        (mon_action_mult a b (mon_action (c, x))) o (mon_action_mult (a +' b) c x)  =
        (mon_action _1 (pair_1 1 (mon_action_mult b c x))) o (mon_action_mult a (b +' c) x) o
                                             (mon_action _1 (pair_1 (moncat_assoc _ a b c) 1));
  }.



(* Definition uncurry_action {S : Symmetric_Monoidal_Category} {X : PreCategory} *)
(*            (a : Monoidal_Action S X) *)
(*   : S -> X -> X. *)
(* Proof. *)
(*   intros s x. *)
(*   exact (a (s,x)). *)
(* Defined. *)


(* Local Notation "g +^^ h" := (mon_action _1 (pair_1 g h)) (at level 40). *)

Record Monoidal_Functor (S T : Symmetric_Monoidal_Category) : Type
  := {
      mon_fun :> Functor S T ;
      mon_fun_sum : forall (a b : S), mon_fun (a +' b) --> (mon_fun a) +' (mon_fun b) ;
      isiso_mon_fun_sum : forall (a b : S), IsIsomorphism (mon_fun_sum a b) ;
      natl_mon_fun_sum : forall (a b a' b' : S) (f : a --> a') (g : b --> b'),
          mon_fun_sum a' b' o mon_fun _1 (f +^ g) =
          mon_fun _1 (f) +^ mon_fun _1 (g) o mon_fun_sum a b ;
      mon_fun_id : mon_fun (moncat_id _) --> moncat_id _ ;
      isiso_mon_fun_id : IsIsomorphism mon_fun_id ;
      mon_fun_assoc : forall (a b c : S),
          moncat_assoc T (mon_fun a) (mon_fun b) (mon_fun c)
                       o ((mon_fun_sum a b) +^ 1)
                       o mon_fun_sum (a +' b) c
          = (1 +^ mon_fun_sum b c) o mon_fun_sum a (b +' c) o mon_fun _1 (moncat_assoc S a b c) ;
      mon_fun_lid : forall a : S,
          mon_fun _1 (moncat_lid S a)
          = moncat_lid T (mon_fun a) o (mon_fun_id +^ 1) o mon_fun_sum (moncat_id _) a ;
      mon_fun_rid : forall a : S,
          mon_fun _1 (moncat_rid S a)
          = moncat_rid T (mon_fun a) o (1 +^ mon_fun_id) o mon_fun_sum a (moncat_id _)
     }.

Definition iso_mon_fun_sum {S T : Symmetric_Monoidal_Category} (F : Monoidal_Functor S T) (a b : S)
  := Build_Isomorphic (isiso_mon_fun_sum S T F a b).

Definition iso_mon_fun_id {S T : Symmetric_Monoidal_Category} (F : Monoidal_Functor S T)
  := Build_Isomorphic (isiso_mon_fun_id S T F).

