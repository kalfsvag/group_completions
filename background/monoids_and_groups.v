Require Import HoTT.
Require Import UnivalenceAxiom.
(* Load group_complete_1type. *)
(* Load monoidal_1type. *)


Section Monoids_and_Groups.
  Definition associative {A : Type}  (m : A->A->A) := forall a b c : A, m (m a b) c = m a (m b c).
  Definition left_identity {A : Type} (m : A->A->A) (e : A) := forall a : A, m e a = a.
  Definition right_identity {A : Type} (m : A->A->A) (e : A) := forall a : A, m a e = a.
  Definition symmetric {A : Type} (m : A->A->A) := forall a b : A, m a b = m b a.
  Definition left_inverse {A : Type} (m : A -> A -> A) (e : A) (inv : A -> A) :=
    forall a : A, m (inv a) a = e.
  Definition right_inverse {A : Type} (m : A -> A -> A) (e : A) (inv : A -> A) :=
    forall a : A, m a (inv a) = e.


  Record Monoid : Type := { mon_set :> hSet;
                            (* mon_isset : IsHSet mon_set; *)
                            mon_mult  : mon_set->mon_set->mon_set;
                            mon_id : mon_set;
                            mon_assoc : associative mon_mult;
                            mon_lid : left_identity mon_mult mon_id ;
                            mon_rid : right_identity mon_mult mon_id
                          }.

  (* Definition type_to_monoid : Monoidal_1Type -> Monoid. *)
  (* Proof. *)
  (*   intro M. *)
  (*   srapply (Build_Monoid (BuildTruncType 0 (Trunc 0 M))). *)
  (*   simpl. *)
  (*   (@mon_mult M)). *)
  

  (* Definition monoid_to_1type : Monoid -> Monoidal_1Type. *)
  (* Proof. *)
  (*   intro M. *)
  (*   srapply *)
  (*     (Build_Monoidal_1Type (BuildTruncType 1 M) *)
  (*                           (mon_mult M) (mon_id M) (mon_assoc M) (mon_lid M) (mon_rid M)). *)
  (*   - intros a b. apply (istrunc_trunctype_type M). *)
  (*   - intros a b. apply (istrunc_trunctype_type M). *)
  (*   - intros a b c d. apply (istrunc_trunctype_type M). *)
  (* Defined. *)

  (* Coercion monoid_to_1type : Monoid >-> Monoidal_1Type. *)
  

  Record Symmetric_Monoid : Type := {mon :> Monoid;
                                     mon_sym : symmetric (mon_mult mon) }.
  Global Arguments mon_sym {S} {a} {b} :rename.

  (* (*Makes mon_isset an implicit argument*) *)
  (* Global Arguments Build_Monoid mon_set {mon_isset} mon_mult mon_id mon_assoc mon_lid mon_rid. *)

  Global Arguments mon_id {M} : rename.
  Global Arguments mon_mult {M} a b : rename.
  Global Arguments mon_assoc {M} {a} {b} {c} : rename.
  Global Arguments mon_lid {M} a : rename.
  Global Arguments mon_rid {M} a : rename.

  

  Global Instance ispointed_M {M : Monoid} : IsPointed M := (@mon_id M).

  (*  (*Formulate the cancellation law for a monoid*)
  Definition right_cancellation_law (M : Monoid) :=
    forall a b s : M, a + s = b + s -> a = b.   *)
  
  Record Group : Type := {grp_mon :> Monoid;
                          grp_inv : grp_mon -> grp_mon;
                          grp_linv : left_inverse mon_mult (mon_id) grp_inv;
                          grp_rinv : right_inverse mon_mult (mon_id) grp_inv
                         }.
  
  Global Arguments grp_inv {G} a :rename.
  Global Arguments grp_linv {G} a:rename.
  Global Arguments grp_rinv {G} a:rename.

  Record Abelian_Group : Type :=
    {grp :> Group;
     grp_sym : symmetric (@mon_mult (grp_mon grp))}.

  Global Arguments grp_sym {A} {a} {b} : rename.

  (*Must do some work to get a coercion Abelian_Group >-> Symmetric_Monoid*)
  Definition forget_to_SymMon : Abelian_Group -> Symmetric_Monoid :=
    fun A => Build_Symmetric_Monoid A (@grp_sym A).

  Coercion forget_to_SymMon : Abelian_Group >-> Symmetric_Monoid.    

End Monoids_and_Groups.


Section nat_monoid.
  
  (*Strangely, I cannot find any proofs of nat being associative*)
  Open Scope nat_scope.
  Definition plus_assoc : forall j k l : nat, (j + k) + l = j + (k + l). 
    intros j k l.
    induction j.
    - exact idpath.
    - exact (ap S IHj).
  Defined.

  Definition nat_monoid : Monoid :=
    Build_Monoid
      (BuildhSet nat) Peano.plus O
      plus_assoc (fun _ => idpath) (fun n => (nat_plus_n_O n)^).

  Definition nat_symm_monoid : Symmetric_Monoid := Build_Symmetric_Monoid nat_monoid nat_plus_comm.    


  (** Cancellation in nat*)
  (** Subtraction of natural numbers.
   Is given by [m,n => -m + n] 
   This is the same as [minus] in HoTT library, but the below lemma is much easier to prove *)
  Fixpoint nat_minus (m n : nat) : nat :=
    match m with
    |0 => n (*-0 + m := m*)
    |m.+1 => match n with
             |0 => 0 (*-(m+1)+0 = 0*)
             |n.+1 => nat_minus m n (*- m+1 + n+1= -m + n*)
             end
    end.

  (* Just to show that this is the same as the old minus. *)
  Lemma nat_minus_is_minus (m n : nat) : nat_minus m n = minus n m.
  Proof.
    revert n.
    induction m.
    - induction n; reflexivity.
    - induction n.
      + reflexivity.
      + simpl. apply IHm.
  Defined.

  Definition nat_plus_minus (m n : nat) : nat_minus m (m + n) = n.
  Proof.
    induction m. 
    - reflexivity.
    - exact IHm.
  Defined.

  Definition nat_plus_cancelL (l m n : nat) : l + m = l + n -> m = n.
  Proof.
    intro p.
    refine ((nat_plus_minus l m)^ @ _ @ nat_plus_minus l n).
    apply (ap (nat_minus l) p).
  Defined.

End nat_monoid.


Declare Scope monoid_scope.
Infix "+" := mon_mult : monoid_scope.
(* Notation "a + b"  := (mon_mult a b) : monoid_scope. *)
Notation "- a" := (grp_inv a) : monoid_scope.
Notation "a - b" := (mon_mult a (grp_inv b)) : monoid_scope.

(*Just so that you dont have to remember what is monoid structure and what is group structure *)
(* Notation "grp_set G" := (mon_set (grp_mon G)) (at level 0) : monoid_scope. *)
(* Notation "grp_isset G" := (mon_isset (grp_mon G)) (at level 0) : monoid_scope. *)
Notation "'grp_id' G" := (@mon_id (grp_mon G)) (at level 0) : monoid_scope.
Notation "'grp_mult'" := (@mon_mult (grp_mon _)) (at level 0, only parsing) : monoid_scope.
Notation "'grp_assoc'" := (mon_assoc ( M := grp_mon _)) (at level 0) : monoid_scope.
Notation "'grp_lid'" := (@mon_lid (grp_mon _)) (at level 0) : monoid_scope.
Notation "'grp_rid'" := (@mon_rid (grp_mon _)) (at level 0) : monoid_scope.
Notation "'grp_rid'" := (@mon_rid (grp_mon _)) (at level 0) : monoid_scope.
(*TODO: Use this notation*)



Section Examples.
  Definition loopGroup (A : Type) (a0 : A) {istrunc_A : IsTrunc 1 A} : Group.
    srapply Build_Group.
    - exact (Build_Monoid (BuildhSet (a0 = a0)) concat idpath concat_pp_p concat_1p concat_p1). 
    - exact inverse.
    - exact concat_Vp.
    - exact concat_pV.
  Defined.

  Definition AutGroup (A : Type) `{isset_A : IsHSet A} : Group :=
    Build_Group
      (Build_Monoid (BuildhSet (A <~> A)) (fun f g => equiv_compose' g f) equiv_idmap
                    ecompose_e_ee ecompose_e1 ecompose_1e)
      equiv_inverse
      ecompose_eV
      ecompose_Ve.
  
End Examples.

Section Group_2.
  Inductive grp_2_set : Type :=
  |even : grp_2_set
  |odd : grp_2_set.


  Definition id_2 : grp_2_set -> grp_2_set :=
    fun i => if i then even else odd.

  Definition id_2_is_id : id_2 == idmap :=
    fun i => match i with
             |even => idpath
             |odd => idpath
             end.

  Definition twist_2 : grp_2_set -> grp_2_set :=
    fun i => if i then odd else even.

  Definition twist_2_twice : twist_2 o twist_2 == idmap :=
    fun i => match i with
             |even => idpath 
             |odd => idpath
             end.

  (* for some reason things freeze later if we use idmap and not id_2. . . *)
  Definition mult_2 : grp_2_set -> grp_2_set -> grp_2_set :=
    fun i =>
      if i then id_2 else twist_2.

  Global Instance isset_grp_2 : IsHSet grp_2_set.
  Proof.
    srefine (trunc_equiv' (Bool) _).
    srapply @equiv_adjointify.
    - intros [ | ].
      + exact even.
      + exact odd.
    - intros [ | ].
      + exact true.
      + exact false.
    - intros [ | ]; reflexivity.
    - intros [|]; reflexivity.
  Qed. 
  
  Definition group_2 : Group.
  Proof.
    srapply Build_Group.
    - srapply Build_Monoid.
      + exact (BuildTruncType 0 grp_2_set).
      + exact mult_2.
      (* intro b. *)
      (* exact (if b then idmap else twist_2). *)
      + exact even.
      + unfold associative.
        intros [ | ] [ | ] [ | ]; reflexivity.
      + unfold left_identity.
        intros [|]; reflexivity.
      + unfold right_identity.
        intros [|]; reflexivity.
    - simpl. exact idmap.       (* every element is its own inverse *)
    - unfold left_inverse. simpl.
      intros [|]; reflexivity.
    - unfold right_inverse. simpl.
      intros [|]; reflexivity.
  Defined.
  Open Scope monoid_scope.
  Definition symm_group_2 : forall a b : group_2,
      (a + b = b + a).
  Proof.
    intros [|] [|]; reflexivity.
  Defined.

  Definition ι : group_2 := even.
  Definition τ : group_2 := odd.
  
End Group_2.


Section Group_lemmas.
  Open Scope monoid_scope.
  Context {G : Group}.
  Definition grp_whiskerL {a b c : G} : b = c -> a + b = a + c
    := ap (fun g => a + g).

  Definition grp_whiskerR {a b c : G} : a = b -> a + c = b + c
    := ap (fun g => g + c).
  
  Definition grp_cancelR {a b : G} (s : G) :
    a + s = b + s -> a = b.
  Proof.
    intro p.      
    refine ((grp_rid a)^ @ _ @ grp_rid b).
    refine ((grp_whiskerL (grp_rinv s))^ @ _ @ grp_whiskerL (grp_rinv s)).
    refine ((grp_assoc)^ @ _ @ (grp_assoc )).
    exact (grp_whiskerR p).
  Defined.
  
  Definition grp_cancelL {a b} (s : G) :
    s + a = s + b -> a = b.
  Proof.
    intro p.
    refine ((grp_lid a)^ @ _ @ grp_lid b).
    refine ((grp_whiskerR (grp_linv s))^ @ _ @ grp_whiskerR (grp_linv s)).
    refine (grp_assoc @ _ @ grp_assoc^).
    exact (grp_whiskerL p).
  Defined.

  Definition grp_moveR_Mg {a b c : G} :
    b = -a + c -> a + b = c.
  Proof.
    intro p.
    refine (grp_whiskerL p @ _).
    refine (grp_assoc^ @ _).
    refine (grp_whiskerR (grp_rinv a) @ _).
    exact (grp_lid c).
  Defined.

  Definition grp_moveR_gM {a b c : G} :
    a = c - b -> a + b = c.
  Proof.
    intro p.
    refine (grp_whiskerR p @ _).
    refine (grp_assoc @ _).
    refine (grp_whiskerL (grp_linv b) @ _).
    exact (grp_rid c).
  Defined.      

  Definition grp_moveR_Vg {a b c : G} :
    b = a + c -> - a + b = c.
  Proof.
    intro p.
    refine (grp_whiskerL p @ _).
    refine (grp_assoc^ @ _).
    refine (grp_whiskerR (grp_linv a) @ _).
    exact (grp_lid c).
  Defined.

  Definition grp_moveR_gV {a b c : G} :
    a = c + b -> a - b = c.
  Proof.
    intro p.
    refine (grp_whiskerR p @ _).
    refine (grp_assoc @ _).
    refine (grp_whiskerL (grp_rinv b) @ _).
    exact (grp_rid c).
  Defined.

  Definition grp_moveL_Mg {a b c : G} :
    -b + a = c -> a = b + c.
  Proof.
    intro p.
    refine (_ @ grp_whiskerL p).
    refine (_ @ grp_assoc).
    refine (_ @ grp_whiskerR (grp_rinv b)^).
    exact (grp_lid a)^.
  Defined.    
  
  Definition grp_moveL_gM {a b c : G} :
    a - c = b-> a = b + c.
  Proof.
    intro p.
    refine (_ @ grp_whiskerR p).
    refine (_ @ grp_assoc^).
    refine (_ @ grp_whiskerL (grp_linv c)^).
    exact (grp_rid a)^.
  Defined.

  Definition grp_moveL_Vg {a b c : G} :
    b + a = c -> a = -b + c.
  Proof.
    intro p.
    refine (_ @ grp_whiskerL p).
    refine (_ @ grp_assoc ).
    refine (_ @ grp_whiskerR (grp_linv b)^).
    exact (grp_lid a)^.
  Defined.    

  Definition grp_moveL_gV {a b c : G} :
    a + c = b -> a = b - c.
  Proof.
    intro p.
    refine (_ @ grp_whiskerR p).
    refine (_ @ grp_assoc^ ).
    refine (_ @ grp_whiskerL (grp_rinv c)^).
    exact (grp_rid a)^.
  Defined.

  Definition grp_moveL_1M {a b : G} :
    a - b = grp_id G -> a = b.
  Proof.
    intro p.
    refine (grp_moveL_gM  p @ _).
    exact (grp_lid b).
  Defined.

  Definition grp_moveL_M1 {a b : G} :
    - a + b = grp_id G -> a = b.
  Proof.
    intro p.
    refine (_ @ (grp_moveL_Mg p)^).
    exact (grp_rid a)^ .
  Defined.

  Definition grp_moveL_1V {a b : G} :
    a + b = grp_id G -> a = - b.
  Proof.
    intro p.
    refine (grp_moveL_gV p @ _).
    exact (grp_lid (- b)).
  Defined.

  Definition grp_moveL_V1 {a b : G} :
    a + b = grp_id G -> b = - a.
  Proof.
    intro p.
    refine (grp_moveL_Vg p @ _).
    exact (grp_rid (-a)).
  Defined.
  
  Definition grp_moveR_M1 {a b : G} :
    grp_id G = -a + b -> a = b.
  Proof.
    intro p.
    refine (_ @ grp_moveR_Mg p).
    exact (grp_rid a)^ .
  Defined.

  Definition grp_moveR_1M {a b : G} :
    grp_id G = b -a -> a = b.
  Proof.
    intro p.
    refine (_ @ grp_moveR_gM p).
    exact (grp_lid a)^ .
  Defined.

  Definition grp_moveR_1V {a b : G} :
    grp_id G = b + a -> -a = b.
  Proof.
    intro p.
    refine (_ @ grp_moveR_gV p).
    exact (grp_lid (-a))^ .
  Defined.

  Definition grp_moveR_V1 {a b : G} :
    grp_id G = a + b -> -a = b.
  Proof.
    intro p.
    refine (_ @ grp_moveR_Vg p).
    exact (grp_rid (-a))^ .
  Defined.

  Definition inv_id : - (grp_id G) = grp_id G
    := grp_moveR_1V (grp_rid _)^ .

  Definition grp_inv_distr {a b: G} :
    - (a + b) = - b - a.
  Proof.
    apply grp_moveL_Vg.
    apply grp_moveR_gV.
    refine (_ @ grp_assoc).
    refine ( _ @ (grp_whiskerR (grp_linv a)^ ) ).
    exact (grp_lid b)^ .
  Defined.

  Definition path_group2 {a b c d : G} : a = c -> b = d -> a + b = c + d
    := fun p q => grp_whiskerL q @ grp_whiskerR p.

  Definition isequiv_grp_mult (g : G) :
    IsEquiv (fun a => a + g).
  Proof.
    srapply @isequiv_adjointify.
    - exact (fun a => a - g).
    - intro a. apply grp_moveR_gM. reflexivity.
    - intro a. apply grp_moveR_gV. reflexivity.
  Defined.

  Definition grp_mult_equiv (g : G) : G <~>G :=
    BuildEquiv G G (fun a => a+ g) (isequiv_grp_mult g).
  
End Group_lemmas.

Section Homomorphism.
  Open Scope type_scope.
  Open Scope monoid_scope.
  
  Record Homomorphism (M N : Monoid) :=
    {hom_map : M -> N ;
     preserve_id : hom_map (mon_id) = mon_id ;
     preserve_mult : forall m1 m2 : M, hom_map (m1 + m2) = (hom_map m1) + (hom_map m2)}. 

  Global Arguments hom_map {M N} h _.
  Global Arguments preserve_id {M N} h.
  Global Arguments preserve_mult {M N} h {m1} {m2}.

  Coercion hom_map : Homomorphism >-> Funclass.

  Definition ishom {M N : Monoid} (f : M -> N) :=
    (f (mon_id) = mon_id) * (forall m1 m2 : M, f (m1 + m2) = f m1 + f m2).
  

  Definition issig_hom (M N : Monoid) :
    {f : M -> N &  ishom f} <~> Homomorphism M N.
  Proof.
    srapply @equiv_adjointify.
    - intros [f [f_id f_mult]].
      apply (Build_Homomorphism _ _ f f_id f_mult).
    - intros [f f_id f_mult].
      exact (f; (f_id, f_mult)).
    - intros [f f_id f_mult]. reflexivity.
    - intros [f [f_id f_mult]]. reflexivity.
      
      (* equiv_via {f : M -> N & *)
      (*                       sig (fun _ : (f (mon_id) = mon_id) => *)
      (*                              (forall m1 m2 : M, f (m1 + m2) = f m1 + f m2) )}. *)
      (* - refine (equiv_functor_sigma_id _). *)
      (*   intro f. *)
      (*   apply equiv_inverse. *)
      (*   exact (equiv_sigma_prod0 _ _). *)
      (* - issig (Build_Homomorphism M N) (@hom_map M N) ( @preserve_id M N) ( @preserve_mult M N). *)
  Defined.

  Definition prop_ishom {M N : Monoid} :
    forall f : M->N, IsHProp (ishom f).
  Proof.
    intro f.
    set (A := (f (mon_id) = mon_id)).
    set (B := (forall m1 m2 : mon_set M, f (m1 + m2) = f m1 + f m2)).
    refine (@trunc_prod -1 A _ B _).
    { exact (istrunc_trunctype_type N _ _). }
    unfold B; clear A; clear B.
    set (P := fun m1 : mon_set M => forall m2, f (m1 + m2) = f m1 + f m2).
    refine (@trunc_forall _ (mon_set M) P -1 _).
    intro m1.
    unfold P; clear P.
    set (P := fun m2 : mon_set M =>
                f (m1 + m2) = f m1 + f m2).
    refine (@trunc_forall _ _ P -1 _).
    intro m2; unfold P; clear P.
    exact (istrunc_trunctype_type N _ _).
  Defined.

  Global Instance isset_hom {M N : Monoid} : IsHSet (Homomorphism M N).
  Proof.
    apply (trunc_equiv' _ (issig_hom M N)).
  Defined.  

  (*Two homomorphisms are equal if their underlying maps are equal.*)
  Definition path_hom {M N : Monoid} (f g : Homomorphism M N) :    
    (hom_map f = hom_map g) <~> f = g :> Homomorphism M N.
  Proof.
    refine ((equiv_ap (issig_hom M N)^-1 f g )^-1 oE _).
    refine (equiv_path_sigma_hprop ((issig_hom M N)^-1 f) ((issig_hom M N)^-1 g)).
  Defined.  

  Definition idhom {M : Monoid} : Homomorphism M M
    := Build_Homomorphism M M idmap idpath (fun _ _ => idpath).
  
  Definition compose_hom {L M N: Monoid} :
    Homomorphism M N -> Homomorphism L M -> Homomorphism L N.
  Proof.
    intros g f.
    refine (Build_Homomorphism _ _ (g o f) _ _).
    - exact (ap g (preserve_id f) @ (preserve_id g)).
    - intros m1 m2.
      refine ((ap g (preserve_mult f)) @ _).
      exact (preserve_mult g ).
  Defined.

  Definition Build_GrpHom {G H : Group}
             (hom_map : G -> H)
             (preserve_mult : forall g1 g2 : G,
                 hom_map (g1 + g2) = hom_map g1 + hom_map g2) :
    Homomorphism G H.
  Proof.
    srefine (Build_Homomorphism G H hom_map _ preserve_mult).
    apply (grp_cancelL (hom_map (grp_id G))).
    refine ((preserve_mult _ _)^ @ _).
    refine (ap hom_map (mon_lid (grp_id G)) @ _).
    apply grp_moveL_Mg.
    refine (grp_linv _ ).
  Defined.    

  (*A homomorphism of groups preserve inverses*)
  Definition preserve_inv {G H : Group} (f : Homomorphism G H) (a : G) :
    f (- a) = - (f a).
  Proof.
    apply grp_moveL_V1.
    refine ((preserve_mult f)^ @ _).
    refine (_ @ preserve_id f).
    exact (ap f (grp_rinv a)).
  Defined.
End Homomorphism.

Notation "'Hom'" := Homomorphism : monoid_scope.
Infix "oH" := compose_hom (at level 40, left associativity).

(* move? *)
Definition homcompose_f_ff {K L M N : Monoid}
           (f : Homomorphism K L) (g : Homomorphism L M) (h : Homomorphism M N)
  : h oH (g oH f) = (h oH g) oH f.
Proof.
  apply path_hom. reflexivity.
Defined.





Section Isomorphism.
  Class Isomorphism (M N : Monoid) :=
    {iso_hom : Homomorphism M N; iso_isequiv : IsEquiv iso_hom}.

  Arguments iso_hom {M} {N}.
  Arguments iso_isequiv {M} {N}.

  Definition iso_fun {M N : Monoid} (f : Isomorphism M N) : (M -> N) :=
    hom_map (iso_hom f).

  Coercion iso_hom : Isomorphism >-> Homomorphism.  

  Global Instance isequiv_iso (M N : Monoid) (f : Isomorphism M N) : IsEquiv f := iso_isequiv f.

  Definition issig_isomorphism (M N : Monoid) :
    {f : Homomorphism M N & IsEquiv f} <~> Isomorphism M N.
  Proof.
    issig (Build_Isomorphism M N) (@iso_hom M N) (@iso_isequiv M N).
  Defined.

  Definition path_isomorphism (M N : Monoid) (f g : Isomorphism M N) :
    iso_hom f = iso_hom g <~> f = g.
  Proof.
    refine ((equiv_ap (issig_isomorphism M N)^-1 f g )^-1 oE _).        
    refine (equiv_path_sigma_hprop ((issig_isomorphism M N)^-1 f) ((issig_isomorphism M N)^-1 g)).
  Defined.

  Definition Build_Isomorphism' (M N : Monoid)
             (f : M <~> N)
             (preserve_id : f (mon_id) = mon_id)
             (preserve_mult : forall (a b : M), f (mon_mult a b) = mon_mult (f a) (f b))
    : Isomorphism M N :=
    (Build_Isomorphism M N (Build_Homomorphism M N f preserve_id preserve_mult) _).

  Definition Build_Grp_Iso' (G F : Group)
             (f : G <~> F)
             (preserve_mult : forall (a b : G), f (mon_mult a b) = mon_mult (f a) (f b))
    : Isomorphism G F :=
    (Build_Isomorphism G F (Build_GrpHom f preserve_mult) _).

  Definition iso_id (M : Monoid) : Isomorphism M M :=
    Build_Isomorphism M M idhom _.    

  Definition iso_inv {M N : Monoid} (f : Isomorphism M N) :
    Isomorphism N M.
  Proof.
    srapply @Build_Isomorphism.
    - srapply @Build_Homomorphism.
      + exact (f^-1).
      + apply moveR_equiv_V.
        exact (preserve_id f)^.
      + intros.
        apply moveR_equiv_V. apply inverse.
        refine (preserve_mult f  @ _).
        apply (ap011 mon_mult); apply eisretr.
    - exact _.
  Defined.

  Definition iso_compose {L M N : Monoid} (f : Isomorphism M N) (g : Isomorphism L M) :
    Isomorphism L N.
  Proof.
    srapply @Build_Isomorphism.
    - exact (f oH g).
    - simpl. apply isequiv_compose.
  Defined.

  Definition isoisretr {M N : Monoid} (f : Isomorphism M N) :
    f oH (iso_inv f) = idhom.
  Proof.
    apply path_hom. apply path_arrow. apply (eisretr f).
  Defined.


End Isomorphism.


Section HomFunctor.
  Open Scope monoid_scope.
  Definition functor_hom {X1 X2 Y1 Y2 : Monoid}
             (f1 : Homomorphism Y1 X1) (f2 : Homomorphism X2 Y2)
    : Homomorphism X1 X2 -> Homomorphism Y1 Y2 :=
    fun g => f2 oH g oH f1.

  Lemma isequiv_functor_hom {X1 X2 Y1 Y2 : Monoid}
        (f1 : Isomorphism Y1 X1) (f2 : Isomorphism X2 Y2)  :
    IsEquiv (functor_hom f1 f2).
  Proof.
    srapply @isequiv_adjointify.
    - exact (functor_hom (iso_inv f1) (iso_inv f2)).
    - intro f. apply path_hom.
      simpl. apply path_arrow. intro x.
      rewrite eisretr. rewrite eissect. reflexivity.
    - intro f. apply path_hom. simpl. apply path_arrow. intro x.
      rewrite eisretr. rewrite eissect. reflexivity.
  Qed.

  Definition equiv_functor_hom {X1 X2 Y1 Y2 : Monoid}
             (f1 : Isomorphism Y1 X1) (f2 : Isomorphism X2 Y2) :
    Homomorphism X1 X2 <~> Homomorphism Y1 Y2 :=
    BuildEquiv _ _ (functor_hom f1 f2) (isequiv_functor_hom f1 f2).

  (* A version of equiv_functor_hom that stays covariant in both arguments *)
  Definition equiv_functor_hom' {X1 X2 Y1 Y2 : Monoid}
    : Isomorphism X1 Y1 -> Isomorphism X2 Y2 -> (Homomorphism X1 X2 <~> Homomorphism Y1 Y2).
  Proof.
    intros f g. apply equiv_functor_hom.
    - apply iso_inv. exact f.
    - exact g.
  Defined.


  Lemma functor_hom_compose {X1 X2 Y1 Y2 Z1 Z2}
        (f1 : Homomorphism Y1 X1) (f2 : Homomorphism X2 Y2)
        (g1 : Homomorphism Z1 Y1) (g2 : Homomorphism Y2 Z2)
    : functor_hom (f1 oH g1) (g2 oH f2) ==
      functor_hom g1 g2 o functor_hom f1 f2 .
  Proof.
    intro h.
    apply path_hom. reflexivity.
  Defined.


  Definition equiv_functor_hom_compose {X1 X2 Y1 Y2 Z1 Z2 : Monoid}
             (f1 : Isomorphism X1 Y1) (f2 : Isomorphism X2 Y2)
             (g1 : Isomorphism Y1 Z1) (g2 : Isomorphism Y2 Z2)
    : equiv_functor_hom' (iso_compose g1 f1) (iso_compose g2 f2) ==
      equiv_functor_hom' g1 g2 oE equiv_functor_hom' f1 f2.
  Proof.
    intro x.
    refine (_ @ functor_hom_compose _ _ _ _ _).
    unfold equiv_functor_hom'.
    apply (ap (fun e => functor_hom e (g2 oH f2) x)).
    apply path_hom. reflexivity.
  Defined.

  Definition functor_hom_id (X Y : Monoid)
             (f : Isomorphism X Y) :
    functor_hom (iso_inv f) f idhom == idhom.
  Proof.
    unfold functor_hom. simpl.
    intro x. apply eisretr.
  Defined.

  Definition functor_hom_compose_001 {X1 X2 X3 Y1 Y2 Y3: Monoid}
             (f1 : Homomorphism Y1 X1) 
             (f2 : Isomorphism Y2 X2)
             (f3 : Homomorphism X3 Y3)
             (h1 : Homomorphism X1 X2) (h2 : Homomorphism X2 X3)
    : functor_hom f1 f3 (h2 oH h1)
      =
      (functor_hom f2 f3 h2) oH (functor_hom f1 (iso_inv f2) h1).
  Proof.
    apply path_hom. apply path_arrow. simpl. intro x.
    apply (ap (f3 o h2)).
    apply inverse. apply eisretr.
  Defined.
  



End HomFunctor.

Section Product.
  Open Scope monoid_scope.
  Definition mon_prod (M N : Monoid) : Monoid.
  Proof.
    srapply @Build_Monoid.
    - exact (BuildTruncType 0 (M * N)).
    - simpl.
      intros [m1 n1] [m2 n2].
      exact (m1 + m2, n1 + n2).
    - exact (mon_id, mon_id).
    - simpl. unfold associative.
      intros [m1 n1] [m2 n2] [m3 n3].
      apply path_prod;
        apply mon_assoc.
    - unfold left_identity. simpl.
      intros [m n]. apply path_prod; apply mon_lid.
    - intros [m n]. apply path_prod; apply mon_rid.
  Defined.

  Definition grp_prod (G H : Group) : Group.
  Proof.
    srapply @Build_Group.
    - exact (mon_prod G H).
    - simpl.
      intros [g h]. exact (grp_inv g, grp_inv h).
    - unfold left_inverse. simpl.
      intros [g h].
      apply path_prod; apply grp_linv.
    - intros [g h].
      apply path_prod; apply grp_rinv.
  Defined.

  (** If a group is abelian, then the multiplication G*G -> G is a homomorphism *)
  Definition mult_hom (M : Monoid) (symm_M : symmetric (@mon_mult M))
    : Homomorphism (mon_prod M M) M.
  Proof.
    srapply @Build_Homomorphism.
    - intros [m n].
      exact (m + n).
    - apply mon_lid.
    - simpl. intros [m1 n1] [m2 n2].
      refine (mon_assoc @ _ @ mon_assoc^).
      apply (ap (mon_mult m1)).
      refine (mon_assoc^ @ _ @ mon_assoc).
      apply (ap (fun x => x + n2)).
      apply symm_M.
  Defined.

  Definition mon_prod_hom {M1 M2 N1 N2 : Monoid}
             (f1 : Homomorphism M1 N1)
             (f2 : Homomorphism M2 N2) :
    Homomorphism (mon_prod M1 M2) (mon_prod N1 N2).
  Proof.
    srapply @Build_Homomorphism.
    - exact (functor_prod f1 f2).
    - apply path_prod; apply preserve_id.
    - intros [m1 m2] [n1 n2].
      apply path_prod; apply preserve_mult.
  Defined.

  Definition iso_prod_hom {M1 M2 N1 N2 : Monoid}
             (f1 : Isomorphism M1 N1)
             (f2 : Isomorphism M2 N2) :
    Isomorphism (mon_prod M1 M2) (mon_prod N1 N2).
  Proof.
    apply (Build_Isomorphism _ _ (mon_prod_hom f1 f2)).
    apply isequiv_functor_prod.
  Defined.

  (* move? *)
  Definition functor_mon_prod {A1 A2 B1 B2 C1 C2 D1 D2}
             (f1 : Homomorphism C1 A1)
             (f2 : Homomorphism C2 A2)
             (g1 : Homomorphism B1 D1)
             (g2 : Homomorphism B2 D2)
             (h1 : Homomorphism A1 B1)
             (h2 : Homomorphism A2 B2)
    : mon_prod_hom
        (functor_hom f1 g1 h1)
        (functor_hom f2 g2 h2)
      = functor_hom (mon_prod_hom f1 f2) (mon_prod_hom g1 g2) (mon_prod_hom h1 h2).
  Proof.
    apply path_hom. apply path_arrow. intros [c1 c2]; reflexivity.
  Defined.

  (* move? *)
  Definition mon_prod_hom_compose {A1 A2 A3 B1 B2 B3 : Monoid}
             (f1 : Homomorphism A1 A2)
             (f2 : Homomorphism A2 A3)
             (g1 : Homomorphism B1 B2)
             (g2 : Homomorphism B2 B3)
    : mon_prod_hom (f2 oH f1) (g2 oH g1) = mon_prod_hom f2 g2 oH mon_prod_hom f1 g1.
  Proof.
    apply path_hom. apply path_arrow. intros [a b]. reflexivity.
  Defined.

  Definition mon_prod_hom_id (A1 A2 : Monoid)
    : mon_prod_hom (@idhom A1) (@idhom A2) = @idhom (mon_prod A1 A2).
  Proof.
    apply path_hom. apply path_arrow. intros [a1 a2]. reflexivity.
  Defined.


End Product.


(* Require Import B_Aut. *)
(* Section Iso_Loop_Aut. *)
(*   Context (X : Type) `{IsHSet X}. *)


(*   (* Global Instance istrunc_BAut : IsTrunc 1 B_Aut. *) *)
(*   (* Proof. *) *)
(*   (*   intros x y. change (IsTrunc_internal 0) with IsHSet. *) *)
(*   (*   apply (trunc_equiv' (x.1 <~> y.1)). *) *)
(*   (*   - refine (_ oE equiv_path_universe _ _ ). *) *)
(*   (*     apply equiv_path_sigma_hprop. *) *)
(*   (*   - srapply @istrunc_equiv. *) *)
(*   (*     destruct y as [y e]. strip_truncations. simpl. *) *)
(*   (*     apply (trunc_equiv' X (equiv_inverse e)). *) *)
(*   (* Qed. *) *)

(*   Definition iso_loop_aut : *)
(*     Isomorphism  (AutGroup X) *)
(*                  (loopGroup *)
(*                     (Build_pType *)
(*                        {A : Type & merely (A <~> X)} *)
(*                        (X; tr (equiv_idmap)))). *)
(*                        (B_Aut X) _)). *)
(*   Proof. *)
(*     srapply @Build_Isomorphism. *)
(*     - srapply @Build_GrpHom. *)
(*       + simpl. unfold point. *)
(*         refine (_ oE equiv_path_universe X X). *)
(*         refine (equiv_path_sigma_hprop (_;_) (_;_)).  *)
(*       + simpl. intros. *)
(*         refine (_ @ path_sigma_hprop_pp _ _ _ _ _). *)
(*         apply (ap (path_sigma_hprop (_; _) (_; _)) (path_universe_compose_uncurried g1 g2)). *)
(*     - exact _. *)
(*   Defined. *)
(* End Iso_Loop_Aut. *)

Definition hom_prod_loopGroup
           (A B : Type) (a0 : A) (b0 : B)
           {istrunc_A : IsTrunc 1 A}
           {istrunc_B : IsTrunc 1 B}
  : Homomorphism (loopGroup (A*B) (a0, b0))
                 (grp_prod (loopGroup A a0) (loopGroup B b0)).
Proof.
  srapply @Build_Homomorphism.
  - exact (fun p => (ap fst p, ap snd p)).
  - reflexivity.
  - simpl. intros p q.
    apply path_prod; simpl; refine (ap_pp _ p q).
Defined.

Definition isequiv_prod_loopGroup
           (A B : pType) (a0 : A) (b0 : B)
           {istrunc_A : IsTrunc 1 A}
           {istrunc_B : IsTrunc 1 B}
  : IsEquiv (hom_prod_loopGroup A B a0 b0).
Proof.
  simpl. srapply @isequiv_adjointify.
  - intros [p q]. unfold point.
    exact (path_prod (_,_) (_,_) p q).
  - simpl. intros [[] [] ]. reflexivity.
  - simpl. intro p. 
    revert p.
    cut (forall (ab : A * B) (p : (a0, b0) = ab),
            path_prod (a0,b0) ab (ap fst p) (ap snd p) = p).
    { intro H. apply H. }
    intros ab []. reflexivity.
Defined.    

Definition iso_prod_loopGroup
           (A B : pType) (a0 : A) (b0 : B)
           {istrunc_A : IsTrunc 1 A}
           {istrunc_B : IsTrunc 1 B} :
  Isomorphism (loopGroup (A*B) (a0,b0))
              (grp_prod (loopGroup A a0) (loopGroup B b0))
  := Build_Isomorphism _ _ (hom_prod_loopGroup A B a0 b0) (isequiv_prod_loopGroup A B a0 b0).
(* Proof. *)
(*   srapply Build_Grp_Iso'. *)
(*   - simpl. *)

(*     apply equiv_inverse. *)
(*     apply (equiv_path_prod (_,_)(_,_)). *)
(*   - simpl. intros p q. revert p q. *)
(*     cut (forall (a b: A1*A2) (p : point (A1 * A2) = a) (q : a = b), *)
(*             (ap fst (p @ q), ap snd (p @ q)) = (ap fst p @ ap fst q, ap snd p @ ap snd q)). *)
(*     { intro H. apply H. } *)
(*     intros a b p []. destruct p. reflexivity. *)
(* Defined. *)

(* The rest here is important, don't forget it! *)


(* (* Defining sets with a monoid action (see MacLane, p5) *) *)
(* Section Monoid_action. *)
(*   Open Scope monoid_scope. *)
(*   Record Monoid_Action (M : Monoid) (X : hSet) := {function_of : M -> (X -> X); *)
(*                                                    assoc_function_of : forall (m1 m2 : M) (x : X), *)
(*                                                        function_of m1 (function_of m2 x) = function_of (m1 + m2) x; *)
(*                                                    preserve_id_function_of : forall x : X, *)
(*                                                        function_of (mon_id M) x = x *)
(*                                                   }. *)
(*   Arguments function_of {M} {X} _ _ _. *)
(*   Definition product_action (M : Monoid) : Monoid_Action M (BuildhSet (M*M)). *)
(*   Proof. *)
(*     srapply (@Build_Monoid_Action). *)
(*     (* The action *) *)
(*     - intro m. *)
(*       intros [a b]. *)
(*       exact (m + a, m + b). *)
(*     - intros m1 m2 [x1 x2]. *)
(*       apply path_prod; apply mon_assoc. *)
(*     - intros [x1 x2]. apply path_prod; apply mon_lid. *)
(*   Defined. *)

(*   (* [S X] *) *)
(*   (* The quotient X/~, where x ~ y if there is a s : S s.t. s + x = y *) *)
(*   Definition grp_compl_relation {M : Monoid} (X : hSet) (a : Monoid_Action M X) : relation X *)
(*     := (fun x y => {m : M | function_of a m x = y}). *)

(*   Lemma relation_is_mere {M : Monoid} (X : hSet) *)
(*         (a : Monoid_Action M X) *)
(*         (isfree_a : forall (m1 m2 : M) (x : X), (function_of a m1 x = function_of a m2 x -> m1 = m2)) *)
(*     : is_mere_relation X (grp_compl_relation X a). *)
(*   Proof. *)
(*     intros. *)
(*     unfold grp_compl_relation. *)
(*     apply (trunc_sigma' _). *)
(*     - intros [m1 p1] [m2 p2]. simpl. *)
(*       apply (contr_inhabited_hprop _). *)
(*       exact (isfree_a m1 m2 x (p1 @ p2^)). *)
(*   Qed. *)

(*   Definition isfree_product_action (M : Monoid) (right_cancellation_M : forall l m n : M, m + l = n + l -> m = n) *)
(*     : forall (m1 m2 : M) (x : M*M), *)
(*       function_of (product_action M) m1 x = function_of (product_action M) m2 x -> m1 = m2. *)
(*   Proof. *)
(*     intros m1 m2 [x1 x2]. simpl. *)
(*     intro p. *)
(*     apply (right_cancellation_M x1). *)
(*     exact (ap fst p). *)
(*   Defined. *)

(*   Definition group_completion (M : Monoid) (right_cancellation_M : forall l m n : M, m + l = n + l -> m = n) : Type. *)
(*   Proof. *)
(*     refine (quotient (grp_compl_relation (BuildhSet (M*M)) (product_action M)) *)
(*                     (sR := relation_is_mere (BuildhSet (M*M)) (product_action M) (isfree_product_action _ right_cancellation_M))). *)
(*   Defined. *)

(*   (* TODO: Make this cleaner, move to group_completion, and see if the same stuff can be proved. *) *)




(*   Definition divide_action (S : Symmetric_Monoid) (X: hSet) (action : Monoid_Action S X): hSet. *)
(*   Proof. *)



(* End Monoid_action. *)

(* Section MonType_to_Mon. *)
(*   (* Truncating a monoidal category to a monoid *) *)
(*   Definition montype_to_monoid : Monoidal_1Type -> Monoid. *)
(*   Proof. *)
(*     intro S. *)
(*     srapply @Build_Monoid. *)
(*     - exact (BuildTruncType 0 (Trunc 0 S)). *)
(*     - intro a. *)
(*       apply Trunc_rec. *)
(*       revert a. *)
(*       simpl. *)
(*       apply (Trunc_rec (A := S) (X := S -> Trunc 0 S)). *)
(*       intros a b. *)
(*       apply tr. exact (montype_mult a b). *)
(*     - exact (tr montype_id). *)
(*     - unfold associative. simpl. *)
(*       intros a b c. *)
(*       strip_truncations. simpl. *)
(*       apply (ap tr). apply montype_assoc. *)
(*     - unfold left_identity_mult. *)
(*       intro a. strip_truncations. simpl. *)
(*       apply (ap tr). apply montype_lid. *)
(*     - unfold right_identity_mult. intro a. *)
(*       strip_truncations. simpl. *)
(*       apply (ap tr). apply montype_rid. *)
(*   Defined. *)

(*   Definition functor_montype_to_monoid {M N : Monoidal_1Type} : *)
(*     Monoidal_Map M N -> Homomorphism (montype_to_monoid M) (montype_to_monoid N). *)
(*   Proof. *)
(*     intro f. *)
(*     srapply @Build_Homomorphism. *)
(*     - simpl. apply Trunc_rec. intro a. *)
(*       apply tr. exact (f a). *)
(*     - apply (ap tr). apply montype_map_id. *)
(*     - intros a b. strip_truncations. simpl. *)
(*       apply (ap tr). apply montype_map_mult. *)
(*   Defined. *)

(*   Definition sym_montype_to_monoid : Symmetric_Monoidal_1Type -> Symmetric_Monoid. *)
(*   Proof. *)
(*     intro S. *)
(*     apply (Build_Symmetric_Monoid (montype_to_monoid S)). *)
(*     unfold symmetric. intros a b. strip_truncations. simpl. *)
(*     apply (ap tr). apply smontype_sym. *)
(*   Defined. *)


(*   Definition group_group_completion_to_monoid (S : Symmetric_Monoidal_1Type) *)
(*              {faithful_S : left_faithful (@montype_mult S)} *)
(*     : Abelian_Group. *)
(*   Proof. *)
(*     srapply @Build_Abelian_Group. *)
(*     srapply @Build_Group. *)
(*     srapply @Build_Monoid. *)
(*     - exact (BuildTruncType 0 (Trunc 0 (group_completion S faithful_S))). *)
(*     - simpl. intro a. *)
(*       apply Trunc_rec. revert a. *)
(*       apply (Trunc_rec (A := S*S) (X := S*S -> Trunc 0 (S*S))). *)
(*       intros a b. apply tr. revert a b. *)
(*       apply (mult_group_completion S faithful_S). *)
(*     - simpl. *)
(*       exact (tr (smontype_id, smontype_id)). *)
(*     - unfold associative. simpl. *)
(*       intros a b c. strip_truncations. simpl. apply (ap tr). *)






(*   Definition equiv_group_completion_to_monoid (S : Symmetric_Monoidal_Type) : *)
(*     group_ *)




