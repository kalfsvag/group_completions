Require Import HoTT.
Require Import UnivalenceAxiom.

From A_BPQ Require Import path_lemmas.

(** We definine the type of monoidal 1-Types (this corresponds to a monoidal category)*)
Definition associative {A : Type}  (m : A-> A -> A) := forall (a b c: A),  m (m a b) c = m a (m b c).
Definition left_identity_mult {A : Type} (m : A->A->A) (e : A) := forall a : A, m e a = a.
Definition right_identity_mult {A : Type} (m : A->A->A) (e : A) := forall a : A, m a e = a.

(* Unneccesary but perhaps easier to just assume *)
Definition coherence_triangle1 {A : Type} {m : A -> A -> A} {e : A}
           (assoc : associative m) (lid : left_identity_mult m e)  :=
  forall a b : A,
    ap (fun x => m x b) (lid a) = assoc e a b @ lid (m a b).

Definition coherence_triangle2 {A : Type} {m : A -> A -> A} {e : A}
           (assoc : associative m) (lid : left_identity_mult m e) (rid : right_identity_mult m e) :=
  forall a b : A,
    ap (fun c => m c b) (rid a) = assoc a e b @ ap (m a) (lid b).

Definition coherence_pentagon {A : Type} {m : A -> A -> A} (assoc : associative m) :=
  forall a b c d: A,
    ap (fun x => m x d) (assoc a b c) =
    assoc (m a b) c d @ assoc a b (m c d) @ (ap (m a) (assoc b c d))^ @ (assoc a (m b c) d)^.


Record Monoidal_1Type : Type := { montype_type :> 1-Type;
                                  montype_mult  : montype_type->montype_type->montype_type;
                                  montype_id : montype_type;
                                  montype_assoc : associative montype_mult;
                                  montype_lid : left_identity_mult montype_mult montype_id ;
                                  montype_rid : right_identity_mult montype_mult montype_id ;
                                  montype_triangle1 : coherence_triangle1 montype_assoc montype_lid ;
                                  montype_triangle2 : coherence_triangle2 montype_assoc montype_lid montype_rid ;
                                  montype_pentagon : coherence_pentagon montype_assoc
                                }.

Global Arguments montype_mult {M} a b : rename.
Global Arguments montype_id {M} : rename.
Global Arguments montype_assoc {M} a b c : rename.
Global Arguments montype_lid {M} a : rename.
Global Arguments montype_rid {M} a : rename.


Infix "⊗" := montype_mult (at level 50,no associativity).

Definition left_faithful {A B : Type} (m : A -> B -> B) :=
  forall (s t : A) (p q : s = t) (b : B),
    ap (fun x => m x b) p = ap (fun x => m x b) q -> p = q.



Section Monoidal_Map.
  (** Definining monoidal maps.  *)
  Record Monoidal_Map (M N : Monoidal_1Type) :=
    {montype_map :> M -> N;
     montype_map_mult (a b : M) : montype_map (a ⊗ b) = (montype_map a) ⊗ (montype_map b) ;
     montype_map_id : montype_map (montype_id) = montype_id;
     montype_map_assoc (a b c : M) :
       ap montype_map (montype_assoc a b c) =
       montype_map_mult (a ⊗ b) c @ ap (fun x => x ⊗ (montype_map c)) (montype_map_mult a b) @
                        montype_assoc (montype_map a) (montype_map b) (montype_map c) @
                        (ap (montype_mult (montype_map a)) (montype_map_mult b c))^
       @ (montype_map_mult a (b ⊗ c))^ ;
     montype_map_lid (x : M)
     : ap montype_map (montype_lid x) =
       montype_map_mult montype_id x @
                        ap (fun s => s ⊗ montype_map x) montype_map_id @ montype_lid (montype_map x);
     montype_map_rid (x : M)
     : ap montype_map (montype_rid x) =
       montype_map_mult x montype_id @ ap (montype_mult (montype_map x)) montype_map_id
                        @ montype_rid (montype_map x) }.
  
  Global Arguments montype_map_mult {M N} F a b : rename.
  Global Arguments montype_map_id {M N} F : rename.
  Global Arguments montype_map_assoc {M N} F a b c : rename.
  Global Arguments montype_map_lid {M N} F a : rename.
  Global Arguments montype_map_rid {M N} F a : rename.

  Definition monoidal_map_id (M : Monoidal_1Type) : Monoidal_Map M M.
  Proof.
    srapply (Build_Monoidal_Map M M idmap); try reflexivity.
    - intros. simpl.
      rewrite ap_idmap. repeat rewrite concat_p1. apply inverse. apply concat_1p.
  Defined.
  
  Definition monoidal_map_compose (M N O : Monoidal_1Type) :
    Monoidal_Map M N -> Monoidal_Map N O -> Monoidal_Map M O.
  Proof.
    intros F G.
    srapply @Build_Monoidal_Map.
    - exact (G o F).
    - intros a b.
      refine (ap G (montype_map_mult F a b) @ montype_map_mult G _ _).
    - refine (ap G (montype_map_id F) @ montype_map_id G).
    - intros.
      refine (ap_compose F G _ @ _).
      refine (ap (ap G) (montype_map_assoc F a b c) @ _).
      repeat rewrite ap_pp.
      rewrite (montype_map_assoc G (F a) (F b) (F c)). 
      repeat rewrite (concat_pp_p). apply whiskerL.
      repeat rewrite <- (ap_compose G).
      rewrite ap_V. rewrite ap_V. 
      rewrite <- (ap_compose (montype_mult (F a)) G (montype_map_mult F b c)).
      rewrite <- (ap_compose (fun x : N => x ⊗ F c) G).
      rewrite inv_pp. rewrite inv_pp. 
      
      repeat rewrite concat_p_pp.
      assert (H : (ap (fun x : N => G (x ⊗ F c)) (montype_map_mult F a b) @ montype_map_mult G (F a ⊗ F b) (F c)) =
                  (montype_map_mult G (F (a ⊗ b)) (F c) @ ap (fun x : N => G x ⊗ G (F c)) (montype_map_mult F a b))).
      { destruct (montype_map_mult F a b). hott_simpl. }
      rewrite H. repeat rewrite concat_pp_p. repeat (apply whiskerL).
      repeat rewrite concat_p_pp. apply whiskerR.
      destruct (montype_map_mult F b c). hott_simpl.
    - intro x.
      refine (ap_compose F G _ @ _).
      refine ( ap (ap G) (montype_map_lid F x) @ _).
      refine (ap_pp G _ _ @ _).
      refine (ap (fun p => p @ ap G (montype_lid (F x))) (ap_pp G _ _) @ _).
      refine (whiskerL _ (montype_map_lid G (F x)) @ _).
      repeat refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      repeat refine (concat_pp_p _ _ _ @ _).
      repeat refine (_ @ concat_p_pp _ _ _). apply whiskerL.
      refine (_ @ whiskerL _ (ap_pp (fun s : O => s ⊗ G (F x)) _ _)^).
      repeat refine (_ @ concat_pp_p _ _ _).
      repeat refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      refine (whiskerR (ap_compose _ G (montype_map_id F))^ _ @ _).
      refine (_ @ whiskerL _ (ap_compose G _ (montype_map_id F))).
      destruct (montype_map_id F). cbn.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intro x.
      refine (ap_compose F G _ @ _ ).
      refine ( ap (ap G) (montype_map_rid F x) @ _).
      refine (ap_pp G _ _ @ _).
      refine (ap (fun p => p @ ap G (montype_rid (F x))) (ap_pp G _ _) @ _).
      refine (whiskerL _ (montype_map_rid G (F x)) @ _).
      repeat refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      repeat refine (concat_pp_p _ _ _ @ _).
      repeat refine (_ @ concat_p_pp _ _ _). apply whiskerL.
      refine (_ @ whiskerL _ (ap_pp (fun s : O => G (F x) ⊗ s) _ _)^).
      repeat refine (_ @ concat_pp_p _ _ _).
      repeat refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      refine (whiskerR (ap_compose _ G (montype_map_id F))^ _ @ _).
      refine (_ @ whiskerL _ (ap_compose G _ (montype_map_id F))).
      destruct (montype_map_id F). cbn.
      exact (concat_1p _ @ (concat_p1 _)^).
  Defined.
  

  (** Given a 1-Type X, the type X->X is a monoidal 1-type *)
  Definition endomorphism (X : 1-Type) : Monoidal_1Type.
  Proof.
    srapply @Build_Monoidal_1Type.
    - apply (BuildTruncType 1 (X -> X)).
    - intros f g. exact (f o g).
    - cbn. exact idmap.
    - cbn. unfold associative. reflexivity.
    - cbn. unfold left_identity_mult. reflexivity.
    - cbn. unfold right_identity_mult. reflexivity.
    - unfold coherence_triangle1. cbn. reflexivity.
    - unfold coherence_triangle2. cbn. reflexivity.
    - unfold coherence_pentagon. cbn. reflexivity.
  Defined.
  
  Definition to_endomorphism (M : Monoidal_1Type) : Monoidal_Map M (endomorphism M).
  Proof.    
    srapply @Build_Monoidal_Map.
    - simpl. apply montype_mult.
    - intros a b. apply path_arrow. intro c.
      apply montype_assoc.
    - apply path_arrow. apply montype_lid.
    - intros a b c. simpl. hott_simpl.
      transitivity (path_arrow _ _ (fun d : M => ap (fun x : M => x ⊗ d) (montype_assoc a b c)));
        simpl.     
      { destruct (montype_assoc a b c). simpl. apply inverse. apply path_forall_1. }      
      rewrite (path_forall _ _ (montype_pentagon M a b c) ).
      repeat rewrite path_arrow_pp.
      rewrite path_arrow_V. rewrite path_arrow_V.
      apply whiskerR. apply concat2.
      + apply whiskerL.
        apply inverse.
        refine (ap_functor_arrow _ idmap (montype_mult (a ⊗ b)) (fun x : M => a ⊗ (b ⊗ x)) (fun c0 : M => montype_assoc a b c0) @ _).
        apply (ap (path_arrow (fun b0 : M => (a ⊗ b) ⊗ (c ⊗ b0)) (fun b0 : M => a ⊗ (b ⊗ (c ⊗ b0))))).
        apply path_forall. intro m.
        apply ap_idmap.
      + apply (ap inverse).
        apply inverse.
        refine (ap_functor_arrow idmap _ (montype_mult (b ⊗ c)) (fun x : M => b ⊗ (c ⊗ x)) (fun c0 : M => montype_assoc b c c0) ).        
    - intro a. simpl. hott_simpl.
      transitivity (path_arrow _ _ (fun b : M => ap (fun x : M => x ⊗ b) (montype_lid a))).
      { simpl. destruct (montype_lid a). simpl. apply inverse. apply path_forall_1. }
      (* Check (montype_triangle1 M a). *)
      rewrite (path_forall _ _ (montype_triangle1 M a)).
      repeat rewrite path_arrow_pp.
      apply whiskerL.
      apply inverse.
      refine (ap_functor_arrow (montype_mult a) idmap (montype_mult montype_id) idmap montype_lid @ _).
      apply (ap (path_arrow (fun b : M => montype_id ⊗ (a ⊗ b)) (fun b : M => a ⊗ b))).
      apply path_forall. intro b. apply ap_idmap.
    - intro a. simpl. hott_simpl.
      transitivity (path_arrow _ _ (fun b : M => ap (fun x : M => x ⊗ b) (montype_rid a))).
      { simpl. destruct (montype_rid a). simpl. apply inverse. apply path_forall_1. }
      (* Check (montype_triangle2 M a). *)
      rewrite (path_forall _ _ (montype_triangle2 M a)).
      repeat rewrite path_arrow_pp.
      apply whiskerL.
      apply inverse.
      refine (ap_functor_arrow _ _ (montype_mult montype_id) idmap montype_lid ).
  Defined.

  
  (* Definition old_act_on_prod (M : Monoidal_1Type) (X Y: 1-Type) (a1 : Monoidal_Map M (endomorphism X)) (a2 : Monoidal_Map M (endomorphism Y)): *)
  (*   Monoidal_Map M (endomorphism (BuildTruncType 1 (X*Y))). *)
  (* Proof. *)
  (*   srapply @Build_Monoidal_Map. *)
  (*   - simpl. intro s. *)
  (*     apply (functor_prod (a1 s) (a2 s)). *)
  (*   - intros s t. simpl. *)
  (*     apply (ap011 functor_prod (montype_map_mult a1 _ _) (montype_map_mult a2 _ _)). *)
  (*   - apply (ap011 functor_prod (montype_map_id a1) (montype_map_id a2)). *)
  (*   - intros s t u. simpl. *)
  (*     transitivity (ap011 (functor_prod) (ap a1 (montype_assoc s t u)) (ap a2 (montype_assoc s t u))). *)
  (*     { destruct (montype_assoc s t u). reflexivity. } hott_simpl. *)
  (*     transitivity (ap011 functor_prod *)
  (*                         (((montype_map_mult a1 (s ⊗ t) u @ ap (fun x : (X -> X) => x o (a1 u)) (montype_map_mult a1 s t)) *)
  (*                             @ (ap (montype_mult (a1 s)) (montype_map_mult a1 t u))^) @ (montype_map_mult a1 s (t ⊗ u))^) *)
  (*                         (((montype_map_mult a2 (s ⊗ t) u @ ap (fun y : (Y -> Y) => y o (a2 u)) (montype_map_mult a2 s t)) *)
  (*                             @ (ap (montype_mult (a2 s)) (montype_map_mult a2 t u))^) @ (montype_map_mult a2 s (t ⊗ u))^)). *)
  (*     { apply (ap011 (ap011 functor_prod)). *)
  (*       - refine (montype_map_assoc a1 s t u @ _). simpl. hott_simpl. *)
  (*       - refine (montype_map_assoc a2 s t u @ _). simpl. hott_simpl. } *)
  (*     refine (ap011_pp_pp functor_prod _ _ _ _ @ _). *)
  (*     refine (whiskerR (ap011_pp_pp functor_prod _ _ _ _ ) _ @ _). *)
  (*     refine (whiskerR (whiskerR (ap011_pp_pp functor_prod _ _ _ _ ) _) _ @ _). *)
  (*     apply concat2. *)
  (*     + apply concat2. *)
  (*       * apply whiskerL. *)
  (*         cut (forall (f1 f2 : X -> X) (g1 g2 : Y -> Y) (p : f1 = f2) (q : g1 = g2), *)
  (*                 ap011 functor_prod (ap (fun f => f o (a1 u)) p) (ap (fun g => g o (a2 u)) q) = *)
  (*                 ap (fun f => f o (functor_prod (a1 u) (a2 u))) (ap011 functor_prod p q)). *)
  (*         { intro H. apply H. } *)
  (*           by path_induction. *)
  (*       *  simpl. *)
  (*          cut (forall (f1 f2 : X -> X) (g1 g2 : Y -> Y) (p : f1 = f2) (q : g1 = g2), *)
  (*                  ap011 functor_prod (ap (fun f => (a1 s) o f) p)^ (ap (fun g => (a2 s) o g) q)^ = *)
  (*                  (ap (fun f => (functor_prod (a1 s) (a2 s)) o f) (ap011 functor_prod p q))^). *)
  (*          { intro H. apply H. } *)
  (*            by path_induction.         *)
  (*     + cut (forall (f1 f2 : X -> X) (g1 g2 : Y -> Y) (p : f1 = f2) (q : g1 = g2), *)
  (*               ap011 functor_prod p^ q^ = (ap011 functor_prod p q)^). *)
  (*       { intro H. apply H. } *)
  (*         by path_induction.         *)
  (*   - intro s. *)
  (*     transitivity (ap011 functor_prod (ap a1 (montype_lid s)) (ap a2 (montype_lid s))). *)
  (*     { destruct (montype_lid s). reflexivity. } *)
  (*     transitivity (ap011 functor_prod *)
  (*                         ((montype_map_mult a1 montype_id s @ ap (fun f => f o (a1 s)) (montype_map_id a1))) *)
  (*                         ((montype_map_mult a2 montype_id s @ ap (fun f => f o (a2 s)) (montype_map_id a2)))). *)
  (*     { apply (ap011 (ap011 functor_prod)). *)
  (*       - refine (montype_map_lid a1 s @ _). hott_simpl. *)
  (*       - refine (montype_map_lid a2 s @ _). hott_simpl. } *)
  (*     refine (ap011_pp_pp functor_prod _ _ _ _ @ _). simpl. hott_simpl. apply whiskerL. *)
  (*     cut (forall (f1 f2 : X -> X) (g1 g2 : Y -> Y) (p : f1 = f2) (q : g1 = g2), *)
  (*             ap011 functor_prod (ap (fun f => f o (a1 s)) p) (ap (fun g => g o (a2 s)) q) = *)
  (*             ap (fun f => f o (functor_prod (a1 s) (a2 s))) (ap011 functor_prod p q)). *)
  (*     { intro H.  apply (H _ _ _ _ (montype_map_id a1) (montype_map_id a2)). } *)
  (*       by path_induction. *)
  (*   - intro s. *)
  (*     transitivity (ap011 functor_prod (ap a1 (montype_rid s)) (ap a2 (montype_rid s))). *)
  (*     { destruct (montype_rid s). reflexivity. } *)
  (*     transitivity (ap011 functor_prod *)
  (*                         ((montype_map_mult a1 s montype_id @ ap (montype_mult (a1 s)) (montype_map_id a1))) *)
  (*                         ((montype_map_mult a2 s montype_id @ ap (montype_mult (a2 s)) (montype_map_id a2)))). *)
  (*     { apply (ap011 (ap011 functor_prod)). *)
  (*       - refine (montype_map_rid a1 s @ _). hott_simpl. *)
  (*       - refine (montype_map_rid a2 s @ _). hott_simpl. } *)
  (*     refine (ap011_pp_pp functor_prod _ _ _ _ @ _). simpl. hott_simpl. apply whiskerL. *)
  (*     cut (forall (f1 f2 : X -> X) (g1 g2 : Y -> Y) (p : f1 = f2) (q : g1 = g2), *)
  (*             ap011 functor_prod (ap (fun f => (a1 s) o f) p) (ap (fun g => (a2 s) o g) q) = *)
  (*             ap (fun f => (functor_prod (a1 s) (a2 s)) o f) (ap011 functor_prod p q)). *)
  (*     { intro H.  apply (H _ _ _ _ (montype_map_id a1) (montype_map_id a2)). } *)
  (*       by path_induction. *)
  (* Defined. *)
End Monoidal_Map.

Section Monoidal_Action.
  (** We could define monoidal actions to be [Monoidal_Map M (endomorphism X)],
but the following definition is easier to work with.*)

  Record monoidal_action (M : Monoidal_1Type) (X : 1-Type) :=
    { act :> M -> X -> X;
      montype_act_mult : forall (s t : M) (x : X), act (s ⊗ t) x = act s (act t x) ;
      montype_act_id : forall x : X, act montype_id x = x;
      montype_act_triangle1 : forall (a : M) (x : X),
          ap (fun m : M => act m x) (montype_lid a) = montype_act_mult montype_id a x @ montype_act_id (act a x);
      montype_act_triangle2 : forall (a : M) (x : X),
          ap (fun m : M => act m x) (montype_rid a) = montype_act_mult a montype_id x @ ap (fun y : X => act a y) (montype_act_id x);
      montype_act_pentagon : forall (a b c : M) (x : X),
          ap (fun m : M => act m x) (montype_assoc a b c) =
          montype_act_mult (a ⊗ b) c x @ montype_act_mult a b (act c x) @ (ap (act a) (montype_act_mult b c x))^ @ (montype_act_mult a (b ⊗ c) x)^ }.

  Global Arguments montype_act_mult {M} {X} a s t x : rename.
  Global Arguments montype_act_id {M} {X} a x : rename.
  

  Definition action_on_path {M} {X} (a : monoidal_action M X) {s t : M} (x : X) (p : s = t)
    := ap (fun s => a s x) p.

  (** A monoidal 1-type acts on itself per definition.  *)
  Definition act_on_self (M : Monoidal_1Type) : monoidal_action M M.
  Proof.
    srapply @Build_monoidal_action.
    - exact montype_mult.
    - apply montype_assoc.
    - apply montype_lid.
    - apply montype_triangle1.
    - apply montype_triangle2.
    - apply montype_pentagon.
  Defined.

  Definition endomorphism_to_action (M : Monoidal_1Type) (X : 1-Type)
             (F : Monoidal_Map M (endomorphism X))
    : monoidal_action M X.
  Proof.
    srapply @Build_monoidal_action.
    - exact F.
    - intros s t. apply ap10.
      apply (montype_map_mult F).
    - apply ap10.
      apply (montype_map_id F).
    - intros a x.      
      refine (ap_compose F (fun f => f x) (montype_lid a) @ _).
      rewrite montype_map_lid.
      repeat rewrite ap_pp. simpl. rewrite concat_p1.
      rewrite <- (ap_compose (fun (s : X -> X) (x0 : X) => s (F a x0)) (fun f : X -> X => f x) (montype_map_id F)). simpl.
      rewrite ap_apply_l. rewrite ap_apply_l. reflexivity.
    - intros a x.
      refine (ap_compose F (fun f => f x) (montype_rid a) @ _).
      rewrite montype_map_rid.
      repeat rewrite ap_pp. simpl. rewrite concat_p1.
      rewrite ap_apply_l. apply whiskerL.
      rewrite ap_apply_l.
      apply (ap10_ap_postcompose (F a) (montype_map_id F) x).
    - intros a b c x. simpl.
      refine (ap_compose F (fun f => f x) (montype_assoc a b c) @ _).
      rewrite montype_map_assoc.
      repeat rewrite ap_pp. simpl. rewrite concat_p1.
      rewrite ap_apply_l. rewrite ap_apply_l. rewrite ap_apply_l. rewrite ap_apply_l.
      apply concat2.
      { apply concat2.
        { apply whiskerL.
          apply (ap10_ap_precompose (F c) (montype_map_mult F a b) x ). }
        rewrite ap10_V. apply (ap inverse).
        apply (ap10_ap_postcompose (F a) (montype_map_mult F b c) x). }
      apply (ap10_V (montype_map_mult F a (b ⊗ c)) x).
  Defined.

  Definition monmap_to_action {M : Monoidal_1Type} {X : Monoidal_1Type} (F : Monoidal_Map M X) :
    monoidal_action M X.
  Proof.
    apply endomorphism_to_action.
    apply (monoidal_map_compose M X (endomorphism X) F).
    apply (to_endomorphism).
  Defined.

  Definition act_on_prod (M : Monoidal_1Type) (X Y: 1-Type)
             (act1 : monoidal_action M X) (act2 : monoidal_action M Y) :
    monoidal_action M (BuildTruncType 1 (X*Y)).
  Proof.
    srapply @Build_monoidal_action; simpl.
    - intro s.
      apply (functor_prod (act1 s) (act2 s)).
    - simpl. intros s t x.
      apply path_prod; apply montype_act_mult.
    - simpl. intro x.
      apply path_prod; apply montype_act_id.
    - simpl. intros s x.
      transitivity (path_prod (_,_) (_,_) (ap (fun m : M => act1 m (fst x)) (montype_lid s)) (ap (fun m : M => act2 m (snd x)) (montype_lid s))).
      { destruct (montype_lid s). reflexivity. }
      refine (_ @ path_prod_pp _ _ _ _ _ _ _).      
      apply (ap011 (path_prod _ _)); apply montype_act_triangle1.
    - intros s x. simpl.
      transitivity (path_prod (_,_) (_,_) (ap (fun m : M => act1 m (fst x)) (montype_rid s)) (ap (fun m : M => act2 m (snd x)) (montype_rid s))).
      { destruct (montype_rid s). reflexivity. }
      refine (_ @ whiskerL _ (ap_functor_prod _ _ _ _ _ _)^).      
      refine (_ @ path_prod_pp _ _ _ _ _ _ _).
      apply (ap011 (path_prod _ _)); apply montype_act_triangle2.
    - intros a b c x. simpl.
      transitivity (path_prod (_,_) (_,_)
                              (ap (fun m : M => act1 m (fst x)) (montype_assoc a b c)) (ap (fun m : M => act2 m (snd x)) (montype_assoc a b c))).
      { destruct (montype_assoc a b c). reflexivity. }
      rewrite (ap_functor_prod).
      repeat rewrite <- path_prod_VV.
      repeat rewrite <- path_prod_pp.
      apply (ap011 (path_prod _ _)); apply montype_act_pentagon.
  Defined.

  (* Definition act_from_monmap (M X : Monoidal_1Type) (F : Monoidal_Map M X) : *)
  (*   monoidal_action M X. *)
  (* Proof. *)
  (*   srapply @Build_monoidal_action. *)
  (*   - intros m x. exact ((F m) ⊗ x). *)
  (*   - intros s t x. simpl. *)
  (*     refine (ap (fun y => y ⊗ x) (montype_map_mult F s t) @ _). *)
  (*     apply montype_assoc. *)
  (*   - intro x. simpl. *)
  (*     exact (ap (fun y => y ⊗ x) (montype_map_id F) @ (montype_lid x)). *)
  (*   - intros a x. simpl. *)
  (*     refine (ap_compose F (fun y : X => y ⊗ x) (montype_lid a) @ _). *)
  (*     rewrite montype_map_lid. *)
  (*     repeat rewrite ap_pp. *)
  (*     rewrite montype_triangle1. *)
  (*     repeat rewrite concat_p_pp. apply whiskerR. *)
  (*     repeat rewrite concat_pp_p. apply whiskerL. *)
  (*     rewrite <- (ap_compose (fun s : X => s ⊗ F a) (fun y : X => y ⊗ x)). *)
  (*     destruct (montype_map_id F). simpl. *)
  (*     destruct (montype_assoc (F montype_id) (F a) x). reflexivity. *)
  (*   - intros a x. simpl. *)
  (*     refine (ap_compose F (fun y : X => y ⊗ x) (montype_rid a) @ _). *)
  (*     rewrite montype_map_rid. *)
  (*     repeat rewrite ap_pp. *)
  (*     rewrite montype_triangle2. *)
  (*     repeat rewrite concat_p_pp. apply whiskerR. *)
  (*     repeat rewrite concat_pp_p. apply whiskerL. *)
  (*     rewrite <- (ap_compose (montype_mult (F a)) (fun y : X => y ⊗ x)). *)
  (*     destruct (montype_map_id F). simpl. *)
  (*     destruct (montype_assoc (F a) (F montype_id)  x). reflexivity. *)
  (*   - intros a b c x. simpl. *)
  (*     refine (ap_compose F (fun y : X => y ⊗ x) (montype_assoc a b c) @ _). *)
  (*     rewrite montype_map_assoc. *)
  (*     repeat rewrite ap_pp. *)
  (*     rewrite montype_pentagon. *)
  (*     repeat rewrite concat_pp_p. apply whiskerL. *)
  (*     repeat rewrite concat_p_pp. apply whiskerR. *)
  (*     refine (ap_pp _ _ _ @ _). *)
  (*     refine (montype_triangle1 M _ _ @ _). *)
End Monoidal_Action.


Section Symmetric_Monoidal_1Type.
  (** Define symmetric monoidal 1-type.  *)
  
  Definition symmetric {A : Type} (m : A->A->A) := forall a b : A, m a b = m b a.
  Definition coherence_hexagon {A : Type} {m : A -> A -> A} (assoc : associative m)
             (symm : symmetric m) :=
    forall (a b c : A),
      ap (fun x : A => m x c) (symm a b) =
      assoc a b c @ symm a (m b c) @ assoc b c a @ (ap (m b) (symm a c))^ @ (assoc b a c)^.

  Record Symmetric_Monoidal_1Type : Type :=
    { smontype_type :> 1-Type;
      smontype_mult  : smontype_type -> smontype_type -> smontype_type;
      smontype_id : smontype_type;
      smontype_assoc : associative smontype_mult;
      smontype_lid : left_identity_mult smontype_mult smontype_id ;
      smontype_rid : right_identity_mult smontype_mult smontype_id ;
      smontype_sym : symmetric smontype_mult ;
      smontype_sym_inv : forall a b : smontype_type, smontype_sym a b = (smontype_sym b a)^ ;
      smontype_triangle1 : coherence_triangle1 smontype_assoc smontype_lid ;
      smontype_triangle2 : coherence_triangle2 smontype_assoc smontype_lid smontype_rid ;
      smontype_pentagon : coherence_pentagon smontype_assoc;
      smontype_hexagon : coherence_hexagon smontype_assoc smontype_sym
    }.
  Global Arguments smontype_mult {S} a b : rename.
  Global Arguments smontype_id {S} : rename.
  Global Arguments smontype_assoc {S} a b c : rename.
  Global Arguments smontype_lid {S} a : rename.
  Global Arguments smontype_rid {S} a : rename.
  Global Arguments smontype_sym {S} a b : rename.

  Definition forget_symmetry : Symmetric_Monoidal_1Type -> Monoidal_1Type :=
    fun S => Build_Monoidal_1Type S smontype_mult smontype_id smontype_assoc smontype_lid smontype_rid
                                  (smontype_triangle1 S) (smontype_triangle2 S) (smontype_pentagon S).

  Coercion forget_symmetry : Symmetric_Monoidal_1Type >-> Monoidal_1Type.
End Symmetric_Monoidal_1Type.



  
    



  



     
                   
  
  