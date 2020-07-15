Require Import HoTT.

(** A couple auxiliary lemmas we need  *)
Definition ap011_pp_pp {A B C : Type} (f : A -> B -> C) {x x' x'' : A} {y y' y'' : B}
           (p : x = x') (p' : x' = x'') (q : y = y') (q' : y' = y'') :
  ap011 f (p @ p') (q @ q') = ap011 f p q @ ap011 f p' q'.
Proof.
    by path_induction.
Qed.

Lemma ap011_VV
  : forall {A B C: Type} (f : A -> B -> C)
           {a0 a1 : A} {b0 b1 : B}
           (p : a0 = a1) (q : b0 = b1),
    (ap011 f p q)^ = ap011 f p^ q^.
Proof.
  intros. destruct p. destruct q. reflexivity.
Defined.

Definition double_pathover {A B : Type} (P : A -> B -> Type)
           {a a' : A} (p : a = a')
           {b b' : B} (q : b = b')
           (c : P a b) (c' : P a' b') : Type.
Proof.
  destruct p,q. exact (c = c').
Defined.

Definition double_pathover_to_path {A B : Type} (P : A -> B -> Type)
           {a a' : A} (p : a = a')
           {b b' : B} (q : b = b')
           (c : P a b) (c' : P a' b')
  : double_pathover P p q c c' ->
    transport (uncurry P) (path_prod (a,b) (a',b') p q) c = c'.
Proof.
  destruct p, q. exact idmap.
Defined.

Definition path_to_double_pathover {A B : Type} (P : A -> B -> Type)
           {a a' : A} (p : a = a')
           {b b' : B} (q : b = b') (c : P a b) (c' : P a' b')
  : transport (uncurry P) (path_prod (a, b) (a', b') p q) c = c' ->
    double_pathover P p q c c'.
Proof.
  destruct p. destruct q. exact idmap.
Defined.



Definition path_triple_prod {A B C : Type} (a1 a2 : A * (B * C)) :
  (fst a1 = fst a2) * ((fst (snd a1) = fst (snd a2)) * (snd (snd a1) = snd (snd a2))) -> a1 = a2.
Proof.
  intros [p [q r]].
  apply (path_prod a1 a2 p (path_prod (_,_) (_,_) q r)).
Defined.

Definition equiv_path_triple_prod {A B C : Type} (a1 a2 : A * (B * C)) :
  (fst a1 = fst a2) * ((fst (snd a1) = fst (snd a2)) * (snd (snd a1) = snd (snd a2))) <~> a1 = a2.
Proof.
  srapply (@equiv_adjointify _ _ (path_triple_prod a1 a2)).
  - intro p.
    exact (ap fst p, (ap fst (ap snd p), (ap snd (ap snd p)))).
  - intros []. reflexivity.
  - intros [p [q r]].
    destruct a2 as [a2 [b2 c2]]. simpl in *.
    destruct p,q,r. reflexivity.
Defined.



(* (*ap12 and ap12' are badly named. ap12' is the same as ap_to_conjp *) *)
(* Definition ap12 {A B : Type} {a b : A} (p : a = b) {f g : A->B} (q : f=g)  : *)
(*   (ap10 q a)^ @ (ap f p) @ (ap10 q b) = ap g p. *)
(* Proof. *)
(*   destruct p, q. reflexivity. *)
(* Defined. *)

(* (*Needs better name, I guess. . .*) *)
(* Definition ap12' `{Funext} {A B : Type} {a b : A} (p : a = b) {f g : A->B} (q : f==g)  : *)
(*   (q a)^ @ (ap f p) @ q b = ap g p. *)
(* Proof. *)
(*   refine (_ @ ap12 p (path_arrow _ _ q)). *)
(*   apply concat2. *)
(*   { apply whiskerR. *)
(*     apply inverse2. exact (inverse (ap10_path_arrow f g q _)). } *)
(*   exact (inverse (ap10_path_arrow f g q _)). *)
(* Defined. *)

(* Definition ap011_pp_pp {A B C : Type} (f : A -> B -> C) {x x' x'' : A} {y y' y'' : B} *)
(*            (p : x = x') (p' : x' = x'') (q : y = y') (q' : y' = y'') : *)
(*   ap011 f (p @ p') (q @ q') = ap011 f p q @ ap011 f p' q'. *)
(* Proof. *)
(*   by path_induction. *)
(*   (* destruct p, p', q, q'. exact idpath. *) *)
(* Qed. *)




(* Definition double_pathover {A B : Type} (P : A -> B -> Type) *)
(*            {a a' : A} (p : a = a') *)
(*            {b b' : B} (q : b = b') *)
(*            (c : P a b) (c' : P a' b') : Type. *)
(* Proof. *)
(*   destruct p,q. exact (c = c'). *)
(* Defined. *)

(* Definition double_pathover_to_path {A B : Type} (P : A -> B -> Type) *)
(*            {a a' : A} (p : a = a') *)
(*            {b b' : B} (q : b = b') *)
(*            (c : P a b) (c' : P a' b') *)
(*   : double_pathover P p q c c' -> *)
(*     transport (uncurry P) (path_prod (a,b) (a',b') p q) c = c'. *)
(* Proof. *)
(*   destruct p, q. exact idmap. *)
(* Defined. *)

(* Definition apd_po011 *)
(*            (A B : Type) (C : A -> B -> Type) (f : forall (a : A) (b : B), C a b) *)
(*            (a1 a2 : A) (b1 b2 : B) *)
(*            (p : a1 = a2) (q : b1 = b2) *)
(*   : double_pathover C p q (f a1 b1) (f a2 b2). *)
(* Proof. *)
(*   destruct p. destruct q. reflexivity. *)
(* Defined. *)


(* Definition path_to_double_pathover {A B : Type} (P : A -> B -> Type) *)
(*            {a a' : A} (p : a = a') *)
(*            {b b' : B} (q : b = b') (c : P a b) (c' : P a' b') *)
(*   : transport (uncurry P) (path_prod (a, b) (a', b') p q) c = c' -> *)
(*     double_pathover P p q c c'. *)
(* Proof. *)
(*   destruct p. destruct q. exact idmap. *)
(* Defined. *)

(* Lemma ap011_VV *)
(*   : forall {A B C: Type} (f : A -> B -> C) *)
(*            {a0 a1 : A} {b0 b1 : B} *)
(*            (p : a0 = a1) (q : b0 = b1), *)
(*     (ap011 f p q)^ = ap011 f p^ q^. *)
(* Proof. *)
(*   intros. destruct p. destruct q. reflexivity. *)
(* Defined. *)





(* (* Definition pathover {A : Type} (B : A -> Type) {a a' : A} (p : a = a') (b : B a) (b' : B a') *) *)
(* (*   := transport B p b = b'.            *) *)

(* (* Notation "a =^ B [ p ] b" := (pathover B p a b) (at level 20, format "a  =^ B [ p ]  b"). *) *)
(* (* Notation "a =[ p ] b" := (pathover _ p a  b) (at level 20, format "a  =[ p ]  b"). *) *)

(* (*For now, define pathovers just as notation. *) *)

(* (* Notation "'pathover' B p a b" := (transport B p a = b) (at level 20) : pathover_scope. *) *)
(* (* Notation "a =[ p ] b" := (transport _ p a = b) *) *)
(* (*                            (at level 20, format "a  =[ p ]  b") : pathover_scope. *) *)
(* (* Notation "a =^ ( B ) [ p ] b" := (transport B p a = b) *) *)
(* (*                                (at level 20, format "a  =^ ( B ) [ p ]  b") : pathover_scope. *) *)

(* (* (*Make another scope where the explicit notation is parsing only*) *) *)
(* (* Notation "'pathover' B p a b" := (transport B p a = b) (at level 20) : implicit_pathover_scope. *) *)
(* (* Notation "a =[ p ] b" := (transport _ p a = b) *) *)
(* (*                            (at level 20, format "a  =[ p ]  b") : implicit_pathover_scope. *) *)
(* (* Notation "a =^ B [ p ] b" := (transport B p a = b) *) *)
(* (*                                (at level 20, only parsing, format "a  =^ B [ p ]  b") : implicit_pathover_scope. *) *)


(* (*This is already defined as [transport_apD_transportD], but I like this name better. . .*) *)
(* Definition transport_composeD {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type) *)
(*            (f : forall a : A, B a) *)
(*            {a a' : A} (p : a = a') (c : C a (f a)) : *)
(*   transport (fun a0 : A => C a0 (f a0)) p c = transport (C a') (apD f p) (transportD B C p (f a) c). *)
(* Proof. *)
(*   induction p. reflexivity. *)
(* Defined. *)


(* (* Definition path_sigma' {A : Type} {B : A -> Type} {ab ab' : {a : A & B a}} *) *)
(* (*            (p : ab.1 = ab'.1) (q : path_over B p (ab.2) (ab'.2)) *) *)
(* (*   : ab = ab'. *) *)
(* (* Proof. *) *)
(* (*   destruct ab as [a b]. destruct ab' as [a' b']. simpl in *. *) *)
(* (*   destruct q. reflexivity. *) *)
(* (* Defined. *) *)

(* (* Definition path_sigma_concat' {A : Type} {B : A -> Type} {x y z : {a : A & B a}} *) *)
(* (*            (p : x.1 = y.1) (q : path_over B p (x.2) (y.2)) *) *)
(* (*            (p' : y.1 = z.1) (q' : path_over B p' (y.2) (z.2)) *) *)
(* (*   : path_sigma' p q @ path_sigma' p' q' = *) *)
(* (*     path_sigma' (p @ p') (path_over_concat q q'). *) *)
(* (* Proof. *) *)
(* (*   destruct x as [x1 x2]. destruct y as [y1 y2]. destruct z as [z1 z2]. simpl in *. *) *)
(* (*   destruct q'. destruct q. reflexivity. *) *)
(* (* Defined. *) *)


(* (* Definition equiv_path_sigma' {A : Type} {B : A -> Type} (ab ab' : {a : A & B a}) : *) *)
(* (*   {p : ab.1 = ab'.1 & path_over B p (ab.2) (ab'.2)} <~> ab = ab'. *) *)
(* (* Proof. *) *)
(* (*   srapply @equiv_adjointify. *) *)
(* (*   - intros [p q]. exact (path_sigma' p q). *) *)
(* (*   - intros []. exists idpath. apply path_over_id. *) *)
(* (*   - intros []. reflexivity. *) *)
(* (*   - intros [p q]. *) *)
(* (*     destruct ab as [a b]. destruct ab' as [a' b']. simpl in *. *) *)
(* (*     destruct p. destruct q. reflexivity. *) *)
(* (* Defined. *) *)

(* (*   Lemma equiv_path_over_id {A : Type} {B : A -> Type} (a : A) (b1 b2 : B a) *) *)
(* (*     : path_over B (idpath a) b1 b2 <~> b1 = b2. *) *)
(* (*   Proof. *) *)
(* (*     srapply @equiv_adjointify. *) *)
(* (*     - apply (path_over_to_path (p := idpath a)). *) *)
(* (*     - apply (path_to_path_over (p := idpath a)). *) *)
(* (*     - simpl. intros []. reflexivity. *) *)
(* (*     - intro q. destruct q. reflexivity. *) *)
(* (*   Defined.       *) *)

(* (*   Definition isequiv_path_over_concat {A : Type} {B : A -> Type} *) *)
(* (*              {a1 a2 a3: A} {p1 : a1 = a2} (p2 : a2 = a3) *) *)
(* (*              {b1 : B a1} {b2 : B a2} (q : path_over B p1 b1 b2) *) *)
(* (*              (b3 : B a3)  *) *)
(* (*     : IsEquiv (path_over_concat (p₂ := p2) (c₃ := b3) q). *) *)
(* (*   Proof. *) *)
(* (*     srapply @isequiv_adjointify. *) *)
(* (*     - destruct p2. destruct q. exact idmap. *) *)
(* (*     - destruct q. destruct p2.  *) *)
(* (*       intro q. simpl in q. revert q. *) *)
(* (*       apply (equiv_functor_forall_pf (equiv_path_over_id a c b3)). *) *)
(* (*       intros []. reflexivity. *) *)
(* (*     - destruct q. destruct p2. simpl. *) *)
(* (*       apply (equiv_functor_forall_pf (equiv_path_over_id a c b3)). *) *)
(* (*       intros []. reflexivity. *) *)
(* (*   Defined. *) *)







(* Section Dependent_paths. *)


(*   Definition apD_composeD {A : Type} {B : Type} {C : B -> Type} *)
(*              (f : forall b : B, C b) *)
(*              (g : A -> B) *)
(*              {a a' : A} (p : a = a') :      *)
(*     apD (f oD g) p = transport_compose C g p (f (g a)) @ apD f (ap g p). *)
(*   Proof. *)
(*     destruct p. reflexivity. *)
(*   Defined. *)


(*   Definition composeDD {A : Type} {B : A -> Type} {C : forall a : A, B a -> Type} *)
(*              (f : forall a : A, forall b : B a, C a b) *)
(*              (g : forall a : A, B a) *)
(*   : forall a : A, C a (g a) *)
(*     := fun a => f a (g a). *)

(*   (* Notation "f 'oDD' g" := (composeDD f g) (at level 0): function_scope. *) *)



(*   (*. . . *) *)
(*   Definition apD_composeDD {A : Type} {B : A -> Type} {C : forall a : A, B a -> Type} *)
(*              (f : forall a : A, forall b : B a, C a b) *)
(*              (g : forall a : A, B a) *)
(*              {a a' : A} (p : a = a') : *)
(*     apD (composeDD f g) p = *)
(*     transport_composeD B C g p (f a (g a)) @ apD011 f p (apD g p). *)
(*   Proof. *)
(*     destruct p; reflexivity. *)
(*   Defined. *)


(*   (* Definition apD_composeDD' {A : Type} {B : A -> Type} {C : forall a : A, B a -> Type} *) *)
(*   (*            (f : forall a : A, forall b : B a, C a b) *) *)
(*   (*            (g : forall a : A, B a) *) *)
(*   (*            {a a' : A} (p : a = a') : *) *)
(*   (*   apD (composeDD f g) p = apD (f a') (apD g p) *) *)


(*   (* Notation "a =^ P p b" := (transport P p a = b) (at level 20, format *) *)
(*   (*                                                      "a  =^ P  p  b"). *) *)



(*   (* Definition concat_over {A : Type} (B : A -> Type) {a1 a2 a3 : A} (p : a1 = a2) (q : a2 = a3) *) *)
(*   (*            {b1 : B a1} {b2 : B a2} {b3 : B a3} :  *) *)

(*   (*   b1 =[p] b2 -> b2 =[q] b3 -> b1 =[p @ q] b3 *) *)
(*   (*   := fun over_p over_q => (transport_pp B p q b1 @ ap (transport B q) over_p @ over_q). *) *)

(*   (* Notation "r @[ p , q ] s" := (concat_over _ p q r s) (at level 20, format "r  @[ p , q ]  s"). *) *)

(*   (* Definition apD_pp {A : Type} {B : A -> Type} (f : forall a : A, B a) *) *)
(*   (*            {a1 a2 a3 : A} (p : a1 = a2) (q : a2 = a3) :  *) *)
(*   (*   apD f (p @ q) = (apD f p @[p, q] apD f q). *) *)
(*   (* Proof. *) *)
(*   (*   destruct p. destruct q. reflexivity. *) *)
(*   (* Qed. *) *)

(*   (* Definition transport_PQ {A : Type} {P : A -> Type} {Q : A -> Type} (h : P == Q) *) *)
(*   (*            {a b : A} (pth : a = b) *) *)
(*   (*            (p : P a) *) *)
(*   (* :  transport idmap (h b) (transport P pth p) = transport Q pth (transport idmap (h a) p). *) *)
(*   (*   destruct pth. reflexivity. Defined. *) *)

(*   Definition transport_PequivQ  {A : Type} {P : A -> Type} {Q : A -> Type} (h : forall a : A, P a <~> Q a) *)
(*              {a b : A} (pth : a = b) *)
(*              (p : P a) *)
(*   :  transport P pth p = (h b)^-1 (transport Q pth (h a p)). *)
(*     destruct pth. simpl. apply moveL_equiv_V. reflexivity. Defined. *)


(*   (* (*A version of transport_compose I need now*) *) *)
(*   (* Definition transport_compose_mine {A B : Type} (C : forall a : A, B -> Type) (f : A -> B) *) *)
(*   (*            {a a' : A} (p : a = a') (c : C a (f a)) : *) *)
(*   (*              transport (fun a => C a (f a)) p c = *) *)
(*   (*               ap ? @ (transport (C a) (ap f p) c). *) *)
(*   (* Proof. *) *)
(*   (*   destruct p. reflexivity. *) *)
(*   (* Defined. *) *)

(* End Dependent_paths. *)
