Require Import HoTT.
Require Import FunextAxiom.

Require Import Functor Categories Category Morphisms.

From A_BPQ Require Import path_over categories.

(** Making an induction principle for pointed connected 1-types, based on notes by Thierry Coquand *)
(** This is a more general version of deloop.v  *)
  
Section rezk_rec.
  Context (X : Type) .

  Context (C : PreCategory)
          (H_0 : C -> X)
          `{merely_surj_H : forall (x : X), merely {c : C & H_0 c = x}}
          (H_1 : forall {c1 c2 : C},
              morphism C c1 c2 -> H_0 c1 = H_0 c2)
          `{isequiv_H1 : forall (c1 c2 : C), IsEquiv (@H_1 c1 c2)}
          (H_2 : forall (c1 c2 c3 : C) (g : morphism C c1 c2) (h : morphism C c2 c3),
              H_1 (h o g)%morphism = H_1 g @ H_1 h)
          (H_idhom : forall (c : C), H_1 (identity c) = idpath).
  Arguments H_1 {c1 c2}.
  Arguments H_2 {c1 c2 c3}.

  Context (Y : Type)
          `{istrunc_Y : IsTrunc 1 (Y)}
          (f0 : C -> Y)
          (f1 : forall {c1 c2 : C} (g : morphism C c1 c2),
              (f0 c1) =  (f0 c2))
          (f2 : forall (c1 c2 c3 : C) (g : morphism C c1 c2) (h : morphism C c2 c3),
                        (f1 (h o g)%morphism) =
                        ((f1 g) @ (f1 h))).
  Arguments f1 {c1 c2} g.
  Arguments f2 {c1 c2 c3} g h.

  Lemma f1_idhom (c : C) : f1 (identity c) = idpath.
  Proof.
    apply (equiv_inj (concat (f1 1))).
    refine (_ @ (concat_p1 _)^).
    apply inverse.
    refine (_ @ f2 1 1).
    apply (ap f1).
    apply inverse.
    apply left_identity.
  Qed.

  
  Definition B (x : X) (y : Y) :=
    {q : forall (c : C) (p : H_0 c = x), (f0 c) = y &
     forall (c1 c2 : C) (g : morphism C c1 c2) (p : H_0 c2 = x),
       q c1 (H_1 g @ p) =
       (f1 g) @ (q c2 p)}.

  Lemma q_is_f1 (c1 c2 : C) (y : Y) (q : B (H_0 c2) y) (h : morphism C c1 c2) :
    q.1 c1 (H_1 h) =
    (f1 h) @ (q.1 c2 idpath).
  Proof.
    destruct q as [q b]. simpl.
    refine (ap (q c1) (concat_p1 (H_1 h))^ @ _).
    apply b.
  Qed.
  
  Definition B_base : forall (c : C) (y : Y), (B (H_0 c) y) <~> (f0 c = y).
  Proof.
    intros c y. unfold B.
    transitivity
      {q : forall c0 : C, morphism C c0 c -> f0 c0 = y &
         forall (c1 c2 : C) (g : morphism C c1 c2) (h : morphism C c2 c),
           q c1 (h o g)%morphism = f1 g @ q c2 h}.
    { srapply @equiv_functor_sigma'.
      - apply equiv_functor_forall_id.
        intro c1.
        apply (equiv_precompose').
        exact (BuildEquiv _ _ H_1 _).
      - intro q. simpl.
        apply equiv_functor_forall_id. intro c1.
        apply equiv_functor_forall_id. intro c2.
        apply equiv_functor_forall_id. intro g.
        srapply @equiv_functor_forall'.
        { exact (BuildEquiv _ _ H_1 _). }
        intro h. simpl.
        unfold functor_forall.
        apply equiv_concat_l.
        apply (ap (q c1)).
        apply H_2. }
            
    
    srapply @equiv_adjointify.
    - intros [q b].
      apply (q c). apply identity.
    - intro p. (* destruct p0. *)
      srapply @exist.
      + intros c1 h. refine (_ @ p).
        apply f1. exact h.
      + hnf. intros.
        refine (_ @ concat_pp_p _ _ _ ). apply whiskerR.
        refine (f2 _ _).
    - intro p.
      refine (whiskerR (f1_idhom _) _ @ _). apply concat_1p.
    - intros [q b]. 
      apply path_sigma_hprop. simpl.
      apply path_forall. intro c1.
      apply path_forall. intro g.
      refine (_ @ ap (q c1) (left_identity _ _ _ _)).
      apply inverse. apply b.
  Defined.




  Instance contr_B :
    forall (x : X), Contr {y : Y & B x y}.
  Proof.
    intro x.
    cut (merely ({c : C & H_0 c = x}) -> Contr {y : Y & B x y}).
    { intro hyp. apply hyp.
      apply merely_surj_H. }
    apply Trunc_rec. intros [c []].
    apply (contr_equiv' {y : Y & (f0 c = y)}).
    { apply equiv_functor_sigma_id. intro y.
      apply equiv_inverse.
      apply B_base. }
    apply contr_basedpaths.
  Defined.

  Definition rezk_rec : X -> Y
    := fun x => (center _ (contr_B x)).1 .

  Definition rezk_rec_q (x : X) (c : C):
    forall (p : H_0 c = x), f0 c = rezk_rec x
    := ((center {y : Y & B x y}).2.1 c).  


  Lemma q_is_ap_rezk_rec :
    forall (x x': X) (c : C) (p : H_0 c = x) (q : x = x'),
      rezk_rec_q x' c (p @ q) =
      rezk_rec_q x c p @ ap rezk_rec q.
      (* transport_pp Y α β _ @ ap (transport Y β) (deloop_ind_p x α) @ apD deloop_ind β. *)
  Proof.
    intros. destruct q. destruct p. simpl.
    apply inverse. apply concat_p1.
  Qed.

  Definition rezk_rec_beta_obj (c : C) : rezk_rec (H_0 c) = f0 c:=
    (rezk_rec_q (H_0 c) c idpath)^.


  Definition rezk_rec_beta_morphism : forall (c1 c2 : C) (g :  morphism C c1 c2),
      ap rezk_rec (H_1 g) = (rezk_rec_beta_obj c1) @ (f1 g) @ (rezk_rec_beta_obj c2)^.
      (* (ap (transport Y ω) deloop_ind_beta_pt)^ @ apD deloop_ind ω @ deloop_ind_beta_pt = f ω. *)
  Proof.
    intros. unfold rezk_rec_beta_obj.
    rewrite inv_V. refine (_ @ concat_p_pp _ _ _). apply moveL_Vp.
    apply inverse.
    refine (_ @ q_is_ap_rezk_rec _ _ _ _ _). rewrite concat_1p.
    apply inverse. apply q_is_f1.
  Defined.
End rezk_rec.


Section rezk_ind_set.
  Context (X : Type) (* `{IsTrunc_X : IsTrunc 1 X} *). (* the latter variable not strictly necessary *)
  (* Context (X : Type) (x0 : X) (* (istrunc_X : IsTrunc 1 X) *) *)
  (*         `{isconn_X : forall (x : X), merely (x0 = x)}. *)

  Context (C : PreCategory)
          (* (H : Functor C (groupoid_category X)) *)
          (* (isfullyfaithful_H : IsFullyFaithful H) *)
          (* (isessentiallysurjective_H : IsEssentiallySurjective H). *)
          (* The following is uncurrying a weak equivalence from C to X *)
          (H_0 : C -> X)
          `{merely_surj_H : forall (x : X), merely {c : C & H_0 c = x}}
          (H_1 : forall {c1 c2 : C},
              morphism C c1 c2 -> H_0 c1 = H_0 c2)
          `{isequiv_H1 : forall (c1 c2 : C), IsEquiv (@H_1 c1 c2)}
          (H_idhom : forall (c : C), H_1 (identity c) = idpath)
          (H_2 : forall (c1 c2 c3 : C) (g : morphism C c1 c2) (h : morphism C c2 c3),
              H_1 (h o g)%morphism = H_1 g @ H_1 h).
  Arguments H_1 {c1 c2}.
  Arguments H_2 {c1 c2 c3}.

  (* Lemma H_idhom (c : C) : H_1 (identity c) = idpath. *)
  (* Proof. *)
  (*   apply (equiv_inj (concat (H_1 1))). *)
  (*   refine (ap H_1 (identity_identity C c)^ @ _). *)
  (*   refine (H_2 (identity c) (identity c) @ _). *)
  (*   ap H_1 (identity_identity C c)^ @ H_2 (identity c) (identity c) *)
  (* Instance istrunc_X : IsTrunc 1 X. *)
  (* Proof. *)
  (*   intros x1 x2. *)
  (*   generalize (merely_surj_H x1). apply Trunc_rec. intros [c1 p]. destruct p. *)
  (*   generalize (merely_surj_H x2). apply Trunc_rec. intros [c2 p]. destruct p. *)
  (*   apply (trunc_equiv _ H_1). *)
  (* Defined. *)

  Context (Y : X -> Type)
          `{istrunc_Y : forall (x : X), IsHSet (Y x)}
          (f0 : forall (c : C), Y (H_0 c))
          (f1 : forall {c1 c2 : C} (g : morphism C c1 c2),
              path_over Y (H_1 g) (f0 c1) (f0 c2)).
  Arguments f1 {c1 c2} g.
  (* Arguments f2 {c1 c2 c3} g h. *)
  (* Definition sect_of_rezk_ind : X -> {x : X & Y x}. *)
  (* Proof. *)
  (*   srapply (@rezk_rec X C (@H_0) (merely_surj_H) (@H_1) _ (@H_2)). *)
  (*   - intro c. exists (H_0 c). exact (f0 c). *)
  (*   - intros c1 c2 g. simpl. *)
  (*     srapply @path_sigma'. *)
  (*     + simpl. apply H_1. exact g. *)
  (*     + simpl. apply f1. *)
  (*   - simpl. intros. *)
  (*     refine (_ @ (path_sigma_concat' _ _ _ _)^). *)
  (*     change (path_sigma' ?p ?q) with (equiv_path_sigma' (_ ; _) (_;_) (p; q)). *)
  (*     apply (ap (equiv_path_sigma' _ _)). *)
  (*     srapply @path_sigma'. *)
  (*     + simpl. apply H_2. *)
  (*     + simpl. apply f2. *)
  (* Defined. *)
  (* Definition issect_sect_of_rezk_ind (x : X) : (sect_of_rezk_ind x).1 = x. *)
  (* Proof. *)
  (*   simpl. Abort. *)
    Definition B_set (x : X) (y : Y x) :=
      (forall (c : C) (p : H_0 c = x), path_over Y p (f0 c) y).
                                              
    (* {q : forall (c : C) (p : H_0 c = x), (f0 c) = y & *)
    (*  forall (c1 c2 : C) (g : morphism C c1 c2) (p : H_0 c2 = x), *)
    (*    q c1 (H_1 g @ p) = *)
    (*    (f1 g) @ (q c2 p)}. *)
  (* Lemma q_is_f1 (c1 c2 : C) (y : Y) (q : B (H_0 c2) y) (h : morphism C c1 c2) : *)
  (*   q.1 c1 (H_1 h) = *)
  (*   (f1 h) @ (q.1 c2 idpath). *)
  (* Proof. *)
  (*   destruct q as [q b]. simpl. *)
  (*   refine (ap (q c1) (concat_p1 (H_1 h))^ @ _). *)
  (*   apply b. *)
  (* Qed. *)
  
  Definition B_set_base : forall (c : C) (y : Y (H_0 c)),
        (B_set (H_0 c) y) <~> (f0 c = y).
  Proof.
    intros c y. unfold B_set.
    transitivity
      (forall (c0 : C) (g : morphism C c0 c), path_over Y (H_1 g) (f0 c0) y).
    { apply equiv_functor_forall_id. intro c1.
      refine (equiv_functor_forall_pb (BuildEquiv _ _ (@H_1 c1 c) _)). }
    apply equiv_iff_hprop.
    - intro q.
      refine (_ @ path_over_to_path (q c (identity c))).
      apply inverse.
      refine (ap (fun p => transport Y p (f0 c)) (H_idhom c)).
    - intro p. destruct p.
      intros c1 g. apply f1.
  Defined.

  Instance contr_B_set :
    forall (x : X), Contr {y : Y x & B_set x y}.
  Proof.
    intro x.
    cut (merely ({c : C & H_0 c = x}) -> Contr {y : Y x & B_set x y}).
    { intro hyp. apply hyp.
      apply merely_surj_H. }
    apply Trunc_rec. intros [c []].
    apply (contr_equiv' {y : Y (H_0 c) & (f0 c = y)}).
    { apply equiv_functor_sigma_id. intro y.
      apply equiv_inverse.
      apply B_set_base. }
    apply contr_basedpaths.
  Defined.

  Definition rezk_ind_set : forall (x : X), Y x
    := fun x => (center _ (contr_B_set x)).1 .

  (* Definition deloop_ind : forall (x : X), Y x *)
  (*   := fun x => pr1 (center _ (contr_C x)) *)

  Definition rezk_ind_set_q (x : X) (c : C):
    forall (p : H_0 c = x), path_over Y p (f0 c) (rezk_ind_set x)
    := ((center {y : Y x & B_set x y}).2 c).  

  (* Definition deloop_ind_p (x : X) : forall ω : (point X) = x, transport Y ω y0 = deloop_ind x *)
  (*   := pr1 (pr2 (center {y : Y x & C x y} )). *)
  
  (* Lemma q_is_ap_rezk_rec : *)
  (*   forall (x x': X) (c : C) (p : H_0 c = x) (q : x = x'), *)
  (*     rezk_rec_q x' c (p @ q) = *)
  (*     rezk_rec_q x c p @ ap rezk_rec q. *)
  (*     (* transport_pp Y α β _ @ ap (transport Y β) (deloop_ind_p x α) @ apD deloop_ind β. *) *)
  (* Proof. *)
  (*   intros. destruct q. destruct p. simpl. *)
  (*   apply inverse. apply concat_p1. *)
  (* Qed. *)
  Lemma equiv_path_over_id {A : Type} {B : A -> Type} (a : A) (b1 b2 : B a)
    : path_over B (idpath a) b1 b2 <~> b1 = b2.
  Proof.
    srapply @equiv_adjointify.
    - apply (path_over_to_path (p := idpath a)).
    - apply (path_to_path_over (p := idpath a)).
    - simpl. intros []. reflexivity.
    - intro q. destruct q. reflexivity.
  Defined.


  Definition rezk_ind_set_beta_obj (c : C) : (rezk_ind_set (H_0 c)) = f0 c.
  Proof.
    apply inverse.
    apply equiv_path_over_id. 
    apply (rezk_ind_set_q).
  Defined.


  (* Definition rezk_rec_beta_morphism : forall (c1 c2 : C) (g :  morphism C c1 c2), *)
  (*     ap rezk_rec (H_1 g) = (rezk_rec_beta_obj c1) @ (f1 g) @ (rezk_rec_beta_obj c2)^. *)
  (*     (* (ap (transport Y ω) deloop_ind_beta_pt)^ @ apD deloop_ind ω @ deloop_ind_beta_pt = f ω. *) *)
  (* Proof. *)
  (*   intros. unfold rezk_rec_beta_obj. *)
  (*   rewrite inv_V. refine (_ @ concat_p_pp _ _ _). apply moveL_Vp. *)
  (*   apply inverse. *)
  (*   refine (_ @ q_is_ap_rezk_rec _ _ _ _ _). rewrite concat_1p. *)
  (*   apply inverse. apply q_is_f1. *)
  (* Defined. *)

  


  (* Lemma f1_idhom (c : C) :  *)
  (*   path_over (fun p => path_over Y p (f0 c) (f0 c)) (H_idhom c) *)
  (*             (f1 (identity c)) (path_over_id (f0 c)). *)
  (* Proof. *)
  (*   assert (H_idhom c = *)
  (*           ap H_1 (identity_identity C c)^ @ H_2 (identity c) (identity c) *)
  (*   assert (q : path_over (fun p : H_0 c = H_0 c => path_over Y p (f0 c) (f0 c)) *)
  (*                         (H_2 (identity c) (identity c))  *)
  (*   apply (equiv_inj (path_over_concat _ (f2 1 1) *)
    
  (*   refine (transport_path_over *)
  (*   refine (path_over_concat _ (path_over_concat (f2 1 1) _ )). *)
  (*   apply (equiv_inj (concat (f1 1))). *)
  (*   refine (_ @ (concat_p1 _)^). *)
  (*   apply inverse. *)
  (*   refine (_ @ f2 1 1). *)
  (*   apply (ap f1). *)
  (*   apply inverse. *)
  (*   apply left_identity. *)
  (* Qed. *)

  
  (* Definition B (x : X) (y : Y) := *)
  (*   {q : forall (c : C) (p : H_0 c = x), (f0 c) = y & *)
  (*    forall (c1 c2 : C) (g : morphism C c1 c2) (p : H_0 c2 = x), *)
  (*      q c1 (H_1 g @ p) = *)
  (*      (f1 g) @ (q c2 p)}. *)

  (* Lemma q_is_f1 (c1 c2 : C) (y : Y) (q : B (H_0 c2) y) (h : morphism C c1 c2) : *)
  (*   q.1 c1 (H_1 h) = *)
  (*   (f1 h) @ (q.1 c2 idpath). *)
  (* Proof. *)
  (*   destruct q as [q b]. simpl. *)
  (*   refine (ap (q c1) (concat_p1 (H_1 h))^ @ _). *)
  (*   apply b. *)
  (* Qed. *)
  
  (* Definition B_base : forall (c : C) (y : Y), (B (H_0 c) y) <~> (f0 c = y). *)
  (* Proof. *)
  (*   intros c y. unfold B. *)
  (*   transitivity *)
  (*     {q : forall c0 : C, morphism C c0 c -> f0 c0 = y & *)
  (*        forall (c1 c2 : C) (g : morphism C c1 c2) (h : morphism C c2 c), *)
  (*          q c1 (h o g)%morphism = f1 g @ q c2 h}. *)
  (*   { srapply @equiv_functor_sigma'. *)
  (*     - apply equiv_functor_forall_id. *)
  (*       intro c1. *)
  (*       apply (equiv_precompose'). *)
  (*       exact (BuildEquiv _ _ H_1 _). *)
  (*     - intro q. simpl. *)
  (*       apply equiv_functor_forall_id. intro c1. *)
  (*       apply equiv_functor_forall_id. intro c2. *)
  (*       apply equiv_functor_forall_id. intro g. *)
  (*       srapply @equiv_functor_forall'. *)
  (*       { exact (BuildEquiv _ _ H_1 _). } *)
  (*       intro h. simpl. *)
  (*       unfold functor_forall. *)
  (*       apply equiv_concat_l. *)
  (*       apply (ap (q c1)). *)
  (*       apply H_2. } *)
            
    
  (*   srapply @equiv_adjointify. *)
  (*   - intros [q b]. *)
  (*     apply (q c). apply identity. *)
  (*   - intro p. (* destruct p0. *) *)
  (*     srapply @exist. *)
  (*     + intros c1 h. refine (_ @ p). *)
  (*       apply f1. exact h. *)
  (*     + hnf. intros. *)
  (*       refine (_ @ concat_pp_p _ _ _ ). apply whiskerR. *)
  (*       refine (f2 _ _). *)
  (*   - intro p. *)
  (*     refine (whiskerR (f1_idhom _) _ @ _). apply concat_1p. *)
  (*   - intros [q b].  *)
  (*     apply path_sigma_hprop. simpl. *)
  (*     apply path_forall. intro c1. *)
  (*     apply path_forall. intro g. *)
  (*     refine (_ @ ap (q c1) (left_identity _ _ _ _)). *)
  (*     apply inverse. apply b. *)
  (* Defined. *)




  (* Instance contr_B : *)
  (*   forall (x : X), Contr {y : Y & B x y}. *)
  (* Proof. *)
  (*   intro x. *)
  (*   cut (merely ({c : C & H_0 c = x}) -> Contr {y : Y & B x y}). *)
  (*   { intro hyp. apply hyp. *)
  (*     apply merely_surj_H. } *)
  (*   apply Trunc_rec. intros [c []]. *)
  (*   apply (contr_equiv' {y : Y & (f0 c = y)}). *)
  (*   { apply equiv_functor_sigma_id. intro y. *)
  (*     apply equiv_inverse. *)
  (*     apply B_base. } *)
  (*   apply contr_basedpaths. *)
  (* Defined. *)

  (* Definition rezk_rec : X -> Y *)
  (*   := fun x => (center _ (contr_B x)).1 . *)

  (* (* Definition deloop_ind : forall (x : X), Y x *) *)
  (* (*   := fun x => pr1 (center _ (contr_C x)) *) *)

  (* Definition rezk_rec_q (x : X) (c : C): *)
  (*   forall (p : H_0 c = x), f0 c = rezk_rec x *)
  (*   := ((center {y : Y & B x y}).2.1 c).   *)

  (* (* Definition deloop_ind_p (x : X) : forall ω : (point X) = x, transport Y ω y0 = deloop_ind x *) *)
  (* (*   := pr1 (pr2 (center {y : Y x & C x y} )). *) *)
  
  (* Lemma q_is_ap_rezk_rec : *)
  (*   forall (x x': X) (c : C) (p : H_0 c = x) (q : x = x'), *)
  (*     rezk_rec_q x' c (p @ q) = *)
  (*     rezk_rec_q x c p @ ap rezk_rec q. *)
  (*     (* transport_pp Y α β _ @ ap (transport Y β) (deloop_ind_p x α) @ apD deloop_ind β. *) *)
  (* Proof. *)
  (*   intros. destruct q. destruct p. simpl. *)
  (*   apply inverse. apply concat_p1. *)
  (* Qed. *)

  (* Definition rezk_rec_beta_obj (c : C) : rezk_rec (H_0 c) = f0 c:= *)
  (*   (rezk_rec_q (H_0 c) c idpath)^. *)


  (* Definition rezk_rec_beta_morphism : forall (c1 c2 : C) (g :  morphism C c1 c2), *)
  (*     ap rezk_rec (H_1 g) = (rezk_rec_beta_obj c1) @ (f1 g) @ (rezk_rec_beta_obj c2)^. *)
  (*     (* (ap (transport Y ω) deloop_ind_beta_pt)^ @ apD deloop_ind ω @ deloop_ind_beta_pt = f ω. *) *)
  (* Proof. *)
  (*   intros. unfold rezk_rec_beta_obj. *)
  (*   rewrite inv_V. refine (_ @ concat_p_pp _ _ _). apply moveL_Vp. *)
  (*   apply inverse. *)
  (*   refine (_ @ q_is_ap_rezk_rec _ _ _ _ _). rewrite concat_1p. *)
  (*   apply inverse. apply q_is_f1. *)
  (* Defined. *)
End rezk_ind_set.

Section Universal_principle.
  Context (X : Type) `{istrunc_X : IsTrunc 1 (X)}.
  Context (C : PreCategory)
          (H_0 : C -> X)
          `{merely_surj_H : forall (x : X), merely {c : C & H_0 c = x}}
          (H_1 : forall {c1 c2 : C},
              morphism C c1 c2 -> H_0 c1 = H_0 c2)
          `{isequiv_H1 : forall (c1 c2 : C), IsEquiv (@H_1 c1 c2)}
          (H_2 : forall (c1 c2 c3 : C) (g : morphism C c1 c2) (h : morphism C c2 c3),
              H_1 (h o g)%morphism = H_1 g @ H_1 h)
          (H_idhom : forall (c : C), H_1 (identity c) = idpath).
  Context (Y : Type) `{istrunc_Y : IsTrunc 1 (Y)}.

  Definition pg_functor (f : X -> Y) : Functor (groupoid_category X) (groupoid_category Y).
  Proof.
    srapply @Build_Functor; simpl.
    - exact f.
    - intros x y. exact (ap f).
    - intros x y z p q. simpl. apply ap_pp.
    - intro x. reflexivity.
  Defined.
  
  Definition rezk_restrict : (X -> Y) -> Functor C (groupoid_category Y).
  Proof.
    intro f.
    refine (Functor.compose (D := (groupoid_category X)) _ _).
    - exact (pg_functor f).
    - srapply @Build_Functor; simpl.
      + exact H_0.
      + exact H_1.
      + apply H_2.
      + apply H_idhom.
  Defined.

  Lemma isequiv_rezk_restrict : IsEquiv (rezk_restrict).
  Proof.
    srapply @isequiv_adjointify.
    - intro F.
      srefine (rezk_rec X C H_0 H_1 H_2 Y _ _ _ ).
      { apply (merely_surj_H). }
      + intro c. exact (F c).
      + simpl. 
        apply (morphism_of F).
      + apply (composition_of F).
    - intro F.
      srapply @path_functor'.
      + simpl. intro c. 
        apply rezk_rec_beta_obj.
      + simpl.
        assert (h :forall (y1 y2 : Y) (p : y1 = y2),
                   idtohom (C := Core.groupoid_category Y) p = p).
        { intros. destruct p. reflexivity. }
        intros.
        rewrite h. rewrite h. clear h.
        rewrite rezk_rec_beta_morphism.
        apply moveR_Vp.
        rewrite concat_pp_p.
        rewrite concat_Vp. rewrite concat_p1. reflexivity.
    - intro f.
      apply path_arrow. intro x.
      revert x.
      srefine (rezk_ind_set X C H_0 H_1  H_idhom 
                            (fun x => rezk_rec X C H_0 H_1 H_2 Y
                                               (fun c : C => ((rezk_restrict f) _0 c)%object)
                                               (morphism_of (rezk_restrict f))
                                               (composition_of (rezk_restrict f)) x
                                      = f x) _ _).
      { apply merely_surj_H. }
      + intro c. simpl.
        apply rezk_rec_beta_obj.
      + intros.
        apply path_to_path_over. simpl.
        refine (transport_paths_FlFr _ _ @ _).
        rewrite rezk_rec_beta_morphism. simpl.
        rewrite inv_pp. rewrite inv_pp.
        repeat rewrite concat_pp_p.
        apply moveR_Vp. rewrite concat_Vp.
        apply moveR_Vp. rewrite concat_p_pp. rewrite concat_Vp.
        rewrite concat_1p. rewrite concat_p1. reflexivity.
  Qed. 
End Universal_principle.


(* Section rezk_ind. *)
(*     Context (X : Type) (* `{IsTrunc_X : IsTrunc 1 X} *). (* the latter variable not strictly necessary *) *)
(*   (* Context (X : Type) (x0 : X) (* (istrunc_X : IsTrunc 1 X) *) *) *)
(*   (*         `{isconn_X : forall (x : X), merely (x0 = x)}. *) *)

(*   Context (C : PreCategory) *)
(*           (* (H : Functor C (groupoid_category X)) *) *)
(*           (* (isfullyfaithful_H : IsFullyFaithful H) *) *)
(*           (* (isessentiallysurjective_H : IsEssentiallySurjective H). *) *)
(*           (* The following is uncurrying a weak equivalence from C to X *) *)
(*           (H_0 : C -> X) *)
(*           `{merely_surj_H : forall (x : X), merely {c : C & H_0 c = x}} *)
(*           (H_1 : forall {c1 c2 : C}, *)
(*               morphism C c1 c2 -> H_0 c1 = H_0 c2) *)
(*           `{isequiv_H1 : forall (c1 c2 : C), IsEquiv (@H_1 c1 c2)} *)
(*           (H_idhom : forall (c : C), H_1 (identity c) = idpath) *)
(*           (H_2 : forall (c1 c2 c3 : C) (g : morphism C c1 c2) (h : morphism C c2 c3), *)
(*               H_1 (h o g)%morphism = H_1 g @ H_1 h). *)
(*   Arguments H_1 {c1 c2}. *)
(*   Arguments H_2 {c1 c2 c3}. *)

(*   (* Lemma H_idhom (c : C) : H_1 (identity c) = idpath. *) *)
(*   (* Proof. *) *)
(*   (*   apply (equiv_inj (concat (H_1 1))). *) *)
(*   (*   refine (ap H_1 (identity_identity C c)^ @ _). *) *)
(*   (*   refine (H_2 (identity c) (identity c) @ _). *) *)
(*   (*   ap H_1 (identity_identity C c)^ @ H_2 (identity c) (identity c) *) *)

(*   Instance istrunc_X : IsTrunc 1 X. *)
(*   Proof. *)
(*     intros x1 x2. *)
(*     generalize (merely_surj_H x1). apply Trunc_rec. intros [c1 p]. destruct p. *)
(*     generalize (merely_surj_H x2). apply Trunc_rec. intros [c2 p]. destruct p. *)
(*     apply (trunc_equiv _ H_1). *)
(*   Defined. *)

(*   Context (Y : X -> Type) *)
(*           `{istrunc_Y : forall (x : X), IsHSet (Y x)} *)
(*           (f0 : forall (c : C), Y (H_0 c)) *)
(*           (f1 : forall {c1 c2 : C} (g : morphism C c1 c2), *)
(*               path_over Y (H_1 g) (f0 c1) (f0 c2)) *)
(*           (f2 : forall {c1 c2 c3 : C} (g : morphism C c1 c2) (h : morphism C c2 c3), *)
(*               path_over (fun p => path_over Y p (f0 c1) (f0 c3)) *)
(*                         (H_2 g h) *)
(*                         (f1 (h o g)%morphism) *)
(*                         (path_over_concat (f1 g) (f1 h))).            *)
(*   Arguments f1 {c1 c2} g. *)
(*   Arguments f2 {c1 c2 c3} g h. *)

  

(*   Definition sect_of_rezk_ind : X -> {x : X & Y x}. *)
(*   Proof. *)
(*     srapply (@rezk_rec X C (@H_0) (merely_surj_H) (@H_1) _ (@H_2)). *)
(*     - intro c. exists (H_0 c). exact (f0 c). *)
(*     - intros c1 c2 g. simpl. *)
(*       srapply @path_sigma'. *)
(*       + simpl. apply H_1. exact g. *)
(*       + simpl. apply f1. *)
(*     -  simpl. intros. *)
(*        refine (_ @ (path_sigma_concat' _ _ _ _)^). *)
(*        change (path_sigma' ?p ?q) with (equiv_path_sigma' (_ ; _) (_;_) (p; q)). *)
(*        apply (ap (equiv_path_sigma' _ _)). *)
(*        srapply @path_sigma'. *)
(*       + simpl. apply H_2. *)
(*       + simpl. apply f2. *)
(*   Defined. *)

(*   Definition sect_of_rezk_ind_beta_obj (c : C) : *)
(*     sect_of_rezk_ind (H_0 c) = (H_0 c; f0 c). *)
(*   Proof. *)
(*     apply rezk_rec_beta_obj. *)
(*   Defined.   *)
      
(*   Definition issect_sect_of_rezk_ind (x : X) : (sect_of_rezk_ind x).1 = x. *)
(*   Proof. *)
(*     revert x.     *)
(*     srapply (@rezk_ind_set X C H_0 merely_surj_H (@H_1) _ (@H_idhom)). *)
(*     - intro c. simpl. *)
(*       change (H_0 c) with (H_0 c; f0 c).1. *)
(*       apply (ap (fun x => x.1)). *)
(*       apply sect_of_rezk_ind_beta_obj. *)
(*     - intros.  simpl. *)
(*       apply path_to_path_over. *)
(*       refine (transport_paths_FlFr (H_1 g) _ @ _). rewrite ap_idmap.       *)
(*       rewrite (ap_compose _ (fun x => x.1)). *)
(*       refine (concat_pp_p _ _ _ @ _). *)

(*       apply moveR_Vp. *)
(*       refine (_ @ ap_pp (fun x : {x : X & Y x} => x.1) *)
(*                 (ap sect_of_rezk_ind (H_1 g)) (sect_of_rezk_ind_beta_obj c2)). *)
(*       apply moveR_Mp.       *)
(*       rewrite <- (ap_V (fun x : {x : X & Y x} => x.1) (sect_of_rezk_ind_beta_obj c1)). *)
(*       refine (_ @ ap_pp (fun x : {x : X & Y x} => x.1) *)
(*                         (sect_of_rezk_ind_beta_obj c1)^ _). *)

(*       rezk_rec_beta_morphism *)
(*                 _ _). *)
(*       rewrite <- (ap_pp (fun x : {x : X & Y x} => x.1) *)
(*                         (ap sect_of_rezk_ind (H_1 g))^ *)
(*                         (sect_of_rezk_ind_beta_obj c1)). *)

(*       apply moveR_Mp. *)
(*       refine ( *)
          
(*           (ap_pp (fun x : {x : X & Y x} => x.1) (ap sect_of_rezk_ind (H_1 g))^ ((rezk_rec_beta_obj X C H_0 (@H_1) (@H_2) {x : X & Y x} (fun c : C => (H_0 c; f0 c)) *)
(*        (fun (c0 c3 : C) (g0 : morphism C c0 c3) => path_sigma' (H_1 g0) (f1 g0)) *)
(*        (fun (c0 c3 c4 : C) (g0 : morphism C c0 c3) (h : morphism C c3 c4) => *)
(*         ap (fun X0 : {p : H_0 c0 = H_0 c4 & path_over Y p (f0 c0) (f0 c4)} => path_sigma' X0.1 X0.2) *)
(*           (path_sigma' (H_2 g0 h) (f2 g0 h)) @ (path_sigma_concat' (H_1 g0) (f1 g0) (H_1 h) (f1 h))^) *)
(*        c1)))^ @ _). *)

(*       rewrite <-  *)
(*       rewrite (ap_compose (fun x => x.1)). *)
      
(*       transitivity (H_0 c; f0 c).1. *)
(*       {  } *)
      
(*       unfold sect_of_rezk_ind. *)
(*       refine (rezk_rec_beta_obj *)
(*                 X C H_0 (@H_1) (@H_2) {x : X & Y x} (fun c0 : C => (H_0 c0; f0 c0)) *)
(*                 (fun (c1 c2 : C) (g : morphism C c1 c2) => path_sigma' (H_1 g) (f1 g)) *)
(*                 (fun (c1 c2 c3 : C) (g : morphism C c1 c2) (h : morphism C c2 c3) => *)
(*                    ap (equiv_path_sigma' (H_0 c1; f0 c1) (H_0 c3; f0 c3)) *)
(*                       (path_sigma' (H_2 g h) (f2 g h)) @ *)
(*                       (path_sigma_concat' (H_1 g) (f1 g) (H_1 h) (f1 h))^)) *)


(*                                 _ _ _ _ _ _ _  c @ _). *)
(*       Check ( X ). *)
      
    
(*     simpl. *)



(* (* Section rezk_ind_prop. *) *)
(* (*   Context (X : Type).  *) *)
(* (*   Context (Y : X -> hProp) *) *)
(* (*           (y0 : forall (c : C), Y (H_0 c)). *) *)

(* (*   Definition deloop_ind_prop : forall x : X, Y x. *) *)
(* (*   Proof. *) *)
(* (*     intro x. *) *)
(* (*     generalize (isconn_conn_ptype X x). *) *)
(* (*     apply Trunc_ind. *) *)
(* (*     { exact _. } *) *)
(* (*     intros []. exact y0. *) *)
(* (*   Defined. *) *)
(* (* End rezk_ind_prop.     *) *)
    




(* (* Section rezk_ind_prop. *) *)
(* (*   Context (X : Type).  *) *)
(* (*   Context (Y : X -> hProp) *) *)
(* (*           (y0 : forall (c : C), Y (H_0 c)). *) *)

(* (*   Definition deloop_ind_prop : forall x : X, Y x. *) *)
(* (*   Proof. *) *)
(* (*     intro x. *) *)
(* (*     generalize (isconn_conn_ptype X x). *) *)
(* (*     apply Trunc_ind. *) *)
(* (*     { exact _. } *) *)
(* (*     intros []. exact y0. *) *)
(* (*   Defined. *) *)
(* (* End rezk_ind_prop.     *) *)
    

(* Section rezk_ind. *)
(*   Context (X : Type). *)
(*   Context (C : PreCategory) *)
(*           (* (H : Functor C (groupoid_category X)) *) *)
(*           (* (isfullyfaithful_H : IsFullyFaithful H) *) *)
(*           (* (isessentiallysurjective_H : IsEssentiallySurjective H). *) *)
(*           (* The following is uncurrying a weak equivalence from C to X *) *)
(*           (H_0 : C -> X) *)
(*           (merely_surj_H : forall (x : X), merely {c : C & H_0 c = x}) *)
(*           (H_1 : forall {c1 c2 : C}, *)
(*               morphism C c1 c2 -> H_0 c1 = H_0 c2) *)
(*           `{isequiv_H1 : forall (c1 c2 : C), IsEquiv (@H_1 c1 c2)} *)
(*           (H_idhom : forall (c : C), H_1 (identity c) = idpath) *)
(*           (H_2 : forall (c1 c2 c3 : C) (g : morphism C c1 c2) (h : morphism C c2 c3), *)
(*               H_1 (h o g)%morphism = H_1 g @ H_1 h). *)
(*   Arguments H_1 {c1 c2}. *)
(*   Arguments H_2 {c1 c2 c3}.   *)
  

(*   Context (Y : X -> Type) *)
(*           `{isset_y : forall x : X, IsHSet (Y x)} *)
(*           (f0 : forall c : C, Y (H_0 c)) *)
(*           (f1 : forall {c1 c2 : C} (g : morphism C c1 c2), *)
(*               path_over Y (H_1 g) (f0 c1) (f0 c2)). *)

(*   Definition deloop_ind_set : forall x : X, Y x. *)
(*   Proof. *)
(*     apply (deloop_ind X Y y0 f). *)
(*     intros. *)
(*     apply isset_y. *)
(*   Defined. *)
(* End deloop_ind_set. *)

(* Section deloop_rec. *)
(*   Context (X : Conn_pType). *)
(*   Context (Y : Type) *)
(*           `{istrunc_y : IsTrunc 1 Y} *)
(*           (y0 : Y) *)
(*           (f : ((point X) = (point X)) -> (y0 = y0)) *)
(*           (ishom_f : forall (α ω : (point X) = (point X)), *)
(*               f (α @ ω) = f α @ f ω). *)

(*   Lemma rec_help (α ω : (point X) = (point X)) : *)
(*     transport_const (α @ ω) y0 @ f (α @ ω) = *)
(*     (transport_pp (fun _ : X => Y) α ω y0 *)
(*                   @ ap (transport (fun _ : X => Y) ω) (transport_const α y0 @ f α)) *)
(*       @ (transport_const ω y0 @ f ω). *)
(*   Proof. *)
(*     rewrite ishom_f. *)
(*     destruct (f ω). destruct (f α). *)
(*     destruct ω. destruct α. reflexivity. *)
(*   Qed. *)

(*   Definition deloop_rec : X -> Y := *)
(*     deloop_ind X (fun _ => Y) y0 (fun ω => transport_const ω y0 @ f ω) rec_help. *)

(*   Definition deloop_rec_beta_pt : deloop_rec (point X) = y0 := *)
(*     deloop_ind_beta_pt X _ _ _ _ . *)

(*   Definition deloop_rec_beta_loop (ω : (point X) = (point X)) : *)
(*     deloop_rec_beta_pt^ @ ap deloop_rec ω @ deloop_rec_beta_pt = f ω. *)
(*   Proof. *)
(*     apply (cancelL (transport_const ω y0)). *)
(*     refine (_ @ deloop_ind_beta_loop X (fun _ => Y) y0 *)
(*               (fun ω => transport_const _ _ @ f ω) rec_help ω). *)
(*     change (deloop_ind X (fun _ => Y) y0 (fun ω => transport_const ω y0 @ f ω) rec_help) *)
(*     with deloop_rec. *)
(*     change (deloop_ind_beta_pt X  *)
(*                                (fun _ : X => Y) y0 *)
(*                                (fun ω0 : (point X) = (point X) => transport_const ω0 y0 @ f ω0) rec_help) *)
(*     with deloop_rec_beta_pt. *)
(*     generalize (deloop_rec_beta_pt). intros []. simpl. *)
(*     revert ω. *)
(*     cut (forall (x : X) (ω : point X = x), *)
(*             transport_const ω (deloop_rec (point X)) @ ((1 @ ap deloop_rec ω) @ 1) = *)
(*             (1 @ apD deloop_rec ω) @ 1). *)
(*     { intro H. apply H. } *)
(*     intros x []. reflexivity. *)
(*   Qed. *)

(*   Definition deloop_rec_beta_loop' (ω : (point X) = (point X)) : *)
(*     ap deloop_rec ω = deloop_rec_beta_pt @ f ω @ deloop_rec_beta_pt^. *)
(*   Proof. *)
(*     apply moveL_pV. apply moveL_Mp. *)
(*     refine (concat_p_pp _ _ _ @ _). *)
(*     apply deloop_rec_beta_loop. *)
(*   Qed. *)

(* End resc_rec. *)


