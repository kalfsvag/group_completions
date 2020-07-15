Require Import HoTT.
Require Import FunextAxiom.

From A_BPQ Require Import conn_ptype.

(* Making an induction principle for pointed connected 1-types, based on notes by Thierry Coquand *)

Section deloop_induction.
  Context (X : Conn_pType) .
  (* Context (X : Type) (x0 : X) (* (istrunc_X : IsTrunc 1 X) *) *)
  (*         `{isconn_X : forall (x : X), merely (x0 = x)}. *)

  Context (Y : X -> Type)
          `{istrunc_Y : forall x : X, IsTrunc 1 (Y x)}
          (y0 : Y (point X))
          (f : forall (ω : point X = point X), transport Y ω y0 = y0)
          (ishom_f : forall (α ω : point X = point X),
              f (α @ ω) =
              transport_pp Y  α ω y0 @ ap (transport Y ω) (f α) @ (f ω)).
  Lemma ishom_f_1 :
    f idpath = idpath.
  Proof.
    apply (equiv_inj (concat (f idpath))).
    refine (_ @ (concat_p1 _)^).
    apply inverse.
    refine (ishom_f idpath idpath @ _).
    apply whiskerR. simpl.
    refine (concat_1p _ @ _).
    apply ap_idmap.
  Qed.

  
  Definition C (x : X) (y : Y x) :=
    {p : forall (ω : point X = x),
        transport Y ω y0 = y &
        forall (α : point X = point X) (ω : point X = x),
          p (α @ ω) =
          transport_pp Y α ω _ @ ap (transport Y ω) (f α) @ p (ω)}.

  Lemma p_is_f (y : Y (point X)) (p : C (point X) y) (α : (point X) = (point X)) :
    p.1 α = f α @ (p.1 idpath).
  Proof.
    destruct p as [p H]. simpl.
    refine ((apD p (concat_p1 α))^ @ _).
    refine (transport_paths_Fl (concat_p1 α) (p (α @ 1)) @ _).
    apply moveR_Vp.
    refine (H α idpath @ _).
    refine (_ @ concat_pp_p _ _ _ ). apply whiskerR.
    apply concat2.
    + destruct α. reflexivity.
    + destruct (f α). reflexivity.
  Qed.    
  
  Definition C_base : forall y : Y (point X), (C (point X) y) <~> y0 = y.
  Proof.
    intro y.
    srapply @equiv_adjointify.
    - intros [p H].
      exact (p idpath).
    - intro p0.
      exists (fun ω => f ω @ p0).
      intros.
      refine (_ @ concat_pp_p _ _ _). apply whiskerR.
      apply ishom_f.
    - intro p0.
      refine (_ @ concat_1p _). apply whiskerR.
      apply ishom_f_1.
    - intros [p H].
      apply path_sigma_hprop. simpl.
      apply path_forall. intro α.
      apply inverse.
      apply (p_is_f y (p; H)).
  Defined.


  Instance contr_C :
    forall (x : X), Contr {y : Y x & C x y}.
  Proof.
    intro x. 
    generalize (isconn_conn_ptype X x).
    (* Being contractible is a proposition, so we can assume that X is a single point *)
    apply Trunc_rec. intros [].
    apply (contr_equiv' {y : Y (point X) & y0 = y}).
    { apply equiv_functor_sigma_id. intro y.
      apply equiv_inverse.
      apply C_base. }
    apply contr_basedpaths.
  Defined.

  Definition deloop_ind : forall (x : X), Y x
    := fun x => pr1 (center _ (contr_C x)).

  Definition deloop_ind_p (x : X) : forall ω : (point X) = x, transport Y ω y0 = deloop_ind x
    := pr1 (pr2 (center {y : Y x & C x y} )).
  
  Lemma p_is_apD_ind :
    forall (x x': X) (α : (point X) = x) (β : x = x'),
      deloop_ind_p x' (α @ β) =
      transport_pp Y α β _ @ ap (transport Y β) (deloop_ind_p x α) @ apD deloop_ind β.
  Proof.
    intros. destruct β. destruct α. simpl.
    destruct (deloop_ind_p (point X) idpath). reflexivity.
  Qed.

  Definition deloop_ind_beta_pt : deloop_ind (point X) = y0 :=
    (deloop_ind_p (point X) idpath)^.


  Definition deloop_ind_beta_loop : forall (ω : (point X) = (point X)),
      (ap (transport Y ω) deloop_ind_beta_pt)^ @ apD deloop_ind ω @ deloop_ind_beta_pt = f ω.
  Proof.
    intro. apply moveR_pM. unfold deloop_ind_beta_pt.
    rewrite ap_V. rewrite inv_V. rewrite inv_V.
    refine (_ @ p_is_f _ _ ω).
    change ((center {y : Y (point X) & C (point X) y}).2).1 with (deloop_ind_p (point X)).
    apply inverse.
    rewrite <- (concat_1p ω).    
    refine ((p_is_apD_ind (point X) (point X) idpath ω) @ _).
    simpl. revert ω.
    cut (forall (x : X) (ω : point X = x),
            (transport_pp Y 1 ω y0 @ ap (transport Y ω) (deloop_ind_p (point X) 1)) @ apD deloop_ind ω =
            ap (transport Y (1 @ ω)) (deloop_ind_p (point X) 1) @ apD deloop_ind (1 @ ω)).
    { intro H. apply H. }
    intros x [].
    simpl. destruct (deloop_ind_p (point X) idpath).
    reflexivity.
  Qed.
End deloop_induction.

Section deloop_ind_prop.
  Context (X : Conn_pType).
  Context (Y : X -> hProp)
          (y0 : Y ((point X))).

  Definition deloop_ind_prop : forall x : X, Y x.
  Proof.
    intro x.
    generalize (isconn_conn_ptype X x).
    apply Trunc_ind.
    { exact _. }
    intros []. exact y0.
  Defined.
End deloop_ind_prop.    
    

Section deloop_ind_set.
  Context (X : Conn_pType).

  Context (Y : X -> Type)
          `{isset_y : forall x : X, IsHSet (Y x)}
          (y0 : Y ((point X)))
          (f : forall (ω : (point X) = (point X)), transport Y ω y0 = y0).

  Definition deloop_ind_set : forall x : X, Y x.
  Proof.
    apply (deloop_ind X Y y0 f).
    intros.
    apply isset_y.
  Defined.
End deloop_ind_set.

Section deloop_rec.
  Context (X : Conn_pType).

  Context (Y : Type)
          `{istrunc_y : IsTrunc 1 Y}
          (y0 : Y)
          (f : ((point X) = (point X)) -> (y0 = y0))
          (ishom_f : forall (α ω : (point X) = (point X)),
              f (α @ ω) = f α @ f ω).

  Lemma rec_help (α ω : (point X) = (point X)) :
    transport_const (α @ ω) y0 @ f (α @ ω) =
    (transport_pp (fun _ : X => Y) α ω y0
                  @ ap (transport (fun _ : X => Y) ω) (transport_const α y0 @ f α))
      @ (transport_const ω y0 @ f ω).
  Proof.
    rewrite ishom_f.
    destruct (f ω). destruct (f α).
    destruct ω. destruct α. reflexivity.
  Qed.

  Definition deloop_rec : X -> Y :=
    deloop_ind X (fun _ => Y) y0 (fun ω => transport_const ω y0 @ f ω) rec_help.

  Definition deloop_rec_beta_pt : deloop_rec (point X) = y0 :=
    deloop_ind_beta_pt X _ _ _ _ .

  Definition deloop_rec_beta_loop (ω : (point X) = (point X)) :
    deloop_rec_beta_pt^ @ ap deloop_rec ω @ deloop_rec_beta_pt = f ω.
  Proof.
    apply (cancelL (transport_const ω y0)).
    refine (_ @ deloop_ind_beta_loop X (fun _ => Y) y0
              (fun ω => transport_const _ _ @ f ω) rec_help ω).
    change (deloop_ind X (fun _ => Y) y0 (fun ω => transport_const ω y0 @ f ω) rec_help)
    with deloop_rec.
    change (deloop_ind_beta_pt X 
                               (fun _ : X => Y) y0
                               (fun ω0 : (point X) = (point X) => transport_const ω0 y0 @ f ω0) rec_help)
    with deloop_rec_beta_pt.
    generalize (deloop_rec_beta_pt). intros []. simpl.
    revert ω.
    cut (forall (x : X) (ω : point X = x),
            transport_const ω (deloop_rec (point X)) @ ((1 @ ap deloop_rec ω) @ 1) =
            (1 @ apD deloop_rec ω) @ 1).
    { intro H. apply H. }
    intros x []. reflexivity.
  Qed.

  Definition deloop_rec_beta_loop' (ω : (point X) = (point X)) :
    ap deloop_rec ω = deloop_rec_beta_pt @ f ω @ deloop_rec_beta_pt^.
  Proof.
    apply moveL_pV. apply moveL_Mp.
    refine (concat_p_pp _ _ _ @ _).
    apply deloop_rec_beta_loop.
  Qed.

End deloop_rec.

Section universal.
  Context (X : Conn_pType).
  Context (Y : Type) `{istrunc_y : IsTrunc 1 Y}.

  Definition rec_of (g : X -> Y) : X -> Y.
  Proof.
    apply (deloop_rec X Y (g (point X)) (fun ω => ap g ω)).
    intros. apply ap_pp.
  Defined.

  Definition is_rec (g : X -> Y) :
    rec_of g == g.
  Proof.
    intro x. revert x.
    srapply (deloop_ind_set X); simpl.
    - simpl. apply deloop_rec_beta_pt.
    - simpl. intros.
      refine (transport_paths_FlFr ω _ @ _).
      refine (concat_pp_p _ _ _ @ _).
      apply moveR_Vp.
      apply moveR_Mp. apply inverse.
      refine (concat_p_pp _ _ _ @ _).
      refine (deloop_rec_beta_loop X Y (g (point X))
                                   (fun ω0 : (point X) = (point X) => ap g ω0)
                                   (fun α ω0 : (point X) = (point X) => ap_pp g α ω0) ω).
  Defined.

  Definition deloop_rec_uncurried :
    {y0 : Y &
          {f : ((point X) = (point X)) -> (y0 = y0) &
                forall (α ω : (point X) = (point X)), f (α @ ω) = f α @ f ω}} -> X -> Y.
  Proof.
    intros [y0 [f ishom_f]]. exact (deloop_rec X Y y0 f ishom_f).
  Defined.

  Definition isequiv_deloop_rec_uncurried : IsEquiv deloop_rec_uncurried.
  Proof.
    srapply @isequiv_adjointify.
    - intro g.
      exists (g (point X)). exists (fun ω => ap g ω). intros. apply ap_pp.
    - intro g. apply path_arrow.
      apply (is_rec g).
    - intros [y0 [f ishom_f]].
      srapply @path_sigma.
      + simpl. apply deloop_rec_beta_pt.
      + simpl. srapply @path_sigma_hprop. simpl.
        apply path_forall. intro ω.
        refine (_ @ deloop_rec_beta_loop X Y y0 f ishom_f ω).
        generalize (deloop_rec_beta_pt X Y y0 f ishom_f). intros [].
        simpl.
        rewrite concat_1p. rewrite concat_p1. reflexivity.
  Defined.

  Definition path_deloop
             (f g : X -> Y)
             (p : f (point X) = g (point X))
             (eq_ap : forall w : (point X) = (point X), ap f w = p @ ap g w @ p^)
    : f == g.
  Proof.
    intro x. revert x.
    srapply (deloop_ind_set X).
    - simpl. exact p.
    - intro. simpl.
      refine (transport_paths_FlFr _ p @ _).
      rewrite eq_ap.
      rewrite inv_pp. rewrite inv_V.
      rewrite inv_pp. rewrite concat_p_pp.
      rewrite concat_pV_p. rewrite concat_pV_p. reflexivity.
  Defined.

  Definition path_deloop_id (f : X -> Y) (x : X) : 
    path_deloop f f idpath (fun w => inverse (concat_p1 _ @ concat_1p (ap f w))) x = idpath.
  Proof.
    revert x.
    apply (deloop_ind_prop X). simpl.
    refine (deloop_ind_beta_pt X _ _ _ _ ).
  Qed.    
    
End universal.

Section pointed_rec.
  Context (X : Conn_pType).
  
  Context (Y : pType) {istrunc_y : IsTrunc 1 Y}.
  
  (* Record p1Type := *)
  (*   {onetype_of :> 1-Type ; *)
  (*    ispointed_1type_of : IsPointed onetype_of}. *)
  (* Global Instance ispointed_1type_of' (Y : p1Type) : IsPointed Y *)
  (*   := ispointed_1type_of Y. *)
  (* Definition ptype_of (Y : p1Type) := Build_pType Y _. *)
  (* Coercion ptype_of : p1Type >-> pType. *)
  (* Context (Y : p1Type). *)

  Definition equiv_deloop_prec :
    {f : loops X -> loops Y & forall α ω : loops X, f (α @ ω) = f α @ f ω} <~> pMap X Y.
  Proof.
    refine (issig_pmap X Y oE _).
    transitivity
      {a : {y : Y & {f : loops X -> y = y &
                                    forall α ω : loops X, f (α @ ω) = f α @ f ω}} & point Y = pr1 a}.
    - srapply @equiv_adjointify.
      + intros [f ishom_f].
        srapply @exist.
        *  exists (point Y).
           exists f. exact ishom_f.
        * reflexivity.
      + intros [[y [f ishom]] p].
        simpl in p.  destruct p.
        exact (f; ishom).
      + intros [[y [f ishom]] p]. simpl in p. destruct p.
        reflexivity.
      + intros [f ishom_f]. reflexivity.
    - srapply @equiv_functor_sigma'.
      + exact (BuildEquiv _ _ (deloop_rec_uncurried X  Y)
                          (isequiv_deloop_rec_uncurried X Y)).
      + simpl.
        intros [y [f ishom]].
        refine (equiv_path_inverse _ _ oE _).
        apply equiv_concat_r.
        simpl. apply inverse. unfold deloop_rec_uncurried.
        apply deloop_rec_beta_pt.
  Defined.

  Definition deloop_prec (f : loops X -> loops Y)
             (ishom_f : forall α ω : loops X, f (α @ ω) = f α @ f ω) :
    pMap X Y.
  Proof.
    apply (Build_pMap X Y (deloop_rec X Y (point Y) f ishom_f)).
    apply deloop_rec_beta_pt.
  Defined.

  Lemma deloop_prec_eq_equiv_dloop_prec (f : loops X -> loops Y)
             (ishom_f : forall α ω : loops X, f (α @ ω) = f α @ f ω) :
    deloop_prec f ishom_f = equiv_deloop_prec (f; ishom_f).
  Proof.
    simpl. rewrite concat_1p. rewrite inv_V.
    reflexivity.
  Qed.

End pointed_rec.


Require Import monoids_and_groups.
Section functor_deloop.
  Context (X : Conn_pType) `{istrunc_X : IsTrunc 1 X}.
  Context (Y : pType) `{istrunc_Y : IsTrunc 1 Y}.

  Definition equiv_functor_deloop'
    : Homomorphism (loopGroup X (point X)) (loopGroup Y (point Y)) <~> pMap X Y.
  Proof.
    refine (equiv_deloop_prec X Y oE _).
    srapply @equiv_adjointify.
    - intros [f f_id f_mult]. exact (f; f_mult).
    - intros [f f_mult].
      apply (@Build_GrpHom (loopGroup X _) (loopGroup Y _) f f_mult).
    - intro f.
      apply path_sigma_hprop. reflexivity.
    - intro f. apply path_hom. reflexivity.
  Defined.

  Definition functor_deloop : Homomorphism (loopGroup X (point X)) (loopGroup Y (point Y)) -> pMap X Y.
  Proof.
    intros [f f_1 f_mult]. simpl in f_mult.
    srapply @Build_pMap.
    - apply (deloop_rec X Y (point Y) f f_mult).
    - apply deloop_rec_beta_pt.
  Defined.      

  Definition functor_loop : pMap X Y -> Homomorphism (loopGroup X (point X)) (loopGroup Y (point Y)).
  Proof.
    intro f.
    srapply @Build_GrpHom.
    - apply (loops_functor f).
    - simpl. destruct (point_eq f).
      intros. destruct g2. destruct g1. reflexivity.
  Defined.

  Global Instance isequiv_functor_loop : IsEquiv functor_loop.
  Proof.
    apply (isequiv_adjointify functor_loop functor_deloop).
    - intro f. apply path_hom. apply path_arrow.
      intro w. simpl in w. destruct f as [f f_1 f_mult]. simpl.
      rewrite deloop_rec_beta_loop'. hott_simpl.
    - intro f. apply path_pmap.          
      srapply @Build_pHomotopy.
      + srapply (path_deloop X ).
        { refine (deloop_rec_beta_pt X _ _ _ _@ (point_eq f)^). }
        intro w.
        refine (deloop_rec_beta_loop' X Y (point Y) _ _ w @ _).
        pointed_reduce.
        reflexivity.
      + apply moveR_pM.
        refine (deloop_ind_beta_pt X  _ _ _ _ ). 
  Defined.

  Definition equiv_functor_loop
    : pMap X Y <~> Homomorphism (loopGroup X (point X)) (loopGroup Y (point Y))
    := BuildEquiv _ _ functor_loop _.

  Definition functor_deloop_loop
             (f : Homomorphism (loopGroup X (point X)) (loopGroup Y (point Y)))
    : loops_functor (functor_deloop f) == f.
  Proof.
    intro ω. unfold loops_functor. simpl.
    refine (concat_p_pp _ _ _ @ _). apply deloop_rec_beta_loop.
  Defined.




End functor_deloop.

  Lemma functor_loop_id (X : Conn_pType) 
        `{istrunc_X : IsTrunc 1 X} :
    functor_loop X X (@pmap_idmap X) == idhom.
  Proof.
    unfold functor_loop. simpl. intros []. reflexivity.
  Defined.


  Lemma functor_loop_compose
        (X : Conn_pType)  `{istrunc_X : IsTrunc 1 X}
        (Y : Conn_pType) `{istrunc_Y : IsTrunc 1 Y}
        (Z : pType) `{istrunc_Z : IsTrunc 1 Z}
        (f : pMap X Y) (g : pMap Y Z)
    : functor_loop Y Z g oH functor_loop X Y f ==
      functor_loop X Z (pmap_compose g f).
  Proof.
    unfold functor_loop. simpl. intro p.
    pointed_reduce.
    apply inverse. apply ap_compose.
  Qed.


Section functor_deloop_id.
  Context (X : Conn_pType)  `{istrunc_X : IsTrunc 1 X}.
  Definition functor_deloop_id :
    (functor_deloop X X idhom) = @pmap_idmap X.
  Proof.
    apply (equiv_inj (functor_loop X X)).
    refine (eisretr (functor_loop X X) idhom @ _).
    apply inverse. 
    apply path_hom. apply path_arrow.
    apply functor_loop_id.
  Defined.
End functor_deloop_id.

Section functor_deloop_compose.
  Context (X : Conn_pType) `{istrunc_X : IsTrunc 1 X}.
  Context (Y : Conn_pType) `{istrunc_Y : IsTrunc 1 Y}.
  Context (Z : pType) `{istrunc_Z : IsTrunc 1 Z}.

  Open Scope monoid_scope.
  Definition functor_deloop_compose
             (f : Homomorphism (loopGroup X (point X)) (loopGroup Y (point Y)))
             (g : Homomorphism (loopGroup Y (point Y)) (loopGroup Z (point Z))) :
    (functor_deloop X Z (g oH f)) =
    (pmap_compose (functor_deloop Y Z g)
                  (functor_deloop X Y f)).
  Proof.
    apply (equiv_inj (functor_loop X Z)).
    refine (eisretr (functor_loop X Z) (g oH f) @ _).
    apply path_hom. apply path_arrow. intro x.
    refine (_ @ functor_loop_compose _ _ _ _ _ _).
    apply inverse.
    apply (ap011 (fun a b => (a oH b) x)).
    - refine (eisretr (functor_loop Y Z) g).
    - refine (eisretr (functor_loop X Y) f).
  Qed.
End functor_deloop_compose.



(* Section deloop_double_rec. *)
(*     Context (X1 : Type) (a : X1)  *)
(*           (isconn_X1 : forall (x : X1), merely (a = x)). *)
(*     Context (X2 : Type) (b : X2)  *)
(*             (isconn_X2 : forall (x : X2), merely (b = x)). *)
(*     Context (Y : 1-Type) *)
(*             (y0 : Y) *)
(*             (fl : a = a -> y0 = y0) *)
(*             (ishom_fl : forall (α ω : a = a), *)
(*                 fl (α @ ω) = fl α @ fl ω) *)
(*             (fr : b = b -> y0 = y0) *)
(*             (ishom_fr : forall (α ω : b = b), *)
(*                 fr (α @ ω) = fr α @ fr ω) *)
(*             (natl_flr : forall (α : a = a) (ω : b = b), *)
(*                 fl α @ fr ω = fr ω @ fl α). *)
    
(*     Definition deloop_double_rec : X1 -> X2 -> Y. *)
(*     Proof. *)
(*       srefine (deloop_rec X1 a isconn_X1 _ _ _ _). *)
(*       - simpl. *)
(*         exact (deloop_rec X2 b isconn_X2 Y y0 fr ishom_fr). *)
(*       - intro α. apply path_arrow. intro x2. revert x2. *)
(*         srefine (deloop_ind_set X2 b isconn_X2 _ _ _ ). *)
(*         + simpl. *)
(*           refine *)
(*             (deloop_rec_beta_x0 X2 b isconn_X2 Y y0 fr ishom_fr @ _ @ *)
(*                                 (deloop_rec_beta_x0 _ _ _ _ _ _ _ )^). *)
(*           exact (fl α). *)
(*         + intro. simpl.  *)
(*           refine (transport_paths_FlFr  _ _ @ _). *)
(*           rewrite *)
(*             (moveL_Mp _ _ _ (moveL_pV _ _ _ (deloop_rec_beta_loop X2 b isconn_X2 Y y0 fr ishom_fr ω))). *)
(*           generalize ((deloop_rec_beta_x0 X2 b isconn_X2 Y y0 fr ishom_fr)). *)
(*           intro p. *)
(*           rewrite inv_pp. rewrite inv_pp. rewrite inv_V. *)
(*           repeat rewrite concat_p_pp. *)
(*           apply whiskerR. apply moveR_pM. *)
(*           repeat rewrite concat_pp_p. apply whiskerL. *)
(*           apply moveR_Vp. *)
(*           rewrite concat_Vp. rewrite concat_p1. *)
(*           rewrite concat_V_pp. *)
(*           rewrite concat_p_pp. apply moveL_pV. apply natl_flr. *)
(*       - simpl. intros. *)
(*         apply (ap (path_arrow (deloop_rec X2 b isconn_X2 Y y0 fr ishom_fr) (deloop_rec X2 b isconn_X2 Y y0 fr ishom_fr))). *)
(*         apply (istrunc_trunctype_type Y). *)
          
(*           generalize *)
(*             ((deloop_rec_beta_x0 X2 b isconn_X2 Y y0 fr ishom_fr @ fl α) *)
(*                @ (deloop_rec_beta_x0 X2 b isconn_X2 Y y0 fr ishom_fr)^). *)
(*           generalize (ap (deloop_rec X2 b isconn_X2 Y y0 fr ishom_fr) ω ). *)
(*           repeat rewrite concat_p_pp. *)
(*           destruct ((ap (deloop_rec X2 b isconn_X2 Y y0 fr ishom_fr) ω)). *)

(*       intros x1. *)
      


(*           (y0 : Y) *)
(*           (f : (x0 = x0) -> (y0 = y0)) *)
(*           (ishom_f : forall (α ω : x0 = x0), *)
(*               f (α @ ω) = f α @ f ω). *)

(* End deloop_double_rec. *)


Section deloop_double_ind_set.
  Context (X1 : Conn_pType).
  Context (X2 : Conn_pType).

  Context (Y : X1 -> X2 -> 0-Type)
          (y0 : Y (point X1) (point X2))
          (fr : forall (ω : (point X2) = (point X2)), transport (Y (point X1)) ω y0 = y0)
          (fl : forall (ω : (point X1) = (point X1)), transport (fun x1 => Y x1 (point X2)) ω y0 = y0).
  
  Definition deloop_double_ind_set : forall (x1 : X1) (x2 : X2), Y x1 x2.
  Proof.
    intros x1.
    simple refine (deloop_ind_set X2 (fun x2 => Y x1 x2) _ _).
    - exact (deloop_ind_set X1 (fun x1 => Y x1 (point X2)) y0 fl x1).
    - simpl. intro.
      revert x1.
      apply (deloop_ind_prop X1). simpl.
      refine (_ @ fr ω @ _).
      + apply (ap (transport (fun x : X2 => Y (point X1) x) ω)).
        unfold deloop_ind_set.
        exact (deloop_ind_beta_pt X1
                   (fun x : X1 => Y x (point X2)) y0 _ _ ) .
      + apply inverse.
        unfold deloop_ind_set.
        exact (deloop_ind_beta_pt X1
                   (fun x : X1 => Y x (point X2)) y0 _ _).
  Defined.

  Definition deloop_double_ind_set_beta_pt :
    deloop_double_ind_set (point X1) (point X2) = y0.
  Proof.
    unfold deloop_double_ind_set. unfold deloop_ind_set.
    refine (deloop_ind_beta_pt X2 _ _ _ _ @ _).
    apply (deloop_ind_beta_pt X1 (fun x : X1 => Y x (point X2))).
  Defined.    
    
End deloop_double_ind_set.

Section deloop_double_ind_set'.
  Context (X1 : Conn_pType).
  Context (X2 : Conn_pType).

  Context (Y : X1 -> X2 -> 0-Type)
          (y0 : Y (point X1) (point X2))
          (fl_fr : forall (ω1 : (point X1) = (point X1)) (ω2 : (point X2) = (point X2)),
              transport (uncurry Y) (path_prod (_,_) (_,_) ω1 ω2) y0 = y0).

  
  Definition deloop_double_ind_set' : forall (x1 : X1) (x2 : X2), Y x1 x2.
  Proof.
    intros x1 x2.
    simple refine (deloop_ind_set (conn_ptype_prod X1 X2) (uncurry Y) y0 _ (x1, x2)).
    unfold point. simpl.
    apply (equiv_functor_forall_pb (equiv_path_prod (point X1, point X2) (point X1, point X2))).
    intros [ω1 ω2]. simpl in ω1, ω2.
    apply fl_fr.
  Defined.

  Definition deloop_double_ind_set_beta_pt' :
    deloop_double_ind_set' (point X1) (point X2) = y0.
  Proof.
    unfold deloop_double_ind_set'. unfold deloop_ind_set. simpl.
    change (point X1, point X2) with (point (conn_ptype_prod X1 X2)).
    apply (deloop_ind_beta_pt (conn_ptype_prod X1 X2) (uncurry Y) y0).
  Defined.

End deloop_double_ind_set'.
  

    
(* todo: replace transport with pathover above, and write out deloop_double_ind *)
(* this should replace the two above *)
(* Section deloop_double_ind. *)
  