Require Import HoTT.
Require Import UnivalenceAxiom.

From A_BPQ Require Import finite_types.

Section Fin_Transpose.
  (** Defining transpositions. [fin_transpose x y] is the permutation that swaps x and y  *)
  Definition fin_transpose {n : nat} (x y : fintype n)
  : fintype n <~> fintype n.
  Proof.
    induction n.
    - destruct x.
    - destruct y as [y | []].
      + destruct x as [x | []].
        * exact (IHn x y +E 1).
        * exact (fin_transpose_last_with n (inl y)).
      + exact (fin_transpose_last_with n x).
  Defined.

  Definition fin_transpose_same_is_id {n : nat} (x : fintype n) :
    fin_transpose x x == idmap.
  Proof.
    intro i.
    induction n.
    { destruct x. }
    destruct x as [x | []].
    - simpl. destruct i as [i | []].
      + apply (ap inl). apply IHn.
      + reflexivity.
    - simpl. apply fin_transpose_last_with_last_other.
  Defined.

  Definition fin_transpose_invol {n : nat} (x y : fintype n) :
    fin_transpose x y o fin_transpose x y == idmap.
  Proof.
    induction n.
    {destruct x. }
    intro i. ev_equiv.
    destruct y as [y | []].
    - destruct x as [x | []].
      + simpl. destruct i as [i | []].
        { simpl. apply (ap inl). apply IHn. }
        reflexivity.
      + simpl. apply fin_transpose_last_with_invol.
    - simpl. apply fin_transpose_last_with_invol.
  Defined.

  Definition fin_transpose_sym {n : nat} (x y : fintype n) :
    fin_transpose x y == fin_transpose y x.
  Proof.
    induction n.
    { destruct x. }
    intro i.
    destruct y as [y | []]; destruct x as [x | []]; try reflexivity.
    - simpl. destruct i as [i | []].
      + apply (ap inl). apply IHn.
      + reflexivity.
  Defined.

  Definition fin_transpose_beta_r {n : nat} (x y : fintype n) :
    fin_transpose x y y = x.
  Proof.
    induction n.
    { destruct x. }
    destruct y as [y | []]; destruct x as [x | []]; try (apply fin_transpose_last_with_last).
    - simpl. apply (ap inl). apply IHn.
    - simpl. apply fin_transpose_last_with_with.
  Defined.

  Definition fin_transpose_beta_l {n : nat} (x y : fintype n) :
    fin_transpose x y x = y.
  Proof.
    refine (fin_transpose_sym x y x @ _).
    apply fin_transpose_beta_r.
  Defined.

  Definition fin_transpose_other {n : nat} (x y : fintype n) (i : fintype n):
    (i <> x) -> (i <> y) -> fin_transpose x y i = i.
  Proof.
    intros n_x n_y.
    induction n.
    { destruct x.  }
    destruct y as [y | []].
    - destruct x as [x | []].
      + simpl. destruct i as [i | []].
        * apply (ap inl). apply IHn.
          { intro p. apply n_x. exact (ap inl p). }
          { intro p. apply n_y. exact (ap inl p). }
        * reflexivity.
      + simpl. destruct i as [i | []].
        * apply fin_transpose_last_with_rest.
          intro p. apply n_y. exact p^.
        * destruct (n_x idpath).
    - simpl. destruct i as [i | []].
      + apply fin_transpose_last_with_rest.
        intro p. apply n_x. exact p^.
      + destruct (n_y idpath).
  Defined.

  (** either i = x, i = y, or equal to neither *)
  Definition decompose_fin_n {n : nat} (x y : fintype n) (i : fintype n) :
    (i = x) + (i = y) + ((i <> x) * (i <> y)).
  Proof.
    destruct (decidablepaths_fin n i x).
    - exact (inl (inl p)).
    - destruct (decidablepaths_fin n i y).
      + apply inl. exact (inr p).
      + apply inr. exact (n0, n1).
  Qed.    

  Definition natural_fin_transpose {n : nat} (x y : fintype n) (e : fintype n <~> fintype n) :
    e o (fin_transpose x y) == fin_transpose (e x) (e y) o e.
  Proof.
    intro i. ev_equiv.
    destruct (decompose_fin_n x y i) as [[p | p] |[n_x n_y] ].
    - rewrite p.
      rewrite fin_transpose_beta_l.
      apply inverse. apply fin_transpose_beta_l.
    - rewrite p.
      rewrite fin_transpose_beta_r.
      apply inverse. apply fin_transpose_beta_r.
    - rewrite (fin_transpose_other x y i n_x n_y).
      apply inverse. apply fin_transpose_other.
      + intro p. apply n_x. apply (equiv_inj e p).
      + intro p. apply n_y. apply (equiv_inj e p).
  Qed.

  Definition fin_transpose_eta {n : nat} (x y : fintype n) (e : fintype n -> fintype n) :
    (e x = y) -> (e y = x) -> (forall i : fintype n, i <> x -> i <> y -> e i = i) ->
    fin_transpose x y == e.
  Proof.
    intros p q neq.
    intro i.
    destruct (decidablepaths_fin n i x) as [eq_x | neq_x].
    - rewrite eq_x.
      rewrite p.
      apply fin_transpose_beta_l.
    - destruct (decidablepaths_fin n i y) as [eq_y | neq_y].
      + rewrite eq_y.  rewrite q.
        apply fin_transpose_beta_r.
      + rewrite (neq i neq_x neq_y).
        apply (fin_transpose_other _ _ _ neq_x neq_y).
  Qed.
  
End Fin_Transpose.

Section Sym2.
  (** The permutations of two letters is the group of two elements.  *)
  Definition sym2_fixlast (σ : fintype 2 <~> fintype 2) :
    (σ (inr tt) = inr tt) -> σ == equiv_idmap.
  Proof.
    intro p.
    intros [[[] | []] | []]; simpl.
    - recall (σ ((inl (inr tt)))) as x eqn:q.
      rewrite q.
      destruct x as [[[] | []] | []].
      + reflexivity.
      + destruct (inr_ne_inl tt (inr tt) (equiv_inj σ (p @ q^))). (* absurd case *)
    - exact p.
  Qed.

  Definition twist2 : fintype 2 <~> fintype 2 :=
    fin_transpose (n := 2) (inl (inr tt)) (inr tt).

  Definition twist2_inv : equiv_inverse twist2 = twist2.
  Proof.
    apply path_equiv. reflexivity.
  Qed.

  Definition sym2_notfixlast (σ : fintype 2 <~> fintype 2) :
    (σ (inr tt) = inl (inr tt)) -> σ == twist2.
  Proof.
    intro p.
    intros [[[] | []] | []]; simpl.
    - recall (σ ((inl (inr tt)))) as x eqn:q.
      rewrite q.
      destruct x as [[[] | []] | []].
      + destruct (inr_ne_inl tt (inr tt) (equiv_inj σ (p @ q^))). (* absurd case *)
      + reflexivity.
    - exact p.
  Qed.

  Definition symm_sym2 (σ1 σ2 : fintype 2 <~> fintype 2) :
    σ1 oE σ2 = σ2 oE σ1.
  Proof.
    recall (σ1 (inr tt)) as x eqn:p.
    destruct x as [[[] | []] | []].
    - rewrite (path_equiv (path_forall _ _ (sym2_notfixlast σ1 p))).
      recall (σ2 (inr tt)) as y eqn:q.
      destruct y as [[[] | []] | []].
      + rewrite (path_equiv (path_forall _ _ (sym2_notfixlast σ2 q))).
        reflexivity.
      + rewrite (path_equiv (path_forall _ _ (sym2_fixlast σ2 q))).
        rewrite ecompose_e1. rewrite ecompose_1e. reflexivity.
    - rewrite (path_equiv (path_forall _ _ (sym2_fixlast σ1 p))).
      rewrite ecompose_e1. rewrite ecompose_1e. reflexivity.
  Qed.

  Definition SymGrp2_cases (sigma : fintype 2 <~> fintype 2)
    : (sigma = equiv_idmap) + (sigma = twist2).
  Proof.
    recall (sigma (inr tt)) as x eqn:p.
    destruct x as [[[] | []] | []].
    - apply inr.
      apply path_equiv. apply path_arrow. apply sym2_notfixlast. exact p.
    - apply inl.
      apply path_equiv. apply path_arrow. apply sym2_fixlast. exact p.
  Defined.

  Lemma invol_SymGrp2 (sigma : fintype 2 <~> fintype 2)
    : (sigma oE sigma) = equiv_idmap.
  Proof.
    destruct (SymGrp2_cases sigma) as [p | p].
    - refine (ap011 equiv_compose' p p @ _).
      apply path_equiv. reflexivity.
    - refine (ap011 equiv_compose' p p @ _).
      apply path_equiv. apply path_arrow.
      intros [[[] | []] | []]; reflexivity.
  Qed.
End Sym2.

Section Restrict_Equivalence.
  (** Given an equivalence [A + Unit <~> B + Unit] fixing Unit, we may restrict it to an equivalence [A <~> B]  *)
  Context {n : nat}
          {A : Type}
          (e : A + Unit <~> fintype n.+1)
          (fixlast : e (inr tt) = inr tt).

  Lemma not_inr_is_inl {X Y : Type}
        (x :  X + Y)
        (not_inr : forall y : Y, x <> inr y)
    : is_inl x.
  Proof.
    destruct x as [x | y'].
    - exact tt.
    - destruct (not_inr y' idpath).
  Qed.
  
  Lemma fix_last_is_inr :
    forall u : Unit, is_inr (e (inr u)).
  Proof.
    intros []. rewrite fixlast.
    exact tt.
  Qed.

  Lemma fix_last_is_inl :
    forall a : A, is_inl (e (inl a)).
  Proof.
    intro a. apply not_inr_is_inl.
    intros []. rewrite <- fixlast.
    intro q. apply (inl_ne_inr a tt).
    exact (equiv_inj e q).
  Qed.

  Definition equiv_restrict :=
    equiv_unfunctor_sum_l e fix_last_is_inl fix_last_is_inr.

  Definition swap_last := fin_transpose (e (inr tt)) (inr tt).

  Lemma swap_fix_last :
    (swap_last oE e) (inr tt) = inr tt.
  Proof.
    unfold swap_last. ev_equiv. apply fin_transpose_last_with_with.
  Qed.

  
  Definition equiv_restrict_eta :
    equiv_restrict +E equiv_idmap == e.
  Proof.
    intro x.
    refine (_ @ unfunctor_sum_eta _ fix_last_is_inl fix_last_is_inr x).
    destruct x as [x | []]; try reflexivity.   
    simpl.
    destruct (unfunctor_sum_r e fix_last_is_inr tt).
    reflexivity.
  Qed.      
End Restrict_Equivalence.

Definition equiv_restrict_plus1 {n : nat} {A : Type} (e : A <~> fintype n) :
  equiv_restrict (e +E equiv_idmap) idpath == e.
Proof.
  intro a.
  apply (path_sum_inl Unit).
  refine (unfunctor_sum_l_beta _ _ a ).
Qed.


Definition inj_equiv_plus1 {n : nat} {A : Type} (e1 e2 : A <~> fintype n) :
  (e1 +E (equiv_idmap Unit)) == (e2 +E (equiv_idmap Unit)) -> e1 == e2.
Proof.
  intro H.
  intro x.
  apply (path_sum_inl Unit). apply (H (inl x)).
Qed.

Definition fin_decompose_ind {m n : nat} (P : fintype (n+m) -> Type)
           (Pl : forall i : fintype m, P (finl _ _ i))
           (Pr : forall i : fintype n, P (finr _ _ i))
  : forall i : fintype (n+m), P i.
Proof.
  cut (forall j : (fintype m)+(fintype n), P (finsum m n j)).
  - intro f.
    intro i.
    apply (transport P (eisretr (finsum m n) i)).
    exact (f ((finsum m n)^-1 i)).
  - intros [j | j].
    + exact (Pl j).
    + exact (Pr j).
Defined.

Section Transpose_and_restrict.
  (** Given a permutation [fintype n.+1 <~> fintype n.+1], we compose it with a transposition so that it fixes [n+1] and restricts it to a permutation [fintype n <~> fintype n]  *)
  
  Definition transpose_and_restrict {n n': nat} (e : fintype n.+1 <~> fintype n'.+1)  :
    fintype n <~> fintype n' :=
    (equiv_restrict (swap_last e oE e) (swap_fix_last e)).

  Definition transpose_and_restrict_eta {n n': nat} (e : fintype n.+1 <~> fintype n'.+1) :
    (transpose_and_restrict e) +E 1 == (swap_last e) oE e.
  Proof.
    apply equiv_restrict_eta.
  Defined.

  (** A reformulation: *)
  Definition factorize_permutation {a a': nat} (alpha : fintype a.+1 <~> fintype a'.+1)
    : alpha = swap_last alpha oE (transpose_and_restrict alpha +E 1).
  Proof.
    apply emoveL_Me.
    refine (_ @ (path_equiv (path_arrow _ _ (transpose_and_restrict_eta alpha)))^).
    apply (ap (fun e => e oE alpha)).
    unfold swap_last.
    refine ((ecompose_e1 _)^ @ _).
    apply emoveR_Ve. apply inverse.
    apply path_equiv. apply path_arrow. apply fin_transpose_invol.
  Defined.

  Definition transpose_and_restrict_id {n : nat} :
    @transpose_and_restrict n n equiv_idmap == equiv_idmap.
  Proof.
    intro x. simpl.
    destruct n; reflexivity.
  Qed.

  Definition transpose_and_restrict_transpose_nfx {n : nat} (x : fintype n.+1) :
    transpose_and_restrict (fin_transpose x (inr tt)) == equiv_idmap.
  Proof.
    apply (inj_equiv_plus1 ).
    intro i.
    refine (transpose_and_restrict_eta _ i @ _).
    unfold swap_last.
    ev_equiv.
    assert (h : (1 +E 1) i = i). { destruct i as [i | []]; reflexivity. }
    rewrite h. clear h.
    rewrite fin_transpose_beta_r.
    apply (fin_transpose_invol x (inr tt)).
  Qed.

  Definition transpose_and_restrict_transpose_fixlast {n : nat} (x y : fintype n) :
    transpose_and_restrict (fin_transpose (n := n.+1) (inl x) (inl y)) == fin_transpose x y.
  Proof.
    apply (inj_equiv_plus1 ).
    intro i.
    refine (transpose_and_restrict_eta _ i @ _).
    unfold swap_last.
    ev_equiv.
    assert (h : fin_transpose (n := n.+1) (inl x) (inl y) (inr tt) = inr tt).
    { apply fin_transpose_other; apply inr_ne_inl. }
    rewrite h. clear h.
    refine (fin_transpose_same_is_id (n := n.+1) (inr tt) _ @ _).
    destruct i as [i | []]; reflexivity.
  Qed.
End Transpose_and_restrict.

Section Block_Sum.
  (* First a more general definition *)
  Definition fin_equiv_sum {a b c d : nat} (e : (fintype a + fintype b) <~> (fintype c + fintype d))
    : fintype (b + a) <~> fintype (d + c) :=
    (equiv_finsum c d) oE e oE (equiv_inverse (equiv_finsum a b)).

  Definition fin_equiv_sum_compose {a b c d e f : nat}
             (e1 : (fintype a + fintype b) <~> (fintype c + fintype d))
             (e2 : (fintype c + fintype d) <~> (fintype e + fintype f))
    : fin_equiv_sum (e2 oE e1) =
      fin_equiv_sum e2 oE fin_equiv_sum e1.
  Proof.
    unfold fin_equiv_sum.
    apply path_equiv. apply path_arrow. intro x.
    ev_equiv.
    rewrite (eissect (equiv_finsum c d)).
    reflexivity.
  Defined.

  Definition block_sum {a a' b b' : nat}
             (alpha : fintype a <~> fintype a') (betta : fintype b <~> fintype b')
    : fintype (a +' b)%nat <~> fintype (a' +' b')
    := fin_equiv_sum (alpha +E betta).
             

  (* Definition block_sum {m n: nat} (e1 : fintype m <~> fintype m) (e2 : fintype n <~> fintype n) : *)
  (*   fintype (n+m)%nat <~> fintype (n+m)%nat := *)
  (*   fin_equiv_sum (e1 +E e2). *)

  Definition block_sum_beta_finl {m m' n n': nat}
             (e1 : fintype m <~> fintype m') (e2 : fintype n <~> fintype n')
             (i : fintype m) :
    block_sum e1 e2 (finl _ _ i) = finl _ _ (e1 i).
  Proof.
    unfold block_sum. unfold fin_equiv_sum. ev_equiv.
    rewrite (eissect (equiv_finsum m n) (inl i)). reflexivity.
  Qed.

  Definition block_sum_beta_finr {m m' n n' : nat}
             (e1 : fintype m <~> fintype m') (e2 : fintype n <~> fintype n')
             (i : fintype n) :
    block_sum e1 e2 (finr _ _ i) = finr _ _ (e2 i).
  Proof.
    unfold block_sum. unfold fin_equiv_sum. ev_equiv.
    rewrite (eissect (equiv_finsum m n) (inr i)). reflexivity.
  Qed.

  Definition block_sum_eta {m m' n n' : nat} 
             (e1 : fintype m <~> fintype m') (e2 : fintype n <~> fintype n')
             (g : fintype (n + m) <~> fintype (n' + m'))
             (eq_l : forall i : fintype m,
                 finl _ _(e1 i)
                 = g (finl _ _ i))
             (eq_r : forall i : fintype n,
                 (finr _ _ (e2 i)
                  = g (finr _ _ i)))
    : block_sum e1 e2 == g .
  Proof.
    unfold block_sum. unfold fin_equiv_sum. intro j. revert j.
    apply fin_decompose_ind.
    - intro i. ev_equiv. rewrite (eissect (equiv_finsum m n) (inl i)).
      apply eq_l.
    - intro i.  ev_equiv. rewrite (eissect (equiv_finsum m n) (inr i)).
      apply eq_r.
  Qed.

  Definition block_sum_compose {m m' m'' n n' n'': nat}
             (e1 : fintype m' <~> fintype m'')
             (g1 : fintype m <~> fintype m')
             (e2 : fintype n' <~> fintype n'')
             (g2 : fintype n <~> fintype n') :
    block_sum (e1 oE g1) (e2 oE g2) =
    (block_sum e1 e2) oE (block_sum g1 g2).
  Proof.
    refine (_ @ fin_equiv_sum_compose _ _).
    apply (ap fin_equiv_sum).
    apply path_equiv. apply path_arrow.
    intros [x | x]; reflexivity.
  Defined.
    

  Definition block_sum_compose' {m m' m'' n n' n'': nat}
             (e1 : fintype m' <~> fintype m'')
             (g1 : fintype m <~> fintype m')
             (e2 : fintype n' <~> fintype n'')
             (g2 : fintype n <~> fintype n') :
    block_sum (e1 oE g1) (e2 oE g2) ==
    (block_sum e1 e2) oE (block_sum g1 g2).
  Proof.
    apply block_sum_eta.
    - intro i. ev_equiv.
      rewrite block_sum_beta_finl.
      rewrite block_sum_beta_finl.
      reflexivity.
    - intro i. ev_equiv.
      rewrite block_sum_beta_finr.
      rewrite block_sum_beta_finr.
      reflexivity.
  Qed.

  Definition block_sum_plus1 {m m' n n' : nat}
             (e1 : fintype m <~> fintype m')
             (e2 : fintype n <~> fintype n') :
    block_sum (b := n.+1) (b' := n'.+1) e1 (e2 +E (equiv_idmap Unit))
    == (block_sum e1 e2) +E (equiv_idmap Unit).
  Proof.    
    apply block_sum_eta.
    - intro i. simpl. 
      apply (ap inl).
      change (finsum_inv m n) with (equiv_finsum m n)^-1.
      rewrite (eissect (finsum m n) (inl i)). reflexivity.
    - simpl. intros [i | []].
      + simpl.
        change (finsum_inv m n) with (equiv_finsum m n)^-1.
        rewrite (eissect (finsum m n) (inr i)). reflexivity.
      + reflexivity.
  Qed.

  (* should be moved. . . *)
  Definition functor_not {A B : Type} :
    (B -> A) -> (not A) -> (not B).
  Proof.
    intro f. intros n false. apply n. exact (f false).
  Qed.

  Definition blocksum_transpose {m n : nat}
             (x y : fintype n) :
    fin_transpose (finr _ _ x) (finr _ _ y) ==
    @block_sum m m n n equiv_idmap (fin_transpose x y).    
  Proof.
    apply fin_transpose_eta.
    - rewrite block_sum_beta_finr.
      rewrite fin_transpose_beta_l.  reflexivity.
    - rewrite block_sum_beta_finr.
      rewrite fin_transpose_beta_r. reflexivity.
    - apply (fin_decompose_ind
               (fun i : fintype (n+m) =>
               i <> finr m n x -> i <> finr m n y ->
               (block_sum equiv_idmap (fin_transpose x y)) i = i)).
      + intros i neqx neqy.
        apply block_sum_beta_finl.
      + intros i neqx neqy.
        refine (block_sum_beta_finr _ _ _ @ _).
        apply (ap (finr m n)).  apply (fin_transpose_other x y i).
        { apply (functor_not (ap (finr m n)) neqx). }
        { apply (functor_not (ap (finr m n)) neqy). }
  Qed.
  
  Definition swap_last_blocksum {m m' n n' : nat}
             (e1 : fintype m <~> fintype m')
             (e2 : fintype n.+1 <~> fintype n'.+1) :
    swap_last (block_sum e1 e2) ==
    block_sum equiv_idmap (swap_last e2) .
  Proof.
    unfold swap_last.
    rewrite (block_sum_beta_finr (n := n.+1) e1 e2 (inr tt)).
    apply (@blocksum_transpose m' n'.+1 (e2 (inr tt)) ((inr (fintype n') tt))).
  Qed.

  
  Definition transpose_and_restrict_block_sum {m m' n n' : nat}
             (e1 : fintype m <~> fintype m')
             (e2 : fintype n.+1 <~> fintype n'.+1) :
    transpose_and_restrict (block_sum e1 e2) == block_sum e1 (transpose_and_restrict e2).
  Proof.
    apply inj_equiv_plus1.
    intro x.
    refine (equiv_restrict_eta _ _ _ @ _).
    refine (swap_last_blocksum e1 e2 _ @ _).
    refine ((block_sum_compose' equiv_idmap e1 (swap_last e2) e2 x)^ @ _).
    rewrite (ecompose_1e).
    refine (_ @ (block_sum_plus1 _ _ x)).
    apply (ap (fun g => ((block_sum (b:=n.+1) e1 g) x))).
    apply path_equiv. apply path_arrow.
    intro y.
    apply inverse.
    apply transpose_and_restrict_eta.
  Defined.    
  
End Block_Sum.

Require Import monoids_and_groups.

Definition SymGrp (m : nat) := AutGroup (fintype m).

Section Block_Sum_Hom.
  (** Block sum as a homomorphism *)
  Definition block_sum_hom (m n : nat):
    Homomorphism (grp_prod (SymGrp m) (SymGrp n)) (SymGrp (n+m)).
  Proof.
    srapply @Build_Homomorphism.
    - intros [s t].
      exact (block_sum s t).
    - simpl. apply path_equiv. apply path_arrow.
      apply block_sum_eta; reflexivity.
    - simpl. intros [s1 s2] [t1 t2].
      (* apply path_equiv. apply path_arrow. *)
      apply block_sum_compose.
  Defined.
End Block_Sum_Hom.
