Require Import MatrixExampleBase.
Require Import MatrixPermBase.
From ViCaR Require Import ExamplesAutomation.

#[export] Instance MxCategory : Category nat := {
  morphism := Matrix;

  equiv := @mat_equiv;  (* fun m n => @eq (Matrix m n); *)
  equiv_rel := @mat_equiv_equivalence;

  compose := @Mmult;
  compose_compat := fun n m o f g Hfg h i Hhi =>
    @Mmult_simplify_mat_equiv n m o f g h i Hfg Hhi;
  assoc := @Mmult_assoc_mat_equiv;

  c_identity n := I n;
  left_unit := Mmult_1_l_mat_eq;
  right_unit := Mmult_1_r_mat_eq;
}.

Lemma direct_sum'_id_mat_equiv : forall n m, 
  direct_sum' (I n) (I m) ≡ I (n + m).
Proof.
  intros n m.
  intros i j Hi Hj.
  unfold direct_sum', I.
  bdestructΩ'simp.
Qed.

Lemma direct_sum'_id : forall n m, 
  direct_sum' (I n) (I m) = I (n + m).
Proof.
  intros n m.
  rewrite <- mat_equiv_eq_iff by auto with wf_db.
  apply direct_sum'_id_mat_equiv.
Qed.

Lemma big_sum_split : forall {G : Type} {H : Monoid G} (n k : nat) (f : nat -> G),
  big_sum f (n + k) =
  (big_sum f n + big_sum (fun x : nat => f (n + x)%nat) k)%G.
Proof.
  intros G H n.
  induction k; intros f.
  - simpl; rewrite Nat.add_0_r, Gplus_0_r; easy.
  - rewrite Nat.add_succ_r, <- big_sum_extend_r, IHk, <- Gplus_assoc.
    reflexivity.
Qed.

Lemma direct_sum'_Mmult : forall {n m o p q r}
  (A : Matrix n m) (B : Matrix m o) (C : Matrix p q) (D : Matrix q r),
  direct_sum' (A × B) (C × D) ≡ direct_sum' A C × direct_sum' B D.
Proof.
  intros n m o p q r A B C D.
  intros i j Hi Hj.
  symmetry.
  unfold direct_sum', Mmult.
  bdestruct (i <? n);
  bdestruct (j <? o); simpl; 
  [ | | | bdestruct (i <? n + p);
  bdestruct (j <? o + r); simpl];
  try (
    rewrite big_sum_0_bounded; [easy|];
    intros k Hk;
    bdestructΩ'simp
  ).
  - rewrite big_sum_split.
    rewrite (big_sum_0 _ q) by (intros k; bdestruct (m + k <? m); [lia | lca]).
    rewrite Gplus_0_r.
    apply big_sum_eq_bounded.
    intros k Hk.
    bdestructΩ'simp.
  - rewrite big_sum_split.
    rewrite (big_sum_0_bounded _ m) 
      by (intros k Hk; bdestruct (k <? m); [lca | lia]).
    rewrite Gplus_0_l.
    apply big_sum_eq_bounded.
    intros k Hk.
    bdestructΩ'.
    do 2 f_equal; lia.
Qed.

Lemma direct_sum'_assoc : forall {n m o p q r}
  (A : Matrix n m) (B : Matrix o p) (C : Matrix q r),
  direct_sum' A (direct_sum' B C) ≡ direct_sum' (direct_sum' A B) C.
Proof.
  intros n m o p q r A B C i j Hi Hj.
  unfold direct_sum'.
  repeat (bdestruct_one; simpl; subst; try easy; try lia).
  f_equal; lia.
Qed.

Lemma direct_sum'_0_l : forall {n m} (A : Matrix n m) (appendix : Matrix 0 0),
  direct_sum' appendix A ≡ A.
Proof.
  intros n m A app i j Hi Hj.
  unfold direct_sum'.
  rewrite 2!(Nat.sub_0_r).
  bdestructΩ'simp.
Qed.

Lemma direct_sum'_0_r : forall {n m} (A : Matrix n m) (appendix : Matrix 0 0),
  direct_sum' A appendix ≡ A.
Proof.
  intros n m A app i j Hi Hj.
  unfold direct_sum'.
  bdestructΩ'simp.
Qed.

Definition MxDirectSumBiFunctor : Bifunctor MxCategory MxCategory MxCategory := {|
  obj2_map := Nat.add;
  morphism2_map := @direct_sum';
  id2_map := direct_sum'_id_mat_equiv;
  compose2_map := @direct_sum'_Mmult;
  morphism2_compat := @direct_sum'_simplify_mat_equiv;
|}.

#[export] Instance MxDirectSumMonoidalCategory : MonoidalCategory nat := {
  tensor := MxDirectSumBiFunctor;
  I := O;
  
  associator := fun n m o => {|
  forward := (I (n + m + o) : Matrix (n + m + o) (n + (m +o)));
  reverse := (I (n + m + o) : Matrix (n + (m +o)) (n + m + o));
  id_A := ltac:(simpl; rewrite Nat.add_assoc, Mmult_1_r_mat_eq; easy);
  id_B := ltac:(simpl; rewrite Nat.add_assoc, Mmult_1_r_mat_eq; easy);
  |};

  left_unitor := fun n => {|
  forward := (I n : Matrix (0 + n) n);
  reverse := (I n : Matrix n (0 + n));
  id_A := ltac:(simpl; rewrite Mmult_1_r_mat_eq; easy);
  id_B := ltac:(simpl; rewrite Mmult_1_r_mat_eq; easy);
  |};

  right_unitor := fun n => {|
  forward := (I n : Matrix (n + 0) n);
  reverse := (I n : Matrix n (n + 0));
  id_A := ltac:(rewrite Nat.add_0_r, Mmult_1_r_mat_eq; easy);
  id_B := ltac:(rewrite Nat.add_0_r, Mmult_1_r_mat_eq; easy);
  |};

  associator_cohere := ltac:(intros; simpl in *; 
    rewrite 2!Nat.add_assoc, Mmult_1_l_mat_eq, 
      Mmult_1_r_mat_eq, <-2!Nat.add_assoc; rewrite (direct_sum'_assoc f g h); easy);
  left_unitor_cohere := ltac:(intros; simpl;
    rewrite direct_sum'_0_l, Mmult_1_l_mat_eq, Mmult_1_r_mat_eq; easy);
  right_unitor_cohere := ltac:(intros; simpl; rewrite direct_sum'_0_r; 
    rewrite 2!Nat.add_0_r, Mmult_1_r_mat_eq, Mmult_1_l_mat_eq; easy);

    pentagon := ltac:(intros; simpl in *; restore_dims;
    rewrite 4!Nat.add_assoc, Mmult_1_r_mat_eq, 
      2!direct_sum'_id, 2!Mmult_1_l_mat_eq, 2!Nat.add_assoc; easy); 
    triangle :=  ltac:(intros; simpl in *; 
    rewrite Nat.add_0_r, direct_sum'_id, Mmult_1_r_mat_eq; easy);
}.




Notation mx_braiding := (fun n m => (perm_mat (n+m) (rotr (n+m) n) : Matrix (n+m) (m+n))%nat).

Lemma mx_braiding_compose_inv : forall n m,
  (mx_braiding n m) × (mx_braiding m n) ≡ I (n + m).
Proof.
  intros n m.
  simpl.
  rewrite (Nat.add_comm m n).
  rewrite perm_mat_Mmult by auto with perm_db.
  cleanup_perm.
  rewrite perm_mat_I by easy.
  easy.
Qed.





Lemma mx_braiding_braids_eq : forall n m o p (A : Matrix n m) (B : Matrix o p),
  (direct_sum' A B × perm_mat (m + p) (rotr (m + p) m)
  = perm_mat (n + o) (rotr (n + o) n) × direct_sum' B A).
Proof.
  intros n m o p A B.
  apply equal_on_basis_vectors_implies_equal; 
    [|rewrite Nat.add_comm, (Nat.add_comm m p) |]; auto with wf_db.
  intros k Hk.
  rewrite <- mat_equiv_eq_iff; 
    [| | apply WF_mult; [apply WF_mult|]]; auto with wf_db;
    [|rewrite (Nat.add_comm m p), (Nat.add_comm n o); auto with wf_db].
  rewrite Mmult_assoc.
  rewrite perm_mat_permutes_basis_vectors_r, basis_vector_eq_e_i by easy.
  rewrite <- (matrix_by_basis _ _ Hk).
  rewrite <- matrix_by_basis.
  2: { (* TODO: replace with 'apply permutation_is_bounded; auto with perm_db' *)
    assert (Hp: (permutation (m+p) (rotr (m + p) m))%nat) by auto with perm_db. 
    destruct Hp as [finv Hfinv].
    destruct (Hfinv k Hk); easy.
  }
  intros x y Hx Hy; replace y with O by lia; clear y Hy.
  unfold get_vec.
  rewrite Nat.eqb_refl.
  rewrite perm_mat_permutes_matrix_r by auto with perm_db.
  rewrite perm_inv_of_rotr by easy.
  rewrite rotl_eq_rotr_sub.
  bdestruct (o =? 0);
  [subst o; 
  rewrite Nat.add_0_r, Nat.mod_same, Nat.sub_0_r, rotr_n by lia|
  rewrite Nat.mod_small by lia;
  replace (n + o - n)%nat with o by lia];
  unfold direct_sum', rotr, rotl; simpl;
  rewrite 1?Nat.add_0_r;

  [ replace_bool_lia (x <? n) true |
    replace_bool_lia (x <? n + o) true];
  replace_bool_lia (k <? p + m) true;
  rewrite 2?andb_true_r; simpl;
  [|replace_bool_lia (n + o <=? x) false];
  replace_bool_lia (m + p <=? k) false;
  (bdestruct (k <? p); simpl;
  [rewrite (Nat.mod_small (k+m) (m+p)) by lia;
  replace_bool_lia (k + m <? m) false |
  rewrite (mod_n_to_2n (k+m) (m+p)) by lia;
  replace_bool_lia (k + m - (m+p) <? m) true];
  rewrite 1?andb_true_r, 1?orb_true_r, 1?andb_false_r, 1?orb_false_r;
  simpl); [easy | f_equal; lia | 
  replace_bool_lia (k + m <? m + p) true;
  rewrite Nat.add_sub, andb_true_r |];
  bdestruct (x <? n);
  simplify_mods_of (x+o)%nat (n+o)%nat; simpl; bdestruct_one; try lia; 
  simpl; try easy; 
  [| bdestructΩ']; f_equal; lia.
Qed.
  

Definition MxBraidingIsomorphism : forall n m, 
  Isomorphism (MxDirectSumBiFunctor n m) ((CommuteBifunctor MxDirectSumBiFunctor) n m) :=
  fun n m => Build_Isomorphism nat MxCategory (n+m)%nat (m+n)%nat
    (mx_braiding n m) (mx_braiding m n)
    (mx_braiding_compose_inv n m) (mx_braiding_compose_inv m n).

#[export] Instance MxBraidingBiIsomorphism : 
  NaturalBiIsomorphism MxDirectSumBiFunctor (CommuteBifunctor MxDirectSumBiFunctor) := {|
  component2_iso := MxBraidingIsomorphism;
  component2_iso_natural := ltac:(intros; simpl in *; 
    restore_dims; rewrite mx_braiding_braids_eq; easy);
|}.

Lemma if_mult_dist_r (b : bool) (z : C) :
  (if b then C1 else C0) * z = 
  if b then z else C0.
Proof.
  destruct b; lca.
Qed.

Lemma if_mult_dist_l (b : bool) (z : C) :
  z * (if b then C1 else C0) = 
  if b then z else C0.
Proof.
  destruct b; lca.
Qed.

Lemma if_mult_dist_r_gen (b : bool) (z x y : C) :
  (if b then x else y) * z = 
  if b then x*z else y*z.
Proof.
  destruct b; lca.
Qed.

Lemma if_mult_dist_l_gen (b : bool) (z x y : C) :
  z * (if b then x else y) = 
  if b then z*x else z*y.
Proof.
  destruct b; lca.
Qed.

Lemma if_mult_and (b c : bool) :
  (if b then C1 else C0) * (if c then C1 else C0) =
  if (b && c) then C1 else C0.
Proof.
  destruct b; destruct c; lca.
Qed.

Lemma if_if_if_combine {A : Type} : forall (x y : A) (b c d:bool),
  (if b then if c then x else y
  else if d then x else y) = 
  if (b&&c)||((¬b) && d) then x else y.
Proof.
  intros.
  bdestructΩ'.
Qed.

(* Definition unshift {A} (f : nat -> A) (k : nat) (x : A) : nat -> A :=
  fun i => if i <? k then x else f (i - k)%nat. *)

Definition unshift_vec {n : nat} (v : Vector n) (k : nat) : Vector (n-k) :=
  fun i j => if (O <? j) || (i <? k) then C0 else v (i - k)%nat j.
  

Lemma vector_split : forall {n o} (v : Vector (n+o)),
  v ≡ (make_WF (v : Vector n)) .+ ((unshift_vec (shift v n : Vector (n+o)) n) : Vector o).
Proof.
  intros n o v.
  intros i j Hi Hj; replace j with O by lia; clear j Hj.
  unfold make_WF, shift, unshift_vec, Mplus.
  bdestructΩ'simp; try lca.
  rewrite Cplus_0_l. f_equal; lia.
Qed.

Definition unshift_mx {n m : nat} (v : Matrix n m) (k : nat) : Matrix (k + n) m :=
  fun i j => if (i <? k) then C0 else v (i - k)%nat j.


Lemma direct_sum'_mul_vec_r : forall {n m o p} (A : Matrix n m) (B : Matrix o p)
  (v : Vector (m + p)), 
  direct_sum' A B × v 
  ≡ (make_WF ((A × (v : Vector m))) : Matrix (n + o) 1) .+ (unshift_mx (B × (shift v m : Vector p)) n).
Proof.
  intros n m o p A B v.
  intros i j Hi Hj; replace j with O by lia; clear j Hj.
  unfold direct_sum', Mmult, unshift_mx, make_WF, shift, Mplus.
  simpl_bools.
  bdestruct (i <? n); simpl_bools.
  - rewrite big_sum_split.
    simpl.
    f_equal.
    + apply big_sum_eq_bounded.
      intros k Hk.
      bdestructΩ'.
    + rewrite big_sum_0_bounded; [easy|].
      intros k Hk.
      bdestructΩ'simp.
  - rewrite big_sum_split.
    simpl.
    f_equal.
    + rewrite big_sum_0_bounded; [easy|].
      intros k Hk.
      bdestructΩ'simp.
    + apply big_sum_eq_bounded.
      intros k Hk.
      bdestructΩ'; do 2 f_equal; lia.
Qed.

Lemma direct_sum'_stack_perms : forall n m f g, 
  permutation n f -> permutation m g ->
  direct_sum' (perm_mat n f) (perm_mat m g) ≡ perm_mat (n+m) (stack_perms n m f g).
Proof.
  intros n m f g Hf Hg.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite perm_mat_permutes_ei_r, direct_sum'_mul_vec_r by lia.
  unfold make_WF, Mplus.
  intros i j Hi Hj.
  replace j with O by lia; clear j Hj.
  simpl_bools.
  unfold make_WF, perm_mat, stack_perms, unshift_mx, shift, e_i, Mmult.
  replace_bool_lia (k <? n+m) true.
  replace_bool_lia (i <? n+m) true.
  simpl_bools.
  bdestruct (k <? n);
  (* [bdestruct (i =? f k) | bdestruct (i =? g (k - n)%nat)]; *)
  bdestruct (i <? n); simpl_bools;
  Csimpl; try simplify_bools_lia_one_kernel;
  [bdestruct (i =? f k); [subst i|] | bdestruct (i =? f k); [subst i|]
  | | bdestruct (i =? g(k-n)+n)%nat; [subst i|]];
  match goal with
  | |- _ = C1 => apply big_sum_unique
  | |- _ = C0 => rewrite big_sum_0_bounded; [easy|]; intros; bdestructΩ'simp
  end.
  4: {
    rewrite Nat.add_sub in *;
    lia.
  }
  - exists k; repeat split; try lia; intros; bdestructΩ'simp.
  - destruct Hf as [? Hf].
    specialize (Hf k).
    lia.
  - exists (k - n)%nat; repeat split; intros; bdestructΩ'simp.
Qed.

Lemma perm_mat_idn : forall n,
  perm_mat n idn = I n.
Proof.
  intros n.
  apply perm_mat_I; easy.
Qed.

Lemma direct_sum'_stack_perm_I_r : forall n m f, 
  permutation n f -> 
  direct_sum' (perm_mat n f) (I m) ≡ perm_mat (n+m) (stack_perms n m f idn).
Proof.
  intros n m f Hf.
  rewrite <- perm_mat_idn.
  rewrite direct_sum'_stack_perms; (auto with perm_db).
  easy.
Qed.

Lemma direct_sum'_stack_perm_I_l : forall n m f, 
  permutation m f -> 
  direct_sum' (I n) (perm_mat m f) ≡ perm_mat (n+m) (stack_perms n m idn f).
Proof.
  intros n m f Hf.
  rewrite <- perm_mat_idn.
  rewrite direct_sum'_stack_perms; (auto with perm_db).
  easy.
Qed.

Lemma mx_braiding_hexagon1: forall n m o (* M B A *),
  ((direct_sum' (mx_braiding n m) (I o) × I (m + n + o)
  × direct_sum' (I m) (mx_braiding n o)))
  ≡ (I (n + m + o) × (mx_braiding n (m + o)%nat) × I (m + o + n)).
Proof.
  intros n m o.
  (* replace (n + (o+m))%nat with (m+o+n)%nat by lia. *)
  rewrite 2!Mmult_1_r_mat_eq, Mmult_1_l_mat_eq.
  rewrite (Nat.add_comm m n), (Nat.add_comm o n).
  rewrite direct_sum'_stack_perm_I_r by auto with perm_db.
  replace (n+m+o)%nat with (m+(n+o))%nat by lia.
  replace (m+o+n)%nat with (m+(n+o))%nat by lia.
  rewrite direct_sum'_stack_perm_I_l by auto with perm_db.
  rewrite perm_mat_Mmult by auto with perm_db.
  apply perm_mat_equiv_of_perm_eq'; [lia|].
  intros k Hk.
  unfold stack_perms, rotr, Basics.compose;
  replace_bool_lia (k <? m + (n + o)) true.
  bdestructΩ'simp; solve_simple_mod_eqns.
  (* bdestruct (k <? m);
  bdestruct (n + o <=? k - m);
  bdestruct (k <? n + m);
  bdestructΩ'simp; solve_simple_mod_eqns. *)
(*  intros i j Hi Hj.
  unfold perm_mat, rotr.
  do 3 simplify_bools_lia_one.
  unfold direct_sum', Mmult.
  (* repeat (bdestruct_one; simpl_bools; simpl; subst; try easy; try lia). *)

  erewrite big_sum_eq_bounded.
  2: {
    intros k Hk.
    unfold I.
    rewrite <- 2!andb_if.
    rewrite 2!if_if_if_combine.
    rewrite if_mult_and.
    replace_bool_lia (j <? n + m + o) true.
    replace_bool_lia (k <? m + n + o) true.
    replace_bool_lia (i <? n + m + o) true.
    
    replace_bool_lia (k <? m + (n + o)) true.
    replace_bool_lia (j <? m + (o + n)) true.
    simpl_bools.
    
    replace (n + m <=? k) with (¬ k <? n + m) by bdestructΩ'.
    replace_bool_lia ((i - (n + m) <? o)) (0 <? o).
    reflexivity.
  }

  bdestruct (j <? (m + o));
  simplify_mods_of (j + n)%nat (n + (m + o))%nat.
  
  bdestruct (i =? j + n).
  + subst i.
    erewrite big_sum_eq_bounded.
    2: {
      intros k Hk.
      replace_bool_lia (j + n <? n + m) (j <? m).
      unshelve (instantiate (1:=_)).
      refine (fun k => if (k =? j) then _ else _); shelve.
      bdestruct (k =? j).
      - replace j with k by easy. 
        rewrite Nat.eqb_refl.
        unshelve (instantiate (1:=_)).
        refine (if (k <? m) then _ else _); shelve.
        bdestruct (k <? m); simpl_bools.
        + replace_bool_lia (k <? n + m) true;
          replace_bool_lia (k <? m + n) true; simpl_bools.
          rewrite Nat.mod_small, Nat.eqb_refl by lia.
          reflexivity.
        + (* replace_bool_lia (k + n <? n + m) false.  *)
          replace_bool_lia (0 <? o) true.
          replace_bool_lia (n + o <=? k - m) false. 
          replace_bool_lia (k - m <? n + o) true. simpl_bools.
          rewrite Nat.mod_small by lia.
          unshelve (instantiate (1:=_)).
          refine (if (k <? m + n) then _ else _); shelve.
          bdestruct (k <? m + n); simpl_bools; [reflexivity|].
          replace ((k + n - (n + m) =? k - (m + n)) && (k - m =? k - m + n))
            with (¬ 0<?n) by (bdestructΩ').
          rewrite negb_if.
          reflexivity.
      - replace_bool_lia (k =? j) false.
        simpl_bools.
        unshelve (instantiate (1:=_)).
        refine (if (k <? m) then _ else _); shelve.
        bdestruct (k <? m); simpl_bools; [reflexivity|].
        replace_bool_lia (n + o <=? j - m) false.
        replace_bool_lia (k - m <? n + o) true;
        replace_bool_lia (j - m <? n + o) true; simpl_bools.
        replace_bool_lia (k <? m + n) (k <? n + m).

        unshelve (instantiate (1:=_)).
        refine (if (j <? m) then _ else _); shelve.
        bdestruct (j <? m); simpl_bools; [reflexivity|].
        replace_bool_lia (0 <? o) true; simpl_bools.
        rewrite Nat.mod_small by lia.
        unshelve (instantiate (1:=_)).
        refine (if (k <? n+m) then _ else _); shelve.
        bdestruct (k <? n+m); simpl_bools; [reflexivity|].
        
        replace_bool_lia ((k - m =? j - m + n)) (k =? j + n).
        replace_bool_lia (j + n - (n + m) =? k - (m + n)) (k=?j+n).
        rewrite andb_diag.
        reflexivity.
    } 
    bdestruct (j<?m).
    - apply big_sum_unique.
      exists j; repeat split; try lia; bdestructΩ'; intros; bdestructΩ'.
    - apply big_sum_unique. 
      exists (j+n)%nat; repeat split; try lia.
      bdestructΩ'.
      intros; bdestructΩ'.
  + rewrite big_sum_0_bounded; [easy|].
    intros k Hk.
    repeat (bdestruct_one; simpl_bools; simpl in *; try lia; try easy);
    solve_simple_mod_eqns.
  + replace_bool_lia (j <? m) false.
    replace_bool_lia (j - m <? n + o) true.
    erewrite big_sum_eq_bounded.
    2: {
      intros k Hk.
      replace_bool_lia (n + o <=? j - m) false.
      replace_bool_lia (k - m <? n + o) true.
      simpl_bools.
      rewrite (mod_n_to_2n _ (n+o)) by lia.
      replace_bool_lia (k - m =? j - m + n - (n + o))
      (k - m =? j - m - o).
      replace_bool_lia (k <? m + n) (k <? n + m).
      unshelve (instantiate (1:=_)).
      refine (fun k => if (k <? n + m) then _ else _); shelve.
      simpl.
      bdestruct (k <? n + m); simpl_bools;
      (unshelve (instantiate (1:=_)); [
      refine (if (i <? n + m) then _ else _); shelve|]);
      bdestruct (i <? n + m); simpl_bools; simplify_bools_lia;
      [|reflexivity|reflexivity|reflexivity].
      unshelve (instantiate (1:=_)).
      refine (if (k <? m) then _ else _); shelve.
      bdestruct (k <? m); simpl_bools; [reflexivity|].
      rewrite mod_n_to_2n by lia.
      replace_bool_lia (k - m =? j - m - o) (k =? j - o).
      replace_bool_lia (i =? k + n - (n + m)) (i =? k - m).
      reflexivity.
    }
    replace_bool_lia (i =? j + n - (n + (m + o))) (i =? j - m - o).
    bdestruct (i =? j - m -o).
    - replace_bool_lia (i <? n+m) true.
      subst i.
      apply big_sum_unique.
      exists (j - o)%nat; repeat split; try lia; bdestructΩ'; intros; bdestructΩ'.
    - rewrite big_sum_0_bounded; [easy|].
      intros k Hk.
      bdestructΩ'.
*)
Qed.

Lemma mx_braiding_hexagon2 : forall A B M,
  (@mat_equiv (A+B+M) (B+(M+A)) 
  (@Mmult (A+B+M) (B+(A+M)) (B+(M+A))
    (@Mmult (A+B+M) (B+A+M) (B+(A+M)) 
      (@direct_sum' (A+B) (B+A) M M (perm_mat (A+B) (rotr (A+B) A)) (I M)) 
      (I (B+A+M))
    )
    (@direct_sum' B B (A+M) (M+A) (I B) (perm_mat (A+M) (rotr (A+M) A))))
  (@Mmult (A+B+M) (B+M+A) (B+(M+A))
    (@Mmult (A+B+M) (A+(B+M)) (B+M+A) 
      (I (A+B+M))
      (perm_mat (A+(B+M)) (rotr (A+(B+M)) A)))
      (I (B+M+A)))).
Proof.
  intros n m o.
  rewrite (Nat.add_comm m n), (Nat.add_comm o n).
  rewrite direct_sum'_stack_perm_I_r by auto with perm_db.
  rewrite direct_sum'_stack_perm_I_l by auto with perm_db.
  replace (m + (n + o))%nat with (n+m+o)%nat by lia.
  rewrite Mmult_1_r_mat_eq.
  rewrite perm_mat_Mmult; 
    [| replace (n+m+o)%nat with (m+(n+o))%nat by lia; auto with perm_db].
  rewrite (Nat.add_assoc).
  restore_dims.
  rewrite Mmult_1_r_mat_eq, Mmult_1_l_mat_eq.
  apply perm_mat_equiv_of_perm_eq.
  intros k Hk.
  unfold stack_perms, rotr. 
  bdestructΩ'.
  unfold compose.
  replace_bool_lia (k <? m + (n + o)) true;
  bdestruct (k <? m); [do 2 simplify_mods_one; bdestructΩ'simp|];
  simplify_bools_lia_one_kernel;
  case_mods_one;
  simplify_bools_lia_one_kernel;
  simplify_mods_one; [|simplify_mods_one];
  simplify_bools_lia_one_kernel; lia.
Qed.

#[export] Instance MxBraidedMonoidalCategory : BraidedMonoidalCategory nat := {
  braiding := MxBraidingBiIsomorphism;

  hexagon_1 := ltac:(intros A B M; simpl in *;
    pose proof (mx_braiding_hexagon1 A B M) as H;
    replace (B+M+A)%nat with ((B + (M+A))%nat) in * by lia;
    apply_with_obligations H; f_equal; try lia;
    restore_dims; easy);
  hexagon_2 := ltac:(intros; simpl in *; 
    apply mx_braiding_hexagon2
  );
}.



#[export] Instance MxSymmetricMonoidalCategory : SymmetricMonoidalCategory nat := {
  symmetry := ltac:(easy);
}.


#[export] Instance MxDaggerCategory : DaggerCategory nat := {
  adjoint := @adjoint;
  involutive := ltac:(intros; rewrite adjoint_involutive; easy);
  preserves_id := ltac:(intros; rewrite id_adjoint_eq; easy);
  contravariant := ltac:(intros; rewrite Mmult_adjoint; easy);
}.


Lemma direct_sum'_adjoint : forall m n o p (A : Matrix m n) (B : Matrix o p),
  direct_sum' (A †) (B †) ≡ (direct_sum' A B) †.
Proof.
  intros m n o p A B.
  unfold adjoint, direct_sum'.
  intros i j Hi Hj. 
  rewrite 2!(if_dist _ _ _ Cconj).
  rewrite Cconj_0.
  bdestructΩ'.
Qed.

#[export] Instance MxDaggerMonoidalCategory : DaggerMonoidalCategory nat := {
  dagger_compat := ltac: (intros; apply direct_sum'_adjoint);

  associator_unitary_r := ltac:(intros; simpl in *;
    rewrite Nat.add_assoc, id_adjoint_eq, Mmult_1_r by auto with wf_db;
    easy);
  associator_unitary_l := ltac:(intros; simpl in *;
    rewrite Nat.add_assoc, id_adjoint_eq, Mmult_1_r by auto with wf_db;
    easy);
  left_unitor_unitary_r := ltac:(intros; simpl in *;
    rewrite id_adjoint_eq, Mmult_1_r by auto with wf_db;
    easy);
  left_unitor_unitary_l := ltac:(intros; simpl in *;
    rewrite id_adjoint_eq, Mmult_1_r by auto with wf_db;
    easy);
  right_unitor_unitary_r := ltac:(intros;  simpl in *;
    rewrite Nat.add_0_r, id_adjoint_eq, Mmult_1_r by auto with wf_db;
    easy);
  right_unitor_unitary_l := ltac:(intros; simpl in *;
    rewrite Nat.add_0_r, id_adjoint_eq, Mmult_1_r by auto with wf_db;
    easy);
}.

#[export] Instance MxDaggerBraidedMonoidalCategory : DaggerBraidedMonoidalCategory nat := {}.

#[export] Instance MxDaggerSymmetricMonoidalCategory : DaggerSymmetricMonoidalCategory nat := {}.