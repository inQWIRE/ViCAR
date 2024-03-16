Require Import MatrixPermBase.
Require Import KronComm.
Require Export MatrixExampleBase.
Require Import ExamplesAutomation.


#[export] Instance MxCategory : Category nat := {
  morphism := Matrix;

  c_equiv := @mat_equiv;  (* fun m n => @eq (Matrix m n); *)
  c_equiv_rel := @mat_equiv_equivalence;

  compose := @Mmult;
  compose_compat := fun n m o f g Hfg h i Hhi =>
    @Mmult_simplify_mat_equiv n m o f g h i Hfg Hhi;
  assoc := @Mmult_assoc_mat_equiv;

  c_identity n := I n;
  left_unit := Mmult_1_l_mat_eq;
  right_unit := Mmult_1_r_mat_eq;
}.


Definition MxKronBiFunctor : Bifunctor MxCategory MxCategory MxCategory := {|
  obj_bimap := Nat.mul;
  morphism_bimap := @kron;
  id_bimap := ltac:(intros; rewrite id_kron; easy);
  compose_bimap := ltac:(intros; rewrite kron_mixed_product; easy);
  morphism_bicompat := ltac:(intros; apply kron_mat_equiv_morph; easy);
|}.



#[export] Instance MxKronMonoidalCategory : MonoidalCategory nat := {
  tensor := MxKronBiFunctor;
  I := 1;
  
  associator := fun n m o => {|
  forward := (I (n * m * o) : Matrix (n * m * o) (n * (m * o)));
  reverse := (I (n * m * o) : Matrix (n * (m * o)) (n * m * o));
  isomorphism_inverse := ltac:(split; simpl; rewrite Nat.mul_assoc, Mmult_1_r_mat_eq; easy);
  (* id_A := ltac:(simpl; rewrite Nat.mul_assoc, Mmult_1_r_mat_eq; easy);
  id_B := ltac:(simpl; rewrite Nat.mul_assoc, Mmult_1_r_mat_eq; easy); *)
  |};
  
  left_unitor := fun n => {|
  forward := (I n : Matrix (1 * n) n);
  reverse := (I n : Matrix n (1 * n));
  isomorphism_inverse 
    := ltac:(abstract(split; rewrite Nat.mul_1_l, Mmult_1_r_mat_eq; easy));
  (* id_A := ltac:(rewrite Nat.mul_1_l, Mmult_1_r_mat_eq; easy);
  id_B := ltac:(rewrite Nat.mul_1_l, Mmult_1_r_mat_eq; easy); *)
  |};

  right_unitor := fun n => {|
  forward := (I n : Matrix (n * 1) n);
  reverse := (I n : Matrix n (n * 1));
  isomorphism_inverse 
    := ltac:(abstract(split; rewrite Nat.mul_1_r, Mmult_1_r_mat_eq; easy));
  (* id_A := ltac:(rewrite Nat.mul_1_r, Mmult_1_r_mat_eq; easy);
  id_B := ltac:(rewrite Nat.mul_1_r, Mmult_1_r_mat_eq; easy); *)
  |};

  associator_cohere := ltac:(intros; simpl in *; 
    rewrite kron_assoc_mat_equiv;  
    rewrite 2!Nat.mul_assoc, Mmult_1_r_mat_eq, Mmult_1_l_mat_eq;
    easy
  );
  left_unitor_cohere := ltac:(intros; cbn;
   rewrite kron_1_l_mat_equiv, 2!Nat.add_0_r, 
     Mmult_1_l_mat_eq, Mmult_1_r_mat_eq; easy);
  right_unitor_cohere := ltac:(intros; cbn;
  rewrite kron_1_r_mat_equiv, 2!Nat.mul_1_r, 
    Mmult_1_l_mat_eq, Mmult_1_r_mat_eq; easy);

  pentagon := ltac:(intros; simpl in *; 
    rewrite ?Nat.mul_assoc, 2!id_kron, Mmult_1_l_mat_eq;
    rewrite ?Nat.mul_assoc, Mmult_1_l_mat_eq;
    easy
    ); 
  triangle :=  ltac:(intros; 
    cbn;
    rewrite Nat.mul_1_r, Nat.add_0_r in *;
    rewrite Mmult_1_l_mat_eq;
    easy
    );
}.

Definition MxKronBraidingIsomorphism : forall n m, 
  Isomorphism (MxKronBiFunctor n m) ((CommuteBifunctor MxKronBiFunctor) n m) :=
  fun n m => Build_Isomorphism nat MxCategory (n*m)%nat (m*n)%nat
    (kron_comm n m) (kron_comm m n)
    ltac:(intros; simpl; split; 
    [rewrite (Nat.mul_comm m n), (kron_comm_mul_inv n m)
    | rewrite (Nat.mul_comm n m), (kron_comm_mul_inv m n)]; easy).



#[export] Instance MxKronBraidingBiIsomorphism : 
  NaturalBiIsomorphism MxKronBiFunctor (CommuteBifunctor MxKronBiFunctor) := {|
  component_biiso := MxKronBraidingIsomorphism;
  component_biiso_natural := ltac:(intros; simpl in *; 
    rewrite (Nat.mul_comm B2 B1), (Nat.mul_comm A2 A1); 
    rewrite (kron_comm_commutes_r_mat_equiv);
    easy);
|}.


Lemma mod_sub : forall a b c, (b*c<=a)%nat -> c <> O ->
  ((a - b * c) mod c = a mod c)%nat.
Proof.
  intros a b c Hbca Hc.
  symmetry.
  apply Nat.mod_unique with (a/c-b)%nat; auto.
  - apply Nat.mod_upper_bound; auto.
  - rewrite Nat.mul_sub_distr_l, <- Nat.add_sub_swap.
    + rewrite <- Nat.div_mod, Nat.mul_comm; lia.
    + apply Nat.mul_le_mono_l.
      apply Nat.div_le_lower_bound; lia.
Qed.

Lemma mod_sub_l_small : forall a b c, (c < b)%nat -> a <> O ->
  ((a * b - c) mod b = (b - c) mod b)%nat.
Proof.
  intros a b c Hc Ha.
  symmetry.
  rewrite <- (Nat.mod_add _ (a-1) b) by lia.
  rewrite <- Nat.add_sub_swap by lia.
  f_equal.
  nia.
Qed.

Lemma mod_sub_l_small_alt : forall a b c, (c <= b)%nat -> b <> O -> a <> O ->
  ((a * b - c) mod b = (b - c) mod b)%nat.
Proof.
  intros a b c Hc Ha.
  symmetry.
  rewrite <- (Nat.mod_add _ (a-1) b) by lia.
  rewrite <- Nat.add_sub_swap by easy.
  f_equal.
  nia.
Qed.


Lemma mod_sub_l : forall a b c, (c <= a*b)%nat -> b <> O ->
  ((a * b - c) mod b = (b - c mod b) mod b)%nat.
Proof.
  intros a b c Hbca Hb.
  bdestruct (c mod b =? 0).
  - replace (c mod b).
    destruct (proj1 (Nat.mod_divide c b Hb) ltac:(easy)) as [q Hq].
    subst c.
    rewrite <- Nat.mul_sub_distr_r, Nat.mod_mul, 
      Nat.sub_0_r, Nat.mod_same; easy.
  - rewrite (Nat.mod_small (b - _)) by lia.
    rewrite (Nat.div_mod c b Hb) at 1.
    rewrite (Nat.mul_comm b _), Nat.sub_add_distr, 
      <- Nat.mul_sub_distr_r.
    rewrite mod_sub_l_small.
    + rewrite Nat.mod_small; lia.
    + apply Nat.mod_upper_bound; lia.
    + rewrite Nat.sub_0_le, Nat.nle_gt.
      apply Nat.div_lt_upper_bound; [easy|].
      bdestruct (c =? a * b).
      * subst c.
        rewrite Nat.mod_mul in *; easy.
      * lia.
Qed.

Lemma div_sub_r : forall a b c, c <> O ->
  ((a - b * c)/ c = a / c - b)%nat.
Proof.
  intros a b c Hc.
  bdestruct (a <? b*c ).
  - rewrite (proj2 (Nat.sub_0_le _ _)), Nat.div_0_l by lia. 
    symmetry; apply Minus.not_le_minus_0_stt.
    rewrite Nat.nle_gt.
    apply Nat.div_lt_upper_bound; lia.
  - apply (Nat.mul_cancel_l _ _ c Hc).
    apply (Nat.add_cancel_r _ _ ((a-b*c) mod c)).
    rewrite <- Nat.div_mod by lia.
    rewrite Nat.mul_sub_distr_l, mod_sub by lia.
    rewrite <- Nat.add_sub_swap by 
      (apply Nat.mul_le_mono_l, Nat.div_le_lower_bound; lia).
    rewrite <- Nat.div_mod; lia.
Qed.

Lemma mod_of_div : forall n m k, n <> O -> m <> O ->
  ((k / n) mod m = k mod (n * m) / n)%nat.
Proof.
  intros n m k Hn Hm.
  rewrite 2!mod_eq_sub.
  rewrite <- Nat.mul_assoc, (Nat.mul_comm n _), 
    div_sub_r, Nat.div_div; lia.
Qed.

Lemma ei_kron_split_l_mat_equiv : forall (n m k : nat),
  @e_i (n*m) k ≡ @e_i m (k / n) ⊗ @e_i n (k mod n).
Proof.
  intros n m k.
  intros i j Hi Hj; replace j with O by lia; clear j Hj.
  unfold kron, e_i.
  replace_bool_lia (i <? n * m) true.
  rewrite Nat.div_1_r, Nat.mod_1_r.
  pose proof (Nat.div_lt_upper_bound i n m).
  pose proof (Nat.mod_upper_bound i n).
  replace_bool_lia (i / n <? m) true.
  replace_bool_lia (i mod n <? n) true.
  simpl_bools.
  bdestructΩ'simp.
  contradict H1.
  rewrite (Nat.div_mod i n), (Nat.div_mod k n) by lia.
  lia.
Qed.


Lemma mx_hexagon_helper : forall A B M : nat, 
  @mat_equiv (A*B*M) (B*M*A) 
    (@Mmult (A*B*M) (B*A*M) (B*M*A)
    (@kron (A*B) (B*A) M M
        (kron_comm A B) (I M))
    (@kron B B (A*M) (M*A)
        (I B) (kron_comm A M)))
  (kron_comm A (B*M)).
Proof.
  intros A B M.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  replace (B*M*A)%nat with (A*M*B)%nat by lia.
  rewrite (ei_kron_split_l_mat_equiv) at 1.
  rewrite Mmult_assoc_mat_equiv, (Nat.mul_comm M A).
  replace (B*A*M)%nat with (B*(A*M))%nat by lia.
  replace (A*M*B)%nat with (B*(A*M))%nat by lia.
  rewrite (@kron_mixed_product B B 1 (A*M) (A*M) 1).
  rewrite Mmult_1_l_mat_eq.
  rewrite ei_kron_split_l_mat_equiv.
  rewrite kron_comm_commutes_vectors_l_mat_equiv.
  replace (A*B*M)%nat with (B*(A*M))%nat by lia.
  rewrite <- (@kron_assoc B 1 A 1 M 1) by (auto with wf_db).
  simpl.
  replace (B*(A*M))%nat with (A*B*M)%nat by lia.
  rewrite (Nat.mul_comm B A).
  simpl_rewrite (kron_mixed_product (o:=1) (r:=1) (kron_comm A B) (I M)).
  rewrite Mmult_1_l_mat_eq.
  rewrite kron_comm_commutes_vectors_l_mat_equiv.
  rewrite <- Nat.mul_assoc, ei_kron_split_l_mat_equiv.
  rewrite kron_comm_commutes_vectors_l_mat_equiv.
  rewrite (Nat.mul_comm A M), mod_product, Nat.mul_assoc by lia.
  rewrite (kron_e_i_e_i B A); [
    | apply Nat.div_lt_upper_bound;lia
    | apply Nat.mod_upper_bound; lia].
  rewrite (kron_e_i_e_i (B*M) (A)); [
    | apply Nat.div_lt_upper_bound;lia
    | apply Nat.mod_upper_bound; lia].

  intros i j Hi Hj.
  replace j with O by lia; clear j Hj.
  unfold kron, e_i.
  replace_bool_lia (i <? B*M*A) true.
  assert (HiMAB : (i / M < A * B)%nat) by (
    apply Nat.div_lt_upper_bound; lia
  ).
  replace_bool_lia (i / M <? B*A) true.
  pose (Nat.mod_upper_bound i M); 
  replace_bool_lia (i mod M <? M) true.
  simpl_bools.
  rewrite if_mult_and, (Nat.mul_comm M A), <- mod_of_div by lia.
  bdestruct (i =? k mod A * (B*M) + k/A).
  - subst.
    rewrite Nat.mul_assoc, Nat.div_add_l by lia.
    rewrite Nat.div_div, Nat.eqb_refl by lia.
    rewrite Nat.add_comm, Nat.mod_add, Nat.eqb_refl by lia.
    easy.
  - bdestructΩ'simp.
    contradict H.
    rewrite (Nat.div_mod i M) by lia.
    replace -> (i/M)%nat.
    replace -> (i mod M).
    rewrite Nat.mul_add_distr_l.
    rewrite <- Nat.add_assoc, <- Nat.div_div, <- Nat.div_mod by lia.
    lia.
Qed.
  

#[export, program] Instance MxBraidedMonoidal : BraidedMonoidalCategory nat := {
  braiding := MxKronBraidingBiIsomorphism
}.
Next Obligation.
  rewrite 3!Nat.mul_assoc.
  rewrite Mmult_1_r_mat_eq, Mmult_1_r_mat_eq.
  rewrite Mmult_1_l_mat_eq.
  apply mx_hexagon_helper.
Qed.
Next Obligation.
  rewrite 3!Nat.mul_assoc.
  rewrite Mmult_1_r_mat_eq, Mmult_1_r_mat_eq.
  rewrite Mmult_1_l_mat_eq.
  apply mx_hexagon_helper.
Qed.

#[export, program] Instance MxSymmetricMonoidal : 
  SymmetricMonoidalCategory nat. 
Next Obligation.
 easy.
Qed.

Definition mat_unit (n : nat) : Matrix 1 (n*n) :=
  fun i j => if (i =? 0) && (0 <? n) && (j / n =? j mod n) then C1 else C0.

Lemma WF_mat_unit {n} : WF_Matrix (mat_unit n).
Proof.
  unfold mat_unit.
  intros i j [Hi | Hj].
  - bdestructΩ'.
  - bdestructΩ'simp. 
    pose proof (Nat.mod_upper_bound j n).
    assert (n <= j / n)%nat by (apply Nat.div_le_lower_bound; lia).
    lia.
Qed.

#[export] Hint Resolve WF_mat_unit : wf_db.

Lemma mat_counit_mat_equiv (n : nat) : (mat_unit n) ⊤ ≡
  big_sum (G:=Matrix (n*n)%nat 1) (fun i => @e_i n i ⊗ @e_i n i) n.
Proof.
  intros i j Hi Hj; replace j with O by lia; clear j Hj.
  unfold mat_unit, e_i, transpose, kron.
  replace_bool_lia (0 <? n) true.
  rewrite andb_true_l.
  rewrite Msum_Csum.
  erewrite big_sum_eq_bounded. 
  2: {
    intros k Hk.
    rewrite Nat.div_1_r, Nat.mod_1_r.
    pose proof (Nat.mod_upper_bound i n);
    replace_bool_lia (i mod n <? n) true.
    pose proof (Nat.div_lt_upper_bound i n n);
    replace_bool_lia (i / n <? n) true.
    simpl_bools.
    rewrite if_mult_and.
    reflexivity.
  }
  symmetry.
  bdestruct (i / n =? i mod n).
  - apply big_sum_unique.
    exists (i mod n).
    split; [apply Nat.mod_upper_bound; lia|].
    split; [rewrite Nat.eqb_refl; bdestructΩ'simp |].
    intros i' Hi' Hfalse.
    bdestructΩ'simp.
  - rewrite big_sum_0_bounded; [easy|].
    intros j Hj.
    bdestructΩ'simp.
Qed.

(* Definition mat_counit (n : nat) : Matrix n 1 := (mat_unit n) ⊤. *)

#[export, program] Instance MxCompactClosed : CompactClosedCategory nat := {
  dual := fun A => A;
  unit := mat_unit;
  counit := fun n => (mat_unit n) ⊤;
}.
Next Obligation.
  rewrite Nat.add_0_r, Nat.mul_1_r.
  rewrite Mmult_1_r_mat_eq, Mmult_1_l_mat_eq.
  rewrite <- Nat.mul_assoc.
  rewrite Mmult_1_r_mat_eq.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite Mmult_1_l_mat_eq.
  rewrite Mmult_assoc.
  pose (kron_e_i_e_i A 1 k 0 Hk (le_n 1)) as Hek.
  rewrite !Nat.mul_1_r, Nat.mul_0_l, Nat.add_0_l in Hek.
  rewrite <- Hek at 1.
  rewrite Nat.mul_assoc.
  pose (@kron_mixed_product (A*A)%nat 1 1 A A 1) as Hkron;
    rewrite !Nat.mul_1_l in Hkron.
  rewrite Hkron.
  assert (H: @e_i 1 0 = I 1) by (unfold e_i; solve_matrix; bdestructΩ'simp).
  rewrite H.
  rewrite Mmult_1_r_mat_eq, Mmult_1_l_mat_eq.
  intros i j Hi Hj; replace j with O by lia; clear j Hj.
  unfold I, e_i, kron, mat_unit, Mmult, transpose.
  rewrite !Nat.div_1_r, !Nat.mod_1_r.
  replace_bool_lia (0 <? A) true.
  replace_bool_lia (i <? A) true.
  simpl_bools.
  bdestruct (i =? k).
  - subst i.
    apply big_sum_unique.
    assert (0 < A)%nat by lia.
    assert (0 < A*A)%nat by lia.
    assert (A <> 0)%nat by lia.
    assert (A*A <> 0)%nat by lia.
    exists ((A*A)*k + k*(1 + A))%nat.
    pose proof (Nat.mod_small k A Hi) as Hmodk.
    assert (k < A * A)%nat by nia.
    pose proof (Nat.mod_small k (A*A) ltac:(nia)).
    split; [nia|].
    rewrite Nat.mul_comm, Nat.div_add_l, Nat.div_small, 
      Nat.add_0_r, Nat.eqb_refl, andb_true_r, Cmult_1_l by (easy || nia).
    rewrite Nat.add_comm, Nat.mod_add, Nat.mod_small by (easy || nia).
    rewrite Nat.mul_add_distr_l, Nat.mul_1_r, Nat.div_add, Nat.mod_add,
      Nat.div_small, Nat.mod_small, Nat.eqb_refl, Cmult_1_l by (easy || nia).
    rewrite Nat.div_div, Nat.div_add, Nat.div_small, Nat.mul_assoc, 
      2!Nat.div_add, Nat.div_small, Nat.mod_add, Nat.mod_small,
      Nat.eqb_refl, Cmult_1_l by (easy || nia).
    split; [rewrite 2!Nat.mod_add, Hmodk; bdestructΩ'simp|].
    intros k' Hk' Hfalse.
    pose proof (Nat.div_mod k' (A*A) ltac:(nia)) as Hk'eq.
    rewrite Hk'eq.
    pose proof (Nat.mod_upper_bound k' (A*A) ltac:(lia)) as Hk'modAA.
    rewrite Nat.mul_comm, Nat.div_add_l, (Nat.div_small _ _ Hk'modAA), 
      Nat.add_0_r, andb_true_r by (easy || nia).
    bdestruct (k =? k' / (A*A)); [|lca].
    replace <- (k' / (A * A))%nat.
    rewrite Nat.add_comm, Nat.mod_add, Cmult_1_l by (easy || nia).
    rewrite Nat.mod_mod, mod_product, Nat.div_div, Nat.div_add by (easy || nia).
    rewrite Nat.mul_assoc, Nat.div_add, Nat.mod_add, <- mod_of_div by easy.
    rewrite Nat.mod_mod, Nat.mod_add, mod_product by easy.
    bdestruct (k' mod A =? k); [|lca].
    replace (k' mod A).
    replace_bool_lia (k <? A) true.
    rewrite 2!andb_true_r, Cmult_1_r.
    pose proof (Nat.div_mod (k' mod (A*A)) A ltac:(easy)) as Hk'modAAeq.
    rewrite mod_product, <- mod_of_div in Hk'modAAeq by easy.
    bdestruct ((k' / A) mod A =? k); [|lca].
    lia.
  - rewrite big_sum_0_bounded; [easy|].
    intros j HJ.
    bdestructΩ'simp.
    rewrite mod_product, <- mod_of_div, Nat.div_div in * by lia.
    lia.
Qed.
Next Obligation.
  rewrite Nat.add_0_r, Nat.mul_1_r.
  rewrite Mmult_1_r_mat_eq, Mmult_1_l_mat_eq.
  rewrite <- Nat.mul_assoc.
  rewrite Mmult_1_r_mat_eq.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite Mmult_1_l_mat_eq.
  rewrite Mmult_assoc.
  pose (kron_e_i_e_i 1 A 0 k (le_n 1) Hk) as Hek.
  rewrite !Nat.mul_1_r, Nat.mul_1_l, Nat.add_0_r in Hek.
  rewrite <- Hek at 1.
  rewrite Nat.mul_assoc.
  pose (@kron_mixed_product A A 1 (A*A)%nat 1 1) as Hkron;
    rewrite !Nat.mul_1_l, Nat.mul_1_r, Nat.mul_assoc in Hkron.
  rewrite Hkron.
  assert (H: @e_i 1 0 = I 1) by (unfold e_i; solve_matrix; bdestructΩ'simp).
  rewrite H.
  rewrite <- Nat.mul_assoc.
  rewrite Mmult_1_l_mat_eq, Mmult_1_r_mat_eq.
  intros i j Hi Hj; replace j with O by lia; clear j Hj.
  unfold I, e_i, kron, mat_unit, Mmult, transpose.
  rewrite !Nat.div_1_r, !Nat.mod_1_r.
  replace_bool_lia (0 <? A) true.
  replace_bool_lia (i <? A) true.
  simpl_bools.
  bdestruct (i =? k).
  - subst i.
    apply big_sum_unique.
    assert (0 < A)%nat by lia.
    assert (0 < A*A)%nat by lia.
    assert (A <> 0)%nat by lia.
    assert (A*A <> 0)%nat by lia.
    exists ((A*A)*k + k*(1 + A))%nat.
    pose proof (Nat.mod_small k A Hi) as Hmodk.
    assert (k < A * A)%nat by nia.
    pose proof (Nat.mod_small k (A*A) ltac:(nia)).
    split; [nia|].
    rewrite Nat.div_small, Nat.mul_comm, Nat.div_div, Nat.div_add_l, 
      Nat.div_small, Nat.add_0_r, Nat.add_comm, Nat.mul_assoc, 
      Nat.mul_add_distr_l, Nat.mul_1_r, 2!Nat.div_add, Nat.mod_add, 
      Nat.div_small, Nat.mod_small, Nat.add_0_l, 2!Nat.eqb_refl,
      andb_true_r, Cmult_1_l, Hmodk by (easy || nia).
    rewrite 2!Nat.mod_add, Hmodk, Nat.eqb_refl, <- Nat.mul_assoc, Nat.mod_add, 
      mod_product, Nat.mod_add, Nat.mod_small, Nat.div_add, Nat.div_small,
      Hmodk, Nat.eqb_refl by (easy || nia).
    replace_bool_lia (k <? A) true.
    split; [bdestructΩ'simp|].
    intros k' Hk' Hfalse.
    pose proof (Nat.div_mod k' (A*A) ltac:(nia)) as Hk'eq.
    rewrite Hk'eq.
    pose proof (Nat.mod_upper_bound k' (A*A) ltac:(lia)) as Hk'modAA.
    rewrite Nat.mul_comm, Nat.div_div, Nat.div_add_l,
      (Nat.div_small _ _ Hk'modAA), Nat.add_0_r, Nat.add_comm, Nat.mod_add,
      Nat.mul_assoc, Nat.div_add, 2!Nat.mod_add, <- mod_of_div, 2!Nat.mod_mod,
      mod_product by easy.
    
    bdestruct (k' / (A*A) <? A); [|nia].
    simpl_bools.
    pose proof (Nat.div_mod (k' mod (A*A)) A ltac:(easy)) as Hk'modAAeq.
    
    rewrite mod_product in Hk'modAAeq by easy.
    bdestruct ((k' / (A * A)) =? k); [|lca].
    bdestruct (k' mod (A * A) / A =? k' mod A); [|lca].
    bdestruct (k =? k' mod A); [|lca].
    lia.
  - rewrite big_sum_0_bounded; [easy|].
    intros j HJ.
    rewrite Nat.div_small, (Nat.mod_small i) by easy.
    replace_bool_lia (i <? A) true.
    bdestruct (j / (A*A) <? A); [|simpl_bools; lca].
    rewrite mod_product, <- mod_of_div, Nat.eqb_refl, Nat.div_div by lia.
    simpl_bools.
    bdestructΩ'simp.
Qed.

#[program, export] Instance MxDaggerCategory : DaggerCategory nat := {
  adjoint := @adjoint
}.
Next Obligation.
  rewrite adjoint_involutive; easy.
Qed.
Next Obligation.
  rewrite id_adjoint_eq; easy.
Qed.
Next Obligation.
  rewrite Mmult_adjoint; easy.
Qed.
Next Obligation.
  unfold adjoint.
  intros ? ? ? ?; rewrite H; easy.
Qed.

#[program, export] Instance MxDaggerMonoidalCategory : DaggerMonoidalCategory nat.
Next Obligation.
  rewrite kron_adjoint; easy.
Qed.
Next Obligation.
  rewrite Nat.mul_assoc.
  unfold unitary; 
  rewrite adjoint_id, ?left_unit; easy.
Qed.
Next Obligation.
  rewrite Nat.add_0_r.
  unfold unitary;  
  rewrite adjoint_id, ?left_unit; 
  easy.
Qed.
Next Obligation.
  rewrite Nat.mul_1_r.
  unfold unitary;  
  rewrite adjoint_id, ?left_unit; 
  easy.
Qed.

From ViCaR Require Import CategoryAutomation.

Open Scope matrix_scope.

Delimit Scope matrix_scope with mat.

Lemma test {n} : forall (zx : Matrix n n),
  ((λ_ n).(forward) × zx ≡ Matrix.I (S O) ⊗ zx × (ρ_ n).(forward)).
Proof.
  intros.
  simpl. to_Cat.
  replace (n+0)%nat with (1*n)%nat by lia.
  simpl forward.
  to_Cat.
  rewrite (left_unitor_cohere (f:=zx : (MxCategory.(morphism) n n)%Cat)).
  easy.
Qed.