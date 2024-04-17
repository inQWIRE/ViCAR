Require Import MatrixPermBase.
Require Import KronComm.
Require Export MatrixExampleBase.
Require Import ExamplesAutomation.
From ViCaR Require Import CategoryTypeclassCompatibility.


#[export] Instance MxCategory : Category nat := {
  morphism := Matrix;
  c_equiv := @mat_equiv;  (* fun m n => @eq (Matrix m n); *)
  compose := @Mmult;
  c_identity n := I n;
}.

#[export] Instance MxCategoryC : CategoryCoherence MxCategory := {
  c_equiv_rel := @mat_equiv_equivalence;

  compose_compat := fun n m o f g Hfg h i Hhi =>
    @Mmult_simplify_mat_equiv n m o f g h i Hfg Hhi;
  assoc := @Mmult_assoc_mat_equiv;

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

Obligation Tactic := idtac.

#[export, program] Instance MxKronMonoidalCategory 
  : MonoidalCategory MxCategory := {
  obj_tensor := Nat.mul;
  mor_tensor := @kron;
  mon_I := 1;
  
  associator := fun n m o => {|
  forward := (I (n * m * o) : Matrix (n * m * o) (n * (m * o)));
  reverse := (I (n * m * o) : Matrix (n * (m * o)) (n * m * o));
  (* id_A := ltac:(simpl; rewrite Nat.mul_assoc, Mmult_1_r_mat_eq; easy);
  id_B := ltac:(simpl; rewrite Nat.mul_assoc, Mmult_1_r_mat_eq; easy); *)
  |};
  
  left_unitor := fun n => {|
  forward := (I n : Matrix (1 * n) n);
  reverse := (I n : Matrix n (1 * n));
  (* id_A := ltac:(rewrite Nat.mul_1_l, Mmult_1_r_mat_eq; easy);
  id_B := ltac:(rewrite Nat.mul_1_l, Mmult_1_r_mat_eq; easy); *)
  |};

  right_unitor := fun n => {|
  forward := (I n : Matrix (n * 1) n);
  reverse := (I n : Matrix n (n * 1));
  (* id_A := ltac:(rewrite Nat.mul_1_r, Mmult_1_r_mat_eq; easy);
  id_B := ltac:(rewrite Nat.mul_1_r, Mmult_1_r_mat_eq; easy); *)
  |};
}.
Next Obligation.
  split;
  simpl; 
  rewrite Nat.mul_assoc, Mmult_1_r_mat_eq;
  easy.
Qed.
Next Obligation.
  split; 
  rewrite Nat.mul_1_l, Mmult_1_r_mat_eq; 
  easy.
Qed.
Next Obligation.
  split; 
  rewrite Nat.mul_1_r, Mmult_1_r_mat_eq; 
  easy.
Qed.

#[export, program] Instance MxKronMonoidalCategoryC :
  MonoidalCategoryCoherence MxKronMonoidalCategory := {}.
Next Obligation.
  intros; simpl in *.
  rewrite id_kron; easy.
Qed.
Next Obligation.
  simpl; intros.
  rewrite kron_mixed_product; easy.
Qed.
Next Obligation.
  simpl; intros.
  apply kron_mat_equiv_morph; easy.
Qed.
Next Obligation.
  intros; simpl in *.
  rewrite kron_assoc_mat_equiv.
  rewrite 2!Nat.mul_assoc, Mmult_1_r_mat_eq, Mmult_1_l_mat_eq.
  easy.
Qed.
Next Obligation.
  intros; simpl.
  rewrite kron_1_l_mat_equiv, 2!Nat.add_0_r, 
    Mmult_1_l_mat_eq, Mmult_1_r_mat_eq.
  easy.
Qed.
Next Obligation.
  intros; simpl.
  rewrite kron_1_r_mat_equiv, 2!Nat.mul_1_r, 
    Mmult_1_l_mat_eq, Mmult_1_r_mat_eq; easy. 
Qed.
Next Obligation.
  intros; simpl in *.
  (* change (B+0)%nat with (1*B)%nat. *)
  rewrite Nat.add_0_r, ?Nat.mul_assoc.
  rewrite Nat.mul_1_r.
  rewrite id_kron.
  rewrite Mmult_1_r_mat_eq.
  easy.
Qed.
Next Obligation.
  intros; simpl in *.
  rewrite ?Nat.mul_assoc.
  rewrite 2!id_kron, 2!Mmult_1_l_mat_eq.
  rewrite ?Nat.mul_assoc.
  easy.
Qed.

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
  

#[export] Instance MxBraidedMonoidal 
  : BraidedMonoidalCategory MxKronMonoidalCategory := {
  braiding := MxKronBraidingIsomorphism
}.

#[export, program] Instance MxBraidedMonoidalC 
  : BraidedMonoidalCategoryCoherence MxBraidedMonoidal := {
    (* braiding_natural *)
}.
Next Obligation.
  intros; simpl in *.
  rewrite (Nat.mul_comm B2 B1), (Nat.mul_comm A2 A1).
  rewrite (kron_comm_commutes_r_mat_equiv).
  easy.
Qed. 
Next Obligation.
  intros; simpl in *.
  rewrite 3!Nat.mul_assoc.
  rewrite Mmult_1_r_mat_eq, Mmult_1_r_mat_eq.
  rewrite Mmult_1_l_mat_eq.
  apply mx_hexagon_helper.
Qed.
Next Obligation.
  intros; simpl in *.
  rewrite 3!Nat.mul_assoc.
  rewrite Mmult_1_r_mat_eq, Mmult_1_r_mat_eq.
  rewrite Mmult_1_l_mat_eq.
  apply mx_hexagon_helper.
Qed.

#[export, program] Instance MxSymmetricMonoidal : 
  SymmetricMonoidalCategory MxBraidedMonoidal. 
Next Obligation.
 easy.
Qed.



From ViCaR Require Import CategoryAutomationCompatibility.

Open Scope matrix_scope.

Delimit Scope matrix_scope with mat.

Lemma test {n} : forall (zx : Matrix n n),
  ((λ_ n).(forward) × zx ≡ Matrix.I (S O) ⊗ zx × (ρ_ n).(forward)).
Proof.
  intros.
  simpl forward.
  to_Cat.
  rewrite left_unitor_cohere.
  easy.
Qed.