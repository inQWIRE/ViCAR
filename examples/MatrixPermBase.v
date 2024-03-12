Require Export MatrixExampleBase.
Require Import ExamplesAutomation.

Lemma perm_mat_permutes_ei_r : forall n f k, (k < n)%nat ->
  (perm_mat n f) × (e_i k) = e_i (f k).
Proof.
  intros n f k Hk.
  rewrite <- mat_equiv_eq_iff by auto with wf_db.
  intros i j Hi Hj.
  replace j with O by lia; clear j Hj.
  unfold e_i.
  bdestruct (i =? f k).
  - unfold perm_mat, Mmult.
    bdestruct_one; [|lia].
    simpl.
    apply big_sum_unique.
    exists k.
    repeat split; [lia | bdestructΩ'simp | ].
    intros k' Hk' Hk'k'.
    bdestructΩ'simp.
  - simpl.
    unfold perm_mat, Mmult.
    rewrite big_sum_0_bounded; [easy|].
    intros k' Hk'.
    bdestructΩ'simp.
Qed.

Lemma basis_vector_equiv_e_i : forall n k, 
  basis_vector n k ≡ e_i k.
Proof.
  intros n k i j Hi Hj.
  unfold basis_vector, e_i.
  bdestructΩ'simp.
Qed.

Lemma basis_vector_eq_e_i : forall n k, (k < n)%nat ->
  basis_vector n k = e_i k.
Proof.
  intros n k Hk.
  rewrite <- mat_equiv_eq_iff by auto with wf_db.
  apply basis_vector_equiv_e_i.
Qed.

Lemma perm_mat_permutes_basis_vectors_r : forall n f k, (k < n)%nat ->
  (perm_mat n f) × (basis_vector n k) = e_i (f k).
Proof.
  intros n f k Hk.
  rewrite basis_vector_eq_e_i by easy.
  apply perm_mat_permutes_ei_r; easy.
Qed.

Lemma mat_equiv_of_equiv_on_ei : forall {n m} (A B : Matrix n m),
  (forall k, (k < m)%nat -> A × e_i k ≡ B × e_i k) ->
  A ≡ B.
Proof.
  intros n m A B Heq.
  intros i j Hi Hj.
  specialize (Heq j Hj).
  rewrite <- 2!(matrix_by_basis _ _ Hj) in Heq.
  specialize (Heq i O Hi ltac:(lia)).
  unfold get_vec in Heq.
  rewrite Nat.eqb_refl in Heq.
  easy.
Qed.

(* FIXME: Temp; only until pull mx stuff out of ZXExample *)
Lemma vector_eq_basis_comb : forall n (y : Vector n),
  WF_Matrix y -> 
  y = big_sum (G:=Vector n) (fun i => y i O .* @e_i n i) n.
Proof.
  intros n y Hwfy.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  replace j with O by lia; clear j Hj.
  symmetry.
  rewrite Msum_Csum.
  apply big_sum_unique.
  exists i.
  repeat split; try easy.
  - unfold ".*", e_i; bdestructΩ'simp.
  - intros l Hl Hnk.
  unfold ".*", e_i; bdestructΩ'simp.
Qed.

Lemma vector_equiv_basis_comb : forall n (y : Vector n),
  y ≡ big_sum (G:=Vector n) (fun i => y i O .* @e_i n i) n.
Proof.
  intros n y.
  intros i j Hi Hj.
  replace j with O by lia; clear j Hj.
  symmetry.
  rewrite Msum_Csum.
  apply big_sum_unique.
  exists i.
  repeat split; try easy.
  - unfold ".*", e_i; bdestructΩ'simp.
  - intros l Hl Hnk.
  unfold ".*", e_i; bdestructΩ'simp.
Qed.

Lemma perm_mat_permutes_matrix_r : forall n m f (A : Matrix n m),
  permutation n f ->
  (perm_mat n f) × A ≡ (fun i j => A (perm_inv n f i) j).
Proof.
  intros n m f A Hperm.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite Mmult_assoc, <- 2(matrix_by_basis _ _ Hk).
  rewrite (vector_equiv_basis_comb _ (get_vec _ _)).
  rewrite Mmult_Msum_distr_l.
  erewrite big_sum_eq_bounded.
  2: {
    intros l Hl.
    rewrite Mscale_mult_dist_r, perm_mat_permutes_ei_r by easy.
    reflexivity.
  }
  intros i j Hi Hj; replace j with O by lia; clear j Hj.
  rewrite Msum_Csum.
  unfold get_vec, scale, e_i.
  rewrite Nat.eqb_refl.
  apply big_sum_unique.
  exists (perm_inv n f i).
  repeat split; auto with perm_bdd_db.
  - rewrite (perm_inv_is_rinv_of_permutation n f Hperm i Hi), Nat.eqb_refl.
    bdestructΩ'simp.
  - intros j Hj Hjne.
    bdestruct (i =? f j); [|bdestructΩ'simp].
    exfalso; apply Hjne.
    apply (permutation_is_injective n f Hperm); auto with perm_bdd_db.
    rewrite (perm_inv_is_rinv_of_permutation n f Hperm i Hi); easy.
Qed.

Lemma perm_inv_of_rotr : forall n k, 
  forall i, (i < n)%nat ->
  perm_inv n (rotr n k) i = rotl n k i.
Proof.
  intros n k i Hi.
  assert (Hp : permutation n (rotr n k)) by auto with perm_db.
  apply (permutation_is_injective n _ Hp); auto with perm_bdd_db.
  pose proof (rotr_rotl_inv n k) as H.
  unfold compose in H.
  rewrite perm_inv_is_rinv_of_permutation; auto with perm_db.
  set (g:=(fun x : nat => rotr n k (rotl n k x))).
  fold g in H.
  enough (g i = idn i) by (unfold g in *; easy).
  rewrite H.
  easy.
Qed.

Lemma perm_mat_equiv_of_perm_eq : forall n f g, 
  (forall k, (k<n)%nat -> f k = g k) ->
  perm_mat n f ≡ perm_mat n g.
Proof.
  intros n f g Heq.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite 2!perm_mat_permutes_ei_r, Heq by easy.
  easy.
Qed.

Lemma perm_mat_equiv_of_perm_eq' : forall n m f g, n = m ->
  (forall k, (k<n)%nat -> f k = g k) ->
  perm_mat n f ≡ perm_mat m g.
Proof.
  intros; subst n; apply perm_mat_equiv_of_perm_eq; easy.
Qed.