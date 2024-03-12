Require Import Setoid.

From VyZX Require Import CoreData.
From VyZX Require Import CoreRules.
From VyZX Require Import PermutationRules.
From ViCaR Require Export CategoryTypeclass.

Local Open Scope matrix_scope.

Lemma Msum_transpose : forall n m p f,
  (big_sum (G:=Matrix n m) f p) ⊤ = 
  big_sum (G:=Matrix n m) (fun i => (f i) ⊤) p.
Proof.
  intros.
  rewrite (big_sum_func_distr f transpose); easy.
Qed.

Ltac print_state :=
  try (match goal with | H : ?p |- _ => idtac H ":" p; fail end);
  idtac "---------------------------------------------------------";
  match goal with |- ?P => idtac P 
end.


Ltac is_C0 x :=
  assert (x = C0) by lca.

Ltac is_C1 x :=
  assert (x = C1) by lca.

Ltac print_C x :=
  tryif is_C0 x then idtac "0" else
  tryif is_C1 x then idtac "1" else idtac "X".

Ltac print_LHS_matU :=
  intros;
  (let i := fresh "i" in
  let j := fresh "j" in
  let Hi := fresh "Hi" in
  let Hj := fresh "Hj" in
  intros i j Hi Hj; try solve_end;
    repeat
    (destruct i as [| i]; [  | apply <- Nat.succ_lt_mono in Hi ];
    try solve_end); clear Hi;
    repeat
    (destruct j as [| j]; [  | apply <- Nat.succ_lt_mono in Hj ];
    try solve_end); clear Hj);
  match goal with |- ?x = ?y ?i ?j => autounfold with U_db; simpl; 
  match goal with
  | |- ?x = _ => idtac i; idtac j; print_C x; idtac ""
  end
end.

Definition kron_comm p q : Matrix (p*q) (p*q):=
  @make_WF (p*q) (p*q) (fun s t => 
  (* have blocks H_ij, p by q of them, and each is q by p *)
  let i := (s / q)%nat in let j := (t / p)%nat in 
  let k := (s mod q)%nat in let l := (t mod p) in
  (* let k := (s - q * i)%nat in let l := (t - p * t)%nat in *)
  if (i =? l) && (j =? k) then C1 else C0
  (* s/q =? t mod p /\ t/p =? s mod q *)
).

Lemma WF_kron_comm p q : WF_Matrix (kron_comm p q).
Proof. unfold kron_comm; auto with wf_db. Qed.
#[export] Hint Resolve WF_kron_comm : wf_db.

(* Lemma test_kron : kron_comm 2 3 = Matrix.Zero.
Proof.
  apply mat_equiv_eq; unfold kron_comm; auto with wf_db.
  print_LHS_matU. 
*)

Lemma kron_comm_transpose : forall p q, 
  (kron_comm p q) ⊤ = kron_comm q p.
Proof.
  intros p q.
  apply mat_equiv_eq; auto with wf_db.
  1: rewrite Nat.mul_comm; apply WF_kron_comm.
  intros i j Hi Hj.
  unfold kron_comm, transpose, make_WF.
  rewrite andb_comm, Nat.mul_comm.
  rewrite (andb_comm (_ =? _)).
  easy.
Qed.

Lemma kron_comm_1_r : forall p, 
  (kron_comm p 1) = Matrix.I p.
Proof.
  intros p.
  apply mat_equiv_eq; [|rewrite 1?Nat.mul_1_r|]; auto with wf_db.
  intros s t Hs Ht.
  unfold kron_comm.
  unfold make_WF.
  unfold Matrix.I.
  rewrite Nat.mul_1_r, Nat.div_1_r, Nat.mod_1_r, Nat.div_small, Nat.mod_small by lia. 
  bdestructΩ'.
Qed.

Lemma kron_comm_1_l : forall p, 
  (kron_comm 1 p) = Matrix.I p.
Proof.
  intros p.
  apply mat_equiv_eq; [|rewrite 1?Nat.mul_1_l|]; auto with wf_db.
  intros s t Hs Ht.
  unfold kron_comm.
  unfold make_WF.
  unfold Matrix.I.
  rewrite Nat.mul_1_l, Nat.div_1_r, Nat.mod_1_r, Nat.div_small, Nat.mod_small by lia. 
  bdestructΩ'.
Qed.

Definition mx_to_vec {n m} (A : Matrix n m) : Vector (n*m) :=
  make_WF (fun i j => A (i mod n)%nat (i / n)%nat
  (* Note: goes columnwise. Rowwise would be:
  make_WF (fun i j => A (i / m)%nat (i mod n)%nat
  *)
).

Lemma WF_mx_to_vec {n m} (A : Matrix n m) : WF_Matrix (mx_to_vec A).
Proof. unfold mx_to_vec; auto with wf_db. Qed.
#[export] Hint Resolve WF_mx_to_vec : wf_db.

(* Compute vec_to_list (mx_to_vec (Matrix.I 2)). *)
From Coq Require Import ZArith.
Ltac Zify.zify_post_hook ::= PreOmega.Z.div_mod_to_equations.

Lemma kron_comm_vec_helper : forall i p q, (i < p * q)%nat ->
  (p * (i mod q) + i / q < p * q)%nat.
Proof.
  intros i p q.
  intros Hi.
  assert (i / q < p)%nat by (apply Nat.div_lt_upper_bound; lia).
  destruct p; [lia|];
  destruct q; [lia|].
  enough (S p * (i mod S q) <= S p * q)%nat by lia.
  apply Nat.mul_le_mono; [lia | ].
  pose proof (Nat.mod_upper_bound i (S q) ltac:(easy)).
  lia.
Qed.

Lemma mx_to_vec_additive {n m} (A B : Matrix n m) :
  mx_to_vec (A .+ B) = mx_to_vec A .+ mx_to_vec B.
Proof.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  replace j with O by lia; clear dependent j.
  unfold mx_to_vec, make_WF, Mplus.
  bdestructΩ'.
Qed.

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

Lemma if_mult_and (b c : bool) :
  (if b then C1 else C0) * (if c then C1 else C0) =
  if (b && c) then C1 else C0.
Proof.
  destruct b; destruct c; lca.
Qed.

Lemma kron_comm_vec : forall p q (A : Matrix p q),
  kron_comm p q × mx_to_vec A = mx_to_vec (A ⊤).
Proof.
  intros p q A.
  apply mat_equiv_eq; [|rewrite Nat.mul_comm|]; auto with wf_db.
  intros i j Hi Hj.
  replace j with O by lia; clear dependent j.
  unfold transpose, mx_to_vec, kron_comm, make_WF, Mmult.
  rewrite (Nat.mul_comm q p). 
  replace_bool_lia (i <? p * q) true.
  replace_bool_lia (0 <? 1) true.
  simpl.
  erewrite big_sum_eq_bounded.
  2: {
  intros k Hk.
  rewrite andb_true_r, <- andb_if.
  replace_bool_lia (k <? p * q) true.
  simpl.
  rewrite if_mult_dist_r.
  replace ((i / q =? k mod p) && (k / p =? i mod q)) with 
    (k =? p * (i mod q) + (i/q));
  [reflexivity|]. (* Set this as our new Σ body; NTS the equality we claimed*)
  rewrite eq_iff_eq_true.
  rewrite andb_true_iff, 3!Nat.eqb_eq.
  split.
  - intros ->.
    destruct p; [lia|].
    destruct q; [lia|].
    split.
    + rewrite Nat.add_comm, Nat.mul_comm.
    rewrite Nat.mod_add by easy.
    rewrite Nat.mod_small; [lia|].
    apply Nat.div_lt_upper_bound; lia.
    + rewrite Nat.mul_comm, Nat.div_add_l by easy.
    rewrite Nat.div_small; [lia|].
    apply Nat.div_lt_upper_bound; lia.
  - intros [Hmodp Hdivp].
    rewrite (Nat.div_mod_eq k p).
    lia.
  }
  apply big_sum_unique.
  exists (p * (i mod q) + i / q)%nat; repeat split;
  [apply kron_comm_vec_helper; easy | rewrite Nat.eqb_refl | intros; bdestructΩ'].
  destruct p; [lia|];
  destruct q; [lia|].
  f_equal.
  - rewrite Nat.add_comm, Nat.mul_comm, Nat.mod_add, Nat.mod_small; try easy.
  apply Nat.div_lt_upper_bound; lia.
  - rewrite Nat.mul_comm, Nat.div_add_l by easy. 
  rewrite Nat.div_small; [lia|].
  apply Nat.div_lt_upper_bound; lia.
Qed.

Lemma kron_comm_ei_kron_ei_sum : forall p q, 
  kron_comm p q = 
  big_sum (G:=Square (p*q)) (fun i => big_sum (G:=Square (p*q)) (fun j =>
  (@e_i p i ⊗ @e_i q j) × ((@e_i q j ⊗ @e_i p i) ⊤))
   q) p.
Proof.
  intros p q.
  apply mat_equiv_eq; auto with wf_db.
  1: apply WF_Msum; intros; apply WF_Msum; intros; 
   rewrite Nat.mul_comm; apply WF_mult;
   auto with wf_db; rewrite Nat.mul_comm;
   auto with wf_db.
  intros i j Hi Hj.
  rewrite Msum_Csum.
  erewrite big_sum_eq_bounded.
  2: {
  intros k Hk.
  rewrite Msum_Csum.
  erewrite big_sum_eq_bounded.
  2: {
  intros l Hl.
  unfold Mmult, kron, transpose, e_i.
  erewrite big_sum_eq_bounded.
  2: {
  intros m Hm.
  (* replace m with O by lia. *)
  rewrite Nat.div_1_r, Nat.mod_1_r.
  replace_bool_lia (m =? 0) true; rewrite 4!andb_true_r.
  rewrite 3!if_mult_and.
  match goal with 
  |- context[if ?b then _ else _] => 
    replace b with ((i =? k * q + l) && (j =? l * p + k))
  end.
  1: reflexivity. (* set our new function *)
  clear dependent m.
  rewrite eq_iff_eq_true, 8!andb_true_iff, 
    6!Nat.eqb_eq, 4!Nat.ltb_lt.
  split.
  - intros [Hieq Hjeq].
    subst i j.
    rewrite 2!Nat.div_add_l, Nat.div_small, Nat.add_0_r by lia.
    rewrite Nat.add_comm, Nat.mod_add, Nat.mod_small, 
    Nat.div_small, Nat.add_0_r by lia.
    rewrite Nat.add_comm, Nat.mod_add, Nat.mod_small by lia.
    easy.
  - intros [[[] []] [[] []]].
    split.
    + rewrite (Nat.div_mod_eq i q) by lia; lia.
    + rewrite (Nat.div_mod_eq j p) by lia; lia.
  }
  simpl; rewrite Cplus_0_l.
  reflexivity.
  }
  apply big_sum_unique.
  exists (i mod q).
  split; [|split].
  - apply Nat.mod_upper_bound; lia.
  - reflexivity.
  - intros l Hl Hnmod.
  bdestructΩ'.
  exfalso; apply Hnmod.
  rewrite Nat.add_comm, Nat.mod_add, Nat.mod_small by lia; lia.
  }
  symmetry.
  apply big_sum_unique.
  exists (j mod p).
  repeat split.
  - apply Nat.mod_upper_bound; lia.
  - unfold kron_comm, make_WF.
  replace_bool_lia (i <? p * q) true.
  replace_bool_lia (j <? p * q) true.
  simpl.
  match goal with
  |- (if ?b then _ else _) = (if ?c then _ else _) =>
    enough (b = c) by bdestructΩ'
  end.
  rewrite eq_iff_eq_true, 2!andb_true_iff, 4!Nat.eqb_eq.
  split.
  + intros [Hieq Hjeq].
    split; [rewrite Hieq | rewrite Hjeq];
    rewrite Hieq, Nat.div_add_l by lia;
    (rewrite Nat.div_small; [lia|]);
    apply Nat.mod_upper_bound; lia.
  + intros [Hidiv Hjdiv].
    rewrite (Nat.div_mod_eq i q) at 1 by lia.
    rewrite (Nat.div_mod_eq j p) at 2 by lia.
    lia.
  - intros k Hk Hkmod.
  bdestructΩ'.
  exfalso; apply Hkmod.
  rewrite Nat.add_comm, Nat.mod_add, Nat.mod_small by lia; lia.
Qed.

Lemma kron_comm_ei_kron_ei_sum' : forall p q, 
  kron_comm p q = 
  big_sum (G:=Square (p*q)) (fun ij =>
  let i := (ij / q)%nat in let j := (ij mod q) in
  ((@e_i p i ⊗ @e_i q j) × ((@e_i q j ⊗ @e_i p i) ⊤))) (p*q).
Proof.
  intros p q.
  rewrite kron_comm_ei_kron_ei_sum, big_sum_double_sum, Nat.mul_comm.
  reflexivity.
Qed.

Lemma div_eq_iff : forall a b c, b <> O ->
  (a / b)%nat = c <-> (b * c <= a /\ a < b * (S c))%nat.
Proof.
  intros a b c Hb.
  split.
  intros Hadivb.
  split;
  subst c.
  etransitivity; [
  apply Nat.div_mul_le, Hb |].
  rewrite Nat.mul_comm, Nat.div_mul; easy.
  apply Nat.mul_succ_div_gt, Hb.
  intros [Hge Hlt].
  symmetry.
  apply (Nat.div_unique _ _ _ (a - b*c)); [lia|].
  lia.
Qed.

Lemma kron_e_i_transpose_l : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  (@e_i n k)⊤ ⊗ A = (fun i j =>
  if (i <? m) && (j / o =? k) then A i (j - k * o)%nat else 0).
Proof.
  intros k n m o A Hk Ho Hm.
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.
  unfold kron, transpose, e_i.
  rewrite if_mult_dist_r.
  bdestruct (i <? m).
  - rewrite (Nat.div_small i m),
  (Nat.mod_small i m), Nat.eqb_refl, andb_true_r, andb_true_l by easy.
  replace ((j / o =? k) && (j / o <? n)) with (j / o =? k) by bdestructΩ'.
  (*mark*) bdestruct_one; [|easy].
  rewrite mod_eq_sub; f_equal;
  lia.
  - bdestructΩ'.
  rewrite Nat.div_small_iff in *; lia.
Qed.

Lemma kron_e_i_l : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  (@e_i n k) ⊗ A = (fun i j =>
  if (j <? o) && (i / m =? k) then A (i - k * m)%nat j else 0).
Proof.
  intros k n m o A Hk Ho Hm.
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.
  unfold kron, transpose, e_i.
  rewrite if_mult_dist_r.
  bdestruct (j <? o).
  - rewrite (Nat.div_small j o),
  (Nat.mod_small j o), Nat.eqb_refl, andb_true_r, andb_true_l by easy.
  replace ((i / m =? k) && (i / m <? n)) with (i / m =? k) by bdestructΩ'.
  (*mark*) bdestruct_one; [|easy].
  rewrite mod_eq_sub; f_equal;
  lia.
  - bdestructΩ'.
  rewrite Nat.div_small_iff in *; lia.
Qed.

Lemma kron_e_i_transpose_l' : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  (@e_i n k)⊤ ⊗ A = (fun i j =>
  if (i <? m) && (k * o <=? j) && (j <? (S k) * o) then A i (j - k * o)%nat else 0).
Proof.
  intros k n m o A Hk Ho Hm.
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.
  unfold kron, transpose, e_i.
  rewrite if_mult_dist_r.
  bdestruct (i <? m).
  - rewrite (Nat.div_small i m), Nat.eqb_refl, andb_true_r, andb_true_l by easy.
  rewrite Nat.mod_small by easy.
  replace ((j / o =? k) && (j / o <? n)) with ((k * o <=? j) && (j <? S k * o)).
  + do 2 (*mark*) bdestruct_one; simpl; try easy.
    destruct o; [lia|].
    f_equal.
    rewrite mod_eq_sub, Nat.mul_comm.
    do 2 f_equal.
    rewrite div_eq_iff; lia.
  + rewrite eq_iff_eq_true, 2!andb_true_iff, Nat.eqb_eq, 2!Nat.ltb_lt, Nat.leb_le.
    assert (Hrw: ((j / o)%nat = k /\ (j / o < n)%nat) <-> ((j/o)%nat=k)) by lia;
    rewrite Hrw; clear Hrw.
    symmetry.
    rewrite div_eq_iff by lia.
    lia.
  - replace (i / m =? 0) with false.
  rewrite andb_false_r; easy.
  symmetry.
  rewrite Nat.eqb_neq.
  rewrite Nat.div_small_iff; lia.
Qed.

Lemma kron_e_i_l' : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  (@e_i n k) ⊗ A = (fun i j =>
  if (j <? o) && (k * m <=? i) && (i <? (S k) * m) then A (i - k * m)%nat j else 0).
Proof.
  intros k n m o A Hk Ho Hm.
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.
  unfold kron, e_i.
  rewrite if_mult_dist_r.
  bdestruct (j <? o).
  - rewrite (Nat.div_small j o), Nat.eqb_refl, andb_true_r, andb_true_l by easy.
  rewrite (Nat.mod_small j o) by easy.
  replace ((i / m =? k) && (i / m <? n)) with ((k * m <=? i) && (i <? S k * m)).
  + do 2 (*mark*) bdestruct_one; simpl; try easy.
    destruct m; [lia|].
    f_equal.
    rewrite mod_eq_sub, Nat.mul_comm.
    do 2 f_equal.
    rewrite div_eq_iff; lia.
  + rewrite eq_iff_eq_true, 2!andb_true_iff, Nat.eqb_eq, 2!Nat.ltb_lt, Nat.leb_le.
    assert (Hrw: ((i/m)%nat=k/\(i/m<n)%nat) <-> ((i/m)%nat=k)) by lia;
    rewrite Hrw; clear Hrw.
    symmetry.
    rewrite div_eq_iff by lia.
    lia.
  - replace (j / o =? 0) with false.
  rewrite andb_false_r; easy.
  symmetry.
  rewrite Nat.eqb_neq.
  rewrite Nat.div_small_iff; lia.
Qed.

Lemma kron_e_i_r : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  A ⊗ (@e_i n k) = (fun i j =>
  if (i mod n =? k) then A (i / n)%nat j else 0).
Proof.
  intros k n m o A Hk Ho Hm.
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.
  unfold kron, e_i.
  rewrite if_mult_dist_l, Nat.div_1_r.
  rewrite Nat.mod_1_r, Nat.eqb_refl, andb_true_r.
  replace (i mod n <? n) with true;
  [rewrite andb_true_r; easy |].
  symmetry; rewrite Nat.ltb_lt.
  apply Nat.mod_upper_bound; lia.
Qed.

Lemma kron_e_i_transpose_r : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  A ⊗ (@e_i n k) ⊤ = (fun i j =>
  if (j mod n =? k) then A i (j / n)%nat else 0).
Proof.
  intros k n m o A Hk Ho Hm.
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.
  unfold kron, transpose, e_i.
  rewrite if_mult_dist_l, Nat.div_1_r.
  rewrite Nat.mod_1_r, Nat.eqb_refl, andb_true_r.
  replace (j mod n <? n) with true;
  [rewrite andb_true_r; easy |].
  symmetry; rewrite Nat.ltb_lt.
  apply Nat.mod_upper_bound; lia.
Qed.

Lemma ei_kron_I_kron_ei : forall m n k, (k < n)%nat -> m <> O ->
  (@e_i n k) ⊤ ⊗ (Matrix.I m) ⊗ (@e_i n k) =
  (fun i j => if (i mod n =? k) && (j / m =? k)%nat 
  && (i / n =? j - k * m) && (i / n <? m)
  then 1 else 0).
Proof.
  intros m n k Hk Hm.
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.
  rewrite kron_e_i_transpose_l by easy.
  rewrite kron_e_i_r; try lia;
  [| rewrite Nat.mul_eq_0; lia].
  unfold Matrix.I.
  rewrite <- 2!andb_if.
  (*mark*) bdestruct_one; [
  rewrite 2!andb_true_r, andb_true_l | rewrite 4!andb_false_r; easy
  ].
  easy.
Qed.

Lemma kron_comm_kron_form_sum : forall m n,
  kron_comm m n = big_sum (G:=Square (m*n)) (fun j =>
  (@e_i n j) ⊤ ⊗ (Matrix.I m) ⊗ (@e_i n j)) n.
Proof.
  intros m n.
  apply mat_equiv_eq; auto with wf_db.
  1: apply WF_Msum; intros; apply WF_kron; auto with wf_db arith.
  intros i j Hi Hj.
  rewrite Msum_Csum.
  erewrite big_sum_eq_bounded.
  2: {
  intros ij Hij.
  rewrite ei_kron_I_kron_ei by lia.
  reflexivity.
  }
  unfold kron_comm, make_WF.
  replace_bool_lia (i <? m * n) true.
  replace_bool_lia (j <? m * n) true.
  simpl.
  replace (i / n <? m) with true by (
  symmetry; rewrite Nat.ltb_lt; apply Nat.div_lt_upper_bound; lia).
  (*mark*) bdestruct_one; [(*mark*) bdestruct_one|]; simpl; symmetry; [
  apply big_sum_unique;
  exists (j / m)%nat;
  split; [ apply Nat.div_lt_upper_bound; lia | ];
  split; [rewrite (Nat.mul_comm (j / m) m), <- mod_eq_sub by lia; bdestructΩ'|];
  intros k Hk Hkne; bdestructΩ'
  | |];
  (rewrite big_sum_0; [easy|]; intros k; bdestructΩ').
  pose proof (mod_eq_sub j m); lia.
Qed.

Lemma kron_comm_kron_form_sum' : forall m n,
  kron_comm m n = big_sum (G:=Square (m*n)) (fun i =>
  (@e_i m i) ⊗ (Matrix.I n) ⊗ (@e_i m i)⊤) m.
Proof.
  intros.
  rewrite <- (kron_comm_transpose n m).
  rewrite (kron_comm_kron_form_sum n m).
  rewrite Msum_transpose.
  apply big_sum_eq_bounded.
  intros k Hk.
  rewrite Nat.mul_1_l.
  pose proof (kron_transpose _ _ _ _ ((@e_i m k) ⊤ ⊗ Matrix.I n) (@e_i m k)) as H;
  rewrite Nat.mul_1_l, Nat.mul_1_r in H;
  rewrite (Nat.mul_comm n m), H in *; clear H.
  pose proof (kron_transpose _ _ _ _ ((@e_i m k) ⊤) (Matrix.I n)) as H;
  rewrite Nat.mul_1_l in H; 
  rewrite H; clear H.
  rewrite transpose_involutive, id_transpose_eq; easy.
Qed.

Lemma e_i_dot_is_component : forall p k (x : Vector p),
  (k < p)%nat -> WF_Matrix x ->
  (@e_i p k) ⊤ × x = x k O .* Matrix.I 1.
Proof.
  intros p k x Hk HWF.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj;
  replace i with O by lia;
  replace j with O by lia;
  clear i Hi;
  clear j Hj.
  unfold Mmult, transpose, scale, e_i, Matrix.I.
  bdestructΩ'.
  rewrite Cmult_1_r.
  apply big_sum_unique.
  exists k.
  split; [easy|].
  bdestructΩ'.
  rewrite Cmult_1_l.
  split; [easy|].
  intros l Hl Hkl.
  bdestructΩ'; lca.
Qed.

Lemma kron_e_i_e_i : forall p q k l,
  (k < p)%nat -> (l < q)%nat -> 
  @e_i q l ⊗ @e_i p k = @e_i (p*q) (l*p + k).
Proof.
  intros p q k l Hk Hl.
  apply functional_extensionality; intro i.
  apply functional_extensionality; intro j.
  unfold kron, e_i.
  rewrite Nat.mod_1_r, Nat.div_1_r.
  rewrite if_mult_and.
  lazymatch goal with
  |- (if ?b then _ else _) = (if ?c then _ else _) =>
  enough (H : b = c) by (rewrite H; easy)
  end.
  rewrite Nat.eqb_refl, andb_true_r.
  destruct (j =? 0); [|rewrite 2!andb_false_r; easy].
  rewrite 2!andb_true_r.
  rewrite eq_iff_eq_true, 4!andb_true_iff, 3!Nat.eqb_eq, 3!Nat.ltb_lt.
  split.
  - intros [[] []].
  rewrite (Nat.div_mod_eq i p).
  split; nia.
  - intros [].
  subst i.
  rewrite Nat.div_add_l, Nat.div_small, Nat.add_0_r,
  Nat.add_comm, Nat.mod_add, Nat.mod_small by lia.
  easy.
Qed.

Lemma kron_eq_sum : forall p q (x : Vector q) (y : Vector p),
  WF_Matrix x -> WF_Matrix y ->
  y ⊗ x = big_sum (fun ij =>
  let i := (ij / q)%nat in let j := ij mod q in
  (x j O * y i O) .* (@e_i p i ⊗ @e_i q j)) (p * q).
Proof.
  intros p q x y Hwfx Hwfy.
  
  erewrite big_sum_eq_bounded.
  2: {
  intros ij Hij.
  simpl.
  rewrite (@kron_e_i_e_i q p) by 
    (try apply Nat.mod_upper_bound; try apply Nat.div_lt_upper_bound; lia).
  rewrite (Nat.mul_comm (ij / q) q).
  rewrite <- (Nat.div_mod_eq ij q).
  reflexivity.
  }
  apply mat_equiv_eq; [|rewrite Nat.mul_comm|]; auto with wf_db.
  intros i j Hi Hj.
  replace j with O by lia; clear j Hj.
  simpl.
  rewrite Msum_Csum.
  symmetry.
  apply big_sum_unique.
  exists i.
  split; [lia|].
  unfold e_i; split.
  - unfold scale, kron; bdestructΩ'.
  rewrite Cmult_1_r, Cmult_comm.
  easy.
  - intros j Hj Hij.
  unfold scale, kron; bdestructΩ'.
  rewrite Cmult_0_r.
  easy.
Qed.

Lemma kron_comm_commutes_vectors_l : forall p q (x : Vector q) (y : Vector p),
  WF_Matrix x -> WF_Matrix y ->
  kron_comm p q × (x ⊗ y) = (y ⊗ x).
Proof.
  intros p q x y Hwfx Hwfy.
  rewrite kron_comm_ei_kron_ei_sum', Mmult_Msum_distr_r.
  erewrite big_sum_eq_bounded.
  2: {
  intros k Hk.
  simpl.
  match goal with 
  |- (?A × ?B) × ?C = _ => 
  assert (Hassoc: (A × B) × C = A × (B × C)) by apply Mmult_assoc
  end.
  simpl in Hassoc.
  rewrite (Nat.mul_comm q p) in *.
  rewrite Hassoc. clear Hassoc.
  pose proof (kron_transpose _ _ _ _ (@e_i q (k mod q)) (@e_i p (k / q))) as Hrw;
  rewrite (Nat.mul_comm q p) in Hrw;
  simpl in Hrw; rewrite Hrw; clear Hrw.
  pose proof (kron_mixed_product ((e_i (k mod q)) ⊤) ((e_i (k / q)) ⊤) x y) as Hrw;
  rewrite (Nat.mul_comm q p) in Hrw;
  simpl in Hrw; rewrite Hrw; clear Hrw.
  rewrite 2!e_i_dot_is_component; [|
  apply Nat.div_lt_upper_bound; lia |
  easy |
  apply Nat.mod_upper_bound; lia |
  easy].
  rewrite Mscale_kron_dist_l, Mscale_kron_dist_r, Mscale_assoc.
  rewrite kron_1_l, Mscale_mult_dist_r, Mmult_1_r by auto with wf_db.
  reflexivity.
  }
  rewrite <- kron_eq_sum; easy.
Qed.

Lemma kron_basis_vector_basis_vector : forall p q k l,
  (k < p)%nat -> (l < q)%nat -> 
  basis_vector q l ⊗ basis_vector p k = basis_vector (p*q) (l*p + k).
Proof.
  intros p q k l Hk Hl.
  apply functional_extensionality; intros i.
  apply functional_extensionality; intros j.
  unfold kron, basis_vector.
  rewrite Nat.mod_1_r, Nat.div_1_r, Nat.eqb_refl, andb_true_r, if_mult_and.
  bdestructΩ';
  try pose proof (Nat.div_mod_eq i p);
  try nia.
  rewrite Nat.div_add_l, Nat.div_small in * by lia.
  lia.
Qed.

Lemma kron_extensionality : forall n m s t (A B : Matrix (n*m) (s*t)),
  WF_Matrix A -> WF_Matrix B ->
  (forall (x : Vector s) (y :Vector t), 
  WF_Matrix x -> WF_Matrix y ->
  A × (x ⊗ y) = B × (x ⊗ y)) ->
  A = B.
Proof.
  intros b n s t A B HwfA HwfB Hext.
  apply equal_on_basis_vectors_implies_equal; try easy.
  intros i Hi.
  
  pose proof (Nat.div_lt_upper_bound i t s ltac:(lia) ltac:(lia)).
  pose proof (Nat.mod_upper_bound i s ltac:(lia)).
  pose proof (Nat.mod_upper_bound i t ltac:(lia)).

  specialize (Hext (basis_vector s (i / t)) (basis_vector t (i mod t))
  ltac:(apply basis_vector_WF; easy)
  ltac:(apply basis_vector_WF; easy)
  ).
  rewrite (kron_basis_vector_basis_vector t s) in Hext by lia.

  simpl in Hext.
  rewrite (Nat.mul_comm (i/t) t), <- (Nat.div_mod_eq i t) in Hext.
  rewrite (Nat.mul_comm t s) in Hext. easy.
Qed.

Lemma kron_comm_commutes : forall n s m t 
  (A : Matrix n s) (B : Matrix m t),
  WF_Matrix A -> WF_Matrix B ->
  kron_comm m n × (A ⊗ B) × (kron_comm s t) = (B ⊗ A).
Proof.
  intros n s m t A B HwfA HwfB.
  apply (kron_extensionality _ _ t s); [| 
  apply WF_kron; try easy; lia |].
  rewrite (Nat.mul_comm t s); apply WF_mult; auto with wf_db;
  apply WF_mult; auto with wf_db;
  rewrite Nat.mul_comm; auto with wf_db.
  (* rewrite Nat.mul_comm; apply WF_mult; [rewrite Nat.mul_comm|auto with wf_db];
  apply WF_mult; auto with wf_db; rewrite Nat.mul_comm; auto with wf_db. *)
  intros x y Hwfx Hwfy.
  (* simpl. *)
  (* Search "assoc" in Matrix. *)
  rewrite (Nat.mul_comm s t).
  rewrite (Mmult_assoc (_ × _)).
  rewrite (Nat.mul_comm t s).
  rewrite kron_comm_commutes_vectors_l by easy.
  rewrite Mmult_assoc, (Nat.mul_comm m n).
  rewrite kron_mixed_product.
  rewrite (Nat.mul_comm n m), kron_comm_commutes_vectors_l by (auto with wf_db).
  rewrite <- kron_mixed_product.
  f_equal; lia.
Qed.

Lemma commute_kron : forall n s m t 
  (A : Matrix n s) (B : Matrix m t),
  WF_Matrix A -> WF_Matrix B ->
  (A ⊗ B) = kron_comm n m × (B ⊗ A) × (kron_comm t s).
Proof.
  intros n s m t A B HA HB. 
  rewrite (kron_comm_commutes m t n s B A HB HA); easy.
Qed.

#[export] Hint Extern 4 (WF_Matrix (@Mmult ?m ?n ?o ?A ?B)) => (
  match type of A with Matrix ?m' ?n' =>
  match type of B with Matrix ?n'' ?o'' =>
  let Hm' := fresh "Hm'" in let Hn' := fresh "Hn'" in
  let Hn'' := fresh "Hn''" in let Ho'' := fresh "Hoo'" in
  assert (Hm' : m = m') by lia;
  assert (Hn' : n = n') by lia;
  assert (Hn'' : n = n'') by lia;
  assert (Ho' : o = o'') by lia;
  replace (@Mmult m n o A B) with (@Mmult m' n' o A B) 
    by (first [try (rewrite Hm' at 1); try (rewrite Hn' at 1); reflexivity | f_equal; lia]);
  apply WF_mult; [
    auto with wf_db |
    apply WF_Matrix_dim_change;
    auto with wf_db
  ]
  end end) : wf_db.

Lemma kron_comm_mul_inv : forall p q,
  kron_comm p q × kron_comm q p = Matrix.I _.
Proof.
  intros p q.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  unfold Mmult, kron_comm, make_WF.
  erewrite big_sum_eq_bounded.
  2: {
  intros k Hk.
  rewrite <- 2!andb_if, if_mult_and.
  replace_bool_lia (k <? p * q) true;
  replace_bool_lia (i <? p * q) true;
  replace_bool_lia (j <? q * p) true;
  replace_bool_lia (k <? q * p) true.
  rewrite 2!andb_true_l.
  match goal with |- context[if ?b then _ else _] =>
  replace b with ((i =? j) && (k =? (i mod q) * p + (j/q)))
  end;
  [reflexivity|].
  rewrite eq_iff_eq_true, 4!andb_true_iff, 6!Nat.eqb_eq.
  split.
  - intros [? ?]; subst.
  destruct p; [easy|destruct q;[lia|]].
  assert (j / S q < S p)%nat by (apply Nat.div_lt_upper_bound; lia).
  rewrite Nat.div_add_l, (Nat.div_small (j / (S q))), Nat.add_0_r by easy.
  rewrite Nat.add_comm, Nat.mod_add, Nat.mod_small by easy.
  easy.
  - intros [[Hiqkp Hkpiq] [Hkpjq Hjqkp]].
  split.
  + rewrite (Nat.div_mod_eq i q), (Nat.div_mod_eq j q).
    lia.
  + rewrite (Nat.div_mod_eq k p).
    lia.
  }
  bdestruct (i =? j).
  - subst.
  apply big_sum_unique.
  exists ((j mod q) * p + (j/q))%nat.
  split; [|split].
  + rewrite Nat.mul_comm. apply kron_comm_vec_helper; easy.
  + unfold Matrix.I.
    rewrite Nat.eqb_refl; bdestructΩ'.
  + intros; bdestructΩ'.
  - unfold Matrix.I.
  replace_bool_lia (i =? j) false.
  rewrite andb_false_l.
  rewrite big_sum_0; [easy|].
  intros; rewrite andb_false_l; easy.
Qed.

Lemma kron_comm_mul_transpose_r : forall p q,
  kron_comm p q × (kron_comm p q) ⊤ = Matrix.I _.
Proof.
  intros p q.
  rewrite (kron_comm_transpose p q).
  apply kron_comm_mul_inv.
Qed.

Lemma kron_comm_mul_transpose_l : forall p q,
  (kron_comm p q) ⊤ × kron_comm p q = Matrix.I _.
Proof.
  intros p q.
  rewrite <- (kron_comm_transpose q p).
  rewrite (Nat.mul_comm p q).
  rewrite (transpose_involutive _ _ (kron_comm q p)).
  apply kron_comm_mul_transpose_r.
Qed.

Lemma kron_comm_commutes_l : forall n s m t 
  (A : Matrix n s) (B : Matrix m t),
  WF_Matrix A -> WF_Matrix B ->
  kron_comm m n × (A ⊗ B) = (B ⊗ A) × (kron_comm t s).
Proof.
  intros n s m t A B HwfA HwfB.
  match goal with |- ?A = ?B =>
  rewrite <- (Mmult_1_r _ _ A), <- (Mmult_1_r _ _ B)  ; auto with wf_db
  end.
  rewrite (Nat.mul_comm t s).
  rewrite <- (kron_comm_mul_transpose_r), <- 2!Mmult_assoc.
  rewrite (kron_comm_commutes n s m t) by easy.
  apply Mmult_simplify; [|easy].
  rewrite Mmult_assoc.
  rewrite (Nat.mul_comm s t), (kron_comm_mul_inv t s), Mmult_1_r by auto with wf_db.
  easy.
Qed.

Lemma kron_comm_commutes_r : forall n s m t 
  (A : Matrix n s) (B : Matrix m t),
  WF_Matrix A -> WF_Matrix B ->
  (A ⊗ B) × kron_comm s t = (kron_comm n m) × (B ⊗ A).
Proof.
  intros n s m t A B HA HB.
  rewrite kron_comm_commutes_l; easy.
Qed.
  


(* Lemma kron_comm_commutes_r : forall n s m t 
  (A : Matrix n s) (B : Matrix m t),
  WF_Matrix A -> WF_Matrix B ->
  kron_comm m n × (A ⊗ B) = (B ⊗ A) × (kron_comm t s).
Proof.
  intros n s m t A B HwfA HwfB.
  match goal with |- ?A = ?B =>
  rewrite <- (Mmult_1_r _ _ A), <- (Mmult_1_r _ _ B)  ; auto with wf_db
  end.
  rewrite (Nat.mul_comm t s).
  rewrite <- (kron_comm_mul_transpose_r), <- 2!Mmult_assoc.
  rewrite (kron_comm_commutes n s m t) by easy.
  apply Mmult_simplify; [|easy].
  rewrite Mmult_assoc.
  rewrite (Nat.mul_comm s t), (kron_comm_mul_inv t s), Mmult_1_r by auto with wf_db.
  easy.
Qed. *)




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
  - unfold ".*", e_i; bdestructΩ'; lca.
  - intros l Hl Hnk.
  unfold ".*", e_i; bdestructΩ'; lca.
Qed.

Lemma kron_vecT_matrix_vec : forall m n o p
  (P : Matrix m o) (y : Vector n) (z : Vector p),
  WF_Matrix y -> WF_Matrix z -> WF_Matrix P ->
  (z⊤) ⊗ P ⊗ y = @Mmult (m*n) (m*n) (o*p) (kron_comm m n) ((y × (z⊤)) ⊗ P).
Proof.
  intros m n o p P y z Hwfy Hwfz HwfP.
  match goal with |- ?A = ?B =>
  rewrite <- (Mmult_1_l _ _ A) ; auto with wf_db
  end.
  rewrite Nat.mul_1_l.
  rewrite <- (kron_comm_mul_transpose_r), Mmult_assoc at 1.
  rewrite Nat.mul_1_r, (Nat.mul_comm o p).
  apply Mmult_simplify; [easy|].
  rewrite kron_comm_kron_form_sum.
  rewrite Msum_transpose.
  rewrite Mmult_Msum_distr_r.
  erewrite big_sum_eq_bounded.
  2: {
  intros k Hk.
  pose proof (kron_transpose _ _ _ _ ((@e_i n k) ⊤ ⊗ Matrix.I m) (@e_i n k)) as H;
  rewrite Nat.mul_1_l, Nat.mul_1_r, (Nat.mul_comm m n) in *;
  rewrite H; clear H.
  pose proof (kron_transpose _ _ _ _ ((@e_i n k) ⊤) (Matrix.I m)) as H;
  rewrite Nat.mul_1_l in *;
  rewrite H; clear H.
  restore_dims.
  rewrite 2!kron_mixed_product.
  rewrite id_transpose_eq, Mmult_1_l by easy.
  rewrite e_i_dot_is_component, transpose_involutive by easy.
  (* rewrite <- Mmult_transpose. *)
  rewrite Mscale_kron_dist_r, <- 2!Mscale_kron_dist_l.
  rewrite kron_1_r.
  rewrite <- Mscale_mult_dist_l.
  reflexivity.
  }
  rewrite <- (kron_Msum_distr_r n _ P).
  rewrite <- (Mmult_Msum_distr_r).
  rewrite <- vector_eq_basis_comb by easy.
  easy.
Qed.

Lemma kron_vec_matrix_vecT : forall m n o p
  (Q : Matrix n o) (x : Vector m) (z : Vector p),
  WF_Matrix x -> WF_Matrix z -> WF_Matrix Q ->
  x ⊗ Q ⊗ (z⊤) = @Mmult (m*n) (m*n) (o*p) (kron_comm m n) (Q ⊗ (x × z⊤)).
Proof.
  intros m n o p Q x z Hwfx Hwfz HwfQ.
  match goal with |- ?A = ?B =>
  rewrite <- (Mmult_1_l _ _ A) ; auto with wf_db
  end.
  rewrite Nat.mul_1_r.
  rewrite <- (kron_comm_mul_transpose_r), Mmult_assoc at 1.
  rewrite Nat.mul_1_l.
  apply Mmult_simplify; [easy|].
  rewrite kron_comm_kron_form_sum'.
  rewrite Msum_transpose.
  rewrite Mmult_Msum_distr_r.
  erewrite big_sum_eq_bounded.
  2: {
  intros k Hk.
  pose proof (kron_transpose _ _ _ _ ((@e_i m k) ⊗ Matrix.I n) ((@e_i m k) ⊤)) as H;
  rewrite Nat.mul_1_l, Nat.mul_1_r, (Nat.mul_comm m n) in *;
  rewrite H; clear H.
  pose proof (kron_transpose _ _ _ _ ((@e_i m k)) (Matrix.I n)) as H;
  rewrite Nat.mul_1_l, (Nat.mul_comm m n) in *;
  rewrite H; clear H.
  restore_dims.
  rewrite 2!kron_mixed_product.
  rewrite id_transpose_eq, Mmult_1_l by easy.
  rewrite e_i_dot_is_component, transpose_involutive by easy.
  (* rewrite <- Mmult_transpose. *)
  rewrite 2!Mscale_kron_dist_l, kron_1_l, <-Mscale_kron_dist_r by easy.
  rewrite <- Mscale_mult_dist_l.
  restore_dims.
  reflexivity.
  }
  rewrite <- (kron_Msum_distr_l m _ Q).
  rewrite <- (Mmult_Msum_distr_r).
  rewrite <- vector_eq_basis_comb by easy.
  easy.
Qed.

Lemma kron_comm_triple_cycle : forall m n s t p q (A : Matrix m n)
  (B : Matrix s t) (C : Matrix p q), WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
  A ⊗ B ⊗ C = (kron_comm (m*s) p) × (C ⊗ A ⊗ B) × (kron_comm q (t*n)).
Proof.
  intros m n s t p q A B C HA HB HC.
  rewrite (commute_kron _ _ _ _ (A ⊗ B) C) by auto with wf_db.
  rewrite kron_assoc by easy.
  f_equal; try lia; f_equal; lia.
Qed.

Lemma kron_comm_triple_cycle2 : forall m n s t p q (A : Matrix m n)
  (B : Matrix s t) (C : Matrix p q), WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
  A ⊗ B ⊗ C = (kron_comm m (s*p)) × (B ⊗ C ⊗ A) × (kron_comm (q*t) n).
Proof.
  intros m n s t p q A B C HA HB HC.
  rewrite kron_assoc by easy.
  rewrite (commute_kron _ _ _ _ A (B ⊗ C)) by auto with wf_db.
  f_equal; try lia; f_equal; lia.
Qed.

Lemma id_eq_sum_kron_e_is : forall n, 
  Matrix.I n = big_sum (G:=Square n) (fun i => @e_i n i ⊗ (@e_i n i) ⊤) n.
Proof.
  intros n.
  symmetry.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  rewrite Msum_Csum.
  erewrite big_sum_eq_bounded.
  2: {
  intros k Hk.
  rewrite kron_e_i_l by lia.
  unfold transpose, e_i.
  rewrite <- andb_if.
  replace_bool_lia (j <? n) true.
  rewrite Nat.div_1_r.
  simpl.
  replace ((i =? k) && ((j =? k) && true && (i - k * 1 =? 0)))%nat 
    with ((i =? k) && (j =? k)) by bdestructΩ'.
  reflexivity.
  }
  unfold Matrix.I.
  replace_bool_lia (i <? n) true.
  rewrite andb_true_r.
  bdestruct (i =? j).
  - subst.
  apply big_sum_unique.
  exists j; repeat split; intros; bdestructΩ'.
  - rewrite big_sum_0; [easy|].
  intros k; bdestructΩ'.
Qed.  

Lemma kron_comm_cycle_indices : forall t s n,
  (kron_comm (t*s) n = @Mmult (s*(n*t)) (s*(n*t)) (t*(s*n)) (kron_comm s (n*t)) (kron_comm t (s*n))).
Proof.
  intros t s n.
  rewrite kron_comm_kron_form_sum.
  erewrite big_sum_eq_bounded.
  2: {
  intros j Hj.
  rewrite (Nat.mul_comm t s), <- id_kron, <- kron_assoc by auto with wf_db.
  restore_dims.
  rewrite kron_assoc by auto with wf_db.
  (* rewrite (kron_assoc ((@e_i n j)⊤ ⊗ Matrix.I t) (Matrix.I s) (@e_i n j)) by auto with wf_db. *)
  lazymatch goal with
  |- ?A ⊗ ?B = _ => rewrite (commute_kron _ _ _ _ A B) by auto with wf_db
  end.
  (* restore_dims. *)
  reflexivity.
  }
  (* rewrite ?Nat.mul_1_r, ?Nat.mul_1_l. *)
  (* rewrite <- Mmult_Msum_distr_r. *)

  rewrite <- (Mmult_Msum_distr_r n _ (kron_comm (t*1) (n*s))).
  rewrite <- Mmult_Msum_distr_l.
  erewrite big_sum_eq_bounded.
  2: {
  intros j Hj.
  rewrite <- kron_assoc, (kron_assoc (Matrix.I t)) by auto with wf_db.
  restore_dims.
  reflexivity.
  } 
  (* rewrite Nat.mul_1_l *)
  rewrite <- (kron_Msum_distr_r n _ (Matrix.I s)).
  rewrite <- (kron_Msum_distr_l n _ (Matrix.I t)).
  rewrite 2!Nat.mul_1_r, 2!Nat.mul_1_l.
  rewrite <- (id_eq_sum_kron_e_is n).
  rewrite 2!id_kron.
  restore_dims.
  rewrite Mmult_1_r by auto with wf_db.
  rewrite (Nat.mul_comm t n), (Nat.mul_comm n s).
  easy.
Qed.

Lemma kron_comm_cycle_indices_rev : forall t s n,
  @Mmult (s*(n*t)) (s*(n*t)) (t*(s*n)) (kron_comm s (n*t)) (kron_comm t (s*n)) = kron_comm (t*s) n.
Proof.
  intros. 
  rewrite <- kron_comm_cycle_indices.
  easy.
Qed.


Lemma kron_comm_triple_id : forall t s n, 
  (kron_comm (t*s) n) × (kron_comm (s*n) t) × (kron_comm (n*t) s) = Matrix.I (t*s*n).
Proof.
  intros t s n.
  rewrite kron_comm_cycle_indices.
  restore_dims.
  rewrite (Mmult_assoc (kron_comm s (n*t))).
  restore_dims.
  rewrite (Nat.mul_comm (s*n) t). (* TODO: Fix kron_comm_mul_inv to have the 
    right dimensions by default (or, better yet, to be ambivalent) *)
  rewrite (kron_comm_mul_inv t (s*n)).
  restore_dims.
  rewrite Mmult_1_r by auto with wf_db.
  rewrite (Nat.mul_comm (n*t) s).
  rewrite (kron_comm_mul_inv).
  f_equal; lia.
Qed.

Lemma kron_comm_triple_id' : forall t s n, 
  (kron_comm n (t*s)) × (kron_comm t (s*n)) × (kron_comm s (n*t)) = Matrix.I (t*s*n).
Proof.
  intros t s n.
  apply transpose_matrices.
  rewrite 2!Mmult_transpose.
  (* restore_dims. *)
  rewrite (kron_comm_transpose s (n*t)).
  restore_dims.
  rewrite (kron_comm_transpose n (t*s)).
  restore_dims.
  replace (n*(t*s))%nat with (t*(s*n))%nat by lia.
  replace (s*(n*t))%nat with (t*(s*n))%nat by lia.
  rewrite (kron_comm_transpose t (s*n)).
  restore_dims.
  rewrite Nat.mul_assoc, id_transpose_eq.
  restore_dims.
  (* rewrite (kron_comm_triple_id n t s). *)
  Admitted.

Lemma kron_comm_triple_indices_commute : forall t s n,
  @Mmult (s*t*n) (s*t*n) (t*(s*n)) (kron_comm (s*t) n) (kron_comm t (s*n)) = 
  @Mmult (t*(s*n)) (t*(s*n)) (s*t*n) (kron_comm t (s*n)) (kron_comm (s*t) n).
Proof.
  intros t s n.
  rewrite <- (kron_comm_cycle_indices_rev s t n).
  Admitted.
  (* rewrite kron_comm_triple_id.
rewrite <- (kron_comm_cycle_indices t s n). *)


Lemma f_to_vec_split : forall (f : nat -> bool) (m n : nat),
  f_to_vec (m + n) f = f_to_vec m f ⊗ f_to_vec n (VectorStates.shift f m).
Proof.
  intros f m n.
  rewrite f_to_vec_merge.
  apply f_to_vec_eq.
  intros i Hi.
  unfold VectorStates.shift.
  bdestructΩ'.
  f_equal; lia.
Qed.

Lemma n_top_to_bottom_semantics_eq_kron_comm : forall n o,
  ⟦ n_top_to_bottom n o ⟧ = kron_comm (2^o) (2^n).
Proof.
  intros n o.
  rewrite zxperm_permutation_semantics by auto with zxperm_db.
  unfold zxperm_to_matrix.
  rewrite perm_of_n_top_to_bottom.
  apply equal_on_basis_states_implies_equal; auto with wf_db.
  1: {
  rewrite Nat.add_comm, Nat.pow_add_r.
  auto with wf_db.
  }
  intros f.
  pose proof (perm_to_matrix_permutes_qubits (n + o) (rotr (n+o) n) f).
  unfold perm_to_matrix in H.
  rewrite H by auto with perm_db.
  rewrite (f_to_vec_split f).
  pose proof (kron_comm_commutes_vectors_l (2^o) (2^n)
  (f_to_vec n f) (f_to_vec o (@VectorStates.shift bool f n))
  ltac:(auto with wf_db) ltac:(auto with wf_db)).
  replace (2^(n+o))%nat with (2^o *2^n)%nat by (rewrite Nat.pow_add_r; lia).
  simpl in H0.
  rewrite H0.
  rewrite Nat.add_comm, f_to_vec_split.
  f_equal.
  - apply f_to_vec_eq.
  intros i Hi.
  unfold VectorStates.shift.
  f_equal; unfold rotr.
  rewrite Nat.mod_small by lia.
  bdestructΩ'.
  - apply f_to_vec_eq.
  intros i Hi.
  unfold VectorStates.shift, rotr.
  rewrite <- Nat.add_assoc, mod_add_n_r, Nat.mod_small by lia.
  bdestructΩ'.
Qed.


Lemma compose_semantics' :
forall {n m o : nat} (zx0 : ZX n m) (zx1 : ZX m o),
@eq (Matrix (Nat.pow 2 o) (Nat.pow 2 n))
  (@ZX_semantics n o (@Compose n m o zx0 zx1))
  (@Mmult (Nat.pow 2 o) (Nat.pow 2 m) (Nat.pow 2 n) 
	 (@ZX_semantics m o zx1) (@ZX_semantics n m zx0)).
Proof.
  intros.
  rewrite (@compose_semantics n m o).
  easy.
Qed.
