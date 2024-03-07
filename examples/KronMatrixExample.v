
Require Import MatrixPermBase.
Require Import KronComm.
Require Export MatrixExampleBase.
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


Definition MxKronBiFunctor : Bifunctor MxCategory MxCategory MxCategory := {|
  obj2_map := Nat.mul;
  morphism2_map := @kron;
  id2_map := ltac:(intros; rewrite id_kron; easy);
  compose2_map := ltac:(intros; rewrite kron_mixed_product; easy);
  morphism2_compat := ltac:(intros; apply kron_mat_equiv_morph; easy);
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
  isomorphism_inverse := ltac:(split; rewrite Nat.mul_1_l, Mmult_1_r_mat_eq; easy);
  (* id_A := ltac:(rewrite Nat.mul_1_l, Mmult_1_r_mat_eq; easy);
  id_B := ltac:(rewrite Nat.mul_1_l, Mmult_1_r_mat_eq; easy); *)
  |};

  right_unitor := fun n => {|
  forward := (I n : Matrix (n * 1) n);
  reverse := (I n : Matrix n (n * 1));
  isomorphism_inverse := ltac:(split; rewrite Nat.mul_1_r, Mmult_1_r_mat_eq; easy);
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
  component2_iso := MxKronBraidingIsomorphism;
  component2_iso_natural := ltac:(intros; simpl in *; 
    rewrite (Nat.mul_comm B2 B1), (Nat.mul_comm A2 A1); 
    rewrite (kron_comm_commutes_r_mat_equiv);
    easy);
|}.