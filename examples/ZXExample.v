Require Import Setoid.

From VyZX Require Import CoreData.
From VyZX Require Import CoreRules.
From VyZX Require Import PermutationRules.
From ViCaR Require Export CategoryTypeclass.


Lemma proportional_equiv {n m : nat} : equivalence (ZX n m) proportional.
Proof.
  constructor.
  unfold reflexive; apply proportional_refl.
  unfold transitive; apply proportional_trans.
  unfold symmetric; apply proportional_symm.
Qed.

Lemma equality_equiv : equivalence nat eq.
Proof. 
  constructor. 
  unfold reflexive; easy.
  unfold transitive; apply eq_trans.
  unfold symmetric; apply eq_sym.
Qed.

#[export] Instance ZXCategory : Category nat := {
  morphism := ZX;

  equiv := @proportional;
  equiv_rel := @proportional_equiv;

  compose := @Compose;
  compose_compat := @Proportional.compose_compat;
  assoc := @ComposeRules.compose_assoc;

  c_identity n := n_wire n;
  left_unit _ _ := nwire_removal_l;
  right_unit _ _ := nwire_removal_r;
}.

Definition zx_associator {n m o} :=
  let l := (n + m + o)%nat in
  let r := (n + (m + o))%nat in
  let assoc := Nat.add_assoc n m o in
    cast l r (eq_refl l) assoc (n_wire l).

Definition zx_inv_associator {n m o} :=
  let l := (n + (m + o))%nat in
  let r := (n + m + o)%nat in
  let assoc := Nat.add_assoc n m o in 
    cast l r (eq_refl l) (eq_sym assoc) (n_wire l).

Lemma zx_associator_inv_compose : forall {n m o},
  zx_associator ⟷ zx_inv_associator ∝ n_wire (n + m + o).
Proof.
  intros.
  unfold zx_associator. unfold zx_inv_associator.
  rewrite cast_compose_r. 
  cleanup_zx. simpl_casts.
  reflexivity.
Qed.

Lemma zx_inv_associator_compose : forall {n m o},
  zx_inv_associator ⟷ zx_associator ∝ n_wire (n + (m + o)).
Proof.
  intros.
  unfold zx_associator. unfold zx_inv_associator.
  rewrite cast_compose_l.
  cleanup_zx. simpl_casts.
  reflexivity.
Qed.

Lemma zx_associator_cohere : forall {n m o p q r} 
  (zx0 : ZX n m) (zx1 : ZX o p) (zx2 : ZX q r),
  zx_associator ⟷ (zx0 ↕ (zx1 ↕ zx2)) 
  ∝ (zx0 ↕ zx1 ↕ zx2) ⟷ zx_associator.
Proof.
  intros. 
  unfold zx_associator.
  repeat rewrite cast_compose_r.
  simpl_casts. cleanup_zx.
  rewrite cast_compose_l.
  cleanup_zx. simpl_casts.
  rewrite stack_assoc.
  reflexivity.
Qed.

Definition zx_left_unitor {n} := 
  cast (0 + n) n (Nat.add_0_l n) (eq_refl n) (n_wire n).

Definition zx_inv_left_unitor {n} := 
  cast n (0 + n) (eq_refl n) (Nat.add_0_l n) (n_wire n).

Lemma zx_left_inv_compose : forall {n},
  zx_left_unitor ⟷ zx_inv_left_unitor ∝ n_wire (0 + n).
Proof.
  intros. 
  unfold zx_left_unitor. unfold zx_inv_left_unitor.
  simpl_casts. cleanup_zx. reflexivity.
Qed.

Lemma zx_inv_left_compose : forall {n}, 
  zx_inv_left_unitor ⟷ zx_left_unitor ∝ n_wire n.
Proof.
  intros. 
  unfold zx_left_unitor. unfold zx_inv_left_unitor.
  simpl_casts. cleanup_zx. reflexivity.
Qed.

Lemma zx_left_unitor_cohere : forall {n m} (zx : ZX n m), 
  zx_left_unitor ⟷ zx ∝ (n_wire 0) ↕ zx ⟷ zx_left_unitor.
Proof.
  intros.
  unfold zx_left_unitor.
  simpl_casts.
  rewrite nwire_removal_l.
  rewrite stack_empty_l.
  rewrite nwire_removal_r.
  reflexivity.
Qed.

Definition zx_right_unitor {n} := 
  cast (n + 0) n (Nat.add_0_r n) (eq_refl n) (n_wire n).

Definition zx_inv_right_unitor {n} := 
  cast n (n + 0) (eq_refl n) (Nat.add_0_r n) (n_wire n).

Lemma zx_right_inv_compose : forall {n},
  zx_right_unitor ⟷ zx_inv_right_unitor ∝ n_wire (n + 0).
Proof.
  intros.
  unfold zx_right_unitor. unfold zx_inv_right_unitor.
  rewrite cast_compose_l.
  cleanup_zx. simpl_casts. reflexivity.
Qed.

Lemma zx_inv_right_compose : forall {n},
  zx_inv_right_unitor ⟷ zx_right_unitor ∝ n_wire n.
Proof.
  intros.
  unfold zx_right_unitor. unfold zx_inv_right_unitor.
  rewrite cast_compose_r.
  cleanup_zx. simpl_casts. reflexivity.
Qed.

Lemma zx_right_unitor_cohere : forall {n m} (zx : ZX n m), 
  zx_right_unitor ⟷ zx ∝ zx ↕ (n_wire 0) ⟷ zx_right_unitor.
Proof.
  intros.
  unfold zx_right_unitor; cleanup_zx.
  rewrite <- cast_compose_mid_contract.
  cleanup_zx.
  rewrite cast_compose_l; simpl_casts.
  rewrite nwire_removal_l.
  reflexivity.
  Unshelve. all: easy.
Qed.

Lemma zx_triangle_lemma : forall {n m}, 
  zx_associator ⟷ (n_wire n ↕ zx_left_unitor) ∝ 
  zx_right_unitor ↕ n_wire m.
Proof.
  intros.
  unfold zx_associator.
  unfold zx_right_unitor.
  unfold zx_left_unitor.
  simpl_casts.
  repeat rewrite n_wire_stack.
  cleanup_zx.
  simpl_casts.
  reflexivity.
Qed.

Lemma zx_pentagon_lemma : forall {n m o p}, 
  (zx_associator ↕ n_wire p) ⟷ zx_associator ⟷ (n_wire n ↕ zx_associator)
  ∝ (@zx_associator (n + m) o p) ⟷ zx_associator.
Proof.
  intros.
  unfold zx_associator.
  simpl_casts.
  repeat rewrite n_wire_stack.
  repeat rewrite cast_compose_l.
  repeat rewrite cast_compose_r.
  cleanup_zx; simpl_casts; reflexivity.
Qed.

Definition ZXTensorBiFunctor : Bifunctor ZXCategory ZXCategory ZXCategory := {|
  obj2_map := Nat.add;
  morphism2_map := @Stack;
  id2_map := n_wire_stack;
  compose2_map := @stack_compose_distr;
  morphism2_compat := @stack_simplify;
|}.

#[export] Instance ZXMonoidalCategory : MonoidalCategory nat := {
  tensor := ZXTensorBiFunctor;
  
  associator := fun n m o => {|
  forward := @zx_associator n m o;
  reverse := @zx_inv_associator n m o;
  id_A := @zx_associator_inv_compose n m o;
  id_B := @zx_inv_associator_compose n m o;
  |};

  left_unitor := fun n => {|
  forward := @zx_left_unitor n;
  reverse := @zx_inv_left_unitor n;
  id_A := @zx_left_inv_compose n;
  id_B := @zx_inv_left_compose n;
  |};

  right_unitor := fun n => {|
  forward := @zx_right_unitor n;
  reverse := @zx_inv_right_unitor n;
  id_A := @zx_right_inv_compose n;
  id_B := @zx_inv_right_compose n;
  |};

  associator_cohere := @zx_associator_cohere;
  left_unitor_cohere := @zx_left_unitor_cohere;
  right_unitor_cohere := @zx_right_unitor_cohere;

  triangle := @zx_triangle_lemma;
  pentagon := @zx_pentagon_lemma; 
(*
  tensor := Nat.add;
  I := 0;

  tensor_morph _ _ _ _ := Stack;
  tensor_morph_compat := stack_compat;

  associator := @zx_associator;
  inv_associator := @zx_inv_associator;
  associator_inv_compose := @zx_associator_inv_compose;
  inv_associator_compose := @zx_inv_associator_compose;

  left_unitor := @zx_left_unitor;
  inv_left_unitor := @zx_inv_left_unitor;
  left_inv_compose := @zx_left_inv_compose;
  inv_left_compose := @zx_inv_left_compose;

  right_unitor := @zx_right_unitor;
  inv_right_unitor := @zx_inv_right_unitor;
  right_inv_compose := @zx_right_inv_compose;
  inv_right_compose := @zx_inv_right_compose;

  bifunctor_id := n_wire_stack;
  bifunctor_comp := @stack_compose_distr;

  associator_cohere := @zx_associator_cohere;
  left_unitor_cohere := @zx_left_unitor_cohere;
  right_unitor_cohere := @zx_right_unitor_cohere;

  triangle := @zx_triangle_lemma;
  pentagon := @zx_pentagon_lemma; 
*)
}.

Definition zx_braiding {n m} :=
  let l := (n + m)%nat in
  let r := (m + n)%nat in
    cast l r (eq_refl l) (Nat.add_comm m n) (n_top_to_bottom n m).

Definition zx_inv_braiding {n m} :=
  let l := (m + n)%nat in
  let r := (n + m)%nat in
    cast l r (eq_refl l) (Nat.add_comm n m) (n_bottom_to_top n m).

(* Because they're not definitionally square, it's kinda useless to show
   zx_braiding and zx_inv_braiding are (up to cast) ZXperm's. Instead, we
   can hint it to unfold them automatically and let the casting wizardy take
   it from there: *)
#[export] Hint Unfold zx_braiding zx_inv_braiding 
  zx_associator zx_inv_associator 
  zx_left_unitor zx_right_unitor
  zx_inv_left_unitor zx_inv_right_unitor : zxperm_db.

Definition n_compose_bot n m := n_compose n (bottom_to_top m).
Definition n_compose_top n m := n_compose n (top_to_bottom m).

Lemma zx_braiding_inv_compose : forall {n m},
  zx_braiding ⟷ zx_inv_braiding ∝ n_wire (n + m).
Proof.
  intros.
  prop_perm_eq.
  rewrite Nat.add_comm.
  cleanup_perm_of_zx; easy.
  (* intros.
  unfold zx_braiding. unfold zx_inv_braiding.
  unfold n_top_to_bottom. 
  unfold n_bottom_to_top.
  rewrite cast_compose_mid.
  simpl_casts.
  fold (n_compose_bot n (m + n)).
  rewrite cast_fn_eq_dim.
  rewrite n_compose_top_compose_bottom.
  reflexivity.
  Unshelve. 
  all: rewrite (Nat.add_comm n m); easy. *)
Qed.

Lemma zx_inv_braiding_compose : forall {n m},
  zx_inv_braiding ⟷ zx_braiding ∝ n_wire (m + n).
Proof.
  intros.
  prop_perm_eq.
  rewrite Nat.add_comm.
  cleanup_perm_of_zx; easy.
  (* intros. 
  unfold zx_braiding. unfold zx_inv_braiding.
  unfold n_top_to_bottom. 
  unfold n_bottom_to_top.
  rewrite cast_compose_mid.
  simpl_casts.
  fold (n_compose_top n (n + m)).
  rewrite cast_fn_eq_dim.
  rewrite n_compose_bottom_compose_top.
  reflexivity.
  Unshelve. 
  all: rewrite (Nat.add_comm n m); easy. *)
Qed.

Lemma n_top_to_bottom_split : forall {n m o o'} prf1 prf2 prf3 prf4,
  n_top_to_bottom n m ↕ n_wire o
  ⟷ cast (n + m + o) o' prf1 prf2 (n_wire m ↕ n_top_to_bottom n o)
  ∝ cast (n + m + o) o' prf3 prf4 (n_top_to_bottom n (m + o)).
Proof.
  intros.
  prop_perm_eq.
  solve_modular_permutation_equalities.
Qed.

Lemma hexagon_lemma_1 : forall {n m o}, 
  (zx_braiding ↕ n_wire o) ⟷ zx_associator ⟷ (n_wire m ↕ zx_braiding)
  ∝ zx_associator ⟷ (@zx_braiding n (m + o)) ⟷ zx_associator.
Proof.
  intros.
  prop_perm_eq.
  solve_modular_permutation_equalities.
  (* intros.
  unfold zx_braiding. unfold zx_associator.
  simpl_casts.
  rewrite cast_compose_l. simpl_casts.
  rewrite compose_assoc.
  rewrite cast_compose_l. simpl_casts.
  cleanup_zx. simpl_casts.  
  rewrite cast_compose_l. 
  simpl_casts. cleanup_zx.
  rewrite cast_compose_l. simpl_casts.
  rewrite (cast_compose_r _ _ _ (n_wire (m + o + n))).
  cleanup_zx. simpl_casts.
  rewrite n_top_to_bottom_split.
  reflexivity. *)
Qed.

Lemma n_bottom_to_top_split : forall {n m o o'} prf1 prf2 prf3 prf4,
  n_bottom_to_top m n ↕ n_wire o
  ⟷ cast (n + m + o) o' prf1 prf2 (n_wire m ↕ n_bottom_to_top o n)
  ∝ cast (n + m + o) o' prf3 prf4 (n_bottom_to_top (m + o) n).
Proof.
  prop_perm_eq.
  solve_modular_permutation_equalities.
Qed.

Lemma hexagon_lemma_2 : forall {n m o},
  (zx_inv_braiding ↕ n_wire o) ⟷ zx_associator ⟷ (n_wire m ↕ zx_inv_braiding)
  ∝ zx_associator ⟷ (@zx_inv_braiding (m + o) n) ⟷ zx_associator.
Proof.
  prop_perm_eq.
  solve_modular_permutation_equalities.
  (* intros.
  unfold zx_inv_braiding. unfold zx_associator.
  simpl_casts.
  rewrite cast_compose_l. simpl_casts.
  rewrite compose_assoc.
  rewrite cast_compose_l. simpl_casts.
  cleanup_zx. simpl_casts.
  rewrite cast_compose_l.
  simpl_casts. cleanup_zx.
  rewrite cast_compose_l. simpl_casts.
  rewrite (cast_compose_r _ _ _ (n_wire (m + o + n))).
  cleanup_zx. simpl_casts.
  rewrite n_bottom_to_top_split.
  reflexivity. *)
Qed.

Require Export KronComm_orig.






Lemma zx_braiding_commutes (A1 B1 A2 B2 : nat) (f1 : ZX A1 B1) (f2 : ZX A2 B2) :
  zx_braiding ⟷ (f1 ↕ f2) ⟷ zx_braiding ∝ (f2 ↕ f1).
Proof.
  unfold zx_braiding.
  prop_exists_nonzero 1.
  rewrite 2!compose_semantics'. 
  rewrite (@cast_semantics _ _ (A2+A1) (A1+A2) _ _ (n_top_to_bottom A2 A1)).
  rewrite (@cast_semantics (B1+B2) (B1+B2) (B1+B2) (B2+B1) _ _ (n_top_to_bottom B1 B2)).
  rewrite 2!n_top_to_bottom_semantics_eq_kron_comm.
  rewrite 2!stack_semantics, Mscale_1_l.
  rewrite <- (kron_comm_commutes (2^B1)%nat (2^A1)%nat (2^B2) (2^A2) (⟦ f1 ⟧) (⟦ f2 ⟧))
  by (auto with wf_db).
  rewrite Mmult_assoc.
  rewrite (Nat.add_comm B1 B2), (Nat.add_comm A2 A1).
  rewrite 2!Nat.pow_add_r.
  easy.
Qed.

Lemma zx_braiding_eq_zx_inv_braiding : forall n m, 
  @zx_braiding n m ∝ zx_inv_braiding.
Proof.
  prop_perm_eq; solve_modular_permutation_equalities.
Qed.

Lemma zx_braiding_pass_through_l (A1 B1 A2 B2 : nat) (f1 : ZX A1 B1) (f2 : ZX A2 B2) :
  zx_braiding ⟷ (f1 ↕ f2) ∝ (f2 ↕ f1) ⟷ zx_inv_braiding.
Proof.
  rewrite <- (nwire_removal_r (zx_braiding ⟷ _)), <- zx_braiding_inv_compose.
  rewrite <-compose_assoc.
  apply compose_simplify; [|easy].
  apply zx_braiding_commutes.
Qed.

Lemma zx_braiding_iso_natural (A1 B1 A2 B2 : nat) (f1 : ZX A1 B1) (f2 : ZX A2 B2) :
  f1 ↕ f2 ⟷ zx_braiding ∝ zx_braiding ⟷ (f2 ↕ f1).
Proof. 
  rewrite (zx_braiding_eq_zx_inv_braiding A1 A2).
  rewrite <- (nwire_removal_l (_ ⟷ zx_braiding)), <- zx_inv_braiding_compose.
  rewrite compose_assoc.
  apply compose_simplify; [easy|].
  rewrite <- compose_assoc.
  apply zx_braiding_commutes.
Qed.

Definition ZXBraidingIsomorphism : forall n m, 
  Isomorphism (ZXTensorBiFunctor n m) ((CommuteBifunctor ZXTensorBiFunctor) n m) :=
  fun n m => Build_Isomorphism nat ZXCategory _ _
    ((* forward := *) @zx_braiding n m)
    ((* reverse := *) @zx_inv_braiding n m)
    ((* id_A := *) @zx_braiding_inv_compose n m)
    ((* id_B := *) @zx_inv_braiding_compose n m).

#[export] Instance ZXBraidingBiIsomorphism : 
  NaturalBiIsomorphism ZXTensorBiFunctor (CommuteBifunctor ZXTensorBiFunctor) := {|
  component2_iso := ZXBraidingIsomorphism;
  component2_iso_natural := zx_braiding_iso_natural;
|}.


#[export] Instance ZXBraidedMonoidalCategory : BraidedMonoidalCategory nat := {
  braiding := ZXBraidingBiIsomorphism;

  hexagon_1 := @hexagon_lemma_1;
  hexagon_2 := @hexagon_lemma_2;
(*  
  braiding := @zx_braiding;
  inv_braiding := @zx_inv_braiding;
  braiding_inv_compose := @zx_braiding_inv_compose;
  inv_braiding_compose := @zx_inv_braiding_compose;

  hexagon_1 := @hexagon_lemma_1;
  hexagon_2 := @hexagon_lemma_2;
*)
}.

Lemma n_top_to_bottom_is_bottom_to_top : forall {n m},
  n_top_to_bottom n m ∝ n_bottom_to_top m n.
Proof.
  prop_perm_eq.
  solve_modular_permutation_equalities.
(* 
  intros.
  unfold n_bottom_to_top. 
  unfold bottom_to_top.
  unfold n_top_to_bottom.
  induction n.
  - intros.
    rewrite n_compose_0.
    simpl.
    rewrite <- n_compose_transpose.
    rewrite n_compose_n_top_to_bottom.
    rewrite n_wire_transpose.
    reflexivity.
  - intros.
    rewrite n_compose_grow_l.
    assert ((S n + m)%nat = (n + S m)%nat) by lia.
    assert (top_to_bottom (S n + m) 
    ∝ cast (S n + m) (S n + m) H H (top_to_bottom (n + S m))) 
    by (rewrite cast_fn_eq_dim; reflexivity).
    rewrite H0.
    rewrite cast_n_compose.
    rewrite IHn.
    rewrite <- cast_n_compose.
    rewrite <- H0.
    rewrite n_compose_grow_l.
    rewrite <- cast_transpose.
    rewrite <- H0.
    fold (bottom_to_top (S n + m)).
    rewrite <- compose_assoc.
    rewrite top_to_bottom_to_top. cleanup_zx.
    reflexivity. *)
Qed.

Lemma braiding_symmetry : forall n m, 
  @zx_braiding n m ∝ @zx_inv_braiding m n.
Proof.
  prop_perm_eq.
  solve_modular_permutation_equalities.
(* intros.
  unfold zx_braiding. unfold zx_inv_braiding.
  apply cast_compat.
  rewrite n_top_to_bottom_is_bottom_to_top.
  reflexivity. *)
Qed.

#[export] Instance ZXSymmetricMonoidalCategory : SymmetricMonoidalCategory nat := {
  symmetry := braiding_symmetry;
}.

Lemma nwire_adjoint : forall n, (n_wire n) †%ZX ∝ n_wire n.
Proof.
  intros.
  induction n; try easy.
  - intros.
    unfold ZXCore.adjoint.
    simpl.
    unfold ZXCore.adjoint in IHn.
    rewrite IHn.
    reflexivity.
Qed.

Lemma compose_adjoint : forall {n m o}
  (zx0 : ZX n m) (zx1 : ZX m o), 
  (zx0 ⟷ zx1) †%ZX ∝ zx1 †%ZX ⟷ zx0 †%ZX.
Proof.
  intros; easy.
Qed.

Lemma stack_adjoint : forall {n n' m m'} 
  (zx0: ZX n m) (zx1 : ZX n' m'),
  (zx0 ↕ zx1) †%ZX ∝ zx0 †%ZX ↕ zx1 †%ZX.
Proof.
  intros.
  unfold ZXCore.adjoint.
  simpl.
  easy.
Qed.

#[export] Instance ZXDaggerCategory : DaggerCategory nat := {
  adjoint := @ZXCore.adjoint;
  involutive := @Proportional.adjoint_involutive;
  preserves_id := nwire_adjoint;
  contravariant := @compose_adjoint;
}.

Lemma zx_dagger_compat : forall {n n' m m'} 
  (zx0: ZX n m) (zx1 : ZX n' m'),
  zx0 †%ZX ↕ zx1 †%ZX ∝ (zx0 ↕ zx1) †%ZX.
Proof.
  intros.
  rewrite stack_adjoint.
  easy.
Qed.

Lemma zx_associator_unitary_r : forall {n m o},
  zx_associator ⟷ zx_associator †%ZX ∝ n_wire (n + m + o).
Proof.
  intros. 
  unfold zx_associator.
  rewrite cast_adj. 
  rewrite nwire_adjoint.
  simpl_permlike_zx.
  reflexivity.
Qed.

Lemma zx_associator_unitary_l : forall {n m o},
  zx_associator †%ZX ⟷ zx_associator ∝ n_wire (n + (m + o)).
Proof.
  intros.
  unfold zx_associator. 
  rewrite cast_adj.
  rewrite nwire_adjoint.
  simpl_permlike_zx.
  rewrite cast_n_wire.
  reflexivity.
Qed.

Lemma zx_left_unitor_unitary_r : forall {n},
  zx_left_unitor ⟷ zx_left_unitor †%ZX ∝ n_wire (0 + n).
Proof.
  intros. unfold zx_left_unitor.
  simpl_permlike_zx.
  rewrite nwire_adjoint.
  reflexivity.
Qed.

Lemma zx_left_unitor_unitary_l : forall {n},
  zx_left_unitor †%ZX ⟷ zx_left_unitor ∝ n_wire n.
Proof.
  intros. unfold zx_left_unitor.
  simpl_permlike_zx.
  rewrite nwire_adjoint.
  reflexivity.
Qed.

Lemma zx_right_unitor_unitary_r : forall {n},
  zx_right_unitor ⟷ zx_right_unitor †%ZX ∝ n_wire (n + 0).
Proof.
  intros. unfold zx_right_unitor.
  simpl_permlike_zx.
  rewrite cast_adj, nwire_adjoint.
  simpl_permlike_zx.
  rewrite cast_n_wire.
  reflexivity.
Qed.

Lemma zx_right_unitor_unitary_l : forall {n},
  zx_right_unitor †%ZX ⟷ zx_right_unitor ∝ n_wire n.
Proof.
  intros. unfold zx_right_unitor.
  simpl_permlike_zx.
  rewrite cast_adj, nwire_adjoint.
  simpl_permlike_zx.
  reflexivity.
Qed.

Lemma helper_eq: forall n m (prf: n = m), (n + n = m + m)%nat.
Proof. intros. subst. reflexivity. Qed. 

Lemma cast_n_cup_unswapped : forall n m prf1 prf2,
  cast (n + n) 0 (helper_eq _ _ prf1) prf2 (n_cup_unswapped m) ∝ n_cup_unswapped n.
Proof.
  intros.
  subst.
  rewrite cast_id_eq.
  easy.
Qed.

Lemma wire_stack_distr_compose_l : forall n m o (zx0 : ZX n m) (zx1 : ZX m o),
  — ↕ (zx0 ⟷ zx1) ∝ (— ↕ zx0) ⟷ (— ↕ zx1).
Proof.
  intros.
  rewrite <- stack_compose_distr.
  cleanup_zx.
  easy.
Qed.

Lemma wire_stack_distr_compose_r : forall n m o (zx0 : ZX n m) (zx1 : ZX m o),
  (zx0 ⟷ zx1) ↕ — ∝ (zx0 ↕ —) ⟷ (zx1 ↕ —).
Proof.
  intros.
  rewrite <- stack_compose_distr.
  cleanup_zx.
  easy.
Qed.

Lemma n_cup_unswapped_grow_r : forall n prf1 prf2,
  n_cup_unswapped (S n) ∝ 
  cast _ _ prf1 prf2 (— ↕ n_cup_unswapped n ↕ —) ⟷ ⊃.
Proof.
  intros.
  induction n.
  - simpl. cleanup_zx.
    apply compose_simplify; [|easy].
    prop_perm_eq.
  - rewrite n_cup_unswapped_grow_l.
    rewrite IHn at 1.
    rewrite n_cup_unswapped_grow_l.
    bundle_wires.
    rewrite <- compose_assoc.
    apply compose_simplify; [|easy].
    rewrite wire_stack_distr_compose_l, wire_stack_distr_compose_r.
    rewrite (prop_iff_double_cast _ (1 + 0 + 1) _ _ eq_refl).
    simpl_casts.
    rewrite (cast_compose_mid_contract _ (1 + (n + n) + 1)).
    rewrite 2!cast_contract, cast_id.
    apply compose_simplify; [|easy].
    simpl_casts.
    simpl (n_wire S n).
    rewrite 4!stack_assoc.
    rewrite (stack_assoc — (n_wire n) _).
    simpl_casts.
    repeat (rewrite cast_stack_distribute; apply stack_simplify; try prop_perm_eq).
    rewrite cast_id; easy.
  Unshelve.
  all: lia.
Qed.

Lemma nwire_stack_distr_compose_l : forall k n m o (zx0 : ZX n m) (zx1 : ZX m o),
  n_wire k ↕ (zx0 ⟷ zx1) ∝ (n_wire k ↕ zx0) ⟷ (n_wire k ↕ zx1).
Proof.
  intros.
  rewrite <- stack_compose_distr.
  cleanup_zx.
  easy.
Qed.

Lemma nwire_stack_distr_compose_r : forall k n m o (zx0 : ZX n m) (zx1 : ZX m o),
  (zx0 ⟷ zx1) ↕ n_wire k ∝ (zx0 ↕ n_wire k) ⟷ (zx1 ↕ n_wire k).
Proof.
  intros.
  rewrite <- stack_compose_distr.
  cleanup_zx.
  easy.
Qed.

Lemma n_cup_unswapped_comm_1 : forall k prf1 prf2 prf3 prf4,
  cast (S k + (S k)) _ prf1 prf2 (n_wire k ↕ ⊃ ↕ n_wire k) ⟷ (n_cup_unswapped k)
  ∝ cast _ _ prf3 prf4 (— ↕ n_cup_unswapped k ↕ —) ⟷ ⊃.
Proof.
  intros.
  rewrite <- n_cup_unswapped_grow_l.
  rewrite <- n_cup_unswapped_grow_r.
  easy.
Qed.

Lemma n_wire_add_stack : forall n k,
  n_wire (n + k) ∝ n_wire n ↕ n_wire k.
Proof. prop_perm_eq. Qed.

Lemma n_wire_add_stack_rev : forall n k prf1 prf2,
  n_wire (n + k) ∝ cast _ _ prf1 prf2 (n_wire k ↕ n_wire n).
Proof. prop_perm_eq. Qed.

Lemma stack_assoc' : forall {n0 n1 n2 m0 m1 m2} (zx0 : ZX n0 m0) 
  (zx1 : ZX n1 m1) (zx2 : ZX n2 m2) prfn prfm,
  zx0 ↕ (zx1 ↕ zx2) ∝ cast _ _ prfn prfm ((zx0 ↕ zx1) ↕ zx2).
Proof.
  intros.
  rewrite stack_assoc.
  rewrite cast_cast_eq, cast_id.
  easy.
  Unshelve.
  all: lia.
Qed.

Lemma n_cup_unswapped_comm : forall n k prf1 prf2 prf3 prf4,
  cast (S n + k + (S n + k)) _ prf1 prf2 (n_wire (n + k) ↕ ⊃ ↕ n_wire (n + k)) ⟷ (n_wire n ↕ n_cup_unswapped k ↕ n_wire n)
  ∝ cast _ _ prf3 prf4 (n_wire (S n) ↕ n_cup_unswapped k ↕ n_wire (S n)) ⟷ (n_wire n ↕ ⊃ ↕ n_wire n).
Proof.
  intros.
  rewrite n_wire_add_stack at 1.
  rewrite n_wire_add_stack_rev at 1.
  rewrite (n_wire_add_stack_rev 1 n) at 1.
  rewrite (n_wire_add_stack 1 n) at 1.
  rewrite 5!stack_assoc.
  repeat rewrite cast_cast_eq.
  simpl_casts.
  rewrite stack_assoc.
  rewrite (prop_iff_double_cast (n + (k + 2 + k + n)) (n + (0 + n))).
  rewrite (cast_compose_mid_contract _ (n + (k + 0 + k + n))).
  repeat rewrite cast_cast_eq.
  rewrite (cast_compose_mid_contract _ (n + (2 + n))).
  rewrite 2!cast_cast_eq.
  erewrite 3!(cast_stack_distribute _ _ _ _ _ _ (n_wire n)).
  rewrite 4!cast_id_eq.
  rewrite <- 2!nwire_stack_distr_compose_l.
  apply stack_simplify; [easy|].
  rewrite <- wire_to_n_wire.
  rewrite 3!stack_assoc'.
  rewrite (stack_assoc' (_ ↕ _) (—) (n_wire n)).
  repeat rewrite cast_cast_eq.
  rewrite 3!(cast_stack_distribute (o':=n)).
  rewrite (cast_id (n:=n)).
  rewrite <- 2!nwire_stack_distr_compose_r.
  apply stack_simplify; [|easy].
  rewrite (prop_iff_double_cast ((S k) + (S k)) (0)).
  simpl_permlike_zx.
  symmetry.
  rewrite (cast_compose_mid_contract _ 2).
  symmetry.
  rewrite cast_id_eq.
  rewrite cast_cast_eq.
  rewrite <- n_cup_unswapped_comm_1.
  rewrite (prop_iff_double_cast ((S k) + (S k)) (0)).
  rewrite (cast_compose_mid_contract _ (k + k)).
  simpl_casts.
  easy.
  Unshelve.
  all: lia.
Qed.



Lemma n_cup_unswapped_grow_k_l : forall n k prf1 prf2,
  n_cup_unswapped (n + k) ∝ 
  cast _ _ prf1 prf2 (n_wire n ↕ (n_cup_unswapped k) ↕ n_wire n) ⟷ n_cup_unswapped n.
Proof.
  intros.
  induction n.
  - rewrite stack_empty_l, stack_empty_r, cast_cast_eq,
    cast_id_eq, compose_empty_r.
    easy.
  - rewrite (prop_iff_double_cast (S (n + k) + S (n + k)) 0).
    rewrite cast_n_cup_unswapped.
    rewrite n_cup_unswapped_grow_l, IHn.
    rewrite n_cup_unswapped_grow_l.
    simpl_permlike_zx.
    (* simpl_casts. *)
    repeat rewrite <- compose_assoc.
    apply compose_simplify; [|easy].
    symmetry.
    rewrite (cast_compose_mid (n + 2 + n)).
    erewrite (prop_iff_double_cast ((S n + k) + (S n + k)) (n + 0 + n) _ _ eq_refl).
    rewrite 2!cast_contract.
    rewrite cast_compose_mid_contract, 2!cast_contract, cast_id.
    rewrite cast_compose_mid_contract, 2!cast_contract, cast_id.
    rewrite n_cup_unswapped_comm.
    easy.
  Unshelve.
  all: try easy; auto with arith; lia.
Qed.

Lemma n_cup_unswapped_add_comm : forall n k prf1 prf2,
  n_cup_unswapped (n + k) ∝ cast _ _ prf1 prf2 (n_cup_unswapped (k + n)).
Proof.
  intros. 
  assert (H: (k + n = n + k)%nat) by lia.
  generalize dependent (k + n)%nat.
  generalize dependent (n + k)%nat.
  intros; subst.
  rewrite cast_id_eq.
  easy.
Qed.

Lemma n_cup_unswapped_grow_k_r : forall n k prf1 prf2,
  n_cup_unswapped (n + k) ∝ 
  cast _ _ prf1 prf2 (n_wire k ↕ (n_cup_unswapped n) ↕ n_wire k) ⟷ n_cup_unswapped k.
Proof.
  intros.
  rewrite n_cup_unswapped_add_comm.
  rewrite n_cup_unswapped_grow_k_l.
  rewrite (cast_compose_mid_contract _ (k + k)%nat).
  simpl_casts.
  apply compose_simplify; [|easy].
  erewrite cast_proof_independence.
  reflexivity.
  Unshelve. all:lia.
Qed.



Lemma stack_ncup_unswapped_split : forall {n0t n0b n1t n1b} n m (zx0top : ZX n0t m) (zx0bot : ZX n0b m)
  (zx1top : ZX n1t n) (zx1bot : ZX n1b n) prf1 prf2 prf3 prf4 prf5 prf6,
  (zx1top ↕ zx0top) ↕ (zx0bot ↕ zx1bot) 
    ⟷ cast ((n + m) + (m + n)) 0 prf1 prf2 (n_cup_unswapped (n + m))
  ∝ cast _ _ prf5 prf6 (zx1top ↕ ((zx0top ↕ zx0bot) ⟷ n_cup_unswapped m) ↕ zx1bot 
    ⟷ cast (n + 0 + n) 0 prf3 prf4 (n_cup_unswapped n)).
Proof.
  intros.
  rewrite cast_compose_r.
  simpl_permlike_zx.
  rewrite n_cup_unswapped_grow_k_l, <- compose_assoc.
  rewrite (cast_compose_mid_contract _ (n + n)).
  simpl_permlike_zx.
  apply compose_simplify; [|easy].
  rewrite stack_assoc, (stack_assoc' zx0top).
  simpl_casts.
  rewrite stack_assoc'.
  rewrite cast_cast_eq.
  rewrite (prop_iff_double_cast (n1t + (n0t + n0b) + n1b) (n + 0 + n)).
  rewrite (cast_compose_mid_contract _ (n + (m + m) + n)).
  simpl_permlike_zx.
  rewrite <- 2!stack_compose_distr, 2!nwire_removal_r.
  easy.
  Unshelve.
  all: lia.
Qed.

(* Local Open Scope matrix_scope. *)



Lemma sem_n_cup_unswapped_2 :
  ⟦ n_cup_unswapped 2 ⟧ = 
  fun x y => if (x=?0) && ((y=?0) || (y=?6) || (y=?9) || (y=?15)) then C1 else C0.
Proof.
  unfold n_cup_unswapped.
  repeat (simpl;
  rewrite cast_semantics; simpl).
  rewrite 2!id_kron.
  replace (list2D_to_matrix [[C1; C0; C0; C1]]) with
  (fun x y => if (x =? 0)&&((y =? 0) || (y =? 3)) then C1 else C0) by solve_matrix.
  solve_matrix.
Qed.





Lemma swap_2cup_transport : 
  ⟦ n_cup_unswapped 2 ⟧ × (swap ⊗ (Matrix.I (2^2))) 
  = ⟦ n_cup_unswapped 2 ⟧ × ((Matrix.I (2^2)) ⊗ swap).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  rewrite sem_n_cup_unswapped_2.
  by_cell; try lca.
Qed.

Lemma swap_2cup_flip : 
  ⨉ ↕ n_wire 2 ⟷ n_cup_unswapped 2 ∝ n_wire 2 ↕ ⨉ ⟷ n_cup_unswapped 2.
Proof.
  prop_exists_nonzero 1.
  rewrite (compose_semantics (⨉ ↕ n_wire 2) (n_cup_unswapped 2)). (* For some reason, it needs *)
  rewrite (compose_semantics (n_wire 2 ↕ ⨉) (n_cup_unswapped 2)). (* its arguments explicitly *)
  rewrite Mscale_1_l.
  rewrite 2!stack_semantics, n_wire_semantics.
  simpl (⟦ ⨉ ⟧).
  apply swap_2cup_transport.
Qed.

Tactic Notation "preplace" constr(zx0) "with" constr(zx1) :=
  (let H := fresh "H" in 
  enough (H: zx0 ∝ zx1); 
  [rewrite H; clear H| ]).

Tactic Notation "preplace" constr(zx0) "with" constr(zx1) "in" hyp(target) :=
  (let H := fresh "H" in 
  enough (H: zx0 ∝ zx1); 
  [rewrite H in target; clear H| ]).

Tactic Notation "preplace" constr(zx0) "with" constr(zx1) "in" "*" :=
  (let H := fresh "H" in 
  enough (H: zx0 ∝ zx1); 
  [rewrite H in *; clear H| ]).

Tactic Notation "preplace" constr(zx0) "with" constr(zx1) "by" tactic(slv) :=
  (let H := fresh "H" in 
  assert (H: zx0 ∝ zx1) by slv; 
  rewrite H; clear H).

Tactic Notation "preplace" constr(zx0) "with" constr(zx1) "in" hyp(target) "by" tactic(slv) :=
  (let H := fresh "H" in 
  assert (H: zx0 ∝ zx1) by slv; 
  rewrite H in target; clear H).

Tactic Notation "preplace" constr(zx0) "with" constr(zx1) "in" "*" "by" tactic(slv) :=
  (let H := fresh "H" in 
  assert (H: zx0 ∝ zx1) by slv; 
  rewrite H in *; clear H).



Lemma n_cup_unswapped_split_stack : forall {n00 m0 n01 m1 n10 n11 nbot}
  (zx00 : ZX n00 m0) (zx01 : ZX n01 m1) (zx10 : ZX n10 m1) (zx11 : ZX n11 m0)
  prf1 prf2 prf3 prf4 prf5 prf6,
  (zx00 ↕ zx01) ↕ (cast nbot (m0 + m1) prf1 prf2 (zx10 ↕ zx11)) ⟷ n_cup_unswapped (m0 + m1) 
  ∝
  cast _ 0 prf5 prf6 (n_wire n00
   ↕ (zx01 ↕ zx10 ⟷ n_cup_unswapped m1) ↕ n_wire n11 ⟷ 
    cast _ 0 prf3 prf4 (zx00 ↕ zx11 ⟷ n_cup_unswapped m0)).
Proof.
  intros. 
  rewrite cast_stack_r.
  rewrite n_cup_unswapped_grow_k_l.
  rewrite <- compose_assoc.
  rewrite stack_assoc, (stack_assoc' zx01).
  simpl_casts.
  rewrite stack_assoc', cast_cast_eq.
  rewrite <- cast_compose_mid_contract.
  rewrite <- 2!stack_compose_distr, 2!nwire_removal_r. 
  rewrite pull_out_bot, <- (nwire_removal_l zx11), stack_compose_distr.
  rewrite cast_compose_distribute.
  rewrite (cast_compose_mid_contract _ (n00 + 0 + n11)).
  rewrite compose_assoc.
  apply compose_simplify; [easy | ].
  simpl_casts.
  rewrite cast_compose_mid_contract, cast_id_eq.
  apply compose_simplify; [|easy].
  rewrite nwire_removal_l.
  easy.
  Unshelve.
  all: lia.
Qed.

Lemma n_cup_unswapped_split_stack' : forall {n00 m0 n01 m1 n10 n11 ntop}
  (zx00 : ZX n00 m0) (zx01 : ZX n01 m1) (zx10 : ZX n10 m1) (zx11 : ZX n11 m0)
  prf1 prf2 prf3 prf4 prf5 prf6,
  (cast ntop (m1 + m0) prf1 prf2 (zx00 ↕ zx01)) ↕ (zx10 ↕ zx11) ⟷ n_cup_unswapped (m1 + m0) 
  ∝
  cast _ 0 prf5 prf6 (n_wire n00
   ↕ (zx01 ↕ zx10 ⟷ n_cup_unswapped m1) ↕ n_wire n11 ⟷ 
    cast _ 0 prf3 prf4 (zx00 ↕ zx11 ⟷ n_cup_unswapped m0)).
Proof.
  intros.
  rewrite (prop_iff_double_cast (ntop + (n10 + n11)) 0).
  rewrite (cast_compose_mid_contract _ (m0 + m1 + (m0 + m1))).
  rewrite cast_n_cup_unswapped by lia.
  subst ntop.
  rewrite cast_stack_distribute, cast_cast_eq, cast_id_eq.
  rewrite n_cup_unswapped_split_stack.
  simpl_casts.
  easy.
  Unshelve.
  all: lia.
Qed.

Lemma n_cup_unswapped_split_stack_cast : forall {n00 m0 n01 m1 n10 n11 ntop nbot}
  (zx00 : ZX n00 m0) (zx01 : ZX n01 m1) (zx10 : ZX n10 m1) (zx11 : ZX n11 m0)
  prf1 prf2 prf3 prf4 prf5 prf6 prf7 prf8,
  (cast ntop (m0 + m1) prf1 prf2 (zx00 ↕ zx01)) 
  ↕ (cast nbot (m0 + m1) prf3 prf4 (zx10 ↕ zx11))   
    ⟷ n_cup_unswapped (m0 + m1) ∝
  cast _ 0 prf5 prf6 (
  n_wire n00 ↕ (zx01 ↕ zx10 ⟷ n_cup_unswapped m1) ↕ n_wire n11 
    ⟷ cast _ 0 prf7 prf8 (zx00 ↕ zx11 ⟷ n_cup_unswapped m0)).
Proof.
  intros.
  subst ntop.
  rewrite cast_id_eq.
  apply n_cup_unswapped_split_stack.
Qed.


Lemma n_cup_unswapped_split_stack_n_wire_bot : forall {n0 n1}
  (zx0 : ZX n0 n0) (zx1 : ZX n1 n1) prf1 prf2 prf3 prf4,
  zx0 ↕ zx1 ↕ n_wire (n0 + n1) ⟷ n_cup_unswapped (n0 + n1) 
  ∝ cast _ 0 prf1 prf2 (
    n_wire n0 ↕ (zx1 ↕ n_wire n1 ⟷ n_cup_unswapped n1) ↕ n_wire n0 ⟷ 
    cast _ 0 prf3 prf4 (zx0 ↕ n_wire n0 ⟷ n_cup_unswapped n0)).
Proof.
  intros.
  rewrite n_wire_add_stack_rev.
  rewrite n_cup_unswapped_split_stack.
  easy.
  Unshelve.
  all: lia.
Qed.



Lemma n_cup_unswapped_split_stack_n_wire_top : forall {n0 n1}
  (zx0 : ZX n0 n0) (zx1 : ZX n1 n1) prf1 prf2 prf3 prf4,
  n_wire (n0 + n1) ↕ (zx0 ↕ zx1) ⟷ n_cup_unswapped (n0 + n1) 
  ∝ cast _ 0 prf1 prf2 (
    n_wire n1 ↕ (n_wire n0 ↕ zx0 ⟷ n_cup_unswapped n0) ↕ n_wire n1 ⟷ 
    cast _ 0 prf3 prf4 (n_wire n1 ↕ zx1 ⟷ n_cup_unswapped n1)).
Proof.
  intros.
  rewrite n_wire_add_stack_rev.
  rewrite n_cup_unswapped_split_stack'.
  easy.
  Unshelve.
  all: lia.
Qed.

Lemma n_cup_unswapped_split_stack_n_wire_bot' : forall {n0 n1 ntop}
  (zx0 : ZX n0 n0) (zx1 : ZX n1 n1) prf1 prf2 prf3 prf4 prf5 prf6,
  cast ntop _ prf1 prf2 (zx0 ↕ zx1) ↕ n_wire (n1 + n0) ⟷ n_cup_unswapped (n1 + n0)
  ∝ cast _ 0 prf3 prf4 (
    n_wire n0 ↕ (zx1 ↕ n_wire n1 ⟷ n_cup_unswapped n1) ↕ n_wire n0 ⟷ 
    cast _ 0 prf5 prf6 (zx0 ↕ n_wire n0 ⟷ n_cup_unswapped n0)).
Proof.
  intros.
  rewrite n_wire_add_stack.
  rewrite n_cup_unswapped_split_stack'.
  easy.
  Unshelve.
  all: lia.
Qed.

Lemma n_cup_unswapped_split_stack_n_wire_top' : forall {n0 n1 ntop}
  (zx0 : ZX n0 n0) (zx1 : ZX n1 n1) prf1 prf2 prf3 prf4 prf5 prf6,
  n_wire (n1 + n0) ↕ cast ntop _ prf1 prf2 (zx0 ↕ zx1) ⟷ n_cup_unswapped (n1 + n0)
  ∝ cast _ 0 prf3 prf4 (
    n_wire n1 ↕ (n_wire n0 ↕ zx0 ⟷ n_cup_unswapped n0) ↕ n_wire n1 ⟷ 
    cast _ 0 prf5 prf6 (n_wire n1 ↕ zx1 ⟷ n_cup_unswapped n1)).
Proof.
  intros.
  rewrite n_wire_add_stack.
  rewrite n_cup_unswapped_split_stack.
  easy.
  Unshelve.
  all: lia.
Qed.


Lemma n_cup_unswapped_grow_r_back : forall n prf1 prf2,
  (— ↕ n_cup_unswapped (n) ↕ — ⟷ ⊃)
  ∝ cast _ _ prf1 prf2 (n_cup_unswapped (S n)).
Proof.
  intros.
  rewrite (n_cup_unswapped_grow_r n).
  rewrite cast_compose_l.
  rewrite cast_cast_eq, 2!cast_id_eq.
  easy.
  Unshelve.
  all: lia.
Qed.

Lemma n_cup_unswapped_grow_k_r_back : forall n k prf1 prf2 prf3 prf4,
  (n_wire k ↕ n_cup_unswapped n ↕ n_wire k) 
    ⟷ cast (k + 0 + k) 0 prf1 prf2 (n_cup_unswapped k)
  ∝ cast _ 0 prf3 prf4 (n_cup_unswapped (n + k)).
Proof.
  intros.
  rewrite n_cup_unswapped_grow_k_r.
  rewrite (cast_compose_mid_contract _ (k + 0 + k)).
  rewrite cast_cast_eq, cast_id_eq.
  easy.
  Unshelve.
  all: lia.
Qed.

Lemma compose_n_wire_comm : forall {n m} (zx : ZX n m),
  n_wire n ⟷ zx ∝ zx ⟷ n_wire m.
Proof.
  intros.
  cleanup_zx; easy.
Qed.

Lemma compose_stack_n_wire_comm : forall {n0 m0 n1 m1} (zx0 : ZX n0 m0) (zx1 : ZX n1 m1),
  zx0 ↕ n_wire n1 ⟷ (n_wire m0 ↕ zx1) ∝ n_wire n0 ↕ zx1 ⟷ (zx0 ↕ n_wire m1).
Proof.
  intros.
  cleanup_zx.
  easy.
Qed.

Lemma top_to_bottom_cup_flip : forall k,
  top_to_bottom k ↕ n_wire k ⟷ n_cup_unswapped k
  ∝ n_wire k ↕ top_to_bottom k ⟷ n_cup_unswapped k.
Proof.
  destruct k; [prop_perm_eq|].
  induction k; 
    [ apply compose_simplify; [prop_perm_eq | easy] | ].
  rewrite top_to_bottom_grow_r at 1.
  rewrite nwire_stack_distr_compose_r.
  rewrite compose_assoc.
  rewrite (n_wire_add_stack 2 k) at 2.
  rewrite (n_cup_unswapped_split_stack' (n_wire k) ⨉ (n_wire 2) (n_wire k)).
  rewrite swap_2cup_flip.
  bundle_wires; cleanup_zx.
  rewrite nwire_stack_distr_compose_l, nwire_stack_distr_compose_r.
  rewrite compose_assoc.
  rewrite n_cup_unswapped_grow_k_r_back.
  rewrite (stack_assoc' (n_wire k)).
  rewrite 2!cast_stack_l.
  rewrite (stack_assoc _ ⨉), cast_cast_eq.
  rewrite (cast_compose_mid_contract _ (S (S k) + S (S k))).
  simpl_casts.
  rewrite 2!cast_stack_distribute.
  simpl_permlike_zx.
  bundle_wires; rewrite cast_n_wire.
  rewrite <- compose_assoc, compose_stack_n_wire_comm.
  rewrite (n_wire_add_stack 1 (S k)) at 2.
  rewrite compose_assoc.
  rewrite (n_cup_unswapped_split_stack' (top_to_bottom (S k)) — (n_wire 1) (n_wire S k)).
  rewrite IHk.
  rewrite <- n_cup_unswapped_split_stack'.
  rewrite <- compose_assoc.
  rewrite <- stack_compose_distr.
  rewrite <- wire_to_n_wire.
  rewrite <- (top_to_bottom_grow_l k).
  apply compose_simplify; [|easy].
  apply stack_simplify; [|easy].
  prop_perm_eq.
  Unshelve.
  all: lia.
Qed.

Lemma bottom_to_top_cup_flip : forall k,
  bottom_to_top k ↕ n_wire k ⟷ n_cup_unswapped k
  ∝ n_wire k ↕ bottom_to_top k ⟷ n_cup_unswapped k.
Proof.
  intros k.
  destruct k; [prop_perm_eq | ].
  induction k; 
    [ apply compose_simplify; [prop_perm_eq | easy] | ].
  rewrite bottom_to_top_grow_r at 1.
  rewrite nwire_stack_distr_compose_r.
  rewrite compose_assoc.
  rewrite (n_wire_add_stack_rev 2 k) at 2.
  rewrite (n_cup_unswapped_split_stack ⨉ (n_wire k) (n_wire k) (n_wire 2)).
  rewrite swap_2cup_flip.
  rewrite <- n_cup_unswapped_split_stack.
  rewrite <- compose_assoc, <- n_wire_add_stack, compose_stack_n_wire_comm.
  preplace (n_wire (2 + k)) with (n_wire (1 + (S k))) by easy.
  rewrite (n_wire_add_stack_rev 1 (S k)).
  rewrite compose_assoc.
  rewrite (n_cup_unswapped_split_stack — (bottom_to_top (S k)) (n_wire S k) (n_wire 1)).
  rewrite IHk.
  rewrite <- n_cup_unswapped_split_stack.
  rewrite <- compose_assoc.
  apply compose_simplify; [|easy].
  rewrite <- stack_compose_distr.
  apply stack_simplify; [prop_perm_eq | ].
  rewrite <- wire_to_n_wire.
  rewrite cast_compose_r, cast_cast_eq.
  rewrite (cast_compose_partial_contract_l _ (S k + 1)).
  rewrite <- (bottom_to_top_grow_l k).
  easy.
  Unshelve.
  all: lia.
Qed.

Lemma a_swap_cup_flip : forall k,
  a_swap k ↕ n_wire k ⟷ n_cup_unswapped k
  ∝ n_wire k ↕ a_swap k ⟷ n_cup_unswapped k.
Proof.
  intros k.
  destruct k; [prop_perm_eq|].
  simpl a_swap.
  rewrite nwire_stack_distr_compose_r, compose_assoc.
  rewrite (n_cup_unswapped_split_stack_n_wire_bot —).
  rewrite top_to_bottom_cup_flip.
  rewrite <- (cast_cast_eq _ _ (k + 1 + (k + 1)) 0 (1 + k + (1 + k)) 0).
  preplace (— ↕ n_wire 1) with (n_wire 1 ↕ —) by prop_perm_eq.
  rewrite <- (n_cup_unswapped_split_stack_n_wire_top (top_to_bottom k) —).
  rewrite (cast_compose_mid_contract _ (1 + k + (1 + k))).
  rewrite cast_n_cup_unswapped, cast_stack_distribute, cast_n_wire by lia.
  rewrite <- compose_assoc, compose_stack_n_wire_comm, compose_assoc.
  rewrite bottom_to_top_cup_flip.
  rewrite <- compose_assoc.
  apply compose_simplify; [|easy].
  rewrite <- stack_compose_distr.
  rewrite nwire_removal_r.
  apply stack_simplify; prop_perm_eq.
  solve_modular_permutation_equalities.
  Unshelve. 
  all: lia.
Qed.

Lemma n_swap_zxperm : forall n, 
  ZXperm n (n_swap n).
Proof.
  induction n; simpl; auto with zxperm_db.
Qed.

#[export] Hint Resolve n_swap_zxperm : zxperm_db.

Lemma perm_of_n_swap : forall n,
  perm_of_zx (n_swap n) = fun k => if n <=? k then k else (n - S k)%nat.
Proof.
  (* destruct n; [simpl; solve_modular_permutation_equalities|]. *)
  induction n; simpl perm_of_zx; cleanup_perm_of_zx;
  [|rewrite IHn]; solve_modular_permutation_equalities.
Qed.

#[export] Hint Rewrite perm_of_n_swap : perm_of_zx_cleanup_db.

Lemma n_swap_cup_flip : forall k,
  n_swap k ↕ n_wire k ⟷ n_cup_unswapped k
  ∝ n_wire k ↕ n_swap k ⟷ n_cup_unswapped k.
Proof.
  intros k.
  (* destruct k; [prop_perm_eq|]. *)
  induction k;
    [prop_perm_eq | ].
    (* [apply compose_simplify; [prop_perm_eq | easy] | ]. *)
  simpl (n_swap (S k)).
  rewrite nwire_stack_distr_compose_r, compose_assoc.
  rewrite (n_cup_unswapped_split_stack_n_wire_bot —), IHk.
  preplace (— ↕ n_wire 1) with (n_wire 1 ↕ —) by prop_perm_eq.
  rewrite <- (n_cup_unswapped_split_stack_n_wire_top' (n_swap k) —).
  rewrite <- compose_assoc, compose_stack_n_wire_comm, compose_assoc.
  rewrite bottom_to_top_cup_flip, <- compose_assoc.
  apply compose_simplify; [|easy].
  rewrite <- stack_compose_distr, nwire_removal_l.
  apply stack_simplify; [easy|].
  prop_perm_eq.
  solve_modular_permutation_equalities.
  Unshelve.
  all: lia.
Qed.






Local Open Scope ZX_scope.



Lemma n_yank_1_l_helper_helper : forall n,
  (⊃) ⊤ ↕ n_wire n ⟷ (— ↕ n_wire (1 + n)) ∝ n_wire n ⟷ (⊂ ↕ n_wire n).
Proof.
  intros n.
  simpl.
  rewrite nwire_removal_l, nwire_removal_r.
  easy.
Qed.

Lemma n_yank_1_l_helper : forall n prf1 prf2 prf3 prf4 prf5 prf6 prf7 prf8,
  cast (S n + (n + n)) (1 + n + S n + S n) prf1 prf2 (n_wire (1 + n) ↕ (n_wire n ↕ ⊃ ↕ n_wire n) ⊤)
    ⟷ (((cast (S n + S n) 2 prf3 prf4 (— ↕ n_cup_unswapped n ↕ —)) ⟷ ⊃) ↕ (— ↕ n_wire n))
  ∝ cast _ _ prf7 prf8 (
    (— ↕ (n_wire n ↕ n_wire n) ↕ n_wire n) ⟷ (cast (1 + (n + n) + n) (1 + 0 + n) prf5 prf6 (— ↕ (n_cup_unswapped n) ↕ n_wire n) )
    ⟷ (— ↕ ⊂ ↕ n_wire n) ⟷ (⊃ ↕ — ↕ n_wire n)
  ).
Proof.
  intros.
  rewrite nwire_stack_distr_compose_r.
  rewrite <- compose_assoc.
  rewrite (cast_compose_mid_contract _ (2 + 1 + n)).
  apply compose_simplify; [|
    rewrite stack_assoc, cast_cast_eq, cast_id; easy].
  rewrite 2!stack_transpose, n_wire_transpose.
  rewrite 2!stack_assoc', (stack_assoc — (n_wire n) (n_wire n)).
  simpl_permlike_zx.
  rewrite cast_stack_l, cast_cast_eq.
  rewrite (stack_assoc _ ((⊃) ⊤) (n_wire n)).
  rewrite (prop_iff_double_cast (S (n + n) + (0 + n)) (1 + (1 + (1 + n)))).
  rewrite (cast_compose_mid_contract _ ((n + n) + 1 + (1 + (1 + n)))).

  rewrite 2!cast_cast_eq.
  rewrite cast_stack_distribute.
  rewrite (cast_stack_l (mTop':=2)).
  rewrite (stack_assoc _ —).
  rewrite 2!cast_cast_eq.
  rewrite (cast_stack_distribute (o':= 1 + (1 + n))).
  rewrite <- stack_compose_distr.

  simpl_permlike_zx.
  rewrite n_yank_1_l_helper_helper.
  rewrite <- (nwire_removal_r (— ↕ n_cup_unswapped n)).
  rewrite stack_compose_distr.
  rewrite compose_assoc.
  apply compose_simplify; [
  bundle_wires; prop_perm_eq|].
  cleanup_zx.
  enough (Hrw : — ↕ n_cup_unswapped n ↕ n_wire n ⟷ (— ↕ ⊂ ↕ n_wire n)
    ∝ @cast (1 + (n + n) + n) (1 + 2 + n) (1 + (n + n) + 0 + n) (1 + 0 + 2 + n)
    (ltac:(lia)) (ltac:(lia)) (
    — ↕ n_cup_unswapped n ↕ ⦰ ↕ n_wire n ⟷ (— ↕ ⦰ ↕ ⊂ ↕ n_wire n))).
  - rewrite Hrw.
    repeat rewrite <- stack_compose_distr.
    rewrite 2!nwire_removal_l.
    rewrite (stack_assoc' _ ⊂ (n_wire n)).
    simpl_casts.
    do 2 (apply stack_simplify; [|easy]).
    apply stack_simplify; cleanup_zx; easy.

  - cleanup_zx. simpl_permlike_zx.
    rewrite (cast_compose_mid_contract _ (1 + 0 + n)), cast_id_eq.
    apply compose_simplify; [|easy].
    rewrite cast_stack_l, cast_cast_eq, cast_id_eq.
    easy.
  
  Unshelve. all: lia.
Qed.
  


Lemma n_yank_1_l : forall n,
  (— ↕ n_wire n) ↕ ((n_cup_unswapped (S n)) ⊤) ⟷ zx_inv_associator ⟷ ((n_cup_unswapped (S n)) ↕ (— ↕ n_wire n))
  ∝ — ↕ (n_wire n ↕ ((n_cup_unswapped n) ⊤) ⟷ zx_inv_associator ⟷ ((n_cup_unswapped n) ↕ n_wire n)).
Proof.
  intros n.
  rewrite n_cup_unswapped_grow_l at 1.
  rewrite compose_transpose.
  rewrite n_cup_unswapped_grow_r.
  unfold zx_inv_associator.
  simpl_permlike_zx.
  (* bundle_wires. *)
  rewrite nwire_stack_distr_compose_l.
  rewrite (cast_compose_mid_contract _ ((S n + (n + n)))).
  rewrite (cast_stack_distribute).
  simpl_permlike_zx.
  rewrite compose_assoc.
  simpl_casts.
  rewrite n_yank_1_l_helper, cast_id_eq.
  rewrite compose_assoc.
  rewrite <- 3!stack_compose_distr.
  rewrite yank_l.
  simpl (n_wire (1 + n)).
  rewrite (stack_assoc —).
  rewrite cast_id_eq.
  rewrite wire_to_n_wire, nwire_removal_r, <- wire_to_n_wire.
  rewrite (stack_assoc —).
  rewrite cast_id_eq.
  rewrite <- n_wire_add_stack.
  rewrite 2!nwire_removal_l.
  (* rewrite <- (wire_stack_distr_compose_l _ _ _ (n_cup_unswapped n ↕ n_wire n) (n_wire n)). *)
  replace (S n + (n + n))%nat with (1 + (n + (n + n)))%nat by easy.
  rewrite (wire_stack_distr_compose_l (n + 0)).
  simpl_casts.
  rewrite wire_to_n_wire at 5.
  rewrite <- n_wire_add_stack, nwire_removal_r.
  rewrite (prop_iff_double_cast (1 + (n + 0)) (0 + (1 + n))).
  rewrite 2!(cast_compose_mid_contract _ (1 + (n + n + n))).
  rewrite 2!cast_cast_eq, 2!cast_id_eq.
  easy.
  Unshelve. all: try easy; auto with arith; lia.
Qed.


Lemma n_yank_l_unswapped : forall n {prf1 prf2},
  (n_wire n) ↕ ((n_cup_unswapped n) ⊤) ⟷ zx_inv_associator ⟷ ((n_cup_unswapped n) ↕ (n_wire n))
  ∝ cast _ _ prf1 prf2 (n_wire n).
Proof. 
  intros.
  induction n.
  - unfold zx_inv_associator, n_cup_unswapped.
    prop_perm_eq.
  - simpl (n_wire S n).
    rewrite n_yank_1_l, IHn.
    prop_perm_eq.
  Unshelve.
  all: auto with arith.
Qed.

Lemma compose_zx_inv_associator_r : forall {n0 n m o} (zx : ZX n0 (n + (m + o))) prf1 prf2,
  zx ⟷ zx_inv_associator ∝ cast n0 (n + m + o) prf1 prf2 zx.
Proof.
  intros.
  rewrite (prop_iff_double_cast n0 (n + (m + o))).
  rewrite (cast_compose_mid_contract _ (n + (m + o))).
  rewrite cast_cast_eq, 2!cast_id_eq.
  rewrite <- (nwire_removal_r zx) at 2.
  apply compose_simplify; [easy | prop_perm_eq].
  Unshelve.
  all: auto with arith. 
Qed.

Lemma n_yank_l_unswapped': forall n {prf1 prf2},
  cast n (n+n+n) prf1 prf2 (n_wire n ↕ (n_cup_unswapped n) ⊤) ⟷ ((n_cup_unswapped n) ↕ (n_wire n))
  ∝ n_wire n.
Proof.
  intros.
  rewrite (prop_iff_double_cast (n + 0) (0 + n)).
  rewrite <- n_yank_l_unswapped.
  rewrite compose_zx_inv_associator_r.
  rewrite (cast_compose_mid_contract _ (n + n + n)), cast_id_eq, cast_cast_eq.
  easy.
  Unshelve.
  all: auto with arith. 
Qed.

Lemma n_swap_grow_r' : forall n prf1 prf2,
  n_swap (S n) ∝ top_to_bottom (S n) ⟷ cast (S n) (S n) prf1 prf2 (n_swap n ↕ —).
Proof.
  intros.
  prop_perm_eq.
  solve_modular_permutation_equalities.
Qed.

Lemma n_swap_n_swap : forall n,
  n_swap n ⟷ n_swap n ∝ n_wire n.
Proof.
  prop_perm_eq.
  solve_modular_permutation_equalities.
Qed.

#[export] Hint Rewrite n_swap_n_swap : perm_inv_db.


Lemma n_cup_unswapped_n_swap_n_swap : forall n, 
  n_swap n ↕ n_swap n ⟷ n_cup_unswapped n ∝ n_cup_unswapped n.
Proof.
  intros n.
  rewrite <- (nwire_removal_l (n_swap n)) at 1.
  rewrite <- (nwire_removal_r (n_swap n)) at 2.
  rewrite stack_compose_distr.
  rewrite compose_assoc, n_swap_cup_flip, <- compose_assoc.
  rewrite <- stack_compose_distr, n_swap_n_swap.
  rewrite nwire_removal_l, <- n_wire_add_stack, nwire_removal_l.
  easy.
Qed.

Lemma n_cup_inv_n_swap_n_wire' : forall n, n_cup n ∝ n_wire n ↕ n_swap n ⟷ n_cup_unswapped n.
Proof.
  intros n.
  unfold n_cup.
  apply n_swap_cup_flip.
Qed.

Lemma n_swap_transpose : forall n,
  (n_swap n) ⊤ ∝ n_swap n.
Proof.
  intros n.
  prop_perm_eq.
  perm_eq_by_WF_inv_inj (perm_of_zx (n_swap n)) n;
  [apply zxperm_permutation | apply perm_of_zx_WF 
  | rewrite perm_of_transpose_is_linv | ];
  auto with zxperm_db.
  cleanup_perm_of_zx.
  solve_modular_permutation_equalities.
Qed.

Lemma n_yank_l : forall n {prf1 prf2},
  cast n (n + n + n) prf1 prf2 (n_wire n ↕ n_cap n)
  ⟷ (n_cup n ↕ n_wire n) ∝ n_wire n.
Proof.
  intros.
  unfold n_cap.
  rewrite n_cup_inv_n_swap_n_wire' at 2.
  unfold n_cup.
  (* rewrite n_cup_inv_n_swap_n_wire. *)
  simpl.
  rewrite n_wire_transpose, n_swap_transpose.
  rewrite nwire_stack_distr_compose_l.
  rewrite stack_assoc'.
  rewrite (cast_compose_mid_contract n (n + n + n) (n + n + n)).
  rewrite cast_cast_eq, cast_id_eq.
  rewrite nwire_stack_distr_compose_r.
  rewrite <- compose_assoc, (compose_assoc _ _ (_ ↕ n_swap n ↕ _)).
  rewrite <- 2!stack_compose_distr, n_swap_n_swap, nwire_removal_l.
  rewrite <- 2!n_wire_add_stack, nwire_removal_r.
  apply n_yank_l_unswapped'.
  Unshelve.
  all: lia.
Qed.

Lemma n_yank_r : forall n {prf1 prf2 prf3 prf4},
  cast n n prf3 prf4 (cast n (n + (n + n)) prf1 prf2 (n_cap n ↕ n_wire n)
  ⟷ (n_wire n ↕ n_cup n)) ∝ n_wire n.
Proof.
  intros.
  apply transpose_diagrams.
  rewrite cast_transpose, compose_transpose.
  rewrite (cast_compose_mid_contract _ (n+n+n)).
  rewrite cast_transpose, cast_cast_eq, cast_id_eq.
  rewrite 2!stack_transpose.
  rewrite n_wire_transpose.
  unfold n_cap.
  rewrite Proportional.transpose_involutive.
  apply n_yank_l.
  Unshelve.
  all: lia.
Qed.

Lemma zx_triangle_1 : forall n,
  zx_inv_right_unitor ⟷ (n_wire n ↕ n_cap n) ⟷ zx_inv_associator
  ⟷ (n_cup n ↕ n_wire n) ⟷ zx_left_unitor ∝ n_wire n.
Proof.
  intros.
  unfold zx_inv_right_unitor.
  unfold zx_inv_associator.
  unfold zx_left_unitor.
  simpl_casts. cleanup_zx.
  rewrite cast_compose_l. 
  simpl_casts. cleanup_zx.
  rewrite cast_compose_r.
  cleanup_zx. simpl_casts.
  rewrite n_yank_l.
  reflexivity.
Qed.

Lemma zx_triangle_2 : forall n,
  zx_inv_left_unitor ⟷ (n_cap n ↕ n_wire n) ⟷ zx_associator
  ⟷ (n_wire n ↕ n_cup n) ⟷ zx_right_unitor ∝ n_wire n.
Proof.
  intros.
  unfold zx_inv_left_unitor.
  unfold zx_associator.
  unfold zx_right_unitor.
  simpl_casts. cleanup_zx.
  rewrite cast_compose_r.
  simpl_casts. cleanup_zx.
  rewrite cast_compose_r.
  simpl_casts. cleanup_zx.
  rewrite n_yank_r.
  reflexivity.
Qed.

#[export] Instance ZXCompactClosedCategory : CompactClosedCategory nat := {
  dual n := n;
  unit n := n_cap n;
  counit n := n_cup n;
  triangle_1 := zx_triangle_1;
  triangle_2 := zx_triangle_2;
}.



#[export] Instance ZXDaggerMonoidalCategory : DaggerMonoidalCategory nat := {
  dagger_compat := @zx_dagger_compat;

  associator_unitary_r := @zx_associator_unitary_r;
  associator_unitary_l := @zx_associator_unitary_l;
  left_unitor_unitary_r := @zx_left_unitor_unitary_r;
  left_unitor_unitary_l := @zx_left_unitor_unitary_l;
  right_unitor_unitary_r := @zx_right_unitor_unitary_r;
  right_unitor_unitary_l := @zx_right_unitor_unitary_l;
}.

#[export] Instance ZXDaggerBraidedMonoidalCategory : DaggerBraidedMonoidalCategory nat := {}.

#[export] Instance ZXDaggerSymmetricMonoidalCategory : DaggerSymmetricMonoidalCategory nat := {}. 