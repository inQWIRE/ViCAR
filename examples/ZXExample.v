From VyZX Require Import CoreData.
From VyZX Require Import CoreRules.
From VyZX Require Import PermutationRules.
From ViCaR Require Export CategoryTypeclass.

#[export] Instance ZXCategory : Category nat := {
    morphism := ZX;

    equiv := @proportional;
    equiv_symm := @proportional_symm;
    equiv_trans := @proportional_trans;
    equiv_refl := @proportional_refl;

    obj_equiv := eq;
    obj_equiv_symm := @eq_sym nat;
    obj_equiv_trans := @eq_trans nat;
    obj_equiv_refl := @eq_refl nat;

    c_identity n := n_wire n;

    compose := @Compose;
    compose_compat := @Proportional.compose_compat;

    left_unit _ _ := nwire_removal_l;
    right_unit _ _ := nwire_removal_r;
    assoc := @ComposeRules.compose_assoc;
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

#[export] Instance ZXMonoidalCategory : MonoidalCategory nat := {
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
}.

Definition zx_braiding {n m} :=
    let l := (n + m)%nat in
    let r := (m + n)%nat in
        cast l r (eq_refl l) (Nat.add_comm m n) (n_top_to_bottom n m).

Definition zx_inv_braiding {n m} :=
    let l := (m + n)%nat in
    let r := (n + m)%nat in
        cast l r (eq_refl l) (Nat.add_comm n m) (n_bottom_to_top n m).

Definition n_compose_bot n m := n_compose n (bottom_to_top m).
Definition n_compose_top n m := n_compose n (top_to_bottom m).

Lemma zx_braiding_inv_compose : forall {n m},
    zx_braiding ⟷ zx_inv_braiding ∝ n_wire (n + m).
Proof.
    intros.
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
    all: rewrite (Nat.add_comm n m); easy.
Qed.

Lemma zx_inv_braiding_compose : forall {n m},
    zx_inv_braiding ⟷ zx_braiding ∝ n_wire (m + n).
Proof.
    intros. 
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
    all: rewrite (Nat.add_comm n m); easy.
Qed.

Lemma n_top_to_bottom_split : forall {n m o o'} prf1 prf2 prf3 prf4,
    n_top_to_bottom n m ↕ n_wire o
    ⟷ cast (n + m + o) o' prf1 prf2 (n_wire m ↕ n_top_to_bottom n o)
    ∝ cast (n + m + o) o' prf3 prf4 (n_top_to_bottom n (m + o)).
Proof.
    intros. unfold n_top_to_bottom. 
    prop_perm_eq.
    1: auto 10 with zxperm_db.
    solve_modular_permutation_equalities.
Qed.

Lemma hexagon_lemma_1 : forall {n m o}, 
    (zx_braiding ↕ n_wire o) ⟷ zx_associator ⟷ (n_wire m ↕ zx_braiding)
    ∝ zx_associator ⟷ (@zx_braiding n (m + o)) ⟷ zx_associator.
Proof.
    intros.
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
    reflexivity.
Qed.

Lemma n_bottom_to_top_split : forall {n m o o'} prf1 prf2 prf3 prf4,
    n_bottom_to_top m n ↕ n_wire o
    ⟷ cast (n + m + o) o' prf1 prf2 (n_wire m ↕ n_bottom_to_top o n)
    ∝ cast (n + m + o) o' prf3 prf4 (n_bottom_to_top (m + o) n).
Proof.
    intros. unfold n_bottom_to_top. subst.
    prop_perm_eq.
    solve_modular_permutation_equalities.
Qed.

Lemma hexagon_lemma_2 : forall {n m o},
    (zx_inv_braiding ↕ n_wire o) ⟷ zx_associator ⟷ (n_wire m ↕ zx_inv_braiding)
    ∝ zx_associator ⟷ (@zx_inv_braiding (m + o) n) ⟷ zx_associator.
Proof.
    intros.
    unfold zx_inv_braiding. unfold zx_associator.
    (* alternate proof:
    unfold n_bottom_to_top; prop_perm_eq;
     solve_modular_permutation_equalities.
    *)
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
    reflexivity.
Qed.

#[export] Instance ZXBraidedMonoidalCategory : BraidedMonoidalCategory nat := {
    braiding := @zx_braiding;
    inv_braiding := @zx_inv_braiding;
    braiding_inv_compose := @zx_braiding_inv_compose;
    inv_braiding_compose := @zx_inv_braiding_compose;

    hexagon_1 := @hexagon_lemma_1;
    hexagon_2 := @hexagon_lemma_2;
}.

Lemma n_top_to_bottom_is_bottom_to_top : forall {n m},
    n_top_to_bottom n m ∝ n_bottom_to_top m n.
Proof.
    (* alternate proof:
    unfold n_bottom_to_top, n_top_to_bottom;
    intros;
    prop_perm_eq;
    solve_modular_permutation_equalities;
    rewrite rotr_eq_rotl_sub.*)
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
      reflexivity.
Qed.

Lemma braiding_symmetry : forall n m, 
    @zx_braiding n m ∝ @zx_inv_braiding m n.
Proof.
    intros.
    unfold zx_braiding. unfold zx_inv_braiding.
    apply cast_compat.
    rewrite n_top_to_bottom_is_bottom_to_top.
    reflexivity.
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
    unfold ZXCore.adjoint.
    simpl.
    reflexivity.
Qed.

Lemma zx_associator_unitary_r : forall {n m o},
    zx_associator ⟷ zx_associator †%ZX ∝ n_wire (n + m + o).
Proof.
    intros. 
    unfold zx_associator.
    rewrite cast_adj. 
    rewrite nwire_adjoint.
    rewrite cast_compose_mid.
    simpl_casts.
    rewrite nwire_removal_r.
    reflexivity.
    Unshelve. all: lia.
Qed.

Lemma zx_associator_unitary_l : forall {n m o},
    zx_associator †%ZX ⟷ zx_associator ∝ n_wire (n + (m + o)).
Proof.
    intros.
    unfold zx_associator. 
    rewrite cast_adj.
    rewrite nwire_adjoint.
    rewrite cast_compose_mid.
    simpl_casts.
    rewrite nwire_removal_r.
    reflexivity.
    Unshelve. all: lia.
Qed.

Lemma zx_left_unitor_unitary_r : forall {n},
    zx_left_unitor ⟷ zx_left_unitor †%ZX ∝ n_wire (0 + n).
Proof.
    intros. unfold zx_left_unitor.
    simpl_casts. cleanup_zx.
    rewrite nwire_adjoint.
    reflexivity.
Qed.

Lemma zx_left_unitor_unitary_l : forall {n},
    zx_left_unitor †%ZX ⟷ zx_left_unitor ∝ n_wire n.
Proof.
    intros. unfold zx_left_unitor.
    simpl_casts. cleanup_zx.
    rewrite nwire_adjoint.
    reflexivity.
Qed.

Lemma zx_right_unitor_unitary_r : forall {n},
    zx_right_unitor ⟷ zx_right_unitor †%ZX ∝ n_wire (n + 0).
Proof.
    intros. unfold zx_right_unitor.
    rewrite cast_compose_mid. simpl_casts.
    rewrite nwire_adjoint.
    cleanup_zx. 
    rewrite cast_n_wire.
    reflexivity.
    Unshelve. all: lia.
Qed.

Lemma zx_right_unitor_unitary_l : forall {n},
    zx_right_unitor †%ZX ⟷ zx_right_unitor ∝ n_wire n.
Proof.
    intros. unfold zx_right_unitor.
    rewrite cast_compose_mid. simpl_casts.
    rewrite nwire_adjoint.
    cleanup_zx. 
    reflexivity.
    Unshelve. all: lia.
Qed.

Lemma n_yank_l : forall n {prf1 prf2},
    cast n (n + n + n) prf1 prf2 (n_wire n ↕ n_cap n) 
    ⟷ (n_cup n ↕ n_wire n) ∝ n_wire n.
Proof.
    induction n.
    - intros.
      rewrite n_cap_0_empty.
      rewrite n_cup_0_empty.
      simpl_casts.
      cleanup_zx. simpl.
      simpl_casts. cleanup_zx.
      easy.
    - intros.
Admitted.

Lemma n_yank_r : forall n {prf1 prf2 prf3 prf4},
    cast n n prf3 prf4 (cast n (n + (n + n)) prf1 prf2 (n_cap n ↕ n_wire n)
    ⟷ (n_wire n ↕ n_cup n)) ∝ n_wire n.
Proof.
    induction n.
    - intros.
      rewrite n_cap_0_empty.
      rewrite n_cup_0_empty.
      simpl_casts.
      cleanup_zx. simpl.
      simpl_casts. cleanup_zx.
      easy.
    - intros.
Admitted.

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