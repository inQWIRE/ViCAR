Require Import Setoid.

From VyZX Require Import CoreData.
From VyZX Require Import CoreRules.
From VyZX Require Import PermutationRules.

From ViCaR Require Import CategoryTypeclassCompatibility. 

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
  c_equiv := @proportional;
  compose := @Compose;
  c_identity n := n_wire n;
}.

#[export] Instance ZXCategoryC : CategoryCoherence ZXCategory := {
  c_equiv_rel := @proportional_equiv;

  compose_compat := @Proportional.compose_compat;
  assoc := @ComposeRules.compose_assoc;

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
  obj_bimap := Nat.add;
  morphism_bimap := @Stack;
  id_bimap := n_wire_stack;
  compose_bimap := @stack_compose_distr;
  morphism_bicompat := @stack_simplify;
|}.

#[export] Instance ZXMonoidalCategory : MonoidalCategory ZXCategory := {
  obj_tensor := Nat.add;
  mor_tensor := @Stack;
  mon_I := O;
  
  associator := fun n m o => {|
  forward := @zx_associator n m o;
  reverse := @zx_inv_associator n m o;
  isomorphism_inverse := 
    conj (@zx_associator_inv_compose n m o) (@zx_inv_associator_compose n m o)
  |};

  left_unitor := fun n => {|
  forward := @zx_left_unitor n;
  reverse := @zx_inv_left_unitor n;
  isomorphism_inverse := 
    conj (@zx_left_inv_compose n) (@zx_inv_left_compose n)
  |};

  right_unitor := fun n => {|
  forward := @zx_right_unitor n;
  reverse := @zx_inv_right_unitor n;
  isomorphism_inverse := 
    conj (@zx_right_inv_compose n) (@zx_inv_right_compose n)
  |};
}.

#[export] Instance ZXMonoidalCategoryC : 
  MonoidalCategoryCoherence ZXMonoidalCategory := {
  tensor_id := n_wire_stack;
  tensor_compose := @stack_compose_distr;
  tensor_compat := @stack_simplify;

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
Qed.

Lemma zx_inv_braiding_compose : forall {n m},
  zx_inv_braiding ⟷ zx_braiding ∝ n_wire (m + n).
Proof.
  intros.
  prop_perm_eq.
  rewrite Nat.add_comm.
  cleanup_perm_of_zx; easy.
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
Qed.

Require Export KronComm.



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
    ((* isomorphism_inverse := *) 
      conj (@zx_braiding_inv_compose n m) (@zx_inv_braiding_compose n m))
    (* ((* id_A := *) @zx_braiding_inv_compose n m)
    ((* id_B := *) @zx_inv_braiding_compose n m) *).

#[export] Instance ZXBraidingBiIsomorphism : 
  NaturalBiIsomorphism ZXTensorBiFunctor (CommuteBifunctor ZXTensorBiFunctor) := {|
  component_biiso := ZXBraidingIsomorphism;
  component_biiso_natural := zx_braiding_iso_natural;
|}.


#[export] Instance ZXBraidedMonoidalCategory : 
  BraidedMonoidalCategory ZXMonoidalCategory := {
  braiding := ZXBraidingBiIsomorphism;
}.

#[export] Instance ZXBraidedMonoidalCategoryC :
  BraidedMonoidalCategoryCoherence ZXBraidedMonoidalCategory := {
  braiding_natural := zx_braiding_iso_natural;
  hexagon_1 := @hexagon_lemma_1;
  hexagon_2 := @hexagon_lemma_2;
}.

Lemma n_top_to_bottom_is_bottom_to_top : forall {n m},
  n_top_to_bottom n m ∝ n_bottom_to_top m n.
Proof.
  prop_perm_eq.
  solve_modular_permutation_equalities.
Qed.

Lemma braiding_symmetry : forall n m, 
  @zx_braiding n m ∝ @zx_inv_braiding m n.
Proof.
  prop_perm_eq.
  solve_modular_permutation_equalities.
Qed.

#[export] Instance ZXSymmetricMonoidalCategory 
  : SymmetricMonoidalCategory ZXBraidedMonoidalCategory := {
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






From ViCaR Require Import CategoryAutomationCompatibility.

Section Testing.

(* Import (notations) CategoryAutomation. *)

Local Open Scope Cat_scope.

Lemma stack_nwire_distribute_r : forall {n m o p} (zx0 : ZX n m) (zx1 : ZX m o),
(zx0 ⟷ zx1) ↕ n_wire p ∝ (zx0 ↕ n_wire p) ⟷ (zx1 ↕ n_wire p).
Proof.
  to_Cat.
  intros.
Admitted.
  



Lemma test_part_rw : forall {nIn nOut} (zx : ZX nIn 0) (zx1 : ZX 0 nOut),
  zx ⟷ (⦰ ⟷ zx1) ∝ zx ⟷ zx1.
Proof.
  intros.
  to_Cat.
  assoc_rw_to_Cat compose_empty_r.
  easy.
Qed.

Lemma test_part_rw_long : forall {nIn nOut} 
  (zx0 zx2 zx3 zx4 zx5 zx6 zx7: ZX nIn nIn)
  (zx : ZX nIn 0) (zx1 : ZX 0 nOut),
  zx0 ⟷ (zx2 ⟷ (zx3 ⟷ (zx4 ⟷ (zx5 ⟷ 
  (zx6 ⟷ (zx7 ⟷ (zx ⟷ (⦰ ⟷ zx1)))))))) ∝ zx ⟷ zx1.
Proof.
  intros.
  to_Cat.
  assoc_rw_to_Cat compose_empty_r.
  Abort.

  
Lemma helper_tester_2 : forall {n m} (zx0 : ZX n m) (zx1 : ZX m O),
  zx0 ⟷ zx1 ⟷ ⦰ ∝ zx0 ⟷ zx1.
Proof.
  intros.
  apply compose_empty_r.
Qed.


Lemma test_part_rw_long : forall {nIn nOut} 
  (zx0 zx2 zx3 zx4 zx5 zx6 zx7: ZX nIn nIn)
  (zx : ZX nIn 0) (zx1 : ZX 0 nOut),
  zx0 ⟷ (zx2 ⟷ (zx3 ⟷ (zx4 ⟷ (zx5 ⟷ 
  (zx6 ⟷ (zx7 ⟷ (zx ⟷ (⦰ ⟷ zx1)))))))) ∝ zx ⟷ zx1.
Proof.
  intros.
  to_Cat.
  set (zx_empty := ⦰).
  unfold zx_empty.

  assoc_rw_to_Cat compose_empty_r.
  Abort.

Lemma test  :  forall {n m o} (zx0 : ZX n m) (zx1 : ZX m o),
	(zx0 ⟷ zx1) ↕ — ⟷ zx_braiding ∝ (zx0 ↕ —) ⟷ (zx1 ↕ —) ⟷ zx_braiding.
Proof.
  (* setoid_rewrite wire_to_n_wire. *)
  intros.
  rewrite wire_to_n_wire.
  to_Cat.
  foliate_LHS.
  Fail easy.
  cat_easy.
Qed.

Lemma test2 :  forall {n m o p} (zx0 : ZX n m) (zx1 : ZX o p),
	(zx0 ↕ zx1)  ∝ (zx0 ↕ n_wire _) ⟷ (n_wire _ ↕ zx1).
Proof.
  (* setoid_rewrite wire_to_n_wire. *)
  intros.
  to_Cat.
  foliate_LHS.
  easy. 
Qed.

End Testing.