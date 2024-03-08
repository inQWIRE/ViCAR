Require Import Setoid.
From ViCaR Require Export CategoryTypeclass.

Require Import Psatz.

From QuantumLib Require Import Prelim.
From ViCaR Require Import ExamplesAutomation.
From ViCaR Require Export CategoryTypeclass.


Close Scope C_scope.
Close Scope R_scope.
(* Phantom types... *)
Definition reln (n m : nat) := relation nat.

Definition reln_equiv {n m} (A B : reln n m) :=
  forall i j, i < n -> j < m -> A i j <-> B i j.

Definition compose_relns {n m o : nat} (A : reln n m) (B : reln m o) : reln n o :=
  fun i j => exists k, k < m /\ A i k /\ B k j.

Local Notation "A '~' B" := (reln_equiv A B) (at level 80).
Local Notation "A '\o' B" := (compose_relns A B) (at level 40, left associativity).

Definition idn {n} : reln n n :=
  fun i j => i = j.

Lemma compose_relns_assoc {n m o p : nat} 
  (A : reln n m) (B : reln m o) (C : reln o p) :
  A \o B \o C ~ A \o (B \o C).
Proof.
  intros i j Hi Hj.
  unfold compose_relns. 
  split;
  [ intros [? [? [[? [? [? ?]]] ?]]]
  | intros [? [? [? [? [? [? ?]]]]]]];
    eexists; repeat split; try eexists; 
    repeat split; eassumption.
Qed.

Lemma compose_relns_id_l {n m} (A : reln n m) :
  idn \o A ~ A.
Proof.
  intros i j Hi Hj.
  unfold compose_relns, idn.
  split; 
  [intros [? [? []]]; subst; easy | 
  intros; eexists; repeat split; eassumption].
Qed.

Lemma compose_relns_id_r {n m} (A : reln n m) :
  A \o idn ~ A.
Proof.
  intros i j Hi Hj.
  unfold compose_relns, idn.
  split; 
  [intros [? [? []]]; subst; easy | 
  intros; eexists; repeat split; eassumption].
Qed.

Lemma reln_equiv_equivalence {n m} : 
  equivalence (reln n m) (@reln_equiv n m).
Proof.
  split; unfold reln_equiv; try easy.
  - intros A B C HAB HBC i j Hi Hj.
    rewrite HAB by easy.
    apply HBC; easy.
  - intros A B HAB. symmetry; apply HAB; easy.
Qed.

Lemma compose_relns_compat {n m o} : forall (A A' : reln n m),
  A ~ A' -> forall (B B' : reln m o),
  B ~ B' -> A \o B ~ A' \o B'.
Proof.
  unfold reln_equiv, compose_relns.
  intros A A' HA B B' HB i j Hi Hj.
  split;
  intros [k [Hk [HAk HBk]]];
  [ rewrite HA in HAk by easy; rewrite HB in HBk by easy
  | rewrite <-HA in HAk by easy; rewrite <-HB in HBk by easy];
  eexists;
  repeat split; try eassumption.
Qed.

#[export] Instance RelationCategory : Category nat := {
  morphism := @reln;
  equiv := @reln_equiv;
  equiv_rel := @reln_equiv_equivalence;
  compose := @compose_relns;
  compose_compat := @compose_relns_compat;
  assoc := @compose_relns_assoc;
  c_identity := @idn;
  left_unit := @compose_relns_id_l;
  right_unit := @compose_relns_id_r;
}.

Definition stack_relns n0 m0 n1 m1 (A : reln n0 m0) (B : reln n1 m1) 
  : reln (n0+n1) (m0+m1) :=
  fun i j => 
    (i < n0) /\ (j < m0) /\ A i j
    \/ (n0 <= i < n0 + n1) /\ (m0 <= j < m0 + m1) /\ B (i - n0) (j - m0).





Ltac solve_relations_fast :=  
  repeat (repeat (intros ?); subst; try lia; match goal with
  | H : (exists _, _) |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | |- _ <-> _ => split
  | |- _ /\ _ => split
  | |- ?f ?x ?y => match type of f with reln ?n ?m => eassumption end
  | |- ?x = _ => match type of x with nat => reflexivity || lia end
  | |- _ \/ _ => (left; solve [solve_relations_fast; lia]) 
    || (right; solve [solve_relations_fast; lia]) || (* print_state; *) fail 2
  
  | |- exists _, _ => 
    (* idtac "trying vars"; print_state;  *)
    match goal with
      | x : nat |- _ => match goal with 
        | _ : reln x _ |- _ => (* idtac "not" x; *) fail 1
        | _ : reln _ x |- _ => (* idtac "not" x; *) fail 1
        | _ => exists x; (* idtac "yes" x; *) (solve [solve_relations_fast; lia])
        end
      end
  | H : ?A ?i ?j |- ?A ?i' ?j' =>
    match type of A with 
    | reln ?n ?m => 
      (* idtac "matched " H " :"; print_state;  *)
      (apply H || ( (* idtac "needed rewrite"; *)
      replace i' with i by lia; replace j' with j by lia; apply H)
      (* || idtac "failed" *)
      )
    end
  | H : ?A ~ ?A' |- ?A ?i ?j => 
    eassumption || rewrite (H i j) by lia; eassumption
  | H : ?A ~ ?A' |- ?A' ?i ?j => 
    eassumption || rewrite <- (H i j) by lia; eassumption

  
  end);
  repeat ( 
    try eassumption;
    try reflexivity;
    try easy;
    try lia);
  try lia.


Ltac __solve_relations_end := 
  try eassumption;
  try reflexivity;
  try easy;
  (* try lia); *)
  try lia;
  try match goal with
  | |- ?f ?x ?y => match type of f with reln ?n ?m => eassumption end
  | |- ?x = _ => match type of x with nat => reflexivity || lia end
  | H : ?A ?i ?j |- ?A ?i' ?j' =>
    match type of A with 
    | reln ?n ?m => 
      (* idtac "matched " H " :"; print_state;  *)
      (apply H || ( (* idtac "needed rewrite"; *)
      replace i' with i by lia; replace j' with j by lia; apply H)
      (* || idtac "failed" *)
      )
    end
  | H : ?A ~ ?A' |- ?A ?i ?j => 
    eassumption || rewrite (H i j) by lia; eassumption
  | H : ?A ~ ?A' |- ?A' ?i ?j => 
    eassumption || rewrite <- (H i j) by lia; eassumption
    (*
      match type of H with 
      | _ < _ => fail 1
      | _ <= _ => fail 1
      | _ =>
      (* idtac "matched " H " :"; print_state;  *)
      (apply H || ( (* idtac "needed rewrite"; *)
      replace i' with i by lia; replace j' with j by lia; apply H)
      (* || idtac "failed" *)
      )
      end
    *)
  end.


Ltac __solve_relations_l := idtac.
Ltac __solve_relations_r := idtac.

Ltac __solve_relations_l ::= 
  repeat (repeat (intros ?); subst; auto; try lia; match goal with
  | H : (exists _, _) |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | |- _ <-> _ => split
  | |- _ /\ _ => split
  | H : _ \/ _ |- _ => destruct H; [__solve_relations_l | __solve_relations_r]
  | |- _ \/ _ => 
       (left; solve [__solve_relations_l; lia]) 
    || (right; solve [__solve_relations_r; lia]) 
    || (* print_state; *) fail 2
  | |- exists _, _ => 
    (* idtac "trying vars"; print_state;  *)
    match goal with
      | x : nat |- _ => match goal with 
        | _ : reln x _ |- _ => (* idtac "not" x; *) fail 1
        | _ : reln _ x |- _ => (* idtac "not" x; *) fail 1
        | _ => exists x; (* idtac "yes" x; *) (solve [__solve_relations_l; lia])
        end
      end; match goal with
      | |- _ => (* idtac "none worked"; *) eexists
    end
  end);
  __solve_relations_end.

Ltac __solve_relations_r ::= 
  repeat (repeat (intros ?); subst; auto; try lia; match goal with
  | H : (exists _, _) |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | |- _ <-> _ => split
  | |- _ /\ _ => split
  | H : _ \/ _ |- _ => destruct H; [__solve_relations_l | __solve_relations_r]
  | |- _ \/ _ => 
       (right; solve [__solve_relations_r; lia])
    || (left; solve [__solve_relations_l; lia]) 
    || (* print_state; *) fail 2
  | |- exists _, _ => 
    (* idtac "trying vars"; print_state;  *)
    match goal with
      | x : nat |- _ => match goal with 
        | _ : reln x _ |- _ => (* idtac "not" x; *) fail 1
        | _ : reln _ x |- _ => (* idtac "not" x; *) fail 1
        | _ => exists x; (* idtac "yes" x; *) (solve [__solve_relations_r; lia])
        end
      end; match goal with
      | |- _ => (* idtac "none worked"; *) eexists
    end
  end);
  __solve_relations_end.

Ltac solve_relations :=
  simpl in *;
  unfold idn, compose_relns, stack_relns, reln_equiv in *;
  __solve_relations_l.

Lemma stack_relns_idn : forall n m,
  stack_relns n n m m idn idn ~ idn.
Proof.
  intros n m i j Hi Hj;
  unfold stack_relns, "id_"; simpl;
  unfold idn;
  lia.
Qed.

Lemma stack_relns_compose : forall n0 m0 o0 n1 m1 o1 
  (A1 : reln n0 m0) (B1 : reln m0 o0) (A2 : reln n1 m1) (B2 : reln m1 o1),
  stack_relns n0 o0 n1 o1 (A1 \o B1) (A2 \o B2) ~ 
  stack_relns n0 m0 n1 m1 A1 A2 \o stack_relns m0 o0 m1 o1 B1 B2.
Proof.
  intros n0 m0 o0 n1 m1 o1 A1 B1 A2 B2.
  simpl. 
  unfold stack_relns, compose_relns.
  intros i j Hi Hj.
  split.
  + intros [[Hi' [Hj' [k [Hk [HAk HBk]]]]] | [Hi' [Hj' [k [Hk [HAk HBk]]]]]].
    * exists k; split; [lia|].
      split; left; repeat split; lia || easy.
    * exists (m0 + k); split; [lia|].
      split; right; repeat split; lia || (try easy);
      replace (m0+k-m0) with k by lia; easy.      
  + intros [k [Hk [[[? [? ?]] | [? [? ?]]] [[? [? ?]] | [[? ?] [? ?]]]]]]; 
    try lia; [left | right];
    repeat (split; try easy); eexists; repeat split; try eassumption; lia.
Qed.

Lemma stack_relns_compat : forall n0 m0 n1 m1 
  (A A' : reln n0 m0) (B B' : reln n1 m1), A ~ A' -> B ~ B' ->
  stack_relns n0 m0 n1 m1 A B ~ stack_relns n0 m0 n1 m1 A' B'.
Proof.
  simpl. 
  intros n0 m0 n1 m1 A A' B B' HA HB.
  revert n0 m0 n1 m1 A A' B B' HA HB.
  intros i j Hi Hj.
  simpl in *.
  unfold stack_relns, reln_equiv in *.
  split;
  (intros [[? [? ?]] | [? [? ?]]]; [left | right]);
  (split; [lia | split; [lia | ]]);
  (rewrite 1?HA, 1?HB by lia; easy) || 
  (rewrite <- 1?HA, <- 1?HB by lia; easy).
Qed.

#[export] Instance StackRelnsBifunctor : 
  Bifunctor RelationCategory RelationCategory RelationCategory. 
  refine {|
    obj2_map := Nat.add;
    morphism2_map := stack_relns;
  |}.
Proof.
  - apply stack_relns_idn.
  - apply stack_relns_compose.
  - apply stack_relns_compat.
Defined.

#[export] Instance RelationMonoidalCategory : MonoidalCategory nat := {
  tensor := StackRelnsBifunctor;
  I := O;
  
  associator := fun n m o => {|
  forward := (@idn (n + m + o) : reln (n + m + o) (n + (m +o)));
  reverse := (@idn (n + m + o) : reln (n + (m +o)) (n + m + o));
  isomorphism_inverse := ltac:(abstract(solve_relations));
  |};

  left_unitor := fun n => {|
  forward := (@idn n : reln (0 + n) n);
  reverse := (@idn n : reln n (0 + n));
  isomorphism_inverse := ltac:(abstract(solve_relations));
  |};

  right_unitor := fun n => {|
  forward := (@idn n : reln (n + 0) n);
  reverse := (@idn n : reln n (n + 0));
  isomorphism_inverse := ltac:(abstract(solve_relations));
  |};

  associator_cohere := ltac:(abstract(solve_relations));
  left_unitor_cohere := ltac:(abstract(solve_relations));
  right_unitor_cohere := ltac:(abstract(solve_relations));

  pentagon := ltac:(abstract(solve_relations)); 
  triangle :=  ltac:(abstract(solve_relations));
}.

Definition braid_relation n m : reln (n + m) (m + n) :=
  fun i j => 
  (i < n) /\ (m <= j <= m + n) /\ (i = j - m) \/
  (n <= i < n + m) /\ (j < m) /\ (i - n = j).

Definition BraidRelationIsomorphism n m : Isomorphism (n + m) (m + n).
  refine ({| 
    forward := braid_relation n m;
    reverse := braid_relation m n; |}).
Proof.
  unfold braid_relation.
  solve_relations; intros; subst j.
  - bdestruct (i <? n); [
      exists (i + m) | exists (i - n)
    ]; lia.
  - bdestruct (i <? m); [
      exists (i + n) | exists (i - m)
    ]; lia.
Defined.

#[export] Instance BraidRelationNaturalBiIsomorphism :
  NaturalBiIsomorphism StackRelnsBifunctor (CommuteBifunctor StackRelnsBifunctor).
  apply Build_NaturalBiIsomorphism with BraidRelationIsomorphism.
  abstract(simpl;
  unfold braid_relation;
  solve_relations;
  [ exists (i + A2) | exists (i - A1) | exists (j + B1) | exists (j - B2) ];
  solve_relations).
Defined.

Lemma reln_hexagon_1 : forall A B M : nat,
  (morphism2_map (BraidRelationNaturalBiIsomorphism A B) (id_ M) ∘ associator
    ∘ morphism2_map (id_ B) (BraidRelationNaturalBiIsomorphism A M)
   ≃ associator ∘ BraidRelationNaturalBiIsomorphism A (B × M) ∘ associator)%Cat.
Proof.
  unfold braid_relation.
  simpl (forward).
  simpl (obj2_map).
  intros n m o.

  rewrite (Nat.add_comm m n).
  replace (m + o + n) with (n + m + o) by lia.
  replace (m + (o + n)) with (n + m + o) by lia.
  replace (m + (n + o)) with (n + m + o) by lia.
  replace (n + (m + o)) with (n + m + o) by lia.
  rewrite right_unit, left_unit.
  rewrite (Nat.add_comm m n).
  rewrite right_unit.

  simpl.
  unfold braid_relation, idn, stack_relns, compose_relns.
  intros i j Hi Hj.
  split.
  + solve_relations.
  + intros [H1 | H2].
    * exists (i + m).
      split; [lia |].
      split; [left; lia |].
      right.
      split; [lia|].
      split; [lia|].
      left; lia.
    * do 2 destruct H2 as [? H2]. 
      subst j.
      bdestruct (n + m <=? i).
      --exists i; split; [lia | ]; 
        split; [right; lia |];
        right; split; [lia | ];
        split; [lia | ]; right; lia.
      --exists (i-n). split; [lia | ];
        split; [left; lia |].
        left; split; lia.
Qed.

Lemma reln_hexagon_2 : forall A B M : nat,
(morphism2_map (BraidRelationNaturalBiIsomorphism B A ^-1) (id_ M) ∘ associator
 ∘ morphism2_map (id_ B) (BraidRelationNaturalBiIsomorphism M A ^-1)
 ≃ associator ∘ BraidRelationNaturalBiIsomorphism (B × M) A ^-1 ∘ associator)%Cat. 
Proof.
  simpl (forward).
  simpl (reverse).
  simpl (obj2_map).
  intros n m o.

  rewrite (Nat.add_comm m n).
  replace (m + o + n) with (n + m + o) by lia.
  replace (m + (o + n)) with (n + m + o) by lia.
  replace (m + (n + o)) with (n + m + o) by lia.
  replace (n + (m + o)) with (n + m + o) by lia.
  rewrite right_unit, left_unit.
  (* rewrite (Nat.add_comm m n). *)
  rewrite right_unit.
  simpl.
  unfold braid_relation, idn, stack_relns, compose_relns.
  intros i j Hi Hj.
  split.
  + solve_relations.
  + intros [H1 | H2].
    * exists (i + m).
      split; [lia |].
      split; [left; lia |].
      right.
      split; [lia|].
      split; [lia|].
      left; lia.
    * do 2 destruct H2 as [? H2]. 
      subst j.
      bdestruct (n + m <=? i).
      --exists i; split; [lia | ]; 
        split; [right; lia |];
        right; split; [lia | ];
        split; [lia | ]; right; lia.
      --exists (i-n). split; [lia | ];
        split; [left; lia |].
        left; split; lia.
Qed.

#[export] Instance RelationBraidedMonoidalCategory :
  BraidedMonoidalCategory nat.
  apply Build_BraidedMonoidalCategory with BraidRelationNaturalBiIsomorphism.
  - apply reln_hexagon_1.
  - apply reln_hexagon_2.
Defined.

#[export] Instance RelationSymmetricMonoidalCategory :
  SymmetricMonoidalCategory nat := {
  symmetry := ltac:(reflexivity)
}.

Definition flipn {n m} (A : reln n m) : reln m n :=
  fun i j => A j i.

Lemma flipn_idn {n} : 
  flipn (@idn n) ~ @idn n.
Proof.
  easy.
Qed.

Lemma flipn_compose {n m o} (A : reln n m) (B : reln m o) :
  flipn (A \o B) ~ flipn B \o flipn A.
Proof.
  unfold flipn.
  solve_relations.
Qed.

Lemma flipn_compat {n m} (A B : reln n m) : 
  A ~ B -> flipn A ~ flipn B.
Proof.
  unfold flipn.
  solve_relations.
Qed.

#[export] Instance RelationDaggerCategory : 
  DaggerCategory nat. 
  apply Build_DaggerCategory with (fun A B => flipn).
  - reflexivity.
  - apply @flipn_idn.
  - apply @flipn_compose.
  - apply @flipn_compat.
Defined.

#[export] Instance RelationDaggerMonoidalCategory : 
  DaggerMonoidalCategory nat.
Proof.
  apply Build_DaggerMonoidalCategory.
  - simpl ; unfold flipn.
    solve_relations.
  - unfold unitary; simpl; unfold flipn. 
    solve_relations.
  - unfold unitary; simpl; unfold flipn. 
    solve_relations.
  - unfold unitary; simpl; unfold flipn. 
    solve_relations.
Qed.


