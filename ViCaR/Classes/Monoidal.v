Require Import Category.
Require Import Setoid.

#[local] Set Universe Polymorphism.

Local Open Scope Cat_scope.
Local Open Scope Mor_scope.
Local Open Scope Obj_scope.

Declare Scope Mon_scope.
Delimit Scope Mon_scope with Mon.
Open Scope Mon_scope.


(* 
Removing the reservation to allow confining these to a particular scope.

Reserved Notation "x × y" (at level 40, left associativity). (* \times *)
Reserved Notation "x ⊗ y" (at level 40, left associativity). (* \otimes *) 
Reserved Notation "'λ_' x" (at level 30, no associativity). (* \lambda *) 
Reserved Notation "'ρ_' x" (at level 30, no associativity). (* \rho *)  
*)
Class MonoidalCategory {C : Type} (cC : Category C) : Type := {
  tensor : Bifunctor cC cC cC;
    (* where "x × y" := (tensor x y); *)
  mon_I : C;
    (* where "x ⊗ y" := (tensor @@ x, y) ;*)

  associator (A B M : C) : 
    tensor (tensor A B) M <~> tensor A (tensor B M);

  left_unitor (A : C) : tensor mon_I A <~> A;
    (* where "'λ_' x" := (left_unitor x); *)

  right_unitor (A : C) : tensor A mon_I <~> A;
    (* where "'ρ_' x" := (right_unitor x); *)

  (* Coherence conditions for α, λ, ρ *)
  associator_cohere {A B M N P Q : C} 
    (f : A ~> B) (g : M ~> N) (h : P ~> Q) : 
    associator A M P ∘ (tensor @@ f, (tensor @@ g, h)) 
    ≃ (tensor @@ (tensor @@ f, g), h) ∘ associator B N Q;
  left_unitor_cohere {A B : C} (f : A ~> B) : 
    left_unitor A ∘ f ≃ (tensor @@ id_ mon_I, f) ∘ left_unitor B;
  right_unitor_cohere {A B : C} (f : A ~> B) : 
    right_unitor A ∘ f ≃ (tensor @@ f, id_ mon_I) ∘ right_unitor B;

  (* Commutative diagrams *)
  triangle (A B : C) : 
    associator A mon_I B ∘ (tensor @@ id_ A, left_unitor B)
    ≃ tensor @@ right_unitor A, id_ B;
  pentagon (A B M N : C) : 
    (tensor @@ associator A B M, id_ N) 
    ∘ associator A (tensor B M) N
    ∘ (tensor @@ id_ A, associator B M N)
    ≃ associator (tensor A B) M N ∘ associator A B (tensor M N);
}.

Arguments MonoidalCategory {_} (_)%Cat.
Arguments tensor {_} {_}%Cat (mC)%Cat : rename.
Arguments mon_I {_} {_}%Cat (mC)%Cat : rename.
Arguments associator {_} {_}%Cat {mC}%Cat (_ _ _)%Obj : rename.
Arguments left_unitor {_} {_}%Cat {mC}%Cat (_)%Obj : rename.
Arguments right_unitor {_} {_}%Cat {mC}%Cat (_)%Obj : rename.
Arguments associator_cohere {_} {_}%Cat {mC}%Cat 
  {_ _ _ _ _ _}%Obj (_ _ _)%Mor : rename.
Arguments left_unitor_cohere {_} {_}%Cat {mC}%Cat {_ _}%Obj (_)%Mor : rename.
Arguments right_unitor_cohere {_} {_}%Cat {mC}%Cat {_ _}%Obj (_)%Mor : rename.
Arguments triangle {_} {_}%Cat {mC}%Cat (_ _)%Obj: rename.
Arguments pentagon {_} {_}%Cat {mC}%Cat (_ _ _ _)%Obj : rename.

Notation "'I'" := (mon_I _%Cat) (at level 0) : Mon_scope.
Notation "A '×' B" := (tensor _%Cat A%Obj B%Obj)
  (at level 40, left associativity) : Mon_scope. (* \times *)
Notation "f '⊗' g" := 
  (morphism_bimap (tensor _%Cat) f%Obj g%Obj) 
  (at level 40, left associativity) : Mon_scope . (* \otimes *)  
Notation "'λ_' x" := (left_unitor x) 
  (at level 20, no associativity) : Mon_scope. (* \lambda *) 
Notation "'ρ_' x" := (right_unitor x) 
  (at level 20, no associativity) : Mon_scope. (* \rho *) 

Add Parametric Morphism {C : Type}
  {cC : Category C} {mC: MonoidalCategory cC}
  (A1 B1 A2 B2 : C) : mC.(tensor).(morphism_bimap)
  with signature 
  (cC.(c_equiv) (A:=A1) (B:=B1)) ==> 
  (cC.(c_equiv) (A:=A2) (B:=B2)) ==> 
  cC.(c_equiv) as stack_equiv_mor.
Proof. intros. apply morphism_bicompat; assumption. Qed.


Add Parametric Morphism {C : Type}
  {cC : Category C} {mC : MonoidalCategory cC} : mC.(tensor).(obj_bimap)
  with signature 
  (@isomorphic C cC) ==> 
  (@isomorphic C cC) ==> 
  @isomorphic C cC as stack_isomorphic_mor.
Proof. intros A B [fAB [fBA [HfAB HfBA]]] M N [fMN [fNM [HfMN HfNM]]].
  exists (fAB ⊗ fMN); exists (fBA ⊗ fNM).
  rewrite <- 2!compose_bimap, HfAB, HfBA, HfMN, HfNM.
  rewrite 2!id_bimap; easy.
Qed.

Fixpoint n_times_r {C} {cC : Category C} {mC : MonoidalCategory cC} 
    (n : nat) (A : C) : C :=
  match n with 
  | O => I
  | S n' => A × (n_times_r n' A)
  end.

Fixpoint n_times_l {C} {cC : Category C} {mC : MonoidalCategory cC}
    (n : nat) (A : C) : C :=
  match n with 
  | O => I
  | S n' => (n_times_l n' A) × A
  end.

Fixpoint n_tensor_r {C} {cC : Category C} {mC : MonoidalCategory cC} 
    {A B : C} (n : nat) (f : A ~> B) 
  : (n_times_r n A ~> n_times_r n B) :=
  match n with
  | O => id_ I
  | S n' => f ⊗ (n_tensor_r n' f)
  end.

Fixpoint n_tensor_l {C} {cC : Category C} {mC : MonoidalCategory cC} 
    {A B : C} (n : nat) (f : A ~> B) 
  : (n_times_l n A ~> n_times_l n B) :=
  match n with
  | O => id_ I
  | S n' => (n_tensor_l n' f) ⊗ f
  end.

Arguments n_times_r {_} {_ _}%Cat _ _%Obj.
Arguments n_times_l {_} {_ _}%Cat _ _%Obj.
Arguments n_tensor_r {_} {_ _}%Cat {_ _}%Obj _ _%Mor.
Arguments n_tensor_l {_} {_ _}%Cat {_ _}%Obj _ _%Mor.

Add Parametric Morphism {C : Type} 
  {cC : Category C} {mC : MonoidalCategory cC} : (@n_times_r C cC mC)
  with signature 
  (@eq nat) ==> (@isomorphic C cC) ==> (@isomorphic C cC) 
  as n_times_r_isomorphic_mor.
Proof.
  intros n A B [fAB [fBA HAB]].
  exists (n_tensor_r n fAB); exists (n_tensor_r n fBA).
  induction n; simpl.
  - rewrite left_unit; split; easy.
  - rewrite <- 2!compose_bimap, (proj1 HAB), (proj2 HAB),
      (proj1 IHn), (proj2 IHn), 2!id_bimap.
    split; easy.
Qed.

Add Parametric Morphism {C : Type} 
  {cC : Category C} {mC : MonoidalCategory cC} : (@n_times_l C cC mC)
  with signature 
  (@eq nat) ==> (@isomorphic C cC) ==> (@isomorphic C cC) 
  as n_times_l_isomorphic_mor.
Proof.
  intros n A B [fAB [fBA HAB]].
  exists (n_tensor_l n fAB); exists (n_tensor_l n fBA).
  induction n; simpl.
  - rewrite left_unit; split; easy.
  - rewrite <- 2!compose_bimap, (proj1 HAB), (proj2 HAB),
      (proj1 IHn), (proj2 IHn), 2!id_bimap.
    split; easy.
Qed.

Add Parametric Morphism {C : Type} 
  {cC : Category C} {mC : MonoidalCategory cC} {A B : C} {n : nat} : 
  (@n_tensor_r C cC mC A B n) 
  with signature 
  (@c_equiv C cC A B) 
    ==> (@c_equiv C cC (n_times_r n A) (n_times_r n B))
  as n_tensor_r_equiv_mor.
Proof.
  intros f g Hfg.
  induction n.
  - easy.
  - apply morphism_bicompat; assumption.
Qed.

Add Parametric Morphism {C : Type} 
  {cC : Category C} {mC : MonoidalCategory cC} {A B : C} {n : nat} : 
  (@n_tensor_l C cC mC A B n) 
  with signature 
  (@c_equiv C cC A B) 
    ==> (@c_equiv C cC (n_times_l n A) (n_times_l n B))
  as n_tensor_l_equiv_mor.
Proof.
  intros f g Hfg.
  induction n.
  - easy.
  - apply morphism_bicompat; assumption.
Qed.


Lemma compose_tensor_iso_r : forall {C} {cC : Category C} 
  {mC : MonoidalCategory cC}
  {A B1 M1 B2 M2 : C} (f : A ~> B1 × B2) 
  (g1 : B1 <~> M1) (g2 : B2 <~> M2) (h : A ~> M1 × M2), 
    f ∘ g1⊗g2 ≃ h <-> f ≃ h ∘ (g1^-1 ⊗ g2^-1).
Proof.
  intros; split; intro Heq.
  - rewrite <- Heq, assoc, <- compose_bimap, 
      2!iso_inv_r, id_bimap, right_unit; easy.
  - rewrite Heq, assoc, <- compose_bimap, 
      2!iso_inv_l, id_bimap, right_unit; easy.
Qed.

Lemma compose_tensor_iso_r' : forall {C} {cC : Category C} 
  {mC : MonoidalCategory cC}
  {A B1 M1 B2 M2 : C} (f : A ~> B1 × B2) 
  (g1 : B1 <~> M1) (g2 : B2 <~> M2) (h : A ~> M1 × M2), 
  h ≃ f ∘ g1⊗g2 <-> h ∘ (g1^-1 ⊗ g2^-1) ≃ f.
Proof.
  intros. 
  split; symmetry; apply compose_tensor_iso_r; easy.
Qed.

Lemma compose_tensor_iso_l : forall {C} {cC : Category C} 
  {mC : MonoidalCategory cC}
  {A1 B1 M A2 B2 : C} (f1 : A1 <~> B1) (f2 : A2 <~> B2)
  (g : B1 × B2 ~> M) (h : A1 × A2 ~> M), 
  f1⊗f2 ∘ g ≃ h <-> g ≃ (f1^-1 ⊗ f2^-1) ∘ h.
Proof.
  intros; split; intro Heq.
  - rewrite <- Heq, <- assoc, <- compose_bimap,
      2!iso_inv_l, id_bimap, left_unit; easy.
  - rewrite Heq, <- assoc, <- compose_bimap, 
      2!iso_inv_r, id_bimap, left_unit; easy.
Qed.

Lemma compose_tensor_iso_l' : forall {C} {cC : Category C} 
  {mC : MonoidalCategory cC}
  {A1 B1 M A2 B2 : C} (f1 : A1 <~> B1) (f2 : A2 <~> B2)
  (g : B1 × B2 ~> M) (h : A1 × A2 ~> M), 
  h ≃ f1⊗f2 ∘ g <-> (f1^-1 ⊗ f2^-1) ∘ h ≃ g.
Proof.
  intros; split; symmetry; apply compose_tensor_iso_l; easy.
Qed.


Local Close Scope Mon_scope.
Local Close Scope Obj_scope.
Local Close Scope Mor_scope.
Local Close Scope Cat_scope.
