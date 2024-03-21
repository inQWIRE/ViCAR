Require Import Category.
Require Import Setoid.

#[local] Set Universe Polymorphism.

Local Open Scope Cat_scope.

Reserved Notation "x × y" (at level 34, left associativity). (* \times *)
Reserved Notation "x ⊗ y" (at level 34, left associativity). (* \otimes *) 
Reserved Notation "'λ_' x" (at level 20, no associativity). (* \lambda *) 
Reserved Notation "'ρ_' x" (at level 20, no associativity). (* \rho *)  
Reserved Notation "'α_' A , B , M" (at level 20, no associativity). (* \alpha *)

Class MonoidalCategory {C : Type} (cC : Category C) : Type := {
  obj_tensor : C -> C -> C
    where "x × y" := (obj_tensor x y);
  mor_tensor {A1 A2 B1 B2 : C} (f : A1 ~> B1) (g : A2 ~> B2) : 
    A1 × A2 ~> B1 × B2;
  mon_I : C;

  associator (A B M : C) : 
    (A × B) × M <~> A × (B × M);

  left_unitor (A : C) : mon_I × A <~> A;

  right_unitor (A : C) : A × mon_I <~> A;
}.
Arguments obj_tensor {_} {_}%Cat (mC)%Cat (A B)%Cat : rename.
Arguments mor_tensor {_} {_}%Cat (mC)%Cat {_ _ _ _}%Cat (_ _)%Cat : rename.
Arguments mon_I {_} {_}%Cat (mC)%Cat : rename.
Arguments associator {_} {_}%Cat {mC}%Cat (_ _ _)%Cat : rename.
Arguments left_unitor {_} {_}%Cat {mC}%Cat (_)%Cat : rename.
Arguments right_unitor {_} {_}%Cat {mC}%Cat (_)%Cat : rename.

Notation "'I'" := (mon_I _%Cat) (at level 0) : Cat_scope.
Notation "A '×' B" := (obj_tensor _%Cat A%Cat B%Cat)
  (at level 34, left associativity) : Cat_scope. (* \times *)
Notation "f '⊗' g" := 
  (mor_tensor _%Cat f%Cat g%Cat) 
  (at level 34, left associativity) : Cat_scope . (* \otimes *)  
Notation "'α_' A , B , M" := 
  (associator A%Cat B%Cat M%Cat)
  (at level 20, no associativity) : Cat_scope. (* \alpha *)
Notation "'λ_' x" := (left_unitor x) 
  (at level 20, no associativity) : Cat_scope. (* \lambda *) 
Notation "'ρ_' x" := (right_unitor x) 
  (at level 20, no associativity) : Cat_scope. (* \rho *) 



Class MonoidalCategoryCoherence {C : Type} {cC : Category C}
  {cCh : CategoryCoherence cC} (mC : MonoidalCategory cC) : Type := {
  to_base_struct_moncat := mC;
  tensor_id (A1 A2 : C) : (id_ A1) ⊗ (id_ A2) ≃ id_ (A1 × A2);
  tensor_compose {A1 B1 M1 A2 B2 M2 : C} 
    (f1 : A1 ~> B1) (g1 : B1 ~> M1) 
    (f2 : A2 ~> B2) (g2 : B2 ~> M2) :
    (f1 ∘ g1) ⊗ (f2 ∘ g2) ≃ f1 ⊗ f2 ∘ g1 ⊗ g2;
  tensor_compat {A1 B1 A2 B2 : C}
    (f f' : A1 ~> B1) (g g' : A2 ~> B2) :
    f ≃ f' -> g ≃ g' -> f ⊗ g ≃ f' ⊗ g';

  (* Coherence conditions for α, λ, ρ *)
  associator_cohere {A B M N P Q : C} 
    (f : A ~> B) (g : M ~> N) (h : P ~> Q) : 
    α_ A, M, P ∘ (f ⊗ (g ⊗ h)) 
    ≃ ((f ⊗ g) ⊗ h) ∘ α_ B, N, Q;
  left_unitor_cohere {A B : C} (f : A ~> B) : 
    λ_ A ∘ f ≃ (id_ I ⊗ f) ∘ λ_ B;
  right_unitor_cohere {A B : C} (f : A ~> B) : 
    ρ_ A ∘ f ≃ (f ⊗ id_ I) ∘ ρ_ B;

  (* Commutative diagrams *)
  triangle (A B : C) : 
    α_ A, I, B ∘ (id_ A ⊗ λ_ B)
    ≃ ρ_ A ⊗ id_ B;
  pentagon (A B M N : C) : 
    (α_ A, B, M ⊗ id_ N) 
    ∘ α_ A, (B × M), N
    ∘ (id_ A ⊗ α_ B, M, N)
    ≃ α_ (A × B), M, N ∘ α_ A, B, (M × N);
}.

Coercion to_base_struct_moncat : MonoidalCategoryCoherence >-> MonoidalCategory.

Arguments associator_cohere {_} {_ _ _}%Cat {mCh}%Cat 
  {_ _ _ _ _ _}%Cat (_ _ _)%Cat : rename.
Arguments left_unitor_cohere {_} {_ _ _}%Cat {mCh}%Cat {_ _}%Cat (_)%Cat : rename.
Arguments right_unitor_cohere {_} {_ _ _}%Cat {mCh}%Cat {_ _}%Cat (_)%Cat : rename.
Arguments triangle {_} {_ _ _}%Cat {mCh}%Cat (_ _)%Cat: rename.
Arguments pentagon {_} {_ _ _}%Cat {mCh}%Cat (_ _ _ _)%Cat : rename.

Add Parametric Morphism {C : Type} {cC : Category C} 
  {mC : MonoidalCategory cC} {cCh : CategoryCoherence cC} 
  {mCh : MonoidalCategoryCoherence mC} {A1 B1 A2 B2 : C} : (mor_tensor mCh)
  with signature 
  (cC.(c_equiv) (A:=A1) (B:=B1)) ==> 
  (cC.(c_equiv) (A:=A2) (B:=B2)) ==> 
  cC.(c_equiv) as mor_tensor_equiv_mor.
Proof. intros. apply tensor_compat; assumption. Qed.

Section TensorBifunctor.

Context {C : Type} {cC : Category C} (mC : MonoidalCategory cC)
  {cCh : CategoryCoherence cC} {mCh : MonoidalCategoryCoherence mC}.

#[export, program] Instance TensorIsomorphism {A1 B1 A2 B2} 
  (f1 : A1 <~> B1) (f2 : A2 <~> B2) : A1 × A2 <~> B1 × B2 := {
  forward := f1 ⊗ f2;
  reverse := f1^-1 ⊗ f2^-1;
}.
Next Obligation.
  rewrite <- 2!mCh.(tensor_compose), 2!iso_inv_r, 2!iso_inv_l, 2!tensor_id.
  easy.
Qed.

#[export] Instance tensor : Bifunctor cC cC cC := {
  obj_bimap := mC.(obj_tensor);
  morphism_bimap := fun A1 B1 B1 B2 => mC.(mor_tensor);
  id_bimap := tensor_id;
  compose_bimap := fun A1 B1 M1 A2 B2 M2 => tensor_compose;
  morphism_bicompat := fun A1 B1 A2 B2 => tensor_compat;
}.

Add Parametric Morphism (A1 B1 A2 B2 : C) : tensor.(morphism_bimap)
  with signature 
  (cC.(c_equiv) (A:=A1) (B:=B1)) ==> 
  (cC.(c_equiv) (A:=A2) (B:=B2)) ==> 
  cC.(c_equiv) as tensor_equiv_mor.
Proof. intros. apply morphism_bicompat; assumption. Qed.


Add Parametric Morphism : tensor.(obj_bimap)
  with signature 
  (@isomorphic C cC) ==> 
  (@isomorphic C cC) ==> 
  @isomorphic C cC as stack_isomorphic_mor.
Proof. intros A B [fAB [fBA [HfAB HfBA]]] M N [fMN [fNM [HfMN HfNM]]].
  exists (fAB ⊗ fMN); exists (fBA ⊗ fNM).
  simpl.
  rewrite <- 2!mCh.(tensor_compose), HfAB, HfBA, HfMN, HfNM.
  rewrite 2!mCh.(tensor_id); easy.
Qed.

End TensorBifunctor.

Arguments tensor {_} {_}%Cat (mC)%Cat {_ _}%Cat.
Arguments TensorIsomorphism {_} {_ mC cCh mCh}%Cat {_ _ _ _}%Cat (_ _)%Cat.

Section TensorIsomorphismRewrites.

Context {C : Type} {cC : Category C} {mC : MonoidalCategory cC}
  {cCh : CategoryCoherence cC} {mCh : MonoidalCategoryCoherence mC}.

Lemma compose_tensor_iso_r : forall {A B1 M1 B2 M2 : C} (f : A ~> B1 × B2) 
  (g1 : B1 <~> M1) (g2 : B2 <~> M2) (h : A ~> M1 × M2), 
    f ∘ g1⊗g2 ≃ h <-> f ≃ h ∘ (g1^-1 ⊗ g2^-1).
Proof.
  intros; split; intro Heq.
  - rewrite <- Heq, cCh.(assoc), <- mCh.(tensor_compose),
      2!iso_inv_r, mCh.(tensor_id), cCh.(right_unit); easy.
  - rewrite Heq, cCh.(assoc), <- mCh.(tensor_compose),
    2!iso_inv_l, mCh.(tensor_id), cCh.(right_unit); easy. 
Qed.

Lemma compose_tensor_iso_r' : forall {A B1 M1 B2 M2 : C} (f : A ~> B1 × B2) 
  (g1 : B1 <~> M1) (g2 : B2 <~> M2) (h : A ~> M1 × M2), 
  h ≃ f ∘ g1⊗g2 <-> h ∘ (g1^-1 ⊗ g2^-1) ≃ f.
Proof.
  intros. 
  split; symmetry; apply compose_tensor_iso_r; easy.
Qed.

Lemma compose_tensor_iso_l : forall {A1 B1 M A2 B2 : C} 
  (f1 : A1 <~> B1) (f2 : A2 <~> B2) 
  (g : B1 × B2 ~> M) (h : A1 × A2 ~> M), 
  f1⊗f2 ∘ g ≃ h <-> g ≃ (f1^-1 ⊗ f2^-1) ∘ h.
Proof.
  intros; split; intro Heq.
  - rewrite <- Heq, <- cCh.(assoc), <- mCh.(tensor_compose),
      2!iso_inv_l, mCh.(tensor_id), cCh.(left_unit); easy.
  - rewrite Heq, <- cCh.(assoc), <- mCh.(tensor_compose),
      2!iso_inv_r, mCh.(tensor_id), cCh.(left_unit); easy. 
Qed.

Lemma compose_tensor_iso_l' : forall {A1 B1 M A2 B2 : C} 
  (f1 : A1 <~> B1) (f2 : A2 <~> B2)
  (g : B1 × B2 ~> M) (h : A1 × A2 ~> M), 
  h ≃ f1⊗f2 ∘ g <-> (f1^-1 ⊗ f2^-1) ∘ h ≃ g.
Proof.
  intros; split; symmetry; apply compose_tensor_iso_l; easy.
Qed.

End TensorIsomorphismRewrites.

Local Close Scope Cat_scope.
