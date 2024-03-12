Require Import Category.
Require Import Setoid.

#[local] Set Universe Polymorphism.

Local Open Scope Cat_scope.

Reserved Notation "x × y" (at level 40, left associativity). (* \times *)
Reserved Notation "x ⊗ y" (at level 40, left associativity). (* \otimes *) 
Reserved Notation "'λ_' x" (at level 30, no associativity). (* \lambda *) 
Reserved Notation "'ρ_' x" (at level 30, no associativity). (* \rho *) 
Class MonoidalCategory (C : Type) `{cC : Category C} : Type := {
  tensor : Bifunctor cC cC cC
    where "x × y" := (tensor x y);
  I : C
    where "x ⊗ y" := (tensor @@ x, y);

  associator {A B M : C} : (A × B) × M <~> A × (B × M);

  left_unitor {A : C} : I × A <~> A
    where "'λ_' x" := (@left_unitor x);

  right_unitor {A : C} : A × I <~> A
    where "'ρ_' x" := (@right_unitor x);

  (* Coherence conditions for α, λ, ρ *)
  associator_cohere {A B M N P Q : C} 
    {f : A ~> B} {g : M ~> N} {h : P ~> Q} : 
    associator ∘ (f ⊗ (g ⊗ h)) ≃ ((f ⊗ g) ⊗ h) ∘ associator;
  left_unitor_cohere {A B : C} {f : A ~> B} : 
    left_unitor ∘ f ≃ ((c_identity I) ⊗ f) ∘ left_unitor;
  right_unitor_cohere {A B : C} {f : A ~> B} : 
    right_unitor ∘ f ≃ (f ⊗ (c_identity I)) ∘ right_unitor;

  (* Commutative diagrams *)
  triangle {A B : C} : 
    associator ∘ ((c_identity A) ⊗ left_unitor)
    ≃ right_unitor ⊗ (c_identity B);
  pentagon {A B M N : C} : 
    (associator ⊗ (c_identity N)) ∘ associator ∘ ((c_identity A) ⊗ associator)
    ≃ @associator (A × B) M N ∘ associator;

(*
  tensor : C -> C -> C
    where "x × y" := (tensor x y);
  I : C;

  tensor_morph {A B M N : C} : 
    (A ~> M) -> (B ~> N) -> (A × B) ~> (M × N)
    where "x ⊗ y" := (tensor_morph x y);

  tensor_morph_compat {A B M N : C} : 
    forall (f g : A ~> B), f ≃ g ->
    forall (h j : M ~> N), h ≃ j ->
    f ⊗ h ≃ g ⊗ j;
  
  (* These are all isomorphisms *)
  associator {A B M : C} : (A × B) × M ~> A × (B × M);
  inv_associator {A B M : C} : A × (B × M) ~> (A × B) × M;
  associator_inv_compose {A B M : C} : associator ∘ inv_associator
    ≃ c_identity ((A × B) × M);
  inv_associator_compose {A B M : C} : inv_associator ∘ associator 
    ≃ c_identity (A × (B × M));

  left_unitor {A : C} : I × A ~> A;
  inv_left_unitor {A : C} : A ~> I × A;
  left_inv_compose {A : C} : 
    left_unitor ∘ inv_left_unitor ≃ c_identity (I × A);
  inv_left_compose {A : C} : 
    inv_left_unitor ∘ left_unitor ≃ c_identity A;

  right_unitor {A : C} : A × I ~> A;
  inv_right_unitor {A : C} : A ~> A × I;
  right_inv_compose {A : C} : 
    right_unitor ∘ inv_right_unitor ≃ c_identity (A × I);
  inv_right_compose {A : C} : 
    inv_right_unitor ∘ right_unitor ≃ c_identity A;

  bifunctor_id {A B : C} : 
    (c_identity A) ⊗ (c_identity B) ≃ c_identity (A × B);
  bifunctor_comp {A B M N P Q : C} 
    {f : A ~> B} {g : B ~> M}
    {h : N ~> P} {k : P ~> Q} : 
    (f ∘ g) ⊗ (h ∘ k) ≃ (f ⊗ h) ∘ (g ⊗ k);

  (* Coherence conditions for α, λ, ρ *)
  associator_cohere {A B M N P Q : C} 
    {f : A ~> B} {g : M ~> N} {h : P ~> Q} : 
    associator ∘ (f ⊗ (g ⊗ h)) ≃ ((f ⊗ g) ⊗ h) ∘ associator;
  left_unitor_cohere {A B : C} {f : A ~> B} : 
    left_unitor ∘ f ≃ ((c_identity I) ⊗ f) ∘ left_unitor;
  right_unitor_cohere {A B : C} {f : A ~> B} : 
    right_unitor ∘ f ≃ (f ⊗ (c_identity I)) ∘ right_unitor;

  (* Commutative diagrams *)
  triangle {A B : C} : 
    associator ∘ ((c_identity A) ⊗ left_unitor)
    ≃ right_unitor ⊗ (c_identity B);
  pentagon {A B M N : C} : 
    (associator ⊗ (c_identity N)) ∘ associator ∘ ((c_identity A) ⊗ associator)
    ≃ @associator (A × B) M N ∘ associator;
*)
}.
Infix "×" := tensor (at level 40, left associativity) : Cat_scope. (* \times *)
Notation "A '⊗' B" := 
  (@morphism2_map _ _ _ _ _ _ (@tensor _ _ _) _ _ _ _ A B) 
  (at level 40, left associativity) (* : Cat_scope *) . (* \otimes *)  
Notation "'λ_' x" := (@left_unitor _ _ _ x) (at level 30, no associativity). (* \lambda *) 
Notation "'ρ_' x" := (@right_unitor _ _ _ x) (at level 30, no associativity). (* \rho *) 

(* TODO: Conflicts with VyZX, I think. Or maybe QuantumLib.
Notation "A '⨂' B" := (@morphism2_map _ _ _ _ _ _ (tensor) _ _ _ _ A B)
  (at level 40, only printing). *)

Add Parametric Morphism {C : Type}
  `{Cat : Category C, MonCat: !MonoidalCategory C}
  (n0 m0 n1 m1 : C) : tensor.(morphism2_map)
  with signature 
  (@Category.equiv C Cat n0 m0) ==> 
  (@Category.equiv C Cat n1 m1) ==> 
  Category.equiv as stack_equiv_mor.
Proof. intros. apply morphism2_compat; assumption. Qed.


Add Parametric Morphism {C : Type}
  `{Cat : Category C, MonCat : !MonoidalCategory C} : tensor.(obj2_map)
  with signature 
  (@isomorphic C Cat) ==> 
  (@isomorphic C Cat) ==> 
  @isomorphic C Cat as stack_isomorphic_mor.
Proof. intros A B [fAB [fBA [HfAB HfBA]]] M N [fMN [fNM [HfMN HfNM]]].
  exists (fAB ⊗ fMN); exists (fBA ⊗ fNM).
  rewrite <- 2!compose2_map, HfAB, HfBA, HfMN, HfNM.
  rewrite 2!id2_map; easy.
Qed.

Fixpoint n_times_r {C} `{MonoidalCategory C} (n : nat) (A : C) : C :=
  match n with 
  | O => I
  | S n' => A × (n_times_r n' A)
  end.

Fixpoint n_times_l {C} `{MonoidalCategory C} (n : nat) (A : C) : C :=
  match n with 
  | O => I
  | S n' => (n_times_l n' A) × A
  end.

Fixpoint n_tensor_r {C} `{MonoidalCategory C} {A B : C} (n : nat) (f : A ~> B) 
  : (n_times_r n A ~> n_times_r n B) :=
  match n with
  | O => id_ I
  | S n' => f ⊗ (n_tensor_r n' f)
  end.

Fixpoint n_tensor_l {C} `{MonoidalCategory C} {A B : C} (n : nat) (f : A ~> B) 
  : (n_times_l n A ~> n_times_l n B) :=
  match n with
  | O => id_ I
  | S n' => (n_tensor_l n' f) ⊗ f
  end.

Add Parametric Morphism {C : Type} 
  `{cC : Category C, cMonC : !MonoidalCategory C} : (@n_times_r C cC cMonC)
  with signature 
  (@eq nat) ==> (@isomorphic C cC) ==> (@isomorphic C cC) 
  as n_times_r_isomorphic_mor.
Proof.
  intros n A B [fAB [fBA HAB]].
  exists (n_tensor_r n fAB); exists (n_tensor_r n fBA).
  induction n; simpl.
  - rewrite left_unit; split; easy.
  - rewrite <- 2!compose2_map, (proj1 HAB), (proj2 HAB),
      (proj1 IHn), (proj2 IHn), 2!id2_map.
    split; easy.
Qed.

Add Parametric Morphism {C : Type} 
  `{cC : Category C, cMonC : !MonoidalCategory C} : (@n_times_l C cC cMonC)
  with signature 
  (@eq nat) ==> (@isomorphic C cC) ==> (@isomorphic C cC) 
  as n_times_l_isomorphic_mor.
Proof.
  intros n A B [fAB [fBA HAB]].
  exists (n_tensor_l n fAB); exists (n_tensor_l n fBA).
  induction n; simpl.
  - rewrite left_unit; split; easy.
  - rewrite <- 2!compose2_map, (proj1 HAB), (proj2 HAB),
      (proj1 IHn), (proj2 IHn), 2!id2_map.
    split; easy.
Qed.

Add Parametric Morphism {C : Type} 
  `{cC : Category C, cMonC : !MonoidalCategory C} {A B : C} {n : nat} : 
  (@n_tensor_r C cC cMonC A B n) 
  with signature 
  (@Category.equiv C cC A B) 
    ==> (@Category.equiv C cC (n_times_r n A) (n_times_r n B))
  as n_tensor_r_equiv_mor.
Proof.
  intros f g Hfg.
  induction n.
  - easy.
  - apply morphism2_compat; assumption.
Qed.

Add Parametric Morphism {C : Type} 
  `{cC : Category C, cMonC : !MonoidalCategory C} {A B : C} {n : nat} : 
  (@n_tensor_l C cC cMonC A B n) 
  with signature 
  (@Category.equiv C cC A B) 
    ==> (@Category.equiv C cC (n_times_l n A) (n_times_l n B))
  as n_tensor_l_equiv_mor.
Proof.
  intros f g Hfg.
  induction n.
  - easy.
  - apply morphism2_compat; assumption.
Qed.




Local Close Scope Cat.
