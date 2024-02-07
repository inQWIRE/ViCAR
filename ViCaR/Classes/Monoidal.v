Require Import Category.
Require Import Setoid.

Local Open Scope Cat.

Class MonoidalCategory (C : Type) `{Category C} : Type := {
    tensor : C -> C -> C;
    I : C;

    tensor_morph {A B M N : C} : 
        (A ~> M) -> (B ~> N) -> (tensor A B) ~> (tensor M N);
    tensor_morph_compat {A B M N : C} : 
        forall (f g : A ~> B), f ≃ g ->
        forall (h j : M ~> N), h ≃ j ->
        tensor_morph f h ≃ tensor_morph g j;
    
    (* These are all isomorphisms *)
    associator {A B M : C} : tensor (tensor A B) M ~> tensor A (tensor B M);
    inv_associator {A B M : C} : tensor A (tensor B M) ~> tensor (tensor A B) M;
    associator_inv_compose {A B M : C} : associator ∘ inv_associator
        ≃ c_identity (tensor (tensor A B) M);
    inv_associator_compose {A B M : C} : inv_associator ∘ associator 
        ≃ c_identity (tensor A (tensor B M));

    left_unitor {A : C} : tensor I A ~> A;
    inv_left_unitor {A : C} : A ~> tensor I A;
    left_inv_compose {A : C} : 
        left_unitor ∘ inv_left_unitor ≃ c_identity (tensor I A);
    inv_left_compose {A : C} : 
        inv_left_unitor ∘ left_unitor ≃ c_identity A;

    right_unitor {A : C} : tensor A I ~> A;
    inv_right_unitor {A : C} : A ~> tensor A I;
    right_inv_compose {A : C} : 
        right_unitor ∘ inv_right_unitor ≃ c_identity (tensor A I);
    inv_right_compose {A : C} : 
        inv_right_unitor ∘ right_unitor ≃ c_identity A;

    bifunctor_id {A B : C} : 
        tensor_morph (c_identity A) (c_identity B) ≃ c_identity (tensor A B);
    bifunctor_comp {A B M N P Q : C} 
        {f : A ~> B} {g : B ~> M}
        {h : N ~> P} {k : P ~> Q} : 
        tensor_morph (f ∘ g) (h ∘ k) ≃ (tensor_morph f h) ∘ (tensor_morph g k);

    (* Coherence conditions for α, λ, ρ *)
    associator_cohere {A B M N P Q : C} 
        {f : A ~> B} {g : M ~> N} {h : P ~> Q} : 
        associator ∘ (tensor_morph f (tensor_morph g h)) ≃ (tensor_morph (tensor_morph f g) h) ∘ associator;
    left_unitor_cohere {A B : C} {f : A ~> B} : 
        left_unitor ∘ f ≃ (tensor_morph (c_identity I) f) ∘ left_unitor;
    right_unitor_cohere {A B : C} {f : A ~> B} : 
        right_unitor ∘ f ≃ (tensor_morph f (c_identity I)) ∘ right_unitor;

    (* Commutative diagrams *)
    triangle {A B : C} : 
        associator ∘ (tensor_morph (c_identity A) left_unitor)
        ≃ tensor_morph right_unitor (c_identity B);
    pentagon {A B M N : C} : 
        (tensor_morph associator (c_identity N)) ∘ associator ∘ (tensor_morph (c_identity A) associator)
        ≃ @associator (tensor A B) M N ∘ associator;
}.

Infix "×" := tensor (at level 40, left associativity) : Cat_scope. (* \times *)
Infix "⊗" := tensor_morph (at level 40, left associativity) : Cat_scope. (* \otimes *) 

Add Parametric Morphism {C : Type}
  {Cat : Category C} (MonCat : MonoidalCategory C)
  (n0 m0 n1 m1 : C) : tensor_morph
  with signature 
    (@Category.equiv C Cat n0 m0) ==> 
    (@Category.equiv C Cat n1 m1) ==> 
    Category.equiv as stack_mor.
Proof. apply tensor_morph_compat; assumption. Qed.


Local Close Scope Cat.
