Require Import Category.
Require Import Monoidal.

Local Open Scope Cat.

Class BraidedMonoidalCategory (C : Type) `{MonoidalCategory C} : Type := {
    braiding {A B : C} : A × B ~> B × A;
    inv_braiding {A B : C} : B × A ~> A × B;
    braiding_inv_compose {A B : C} : braiding ∘ inv_braiding ≃ c_identity (A × B);
    inv_braiding_compose {A B : C} : inv_braiding ∘ braiding ≃ c_identity (B × A);

    hexagon_1 {A B M : C} : 
        (braiding ⊗ c_identity M) ∘ associator ∘ (c_identity B ⊗ braiding)
        ≃ associator ∘ (@braiding A (B × M)) ∘ associator;

    hexagon_2 {A B M : C} : (inv_braiding ⊗ c_identity M) ∘ associator ∘ (c_identity B ⊗ inv_braiding)
        ≃ associator ∘ (@inv_braiding (B × M) A) ∘ associator;
}.

Local Close Scope Cat.