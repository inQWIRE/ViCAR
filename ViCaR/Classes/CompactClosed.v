Require Import Category.
Require Import Monoidal.
Require Import BraidedMonoidal.
Require Import SymmetricMonoidal.

Local Open Scope Cat.

Reserved Notation "A ★" (at level 0).

(* A compact closed category is a right autonomous symmetric monoidal category *)
Class CompactClosedCategory (C : Type) `{SymmetricMonoidalCategory C} : Type := {
    dual (A : C) : C
        where "A ★" := (dual A);
    unit {A : C} : I ~> A ★ × A;
    counit {A : C} : A × A ★ ~> I;

    triangle_1 {A : C} : 
        inv_right_unitor ∘ (c_identity A ⊗ unit) ∘ inv_associator 
        ∘ (counit ⊗ c_identity A) ∘ left_unitor ≃ c_identity A;

    triangle_2 {A : C} : 
        inv_left_unitor ∘ (unit ⊗ c_identity A ★) ∘ associator 
        ∘ (c_identity A ★ ⊗ counit) ∘ right_unitor ≃ c_identity A ★;
}.

Notation "A ★" := (dual A) : Cat_scope.

Local Close Scope Cat.
