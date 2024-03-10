Require Import Category.
Require Import Monoidal.
Require Import BraidedMonoidal.

Local Open Scope Cat.

Class SymmetricMonoidalCategory (C : Type) `{BraidedMonoidalCategory C} : Type := {
    symmetry {A B : C} : B_ A,B ≃ (B_ B,A)^-1;
}.
Definition BraidedMonoidalCategory_of_SymmetricMonoidalCategory 
  {C : Type} `{SymmetricMonoidalCategory C} : BraidedMonoidalCategory C
  := _.
Coercion BraidedMonoidalCategory_of_SymmetricMonoidalCategory 
 : SymmetricMonoidalCategory >-> BraidedMonoidalCategory.

Local Close Scope Cat.
