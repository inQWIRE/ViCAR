Require Import Category.
Require Import Monoidal.
Require Import BraidedMonoidal.

Local Open Scope Cat.

Class SymmetricMonoidalCategory (C : Type) `{BraidedMonoidalCategory C} : Type := {
    symmetry {A B : C} : (@braiding C H H0 H1 A B) ≃ inv_braiding;
}.

Local Close Scope Cat.
