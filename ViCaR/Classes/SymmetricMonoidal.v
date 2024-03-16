Require Import Category.
Require Import Monoidal.
Require Import BraidedMonoidal.

#[local] Set Universe Polymorphism.

Local Open Scope Cat.
Local Open Scope Brd.

Class SymmetricMonoidalCategory {C : Type} {cC : Category C}
  {mC : MonoidalCategory cC} (bC : BraidedMonoidalCategory mC) : Type := {
  symmetry (A B : C) : B_ A,B ≃ (B_ B,A)^-1;

  BraidedMonoidalCategory_of_SymmetricMonoidalCategory := bC;
}.
Arguments SymmetricMonoidalCategory {_} {_ _}%Cat (_)%Cat.
Arguments symmetry {_} {_ _ _ _}%Cat (_ _)%Obj.

Coercion BraidedMonoidalCategory_of_SymmetricMonoidalCategory 
  : SymmetricMonoidalCategory >-> BraidedMonoidalCategory.

Local Close Scope Brd.
Local Close Scope Cat.
