Require Import Category.
Require Import Dagger.
Require Import Monoidal.
Require Import BraidedMonoidal.
Require Import DaggerMonoidal.

#[local] Set Universe Polymorphism.

Local Open Scope Cat.

Class DaggerBraidedMonoidalCategory {C : Type} {cC : Category C} 
  {dagC : DaggerCategory cC} {mC : MonoidalCategory cC}
  (mdagC : DaggerMonoidalCategory dagC mC) (bC : BraidedMonoidalCategory mC)
   : Type := {}.


Local Close Scope Cat.