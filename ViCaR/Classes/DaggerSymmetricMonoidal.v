Require Import Category.
Require Import Dagger.
Require Import Monoidal.
Require Import BraidedMonoidal.
Require Import DaggerMonoidal.
Require Import SymmetricMonoidal.
Require Import DaggerBraidedMonoidal.

#[local] Set Universe Polymorphism.

Local Open Scope Cat.

Class DaggerSymmetricMonoidalCategory {C : Type} {cC : Category C} 
    {dagC : DaggerCategory cC} {mC : MonoidalCategory cC}
    {bC : BraidedMonoidalCategory mC}
    {mdagC : DaggerMonoidalCategory dagC mC}
    (bdagC : DaggerBraidedMonoidalCategory mdagC bC)
    (sC : SymmetricMonoidalCategory bC) : Type := {}.


Local Close Scope Cat.