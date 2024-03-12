Require Import Category.
Require Import Dagger.
Require Import Monoidal.
Require Import BraidedMonoidal.
Require Import DaggerMonoidal.

#[local] Set Universe Polymorphism.

Local Open Scope Cat.

Class DaggerBraidedMonoidalCategory (C : Type) 
    `{!Category C} `{!DaggerCategory C} `{!MonoidalCategory C} 
    `{!DaggerMonoidalCategory C} `{!BraidedMonoidalCategory C} : Type := {}.


Local Close Scope Cat.