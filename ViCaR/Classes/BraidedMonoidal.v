Require Import Category.
Require Import Monoidal.
Require Import Setoid.

Local Open Scope Cat.

Notation CommuteBifunctor' F := ({|
  obj2_map := fun A B => F B A;
  morphism2_map := fun A1 A2 B1 B2 fAB1 fAB2 => F @@ fAB2, fAB1;
  id2_map := ltac:(intros; apply id2_map);
  compose2_map := ltac:(intros; apply compose2_map);
  morphism2_compat := ltac:(intros; apply morphism2_compat; easy);
|}).



Reserved Notation "'B_' x , y" (at level 39).
Class BraidedMonoidalCategory (C : Type) `{MonoidalCategory C} : Type := {
  braiding : NaturalBiIsomorphism (tensor) (CommuteBifunctor tensor)
    where "'B_' x , y " := (braiding x y);

  hexagon_1 {A B M : C} : 
    (B_ A,B ⊗ c_identity M) ∘ associator ∘ (c_identity B ⊗ B_ A,M)
    ≃ associator ∘ (B_ A,(B × M)) ∘ associator;

  hexagon_2 {A B M : C} : ((B_ B,A) ^-1 ⊗ c_identity M) ∘ associator ∘ (c_identity B ⊗ (B_ M,A)^-1)
    ≃ associator ∘ (B_ (B × M), A)^-1 ∘ associator;
(* 
  braiding {A B : C} : A × B <~> B × A;

  hexagon_1 {A B M : C} : 
    (braiding ⊗ c_identity M) ∘ associator ∘ (c_identity B ⊗ braiding)
    ≃ associator ∘ (@braiding A (B × M)) ∘ associator;

  hexagon_2 {A B M : C} : (braiding^-1 ⊗ c_identity M) ∘ associator ∘ (c_identity B ⊗ braiding^-1)
    ≃ associator ∘ (@braiding (B × M) A)^-1 ∘ associator; 
*)


(*
  braiding {A B : C} : A × B ~> B × A;
  inv_braiding {A B : C} : B × A ~> A × B;
  braiding_inv_compose {A B : C} : braiding ∘ inv_braiding ≃ c_identity (A × B);
  inv_braiding_compose {A B : C} : inv_braiding ∘ braiding ≃ c_identity (B × A);

  hexagon_1 {A B M : C} : 
    (braiding ⊗ c_identity M) ∘ associator ∘ (c_identity B ⊗ braiding)
    ≃ associator ∘ (@braiding A (B × M)) ∘ associator;

  hexagon_2 {A B M : C} : (inv_braiding ⊗ c_identity M) ∘ associator ∘ (c_identity B ⊗ inv_braiding)
    ≃ associator ∘ (@inv_braiding (B × M) A) ∘ associator;
*)
}.
Notation "'B_' x , y" := (braiding x y) (at level 39, no associativity).

Local Close Scope Cat.