Require Import Category.
Require Import Dagger.
Require Import Monoidal.

#[local] Set Universe Polymorphism.

Local Open Scope Cat.
Local Open Scope Mon.

Class DaggerMonoidalCategory {C : Type} {cC : Category C} 
  (dagC : DaggerCategory cC) (mC : MonoidalCategory cC) : Type := {
  dagger_tensor_compat {A B M N : C} (f : A ~> M) (g : B ~> N) :
    f † ⊗ g † ≃ (f ⊗ g) †;
  
  associator_unitary {A B M : C} : 
    unitary (associator A B M);
  left_unitor_unitary {A : C} : 
    unitary (left_unitor A);
  
  right_unitor_unitary {A : C} : 
    unitary (right_unitor A);
      
  
  (* associator_unitary_r {A B M : C} : 
    associator ∘ associator † ≃ c_identity (A × B × M);
  associator_unitary_l {A B M : C} : 
    associator † ∘ associator ≃ c_identity (A × (B × M));

  left_unitor_unitary_r {A : C} : 
    left_unitor ∘ left_unitor † ≃ c_identity (I × A);
  left_unitor_unitary_l {A : C} : 
    left_unitor † ∘ left_unitor ≃ c_identity A;

  right_unitor_unitary_r {A : C} : 
    right_unitor ∘ right_unitor † ≃ c_identity (A × I);
  right_unitor_unitary_l {A : C} :
    right_unitor † ∘ right_unitor ≃ c_identity A; *)
}.

Local Close Scope Cat.
