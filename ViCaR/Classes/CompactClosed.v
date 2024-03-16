Require Import Category.
Require Import Monoidal.
Require Import BraidedMonoidal.
Require Import SymmetricMonoidal.

#[local] Set Universe Polymorphism.

Local Open Scope Cat.
Local Open Scope Mon.
(* Reserved Notation "A ★" (at level 0). (* \bigstar *) *)

(* A compact closed category is a right autonomous symmetric monoidal category *)
Class CompactClosedCategory {C : Type} {cC : Category C} {mC : MonoidalCategory cC}
  {bC : BraidedMonoidalCategory mC} (sC : SymmetricMonoidalCategory bC) : Type := {
  dual (A : C) : C;
    (* where "A ★" := (dual A); *)
  unit (A : C) : I ~> dual A × A;
  counit (A : C) : A × dual A ~> I;

  triangle_1 (A : C) : 
    (right_unitor A)^-1 ∘ (id_ A ⊗ unit A) ∘ (associator A (dual A) A)^-1
    ∘ (counit A ⊗ id_ A) ∘ left_unitor A ≃ id_ A;

  triangle_2 {A : C} : 
    (left_unitor (dual A))^-1 ∘ (unit A ⊗ id_ (dual A)) 
    ∘ (associator (dual A) A (dual A)) 
    ∘ (id_ (dual A) ⊗ counit A) ∘ right_unitor (dual A) ≃ id_ (dual A);
}.

Notation "A ★" := (dual A%Obj) (at level 0) : Obj_scope.

Local Close Scope Cat.
