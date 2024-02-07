Require Import Category.

Local Open Scope Cat.

Reserved Notation "f †" (at level 0).

Class DaggerCategory (C : Type) `{Category C} : Type := {
    adjoint {A B : C} (f : A ~> B) : B ~> A
        where "f †" := (adjoint f);

    involutive {A B : C} {f : A ~> B} : f † † ≃ f;

    preserves_id {A : C} : (c_identity A) † ≃ c_identity A;

    contravariant {A B M : C} {f : A ~> B} {g : B ~> M} :
        (f ∘ g) † ≃ g † ∘ f †;
}.

Notation "f †" := (adjoint f) : Cat_scope. (* \dag *)


Local Close Scope Cat.
