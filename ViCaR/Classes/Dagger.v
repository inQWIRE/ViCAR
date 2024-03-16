Require Import Setoid.
Require Import Category.

#[local] Set Universe Polymorphism.

Local Open Scope Cat.

(* Reserved Notation "f †" (at level 0). *)

Class DaggerCategory {C : Type} (cC : Category C) : Type := {
  adjoint {A B : C} (f : A ~> B) : B ~> A;
    (* where "f †" := (adjoint f); *)

  adjoint_involutive {A B : C} (f : A ~> B) : 
    adjoint (adjoint f) ≃ f;

  adjoint_id (A : C) : adjoint (id_ A) ≃ id_ A;

  adjoint_contravariant {A B M : C} (f : A ~> B) (g : B ~> M) :
    adjoint (f ∘ g) ≃ adjoint g ∘ adjoint f;

  adjoint_compat {A B : C} (f g : A ~> B) :
    f ≃ g -> adjoint f ≃ adjoint g;
}.

Notation "f †" := (adjoint f) (at level 0) : Mor_scope. (* \dag *)

#[export] Instance AdjointContraFunctor {C} {cC : Category C}
  {dagC : DaggerCategory cC} : ContraFunctor cC cC := {|
  obj_contramap := fun A => A;
  morphism_contramap := @adjoint C cC dagC;
  id_contramap := @adjoint_id C cC dagC;
  compose_contramap := @adjoint_contravariant C cC dagC;
  morphism_contracompat := @adjoint_compat C cC dagC;
|}.

Add Parametric Morphism {C} {cC : Category C}
  {dagC : DaggerCategory cC} {A B : C} : 
  (@adjoint C cC dagC A B)
  with signature 
  (@c_equiv C cC A B) ==> (@c_equiv C cC B A)
  as adjoint_equiv_morph.
Proof. intros. apply adjoint_compat. easy. Qed.


Notation "'unitary' f" := (is_inverse f%Mor f%Mor †) 
  (at level 10, f at next level) : Cat_scope.



Add Parametric Morphism {C : Type} {cC : Category C} {dagC : DaggerCategory cC}
(A B : C) : (fun f => is_inverse f f†)
  with signature (@c_equiv C cC A B) ==> iff as unitary_mor.
Proof. 
  intros f g Hequiv.
  rewrite Hequiv.
  easy.
Qed. 

Lemma unitary_compose {C} {cC : Category C} {dagC : DaggerCategory cC}
   {A B M : C} {f : A ~> B} {g : B ~> M} (Hf : unitary f) (Hg : unitary g) :
  unitary (f ∘ g).
Proof.
  split.
  - rewrite adjoint_contravariant, assoc, <- (assoc g), (proj1 Hg),
    left_unit; easy.
  - rewrite adjoint_contravariant, assoc, <- (assoc f†), (proj2 Hf),
    left_unit; easy.
Qed.

Lemma unitary_adjoint {C} {cC : Category C} {dagC : DaggerCategory cC} 
  {A B : C} {f : A ~> B} (Hf : unitary f) : unitary (f†).
Proof.
  rewrite adjoint_involutive.
  split; easy.
Qed.

Lemma unitary_inverse {C} {cC : Category C} {dagC : DaggerCategory cC} 
  {A B : C} {f : A ~> B} {g : B ~> A} (Hf : unitary f) (Hinv : is_inverse f g) : 
  unitary g.
Proof.
  rewrite (inverse_unique Hinv Hf).
  apply unitary_adjoint; easy.
Qed.

Class UnitaryIsomorphism {C : Type} {cC : Category C} {dagC : DaggerCategory cC}
  (A B : C) := {
  unitary_isomorphism : A <~> B;
  is_unitary_isomorphism : unitary unitary_isomorphism.(forward)
}.
Coercion unitary_isomorphism : UnitaryIsomorphism >-> Isomorphism.

Lemma is_unitary_isomorphism_rev {C} {cC : Category C} {dagC : DaggerCategory cC}
  {A B : C} (f : UnitaryIsomorphism A B) : unitary f.(reverse).
Proof.
  apply (unitary_inverse is_unitary_isomorphism isomorphism_inverse).
Qed.


Local Close Scope Cat.
