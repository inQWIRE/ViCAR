Require Import Setoid.
Require Import Category.

#[local] Set Universe Polymorphism.

Local Open Scope Cat.

Reserved Notation "f †" (at level 0).

Class DaggerCategory (C : Type) `{cC : Category C} : Type := {
  adjoint {A B : C} (f : A ~> B) : B ~> A
    where "f †" := (adjoint f);

  adjoint_involutive {A B : C} {f : A ~> B} : f † † ≃ f;

  adjoint_id {A : C} : (id_ A) † ≃ id_ A;

  adjoint_contravariant {A B M : C} {f : A ~> B} {g : B ~> M} :
    (f ∘ g) † ≃ g † ∘ f †;

  adjoint_compat {A B : C} {f g : A ~> B} :
    f ≃ g -> f † ≃ g †;
}.

#[export] Instance AdjointContraFunctor {C} `{cC : Category C}
  `{dagC : @DaggerCategory C cC} : ContraFunctor cC cC := {|
  obj_contramap := fun A => A;
  morphism_contramap := @adjoint C cC dagC;
  id_contramap := @adjoint_id C cC dagC;
  compose_contramap := @adjoint_contravariant C cC dagC;
  morphism_contracompat := @adjoint_compat C cC dagC;
|}.

Add Parametric Morphism {C} `{cC : Category C}
  `{dagC : @DaggerCategory C cC} {A B : C} : 
  (@adjoint C cC dagC A B)
  with signature 
  (@equiv C cC A B) ==> (@equiv C cC B A)
  as adjoint_equiv_morph.
Proof. intros. apply adjoint_compat. easy. Qed.

Notation "f †" := (adjoint f) : Cat_scope. (* \dag *)

Definition unitary {C} `{DaggerCategory C} {A B : C} : A ~> B -> Prop :=
  fun f => is_inverse f f†.

Add Parametric Morphism {C : Type} `{Cat : Category C, dagC : !DaggerCategory C}
(A B : C) : unitary
  with signature (@equiv C Cat A B) ==> iff as unitary_mor.
Proof. 
  intros f g Hequiv.
  unfold unitary.
  rewrite Hequiv.
  easy.
Qed. 

Lemma unitary_compose {C} `{DaggerCategory C} {A B M : C} 
  {f : A ~> B} {g : B ~> M} (Hf : unitary f) (Hg : unitary g) :
  unitary (f ∘ g).
Proof.
  unfold unitary in *.
  split.
  - rewrite adjoint_contravariant, assoc, <- (assoc (f:=g)), (proj1 Hg),
    left_unit; easy.
  - rewrite adjoint_contravariant, assoc, <- (assoc (f:=f†)), (proj2 Hf),
    left_unit; easy.
Qed.

Lemma unitary_adjoint {C} `{DaggerCategory C} {A B : C} 
  {f : A ~> B} (Hf : unitary f) : unitary (f†).
Proof.
  unfold unitary in *.
  rewrite adjoint_involutive.
  split; easy.
Qed.

Lemma unitary_inverse {C} `{DaggerCategory C} {A B : C} 
  {f : A ~> B} {g : B ~> A} (Hf : unitary f) (Hinv : is_inverse f g) : 
  unitary g.
Proof.
  rewrite (inverse_unique Hinv Hf).
  apply unitary_adjoint; easy.
Qed.

Class UnitaryIsomorphism {C : Type} `{DaggerCategory C} (A B : C) := {
  unitary_isomorphism : A <~> B;
  is_unitary_isomorphism : unitary unitary_isomorphism.(forward)
}.
Coercion unitary_isomorphism : UnitaryIsomorphism >-> Isomorphism.



Local Close Scope Cat.
