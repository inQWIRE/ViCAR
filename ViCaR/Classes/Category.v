Require Import Setoid.

Declare Scope Cat_scope.
Delimit Scope Cat_scope with Cat.
Local Open Scope Cat.

Reserved Notation "A ~> B" (at level 50).
Reserved Notation "f ≃ g" (at level 60).
Reserved Notation "A ≅ B" (at level 60).

Class Category (C : Type) : Type := {
    morphism : C -> C -> Type
        where "A ~> B" := (morphism A B);

    (* Morphism equivalence *)
    equiv {A B : C} : relation (A ~> B)
        where "f ≃ g" := (equiv f g) : Cat_scope;
    equiv_rel {A B : C} : equivalence (A ~> B) equiv;

    (* Object equivalence *)
    obj_equiv : relation C
        where "A ≅ B" := (obj_equiv A B) : Cat_scope;
    obj_equiv_rel : equivalence C obj_equiv;

    compose {A B M : C} : 
        (A ~> B) -> (B ~> M) -> (A ~> M);
    compose_compat {A B M : C} : 
        forall (f g : A ~> B), f ≃ g ->
        forall (h j : B ~> M), h ≃ j ->
        compose f h ≃ compose g j;
    assoc {A B M N : C}
        {f : A ~> B} {g : B ~> M} {h : M ~> N} : 
        compose (compose f g) h ≃ compose f (compose g h);

    c_identity (A : C) : A ~> A;
    left_unit {A B : C} {f : A ~> B} : compose (c_identity A) f ≃ f;
    right_unit {A B : C} {f : A ~> B} : compose f (c_identity B) ≃ f;
}.

Notation "A ~> B" := (morphism A B) : Cat_scope.
Notation "f ≃ g" := (equiv f g) : Cat_scope. (* \simeq *)
Notation "A ≅ B" := (obj_equiv A B) : Cat_scope. (* \cong *)
Infix "∘" := compose (at level 40, left associativity) : Cat_scope. (* \circ *)

Add Parametric Relation {C : Type} {Cat : Category C} 
    (A B : C) : (A ~> B) equiv
  reflexivity proved by (equiv_refl (A ~> B) equiv equiv_rel)
  symmetry proved by (equiv_sym (A ~> B) equiv equiv_rel)
  transitivity proved by (equiv_trans (A ~> B) equiv equiv_rel)
  as prop_equiv_rel.

Add Parametric Morphism {C : Type} {Cat : Category C} (n o m : C) : compose
  with signature (@equiv C Cat n m) ==> (@equiv C Cat m o) ==> equiv as compose_mor.
Proof. apply compose_compat; assumption. Qed.

Local Close Scope Cat.
