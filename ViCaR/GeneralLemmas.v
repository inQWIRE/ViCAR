Require Import Category.
Require Import Monoidal.
Require Import Setoid.

Local Open Scope Cat.

Lemma compose_simplify_general : forall {C : Type} {Cat : Category C}
  {A B M : C} (f1 f3 : A ~> B) (f2 f4 : B ~> M),
  f1 ≃ f3 -> f2 ≃ f4 -> (f1 ∘ f2) ≃ (f3 ∘ f4).
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma stack_simplify_general : forall {C : Type} 
  {Cat : Category C} {MonCat : MonoidalCategory C}
  {A B M N : C} (f1 f3 : A ~> B) (f2 f4 : M ~> N),
  f1 ≃ f3 -> f2 ≃ f4 -> (f1 ⊗ f2) ≃ (f3 ⊗ f4).
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma nwire_stack_compose_topleft_general : forall {C : Type}
  {Cat : Category C} {MonCat : MonoidalCategory C}
  {topIn botIn topOut botOut : C} 
  (f0 : botIn ~> botOut) (f1 : topIn ~> topOut),
  ((c_identity topIn) ⊗ f0) ∘ (f1 ⊗ (c_identity botOut)) ≃ (f1 ⊗ f0).
Proof.
  intros.
  rewrite <- compose2_map.
  rewrite left_unit; rewrite right_unit.
  easy.
Qed.

Lemma nwire_stackcompose_topright_general : forall {C : Type}
  {Cat: Category C} {MonCat : MonoidalCategory C}
  {topIn botIn topOut botOut : C} 
  (f0 : topIn ~> topOut) (f1 : botIn ~> botOut),
  (f0 ⊗ (c_identity botIn)) ∘ ((c_identity topOut) ⊗ f1) ≃ (f0 ⊗ f1).
Proof.
  intros.
  rewrite <- compose2_map.
  rewrite right_unit, left_unit.
  easy.
Qed.

Definition cast {C : Type} `{Category C} (A B : C) {A' B' : C} 
  (prfA : A = A') (prfB : B = B') (f : A' ~> B') : A ~> B.
Proof.
  destruct prfA.
  destruct prfB.
  exact f.
Defined.

Add Parametric Morphism {C : Type} `{cC : Category C} {A B : C} {A' B' : C}
  {prfA : A = A'} {prfB : B = B'} : (@cast C cC A B A' B' prfA prfB)
  with signature
  (@Category.equiv C cC A' B') ==> (@Category.equiv C cC A B) as cast_equiv_morphism.
Proof.
  intros. 
  subst.
  easy.
Qed.

Local Close Scope Cat.
