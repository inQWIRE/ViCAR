Require Import Category.
Require Import Monoidal.
Require Import Setoid.

#[local] Set Universe Polymorphism.

Local Open Scope Cat_scope.


Class BraidedMonoidalCategory {C : Type} {cC : Category C} 
  (mC : MonoidalCategory cC) : Type := {
  braiding (A B : C) : A × B <~> B × A;
}.
Arguments BraidedMonoidalCategory {_} {_}%Cat (_)%Cat.
Arguments braiding {_} {_}%Cat {_}%Cat (_)%Cat.
Notation "'β_' x , y" := (braiding _%Cat x%Cat y%Cat) 
  (at level 20) : Cat_scope.

Class BraidedMonoidalCategoryCoherence {C} {cC : Category C} 
  {mC : MonoidalCategory cC} {cCh : CategoryCoherence cC}
  {mCh : MonoidalCategoryCoherence mC} (bC : BraidedMonoidalCategory mC)
  : Type := {
  braiding_natural {A1 B1 A2 B2} (f1 : A1 ~> B1) (f2 : A2 ~> B2) :
    f1 ⊗ f2 ∘ β_ B1, B2 ≃ β_ A1, A2 ∘ f2 ⊗ f1;

  hexagon_1 (A B M : C) : 
    (β_ A, B ⊗ id_ M) ∘ α_ _, _, _ ∘ (id_ B ⊗ β_ A, M)
    ≃ α_ _, _, _ ∘ (β_ A, (B × M)) ∘ α_ _, _, _;

  hexagon_2 (A B M : C) : 
    ((β_ B, A) ^-1 ⊗ id_ M) ∘ α_ _, _, _ 
      ∘ (id_ B ⊗ (β_ M, A)^-1)
    ≃ α_ _, _, _ ∘ (β_ (B × M), A)^-1 ∘ α_ _, _, _;
  
  MonoidalCategory_of_BraidedMonoidalCategory := mC;
}.

Section BraidedCoherenceRewrites.


Context {C : Type} {cC : Category C} {mC : MonoidalCategory cC}
  {bC : BraidedMonoidalCategory mC} {cCh : CategoryCoherence cC} 
  {mCh : MonoidalCategoryCoherence mC}
  {bCh : BraidedMonoidalCategoryCoherence bC}.

#[export, program] Instance BraidingNaturalBiIsomorphism :
  NaturalBiIsomorphism (tensor _) (CommuteBifunctor (tensor _)) := {
  component_biiso := braiding _;
}.
Next Obligation. rewrite bCh.(braiding_natural); easy. Qed.

Lemma inv_braiding_natural {A1 B1 A2 B2 : C} (f1 : A1 ~> B1) (f2 : A2 ~> B2) : 
  f1 ⊗ f2 ∘ (β_ B2, B1)^-1 ≃ (β_ A2, A1)^-1 ∘ f2 ⊗ f1.
Proof. symmetry. 
  apply (component_biiso_natural_reverse (N:=BraidingNaturalBiIsomorphism)).
Qed.

Lemma braiding_inv_r (A B : C) : 
  β_ A, B ∘ (β_ A, B)^-1 ≃ id_ (A × B).
Proof. apply iso_inv_r. Qed.

Lemma braiding_inv_l (A B : C) : 
  (β_ A, B)^-1 ∘ β_ A, B ≃ id_ (B × A).
Proof. apply iso_inv_l. Qed.

Lemma hexagon_resultant_1 (A B M : C) :
  id_ B ⊗ β_ M, A ∘ β_ B, (A×M) ∘ associator A M B ∘ id_ A ⊗ (β_ B, M)^-1
  ≃ associator B M A ^-1 ∘ β_ (B × M), A.
Proof.
  pose proof (hexagon_2 A B M) as hex2.
  replace (id_ A) with (IdentityIsomorphism A ^-1) by easy.
  rewrite <- (compose_tensor_iso_r' (associator B M A ^-1 ∘ B_ B × M, A) (IdentityIsomorphism A) (B_ B, M)).
  simpl.
  rewrite 2!compose_iso_r.
  rewrite !(assoc).
  rewrite <- compose_iso_l.
  Check compose_tensor_iso_r.
  replace (id_ B) with (forward (IdentityIsomorphism B)) by easy.
  rewrite (compose_tensor_iso_r _ (IdentityIsomorphism _)).
  rewrite (assoc), compose_iso_l'.
  symmetry in hex2.
  rewrite (assoc) in hex2.
  rewrite compose_iso_l in hex2.
  rewrite hex2.
  simpl.
  rewrite <- !(assoc).
  apply compose_cancel_r.
  pose proof (hexagon_1 B A M) as hex1.
  rewrite <- compose_iso_l'.
  replace (id_ M) with (IdentityIsomorphism M ^-1) by easy.
  rewrite <- (compose_tensor_iso_l' _ (IdentityIsomorphism _)).
  simpl.
  rewrite <- 3!(assoc).
  rewrite <- 2!compose_iso_r.
  rewrite <- hex1.
  easy.
Qed.

Local Close Scope Cat.