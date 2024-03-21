Require Import Category.
Require Import Monoidal.
Require Import Setoid.

#[local] Set Universe Polymorphism.

Local Open Scope Cat_scope.

(* Reserved Notation "'B_' x , y" (at level 39). *)
Class BraidedMonoidalCategory {C : Type} {cC : Category C} 
  (mC : MonoidalCategory cC) : Type := {
  braiding (A B : C) : A × B <~> B × A;
}.
Arguments BraidedMonoidalCategory {_} {_}%Cat (_)%Cat.
Arguments braiding {_} {_}%Cat {_}%Cat (_)%Cat.
Notation "'B_' x , y" := (braiding _%Cat x%Cat y%Cat) 
  (at level 20) : Cat_scope.

Class BraidedMonoidalCategoryCoherence {C} {cC : Category C} 
  {mC : MonoidalCategory cC} {cCh : CategoryCoherence cC}
  {mCh : MonoidalCategoryCoherence mC} (bC : BraidedMonoidalCategory mC)
  : Type := {
  to_base_struct_cat_braid := bC;
  braiding_natural {A1 B1 A2 B2} (f1 : A1 ~> B1) (f2 : A2 ~> B2) :
    f1 ⊗ f2 ∘ B_ B1, B2 ≃ B_ A1, A2 ∘ f2 ⊗ f1;

  hexagon_1 (A B M : C) : 
    (B_ A, B ⊗ id_ M) ∘ α_ _, _, _ ∘ (id_ B ⊗ B_ A, M)
    ≃ α_ _, _, _ ∘ (B_ A, (B × M)) ∘ α_ _, _, _;

  hexagon_2 (A B M : C) : 
    ((B_ B, A) ^-1 ⊗ id_ M) ∘ α_ _, _, _ 
      ∘ (id_ B ⊗ (B_ M, A)^-1)
    ≃ α_ _, _, _ ∘ (B_ (B × M), A)^-1 ∘ α_ _, _, _;
  
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
  f1 ⊗ f2 ∘ (B_ B2, B1)^-1 ≃ (B_ A2, A1)^-1 ∘ f2 ⊗ f1.
Proof. symmetry. 
  apply (component_biiso_natural_reverse (N:=BraidingNaturalBiIsomorphism)).
Qed.

Lemma braiding_inv_r (A B : C) : 
  B_ A, B ∘ (B_ A, B)^-1 ≃ id_ (A × B).
Proof. apply iso_inv_r. Qed.

Lemma braiding_inv_l (A B : C) : 
  (B_ A, B)^-1 ∘ B_ A, B ≃ id_ (B × A).
Proof. apply iso_inv_l. Qed.

Lemma hexagon_resultant_1 (A B M : C) :
  id_ B ⊗ B_ M, A ∘ B_ B, (A×M) ∘ associator A M B ∘ id_ A ⊗ (B_ B, M)^-1
  ≃ associator B M A ^-1 ∘ B_ (B × M), A.
Proof.
  (* rewrite <- compose_iso_l. *)
  pose proof (hexagon_2 A B M) as hex2.
  rewrite <- (compose_tensor_iso_r' _ (IdentityIsomorphism _)).
  simpl.
  rewrite 2!compose_iso_r.
  rewrite !cCh.(assoc).
  rewrite <- compose_iso_l.
  rewrite (compose_tensor_iso_r _ (IdentityIsomorphism _)).
  rewrite cCh.(assoc), compose_iso_l'.
  symmetry in hex2.
  rewrite cCh.(assoc) in hex2.
  rewrite compose_iso_l in hex2.
  rewrite hex2.
  simpl.
  rewrite <- !cCh.(assoc).
  apply compose_cancel_r.
  pose proof (hexagon_1 B A M) as hex1.
  rewrite assoc, <- compose_iso_l'.
  rewrite <- (compose_tensor_iso_l' _ (IdentityIsomorphism _)).
  simpl.
  rewrite <- 3!cCh.(assoc).
  rewrite <- 2!compose_iso_r.
  rewrite <- hex1.
  easy.
Qed.

End BraidedCoherenceRewrites.


Local Close Scope Cat.