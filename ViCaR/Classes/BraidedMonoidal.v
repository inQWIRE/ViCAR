Require Import Category.
Require Import Monoidal.
Require Import Setoid.

#[local] Set Universe Polymorphism.

Local Open Scope Cat_scope.
Local Open Scope Mor_scope.
Local Open Scope Obj_scope.
Local Open Scope Mon_scope.

Declare Scope Brd_scope.
Delimit Scope Brd_scope with Brd.
Local Open Scope Brd_scope.

(* Notation CommuteBifunctor' F := ({|
  obj_bimap := fun A B => F B A;
  morphism_bimap := fun A1 A2 B1 B2 fAB1 fAB2 => F @@ fAB2, fAB1;
  id_bimap := ltac:(intros; apply id_bimap);
  compose_bimap := ltac:(intros; apply compose_bimap);
  morphism_bicompat := ltac:(intros; apply morphism_bicompat; easy);
|}) (only parsing). *)



(* Reserved Notation "'B_' x , y" (at level 39). *)
Class BraidedMonoidalCategory {C : Type} {cC : Category C} 
  (mC : MonoidalCategory cC) : Type := {
  braiding : NaturalBiIsomorphism mC.(tensor) (CommuteBifunctor mC.(tensor));
    (* where "'B_' x , y " := (braiding x y); *)

  hexagon_1 (A B M : C) : 
    (braiding A B ⊗ id_ M) ∘ associator _ _ _ ∘ (id_ B ⊗ braiding A M)
    ≃ associator _ _ _ ∘ (braiding A (B × M)) ∘ associator _ _ _;

  hexagon_2 (A B M : C) : 
    ((braiding B A) ^-1 ⊗ id_ M) ∘ associator _ _ _ 
      ∘ (id_ B ⊗ (braiding M A)^-1)
    ≃ associator _ _ _ ∘ (braiding (B × M) A)^-1 ∘ associator _ _ _;
  
  MonoidalCategory_of_BraidedMonoidalCategory := mC;
}.
Arguments BraidedMonoidalCategory {_} {_}%Cat (_)%Cat.
Arguments braiding {_} {_}%Cat {_}%Cat (_)%Cat.
Notation "'B_' x , y" := (braiding _%Cat x%Obj y%Obj) 
  (at level 20) : Brd_scope.

Coercion MonoidalCategory_of_BraidedMonoidalCategory 
  : BraidedMonoidalCategory >-> MonoidalCategory.

Lemma braiding_natural {C} {cC : Category C} {mC : MonoidalCategory cC}
  {bC : BraidedMonoidalCategory mC} {A1 B1 A2 B2 : C} 
  (f1 : A1 ~> B1) (f2 : A2 ~> B2) : 
  f1 ⊗ f2 ∘ B_ B1, B2 ≃ B_ A1, A2 ∘ f2 ⊗ f1.
Proof. rewrite component_biiso_natural; easy. Qed.

Lemma inv_braiding_natural {C} {cC : Category C} {mC : MonoidalCategory cC}
  {bC : BraidedMonoidalCategory mC} {A1 B1 A2 B2 : C} 
  (f1 : A1 ~> B1) (f2 : A2 ~> B2) : 
  f1 ⊗ f2 ∘ (B_ B2, B1)^-1 ≃ (B_ A2, A1)^-1 ∘ f2 ⊗ f1.
Proof. symmetry. rewrite (component_biiso_natural_reverse); easy. Qed.

Lemma braiding_inv_r {C} {cC : Category C} {mC : MonoidalCategory cC}
  {bC : BraidedMonoidalCategory mC} (A B : C) : 
  B_ A, B ∘ (B_ A, B)^-1 ≃ id_ (A × B).
Proof. apply iso_inv_r. Qed.

Lemma braiding_inv_l {C} {cC : Category C} {mC : MonoidalCategory cC}
  {bC : BraidedMonoidalCategory mC} (A B : C) : 
  (B_ A, B)^-1 ∘ B_ A, B ≃ id_ (B × A).
Proof. apply iso_inv_l. Qed.

Lemma hexagon_resultant_1 {C} {cC : Category C} {mC : MonoidalCategory cC}
  {bC : BraidedMonoidalCategory mC} (A B M : C) :
  id_ B ⊗ B_ M, A ∘ B_ B, (A×M) ∘ associator A M B ∘ id_ A ⊗ (B_ B, M)^-1
  ≃ associator B M A ^-1 ∘ B_ (B × M), A.
Proof.
  (* rewrite <- compose_iso_l. *)
  pose proof (hexagon_2 A B M) as hex2.
  rewrite <- (compose_tensor_iso_r' _ (IdentityIsomorphism _)).
  simpl.
  rewrite 2!compose_iso_r.
  rewrite !assoc.
  rewrite <- compose_iso_l.
  rewrite (compose_tensor_iso_r _ (IdentityIsomorphism _)).
  rewrite assoc, compose_iso_l'.
  symmetry in hex2.
  rewrite assoc in hex2.
  rewrite compose_iso_l in hex2.
  rewrite hex2.
  simpl.
  rewrite <- 1!assoc.
  apply compose_cancel_r.
  pose proof (hexagon_1 B A M) as hex1.
  rewrite <- compose_iso_l'.
  rewrite <- (compose_tensor_iso_l' _ (IdentityIsomorphism _)).
  simpl.
  rewrite <- 3!assoc.
  rewrite <- 2!compose_iso_r.
  rewrite <- hex1.
  easy.
Qed.


Local Close Scope Cat.