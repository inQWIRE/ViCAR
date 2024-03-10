Require Import Setoid.

Require Import Category.
Require Import Monoidal.
Require Import BraidedMonoidal.
Require Import SymmetricMonoidal.

Local Open Scope Cat_scope.


Class PreDistributiveBimonoidalCategory {C : Type} `{cC : Category C}
  `(AddC : SymmetricMonoidalCategory C (cC:=cC))
  `(MulC : MonoidalCategory C (cC:=cC)) := {
  (* left_distr_iso (A B M : C) :
    A × (B + M) <~> A×B + A×M;
  left_distr_natural {A B M A' B' M' : C} : forall 
    (f : A ~> A') (g : B ~> B') (h : M ~> M'),
    left_distr_iso A B M ∘ (f ⊠ g ⊞ f ⊠ h)
    ≃ (f ⊠ (g ⊞ h)) ∘ left_distr_iso A' B' M'; *)
  
  (* NOTE: By not defining these as actual natural transformations, we
     *should* only be 'losing' the declaration that the underlying
     transformations are functorial... but as compositions of functors,
     they are — plus, it's awkward to get the definitions working nicely
     in functor land. So for now, we do it directly. *)
  left_distr_iso (A B M : C) :
    MulC.(tensor) A (AddC.(tensor) B M) 
    <~> AddC.(tensor) (MulC.(tensor) A B) (MulC.(tensor) A M);
  left_distr_natural {A B M A' B' M' : C} : forall 
    (f : A ~> A') (g : B ~> B') (h : M ~> M'),
    left_distr_iso A B M ∘ 
      (AddC.(tensor) @@ (MulC.(tensor) @@ f, g), (MulC.(tensor) @@ f, h))
    ≃ MulC.(tensor) @@ f, (AddC.(tensor) @@ g, h)
      ∘ left_distr_iso A' B' M';

  right_distr_iso (A B M : C) :
    MulC.(tensor) (AddC.(tensor) A B) M 
    <~> AddC.(tensor) (MulC.(tensor) A M) (MulC.(tensor) B M);
  right_distr_natural {A B M A' B' M' : C} : forall 
    (f : A ~> A') (g : B ~> B') (h : M ~> M'),
  right_distr_iso A B M ∘ 
    (AddC.(tensor) @@ (MulC.(tensor) @@ f, h), (MulC.(tensor) @@ g, h))
  ≃ MulC.(tensor) @@ (AddC.(tensor) @@ f, g), h
    ∘ right_distr_iso A' B' M';
}.

Declare Scope Rig_scope.
Open Scope Rig_scope.

Definition add_of_prerig {C} {cC}
  {H1} {H2} {AddC} {MulC} 
  `{@PreDistributiveBimonoidalCategory C cC H1 H2 AddC MulC} := AddC.

Definition mul_of_prerig {C} {cC}
  {H1} {H2} {AddC} {MulC} 
  `{@PreDistributiveBimonoidalCategory C cC H1 H2 AddC MulC} := MulC.

Notation "'addC'" := add_of_prerig (at level 0) : Rig_scope.
Notation "'mulC'" := mul_of_prerig (at level 0) : Rig_scope.

Notation "A + B" := (addC.(tensor) A B) 
  (at level 50, left associativity) : Rig_scope.
Notation "A × B" := (mulC.(tensor) A B) 
  (at level 40, left associativity) : Rig_scope.

Notation "f ⊞ g" := (addC.(tensor) @@ f, g) 
  (at level 50, left associativity) : Rig_scope.
Notation "f ⊠ g" := (mulC.(tensor) @@ f, g)
  (at level 40, left associativity) : Rig_scope.


Notation "'c1'" :=
  (mulC.(I))
  (at level 20, no associativity) : Rig_scope.
Notation "'c0'" :=
  (addC.(I))
  (at level 20, no associativity) : Rig_scope.

Notation "'α_' A , B , M" :=
  (mulC.(associator) (A:=A) (B:=B) (M:=M)).(reverse)
  (at level 35, no associativity) : Rig_scope.
Notation "'α'_' A , B , M" :=
  (addC.(associator) (A:=A) (B:=B) (M:=M)).(reverse)
  (at level 35, no associativity) : Rig_scope.
Notation "'α^-1_' A , B , M" :=
  (mulC.(associator) (A:=A) (B:=B) (M:=M)).(forward)
  (at level 35, no associativity) : Rig_scope.
Notation "'α'^-1_' A , B , M" :=
  (addC.(associator) (A:=A) (B:=B) (M:=M)).(forward)
  (at level 35, no associativity) : Rig_scope.


Notation "'δ_' A , B , M" :=
  (left_distr_iso A B M) 
  (at level 35, no associativity) : Rig_scope.
Notation "'δ#_' A , B , M" :=
  (right_distr_iso A B M) 
  (at level 35, no associativity) : Rig_scope.

Notation "'γ'_' A , B" :=
  (addC.(braiding) A B)
  (at level 35, no associativity) : Rig_scope.
(* NOTE! This one won't work unless in a Braided Rig: *)
Notation "'γ_' A , B" :=
  (let mulC' := _ : @BraidedMonoidalCategory _ _ mulC 
  in mulC'.(braiding) A B)
  (at level 35, no associativity) : Rig_scope.

Notation "'λ_' A" :=
  (mulC.(left_unitor) (A:=A)) 
  (at level 30, no associativity) : Rig_scope.
Notation "'λ'_' A" :=
  (addC.(left_unitor) (A:=A)) 
  (at level 35, no associativity) : Rig_scope.

Notation "'ρ_' A" :=
  (mulC.(right_unitor) (A:=A)) 
  (at level 30, no associativity) : Rig_scope.
Notation "'ρ'_' A" :=
  (addC.(right_unitor) (A:=A)) 
  (at level 35, no associativity) : Rig_scope.


Class DistributiveBimonoidalCategory {C : Type} `{cC : Category C}
  `(AddC : SymmetricMonoidalCategory C (cC:=cC))
  `(MulC : MonoidalCategory C (cC:=cC)) := {
  predistr_cat :> PreDistributiveBimonoidalCategory AddC MulC;

  left_absorbtion_iso (A : C) : 
    c0 × A <~> c0;
  left_absorbtion_natural {A A' : C} : forall (f : A ~> A'),
    left_absorbtion_iso A ∘ (id_ c0)
    ≃ (id_ c0) ⊠ f ∘ left_absorbtion_iso A';
  
  right_absorbtion_iso (A : C) : 
    A × c0 <~> c0;
  right_absorbtion_natural {A A' : C} : forall (f : A ~> A'),
    right_absorbtion_iso A ∘ (id_ c0)
    ≃ f ⊠ (id_ c0) ∘ right_absorbtion_iso A';
}.




(* Definition left_distr_mor {C} `{H: PreRigCategory C} 
  (A B M : C) : (A + B) × M ~> A×M + B×M
  := (right_distr.(component_niso) A B M). *)



Notation "'λ*_' A" :=
  (left_absorbtion_iso A)
  (at level 35, no associativity) : Rig_scope.
Notation "'ρ*_' A" :=
  (right_absorbtion_iso A)
  (at level 35, no associativity) : Rig_scope.



Class SemiCoherent_DistributiveBimonoidalCategory {DD : Type} `(rC : DistributiveBimonoidalCategory DD) := {
  condition_I (A B C : DD) : 
    δ_ A,B,C ∘ γ'_ (A×B), (A×C) ≃ 
    id_ A ⊠ γ'_ B, C ∘ δ_ A, C, B;
  condition_III (A B C : DD) :
    δ#_ A,B,C ∘ γ'_ (A×C),(B×C)
    ≃ (γ'_ A,B ⊠ id_ C) ∘ δ#_ B,A,C;
  condition_IV (A B C D : DD) :
    (* equiv (A:=(A+(B+C))×D) (B:=(A×D + B×D + C×D)) *)
    δ#_ A,(B+C),D ∘ (id_ (A×D) ⊞ δ#_ B,C,D) ∘ α'_ A×D, B×D, (C×D)
    ≃ (α'_ A,B,C ⊠ (id_ D)) ∘ δ#_ A+B,C,D ∘ (δ#_ A,B,D ⊞ id_ (C×D));
  condition_V (A B C D : DD) :
    δ_ A,B,(C+D) ∘ (id_(A×B) ⊞ δ_ A,C,D) ∘ α'_ A×B,A×C,(A×D)
    ≃ id_ A ⊠ α'_ B,C,D ∘ δ_ A,B+C,D ∘ (δ_ A,B,C ⊞ id_(A×D));
  condition_VI (A B C D : DD) :
    id_ A ⊠ δ_ B,C,D ∘ δ_ A,B×C,(B×D) ∘ (α_ A,B,C ⊞ α_ A,B,D)
    ≃ α_ A,B,(C+D) ∘ δ_ (A×B),C,D;
  condition_VII (A B C D : DD) :
    δ#_ A,B,(C×D) ∘ (α_ A,C,D ⊞ α_ B,C,D) 
    ≃ α_ A+B,C,D ∘ (δ#_A,B,C ⊠ id_ D) ∘ (δ#_ A×C,B×C,D);
  condition_VIII (A B C D : DD) :
    (id_ A ⊠ δ#_ B,C,D) ∘ δ_ A,B×D,(C×D) ∘ (α_ A,B,D ⊞ α_ A,C,D)
    ≃ α_ A,B+C,D ∘ (δ_ A,B,C ⊠ id_ D) ∘ δ#_ A×B,A×C,D;
  condition_IX  (A B C D : DD) :
    δ#_ A,B,(C+D) ∘ (δ_ A,C,D ⊞ δ_ B,C,D) ∘ (α'_ (A×C+A×D),B×C,(B×D))
      ∘ ((α'^-1_ A×C,A×D,(B×C)) ⊞ id_ (B×D))
      ∘ ((id_ (A×C) ⊞ γ'_ A×D, (B×C)) ⊞ id_ (B×D))
      ∘ (α'_ A×C,B×C,(A×D) ⊞ id_ (B×D))
    ≃ δ_ A+B,C,D ∘ (δ#_ A,B,C ⊞ δ#_ A,B,D) ∘ α'_ (A×C+B×C),A×D,(B×D);
  condition_X : 
    λ*_ c0 ≃ ρ*_ c0; 
  condition_XI (A B : DD) :
    δ_ c0,A,B ∘ (λ*_ A ⊞ λ*_ B) ∘ λ'_ c0
    ≃ λ*_ (A + B);
  condition_XII (A B : DD) :
    δ#_ A,B,c0 ∘ (ρ*_ A ⊞ ρ*_ B) ∘ (λ'_ c0)
    ≃ ρ*_ (A+B);
  condition_XIII :
    ρ_ c0 ≃ λ*_ c1;
  condition_XIV :
    λ_ c0 ≃ ρ*_ c1;
  condition_XVI (A B : DD) :
    α_ c0,A,B ∘ (λ*_ A ⊠ id_ B) ∘ λ*_B
    ≃ λ*_ (A×B);
  condition_XVII (A B : DD) : 
    α_ A,c0,B ∘ (ρ*_ A ⊠ id_ B) ∘ λ*_ B
    ≃ id_ A ⊠ λ*_ B ∘ ρ*_ A;
  condition_XVIII (A B : DD) : 
    α_ A,B,c0 ∘ ρ*_ (A×B)
    ≃ (id_ A ⊠ ρ*_ B) ∘ ρ*_ A;
  condition_XIX (A B : DD) :
    δ_ A,c0,B ∘ (ρ*_ A ⊞ id_ (A×B)) ∘ λ'_ (A×B)
    ≃ id_ A ⊠ λ'_ B;
  condition_XX (A B : DD) :
    δ#_ c0,B,A ∘ (λ*_ A ⊞ id_ (B×A)) ∘ λ'_ (B×A)
    ≃ λ'_ B ⊠ id_ A;
  condition_XXI (A B : DD) :
    δ_ A,B,c0 ∘ (id_ (A×B) ⊞ ρ*_ A) ∘ (ρ'_ (A×B))
    ≃ id_ A ⊠ ρ'_ B;
  condition_XXII (A B : DD) : 
    δ#_ A,c0,B ∘ (id_ (A×B) ⊞ λ*_ B) ∘ (ρ'_ (A×B))
    ≃ ρ'_ A ⊠ id_ B;
  condition_XXIII (A B : DD) : 
    δ_ c1,A,B ∘ (λ_ A ⊞ λ_ B)
    ≃ λ_ (A+B);
  condition_XXIV (A B : DD) :
    δ#_ A,B,c1 ∘ (ρ_ A ⊞ ρ_ B)
    ≃ ρ_ (A+B);
}. 




Class SemiCoherent_BraidedDistributiveBimonoidalCategory {DD : Type} {cD} 
  {H1 H2}
  {AddC}
  {MulC} `(rC : @DistributiveBimonoidalCategory DD cD H1 H2 AddC MulC)
  `(@BraidedMonoidalCategory DD cD MulC) := {
  condition_II (A B C : DD) : 
    (* TODO: I had to swap order here?? *)
    (δ#_ A, B, C) ∘ (γ_ A,C ⊞ γ_ B,C)
    ≃ γ_ A+B, C ∘ δ_ C,A,B;
  condition_XV (A : DD) :
    ρ*_ A ≃ γ_ A,c0 ∘ λ*_A;
}.

Close Scope Rig_scope.
