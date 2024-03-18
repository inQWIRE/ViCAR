Require Import Setoid.

Require Import Category.
Require Import Monoidal.
Require Import BraidedMonoidal.
Require Import SymmetricMonoidal.

#[local] Set Universe Polymorphism.

Require Import CategoryAutomation.
Local Close Scope Mon_scope.

Local Open Scope Cat_scope.

Declare Scope Rig_scope.
Delimit Scope Rig_scope with Rig.
Open Scope Rig_scope.

Class PreDistributiveBimonoidalCategory {C : Type} {cC : Category C}
  {mAddC : MonoidalCategory cC} {bAddC : BraidedMonoidalCategory mAddC}
  (AddC : SymmetricMonoidalCategory bAddC)
  (MulC : MonoidalCategory cC) := {
  addC := AddC;
  mulC := MulC;
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

Arguments PreDistributiveBimonoidalCategory {_} {_ _ _}%Cat (_ _)%Cat.
Arguments left_distr_iso {_} {_ _ _ _ _ _}%Cat (_ _ _)%Rig.
Arguments right_distr_iso {_} {_ _ _ _ _ _}%Cat (_ _ _)%Rig.

Close Scope Mon_scope.
Close Scope Brd_scope.
Open Scope Mor_scope.


Notation "'addC_m'" := (addC
.(BraidedMonoidalCategory_of_SymmetricMonoidalCategory)
.(MonoidalCategory_of_BraidedMonoidalCategory)).

Notation "'addC_b'" := (addC
.(BraidedMonoidalCategory_of_SymmetricMonoidalCategory)).


Notation "'cplus'" := (tensor addC_m).

Notation "'cmul'" := (tensor mulC).

Notation "A + B" := (cplus A B) 
  (at level 50, left associativity) : Rig_scope.
Notation "A × B" := (cmul A B) 
  (at level 40, left associativity) : Rig_scope.

Notation "f ⊞ g" := (addC
  .(BraidedMonoidalCategory_of_SymmetricMonoidalCategory)
  .(MonoidalCategory_of_BraidedMonoidalCategory)
  .(tensor) @@ f, g) 
  (at level 50, left associativity) : Rig_scope.
Notation "f ⊠ g" := (mulC.(tensor) @@ f, g)
  (at level 40, left associativity) : Rig_scope.


Notation "'c1'" := (mon_I mulC)
  (at level 0, no associativity) : Rig_scope.
Notation "'c0'" := (mon_I addC_m)
  (at level 0, no associativity) : Rig_scope.

Notation "'α_' A , B , M" :=
  (reverse (mulC.(associator) A B M))
  (at level 20, no associativity) : Rig_scope.
Notation "'α'_' A , B , M" :=
  (reverse (addC_m.(associator) A B M))
  (at level 20, no associativity) : Rig_scope.
Notation "'α^-1_' A , B , M" :=
  (mulC.(associator) A B M).(forward)
  (at level 20, no associativity) : Rig_scope.
Notation "'α'^-1_' A , B , M" :=
  (addC_m.(associator) A B M).(forward)
  (at level 20, no associativity) : Rig_scope.


Notation "'δ_' A , B , M" :=
  (left_distr_iso A B M) 
  (at level 20, no associativity) : Rig_scope.
Notation "'δ#_' A , B , M" :=
  (right_distr_iso A B M) 
  (at level 20, no associativity) : Rig_scope.

Notation "'γ'_' A , B" :=
  (braiding (addC.(BraidedMonoidalCategory_of_SymmetricMonoidalCategory)) A B)
  (at level 35, A at next level, B at next level, no associativity) : Rig_scope.
(* NOTE! This one won't work unless in a Braided Rig: *)
Notation "'γ_' A , B" :=
  (braiding (mC:=mulC) _ A B)
  (at level 35, A at next level, B at next level, no associativity) : Rig_scope.

Notation "'λ_' A" :=
  (mulC.(left_unitor) A) 
  (at level 20, no associativity) : Rig_scope.
Notation "'λ'_' A" :=
  (addC_m.(left_unitor) A) 
  (at level 20, no associativity) : Rig_scope.

Notation "'ρ_' A" :=
  (mulC.(right_unitor) A) 
  (at level 20, no associativity) : Rig_scope.
Notation "'ρ'_' A" :=
  (addC_m.(right_unitor) A) 
  (at level 20, no associativity) : Rig_scope.

Class DistributiveBimonoidalCategory {C : Type} {cC : Category C}
  {mAddC : MonoidalCategory cC} {bAddC : BraidedMonoidalCategory mAddC}
  {AddC : SymmetricMonoidalCategory bAddC}
  {MulC : MonoidalCategory cC}
  (pdC : PreDistributiveBimonoidalCategory AddC MulC) := {
  predistr_cat := pdC;

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

Coercion predistr_cat : 
  DistributiveBimonoidalCategory >-> PreDistributiveBimonoidalCategory.

Notation "'λ*_' A" :=
  (left_absorbtion_iso A)
  (at level 20, no associativity) : Rig_scope.
Notation "'ρ*_' A" :=
  (right_absorbtion_iso A)
  (at level 20, no associativity) : Rig_scope.


(* Notation "'[+]'" := (addC) (at level 0) : Rig_scope.
Notation "'[×]'" := (addC) (at level 0) : Rig_scope. *)

Section CoherenceConditions.

Context {DD : Type} {cC : Category DD}
  {mAddC : MonoidalCategory cC} {bAddC : BraidedMonoidalCategory mAddC}
  {AddC : SymmetricMonoidalCategory bAddC}
  {MulC : MonoidalCategory cC}
  (pdC : PreDistributiveBimonoidalCategory AddC MulC)
  (rC : DistributiveBimonoidalCategory pdC).


Definition condition_I := forall (A B C : DD),
  δ_ A,B,C ∘ γ'_ (A×B), (A×C) ≃ 
  id_ A ⊠ γ'_ B, C ∘ δ_ A, C, B.

Definition condition_III := forall (A B C : DD),
  δ#_ A,B,C ∘ γ'_ (A×C),(B×C)
  ≃ (γ'_ A,B ⊠ id_ C) ∘ δ#_ B,A,C.
  
Definition condition_IV := forall (A B C D : DD),
  (* c_equiv (A:=(A+(B+C))×D) (B:=(A×D + B×D + C×D)) *)
  δ#_ A,(B+C),D ∘ (id_ (A×D) ⊞ δ#_ B,C,D) ∘ α'_ A×D, B×D, (C×D)
  ≃ (α'_ A,B,C ⊠ (id_ D)) ∘ δ#_ A+B,C,D ∘ (δ#_ A,B,D ⊞ id_ (C×D)).

Definition condition_V := forall (A B C D : DD),
  δ_ A,B,(C+D) ∘ (id_(A×B) ⊞ δ_ A,C,D) ∘ α'_ A×B,A×C,(A×D)
  ≃ id_ A ⊠ α'_ B,C,D ∘ δ_ A,B+C,D ∘ (δ_ A,B,C ⊞ id_(A×D)).

Definition condition_VI := forall (A B C D : DD),
  id_ A ⊠ δ_ B,C,D ∘ δ_ A,B×C,(B×D) ∘ (α_ A,B,C ⊞ α_ A,B,D)
  ≃ α_ A,B,(C+D) ∘ δ_ (A×B),C,D.

Definition condition_VII := forall (A B C D : DD),
  δ#_ A,B,(C×D) ∘ (α_ A,C,D ⊞ α_ B,C,D) 
  ≃ α_ A+B,C,D ∘ (δ#_A,B,C ⊠ id_ D) ∘ (δ#_ A×C,B×C,D).

Definition condition_VIII := forall (A B C D : DD),
  (id_ A ⊠ δ#_ B,C,D) ∘ δ_ A,B×D,(C×D) ∘ (α_ A,B,D ⊞ α_ A,C,D)
  ≃ α_ A,B+C,D ∘ (δ_ A,B,C ⊠ id_ D) ∘ δ#_ A×B,A×C,D.

Definition condition_IX := forall (A B C D : DD),
  δ#_ A,B,(C+D) ∘ (δ_ A,C,D ⊞ δ_ B,C,D) ∘ (α'_ (A×C+A×D),B×C,(B×D))
    ∘ ((α'^-1_ A×C,A×D,(B×C)) ⊞ id_ (B×D))
    ∘ ((id_ (A×C) ⊞ γ'_ A×D, (B×C)) ⊞ id_ (B×D))
    ∘ (α'_ A×C,B×C,(A×D) ⊞ id_ (B×D))
  ≃ δ_ A+B,C,D ∘ (δ#_ A,B,C ⊞ δ#_ A,B,D) ∘ α'_ (A×C+B×C),A×D,(B×D).

Definition condition_X :=
  λ*_ c0 ≃ ρ*_ c0.

Definition condition_XI := forall (A B : DD), 
  δ_ c0,A,B ∘ (λ*_ A ⊞ λ*_ B) ∘ λ'_ c0
  ≃ λ*_ (A + B).

Definition condition_XII := forall (A B : DD), 
  δ#_ A,B,c0 ∘ (ρ*_ A ⊞ ρ*_ B) ∘ (λ'_ c0)
  ≃ ρ*_ (A+B).

Definition condition_XIII := 
  ρ_ c0 ≃ λ*_ c1.

Definition condition_XIV :=
  λ_ c0 ≃ ρ*_ c1.

Definition condition_XVI := forall (A B : DD),
  α_ c0,A,B ∘ (λ*_ A ⊠ id_ B) ∘ λ*_B
  ≃ λ*_ (A×B).
  
Definition condition_XVII := forall (A B : DD), 
  α_ A,c0,B ∘ (ρ*_ A ⊠ id_ B) ∘ λ*_ B
  ≃ id_ A ⊠ λ*_ B ∘ ρ*_ A.

Definition condition_XVIII := forall (A B : DD), 
  α_ A,B,c0 ∘ ρ*_ (A×B)
  ≃ (id_ A ⊠ ρ*_ B) ∘ ρ*_ A.

Definition condition_XIX := forall (A B : DD),
  δ_ A,c0,B ∘ (ρ*_ A ⊞ id_ (A×B)) ∘ λ'_ (A×B)
  ≃ id_ A ⊠ λ'_ B.

Definition condition_XX := forall (A B : DD), 
  δ#_ c0,B,A ∘ (λ*_ A ⊞ id_ (B×A)) ∘ λ'_ (B×A)
  ≃ λ'_ B ⊠ id_ A.

Definition condition_XXI := forall (A B : DD),
  δ_ A,B,c0 ∘ (id_ (A×B) ⊞ ρ*_ A) ∘ (ρ'_ (A×B))
  ≃ id_ A ⊠ ρ'_ B.

Definition condition_XXII := forall (A B : DD),
  δ#_ A,c0,B ∘ (id_ (A×B) ⊞ λ*_ B) ∘ (ρ'_ (A×B))
  ≃ ρ'_ A ⊠ id_ B.

Definition condition_XXIII := forall (A B : DD), 
  δ_ c1,A,B ∘ (λ_ A ⊞ λ_ B)
  ≃ λ_ (A+B).

Definition condition_XXIV := forall (A B : DD),
  δ#_ A,B,c1 ∘ (ρ_ A ⊞ ρ_ B)
  ≃ ρ_ (A+B).

(* Conditions specific to braided rigs: *)
Definition condition_II `{@BraidedMonoidalCategory DD cC MulC} :=
  forall (A B C : DD),
    (δ#_ A, B, C) ∘ (γ_ A,C ⊞ γ_ B,C)
    ≃ γ_ A+B, C ∘ δ_ C,A,B.

Definition condition_XV `{@BraidedMonoidalCategory DD cC MulC} :=
  forall (A : DD),
    ρ*_ A ≃ γ_ A,c0 ∘ λ*_A.







Lemma equivalence_1 `{BMul: @BraidedMonoidalCategory DD cC MulC} : 
  condition_II -> (condition_I <-> condition_III).
Proof.
  unfold condition_II, condition_I, condition_III.
  intros cond_2; split.
  - intros cond_1 A B C.
    symmetry.
    rewrite <- right_unit; fold addC.
    rewrite <- (addC.(tensor).(id_bimap)). 
    rewrite <- 2!(proj1 (BMul.(braiding) _ _).(isomorphism_inverse)); fold mulC.
    rewrite compose_bimap.
    rewrite <- assoc, (assoc (_ ⊠ _)).
    rewrite (cond_2 B A C).
    rewrite <- assoc.
    rewrite braiding_natural.
    symmetry.
    rewrite <- (right_unit (δ#_ A,B, C)).
    rewrite <- (addC.(tensor).(id_bimap)).
    rewrite <- 2!braiding_inv_r.
    rewrite compose_bimap.
    rewrite <- assoc.
    rewrite cond_2.
    rewrite (assoc _ (_ ⊞ _)).
    rewrite braiding_natural.
    rewrite (assoc (γ_ (A+B), C)).
    simpl.
    rewrite <- (assoc (δ_ C,A,B)).
    rewrite (cond_1 C A B).
    rewrite <- 2!assoc.
    easy.
  - intros cond_3 A B C.
    rewrite <- (left_unit (δ_ A,B,C)).
    fold addC.
    rewrite <- braiding_inv_l.
    rewrite (assoc _ _ (δ_ _, _, _)).
    rewrite <- cond_2.
    rewrite 2!assoc, braiding_natural.
    rewrite <- (assoc (δ#_ B, C, A)).
    rewrite cond_3.
    symmetry.
    rewrite <- (left_unit (δ_ A,C,B)).
    rewrite <- braiding_inv_l.
    rewrite (assoc _ _ (δ_ _, _, _)).
    rewrite <- cond_2.
    rewrite <- (assoc (id_ A ⊠ _)).
    rewrite inv_braiding_natural.
    rewrite 2!assoc.
    easy.
Qed.


Local Open Scope Mon_scope.

Lemma stack_distr_pushout_r_bot : forall {C : Type}
  {cC : Category C} {mC : MonoidalCategory cC}
  {a b d m n} (f : a ~> b) (g : b ~> d) (h : m ~> n),
  (f ∘ g) ⊗ h ≃ f ⊗ h ∘ (g ⊗ (id_ n)).
Proof.
  intros.
  rewrite <- compose_bimap, right_unit.
  easy.
Qed.

Lemma stack_distr_pushout_r_top : forall {C : Type}
  {cC : Category C} {mC : MonoidalCategory cC}
  {a b m n o} (f : a ~> b) (g : m ~> n) (h : n ~> o),
  f ⊗ (g ∘ h) ≃ f ⊗ g ∘ (id_ b ⊗ h).
Proof.
  intros.
  rewrite <- compose_bimap, right_unit.
  easy.
Qed.

Lemma stack_distr_pushout_l_bot : forall {C : Type}
  {cC : Category C} {mC : MonoidalCategory cC}
  {a b d m n} (f : a ~> b) (g : b ~> d) (h : m ~> n),
  (f ∘ g) ⊗ h ≃ f ⊗ (id_ m) ∘ (g ⊗ h).
Proof.
  intros.
  rewrite <- compose_bimap, left_unit.
  easy.
Qed.

Lemma stack_distr_pushout_l_top : forall {C : Type}
  {cC : Category C} {mC : MonoidalCategory cC}
  {a b m n o} (f : a ~> b) (g : m ~> n) (h : n ~> o),
  f ⊗ (g ∘ h) ≃ id_ a ⊗ g ∘ (f ⊗ h).
Proof.
  intros.
  rewrite <- compose_bimap, left_unit.
  easy.
Qed.

Lemma stack_id_compose_split_top : forall {C : Type}
  {cC : Category C} {mC : MonoidalCategory cC}
  {topIn topMid topOut bot : C} 
  (f0 : topIn ~> topMid) (f1 : topMid ~> topOut),
  (f0 ∘ f1) ⊗ (id_ bot) ≃ f0 ⊗ id_ bot ∘ (f1 ⊗ id_ bot).
Proof.
  intros.
  rewrite <- compose_bimap, left_unit.
  easy.
Qed.

Lemma stack_id_compose_split_bot : forall {C : Type}
  {cC : Category C} {mC : MonoidalCategory cC}
  {top botIn botMid botOut : C} 
  (f0 : botIn ~> botMid) (f1 : botMid ~> botOut),
  (id_ top) ⊗ (f0 ∘ f1) ≃ id_ top ⊗ f0 ∘ (id_ top ⊗ f1).
Proof.
  intros.
  rewrite <- compose_bimap, left_unit.
  easy.
Qed.

Lemma id_stack_compose_topleft_general : forall {C : Type}
  {cC : Category C} {mC : MonoidalCategory cC}
  {topIn botIn topOut botOut : C} 
  (f0 : botIn ~> botOut) (f1 : topIn ~> topOut),
  ((c_identity topIn) ⊗ f0) ∘ (f1 ⊗ (c_identity botOut)) ≃ (f1 ⊗ f0).
Proof.
  intros.
  rewrite <- compose_bimap.
  rewrite left_unit; rewrite right_unit.
  easy.
Qed.

Lemma id_stackcompose_topright_general : forall {C : Type}
  {cC : Category C} {mC : MonoidalCategory cC}
  {topIn botIn topOut botOut : C} 
  (f0 : topIn ~> topOut) (f1 : botIn ~> botOut),
  (f0 ⊗ (c_identity botIn)) ∘ ((c_identity topOut) ⊗ f1) ≃ (f0 ⊗ f1).
Proof.
  intros.
  rewrite <- compose_bimap.
  rewrite right_unit, left_unit.
  easy.
Qed.

Lemma associator_cohere_inv : forall {C } 
  {cC : Category C} {mC : MonoidalCategory cC}
  {A B M N P Q : C} 
  (f : A ~> B) (g : M ~> N) (h : P ~> Q),
  (associator A M P)^-1 ∘ (f ⊗ g ⊗ h) ≃ (f ⊗ (g ⊗ h)) ∘ (associator B N Q)^-1.
Proof.
  intros.
  symmetry.
  rewrite <- compose_iso_l, <- assoc, <- compose_iso_r'.
  apply associator_cohere.
Qed.

Local Close Scope Mon_scope.


Open Scope Cat_scope.
Open Scope Rig_scope.


Ltac rassoc t :=
  let H := fresh in 
  let rt := right_associate t in
  assert (H: (t ≃ rt)%Cat) by (show_equiv_right_associate t);
  rewrite H; clear H.

Ltac rassoc_LHS :=
  match goal with |- (?LHS ≃ ?RHS) => rassoc LHS end.

Ltac rassoc_RHS := 
  match goal with |- (?LHS ≃ ?RHS) => rassoc RHS end.

Ltac right_associate f := 
  match f with 
  | ((?g ∘ ?h) ∘ ?i)%Cat => right_associate (g ∘ (h ∘ i))%Cat
  | (?g ∘ ?h)%Cat => (* g shouldn't be a composition *)
      let RAh := right_associate h in
        constr:((g ∘ RAh)%Cat)
  | _ => constr:(f)
  end.

(* TODO: Test this! *)
Ltac left_associate f := 
  match f with 
  | (?g ∘ (?h ∘ ?i))%Cat => left_associate ((g ∘ h) ∘ i)%Cat
  | (?g ∘ ?h)%Cat => (* h shouldn't be a composition *)
      let LAg := left_associate g in
        constr:((LAg ∘ h)%Cat)
  | _ => constr:(f)
  end.

Lemma assoc_compat_helper' : forall {C} 
  {cC : Category C} {A B M N : C} (f : A ~> B) 
  (g : B ~> M) (h : M ~> N) (fgh : A ~> N),
  (f ∘ g) ∘ h ≃ fgh -> f ∘ (g ∘ h) ≃ fgh.
Proof. intros; rewrite <- assoc; easy. Qed.

Ltac show_equiv_left_associate f :=
  let rec show_left f :=
  match f with  
  | (?g ∘ (?h ∘ ?i))%Cat => 
    (* RHS is `left_associate ((g ∘ h) ∘ i)%Cat` *)
    apply assoc_compat_helper';
    show_left (((g ∘ h) ∘ i)%Cat)
  | (?g ∘ ?h)%Cat => (* h shouldn't be a composition *)
    (* RHS is `(left_associate g ∘ h)` *) 
    apply compose_cancel_r;
    show_left g
  | _ => 
    (* RHS is `constr:(f)` *)
    reflexivity
  end
  in show_left f.

Ltac lassoc t :=
  let H := fresh in 
  let rt := left_associate t in
  assert (H: (t ≃ rt)%Cat) by (show_equiv_left_associate t);
  rewrite H; clear H.

Ltac lassoc_LHS :=
  match goal with |- (?LHS ≃ ?RHS) => lassoc LHS end.

Ltac lassoc_RHS := 
  match goal with |- (?LHS ≃ ?RHS) => lassoc RHS end.



Lemma equivalence_2 `{BMul: @BraidedMonoidalCategory DD cC MulC} :
  condition_II -> (condition_IV <-> condition_V).
Proof.
  unfold condition_II, condition_IV, condition_V.
  intros cond_2.
  split.
  - intros cond_4 A B C D.
    symmetry in cond_2.
    setoid_rewrite compose_iso_l in cond_2.
    symmetry.
    rewrite assoc.
    rewrite <- (compose_iso_l' 
      (BifunctorIsomorphism cmul (IdentityIsomorphism _) (associator _ _ _))).
    simpl.
    rewrite 2!cond_2.
    rewrite 2!assoc.
    rewrite <- compose_iso_l'.
    rewrite 2!stack_id_compose_split_top.
    rewrite assoc, <- 3!(assoc (_ ⊞ _)), <- (assoc (_ ⊠ _)).
    rewrite <- compose_bimap, iso_inv_r, right_unit.
    rewrite <- compose_bimap, right_unit, left_unit.
    rewrite <- assoc.
    rewrite <- id_stackcompose_topright_general, <- assoc.
    symmetry in cond_4.
    setoid_rewrite assoc in cond_4.
    setoid_rewrite <- (compose_iso_l' 
      (BifunctorIsomorphism cmul (associator _ _ _) (IdentityIsomorphism _))) 
      in cond_4.
    rewrite cond_4.
    simpl.
    rewrite 2!(assoc (_ ⊠ _)).
    (* rewrite ?assoc. *)
    rewrite (compose_iso_l 
      (BifunctorIsomorphism cmul (associator _ _ _) (IdentityIsomorphism A))).
    simpl.
    symmetry.
    rewrite <-(assoc (associator _ _ _ ^-1 ⊠ id_ A)).
    rewrite braiding_natural.
    simpl in cond_4.
    rewrite assoc. 
    simpl.
    rewrite <- 2!(assoc (id_ A ⊠ α'_ _, _, _)).
    rewrite <- compose_bimap, iso_inv_l, left_unit, id_bimap, left_unit.
    rewrite 2!cond_2.
    rewrite <- !assoc.
    rewrite iso_inv_r, left_unit.
    (* rewrite stack_id_compose_split_bot. *)
    rewrite 2!assoc.
    rewrite <- 1!(assoc (γ_ _, _ ⊞ γ_ _, _)).
    rewrite <- compose_bimap, right_unit.
    rewrite <- 2!(assoc ((γ_ _, A))).
    rewrite iso_inv_r, left_unit.
    rewrite ?assoc.
    apply compose_cancel_l.
    rewrite <- compose_bimap, left_unit, right_unit.
    rewrite associator_cohere_inv.
    rewrite <- assoc.
    apply compose_cancel_r.
    rewrite stack_distr_pushout_l_top.
    easy.
  - intros cond_5 A B C D.
    setoid_rewrite (compose_iso_r _ (BifunctorIsomorphism cplus _ _)) in cond_2.
    symmetry.
    rewrite assoc.
    simpl in cond_2.
    rewrite <- (compose_iso_l' 
      (BifunctorIsomorphism cmul (associator _ _ _) (IdentityIsomorphism D))).
    rewrite cond_2.
    rewrite 2!(assoc (γ_ _, _)).
    rewrite compose_iso_l.
    rewrite assoc. 
    simpl.
    rewrite <- compose_bimap.
    rewrite right_unit.
    setoid_rewrite assoc in cond_2.
    setoid_rewrite compose_iso_l' in cond_2.
    rewrite (cond_2 A B D).
    rewrite stack_distr_pushout_l_bot, <- assoc.
    setoid_rewrite assoc in cond_5.
    setoid_rewrite <- (compose_iso_l 
      (BifunctorIsomorphism cmul 
      (IdentityIsomorphism _) (associator _ _ _))) in cond_5.
    simpl in cond_5.
    rewrite <- cond_5.
    rewrite <- 2!(assoc _ _ (associator _ _ _ ^-1)).
    rewrite (assoc _ (associator _ _ _^-1)).
    rewrite associator_cohere_inv.

    (* rewrite <- 3!assoc. *)
    rewrite <- compose_iso_l.
    rewrite <- 2!(assoc (γ_ _, _)).
    rewrite <- braiding_natural.
    rewrite 2!(assoc (associator _ _ _ ⊠ id_ D)).
    apply compose_cancel_l.
    rewrite <- assoc.
    apply compose_cancel_r.
    rewrite (assoc (γ_ _, _)).
    rewrite compose_iso_l.
    rewrite <- (assoc ((γ_ _, _) ^-1)).
    simpl.
    rewrite (cond_2 A (B + C) D).
    rassoc_LHS; rassoc_RHS.
    apply compose_cancel_l.
    symmetry.
    simpl.
    rewrite <- compose_bimap, right_unit.
    rewrite (cond_2 B C D).
    apply stack_distr_pushout_l_top.
Qed.

Lemma distributive_hexagon_1 {BMulC : BraidedMonoidalCategory MulC} : 
  forall (A B C D : DD),
  id_ A ⊠ γ_ B, C ⊞ id_ A ⊠ γ_ B, D ∘ γ_ A,(C×B) ⊞ γ_ A, (D×B)
   ∘ α^-1_ C,B,A ⊞ α^-1_ D,B,A ∘ id_ C ⊠ (γ_ A, B)^-1 ⊞ id_ D ⊠ (γ_ A, B)^-1
  ≃ α_ A,B,C ⊞ α_ A,B,D ∘ γ_ (A×B),C ⊞ γ_ (A×B), D.
Proof.
  intros A B C D.
  rewrite <- 4!(compose_bimap cplus).
  apply morphism_bicompat; apply hexagon_resultant_1.
Qed.

Lemma distributive_hexagon_2 {BMulC : BraidedMonoidalCategory MulC} : 
  forall (A B C D : DD),
  id_ A ⊠ γ_ B,(C+D) ∘ γ_ A,((C+D)×B) 
   ∘ α^-1_ (C+D), B, A ∘ id_(C+D) ⊠ (γ_ A,B)^-1
  ≃ α_ A, B, (C+D) ∘ γ_ (A×B),(C+D).
Proof.
  intros.
  apply hexagon_resultant_1.
Qed.

Lemma equivalence_3_helper_1 {BMul : BraidedMonoidalCategory MulC} :
  forall (A B C D : DD),
  α^-1_ (C+D), B, A 
  ≃ (γ_ A,((C+D)×B)) ^-1 ∘ id_ A ⊠ (γ_ B, (C+D)) ^-1
   ∘ α_ A, B, (C+D) ∘ γ_ (A×B),(C+D) ∘ id_(C+D) ⊠ γ_ A,B.
Proof.
  intros A B C D.
  simpl.
  epose proof (compose_tensor_iso_r' (mC:=mulC) _ 
    (IdentityIsomorphism (C+D)) (γ_ A,B))
    as e; simpl in e; rewrite e; clear e.
  rassoc_RHS.
  rewrite <- compose_iso_l.
  rewrite <- (compose_tensor_iso_l (IdentityIsomorphism _)).
  simpl.
  lassoc_LHS.
  apply distributive_hexagon_2.
Qed.

Lemma equivalence_3_helper_2 {BMul : BraidedMonoidalCategory MulC} :
  forall (A B C D : DD),



  intros A B C D.
  epose proof BMul.(hexagon_1) as hex1.
  epose proof BMul.(hexagon_2) as hex2.
  fold mulC in hex1, hex2.
  progress simpl in hex1, hex2. (* ??? *)
  rewrite <- inv_braiding_natural.
  rassoc_RHS.
  rewrite <- compose_iso_l.
  symmetry in hex1.
  setoid_rewrite assoc in hex1.
  setoid_rewrite compose_iso_l in hex1.
  rewrite hex1.
  lassoc_RHS.
  rewrite compose_iso_r'.
  rassoc_LHS.
  rewrite <- compose_iso_l'.

  lassoc_RHS.
  rewrite <- hex2.
  setoid_rewrite compose_iso_r' in hex2.
  setoid_rewrite compose_iso_l' in hex2.
  rewrite <- hex2.


  setoid_rewrite compose_iso_l in hex1.
  rewrite hex1.

  setoid_rewrite assoc in hex1.
  setoid_rewrite compose_iso_l
  specialize (hex2 M (C+D))
  setoid_rewrite <- (compose_tensor_iso_r' _ (IdentityIsomorphism _) _) in hex2.
  setoid_rewrite <- (compose_tensor_iso_l' _ (IdentityIsomorphism _)) in hex2.
  rewrite hex2.
  
  setoid_rewrite compose_iso_l in hex1.

(* We don't need laplaza's coherence requirement, as that's baked-in for us. *)
Lemma equivalence_3 `{BMul: @BraidedMonoidalCategory DD cC MulC} : 
  condition_II -> (condition_VI <-> condition_VII).
Proof.
  unfold condition_II, condition_VI, condition_VII.
  intros cond_2; simpl in *; split.
  - intros cond_6 A B C D.
    symmetry.
    setoid_rewrite (compose_iso_r _ 
      (BifunctorIsomorphism tensor 
       (BMul.(braiding) _ _) (BMul.(braiding) _ _))) in cond_2.
    simpl in cond_2.
    epose proof (braiding.(component_biiso_natural)) as Hbr.
    setoid_rewrite compose_iso_r in Hbr.
    simpl in Hbr.
    rewrite (Hbr _ _ _ _ (δ#_ A, B, C) (id_ D)).
    rassoc_LHS.
    rewrite <- compose_iso_l'.
    rewrite 2!cond_2.
    rassoc_LHS.
    
    rewrite <- (assoc (g:= (B_ _, _))).
    rewrite iso_inv_l, left_unit.
    rewrite stack_id_compose_split_bot.
    rewrite (assoc (g:= id_ _ ⊗ _)).
    rewrite <- (assoc (f:= id_ _ ⊗ (_ ⊗ _))).
    rewrite <- left_distr_natural.
    lassoc_LHS.
    rewrite (assoc (g:= id_ _ ⊗ (_ ∘ _))).
    rewrite stack_id_compose_split_bot.
    rewrite (assoc (f:= id_ _ ⊗ B_ _, _)).
    setoid_rewrite <- (compose_iso_r' _
      (BifunctorIsomorphism tensor associator associator)) in cond_6.
    Local Open Scope Cat_scope.
    simpl in cond_6.
    rewrite (cond_6 D C A B).
    rewrite cond_2.

    rassoc_LHS.
    rewrite <- 2!compose_bimap.
    
    pose proof BMul.(@hexagon_2 _ _ _) as hex2.
    setoid_rewrite assoc in hex2.
    
    pose proof BMul.(@hexagon_1 _ _ _) as hex1.
    setoid_rewrite (compose_iso_r _
      (BifunctorIsomorphism tensor (IdentityIsomorphism _) (BMul.(braiding) _ _)))
      in hex1.
    setoid_rewrite <- (compose_iso_r _ 
      (BifunctorIsomorphism tensor (IdentityIsomorphism _) 
        (BMul.(braiding) _ _))) in hex1.
    setoid_rewrite assoc in hex1.
    setoid_rewrite (compose_iso_l
      (BifunctorIsomorphism tensor 
       (BMul.(braiding) _ _) (IdentityIsomorphism _)))
      in hex1.
    simpl in hex1.
    setoid_rewrite compose_iso_l in hex1.
    rewrite compose_iso_l.
    rewrite hex1.
    rassoc_LHS.
    rewrite <- compose_iso_l'.
    lassoc_RHS.
    setoid_rewrite <- assoc in hex2.
    rewrite <- hex2.
    rassoc_RHS.
    do 2 apply compose_cancel_l.
    rewrite compose_iso_l.
    lassoc_RHS.
    epose proof (component_biiso_natural_reverse 
      (N:=BMul.(braiding))) as e; simpl in e;
      rewrite e; clear e.
    rewrite (assoc (g:= (B_ _, _)^-1)).
    rewrite iso_inv_l, right_unit.
    lassoc_LHS.
    rewrite iso_inv_r, left_unit.
    rewrite <- id_bimap.
    rewrite <- left_distr_natural.
    rassoc_RHS.
    apply compose_cancel_l.
    rewrite <- 2!compose_bimap.
  
    specialize hex2 as hex2'.
    setoid_rewrite <- (compose_iso_r' _
      (BifunctorIsomorphism tensor 
      (IdentityIsomorphism _)
      (BMul.(braiding) _ _))) in hex2'.
    setoid_rewrite compose_iso_r in hex2'.
    unfold CommuteBifunctor in hex2'.
    simpl in hex2'.

    pose proof BMul.(@hexagon_1 _ _ _) as hex1'.
    setoid_rewrite (compose_iso_r _
      (BifunctorIsomorphism tensor 
      (IdentityIsomorphism _) (BMul.(braiding) _ _)))
      in hex1'.
    setoid_rewrite (compose_iso_r _ associator) in hex1'.
    do 3 setoid_rewrite assoc in hex1'.
    do 3 setoid_rewrite compose_iso_l' in hex1'.
    do 2 setoid_rewrite <- assoc in hex1'.
    setoid_rewrite (compose_iso_r _
      (BifunctorIsomorphism tensor 
       (BMul.(braiding) _ _) (IdentityIsomorphism _)))
      in hex1'.
    simpl in hex1'.

    apply morphism_bicompat;
  
    rewrite (hex2' D C _);
    rassoc_RHS;
    apply compose_cancel_l;

    rewrite <- (assoc (f:=associator ^-1));
    rewrite (hex1' _ C D);
    rewrite <- 2!(assoc (f:= id_ C ⊗ B_ _, _)), 
      <- compose_bimap, iso_inv_r, left_unit, id_bimap, left_unit;
    rewrite <- (assoc (f:=associator)), iso_inv_r, left_unit;
    
    epose proof (component_biiso_natural_reverse 
      (N:=BMul.(braiding)) _ _ _ _ _) as e;
    simpl in e; rewrite <- e;
    easy.
  - intros cond_7 A B C D.
    symmetry in cond_2.
    setoid_rewrite (compose_iso_l) in cond_2.
    simpl in cond_2.
    epose proof (braiding.(component_biiso_natural)) as Hbr.
    epose proof (braiding.(component_biiso_natural)) as Hbr'.
    epose proof (braiding.(component_biiso_natural)) as Hbr''.
    setoid_rewrite compose_iso_r in Hbr'.
    setoid_rewrite compose_iso_l' in Hbr''.
    simpl in Hbr, Hbr', Hbr''.
    rewrite <- (Hbr'' _ _ _ _ (δ_ B, C, D) (id_ A)).
    rassoc_LHS; rewrite <- compose_iso_l'.


    rewrite 2!cond_2.
    rewrite <- 2!(assoc (f:=B_ _, A)).
    rewrite iso_inv_r, left_unit.
    symmetry.
    rewrite cond_2.
    
    
    (* symmetry. *)
    rewrite 2!stack_id_compose_split_top.
    rassoc_RHS.
    epose proof (compose_iso_l (BifunctorIsomorphism tensor 
      (BMul.(braiding) _ _) (IdentityIsomorphism _))) as e;
      simpl in e; rewrite <- e; clear e.
    lassoc_LHS.
    rewrite Hbr.


    pose proof BMul.(@hexagon_2 _ _ _) as hex2.
    setoid_rewrite assoc in hex2.
    
    pose proof BMul.(@hexagon_1 _ _ _) as hex1.
    setoid_rewrite (compose_iso_r _
      (BifunctorIsomorphism tensor (IdentityIsomorphism _) (BMul.(braiding) _ _)))
      in hex1.
    setoid_rewrite <- (compose_iso_r _ 
      (BifunctorIsomorphism tensor (IdentityIsomorphism _) 
        (BMul.(braiding) _ _))) in hex1.
    setoid_rewrite assoc in hex1.
    setoid_rewrite (compose_iso_l
      (BifunctorIsomorphism tensor 
       (BMul.(braiding) _ _) (IdentityIsomorphism _)))
      in hex1.
    simpl in hex1.
    lassoc_RHS.
    rewrite <- (compose_iso_r _
      (BifunctorIsomorphism tensor associator associator)).
    unfold CommuteBifunctor.
    simpl.
    symmetry.

    epose proof (compose_iso_r _
      (BifunctorIsomorphism AddC.(tensor) 
      (BMul.(braiding) _ _) (BMul.(braiding) _ _))) as e;
      simpl in e.
    rewrite e; clear e.
    Admitted.

.
End CoherenceConditions.

Class SemiCoherent_DistributiveBimonoidalCategory {DD : Type} {cC : Category DD}
  {mAddC : MonoidalCategory cC} {bAddC : BraidedMonoidalCategory mAddC}
  {AddC : SymmetricMonoidalCategory bAddC}
  {MulC : MonoidalCategory cC}
  {pdC : PreDistributiveBimonoidalCategory AddC MulC}
  (rC : DistributiveBimonoidalCategory pdC) := {
  cond_I     : condition_I       _;
  cond_III   : condition_III     _;
  cond_IV    : condition_IV      _;
  cond_V     : condition_V       _;
  cond_VI    : condition_VI      _;
  cond_VII   : condition_VII     _;
  cond_VIII  : condition_VIII    _;
  cond_IX    : condition_IX      _;
  cond_X     : condition_X       _ _;
  cond_XI    : condition_XI      _ _;
  cond_XII   : condition_XII     _ _;
  cond_XIII  : condition_XIII    _ _;
  cond_XIV   : condition_XIV     _ _;
  cond_XVI   : condition_XVI     _ _;
  cond_XVII  : condition_XVII    _ _;
  cond_XVIII : condition_XVIII   _ _;
  cond_XIX   : condition_XIX     _ _;
  cond_XX    : condition_XX      _ _;
  cond_XXI   : condition_XXI     _ _;
  cond_XXII  : condition_XXII    _ _;
  cond_XXIII : condition_XXIII   _;
  cond_XXIV  : condition_XXIV    _;

(* condition_I (A B C : DD) : 
    δ_ A,B,C ∘ γ'_ (A×B), (A×C) ≃ 
    id_ A ⊠ γ'_ B, C ∘ δ_ A, C, B;
  condition_III (A B C : DD) :
    δ#_ A,B,C ∘ γ'_ (A×C),(B×C)
    ≃ (γ'_ A,B ⊠ id_ C) ∘ δ#_ B,A,C;
  condition_IV (A B C D : DD) :
    (* c_equiv (A:=(A+(B+C))×D) (B:=(A×D + B×D + C×D)) *)
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
*)
}. 




Class SemiCoherent_BraidedDistributiveBimonoidalCategory {DD : Type} {cC : Category DD}
  {mAddC : MonoidalCategory cC} {bAddC : BraidedMonoidalCategory mAddC}
  {AddC : SymmetricMonoidalCategory bAddC}
  {MulC : MonoidalCategory cC}
  {pdC : PreDistributiveBimonoidalCategory AddC MulC}
  (rC : DistributiveBimonoidalCategory pdC)
  (bMulC : BraidedMonoidalCategory MulC) := {
  cond_II   : condition_II      _;
  cond_XV   : condition_XV      _ _;
(*   
  condition_II (A B C : DD) : 
    (δ#_ A, B, C) ∘ (γ_ A,C ⊞ γ_ B,C)
    ≃ γ_ A+B, C ∘ δ_ C,A,B;
  condition_XV (A : DD) :
    ρ*_ A ≃ γ_ A,c0 ∘ λ*_A;
*)
}.

Close Scope Rig_scope.
