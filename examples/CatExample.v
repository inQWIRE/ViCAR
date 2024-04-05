Require Import Setoid.
From ViCaR Require Import CategoryTypeclass.

Open Scope Cat_scope.

Set Universe Polymorphism.

(* Generalizable Variables A B C D E cA cB cC cD cE. *)

Section IsomorphismInstances.

Context {C:Type} {cC : Category C} {cCh : CategoryCoherence cC}.

#[export] Instance IdentityIsomorphism (A : C) 
  : Isomorphism A A := {|
    forward := id_ A;
    reverse := id_ A;
    isomorphism_inverse := ltac:(rewrite left_unit; easy)
|}.

Definition ReverseIsomorphism {C : Type} {cC : Category C} 
  {cCh : CategoryCoherence cC} {A B : C} 
  (f : A <~> B) : B <~> A := {|
    forward := f.(reverse);
    reverse := f.(forward);
    isomorphism_inverse := 
      let (hA, hB) := f.(isomorphism_inverse) in conj hB hA
|}.

Program Definition ComposeIsomorphisms {A B M : C} 
  (f : A <~> B) (g : B <~> M) := {|
    forward := f ∘ g;
    reverse := g^-1 ∘ f^-1;
|}.
Next Obligation.
  split.
  - rewrite <- assoc, (assoc (f)), (iso_inv_r g), right_unit, (iso_inv_r f); easy.
  - rewrite <- assoc, (assoc (g^-1)), (iso_inv_l f), right_unit, (iso_inv_l g); easy.
Qed.

Program Definition Isomorphism_by_Functor
    {D} {cD : Category D} {cDh : CategoryCoherence cD}
  {A B : C} (F : Functor cC cD) (H : A <~> B) : F A <~> F B :=
  {|
    forward := F @ H;
    reverse := F @ H^-1
  |}.
Next Obligation.
  split; rewrite <- compose_map.
  - rewrite (iso_inv_r H), id_map; easy.
  - rewrite (iso_inv_l H), id_map; easy.
Qed.

End IsomorphismInstances.

Section NaturalTransformationInstances.

Context {C D E : Type} 
  {cC : Category C} {cD : Category D} {cE : Category E}
  {cCh : CategoryCoherence cC} 
  {cDh : CategoryCoherence cD} 
  {cEh : CategoryCoherence cE}.

Program Definition ReverseNaturalIsomorphism 
  {F G : Functor cC cD} (N : NaturalIsomorphism F G) : NaturalIsomorphism G F :=
  {| 
  component_iso := fun A => (ReverseIsomorphism (N A));
|}.
Next Obligation.
  match goal with
  |- ?g ≃ ?h => rewrite <- (right_unit h)
  end.
  rewrite <- (proj1 (N B).(isomorphism_inverse)).
  rewrite <- assoc, !(assoc _ _ (N B)), N.(component_iso_natural).
  apply compose_compat; [|easy].
  rewrite <- assoc, (proj2 (N A).(isomorphism_inverse)).
  rewrite left_unit.
  easy.
Qed.

Program Definition ComposeNaturalTransformations
  {F G H : Functor cC cD} (N : NaturalTransformation F G)
    (M : NaturalTransformation G H) : NaturalTransformation F H := {|
    component_map := fun A => (N.(component_map) A) ∘ (M.(component_map) A)
  |}.
Next Obligation.
  rewrite <- assoc, N.(component_map_natural), 
  assoc, M.(component_map_natural), <- assoc.
  easy.
Qed.

Notation "N '⨀' M" := (ComposeNaturalTransformations N M) 
  (at level 59, left associativity) : Cat_scope.

Program Definition ComposeNaturalIsomorphisms 
  {F G H : Functor cC cD} (N : NaturalIsomorphism F G) (M : NaturalIsomorphism G H)
   : NaturalIsomorphism F H :=
  {| 
  component_iso := fun A => ComposeIsomorphisms (N A) (M A)
|}.
Next Obligation.
  rewrite <- assoc, N.(component_iso_natural), 
    assoc, M.(component_iso_natural), <- assoc.
  easy.
Qed.

Program Definition ComposeFunctors {C D E : Type} 
  {cC : Category C} {cCh : CategoryCoherence cC}
  {cD : Category D} {cDh : CategoryCoherence cD}
  {cE : Category E} {cEh : CategoryCoherence cE}
  (F : Functor cC cD) (G : Functor cD cE) : Functor cC cE := {|
    obj_map := fun A => G (F A);
    morphism_map := fun A B f => G @ (F @ f);
  |}.
Next Obligation.
  rewrite 2!id_map; easy. Qed.
Next Obligation.
  rewrite 2!compose_map; easy. Qed.
Next Obligation.
  apply morphism_compat, morphism_compat; easy.
Qed.

Notation "F '○' G" := (ComposeFunctors F G)
  (at level 59, left associativity) : Cat_scope. 

Program Definition ComposeFunctorsAssociator {A B C D}
  {cA : Category A} {cB : Category B} {cC : Category C} {cD : Category D}
  {cAh : CategoryCoherence cA} {cBh : CategoryCoherence cB} 
  {cCh : CategoryCoherence cC} {cDh : CategoryCoherence cD}
  (F : Functor cA cB) (G : Functor cB cC) (H : Functor cC cD) : 
  NaturalIsomorphism (F ○ G ○ H) (F ○ (G ○ H)) :=
   {| component_iso := fun A => IdentityIsomorphism _ |}.
Next Obligation.
  rewrite left_unit, right_unit; easy.
Qed.

Program Definition NaturalIsomorphism_of_Compose 
  {F F' : Functor cC cD} {G G' : Functor cD cE} 
  (N : NaturalIsomorphism F F') (M : NaturalIsomorphism G G') 
    : NaturalIsomorphism (F ○ G) (F' ○ G') := 
  {| 
    component_iso := fun A => ComposeIsomorphisms 
      (Isomorphism_by_Functor G (N A)) (M (F' A))
|}.
Next Obligation.
  rewrite 2!component_iso_natural, <- assoc.
  rewrite component_iso_natural, 2!(assoc (M (F A))).
  apply compose_compat; [easy|].
  rewrite <- 2!compose_map.
  rewrite component_iso_natural.
  easy.
Qed.


Program Definition IdentityFunctor {C} (cC : Category C) 
  {cCh : CategoryCoherence cC} : Functor cC cC :=
  {| obj_map := fun A => A; morphism_map := fun _ _ f => f |}.
Solve All Obligations with (rewrite ?left_unit, ?right_unit; easy).

Program Definition IdentityNaturalIsomorphism {C D}
  {cC : Category C} {cD : Category D}
  {cCh : CategoryCoherence cC} {cDh : CategoryCoherence cD}
  (F : Functor cC cD) : 
  NaturalIsomorphism F F :=
  {| component_iso := fun A => IdentityIsomorphism _ |}.
Next Obligation.
  rewrite ?left_unit, ?right_unit; easy.
Qed.

End NaturalTransformationInstances.

Notation "N '⨀' M" := (ComposeNaturalTransformations N M) 
  (at level 59, left associativity) : Cat_scope.
Notation "F '○' G" := (ComposeFunctors F G)
  (at level 59, left associativity) : Cat_scope. 

Section NaturallyIsomorphic.

Context {C D E : Type} 
  {cC : Category C} {cCh : CategoryCoherence cC}
  {cD : Category D} {cDh : CategoryCoherence cD}.

Definition naturally_isomorphic {C D} {cC : Category C} {cD : Category D} 
  : relation (Functor cC cD) :=
  fun F G => exists (comp_map : forall A : C, F A <~> G A), 
    forall (A B : C) (f : A ~> B),
    F @ f ∘ comp_map B ≃ comp_map A ∘ G @ f.

Lemma naturally_isomorphic_of_NaturalIsomorphism {F G : Functor cC cD} : 
  NaturalIsomorphism F G -> naturally_isomorphic F G.
Proof.
  intros [c Hc].
  exists c; exact Hc.
Qed.

Lemma naturally_isomorphic_iff_ex_NaturalIsomorphism (F G : Functor cC cD) : 
  naturally_isomorphic F G <-> (exists _ : NaturalIsomorphism F G, True).
Proof.
  split.
  - intros [c Hc]. 
    exists {| component_iso := c; component_iso_natural := Hc |};
    easy.
  - intros [[c Hc] _]; exists c; exact Hc.
Qed.

Lemma naturally_isomorphic_refl :
  reflexive _ (@naturally_isomorphic C D cC cD).
Proof.
  intros F.
  apply naturally_isomorphic_of_NaturalIsomorphism, 
    IdentityNaturalIsomorphism.
Qed.

Lemma naturally_isomorphic_sym :
  symmetric _ (@naturally_isomorphic C D cC cD).
Proof.
  intros F G.
  rewrite naturally_isomorphic_iff_ex_NaturalIsomorphism.
  intros [N _].
  apply naturally_isomorphic_of_NaturalIsomorphism.
  exact (ReverseNaturalIsomorphism N).
Qed.

Lemma naturally_isomorphic_trans  :
  transitive _ (@naturally_isomorphic C D cC cD).
Proof.
  intros F G H.
  rewrite 2!naturally_isomorphic_iff_ex_NaturalIsomorphism.
  intros [N _] [M _].
  apply naturally_isomorphic_of_NaturalIsomorphism.
  exact (ComposeNaturalIsomorphisms N M).
Qed.

End NaturallyIsomorphic.


Section CategoryCat.

Lemma compose_functors_assoc {A B C D}
  {cA : Category A} {cB : Category B} {cC : Category C} {cD : Category D}
  {cAh : CategoryCoherence cA} {cBh : CategoryCoherence cB} 
  {cCh : CategoryCoherence cC} {cDh : CategoryCoherence cD}
  (F : Functor cA cB) (G : Functor cB cC) (H : Functor cC cD) 
  : naturally_isomorphic (F ○ G ○ H) (F ○ (G ○ H)).
Proof.
  exact (naturally_isomorphic_of_NaturalIsomorphism 
    (ComposeFunctorsAssociator F G H)).
Qed.
Record Cat := { 
  base_type : Type; 
  cat_inst : Category base_type; 
  cat_coh :> CategoryCoherence cat_inst 
}.

Existing Instance cat_coh.

Definition in_cat_of_category {U} (cU : Category U)
  {cUh : CategoryCoherence cU} : Cat :=
  {| base_type := U |}. 

Coercion cat_inst : Cat >-> Category.



#[export] Program Instance CatCategory : Category Cat := 
  {|
    morphism := fun U V => Functor U V;
    c_equiv := fun A B => naturally_isomorphic;
    compose := fun A B C => ComposeFunctors;
    c_identity := fun A => IdentityFunctor A
  |}.

#[export] Program Instance CatCategoryC : CategoryCoherence CatCategory.
Next Obligation.
  split.
  - apply naturally_isomorphic_refl.
  - apply naturally_isomorphic_trans.
  - apply naturally_isomorphic_sym.
Qed.
Next Obligation.
  destruct H as [cfg Hcfg].
  destruct H0 as [chj Hchj].
  eexists (fun A => ComposeIsomorphisms 
    (Isomorphism_by_Functor h (cfg A)) (chj (g A))).
  intros x y fxy.
  simpl.
  rewrite 2!Hchj, <- assoc.
  rewrite Hchj, 2!(assoc (chj (f x))).
  apply compose_compat; [easy|].
  rewrite <- 2!compose_map.
  rewrite Hcfg.
  easy.
Qed.
Next Obligation.
  apply naturally_isomorphic_of_NaturalIsomorphism.
  apply ComposeFunctorsAssociator.
Qed.
Next Obligation.
  exists (fun x => IdentityIsomorphism (f x)).
  intros.
  simpl.
  unfold id.
  rewrite left_unit, right_unit.
  easy.
Qed.
Next Obligation.
  exists (fun x => IdentityIsomorphism (f x)).
  intros.
  simpl. unfold id.
  rewrite left_unit, right_unit.
  easy.
Qed.

End CategoryCat.

Section CategoryCatProperties.


Context {C D E : Type} 
  {cC : Category C} {cCh : CategoryCoherence cC}
  {cD : Category D} {cDh : CategoryCoherence cD}
  {cE : Category E} {cEh : CategoryCoherence cE}.

Class CategoryProduct (A B : C) := {
  prod_AB : C;
  p_A : prod_AB ~> A;
  p_B : prod_AB ~> B;
  prod_mor : 
    forall (Q : C) (fA : Q ~> A) (fB : Q ~> B), Q ~> prod_AB;
  prod_mor_prop: 
    forall (Q : C) (fA : Q ~> A) (fB : Q ~> B),
    (prod_mor Q fA fB) ∘ p_A ≃ fA /\
    (prod_mor Q fA fB) ∘ p_B ≃ fB;
  prod_mor_unique : 
    forall (Q : C) (fA : Q ~> A) (fB : Q ~> B) 
    (fAB' : Q ~> prod_AB), 
    fA ≃ fAB' ∘ p_A -> fB ≃ fAB' ∘ p_B -> 
    fAB' ≃ prod_mor Q fA fB
}.

Local Notation "'@' AB" := (AB.(prod_AB)) (at level 8) : Cat_scope.

Lemma prod_mor_unique' {A B : C} 
  (AB : CategoryProduct A B) {Q} (fA : Q ~> A) (fB : Q ~> B) : 
  forall (fAB fAB' : Q ~> AB.(prod_AB)),
  fAB ∘ p_A ≃ fA  -> fAB ∘ p_B ≃ fB -> 
  fAB' ∘ p_A ≃ fA -> fAB' ∘ p_B ≃ fB -> 
  fAB ≃ fAB'.
Proof.
  intros.
  rewrite (prod_mor_unique Q fA fB) by easy.
  symmetry;
  rewrite (prod_mor_unique Q fA fB) by easy.
  easy.
Qed.

Program Definition category_product_unique (A B : C) :
  forall (AB AB' : CategoryProduct A B), Isomorphism @AB @AB' :=
  fun AB AB' =>
  {|
    forward := AB'.(prod_mor) @AB p_A p_B;
    reverse := AB.(prod_mor) @AB' p_A p_B;
  |}.
Next Obligation.
  split; eapply (prod_mor_unique' _ p_A p_B); rewrite 1?assoc.
  1,5: rewrite 2!(proj1 (prod_mor_prop _ _ _)); easy.
  1,4: rewrite 2!(proj2 (prod_mor_prop _ _ _)); easy.
  all: rewrite left_unit; easy.
Qed.

Class CategoryBigProd {J : Type} 
  (obj : J -> C) (prod_J : C) := {
  p_i : forall i, prod_J ~> obj i;
  big_cat_prod_mor : 
    forall (Q : C) (fQ_ : forall i, Q ~> obj i), Q ~> prod_J;
  big_cat_prod_mor_prop: 
    forall (Q : C) (fQ_ : forall i, Q ~> obj i),
    forall i, 
    (big_cat_prod_mor Q fQ_) ∘ p_i i ≃ fQ_ i;
  big_cat_prod_mor_unique : 
    forall (Q : C) (fQ_ : forall i, Q ~> obj i)
    (fAB' : Q ~> prod_J), 
    (forall i, fQ_ i ≃ fAB' ∘ p_i i) ->
    fAB' ≃ big_cat_prod_mor Q fQ_
}.

Lemma big_cat_prod_mor_unique' {J} {obj : J -> C} {pJ : C} 
  (HJ : CategoryBigProd obj pJ) {Q} (fQ_ : forall i, Q ~> obj i) :
  forall (fAB fAB' : Q ~> pJ),
  (forall i, fAB  ∘ p_i i ≃ fQ_ i) ->
  (forall i, fAB' ∘ p_i i ≃ fQ_ i) ->
  fAB ≃ fAB'.
Proof.
  intros.
  rewrite (big_cat_prod_mor_unique Q fQ_) by easy.
  symmetry;
  rewrite (big_cat_prod_mor_unique Q fQ_) by easy.
  easy.
Qed.

Program Definition category_big_cat_prod_unique {J} {obj : J -> C} :
  forall {pJ pJ'} (HJ : CategoryBigProd obj pJ) (HI' : CategoryBigProd obj pJ'), 
    Isomorphism pJ pJ' :=
  fun pJ pJ' HJ HJ' =>
  {|
    forward := HJ'.(big_cat_prod_mor) pJ p_i;
    reverse := HJ.(big_cat_prod_mor) pJ' p_i;
  |}.
Obligations.
Next Obligation.
  split; eapply (big_cat_prod_mor_unique' _ p_i); rewrite 1?assoc.
  1,3: intros i; rewrite assoc, 2!(big_cat_prod_mor_prop _ _); easy.
  all: intros; rewrite left_unit; easy.
Qed.


(* Search Morphisms.pointwise_relation. *)

Definition nat_trans_equiv `{cC : Category C, cD : Category D} 
  (F G : Functor cC cD) : relation (NaturalTransformation F G) := 
  fun N M => forall (A:C), N.(component_map) A ≃ M.(component_map) A.

(* #[program] Definition nat_trans_equiv_equivalence *)

Coercion NaturalTransformation_of_NaturalIsomorphism 
  : NaturalIsomorphism >-> NaturalTransformation.
(* I'm fine exporting, seeing as we're unlikely to be asking for any other
   category on Functor cC cD... or any at all! *)
#[export, program] Instance FunctorCategory : 
  Category (Functor cC cD) := {|
    morphism := @NaturalTransformation C D cC cD;
    c_equiv := nat_trans_equiv;
    compose := fun F G H => ComposeNaturalTransformations;
    c_identity := fun F => IdentityNaturalIsomorphism F;
  |}.

#[export, program] Instance FunctorCategoryC : 
  CategoryCoherence FunctorCategory.
Next Obligation.
  split; try easy.
  - intros F G H h1 h2 ?.
    etransitivity; [apply h1 | apply h2].
Qed.
Next Obligation.
  intros a. 
  simpl.
  apply compose_compat; easy.
Qed.
Next Obligation.
  intros a.
  simpl.
  rewrite assoc; easy.
Qed.
Next Obligation.
  intros a; simpl.
  rewrite left_unit; easy.
Qed.
Next Obligation.
  intros a; simpl.
  rewrite right_unit; easy.
Qed.

Definition big_prod {J : Type} (CJ : J -> Type) := forall i, CJ i.

#[export, program] Instance BigProductCategory {J : Type} (CJ : J -> Type)
  (cJ : forall i : J, Category (CJ i)) : Category (big_prod CJ) := {|
  morphism := fun is js => forall i, is i ~> js i;
  c_equiv := fun is js fis fjs => forall i, fis i ≃ fjs i;
  compose := fun is js ks fijs fjks => fun i => fijs i ∘ fjks i;
  c_identity := fun is => fun i => id_ (is i);
|}.

#[export, program] Instance BigProductCategoryC {J : Type} (CJ : J -> Type)
  (cJ : forall i : J, Category (CJ i)) 
  (cJh : forall i : J, CategoryCoherence (cJ i)) :
  CategoryCoherence (BigProductCategory CJ cJ).
Next Obligation.
  split; intros ? **; try easy.
  - etransitivity; easy.
Qed.
Next Obligation.
  apply compose_compat; easy.
Qed.
Next Obligation.
  rewrite assoc; easy.
Qed.
Next Obligation.
  rewrite left_unit; easy.
Qed.
Next Obligation.
  rewrite right_unit; easy.
Qed.

#[program, export] Instance BigProductComponentFunctor {J} (CJ : J -> Type) 
  (cJ : forall i : J, Category (CJ i))
  (cJh : forall i : J, CategoryCoherence (cJ i))
  (i : J) : 
  Functor (BigProductCategory CJ cJ) (cJ i) := {
  obj_map := fun is => is i;
  morphism_map := fun is js fijs => fijs i;
}.
Solve All Obligations with easy.

#[export] Instance BigProductFunctor_of_Components {J} 
  (CJ : J -> Type) (cJ : forall i : J, Category (CJ i)) (Q : Cat) 
  (fQ_ : forall i, Functor Q.(cat_inst) (cJ i)) : 
  Functor Q (BigProductCategory CJ cJ) := {
  obj_map := fun q => fun i => fQ_ i q;
  morphism_map := fun q r fqr => fun i => (fQ_ i).(morphism_map) fqr;
  id_map := fun a => fun i => (fQ_ i).(id_map) a;
  compose_map := fun a b m f g => fun i => (fQ_ i).(compose_map) f g;
  morphism_compat := fun a b f g H => fun i => (fQ_ i).(morphism_compat) f g H;
}.

#[export, program] Instance BigProductIsomorphism_of_Components {J} 
  (CJ : J -> Type) (cJ : forall i : J, Category (CJ i)) (As Bs : big_prod CJ)
  (Hiso : forall i, As i <~> Bs i) : As <~> Bs := {
  forward := fun i => Hiso i;
  reverse := fun i => Hiso i ^-1;
}.
Next Obligation.
  split; intros i; apply (Hiso i).(isomorphism_inverse).
Qed.

End CategoryCatProperties.