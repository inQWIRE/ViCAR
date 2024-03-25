Require Import Setoid.

Declare Scope Cat_scope.
Delimit Scope Cat_scope with Cat.
Local Open Scope Cat.

#[local] Set Universe Polymorphism.

Reserved Notation "A ~> B" (at level 38).
Reserved Notation "f ≃ g" (at level 70). (* \simeq *)
Reserved Notation "A ≅ B" (at level 70). (* \cong *)
Reserved Notation "'id_' A" (at level 15).

Class Category (C : Type) : Type := {
    morphism : C -> C -> Type
        where "A ~> B" := (morphism A B);

    (* Morphism equivalence *)
    c_equiv {A B : C} : relation (A ~> B)
        where "f ≃ g" := (c_equiv f g) : Cat_scope;

    compose {A B M : C} : 
        (A ~> B) -> (B ~> M) -> (A ~> M);

    c_identity (A : C) : A ~> A;
}.

Arguments morphism {_} (cC)%Cat (A B)%Cat : rename.
Arguments c_equiv {_} (cC)%Cat {A B}%Cat (f g)%Cat : rename.
Arguments compose {_} (cC)%Cat {_ _ _}%Cat (f g)%Cat : rename.
Arguments c_identity {_} {cC}%Cat (A)%Cat : rename.

Notation "'id_' A" := (c_identity A%Cat) 
  (at level 15, A at next level, no associativity) : Cat_scope.
Notation "A ~> B" := (morphism _%Cat A%Cat B%Cat)
  (at level 38, B at next level, no associativity) : Cat_scope.
Notation "f ≃ g" := (c_equiv _%Cat f%Cat g%Cat) 
  (at level 70, g at next level) : Cat_scope. (* \simeq *)
Notation "f ∘ g" := (compose _%Cat f%Cat g%Cat) 
  (at level 40, g at next level, left associativity) : Cat_scope. (* \circ *)

Class CategoryCoherence {C} (cC : Category C) : Type := {
  (* to_base_struct_cat := cC; *)

  c_equiv_rel {A B : C} : equivalence (A ~> B) cC.(c_equiv);

  compose_compat {A B M : C} : 
      forall (f g : A ~> B), f ≃ g ->
      forall (h j : B ~> M), h ≃ j ->
      f ∘ h ≃ g ∘ j;

  assoc {A B M N : C}
      (f : A ~> B) (g : B ~> M) (h : M ~> N) : 
      (f ∘ g) ∘ h ≃ f ∘ (g ∘ h);

  left_unit {A B : C} (f : A ~> B) : id_ A ∘ f ≃ f;
  right_unit {A B : C} (f : A ~> B) : f ∘ id_ B ≃ f;
}.

Arguments c_equiv_rel {_} {cC}%Cat {cCh}%Cat {A B}%Cat : rename.
Arguments assoc {_} {cC}%Cat {cCh}%Cat {_ _ _ _}%Cat (f g h)%Cat : rename.
Arguments compose_compat {_} {cC}%Cat {cCh}%Cat {_ _ _}%Cat (f g)%Cat _ (h j)%Cat : rename.
Arguments left_unit {_} {cC}%Cat {cCh}%Cat {A B}%Cat (f)%Cat : rename.
Arguments right_unit {_} {cC}%Cat {cCh}%Cat {A B}%Cat (f)%Cat : rename.

(* Coercion to_base_struct_cat : CategoryCoherence >-> Category. *)

Add Parametric Relation {C : Type} {cC : Category C} 
  {cCh : CategoryCoherence cC} (A B : C) : (A ~> B) cC.(c_equiv)
  reflexivity proved by (equiv_refl (A ~> B) _ (c_equiv_rel))
  symmetry proved by (equiv_sym (A ~> B) _ (c_equiv_rel))
  transitivity proved by (equiv_trans (A ~> B) _ (c_equiv_rel))
  as prop_equiv_rel.

Add Parametric Morphism {C : Type} {cC : Category C} {cCh : CategoryCoherence cC}
  (n o m : C) : cC.(compose)
  with signature (@c_equiv C cC n m) ==> 
    (@c_equiv C cC m o) ==> cC.(c_equiv) as compose_mor.
Proof. apply compose_compat. Qed.


Notation " 'is_inverse'  f  g" :=
  (f%Cat ∘ g%Cat ≃ id_ _ /\ g%Cat ∘ f%Cat ≃ id_ _) 
  (at level 10, f at next level, g at next level) : Cat_scope.

Lemma inverse_comm {C} {cC : Category C} {A B : C} (f : A ~> B) (g : B ~> A) : 
  is_inverse f g <-> is_inverse g f.
Proof. easy. Qed.

Lemma inverse_unique {C} {cC : Category C} {cCh : CategoryCoherence cC} {A B : C} 
  {f : A ~> B} {g g' : B ~> A} (Hg : is_inverse f g) (Hg' : is_inverse f g') :
  g ≃ g'.
Proof.
  rewrite <- (right_unit g).
  rewrite <- (proj1 Hg'), <- assoc, (proj2 Hg), left_unit.
  easy.
Qed.

(** Isomorphism of objects in a category, and equivalent typeclass, with
    parametric equivalence *)

Definition isomorphic {C : Type} {cC : Category C} (A B : C) :=
  exists (f : A ~> B) (g : B ~> A), is_inverse f g.

Arguments isomorphic {_} {_}%Cat (_ _)%Cat.

Class Isomorphism {C : Type} {cC : Category C} (A B : C) := {
  forward : A ~> B;
  reverse : B ~> A;
  isomorphism_inverse : is_inverse forward reverse;
}.
Arguments Isomorphism {_} {_}%Cat (_ _)%Cat.
Arguments forward {_} {_}%Cat {_ _}%Cat (f)%Cat : rename.
Arguments reverse {_} {_}%Cat {_ _}%Cat (f)%Cat : rename.
(* Notation id_A I := (proj1 I.(isomorphism_inverse)).
Notation id_B I := (proj2 I.(isomorphism_inverse)). *)
Coercion forward : Isomorphism >-> morphism.
Notation "f '^-1'" := (reverse f%Cat) (at level 25, only parsing) : Cat_scope.
Notation "f '⁻¹'" := (reverse f%Cat) (at level 25) : Cat_scope. (* \^- \^1 *)

Notation "A '<~>' B" := (Isomorphism A%Cat B%Cat) (at level 70) : Cat_scope.
Notation "A ≅ B" := (isomorphic A%Cat B%Cat) (at level 70) : Cat_scope. (* \cong *)

Lemma isomorphic_iff_Isomorphism {C : Type} {cC : Category C} (A B : C) :
  isomorphic A B <-> exists _: Isomorphism A B, True.
Proof.
  split.
  - intros [f [g [Hfg Hgf]]].
    eexists.
    + eapply Build_Isomorphism; split; eassumption.
    + apply I.
  - intros [[f g [Hfg Hgf]] _].
    exists f; exists g; auto.
Qed.

Lemma left_unit' {C : Type} {cC : Category C} {cCh : CategoryCoherence cC}
  {A B : C} (f : A ~> B) : id_ _ ∘ f ≃ f.
Proof.
  rewrite (left_unit).
  easy. 
Qed.

Lemma isomorphic_refl {C : Type} {cC : Category C} {cCh : CategoryCoherence cC}
  (A : C) : isomorphic A A.
Proof.
  exists (c_identity A).
  exists (c_identity A).
  rewrite left_unit.
  split; reflexivity.
Qed.

Lemma isomorphic_trans {C : Type} {cC : Category C} {cCh : CategoryCoherence cC}
  (A B M : C) : 
  isomorphic A B -> isomorphic B M -> isomorphic A M.
Proof.
  intros [fAB [fBA [HfABA HfBAB]]] [fBM [fMB [HfBMB HfMBM]]].
  exists (fAB ∘ fBM).
  exists (fMB ∘ fBA).
  split;
  rewrite (assoc).
  - rewrite <- (assoc fBM), HfBMB, (left_unit), HfABA.
    reflexivity.
  - rewrite <- (assoc fBA), HfBAB, (left_unit), HfMBM.
    reflexivity.
Qed.

Lemma isomorphic_sym {C : Type} {cC : Category C} {cCh : CategoryCoherence cC} 
  (A B : C) : 
  isomorphic A B -> isomorphic B A.
Proof.
  intros [fAB [fBA [HfABA HfBAB]]].
  exists fBA; exists fAB.
  rewrite HfABA, HfBAB.
  split; reflexivity.
Qed.

Add Parametric Relation {C : Type} {cC : Category C} 
  {cCh : CategoryCoherence cC} : C (@isomorphic C cC)
  reflexivity proved by isomorphic_refl
  symmetry proved by isomorphic_sym
  transitivity proved by isomorphic_trans
  as isomorphic_equiv_rel.

(** Functors, including instances as equivalence & isomorphism parametric morphisms *)
Class Functor {C D : Type} (cC: Category C) (cD : Category D) : Type := {
  obj_map : C -> D;
  morphism_map {A B : C} : (A ~> B) -> (obj_map A ~> obj_map B);
  id_map (A : C) : morphism_map (id_ A) ≃ id_ (obj_map A);
  compose_map {A B M : C} (f : A ~> B) (g : B ~> M) :
    morphism_map (f ∘ g) ≃ morphism_map f ∘ morphism_map g;
  morphism_compat {A B : C} (f g : A ~> B) : f ≃ g -> (morphism_map f) ≃ (morphism_map g);
}.

Arguments obj_map {_ _} {_ _}%Cat (F)%Cat (A)%Cat : rename.
Arguments morphism_map {_ _} {_ _}%Cat (F)%Cat {A B}%Cat (f)%Cat : rename.
Arguments id_map {_ _} {_ _}%Cat (F)%Cat (A)%Cat : rename.
Arguments compose_map {_ _} {_ _}%Cat (F)%Cat {A B M}%Cat (f g)%Cat : rename.
Arguments morphism_compat {_ _} {_ _}%Cat (F)%Cat {A B}%Cat (f g)%Cat : rename.

Coercion obj_map : Functor >-> Funclass.
Arguments morphism_map {_ _} {_ _}%Cat (_)%Cat {_ _}%Cat (_)%Cat.
Notation "F @ f" := (morphism_map F%Cat f%Cat) (at level 38) : Cat_scope.

Add Parametric Morphism {C D : Type} {cC : Category C} {cD : Category D}
  (F : Functor cC cD) (A B : C): F.(morphism_map)
  with signature (@c_equiv C cC A B) ==> (@c_equiv D cD (F A) (F B)) as functor_equiv_mor.
Proof. apply morphism_compat. Qed.

Add Parametric Morphism {C D : Type} {cC : Category C} 
  {cCh : CategoryCoherence cC} {cD : Category D} {cDh : CategoryCoherence cD}
  (F : Functor cC cD) : F.(obj_map)
  with signature (@isomorphic C cC) ==> (@isomorphic D cD) as functor_isomorphic_mor.
Proof. 
  intros A B [fAB [fBA [HfABA HfBAB]]].
  exists (F @ fAB); exists (F @ fBA).
  rewrite <- 2!compose_map, HfABA, HfBAB.
  split; apply id_map.
Qed.



Class Bifunctor {C1 C2 D : Type} (cC1: Category C1) 
  (cC2 : Category C2) (cD : Category D) := {
  obj_bimap : C1 -> C2 -> D;
  morphism_bimap {A1 B1 : C1} {A2 B2 : C2} : (A1 ~> B1) -> (A2 ~> B2) ->
    (obj_bimap A1 A2) ~> (obj_bimap B1 B2);
  id_bimap (A1 : C1) (A2 : C2) :
    (morphism_bimap (id_ A1) (id_ A2)) ≃ id_ (obj_bimap A1 A2);
  compose_bimap {A1 B1 M1 : C1} {A2 B2 M2 : C2}
    (f1 : A1 ~> B1) (g1 : B1 ~> M1) (f2 : A2 ~> B2) (g2 : B2 ~> M2) :
    morphism_bimap (f1 ∘ g1) (f2 ∘ g2) ≃ morphism_bimap f1 f2 ∘ morphism_bimap g1 g2;
  morphism_bicompat {A1 B1 : C1} {A2 B2 : C2} (f f' : A1 ~> B1) (g g' : A2 ~> B2) :
    f ≃ f' -> g ≃ g' -> morphism_bimap f g ≃ morphism_bimap f' g'
}.

Arguments obj_bimap {_ _ _} {_ _ _}%Cat (F)%Cat (A1 A2)%Cat : rename.
Arguments morphism_bimap {_ _ _} {_ _ _}%Cat (F)%Cat 
  {A1 B1 A2 B2}%Cat (f1 f2)%Cat : rename.
Arguments id_bimap {_ _ _} {_ _ _}%Cat (F)%Cat (A1 A2)%Cat : rename.
Arguments compose_bimap {_ _ _} {_ _ _}%Cat (F)%Cat 
  {A1 B1 M1 A2 B2 M2}%Cat (f1 g1 f2 g2)%Cat : rename.
Arguments morphism_bicompat {_ _ _} {_ _ _}%Cat (F)%Cat
  {A1 B1 A2 B2}%Cat (f1 f1' f2 f2')%Cat : rename.

Coercion obj_bimap : Bifunctor >-> Funclass.
Notation " F '@@' X , Y " := (morphism_bimap F%Cat X%Cat Y%Cat) 
  (at level 38) : Cat_scope.

Add Parametric Morphism {C1 C2 D : Type} 
  {cC1 : Category C1} {cC2 : Category C2} {cD : Category D}
  (F : Bifunctor cC1 cC2 cD) (A1 B1 : C1) (A2 B2 : C2) : F.(morphism_bimap)
  with signature (@c_equiv C1 cC1 A1 B1) ==> (@c_equiv C2 cC2 A2 B2) 
    ==> (@c_equiv D cD (F A1 A2) (F B1 B2)) as bifunctor_equiv_mor.
Proof. intros. apply morphism_bicompat; easy. Qed.

Add Parametric Morphism {C1 C2 D : Type} {cC1 : Category C1} 
  {cC1h : CategoryCoherence cC1} {cC2 : Category C2} 
  {cC2h : CategoryCoherence cC2} {cD : Category D} {cDh : CategoryCoherence cD} 
  (F : Bifunctor cC1 cC2 cD) : F.(obj_bimap)
  with signature (@isomorphic C1 cC1) ==> (@isomorphic C2 cC2) 
    ==> (@isomorphic D cD) as bifunctor_isometric_mor.
Proof. 
  intros A1 B1 [fAB1 [fBA1 [HfABA1 HfBAB1]]] A2 B2 [fAB2 [fBA2 [HfABA2 HfBAB2]]].
  exists (F @@ fAB1, fAB2); exists (F @@ fBA1, fBA2).
  rewrite <- 2!F.(compose_bimap), HfABA1, HfBAB1, HfABA2, HfBAB2.
  split; apply id_bimap.
Qed.

Definition CommuteBifunctor {C1 C2 D : Type} `{cC1 : Category C1} 
  `{cC2 : Category C2} `{cD : Category D} (F : Bifunctor cC1 cC2 cD) 
  : Bifunctor cC2 cC1 cD := {|
  obj_bimap := fun A B => F B A;
  morphism_bimap := fun A1 A2 B1 B2 fAB1 fAB2 => F @@ fAB2, fAB1;
  id_bimap := ltac:(intros; apply id_bimap);
  compose_bimap := ltac:(intros; apply compose_bimap);
  morphism_bicompat := ltac:(intros; apply morphism_bicompat; easy);
|}.

Arguments CommuteBifunctor {_ _ _} {_ _ _}%Cat (_)%Cat /.
#[export] Typeclasses Transparent CommuteBifunctor.


(** Natural Transformations & Isomorphisms (and the equivalents for Bifunctors) *)
Class NaturalTransformation {C D : Type} `{cC: Category C} `{cD : Category D}
  (F G : Functor cC cD) := {
  component_map (A : C) : F A ~> G A;
  component_map_natural {A B : C} (f : A ~> B) :
    F @ f ∘ component_map B ≃ component_map A ∘ G @ f;
}.
Arguments NaturalTransformation {_ _} {_ _}%Cat (_ _)%Cat.
Arguments component_map {_ _} {_ _}%Cat {_ _}%Cat (N)%Cat (_)%Cat : rename.
Arguments component_map_natural {_ _} {_ _}%Cat {_ _}%Cat 
  {N}%Cat {_ _}%Cat (f)%Cat : rename.

Class NaturalIsomorphism {C D : Type} `{cC: Category C} `{cD : Category D}
  (F G : Functor cC cD) := {
  component_iso (A : C) : F A <~> G A;
  component_iso_natural (A B : C) (f : A ~> B) :
    F@f ∘ component_iso B ≃ component_iso A ∘ G@f;
}.
Arguments NaturalIsomorphism {_ _} {_ _}%Cat (_ _)%Cat.
Arguments component_iso {_ _} {_ _}%Cat {_ _}%Cat (N)%Cat (_)%Cat : rename.
Arguments component_iso_natural {_ _} {_ _}%Cat {_ _}%Cat 
  {N}%Cat {_ _}%Cat (f)%Cat : rename.

Coercion component_iso : NaturalIsomorphism >-> Funclass.

Definition NaturalTransformation_of_NaturalIsomorphism {C D : Type} 
  `{cC : Category C} `{cD : Category D} {F G : Functor cC cD}
  (N : NaturalIsomorphism F G) : NaturalTransformation F G := {|
  component_map := component_iso N;
  component_map_natural := ltac:(intros; apply component_iso_natural);
|}.



Class NaturalBiTransformation {C1 C2 D : Type} `{cC1 : Category C1} 
  `{cC2 : Category C2} `{cD : Category D} (F G : Bifunctor cC1 cC2 cD) := {
  component_bimap (A1 : C1) (A2 : C2) : F A1 A2 ~> G A1 A2;
  component_bimap_natural {A1 B1 : C1} {A2 B2 : C2}
    (f1 : A1 ~> B1) (f2 : A2 ~> B2) :
    (F @@ f1, f2) ∘ (component_bimap B1 B2) 
      ≃ (component_bimap A1 A2) ∘ (G @@ f1, f2)
}.
Arguments NaturalBiTransformation {_ _ _} {_ _ _}%Cat (_ _)%Cat.
Arguments component_bimap {_ _ _} {_ _ _}%Cat {_ _}%Cat 
  (N)%Cat (_ _)%Cat : rename.
Arguments component_bimap_natural {_ _ _} {_ _ _}%Cat {_ _}%Cat 
  {N}%Cat {_ _ _ _}%Cat (f1 f2)%Cat : rename.

Class NaturalBiIsomorphism {C1 C2 D : Type} `{cC1 : Category C1} 
  `{cC2 : Category C2} `{cD : Category D} (F G : Bifunctor cC1 cC2 cD) := {
  component_biiso (A1 : C1) (A2 : C2) : F A1 A2 <~> G A1 A2;
  component_biiso_natural (A1 B1 : C1) (A2 B2 : C2) (f1 : A1 ~> B1) (f2 : A2 ~> B2) :
    (F @@ f1, f2) ∘ (component_biiso B1 B2) ≃ (component_biiso A1 A2) ∘ (G @@ f1, f2)
}.
Arguments NaturalBiIsomorphism {_ _ _} {_ _ _}%Cat (_ _)%Cat.
Arguments component_biiso {_ _ _} {_ _ _}%Cat {_ _}%Cat 
  (N)%Cat (_ _)%Cat : rename.
Arguments component_bimap_natural {_ _ _} {_ _ _}%Cat {_ _}%Cat 
  {N}%Cat {_ _ _ _}%Cat (f1 f2)%Cat : rename.
Coercion component_biiso : NaturalBiIsomorphism >-> Funclass.

Definition NaturalBiTransformation_of_NaturalBiIsomorphism {C1 C2 D : Type} 
  `{cC1 : Category C1} `{cC2 : Category C2} `{cD : Category D} {F G : Bifunctor cC1 cC2 cD}
  (N: NaturalBiIsomorphism F G) : NaturalBiTransformation F G := {|
  component_bimap := N.(component_biiso);
  component_bimap_natural := ltac:(intros; apply component_biiso_natural);
|}.
(* Just to simplify notation, I'm removing this for now... *)
(* Coercion NaturalBiTransformation_of_NaturalBiIsomorphism : 
  NaturalBiIsomorphism >-> NaturalBiTransformation. *)



(** The opposite category, contravariant functor (currently unused) *)
(* This should in fact be a definition, not an instance, as we definititely
   don't want typeclass resolution trying to use it. *)
Definition OppositeCategory {C : Type} (cC : Category C) : Category C := {|
  morphism := fun A B => cC.(morphism) B A; 
  c_equiv := fun A B => @c_equiv C cC B A;
  compose := fun A B M fAB fBM => fBM ∘ fAB;
  c_identity := c_identity;
|}.

Notation "C '^op'" := (OppositeCategory C%Cat) 
  (at level 34, left associativity, only parsing) : Cat_scope.
Notation "C 'ᵒᵖ'" := (OppositeCategory C%Cat) 
  (at level 34, left associativity) : Cat_scope. (* \^o \^p *)
#[export] Typeclasses Transparent OppositeCategory.

#[program] Definition OppositeCategoryCoherence {C : Type} {cC : Category C}
  (cCh : CategoryCoherence cC) : CategoryCoherence (cC^op) := {|
  c_equiv_rel := fun A B => @c_equiv_rel C cC cCh B A;
  compose_compat := fun A B M f g Hfg h j Hhj => 
    @compose_compat C cC cCh M B A _ _ Hhj _ _ Hfg;
  assoc := fun A B M N f g h => 
    equiv_sym _ _ (c_equiv_rel) _ _ (@assoc C cC cCh N M B A h g f);
  left_unit := fun A B => @right_unit C cC cCh B A;
  right_unit := fun A B => @left_unit C cC cCh B A;
|}.

Class ContraFunctor {C D : Type} (cC: Category C) (cD : Category D) : Type := {
  obj_contramap : C -> D;
  morphism_contramap {A B : C} : (A ~> B) -> 
    (obj_contramap B ~> obj_contramap A);
  id_contramap (A : C) : morphism_contramap (id_ A) ≃ id_ (obj_contramap A);
  compose_contramap {A B M : C} (f : A ~> B) (g : B ~> M) :
    morphism_contramap (f ∘ g) ≃ morphism_contramap g ∘ morphism_contramap f;
  morphism_contracompat {A B : C} (f g : A ~> B) : f ≃ g -> 
    (morphism_contramap f) ≃ (morphism_contramap g);
}.
Arguments ContraFunctor {_ _} (_ _)%Cat.
Arguments obj_contramap {_ _} {_ _}%Cat (F)%Cat (A)%Cat : rename.
Arguments morphism_contramap {_ _} {_ _}%Cat (F)%Cat 
  {A B}%Cat (f)%Cat : rename.
Arguments id_contramap {_ _} {_ _}%Cat (F)%Cat (A)%Cat : rename.
Arguments compose_contramap {_ _} {_ _}%Cat (F)%Cat 
  {A B M}%Cat (f g)%Cat : rename.
Arguments morphism_contracompat {_ _} {_ _}%Cat (F)%Cat 
  {A B}%Cat (f g)%Cat : rename.
Coercion obj_contramap : ContraFunctor >-> Funclass.
Notation "F @' X" := (F.(morphism_contramap) X) 
  (at level 55, no associativity) : Cat_scope.

Add Parametric Morphism {C D : Type} {cC : Category C} {cD : Category D}
  (F : ContraFunctor cC cD) (A B : C): F.(morphism_contramap)
  with signature 
  (@c_equiv C cC A B) ==> (@c_equiv D cD (F B) (F A)) as contrafunctor_equiv_mor.
Proof. apply morphism_contracompat. Qed.

Add Parametric Morphism {C D : Type} {cC : Category C} {cCh : CategoryCoherence cC} 
  {cD : Category D} {cDh : CategoryCoherence cD}
  (F : ContraFunctor cC cD) : F.(obj_contramap)
  with signature 
  (@isomorphic C cC) ==> (@isomorphic D cD) as contrafunctor_isomorphic_mor.
Proof. 
  intros A B [fAB [fBA [HfABA HfBAB]]].
  exists (F @' fBA); exists (F @' fAB).
  rewrite <- 2!compose_contramap, HfABA, HfBAB.
  split; apply id_contramap.
Qed.

Definition ContravariantFunctor {C D : Type} 
  (cC: Category C) (cD : Category D) : Type := Functor (cC^op) cD.

#[export] Typeclasses Transparent ContravariantFunctor.

Definition ContravariantFunctor_of_ContraFunctor {C D : Type} 
  `{cC : Category C} `{cD : Category D} (F : ContraFunctor cC cD) : 
  ContravariantFunctor cC cD := {|
  obj_map := F.(obj_contramap);
  morphism_map := fun (A B : C) (f : @morphism C (cC^op) A B) =>
    F.(morphism_contramap) f;
  id_map := F.(id_contramap);
  compose_map := fun (A B M : C) (f : @morphism C (cC^op) A B)
    (g : @morphism C (cC^op) B M) =>
    F.(compose_contramap) g f;
  morphism_compat := fun A B => F.(morphism_contracompat);
|}.

Definition ContraFunctor_of_ContravariantFunctor {C D : Type} 
  `{cC : Category C} `{cD : Category D} (F : ContravariantFunctor cC cD) : 
  ContraFunctor cC cD := {|
  obj_contramap := F.(obj_map);
  morphism_contramap := fun A B (f : cC.(morphism) A B) =>
    F @ f;
  id_contramap := F.(id_map);
  compose_contramap := fun A B M f g => F.(compose_map) g f;
  morphism_contracompat := fun A B f g => F.(morphism_compat) f g;
|}.


Section ProductCategories.

(** Product categories, equivalence of functors from them and bifunctors (currently unused) *)
Local Notation product_relation simT simU := (fun AB CD =>
  simT (fst AB) (fst CD) /\ simU (snd AB) (snd CD)).

Definition product_relation_refl {T U : Type} 
  {simT : relation T} {simU : relation U} 
  (reflT : reflexive T simT) (reflU : reflexive U simU) : 
    reflexive (T*U) (product_relation simT simU) :=
  fun AB => match AB with (A, B) => conj (reflT A) (reflU B) end.

Definition product_relation_trans {T U : Type} {simT : relation T} {simU : relation U}
  (transT : transitive T simT) (transU : transitive U simU) : transitive (T*U) (product_relation simT simU) :=
  fun AB CD EF => 
  match AB with (A, B) =>
  match CD with (C, D) =>
  match EF with (E, F) => fun sABCD sCDEF =>
  match sABCD with conj sAC sBD =>
  match sCDEF with conj sCE sDF =>
    conj (transT A C E sAC sCE) (transU B D F sBD sDF)
  end end end end end.

Definition product_relation_sym {T U : Type} {simT : relation T} {simU : relation U}
  (symT : symmetric T simT) (symU : symmetric U simU) : symmetric (T*U) (product_relation simT simU) :=
  fun AB CD =>
  match AB with (A, B) =>
  match CD with (C, D) => fun sABCD =>
  match sABCD with conj sAC sBD =>
    conj (symT A C sAC) (symU B D sBD)
  end end end.

Definition product_relation_equivalence {T U : Type} {simT : relation T} {simU : relation U}
  (eqT : equivalence T simT) (eqU : equivalence U simU) 
  : equivalence (T*U) (product_relation simT simU) :=
  match eqT with 
  | {| equiv_refl := reflT; equiv_trans := transT; equiv_sym := symT |} =>
  match eqU with 
  | {| equiv_refl := reflU; equiv_trans := transU; equiv_sym := symU |} =>
  {| 
    equiv_refl := product_relation_refl reflT reflU;
    equiv_trans := product_relation_trans transT transU; 
    equiv_sym := product_relation_sym symT symU;
  |}
end end.

#[local] Instance ProductCategory {C D : Type} 
  (cC : Category C) (cD : Category D) : Category (C*D) := {
  morphism := fun AB MN =>
    prod (cC.(morphism) (fst AB) (fst MN)) (cD.(morphism) (snd AB) (snd MN));
  c_equiv :=
    fun AB A'B' => 
    match AB with (A, B) =>
    match A'B' with (A', B') => 
      product_relation (@c_equiv C cC A A') (@c_equiv D cD B B')
    end end;
  compose := fun AB MN EF =>
    match AB with (A, B) =>
    match MN with (M, N) =>
    match EF with (E, F) => fun sABMN sMNEF =>
    match sABMN with pair sAM sBN =>
    match sMNEF with pair sME sNF =>
      (sAM ∘ sME, sBN ∘ sNF)
    end end end end end;
  c_identity := fun AB => match AB with (A, B) => (c_identity A, c_identity B) end;
}.

#[program] Instance ProductCategoryCoherence {C D : Type} 
  {cC : Category C} {cD : Category D}
  (cCh : CategoryCoherence cC) (cDh : CategoryCoherence cD) 
  : CategoryCoherence (ProductCategory cC cD) := {
  c_equiv_rel := fun AB A'B' => 
    match AB with (A, B) =>
    match A'B' with (A', B') =>
      product_relation_equivalence (@c_equiv_rel C cC cCh A A') 
        (@c_equiv_rel D cD cDh B B')
    end end;
}.
Next Obligation.
  split; apply compose_compat; easy.
Qed.
Next Obligation.
  split; apply assoc.
Qed.
Next Obligation.
  split; apply left_unit.
Qed.
Next Obligation.
  split; apply right_unit.
Qed.

Definition ProductCategoryFunctor_of_Bifunctor {C1 C2 D : Type} `{cC1 : Category C1} 
  `{cC2 : Category C2} `{cD : Category D} (F : Bifunctor cC1 cC2 cD) : 
  Functor (ProductCategory cC1 cC2) cD := {|
    obj_map := fun AB => F (fst AB) (snd AB);
    morphism_map := fun AB MN fABMN =>
      match fABMN with pair fAM fBN => F @@ fAM, fBN end;
    id_map := ltac:(intros [A1 A2]; apply id_bimap);
    compose_map := ltac:(intros [A1 A2] [B1 B2] [M1 M2]; simpl; 
      intros [fA1B1 fA2B2] [fB1M1 fB2M2]; simpl; apply compose_bimap);
    morphism_compat := ltac:(intros [A1 A2] [B1 B2]; simpl; 
      intros [fA1B1 fA2B2] [gA1B1 gA2B2]; simpl; intros [Hfg1 Hfg2]; 
      apply morphism_bicompat; assumption);
|}.

Definition Bifunctor_of_ProductCategoryFunctor {C1 C2 D : Type} `{cC1 : Category C1} 
  `{cC2 : Category C2} {cD : Category D} {cDh : CategoryCoherence cD} 
  (F : Functor (ProductCategory cC1 cC2) cD) : 
  Bifunctor cC1 cC2 cD := {|
    obj_bimap := fun A B => F (A, B);
    morphism_bimap := fun A1 B1 A2 B2 fA1B1 fA2B2 => 
      F @ ((fA1B1, fA2B2) : (A1, A2) ~> (B1, B2));
    id_bimap := fun A B => ltac:(simpl; rewrite <- id_map; reflexivity);
    compose_bimap := ltac:(intros; rewrite <- compose_map; reflexivity);
    morphism_bicompat := ltac:(intros; apply morphism_compat; constructor; easy);
|}.

End ProductCategories.

(* Some useful little lemmas *)
Lemma compose_cancel_r : forall {C} {cC : Category C} 
  {cCh : CategoryCoherence cC} {A B M : C} 
  (f g : A ~> B) (h : B ~> M), f ≃ g -> f ∘ h ≃ g ∘ h.
Proof.
  intros.
  apply compose_compat; easy.
Qed.

Lemma compose_cancel_l : forall {C} {cC:Category C} 
  {cCh : CategoryCoherence cC} {A B M : C} 
  (f : A ~> B) (g h : B ~> M), g ≃ h -> f ∘ g ≃ f ∘ h.
Proof.
  intros.
  apply compose_compat; easy.
Qed.

Lemma iso_inv_r : forall {C} {cC:Category C} 
  {cCh : CategoryCoherence cC} {A B : C} 
  (f : A <~> B), f ∘ f^-1 ≃ id_ A.
Proof. intros; apply isomorphism_inverse. Qed.

Lemma iso_inv_l : forall {C} {cC:Category C}
  {cCh : CategoryCoherence cC} {A B : C} 
  (f : A <~> B), f^-1 ∘ f ≃ id_ B.
Proof. intros; apply isomorphism_inverse. Qed.


Lemma equiv_of_iso_compose_l {C : Type} `{cC : Category C} 
  {cCh : CategoryCoherence cC} {A A' B : C}
  (I : Isomorphism A A') (f g : A' ~> B) (H : I ∘ f ≃ I ∘ g) :
  f ≃ g. 
Proof.
  rewrite <- (left_unit f), <- (left_unit g).
  rewrite <- (iso_inv_l I), 2!assoc, H.
  easy.
Qed.

Lemma equiv_of_iso_compose_r {C : Type} `{cC : Category C} 
  {cCh : CategoryCoherence cC} {A B' B : C}
  (I : Isomorphism B' B) (f g : A ~> B') (H : f ∘ I ≃ g ∘ I) :
  f ≃ g. 
Proof.
  rewrite <- (right_unit f), <- (right_unit g).
  rewrite <- (iso_inv_r I), <- 2!assoc, H.
  easy.
Qed.


Lemma compose_iso_r : forall {C} {cC:Category C} 
  {cCh : CategoryCoherence cC} {A B M : C} 
  (f : A ~> B) (g : B <~> M) (h : A ~> M), 
    f ∘ g ≃ h <-> f ≃ h ∘ g^-1.
Proof.
  intros; split; intro Heq.
  - rewrite <- Heq, (assoc), iso_inv_r, right_unit; easy.
  - rewrite Heq, (assoc), iso_inv_l, right_unit; easy.
Qed.

Lemma compose_iso_l : forall {C} {cC:Category C} 
  {cCh : CategoryCoherence cC} {A B M : C} 
  (f : A <~> B) (g : B ~> M) (h : A ~> M), 
    f ∘ g ≃ h <-> g ≃ f^-1 ∘ h.
Proof.
  intros; split; intro Heq.
  - rewrite <- Heq, <- (assoc), iso_inv_l, left_unit; easy.
  - rewrite Heq, <- (assoc), iso_inv_r, left_unit; easy.
Qed.

Lemma compose_iso_r' : forall {C} {cC:Category C}
  {cCh : CategoryCoherence cC} {A B M : C} 
  (f : A ~> B) (g : B <~> M) (h : A ~> M), 
    h ≃ f ∘ g <-> h ∘ g^-1 ≃ f.
Proof.
  intros; split; symmetry; apply compose_iso_r; easy.
Qed.

Lemma compose_iso_l' : forall {C} {cC:Category C} 
  {cCh : CategoryCoherence cC} {A B M : C} 
  (f : A <~> B) (g : B ~> M) (h : A ~> M), 
    h ≃ f ∘ g <-> f^-1 ∘ h ≃ g.
Proof.
  intros; split; symmetry; apply compose_iso_l; easy.
Qed.


#[program] Definition FunctorIsomorphism {C D} {cC : Category C} 
  {cCh : CategoryCoherence cC} {cD : Category D} {cDh : CategoryCoherence cD}
  {A B : C} (F : Functor cC cD) (f : A <~> B) : F A <~> F B := {|
  forward := F @ f;
  reverse := F @ (f ^-1);
|}.
Next Obligation.
  rewrite <- 2!compose_map, (proj1 isomorphism_inverse), 
    (proj2 isomorphism_inverse), 2!id_map; easy.
Qed.

#[program] Definition BifunctorIsomorphism {C1 C2 D} {cC1 : Category C1} 
  {cC1h : CategoryCoherence cC1} {cC2 : Category C2} 
  {cC2h : CategoryCoherence cC2} {cD : Category D} {cDh : CategoryCoherence cD}
  {A1 B1 : C1} {A2 B2 : C2} (F : Bifunctor cC1 cC2 cD) 
    (f1 : A1 <~> B1) (f2 : A2 <~> B2) : F A1 A2 <~> F B1 B2 := {|
  forward := F @@ f1, f2;
  reverse := F @@ f1^-1, f2^-1;
|}.
Next Obligation.
  rewrite <- 2!compose_bimap, 2!(proj1 isomorphism_inverse),
    2!(proj2 isomorphism_inverse), 2!id_bimap; easy.
Qed.

#[export] Instance IdentityIsomorphism {C} {cC : Category C} 
  {cCh : CategoryCoherence cC} (A : C) 
  : Isomorphism A A := {|
    forward := id_ A;
    reverse := id_ A;
    isomorphism_inverse := ltac:(rewrite left_unit; easy)
|}.

Lemma component_iso_natural_reverse : forall {C D} 
  {cC : Category C} {cCh : CategoryCoherence cC} 
  {cD : Category D} {cDh : CategoryCoherence cD}
  {F G : Functor cC cD} {N : NaturalIsomorphism F G} (A B : C) 
  (f : A ~> B),
  N A ^-1 ∘ F.(morphism_map) f ≃ G.(morphism_map) f ∘ N B ^-1.
Proof.
  intros.
  rewrite <- right_unit, <- (proj1 (N _).(isomorphism_inverse)).
  rewrite assoc, <- (assoc _ (N B)), component_iso_natural.
  rewrite <- 2!assoc.
  rewrite (proj2 isomorphism_inverse), left_unit.
  easy.
Qed.

Lemma component_biiso_natural_reverse : forall {C1 C2 D : Type} 
  {cC1 : Category C1} {cC1h : CategoryCoherence cC1} 
  {cC2 : Category C2} {cC2h : CategoryCoherence cC2} 
  {cD : Category D} {cDh : CategoryCoherence cD}
  {F G : Bifunctor cC1 cC2 cD} {N : NaturalBiIsomorphism F G} 
  (A1 B1 : C1) (A2 B2 : C2) (f1 : A1 ~> B1) (f2 : A2 ~> B2),
  (N A1 A2) ^-1 ∘ F.(morphism_bimap) f1 f2
  ≃ G.(morphism_bimap) f1 f2 ∘ N B1 B2 ^-1.
Proof.
  intros.
  rewrite <- right_unit, <- (proj1 (N _ _).(isomorphism_inverse)).
  rewrite assoc, <- (assoc _ (N _ _)), component_biiso_natural.
  rewrite <- 2!assoc.
  rewrite (proj2 isomorphism_inverse), left_unit.
  easy.
Qed.



Local Close Scope Cat.
