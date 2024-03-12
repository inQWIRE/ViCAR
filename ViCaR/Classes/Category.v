Require Import Setoid.

Declare Scope Cat_scope.
Delimit Scope Cat_scope with Cat.
Local Open Scope Cat.

#[local] Set Universe Polymorphism.

Reserved Notation "A ~> B" (at level 55).
Reserved Notation "f ≃ g" (at level 60).
Reserved Notation "A ≅ B" (at level 60).

Class Category (C : Type) : Type := {
    morphism : C -> C -> Type
        where "A ~> B" := (morphism A B);

    (* Morphism equivalence *)
    equiv {A B : C} : relation (A ~> B)
        where "f ≃ g" := (equiv f g) : Cat_scope;
    equiv_rel {A B : C} : equivalence (A ~> B) equiv;

    (* Object equivalence
    obj_equiv : relation C
        where "A ≅ B" := (obj_equiv A B) : Cat_scope;
    obj_equiv_rel : equivalence C obj_equiv; *)

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

(* Notations didn't work with:
Class Category (C : Type) (morphism : C -> C -> Type) 
  (equiv : forall {A B : C}, relation (morphism A B))
  (compose : forall {A B M : C}, morphism A B -> morphism B M -> morphism A M)
  (c_identity : forall (A : C), morphism A A)
  : Type := {
    
        (* where "A ~> B" := (morphism A B); *)

    (* Morphism equivalence *)
    
        (* where "f ≃ g" := (equiv f g) : Cat_scope; *)
    equiv_rel {A B : C} : equivalence (morphism A B) equiv
      where "A ~> B" := (morphism A B);
    

    (* Object equivalence
    obj_equiv : relation C
        where "A ≅ B" := (obj_equiv A B) : Cat_scope;
    obj_equiv_rel : equivalence C obj_equiv; *)

    compose_compat {A B M : C} : 
        forall (f g : A ~> B), equiv f g ->
        forall (h j : B ~> M), equiv h j ->
        equiv (compose f h) (compose g j)
        where "f ≃ g" := (equiv f g) : Cat_scope;
    assoc {A B M N : C}
        {f : A ~> B} {g : B ~> M} {h : M ~> N} : 
        compose (compose f g) h ≃ compose f (compose g h);

    left_unit {A B : C} {f : A ~> B} : compose (c_identity A) f ≃ f;
    right_unit {A B : C} {f : A ~> B} : compose f (c_identity B) ≃ f;
}.
*)

Notation "'id_' A" := (c_identity A) (at level 10, no associativity).
Notation "A ~> B" := (morphism A B) (at level 55, no associativity) : Cat_scope.
Notation "f ≃ g" := (equiv f g) : Cat_scope. (* \simeq *)
Infix "∘" := compose (at level 40, left associativity) : Cat_scope. (* \circ *)

Add Parametric Relation {C : Type} `{Cat : Category C} 
    (A B : C) : (A ~> B) equiv
  reflexivity proved by (equiv_refl (A ~> B) equiv equiv_rel)
  symmetry proved by (equiv_sym (A ~> B) equiv equiv_rel)
  transitivity proved by (equiv_trans (A ~> B) equiv equiv_rel)
  as prop_equiv_rel.

Add Parametric Morphism {C : Type} `{Cat : Category C} (n o m : C) : compose
  with signature (@equiv C Cat n m) ==> (@equiv C Cat m o) ==> equiv as compose_mor.
Proof. apply compose_compat; assumption. Qed.



Notation is_inverse f g :=
  (f ∘ g ≃ id_ _ /\ g ∘ f ≃ id_ _).

Lemma inverse_unique {C} `{Category C} {A B : C} 
  {f : A ~> B} {g g' : B ~> A} (Hg : is_inverse f g) (Hg' : is_inverse f g') :
  g ≃ g'.
Proof.
  rewrite <- (right_unit (f:=g)).
  rewrite <- (proj1 Hg'), <- assoc, (proj2 Hg), left_unit.
  easy.
Qed.

(** Isomorphism of objects in a category, and equivalent typeclass, with
    parametric equivalence *)
Definition isomorphism {C : Type} `{Category C} {A B : C} (f : A ~> B) :=
  exists (g : B ~> A), is_inverse f g.

Definition isomorphic {C : Type} `{Category C} (A B : C) :=
  exists (f : A ~> B), isomorphism f.

Class Isomorphism {C : Type} `{Category C} (A B : C) := {
  forward : A ~> B;
  reverse : B ~> A;
  isomorphism_inverse : is_inverse forward reverse;
}.
Notation id_A I := (proj1 I.(isomorphism_inverse)).
Notation id_B I := (proj2 I.(isomorphism_inverse)).
Coercion forward : Isomorphism >-> morphism.
Notation "f '^-1'" := (f.(reverse)) (at level 30) : Cat_scope.

Notation "A '<~>' B" := (Isomorphism A B) (at level 65) : Cat_scope.
Notation "A ≅ B" := (isomorphic A B) : Cat_scope. (* \cong *)

Lemma isomorphic_iff_Isomorphism {C : Type} `{Category C} (A B : C) :
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

Lemma isomorphic_refl {C : Type} `{Category C} (A : C) : isomorphic A A.
Proof.
  exists (c_identity A).
  exists (c_identity A).
  rewrite left_unit.
  split; reflexivity.
Qed.

Lemma isomorphic_trans {C : Type} `{Category C} (A B M : C) : 
  isomorphic A B -> isomorphic B M -> isomorphic A M.
Proof.
  intros [fAB [fBA [HfABA HfBAB]]] [fBM [fMB [HfBMB HfMBM]]].
  exists (fAB ∘ fBM).
  exists (fMB ∘ fBA).
  split;
  rewrite assoc.
  - rewrite <- (assoc (f:=fBM)), HfBMB, left_unit, HfABA.
    reflexivity.
  - rewrite <- (assoc (f:=fBA)), HfBAB, left_unit, HfMBM.
    reflexivity.
Qed.

Lemma isomorphic_sym {C : Type} `{Category C} (A B : C) : 
  isomorphic A B -> isomorphic B A.
Proof.
  intros [fAB [fBA [HfABA HfBAB]]].
  exists fBA; exists fAB.
  rewrite HfABA, HfBAB.
  split; reflexivity.
Qed.

Add Parametric Relation {C : Type} `{Cat : Category C} : C (@isomorphic C Cat)
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
Coercion obj_map : Functor >-> Funclass.
Notation "F @ X" := (F.(morphism_map) X) (at level 39, no associativity).

Add Parametric Morphism {C D : Type} {cC : Category C} {cD : Category D}
  (F : Functor cC cD) (A B : C): F.(morphism_map)
  with signature (@equiv C cC A B) ==> (@equiv D cD (F A) (F B)) as functor_equiv_mor.
Proof. apply morphism_compat. Qed.

Add Parametric Morphism {C D : Type} `{cC : Category C} `{cD : Category D}
  (F : Functor cC cD) : F.(obj_map)
  with signature (@isomorphic C cC) ==> (@isomorphic D cD) as functor_isomorphic_mor.
Proof. 
  intros A B [fAB [fBA [HfABA HfBAB]]].
  exists (F @ fAB); exists (F @ fBA).
  rewrite <- 2!compose_map, HfABA, HfBAB.
  split; apply id_map.
Qed.

(* TODO: replace "2_map" with "bimap" *)
Reserved Notation " F '@@' X , Y " (at level 39, no associativity).
Class Bifunctor {C1 C2 D : Type} (cC1: Category C1) (cC2 : Category C2) (cD : Category D) := {
  obj2_map : C1 -> C2 -> D;
  morphism2_map {A1 B1 : C1} {A2 B2 : C2} : (A1 ~> B1) -> (A2 ~> B2) ->
    (obj2_map A1 A2) ~> (obj2_map B1 B2);
  id2_map {A1 : C1} {A2 : C2} :
    (morphism2_map (id_ A1) (id_ A2)) ≃ id_ (obj2_map A1 A2);
  compose2_map {A1 B1 M1 : C1} {A2 B2 M2 : C2}
    (f1 : A1 ~> B1) (g1 : B1 ~> M1) (f2 : A2 ~> B2) (g2 : B2 ~> M2) :
    morphism2_map (f1 ∘ g1) (f2 ∘ g2) ≃ morphism2_map f1 f2 ∘ morphism2_map g1 g2;
  morphism2_compat {A1 B1 : C1} {A2 B2 : C2} (f f' : A1 ~> B1) (g g' : A2 ~> B2) :
    f ≃ f' -> g ≃ g' -> morphism2_map f g ≃ morphism2_map f' g'
}.
Coercion obj2_map : Bifunctor >-> Funclass.
Notation " F '@@' X , Y " := (F.(morphism2_map) X Y) (at level 39, no associativity).

Add Parametric Morphism {C1 C2 D : Type} 
  {cC1 : Category C1} {cC2 : Category C2} {cD : Category D}
  (F : Bifunctor cC1 cC2 cD) (A1 B1 : C1) (A2 B2 : C2) : F.(morphism2_map)
  with signature (@equiv C1 cC1 A1 B1) ==> (@equiv C2 cC2 A2 B2) 
    ==> (@equiv D cD (F A1 A2) (F B1 B2)) as bifunctor_equiv_mor.
Proof. intros. apply morphism2_compat; easy. Qed.

Add Parametric Morphism {C1 C2 D : Type} `{cC1 : Category C1} `{cC2 : Category C2}
 `{cD : Category D} (F : Bifunctor cC1 cC2 cD) : F.(obj2_map)
  with signature (@isomorphic C1 cC1) ==> (@isomorphic C2 cC2) 
    ==> (@isomorphic D cD) as bifunctor_isometric_mor.
Proof. 
  intros A1 B1 [fAB1 [fBA1 [HfABA1 HfBAB1]]] A2 B2 [fAB2 [fBA2 [HfABA2 HfBAB2]]].
  exists (F @@ fAB1, fAB2); exists (F @@ fBA1, fBA2).
  rewrite <- 2!compose2_map, HfABA1, HfBAB1, HfABA2, HfBAB2.
  split; apply id2_map.
Qed.

Definition CommuteBifunctor {C1 C2 D : Type} `{cC1 : Category C1} 
  `{cC2 : Category C2} `{cD : Category D} (F : Bifunctor cC1 cC2 cD) 
  : Bifunctor cC2 cC1 cD := {|
  obj2_map := fun A B => F B A;
  morphism2_map := fun A1 A2 B1 B2 fAB1 fAB2 => F @@ fAB2, fAB1;
  id2_map := ltac:(intros; apply id2_map);
  compose2_map := ltac:(intros; apply compose2_map);
  morphism2_compat := ltac:(intros; apply morphism2_compat; easy);
|}.



(** Natural Transformations & Isomorphisms (and the equivalents for Bifunctors) *)
Reserved Notation "'α_' X" (at level 20). (* \alpha *)
Class NaturalTransformation {C D : Type} `{cC: Category C} `{cD : Category D}
  (F G : Functor cC cD) := {
  component_map (A : C) : F A ~> G A
    where "'α_' X" := (component_map X);
  component_map_natural (A B : C) (f : A ~> B) :
    F@f ∘ α_ B ≃ α_ A ∘ G@f;
}.
Notation "'α_' X" := (component_map X) (at level 20).

Class NaturalIsomorphism {C D : Type} `{cC: Category C} `{cD : Category D}
  (F G : Functor cC cD) := {
  component_iso (A : C) : F A <~> G A;
  component_iso_natural (A B : C) (f : A ~> B) :
    F@f ∘ component_iso B ≃ component_iso A ∘ G@f;
}.
Coercion component_iso : NaturalIsomorphism >-> Funclass. (* TODO: is this sensible? I think not *)

Definition NaturalTransformation_of_NaturalIsomorphism {C D : Type} 
  `{cC : Category C} `{cD : Category D} {F G : Functor cC cD}
  (NI : NaturalIsomorphism F G) : NaturalTransformation F G := {|
  component_map := component_iso;
  component_map_natural := ltac:(intros; apply component_iso_natural);
|}.
Coercion NaturalTransformation_of_NaturalIsomorphism : 
  NaturalIsomorphism >-> NaturalTransformation.


Reserved Notation "'β_' X , Y" (at level 20). (* \beta *)
Class NaturalBiTransformation {C1 C2 D : Type} `{cC1 : Category C1} 
  `{cC2 : Category C2} `{cD : Category D} (F G : Bifunctor cC1 cC2 cD) := {
  component2_map (A1 : C1) (A2 : C2) : F A1 A2 ~> G A1 A2
    where "'β_' X , Y" := (component2_map X Y);
  component2_map_natural (A1 B1 : C1) (A2 B2 : C2) (f1 : A1 ~> B1) (f2 : A2 ~> B2) :
    (F @@ f1, f2) ∘ (β_ B1,B2) ≃ (β_ A1,A2) ∘ (G @@ f1, f2)
}.
Notation "'β_' X , Y" := (component2_map X Y) (at level 20).

Class NaturalBiIsomorphism {C1 C2 D : Type} `{cC1 : Category C1} 
  `{cC2 : Category C2} `{cD : Category D} (F G : Bifunctor cC1 cC2 cD) := {
  component2_iso (A1 : C1) (A2 : C2) : F A1 A2 <~> G A1 A2;
  component2_iso_natural (A1 B1 : C1) (A2 B2 : C2) (f1 : A1 ~> B1) (f2 : A2 ~> B2) :
    (F @@ f1, f2) ∘ (component2_iso B1 B2) ≃ (component2_iso A1 A2) ∘ (G @@ f1, f2)
}.
Coercion component2_iso : NaturalBiIsomorphism >-> Funclass.

Definition NaturalBiTransformation_of_NaturalBiIsomorphism {C1 C2 D : Type} 
  `{cC1 : Category C1} `{cC2 : Category C2} `{cD : Category D} {F G : Bifunctor cC1 cC2 cD}
  (NI: NaturalBiIsomorphism F G) : NaturalBiTransformation F G := {|
  component2_map := component2_iso;
  component2_map_natural := ltac:(intros; apply component2_iso_natural);
|}.

Coercion NaturalBiTransformation_of_NaturalBiIsomorphism : 
  NaturalBiIsomorphism >-> NaturalBiTransformation.


(** The opposite category, contravariant functor (currently unused) *)
(* This should in fact be a definition, not an instance, as we definititely
   don't want typeclass resolution trying to use it. *)
Definition OppositeCategory {C : Type} (cC : Category C) : Category C := {|
  morphism := fun A B => morphism B A; 
  equiv := fun A B => @equiv C cC B A;
  equiv_rel := fun A B => @equiv_rel C cC B A;
  compose := fun A B M fAB fBM => fBM ∘ fAB;
  compose_compat := fun A B M f g Hfg h j Hhj => @compose_compat C cC M B A _ _ Hhj _ _ Hfg;
  assoc := fun A B M N f g h => equiv_sym _ _ equiv_rel _ _ (@assoc C cC N M B A h g f);
  c_identity := c_identity;
  left_unit := fun A B => @right_unit C cC B A;
  right_unit := fun A B => @left_unit C cC B A;
|}.

Notation "C '^op'" := (OppositeCategory C) (at level 40, left associativity).

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
Coercion obj_contramap : ContraFunctor >-> Funclass.
Notation "F @' X" := (F.(morphism_contramap) X) (at level 39, no associativity).

Add Parametric Morphism {C D : Type} {cC : Category C} {cD : Category D}
  (F : ContraFunctor cC cD) (A B : C): F.(morphism_contramap)
  with signature 
  (@equiv C cC A B) ==> (@equiv D cD (F B) (F A)) as contrafunctor_equiv_mor.
Proof. apply morphism_contracompat. Qed.

Add Parametric Morphism {C D : Type} `{cC : Category C} `{cD : Category D}
  (F : ContraFunctor cC cD) : F.(obj_contramap)
  with signature 
  (@isomorphic C cC) ==> (@isomorphic D cD) as contrafunctor_isomorphic_mor.
Proof. 
  intros A B [fAB [fBA [HfABA HfBAB]]].
  exists (F @' fBA); exists (F @' fAB).
  rewrite <- 2!compose_contramap, HfABA, HfBAB.
  split; apply id_contramap.
Qed.

Definition ContravariantFunctor {C D : Type} (cC: Category C) (cD : Category D) : Type :=
  Functor (cC^op) cD.

Definition ContravariantFunctor_of_ContraFunctor {C D : Type} 
  `{cC : Category C} `{cD : Category D} (F : ContraFunctor cC cD) : 
  ContravariantFunctor cC cD := {|
  obj_map := F.(obj_contramap);
  morphism_map := fun (A B : C) (f : @morphism C (cC^op) A B) =>
    F.(morphism_contramap) f;
  id_map := id_contramap;
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
  id_contramap := id_map;
  compose_contramap := fun A B M f g => F.(compose_map) g f;
  morphism_contracompat := fun A B f g => F.(morphism_compat) f g;
|}.


(** Product categories, equivalence of functors from them and bifunctors (currently unused) *)
Notation product_relation simT simU := (fun AB CD =>
  simT (fst AB) (fst CD) /\ simU (snd AB) (snd CD)).

Definition product_relation_refl {T U : Type} {simT : relation T} {simU : relation U}
  (reflT : reflexive T simT) (reflU : reflexive U simU) : reflexive (T*U) (product_relation simT simU) :=
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

Local Instance ProductCategory {C D : Type} (cC : Category C) (cD : Category D) : Category (C*D) := {|
  morphism := fun AB MN =>
    prod (morphism (fst AB) (fst MN)) (morphism (snd AB) (snd MN));
  equiv :=
    fun AB A'B' => 
    match AB with (A, B) =>
    match A'B' with (A', B') => 
      product_relation (@equiv C cC A A') (@equiv D cD B B')
    end end;
  equiv_rel := fun AB A'B' => 
    match AB with (A, B) =>
    match A'B' with (A', B') =>
      product_relation_equivalence (@equiv_rel C cC A A') (@equiv_rel D cD B B')
    end end;
  compose := fun AB MN EF =>
    match AB with (A, B) =>
    match MN with (M, N) =>
    match EF with (E, F) => fun sABMN sMNEF =>
    match sABMN with pair sAM sBN =>
    match sMNEF with pair sME sNF =>
      (sAM ∘ sME, sBN ∘ sNF)
    end end end end end;
  compose_compat := ltac:(intros [A B] [M N] [E F]; simpl;
    intros f f'; destruct f as [fAM fBN]; destruct f' as [f'AM f'BN]; simpl;
    intros [hff'AM hff'BN];
    intros [gAM gBN] [g'AM g'BN]; simpl;
    intros [hgg'AM hgg'BN];
    split; apply compose_compat; easy);
  assoc := ltac:(intros [A B] [A' B'] [M N] [M' N']; simpl;
    intros [fAA' fBB'] [gA'M gB'N] [hMM' hNN']; simpl;
    split; apply assoc);
  c_identity := fun AB => match AB with (A, B) => (c_identity A, c_identity B) end;
  left_unit := ltac:(intros [A B] [M N]; simpl; intros [fAA' fBB']; simpl; split; apply left_unit);
  right_unit := ltac:(intros [A B] [M N]; simpl; intros [fAA' fBB']; simpl; split; apply right_unit);
|}.

Definition ProductCategoryFunctor_of_Bifunctor {C1 C2 D : Type} `{cC1 : Category C1} 
  `{cC2 : Category C2} `{cD : Category D} (F : Bifunctor cC1 cC2 cD) : 
  Functor (ProductCategory cC1 cC2) cD := {|
    obj_map := fun AB => F (fst AB) (snd AB);
    morphism_map := fun AB MN fABMN =>
      match fABMN with pair fAM fBN => F @@ fAM, fBN end;
    id_map := ltac:(intros [A1 A2]; apply id2_map);
    compose_map := ltac:(intros [A1 A2] [B1 B2] [M1 M2]; simpl; 
      intros [fA1B1 fA2B2] [fB1M1 fB2M2]; simpl; apply compose2_map);
    morphism_compat := ltac:(intros [A1 A2] [B1 B2]; simpl; 
      intros [fA1B1 fA2B2] [gA1B1 gA2B2]; simpl; intros [Hfg1 Hfg2]; 
      apply morphism2_compat; assumption);
|}.

Definition Bifunctor_of_ProductCategoryFunctor {C1 C2 D : Type} `{cC1 : Category C1} 
  `{cC2 : Category C2} `{cD : Category D} (F : Functor (ProductCategory cC1 cC2) cD) : 
  Bifunctor cC1 cC2 cD := {|
    obj2_map := fun A B => F (A, B);
    morphism2_map := fun A1 B1 A2 B2 fA1B1 fA2B2 => 
      F @ ((fA1B1, fA2B2) : (A1, A2) ~> (B1, B2));
    id2_map := fun A B => ltac:(simpl; rewrite <- id_map; reflexivity);
    compose2_map := ltac:(intros; rewrite <- compose_map; reflexivity);
    morphism2_compat := ltac:(intros; apply morphism_compat; constructor; easy);
|}.

Lemma equiv_of_iso_compose_l {C : Type} `{cC : Category C} {A A' B : C}
  (I : Isomorphism A A') (f g : A' ~> B) (H : I ∘ f ≃ I ∘ g) :
  f ≃ g. 
Proof.
  rewrite <- (left_unit (f:=f)), <- (left_unit (f:=g)).
  rewrite <- (id_B I), 2!assoc, H.
  easy.
Qed.

Lemma equiv_of_iso_compose_r {C : Type} `{cC : Category C} {A B' B : C}
  (I : Isomorphism B' B) (f g : A ~> B') (H : f ∘ I ≃ g ∘ I) :
  f ≃ g. 
Proof.
  rewrite <- (right_unit (f:=f)), <- (right_unit (f:=g)).
  rewrite <- (id_A I), <- 2!assoc, H.
  easy.
Qed.



Local Close Scope Cat.
