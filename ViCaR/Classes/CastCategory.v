Require Import Setoid.

Require Export CategoryTypeclass.
Require Logic.Eqdep_dec. (* only for UIP_dec *)
Require PeanoNat. (* only for eq_dep on nat *)

#[local] Set Universe Polymorphism.

Local Open Scope Cat.

Class CastCategory (C : Type) {cC : Category C} : Type := {
  cast {A B A' B' : C} (HA : A = A') (HB : B = B') :
    A' ~> B' -> A ~> B;
  (* After experimentation, this is actually all we need: *)
  cast_refl {A B : C} (HA : A = A) (HB : B = B) f : 
    cast HA HB f ≃ f;
  (* That's tenable! *)

  (* Old, for reference:
      (* Will need some coherence conditions, probably 
      cast_id, cast_compose? Might be it. Oh, we may want 
      cast HA HB (cast (eq_sym HA) (eq_sym HB) f) ≃ f as 
      well, just giving bijectivity. All should be trivial
      for any sensible cast. This seems sufficient on no 
      reflection, so let's see how far it can go: *)
    cast_invertible {A B A' B' : C} 
    (HA : A' = A) (HB : B' = B) (HA' : A = A') (HB' : B = B') f : 
      cast HA' HB' (cast HA HB f) ≃ f;
    (* On more reflection, this allows any involution to
      go along with the cast (e.g. cast is cast of a matrix
      but also scales by -1). So, we do need: *)
    
      (* In theory, we could specialize this to just 
        @eq_refl C A and @eq_refl C B, but I think 
        this might be better. Maybe not, though, as
        it *purely conjuecturally* *seems* like this
        property with equality correlates with decidable
        equality, which we _might_ not want to require? *)
    (* I think we need this, too: *)
    (* cast_compose {A A' B M M' : C} (HA : A = A') (HM : M = M')
      (f : A' ~> B) (g: B ~> M') : 
      cast HA HM (f ∘ g) ≃ cast HA eq_refl f ∘ cast eq_refl HM g; *)
  *)
}.

Notation "'cast' A B f" := (@cast _ _ _ A B _ _ _ _ f) 
  (at level 0, A at next level, B at next level, only printing).

Add Parametric Morphism {C : Type} `{cC : Category C, castC : !CastCategory C}
  {A B : C} {A' B' : C}
  {prfA : A = A'} {prfB : B = B'} : (@cast C cC castC A B A' B' prfA prfB)
  with signature
  (@Category.equiv C cC A' B') ==> (@Category.equiv C cC A B) as cast_equiv_morphism.
Proof.
  intros. 
  subst.
  rewrite 2!cast_refl.
  easy.
Qed.

Lemma cast_id {C} `{castC : CastCategory C}
  (A A' : C) (HA1 HA2 : A = A') :
  cast HA1 HA2 (id_ A') ≃ id_ A.
Proof.
  subst.
  apply cast_refl.
Qed.

Lemma cast_compose_gen {C} `{castC : CastCategory C}
  {A A' B M M' : C} (HA : A = A') (HM : M = M')
    (HB1 HB2 : B = B)
    (f : A' ~> B) (g: B ~> M') : 
    cast HA HM (f ∘ g) ≃ cast HA HB1 f ∘ cast HB2 HM g.
Proof.
  subst.
  rewrite ?cast_refl.
  easy.
Qed.

Lemma cast_compose {C} `{castC : CastCategory C}
  {A A' B M M' : C} (HA : A = A') (HM : M = M')
    (f : A' ~> B) (g: B ~> M') : 
    cast HA HM (f ∘ g) ≃ cast HA eq_refl f ∘ cast eq_refl HM g.
Proof.
  apply cast_compose_gen.
Qed.

Lemma cast_invertible {C} `{castC : CastCategory C}
  {A B A' B' : C} 
  (HA : A' = A) (HB : B' = B) (HA' : A = A') (HB' : B = B') f : 
  cast HA' HB' (cast HA HB f) ≃ f.
Proof.
  subst.
  rewrite ?cast_refl.
  easy.
Qed.
  
Lemma cast_cast_gen {C} `{castC : CastCategory C} 
  {A B A' B' A'' B''} (HA : A = A') (HB : B = B') 
  (HA' : A' = A'') (HB' : B' = B'') (HA'' : A = A'') (HB'' : B = B'')
  : forall f,
  cast HA HB (cast HA' HB' f) ≃ cast HA'' HB'' f.
Proof.
  intros.
  subst.
  rewrite 3!cast_refl.
  easy.
Qed.

Lemma cast_cast {C} `{castC : CastCategory C} 
  {A B A' B' A'' B''} (HA : A = A') (HB : B = B') 
  (HA' : A' = A'') (HB' : B' = B'') : forall f,
  cast HA HB (cast HA' HB' f) ≃ cast (eq_trans HA HA') (eq_trans HB HB') f.
Proof.
  apply cast_cast_gen.
Qed.

Lemma cast_irrelevance {C} `{castC : CastCategory C} 
  {A B A' B'} (HA1 HA2 : A = A') (HB1 HB2 : B = B') : forall f,
  cast HA1 HB1 f ≃ cast HA2 HB2 f.
Proof.
  intros.
  subst.
  rewrite 2!cast_refl.
  easy.
Qed.

Lemma cast_simplify {C} `{castC : CastCategory C} 
  {A B A' B'} (HA1 HA2 : A = A') (HB1 HB2 : B = B') : forall f g,
  f ≃ g -> cast HA1 HB1 f ≃ cast HA2 HB2 g.
Proof.
  intros f g Hfg.
  rewrite Hfg.
  apply cast_irrelevance.
Qed.

Lemma cast_compatability {C} `{castC : CastCategory C} 
  {A B A' B'} (HA1 HA2 : A = A') (HB1 HB2 : B = B') : forall f g,
  cast HA1 HB1 f ≃ cast HA2 HB2 g -> f ≃ g.
Proof.
  intros.
  subst.
  rewrite 2!cast_refl in *.
  easy.
Qed.

Lemma cast_equiv_iff {C} `{castC : CastCategory C} 
  {A B A' B'} (HA1 HA2 : A = A') (HB1 HB2 : B = B') : forall f g,
  cast HA1 HB1 f ≃ cast HA2 HB2 g <-> f ≃ g.
Proof.
  intros.
  split.
  - apply cast_compatability.
  - apply cast_simplify. 
Qed.

Lemma cast_symmetry {C} `{castC : CastCategory C} 
  {A B A' B'} (HA : A = A') (HB : B = B') 
  (HA' : A' = A) (HB' : B' = B) : forall f g,
  cast HA HB f ≃ g <-> f ≃ cast HA' HB' g.
Proof.
  intros.
  subst.
  rewrite 2!cast_refl.
  easy.
Qed.

Lemma cast_symmetry_swap {C} `{castC : CastCategory C} 
  {A B A' B'} (HA : A = A') (HB : B = B') 
  (HA' : A' = A) (HB' : B' = B) : forall f g,
  cast HA HB f ≃ g <-> cast HA' HB' g ≃ f.
Proof.
  intros.
  rewrite cast_symmetry.
  split; intros H; symmetry; apply H.
Qed.

Lemma compose_cast_mid_gen {C} `{castC : CastCategory C} 
  {A M M' B : C} (HM1 HM2 : M = M') (HA : A = A) (HB : B = B) : 
  forall (f : A ~> M') (g : M' ~> B), 
  f ∘ g ≃ cast HA HM1 f ∘ cast HM2 HB g.
Proof.
  intros.
  subst.
  rewrite 2!cast_refl.
  easy.
Qed.

Lemma compose_cast_mid {C} `{castC : CastCategory C} 
  {A M M' B : C} (HM : M = M'): 
  forall (f : A ~> M') (g : M' ~> B), 
  f ∘ g ≃ cast eq_refl HM f ∘ cast HM eq_refl g.
Proof.
  apply compose_cast_mid_gen.
Qed.

Lemma cast_compose_distribute_gen {C} `{castC : CastCategory C} 
  (A A' M M' B B' : C) 
  (HA1 HA2 : A = A') (HB1 HB2 : B = B') (HM1 HM2 : M = M') :
  forall (f : A' ~> M') (g : M' ~> B'),
  cast HA1 HB1 (f ∘ g) ≃ cast HA2 HM1 f ∘ cast HM2 HB2 g.
Proof.
  intros.
  subst.
  rewrite 3!cast_refl.
  easy.
Qed.

Lemma cast_compose_distribute {C} `{castC : CastCategory C} 
  (A A' M M' B B' : C) (HA : A = A') (HB : B = B') (HM : M = M') :
  forall (f : A' ~> M') (g : M' ~> B'),
  cast HA HB (f ∘ g) ≃ cast HA HM f ∘ cast HM HB g.
Proof.
  apply cast_compose_distribute_gen.
Qed.

Lemma cast_compose_split_gen {C} `{castC : CastCategory C} 
  (A A' M B B' : C) 
  (HA1 HA2 : A = A') (HB1 HB2 : B = B') (HM1 HM2 : M = M) :
  forall (f : A' ~> M) (g : M ~> B'),
  cast HA1 HB1 (f ∘ g) ≃ cast HA2 HM1 f ∘ cast HM2 HB2 g.
Proof.
  apply cast_compose_distribute_gen.
Qed.

Lemma cast_compose_split {C} `{castC : CastCategory C} 
  (A A' M B B' : C) (HA : A = A') (HB : B = B') :
  forall (f : A' ~> M) (g : M ~> B'),
  cast HA HB (f ∘ g) ≃ cast HA eq_refl f ∘ cast eq_refl HB g.
Proof.
  apply cast_compose_split_gen.
Qed.


Lemma cast_compose_l_gen {C} `{castC : CastCategory C} 
  (A A' M M' B : C) (HA1 HA2 : A = A') (HM : M = M') 
  (HM' : M' = M) (HB1 HB2 : B = B) :
  forall (f : A' ~> M') (g : M ~> B),
  cast HA1 HM f ∘ g ≃ cast HA2 HB1 (f ∘ cast HM' HB2 g).
Proof.
  intros.
  subst.
  rewrite 3!cast_refl.
  easy.
Qed.

Lemma cast_compose_l {C} `{castC : CastCategory C} 
  (A A' M M' B : C) (HA : A = A') (HM : M = M') :
  forall (f : A' ~> M') (g : M ~> B),
  cast HA HM f ∘ g ≃ cast HA eq_refl (f ∘ cast (eq_sym HM) eq_refl g).
Proof.
  apply cast_compose_l_gen.
Qed.

Lemma cast_compose_r_gen {C} `{castC : CastCategory C} 
  (A M M' B B' : C) (HA1 HA2 : A = A) (HM : M = M') 
  (HM' : M' = M) (HB1 HB2 : B = B') :
  forall (f : A ~> M) (g : M' ~> B'),
  f ∘ cast HM HB1 g ≃ cast HA1 HB2 (cast HA2 HM' f ∘ g).
Proof.
  intros.
  subst.
  rewrite 3!cast_refl.
  easy.
Qed.

Lemma cast_compose_r {C} `{castC : CastCategory C} 
  (A M M' B B' : C) (HM : M = M') (HB : B = B') :
  forall (f : A ~> M) (g : M' ~> B'),
  f ∘ cast HM HB g ≃ cast eq_refl HB (cast eq_refl (eq_sym HM) f ∘ g).
Proof.
  apply cast_compose_r_gen.
Qed.

Lemma cast_contract_l_gen {C} `{castC : CastCategory C} 
  {A A' A'' B B' B'' : C} (HA1 : A = A') (HA2 : A = A'')
  (HB1 : B = B') (HB2 : B = B'') (HA3 : A'' = A') (HB3 : B'' = B'):
  forall (f : A' ~> B') (g : A'' ~> B''),
  cast HA1 HB1 f ≃ cast HA2 HB2 g <-> cast HA3 HB3 f ≃ g.
Proof.
  intros.
  subst.
  rewrite 3!cast_refl.
  easy.
Qed.

Lemma cast_contract_l {C} `{castC : CastCategory C} 
  {A A' A'' B B' B'' : C} (HA1 : A = A') (HA2 : A = A'')
  (HB1 : B = B') (HB2 : B = B'') :
  forall (f : A' ~> B') (g : A'' ~> B''),
  cast HA1 HB1 f ≃ cast HA2 HB2 g <-> 
  cast (eq_trans (eq_sym HA2) HA1) (eq_trans (eq_sym HB2) HB1) f ≃ g.
Proof.
  apply cast_contract_l_gen.
Qed.

Lemma cast_contract_r_gen {C} `{castC : CastCategory C} 
  {A A' A'' B B' B'' : C} (HA1 : A = A') (HA2 : A = A'')
  (HB1 : B = B') (HB2 : B = B'') (HA3 : A' = A'') (HB3 : B' = B''):
  forall (f : A' ~> B') (g : A'' ~> B''),
  cast HA1 HB1 f ≃ cast HA2 HB2 g <-> f ≃ cast HA3 HB3 g.
Proof.
  intros.
  subst.
  rewrite 3!cast_refl.
  easy.
Qed.

Lemma cast_contract_r {C} `{castC : CastCategory C} 
  {A A' A'' B B' B'' : C} (HA1 : A = A') (HA2 : A = A'')
  (HB1 : B = B') (HB2 : B = B'') :
  forall (f : A' ~> B') (g : A'' ~> B''),
  cast HA1 HB1 f ≃ cast HA2 HB2 g <-> 
  f ≃ cast (eq_trans (eq_sym HA1) HA2) (eq_trans (eq_sym HB1) HB2) g.
Proof.
  apply cast_contract_r_gen.
Qed.





Lemma cast_function {C} `{castC : CastCategory C} 
  {A B A' B'} (HA : A = A') (HB : B = B') (f : forall a b, a ~> b) :
  cast HA HB (f A' B') ≃ f A B.
Proof.
  subst.
  rewrite cast_refl.
  easy.
Qed.

Lemma cast_function_diag {C} `{castC : CastCategory C} 
  {A A'} (HA1 HA2 : A = A') (f : forall a, a ~> a) :
  cast HA1 HA2 (f A') ≃ f A.
Proof.
  subst.
  rewrite cast_refl.
  easy.
Qed.

Lemma cast_functor_gen {C D} `{cC : Category C} `{castC : @CastCategory C cC} 
  `{cD : Category D} `{castD : @CastCategory D cD} 
  {A B A' B'} (F : Functor cC cD) (HA : A = A') (HB : B = B')
  (HFA : F A = F A') (HFB : F B = F B') : 
  forall f,
  cast HFA HFB (F @ f) ≃ F @ (cast HA HB f).
Proof.
  intros f.
  subst.
  rewrite 2!cast_refl.
  easy.
Qed.

Definition __cast_functor_proof {C D} {A A'} (F : C -> D) (HA : A = A') :
  F A = F A' := ltac:(subst; easy).

Lemma functor_cast {C D} `{cC : Category C} `{castC : @CastCategory C cC} 
  `{cD : Category D} `{castD : @CastCategory D cD} 
  {A B A' B'} (F : Functor cC cD) (HA : A = A') (HB : B = B') : 
  forall f, F @ (cast HA HB f) ≃
  cast (__cast_functor_proof F HA) (__cast_functor_proof F HB) (F @ f).
Proof.
  symmetry. 
  apply cast_functor_gen.
Qed.

Lemma cast_contravariant_functor_gen {C D} 
  `{cC : Category C} `{castC : @CastCategory C cC} 
  `{cD : Category D} `{castD : @CastCategory D cD} 
  {A B A' B'} (F : ContravariantFunctor cC cD) (HA : A = A') (HB : B = B')
  (HFA : F A = F A') (HFB : F B = F B') : 
  forall f,
  cast HFB HFA (F @ f) ≃ F @ (cast HA HB f).
Proof.
  intros f.
  subst.
  rewrite 2!cast_refl.
  easy.
Qed.

Lemma contravariant_functor_cast {C D} 
  `{cC : Category C} `{castC : @CastCategory C cC} 
  `{cD : Category D} `{castD : @CastCategory D cD} 
  {A B A' B'} (F : ContravariantFunctor cC cD) (HA : A = A') (HB : B = B') : 
  forall (f : cC.(morphism) A' B'), F @ (cast HA HB f) ≃
  cast (__cast_functor_proof F HB) (__cast_functor_proof F HA) (F @ f).
Proof.
  symmetry.
  apply cast_contravariant_functor_gen.
Qed.

Lemma cast_endofunctor_gen {C} `{cC : Category C} `{castC : @CastCategory C cC} 
  {A B A' B'} (F : Functor cC cC) (HA : A = A') (HB : B = B')
  (HFA : F A = F A') (HFB : F B = F B') : 
  forall f,
  cast HFA HFB (F @ f) ≃ F @ (cast HA HB f).
Proof.
  apply cast_functor_gen.
Qed.

Lemma endofunctor_cast {C} `{cC : Category C} `{castC : @CastCategory C cC} 
  {A B A' B'} (F : Functor cC cC) (HA : A = A') (HB : B = B') : 
  forall f, F @ (cast HA HB f) ≃
  cast (__cast_functor_proof F HA) (__cast_functor_proof F HB) (F @ f).
Proof.
  symmetry.
  apply cast_endofunctor_gen.
Qed.

Lemma cast_contravariant_endofunctor_gen 
  {C} `{cC : Category C} `{castC : @CastCategory C cC} 
  {A B A' B'} (F : ContravariantFunctor cC cC) (HA : A = A') (HB : B = B')
  (HFA : F A = F A') (HFB : F B = F B') : 
  forall (f : cC.(morphism) A' B'),
  cast HFB HFA (F @ f) ≃ F @ (cast HA HB f).
Proof.
  intros.
  apply cast_contravariant_functor_gen.
Qed.

Lemma contravariant_endofunctor_cast 
  {C} `{cC : Category C} `{castC : @CastCategory C cC} 
  {A B A' B'} (F : ContravariantFunctor cC cC) (HA : A = A') (HB : B = B')
  (HFA : F A = F A') (HFB : F B = F B') : 
  forall (f : cC.(morphism) A' B'), 
  F @ (cast HA HB f) ≃
  cast (__cast_functor_proof F HB) (__cast_functor_proof F HA) (F @ f).
Proof.
  symmetry.
  apply cast_contravariant_endofunctor_gen.
Qed.


Lemma cast_bifunctor_gen {C1 C2 D} 
  `{cC1 : Category C1} `{castC1 : @CastCategory C1 cC1} 
  `{cC2 : Category C2} `{castC2 : @CastCategory C2 cC2} 
  `{cD : Category D} `{castD : @CastCategory D cD} 
  {A A' B B' : C1} {M M' N N' : C2} (F : Bifunctor cC1 cC2 cD) 
  (HA : A = A') (HB : B = B') (HM : M = M') (HN : N = N')
  (HFAM : F A M = F A' M') (HFBN : F B N = F B' N') : 
  forall f g,
  cast HFAM HFBN (F @@ f, g) ≃ F @@ (cast HA HB f), (cast HM HN g).
Proof.
  intros f g.
  subst.
  rewrite 3!cast_refl.
  easy.
Qed.

Definition __cast_bifunctor_proof {C1 C2 D} {A A'} {B B'} (F : C1 -> C2 -> D) 
  (HA : A = A') (HB : B = B') :
  F A B = F A' B' := ltac:(subst; easy).

Lemma cast_bifunctor {C1 C2 D} 
  `{cC1 : Category C1} `{castC1 : @CastCategory C1 cC1} 
  `{cC2 : Category C2} `{castC2 : @CastCategory C2 cC2} 
  `{cD : Category D} `{castD : @CastCategory D cD} 
  {A A' B B' : C1} {M M' N N' : C2} (F : Bifunctor cC1 cC2 cD) 
  (HA : A = A') (HB : B = B') (HM : M = M') (HN : N = N')
  (HFAM : F A M = F A' M') (HFBN : F B N = F B' N') : 
  forall f g,
  F @@ (cast HA HB f), (cast HM HN g) ≃
  cast (__cast_bifunctor_proof F HA HM) (__cast_bifunctor_proof F HB HN) (F @@ f, g).
Proof.
  symmetry.
  apply cast_bifunctor_gen.
Qed.

(* Lemma cast_bifunctor_gen {C1 C2 D} 
  `{cC1 : Category C1} `{castC1 : @CastCategory C1 cC1} 
  `{cC2 : Category C2} `{castC2 : @CastCategory C2 cC2} 
  `{cD : Category D} `{castD : @CastCategory D cD} 
  {A A' B B' : C1} {M M' N N' : C2} (F : Bifunctor cC1 cC2 cD) 
  (HA : A = A') (HB : B = B') (HM : M = M') (HN : N = N')
  (HFAM : F A M = F A' M') (HFBN : F B N = F B' N') : 
  forall f g,
  cast HFAM HFBN (F @@ f, g) ≃ F @@ (cast HA HB f), (cast HM HN g).
Proof.
  intros f g.
  subst.
  rewrite 3!cast_refl.
  easy.
Qed. *)


(* Section for monoidal category casts *)
Lemma cast_tensor {C} `{cC : Category C}
  `{monC : !MonoidalCategory C} `{castC : @CastCategory C cC}
  {A B M N A' B' M' N' : C} 
  (HA : A = A') (HB : B = B') (HM : M = M') (HN : N = N') 
  (HAB : A × B = A' × B') (HMN : M × N = M' × N') : forall f g, 
  cast HAB HMN (f ⊗ g) ≃ cast HA HM f ⊗ cast HB HN g.
Proof.
  intros f g.
  subst.
  rewrite 3!cast_refl.
  easy.
Qed.

Lemma cast_tensor_r_gen {C} `{cC : Category C}
  `{monC : @MonoidalCategory C cC} `{castC : @CastCategory C cC}
  {A B M N M' N' : C} (HM : M = M') (HN : N = N') 
  (HAM : A × M = A × M') (HBN : B × N = B × N') : forall f g, 
  f ⊗ cast HM HN g ≃ cast HAM HBN (f ⊗ g).
Proof.
  intros f g.
  subst.
  rewrite 2!cast_refl.
  easy.
Qed.

Definition __cast_tensor_r_proof {C} `{monC : MonoidalCategory C}
  {M M' : C} (HM : M = M') A : A × M = A × M' := ltac:(subst;easy).

Lemma cast_tensor_r {C} `{cC : Category C}
  `{monC : @MonoidalCategory C cC} `{castC : @CastCategory C cC}
  {A B M N M' N' : C} (HM : M = M') (HN : N = N') : forall (f : A ~> B) g,
  f ⊗ cast HM HN g ≃ 
  cast (__cast_tensor_r_proof HM A) (__cast_tensor_r_proof HN B) (f ⊗ g).
Proof.
  apply cast_tensor_r_gen.
Qed.
  
Lemma cast_tensor_l_gen {C} `{cC : Category C}
  `{monC : @MonoidalCategory C cC} `{castC : @CastCategory C cC}
  {A B A' B' M N : C} (HA : A = A') (HB : B = B') 
  (HAM : A × M = A' × M) (HBN : B × N = B' × N) : forall f g, 
  cast HA HB f ⊗ g ≃ cast HAM HBN (f ⊗ g).
Proof.
  intros f g.
  subst.
  rewrite 2!cast_refl.
  easy.
Qed.

Definition __cast_tensor_l_proof {C} `{monC : MonoidalCategory C}
  {A A' : C} (HA : A = A') M : A × M = A' × M := ltac:(subst;easy).

Lemma cast_tensor_l {C} `{cC : Category C, monC : !MonoidalCategory C, castC : !CastCategory C}
  {A B A' B' M N : C} (HA : A = A') (HB : B = B') : forall f (g: M ~> N),
  cast HA HB f ⊗ g ≃ cast (__cast_tensor_l_proof HA M) (__cast_tensor_l_proof HB N) (f ⊗ g).
Proof.
  apply cast_tensor_l_gen.
Qed.


(* Section for dagger category casts *)
Lemma cast_dagger_gen {C} `{cC : Category C} `{dagC : @DaggerCategory C cC}
  `{castC : @CastCategory C cC} {A B A' B' : C} 
  (HA1 HA2 : A = A') (HB1 HB2 : B = B'): 
  forall f,
  (cast HA1 HB1 f) † ≃ cast HB2 HA2 (f †).
Proof.
  intros.
  subst.
  rewrite 2!cast_refl.
  easy.
Qed.

Lemma cast_dagger {C} `{cC : Category C} `{dagC : @DaggerCategory C cC}
  `{castC : @CastCategory C cC} {A B A' B' : C} 
  (HA : A = A') (HB : B = B'): 
  forall f,
  (cast HA HB f) † ≃ cast HB HA (f †).
Proof.
  apply cast_dagger_gen; easy.
Qed.

(*
cast_n_compose:
  forall {n n' m : nat} (zx : ZX n n) (prf : n' = n),
  n_compose m ($ n', n' ::: zx $) ∝ $ n', n' ::: n_compose m zx $
cast_n_stack1:
  forall {n n' : nat} (prfn prfm : n' = n) (zx : ZX 1 1),
  $ n', n' ::: n ↑ zx $ ∝ n' ↑ zx





cast_compose_mid_contract:
  forall {n m o : nat} (n' m' o' : nat) (prfn prfn' : n' = n)
	(prfm prfm' : m' = m) (prfo prfo' : o' = o) (zx0 : ZX n m) 
    (zx1 : ZX m o),
  $ n', o' ::: zx0 ⟷ zx1 $ ∝ $ n', m' ::: zx0 $ ⟷ $ m', o' ::: zx1 $
cast_compose_partial_contract_r:
  forall {n m o : nat} (n' m' o' o'' : nat) (prfn : n' = n) 
	(prfm : m' = m) (prfo : o' = o') (prfo' : o' = o) 
    (prfo'' : o' = o'') (prfo''' : o'' = o) (zx0 : ZX n m') 
    (zx1 : ZX m o),
  $ n', o' ::: zx0 ⟷ $ m', o' ::: zx1 $ $
  ∝ $ n', o' ::: zx0 ⟷ $ m', o'' ::: zx1 $ $
cast_compose_partial_contract_l:
  forall {n m o : nat} (n' n'' m' o' : nat) (prfn : n' = n') 
	(prfn' : n' = n) (prfn'' : n' = n'') (prfn''' : n'' = n) 
    (prfm : m' = m) (prfo : o' = o) (zx0 : ZX n m) 
    (zx1 : ZX m' o),
  $ n', o' ::: $ n', m' ::: zx0 $ ⟷ zx1 $
  ∝ $ n', o' ::: $ n'', m' ::: zx0 $ ⟷ zx1 $

*)

Definition CastCategory_of_DecEq_Category {C : Type} (cC: Category C) 
  (dec : forall A B : C, {A = B} + {A <> B}) :
  @CastCategory C cC := {|
  cast := fun A B A' B' HA HB =>
    match HA in (_ = a) return (a ~> B' -> A ~> B) with (* Tell coq that A = A' *)
    | eq_refl =>
      fun f => 
      match HB in (_ = b) return (A ~> b -> A ~> B) with 
      | eq_refl => fun f' => f'
      end f
    end;
  cast_refl := ltac:(intros A B HA HB; 
    rewrite (@Eqdep_dec.UIP_dec C dec A _ _ (eq_refl));
    rewrite (@Eqdep_dec.UIP_dec C dec B _ _ (eq_refl));
    reflexivity);
|}.

Definition CastCategory_of_NatCategory (cC: Category nat) :
  @CastCategory nat cC := {|
  cast := fun A B A' B' HA HB =>
    match HA in (_ = a) return (a ~> B' -> A ~> B) with (* Tell coq that A = A' *)
    | eq_refl =>
      fun f => 
      match HB in (_ = b) return (A ~> b -> A ~> B) with 
      | eq_refl => fun f' => f'
      end f
    end;
  cast_refl := ltac:(intros A B HA HB; 
    rewrite (Eqdep_dec.UIP_refl_nat _ HA);
    rewrite (Eqdep_dec.UIP_refl_nat _ HB);
    reflexivity);
|}.