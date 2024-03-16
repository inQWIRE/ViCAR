Require Import Setoid.
From ViCaR Require Import CategoryTypeclass.

Open Scope Cat_scope.

Set Universe Polymorphism.

Generalizable Variables A B C D E cA cB cC cD cE.

Record Cat := { base_type : Type; cat_inst : Category base_type }.

Program Definition ComposeFunctors 
  `{cC : Category C, cD : Category D, cE : Category E}
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
Unset Printing Universes.

Notation "F '○' G" := (ComposeFunctors F G) (at level 59, left associativity).

#[export] Instance IdentityIsomorphism `{cC : Category C} (A : C) 
  : Isomorphism A A := {|
    forward := id_ A;
    reverse := id_ A;
    isomorphism_inverse := ltac:(rewrite left_unit; easy)
|}.

Definition ReverseIsomorphism `{cC : Category C} {A B : C} 
  (f : A <~> B) : B <~> A := {|
    forward := f.(reverse);
    reverse := f.(forward);
    isomorphism_inverse := 
      let (hA, hB) := f.(isomorphism_inverse) in conj hB hA
|}.

Program Definition ComposeIsomorphisms `{cC : Category C} {A B M : C} 
  (f : A <~> B) (g : B <~> M) := {|
    forward := f ∘ g;
    reverse := g^-1 ∘ f^-1;
|}.
Next Obligation.
  split.
  - rewrite <- assoc, (assoc (f:=f)), (id_A g), right_unit, (id_A f); easy.
  - rewrite <- assoc, (assoc (f:=g^-1)), (id_B f), right_unit, (id_B g); easy.
Qed.
    

Program Definition ReverseNaturalIsomorphism `{cC : Category C, cD : Category D} 
  {F G : Functor cC cD} (N : NaturalIsomorphism F G) : NaturalIsomorphism G F :=
  {| 
  component_iso := fun A => ReverseIsomorphism (N A)
|}.
Next Obligation.
  match goal with
  |- ?g ≃ ?h => rewrite <- (right_unit (f:=h))
  end.
  rewrite <- (proj1 (N B).(isomorphism_inverse)).
  rewrite <- assoc, !(assoc (h:= N B)), N.(component_iso_natural).
  apply compose_compat; [|easy].
  rewrite <- assoc, (proj2 (N A).(isomorphism_inverse)).
  rewrite left_unit.
  easy.
Qed.

Program Definition ComposeNaturalTransformations `{cC : Category C, cD : Category D} 
  {F G H : Functor cC cD} (N : NaturalTransformation F G)
    (M : NaturalTransformation G H) : NaturalTransformation F H := {|
    component_map := fun A => (α_ A) ∘ (α_ A)
  |}.
Next Obligation.
  rewrite <- assoc, N.(component_map_natural), 
  assoc, M.(component_map_natural), <- assoc.
  easy.
Qed.

Notation "N '⨀' M" := (ComposeNaturalTransformations N M) 
  (at level 59, left associativity) : Cat_scope.

Program Definition ComposeNaturalIsomorphisms `{cC : Category C, cD : Category D} 
  {F G H : Functor cC cD} (N : NaturalIsomorphism F G) (M : NaturalIsomorphism G H)
   : NaturalIsomorphism F H :=
  {| 
  component_iso := fun A => ComposeIsomorphisms (N A) (M A)
|}.
Next Obligation.
  rewrite <- assoc, N.(component_map_natural), 
    assoc, M.(component_map_natural), <- assoc.
  easy.
Qed.

Program Definition Isomorphism_by_Functor `{cC : Category C, cD : Category D} 
  {A B : C} (F : Functor cC cD) (H : A <~> B) : F A <~> F B :=
  {|
    forward := F @ H;
    reverse := F @ H^-1
  |}.
Next Obligation.
  split; rewrite <- compose_map.
  - rewrite (id_A H), id_map; easy.
  - rewrite (id_B H), id_map; easy.
Qed.


Program Definition NaturalIsomorphism_of_Compose 
  `{cC : Category C, cD : Category D, cE : Category E}
  {F F' : Functor cC cD} {G G' : Functor cD cE} 
  (N : NaturalIsomorphism F F') (M : NaturalIsomorphism G G') 
    : NaturalIsomorphism (F ○ G) (F' ○ G') := 
  {| 
    component_iso := fun A => ComposeIsomorphisms 
      (Isomorphism_by_Functor G (N A)) (M (F' A))
|}.
Next Obligation.
  rewrite 2!component_iso_natural, <- assoc.
  rewrite component_iso_natural, 2!(assoc (f:=M (F A))).
  apply compose_compat; [easy|].
  rewrite <- 2!compose_map.
  rewrite component_iso_natural.
  easy.
Qed.


Program Definition IdentityFunctor `(cC : Category C) : Functor cC cC :=
  {| obj_map := id; morphism_map := fun _ _ => id |}.
Solve All Obligations with (rewrite ?left_unit, ?right_unit; easy).

Program Definition IdentityNaturalIsomorphism
  `{cC : Category C, cD : Category D} (F : Functor cC cD) : 
  NaturalIsomorphism F F :=
  {| component_iso := fun A => IdentityIsomorphism _ |}.
Next Obligation.
  rewrite ?left_unit, ?right_unit; easy.
Qed.


Definition naturally_isomorphic `{cC : Category C, cD : Category D} 
  : relation (Functor cC cD) :=
  fun F G => exists (comp_map : forall A : C, F A <~> G A), 
    forall (A B : C) (f : A ~> B),
    F @ f ∘ comp_map B ≃ comp_map A ∘ G @ f.

Lemma naturally_isomorphic_of_NaturalIsomorphism 
  `{cC : Category C, cD : Category D} {F G : Functor cC cD} : 
  NaturalIsomorphism F G -> naturally_isomorphic F G.
Proof.
  intros [c Hc].
  exists c; exact Hc.
Qed.

Lemma naturally_isomorphic_iff_ex_NaturalIsomorphism 
  `{cC : Category C, cD : Category D} (F G : Functor cC cD) : 
  naturally_isomorphic F G <-> (exists _ : NaturalIsomorphism F G, True).
Proof.
  split.
  - intros [c Hc]. 
    exists {| component_iso := c; component_iso_natural := Hc |};
    easy.
  - intros [[c Hc] _]; exists c; exact Hc.
Qed.

Lemma naturally_isomorphic_refl `{cC : Category C, cD : Category D} :
  reflexive _ (@naturally_isomorphic C cC D cD).
Proof.
  intros F.
  apply naturally_isomorphic_of_NaturalIsomorphism, 
    IdentityNaturalIsomorphism.
Qed.

Lemma naturally_isomorphic_sym `{cC : Category C, cD : Category D} :
  symmetric _ (@naturally_isomorphic C cC D cD).
Proof.
  intros F G.
  rewrite naturally_isomorphic_iff_ex_NaturalIsomorphism.
  intros [N _].
  apply naturally_isomorphic_of_NaturalIsomorphism.
  exact (ReverseNaturalIsomorphism N).
Qed.

Lemma naturally_isomorphic_trans `{cC : Category C, cD : Category D} :
  transitive _ (@naturally_isomorphic C cC D cD).
Proof.
  intros F G H.
  rewrite 2!naturally_isomorphic_iff_ex_NaturalIsomorphism.
  intros [N _] [M _].
  apply naturally_isomorphic_of_NaturalIsomorphism.
  exact (ComposeNaturalIsomorphisms N M).
Qed.

Definition in_cat_of_cat {U} {cU : Category U} : Cat :=
  {| base_type := U |}. 

Definition cat_of_in_cat {U : Cat} := U.(cat_inst).
Coercion cat_of_in_cat : Cat >-> Category.



Program Definition ComposeFunctorsAssociator 
  `{cA : Category A, cB : Category B, cC : Category C, cD : Category D}
  (F : Functor cA cB) (G : Functor cB cC) (H : Functor cC cD) : 
  NaturalIsomorphism (F ○ G ○ H) (F ○ (G ○ H)) :=
   {| component_iso := fun A => IdentityIsomorphism _ |}.
Next Obligation.
  rewrite left_unit, right_unit; easy.
Qed.

Lemma compose_functors_assoc 
  `{cA : Category A, cB : Category B, cC : Category C, cD : Category D}
  (F : Functor cA cB) (G : Functor cB cC) (H : Functor cC cD) 
  : naturally_isomorphic (F ○ G ○ H) (F ○ (G ○ H)).
Proof.
  exact (naturally_isomorphic_of_NaturalIsomorphism 
    (ComposeFunctorsAssociator F G H)).
Qed.

#[export] Program Instance CatCategory : Category Cat := 
  {|
    morphism := fun U V => Functor U V;
    c_equiv := fun A B => naturally_isomorphic;
    compose := fun A B C => ComposeFunctors;
    c_identity := fun A => IdentityFunctor A
  |}.
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
  rewrite Hchj, 2!(assoc (f:=chj (f x))).
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

Class CategoryProduct `{cC : Category C} (A B : C) := {
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

Lemma prod_mor_unique' `{cC : Category C} {A B : C} 
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

Program Definition category_product_unique `{cC : Category C} (A B : C) :
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

Class CategoryBigProd `{cC : Category C} {I : Type} 
  (obj : I -> C) (prod_I : C) := {
  p_i : forall i, prod_I ~> obj i;
  big_cat_prod_mor : 
    forall (Q : C) (fQ_ : forall i, Q ~> obj i), Q ~> prod_I;
  big_cat_prod_mor_prop: 
    forall (Q : C) (fQ_ : forall i, Q ~> obj i),
    forall i, 
    (big_cat_prod_mor Q fQ_) ∘ p_i i ≃ fQ_ i;
  big_cat_prod_mor_unique : 
    forall (Q : C) (fQ_ : forall i, Q ~> obj i)
    (fAB' : Q ~> prod_I), 
    (forall i, fQ_ i ≃ fAB' ∘ p_i i) ->
    fAB' ≃ big_cat_prod_mor Q fQ_
}.

Lemma big_cat_prod_mor_unique' `{cC : Category C} {I} {obj : I -> C} {pI : C} 
  (HI : CategoryBigProd obj pI) {Q} (fQ_ : forall i, Q ~> obj i) :
  forall (fAB fAB' : Q ~> pI),
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

Program Definition category_big_cat_prod_unique `{cC : Category C} {I} {obj : I->C} :
  forall {pI pI'} (HI : CategoryBigProd obj pI) (HI' : CategoryBigProd obj pI'), 
    Isomorphism pI pI' :=
  fun pI pI' HI HI' =>
  {|
    forward := HI'.(big_cat_prod_mor) pI p_i;
    reverse := HI.(big_cat_prod_mor) pI' p_i;
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

(* I'm fine exporting, seeing as we're unlikely to be asking for any other
   category on Functor cC cD... or any at all! *)
#[export, program] Instance FunctorCategory `(cC : Category C, cD : Category D) : 
  Category (Functor cC cD) := {|
    morphism := @NaturalTransformation C D cC cD;
    c_equiv := nat_trans_equiv;
    compose := fun F G H => ComposeNaturalTransformations;
    c_identity := fun F => IdentityNaturalIsomorphism F;
  |}.
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

Definition big_prod {I : Type} (CI : I -> Type) := forall i, CI i.

#[export, program] Instance BigProductCategory {I : Type} (CI : I -> Type)
  (cI : forall i : I, Category (CI i)) : Category (big_prod CI) := {|
  morphism := fun is js => forall i, is i ~> js i;
  c_equiv := fun is js fis fjs => forall i, fis i ≃ fjs i;
  compose := fun is js ks fijs fjks => fun i => fijs i ∘ fjks i;
  c_identity := fun is => fun i => id_ (is i);
|}.
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

#[program, export] Instance BigProductComponentFunctor {I} (CI : I -> Type) 
  (cI : forall i : I, Category (CI i)) (i : I) : 
  Functor (BigProductCategory CI cI) (cI i) := {
  obj_map := fun is => is i;
  morphism_map := fun is js fijs => fijs i;
}.
Solve All Obligations with easy.

#[export] Instance BigProductFunctor_of_Components {I} 
  (CI : I -> Type) (cI : forall i : I, Category (CI i)) (Q : Cat) 
  (fQ_ : forall i, Functor Q.(cat_inst) (cI i)) : 
  Functor Q (BigProductCategory CI cI) := {
  obj_map := fun q => fun i => fQ_ i q;
  morphism_map := fun q r fqr => fun i => (fQ_ i).(morphism_map) fqr;
  id_map := fun a => fun i => (fQ_ i).(id_map) a;
  compose_map := fun a b m f g => fun i => (fQ_ i).(compose_map) f g;
  morphism_compat := fun a b f g H => fun i => (fQ_ i).(morphism_compat) f g H;
}.

#[export, program] Instance BigProductIsomorphism_of_Components {I} 
  (CI : I -> Type) (cI : forall i : I, Category (CI i)) (As Bs : big_prod CI)
  (Hiso : forall i, As i <~> Bs i) : As <~> Bs := {
  forward := fun i => Hiso i;
  reverse := fun i => Hiso i ^-1;
}.
Next Obligation.
  split; intros i; apply (Hiso i).(isomorphism_inverse).
Qed.

(* 
Lemma exists_big_product_isomorphism_iff_forall_exists {I}
  (CI : I -> Type) (cI : forall i : I, Category (CI i)) (As Ba : big_prod CI) P :
  exists f : As <~> Bs, P f <-> forall i, exists fi : As i <~> Bs i *)

(* #[program, export] Instance big_product_category_is_product {I}
  (CI : I -> Type) (cI : forall i : I, Category (CI i)) : 
  CategoryBigProd (cC := CatCategory) 
    (fun i => {|base_type:=CI i; cat_inst:=cI i|}) 
    {| base_type := big_prod CI; cat_inst := BigProductCategory CI cI |} := {
  p_i := fun i => BigProductComponentFunctor CI cI i;
  big_cat_prod_mor := BigProductFunctor_of_Components CI cI;
}.
Next Obligation.
  exists (fun a => IdentityIsomorphism _).
  intros; rewrite right_unit, left_unit; easy.
Qed.
Next Obligation.
  (* edestruct H as [Hiso Hnat]. *)
  (* unfold naturally_isomorphic in H. *)


  assert (Hex: exists f : forall i, NaturalIsomorphism (fQ_ i) (fAB' ○ BigProductComponentFunctor CI cI i), True)
    by admit.
  destruct Hex as [Hiso _].
  eexists.
  unshelve (instantiate (1:= (fun a => _))).
  - eapply Build_Isomorphism.
    unshelve (instantiate (1:= (fun i => _))).
    exact (Hiso a).(reverse).
  
  
    pose (ReverseIsomorphism (Hiso a)).
    simpl in *.

    eapply Build_Isomorphism.
    unshelve (instantiate (1:= (fun i => _))).
    exact (X i a).(reverse).
    pose (X a).(reverse) as m.
    exact m.
    simpl in m.
    simpl.
    destruct (H i) as [N _].
    
  
  refine (ex_intro _ (fun a => _), _).


Definition big_sum {I : Type} (CI : I -> Type) := {i & CI i}.

#[program] Definition BigSumCategory {I : Type} 
  (UIPI : forall (i:I) (p q : i = i), p = q) 
  (UIUIPI : forall (i:I) (p q : i = i) (H H' : p = q), H = H')
  (CI : I -> Type)
  (cI : forall i : I, Category (CI i)) : Category (big_sum CI) := {|
  morphism := fun somei somej => let (i, ai) := somei in let (j, aj) := somej in
    {H : i = j & _};
  c_equiv := fun somei somej somefi somefj => _;
  (* c_identity := fun somei => let (i, ai) := somei in existT _ eq_refl (id_ ai); *)
  (* compose := fun is js ks fijs fjks => fun i => fijs i ∘ fjks i;
  c_identity := fun is => fun i => id_ (is i); *)
|}.
Next Obligation.
  exact (ai ~> aj).
Defined.
Next Obligation.
  destruct somei as [i ai]; destruct somej as [j aj].
  destruct somefi as [Hij mori], somefj as [? morj].
  subst.
  rewrite (UIPI _ _ eq_refl) in morj.
  exact (mori ≃ morj).
Defined.
Next Obligation.
  destruct A as [i ai], B as [j aj].
  split.
  - intros [Hij mor].
    subst; simpl in *.
    rewrite (UIUIPI _ _ _ _ eq_refl).
    reflexivity.
  - intros [Hij mor] [Hij' mor'] [Hij'' mor''].
    subst.
    pose (UIPI _ Hij'' eq_refl);
    pose (UIPI _ Hij' eq_refl); subst.
    simpl.
    rewrite (UIUIPI _ _ _ _ eq_refl).
    simpl; intros. etransitivity; eauto.
  - intros [Hij mor] [Hij' mor'].
    subst.
    pose (UIPI _ Hij' eq_refl); subst.
    simpl.
    rewrite (UIUIPI _ _ _ _ eq_refl).
    easy.
Qed.
Next Obligation.
  destruct A as [i ai], B as [j aj], M as [k ak].
  destruct X as [Hij morij], X0 as [Hjk morjk].
  eapply (existT _ (eq_trans Hij Hjk)).
  subst.
  exact (morij ∘ morjk).
Defined.
Next Obligation.
  rename j into h'.
  destruct A as [i ai], B as [j aj], M as [k ak].
  destruct f, g, h, h'.
  subst.
  pose (UIPI _ x0 eq_refl);
  pose (UIPI _ x2 eq_refl); subst.
  simpl in *.
  rewrite (UIUIPI _ _ _ _ eq_refl) in *.
  apply compose_compat; easy.
Qed.
Next Obligation.
  destruct A as [i ai], B as [j aj], M as [k ak], N as [l al].
  destruct f as [Hij morij], g as [Hjk morjk], h as [Hkl morkl].
  subst.
  simpl.
  rewrite (UIUIPI _ _ _ _ eq_refl).
  rewrite assoc; easy.
Qed.
Next Obligation.
  destruct A as [i ai].
  apply (existT _ eq_refl (id_ ai)).
Defined.
Next Obligation.
  destruct A as [i ai], B as [j aj].
  destruct f as [Hij morij].
  subst.
  simpl.
  rewrite (UIUIPI _ _ _ _ eq_refl).
  apply left_unit.
Qed.
Next Obligation.
  destruct A as [i ai], B as [j aj].
  destruct f as [Hij morij].
  subst.
  simpl.
  rewrite (UIUIPI _ _ _ _ eq_refl).
  apply right_unit.
Qed.





Require Import Logic.Eqdep_dec.

#[universes(polymorphic=yes), program] Definition BigSumCategory {I : Type} 
  (eqdec_I : forall i j : I, {i = j} + {i <> j}) 
  (CI : I -> Type)
  (cI : forall i : I, Category (CI i)) : Category (big_sum CI) := {|
  morphism := fun somei somej => let (i, ai) := somei in let (j, aj) := somej in _;
    (* match eqdec_I i j with
    | left H => _
    | _ => False
    end; *)
  c_equiv := fun somei somej somefi somefj => _;
  (* compose := fun is js ks fijs fjks => fun i => fijs i ∘ fjks i;
  c_identity := fun is => fun i => id_ (is i); *)
|}.
Next Obligation.
  destruct (eqdec_I i j).
  - subst.
    exact (ai ~> aj).
  - exact False.
Defined.
Next Obligation.
  destruct somei as [i ai]; destruct somej as [j aj].
  (* destruct somefi as mori, somefj as morj. *)
  unfold BigSumCategory_obligation_1 in *.
  destruct (eqdec_I i j).
  - subst. exact (somefi ≃ somefj).
  - destruct somefi.
Defined.
Next Obligation.
  destruct A as [i ai], B as [j aj].
  unfold BigSumCategory_obligation_1 in *.
  simpl in *.
  destruct (eqdec_I i j); [ | easy].
  subst; simpl.
  split.
  - intros somefi; easy.
  - intros ? **.
    etransitivity; eauto.
  - intros ?.
    easy.
Qed.
Next Obligation.
  destruct A as [i ai], B as [j aj], M as [k ak].
  unfold BigSumCategory_obligation_1 in *.
  simpl in *.
  destruct (eqdec_I i j); [ | easy].
  destruct (eqdec_I j k); [ | easy].
  subst.
  destruct (eqdec_I k k); [ | easy].
  rewrite (UIP_dec eqdec_I _ eq_refl).
  simpl.
  
  unfold eq_rect_r in *.
  simpl in *.
  eapply compose; eassumption.
Defined.
Next Obligation.
  rename j into j'.
  destruct A as [i ai], B as [j aj], M as [k ak].
  unfold BigSumCategory_obligation_1 in *.
  (* simpl in H, H0, f, g, h, j'. *)
  simpl in *.
  destruct (eqdec_I i j); [ | easy].
  destruct (eqdec_I j k); [ | easy].
  subst.
  unfold EqdepFacts.internal_eq_rew_r_dep, eq_rect_r in *.
  simpl in *.
  destruct (eqdec_I k k) as [e | ]; [ | easy].

  rewrite (UIP_dec eqdec_I _ eq_refl) in *.
  simpl.
  

  simpl in *.
  unfold EqdepFacts.internal_eq_sym_internal, 
  EqdepFacts.internal_eq_sym_internal0.
  apply compose_compat.
  
  rewrite (UIP_dec eqdec_I _ eq_refl).

  
  





  rewrite assoc; easy.
Qed.
Next Obligation.
  rewrite left_unit; easy.
Qed.
Next Obligation.
  rewrite right_unit; easy.
Qed.

  


Class CartesianMonoidalCategory *)
