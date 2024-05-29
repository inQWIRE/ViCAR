Require Import Setoid.
From ViCaR Require CategoryTypeclass CategoryAutomation.
Require Logic.Eqdep_dec List.
Require CatExample. 
Require Import FunctionalExtensionality.
Require Bool.
Require Import Psatz.

Section FreeMonoid.

Import CategoryTypeclass CategoryAutomation.
Import CatExample (FunctorCategory).

Create HintDb bwarrdb.

Variable (X : Type).

Inductive bw :=
  | e : bw
  | var (x : X) : bw
  | tens (a b : bw) : bw.

Local Notation "a '⨂' b" := (tens a b) (at level 40, left associativity).

Inductive bweq : bw -> bw -> Prop :=
  | bw_refl (a : bw) : bweq a a
  | bw_trans (a b c : bw) : bweq a b -> bweq b c -> bweq a c
  (* | bw_symm (a b : bw) : bweq a b -> bweq b a *)
  | bw_leftidl (a : bw) : bweq (tens e a) a
  | bw_leftidr (a : bw) : bweq a (tens e a)
  | bw_rightidl (a : bw) : bweq (tens a e) a
  | bw_rightidr (a : bw) : bweq a (tens a e)
  | bw_rassoc (a b c : bw) : bweq (tens a (tens b c)) (tens (tens a b) c)
  | bw_lassoc (a b c : bw) : bweq (tens (tens a b) c) (tens a (tens b c))
  | bw_tens (a a' b b' : bw) : bweq a a' -> bweq b b' -> bweq (tens a b) (tens a' b').

Local Notation "a '~' b" := (bweq a b) (at level 70).

Lemma bweq_symm (a b : bw) : bweq a b -> bweq b a.
Proof.
  intros H.
  induction H; eauto using bweq.
Qed.

Add Parametric Relation : bw bweq 
  reflexivity proved by bw_refl 
  symmetry proved by bweq_symm 
  transitivity proved by bw_trans as bweq_setoid.


Inductive bwnorm :=
  | norm_e : bwnorm
  | norm_rtens (n : bwnorm) (x : X) : bwnorm.

Fixpoint bwnorm_to_bw (a : bwnorm): bw :=
  match a with
  | norm_e => e
  | norm_rtens n x => tens (bwnorm_to_bw n) (var x)
  end.
Coercion bwnorm_to_bw : bwnorm >-> bw.

Fixpoint bwbrac (a : bw) : bwnorm -> bwnorm :=
  match a with
  | e => fun n => n
  | var x => fun n => norm_rtens n x
  | tens a b => fun n => bwbrac b (bwbrac a n)
  end.

Local Notation "'⟦' a '⟧'" := (bwbrac a).

Definition Nf : bw -> bwnorm := fun a => ⟦a⟧ norm_e.

Lemma bwbrac_of_bweq (a b : bw) : a ~ b ->
  forall n : bwnorm, ⟦a⟧ n = ⟦b⟧ n.
Proof.
  intros H.
  induction H; 
    eauto using bwnorm;
    intros n.
  - etransitivity; eauto.
  - simpl.
    rewrite IHbweq1.
    apply IHbweq2.
Qed.

Lemma bwnorm_ltens_bw_eq (a : bw) : forall n : bwnorm,
  (tens n a) ~ (bwbrac a n).
Proof.
  induction a; eauto using bweq.
Qed.

Lemma bweq_Nf (a : bw) : a ~ (Nf a).
Proof.
  transitivity (tens e a);
  [constructor |].
  apply (bwnorm_ltens_bw_eq a (norm_e)).
Qed.

Lemma bw_of_bwnorm_inj (n m : bwnorm) : @eq bw n m -> n = m.
Proof.
  revert m.
  induction n; intros m; simpl.
  - intros H.
    destruct m; easy.
  - destruct m; [easy|].
    simpl.
    intros H.
    inversion H.
    subst.
    erewrite IHn by eassumption.
    easy.
Qed.


Inductive bwarr : bw -> bw -> Type :=
  | arrcomp {a b c : bw} (f : bwarr a b) (g : bwarr b c) : bwarr a c
  | arrtens {a a' b b'} (f : bwarr a a') (g : bwarr b b') : bwarr (a ⨂ b) (a' ⨂ b')
  | arrid (a : bw) : bwarr a a
  | arrassoc (a b c : bw) : bwarr (a ⨂ (b ⨂ c)) (a ⨂ b ⨂ c)
  | arrinvassoc (a b c : bw) : bwarr (a ⨂ b ⨂ c) (a ⨂ (b ⨂ c))
  | arrlunitor (a : bw) : bwarr (e ⨂ a) a
  | arrinvlunitor (a : bw) : bwarr a (e ⨂ a)
  | arrrunitor (a : bw) : bwarr (a ⨂ e) a
  | arrinvrunitor (a : bw) : bwarr a (a ⨂ e).

Local Notation "a '⟶' b" := (bwarr a b) (at level 60) : type_scope.

Reserved Notation "f '≅' g" (at level 70).
Inductive bwarrequiv : forall a b, relation (a ⟶ b) :=
  | bwarr_refl {a b} (f : a ⟶ b) : f ≅ f
  | bwarr_trans {a b} (f g h : a ⟶ b) : f ≅ g -> g ≅ h -> f ≅ h
  
  | bwarr_comp {a b c : bw} (f f' : a ⟶ b) (g g' : b ⟶ c) :
      f ≅ f' -> g ≅ g' -> arrcomp f g ≅ arrcomp f' g'
  | bwarr_rassoc {a a' b' b : bw} (f : a ⟶ a') (g : a' ⟶ b') (h : b' ⟶ b) :
      arrcomp f (arrcomp g h) ≅ arrcomp (arrcomp f g) h
  | bwarr_lassoc {a a' b' b : bw} (f : a ⟶ a') (g : a' ⟶ b') (h : b' ⟶ b) :
      arrcomp (arrcomp f g) h ≅ arrcomp f (arrcomp g h)
  | bwarr_lunitl {a b} (f : a ⟶ b) : arrcomp (arrid a) f ≅ f
  | bwarr_lunitr {a b} (f : a ⟶ b) : f ≅ arrcomp (arrid a) f
  | bwarr_runitl {a b} (f : a ⟶ b) : arrcomp f (arrid b) ≅ f
  | bwarr_runitr {a b} (f : a ⟶ b) : f ≅ arrcomp f (arrid b)

  | bwarr_tens {a a' b b' : bw} (f f' : a ⟶ a') (g g' : b ⟶ b') :
    f ≅ f' -> g ≅ g' -> arrtens f g ≅ arrtens f' g'
  | bwarr_tens_idl {a b : bw} :
    arrtens (arrid a) (arrid b) ≅ arrid (a ⨂ b)
  | bwarr_tens_idr {a b : bw} :
    arrid (a ⨂ b) ≅ arrtens (arrid a) (arrid b)
  | bwarr_tens_compl {a b c a' b' c'} 
    (f : a ⟶ b) (g : b ⟶ c) (f' : a' ⟶ b') (g' : b' ⟶ c') :
    arrtens (arrcomp f g) (arrcomp f' g') ≅ 
      arrcomp (arrtens f f') (arrtens g g')
  | bwarr_tens_compr {a b c a' b' c'} 
    (f : a ⟶ b) (g : b ⟶ c) (f' : a' ⟶ b') (g' : b' ⟶ c') :
    arrcomp (arrtens f f') (arrtens g g') ≅ 
      arrtens (arrcomp f g) (arrcomp f' g')
  
  | bwarr_assoc_rinv_r (a b c : bw) :
    arrcomp (arrassoc a b c) (arrinvassoc a b c) ≅ arrid (a ⨂ (b ⨂ c))
  | bwarr_assoc_rinv_l (a b c : bw) :
    arrid (a ⨂ (b ⨂ c)) ≅ arrcomp (arrassoc a b c) (arrinvassoc a b c)

  | bwarr_assoc_linv_r (a b c : bw) :
    arrcomp (arrinvassoc a b c) (arrassoc a b c) ≅ arrid (a ⨂ b ⨂ c)
  | bwarr_assoc_linv_l (a b c : bw) :
    arrid (a ⨂ b ⨂ c) ≅ arrcomp (arrinvassoc a b c) (arrassoc a b c)

  | bwarr_lunitor_rinv_r (a : bw) :
    arrcomp (arrlunitor a) (arrinvlunitor a) ≅ arrid (e ⨂ a)
  | bwarr_lunitor_rinv_l (a : bw) :
    arrid (e ⨂ a) ≅ arrcomp (arrlunitor a) (arrinvlunitor a)

  | bwarr_lunitor_linv_r (a : bw) :
    arrcomp (arrinvlunitor a) (arrlunitor a) ≅ arrid a
  | bwarr_lunitor_linv_l (a : bw) :
    arrid a ≅ arrcomp (arrinvlunitor a) (arrlunitor a)

  | bwarr_runitor_rinv_r (a : bw) :
    arrcomp (arrrunitor a) (arrinvrunitor a) ≅ arrid (a ⨂ e)
  | bwarr_runitor_rinv_l (a : bw) :
    arrid (a ⨂ e) ≅ arrcomp (arrrunitor a) (arrinvrunitor a)

  | bwarr_runitor_linv_r (a : bw) :
    arrcomp (arrinvrunitor a) (arrrunitor a) ≅ arrid a
  | bwarr_runitor_linv_l (a : bw) :
    arrid a ≅ arrcomp (arrinvrunitor a) (arrrunitor a)

  | bwarr_assoc_natl {a b c a' b' c' : bw} 
    (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
    arrcomp (arrassoc a b c) (arrtens (arrtens f g) h)
    ≅ arrcomp (arrtens f (arrtens g h)) (arrassoc a' b' c')
  | bwarr_assoc_natr {a b c a' b' c' : bw} 
    (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
    arrcomp (arrtens f (arrtens g h)) (arrassoc a' b' c')
    ≅ arrcomp (arrassoc a b c) (arrtens (arrtens f g) h)

  | bwarr_lunitor_natl {a b : bw} (f : a ⟶ b) :
    arrcomp (arrlunitor a) f ≅ arrcomp (arrtens (arrid e) f) (arrlunitor b)
  | bwarr_lunitor_natr {a b : bw} (f : a ⟶ b) :
    arrcomp (arrtens (arrid e) f) (arrlunitor b) ≅ arrcomp (arrlunitor a) f
  
  | bwarr_runitor_natl {a b : bw} (f : a ⟶ b) :
    arrcomp (arrrunitor a) f ≅ arrcomp (arrtens f (arrid e)) (arrrunitor b)
  | bwarr_runitor_natr {a b : bw} (f : a ⟶ b) :
    arrcomp (arrtens f (arrid e)) (arrrunitor b) ≅ arrcomp (arrrunitor a) f
  
  | bwarr_pentagonl (a b c d : bw) : 
    arrcomp (arrassoc a b (c⨂d)) (arrassoc (a⨂b) c d)
    ≅ arrcomp 
        (arrcomp (arrtens (arrid a) (arrassoc b c d)) (arrassoc a (b⨂c) d))
        (arrtens (arrassoc a b c) (arrid d))
  | bwarr_pentagonr (a b c d : bw) : 
    arrcomp 
      (arrcomp (arrtens (arrid a) (arrassoc b c d)) (arrassoc a (b⨂c) d))
      (arrtens (arrassoc a b c) (arrid d))
    ≅ arrcomp (arrassoc a b (c⨂d)) (arrassoc (a⨂b) c d)

  | bwarr_trianglel (a b : bw) :
    arrcomp (arrassoc a e b) (arrtens (arrrunitor a) (arrid b))
    ≅ arrtens (arrid a) (arrlunitor b)
  | bwarr_triangler (a b : bw) :
    arrtens (arrid a) (arrlunitor b)
    ≅ arrcomp (arrassoc a e b) (arrtens (arrrunitor a) (arrid b))
  where "f '≅' g" := (bwarrequiv _ _ f g).

Local Notation "f '≅' g" := (bwarrequiv _ _ f g).

Lemma bwarr_symm {a b : bw} (f g : a ⟶ b) : f ≅ g -> g ≅ f.
Proof.
  intros H.
  induction H;
  eauto using bwarrequiv.
Qed.

Add Parametric Relation (a b : bw) : (bwarr a b) (bwarrequiv a b)
  reflexivity proved by bwarr_refl
  symmetry proved by bwarr_symm
  transitivity proved by bwarr_trans as bwarrequiv_setoid.

Add Parametric Morphism (a b c : bw) : (@arrcomp a b c)
  with signature 
  (bwarrequiv a b) ==> (bwarrequiv b c) ==> (bwarrequiv a c)
  as arrcomp_mor.
Proof. eauto using bwarrequiv. Qed.

Add Parametric Morphism (a a' b b' : bw) : (@arrtens a a' b b')
  with signature 
  (bwarrequiv a a') ==> (bwarrequiv b b') ==> (bwarrequiv (a⨂b) (a'⨂b'))
  as arrtens_mor.
Proof. eauto using bwarrequiv. Qed.




Definition bwcat : Category bw := {|
  morphism := bwarr;
  c_equiv := bwarrequiv;
  compose := fun _ _ _ => arrcomp;
  c_identity := arrid;
|}.

Section bwcat_Category.

#[local] Existing Instance bwcat | 10.

#[export, program] Instance bwcath : CategoryCoherence bwcat.
Next Obligation.
split; apply bwarrequiv_setoid.
Qed.
Obligation Tactic := Tactics.program_simpl; eauto 4 using bwarrequiv.
Solve All Obligations.

#[export, program] Instance bwassoc_iso (a b c : bw) 
  : Isomorphism (a ⨂ b ⨂ c) (a ⨂ (b ⨂ c)) := {
  forward := arrinvassoc a b c;
  reverse := arrassoc a b c;
}.

#[export, program] Instance bwlunitor_iso (a : bw) 
  : Isomorphism (e ⨂ a) a := {
  forward := arrlunitor a;
  reverse := arrinvlunitor a;
}.

#[export, program] Instance bwrunitor_iso (a : bw) 
  : Isomorphism (a ⨂ e) a := {
  forward := arrrunitor a;
  reverse := arrinvrunitor a;
}.

#[export] Instance bwmcat : MonoidalCategory bwcat | 10 := {
  obj_tensor := tens;
  mor_tensor := @arrtens;
  associator := bwassoc_iso;
  left_unitor := bwlunitor_iso;
  right_unitor := bwrunitor_iso;
}.

Fixpoint bwarrinv {A B} (h : A ⟶ B) : B ⟶ A :=
  match h with
  | arrid a => arrid a
  | arrassoc a b c => arrinvassoc a b c
  | arrinvassoc a b c => arrassoc a b c
  | arrlunitor a => arrinvlunitor a 
  | arrinvlunitor a => arrlunitor a
  | arrrunitor a => arrinvrunitor a 
  | arrinvrunitor a => arrrunitor a
  | arrcomp f g => arrcomp (bwarrinv g) (bwarrinv f)
  | arrtens f g => arrtens (bwarrinv f) (bwarrinv g)
  end.

Lemma bwarrinv_invol {A B} (h : A ⟶ B) : 
  bwarrinv (bwarrinv h) = h.
Proof.
  induction h; try easy; simpl; rewrite IHh1, IHh2; easy.
Qed.

Lemma bwarrinv_linv {A B} (h : A ⟶ B) : arrcomp (bwarrinv h) h ≅ arrid B.
Proof.
  induction h; [eauto 3 using bwarrequiv .. ]; simpl.
  - rewrite bwarr_lassoc, (bwarr_rassoc (bwarrinv h1)), IHh1; eauto using bwarrequiv.
  - rewrite bwarr_tens_compr, bwarr_tens_idr.
    apply bwarr_tens; auto.
Qed.

Lemma bwarrinv_rinv {A B} (h : A ⟶ B) : arrcomp h (bwarrinv h) ≅ arrid A.
Proof.
  induction h; [eauto 3 using bwarrequiv .. ]; simpl.
  - rewrite bwarr_lassoc, (bwarr_rassoc h2), IHh2; eauto using bwarrequiv.
  - rewrite bwarr_tens_compr, bwarr_tens_idr.
    apply bwarr_tens; auto.
Qed.

Lemma bwinv_unique {a b} (f : a ⟶ b) (g g' : b ⟶ a) : 
  arrcomp f g ≅ arrid a -> arrcomp g' f ≅ arrid b ->
  g ≅ g'.
Proof.
  intros Hfg Hg'f.
  rewrite (bwarr_lunitr g), <- Hg'f.
  rewrite bwarr_lassoc, Hfg.
  eauto 3 using bwarrequiv.
Qed.

Lemma bwinv_unique' {a b} (f : a ⟶ b) (g g' : b ⟶ a) : 
  arrcomp g f ≅ arrid b -> arrcomp f g' ≅ arrid a ->
  g ≅ g'.
Proof.
  intros Hgf Hfg'.
  symmetry.
  eapply bwinv_unique; eauto.
Qed.

Add Parametric Morphism {A B} : (@bwarrinv A B) 
  with signature
  (bwarrequiv A B) ==> (bwarrequiv B A)
  as bwarrinv_mor.
Proof.
  intros x y Hxy.
  apply bwinv_unique with x.
  - apply bwarrinv_rinv.
  - rewrite Hxy.
    apply bwarrinv_linv.
Qed.

Lemma by_bwarrinv {a b : bw} (f f' : a ⟶ b) :
  bwarrinv f ≅ bwarrinv f' -> f ≅ f'.
Proof.
  intros H.
  rewrite <- (bwarrinv_invol f), <- (bwarrinv_invol f').
  rewrite H.
  easy.
Qed.



Lemma bwarr_invassoc_natl {a b c a' b' c'} (f : a' ⟶ a) 
  (g : b' ⟶ b) (h : c' ⟶ c) :
  arrcomp (arrtens (arrtens f g) h) (arrinvassoc a b c) 
  ≅ arrcomp (arrinvassoc a' b' c') (arrtens f (arrtens g h)).
Proof.
  apply by_bwarrinv, bwarr_assoc_natl.
Qed.

Lemma bwarr_invlunitor_natl {a b} (f : b ⟶ a) :
  arrcomp f (arrinvlunitor a)
  ≅ arrcomp (arrinvlunitor b) (arrtens (arrid e) f).
Proof.
  apply by_bwarrinv, bwarr_lunitor_natl.
Qed.

Lemma bwarr_invrunitor_natl {a b} (f : b ⟶ a) :
  arrcomp f (arrinvrunitor a)
  ≅ arrcomp (arrinvrunitor b) (arrtens f (arrid e)).
Proof.
  apply by_bwarrinv, bwarr_runitor_natl.
Qed.

Lemma bwarr_invpentagonl (a b c d : bw) : 
  arrcomp (arrinvassoc (a ⨂ b) c d) (arrinvassoc a b (c ⨂ d))
  ≅ arrcomp (arrtens (arrinvassoc a b c) (arrid d))
    (arrcomp (arrinvassoc a (b ⨂ c) d)
       (arrtens (arrid a) (arrinvassoc b c d))).
Proof.
  apply by_bwarrinv, bwarr_pentagonl.
Qed.

Lemma bwarr_invtrianglel' (a b : bw) : 
  arrcomp (arrinvassoc a e b) (arrtens (arrid a) (arrlunitor b))
  ≅ arrtens (arrrunitor a) (arrid b).
Proof.
  rewrite (bwarr_triangler a b).
  rewrite bwarr_rassoc, bwarr_assoc_linv_r, bwarr_lunitl.
  easy.
Qed.


Hint Constructors bwarrequiv : bwarrdb.
Hint Resolve bwarr_symm bwarrinv_linv bwarrinv_rinv : bwarrdb.
Hint Resolve bwarr_invassoc_natl bwarr_invlunitor_natl 
  bwarr_invrunitor_natl bwarr_invpentagonl bwarr_invtrianglel' : bwarrdb.
Hint Rewrite @bwarr_invassoc_natl 
  @bwarr_invlunitor_natl @bwarr_invrunitor_natl : bwarrdb.
Hint Rewrite <- @bwarr_invassoc_natl 
  @bwarr_invlunitor_natl @bwarr_invrunitor_natl : bwarrdb_rev.

Obligation Tactic := Tactics.program_simpl; simpl; eauto 3 with bwarrdb.


#[export, program] Instance bwmcath : MonoidalCategoryCoherence bwmcat := {}.

Class IsGroupoid {C} (cC : Category C) := {
  groupoid_inv {A B : C} (f : (A ~> B)%Cat) : (B ~> A)%Cat;
  groupoid_inv_is_inv {A B : C} (f : (A ~> B)%Cat) : 
    (is_inverse f (groupoid_inv f))%Cat
}.  

#[export, program] Instance bwgroupoid : IsGroupoid bwcat := {
  groupoid_inv := @bwarrinv
}.

End bwcat_Category.

Hint Constructors bwarrequiv : bwarrdb.
Hint Resolve bwarr_symm bwarrinv_linv bwarrinv_rinv : bwarrdb.
Hint Resolve bwarr_invassoc_natl bwarr_invlunitor_natl 
  bwarr_invrunitor_natl bwarr_invpentagonl bwarr_invtrianglel' : bwarrdb.
Hint Rewrite @bwarr_invassoc_natl 
  @bwarr_invlunitor_natl @bwarr_invrunitor_natl : bwarrdb.
Hint Rewrite <- @bwarr_invassoc_natl 
  @bwarr_invlunitor_natl @bwarr_invrunitor_natl : bwarrdb_rev.

Obligation Tactic := Tactics.program_simpl; simpl; eauto 3 with bwarrdb.


Lemma bweq_of_arr {a b : bw} : a ⟶ b -> a ~ b.
Proof.
  intros f.
  induction f; eauto using bweq.
Qed.

Lemma ex_arr_of_bweq {a b : bw} : a ~ b -> exists (f:a ⟶ b), True.
Proof.
  intros H.
  induction H; try (destruct IHbweq1, IHbweq2); eexists; eauto 2 using bwarr.
Qed.

Lemma bweq_iff_ex_arr {a b : bw} : a ~ b <-> exists (f:a ⟶ b), True.
Proof.
  split; [apply ex_arr_of_bweq|].
  intros [f _]; apply bweq_of_arr; easy.
Qed.

#[program] Definition DiscreteCategory (N : Type) : Category N := {|
  morphism := @eq N;
  c_equiv := fun _ _ _ _ => True;
  c_identity := @eq_refl N
|}.

#[export, program] Instance DiscreteCategoryCoherence (N : Type) 
  : CategoryCoherence (DiscreteCategory N) := {
}.
Solve All Obligations with easy.

(* Local Notation "'𝒩'" := (DiscreteCategory bwnorm).
Local Notation "'𝒩h'" := (DiscreteCategoryCoherence bwnorm). *)

Fixpoint xi_comp_map_forw (n : bwnorm) (A : bw) {struct A} : 
  n ⨂ A ⟶ ⟦A⟧ n :=
  match A with
  | e => arrrunitor n
  | var x => arrid (n ⨂ var x)
  | tens a b => 
    arrcomp (arrassoc n a b) (
    arrcomp (arrtens (xi_comp_map_forw n a) (arrid b)) 
    (xi_comp_map_forw (⟦a⟧ n) b))
  end. 

Fixpoint xi_comp_map_rev (n : bwnorm) (A : bw) {struct A} : ⟦A⟧ n ⟶ n ⨂ A. 
Proof.
  induction A.
  apply arrinvrunitor.
  apply arrid.
  apply (arrcomp (arrcomp (xi_comp_map_rev (⟦A1⟧ n) A2)
  (arrtens (xi_comp_map_rev n A1) (arrid A2)) ) (arrinvassoc n A1 A2)).
Defined.

Notation "'UIP' Y" := (forall (y : Y) (H H' : y = y), H = H') (at level 10).
Notation "'DECEQ' Y" := (forall (x y : Y), {x = y} + {x <> y}) (at level 10).

#[export, program] Instance DecDiscreteCategory {N : Type} (iseq : DECEQ N) :
  Category N := {
  morphism := fun a b => match (iseq a b) with 
    | left yes => True 
    | right no => False
    end;
  c_equiv := fun _ _ _ _ => True;
}.
Next Obligation.
  destruct (iseq A B); [destruct (iseq B M) |]; destruct (iseq A M); try constructor + congruence.
Defined.
Next Obligation.
  destruct (iseq A A).
  constructor.
  apply n, eq_refl.
Defined.

#[export, program] Instance DecDiscreteCategoryCoherence {N : Type} 
  (iseq : DECEQ N) : CategoryCoherence (DecDiscreteCategory iseq) := {}.
Next Obligation.
  destruct (iseq A B); easy.
Qed.

Context (DECEQX : DECEQ X).

Lemma eqbwnorm : DECEQ bwnorm.
Proof.
  intros b.
  induction b; intros c; induction c.
  - left; constructor.
  - right; congruence.
  - right; congruence.
  - destruct (IHb c) as [Heq | Hneq].
    + destruct (DECEQX x x0) as [Hxeq | Hxne].
      * left; subst; easy.
      * right; congruence.
    + right; congruence.
Qed.

Lemma eqbw : DECEQ bw.
Proof.
  intros b.
  induction b; intros c; induction c; eauto; try ((left + right); congruence).
  - destruct (DECEQX x x0); 
    [left; subst; constructor | right; congruence].
  - destruct (IHb1 c1); [| right; congruence].
    destruct (IHb2 c2); [| right; congruence].
    left; subst; constructor.
Qed.


Local Notation "'𝒩'" := (DecDiscreteCategory eqbwnorm).
Local Notation "'𝒩h'" := (DecDiscreteCategoryCoherence eqbwnorm).



Lemma Eq_rect_bw : EqdepFacts.Eq_rect_eq bw.
Proof.
  apply EqdepFacts.Streicher_K__eq_rect_eq, 
  EqdepFacts.UIP_refl__Streicher_K,
  EqdepFacts.UIP__UIP_refl.
  intros ? ** ?.
  apply Eqdep_dec.UIP_dec, eqbw.
Qed.

Lemma Eq_rect_bwnorm : EqdepFacts.Eq_rect_eq bwnorm.
Proof.
  apply EqdepFacts.Streicher_K__eq_rect_eq, 
  EqdepFacts.UIP_refl__Streicher_K,
  EqdepFacts.UIP__UIP_refl.
  intros ? ** ?.
  apply Eqdep_dec.UIP_dec, eqbwnorm.
Qed.

#[export, program] Instance norm_bw_bifunc : 
  Bifunctor 𝒩 bwcat bwcat := {
  obj_bimap := fun n a => n ⨂ a;
  morphism_bimap := fun n n' a b neq f => arrtens (arrid n) f
}.
Next Obligation.
  destruct (eqbwnorm n n'); subst; easy.
Defined.
Next Obligation.
  rewrite <- Eq_rect_bw.
  eauto with bwarrdb.
Qed.
Next Obligation.
  repeat match goal with
  |- context[norm_bw_bifunc_obligation_1 ?a ?b ?c ?d] =>
    (generalize (norm_bw_bifunc_obligation_1 a b c d))
  end.
  simpl.
  intros HBM HAB HAM.
  assert (HAB1: A1 = B1) by
  (destruct (eqbwnorm A1 B1); easy).  
  assert (HBM1: B1 = M1) by
  (destruct (eqbwnorm B1 M1); easy).  
  assert (HAM1: A1 = M1) by
  (destruct (eqbwnorm A1 M1); subst; easy).
  inversion HAB; 
  inversion HBM; 
  inversion HBM; subst.
  erewrite <- !Eq_rect_bw.
  rewrite <- (bwarr_lunitl (arrid M1)) at 1.
  eauto with bwarrdb.
Qed.
Next Obligation.
  assert (HAB1: A1 = B1) by
  (destruct (eqbwnorm A1 B1); easy).
  repeat match goal with
  |- context[norm_bw_bifunc_obligation_1 ?a ?b ?c ?d] =>
    (generalize (norm_bw_bifunc_obligation_1 a b c d))
  end.
  simpl.
  intros Heq Heq'.
  inversion Heq; subst.
  rewrite <- !Eq_rect_bw.
  eauto with bwarrdb.
Qed.

Fixpoint bwbrac_eq_of_arr {a b} (f : a ⟶ b) {struct f} : forall n, ⟦a⟧ n = ⟦b⟧ n.
  induction f; intros n.
  3: apply eq_refl.
  all: try apply eq_refl.
  - rewrite <- IHf2. apply IHf1.
  - simpl.
    rewrite <- IHf1.
    apply IHf2.
Defined.

#[export, program] Instance Nf_functor : Functor bwcat 𝒩 := {
  obj_map := Nf;
  (* morphism_map := fun a b f => (bwbrac_of_bweq a b (bweq_of_arr f) norm_e) *)
}.
Next Obligation.
  destruct (eqbwnorm (Nf A) (Nf B)) as [Heq | Hf].
  constructor.
  apply Hf.
  apply (bwbrac_eq_of_arr X0).
Defined.



#[export, program] Instance bwbrac_functor : 
  Functor bwcat (@FunctorCategory _ _ 𝒩 _ 𝒩 _) := {
  obj_map := fun a => {|obj_map := bwbrac a|};
  morphism_map := fun a b f => 
    {| component_map := fun c => _ |}
  (* morphism_map := fun a b f => (bwbrac_of_bweq a b (bweq_of_arr f) norm_e) *)
}.
Next Obligation.
  destruct (eqbwnorm A B) as [Heq | Hne];
  destruct (eqbwnorm (⟦a⟧ A) (⟦a⟧ B)) as [Heq' | Hne'];
  subst; congruence + constructor.
Defined.
Next Obligation.
  destruct (eqbwnorm (⟦a⟧ c) (⟦b⟧ c)) as [Heq | Hne]; [|apply Hne].
  constructor.
  apply (bwbrac_eq_of_arr f).
Qed.
Solve All Obligations with constructor.




Set Universe Polymorphism.

#[export, program] Instance Bifunctor_of_FunctorCategoryFunctor 
  {C D E : Type} {cC : Category C} {cD : Category D} {cE : Category E}
  (* {cCh : CategoryCoherence cC} *) 
  {cDh : CategoryCoherence cD} {cEh : CategoryCoherence cE} 
  (F : Functor cC (FunctorCategory (cC:=cD) (cD:=cE))) :
  Bifunctor cC cD cE := {
  obj_bimap := F.(obj_map);
  morphism_bimap := fun A1 B1 A2 B2 f1 f2 => 
    (F A1 @ f2 ∘ component_map (F.(morphism_map) f1) B2)%Cat
}.
Next Obligation.
  (* rewrite (F A1).(id_map), left_unit. *)
  rewrite component_map_natural.
  rewrite (F A1).(id_map), right_unit.
  apply F.
Qed.
Next Obligation.
  symmetry.
  rewrite assoc, <- (assoc _ (F B1 @ g2)%Cat).
  rewrite <- component_map_natural.
  rewrite compose_map.
  rewrite !assoc.
  apply compose_cancel_l, compose_cancel_l.
  symmetry.
  apply F.
Qed.
Next Obligation.
  rewrite H0.
  epose proof (F.(morphism_compat) f f') as e.
  specialize (e ltac:(assumption)).
  simpl in e.
  hnf in e.
  rewrite e.
  easy.
Qed.


Definition bwbrac_mor_bimap (n m : bwnorm) (a b : bw) 
  (H : 𝒩.(morphism) n m) (f : a ⟶ b) : ⟦a⟧ n ⟶ ⟦b⟧ m.
Proof.
  simpl in H.
  destruct (eqbwnorm n m) as [Heq | Hf]; [| destruct H].
  subst.
  rewrite <- (bwbrac_eq_of_arr f).
  apply arrid.
Defined.
Arguments bwbrac_mor_bimap _ _ _ _ _ / _.
Arguments eq_rect_r [_] [_] _ _ [_] / _.


#[export, program] Instance bwbrac_bifunctor : 
  Bifunctor 𝒩 bwcat bwcat := {
  obj_bimap := fun n a => ⟦a⟧ n;
  morphism_bimap := bwbrac_mor_bimap;
}.
Next Obligation.
  generalize (DecDiscreteCategory_obligation_2 bwnorm eqbwnorm A1).
  simpl.
  intros H.
  destruct (eqbwnorm A1 A1); [|easy].
  rewrite <- Eq_rect_bwnorm.
  easy.
Qed.
Next Obligation.
  generalize (DecDiscreteCategory_obligation_1 bwnorm eqbwnorm A1 B1 M1 f1 g1).
  simpl.
  intros y.
  (* assert (HAB2: forall n, ⟦A2⟧ n = ⟦B2⟧ n) by
    (apply bwbrac_eq_of_arr; easy).
  assert (HBM2: forall n, ⟦B2⟧ n = ⟦M2⟧ n) by
    (apply bwbrac_eq_of_arr; easy).
  assert (HAM2: forall n, ⟦A2⟧ n = ⟦M2⟧ n) by
    (apply bwbrac_eq_of_arr; eauto using bwarr). *)
  destruct (eqbwnorm A1 B1) as [HAB | Hf];
  destruct (eqbwnorm B1 M1) as [HBM | Hf'];
  destruct (eqbwnorm A1 M1) as [HAM | Hf'']; try congruence;
  try subst A1; try subst B1; simpl; try easy.
  rewrite <- !Eq_rect_bwnorm.
  generalize (bwbrac_eq_of_arr f2 M1) as H1.
  generalize (bwbrac_eq_of_arr g2 M1) as H1.
  match goal with
  |- context[eq_ind ?x ?P ?f ?y ?e] => generalize (eq_ind x P f y e)
  end.
  simpl.
  intros HAM2 HBM2 HAB2.
  generalize dependent (⟦A2⟧ M1);
  intros; subst; simpl.
  generalize dependent (⟦B2⟧ M1);
  intros; subst; simpl.
  rewrite <- Eq_rect_bwnorm.
  eauto with bwarrdb.
Qed.
Next Obligation.
  destruct (eqbwnorm A1 B1) as [Heq | Hf]; [|easy].
  subst.
  rewrite <- !Eq_rect_bwnorm.
  repeat match goal with 
  |- context[eq_rect _ _ _ _ ?H] => generalize H
  end.
  match goal with 
  |- forall H : (?x = ?y), _ => 
    generalize dependent x; intros; subst
  end.
  rewrite <- Eq_rect_bwnorm.
  easy.
Qed.

Local Notation "'ξ_' n a" := (xi_comp_map_forw n a) 
  (at level 10, n at next level, a at next level).

Local Notation "f '○' g" := (arrcomp f g) (at level 59, left associativity).
Local Notation "f '⊠' g" := (arrtens f g) (at level 40, left associativity).

Lemma arrtens_pushout_top {a b c d e : bw} (f : a ⟶ b) (g : b ⟶ c) (h : d ⟶ e) :
  arrtens (arrcomp f g) h
  ≅ arrcomp (arrtens f h) (arrtens g (arrid e)).
Proof.
  rewrite bwarr_tens_compr, bwarr_runitl.
  easy.
Qed.

Lemma arrtens_pushin_top {a b c d e : bw} (f : a ⟶ b) (g : b ⟶ c) (h : d ⟶ e) :
  arrtens (arrcomp f g) h
  ≅ arrcomp (arrtens f (arrid d)) (arrtens g h).
Proof.
  rewrite bwarr_tens_compr, bwarr_lunitl.
  easy.
Qed.

  Lemma arrtens_pushout_bot {a b c d e : bw} (f : a ⟶ b) (g : c ⟶ d) (h : d ⟶ e) :
  arrtens f (arrcomp g h) 
  ≅ arrcomp (arrtens f g) (arrtens (arrid b) h).
Proof.
  rewrite bwarr_tens_compr, bwarr_runitl.
  easy.
Qed.

Lemma arrtens_pushin_bot {a b c d e : bw} (f : a ⟶ b) (g : c ⟶ d) (h : d ⟶ e) :
  arrtens f (arrcomp g h) 
  ≅ arrcomp (arrtens (arrid a) g) (arrtens f h).
Proof.
  rewrite bwarr_tens_compr, bwarr_lunitl.
  easy.
Qed.

Lemma arrtens_split_diag {a b a' b'} (f : a ⟶ a') (g : b ⟶ b') :
  f ⊠ g ≅ f ⊠ arrid b ○ arrid a' ⊠ g.
Proof.
  rewrite bwarr_tens_compr, bwarr_lunitl, bwarr_runitl.
  easy.
Qed.



Lemma bwarr_trianglel' (a b : bw) :
  arrassoc a e b ≅ arrid a ⊠ arrlunitor b ○ arrinvrunitor a ⊠ arrid b.
Proof.
  rewrite (bwarr_runitr (arrassoc a e b)), bwarr_tens_idr,
    (bwarr_runitor_rinv_l), arrtens_pushout_top, bwarr_rassoc,
    bwarr_trianglel.
  easy.
Qed.

Lemma bwarr_compose_l {a b c} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) :
  f ○ g ≅ h <-> g ≅ bwarrinv f ○ h.
Proof.
  split; intros H; rewrite H + rewrite <- H;
  rewrite bwarr_rassoc, ?bwarrinv_linv, ?bwarrinv_rinv, bwarr_lunitl;
  easy.
Qed.

Lemma bwarr_compose_l' {a b c} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) :
  h ≅ f ○ g <-> bwarrinv f ○ h ≅ g.
Proof.
  split; symmetry; apply bwarr_compose_l; symmetry; assumption.
Qed.

Lemma bwarr_compose_r {a b c} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) :
  f ○ g ≅ h <-> f ≅ h ○ bwarrinv g.
Proof.
  split; intros H; [rewrite <- H | rewrite H];
  rewrite bwarr_lassoc, ?bwarrinv_linv, ?bwarrinv_rinv, bwarr_runitl;
  easy.
Qed.

Lemma bwarr_compose_r' {a b c} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) :
  h ≅ f ○ g <-> h ○ bwarrinv g ≅ f.
Proof.
  split; symmetry; apply bwarr_compose_r; symmetry; assumption.
Qed.

Lemma bwarr_compose_cancel_l {a b c} (f : a ⟶ b) (g h : b ⟶ c) :
  f ○ g ≅ f ○ h -> g ≅ h.
Proof.
  intros H.
  rewrite (bwarr_lunitr g), (bwarr_lunitr h), 
    <- (bwarrinv_linv f), bwarr_lassoc, H.
  eauto with bwarrdb.
Qed.

Lemma bwarr_compose_cancel_r {a b c} (f g : a ⟶ b) (h : b ⟶ c) :
  f ○ h ≅ g ○ h -> f ≅ g.
Proof.
  intros H.
  rewrite (bwarr_runitr f), (bwarr_runitr g), <- (bwarrinv_rinv h), 
    bwarr_rassoc, H.
  eauto with bwarrdb.
Qed.

Lemma bwarr_compose_cancel_l_iff {a b c} (f : a ⟶ b) (g h : b ⟶ c) :
  f ○ g ≅ f ○ h <-> g ≅ h.
Proof.
  split; [apply bwarr_compose_cancel_l|now intros ->].
Qed.

Lemma bwarr_compose_cancel_r_iff {a b c} (f g : a ⟶ b) (h : b ⟶ c) :
  f ○ h ≅ g ○ h <-> f ≅ g.
Proof.
  split; [apply bwarr_compose_cancel_r|now intros ->].
Qed.

Local Notation "f '^-'" := (bwarrinv f) (at level 9).


Lemma bwarr_tensor_cancel_e_top {a b} (f g : a ⟶ b) (h : e ⟶ e) :
  h ⊠ f ≅ h ⊠ g -> f ≅ g.
Proof.
  intros H.
  apply bwinv_unique with (f^-);
  [now rewrite bwarrinv_linv|].
  rewrite bwarr_lunitr, bwarr_compose_r, bwarr_tens_idr in H.
  simpl in H.
  rewrite bwarr_tens_compr, bwarrinv_rinv in H.
  rewrite <- (bwarr_compose_cancel_r_iff _ _ (arrlunitor _)) in H.
  rewrite 2!bwarr_lunitor_natr in H.
  rewrite bwarr_compose_cancel_l_iff in H.
  easy.
Qed.

Lemma bwarr_tensor_cancel_e_bot {a b} (f g : a ⟶ b) (h : e ⟶ e) :
  f ⊠ h ≅ g ⊠ h -> f ≅ g.
Proof.
  intros H.
  apply bwinv_unique with (f^-);
  [now rewrite bwarrinv_linv|].
  rewrite bwarr_lunitr, bwarr_compose_r, bwarr_tens_idr in H.
  simpl in H.
  rewrite bwarr_tens_compr, bwarrinv_rinv in H.
  rewrite <- (bwarr_compose_cancel_r_iff _ _ (arrrunitor _)) in H.
  rewrite 2!bwarr_runitor_natr in H.
  rewrite bwarr_compose_cancel_l_iff in H.
  easy.
Qed.

Lemma bwarr_tensor_cancel_e_top_iff {a b} (f g : a ⟶ b) (h : e ⟶ e) :
  h ⊠ f ≅ h ⊠ g <-> f ≅ g.
Proof.
  split; [apply bwarr_tensor_cancel_e_top|now intros ->].
Qed.

Lemma bwarr_tensor_cancel_e_bot_iff {a b} (f g : a ⟶ b) (h : e ⟶ e) :
  f ⊠ h ≅ g ⊠ h <-> f ≅ g.
Proof.
  split; [apply bwarr_tensor_cancel_e_bot|now intros ->].
Qed.


Lemma bwarr_assoc_nat_alt {a b c a' b' c' : bw} 
  (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
  arrassoc a b c ≅ f ⊠ (g ⊠ h) ○ arrassoc a' b' c' ○ ((f ⊠ g) ⊠ h)^-.
Proof.
  rewrite bwarr_compose_r'.
  simpl.
  rewrite 3!bwarrinv_invol.
  apply bwarr_assoc_natl.
Qed.

Lemma bwarr_assoc_nat_alt' {a b c a' b' c' : bw} 
  (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
  arrassoc a b c ≅ f ⊠ (g ⊠ h) ○ arrassoc a' b' c' ○ (f^- ⊠ g^-) ⊠ h^-.
Proof.
  rewrite bwarr_compose_r'.
  simpl.
  rewrite 3!bwarrinv_invol.
  apply bwarr_assoc_natl.
Qed.

Lemma bwarr_invassoc_nat_alt {a b c a' b' c' : bw} 
  (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
  arrinvassoc a b c ≅ (f ⊠ g) ⊠ h ○ arrinvassoc a' b' c' ○ (f ⊠ (g ⊠ h))^-.
Proof.
  apply by_bwarrinv.
  simpl.
  rewrite !bwarrinv_invol, bwarr_rassoc.
  apply bwarr_assoc_nat_alt.
Qed.

Lemma bwarr_invassoc_nat_alt' {a b c a' b' c' : bw} 
  (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
  arrinvassoc a b c ≅ (f ⊠ g) ⊠ h ○ arrinvassoc a' b' c' ○ f^- ⊠ (g^- ⊠ h^-).
Proof.
  apply by_bwarrinv.
  simpl.
  rewrite !bwarrinv_invol, bwarr_rassoc.
  apply bwarr_assoc_nat_alt.
Qed.

Lemma bwarr_triangle_alt (a b : bw) : 
  arrassoc a e b ≅ 
  arrid a ⊠ arrlunitor b ○ arrinvrunitor a ⊠ arrid b.
Proof.
  rewrite bwarr_compose_r'.
  apply bwarr_trianglel.
Qed.

Lemma bwarr_invtriangle_alt (a b : bw) : 
  arrinvassoc a e b ≅ 
  arrrunitor a ⊠ arrid b ○ arrid a ⊠ arrinvlunitor b.
Proof.
  apply by_bwarrinv.
  simpl.
  apply bwarr_triangle_alt.
Qed.


Lemma bwarr_lunitor_tri (b c : bw) : 
  arrassoc e b c ○ arrlunitor b ⊠ arrid c ≅ arrlunitor (b ⨂ c).
Proof.
  pose proof (bwarr_pentagonl e e b c) as p.
  rewrite (bwarr_triangle_alt e b) in p.
  rewrite (bwarr_triangle_alt e (b ⨂ c)) in p.
  rewrite (bwarr_assoc_nat_alt (arrrunitor e) (arrid b) (arrid c)) in p.
  rewrite (bwarr_assoc_nat_alt (arrid e) (arrlunitor b) (arrid c)) in p.
  rewrite !arrtens_pushout_top, !bwarr_rassoc, bwarr_compose_cancel_r_iff in p.
  rewrite !bwarr_lassoc, bwarrinv_linv, bwarr_runitl in p.
  rewrite !bwarr_rassoc, bwarr_compose_cancel_r_iff in p.
  rewrite bwarr_lassoc, bwarr_tens_compr, bwarr_runitor_linv_r in p.
  rewrite bwarr_lunitl, 2!bwarr_tens_idl, bwarr_runitl in p.
  rewrite bwarr_tens_compr, bwarr_lunitl in p.
  rewrite bwarr_tensor_cancel_e_top_iff in p.
  symmetry.
  exact p.
Qed.


Lemma bwarr_runitor_tri (b c : bw) : 
  arrid b ⊠ arrrunitor c ≅ arrassoc b c e ○ arrrunitor (b ⨂ c).
Proof.
  pose proof (bwarr_invpentagonl b c e e) as p.
  rewrite (bwarr_invtriangle_alt c e) in p.
  rewrite (bwarr_invtriangle_alt (b ⨂ c) e) in p.
  rewrite (bwarr_invassoc_nat_alt (arrid b) (arrid c) (arrlunitor e)) in p. (* sure about runitor? *)
  rewrite (bwarr_invassoc_nat_alt (arrid b) (arrrunitor c) (arrid e)) in p. (* runitor?? *)
  simpl in p.
  rewrite !arrtens_pushout_bot, !bwarr_rassoc, bwarr_compose_cancel_r_iff in p.
  rewrite !bwarr_lassoc, 2!bwarr_tens_compr, bwarr_runitor_linv_r in p.
  rewrite !bwarr_lunitl, !bwarr_tens_idl, bwarr_runitl, !bwarr_rassoc in p.
  rewrite bwarr_compose_cancel_r_iff in p.
  rewrite bwarr_lassoc, bwarr_tens_compr, bwarr_lunitor_linv_r in p.
  rewrite bwarr_lunitl, bwarr_tens_idl, bwarr_runitl in p.
  rewrite bwarr_tens_compr, bwarr_lunitl in p.
  rewrite bwarr_tensor_cancel_e_bot_iff in p.
  rewrite p, bwarr_rassoc, bwarr_assoc_rinv_r, bwarr_lunitl.
  easy.
Qed.

#[export, program] Instance bwbinat_trans : 
  NaturalBiIsomorphism norm_bw_bifunc bwbrac_bifunctor  := {
  component_biiso := fun n a => {| 
      forward := xi_comp_map_forw n a; 
      reverse := xi_comp_map_rev n a;
    |};
  component_biiso_natural := fun n m a b hnm f => _
}.
Next Obligation.
  enough (H:forall m b, bwarrinv (xi_comp_map_rev m b) ≅ xi_comp_map_forw m b) by (
    rewrite <- H, bwarrinv_linv, bwarrinv_rinv; easy).
  intros m b.
  (* unfold xi_comp_map_rev, xi_comp_map_for *)
  revert m; 
  induction b; intros m; eauto 2 with bwarrdb.
  simpl.
  rewrite IHb1, IHb2.
  eauto with bwarrdb.
Qed.
Next Obligation.
  Ltac geneqrect :=
    repeat match goal with 
    |- context[eq_rect _ _ _ _ ?H] => generalize H
    end.
  Ltac genheadcast :=
    match goal with 
    |- forall H : (?x = ?y), _ => 
      generalize dependent x; intros; subst
    end.
  Ltac gencast :=
    geneqrect;
    genheadcast.
  geneqrect.
  destruct (eqbwnorm n m) as [Heq | Hf]; [|easy].
  subst; simpl; intros.
  rewrite <- Eq_rect_bw. revert dependent m;
  induction f; intros m e0 e1.
  1:{rewrite arrtens_pushout_bot, bwarr_lassoc,
    (IHf2 m (bwbrac_eq_of_arr f2 m) eq_refl), bwarr_rassoc, 
    (IHf1 m (bwbrac_eq_of_arr f1 m) eq_refl), bwarr_lassoc.
    apply bwarr_comp; [easy|].
    clear e1 IHf1 IHf2.
    gencast.
    rewrite <- Eq_rect_bwnorm.
    gencast.
    rewrite <- !Eq_rect_bwnorm.
    eauto with bwarrdb. }
  1:{ simpl (ξ_ m (a'⨂b')).
    rewrite 3!bwarr_rassoc, bwarr_assoc_natr, (bwarr_lassoc (arrassoc _ _ _)),
      bwarr_tens_compr, (IHf1 m (bwbrac_eq_of_arr f1 m) eq_refl).
    rewrite bwarr_runitl, (bwarr_lunitr f2).
    rewrite bwarr_tens_compl, (arrtens_split_diag _ f2), !bwarr_lassoc.
    rewrite (IHf2 _ (bwbrac_eq_of_arr f2 _) eq_refl).
    simpl.
    rewrite !bwarr_lassoc.
    repeat (apply bwarr_comp; [easy|]).
    geneqrect.
    clear IHf1 IHf2 e0 e1.
    intros H H' H''; revert H'' H' H.
    simpl.
    genheadcast.
    rewrite <- Eq_rect_bwnorm.
    rewrite bwarr_tens_idl, bwarr_lunitl.
    apply bwarr_comp; [easy|].
    gencast.
    rewrite <- !Eq_rect_bwnorm.
    easy. }
  all : rewrite <- ?Eq_rect_bwnorm, ?bwarr_tens_idl, 
    ?bwarr_lunitl, ?bwarr_runitl.
  all : repeat match goal with
  | H : ?x = ?y |- _ => unify x y; clear H
  end.
  1: easy.
  1: { assert (Hassoc : arrid m ⊠ arrassoc a b c ○ 
    ξ_ m (a ⨂ b ⨂ c) ≅ ξ_ m (a ⨂ (b ⨂ c))). 1:{
    simpl.
    rewrite 2!arrtens_pushin_top.
    rewrite !bwarr_rassoc.
    rewrite bwarr_pentagonr.
    do 2 (apply bwarr_comp; [|easy]).
    rewrite !bwarr_lassoc.
    apply bwarr_comp; [easy|].
    rewrite bwarr_assoc_natl.
    apply bwarr_comp; [|easy].
    rewrite bwarr_tens_idl; easy.
  } apply Hassoc. }
  
  1: { assert (Hassoc : arrid m ⊠ arrassoc a b c ○ 
    ξ_ m (a ⨂ b ⨂ c) ≅ ξ_ m (a ⨂ (b ⨂ c))). 1:{
    simpl.
    rewrite 2!arrtens_pushin_top.
    rewrite !bwarr_rassoc.
    rewrite bwarr_pentagonr.
    do 2 (apply bwarr_comp; [|easy]).
    rewrite !bwarr_lassoc.
    apply bwarr_comp; [easy|].
    rewrite bwarr_assoc_natl.
    apply bwarr_comp; [|easy].
    rewrite bwarr_tens_idl; easy.
  } 
    rewrite (bwarr_lunitr (ξ_ m (a ⨂ b ⨂ c))),
      bwarr_tens_idr, bwarr_assoc_linv_l, 
      arrtens_pushin_bot, bwarr_lassoc.
    apply bwarr_comp; [easy|].
    symmetry.
    apply Hassoc.
  }
  - simpl.
    rewrite bwarr_triangler, bwarr_lassoc.
    easy.
  - simpl.
    rewrite (bwarr_rassoc (arrassoc m e a)).
    rewrite bwarr_trianglel.
    rewrite bwarr_rassoc, bwarr_tens_compr, bwarr_lunitor_linv_r,
      bwarr_lunitl, bwarr_tens_idl, bwarr_lunitl.
    easy.
  - simpl.
    rewrite bwarr_runitor_natr, bwarr_rassoc.
    apply bwarr_comp; [|easy].
    apply bwarr_runitor_tri.
  - simpl.
    rewrite bwarr_runitor_natr, bwarr_compose_l, !bwarr_rassoc.
    rewrite bwarr_compose_cancel_r_iff.
    symmetry.
    apply bwarr_runitor_tri.
Qed.

(* #[export, program] Instance  *)


#[export, program] Instance Nf_bwcat_functor : Functor bwcat bwcat := {
  obj_map := Nf;
  (* morphism_map := fun a b f => (bwbrac_of_bweq a b (bweq_of_arr f) norm_e) *)
}.
Next Obligation.
  destruct (eqbwnorm (Nf A) (Nf B)) as [Heq | Hf].
  - rewrite <- Heq.
    apply arrid.
  - exfalso; apply Hf, (bwbrac_eq_of_arr X0 norm_e).
Defined.
Next Obligation.
  unfold Nf_bwcat_functor_obligation_1.
  destruct (eqbwnorm (Nf A) (Nf A)); [|easy].
  rewrite <- Eq_rect_bwnorm.
  easy.
Qed.
Next Obligation.
  unfold Nf_bwcat_functor_obligation_1.
  pose proof (bwbrac_eq_of_arr f norm_e).
  pose proof (bwbrac_eq_of_arr g norm_e).
  destruct (eqbwnorm (Nf A) (Nf B)); [|easy].
  destruct (eqbwnorm (Nf B) (Nf M)); [|easy].
  destruct (eqbwnorm (Nf A) (Nf M)); [|congruence].
  do 3 (gencast;
  rewrite <- Eq_rect_bwnorm).
  apply bwarr_lunitr.
Qed.
Next Obligation.
  unfold Nf_bwcat_functor_obligation_1.
  pose proof (bwbrac_eq_of_arr f norm_e).
  destruct (eqbwnorm (Nf A) (Nf B)); [|easy].
  easy.
Qed.

Lemma bwbrac_arr_of_arr {a b : bw} (f : a ⟶ b) : 
  forall (n : bwnorm), ⟦a⟧ n ⟶ ⟦b⟧ n.
Proof.
  induction f; eauto 2 using bwarr;
  intros n.
  simpl.
  rewrite <- (bwbrac_of_bweq a a' (bweq_of_arr f1) n).
  apply IHf2.
Defined.

#[export, program] Instance toNf_natiso : 
  NaturalIsomorphism (CatExample.IdentityFunctor bwcat) Nf_bwcat_functor := {
  component_iso := fun a =>
    CatExample.ComposeIsomorphisms
    {| forward := arrinvlunitor a : bwcat.(morphism) _ _; reverse := arrlunitor a |}
    (bwbinat_trans norm_e a)
}.
Next Obligation.
  rewrite bwarr_rassoc. 
  unfold id.
  rewrite bwarr_invlunitor_natl, !bwarr_lassoc.
  rewrite bwarr_compose_cancel_l_iff.
  epose proof (bwbinat_trans.(component_biiso_natural) norm_e norm_e 
    A B _ f) as en.
  simpl in en.
  rewrite <- Eq_rect_bw in en.
  rewrite en; clear en.
  rewrite bwarr_compose_cancel_l_iff.
  unshelve (instantiate (1:=_)).
  - simpl.
    destruct (eqbwnorm norm_e norm_e); [|easy].
    constructor.
  - simpl.
    destruct (eqbwnorm norm_e norm_e); [|easy].
    unfold Nf_bwcat_functor_obligation_1.
    rewrite <- Eq_rect_bwnorm.
    pose proof (bwbrac_eq_of_arr f norm_e).
    destruct (eqbwnorm (Nf A) (Nf B)); [|easy].
    clear H e0.
    geneqrect.
    unfold Nf in *.
    clear e1.
    intros.
    generalize dependent (⟦A⟧ norm_e).
    intros; subst.
    rewrite <- !Eq_rect_bwnorm.
    easy.
Qed.

Theorem bw_thin {a b : bw} (f g : a ⟶ b) : f ≅ g.
Proof.
  pose proof ((toNf_natiso).(component_iso_natural) f) as Hf.
  rewrite compose_iso_r in Hf.
  pose proof ((toNf_natiso).(component_iso_natural) g) as Hg.
  rewrite compose_iso_r in Hg.
  simpl in *.
  unfold id in *.
  rewrite Hf, Hg.
  rewrite bwarr_compose_cancel_r_iff,
    bwarr_compose_cancel_l_iff.
  clear Hf Hg.
  unfold Nf_bwcat_functor_obligation_1.
  pose proof (bwbrac_eq_of_arr f norm_e) as H.
  destruct (eqbwnorm (Nf a) (Nf b)); [|easy].
  easy.
Qed.

Section MonoidalCoherence.

Context {cC : Category X} {cCh : CategoryCoherence cC}
  {mC : MonoidalCategory cC} {mCh : MonoidalCategoryCoherence mC}.

Local Open Scope Cat_scope.

Fixpoint realize_bw (a : bw) : X := 
  match a with
  | e => mC.(mon_I)
  | var x => x
  | tens a' b' => mC.(obj_tensor) (realize_bw a') (realize_bw b')
  end.

Coercion realize_bw : bw >-> X.

Existing Instance cC | 0.
Existing Instance mC | 0.


Fixpoint realize_bwarr {A B} (h : A ⟶ B) : (realize_bw A ~> realize_bw B) :=
  match h with
  | arrid a => cC.(c_identity) a
  | arrassoc a b c => (mC.(associator) a b c)^-1
  | arrinvassoc a b c => (mC.(associator) a b c)
  | arrlunitor a => mC.(left_unitor) a
  | arrinvlunitor a => (mC.(left_unitor) a)^-1
  | arrrunitor a => mC.(right_unitor) a
  | arrinvrunitor a => (mC.(right_unitor) a)^-1
  | arrcomp f g => (realize_bwarr f) ∘ (realize_bwarr g)
  | arrtens f g => (realize_bwarr f) ⊗ (realize_bwarr g)
  end.

Obligation Tactic := Tactics.program_simpl; simpl; eauto 3 with bwarrdb; try easy.



#[export, program] Instance RealizationFunctor : 
  Functor bwcat cC := {
  obj_map := realize_bw;
  morphism_map := @realize_bwarr;
}.
Next Obligation.
  induction H; [easy|..]; simpl; 
    rewrite ?iso_inv_l, ?iso_inv_r;
    try ((idtac + symmetry); solve [eauto using assoc, compose_compat, 
      left_unit, right_unit, tensor_id, tensor_compose, tensor_compat,
      associator_cohere, left_unitor_cohere, right_unitor_cohere,
      (equiv_refl _ _ c_equiv_rel); try easy]).
    - etransitivity; eauto.
    - rewrite <- compose_iso_l', <- assoc, <- compose_iso_r.
      symmetry. 
      apply associator_cohere.
    - symmetry. rewrite <- compose_iso_l', <- assoc, <- compose_iso_r.
      symmetry. 
      apply associator_cohere.
    - rewrite <- left_unit, <- assoc.
      rewrite <- 2!compose_iso_r'.
      rewrite !assoc.
      rewrite <- pentagon.
      rewrite <- 2!(assoc (α_ realize_bw a, b, c ⁻¹ ⊗ id_ realize_bw d)).
      rewrite <- tensor_compose, iso_inv_l, right_unit, tensor_id, left_unit.
      cancel_isos.
      now rewrite <- tensor_compose, iso_inv_l, left_unit, tensor_id.
    - symmetry. 
      rewrite <- left_unit, <- assoc.
      rewrite <- 2!compose_iso_r'.
      rewrite !assoc.
      rewrite <- pentagon.
      rewrite <- !(assoc (α_ realize_bw a, b, c ⁻¹ ⊗ id_ realize_bw d)).
      rewrite <- tensor_compose, iso_inv_l, right_unit, tensor_id, left_unit.
      cancel_isos.
      now rewrite <- tensor_compose, iso_inv_l, left_unit, tensor_id.
    - rewrite <- triangle.
      now cancel_isos.
    - rewrite <- triangle.
      now cancel_isos.
Qed.


Theorem monoidal_coherence {a b : bw} (f g : a ⟶ b) :
  realize_bwarr f ≃ realize_bwarr g.
Proof.
  apply RealizationFunctor.(morphism_compat).
  apply bw_thin.
Qed.

Definition real_arr := @realize_bwarr.
Arguments real_arr {_ _} _ : simpl never.

Notation "'[' f '≃' g ']'" := (real_arr f ≃ real_arr g) (at level 200,
  f at level 69, g at level 200) : Cat_scope.

Theorem monoidal_coherence' {a b : bw} (f g : a ⟶ b) :
  [ f ≃ g ].
Proof.
  apply monoidal_coherence.
Qed.

Section MonoidalExpressionNormalForm.

Inductive monarr : bw -> bw -> Type :=
  | monarrcomp {a b c : bw} (f : monarr a b) (g : monarr b c) : monarr a c
  | monarrtens {a a' b b'} (f : monarr a a') (g : monarr b b') : monarr (a ⨂ b) (a' ⨂ b')
  | mongeneric {a b : bw} (f : cC.(morphism) a b) : monarr a b
  | monarrstruct {a b : bw} (f : bwarr a b) : monarr a b.

Coercion monarrstruct : bwarr >-> monarr.
Local Notation "a '⟶' b" := (monarr a b) (at level 60) : type_scope.

Reserved Notation "f '≊' g" (at level 70).
Inductive monarrequiv : forall a b, relation (a ⟶ b) :=
  | monarr_refl {a b} (f : a ⟶ b) : f ≊ f
  | monarr_symm {a b} (f g : a ⟶ b) : f ≊ g -> g ≊ f
  | monarr_trans {a b} (f g h : a ⟶ b) : f ≊ g -> g ≊ h -> f ≊ h
  
  | monarr_comp {a b c : bw} (f f' : a ⟶ b) (g g' : b ⟶ c) :
      f ≊ f' -> g ≊ g' -> monarrcomp f g ≊ monarrcomp f' g'
  | monarr_assoc {a a' b' b : bw} (f : a ⟶ a') (g : a' ⟶ b') (h : b' ⟶ b) :
      monarrcomp f (monarrcomp g h) ≊ monarrcomp (monarrcomp f g) h
  (* | bwarr_lassoc {a a' b' b : bw} (f : a ⟶ a') (g : a' ⟶ b') (h : b' ⟶ b) :
      monarrcomp (monarrcomp f g) h ≊ monarrcomp f (monarrcomp g h) *)
  | monarr_lunit {a b} (f : a ⟶ b) : monarrcomp (arrid a) f ≊ f
  (* | bwarr_lunitr {a b} (f : a ⟶ b) : f ≊ monarrcomp (arrid a) f *)
  | monarr_runit {a b} (f : a ⟶ b) : monarrcomp f (arrid b) ≊ f
  (* | bwarr_runitr {a b} (f : a ⟶ b) : f ≊ monarrcomp f (arrid b) *)

  | monarr_tens {a a' b b' : bw} (f f' : a ⟶ a') (g g' : b ⟶ b') :
    f ≊ f' -> g ≊ g' -> monarrtens f g ≊ monarrtens f' g'
  | monarr_tens_comp {a b c a' b' c'} 
    (f : a ⟶ b) (g : b ⟶ c) (f' : a' ⟶ b') (g' : b' ⟶ c') :
    monarrtens (monarrcomp f g) (monarrcomp f' g') 
      ≊ monarrcomp (monarrtens f f') (monarrtens g g')
  | monarr_struct {a b} (f g : bwarr a b) : 
    (* bwarrequiv a b f g -> *)  (* NOTE: this is given by monoidal coherence! *)
      f ≊ g
  | monarr_arrcomp {a b c} (f : bwarr a b) (g : bwarr b c) :
      monarrcomp f g ≊ arrcomp f g
  | monarr_arrtens {a a' b b'} (f : bwarr a a') (g : bwarr b b') :
      monarrtens f g ≊ arrtens f g
  (* TODO: Add monarr_generic (equiv in cC means equiv here) (this is a 
      maybe; check if it makes the reasoning horrible or not) and 
      monarr_comp_generic / monarr_tens_generic that align cC (mC) ops with
      our formal ones (allows fine-tuning of processing, e.g. foliation).
      Also, consider the same for mongeneric (realize_bwarr f) to monstruct f? *)
  | monarr_assoc_nat {a b c a' b' c' : bw} 
    (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
    monarrcomp (arrassoc a b c) (monarrtens (monarrtens f g) h)
    ≊ monarrcomp (monarrtens f (monarrtens g h)) (arrassoc a' b' c')
  
  | monarr_lunitor_nat {a b : bw} (f : a ⟶ b) :
    monarrcomp (arrlunitor a) f ≊ monarrcomp (monarrtens (arrid e) f) (arrlunitor b)
  
  | monarr_runitor_nat {a b : bw} (f : a ⟶ b) :
    monarrcomp (arrrunitor a) f ≊ monarrcomp (monarrtens f (arrid e)) (arrrunitor b)
    
  where "f '≊' g" := (monarrequiv _ _ f g).

Add Parametric Relation (a b : bw) : (monarr a b) (monarrequiv a b)
  reflexivity proved by monarr_refl
  symmetry proved by monarr_symm
  transitivity proved by monarr_trans as monarrequiv_setoid.

Add Parametric Morphism (a b c : bw) : (@monarrcomp a b c)
  with signature 
  (monarrequiv a b) ==> (monarrequiv b c) ==> (monarrequiv a c)
  as monarrcomp_mor.
Proof. eauto using monarrequiv. Qed.

Add Parametric Morphism (a a' b b' : bw) : (@monarrtens a a' b b')
  with signature 
  (monarrequiv a a') ==> (monarrequiv b b') ==> (monarrequiv (a⨂b) (a'⨂b'))
  as monarrtens_mor.
Proof. eauto using monarrequiv. Qed.


Section monbwcat_Category.

Definition monbwcat : Category bw := {|
  morphism := monarr;
  c_equiv := monarrequiv;
  compose := fun _ _ _ => monarrcomp;
  c_identity := arrid;
|}.

#[local] Existing Instance monbwcat | 9.

#[export, program] Instance monbwcath : CategoryCoherence monbwcat.
Next Obligation.
split; apply monarrequiv_setoid.
Qed.
Obligation Tactic := 
  Tactics.program_simpl; eauto 4 using monarrequiv with bwarrdb; try easy.
Solve All Obligations.

#[export, program] Instance monassoc_iso (a b c : bw) 
  : Isomorphism (a ⨂ b ⨂ c) (a ⨂ (b ⨂ c)) := {
  forward := monarrstruct (arrinvassoc a b c);
  reverse := arrassoc a b c;
}.

#[export, program] Instance monlunitor_iso (a : bw) 
  : Isomorphism (e ⨂ a) a := {
  forward := monarrstruct (arrlunitor a);
  reverse := arrinvlunitor a;
}.

#[export, program] Instance monrunitor_iso (a : bw) 
  : Isomorphism (a ⨂ e) a := {
  forward := arrrunitor a;
  reverse := arrinvrunitor a;
}.

#[export] Instance monbwmcat : MonoidalCategory monbwcat | 10 := {
  obj_tensor := tens;
  mor_tensor := @monarrtens;
  associator := monassoc_iso;
  left_unitor := monlunitor_iso;
  right_unitor := monrunitor_iso;
}.

#[export, program] Instance monbwmcath : MonoidalCategoryCoherence bwmcat := {}.

Fixpoint realize_monarr {A B} (h : A ⟶ B) : (realize_bw A ~> realize_bw B) :=
  match h with
  | monarrcomp f g => realize_monarr f ∘ realize_monarr g
  | monarrtens f g => realize_monarr f ⊗ realize_monarr g
  | mongeneric f => f
  | monarrstruct f => realize_bwarr f
  end.


#[export, program] Instance GeneralRealizationFunctor : 
  Functor monbwcat cC := {
  obj_map := realize_bw;
  morphism_map := @realize_monarr;
}.
Next Obligation.
  induction H; try reflexivity; simpl.
  - symmetry; easy.
  - etransitivity; eauto.
  - apply compose_compat; auto.
  - symmetry; apply assoc.
  - apply left_unit.
  - apply right_unit.
  - apply tensor_compat; easy.
  - apply tensor_compose.
  - apply monoidal_coherence.
  - rewrite <- compose_iso_l', <- assoc, associator_cohere.
    rewrite assoc, iso_inv_r, right_unit.
    easy.
  - apply left_unitor_cohere.
  - apply right_unitor_cohere. 
Qed.

Definition realize_equiv (a b : bw) (f g : a ⟶ b) :=
  realize_monarr f ≃ realize_monarr g.

Arguments realize_equiv _ _ _ _/.

Local Notation "f '≡' g" := (realize_equiv _ _ f g) (at level 70).

Add Parametric Relation (a b : bw) : (monarr a b) (realize_equiv a b)
  reflexivity proved by 
    ltac:(intros ?; simpl; reflexivity)
  symmetry proved by 
    ltac:(intros ?; simpl; symmetry; easy)
  transitivity proved by 
    ltac:(intros ?; simpl; etransitivity; eauto) 
    as realize_equiv_setoid.

Add Parametric Morphism (a b c : bw) : (@monarrcomp a b c)
  with signature 
  (realize_equiv a b) ==> (realize_equiv b c) ==> (realize_equiv a c)
  as monarrcomp_mor_real.
Proof. intros; apply compose_compat; easy. Qed.

Add Parametric Morphism (a a' b b' : bw) : (@monarrtens a a' b b')
  with signature 
  (realize_equiv a a') ==> (realize_equiv b b') ==> (realize_equiv (a⨂b) (a'⨂b'))
  as monarrtens_mor_real.
Proof. intros; apply tensor_compat; easy. Qed.

Lemma realize_monarr_proper {a b} (f : a ⟶ b) : 
  f ≡ (mongeneric (realize_monarr f)).
Proof.
  induction f; simpl; easy.
Qed.


Section VarListNf.

Import List ListNotations.

Local Open Scope list_scope.

Fixpoint bw_to_varlist (b : bw) : list X :=
  match b with
  | e => nil
  | var x => x::nil
  | tens a b => bw_to_varlist b ++ bw_to_varlist a
  end.

Fixpoint bwnorm_to_varlist (n : bwnorm) : list X :=
  match n with
  | norm_e => nil
  | norm_rtens m a => a :: bwnorm_to_varlist m
  end.

Fixpoint varlist_to_bwnorm (l : list X) : bwnorm :=
  match l with
  | nil => norm_e
  | a :: l' => norm_rtens (varlist_to_bwnorm l') a
  end.

Fixpoint bwnormapp (n m : bwnorm) {struct m} : bwnorm := 
  match m with
  | norm_e => n
  | norm_rtens m' a => norm_rtens (bwnormapp n m') a
  end.

Lemma varlist_to_bwnorm_app (l l' : list X) :
  varlist_to_bwnorm (l ++ l') = 
  bwnormapp (varlist_to_bwnorm l') (varlist_to_bwnorm l).
Proof.
  induction l; [easy|].
  now simpl; f_equal.
Qed.

Lemma Nf_tens (b c : bw) : 
  Nf (b ⨂ c) = ⟦c⟧ (Nf b).
Proof.
  easy.
Qed.

Lemma Nf_tens_assoc (b c d : bw) : 
  Nf (b ⨂ (c ⨂ d)) = Nf (b ⨂ c ⨂ d).
Proof.
  easy.
Qed.

Lemma bwnormapp_lnorme (n : bwnorm) : 
  bwnormapp norm_e n = n.
Proof.
  now induction n; auto; simpl; f_equal.
Qed.

Lemma bwnormapp_assoc (n m o : bwnorm) : 
  bwnormapp n (bwnormapp m o) = bwnormapp (bwnormapp n m) o.
Proof.
  induction o; [easy|].
  now simpl; f_equal.
Qed.

Lemma Nf_tens_bwnormapp (b c : bw) : 
  Nf (b ⨂ c) = bwnormapp (Nf b) (Nf c).
Proof.
  revert b; induction c; intros b; [easy..|].
  rewrite Nf_tens_assoc.
  rewrite Nf_tens, IHc1, IHc2.
  rewrite bwnormapp_assoc.
  rewrite <- IHc1, <- IHc2.
  easy.
Qed.
  

Lemma Nf_eq_bwnorm_of_varlist (b : bw) :
  Nf b = varlist_to_bwnorm (bw_to_varlist b).
Proof.
  induction b as [|a|b IHb c IHc]; [easy.. |].
  rewrite Nf_tens_bwnormapp.
  simpl.
  rewrite varlist_to_bwnorm_app.
  now f_equal.
Qed.

Fixpoint to_Nf_arr_aux (a : bw) (b : bwnorm) : 
  bwarr (b ⨂ a) (⟦a⟧ b) := 
  match a with
  | e => arrrunitor _
  | var x => arrid _
  | tens a1 a2 => 
      (arrassoc _ _ _) ○ 
      ((to_Nf_arr_aux a1 b) ⊠ (arrid a2)) ○
      (to_Nf_arr_aux a2 (⟦a1⟧ b))
  end.

Definition to_Nf_arr (a : bw) : bwarr a (Nf a) :=
  (arrinvlunitor a) ○ (to_Nf_arr_aux a norm_e).

Definition from_Nf_arr (a : bw) : bwarr (Nf a) a :=
   (bwarrinv (to_Nf_arr_aux a norm_e)) ○ (arrlunitor a).

Inductive monarrlistelt :=
  | monarrlist_id (a : bw) : monarrlistelt
  | monarrlist_arr (a b : bw) (f : a ⟶ b) : monarrlistelt.

Definition source (f : monarrlistelt) : bw := 
  match f with
  | monarrlist_id a => a
  | monarrlist_arr a b g => a
  end.

Definition target (f : monarrlistelt) : bw := 
  match f with
  | monarrlist_id a => a
  | monarrlist_arr a b g => b
  end.

Definition realize_monarrlistelt (f : monarrlistelt) : 
  monarr (source f) (target f) :=
  match f with
  | monarrlist_id a => arrid a
  | monarrlist_arr a b g => g
  end.

Local Notation monarrlist := (list monarrlistelt).

Definition monarrlist_source (f : monarrlist) : bw :=
  fold_right (fun a n => tens n a) e (map source f).

Definition monarrlist_target (f : monarrlist) : bw :=
  fold_right (fun a n => tens n a) e (map target f).

(* FIXME: change this name to something accurate (namely, not 'realize') *)
Fixpoint realize_monarrlist (f : monarrlist) : 
  monarr (monarrlist_source f) (monarrlist_target f) :=
  match f with
  | nil => arrid norm_e
  | mae :: f' => 
      monarrtens 
        (realize_monarrlist f') 
        (realize_monarrlistelt mae)
  end.

Definition composable (fs gs : monarrlist) :=
  Nf (monarrlist_target fs) = Nf (monarrlist_source gs).

Lemma Nf_eq_iff_bweq (a b : bw) : 
  Nf a = Nf b <-> a ~ b.
Proof.
  split.
  - intros Heq.
    transitivity (Nf a).
    1: apply bweq_Nf.
    rewrite Heq.
    symmetry.
    apply bweq_Nf.
  - rewrite bweq_iff_ex_arr.
    intros [f _].
    unfold Nf.
    apply bwbrac_eq_of_arr; easy.
Qed.

Lemma composable_iff_bweq (fs gs : monarrlist) :
  composable fs gs <-> bweq (monarrlist_target fs) (monarrlist_source gs).
Proof.
  apply Nf_eq_iff_bweq.
Qed.

Definition is_composable (fs gs : monarrlist) : 
  {composable fs gs} + {~ composable fs gs} :=
  eqbwnorm (Nf (monarrlist_target fs)) (Nf (monarrlist_source gs)).

Local Open Scope list_scope.
Local Close Scope Cat_scope.

Fixpoint pairify_helper (facc gacc fs gs : monarrlist) : 
  list (monarrlist * monarrlist) :=
  match fs, gs with 
  | nil, gs' => (facc, gacc ++ gs') :: nil
  | fs', nil => (facc ++ fs', gacc) :: nil
  | f::fs', g::gs' => 
      let facc' := facc ++ [f] in 
      let gacc' := gacc ++ [g] in 
      if (is_composable facc' gacc') 
      then (facc', gacc') :: pairify_helper [] [] fs' gs'
      else pairify_helper facc' gacc' fs' gs'
  end.

Definition pairify (fs gs : monarrlist) := 
  pairify_helper [] [] fs gs.

Lemma varlist_to_bwnorm_inj (a b : list X) : 
  varlist_to_bwnorm a = varlist_to_bwnorm b -> a = b.
Proof.
  revert b;
  induction a; intros b.
  - destruct b; easy.
  - destruct b; [easy|].
    simpl. 
    intros H.
    inversion H; subst.
    erewrite IHa by eassumption.
    easy.
Qed.

Lemma varlist_to_bwnorm_eq_iff (a b : list X) : 
  varlist_to_bwnorm a = varlist_to_bwnorm b <-> a = b.
Proof.
  split.
  - apply varlist_to_bwnorm_inj.
  - intros; subst; easy.
Qed.

Lemma Nf_eq_iff_varlist_eq (a b : bw) : 
  Nf a = Nf b <-> bw_to_varlist a = bw_to_varlist b.
Proof.
  rewrite 2!Nf_eq_bwnorm_of_varlist.
  apply varlist_to_bwnorm_eq_iff.
Qed.

Lemma bw_to_varlist_fold_right (fs : list bw) :
  bw_to_varlist (fold_right (fun a n => n ⨂ a) e fs) = 
  concat (map bw_to_varlist fs).
Proof.
  induction fs; [easy|].
  simpl.
  f_equal.
  easy.
Qed.

Definition source_vars (fs : monarrlist) := 
  flat_map (Basics.compose bw_to_varlist source) fs.

Definition target_vars (fs : monarrlist) := 
  flat_map (Basics.compose bw_to_varlist target) fs.

Lemma composable_iff_varlist_eq (fs gs : monarrlist) : 
  composable fs gs <-> target_vars fs = source_vars gs.
Proof.
  unfold composable.
  rewrite Nf_eq_iff_varlist_eq.
  unfold monarrlist_target, monarrlist_source.
  rewrite 2!bw_to_varlist_fold_right.
  rewrite 2!map_map.
  rewrite <- 2!flat_map_concat_map.
  easy.
Qed.

Lemma composable_of_app_composable {fs fs' gs gs' : monarrlist} : 
  composable (fs ++ fs') (gs ++ gs') ->
  composable fs gs -> composable fs' gs'.
Proof.
  rewrite 3!composable_iff_varlist_eq.
  unfold source_vars, target_vars.
  rewrite 2!flat_map_app.
  intros H H'.
  rewrite H' in H.
  apply app_inv_head in H.
  easy.
Qed.

Lemma pairify_helper_composable (facc gacc fs gs : monarrlist) 
  (H : composable (facc ++ fs) (gacc ++ gs)) :
  Forall (uncurry composable) (pairify_helper facc gacc fs gs).
Proof.
  revert gs facc gacc H;
  induction fs as [| f fs' Hfs]; 
  intros gs facc gacc H;
  [|destruct gs as [|g gs']].
  - constructor; [|easy].
    rewrite app_nil_r in H.
    apply H.
  - constructor; [|easy].
    rewrite app_nil_r in H.
    apply H.
  - simpl. 
    destruct (is_composable (facc ++ [f]) (gacc ++ [g])) as [Hc | Hnc]. 
    + constructor.
      * apply Hc.
      * apply Hfs. revert Hc.
        apply composable_of_app_composable.
        rewrite <- 2!app_assoc.
        apply H.
    + apply Hfs.
      rewrite <- 2!app_assoc.
      apply H.
Qed.

Lemma pairify_composable (fs gs : monarrlist) : 
  composable fs gs ->
  Forall (uncurry composable) (pairify fs gs).
Proof.
  intros H. 
  apply pairify_helper_composable.
  apply H.
Qed.

Definition is_idarr (fs : monarrlistelt) :=
  match fs with
  | monarrlist_id _ => true
  | monarrlist_arr _ _ _ => false
  end.

Definition is_idarrlist (fs : monarrlist) :=
  forallb is_idarr fs.

Definition idarr_of_vars (xs : list X) : monarrlist :=
  map (fun x => monarrlist_id (var x)) xs.

Definition shift_left (fs gs : monarrlist) := 
  if is_idarrlist fs then 
  (gs, idarr_of_vars (target_vars gs))
  else (fs, gs).

Definition shift_right (fs gs : monarrlist) := 
  if is_idarrlist gs then 
  (idarr_of_vars (source_vars fs), fs)
  else (fs, gs).



Definition bwarr_id_cast {a b : bw} (H : a = b) : bwarr a b := 
  eq_rect_r (fun a' => bwarr a' b) (arrid b) H.

Definition monarr_id_cast_norm {a b : bwnorm} (H : a = b) : monarr a b := 
  (eq_rect_r (fun a' => bwarr (bwnorm_to_bw a') b) (arrid b) H).

Definition bwarr_id_cast_norm {a b : bwnorm} (H : a = b) : bwarr a b := 
  (eq_rect_r (fun a' => bwarr (bwnorm_to_bw a') b) (arrid b) H).
  
Definition monarr_of_Nf_eq {a b : bw} (H : Nf a = Nf b) : 
  bwarr a b :=
    (to_Nf_arr a) ○
    (bwarr_id_cast_norm H) ○
    (from_Nf_arr b).

(* Definition monarr_composer_of_composable (fs gs : monarrlist) 
  (H : composable fs gs) :=
  monarrcomp (monarrcomp
    (realize_monarrlist fs) 
    (monarr_of_Nf_eq H))
    (realize_monarrlist gs).

Definition maybe_compose (fs gs : monarrlist) : 
  option (monarr (monarrlist_source fs) (monarrlist_target gs)) :=
  match is_composable fs gs with
  | left H => Some (monarr_composer_of_composable fs gs H)
  | right _ => None
  end. *)

Definition monarr_composer_of_composable {a a' b b'}
  (f : a ⟶ a') (g : b ⟶ b') 
  (H : Nf a' = Nf b) :=
  monarrcomp (monarrcomp
    (f) 
    (monarr_of_Nf_eq H))
    (g).

Definition monarrlist_composer_of_composable (fs gs : monarrlist)
  (H : composable fs gs) :=
  monarrcomp (monarrcomp
    (realize_monarrlist fs) 
    (monarr_of_Nf_eq H))
    (realize_monarrlist gs).

Definition maybe_compose (fs gs : monarrlist) : 
  option (monarr (monarrlist_source fs) (monarrlist_target gs)) :=
  match is_composable fs gs with
  | left H => Some 
    (monarrlist_composer_of_composable fs gs H)
  | right _ => None
  end.

Definition maybe_compose_monarrs {a a' b b'}
  (f : a ⟶ a') (g : b ⟶ b') :
  option (a ⟶ b') :=
  match eqbwnorm (Nf a') (Nf b) with
  | left H => Some 
    (monarr_composer_of_composable f g H)
  | right _ => None
  end.



Lemma composable_independence {fs gs : monarrlist} (H H' : composable fs gs) :
  H = H'.
Proof. 
  apply Eqdep_dec.UIP_dec, eqbwnorm.
Qed.

Lemma maybe_compose_composable {fs gs : monarrlist} (H : composable fs gs) :
  maybe_compose fs gs = 
  Some (monarrlist_composer_of_composable fs gs H).
Proof.
  unfold maybe_compose.
  destruct (is_composable fs gs); [|easy].
  rewrite (composable_independence H c).
  easy.
Qed.

Lemma maybe_compose_monarrs_composable {a a' b b'}
  (f : a ⟶ a') (g : b ⟶ b') (H : Nf a' = Nf b):
  maybe_compose_monarrs f g = 
  Some (monarr_composer_of_composable f g H).
Proof.
  unfold maybe_compose_monarrs.
  destruct (eqbwnorm (Nf a') (Nf b)) as [c|]; [|easy].
  erewrite (Eqdep_dec.UIP_dec eqbwnorm H c).
  easy.
Qed.

Definition monarr_norm_equiv {a a' b b' : bw}
  (f : monarr a a') (g : monarr b b') : Prop :=
  match eqbwnorm (Nf b) (Nf a) with
  | right _ => False
  | left Heq_in => match eqbwnorm (Nf a') (Nf b') with
    | right _ => False
    | left Heq_out =>
      monarrcomp (monarrcomp
        (monarr_of_Nf_eq Heq_in)
        f)
        (monarr_of_Nf_eq Heq_out)
        ≊ g
    end end.

Lemma Nf_eq_in_of_norm_equiv {a a' b b' : bw}
  {f : monarr a a'} {g : monarr b b'} :
  monarr_norm_equiv f g -> Nf a = Nf b.
Proof.
  unfold monarr_norm_equiv.
  destruct (eqbwnorm (Nf b) (Nf a)); easy.
Qed.

Lemma Nf_eq_out_of_norm_equiv {a a' b b' : bw}
  {f : monarr a a'} {g : monarr b b'} :
  monarr_norm_equiv f g -> Nf a' = Nf b'.
Proof.
  unfold monarr_norm_equiv.
  destruct (eqbwnorm (Nf b) (Nf a)); [|easy].
  destruct (eqbwnorm (Nf a') (Nf b')); easy.
Qed.

Definition unary_monarrlist_op_proper (f : monarrlist -> monarrlist) : Prop :=
  forall fs : monarrlist, monarr_norm_equiv 
  (realize_monarrlist (f fs)) (realize_monarrlist fs).

Definition option_2map {A B C} (f : A -> B -> C) 
  (a : option A) (b : option B) :=
  match a, b with
    | Some a', Some b' => Some (f a' b')
    | _, _ => None
    end.

Definition option_rel_map {A B} (f : A -> B -> Prop) 
  (a : option A) (b : option B) :=
  match (option_2map f a b) with
  | Some P => P
  | None => False
  end.

Arguments option_rel_map {_ _} _ !_ !_ /.

Definition binary_monarrlist_op_proper 
  (f : monarrlist -> monarrlist -> monarrlist * monarrlist) : Prop :=
  forall fs gs : monarrlist, composable fs gs ->
  let '(fs', gs') := f fs gs in 
  option_rel_map monarr_norm_equiv 
  (maybe_compose fs gs) (maybe_compose fs' gs').


Lemma source_idarr_of_vars (xs : list X) : 
  source_vars (idarr_of_vars xs) = xs.
Proof.
  induction xs; [easy|].
  simpl; f_equal; easy.
Qed.

Lemma target_idarr_of_vars (xs : list X) : 
  target_vars (idarr_of_vars xs) = xs.
Proof.
  induction xs; [easy|].
  simpl; f_equal; easy.
Qed.

Lemma composable_idarr_of_target (fs : monarrlist) : 
  composable fs (idarr_of_vars (target_vars fs)).
Proof.
  rewrite composable_iff_varlist_eq.
  now rewrite source_idarr_of_vars.
Qed.

Lemma composable_idarr_of_source (fs : monarrlist) : 
  composable (idarr_of_vars (source_vars fs)) fs.
Proof.
  rewrite composable_iff_varlist_eq.
  now rewrite target_idarr_of_vars.
Qed.

Lemma monarr_of_Nf_eq_id (a : bw) (H : Nf a = Nf a) : 
  monarr_of_Nf_eq H ≊ arrid a.
Proof.
  apply monarr_struct.
Qed.

Lemma monarr_norm_equiv_refl {a b : bw} : 
  reflexive _ (@monarr_norm_equiv a b a b).
Proof.
  intros f.
  unfold monarr_norm_equiv.
  destruct (eqbwnorm (Nf a) (Nf a)); [|easy];
  destruct (eqbwnorm (Nf b) (Nf b)); [|easy].
  rewrite 2!monarr_of_Nf_eq_id, monarr_lunit, monarr_runit.
  easy.
Qed.

Lemma monarr_norm_equiv_symm {a a' b b' : bw} 
  (f : monarr a a') (g : monarr b b') : 
  monarr_norm_equiv f g -> monarr_norm_equiv g f.
Proof.
  unfold monarr_norm_equiv.
  destruct (eqbwnorm (Nf b) (Nf a)) as [Hba | ?];
  destruct (eqbwnorm (Nf a) (Nf b)) as [? | ?]; try congruence;
  destruct (eqbwnorm (Nf b') (Nf a')) as [Hba' | ?];
  destruct (eqbwnorm (Nf a') (Nf b')) as [? | ?]; 
  try congruence.
  intros H.
  rewrite <- H.
  rewrite <- (monarr_assoc _ f), (monarr_assoc (monarr_of_Nf_eq _)).
  rewrite !monarr_arrcomp.
  rewrite (monarr_struct _ (arrid a)), monarr_lunit.
  rewrite <- (monarr_assoc f), monarr_arrcomp.
  rewrite (monarr_struct _ (arrid a')), monarr_runit.
  easy.
Qed.

Lemma monarr_norm_equiv_symmetric {a a' b b' : bw} 
  (f : monarr a a') (g : monarr b b') : 
  monarr_norm_equiv f g <-> monarr_norm_equiv g f.
Proof.
  split; apply monarr_norm_equiv_symm.
Qed.

Lemma monarr_norm_equiv_trans {a a' b b' c c' : bw} 
  {f : monarr a a'} {g : monarr b b'} {h : monarr c c'} :
  monarr_norm_equiv f g -> monarr_norm_equiv g h ->
  monarr_norm_equiv f h.
Proof.
  rewrite (monarr_norm_equiv_symmetric f g), 
    (monarr_norm_equiv_symmetric g h).
  unfold monarr_norm_equiv.
  destruct (eqbwnorm (Nf b) (Nf a)) as [Hba | ?];
  destruct (eqbwnorm (Nf a) (Nf b)) as [? | ?]; try congruence;
  destruct (eqbwnorm (Nf b') (Nf a')) as [Hba' | ?];
  destruct (eqbwnorm (Nf a') (Nf b')) as [? | ?]; try congruence;
  destruct (eqbwnorm (Nf c) (Nf a)) as [Hca | ?];
  destruct (eqbwnorm (Nf a) (Nf c)) as [? | ?]; try congruence;
  destruct (eqbwnorm (Nf c') (Nf a')) as [Hca' | ?];
  destruct (eqbwnorm (Nf a') (Nf c')) as [? | ?]; try congruence;
  destruct (eqbwnorm (Nf c) (Nf b)) as [Hcb | ?];
  destruct (eqbwnorm (Nf b) (Nf c)) as [? | ?]; try congruence;
  destruct (eqbwnorm (Nf c') (Nf b')) as [Hcb' | ?];
  destruct (eqbwnorm (Nf b') (Nf c')) as [? | ?]; 
  try congruence; try (intros; exfalso; assumption).
  intros Hfg Hgh.
  rewrite <- Hfg, <- Hgh.
  rewrite !monarr_assoc, !monarr_arrcomp, (monarr_struct _ (arrid _)).
  rewrite monarr_lunit.
  rewrite <- !monarr_assoc, !monarr_arrcomp, (monarr_struct _ (arrid _)).
  rewrite monarr_runit.
  easy.
Qed.

Lemma monarr_norm_equiv_comp {a a' a'' b b' b''} 
  (f : monarr a a') (f' : monarr a' a'') 
  (g : monarr b b') (g' : monarr b' b'') : 
  monarr_norm_equiv f g ->
  monarr_norm_equiv f' g' ->
  monarr_norm_equiv (monarrcomp f f') (monarrcomp g g'). 
Proof.
  unfold monarr_norm_equiv.
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab
  end; try congruence; try (intros; exfalso; assumption).
  intros Hfg Hfg'.
  rewrite <- Hfg, <- Hfg'.
  symmetry.
  rewrite !(monarr_assoc (monarrcomp _ _)).
  rewrite <- (monarr_assoc _ (monarr_of_Nf_eq _) (monarr_of_Nf_eq _)).
  rewrite monarr_arrcomp, (monarr_struct _ (arrid _)), monarr_runit.
  rewrite !monarr_assoc.
  easy.
Qed.

Lemma monarr_norm_equiv_tens {a a' b b' c c' d d'} 
  (f : monarr a a') (f' : monarr b b') 
  (g : monarr c c') (g' : monarr d d') : 
  monarr_norm_equiv f g ->
  monarr_norm_equiv f' g' ->
  monarr_norm_equiv (monarrtens f f') (monarrtens g g'). 
Proof.
  unfold monarr_norm_equiv.
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab
  end; try congruence; try (intros; exfalso; assumption).
  2,3: intros _ _; 
    rewrite Nf_eq_iff_bweq in *;
    apply n;
    apply bw_tens; easy.  
  intros Hfg Hfg'.
  rewrite <- Hfg, <- Hfg'.
  symmetry.
  rewrite !monarr_tens_comp, !monarr_arrtens.
  apply monarr_comp; [apply monarr_comp|]; 
  reflexivity + apply monarr_struct.
Qed.

Lemma target_source_idarr_of_vars (xs : list X) :
  monarrlist_target (idarr_of_vars xs)
  = monarrlist_source (idarr_of_vars xs).
Proof.
  induction xs; [easy|].
  simpl.
  unfold monarrlist_target, monarrlist_source in *.
  simpl.
  f_equal; easy.
Qed.

Lemma source_target_idarr_of_vars (xs : list X) :
  monarrlist_source (idarr_of_vars xs)
  = monarrlist_target (idarr_of_vars xs).
Proof.
  now rewrite target_source_idarr_of_vars.
Qed.

Lemma realize_idarr (xs : list X) : 
  realize_monarrlist (idarr_of_vars xs) ≊ 
  bwarr_id_cast (source_target_idarr_of_vars xs).
Proof.
  induction xs; [apply monarr_struct|].
  simpl.
  rewrite IHxs.
  rewrite monarr_arrtens.
  apply monarr_struct.
Qed.

Lemma monarr_composer_of_composable_idarr_r 
  (gs : monarrlist) (xs : list X) (H : composable gs (idarr_of_vars xs)) : 
  monarr_norm_equiv 
    (realize_monarrlist gs)
    (monarrlist_composer_of_composable gs (idarr_of_vars xs) H).
Proof.
  unfold monarr_norm_equiv.
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab
  end; try congruence.
  2: {
    rewrite target_source_idarr_of_vars in *.
    easy.
  }
  unfold monarrlist_composer_of_composable.
  rewrite monarr_of_Nf_eq_id, monarr_lunit.
  rewrite <- monarr_assoc.
  apply monarr_comp; [easy|].
  rewrite realize_idarr.
  rewrite monarr_arrcomp.
  apply monarr_struct.
Qed.

Lemma monarr_composer_of_composable_idarr_l
  (gs : monarrlist) (xs : list X) (H : composable (idarr_of_vars xs) gs) : 
  monarr_norm_equiv 
    (realize_monarrlist gs)
    (monarrlist_composer_of_composable (idarr_of_vars xs) gs H).
Proof.
  unfold monarr_norm_equiv.
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab
  end; try congruence.
  2: {
    rewrite <- target_source_idarr_of_vars in *.
    easy.
  }
  unfold monarrlist_composer_of_composable.
  rewrite monarr_of_Nf_eq_id, monarr_runit.
  rewrite realize_idarr, monarr_arrcomp.
  apply monarr_comp; [|easy].
  apply monarr_struct.
Qed.

Lemma source_target_is_idarrlist (fs : monarrlist) 
  (H : is_idarrlist fs = true) :
  monarrlist_source fs
  = monarrlist_target fs.
Proof.
  induction fs as [|a fs IHfs]; [easy|].
  destruct a; [|easy].
  simpl in H.
  unfold monarrlist_source, monarrlist_target in *.
  simpl.
  f_equal; auto.
Qed.

Lemma realize_idarrlist (fs : monarrlist) 
  (H : is_idarrlist fs = true) :
  realize_monarrlist fs ≊ 
  bwarr_id_cast (source_target_is_idarrlist fs H). 
Proof.
  induction fs as [|a fs IHfs]; [apply monarr_struct|].
  simpl.
  destruct a; [|easy].
  simpl in H.
  rewrite (IHfs H).
  simpl.
  rewrite monarr_arrtens.
  apply monarr_struct.
Qed.

Add Parametric Morphism (a a' b b' : bw) : (@monarr_norm_equiv a a' b b')
  with signature 
  (monarrequiv a a') ==> (monarrequiv b b') ==> (iff)
  as monarr_norm_equiv_mor.
Proof.
  intros f f' Hf' g g' Hg'.
  unfold monarr_norm_equiv.
  destruct (eqbwnorm (Nf b) (Nf a)) as [Hba | ?];
  destruct (eqbwnorm (Nf a') (Nf b')) as [Hba' | ?]; try reflexivity.
  rewrite Hf', Hg'.
  easy.
Qed.

Lemma Nf_eq_of_arr {a b : bw} (f : bwarr a b) : Nf a = Nf b.
Proof.
  rewrite Nf_eq_iff_bweq.
  apply bweq_of_arr, f.
Qed.

Lemma monarr_norm_equiv_struct_l {a b c : bw} (f : bwarr a b) (g : monarr b c) : 
  monarr_norm_equiv (monarrcomp f g) g.
Proof.
  unfold monarr_norm_equiv.
  pose proof (Nf_eq_of_arr f).
  destruct (eqbwnorm (Nf b) (Nf a)); [|congruence].
  destruct (eqbwnorm (Nf c) (Nf c)); [|congruence].
  rewrite (monarr_struct _ (arrid _)), monarr_runit.
  rewrite monarr_assoc, monarr_arrcomp.
  rewrite (monarr_struct _ (arrid _)), monarr_lunit.
  easy.
Qed.


Lemma monarr_norm_equiv_struct_r {a b c : bw} (f : monarr a b) (g : bwarr b c) : 
  monarr_norm_equiv (monarrcomp f g) f.
Proof.
  unfold monarr_norm_equiv.
  pose proof (Nf_eq_of_arr g).
  destruct (eqbwnorm (Nf a) (Nf a)); [|congruence].
  destruct (eqbwnorm (Nf c) (Nf b)); [|congruence].
  rewrite (monarr_struct _ (arrid _)), monarr_lunit.
  rewrite <- monarr_assoc, monarr_arrcomp.
  rewrite (monarr_struct _ (arrid _)), monarr_runit.
  easy.
Qed.

Lemma shift_left_proper : binary_monarrlist_op_proper shift_left.
Proof.
  intros fs gs H.
  unfold shift_left.
  destruct (is_idarrlist fs) eqn:E;
  rewrite (maybe_compose_composable H);
  [|apply monarr_norm_equiv_refl].
  rewrite (maybe_compose_composable (composable_idarr_of_target gs)).
  simpl.
  apply (@monarr_norm_equiv_trans _ _ _ _ _ _ _ (realize_monarrlist gs)).
  2: apply monarr_composer_of_composable_idarr_r.
  unfold monarrlist_composer_of_composable.
  rewrite (realize_idarrlist _ E).
  rewrite monarr_arrcomp.
  apply monarr_norm_equiv_struct_l.
Qed.

Lemma shift_right_proper : binary_monarrlist_op_proper shift_right.
Proof.
  intros fs gs H.
  unfold shift_right.
  destruct (is_idarrlist gs) eqn:E;
  rewrite (maybe_compose_composable H);
  [|apply monarr_norm_equiv_refl].
  rewrite (maybe_compose_composable (composable_idarr_of_source fs)).
  simpl.
  apply (@monarr_norm_equiv_trans _ _ _ _ _ _ _ (realize_monarrlist fs)).
  2: apply monarr_composer_of_composable_idarr_l.
  unfold monarrlist_composer_of_composable.
  rewrite (realize_idarrlist _ E), <- monarr_assoc.
  rewrite monarr_arrcomp.
  apply monarr_norm_equiv_struct_r.
Qed.

Fixpoint is_struct {a b} (f : a ⟶ b) : bool := 
  match f with 
  | mongeneric _ => false
  | monarrstruct _ => true
  | monarrcomp f' g' => is_struct f' && is_struct g'
  | monarrtens f' g' => is_struct f' && is_struct g'
  end.

Import Bool.

Fixpoint struct_of_is_struct {a b} (f : a ⟶ b) 
  (H : is_struct f = true) : bwarr a b.
  destruct f.
  apply (arrcomp (struct_of_is_struct _ _ _ (proj1 (proj1 (andb_true_iff _ _) H)))
  (struct_of_is_struct _ _ _ (proj2 (proj1 (andb_true_iff _ _) H)))).
  apply (arrtens (struct_of_is_struct _ _ _ (proj1 (proj1 (andb_true_iff _ _) H)))
  (struct_of_is_struct _ _ _ (proj2 (proj1 (andb_true_iff _ _) H)))).
  discriminate H.
  apply f.
Defined.

Fixpoint structify {a b} (f : a ⟶ b) : a ⟶ b :=
  match f with
  | mongeneric f' => mongeneric f'
  | monarrstruct f' => monarrstruct f'
  | monarrcomp f' g' => 
      let fs := structify f' in 
      let gs := structify g' in 
      match bool_dec (is_struct fs) true with
      | right _ => monarrcomp fs gs
      | left Hfstruct => 
        match bool_dec (is_struct gs) true with
        | right _ => monarrcomp fs gs
        | left Hgstruct => 
          arrcomp 
            (struct_of_is_struct fs Hfstruct) 
            (struct_of_is_struct gs Hgstruct) 
        end
      end
  | monarrtens f' g' => 
      let fs := structify f' in 
      let gs := structify g' in 
      match bool_dec (is_struct fs) true with
      | right _ => monarrtens fs gs
      | left Hfstruct => 
        match bool_dec (is_struct gs) true with
        | right _ => monarrtens fs gs
        | left Hgstruct => 
          arrtens 
            (struct_of_is_struct fs Hfstruct) 
            (struct_of_is_struct gs Hgstruct) 
        end
      end
  end.

Lemma struct_of_is_struct_indep {a b} (f : a ⟶ b) 
  (H G : is_struct f = true) : 
  struct_of_is_struct f H = struct_of_is_struct f G.
Proof.
  rewrite (Eqdep_dec.UIP_dec bool_dec H G).
  easy.
Qed.

Lemma is_struct_structify {a b} (f : a ⟶ b) : 
  is_struct f = is_struct (structify f).
Proof.
  induction f; try reflexivity;
    simpl;
    destruct (bool_dec (is_struct (structify f1)) true);
    destruct (bool_dec (is_struct (structify f2)) true);
    simpl; try congruence;
    apply andb_true_iff; split; congruence.
Qed.

Lemma structify_of_is_struct {a b} (f : a ⟶ b) 
  (H : is_struct f = true) :
  structify f = struct_of_is_struct f H.
Proof.
  induction f; try reflexivity + discriminate;
  simpl in H;
  pose proof H as G;
  rewrite (andb_true_iff _ _) in G;
  destruct G as [Hl Hr];
  simpl structify;
  rewrite (IHf1 Hl), (IHf2 Hr);
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab; [|pose proof @is_struct_structify; congruence]
  end;
  simpl;
  erewrite struct_of_is_struct_indep, (struct_of_is_struct_indep f2);
  reflexivity.
Qed.

Lemma monarr_norm_equiv_of_monarrequiv {a b} 
  {f g : a ⟶ b} (H : f ≊ g) : 
  monarr_norm_equiv f g.
Proof.
  unfold monarr_norm_equiv.
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab; [|congruence]
  end.
  rewrite (monarr_struct _ (arrid _)), monarr_lunit.
  rewrite (monarr_struct _ (arrid _)), monarr_runit.
  easy.
Qed.

Lemma struct_of_is_struct_equiv {a b} (f : a ⟶ b) 
  (H : is_struct f = true) : 
  struct_of_is_struct f H ≊ f.
Proof.
  symmetry.
  induction f; [..|discriminate|reflexivity];
  pose proof H as G;
  simpl in G;
  rewrite andb_true_iff in G; destruct G as [Hl Hr];
  rewrite (IHf1 Hl), (IHf2 Hr) at 1;
  simpl;
  [ rewrite <- monarr_arrcomp
  | rewrite <- monarr_arrtens ];
  erewrite struct_of_is_struct_indep, (struct_of_is_struct_indep f2);
  reflexivity.
Qed.


Lemma structify_equiv {a b} (f : a ⟶ b) : 
  f ≊ structify f.
Proof.
  induction f; try reflexivity;
  rewrite IHf1, IHf2 at 1;
  simpl;
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab
  end; try reflexivity.
  - rewrite <- monarr_arrcomp.
    rewrite 2!struct_of_is_struct_equiv by easy.
    easy.
  - rewrite <- monarr_arrtens.
    rewrite 2!struct_of_is_struct_equiv by easy.
    easy.
Qed.

Definition monarrlistelt_map (f : forall a b : bw, a ⟶ b -> a ⟶ b) 
  (g : monarrlistelt) := 
  match g with
  | monarrlist_id a => monarrlist_id a
  | monarrlist_arr a b g' => monarrlist_arr a b (f a b g')
  end.


Definition structify_monarrlistelt (f : monarrlistelt) :=
  monarrlistelt_map (@structify) f.

Definition structify_monarrlist (fs : monarrlist) :=
  map structify_monarrlistelt fs.

Lemma map_proper_proper (f : monarrlistelt -> monarrlistelt) 
  (Hf : forall g, 
    monarr_norm_equiv 
      (realize_monarrlistelt (f g)) 
      (realize_monarrlistelt g)) :
  unary_monarrlist_op_proper
  (map f).
Proof.
  intros fs; induction fs;
  [apply monarr_norm_equiv_of_monarrequiv; easy|].
  simpl.
  apply monarr_norm_equiv_tens; [easy|].
  apply Hf.
Qed.


Lemma monarrlistelt_map_proper (f : forall a b : bw, a ⟶ b -> a ⟶ b)
  (Hf : forall {a b : bw} (g : a ⟶ b), g ≊ f a b g) : 
  unary_monarrlist_op_proper 
  (map (monarrlistelt_map f)).
Proof.
  apply map_proper_proper.
  intros g.
  destruct g; apply monarr_norm_equiv_of_monarrequiv; 
  simpl; easy.
Qed.

Lemma structify_proper : unary_monarrlist_op_proper structify_monarrlist.
Proof.
  apply monarrlistelt_map_proper.
  intros; apply structify_equiv.
Qed.

Definition remove_struct (g : monarrlistelt) :=
  match g with
  | monarrlist_id a => monarrlist_id a
  | monarrlist_arr a b f => 
      match f with
      | monarrstruct _ => monarrlist_id a
      | f' => monarrlist_arr a b f'
      end
  end.

Lemma remove_struct_proper (g : monarrlistelt) : 
  monarr_norm_equiv 
  (realize_monarrlistelt (remove_struct g)) 
  (realize_monarrlistelt g).
Proof.
  destruct g; [apply monarr_norm_equiv_refl|].
  simpl.
  destruct f; [apply monarr_norm_equiv_refl..|].
  unfold monarr_norm_equiv.
  simpl.
  pose proof (Nf_eq_of_arr f).
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab; [|congruence]
  end.
  rewrite !monarr_arrcomp.
  apply monarr_struct.
Qed.
  
Definition remove_structs := map remove_struct.

Lemma remove_structs_proper : 
  unary_monarrlist_op_proper remove_structs.
Proof.
  apply map_proper_proper.
  apply remove_struct_proper.
Qed.


Lemma compose_unary_ops_proper f g 
  (Hf : unary_monarrlist_op_proper f) 
  (Hg : unary_monarrlist_op_proper g) :
  unary_monarrlist_op_proper (Basics.compose f g).
Proof.
  intros fs.
  apply (@monarr_norm_equiv_trans _ _ _ _ _ _ _  (realize_monarrlist (g fs)));
  apply Hf + apply Hg.
Qed.

Definition monarrlist_list_source (fss : list monarrlist) : bw :=
  match fss with 
  | nil => e
  | fs :: fss' => monarrlist_source fs
  end.

Fixpoint monarrlist_list_target (fss : list monarrlist) : bw :=
  match fss with 
  | nil => e
  | fs :: nil => monarrlist_target fs
  | fs :: fss' => monarrlist_list_target fss'
  end.

Definition option_partial_map {A B} (f : A -> option B) (a : option A) :=
  match a with
  | Some a' => f a'
  | None => None
  end.

Fixpoint realize_monarrlist_list_helper
  (fst : monarrlist) (fss : list monarrlist) :
  option (monarr
    (monarrlist_list_source (fst :: fss))
    (monarrlist_list_target (fst :: fss))
  ) := 
  match fss with
  | nil => Some (realize_monarrlist fst)
  | fst' :: fss' => 
      option_partial_map 
        (maybe_compose_monarrs (realize_monarrlist fst))
        (realize_monarrlist_list_helper fst' fss')
  end.


Definition realize_monarrlist_list (fss : list monarrlist) :
  option (monarr
    (monarrlist_list_source fss)
    (monarrlist_list_target fss)
  ) := 
  match fss with
  | nil => Some (monarrstruct (arrid e))
  | fst :: fss' => realize_monarrlist_list_helper fst fss'
  end. 

Fixpoint totally_composable_helper 
  (fst : monarrlist) (fss : list monarrlist) :=
  match fss with 
  | nil => True
  | fst' :: fss' => composable fst fst' /\ 
      totally_composable_helper fst' fss'
  end.

Definition totally_composable (fss : list monarrlist) :=
  match fss with
  | nil => True
  | fst :: fss' => totally_composable_helper fst fss'
  end.


Definition dec_and {P Q : Prop} (HdecP : {P} + {~ P}) (HdecQ : {Q} + {~ Q}) :
  {P /\ Q} + {~ (P /\ Q)} :=
  match HdecP, HdecQ with
  | left HP, left HQ => left (conj HP HQ)
  | right HnP, _ => right (fun HPQ => HnP (proj1 HPQ))
  | _, right HnQ => right (fun HPQ => HnQ (proj2 HPQ))
  end.

Fixpoint totally_composable_helper_dec (fst : monarrlist)
  (fss : list monarrlist) :
  {totally_composable_helper fst fss} + 
  {~ totally_composable_helper fst fss} := 
  match fss with
  | nil => left Logic.I
  | fst' :: fss' => dec_and (eqbwnorm _ _) 
    (totally_composable_helper_dec fst' fss')
  end.

Definition totally_composable_dec (fss : list monarrlist) :
  {totally_composable fss} + {~ totally_composable fss} :=
  match fss with 
  | nil => left Logic.I
  | fst :: fss' => 
    totally_composable_helper_dec fst fss'
  end.

Lemma totally_composable_of_cons {fst : monarrlist} {fss : list monarrlist} : 
  totally_composable (fst :: fss) -> totally_composable fss.
Proof.
  destruct fss; easy + intros H; apply H.
Qed.

Definition compose_monarrlist_list_of_totally_composable 
  (fss : list monarrlist) (H : totally_composable fss) : 
  monarr
    (monarrlist_list_source fss)
    (monarrlist_list_target fss).
induction fss.
- exact (arrid e).
- simpl in H.
  destruct fss as [|fst' fss'].
  + apply realize_monarrlist.
  + apply (monarr_composer_of_composable (realize_monarrlist a) 
    (IHfss (proj2 H)) (proj1 H)).
Defined.

Lemma realize_monarrlist_list_helper_totally_composable (fst : monarrlist)
  (fss : list monarrlist) (H : totally_composable_helper fst fss) : 
  realize_monarrlist_list_helper fst fss = 
  Some (compose_monarrlist_list_of_totally_composable (fst :: fss) H).
Proof.
  revert fst H;
  induction fss; intros fst H.
  - easy.
  - simpl realize_monarrlist_list_helper.
    rewrite (IHfss _ (proj2 H)).
    unfold option_partial_map.
    apply (maybe_compose_monarrs_composable _ _ (proj1 H)).
Qed.

Lemma realize_monarrlist_list_totally_composable 
  (fss : list monarrlist) (H : totally_composable fss) : 
  realize_monarrlist_list fss = 
  Some (compose_monarrlist_list_of_totally_composable fss H).
Proof.
  destruct fss.
  - easy.
  - apply realize_monarrlist_list_helper_totally_composable.
Qed.




Definition monarrlist_list_op_proper (f : list monarrlist -> list monarrlist) :=
  forall fss : list monarrlist,
  totally_composable fss ->
  option_rel_map monarr_norm_equiv 
    (realize_monarrlist_list fss)
    (realize_monarrlist_list (f fss)).

Fixpoint pairwise_apply_helper 
  (f : monarrlist -> monarrlist -> monarrlist * monarrlist) 
  (fst : monarrlist) (fss : list monarrlist) := 
  match fss with
  | nil => fst::nil
  | fst' :: fss' => let '(fstf, fst'f) := f fst fst' in 
      fstf :: (pairwise_apply_helper f fst'f fss')
  end.

Definition pairwise_apply f (fss : list monarrlist) :=
  match fss with
  | nil => nil
  | fst :: fss' => pairwise_apply_helper f fst fss'
  end.

Lemma binary_op_proper_composable f (Hf : binary_monarrlist_op_proper f) 
  (fs gs : monarrlist) (H : composable fs gs) : 
  let '(fs', gs') := (f fs gs) in 
  composable fs' gs'.
Proof.
  specialize (Hf fs gs H).
  destruct (f fs gs) as (fs', gs').
  unfold maybe_compose in Hf.
  destruct (is_composable fs' gs'); [easy|].
  destruct (is_composable fs gs); easy.
Qed.

Lemma Nf_in_eq_of_proper_binary_op f (Hf : binary_monarrlist_op_proper f) 
  (fs gs : monarrlist) (H : composable fs gs) : 
  let '(fs', gs') := f fs gs in 
    Nf (monarrlist_source fs') = Nf (monarrlist_source fs).
Proof.
  pose proof (binary_op_proper_composable f Hf fs gs H) as comp.
  specialize (Hf fs gs H).
  destruct (f fs gs) as (fs', gs').
  rewrite (maybe_compose_composable H), (maybe_compose_composable comp) in Hf.
  simpl in Hf.
  symmetry.
  apply (Nf_eq_in_of_norm_equiv Hf).
Qed.

Lemma Nf_out_eq_of_proper_binary_op f (Hf : binary_monarrlist_op_proper f) 
  (fs gs : monarrlist) (H : composable fs gs) : 
  let '(fs', gs') := f fs gs in 
    Nf (monarrlist_target gs') = Nf (monarrlist_target gs).
Proof.
  pose proof (binary_op_proper_composable f Hf fs gs H) as comp.
  specialize (Hf fs gs H).
  destruct (f fs gs) as (fs', gs').
  rewrite (maybe_compose_composable H), (maybe_compose_composable comp) in Hf.
  simpl in Hf.
  symmetry.
  apply (Nf_eq_out_of_norm_equiv Hf).
Qed.

Lemma binary_op_proper_composable_prefix f (Hf : binary_monarrlist_op_proper f)
  fst fst' fss (H : totally_composable (fst :: fst' :: fss)) : 
  let '(fs', gs') := f fst fst' in
  totally_composable (fs' :: gs' :: fss).
Proof.
  destruct (f fst fst') as (fs', gs') eqn:e.
  split.
  - pose proof (binary_op_proper_composable f Hf fst fst' (proj1 H)) as key.
    rewrite e in key; apply key.
  - destruct fss as [| a fss]; [easy|].
    split; [|apply H].
    pose proof (Nf_out_eq_of_proper_binary_op f Hf fst fst' (proj1 H)) as key.
    rewrite e in key.
    unfold composable.
    rewrite key.
    apply H.
Qed.

Lemma pairwise_apply_helper_totally_composable fst fss f 
  (Hf : binary_monarrlist_op_proper f) : 
  totally_composable_helper fst fss ->
  totally_composable (pairwise_apply_helper f fst fss).
Proof.
  revert fst; induction fss; intros fst; [easy|].
  intros H; pose proof H as G; destruct G as [Hl Hr].
  simpl.
  destruct (f fst a) as (f1, f2) eqn:e.
  simpl. 
  destruct fss as [|fst' fss].
  - split; [|easy].
    pose proof (binary_op_proper_composable f Hf fst a Hl) as key.
    rewrite e in key.
    easy.
  - simpl.
    destruct (f f2 fst') as (f1', f2') eqn:e'.
    split.
    + simpl in Hr.
      pose proof (Hf fst a Hl) as Hf'.
      rewrite e in Hf'.
      pose proof (binary_op_proper_composable f Hf fst a Hl) as cmpb.
      rewrite e in cmpb.
      unfold composable in *.
      rewrite cmpb.
      pose proof (binary_op_proper_composable f Hf f2 fst') as cmpb'.
      rewrite e' in cmpb'.
      pose proof (Nf_in_eq_of_proper_binary_op f Hf f2 fst') as key.
      rewrite e' in key.
      rewrite key; [easy|].
      unfold composable.
      pose proof (Nf_out_eq_of_proper_binary_op f Hf fst a Hl) as key'.
      rewrite e in key'.
      rewrite key'.
      easy.
    + simpl in IHfss. 
      specialize (IHfss f2).
      rewrite e' in IHfss.
      apply IHfss.
      split; [| apply Hr].
      unfold composable.
      pose proof (Nf_out_eq_of_proper_binary_op f Hf fst a Hl) as key'.
      rewrite e in key'.
      rewrite key'.
      apply Hr.
Qed.

Lemma pairwise_apply_totally_composable fss f 
  (Hf : binary_monarrlist_op_proper f) : 
  totally_composable fss ->
  totally_composable (pairwise_apply f fss).
Proof.
  destruct fss; [easy|].
  apply pairwise_apply_helper_totally_composable, Hf.
Qed.

(* Lemma pairwise_apply_step_proper f (Hf : binary_op_proper_composable)
  (a b : monarrlist) (fss : list monarrlist) 
  (H : totally_composable (a :: b :: fss))
  (H' : let '(a', b') := f a b in totally_composable (a' :: b' :: fss)) :
  let '(a', b') := f a b in 
  monarr_norm_equiv 
    (compose) *)

Lemma totally_composable_app_restrict_r {fsts fss} :
  totally_composable (fsts ++ fss) ->
  totally_composable fss.
Proof.
  destruct fss; [easy|].
  induction fsts; [easy|].
  intros H; apply IHfsts.
  simpl in H.
  destruct fsts; apply H.
Qed.

Lemma totally_composable_app_restrict_l {fsts fss} :
  totally_composable (fsts ++ fss) ->
  totally_composable fsts.
Proof.
  (* destruct fss; [rewrite app_nil_r; easy|]. *)
  induction fsts; [easy|].
  destruct fsts; [easy|]. 
  intros H; split.
  - apply H.
  - apply IHfsts, H.
Qed.

Lemma totally_composable_indep (fss : list monarrlist) 
  (H G : totally_composable fss) : H = G.
Proof.
  induction fss; [now destruct H, G|].
  destruct fss; [now destruct H, G|].
  simpl in H, G.
  destruct H, G.
  f_equal.
  * apply (Eqdep_dec.UIP_dec eqbwnorm).
  * apply IHfss.
Qed.

Lemma compose_monarrlist_list_of_totally_composable_indep 
  (fss : list monarrlist) (H G : totally_composable fss) :
  compose_monarrlist_list_of_totally_composable fss H = 
  compose_monarrlist_list_of_totally_composable fss G.
Proof.
  rewrite (totally_composable_indep fss H G).
  easy.
Qed.


Lemma middle_arr_composable_of_totally_composable 
  {a b fss fss'} (H : totally_composable ((a :: fss) ++ (b :: fss'))) : 
  Nf (monarrlist_list_target (a :: fss)) 
  = Nf (monarrlist_list_source (b :: fss')).
Proof.
  simpl monarrlist_list_source.
  revert a H;
  induction fss as [|fst fss IHfss];
  intros a H; [apply H|].
  simpl totally_composable in *.
  specialize (IHfss _ (proj2 H)).
  apply IHfss.
Qed.

Lemma monarrlist_list_target_app {fss b fss'} :
  monarrlist_list_target (fss ++ b :: fss') =
  monarrlist_list_target (b :: fss').
Proof.
  induction fss; [easy|].
  destruct fss;
  apply IHfss.
Qed.

Definition true_rel {A : Type} : relation A :=
  fun _ _ => True.

Add Parametric Relation (A : Type) : A true_rel 
  reflexivity proved by ltac:(easy)
  symmetry proved by ltac:(easy)
  transitivity proved by ltac:(easy)
  as true_rel_relation.

Add Parametric Morphism (a a' b b' : bw) : 
  (@monarr_composer_of_composable a a' b b')
  with signature 
  (monarrequiv a a') ==> (monarrequiv b b') ==> true_rel ==> 
  (monarrequiv a b') as monarr_composer_of_composable_mor.
Proof.
  intros f f' Hf g g' Hg H1 H2 _.
  unfold monarr_composer_of_composable.
  apply monarr_comp; [apply monarr_comp|]; 
  assumption + apply monarr_struct.
Qed.


Lemma compose_monarrlist_list_of_totally_composable_cons
  {a b fss} (H : totally_composable (a :: b :: fss)) : 
  (compose_monarrlist_list_of_totally_composable _ H)
  ≊
  monarr_composer_of_composable (realize_monarrlist a)
    (compose_monarrlist_list_of_totally_composable (b::fss) (proj2 H))
    (proj1 H).
Proof.
  revert a b H.
  induction fss as [|fst fss IHfss];
  intros a b H; [easy|].
  specialize (IHfss _ _ (proj2 H)).
  unfold monarr_composer_of_composable.
  rewrite IHfss.
  easy.
Qed.


Lemma compose_monarrlist_list_of_totally_composable_app_helper
  {a b fss fss'} (H : totally_composable ((a :: fss) ++ (b :: fss'))) : 
  monarrequiv _ _ 
    (compose_monarrlist_list_of_totally_composable _ H)
    (monarrcomp
      (monarr_composer_of_composable
        (compose_monarrlist_list_of_totally_composable (a :: fss)
          (totally_composable_app_restrict_l H))
        (compose_monarrlist_list_of_totally_composable (b :: fss')
          (totally_composable_app_restrict_r H))
        (middle_arr_composable_of_totally_composable H))
      (bwarr_id_cast (eq_sym monarrlist_list_target_app))).
Proof.
  revert a H;
  induction fss as [|fst fss IHfss]; 
  intros a H.
  - simpl app.
    rewrite compose_monarrlist_list_of_totally_composable_cons.
    unfold monarr_composer_of_composable.
    rewrite <- !monarr_assoc.
    apply monarr_comp; [easy|].
    apply monarr_comp; [apply monarr_struct|].
    rewrite (monarr_struct _ (arrid _)), monarr_runit.
    erewrite compose_monarrlist_list_of_totally_composable_indep.
    reflexivity.
  - simpl app.
    rewrite compose_monarrlist_list_of_totally_composable_cons.
    unfold monarr_composer_of_composable.
    rewrite compose_monarrlist_list_of_totally_composable_cons.
    unfold monarr_composer_of_composable.
    rewrite <- !monarr_assoc.
    apply monarr_comp; [easy|].
    apply monarr_comp; [apply monarr_struct|].
    change (fst :: fss ++ b :: fss') with ((fst :: fss) ++ b :: fss').
    rewrite IHfss.
    unfold monarr_composer_of_composable.
    rewrite <- !monarr_assoc.
    repeat apply monarr_comp; 
    apply monarr_struct + 
    (erewrite compose_monarrlist_list_of_totally_composable_indep;
    reflexivity).
Qed.


Lemma monarr_norm_equiv_arrid {a b} (hd : a ⟶ b) : 
  monarr_norm_equiv (arrid e) hd ->
  forall (g : bwarr a b), hd ≊ g.
Proof.
  unfold monarr_norm_equiv.
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab; [|try easy]
  end.
  intros H g.
  rewrite <- H.
  rewrite !monarr_arrcomp.
  apply monarr_struct.
Qed.

Lemma monarrlist_list_source_app fss fss' :
  monarrlist_list_source (fss ++ fss') =
  match fss with
  | nil => monarrlist_list_source fss'
  | x::_ => monarrlist_source x
  end.
Proof.
  destruct fss; easy.
Qed.

Lemma compose_monarrlist_list_cancel_suffix_helper_nil
  hd fss 
  (H1 : totally_composable fss)
  (H2 : totally_composable (hd ++ fss))
  (Hh : totally_composable hd) : 
  monarr_norm_equiv 
    (arrid e)
    (compose_monarrlist_list_of_totally_composable 
      hd Hh) ->
  monarr_norm_equiv
    (compose_monarrlist_list_of_totally_composable _ H1)
    (compose_monarrlist_list_of_totally_composable _ H2).
Proof.
  destruct hd; [|destruct fss].
  - intros _.
    apply monarr_norm_equiv_of_monarrequiv.
    erewrite compose_monarrlist_list_of_totally_composable_indep.
    reflexivity.
  - revert H2.
    rewrite app_nil_r.
    intros H2.
    intros H.
    erewrite (compose_monarrlist_list_of_totally_composable_indep (_::hd)).
    apply H.
  - rewrite compose_monarrlist_list_of_totally_composable_app_helper.
    unfold monarr_norm_equiv.
    repeat match goal with 
    |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
        destruct eqab; [|try easy]
    end.
    2: {
      rewrite monarrlist_list_target_app in *; easy.
    }
    2: {
      epose proof middle_arr_composable_of_totally_composable as H.
      specialize (H ltac:(eassumption)).
      simpl in * |-.
      congruence.
    }
    intros Hequiv_id_e.
    rewrite 2!monarr_arrcomp in Hequiv_id_e.
    (* rewrite (monarr_struct _ (monarr_of_Nf_eq (eq_trans _ _))) in Hequiv_id_e. *)
    rewrite (compose_monarrlist_list_of_totally_composable_indep _ _ Hh).
    symmetry.
    rewrite (compose_monarrlist_list_of_totally_composable_indep _ _ H1).
    generalize (compose_monarrlist_list_of_totally_composable (l0 :: fss) H1).
    intros m.
    rewrite <- Hequiv_id_e.
    unfold monarr_composer_of_composable.
    apply monarr_comp; [|apply monarr_struct].
    rewrite monarr_arrcomp.
    apply monarr_comp; [apply monarr_struct|easy].
Qed.

Lemma monarrcomp_struct_r {a b m} (f : a ⟶ b)
  (g : bwarr b m) (h : a ⟶ m) : 
  monarrcomp f g ≊ h <-> f ≊ monarrcomp h (g ^-).
Proof.
  split;
  intros H;
  [rewrite <- H | rewrite H]; rewrite <- monarr_assoc;
  rewrite monarr_arrcomp, (monarr_struct _ (arrid _));
  now rewrite ?monarr_runit, ?monarr_lunit.
Qed.

Lemma monarrcomp_struct_l {a b m} (f : bwarr a b)
  (g : b ⟶ m) (h : a ⟶ m) : 
  monarrcomp f g ≊ h <-> g ≊ monarrcomp (f ^-) h.
Proof.
  split;
  intros H;
  [rewrite <- H | rewrite H]; rewrite monarr_assoc;
  rewrite monarr_arrcomp, (monarr_struct _ (arrid _));
  now rewrite ?monarr_runit, ?monarr_lunit.
Qed.

Lemma monarrcomp_struct_r' {a b m} (f : a ⟶ b)
  (g : bwarr b m) (h : a ⟶ m) : 
  h ≊ monarrcomp f g <-> monarrcomp h (g ^-) ≊ f.
Proof.
  split;
  intros H; 
  symmetry;
  apply monarrcomp_struct_r; easy.
Qed.

Lemma monarrcomp_struct_l' {a b m} (f : bwarr a b)
  (g : b ⟶ m) (h : a ⟶ m) : 
  h ≊ monarrcomp f g <-> monarrcomp (f ^-) h ≊ g.
Proof.
  split;
  intros H; 
  symmetry;
  apply monarrcomp_struct_l; easy.
Qed.

Lemma monarr_struct_id {a} (f : bwarr a a) : 
  f ≊ arrid a.
Proof.
  apply monarr_struct.
Qed.

Lemma monarr_struct_Nf_eq {a b} (f : bwarr a b) :
  f ≊ monarr_of_Nf_eq (Nf_eq_of_arr f).
Proof.
  apply monarr_struct.
Qed.

Lemma compose_monarrlist_list_cancel_suffix_helper 
  hd1 hd2 fss 
  (H1 : totally_composable (hd1 ++ fss))
  (H2 : totally_composable (hd2 ++ fss))
  (H1h : totally_composable hd1)
  (H2h : totally_composable hd2) : 
  monarr_norm_equiv 
    (compose_monarrlist_list_of_totally_composable 
      hd1 H1h)
    (compose_monarrlist_list_of_totally_composable 
      hd2 H2h) ->
  monarr_norm_equiv
    (compose_monarrlist_list_of_totally_composable _ H1)
    (compose_monarrlist_list_of_totally_composable _ H2).
Proof.
  revert H1 H2.
  induction fss as [|fst fss].
  1: {
    rewrite 2!app_nil_r.
    intros H1 H2.
    rewrite (compose_monarrlist_list_of_totally_composable_indep _ H1 H1h).
    rewrite (compose_monarrlist_list_of_totally_composable_indep _ H2 H2h).
    easy.
  }
  destruct hd1.
  1: {
    clear IHfss.
    simpl app.
    change (compose_monarrlist_list_of_totally_composable [] _) 
      with (monarrstruct (arrid e)).
    intros H1 H2.
    apply compose_monarrlist_list_cancel_suffix_helper_nil.
  } 
  destruct hd2.
  1: {
    clear IHfss.
    simpl app.
    setoid_rewrite monarr_norm_equiv_symmetric.
    change (compose_monarrlist_list_of_totally_composable [] _) 
      with (monarrstruct (arrid e)).
    intros H1 H2.
    apply compose_monarrlist_list_cancel_suffix_helper_nil.
  }
  intros H1 H2.
  rewrite 2!compose_monarrlist_list_of_totally_composable_app_helper.
  unfold monarr_norm_equiv. 
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab; [|try congruence]
  end; try easy.
  2: {
    rewrite !monarrlist_list_target_app in *.
    easy.
  }
  clear IHfss.
  intros H.
  symmetry in H.
  erewrite compose_monarrlist_list_of_totally_composable_indep in H.
  rewrite H.
  unfold monarr_composer_of_composable.
  
  rewrite monarrcomp_struct_r.
  rewrite monarrcomp_struct_l.
  apply monarrcomp_struct_r.

  rewrite <- !monarr_assoc, !monarr_arrcomp.
  clear H.

  rewrite !monarr_assoc, !monarr_arrcomp.
  rewrite monarr_struct_id, monarr_runit.
  rewrite (compose_monarrlist_list_of_totally_composable_indep
    _ _ (totally_composable_app_restrict_r H2)).
  apply monarr_comp; [|easy].
  apply monarrcomp_struct_r.
  rewrite <- !monarr_assoc, !monarr_arrcomp.
  rewrite monarr_struct_id, monarr_runit.
  rewrite (compose_monarrlist_list_of_totally_composable_indep _ _ H1h).
  rewrite monarr_struct_id, monarr_lunit.
  easy.
Qed.

Lemma compose_monarrlist_list_cancel_suffix
  hd1 hd2 fss 
  (H1 : totally_composable (hd1 ++ fss))
  (H2 : totally_composable (hd2 ++ fss)) : 
  monarr_norm_equiv 
    (compose_monarrlist_list_of_totally_composable 
      hd1 (totally_composable_app_restrict_l H1))
    (compose_monarrlist_list_of_totally_composable 
      hd2 (totally_composable_app_restrict_l H2)) ->
  monarr_norm_equiv
    (compose_monarrlist_list_of_totally_composable _ H1)
    (compose_monarrlist_list_of_totally_composable _ H2).
Proof.
  intros H.
  eapply compose_monarrlist_list_cancel_suffix_helper.
  apply H.
Qed.

(* Lemma monarr_norm_equiv_struct {a a' b b' c c'}
  (f : c ⟶ c') (g : bwarr a a') (h : bwarr b b') : 
  monarr_norm_equiv g f -> monarr_norm_equiv h f.
Proof.
  intros H.
  pose proof (Nf_eq_out_of_norm_equiv H).
  pose proof (Nf_eq_in_of_norm_equiv H).
  revert H.
  unfold monarr_norm_equiv.
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab; [|try congruence]
  end.
  2: {

  } *)

Lemma compose_monarrlist_list_cancel_prefix_helper 
  hd1 hd2 fss 
  (H1 : totally_composable (fss ++ hd1))
  (H2 : totally_composable (fss ++ hd2))
  (H1h : totally_composable hd1)
  (H2h : totally_composable hd2) : 
  monarr_norm_equiv 
    (compose_monarrlist_list_of_totally_composable 
      hd1 H1h)
    (compose_monarrlist_list_of_totally_composable 
      hd2 H2h) ->
  monarr_norm_equiv
    (compose_monarrlist_list_of_totally_composable _ H1)
    (compose_monarrlist_list_of_totally_composable _ H2).
Proof.
  intros H.
  induction fss.
  - rewrite (compose_monarrlist_list_of_totally_composable_indep _ _ H1h).
    rewrite (compose_monarrlist_list_of_totally_composable_indep _ _ H2h).
    easy.
  - destruct fss.
    1: {
      destruct hd1, hd2.
      1: apply monarr_norm_equiv_of_monarrequiv;
          erewrite (compose_monarrlist_list_of_totally_composable_indep);
          reflexivity.
      1: {
        specialize (IHfss (Logic.I) (proj2 H2)).
        simpl app.
        rewrite compose_monarrlist_list_of_totally_composable_cons.
        rewrite <- monarr_runit.
        unfold monarr_composer_of_composable.
        apply monarr_norm_equiv_comp.
        - unfold monarr_norm_equiv.
          simpl.
          simpl in H2.
          destruct H2.
          repeat match goal with 
          |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
              destruct eqab; [|try congruence]
          end.
          rewrite monarrcomp_struct_r, monarrcomp_struct_l.
          rewrite monarr_struct_id, monarr_lunit.
          rewrite <- monarr_assoc, monarr_arrcomp, monarr_struct_id.
          now rewrite monarr_runit.
        - simpl in H2.
          pose proof (Nf_eq_in_of_norm_equiv IHfss).
          revert IHfss.
          unfold monarr_norm_equiv.
          destruct H2.
          unfold composable in *.
          repeat match goal with 
          |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
              destruct eqab; [|try (simpl in *; congruence)]
          end.
          2: easy.
          simpl app.
          intros H'.
          rewrite <- H'.
          simpl.
          rewrite !monarr_arrcomp; apply monarr_struct.
      }
      1: {
        specialize (IHfss (proj2 H1) (Logic.I)).
        simpl app.
        rewrite compose_monarrlist_list_of_totally_composable_cons.
        apply monarr_norm_equiv_symm.
        rewrite <- monarr_runit.
        unfold monarr_composer_of_composable.
        apply monarr_norm_equiv_comp.
        - unfold monarr_norm_equiv.
          simpl.
          simpl in H1.
          destruct H1.
          repeat match goal with 
          |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
              destruct eqab; [|try congruence]
          end.
          rewrite monarrcomp_struct_r, monarrcomp_struct_l.
          rewrite monarr_struct_id, monarr_lunit.
          rewrite <- monarr_assoc, monarr_arrcomp, monarr_struct_id.
          now rewrite monarr_runit.
        - simpl in H1.
          pose proof (Nf_eq_in_of_norm_equiv IHfss).
          revert IHfss.
          rewrite monarr_norm_equiv_symmetric.
          unfold monarr_norm_equiv.
          destruct H1.
          unfold composable in *.
          repeat match goal with 
          |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
              destruct eqab; [|try (simpl in *; congruence)]
          end.
          2: easy.
          simpl app.
          intros H'.
          rewrite <- H'.
          simpl.
          rewrite !monarr_arrcomp; apply monarr_struct.
      }
      simpl app.
      rewrite 2!compose_monarrlist_list_of_totally_composable_cons.
      unfold monarr_composer_of_composable.
      apply monarr_norm_equiv_comp; [|apply IHfss].
      apply monarr_norm_equiv_comp.
      - apply monarr_norm_equiv_refl.
      - pose proof (Nf_eq_in_of_norm_equiv H).
        unfold monarr_norm_equiv.
        repeat match goal with 
        |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
            destruct eqab; [|try (simpl in *; congruence)]
        end.
        rewrite !monarr_arrcomp; apply monarr_struct.
    } 
    simpl app.
    rewrite 2!compose_monarrlist_list_of_totally_composable_cons.
    unfold monarr_composer_of_composable.
    apply monarr_norm_equiv_comp; [|apply IHfss].
    apply monarr_norm_equiv_comp.
    + apply monarr_norm_equiv_refl.
    + pose proof (Nf_eq_in_of_norm_equiv H).
      unfold monarr_norm_equiv.
      repeat match goal with 
      |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
          destruct eqab; [|try (simpl in *; congruence)]
      end.
      rewrite !monarr_arrcomp; apply monarr_struct.
Qed.

Lemma compose_monarrlist_list_cancel_prefix
  hd1 hd2 fss 
  (H1 : totally_composable (fss ++ hd1))
  (H2 : totally_composable (fss ++ hd2)) : 
  monarr_norm_equiv 
    (compose_monarrlist_list_of_totally_composable 
      hd1 (totally_composable_app_restrict_r H1))
    (compose_monarrlist_list_of_totally_composable 
      hd2 (totally_composable_app_restrict_r H2)) ->
  monarr_norm_equiv
    (compose_monarrlist_list_of_totally_composable _ H1)
    (compose_monarrlist_list_of_totally_composable _ H2).
Proof.
  intros H.
  eapply compose_monarrlist_list_cancel_prefix_helper.
  apply H.
Qed.

Lemma pairwise_apply_proper_binary_op_proper f 
  (Hf : binary_monarrlist_op_proper f) : 
  monarrlist_list_op_proper (pairwise_apply f).
Proof.
  intros fss.
  destruct fss as [|fst fss]; [intros; apply monarr_norm_equiv_refl|].
  simpl.
  intros H.
  rewrite (realize_monarrlist_list_helper_totally_composable _ _ H).
  rewrite (realize_monarrlist_list_totally_composable _ 
    (pairwise_apply_helper_totally_composable _ _ f Hf H)).
  unfold option_rel_map, option_2map.
  revert fst H;
  induction fss; intros fst H; [apply monarr_norm_equiv_refl|].
  simpl pairwise_apply_helper.
  generalize (pairwise_apply_helper_totally_composable fst (a :: fss) f Hf H)
   as Hc.
  intros Hc.
  simpl in Hc.
  destruct (f fst a) as (f1, f2) eqn:e.
  pose proof (binary_op_proper_composable_prefix f Hf fst a fss H) as Hc'.
  rewrite e in Hc'.
  apply (@monarr_norm_equiv_trans _ _ _ _ _ _ _ 
    (compose_monarrlist_list_of_totally_composable _ Hc')).
  - change (fst :: a :: fss) with ((fst :: a :: nil) ++ fss).
    change (f1 :: f2 :: fss) with ((f1 :: f2 :: nil) ++ fss).
    apply (compose_monarrlist_list_cancel_suffix [fst;a] [f1;f2] fss).
    simpl.
    clear IHfss.
    specialize (Hf fst a (proj1 H)).
    rewrite e in Hf.
    rewrite (maybe_compose_composable (proj1 H)) in Hf.
    rewrite (maybe_compose_composable (proj1 Hc')) in Hf.
    simpl option_rel_map in Hf.
    repeat match goal with
    |- context[proj1 ?k] => generalize (proj1 k)
    end.
    intros h1 h2.
    erewrite (Eqdep_dec.UIP_dec eqbwnorm h1). 
    erewrite (Eqdep_dec.UIP_dec eqbwnorm h2). 
    apply Hf.
  - apply (compose_monarrlist_list_cancel_prefix (f2::fss) 
      (pairwise_apply_helper f f2 fss) [f1]).
    apply monarr_norm_equiv_symm.
    erewrite compose_monarrlist_list_of_totally_composable_indep.
    apply monarr_norm_equiv_symm.
    erewrite compose_monarrlist_list_of_totally_composable_indep.
    apply IHfss.
  Unshelve.
    apply Hc'.
Qed.


Fixpoint depairify (fsgs : list (monarrlist * monarrlist)) 
  : monarrlist * monarrlist :=
  match fsgs with 
  | nil => (nil, nil)
  | fg :: fsgs' =>
      (* let '(fs, gs) := depairify fsgs' in  *)
      (fst fg ++ fst (depairify fsgs'), snd fg ++ snd (depairify fsgs'))
  end.

Lemma varlist_fold_right_tens hd tl : 
  bw_to_varlist (fold_right (fun a n => n ⨂ a) e (hd ++ tl)) =
  bw_to_varlist (fold_right (fun a n => n ⨂ a) e hd)
  ++ bw_to_varlist (fold_right (fun a n => n ⨂ a) e tl).
Proof.
  induction hd; [easy|].
  simpl. 
  rewrite IHhd.
  apply app_assoc.
Qed.

Lemma Nf_fold_right_tens hd tl : 
  Nf (fold_right (fun a n => n ⨂ a) e (hd ++ tl)) =
  bwnormapp 
    (Nf (fold_right (fun a n => n ⨂ a) e tl))
    (Nf (fold_right (fun a n => n ⨂ a) e hd)).
Proof.
  rewrite 3!Nf_eq_bwnorm_of_varlist.
  rewrite 3!bw_to_varlist_fold_right.
  rewrite map_app, concat_app.
  rewrite varlist_to_bwnorm_app.
  easy.
Qed.

Lemma Nf_monarrlist_source_app hd tl : 
  Nf (monarrlist_source (hd ++ tl)) = 
  bwnormapp (Nf (monarrlist_source tl))
    (Nf (monarrlist_source hd)).
Proof.
  unfold monarrlist_source.
  rewrite map_app.
  apply Nf_fold_right_tens.
Qed.

Lemma Nf_monarrlist_target_app hd tl : 
  Nf (monarrlist_target (hd ++ tl)) = 
  bwnormapp (Nf (monarrlist_target tl))
    (Nf (monarrlist_target hd)).
Proof.
  unfold monarrlist_target.
  rewrite map_app.
  apply Nf_fold_right_tens.
Qed.
  
Lemma Nf_monarrlist_source_app' hd tl : 
  Nf (monarrlist_source (hd ++ tl)) = 
  Nf (monarrlist_source tl ⨂ monarrlist_source hd).
Proof.
  rewrite Nf_tens_bwnormapp.
  apply Nf_monarrlist_source_app.
Qed.

Lemma Nf_monarrlist_target_app' hd tl : 
  Nf (monarrlist_target (hd ++ tl)) = 
  Nf (monarrlist_target tl ⨂ monarrlist_target hd).
Proof.
  rewrite Nf_tens_bwnormapp.
  apply Nf_monarrlist_target_app.
Qed.

Lemma composable_app {hd1 hd2 tl1 tl2}
  (Hh : composable hd1 hd2)
  (Ht : composable tl1 tl2) : 
  composable (hd1 ++ tl1) (hd2 ++ tl2).
Proof.
  unfold composable in *.
  rewrite Nf_monarrlist_source_app, Nf_monarrlist_target_app.
  f_equal; easy.
Qed.

Lemma depairify_composable fsgs 
  (H : Forall (uncurry composable) fsgs) : 
  composable (fst (depairify fsgs)) (snd (depairify fsgs)).
Proof.
  induction fsgs as [|[f g] fsgs IHfsgs]; [easy|].
  simpl.
  destruct (depairify fsgs) as (fs, gs).
  simpl.
  inversion H; subst.
  apply composable_app; [assumption|].
  apply IHfsgs; assumption.
Qed.

Definition pairify_apply 
  (f : monarrlist -> monarrlist -> monarrlist * monarrlist)
  (fs : monarrlist) (gs : monarrlist) : monarrlist * monarrlist :=
  depairify (map (uncurry f) (pairify fs gs)).

Lemma monarr_composer_of_composable_indep {a b b' c} {f : a ⟶ b} {g : b' ⟶ c} H G : 
  monarr_composer_of_composable f g H = 
  monarr_composer_of_composable f g G.
Proof.
  rewrite (Eqdep_dec.UIP_dec eqbwnorm H G).
  easy.
Qed.


Lemma monarrlist_composer_of_composable_indep fss gss H G : 
  monarrlist_composer_of_composable fss gss H = 
  monarrlist_composer_of_composable fss gss G.
Proof.
  rewrite (Eqdep_dec.UIP_dec eqbwnorm H G).
  easy.
Qed.


Lemma binary_proper_of_composable_proper 
  (f : monarrlist -> monarrlist -> monarrlist * monarrlist)
  (Hc : forall fs gs, composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs))) 
  (Hprop : forall fs gs (Hfg : composable fs gs)
    (Hc' : forall fs gs, composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs))),
    monarr_norm_equiv 
      (monarrlist_composer_of_composable fs gs Hfg)
      (monarrlist_composer_of_composable (fst (f fs gs)) (snd (f fs gs)) 
        (Hc' fs gs Hfg))
      ): 
  binary_monarrlist_op_proper f.
Proof.
  intros fs gs Hfg.
  pose proof Hc as Hc'.
  specialize (Hc' fs gs Hfg).
  specialize (Hprop fs gs Hfg Hc).
  rewrite (surjective_pairing (f fs gs)).
  rewrite (maybe_compose_composable Hfg), 
    (maybe_compose_composable Hc').
  unfold option_rel_map.
  simpl.
  erewrite (monarrlist_composer_of_composable_indep (fst _)) in Hprop.
  apply Hprop.
Qed.


Lemma binary_proper_iff_composable_proper 
  (f : monarrlist -> monarrlist -> monarrlist * monarrlist) :
  binary_monarrlist_op_proper f <-> 
  (forall fs gs, composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs)))
  /\  forall fs gs (Hfg : composable fs gs)
  (Hc' : forall fs gs, composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs))),
  monarr_norm_equiv 
    (monarrlist_composer_of_composable fs gs Hfg)
    (monarrlist_composer_of_composable (fst (f fs gs)) (snd (f fs gs)) 
      (Hc' fs gs Hfg)).
Proof.
  split; [|intros []; apply binary_proper_of_composable_proper; easy].
  intros Hf.
  split.
  - intros fs gs Hfg.
    specialize (Hf fs gs Hfg).
    rewrite (surjective_pairing (f fs gs)) in Hf.
    revert Hf.
    unfold maybe_compose.
    destruct (is_composable fs gs); [|easy].
    destruct (is_composable (fst (f fs gs)) (snd (f fs gs))); easy.
  - intros fs gs Hfg Hc.
    specialize (Hf fs gs Hfg).
    rewrite (surjective_pairing (f fs gs)) in Hf.
    rewrite (maybe_compose_composable Hfg) in Hf.
    rewrite (maybe_compose_composable (Hc fs gs Hfg)) in Hf.
    apply Hf.
Qed.

Lemma forall_composable_map {f} (Hc : forall fs gs, 
  composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs))) 
  {fsgs} (Hfsgs : Forall (uncurry composable) fsgs) : 
  Forall (uncurry composable) (map (uncurry f) fsgs).
Proof.
  induction fsgs as [|[g g'] fsgs IHfsgs]; [easy|].
  simpl.
  inversion Hfsgs; subst.
  constructor; [|apply IHfsgs; assumption].
  - rewrite (surjective_pairing (f g g')).
    apply Hc; assumption.
Qed.

Lemma pairify_apply_composable f (Hc : forall fs gs, 
  composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs))) : 
  forall fs gs, composable fs gs -> 
  composable (fst (pairify_apply f fs gs)) (snd (pairify_apply f fs gs)).
Proof.
  intros fs gs Hfg.
  unfold pairify_apply.
  apply depairify_composable.
  apply (forall_composable_map Hc).
  apply pairify_composable; assumption.
Qed.



Lemma realize_monarrlist_app fs fss : 
  realize_monarrlist (fs ++ fss) 
  ≊ monarrcomp (monarrcomp 
    (monarr_of_Nf_eq (Nf_monarrlist_source_app' fs fss) )
    (monarrtens (realize_monarrlist fss) (realize_monarrlist fs)))
    (monarr_of_Nf_eq (eq_sym (Nf_monarrlist_target_app' fs fss))).
Proof.
  induction fs.
  - rewrite (monarr_struct _ (arrrunitor _)), <- monarr_assoc.
    rewrite <- monarr_runitor_nat.
    rewrite monarr_assoc.
    rewrite monarr_arrcomp, monarr_struct_id, monarr_lunit.
    easy.
  - simpl.
    rewrite (monarr_struct 
    (monarr_of_Nf_eq (eq_sym (Nf_monarrlist_target_app' (a :: fs) fss)))
    (arrassoc _ _ _ ○
      (monarr_of_Nf_eq (eq_sym (Nf_monarrlist_target_app' fs fss))
       ⊠ arrid (target a)))).
    rewrite <- monarr_arrcomp.
    rewrite monarr_assoc, <- (monarr_assoc (monarr_of_Nf_eq _)).
    rewrite <- 
      (monarr_assoc_nat (realize_monarrlist fss)
        (realize_monarrlist fs)
        (realize_monarrlistelt a)).
    rewrite <- !monarr_assoc, 
      <- (monarr_arrtens 
      (monarr_of_Nf_eq (eq_sym (Nf_monarrlist_target_app' fs fss))) 
      (arrid (target a))).
    simpl.
    rewrite <- 
      (monarr_tens_comp (monarrtens _ _) 
      (monarr_of_Nf_eq (eq_sym (Nf_monarrlist_target_app' fs fss)))
        (realize_monarrlistelt a) (arrid (target a))).
    rewrite monarr_runit.
    rewrite !monarr_assoc.
    rewrite monarr_arrcomp.
    rewrite (monarr_struct _ 
      (monarr_of_Nf_eq (Nf_monarrlist_source_app' fs fss) ⊠ (arrid (source a)))).
    rewrite <- monarr_arrtens.
    rewrite <- 
      (monarr_tens_comp 
        (monarr_of_Nf_eq (Nf_monarrlist_source_app' fs fss))
        (monarrcomp (monarrtens _ _) 
        (monarr_of_Nf_eq (eq_sym (Nf_monarrlist_target_app' fs fss)))) (arrid (source a))
        (realize_monarrlistelt a)).
    apply monarr_tens; [|now rewrite monarr_lunit].
    rewrite monarr_assoc. 
    apply IHfs.
Qed.

Lemma tens_realize_monarrlist fs fss : 
  (monarrtens (realize_monarrlist fss) (realize_monarrlist fs))
  ≊ monarrcomp (monarrcomp 
    (monarr_of_Nf_eq (eq_sym (Nf_monarrlist_source_app' fs fss)))
    (realize_monarrlist (fs ++ fss)))
    (monarr_of_Nf_eq (Nf_monarrlist_target_app' fs fss)).
Proof.
  rewrite realize_monarrlist_app.
  rewrite !monarr_assoc, monarr_arrcomp, monarr_struct_id, monarr_lunit.
  rewrite <- !monarr_assoc, monarr_arrcomp, monarr_struct_id, monarr_runit.
  easy.
Qed.

Lemma monarrlist_composer_of_composable_app_helper {fs gs} 
  (Hfg : composable fs gs) {fss gss} 
  (Hfsgs : composable (fs ++ fss) (gs ++ gss))
  (Hfssgss : composable fss gss) : 
  monarr_norm_equiv 
    (monarrlist_composer_of_composable (fs ++ fss) (gs ++ gss) Hfsgs)
    (monarrtens 
      (monarrlist_composer_of_composable fss gss Hfssgss)
      (monarrlist_composer_of_composable fs gs Hfg)).
Proof.
  unfold monarr_norm_equiv.
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab; [|try easy]
  end;
  rewrite ?Nf_monarrlist_source_app, ?Nf_monarrlist_target_app,
    ?Nf_tens_bwnormapp in *; 
  [|congruence..].
  unfold monarrlist_composer_of_composable.
  rewrite 2!monarr_tens_comp.
  rewrite 2!tens_realize_monarrlist.
  rewrite <- !monarr_assoc.
  rewrite monarrcomp_struct_l'.
  rewrite !monarr_assoc.
  rewrite monarr_arrcomp, monarr_struct_id, monarr_lunit.
  rewrite <- !monarr_assoc.
  apply monarr_comp; [easy|].
  rewrite monarrcomp_struct_l.
  rewrite !monarr_assoc.
  rewrite monarr_arrtens, !monarr_arrcomp, monarr_struct_id, monarr_lunit.
  apply monarr_comp; [easy|].
  apply monarr_struct.
Qed.

Lemma monarrlist_composer_of_composable_app {fs gs} 
  (Hfg : composable fs gs) {fss gss} 
  (Hfsgs : composable (fs ++ fss) (gs ++ gss)): 
  monarr_norm_equiv 
    (monarrlist_composer_of_composable (fs ++ fss) (gs ++ gss) Hfsgs)
    (monarrtens 
      (monarrlist_composer_of_composable fss gss 
        (composable_of_app_composable Hfsgs Hfg))
      (monarrlist_composer_of_composable fs gs Hfg)).
Proof.
  apply monarrlist_composer_of_composable_app_helper.
Qed.


Lemma depairify_apply_compat f (Hf : binary_monarrlist_op_proper f)
  (Hc : forall fs gs, composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs))) 
  (Hprop : forall fs gs (Hfg : composable fs gs)
    (Hc' : forall fs gs, composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs))),
    monarr_norm_equiv 
      (monarrlist_composer_of_composable fs gs Hfg)
      (monarrlist_composer_of_composable (fst (f fs gs)) (snd (f fs gs)) 
        (Hc' fs gs Hfg))) 
  fsgs (Hfsgs : Forall (uncurry composable) fsgs) :
  monarr_norm_equiv 
    (monarrlist_composer_of_composable 
      (fst (depairify fsgs)) (snd (depairify fsgs)) 
      (depairify_composable fsgs Hfsgs))
    
    (monarrlist_composer_of_composable 
      _ _
      (depairify_composable _
        (forall_composable_map Hc Hfsgs))).
Proof.
  induction fsgs as [|[fs gs] fsgs IHfsgs].
  - apply monarr_norm_equiv_of_monarrequiv.
    unfold monarrlist_composer_of_composable.
    simpl.
    rewrite !monarr_arrcomp.
    apply monarr_struct.
  - simpl.
    inversion Hfsgs; subst.
    simpl in * |-.
    eapply monarr_norm_equiv_trans.
    apply (@monarrlist_composer_of_composable_app fs gs ltac:(assumption)).
    eapply monarr_norm_equiv_trans.
    2: {
      apply monarr_norm_equiv_symm.
      apply (monarrlist_composer_of_composable_app (Hc fs gs ltac:(easy))).
    }
    apply monarr_norm_equiv_tens.
    + erewrite monarrlist_composer_of_composable_indep.
      apply monarr_norm_equiv_symm.
      erewrite monarrlist_composer_of_composable_indep.
      apply monarr_norm_equiv_symm.
      apply (IHfsgs ltac:(easy)).
    + apply Hprop.
Qed.

Lemma depairify_pairify_helper_id {fs fss gs gss} 
  (H : composable (fs ++ fss) (gs ++ gss)) :
  depairify (pairify_helper fs gs fss gss) = (fs ++ fss, gs ++ gss).
Proof.
  revert fs gs gss H.
  induction fss; intros fs gs gss H;
  [|destruct gss].
  - simpl.
    now rewrite !app_nil_r.
  - simpl.
    now rewrite !app_nil_r.
  - simpl.
    change (fs ++ a :: fss) with (fs ++ [a] ++ fss) in *.
    change (gs ++ m :: gss) with (gs ++ [m] ++ gss) in *.
    rewrite 2!app_assoc in *.
    destruct (is_composable (fs ++ [a]) (gs ++ [m])) as [c | c].
    + simpl.
      pose proof (composable_of_app_composable H c) as Hc.
      change fss with (nil ++ fss) in Hc.
      change gss with (nil ++ gss) in Hc.
      rewrite (IHfss _ _ _ Hc).
      easy.
    + rewrite (IHfss _ _ _ H).
      easy.
Qed.

Lemma depairify_pairify_id {fss gss} 
  (H : composable fss gss) : 
  depairify (pairify fss gss) = (fss, gss).
Proof.
  unfold pairify. 
  rewrite depairify_pairify_helper_id; easy.
Qed.

Lemma depairify_pairify_monarr_norm_equiv {fss gss} 
  (H : composable fss gss) : 
  monarr_norm_equiv
    (monarrlist_composer_of_composable fss gss H)
    (monarrlist_composer_of_composable 
      (fst (depairify (pairify fss gss)))
      (snd (depairify (pairify fss gss)))
      (depairify_composable _ (pairify_composable _ _ H))).
Proof.
  generalize 
  (depairify_composable (pairify fss gss) (pairify_composable fss gss H)).
  rewrite (depairify_pairify_id H).
  simpl.
  intros ?.
  erewrite monarrlist_composer_of_composable_indep.
  apply monarr_norm_equiv_refl.
Qed.

Lemma pairify_apply_proper f (Hf : binary_monarrlist_op_proper f) :
  binary_monarrlist_op_proper (pairify_apply f).
Proof.
  pose proof Hf as Hf'.
  rewrite binary_proper_iff_composable_proper in Hf.
  apply binary_proper_of_composable_proper.
  - intros fs gs Hfg.
    apply pairify_apply_composable; [apply Hf | apply Hfg].
  - intros fs gs Hfg Hc.
    eapply monarr_norm_equiv_trans.
    apply depairify_pairify_monarr_norm_equiv.
    apply monarr_norm_equiv_symm.
    erewrite monarrlist_composer_of_composable_indep.
    apply monarr_norm_equiv_symm.
    erewrite monarrlist_composer_of_composable_indep.
    apply (depairify_apply_compat _ Hf').
    apply Hf.
    Unshelve.
    + apply pairify_composable, Hfg.
    + apply Hf.
Qed.



Lemma monarrequiv_iff_monarr_norm_equiv {a b} (f g : a ⟶ b) : 
  f ≊ g <-> monarr_norm_equiv f g.
Proof.
  split; [apply monarr_norm_equiv_of_monarrequiv|].
  unfold monarr_norm_equiv.
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab; [|try easy]
  end.
  rewrite monarr_struct_id, monarr_lunit, monarr_struct_id, monarr_runit.
  easy.
Qed.

Definition zip_with_default_l {A B C} (f : A -> B -> C)
  (xs : list A) (ydef : B) : list C :=
  map (fun x => f x ydef) xs.

Definition zip_with_default_r {A B C} (f : A -> B -> C)
  (xdef : A) (ys : list B) : list C :=
  map (f xdef) ys.

Fixpoint zip_defaults {A B C} (f : A -> B -> C)
  (xs : list A) (ys : list B) (xdef : A) (ydef : B) : list C :=
  match xs, ys with
  | nil, ys' => zip_with_default_r f xdef ys'
  | xs', nil => zip_with_default_l f xs' ydef
  | x::xs', y::ys' => (f x y) :: zip_defaults f xs' ys' xdef ydef
  end.

Fixpoint foliate_monarr {a b} (f : a ⟶ b) : list monarrlist :=
  match f with
  | monarrcomp g h => foliate_monarr g ++ foliate_monarr h
  | monarrtens g h => 
    zip_defaults (@app monarrlistelt) (foliate_monarr h) (foliate_monarr g)
      (monarrlist_id (monarrlist_list_target (foliate_monarr h)) :: nil)
      (monarrlist_id (monarrlist_list_target (foliate_monarr g)) :: nil)
  | monarrstruct f => (monarrlist_arr _ _ (monarrstruct f) :: nil) :: nil
  | mongeneric f => (monarrlist_arr _ _ (mongeneric f) :: nil) :: nil
  end.

Lemma app_composable_of_composable_mid {fss gss} 
  (Hf : totally_composable fss) (Hg : totally_composable gss) 
  (Hfg : Nf (monarrlist_list_target fss) = Nf (monarrlist_list_source gss)) :
  totally_composable (fss ++ gss).
Proof.
  induction fss.
  - apply Hg.
  - simpl.
    destruct fss.
    + simpl.
      destruct gss; [easy|].
      split;
      [apply Hfg|].
      apply Hg.
    + split;
      [apply Hf|].
      apply IHfss; [apply Hf|].
      apply Hfg.
Qed.

Lemma foliate_monarr_not_nil {a b} (f : a ⟶ b) : 
  foliate_monarr f <> [].
Proof.
  induction f; try easy; simpl;
  destruct (foliate_monarr f1); 
  destruct (foliate_monarr f2); easy.
Qed.

Lemma monarrlist_list_source_app_not_nil {fss} (H : fss <> []) gss : 
  monarrlist_list_source (fss ++ gss) = monarrlist_list_source fss.
Proof.
  rewrite monarrlist_list_source_app.
  destruct fss; easy.
Qed.

Lemma monarrlist_list_target_app_not_nil {gss} (H : gss <> []) fss : 
  monarrlist_list_target (fss ++ gss) = monarrlist_list_target gss.
Proof.
  destruct gss; [easy|].
  now rewrite monarrlist_list_target_app.
Qed.

Lemma monarrlist_list_source_foliate {a b} (f : a ⟶ b) :
  Nf (monarrlist_list_source (foliate_monarr f)) = Nf a.
Proof.
  induction f; simpl; try easy.
  - rewrite monarrlist_list_source_app_not_nil by apply foliate_monarr_not_nil.
    easy.
  - pose proof (foliate_monarr_not_nil f1).
    pose proof (foliate_monarr_not_nil f2).
    destruct (foliate_monarr f1); 
    destruct (foliate_monarr f2); try easy.
    simpl in *.
    rewrite Nf_monarrlist_source_app, Nf_tens_bwnormapp.
    f_equal; easy.
Qed.

Require Import Arith.

(* Lemma monarrlist_list_target_zip_defaults fss gss fdef gdef :
  monarrlist_list_target (zip_defaults (@app monarrlistelt)
    fss gss fdef gdef) = 
  if (length fss =? 0) && (length gss =? 0) then e else
  (if length fss <=? length gss then monarrlist_list_target gss else monarrlist_target gdef)
  ⨂ (if length gss <=? length fss then monarrlist_list_target fss else monarrlist_target fdef).
Proof.
  revert gss fdef gdef;
  induction fss;
  intros gss fdef gdef.
  - simpl.
    induction gss; [easy|].
    + simpl.
      
  - *)

Lemma zip_defaults_cons {A B C} (f : A -> B -> C) x y xs ys xdef ydef :
  zip_defaults f (x :: xs) (y :: ys) xdef ydef =
  (f x y) :: zip_defaults f xs ys xdef ydef.
Proof.
  easy.
Qed.

Lemma monarrlist_list_target_cons_cons f f' fs :
  monarrlist_list_target (f :: f' :: fs) = monarrlist_list_target (f' :: fs).
Proof.
  easy.
Qed.

Lemma monarrlist_list_target_foliate_helper fss gss :
  Nf (monarrlist_list_target
     (zip_defaults (app (A:=monarrlistelt)) gss fss
        [monarrlist_id (monarrlist_list_target gss)]
        [monarrlist_id (monarrlist_list_target fss)])) = 
  bwnormapp 
    (Nf (monarrlist_list_target fss)) (Nf (monarrlist_list_target gss)).
Proof.
  revert fss;
  induction gss; intro fss.
  - simpl. 
    induction fss; [easy|].
    simpl.
    destruct fss; [easy|].
    apply IHfss.
  - destruct gss.
    + induction fss.
      * simpl.
        rewrite Nf_monarrlist_target_app.
        easy.
      * simpl.
        destruct fss;
        [apply Nf_monarrlist_target_app|].
        simpl (monarrlist_list_target [a]) in IHfss.
        rewrite <- IHfss.
        simpl.
        destruct (zip_with_default_r (app (A:=monarrlistelt)) [monarrlist_id (monarrlist_target a)] fss).
        change (?x :: l) with ((x::nil) ++ l).
        rewrite 2!Nf_monarrlist_target_app.
        easy.
        easy.
    + destruct fss;
      [apply (IHgss nil)|].
      rewrite zip_defaults_cons.
      rewrite monarrlist_list_target_cons_cons.
      destruct fss.
      simpl zip_defaults.
      simpl monarrlist_list_target.
      destruct gss.
      simpl.
      rewrite Nf_monarrlist_target_app; easy.
      destruct gss.
      simpl.
      rewrite Nf_monarrlist_target_app; easy.
      rewrite 2!monarrlist_list_target_cons_cons in *.
      specialize (IHgss (l0::nil)).
      simpl (monarrlist_list_target (l0 :: nil)) in IHgss.
      rewrite <- IHgss.
      easy.
      rewrite monarrlist_list_target_cons_cons.
      rewrite <- IHgss.
      easy.
Qed.

Lemma monarrlist_list_target_foliate {a b} (f : a ⟶ b) :
  Nf (monarrlist_list_target (foliate_monarr f)) = Nf b.
Proof.
  induction f; simpl; try easy.
  - rewrite monarrlist_list_target_app_not_nil by apply foliate_monarr_not_nil.
    easy.
  - rewrite monarrlist_list_target_foliate_helper.
    rewrite Nf_tens_bwnormapp.
    f_equal; easy.
Qed.


Lemma foliate_monarr_totally_composable {a b} (f : a ⟶ b) :
  totally_composable (foliate_monarr f).
Proof.
  induction f; try easy.
  simpl.
  apply app_composable_of_composable_mid; try easy.
  rewrite monarrlist_list_target_foliate, monarrlist_list_source_foliate.
  easy.
  simpl.
  revert IHf1 IHf2.
  generalize (foliate_monarr f2).
  generalize (foliate_monarr f1).
  clear f1 f2.
  intros fss.
  induction fss; intros gss; [|destruct fss]; intros Hf Hg.
  - induction gss; [easy|].
    simpl. 
    destruct gss; [easy|].
    split; [|apply IHgss, Hg].
    apply composable_app;
    [apply Hg|].
    easy.
  - induction gss; [easy|].
    simpl.
    destruct gss; [easy|].
    split;
    [apply composable_app; [apply Hg| easy]|].
    simpl in IHgss.
    destruct gss; try (apply IHgss); try assumption + easy.
    split; [|apply IHgss].
    apply composable_app.
    apply Hg.
    easy.
    intros.
    apply Hg.
  - induction gss; [|destruct gss].
    + clear IHfss.
      split; [apply composable_app; [easy|apply Hf]|].
      apply (@totally_composable_app_restrict_r (a0::nil) _) in Hf.
      revert l Hf.
      induction fss;
      intros l Hf; [easy|].
      split; [apply composable_app; [easy|apply Hf]|].
      apply IHfss, Hf.
    + clear IHfss IHgss.
      split; [apply composable_app; [easy|apply Hf]|].
      apply (@totally_composable_app_restrict_r (a0::nil) _) in Hf.
      revert l Hf.
      induction fss;
      split; [apply composable_app; [easy|apply Hf]|].
      apply IHfss, Hf.
    + split; [apply composable_app; [apply Hg|apply Hf]|].
      rewrite 2!monarrlist_list_target_cons_cons.
      apply (IHfss (l0 :: gss));
      [apply Hf | apply Hg].
Qed.

Lemma middle_arr_composable_of_totally_composable_nonempty 
  {fss fss'} (H : totally_composable (fss ++ fss')) 
  (Hfss : fss <> []) (Hfss' : fss' <> []) : 
  Nf (monarrlist_list_target fss)
  = Nf (monarrlist_list_source fss').
Proof.
  destruct fss, fss'; [easy..|].
  apply middle_arr_composable_of_totally_composable; assumption.
Qed.


Lemma compose_monarrlist_list_of_totally_composable_app_nonempty
  {fss fss'} (H : totally_composable (fss ++ fss')) 
  (Hfss : fss <> []) (Hfss' : fss' <> []) : 
  monarrequiv _ _ 
    (compose_monarrlist_list_of_totally_composable _ H)
    (monarrcomp (monarrcomp 
      (bwarr_id_cast (monarrlist_list_source_app_not_nil Hfss _))
      (monarr_composer_of_composable
        (compose_monarrlist_list_of_totally_composable fss
          (totally_composable_app_restrict_l H))
        (compose_monarrlist_list_of_totally_composable fss'
          (totally_composable_app_restrict_r H))
        (middle_arr_composable_of_totally_composable_nonempty H Hfss Hfss')))
      (bwarr_id_cast (eq_sym (monarrlist_list_target_app_not_nil Hfss' _)))).
Proof.
  destruct fss, fss'; [easy..|].
  rewrite compose_monarrlist_list_of_totally_composable_app_helper.
  rewrite monarr_struct_id, monarr_lunit.
  apply monarr_comp; [|apply monarr_struct].
  erewrite monarr_composer_of_composable_indep.
  easy.
Qed.

Lemma monarrlist_target_singleton fss : 
  monarrlist_target [fss] = e ⨂ target fss.
Proof.
  easy.
Qed.

Lemma zip_with_default_l_totally_composable {fss} 
  (Hf : totally_composable fss) a :
  totally_composable 
    (zip_with_default_l (@app monarrlistelt) fss [monarrlist_id a]).
Proof.
  induction fss; [easy|destruct fss; [easy|]].
  split.
  - apply composable_app; [apply Hf | easy].
  - apply IHfss, Hf.
Qed.

Lemma zip_with_default_r_totally_composable {fss} 
  (Hf : totally_composable fss) a :
  totally_composable 
    (zip_with_default_r (@app monarrlistelt) [monarrlist_id a] fss).
Proof.
  induction fss; [easy|destruct fss; [easy|]].
  split.
  - apply composable_app; [easy | apply Hf].
  - apply IHfss, Hf.
Qed.

Lemma zip_with_default_l_source_nonempty {fss} (H : fss <> []) a :
  Nf (monarrlist_list_source (zip_with_default_l (@app monarrlistelt) fss a))
  = Nf (monarrlist_source a ⨂ monarrlist_list_source fss).
Proof.
  destruct fss; [easy|].
  apply Nf_monarrlist_source_app'.
Qed.

Lemma zip_with_default_l_target_nonempty {fss} (H : fss <> []) a :
  Nf (monarrlist_list_target (zip_with_default_l (@app monarrlistelt) fss a))
  = Nf (monarrlist_target a ⨂ monarrlist_list_target fss).
Proof.
  induction fss; [easy|].
  destruct fss; [apply Nf_monarrlist_target_app'|].
  apply IHfss; easy.
Qed.

Lemma zip_with_default_r_source_nonempty {fss} (H : fss <> []) a :
  Nf (monarrlist_list_source (zip_with_default_r (@app monarrlistelt) a fss))
  = Nf (monarrlist_list_source fss ⨂ monarrlist_source a).
Proof.
  destruct fss; [easy|].
  apply Nf_monarrlist_source_app'.
Qed.

Lemma zip_with_default_r_target_nonempty {fss} (H : fss <> []) a :
  Nf (monarrlist_list_target (zip_with_default_r (@app monarrlistelt) a fss))
  = Nf (monarrlist_list_target fss ⨂ monarrlist_target a).
Proof.
  induction fss; [easy|].
  destruct fss; [apply Nf_monarrlist_target_app'|].
  apply IHfss; easy.
Qed.

Lemma zip_defaults_target_nonempty {fss gss} (Hf : fss <> []) (Hg : gss <> []) : 
  Nf (monarrlist_list_target (zip_defaults (@app monarrlistelt)
    fss gss 
    [monarrlist_id (monarrlist_list_target fss)]
    [monarrlist_id (monarrlist_list_target gss)])) 
  = Nf (monarrlist_list_target gss ⨂ monarrlist_list_target fss).
Proof.
  revert gss Hg;
  induction fss; 
  intros gss Hg; [
  apply (zip_with_default_r_target_nonempty Hg)|]. 
  destruct fss.
  - destruct gss; [easy|].
    destruct gss; [apply Nf_monarrlist_target_app'|].
    rewrite zip_defaults_cons.
    change (?a :: ?l) with ((a::nil) ++ l).
    rewrite monarrlist_list_target_app_not_nil by easy.
    etransitivity.
    apply zip_with_default_r_target_nonempty; easy.
    rewrite monarrlist_list_target_app.
    easy.
  - destruct gss; [easy|].
    destruct gss.
    + rewrite zip_defaults_cons.
      change (?a :: ?l) with ((a::nil) ++ l).
      rewrite monarrlist_list_target_app_not_nil by easy.
      etransitivity.
      apply zip_with_default_l_target_nonempty; easy.
      rewrite monarrlist_list_target_app.
      easy.
    + rewrite zip_defaults_cons.
      change (?a :: ?l) with ((a::nil) ++ l).
      rewrite monarrlist_list_target_app_not_nil by easy.
      rewrite 2!monarrlist_list_target_cons_cons.
      rewrite (IHfss ltac:(easy) (l1 :: gss) ltac:(easy)).
      rewrite 2!monarrlist_list_target_app_not_nil by easy.
      easy.
Qed.

Lemma zip_defaults_source_nonempty {fss gss} (Hf : fss <> []) (Hg : gss <> []) : 
  Nf (monarrlist_list_source (zip_defaults (@app monarrlistelt)
    fss gss 
    [monarrlist_id (monarrlist_list_target fss)]
    [monarrlist_id (monarrlist_list_target gss)])) 
  = Nf (monarrlist_list_source gss ⨂ monarrlist_list_source fss).
Proof.
  destruct fss, gss; try easy.
  apply Nf_monarrlist_source_app'.
Qed.




Lemma monarr_tens_id_split_bot {a b c} (f : a ⟶ b) (g : b ⟶ c) x :
  monarrtens (arrid x) (monarrcomp f g) 
  ≊ monarrcomp (monarrtens (arrid x) f) (monarrtens (arrid x) g).
Proof.
  now rewrite <- monarr_tens_comp, monarr_lunit.
Qed.


Lemma monarr_tens_id_split_top {a b c} (f : a ⟶ b) (g : b ⟶ c) x :
  monarrtens (monarrcomp f g) (arrid x) 
  ≊ monarrcomp (monarrtens f (arrid x)) (monarrtens g (arrid x)).
Proof.
  now rewrite <- monarr_tens_comp, monarr_lunit.
Qed.


Lemma zip_with_default_l_equiv_nonempty {fss} (Hne : fss <> []) 
  (Hf : totally_composable fss) a :
  compose_monarrlist_list_of_totally_composable
    _ (zip_with_default_l_totally_composable Hf a)
  ≊ 
    monarrcomp (monarrcomp 
    (monarr_of_Nf_eq (zip_with_default_l_source_nonempty Hne [monarrlist_id a]))
    (monarrtens 
    (arrid (e⨂a))
    (compose_monarrlist_list_of_totally_composable fss Hf)))
    (monarr_of_Nf_eq (eq_sym 
    (zip_with_default_l_target_nonempty Hne [monarrlist_id a]))).
Proof.
  induction fss; [|destruct fss].
  - simpl.
    rewrite !monarr_arrtens, !monarr_arrcomp.
    apply monarr_struct.
  - simpl.
    rewrite realize_monarrlist_app.
    apply monarr_comp; [apply monarr_comp|]; try apply monarr_struct.
    simpl; rewrite monarr_arrtens, (monarr_struct_id (_ ⊠ _)).
    easy.
  - simpl zip_with_default_l in *.
    rewrite 2!compose_monarrlist_list_of_totally_composable_cons.
    erewrite compose_monarrlist_list_of_totally_composable_indep.
    unshelve (rewrite IHfss); [abstract (easy) + apply Hf .. |].
    unfold monarr_composer_of_composable.
    rewrite realize_monarrlist_app.
    Local Notation "x ⊡ y" := (monarrcomp x y) (at level 50, only printing).
    rewrite <- 6!monarr_assoc.
    rewrite monarrcomp_struct_l.
    rewrite !monarr_assoc.
    rewrite monarr_arrcomp.
    rewrite (monarr_struct_id (_ ○ _)), monarr_lunit.
    simpl (compose_monarrlist_list_of_totally_composable (((monarrlist_id _)::nil) ::nil) Logic.I).
    
    rewrite !monarr_tens_id_split_bot.
    rewrite <- !monarr_assoc.
    apply monarr_comp; [apply monarr_tens;
      [simpl; rewrite monarr_arrtens; apply monarr_struct|easy]|].
    rewrite monarr_arrtens.
    rewrite monarrcomp_struct_l'.
    rewrite !monarr_assoc.
    rewrite !monarr_arrcomp.
    unfold monarrlist_list_source.
    unfold monarrlist_source.
    simpl fold_right.
    rewrite monarr_struct_id, monarr_lunit.
    apply monarr_comp; [|apply monarr_struct].
    erewrite compose_monarrlist_list_of_totally_composable_indep.
    easy.
Qed. 


Lemma zip_with_default_r_equiv_nonempty {fss} (Hne : fss <> []) 
  (Hf : totally_composable fss) a :
  compose_monarrlist_list_of_totally_composable
    _ (zip_with_default_r_totally_composable Hf a)
  ≊ 
    monarrcomp (monarrcomp 
    (monarr_of_Nf_eq (zip_with_default_r_source_nonempty Hne [monarrlist_id a]))
    (monarrtens 
    (compose_monarrlist_list_of_totally_composable fss Hf)
    (arrid (e ⨂ a))))
    (monarr_of_Nf_eq (eq_sym 
    (zip_with_default_r_target_nonempty Hne [monarrlist_id a]))).
Proof.
  induction fss; [|destruct fss].
- simpl.
  rewrite !monarr_arrtens, !monarr_arrcomp.
  apply monarr_struct.
- simpl.
  
  rewrite (monarr_struct _ (arrid (monarrlist_source a0) ⊠ arrinvlunitor a)).
  rewrite <- monarr_arrtens.
  
  rewrite <- (monarr_tens_comp (arrid (monarrlist_source a0)) (realize_monarrlist a0)
    (arrinvlunitor a)).
  rewrite monarr_lunit.
  rewrite (monarr_struct _ (arrid (monarrlist_target a0) ⊠ arrlunitor a)).
  rewrite monarr_runit.
  rewrite <- monarr_arrtens.
  rewrite <- (monarr_tens_comp (realize_monarrlist a0) (arrid _)
    (arrinvlunitor a) (arrlunitor a)), monarr_runit.
  apply monarr_tens; [easy | rewrite monarr_arrcomp; apply monarr_struct].
- simpl zip_with_default_r in *.
  rewrite 2!compose_monarrlist_list_of_totally_composable_cons.
  erewrite compose_monarrlist_list_of_totally_composable_indep.
  unshelve (rewrite IHfss); [abstract (easy) + apply Hf .. |].
  unfold monarr_composer_of_composable.
  simpl realize_monarrlist.
  rewrite !monarr_assoc.
  rewrite <- (monarr_assoc (monarrtens (realize_monarrlist a0) (arrid a))).
  rewrite monarr_arrcomp.
  rewrite 2!monarr_tens_id_split_top.
  (* rewrite <- !monarr_assoc. *)
  rewrite monarr_arrtens.
  rewrite (monarr_struct _ (arrid (monarrlist_source a0) ⊠ arrinvlunitor a)).
  rewrite !monarr_assoc.
  rewrite <- monarr_arrtens.
  rewrite <- (monarr_tens_comp (arrid (monarrlist_source a0)) (realize_monarrlist a0)
    (arrinvlunitor a) (arrid (e ⨂ a))).
  rewrite monarr_lunit, monarr_runit.
  rewrite <- (monarr_runit (realize_monarrlist a0)) at 2.
  rewrite <- (monarr_lunit (arrinvlunitor a)).
  rewrite monarr_tens_comp.
  rewrite <- !monarr_assoc.
  apply monarr_comp; [easy|].
  rewrite monarr_arrtens.
  rewrite 2!monarrcomp_struct_l'.
  rewrite !monarr_assoc.
  rewrite 2!monarr_arrcomp.
  rewrite (monarr_struct_id (_ ○ _)), monarr_lunit.
  apply monarr_comp; [|apply monarr_struct].
  erewrite compose_monarrlist_list_of_totally_composable_indep.
  easy.
Qed.



Lemma zip_defaults_totally_composable {fss gss} 
  (Hf : totally_composable fss) 
  (Hg : totally_composable gss) : 
  totally_composable 
    (zip_defaults (@app monarrlistelt)
      fss gss
      (monarrlist_id (monarrlist_list_target fss) :: nil)
      (monarrlist_id (monarrlist_list_target gss) :: nil)).
Proof.
  revert gss Hg;
  induction fss; intros gss Hg; [|revert a Hf; induction gss as [|l gss IHgss]; 
    intros a Hf; [|destruct fss; [|destruct gss]]].
  - apply zip_with_default_r_totally_composable, Hg.
  - apply zip_with_default_l_totally_composable, Hf.
  - destruct gss; [easy|].
    split.
    + apply composable_app; [easy | apply Hg].
    + apply (@zip_with_default_r_totally_composable (l0 :: gss) (proj2 Hg)).
  - split.
    + apply composable_app; [apply Hf | easy].
    + apply (@zip_with_default_l_totally_composable (l0 :: fss) (proj2 Hf)).
  - split.
    + apply composable_app; [apply Hf | apply Hg].
    + rewrite 2!monarrlist_list_target_cons_cons.
      apply (IHfss (proj2 Hf) (l1 :: gss)), Hg.
Qed.


Local Notation "f ⧆ g" := (monarrtens f g) (at level 40, left associativity).
Local Notation "f ◌ g" := (monarrcomp f g) (at level 50, left associativity).

Section tens_comp_split.

Context {a b c m n o : bw} (f : a ⟶ b) (g : b ⟶ c) 
  (h : m ⟶ n) (j : n ⟶ o).

Lemma monarr_tens_comp_split_diag :
  f ⧆ h ≊ (f ⧆ arrid m) ◌ (arrid b ⧆ h).
Proof.
  now rewrite <- monarr_tens_comp, monarr_lunit, monarr_runit.
Qed.

Lemma monarr_tens_comp_split_antidiag :
  f ⧆ h ≊ (arrid a ⧆ h) ◌ (f ⧆ arrid n).
Proof.
  now rewrite <- monarr_tens_comp, monarr_lunit, monarr_runit.
Qed.
  

Lemma monarr_tens_comp_split_bot_l :
  f ⧆ (h ◌ j) ≊
    (arrid a ⧆ h) ◌ (f ⧆ j).
Proof.
  now rewrite <- monarr_tens_comp, monarr_lunit.
Qed.

Lemma monarr_tens_comp_split_bot_r :
  f ⧆ (h ◌ j) ≊
    (f ⧆ h) ◌ (arrid b ⧆ j).
Proof.
  now rewrite <- monarr_tens_comp, monarr_runit.
Qed.

Lemma monarr_tens_comp_split_top_l :
  (f ◌ g) ⧆ h ≊
    (f ⧆ arrid m) ◌ (g ⧆ h).
Proof.
  now rewrite <- monarr_tens_comp, monarr_lunit.
Qed.

Lemma monarr_tens_comp_split_top_r :
  (f ◌ g) ⧆ h ≊
    (f ⧆ h) ◌ (g ⧆ arrid n).
Proof.
  now rewrite <- monarr_tens_comp, monarr_runit.
Qed.

End tens_comp_split.



Lemma tens_zip_defaults_correct_helper {fss gss} (Hnf : fss <> []) (Hng : gss <> [])
  (Hf : totally_composable fss) (Hg : totally_composable gss) :
  compose_monarrlist_list_of_totally_composable
    _ (zip_defaults_totally_composable Hf Hg)
  ≊ 
    monarrcomp (monarrcomp 
    (monarr_of_Nf_eq (zip_defaults_source_nonempty Hnf Hng))
    (monarrtens 
    (compose_monarrlist_list_of_totally_composable gss Hg)
    (compose_monarrlist_list_of_totally_composable fss Hf)))
    (monarr_of_Nf_eq (eq_sym 
      (zip_defaults_target_nonempty Hnf Hng))).
Proof.
  revert gss Hg Hng;
  induction fss;
  intros gss Hg Hng; [easy|destruct gss; [easy|]].
  destruct fss, gss.
  - simpl.
    rewrite realize_monarrlist_app.
    apply monarr_comp; [apply monarr_comp|];
    easy + apply monarr_struct.
  - simpl zip_defaults.
    rewrite 2!compose_monarrlist_list_of_totally_composable_cons.
    unfold monarr_composer_of_composable.
    pose proof (@zip_with_default_r_equiv_nonempty (l0 :: gss) 
      (fun x => nil_cons (eq_sym x)) (proj2 Hg) (monarrlist_target a)) as H.
    simpl zip_with_default_r in H.
    erewrite compose_monarrlist_list_of_totally_composable_indep.
    rewrite H; clear H.
    rewrite realize_monarrlist_app.
    rewrite <- !monarr_assoc.
    rewrite monarrcomp_struct_l.
    rewrite !(monarr_assoc (_ ^-)), monarr_arrcomp.
    rewrite monarr_tens_comp_split_top_r.
    rewrite (monarr_struct_id (_ ^- ○ _)), monarr_lunit.
    rewrite <- monarr_assoc.
    apply monarr_comp; [easy|].
    rewrite monarr_tens_comp_split_top_r.
    rewrite <- monarr_assoc.
    rewrite monarr_arrtens, monarrcomp_struct_l'.
    rewrite !monarr_assoc, !monarr_arrcomp.
    rewrite (monarr_struct _ (arrid _ ⊠ arrinvlunitor _)).
    rewrite <- monarr_arrtens, <- monarr_tens_comp, monarr_lunit, monarr_runit.
    rewrite monarr_tens_comp_split_diag.
    rewrite <- !monarr_assoc.
    apply monarr_comp; [easy|].
    rewrite monarr_arrtens, monarr_arrcomp.
    apply monarr_struct.
  - simpl zip_defaults.
    rewrite 2!compose_monarrlist_list_of_totally_composable_cons.
    unfold monarr_composer_of_composable.
    pose proof (@zip_with_default_l_equiv_nonempty (l0 :: fss) 
      (fun x => nil_cons (eq_sym x)) (proj2 Hf) (monarrlist_target l)) as H.
    simpl zip_with_default_l in H.
    erewrite compose_monarrlist_list_of_totally_composable_indep.
    rewrite H; clear H.
    rewrite realize_monarrlist_app.
    rewrite <- !monarr_assoc.
    rewrite monarrcomp_struct_l.
    rewrite !(monarr_assoc (_ ^-)), monarr_arrcomp.
    rewrite monarr_tens_comp_split_bot_r.
    rewrite (monarr_struct_id (_ ^- ○ _)), monarr_lunit.
    rewrite <- monarr_assoc.
    apply monarr_comp; [easy|].
    rewrite monarr_tens_comp_split_bot_r.
    rewrite <- monarr_assoc.
    rewrite monarr_arrtens, monarrcomp_struct_l'.
    rewrite !monarr_assoc, !monarr_arrcomp.
    rewrite (monarr_struct _ (arrinvlunitor _ ⊠ arrid _)).
    rewrite <- monarr_arrtens, <- monarr_tens_comp, monarr_lunit, monarr_runit.
    rewrite monarr_tens_comp_split_antidiag.
    rewrite <- !monarr_assoc.
    apply monarr_comp; [easy|].
    rewrite monarr_arrtens, monarr_arrcomp.
    apply monarr_struct.
  - specialize (IHfss (fun x => nil_cons (eq_sym x)) (proj2 Hf) 
    (l1::gss) (proj2 Hg) (fun x => nil_cons (eq_sym x))).
    change (zip_defaults ?f (a :: l0 :: fss) (l :: l1 :: gss)
      [monarrlist_id (monarrlist_list_target (a :: l0 :: fss))]
      [monarrlist_id (monarrlist_list_target (l :: l1 :: gss))])
    with ((a ++ l) :: (l0 ++ l1) :: (zip_defaults f (fss) (gss)
    [monarrlist_id (monarrlist_list_target (l0 :: fss))]
    [monarrlist_id (monarrlist_list_target (l1 :: gss))])).
    rewrite compose_monarrlist_list_of_totally_composable_cons.
    change ((l0 ++ l1) :: (zip_defaults ?f (fss) (gss)
      [monarrlist_id (monarrlist_list_target (l0 :: fss))]
      [monarrlist_id (monarrlist_list_target (l1 :: gss))]))
    with (zip_defaults f (l0 :: fss) (l1 :: gss)
      [monarrlist_id (monarrlist_list_target (l0 :: fss))]
      [monarrlist_id (monarrlist_list_target (l1 :: gss))]).
    unfold monarr_composer_of_composable.
    erewrite compose_monarrlist_list_of_totally_composable_indep.
    rewrite IHfss.
    rewrite 2!compose_monarrlist_list_of_totally_composable_cons.
    unfold monarr_composer_of_composable.
    rewrite <- 3!(monarr_assoc (realize_monarrlist _)).
    rewrite 2!monarr_tens_comp.
    rewrite realize_monarrlist_app.
    rewrite <- !monarr_assoc.
    apply monarr_comp; [apply monarr_struct|].
    apply monarr_comp; [easy|].
    rewrite monarr_arrtens.
    rewrite !monarr_assoc.
    rewrite !monarr_arrcomp.
    erewrite (monarr_struct (monarr_of_Nf_eq (eq_sym _))), 
    monarr_struct.
    easy.
Qed.

Lemma tens_zip_defaults_correct {fss gss} (Hnf : fss <> []) (Hng : gss <> [])
  (Hf : totally_composable fss) (Hg : totally_composable gss) 
  Hcomp :
  compose_monarrlist_list_of_totally_composable
    (zip_defaults (app (A:=monarrlistelt)) fss gss
	    [monarrlist_id (monarrlist_list_target fss)]
      [monarrlist_id (monarrlist_list_target gss)]) 
    Hcomp
  ≊ 
    monarrcomp (monarrcomp 
    (monarr_of_Nf_eq (zip_defaults_source_nonempty Hnf Hng))
    (monarrtens 
    (compose_monarrlist_list_of_totally_composable gss Hg)
    (compose_monarrlist_list_of_totally_composable fss Hf)))
    (monarr_of_Nf_eq (eq_sym 
      (zip_defaults_target_nonempty Hnf Hng))).
Proof.
  erewrite compose_monarrlist_list_of_totally_composable_indep.
  apply tens_zip_defaults_correct_helper.
Qed.

Lemma foliate_correct {a b} (f : a ⟶ b) :
  f ≊
  monarrcomp (monarrcomp
    (monarr_of_Nf_eq (eq_sym (monarrlist_list_source_foliate f)))
    (compose_monarrlist_list_of_totally_composable 
      (foliate_monarr f)
      (foliate_monarr_totally_composable f)))
    (monarr_of_Nf_eq (monarrlist_list_target_foliate f)).
Proof.
  induction f.
  - simpl.
    rewrite (@compose_monarrlist_list_of_totally_composable_app_nonempty
      (foliate_monarr f1) (foliate_monarr f2)
      (foliate_monarr_totally_composable (monarrcomp f1 f2))
      (foliate_monarr_not_nil f1) 
      (foliate_monarr_not_nil f2)).
    rewrite IHf1, IHf2 at 1.
    clear IHf1 IHf2. 
    unfold monarr_composer_of_composable.
    rewrite <- 8!monarr_assoc, 1!monarr_arrcomp.
    rewrite monarrcomp_struct_l.
    rewrite !monarr_assoc, !monarr_arrcomp.
    rewrite monarr_struct_id, monarr_lunit.
    rewrite <- !monarr_assoc.
    apply monarr_comp;
    [erewrite compose_monarrlist_list_of_totally_composable_indep; easy|].
    rewrite 2!monarrcomp_struct_l, monarrcomp_struct_r.
    rewrite !monarr_assoc, !monarr_arrcomp.
    rewrite monarr_struct_id, monarr_lunit. 
    rewrite <- !monarr_assoc, !monarr_arrcomp.
    rewrite monarr_struct_id, monarr_runit.
    erewrite compose_monarrlist_list_of_totally_composable_indep; easy.
  - simpl foliate_monarr.
    unshelve (rewrite tens_zip_defaults_correct);
    [apply foliate_monarr_not_nil + apply foliate_monarr_totally_composable..|].
    rewrite IHf1, IHf2 at 1.
    rewrite 2!monarr_tens_comp, 2!monarr_arrtens.
    symmetry.
    rewrite <- 2!monarr_assoc, monarr_arrcomp.
    rewrite 2!monarr_assoc.
    rewrite monarr_arrcomp.
    apply monarr_comp; [apply monarr_comp|];
    easy + apply monarr_struct.
  - simpl.
    rewrite (monarr_struct _ (arrlunitor b)), 
      <- monarr_assoc, <- (monarr_lunitor_nat (mongeneric f)).
    rewrite monarr_assoc, monarr_arrcomp, monarr_struct_id, monarr_lunit.
    easy.
  - simpl.
    rewrite (monarr_struct _ (arrlunitor b)), 
      <- monarr_assoc, <- (monarr_lunitor_nat f).
    rewrite monarr_assoc, monarr_arrcomp, monarr_struct_id, monarr_lunit.
    easy.
Qed.

Lemma compose_equiv_of_eq {fss gss} (H : fss = gss)
  (Hf : totally_composable fss) (Hg : totally_composable gss) : 
  compose_monarrlist_list_of_totally_composable _ Hf ≊
  bwarr_id_cast (f_equal monarrlist_list_source H) ◌
  compose_monarrlist_list_of_totally_composable _ Hg ◌
  bwarr_id_cast (f_equal monarrlist_list_target (eq_sym H)).
Proof.
  subst.
  rewrite monarr_struct_id, monarr_lunit.
  rewrite monarr_struct_id, monarr_runit.
  erewrite compose_monarrlist_list_of_totally_composable_indep.
  easy.
Qed.



Lemma equiv_of_foliate_eq {a b} (f g : a ⟶ b) : 
  foliate_monarr f = foliate_monarr g ->
  f ≊ g.
Proof.
  intros Heq.
  rewrite foliate_correct, (foliate_correct g).
  rewrite monarrcomp_struct_r, monarrcomp_struct_l.
  rewrite <- monarr_assoc, monarr_arrcomp.
  rewrite !monarr_assoc, monarr_arrcomp.
  erewrite (compose_equiv_of_eq Heq _ (foliate_monarr_totally_composable g)).
  apply monarr_comp; [apply monarr_comp|];
  easy + apply monarr_struct.
Qed.

Definition monarrlistelt_equiv (f g : monarrlistelt) :=
  monarr_norm_equiv 
    (realize_monarrlistelt f)
    (realize_monarrlistelt g).

Fixpoint ForallF {A} (P : A -> Prop) (l : list A) : Prop :=
  match l with
  | nil => True
  | a :: l' => P a /\ ForallF P l'
  end.

Lemma ForallFE {A} (P : A -> Prop) (l : list A) :
  ForallF P l = fold_right and True (map P l).
Proof.
  induction l; [easy|].
  simpl.
  f_equal; apply IHl.
Qed.

Lemma ForallF_iff_Forall {A} (P : A -> Prop) (l : list A) :
  ForallF P l <-> Forall P l.
Proof.
  induction l; [easy|].
  rewrite Forall_cons_iff, <- IHl.
  easy.
Qed.

Definition all_monarrlist_equiv (fs gs : monarrlist) :=
  ForallF (uncurry monarrlistelt_equiv) 
    (zip_defaults pair fs gs (monarrlist_id e) (monarrlist_id e)).

Definition all_monarrlist_list_equiv (fss gss : list monarrlist) :=
  ForallF (uncurry all_monarrlist_equiv)
    (zip_defaults pair fss gss nil nil).

Lemma monarr_norm_equiv_of_Nfs_eq_equiv {a b a' b'} {f : a ⟶ b} {g : a' ⟶ b'}
  (Ha : Nf a = Nf a') (Hb : Nf b = Nf b') :
    f ≊ monarr_of_Nf_eq Ha ◌ g ◌ monarr_of_Nf_eq (eq_sym Hb)
  -> monarr_norm_equiv f g.
Proof.
  intros Hequiv.
  unfold monarr_norm_equiv.
  destruct (eqbwnorm (Nf a') (Nf a)); [|congruence].
  destruct (eqbwnorm (Nf b) (Nf b')); [|congruence].
  rewrite Hequiv.
  rewrite 2!monarr_assoc, monarr_arrcomp, monarr_struct_id, monarr_lunit.
  rewrite <- monarr_assoc, monarr_arrcomp, monarr_struct_id, monarr_runit.
  easy.
Qed.

Lemma zip_defaults_nil_r {A B C} (f : A -> B -> C) xs xdef ydef :
  zip_defaults f xs [] xdef ydef = 
  zip_with_default_l f xs ydef.
Proof.
  destruct xs; easy.
Qed.

Lemma all_monarrlist_cons_equiv_nil {a fs} : 
  all_monarrlist_equiv (a :: fs) [] ->
  all_monarrlist_equiv fs [].
Proof.
  unfold all_monarrlist_equiv.
  rewrite 2!zip_defaults_nil_r.
  simpl.
  easy.
Qed.

Lemma all_monarrlist_list_cons_equiv_nil {a fss} : 
  all_monarrlist_list_equiv (a :: fss) [] ->
  all_monarrlist_list_equiv fss [].
Proof.
  unfold all_monarrlist_list_equiv.
  rewrite 2!zip_defaults_nil_r.
  simpl.
  easy.
Qed.

Lemma monarr_norm_equiv_tens_id_e_l {a b} (f : a ⟶ b) : 
  monarr_norm_equiv (arrid e ⧆ f) f.
Proof.
  unfold monarr_norm_equiv.
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab; [|easy]
  end.
  rewrite (monarr_struct _ (arrinvlunitor _)).
  rewrite (monarr_struct _ (arrlunitor _)).
  rewrite <- monarr_assoc, monarrcomp_struct_l.
  rewrite monarr_lunitor_nat.
  easy.
Qed.

Lemma realize_monarrlist_equiv {fs gs} 
  (H : all_monarrlist_equiv fs gs) : 
  monarr_norm_equiv 
    (realize_monarrlist fs)
    (realize_monarrlist gs).
Proof.
  revert gs H;
  induction fs; intros gs H.
  - induction gs.
    + apply monarr_norm_equiv_refl.
    + change [] with (@nil monarrlistelt ++ nil).
      rewrite realize_monarrlist_app.
      change (a :: gs) with ((a::nil) ++ gs).
      rewrite realize_monarrlist_app.
      eapply monarr_norm_equiv_trans;
      [apply monarr_norm_equiv_struct_r |].
      eapply monarr_norm_equiv_trans;
      [apply monarr_norm_equiv_struct_l |].
      apply monarr_norm_equiv_symm.
      eapply monarr_norm_equiv_trans;
      [apply monarr_norm_equiv_struct_r |].
      eapply monarr_norm_equiv_trans;
      [apply monarr_norm_equiv_struct_l |].
      apply monarr_norm_equiv_symm.
      apply monarr_norm_equiv_tens;
      [apply IHgs, H|].
      destruct H.
      simpl.
      eapply monarr_norm_equiv_trans;
      [apply H|].
      apply monarr_norm_equiv_symm.
      apply monarr_norm_equiv_tens_id_e_l.
  - destruct gs.
    + change [] with (@nil monarrlistelt ++ nil).
      change (a :: fs) with ((a::nil) ++ fs).
      rewrite 2!realize_monarrlist_app.
      eapply monarr_norm_equiv_trans;
      [apply monarr_norm_equiv_struct_r |].
      eapply monarr_norm_equiv_trans;
      [apply monarr_norm_equiv_struct_l |].
      apply monarr_norm_equiv_symm.
      eapply monarr_norm_equiv_trans;
      [apply monarr_norm_equiv_struct_r |].
      eapply monarr_norm_equiv_trans;
      [apply monarr_norm_equiv_struct_l |].
      apply monarr_norm_equiv_symm.
      apply monarr_norm_equiv_tens;
      [apply IHfs, (all_monarrlist_cons_equiv_nil H)|].
      unfold all_monarrlist_equiv in H.
      simpl in H.
      simpl.
      eapply monarr_norm_equiv_trans;
      [| apply H].
      apply monarr_norm_equiv_tens_id_e_l.
    + apply monarr_norm_equiv_tens;
      [apply IHfs, H|].
      apply H.
Qed.

Lemma monarrlistelt_equiv_refl : 
  Reflexive monarrlistelt_equiv.
Proof.
  intros a;
  apply monarr_norm_equiv_refl.
Qed.

Lemma monarrlistelt_equiv_symm : 
  Symmetric monarrlistelt_equiv.
Proof.
  intros a b;
  apply monarr_norm_equiv_symm.
Qed.

Lemma monarrlistelt_equiv_trans : 
  Transitive monarrlistelt_equiv.
Proof.
  intros a b c;
  apply monarr_norm_equiv_trans.
Qed.


Lemma monarrlist_equiv_refl :
  Reflexive all_monarrlist_equiv.
Proof.
  intros f.
  induction f; [easy|].
  split; [apply monarrlistelt_equiv_refl|].
  apply IHf.
Qed.

Lemma monarrlist_equiv_symm :
  Symmetric all_monarrlist_equiv.
Proof.
  intros fss.
  induction fss; intros gss H; [|destruct gss].
  - induction gss; [easy|].
    split.
    + apply monarr_norm_equiv_symm, H. 
    + specialize (IHgss (proj2 H)).
      destruct gss;
      apply IHgss.
  - split.
    + apply monarr_norm_equiv_symm, H. 
    + apply (IHfss nil).
      destruct fss; apply H.
  - split.
    + apply monarr_norm_equiv_symm.
      apply H.
    + apply IHfss, H.
Qed.

Lemma monarrlist_equiv_trans :
  Transitive all_monarrlist_equiv.
Proof.
  intros fs gs hs.
  remember (length fs + length gs + length hs) as k eqn:Heqk.
  assert (Hle : length fs + length gs + length hs <= k) by lia.
  clear Heqk.
  revert fs gs hs Hle.
  induction k;
  [intros [] [] []; easy|].
  intros [|f fs] [|g gs] [|h hs]; try reflexivity + (intros; assumption).
  - simpl.
    intros Hle Hnil Hgh.
    split.
    + eapply monarrlistelt_equiv_trans; [apply Hnil|].
      apply Hgh.
    + apply (IHk [] gs hs); [simpl; lia|apply Hnil|apply Hgh].
  - intros Hle Hnil Hgh.
    split.
    + eapply monarrlistelt_equiv_trans; [apply Hnil|].
      apply Hgh.
    + apply (IHk fs [] hs); [simpl in *; lia| |apply Hgh].
      apply (all_monarrlist_cons_equiv_nil Hnil).
  - intros Hle Hnil Hgh.
    split.
    + eapply monarrlistelt_equiv_trans; [apply Hnil|].
      apply Hgh.
    + pose proof (IHk fs gs [] ltac:(simpl in *;lia) (proj2 Hnil) 
        (all_monarrlist_cons_equiv_nil Hgh)) as e.
      destruct fs; apply e.
  - simpl.
    intros Hle Hfg Hgh.
    split.
    + eapply monarrlistelt_equiv_trans; [apply Hfg|apply Hgh].
    + apply (IHk fs gs hs); [lia|..].
      * apply Hfg.
      * apply Hgh.
Qed.


Lemma monarrlist_list_equiv_refl : 
  Reflexive all_monarrlist_list_equiv.
Proof.
  intros fss.
  induction fss; [easy|].
  split; [| apply IHfss].
  apply monarrlist_equiv_refl.
Qed.


Lemma monarrlist_list_equiv_symm : 
  Symmetric all_monarrlist_list_equiv.
Proof.
  intros fss.
  induction fss; intros gss H; [|destruct gss].
  - induction gss; [easy|].
    split.
    + apply monarrlist_equiv_symm, H. 
    + specialize (IHgss (proj2 H)).
      destruct gss;
      apply IHgss.
  - split.
    + apply monarrlist_equiv_symm, H. 
    + apply (IHfss nil).
      destruct fss; apply H.
  - split.
    + apply monarrlist_equiv_symm.
      apply H.
    + apply IHfss, H.
Qed.

Lemma monarrlist_list_equiv_trans:
  Transitive all_monarrlist_list_equiv.
Proof.
  intros fss gss hss.
  remember (length fss + length gss + length hss) as k eqn:Heqk.
  assert (Hle : length fss + length gss + length hss <= k) by lia.
  clear Heqk.
  revert fss gss hss Hle.
  induction k;
  [intros [] [] []; easy|].
  intros [|fs fss] [|gs gss] [|hs hss]; try reflexivity + (intros; assumption).
  - simpl.
    intros Hle Hnil Hgh.
    split.
    + eapply monarrlist_equiv_trans; [apply Hnil|].
      apply Hgh.
    + apply (IHk [] gss hss); [simpl; lia|apply Hnil|apply Hgh].
  - intros Hle Hnil Hgh.
    split.
    + eapply monarrlist_equiv_trans; [apply Hnil|].
      apply Hgh.
    + apply (IHk fss [] hss); [simpl in *; lia| |apply Hgh].
      apply (all_monarrlist_list_cons_equiv_nil Hnil).
  - intros Hle Hnil Hgh.
    split.
    + eapply monarrlist_equiv_trans; [apply Hnil|].
      apply Hgh.
    + pose proof (IHk fss gss [] ltac:(simpl in *;lia) (proj2 Hnil) 
        (all_monarrlist_list_cons_equiv_nil Hgh)) as e.
      unfold all_monarrlist_list_equiv in e.
      rewrite zip_defaults_nil_r in e.
      apply e.
  - simpl.
    intros Hle Hfg Hgh.
    split.
    + eapply monarrlist_equiv_trans; [apply Hfg|apply Hgh].
    + apply (IHk fss gss hss); [lia|..].
      * apply Hfg.
      * apply Hgh.
Qed.

Add Parametric Relation : monarrlistelt monarrlistelt_equiv
  reflexivity proved by monarrlistelt_equiv_refl
  symmetry proved by monarrlistelt_equiv_symm
  transitivity proved by monarrlistelt_equiv_trans
  as monarrlistelt_equiv_equivalence.

Add Parametric Relation : monarrlist all_monarrlist_equiv
  reflexivity proved by monarrlist_equiv_refl
  symmetry proved by monarrlist_equiv_symm
  transitivity proved by monarrlist_equiv_trans
  as monarrlist_equiv_equivalence.

Add Parametric Relation : (list monarrlist) all_monarrlist_list_equiv
  reflexivity proved by monarrlist_list_equiv_refl
  symmetry proved by monarrlist_list_equiv_symm
  transitivity proved by monarrlist_list_equiv_trans
  as monarrlist_list_equiv_equivalence.


Lemma realize_monarrlist_list_equiv_nil {fss} 
  (H : all_monarrlist_list_equiv fss []) 
  (Hf : totally_composable fss) : 
  monarr_norm_equiv 
    (compose_monarrlist_list_of_totally_composable fss Hf)
    (arrid e).
Proof.
  induction fss;
  [ apply monarr_norm_equiv_refl | destruct fss;
    [apply (realize_monarrlist_equiv (proj1 H))|]].
  rewrite compose_monarrlist_list_of_totally_composable_cons.
  unfold monarr_composer_of_composable.
  rewrite <- (monarr_lunit (arrid e)).
  apply monarr_norm_equiv_comp.
  + eapply monarr_norm_equiv_trans;
    [apply monarr_norm_equiv_struct_r|].
    apply (realize_monarrlist_equiv (proj1 H)).
  + apply IHfss, H.
Qed.

Lemma monarr_norm_equiv_struct_eq_in 
  {a b a' b'} (f : bwarr a b) (g : bwarr a' b')
  (H : Nf a = Nf a') :
  monarr_norm_equiv f g.
Proof.
  pose proof (Nf_eq_of_arr f).
  pose proof (Nf_eq_of_arr g).
  unfold monarr_norm_equiv.
  destruct (eqbwnorm (Nf a') (Nf a)); [|congruence].
  destruct (eqbwnorm (Nf b) (Nf b')); [|congruence].
  rewrite 2!monarr_arrcomp.
  apply monarr_struct.
Qed.

Lemma monarr_norm_equiv_struct_eq_out
  {a b a' b'} (f : bwarr a b) (g : bwarr a' b')
  (H : Nf b = Nf b') :
  monarr_norm_equiv f g.
Proof.
  pose proof (Nf_eq_of_arr f).
  pose proof (Nf_eq_of_arr g).
  unfold monarr_norm_equiv.
  destruct (eqbwnorm (Nf a') (Nf a)); [|congruence].
  destruct (eqbwnorm (Nf b) (Nf b')); [|congruence].
  rewrite 2!monarr_arrcomp.
  apply monarr_struct.
Qed.

(* TODO: Finish these (rather annoying...) proofs: 

Lemma all_monarrlist_list_equiv_iff_ex {fss gss} : 
  all_monarrlist_list_equiv fss gss <->
  exists fshd fsnil gshd gsnil, 
    fss = fshd ++ fsnil /\ gss = gshd ++ gsnil /\
    all_monarrlist_list_equiv gsnil [] /\
    all_monarrlist_list_equiv fsnil [] /\
    length fshd = length gsnil /\
    all_monarrlist_list_equiv fshd gshd.
Proof.
  split.
  2: {
    intros (fshd & fsnil & gshd & gsnil & Hfss & Hgss & Hfnil & Hgnil & _ & Hfg).
    subst.
    apply all_monarrlist_list_equiv

  }*)

Lemma realize_monarrlist_list_equiv {fss gss} 
  (H : all_monarrlist_list_equiv fss gss) 
  (Hf : totally_composable fss)
  (Hg : totally_composable gss) : 
  monarr_norm_equiv 
    (compose_monarrlist_list_of_totally_composable fss Hf)
    (compose_monarrlist_list_of_totally_composable gss Hg).
Proof.
  remember (length fss + length gss) as k.
  assert (Hk : length fss + length gss <= k) by (subst; easy).
  clear Heqk.
  revert fss gss H Hf Hg Hk.
  induction k; intros fss gss;
  destruct fss, gss; 
  try (solve [simpl; intros; easy]);
  intros H Hf Hg Hk;
  [..|destruct fss, gss].
  - apply monarr_norm_equiv_refl.
  - apply monarr_norm_equiv_symm.
    apply realize_monarrlist_list_equiv_nil.
    apply monarrlist_list_equiv_symm, H.
  - apply monarr_norm_equiv_symm.
    apply realize_monarrlist_list_equiv_nil.
    apply monarrlist_list_equiv_symm, H.
  - apply realize_monarrlist_list_equiv_nil, H.
  - apply realize_monarrlist_equiv, H.
  - rewrite <- monarr_runit.
    rewrite compose_monarrlist_list_of_totally_composable_cons.
    apply monarr_norm_equiv_comp.
    + eapply monarr_norm_equiv_symm, monarr_norm_equiv_trans;
      [apply monarr_norm_equiv_struct_r|];
      apply monarr_norm_equiv_symm.
      apply realize_monarrlist_equiv, H.
    + eapply monarr_norm_equiv_trans;
      [|apply (IHk [] (l1::gss) (proj2 H) ltac:(easy) (proj2 Hg))];
      [|simpl in *; lia].
      apply monarr_norm_equiv_struct_eq_in.
      simpl.
      etransitivity;
      [apply ( (Nf_eq_out_of_norm_equiv 
        (realize_monarrlist_equiv (proj1 H))))|].
      specialize (IHk [] (l1::gss) (proj2 H) ltac:(easy) 
        (proj2 Hg) ltac:(simpl in Hk |- *; lia)).
      apply (Nf_eq_in_of_norm_equiv) in IHk.
      simpl in IHk.
      rewrite IHk.
      apply Hg.
  - apply monarr_norm_equiv_symm.
    rewrite <- monarr_runit.
    rewrite compose_monarrlist_list_of_totally_composable_cons.
    apply monarr_norm_equiv_comp.
    + eapply monarr_norm_equiv_symm, monarr_norm_equiv_trans;
      [apply monarr_norm_equiv_struct_r|];
      apply realize_monarrlist_equiv, H.
    + eapply monarr_norm_equiv_trans;
      [|apply (IHk [] (l1::fss) 
        (monarrlist_list_equiv_symm (l1::fss) [] (proj2 H)) 
        ltac:(easy) (proj2 Hf) )];
      [|simpl in *; lia].
      apply monarr_norm_equiv_struct_eq_in.
      simpl.
      etransitivity;
      [apply (eq_sym (Nf_eq_out_of_norm_equiv 
        (realize_monarrlist_equiv (proj1 H))))|].
      specialize (IHk (l1::fss) [] (proj2 H) (proj2 Hf)
        ltac:(easy) ltac:(simpl in Hk |- *; lia)).
      apply (Nf_eq_in_of_norm_equiv) in IHk.
      simpl in IHk.
      rewrite <- IHk.
      apply Hf.
  - rewrite 2!compose_monarrlist_list_of_totally_composable_cons.
    apply monarr_norm_equiv_comp.
    + eapply monarr_norm_equiv_trans;
      [|apply monarr_norm_equiv_symm; 
      eapply monarr_norm_equiv_trans];
    [apply monarr_norm_equiv_struct_r.. |].
    apply monarr_norm_equiv_symm.
    apply realize_monarrlist_equiv, H.
    + apply (IHk (l1 :: fss) (l2 :: gss)); [|simpl in *; lia].
      apply H.
Qed.

Lemma equiv_conj_of_monarr_norm_equiv {a b m n} (f : a ⟶ b)
  (g : m ⟶ n) (h : bwarr a m) (h' : bwarr n b) :
  monarr_norm_equiv f g ->
  f ≊ h ◌ g ◌ h'.
Proof.
  unfold monarr_norm_equiv.
  destruct (eqbwnorm (Nf m) (Nf a)) as [Hma |]; [|easy].
  destruct (eqbwnorm (Nf b) (Nf n)) as [Hbn |]; [|easy].
  intros H.
  rewrite <- H.
  rewrite <- !monarr_assoc, monarr_arrcomp, monarr_struct_id, monarr_runit.
  rewrite monarr_assoc, monarr_arrcomp, monarr_struct_id, monarr_lunit.
  easy.
Qed.

Lemma equiv_of_foliate_equiv {a b} (f g : a ⟶ b) : 
  monarr_norm_equiv 
    (compose_monarrlist_list_of_totally_composable 
      (foliate_monarr f) 
      (foliate_monarr_totally_composable f))
    (compose_monarrlist_list_of_totally_composable 
      (foliate_monarr g) 
      (foliate_monarr_totally_composable g)) ->
  f ≊ g.
Proof.
  intros Heq.
  rewrite foliate_correct, (foliate_correct g).
  rewrite monarrcomp_struct_r, monarrcomp_struct_l.
  rewrite <- monarr_assoc, monarr_arrcomp.
  rewrite !monarr_assoc, monarr_arrcomp.
  apply equiv_conj_of_monarr_norm_equiv.
  apply Heq.
Qed.
  

Lemma equiv_of_foliate_all_equiv {a b} (f g : a ⟶ b) : 
  all_monarrlist_list_equiv (foliate_monarr f) (foliate_monarr g) ->
  f ≊ g.
Proof.
  intros Heq.
  apply equiv_of_foliate_equiv.
  apply realize_monarrlist_list_equiv, Heq.
Qed.

Ltac cleanup_monarrlist_list_equiv :=
  repeat (split; unfold uncurry; try reflexivity + assumption); unfold monarrlistelt_equiv; cbn;
  try apply monarr_norm_equiv_refl;
  try (apply monarr_norm_equiv_struct_eq_in; try reflexivity);
  try (apply monarr_norm_equiv_struct_eq_out; try reflexivity);
  try (apply monarr_norm_equiv_of_monarrequiv; try assumption + easy).

Definition all_ml_equiv' := all_monarrlist_list_equiv.

Arguments all_ml_equiv' : simpl never.

Definition comp_compble := compose_monarrlist_list_of_totally_composable.

Arguments comp_compble : simpl never.

Ltac freeze_equiv :=
  change all_monarrlist_list_equiv with all_ml_equiv';
  change compose_monarrlist_list_of_totally_composable with comp_compble.

Ltac unfreeze_equiv :=
  change all_ml_equiv' with all_monarrlist_list_equiv;
  change comp_compble with compose_monarrlist_list_of_totally_composable.

Lemma monarr_norm_equiv_of_monarrlistelt_equiv {a b c d} 
  (f : a ⟶ b) (g : c ⟶ d) : 
  monarrlistelt_equiv (monarrlist_arr a b f) (monarrlist_arr c d g) ->
  monarr_norm_equiv f g.
Proof.
  intros H; apply H.
Qed.

Lemma foliate_test {a b c m n o} (f : bwarr a b) (g : bwarr b c)
  (h : bwarr m n) (j : bwarr n o) : 
  (f ◌ g) ⧆ h ≊ f ⧆ h ◌ g ⧆ arrid n.
Proof.
  apply equiv_of_foliate_equiv.
  freeze_equiv.
  apply realize_monarrlist_list_equiv.
  cleanup_monarrlist_list_equiv.
Qed.

Lemma unary_proper_op_composable {f} (H : unary_monarrlist_op_proper f)
  {fs gs} : 
  composable fs gs -> composable (f fs) (f gs).
Proof.
  unfold composable.
  intros Hc.
  pose proof (H fs) as Hf.
  pose proof (H gs) as Hg.
  rewrite (Nf_eq_out_of_norm_equiv Hf).
  rewrite (Nf_eq_in_of_norm_equiv Hg).
  apply Hc.
Qed.

Lemma unary_proper_op_totally_composable {f} (H : unary_monarrlist_op_proper f)  
  {fss : list monarrlist} (Hf : totally_composable fss) :
  totally_composable (map f fss).
Proof.
  induction fss; [easy|].
  destruct fss; [easy|].
  specialize (IHfss (proj2 Hf)).
  split.
  - apply (unary_proper_op_composable H), Hf.
  - apply IHfss.
Qed.

Lemma monarr_norm_equiv_comp_composable {a b c d a' b' c' d'}
  (f : a ⟶ b) (g : c ⟶ d) (f' : a' ⟶ b') (g' : c' ⟶ d') Hc Hc' :
  monarr_norm_equiv f f' ->
  monarr_norm_equiv g g' ->
  monarr_norm_equiv
    (monarr_composer_of_composable f g Hc)
    (monarr_composer_of_composable f' g' Hc').
Proof.
  intros Hf Hg.
  unfold monarr_composer_of_composable.
  apply monarr_norm_equiv_comp; 
  [apply monarr_norm_equiv_comp|];
  try assumption.
  apply monarr_norm_equiv_struct_eq_in.
  apply (Nf_eq_out_of_norm_equiv Hf).
Qed.



Lemma unary_proper_op_preserves {f} (H : unary_monarrlist_op_proper f) 
  {fss : list monarrlist} (Hf : totally_composable fss) : 
  monarr_norm_equiv 
    (comp_compble fss Hf)
    (comp_compble (map f fss) (unary_proper_op_totally_composable H Hf)).
Proof.
  induction fss; [apply monarr_norm_equiv_refl|]; destruct fss.
  - apply monarr_norm_equiv_symm.
    apply (H a).
  - unfold comp_compble.
    simpl map.
    rewrite 2!compose_monarrlist_list_of_totally_composable_cons.
    apply monarr_norm_equiv_comp_composable;
    [apply monarr_norm_equiv_symm, (H a)|].
    erewrite (compose_monarrlist_list_of_totally_composable_indep (f l :: _)).
    apply IHfss.
Qed.

Lemma realize_monarrlist_list_Some {fss v} 
  (H : realize_monarrlist_list fss = Some v) : 
  totally_composable fss.
Proof.
  induction fss; [|destruct fss];
  [easy..|].
  simpl in H.
  unfold option_partial_map in H.
  destruct (realize_monarrlist_list_helper l fss) eqn:Elfss;
  [|easy].
  unfold maybe_compose_monarrs in H.
  destruct (eqbwnorm (Nf (monarrlist_target a)) (Nf (monarrlist_source l)));
  [|easy].
  split; [easy|].
  apply (IHfss _ Elfss).
Qed.


Lemma totally_composable_of_monarrlist_list_op_proper {f} 
  (Hf : monarrlist_list_op_proper f) {fss} :
  totally_composable fss -> totally_composable (f fss).
Proof.
  intros Hfss.
  specialize (Hf fss Hfss).
  destruct (realize_monarrlist_list (f fss)) eqn:e in Hf;
  [|destruct (realize_monarrlist_list fss); easy].
  apply (realize_monarrlist_list_Some e).
Qed.



Lemma monarrlist_list_op_proper_iff {f} : 
  monarrlist_list_op_proper f <->
  {Hc : forall fss, totally_composable fss ->
    totally_composable (f fss) &
   forall fss (Hf: totally_composable fss),
    monarr_norm_equiv
      (compose_monarrlist_list_of_totally_composable fss Hf)
      (compose_monarrlist_list_of_totally_composable (f fss) (Hc fss Hf))}.
Proof.
  split.
  - intros Hprop.
    exists (fun fss Hfss =>
      (totally_composable_of_monarrlist_list_op_proper Hprop Hfss)).
    intros fss Hf.
    pose proof (Hprop fss Hf) as H.
    rewrite (realize_monarrlist_list_totally_composable _ Hf) in H.
    rewrite (realize_monarrlist_list_totally_composable _ 
      (totally_composable_of_monarrlist_list_op_proper Hprop Hf)) in H.
    apply H.
  - intros [Hc Hprop].
    intros fss Hf.
    rewrite (realize_monarrlist_list_totally_composable _ Hf).
    rewrite (realize_monarrlist_list_totally_composable _ (Hc _ Hf)).
    apply Hprop.
Qed.

Lemma monarrlist_list_op_proper_preserves {f} (H : monarrlist_list_op_proper f) 
  {fss} (Hfss : totally_composable fss) : 
  monarr_norm_equiv 
    (compose_monarrlist_list_of_totally_composable fss Hfss)
    (compose_monarrlist_list_of_totally_composable (f fss) 
      (totally_composable_of_monarrlist_list_op_proper H Hfss)).
Proof.
  destruct (proj1 monarrlist_list_op_proper_iff H) as [Hc Hprop]. 
  erewrite (compose_monarrlist_list_of_totally_composable_indep (f fss)).
  apply Hprop.
Qed.

Lemma monarrlist_list_op_proper_compose {f g} :
  monarrlist_list_op_proper f ->
  monarrlist_list_op_proper g ->
  monarrlist_list_op_proper (fun fss => g (f fss)).
Proof.
  rewrite 3!monarrlist_list_op_proper_iff.
  intros [Hfc Hfprop] [Hgc Hgprop].
  exists (fun fss Hfss =>
    Hgc (f fss) (Hfc fss Hfss)).
  intros fss Hfss.
  apply (monarr_norm_equiv_trans (Hfprop fss Hfss)).
  apply Hgprop.
Qed.

Lemma monarrlist_list_op_proper_compose' {f g} :
  monarrlist_list_op_proper f ->
  monarrlist_list_op_proper g ->
  monarrlist_list_op_proper (Basics.compose g f).
Proof.
  unfold Basics.compose.
  apply monarrlist_list_op_proper_compose.
Qed.


Lemma monarrlist_list_op_proper_id :
  monarrlist_list_op_proper id.
Proof.
  rewrite monarrlist_list_op_proper_iff.
  exists (fun _ x => x).
  intros; apply monarr_norm_equiv_refl.
Qed.


Lemma monarrlist_list_op_proper_iter {f} :
  monarrlist_list_op_proper f ->
  forall {n : nat},
  monarrlist_list_op_proper (Nat.iter n f).
Proof.
  intros H.
  induction n.
  - apply monarrlist_list_op_proper_id.
  - unfold Nat.iter.
    simpl.
    apply monarrlist_list_op_proper_compose;
    [apply IHn | apply H].
Qed.

Lemma unary_proper_op_monarrlist_list_op_proper {f} 
  (H : unary_monarrlist_op_proper f) :
  monarrlist_list_op_proper (map f).
Proof.
  rewrite monarrlist_list_op_proper_iff.
  exists (@unary_proper_op_totally_composable f H).
  intros fss Hfss.
  induction fss;
  [apply monarr_norm_equiv_refl|].
  destruct fss;
  [apply monarr_norm_equiv_symm, H|].
  simpl map.
  rewrite 2!compose_monarrlist_list_of_totally_composable_cons.
  apply monarr_norm_equiv_comp_composable;
  [apply monarr_norm_equiv_symm, H|].
  erewrite (compose_monarrlist_list_of_totally_composable_indep (f l :: _)).
  apply IHfss.
Qed.


Fixpoint struct_to_id (fss : monarrlist) := 
  match fss with
  | nil => nil
  | fs :: fss' => match fs with
      | monarrlist_id a => monarrlist_id a
      | monarrlist_arr a b (monarrstruct f) => monarrlist_id a
      | monarrlist_arr a b f => monarrlist_arr a b f
      end :: struct_to_id fss'
  end.

Lemma struct_to_id_proper_unary : 
  unary_monarrlist_op_proper struct_to_id.
Proof.
  intros fss.
  induction fss as [|[] fss];
  [apply monarr_norm_equiv_refl|..];
  simpl;
  apply monarr_norm_equiv_tens;
  try assumption + apply monarr_norm_equiv_refl.
  destruct f; try apply monarr_norm_equiv_refl.
  apply monarr_norm_equiv_struct_eq_in.
  easy.
Qed.

Fixpoint split_ids (fss : monarrlist) := 
  match fss with
  | nil => nil
  | fs :: fss' => match fs with
      | monarrlist_id a => map monarrlist_id (map var (bw_to_varlist a))
      | monarrlist_arr a b f => monarrlist_arr a b f :: nil
      end ++ split_ids fss'
  end.

Lemma realize_monarrlist_app' fs fss :
  monarr_norm_equiv 
    (realize_monarrlist (fs ++ fss))
    (realize_monarrlist fss ⧆ realize_monarrlist fs).
Proof.
  rewrite realize_monarrlist_app.
  apply (monarr_norm_equiv_trans (monarr_norm_equiv_struct_r _ _)).
  apply (monarr_norm_equiv_trans (monarr_norm_equiv_struct_l _ _)).
  apply monarr_norm_equiv_refl.
Qed.

Lemma split_id_norm_equiv (a : bw) : 
  monarr_norm_equiv
    (realize_monarrlist (map monarrlist_id (map var (bw_to_varlist a))))
    (arrid a).
Proof.
  induction a;
  [apply monarr_norm_equiv_refl | apply monarr_norm_equiv_tens_id_e_l | ].
  simpl.
  rewrite 2!map_app.
  apply (monarr_norm_equiv_trans (realize_monarrlist_app' _ _)).
  rewrite (monarr_struct _ (arrid a1 ⊠ arrid a2)).
  rewrite <- monarr_arrtens.
  apply monarr_norm_equiv_tens;
  assumption.
Qed.

Lemma split_ids_proper_unary : 
  unary_monarrlist_op_proper split_ids.
Proof.
  intros fss.
  induction fss as [|[] fss];
  [apply monarr_norm_equiv_refl|..];
  simpl;
  [|apply monarr_norm_equiv_tens;
    assumption + apply monarr_norm_equiv_refl].
  apply (monarr_norm_equiv_trans (realize_monarrlist_app' _ _)).
  apply monarr_norm_equiv_tens; [apply IHfss|].
  apply split_id_norm_equiv.
Qed.

Fixpoint combine_ids_helper (a : bw) (fss : monarrlist) :=
  match fss with
  | nil => monarrlist_id a :: nil
  | monarrlist_id b :: fss' => combine_ids_helper (tens b a) fss'
  | fs :: fss' => monarrlist_id a :: fs :: combine_ids fss'
  end
with combine_ids (fss : monarrlist) :=
  match fss with
  | nil => nil
  | monarrlist_id a :: fss' => combine_ids_helper a fss'
  | fs :: fss' => fs :: combine_ids fss'
  end.

Lemma monarr_norm_equiv_tens_assoc {a b c d m n}
  (f : a ⟶ b) (g : c ⟶ d) (h : m ⟶ n) :
  monarr_norm_equiv (f ⧆ g ⧆ h) (f ⧆ (g ⧆ h)).
Proof.
  apply (monarr_norm_equiv_trans (monarr_norm_equiv_symm _ _ 
    (monarr_norm_equiv_struct_l (arrassoc _ _ _) _))).
  rewrite monarr_assoc_nat.
  apply monarr_norm_equiv_struct_r.
Qed.

Lemma combine_ids_and_helper_unary_proper :
  forall fss,
    (monarr_norm_equiv (realize_monarrlist fss)
      (realize_monarrlist (combine_ids fss))
    /\
    forall a,
    monarr_norm_equiv (realize_monarrlist fss ⧆ arrid a)
      (realize_monarrlist (combine_ids_helper a fss))).
Proof.
  intros fss.
  induction fss as [|[] fss].
  - split; intros; apply monarr_norm_equiv_refl.
  - split.
    + apply IHfss.
    + intros b.
    simpl.
    refine (monarr_norm_equiv_trans _ (proj2 IHfss _)).
    rewrite (monarr_struct _ (arrid a ⊠ arrid b)).
    rewrite <- monarr_arrtens.
    apply monarr_norm_equiv_tens_assoc.
  - simpl. 
    split.
    + apply monarr_norm_equiv_tens; [|apply monarr_norm_equiv_refl].
      apply IHfss.
    + intros c.
      do 2 (apply monarr_norm_equiv_tens; [|apply monarr_norm_equiv_refl]).
      apply IHfss.
Qed.

Lemma combine_ids_unary_proper :
  unary_monarrlist_op_proper combine_ids.
Proof.
  intros fss.
  apply monarr_norm_equiv_symm.
  apply combine_ids_and_helper_unary_proper.
Qed.

Definition is_idarr_singleton (fs : monarrlist) :=
  match fs with 
  | monarrlist_id _ :: nil => true
  | _ => false
  end.

Definition bin_to_kary_monarrlist_op_proper 
  (f : monarrlist -> monarrlist -> monarrlist * list monarrlist) :=
  {
    Hc : forall fs gs, composable fs gs -> 
      totally_composable (fst (f fs gs) :: snd (f fs gs)) &
    forall fs gs (Hfg : composable fs gs), 
      monarr_norm_equiv
        (monarr_composer_of_composable 
          (realize_monarrlist fs) 
          (realize_monarrlist gs) Hfg)
        (compose_monarrlist_list_of_totally_composable
          (fst (f fs gs) :: snd (f fs gs)) (Hc fs gs Hfg))
}.

(* Fixpoint pairwise_kary_apply_helper (f : monarrlist -> monarrlist -> 
  monarrlist * list monarrlist) (fs : monarrlist) (fss : list monarrlist) :=
  match fss with
  | nil => fs :: nil
  | fst' :: fss' =>
      match snd (f fs fst') with
      | nil => pairwise_kary_apply_helper (fst (f fs fst')) fss'
      | fst'' :: fst''s => fst (f fs fst') last *)

(* Lemma pairwise_apply_proper_binary_op_proper *)


Definition filter_idarrs (fss : list monarrlist) :=
  match fss with
  | nil => nil
  | fs :: fss' => 
    fs :: filter (fun x => negb (is_idarrlist x)) fss'
    (* if is_idarrlist fs then
    (if length (filter_idarrs fss') > 0 then filter_idarrs fss' else fs :: nil)
    else fs :: (filter_idarrs fss') *)
  end.

Lemma input_output_is_idarrlist {fs} (H : is_idarrlist fs = true) :
  monarrlist_source fs = monarrlist_target fs.
Proof.
  induction fs as [|[] fs]; [easy|..]; simpl in *; [|easy].
  unfold monarrlist_source, monarrlist_target.
  simpl.
  f_equal.
  apply IHfs, H.
Qed.

Lemma totally_composable_helper_swap {a b fss} :
  Nf (monarrlist_target a) = Nf (monarrlist_target b) ->
  totally_composable_helper a fss ->
  totally_composable_helper b fss.
Proof.
  intros Heq.
  destruct fss; [easy|].
  intros [Hl Hr].
  split; [|apply Hr].
  unfold composable in *.
  rewrite <- Heq.
  easy.
Qed.

Lemma totally_composable_filter_idarrs {fss} :
  totally_composable (fss) -> 
  totally_composable (filter_idarrs fss).
Proof.
  destruct fss as [|fs fss]; [easy|].
  revert fs.
  (* intros H. *)
  induction fss as [|fs' fss]; [easy|];
  intros fs H.
  simpl.
  destruct (is_idarrlist fs') eqn:e; simpl.
  - apply IHfss.
    refine (totally_composable_helper_swap _ (proj2 H)).
    rewrite <- (input_output_is_idarrlist e).
    symmetry.
    apply H.
  - split; [apply H|].
    apply IHfss, H.
Qed.

Lemma filter_idarrs_proper :
  monarrlist_list_op_proper filter_idarrs.
Proof.
  rewrite monarrlist_list_op_proper_iff.
  exists @totally_composable_filter_idarrs.
  destruct fss as [|fs fss]; [intros; apply monarr_norm_equiv_refl|].
  simpl filter_idarrs.

  (* induction fss as [|fs' fss]; [intros; apply monarr_norm_equiv_refl|].
  simpl filter_idarrs.

  revert fs.
  induction fss as [|fs' fss]; [intros; apply monarr_norm_equiv_refl|].
  intros fs Hf.
  simpl filter_idarrs.
  generalize (totally_composable_filter_idarrs Hf).
  induction (is_idarrlist fs').

  destruct fss as [|fs fss]; [intros; apply monarr_norm_equiv_refl|].


  
  unshelve (eexists).
  intros fss Hfss. *)
  Abort.

Definition full_process_monarrlist_list :=
  (Basics.compose (Basics.compose (Basics.compose
  (fun fss => 
  Nat.iter (length fss) 
  (Basics.compose (map split_ids) (pairwise_apply (pairify_apply shift_left))) fss)
  (map split_ids))
  (map remove_structs))
  (map structify_monarrlist)).

Lemma full_process_monarrlist_list_proper :
  monarrlist_list_op_proper full_process_monarrlist_list.
Proof.
  unfold full_process_monarrlist_list.
  apply monarrlist_list_op_proper_compose'; 
  [|apply monarrlist_list_op_proper_compose';
  [|apply monarrlist_list_op_proper_compose']].
  - apply unary_proper_op_monarrlist_list_op_proper.
    apply structify_proper.
  - apply unary_proper_op_monarrlist_list_op_proper.
    apply remove_structs_proper.
  - apply unary_proper_op_monarrlist_list_op_proper.
    apply split_ids_proper_unary.
  - intros fss. 
    apply (monarrlist_list_op_proper_iter).
    apply monarrlist_list_op_proper_compose';
    [|apply unary_proper_op_monarrlist_list_op_proper;
      apply split_ids_proper_unary].
    apply pairwise_apply_proper_binary_op_proper.
    apply pairify_apply_proper.
    apply shift_left_proper.
Qed.


End VarListNf.
End monbwcat_Category. 
End MonoidalExpressionNormalForm.
End MonoidalCoherence.
End FreeMonoid.

Section NatDiagram.

Import CategoryTypeclass.


Context (X : Type) {cC : Category X} {cCh : CategoryCoherence cC}
  {mC : MonoidalCategory cC} {mCh : MonoidalCategoryCoherence mC}.

Local Open Scope Cat_scope.



Local Notation bwnat := (bw nat).

Fixpoint realize_nat_bw (f : nat -> X) (a : bwnat) : X :=
  match a with
  | e _ => mC.(mon_I)
  | var _ n => f n
  | tens _ b c => realize_nat_bw f b × realize_nat_bw f c
  end.

Fixpoint map_bw {A B} (f : A -> B) (a : bw A) : bw B :=
  match a with
  | e _ => e B
  | var _ a' => var _ (f a')
  | tens _ a' b' => tens _ (map_bw f a') (map_bw f b')
  end.

Fixpoint map_bwarr {A B} (f : A -> B) {a b} (g : bwarr A a b) : bwarr B (map_bw f a) (map_bw f b) := 
  match g with
  | arrid _ a => arrid _ (map_bw f a)
  | arrassoc _ a b c => arrassoc _ (map_bw f a) (map_bw f b) (map_bw f c)
  | arrinvassoc _ a b c => arrinvassoc _ (map_bw f a) (map_bw f b) (map_bw f c)
  | arrlunitor _ a => arrlunitor _ (map_bw f a)
  | arrinvlunitor _ a => arrinvlunitor _ (map_bw f a)
  | arrrunitor _ a => arrrunitor _ (map_bw f a)
  | arrinvrunitor _ a => arrinvrunitor _ (map_bw f a)
  | arrcomp _ f' g' => arrcomp _ (map_bwarr f f') (map_bwarr f g')
  | arrtens _ f' g' => arrtens _ (map_bwarr f f') (map_bwarr f g')
  end.

Add Parametric Morphism {A B} (f : A -> B) {a b} : (@map_bwarr A B f a b) with signature
  bwarrequiv A a b ==> bwarrequiv B (map_bw f a) (map_bw f b)
  as map_bwarr_mor.
Proof.
  intros g h H.
  induction H; simpl; try constructor;
  eauto 2 using bwarrequiv.
Qed.

Record NatDiagramRealizer := {
  realize_obj : nat -> X;
  realize_mor (n m : bw nat) : nat -> 
    (realize_bw X (map_bw realize_obj n) ~> realize_bw X (map_bw realize_obj m));
}.

Record NatDiagramListRealizer := {
  realize_obj' : nat -> X;
  realize_mor_list (n m : bw nat) :
    list (realize_bw X (map_bw realize_obj' n) ~> realize_bw X (map_bw realize_obj' m));
}.

Definition NatDiagramRealizer_of_NatDiagramListRealizer_default 
  (N : NatDiagramListRealizer)
  (f : forall a b : X, a ~> b) : NatDiagramRealizer := {|
    realize_obj := N.(realize_obj');
    realize_mor n m := 
      List.nth_default (f _ _) (N.(realize_mor_list) n m);
  |}.

Context (N : NatDiagramRealizer).

#[local] Instance FreeNatCategory@{u u1} : Category (nat : Type@{u}) := {
  morphism _ _ := nat : Type@{u1};
  c_equiv _ _ := eq;
  compose _ _ _ := Nat.add;
  c_identity _ := 0;
}.

#[local] Program Instance FreeNatCategoryCoherence : 
  CategoryCoherence FreeNatCategory.
Next Obligation.
  split; intros ? **; congruence.
Qed.
Next Obligation.
  lia.
Qed.

#[local] Program Instance FreeNatMonoidalCategory@{u u1} : 
  MonoidalCategory FreeNatCategory@{u u1} := {
  obj_tensor := Nat.add;
  mor_tensor _ _ _ _ := Nat.add;
  mon_I := 0;
  associator _ _ _ := {|forward := 0; reverse := 0|};
  left_unitor _ := {|forward := 0; reverse := 0|};
  right_unitor _ := {|forward := 0; reverse := 0|};
}.

#[local] Program Instance FreeNatMonoidalCategoryCoherence : 
  MonoidalCategoryCoherence FreeNatMonoidalCategory := {}.
Next Obligation.
  lia.
Qed.
Next Obligation.
  lia.
Qed.
Next Obligation.
  lia.
Qed.


Fixpoint realize_nat_diagram {a b} (f : @monarr nat
  FreeNatCategory FreeNatMonoidalCategory a b) :
  monarr X (map_bw N.(realize_obj) a) (map_bw N.(realize_obj) b) := 
  match f with
  | monarrcomp _ f' g' => monarrcomp _ 
      (realize_nat_diagram f') (realize_nat_diagram g')
  | monarrtens _ f' g' => monarrtens _ 
      (realize_nat_diagram f') (realize_nat_diagram g')
  | mongeneric _ f' => 
      mongeneric _ (N.(realize_mor) _ _ f')
  | monarrstruct _ f' =>
      monarrstruct _ (map_bwarr N.(realize_obj) f')
  end.

Add Parametric Morphism {a b} : (@realize_nat_diagram a b) with signature
  @monarrequiv nat FreeNatCategory FreeNatMonoidalCategory a b ==> 
  monarrequiv X _ _
  as realize_nat_diagram_mor.
Proof.
  intros f g H.
  induction H;
  simpl;
  eauto 2 using monarrequiv.
Qed.

End NatDiagram.

Section Quotation.

Context {X : Type} {cC : Category.Category X} 
  {mC : Monoidal.MonoidalCategory cC}.

(* Fixpoint all_bwarr_in_vars {a b} (f : bwarr X a b) : list X := 
  match f with
  | arrcomp _ _ _ f' g' => all_bwarr_in_vars f' ++ all_bwarr_in_vars g'
  | arrtens _ _ _ _ f' g' => all_bwarr_in_vars f' ++ all_bwarr_in_vars g'
  | _ => bw_to_varlist X a
  end.

Fixpoint all_bwarr_out_vars {a b} (f : bwarr X a b) : list X := 
  match f with
  | arrcomp _ _ _ f' g' => all_bwarr_out_vars g'
  | arrtens _ _ _ _ f' g' => all_bwarr_out_vars f' ++ all_bwarr_out_vars g'
  | _ => bw_to_varlist X b
  end. *)

(* Definition all_bwarr_vars {a b} (f : bwarr X a b) : list X *)

Fixpoint all_in_vars {a b} (f : monarr X a b) : list X :=
  match f with
  | mongeneric _ _ => bw_to_varlist X a
  | monarrstruct _ _ => bw_to_varlist X a 
      (* We can prove that bw_to_varlist b = bw_to_varlist a, 
        so no point having both*)
  | monarrcomp _ f' g' => all_in_vars f' ++ all_in_vars g'
  | monarrtens _ f' g' => all_in_vars f' ++ all_in_vars g'
  end.

Fixpoint all_out_vars {a b} (f : monarr X a b) : list X :=
  match f with
  | mongeneric _ _ => bw_to_varlist X b
  | monarrstruct _ _ => nil
  | monarrcomp _ f' g' => all_out_vars g'
  | monarrtens _ f' g' => all_out_vars f' ++ all_out_vars g'
  end.

Definition all_vars {a b} (f : monarr X a b) : list X :=
  all_in_vars f ++ all_out_vars f.


Require Import List.
Import ListNotations.

Ltac list_in tm lst :=
  match lst with
  | ?l::?lst' => 
    let _ := lazymatch goal with
    | _ => unify l tm 
    end in constr:(true)
  | ?l::?lst' => let res := list_in tm lst' in constr:(res)
  | nil => constr:(false)
  | _ => fail "list_in argument error: list_in" tm lst
  end.

Ltac list_dedup lst := 
  lazymatch lst with
  | @nil ?T => constr:(@nil T)
  | ?l :: ?lst' => 
    let res := list_dedup lst' in  
    lazymatch list_in l res with
    | true => constr:(res)
    | false =>  constr:(l :: res)
    end
  | _ => fail "list_dedup argument error: list_dedup" lst
  end.

Ltac list_union lst1 lst2 := 
  lazymatch lst2 with
  | nil => constr:(lst1)
  | ?l :: ?lst2' => 
    let res := list_union lst1 lst2' in
    lazymatch list_in l lst1 with
    | true => constr:(res) 
    | false => constr:(l :: res)
    end
  | _ => fail "list_union argument error: list_union" lst1 lst2
  end.

Ltac bunify a b :=
  match goal with
  | _ => let _ := match goal with 
      | _ => unify a b
      end in constr:(true)
  | _ => constr:(false)
  end.

Ltac list_index tm lst := 
  (* let _ := match goal with |_ => idtac "finding" tm "in" lst end in *)
  lazymatch lst with
  | nil => fail "Term '" tm "' not found in list (tail:" lst ")"
  | ?l :: ?lst' => lazymatch bunify tm l with
    | true => constr:(0)
    | false => let idx' := list_index tm lst' in
        constr:(S idx')
    end
  | _ => fail "list_index argument error: list_index" tm lst
  end.

Fixpoint mongenerics_list {a b} (f : monarr X a b) : list (monarrlistelt X) := 
  match f with
  | monarrcomp _ f' g' => mongenerics_list f' ++ mongenerics_list g'
  | monarrtens _ f' g' => mongenerics_list f' ++ mongenerics_list g'
  | mongeneric _ f' => [monarrlist_arr _ _ _ (mongeneric X f')]
  | monarrstruct _ _ => []
  end.


  (* Context (x y : X).
Goal True.
pose (fun f => @map_bw X nat f (var X x)) as H.
cbn in H.
let f z := list_index z [x ; y] in constr:(H (fun z => f z)).
specialize (H (fun z => ltac:())). *)



Ltac quote_bw tm vars := 
  lazymatch tm with
  | e _ => constr:(e nat)
  | var _ ?x => let r := list_index x vars in constr:(var nat r)
  | tens _ ?a ?b =>
    let res1 := quote_bw a vars in 
    let res2 := quote_bw b vars in 
    constr:(tens nat res1 res2)
  | _ => fail "bw to quote not recognized:" tm "(in context of vars:" vars")"      
  end.
  
(* Context (x y : X).
Goal True.
let r := quote_bw (var X x) [x] in idtac r. *)

Ltac quote_bwarr tm vars :=
  lazymatch tm with
  | arrid _ ?a => let a' := quote_bw a vars in 
      constr:(arrid nat a')
  | arrassoc _ ?a ?b ?c => 
    let a' := quote_bw a vars in 
    let b' := quote_bw b vars in 
    let c' := quote_bw c vars in 
      constr:(arrassoc nat a' b' c')
  | arrinvassoc _ ?a ?b ?c => 
    let a' := quote_bw a vars in 
    let b' := quote_bw b vars in 
    let c' := quote_bw c vars in 
      constr:(arrinvassoc nat a' b' c')
  | arrlunitor _ ?a => let a' := quote_bw a vars in 
      constr:(arrlunitor nat a')
  | arrinvlunitor _ ?a => let a' := quote_bw a vars in 
      constr:(arrinvlunitor nat a')
  | arrrunitor _ ?a => let a' := quote_bw a vars in 
      constr:(arrrunitor nat a')
  | arrinvrunitor _ ?a => let a' := quote_bw a vars in 
      constr:(arrinvrunitor nat a')
  | arrcomp _ ?f' ?g' => 
    let qf := quote_bwarr f' vars in
    let qg := quote_bwarr g' vars in
      constr:(arrcomp nat f' g')
  | arrtens _ ?f' ?g' => 
    let qf := quote_bwarr f' vars in
    let qg := quote_bwarr g' vars in
      constr:(arrtens nat f' g')
  | _ => fail "bwarr to quote not recognized:" tm "(in context of vars:" vars")"      
  end.

Ltac mongeneric_is_from_to mor source target :=
  lazymatch mor with
  | monarrlist_arr _ ?a ?b _ => 
      lazymatch bunify a source with
      | true => lazymatch bunify b target with
        | true => constr:(true)
        | false => constr:(false)
        end
      | false => constr:(false)
      end
  | _ => fail "mongeneric_is_from_to failed"
  end.

Ltac mongeneric_list_filter_from_to mors source target :=
  lazymatch mors with
  | @nil ?T => constr:(@nil T)
  | ?f :: ?mors' => 
      let res := mongeneric_list_filter_from_to mors' source target in
      lazymatch mongeneric_is_from_to f source target with
      | true => constr:(f :: res)
      | false => constr:(res)
      end
  | _ => fail "mongeneric_list_filter_from_to failed"
  end.

Ltac quote_to_nat_diagram tm vars mors := 
  lazymatch tm with
  | monarrstruct _ ?f => let res := quote_bwarr f vars in 
      constr:(@monarrstruct nat FreeNatCategory FreeNatMonoidalCategory _ _ res)
  | @mongeneric ?X ?cC ?mC ?a ?b ?f => 
    let mors' := mongeneric_list_filter_from_to mors a b in
    let tm' := constr:(@monarrlist_arr X cC mC a b tm) in 
    let idx := list_index tm' mors' in 
    let qa := quote_bw a vars in 
    let qb := quote_bw b vars in 
    constr:(@mongeneric nat FreeNatCategory FreeNatMonoidalCategory qa qb idx)
  | monarrcomp _ ?f ?g => 
    let qf := quote_to_nat_diagram f in
    let qg := quote_to_nat_diagram g in
    constr:(monarrcomp nat f g)
  | monarrtens _ ?f ?g => 
    let qf := quote_to_nat_diagram f in
    let qg := quote_to_nat_diagram g in
    constr:(monarrtens nat f g)
  | _ => fail "monarr to quote not recognized:" tm "(in context of vars:" vars" and mors:" mors")"
  end.

Ltac var_list_nodup f :=
  let lst := eval cbn in (all_vars f) in
  let r := list_dedup lst in constr:(r).

Ltac mongenerics_list_nodup f := 
  let lst := eval cbn in (mongenerics_list f) in
  let r := list_dedup lst in constr:(r).

Ltac quote_monarr_term tm :=
  let vars := var_list_nodup tm in
  let mors := mongenerics_list_nodup tm in 
  let res := quote_to_nat_diagram tm vars mors in
  constr:(res).

Ltac get_sources_targets mors :=
  lazymatch mors with
  | nil => constr:(@nil (bw X * bw X))
  | ?f :: ?mors' => 
      let res := get_sources_targets mors' in 
      lazymatch f with
      | monarrlist_arr _ ?a ?b _ => constr:((a,b) :: res)
      | _ => fail "bad value for get_sources_targets:" f "(in context of mors:" mors ")"
      end
  | _ => fail "bad arguments for get_sources_targets: get_sources_targets" mors
  end.

Definition nateqbw (a b : bw nat) :=
  eqbw nat PeanoNat.Nat.eq_dec a b.

Ltac unwrap_mongeneric_list cC mors a b :=
  lazymatch mors with 
  | nil => constr:(@nil (Category.morphism cC a b))
  | ?f :: ?mors' => let res := unwrap_mongeneric_list cC mors' a b in 
    lazymatch f with
    | monarrlist_arr _ _ _ (@mongeneric _ _ _ _ _ ?f') => constr:(f' :: res)
    | _ => fail "non-generic in unwrap_mongeneric_list:" f
    end
  | _ => fail "bar arguments: unwrap_mongeneric_list" cC mors a b
  end.

Definition cast_mor_list {A} {a a' b b' : A} (f : A -> A -> Type) (Ha : a = a') (Hb : b = b')
  (l : list (f a' b')) : list (f a b).
destruct Ha, Hb.
exact l.
Defined.

Ltac generify_natbw tm :=
  lazymatch tm with
  | e _ => uconstr:(e _)
  | var _ ?n => uconstr:(var _ n)
  | tens _ ?a ?b => 
      let ga := generify_natbw a in 
      let gb := generify_natbw b in 
      uconstr:(tens _ ga gb)
  end.

Definition succ_bwnat (a : bw nat) : bw nat :=
  match a with
  | e _ => e nat
  | var _ n => var nat (S n)
  | tens _ a b => tens nat a b
  end.

Fixpoint update_natbw_func_var (P : bw nat -> Type) (f : forall a, P a)
  (n : nat) : P (var nat n) -> forall a : bw nat, P a :=
  match n with
  | O => 
    fun new a => 
    match a with
    | var _ O => new
    | a' => f a'
    end
  | S n' =>
    fun new a => 
    match a with
    | var _ (S na') => 
        update_natbw_func_var (fun b => P (succ_bwnat b)) 
          (fun b => f (succ_bwnat b)) n' new (var nat na')
    | a' => f a'
    end
  end.


Fixpoint update_natbw_func (P : bw nat -> Type) (f : forall a, P a)
  (s : bw nat) : P s -> forall a : bw nat, P a :=
  match s with
  | e _ => 
    fun new a =>
    match a with
    | e _ => new
    | a' => f a'
    end
  | var _ n => 
    fun new a =>
    update_natbw_func_var P f n new a
  | tens _ sl sr =>
    fun new a => 
    match a with
    | tens _ al ar =>
    update_natbw_func (fun b => forall c, P (tens nat b c)) 
      (fun b c => f (tens nat b c)) 
      sl (fun c => 
        update_natbw_func (fun c => P (tens nat sl c)) 
          (fun c => f (tens nat sl c)) 
          sr new c) al ar
    | a' => f a'
    end
  end.


Definition update_natbw_bifunc (P : bw nat -> bw nat -> Type)
  (f : forall a b : bw nat, P a b) (s t : bw nat) (new : P s t) : 
    forall a b : bw nat, P a b :=
  update_natbw_func (fun a => forall b, P a b) f 
  s (update_natbw_func (P s) (f s) t new).



Ltac realize_mor_list_of_mors_st X cC mC real_obj vars mors st :=
  lazymatch st with
  | nil => constr:(fun a b : bw nat => 
    @nil (Category.morphism cC 
      (realize_bw X (map_bw real_obj a))
      (realize_bw X (map_bw real_obj b))))
  | (?s, ?t) :: ?st' => 
    let f := realize_mor_list_of_mors_st X cC mC real_obj vars mors st' in 
    let heremorelts := mongeneric_list_filter_from_to mors s t in 
    let qs := quote_bw s vars in 
    let qt := quote_bw t vars in 
    let gs := generify_natbw qs in 
    let gt := generify_natbw qt in 
    let heremors := unwrap_mongeneric_list cC 
      heremorelts (@realize_bw X cC mC (map_bw real_obj qs))
      (@realize_bw X cC mC (map_bw real_obj qt)) in
    (* let res := u *)
    let _ := match goal with |- _ => idtac gs gt end in
    let res := constr:(
    update_natbw_bifunc (fun a b =>
      list (Category.morphism cC 
              (realize_bw X (map_bw real_obj a))
              (realize_bw X (map_bw real_obj b)))
    ) f qs qt heremors) in
    (* fun a b : bw nat => 
    match a as a', b as b' return
        list (Category.morphism cC 
              (realize_bw X (map_bw real_obj a'))
              (realize_bw X (map_bw real_obj b')))
      with
    | (var _ 0), (var _ 1) => heremors
    (* | gs, gt => heremors *)
    | a'', b'' => f a'' b''
    end : list (Category.morphism cC 
    (realize_bw X (map_bw real_obj a))
    (realize_bw X (map_bw real_obj b)))) in  *)
    (* let res' := eval cbv delta [gs] in res in  *)
    let _ := match goal with |- _ => idtac res end in constr:(res)
    
    (* match nateqbw a qs, nateqbw b qt with
      | left Heql, left Heqr => 
        (* nth_default 
        (def 
          (realize_bw X (map_bw real_obj) a) 
          (realize_bw X (map_bw real_obj) b)) *)
        cast_mor_list 
          (fun x y => 
            Category.morphism cC 
              (realize_bw X (map_bw real_obj x))
              (realize_bw X (map_bw real_obj y))) 
          Heql Heqr 
          heremors
      | _, _ => f a b
      end
       *)
      
    (* in let _ := match goal with |- _ => idtac res end in constr:(res) *)
  | _ => fail "bad arguments: realize_mor_list_of_mors_st" X cC mC real_obj mors st
  end.

Ltac realize_obj_of_vars X def vars :=
  constr:(@nth_default X def vars).




Ltac var_list_nodup_two f g :=
  let lst := eval cbn in (all_vars f ++ all_vars g) in
  let r := list_dedup lst in constr:(r).

Ltac mongenerics_list_nodup_two f g := 
  let lst := eval cbn in (mongenerics_list f ++ mongenerics_list g) in
  let r := list_dedup lst in constr:(r).





Ltac realize_mor_list_of_mors X cC mC real_obj vars mors :=
  let st := get_sources_targets mors in
  let st' := list_dedup st in 
  let res := realize_mor_list_of_mors_st X cC mC real_obj vars mors st' in
  constr:(res).

Ltac DiagramListRealizer_of_term X cC mC tm := 
  let vars := var_list_nodup tm in
  let mors := mongenerics_list_nodup tm in 
  let monI := constr:(Monoidal.mon_I mC) in
  let real_obj := realize_obj_of_vars X monI vars in 
  let real_mor := realize_mor_list_of_mors X cC mC real_obj vars mors in
  constr:(Build_NatDiagramListRealizer X real_obj real_mor).

Ltac DiagramRealizer_of_term X cC mC tm mordef := 
  let NL := DiagramListRealizer_of_term X cC mC tm in
  constr:(NatDiagramRealizer_of_NatDiagramListRealizer_default X NL mordef).

Ltac DiagramListRealizer_of_two_terms X cC mC tm1 tm2 := 
  let vars := var_list_nodup_two tm1 tm2 in
  let mors := mongenerics_list_nodup_two tm1 tm2 in 
  let monI := constr:(Monoidal.mon_I mC) in
  let real_obj := realize_obj_of_vars X monI vars in 
  let real_mor := realize_mor_list_of_mors X cC mC real_obj vars mors in
  constr:(Build_NatDiagramListRealizer X real_obj real_mor).

Ltac DiagramRealizer_of_two_terms X cC mC tm1 tm2 mordef := 
  let NL := DiagramListRealizer_of_two_terms X cC mC tm1 tm2 in
  constr:(@NatDiagramRealizer_of_NatDiagramListRealizer_default X cC mC NL mordef).




Context (x y : X).
Context (X_def : forall a b : X, Category.morphism cC a b).
Context (h : Category.morphism cC x y).
Goal True.
let r := quote_monarr_term (monarrstruct X (arrlunitor X (var X x)))
in idtac r.
let r := DiagramListRealizer_of_term (monarrstruct X (arrlunitor X (var X x)))
in idtac r.

assert (monarrequiv X _ _ (@mongeneric X cC mC (var X x) (var X y) (h))
  (mongeneric X (X_def _ _) )).

(* let g := 2 in 
let res := uconstr:(fun k:nat => match k with
| g => 1
| _ => 0 end)
in 
let res' := eval lazy zeta in res in 
pose res'. *)

lazymatch goal with 
|- @monarrequiv ?X ?cC ?mC ?a ?b ?f ?g =>
  let R := DiagramRealizer_of_two_terms X cC mC f g X_def in 
  let vars := var_list_nodup_two f g in 
  let mors := mongenerics_list_nodup_two f g in 
  let qa := quote_bw a vars in 
  let qb := quote_bw b vars in 
  let qf := quote_to_nat_diagram f vars mors in 
  let qg := quote_to_nat_diagram g vars mors in 
  idtac qf qg;
  let real_obj := realize_obj_of_vars X (Monoidal.mon_I mC) vars in 
  (* assert (f = @realize_nat_diagram X cC mC R qa qb qf) *)
  change (@monarrequiv X cC mC (map_bw real_obj qa) (map_bw real_obj qb)
    (@realize_nat_diagram X cC mC R qa qb qf)
    (@realize_nat_diagram X cC mC R qa qb qg));
  apply (realize_nat_diagram_mor _ R)
end.



Require Import MetaCoq.Template.All.
Import MCMonadNotation.

cbv.

(* assert ((monarrstruct X (arrlunitor X (var X x))) = (monarrstruct X (arrlunitor X (var X x)))). *)
let tm := constr:(monarrstruct X (arrlunitor X (var X x))) in
let q := quote_monarr_term tm in 
let R := DiagramRealizer_of_term tm X_def in 
assert (monarrequiv _ _ _ tm tm);
change tm with (realize_nat_diagram X R q).
apply realize_nat_diagram_mor.

let tm := constr:(@mongeneric X cC mC (var X x) (var X y) (h)) in
let mgs := eval cbn in (mongenerics_list tm) in idtac mgs;
let q := quote_monarr_term tm in idtac q;
let R := DiagramRealizer_of_term tm f in 
assert (tm = tm);
change tm with (realize_nat_diagram X R q).


let r := quote_bw (var X x) [x] in idtac r.


Ltac extend_monarr_quotation_to N tm :=
  lazymatch tm with
  monarr


  (* Goal True.
  Fail let r := list_index 1 [2 ;  4 ;5] in idtac r. *)

Require Import MetaCoq.Template.All.
Import MCMonadNotation.

Inductive taut : Set :=
| TautTrue : taut
| TautAnd : taut -> taut -> taut
| TautOr : taut -> taut -> taut
| TautImp : taut -> taut -> taut.

Fixpoint tautReify (t : term) : TemplateMonad taut :=
  match t with
  | tInd {| inductive_mind := (MPfile _, "True"%bs); inductive_ind := _ |} _ =>
      ret TautTrue
  | tProd _ a b =>
      a' <- tautReify a ;;
      b' <- tautReify b ;;
      ret (TautImp a' b')
  | tApp (tInd {| inductive_mind := (MPfile _, "and"%bs); inductive_ind := _ |} _) [a ; b] =>
      a' <- tautReify a ;;
      b' <- tautReify b ;;
      ret (TautAnd a' b')
  | tApp (tInd {| inductive_mind := (MPfile _, "or"%bs); inductive_ind := _ |} _) [a ; b] =>
      a' <- tautReify a ;;
      b' <- tautReify b ;;
      ret (TautOr a' b')
  | _ => tmFail "No match for term"%bs
  end.

Fixpoint digramReify (t : term) : TemplateMonad ()

Fixpoint tautDenote (t : taut) : Prop :=
  match t with
    | TautTrue => True
    | TautAnd t1 t2 => tautDenote t1 /\ tautDenote t2
    | TautOr t1 t2 => tautDenote t1 \/ tautDenote t2
    | TautImp t1 t2 => tautDenote t1 -> tautDenote t2
  end.

Theorem tautTrue : forall t, tautDenote t.
  induction t; simpl; intuition.
Qed.

Ltac obvious :=
  match goal with
  | [ |- ?P ] => run_template_program (tmQuote P >>= tmEval all >>= tautReify)
                   (fun p => exact (tautTrue p))
  end.

Goal True /\ (True \/ True).
  match goal with | [ |- ?P ] => let r := constr:((tmQuote P) >>= tmEval all) in 
  idtac r;
  run_template_program r (fun p => idtac p)
  end.
  tmEval
  run_template_program ()
  obvious.

Lemma NatDiagramRealizer_proper




#[local] Instance FreeNatCategory : Category (bw nat) := {
  morphism _ _ := nat : Type;
  c_equiv _ _ := eq;
  compose _ _ _ := Nat.add;
  c_identity _ := 0;
}.

#[local] Program Instance FreeNatCategoryCoherence : 
  CategoryCoherence FreeNatCategory.
Next Obligation.
  split; intros ? **; congruence.
Qed.
Next Obligation.
  lia.
Qed.

#[local] Program Instance FreeNatMonoidalCategory@{u u1} : 
  MonoidalCategory FreeNatCategory@{u u1} := {
  obj_tensor := tens nat;
  mor_tensor _ _ _ _ := Nat.add;
  mon_I := e nat;
  associator _ _ _ := {|forward := 0; reverse := 0|};
  left_unitor _ := {|forward := 0; reverse := 0|};
  right_unitor _ := {|forward := 0; reverse := 0|};
}.

#[local] Program Instance FreeNatMonoidalCategoryCoherence : 
  MonoidalCategoryCoherence FreeNatMonoidalCategory := {}.
Next Obligation.
  lia.
Qed.
Next Obligation.
  lia.
Qed.
Next Obligation.
  lia.
Qed.




Local Notation N_real := (realize_nat_bw N.(realize_obj)).

Fixpoint realize_nat_bwarr {a b} (f : bwarr nat a b) : N_real a ~> N_real b := 
  match f with
  | arrid _ a => id_ (N_real a)
  | arrassoc _ a b c => α_ (N_real a), N_real b, N_real c ⁻¹
  | arrinvassoc _ a b c => α_ (N_real a), N_real b, N_real c
  | arrlunitor _ a => λ_ (N_real a)
  | arrinvlunitor _ a => λ_ (N_real a) ⁻¹
  | arrrunitor _ a => ρ_ (N_real a)
  | arrinvrunitor _ a => ρ_ (N_real a) ⁻¹
  | arrcomp _ f g => realize_nat_bwarr f ∘ realize_nat_bwarr g
  | arrtens _ f g => realize_nat_bwarr f ⊗ realize_nat_bwarr g
  end.

Add Parametric Morphism {a b} : realize_nat_bwarr with signature
  bwarrequiv nat a b ==> cC.(c_equiv)
  as realize_nat_bwarr_mor.
Proof.
  intros f g H.
  induction H.
  - reflexivity.
  - etransitivity; eassumption.
  - apply compose_compat; assumption.
  - simpl; symmetry; apply assoc.
  - simpl; apply assoc.
  - apply left_unit.
  - symmetry; apply left_unit.
  - apply right_unit.
  - symmetry; apply right_unit.
  - apply tensor_compat; assumption.
  - apply tensor_id.
  - symmetry; apply tensor_id.
  - apply tensor_compose.
  - symmetry; apply tensor_compose.
  - apply iso_inv_l.
  - symmetry; apply iso_inv_l.
  - apply iso_inv_r.
  - symmetry; apply iso_inv_r.
  - apply iso_inv_r.
  - symmetry; apply iso_inv_r.
  - apply iso_inv_l.
  - symmetry; apply iso_inv_l.
  - apply iso_inv_r.
  - symmetry; apply iso_inv_r.
  - apply iso_inv_l.
  - symmetry; apply iso_inv_l.
  - simpl. 
    rewrite <- compose_iso_l', <- assoc.
    rewrite <- compose_iso_r.
    symmetry.
    apply associator_cohere.
  - simpl. 
    rewrite <- compose_iso_l, <- assoc.
    rewrite <- compose_iso_r'.
    apply associator_cohere.
  - apply left_unitor_cohere.
  - symmetry; apply left_unitor_cohere.
  - apply right_unitor_cohere.
  - symmetry; apply right_unitor_cohere.
  - simpl.
    rewrite <- compose_iso_l'.
    rewrite <- right_unit.
    rewrite <- compose_iso_l'.
    rewrite <- assoc.
    rewrite <- pentagon.
    rewrite assoc, <- 2!(assoc (id_ _ ⊗ _)).
    rewrite <- tensor_compose, iso_inv_r, left_unit, tensor_id, left_unit.
    rewrite assoc, <- (assoc (α_ _,_,_)), iso_inv_r, left_unit.
    rewrite <- tensor_compose, iso_inv_r, left_unit, tensor_id.
    easy.
  - symmetry.
    simpl.
    rewrite <- compose_iso_l'.
    rewrite <- right_unit.
    rewrite <- compose_iso_l'.
    rewrite <- assoc.
    rewrite <- pentagon.
    rewrite assoc, <- 2!(assoc (id_ _ ⊗ _)).
    rewrite <- tensor_compose, iso_inv_r, left_unit, tensor_id, left_unit.
    rewrite assoc, <- (assoc (α_ _,_,_)), iso_inv_r, left_unit.
    rewrite <- tensor_compose, iso_inv_r, left_unit, tensor_id.
    easy.
  - simpl.
    rewrite <- triangle.
    rewrite <- assoc, iso_inv_l, left_unit.
    easy.
  - symmetry.
    simpl.
    rewrite <- triangle.
    rewrite <- assoc, iso_inv_l, left_unit.
    easy.
Qed.







Lemma binary_proper_op_preserves {f} (H : binary_monarrlist_op_proper f) 
  {fss : list monarrlist} (Hf : totally_composable fss) : 
  monarr_norm_equiv 
    (comp_compble fss Hf)
    (comp_compble (map f fss) (unary_proper_op_totally_composable H Hf)).
Proof.
  induction fss; [apply monarr_norm_equiv_refl|]; destruct fss.
  - apply monarr_norm_equiv_symm.
    apply (H a).
  - unfold comp_compble.
    simpl map.
    rewrite 2!compose_monarrlist_list_of_totally_composable_cons.
    apply monarr_norm_equiv_comp_composable;
    [apply monarr_norm_equiv_symm, (H a)|].
    erewrite (compose_monarrlist_list_of_totally_composable_indep (f l :: _)).
    apply IHfss.
Qed.


Lemma foliate_test2 {a b c m n o} (f : bwarr a b) (g : bwarr b c)
  (h : bwarr m n) (j : bwarr n o) : 
  (f ◌ g) ⧆ (arrid m ◌ h) ≊ f ⧆ h ◌ g ⧆ arrid n.
Proof.
  apply equiv_of_foliate_equiv.
  freeze_equiv.
  cbn.
  etransitivity.
  symmetry.
  
  apply unary_monarrlist_op_proper


  









  



Inductive monnormarr : bwnorm -> bwnorm -> Type :=
  | monnorm_id (a : bwnorm) : monnormarr a a
  | monnorm_monarr {a b : bw} (f : a ⟶ b) 
    : monnormarr (Nf a) (Nf b).

Definition monnormarr_to_monarr {a b : bwnorm} (f : monnormarr a b) 
  : monarr a b :=
  match f with
  | @monnorm_id a => arrid a
  | @monnorm_monarr a' b' f => 
      monarrcomp (monarrcomp
      (from_Nf_arr a') 
      f)
      (to_Nf_arr b')
  end.
Inductive monnormstack : list bwnorm -> list bwnorm -> Type :=
  | monnormstack_nil : monnormstack [] []
  | monnormstack_cons {s t ins outs} 
    (f : monnormarr s t) (fs : monnormstack ins outs) :
      monnormstack (s::ins) (t::outs).

Inductive monnormdiagram : list bwnorm -> list bwnorm -> Type :=
  | monnormdiag_single {ins outs} (fs : monnormstack ins outs) : 
      monnormdiagram ins outs
  | monnormdiag_compose {ins mids outs}
      (fs : monnormstack ins mids) (fdiag : monnormdiagram mids outs) :
      monnormdiagram ins outs.

Definition realize_monnormarr {a b} (f : monnormarr a b) : 
  realize_bw a ~> realize_bw b :=
  realize_monarr (monnormarr_to_monarr f).
  (* match f with
  | monnorm_id a => id_ _
  | @monnorm_monarr a' b' g => 
    realize_bwarr (from_Nf_arr a' ∘
    realize_monarr g ∘
    to_Nf_arr b'
  end. *)

Definition bwnorm_flatten (bwns : list bwnorm) : bw :=
  fold_right (fun a n => tens n (bwnorm_to_bw a)) e bwns.

Fixpoint realize_monnormstack {ins outs} (fs : monnormstack ins outs) : 
  realize_bw (bwnorm_flatten ins) ~> realize_bw (bwnorm_flatten outs) :=
  match fs with
  | monnormstack_nil => c_identity _
  | monnormstack_cons f' fs' => 
    realize_monnormstack fs' ⊗ realize_monnormarr f'
  end.

Fixpoint realize_monnormdiagram {ins outs} (fd : monnormdiagram ins outs) :
  realize_bw (bwnorm_flatten ins) ~> realize_bw (bwnorm_flatten outs) :=
  match fd with
  | monnormdiag_single fs => realize_monnormstack fs
  | monnormdiag_compose fs fd' => 
      realize_monnormstack fs ∘ realize_monnormdiagram fd'
  end.



Definition merge_left_pair (f g : monarrlistelt) : monarrlistelt * monarrlistelt :=
  match eqbw (target f') (source g')
  match f, g with
  | monarrlist_id a, g => (g, )

Fixpoint merge_left_monarrlist (f g : list monarrlistelt) : 
  (list monarrlistelt) * (list monarrlistelt).
  match f, g with
  | fs, [] => (fs, [])
  | [], gs => ([], gs)
  | f'::fs, g'::gs => 
    match merge_left_monarrlist fs gs with
    | fs', gs' =>
      match eqbw (target f') (source g') with
      | left heq_ts => 
        match f', g' with
        | monarrlist_id a, g' => 
        end
      | right _ =>
        (f' :: fs', g' :: gs')
      end
  
Obligation Tactic := 
Tactics.program_simpl; eauto 4 using monarrequiv with bwarrdb; try easy.


(* Inductive monarrequiv : forall a b, relation (a ⟶ b) :=
  | monarr_refl {a b} (f : a ⟶ b) : f ≅ f
  | monarr_symm {a b} (f g : a ⟶ b) : f ≅ g -> g ≅ f
  | monarr_trans {a b} (f g h : a ⟶ b) : f ≅ g -> g ≅ h -> f ≅ h
  
  | monarr_comp {a b c : bw} (f f' : a ⟶ b) (g g' : b ⟶ c) :
      f ≅ f' -> g ≅ g' -> monarrcomp f g ≅ monarrcomp f' g'
  | monarr_assoc {a a' b' b : bw} (f : a ⟶ a') (g : a' ⟶ b') (h : b' ⟶ b) :
      monarrcomp f (monarrcomp g h) ≅ monarrcomp (monarrcomp f g) h
  (* | bwarr_lassoc {a a' b' b : bw} (f : a ⟶ a') (g : a' ⟶ b') (h : b' ⟶ b) :
      arrcomp (arrcomp f g) h ≅ arrcomp f (arrcomp g h) *)
  | monarr_lunit {a b} (f : a ⟶ b) : monarrcomp (arrid a) f ≅ f
  (* | bwarr_lunitr {a b} (f : a ⟶ b) : f ≅ arrcomp (arrid a) f *)
  | monarr_runit {a b} (f : a ⟶ b) : monarrcomp f (arrid b) ≅ f
  (* | bwarr_runitr {a b} (f : a ⟶ b) : f ≅ arrcomp f (arrid b) *)

  | monarr_tens {a a' b b' : bw} (f f' : a ⟶ a') (g g' : b ⟶ b') :
    f ≅ f' -> g ≅ g' -> monarrtens f g ≅ monarrtens f' g'
  (* | monarr_tens_id {a b : bw} :
    monarrtens (arrid a) (arrid b) ≅ arrid (a ⨂ b) *)
  (* | monarr_tens_idr {a b : bw} :
    arrid (a ⨂ b) ≅ arrtens (arrid a) (arrid b) *)
  | monarr_tens_comp {a b c a' b' c'} 
    (f : a ⟶ b) (g : b ⟶ c) (f' : a' ⟶ b') (g' : b' ⟶ c') :
    monarrtens (monarrcomp f g) (monarrcomp f' g') ≅ 
      monarrcomp (monarrtens f f') (monarrtens g g')
  (* | bwarr_tens_compr {a b c a' b' c'} 
    (f : a ⟶ b) (g : b ⟶ c) (f' : a' ⟶ b') (g' : b' ⟶ c') :
    arrcomp (arrtens f f') (arrtens g g') ≅ 
      arrtens (arrcomp f g) (arrcomp f' g') *)
    where "f '≅' g" := (monarrequiv _ _ f g). *)


Inductive monarrequiv : forall (a b : bw), relation (monarr a b) := 
  | monarrstructeq {a b : bw} (f g : bwarr a b) :
      bwarrequiv a b f g -> monarrequiv a b f g
  | mon.

End MonoidalExpressionNormalForm.


Section CoherenceAutomation.

End CoherenceAutomation.

(* 
Lemma bwbrac_arr_of_arr_comp {a b c : bw} (f : a ⟶ b) (g : b ⟶ c) :
  (arrcomp (bwbrac_arr_of_arr f1 n)
  (bwbrac_arr_of_arr f2 n)) ≅ bwbrac_arr_of_arr *)

End MonoidalCoherence.



End FreeMonoid.

Section Old_may_reuse_for_UIP_only. 

(*



Lemma bwbrac_bwnorm : forall (a : bwnorm), ⟦a⟧ norm_e = a.
Proof.
  intros a.
  induction a; auto.
  simpl.
  rewrite IHa.
  easy.
Qed.

Require Import Coq.Program.Equality.

Lemma Nf_bwnorm : forall (n : bwnorm), Nf n = n.
Proof.
  unfold Nf.
  intros n; induction n; simpl; rewrite ?IHn; auto.
Qed.

Lemma bwnorm_eq_of_arr {n m : bwnorm} (i : n ⟶ m) : n = m.
Proof.
  pose proof (Nf_functor.(morphism_map) i) as H.
  rewrite 2!Nf_bwnorm in H.
  apply H.
Qed.

(* Lemma bwnorm_selfarr_id : forall (n : bwnorm) (i : n ⟶ n), i ≅ arrid n.
Lemma bwnorm_arr_thin : forall (n m : bwnorm) (i j : n ⟶ m), i ≅ j.*)
(* 
  F : a, n ↦ n ⊗ a
  G : a, n ↦ ⟦ a ⟧ n 
*)



Lemma bwnorm_eq_of_arr_refl {n : bwnorm} (f : n ⟶ n) : 
  bwnorm_eq_of_arr f = eq_refl.
Proof.
  apply Eqdep_dec.UIP_dec, eqbwnorm.
Qed.

Definition xi_norm_map {a : bw} {n m : bwnorm} (f : n ⟶ m) : ⟦a⟧ n ⟶ ⟦a⟧ m.
  rewrite <- (bwnorm_eq_of_arr f).
  apply arrid.
Defined.
(* 
Definition xi_bimap {a b} {n m : bwnorm} 
  (f : a ⟶ b) (i : n ⟶ m) : ⟦a⟧ n ⟶ ⟦b⟧ m.
  rewrite <- (bwnorm_eq_of_arr i).
  apply (bwbrac_arr_of_arr f).
Defined.
  
Lemma xi_bimap_refl {a b} (n : bwnorm) (f : a ⟶ b) (i : n ⟶ n) :
  xi_bimap f i = bwbrac_arr_of_arr f n.
Proof.
  unfold xi_bimap.
  rewrite bwnorm_eq_of_arr_refl.
  easy.
Qed.

Lemma xi_bimap_compose {a b c} {n m o : bwnorm} 
  (f : a ⟶ b) (g: b ⟶ c) (i : n ⟶ m) (j : m ⟶ o) :
  xi_bimap f i ○ xi_bimap g j ≅ xi_bimap (f ○ g) (i ○ j).
Proof.
  specialize (bwnorm_eq_of_arr i) as Hnm.
  subst n.
  specialize (bwnorm_eq_of_arr j) as Hmo.
  subst m.
  rewrite 3!xi_bimap_refl.
  easy.
Qed.

Lemma xi_bimap_tens {a b a' b'} {n m : bwnorm} 
  (f : a ⟶ a') (g : b ⟶ b') (i : n ⟶ m) :
  xi_bimap g (xi_bimap f i) ≅ xi_bimap (f ⊠ g) i.
Proof.
  specialize (bwnorm_eq_of_arr i) as Hnm.
  subst n.
  rewrite !xi_bimap_refl.
  simpl.
  unfold xi_bimap.
  (* :( )*)
  rewrite (Eqdep_dec.UIP_dec eqbwnorm 
    (bwbrac_of_bweq a a' (bweq_of_arr f) m) 
    (bwnorm_eq_of_arr (bwbrac_arr_of_arr f m))).
  easy.
Qed.


Lemma xi_bimap_norm_indep {a b} {n m : bwnorm} (f : a ⟶ b) (i i' : n ⟶ m) :
  xi_bimap f i ≅ xi_bimap f i'.
Proof.
  specialize (bwnorm_eq_of_arr i) as Hnm; subst n.
  rewrite 2!xi_bimap_refl.
  easy.
Qed. *)



(* Lemma xi_bimap_id (a : bw) {n m : bwnorm} (i : n ⟶ m) :
  xi_bimap (arrid e) i ≅ i.
Proof.
  specialize (bwnorm_eq_of_arr i) as Hnm; subst n.
  rewrite xi_bimap_refl.
  simpl.
  unfold xi_bimap.
  rewrite xi_bimap_refl. *)

(* Lemma xi_norm_natural {n m : bwnorm} (i j : n ) *)

Definition xi_bimap {a b} {n m : bwnorm} 
  (f : a ⟶ b) (i : n = m) : ⟦a⟧ n ⟶ ⟦b⟧ m.
  rewrite <- i.
  apply (bwbrac_arr_of_arr f).
Defined.

Lemma xi_bimap_refl {a b} (n : bwnorm) (f : a ⟶ b) (i : n = n) :
  xi_bimap f i ≅ bwbrac_arr_of_arr f n.
Proof.
  rewrite (Eqdep_dec.UIP_dec eqbwnorm i eq_refl).
  easy.
Qed.

Lemma xi_bimap_refl' {a b} (n : bwnorm) (f : a ⟶ b) (i : n = n) :
  xi_bimap f i ≅ xi_bimap f eq_refl.
Proof.
  rewrite xi_bimap_refl.
  easy.
Qed.

Definition bwnorm_arr_of_eq {n m : bwnorm} (H : n = m) : n ⟶ m.
rewrite <- H.
apply arrid.
Defined.

Lemma xi_bimap_compose' {a b c} {n m o : bwnorm} 
  (f : a ⟶ b) (g : b ⟶ c) (i : n = m) (j : m = o) (k : n = o) :
  xi_bimap (f ○ g) k ≅ xi_bimap f i ○ xi_bimap g j.
Proof.
  subst.
  rewrite xi_bimap_refl.
  easy.
Qed.

Lemma xi_bimap_compose_l {a b c} {n m : bwnorm} 
  (f : a ⟶ b) (g : b ⟶ c) (i : n = m) :
  xi_bimap (f ○ g) i ≅ xi_bimap f i ○ xi_bimap g eq_refl.
Proof.
  subst. easy.
Qed.

Lemma xi_bimap_compose_r {a b c} {n m : bwnorm} 
  (f : a ⟶ b) (g : b ⟶ c) (i : n = m) :
  xi_bimap (f ○ g) i ≅ xi_bimap f eq_refl ○ xi_bimap g i.
Proof.
  subst. easy.
Qed.

Lemma bwnorm_arr_of_eq_refl (m : bwnorm) : 
  bwnorm_arr_of_eq (eq_refl (x:=m)) = arrid m.
Proof.
  easy.
Qed.



(* Lemma bwbrac_eq_of_arr_comp {a b c} (f1 : a ⟶ b) (f2 : b ⟶ c) (n : bwnorm),
  bwbrac_eq_of_arr (f1 ○ f2) n = 

Lemma bwnorm_arr_of_bwbrac_eq_compose {a b c} (f1 : a ⟶ b) (f2 : b ⟶ c) : 
  forall n,
  bwnorm_arr_of_eq (bwbrac_eq_of_arr f1 n)
  ○ bwnorm_arr_of_eq (bwbrac_eq_of_arr f2 n)
  ≅ bwnorm_arr_of_eq (bwbrac_eq_of_arr (f1 ○ f2) n).
Proof.
  unfold bwnorm_arr_of_eq.
  intros n.
  generalize (bwbrac_eq_of_arr f1 n) as Hf1.
  generalize (bwbrac_eq_of_arr f2 n) as Hf2.
  simpl bwbrac_eq_of_arr.


Lemma xi_bimap_refl'' {a b} (n : bwnorm) (f : a ⟶ b) (i : n = n) :
  xi_bimap f i ≅ bwnorm_arr_of_eq (bwbrac_eq_of_arr f n).
Proof.
  rewrite xi_bimap_refl.
  induction f; try easy.
  simpl bwbrac_arr_of_arr.
  rewrite IHf1, IHf2.
  simpl.
  unfold bwbrac_eq_of_arr.
  simpl.
  unfold bwbrac_arr_of_arr.
  s *)


Definition nu_map (a : bw) : a ⟶ Nf a :=
  arrinvlunitor a ○ (xi_comp_map_forw norm_e a).

Definition bwnorm_arr_of_arr {a b} (f : a ⟶ b) : Nf a ⟶ Nf b 
  := bwbrac_arr_of_arr f norm_e.
(* induction f; eauto 2 using bwarr.
unfold Nf in *.
simpl.
rewrite <- (bwnorm_eq_of_arr IHf1).
rewrite <- bwbrac_arr_of_arr *)

(* Lemma nu_map_natural {a b : bw} (f : a ⟶ b) :
  f ○ nu_map b ≅ nu_map a ○ bwnorm_arr_of_arr f.
Proof.
  induction f.
  - unfold bwnorm_arr_of_arr. simpl.
    rewrite bwarr_lassoc, IHf2, bwarr_rassoc, IHf1, bwarr_lassoc.
    easy.
  - unfold nu_map.
*)


(* Lemma Nf_tens (a b : bw) : Nf (a ⊗ b) = norm_e. *)

Definition bwbrac_assoc (a b c : bw) (n : bwnorm) :
  ⟦c⟧ (⟦a ⨂ b⟧ n) = ⟦b ⨂ c⟧ (⟦a⟧ n) := eq_refl.

Definition bwbrac_arr_of_bwnorm_arr (a : bw) 
  {n m : bw} (i : n ⟶ m) : ⟦a⟧ (Nf n) ⟶ ⟦a⟧ (Nf m).
Proof.
  clear DECEQX.
  revert a.
  induction i; try eauto 2 using bwarr.
  intros c.
  unfold Nf.
  rewrite 2!bwbrac_assoc.
  eapply arrcomp.
  - apply IHi1.
  - simpl.
    unfold Nf.
    rewrite <- (bwbrac_eq_of_arr i2). 
    apply arrid.
Defined.

Lemma bwnorm_arr_of_arr_id (n : bw) : 
  bwnorm_arr_of_arr (arrid n) ≅ arrid (Nf n).
Proof. easy. Qed.

Lemma xi_bwbrac_nat (a b : bw) {n m : bw} (i : n ⟶ m) :
  bwbrac_arr_of_bwnorm_arr a i ⊠ arrid b
    ○ (ξ_ (⟦ a ⟧ (⟦ m ⟧ norm_e)) b)
  ≅ (ξ_ (⟦ a ⟧ (⟦ n ⟧ norm_e)) b)
    ○ bwbrac_arr_of_bwnorm_arr (a ⨂ b) i.
Proof.
  revert a b.
  dependent induction i; intros a0 b0.
  - simpl.
    rewrite arrtens_pushout_top, bwarr_lassoc, IHi2, bwarr_rassoc, IHi1.
    rewrite bwarr_lassoc. easy.
  - pose proof (IHi1 (b' ⨂ a0) b0) as e.
    simpl in e.
    to_Cat.
    RHS (fun t => set (rhs := t)).
    simpl.
    
    rewrite <- (bwbrac_assoc a' b' a0) in e.
    dependent rewrite (bwbrac_assoc a' b' a0).
    simpl.
  unfold bwbrac_arr_of_bwnorm_arr.

Lemma xi_natural (a b : bw) (f : a ⟶ b) : forall (n m : bw) (i : n ⟶ m),
  ((bwnorm_arr_of_arr i) ⊠ f) ○ (ξ_ (Nf m) b)
  ≅ (ξ_ (Nf n) a) ○ bwbrac_arr_of_arr f (Nf n) ○ bwbrac_arr_of_bwnorm_arr b i.
Proof.
  induction f; intros n m i.
  - simpl.
    rewrite arrtens_pushin_bot, bwarr_lassoc.

    rewrite <- (bwnorm_arr_of_arr_id n).
    rewrite IHf2, !bwarr_rassoc, IHf1.
    simpl.
    rewrite bwarr_runitl.
    easy.
  - simpl (ξ_ (Nf m) (a' ⨂ b')). 
    rewrite !bwarr_rassoc, bwarr_assoc_natr.
    rewrite (bwarr_lassoc (arrassoc (Nf n) a b)).
    rewrite bwarr_tens_compr, IHf1, bwarr_runitl.
    rewrite arrtens_pushin_top, 2!bwarr_lassoc.
    pose proof (IHf2 (m ⨂ a') (m ⨂ a')) as e.

    unfold Nf in e;
    simpl in e.
    rewrite (arrtens_split_diag _ f2), bwarr_lassoc, 
      <- (bwnorm_arr_of_arr_id (m ⨂ a')).
    rewrite (e (arrid _)).
    clear e.

    rewrite IHf2.
    bwbrac_arr_of_bwnorm_arr
    Check (bwbrac_arr_of_bwnorm_arr a' i ⊠ f2 ○ ξ_ (⟦ a' ⟧ (Nf m)) b').
    evar (gl : ⟦ a' ⟧ (Nf n) ⨂ b ⟶ ⟦ b' ⟧ (⟦ a' ⟧ (Nf m))).
    assert (bwbrac_arr_of_bwnorm_arr a' i ⊠ f2 ○ ξ_ (⟦ a' ⟧ (Nf m)) b' ≅ gl).
    + 
    rewrite IHf2.

    subst.
    rewrite xi_bimap_refl.
    rewrite (arrtens_split_diag _ f2),
      <- (bwnorm_arr_of_eq_refl (⟦a'⟧ m)), bwarr_lassoc.
    rewrite IHf2.
    
    simpl (ξ_ m (a⨂b)).

    rewrite !bwarr_lassoc.
    repeat (apply bwarr_comp; [easy|]).
    rewrite bwarr_rassoc.
    rewrite 3!xi_bimap_refl.
    simpl (bwbrac_arr_of_arr (_ ⊠ _) _).
    
    generalize dependent (⟦a⟧ m).
    simpl.
    

    apply xi_bimap_tens.
  - 
    revert n m i; induction a; intros n m i;
    specialize (bwnorm_eq_of_arr i) as Hnm; 


Lemma xi_natural (a b : bw) (f : a ⟶ b) : forall (n m : bwnorm) (i : n = m),
  arrcomp (arrtens (bwnorm_arr_of_eq i) f) (ξ_ m b) 
  ≅ arrcomp (ξ_ n a) (xi_bimap f i).
Proof.
  induction f; intros n m i.
  - rewrite arrtens_pushout_bot, bwarr_lassoc.
    rewrite <- (bwnorm_arr_of_eq_refl m).
    rewrite IHf2, bwarr_rassoc, IHf1, bwarr_lassoc.
    rewrite xi_bimap_compose_l.
    easy.
  - simpl (ξ_ m (a' ⨂ b')). 
    rewrite !bwarr_rassoc, bwarr_assoc_natr.
    rewrite (bwarr_lassoc (arrassoc n a b)).
    rewrite bwarr_tens_compr, IHf1, bwarr_runitl.
    rewrite arrtens_pushin_top, 2!bwarr_lassoc.

    subst.
    rewrite xi_bimap_refl.
    rewrite (arrtens_split_diag _ f2),
      <- (bwnorm_arr_of_eq_refl (⟦a'⟧ m)), bwarr_lassoc.
    rewrite IHf2.
    
    simpl (ξ_ m (a⨂b)).

    rewrite !bwarr_lassoc.
    repeat (apply bwarr_comp; [easy|]).
    rewrite bwarr_rassoc.
    rewrite 3!xi_bimap_refl.
    simpl (bwbrac_arr_of_arr (_ ⊠ _) _).
    
    generalize dependent (⟦a⟧ m).
    simpl.
    

    apply xi_bimap_tens.
  - 
    revert n m i; induction a; intros n m i;
    specialize (bwnorm_eq_of_arr i) as Hnm; 
    subst n;
    simpl.
    (* rewrite xi_bimap_refl.
    simpl. *)
    rewrite bwarr_runitor_natr.


    rewrite xi_bimap_refl.
    simpl.


Lemma xi_natural (a b : bw) (f : a ⟶ b) : forall (n m : bwnorm) (i : n ⟶ m),
  arrcomp (arrtens (arrid n) f) (ξ_ m b) 
  ≅ arrcomp (ξ_ n a) (xi_bimap f i).
Proof.
  induction f; intros n m i.
  - rewrite arrtens_pushout_bot, bwarr_lassoc, IHf2, 
      bwarr_rassoc, IHf1, bwarr_lassoc.
    rewrite xi_bimap_compose. 
    apply (compose_cancel_l (cC:=bwcat)).
    apply xi_bimap_norm_indep.
  - simpl (ξ_ m (a' ⨂ b')). 
    rewrite !bwarr_rassoc, bwarr_assoc_natr.
    rewrite (bwarr_lassoc (arrassoc n a b)).
    rewrite bwarr_tens_compr, IHf1, bwarr_runitl.
    rewrite arrtens_pushin_top, 2!bwarr_lassoc, IHf2.
    simpl.
    rewrite !bwarr_lassoc.
    repeat (apply bwarr_comp; [easy|]).
    apply xi_bimap_tens.
  - 
    revert n m i; induction a; intros n m i;
    specialize (bwnorm_eq_of_arr i) as Hnm; 
    subst n;
    simpl.
    (* rewrite xi_bimap_refl.
    simpl. *)
    rewrite bwarr_runitor_natr.


    rewrite xi_bimap_refl.
    simpl.

    
    


(* F : a ↦ n ⊗ a
   G : a ↦ ⟦ a ⟧ n *)
Lemma xi_natural (a b : bw) (f : a ⟶ b) : forall (n : bwnorm) (i : n ⟶ n),
  arrcomp (arrtens i f) (ξ_ n b) 
  ≅ arrcomp (ξ_ n a) (bwbrac_arr_of_arr f n).
Proof.
  induction f; intros n i.
  - rewrite arrtens_pushout_bot, bwarr_lassoc, IHf2, 
      bwarr_rassoc, IHf1, bwarr_lassoc.
    easy.
  - simpl (ξ_ n (a' ⨂ b')). 
    rewrite !bwarr_rassoc.
    rewrite bwarr_assoc_natr.
    rewrite (bwarr_lassoc (arrassoc n a b)).
    rewrite bwarr_tens_compr, IHf1.
    
    change @bwarrequiv with (@c_equiv bw bwcat).
    RHS (fun t => set (rhs := t)).
    simpl c_equiv.

    rewrite bwarr_runitl.
    rewrite arrtens_pushout_top, 2!bwarr_lassoc.

    rewrite IHf2.
    simpl.
    rewrite !bwarr_lassoc.
    rewrite 
    simpl.
    rewrite arrtens_pushout_bot. 
    simpl.

 

(* F : a ↦ n ⊗ a
   G : a ↦ ⟦ a ⟧ n *)
Lemma xi_natural (a b : bw) (f : a ⟶ b) : forall (n : bwnorm),
  arrcomp (arrtens (arrid n) f) (ξ_ n b) 
  ≅ arrcomp (ξ_ n a) (bwbrac_arr_of_arr f n).
Proof.
  induction f; intros n.
  (* 3: eauto 3 with bwarrdb. *)
  (* 5: eauto 4 with bwarrdb. *)
  - rewrite arrtens_pushout_bot, bwarr_lassoc, IHf2, 
      bwarr_rassoc, IHf1, bwarr_lassoc.
    easy.
  - simpl (ξ_ n (a' ⨂ b')). 
    rewrite !bwarr_rassoc.
    rewrite bwarr_assoc_natr.
    rewrite (bwarr_lassoc (arrassoc n a b)).
    rewrite bwarr_tens_compr, IHf1. 
    
    change @bwarrequiv with (@c_equiv bw bwcat).
    RHS (fun t => set (rhs := t)).
    simpl c_equiv.

    rewrite bwarr_runitl, bwarr_lassoc.

    rewrite IHf2.
    simpl.
    rewrite !bwarr_lassoc.
    rewrite 
    simpl.
    rewrite arrtens_pushout_bot. 
    simpl.
    


    to_Cat.

    change @arrcomp with (@compose bw bwcat) in *.

    rewrite <- (left_unit (id_ n)%Cat).
    Search "id_" outside CategoryAutomation.



#[export, program] Instance xi_ni :
  NaturalIsomorphism 


*)

End Old_may_reuse_for_UIP_only.