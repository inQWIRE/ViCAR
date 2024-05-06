Require Import Setoid.
From ViCaR Require Import CategoryTypeclass CategoryAutomation.
Require Logic.Eqdep_dec.
Require Import CatExample (FunctorCategory).
Require Import FunctionalExtensionality.


Section FreeMonoid.

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

Inductive monnormarr (a b : bwnorm) :=
  | 
  
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