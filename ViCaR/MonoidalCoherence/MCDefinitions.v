Require Export Setoid.
From ViCaR Require CategoryTypeclass.
Require PeanoNat.
Require EqdepFacts Eqdep_dec.

Create HintDb bwdb.
Create HintDb bwarrdb.
Create HintDb monarrdb.

Declare Scope bw_scope.
Delimit Scope bw_scope with bw.

Section Definitions.

#[local] Set Universe Polymorphism.

#[universes(polymorphic=yes)]
Context {X : Type}.

#[universes(polymorphic=yes,cumulative=yes)]
Inductive bw : Type :=
  | e : bw
  | var (x : X) : bw
  | tens (a b : bw) : bw.

Local Notation "a '⨂' b" := (tens a b) 
  (at level 40, left associativity). (* \bigotimes *)

#[universes(polymorphic=yes,cumulative=yes)]
Inductive bweq : bw -> bw -> Prop :=
  | bw_leftid (a : bw) : bweq (tens e a) a
  | bw_rightid (a : bw) : bweq (tens a e) a 
  | bw_assoc (a b c : bw) : bweq (tens (tens a b) c) (tens a (tens b c))
  | bw_tens (a a' b b' : bw) : bweq a a' -> bweq b b' 
    -> bweq (tens a b) (tens a' b')
  | bw_refl (a : bw) : bweq a a
  | bw_trans (a b c : bw) : bweq a b -> bweq b c -> bweq a c
  | bw_symm (a b : bw) : bweq a b -> bweq b a.

#[universes(polymorphic=yes,cumulative=yes)]
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

Definition Nf (a : bw) : bwnorm := ⟦a⟧ norm_e.

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
  | cons a l' => norm_rtens (varlist_to_bwnorm l') a
  end.

Fixpoint bwnormapp (n m : bwnorm) {struct m} : bwnorm := 
  match m with
  | norm_e => n
  | norm_rtens m' a => norm_rtens (bwnormapp n m') a
  end.

#[universes(polymorphic=yes,cumulative=yes)]
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

Section bwarr.

Local Notation "a '⟶' b" := (bwarr a b) 
  (at level 60) : type_scope. (* \longrightarrow *)

Local Notation "f '○' g" := (arrcomp f g) 
  (at level 59, left associativity). (* \bigcirc *)
Local Notation "f '⊠' g" := (arrtens f g) 
  (at level 40, left associativity). (* \boxtimes *)

Reserved Notation "f '≅' g" (at level 70). (* \cong *)

#[universes(polymorphic=yes,cumulative=yes)]
Inductive bwarrequiv : forall a b, relation (a ⟶ b) :=
  | bwarr_comp {a b c : bw} (f f' : a ⟶ b) (g g' : b ⟶ c) :
      f ≅ f' -> g ≅ g' -> f ○ g ≅ f' ○ g'
  | bwarr_assoc {a a' b' b : bw} (f : a ⟶ a') (g : a' ⟶ b') (h : b' ⟶ b) :
      f ○ g ○ h ≅ f ○ (g ○ h)
  | bwarr_lunit {a b} (f : a ⟶ b) : (arrid a) ○ f ≅ f
  | bwarr_runit {a b} (f : a ⟶ b) : f ○ (arrid b) ≅ f

  | bwarr_tens {a a' b b' : bw} (f f' : a ⟶ a') (g g' : b ⟶ b') :
    f ≅ f' -> g ≅ g' -> arrtens f g ≅ arrtens f' g'
  | bwarr_tens_id {a b : bw} :
    arrid a ⊠ arrid b ≅ arrid (a ⨂ b)
  | bwarr_tens_comp {a b c a' b' c'} 
    (f : a ⟶ b) (g : b ⟶ c) (f' : a' ⟶ b') (g' : b' ⟶ c') :
    (f ○ g) ⊠ (f' ○ g') ≅ 
      f ⊠ f' ○ g ⊠ g'
  
  | bwarr_assoc_rinv (a b c : bw) :
    arrassoc a b c ○ arrinvassoc a b c ≅ arrid (a ⨂ (b ⨂ c))
  | bwarr_assoc_linv (a b c : bw) :
    arrinvassoc a b c ○ arrassoc a b c ≅ arrid (a ⨂ b ⨂ c)

  | bwarr_lunitor_rinv (a : bw) :
    arrlunitor a ○ arrinvlunitor a ≅ arrid (e ⨂ a)
  | bwarr_lunitor_linv (a : bw) :
    arrinvlunitor a ○ arrlunitor a ≅ arrid a

  | bwarr_runitor_rinv (a : bw) :
    arrrunitor a ○ arrinvrunitor a ≅ arrid (a ⨂ e)
  | bwarr_runitor_linv (a : bw) :
    arrinvrunitor a ○ arrrunitor a ≅ arrid a

  | bwarr_assoc_nat {a b c a' b' c' : bw} 
    (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
    arrassoc a b c ○ f ⊠ g ⊠ h
    ≅ f ⊠ (g ⊠ h) ○ arrassoc a' b' c'

  | bwarr_lunitor_nat {a b : bw} (f : a ⟶ b) :
    arrlunitor a ○ f ≅ (arrid e) ⊠ f ○ arrlunitor b
  
  | bwarr_runitor_nat {a b : bw} (f : a ⟶ b) :
    arrrunitor a ○ f ≅ f ⊠ (arrid e) ○ arrrunitor b
  
  | bwarr_pentagon (a b c d : bw) : 
    arrassoc a b (c⨂d) ○ arrassoc (a⨂b) c d
    ≅ arrid a ⊠ arrassoc b c d ○ arrassoc a (b⨂c) d
      ○ arrassoc a b c ⊠ arrid d

  | bwarr_triangle (a b : bw) :
    arrassoc a e b ○ arrrunitor a ⊠ arrid b
    ≅ arrid a ⊠ arrlunitor b
  | bwarr_refl {a b} (f : a ⟶ b) : f ≅ f
  | bwarr_trans {a b} (f g h : a ⟶ b) : f ≅ g -> g ≅ h -> f ≅ h
  | bwarr_symm {a b} (f g : a ⟶ b) : f ≅ g -> g ≅ f
  where "f '≅' g" := (bwarrequiv _ _ f g).

Local Notation "f '≅' g" := (bwarrequiv _ _ f g) (at level 70). (* \cong *)

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

Fixpoint xi_comp_map (n : bwnorm) (A : bw) {struct A} : 
  n ⨂ A ⟶ ⟦A⟧ n :=
  match A with
  | e => arrrunitor n
  | var x => arrid (n ⨂ var x)
  | tens a b => 
    arrassoc n a b ○ xi_comp_map n a ⊠ arrid b
      ○ xi_comp_map (⟦a⟧ n) b
  end. 

Definition to_Nf_arr (a : bw) : bwarr a (Nf a) :=
  (arrinvlunitor a) ○ (xi_comp_map norm_e a).

Definition from_Nf_arr (a : bw) : bwarr (Nf a) a :=
  (bwarrinv (xi_comp_map norm_e a)) ○ (arrlunitor a).

Definition cast_bwarr {n n' m m'} 
  (Hn : n = n') (Hm : m = m') (f : n ⟶ m) : n' ⟶ m'.
rewrite <- Hn, <- Hm.
apply f.
Defined.

Definition bwarr_of_Nf_eq {a b : bw} (H : Nf a = Nf b) : bwarr a b :=
  to_Nf_arr a ○ 
    cast_bwarr eq_refl (f_equal _ H) (arrid (Nf a))
    ○ from_Nf_arr b.

End bwarr.

Section MonoidalCoherence.

Import CategoryTypeclass.

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


Fixpoint realize_bwarr {A B} (h : bwarr A B) : (realize_bw A ~> realize_bw B) :=
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


#[universes(polymorphic=yes,cumulative=yes)]
Inductive monarr : bw -> bw -> Type :=
  | monarrcomp {a b c : bw} (f : monarr a b) (g : monarr b c) : 
      monarr a c
  | monarrtens {a a' b b'} (f : monarr a a') (g : monarr b b') : 
      monarr (a ⨂ b) (a' ⨂ b')
  | mongeneric {a b : bw} (f : cC.(morphism) a b) : 
      monarr a b
  | monarrstruct {a b : bw} (f : bwarr a b) : 
      monarr a b.

Coercion monarrstruct : bwarr >-> monarr.
Local Notation "a '⟶' b" := (monarr a b) (at level 60) : type_scope.

Fixpoint realize_monarr {A B} (h : A ⟶ B) : (realize_bw A ~> realize_bw B) :=
  match h with
  | monarrcomp f g => realize_monarr f ∘ realize_monarr g
  | monarrtens f g => realize_monarr f ⊗ realize_monarr g
  | mongeneric f => f
  | monarrstruct f => realize_bwarr f
  end.

Reserved Notation "f '≊' g" (at level 70).
#[universes(polymorphic=yes,cumulative=yes)]
Inductive monarrequiv : forall a b, relation (a ⟶ b) :=
  | monarr_comp {a b c : bw} (f f' : a ⟶ b) (g g' : b ⟶ c) :
      f ≊ f' -> g ≊ g' -> monarrcomp f g ≊ monarrcomp f' g'
  | monarr_assoc {a a' b' b : bw} (f : a ⟶ a') (g : a' ⟶ b') (h : b' ⟶ b) :
      monarrcomp f (monarrcomp g h) ≊ monarrcomp (monarrcomp f g) h
  | monarr_lunit {a b} (f : a ⟶ b) : monarrcomp (arrid a) f ≊ f
  | monarr_runit {a b} (f : a ⟶ b) : monarrcomp f (arrid b) ≊ f

  | monarr_tens {a a' b b' : bw} (f f' : a ⟶ a') (g g' : b ⟶ b') :
    f ≊ f' -> g ≊ g' -> monarrtens f g ≊ monarrtens f' g'
  | monarr_tens_comp {a b c a' b' c'} 
    (f : a ⟶ b) (g : b ⟶ c) (f' : a' ⟶ b') (g' : b' ⟶ c') :
    monarrtens (monarrcomp f g) (monarrcomp f' g') 
      ≊ monarrcomp (monarrtens f f') (monarrtens g g')
  | monarr_struct {a b} (f g : bwarr a b) : 
    (* bwarrequiv a b f g -> *)  
    (* NOTE: this predicate is given by monoidal coherence! *)
      f ≊ g
  | monarr_arrcomp {a b c} (f : bwarr a b) (g : bwarr b c) :
      monarrcomp f g ≊ arrcomp f g
  | monarr_arrtens {a a' b b'} (f : bwarr a a') (g : bwarr b b') :
      monarrtens f g ≊ arrtens f g

  | monarr_assoc_nat {a b c a' b' c' : bw} 
    (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
    monarrcomp (arrassoc a b c) (monarrtens (monarrtens f g) h)
    ≊ monarrcomp (monarrtens f (monarrtens g h)) (arrassoc a' b' c')
  | monarr_lunitor_nat {a b : bw} (f : a ⟶ b) :
    monarrcomp (arrlunitor a) f ≊ monarrcomp (monarrtens (arrid e) f) (arrlunitor b)
  | monarr_runitor_nat {a b : bw} (f : a ⟶ b) :
    monarrcomp (arrrunitor a) f ≊ monarrcomp (monarrtens f (arrid e)) (arrrunitor b)

  | monarr_refl {a b} (f : a ⟶ b) : f ≊ f
  | monarr_symm {a b} (f g : a ⟶ b) : f ≊ g -> g ≊ f
  | monarr_trans {a b} (f g h : a ⟶ b) : f ≊ g -> g ≊ h -> f ≊ h    
  where "f '≊' g" := (monarrequiv _ _ f g).

End MonoidalCoherence.

End Definitions.

Arguments bw _ : clear implicits.
Arguments bwnorm _ : clear implicits.
#[global] Arguments cast_bwarr {_ _ _ _ _} !_ !_ _ /. 
(* This will simplify only if both casts are constructors, i.e. eq_refl *)

Section ExtraDefinitions.

Fixpoint map_bw {A B} (f : A -> B) (a : bw A) : bw B :=
  match a with
  | e => e
  | var a' => var (f a')
  | tens a' b' => tens (map_bw f a') (map_bw f b')
  end.

Fixpoint map_bwarr {A B} (f : A -> B) {a b} (g : bwarr a b) : 
  bwarr (map_bw f a) (map_bw f b) := 
  match g with
  | arrid a => arrid (map_bw f a)
  | arrassoc a b c => arrassoc (map_bw f a) (map_bw f b) (map_bw f c)
  | arrinvassoc a b c => arrinvassoc (map_bw f a) (map_bw f b) (map_bw f c)
  | arrlunitor a => arrlunitor (map_bw f a)
  | arrinvlunitor a => arrinvlunitor (map_bw f a)
  | arrrunitor a => arrrunitor (map_bw f a)
  | arrinvrunitor a => arrinvrunitor (map_bw f a)
  | arrcomp f' g' => arrcomp (map_bwarr f f') (map_bwarr f g')
  | arrtens f' g' => arrtens (map_bwarr f f') (map_bwarr f g')
  end.

End ExtraDefinitions.

#[export] Hint Constructors bweq : bwdb.
#[export] Hint Constructors bwarr : bwdb.
#[export] Hint Constructors bwarrequiv : bwarrdb.
#[export] Hint Constructors monarrequiv : monarrdb.

Module MC_setoids.

Import CategoryTypeclass.

Definition true_rel {A : Type} : relation A :=
  fun _ _ => True.

#[global] Add Parametric Relation (A : Type) : A true_rel 
  reflexivity proved by ltac:(easy)
  symmetry proved by ltac:(easy)
  transitivity proved by ltac:(easy)
  as true_rel_relation.

#[program, export] Instance subrel_true_rel {A : Type} (R : relation A) :
  subrelation R true_rel.
Next Obligation. easy. Qed.

Add Parametric Relation {X} : (@bw X) bweq 
  reflexivity proved by bw_refl 
  symmetry proved by bw_symm 
  transitivity proved by bw_trans as bweq_setoid.

Add Parametric Relation {X} (a b : @bw X) : (bwarr a b) (bwarrequiv a b)
  reflexivity proved by bwarr_refl
  symmetry proved by bwarr_symm
  transitivity proved by bwarr_trans as bwarrequiv_setoid.

Add Parametric Morphism {X} (a b c : @bw X) : (@arrcomp X a b c)
  with signature 
  (bwarrequiv a b) ==> (bwarrequiv b c) ==> (bwarrequiv a c)
  as arrcomp_mor.
Proof. eauto with bwarrdb. Qed.

Add Parametric Morphism {X} (a a' b b' : @bw X) : (@arrtens X a a' b b')
  with signature 
  (bwarrequiv a a') ==> (bwarrequiv b b') 
  ==> (bwarrequiv (tens a b) (tens a' b'))
  as arrtens_mor.
Proof. eauto with bwarrdb. Qed.

Add Parametric Morphism {A B} (f : A -> B) {a b} : 
  (@map_bwarr A B f a b) with signature
  bwarrequiv a b ==> bwarrequiv (map_bw f a) (map_bw f b)
  as map_bwarr_mor.
Proof.
  intros g h H.
  induction H; simpl; try constructor;
  eauto 3 with bwarrdb.
Qed.


Add Parametric Relation {X} {cC : Category X} {mC : MonoidalCategory cC}
  (a b : @bw X) : (monarr a b) (monarrequiv a b)
  reflexivity proved by monarr_refl
  symmetry proved by monarr_symm
  transitivity proved by monarr_trans as monarrequiv_setoid.

Add Parametric Morphism {X} {cC : Category X} {mC : MonoidalCategory cC}
  (a b c : @bw X) : (@monarrcomp _ _ _ a b c)
  with signature 
  (monarrequiv a b) ==> (monarrequiv b c) ==> (monarrequiv a c)
  as monarrcomp_mor.
Proof. eauto with monarrdb. Qed.

Add Parametric Morphism {X} {cC : Category X} {mC : MonoidalCategory cC}
  (a a' b b' : @bw X) : (@monarrtens _ _ _ a a' b b')
  with signature 
  (monarrequiv a a') ==> (monarrequiv b b') 
  ==> (monarrequiv (tens a b) (tens a' b'))
  as monarrtens_mor.
Proof. eauto with monarrdb. Qed.

Add Parametric Morphism {X} {cC : Category X} {mC : MonoidalCategory cC}
  (a b : @bw X) : (@monarrstruct X cC mC a b)
  with signature true_rel ==> monarrequiv a b
  as monarrstruct_mor.
Proof. eauto with monarrdb. Qed.

End MC_setoids.

Module MC_notations.

Notation "a '⨂' b" := (tens a b) 
  (at level 40, left associativity) : bw_scope. (* \bigotimes *)
Notation "a '~' b" := (bweq a b) (at level 70) : bw_scope.
Notation "'⟦' a '⟧'" := (bwbrac a) : bw_scope. (* \llbracket , \rrbracket *)

Notation "f '≅' g" := (bwarrequiv _ _ f g) 
  (at level 70) : bw_scope. (* \cong *)

Notation "f '○' g" := (arrcomp f g) 
  (at level 59, left associativity) : bw_scope. (* \bigcirc *)
Notation "f '⊠' g" := (arrtens f g) 
  (at level 40, left associativity) : bw_scope. (* \boxtimes *)

Notation "f '^-'" := (bwarrinv f) (at level 9) : bw_scope.

Module bwarr_notation.
Notation "a '⟶' b" := (bwarr a b) 
  (at level 60) : type_scope. (* \longrightarrow *)
End bwarr_notation.



Module monarr_notation.
Notation "a '⟶' b" := (monarr a b) 
  (at level 60) : type_scope. (* \longrightarrow *)
End monarr_notation.


Notation "f '≊' g" := (monarrequiv _ _ f g) 
  (at level 70) : bw_scope.

Notation "f ⧆ g" := (monarrtens f g) 
  (at level 40, left associativity) : bw_scope. (* \boxast *)
Notation "f ◌ g" := (monarrcomp f g) 
  (at level 50, left associativity) : bw_scope. (* \dottedcircle *)
  

End MC_notations.

Module MCClasses.

(* Computing forms of proj1 and proj2, for UIP proofs *)
Definition proj1' {A B} (H : A /\ B) : A :=
  match H with 
  | conj PA PB => PA
  end.

Definition proj2' {A B} (H : A /\ B) : B :=
  match H with 
  | conj PA PB => PB
  end.

#[universes(polymorphic=yes,cumulative=yes)]
Class DECEQ (X : Type) := {
  deceq : forall x y : X, {x = y} + {x <> y}
}.

#[universes(polymorphic=yes,cumulative=yes)]
Class UIP (X : Type) := {
  uip : forall {x y : X} (H H' : x = y), H = H'
}.

#[universes(polymorphic=yes,cumulative=yes)]
Class UIP_refl (X : Type) := {
  uip_refl : forall {x : X} (H : x = x), H = eq_refl
}.

Lemma UIP_iff_UIP_refl (X : Type) : 
  UIP X <-> UIP_refl X.
Proof.
  split.
  - intros H; constructor; intros; apply uip.
  - intros H; constructor.
    intros x y e0.
    case e0.
    symmetry.
    apply uip_refl.
Defined.

#[universes(polymorphic=yes,cumulative=yes)]
Class EQ_RECT_EQ (X : Type) := {
  eq_rect_eq : forall (x : X) (P : X -> Type) (a : P x) (h : x = x),
    eq_rect x P a x h = a
}.

#[universes(polymorphic=yes,cumulative=yes)]
Class EQ_REC_EQ (X : Type) := {
  eq_rec_eq : forall (x : X) (P : X -> Set) (a : P x) (h : x = x),
    eq_rec x P a x h = a
}.

End MCClasses.

Section MCClasses_instances.

Import MCClasses.


#[universes(polymorphic=yes),
  export] Instance DECEQ_UIP {X : Type} (H : DECEQ X) : UIP X := {
  uip := Eqdep_dec.UIP_dec deceq
}.

#[universes(polymorphic=yes),
  export, program] Instance UIP_EQ_RECT_EQ {X : Type} (H : UIP X) 
  : EQ_RECT_EQ X := {}.
Next Obligation.
  symmetry.
  apply EqdepFacts.Streicher_K__eq_rect_eq.
  apply EqdepFacts.UIP_refl__Streicher_K.
  intros ? ?.
  apply uip.
Qed.

#[universes(polymorphic=yes),
  export] Instance EQ_RECT_EQ_EQ_REC_EQ {X} (H : EQ_RECT_EQ X) 
  : EQ_REC_EQ X := {
  eq_rec_eq := eq_rect_eq
}.

#[universes(polymorphic=yes),
  export] Instance DECEQ_nat : DECEQ nat := {
  deceq := PeanoNat.Nat.eq_dec
}.

#[universes(polymorphic=yes),
  export] Instance DECEQ_bool : DECEQ bool := {
  deceq := Bool.bool_dec
}.

End MCClasses_instances.