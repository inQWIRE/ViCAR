Require Import Setoid.
(* From VyZX Require Import PermutationFacts PermutationRules. *)
From ViCaR Require Import CategoryTypeclassCompatibility CategoryAutomationCompatibility.
Require Logic.Eqdep_dec.
Require Import CatExample (FunctorCategory).
Require Import FunctionalExtensionality.
Require Import Psatz.

Require Import MonoidalCoherence.

Require Import Arith ZArith.
Require List.

Section BraidGroup.

Import List ListNotations.

(* 
I believe it may actually be easier to implement the 
infinite braid group than the finite one. This may
not be true when it comes to interpreting a braid
in the strict adjacent symmetric monoidal category.
We'll see.
*)
Local Open Scope list_scope.
Local Open Scope Z_scope.

Local Notation braid := (list Z).

Inductive braideq : relation braid :=
  | braid_refl (a : braid) : a ≃ a
  | braid_symm {a b : braid} : 
      a ≃ b -> b ≃ a
  | braid_trans {a b c : braid} : 
      a ≃ b -> b ≃ c -> a ≃ c
  | braid_cons {a b : braid} (n : Z) : 
      a ≃ b -> (n :: a) ≃ (n :: b)
  | braid_comm (n : Z) (k : nat) {l} : 
      ((Z.of_nat k + 2 + n) :: n :: l) ≃ (n :: (Z.of_nat k + 2 + n) :: l)
  | braid_swap (n : Z) {l} : 
      (n :: (1+n) :: n :: l) ≃ ((1+n) :: n :: (1+n) :: l)
  | braid_cancel (n : Z) {l} : (-n) :: n :: l ≃ l
  | braid_id {l} : 0 :: l ≃ l
  where "a ≃ b" := (braideq a b).

Local Notation "a ≃ b" := (braideq a b).

Local Ltac braidauto := eauto 4 using braideq.
Local Ltac braidauto' := eauto 2 using braideq.

Lemma braideq_equiv : equivalence braid braideq.
Proof.
  split; hnf; braidauto.
Qed.

Add Parametric Relation : braid braideq
  reflexivity proved by braid_refl
  symmetry proved by (fun _ _ => braid_symm)
  transitivity proved by (fun _ _ _ => braid_trans)
  as braideq_setoid.

Lemma braideq_preapp (l a b : list Z) : a ≃ b -> l ++ a ≃ l ++ b.
Proof.
  intros; induction l; braidauto.
Qed.

Lemma braideq_postapp (a b l : list Z) : a ≃ b -> a ++ l ≃ b ++ l.
Proof.
  intros H; induction H; braidauto.
Qed.

Lemma braideq_app (a b l m : list Z) : a ≃ b -> l ≃ m -> a ++ l ≃ b ++ m.
Proof.
  intros H H'.
  transitivity (a ++ m).
  - now apply braideq_preapp.
  - now apply braideq_postapp.
Qed.

Add Parametric Morphism : (@app Z)
  with signature braideq ==> braideq ==> braideq
  as braideq_app_mor.
Proof.
  intros; now apply braideq_app.
Qed.

Definition braidinv (b : braid) := map Z.opp (rev b).
(* Arguments braidinv b. *)

Local Notation "b ^-1" := (braidinv b) (at level 25).

Lemma braid_cancel' (n : Z) (b : braid) : 
  n :: (-n) :: b ≃ b.
Proof.
  rewrite <- Z.opp_involutive at 1.
  apply braid_cancel.
Qed.

Lemma braidinv_linv (b : braid) : b^-1 ++ b ≃ nil.
Proof.
  induction b; [braidauto|].
  unfold braidinv; simpl.
  rewrite map_app, <- app_assoc.
  change (a :: b) with ([a] ++ b).
  rewrite (app_assoc _ _ b).
  simpl.
  now rewrite braid_cancel.
Qed.

Lemma braidinv_rinv (b : braid) : b ++ b^-1 ≃ nil.
Proof.
  induction b using rev_ind; [braidauto|].
  unfold braidinv; simpl.
  rewrite rev_app_distr, map_app, app_assoc, <- (app_assoc _ [x]).
  simpl.
  rewrite braid_cancel'.
  now rewrite app_nil_r.
Qed.

#[export] Instance braid_cat : Category True := {
  morphism := fun _ _ => braid;
  c_equiv := fun _ _ => braideq;
  compose := fun _ _ _ => @app _;
  c_identity := fun _ => [];
}.

#[export, program] Instance braid_cath : 
  CategoryCoherence braid_cat := {
  c_equiv_rel := fun _ _ => braideq_equiv;
  compose_compat := fun _ _ _ f g H h i => braideq_app f g h i H;
  left_unit := fun _ _ => braid_refl;
}.
Next Obligation.
  now rewrite app_assoc.
Qed.
Next Obligation.
  now rewrite app_nil_r.
Qed.

(* TODO: Fix universe issues and uncomment: 
#[export, program] Instance braid_groupoid : IsGroupoid braid_cat := {
  groupoid_inv := fun _ _ => braidinv;
}.
Next Obligation.
  now rewrite braidinv_linv, braidinv_rinv.
Qed. *)

End BraidGroup.


Section NormalBraids.

Variable (X : Type).

Arguments norm_rtens {_}.
Arguments norm_e {_}.

Inductive bwbarr : bwnorm X -> bwnorm X -> Type :=
  | barrcomp {a b c : bwnorm X} 
      (f : bwbarr a b) (g : bwbarr b c) : bwbarr a c
  | barrid (a : bwnorm X) : bwbarr a a
  | barrtensidr {a b : bwnorm X} (f : bwbarr a b) (x : X) :
      bwbarr (norm_rtens a x) (norm_rtens b x)
  | barrbraid (a : bwnorm X) (x y : X) 
    : bwbarr (norm_rtens (norm_rtens a x) y) 
      (norm_rtens (norm_rtens a y) x)
  | barrinvbraid (a : bwnorm X) (x y : X) 
    : bwbarr (norm_rtens (norm_rtens a y) x) 
      (norm_rtens (norm_rtens a x) y).

Inductive bwbarrequiv : forall a b : bwnorm X, 
  relation (bwbarr a b) := 
  | bwbarr_refl {a b} (f : bwbarr a b) : f ≃ f
  | bwbarr_symm {a b} (f g : bwbarr a b) : f ≃ g -> g ≃ f
  | bwbarr_trans {a b} (f g h : bwbarr a b) : 
    f ≃ g -> g ≃ h -> f ≃ h
  | bwbarr_comp {a b c} (f f' : bwbarr a b) (g g' : bwbarr b c) : 
    f ≃ f' -> g ≃ g' -> barrcomp f g ≃ barrcomp f' g'
  | bwbarr_tensidr {a b} (f f' : bwbarr a b) (x : X) :
    f ≃ f' -> barrtensidr f x ≃ barrtensidr f' x
  | bwbarr_lunit {a b} (f : bwbarr a b) :
    barrcomp (barrid a) f ≃ f
  | bwbarr_runit {a b} (f : bwbarr a b) :
    barrcomp f (barrid b) ≃ f
  | bwbarr_tens_id_idr (a : bwnorm X) (x : X) :
    barrtensidr (barrid a) x ≃ barrid (norm_rtens a x)
  | bwbarr_braid_linv a x y : 
    barrcomp (barrinvbraid a x y) (barrbraid a x y)
    ≃ barrid (norm_rtens (norm_rtens a y) x)
  | bwbarr_braid_rinv a x y : 
    barrcomp (barrbraid a x y) (barrinvbraid a x y)
    ≃ barrid (norm_rtens (norm_rtens a x) y)
  where "f ≃ g" := (bwbarrequiv _ _ f g).

#[export] Instance bwbcat : Category (bwnorm X) := {
  morphism := bwbarr;
  c_equiv := bwbarrequiv;
  compose := @barrcomp;
  c_identity := barrid;
}.
(* TODO: Try to make comp work for strictification?
Local Notation comp f g := (fun x => g (f x)).

Definition compassoc {A B C D} (f : A -> B) (g : B -> C) (h : C -> D) :
  comp (comp f g) h = comp f (comp g h) := eq_refl. *)
(* TODO: Try to do a setoid-based category over bw with bweq? *)


#[export, program] Instance bwbcath : CategoryCoherence bwbcat.
Solve All Obligations with (hnf; eauto using bwbarrequiv).

Fixpoint bwnormapp (a b : bwnorm X) {struct b} : bwnorm X := 
  match b with
  | norm_e => a
  | norm_rtens b' x => match a with
    | norm_e => norm_rtens b' x
    | a => norm_rtens (bwnormapp a b') x
    end
  end.
  (* match a with
  | norm_e => b
  | a => match b with
    | norm_e => a
    | norm_rtens b' x => norm_rtens (bwnormapp a b') x
    end
  end. *)
  (* match a, b with
  | norm_e, norm_e => norm_e
  | norm_e, b => b
  | a, norm_e => a
  | a, norm_rtens b' x => norm_rtens (bwnormapp a b') x
  end. *)
(* Arguments bwnormapp _ _ : simpl nomatch. *)

Lemma bwnorm_match_id (b : bwnorm X) :
  match b with |norm_e => norm_e | norm_rtens _ _ => b end = b.
Proof. 
  now destruct b.
Qed.

Lemma bwnormapp_assoc (a b c : bwnorm X) : 
  bwnormapp a (bwnormapp b c) = bwnormapp (bwnormapp a b) c.
Proof.
  induction c; simpl; rewrite ?bwnorm_match_id.
  - easy.
  - rewrite <- IHc.
    now destruct a, b, c.
Qed.

Definition bwbassoc (a b c : bwnorm X) : 
  bwbarr (bwnormapp (bwnormapp a b) c) (bwnormapp a (bwnormapp b c)).
rewrite <- bwnormapp_assoc.
apply barrid.
Defined.

Definition bwbinvassoc (a b c : bwnorm X) : 
  bwbarr (bwnormapp a (bwnormapp b c)) (bwnormapp (bwnormapp a b) c).
rewrite <- bwnormapp_assoc.
apply barrid.
Defined.

Lemma bwnormapp_norm_e_l (a : bwnorm X) : bwnormapp norm_e a = a.
Proof.
  destruct a; reflexivity.
Qed.

Definition bwbleftunitor (a : bwnorm X) : 
  bwbarr (bwnormapp norm_e a) a :=
  match a as b return (bwbarr (bwnormapp norm_e b) b) with
  | norm_e => barrid norm_e
  | norm_rtens n x => barrid (norm_rtens n x)
  end.

Definition bwbinvleftunitor (a : bwnorm X) : 
  bwbarr a (bwnormapp norm_e a) := 
  match a as b return (bwbarr b (bwnormapp norm_e b)) with
  | norm_e => barrid norm_e
  | norm_rtens n x => barrid (norm_rtens n x)
  end.

Definition bwbrightunitor (a : bwnorm X) :
  bwbarr (bwnormapp a norm_e) a := barrid a.

Definition bwbinvrightunitor (a : bwnorm X) :
  bwbarr a (bwnormapp a norm_e) := barrid a.

Definition barrtensid_many {a b : bwnorm X} (f : bwbarr a b) 
  (c : bwnorm X) : bwbarr (bwnormapp a c) (bwnormapp b c).
revert a b f; induction c; intros a b f.
- apply f.
- destruct a, b; apply barrtensidr; destruct c; apply (IHc _ _ f).
Defined.

Definition bwbarrapp {a a' b b' : bwnorm X} 
  (f : bwbarr a a') (g : bwbarr b b') : 
  bwbarr (bwnormapp a b) (bwnormapp a' b').
revert a a' f; induction g; eauto using bwbarr.
- intros; apply (barrtensid_many f).
- intros. destruct a0, a', a, b; apply barrtensidr; apply (IHg _ _ f).
- intros. do 2 try destruct a0; do 2 try destruct a'; 
  try apply barrbraid.
  simpl.



#[export, program] Instance bwbmcat : MonoidalCategory bwbcat := {
  tensor_obj
}


Section Preliminary.

Section N_Functors.

Local Open Scope Cat_scope.

Fixpoint T_fold_l (n : nat) (f : Type -> Type -> Type) 
  (C D : Type) : Type :=
  match n with 
  | O => D
  | S n' => f C (T_fold_l n' f C D)
  end.

Definition Obj_n (n : nat) (C D : Type) : Type :=
  T_fold_l n (fun T U => T -> U) C D.

Fixpoint Mor_n {n : nat} {C D : Type} `{cC : Category C} `{cD : Category D}
  (Fo : Obj_n n C D) (Fp : Obj_n n C D) {struct n}: Type.
Proof.
  destruct n.
  - exact (Fo ~> Fp).
  - exact (forall A B : C, A ~> B -> 
  Mor_n n C D cC cD (Fo A) (Fp B)).
Defined. 

Fixpoint n_id_map {n} {C D : Type} `{cC : Category C} `{cD : Category D}
  (Fo : Obj_n n C D) (Fm : Mor_n Fo Fo) {struct n} : Prop.
Proof.
  destruct n.
  - exact (Fm ≃ id_ Fo).
  - exact (forall A : C, 
    n_id_map n C D cC cD (Fo A) (Fm A A (id_ A))).
Defined.

Fixpoint n_compose_map {n} {C D : Type} `{cC : Category C} `{cD : Category D}
  (Fo Fp Fq : Obj_n n C D)
  (Fm : Mor_n Fo Fq) (Fm' : Mor_n Fo Fp) (Fm'' : Mor_n Fp Fq)
  {struct n}: Prop.
Proof.
  destruct n.
  - exact (Fm ≃ Fm' ∘ Fm'').
  - exact (forall {A B M : C} (f : A ~> B) (g : B ~> M),
    n_compose_map n C D cC cD (Fo A) (Fp B) (Fq M) 
    (Fm A M (f ∘ g)) (Fm' A B f) (Fm'' B M g)).
Defined.

Fixpoint n_map_compat {n} {C D : Type} `{cC : Category C} `{cD : Category D} 
  (Fo Fp : Obj_n n C D) (Fm Fn : Mor_n Fo Fp) 
  {struct n}: Prop.
Proof.
  destruct n.
  - exact (Fm ≃ Fn).
  - exact (forall {A B : C} (f f': A ~> B),
    f ≃ f' ->
    n_map_compat n C D cC cD (Fo A) (Fp B) (Fm A B f) (Fn A B f')).
Defined.

Class Nary_Functor (n : nat) {C D : Type} 
(cC : Category C) (cD : Category D) := {
  obj_nmap : Obj_n n C D;
  morphism_nmap : Mor_n obj_nmap obj_nmap;
  id_nmap : n_id_map obj_nmap morphism_nmap;
  compose_nmap : 
    n_compose_map obj_nmap obj_nmap obj_nmap 
      morphism_nmap morphism_nmap morphism_nmap;
  compat_nmap : 
    n_map_compat obj_nmap obj_nmap morphism_nmap morphism_nmap;
}.
Coercion obj_nmap : Nary_Functor >-> Obj_n.
Coercion morphism_nmap : Nary_Functor >-> Mor_n.


Lemma id_morphism_of_0ary_functor {C D : Type} 
  `{cC : Category C} `{cD : Category D}
  (F : Nary_Functor 0 cC cD) : 
  F.(morphism_nmap) ≃ id_ F.(obj_nmap).
Proof.
  apply F.(id_nmap).
Qed.

Definition Functor_of_Unary_Functor {C D : Type} 
  `{cC : Category C} `{cD : Category D} (F : Nary_Functor 1 cC cD) 
  : Functor cC cD := {|
  obj_map := F.(obj_nmap);
  morphism_map := F.(morphism_nmap);
  id_map := F.(id_nmap);
  compose_map := F.(compose_nmap);
  morphism_compat := F.(compat_nmap);
|}.

Definition Unary_Functor_of_Functor {C D : Type} 
  `{cC : Category C} `{cD : Category D} (F : Functor cC cD)
   : Nary_Functor 1 cC cD. refine ({|
  obj_nmap := F.(obj_map) : Obj_n 1 C D;
  morphism_nmap := (fun A B => F.(morphism_map) (A:=A) (B:=B)) : @Mor_n 1 C D cC cD _ _;
  id_nmap := F.(id_map) |}).
Proof.
  - intros ? *. apply F.(compose_map).
  - intros ? *. apply F.(morphism_compat).
Defined.

Definition Bifunctor_of_Binary_Functor {C D : Type} 
  `{cC : Category C} `{cD : Category D} (F : Nary_Functor 2 cC cD) 
  : Bifunctor cC cC cD := {|
  obj_bimap := F.(obj_nmap);
  morphism_bimap := fun A1 B1 A2 B2 f => 
    F.(morphism_nmap) A1 B1 f A2 B2;
  id_bimap := F.(id_nmap);
  compose_bimap := fun A1 B1 M1 A2 B2 M2 f g => 
    F.(compose_nmap) A1 B1 M1 f g A2 B2 M2;
  morphism_bicompat := fun A1 B1 A2 B2 f f' g g' Hf => 
    F.(compat_nmap) A1 B1 f f' Hf A2 B2 g g';
|}.

Definition Binary_Functor_of_Bifunctor {C D : Type} 
  `{cC : Category C} `{cD : Category D} (F : Bifunctor cC cC cD) 
  : Nary_Functor 2 cC cD := {|
  obj_nmap := F.(obj_bimap) : Obj_n 2 C D;
  morphism_nmap := fun A1 B1 f A2 B2 => 
    F.(morphism_bimap) f;
  id_nmap := fun A1 A2 => F.(id_bimap) A1 A2;
  compose_nmap := fun A1 B1 M1 f g A2 B2 M2 => 
    F.(compose_bimap) f g;
  compat_nmap := fun A1 B1 f f' Hf A2 B2 g g' => 
    F.(morphism_bicompat) f f' g g' Hf;
|}.

(* Coercion Binary_Functor_of_Bifunctor : Bifunctor >-> Nary_Functor. *)

Fixpoint n_component_map {n : nat} {C D} 
  `{cC : Category C} `{cD : Category D}
  (Fo Go : Obj_n n C D) {struct n} : Type.
Proof.
  destruct n.
  - exact (Fo ~> Go).
  - exact (forall A, 
      @n_component_map n C D cC cD (Fo A) (Go A)).
Defined.

Fixpoint n_component_map_natural {n : nat} {C D}
  `{cC : Category C} `{cD : Category D}
  (Fo Fp Go Gp : Obj_n n C D) (Fm : Mor_n Fo Fp) (Gm : Mor_n Go Gp)
  (alphao : n_component_map Fo Go) (alphap : n_component_map Fp Gp)
   {struct n} : Type.
Proof.
  destruct n.
  - exact (Fm ∘ alphap ≃ alphao ∘ Gm).
  - exact (forall A B (f : A ~> B),
    n_component_map_natural n C D cC cD (Fo A) (Fp B) (Go A) (Gp B)
    (Fm A B f) (Gm A B f) (alphao A) (alphap B)).
Defined.

Class Nary_NaturalTransformation {n : nat} {C D}
  `{cC : Category C} `{cD : Category D}
  (F G : Nary_Functor n cC cD) := {
  component_nmap : n_component_map F G;
  component_nmap_natural :
    n_component_map_natural F F G G F G component_nmap component_nmap;
}.

Definition NaturalTransformation_of_Unary_NaturalTransformation {C D : Type} 
  `{cC : Category C} `{cD : Category D} (F G : Nary_Functor 1 cC cD)
  (T : Nary_NaturalTransformation F G) :
  NaturalTransformation 
    (Functor_of_Unary_Functor F) (Functor_of_Unary_Functor G).
  apply Build_NaturalTransformation with T.(component_nmap).
  apply T.(component_nmap_natural).
Defined.

Definition Unary_NaturalTransformation_of_NaturalTransformation {C D : Type} 
  `{cC : Category C} `{cD : Category D} (F G : Functor cC cD)
  (T : NaturalTransformation F G) :
  Nary_NaturalTransformation 
    (Unary_Functor_of_Functor F) (Unary_Functor_of_Functor G).
apply Build_Nary_NaturalTransformation with T.(component_map).
intros ? *; apply T.(component_map_natural).
Defined.

Fixpoint n_component_iso {n : nat} {C D} 
  `{cC : Category C} `{cD : Category D}
  (Fo Go : Obj_n n C D) {struct n} : Type.
Proof.
  destruct n.
  - exact (Fo <~> Go).
  - exact (forall A, 
      @n_component_iso n C D cC cD (Fo A) (Go A)).
Defined.

Fixpoint n_component_iso_natural {n : nat} {C D}
  `{cC : Category C} `{cD : Category D}
  (Fo Fp Go Gp : Obj_n n C D) (Fm : Mor_n Fo Fp) (Gm : Mor_n Go Gp)
  (alphao : n_component_iso Fo Go) (alphap : n_component_iso Fp Gp)
   {struct n} : Type.
Proof.
  destruct n.
  - exact (Fm ∘ alphap ≃ alphao ∘ Gm).
  - exact (forall A B (f : A ~> B),
    n_component_iso_natural n C D cC cD (Fo A) (Fp B) (Go A) (Gp B)
    (Fm A B f) (Gm A B f) (alphao A) (alphap B)).
Defined.

Class Nary_NaturalIsomorphism {n : nat} {C D}
  `{cC : Category C} `{cD : Category D}
  (F G : Nary_Functor n cC cD) := {
  component_niso : n_component_iso F G;
  component_niso_natural :
    n_component_iso_natural F F G G F G component_niso component_niso;
}.
Coercion component_niso : Nary_NaturalIsomorphism >-> n_component_iso.

Definition NaturalIsomorphism_of_Unary_NaturalIsomorphism {C D : Type} 
  `{cC : Category C} `{cD : Category D} (F G : Nary_Functor 1 cC cD)
  (T : Nary_NaturalIsomorphism F G) :
  NaturalIsomorphism 
    (Functor_of_Unary_Functor F) (Functor_of_Unary_Functor G).
  apply Build_NaturalIsomorphism with T.(component_niso).
  apply T.(component_niso_natural).
Defined.

Definition Unary_NaturalIsomorphism_of_NaturalIsomorphism {C D : Type} 
  `{cC : Category C} `{cD : Category D} (F G : Functor cC cD)
  (T : NaturalIsomorphism F G) :
  Nary_NaturalIsomorphism
    (Unary_Functor_of_Functor F) (Unary_Functor_of_Functor G).
apply Build_Nary_NaturalIsomorphism with T.(component_iso).
intros ? *; apply T.(component_iso_natural).
Defined.

Fixpoint precompose_Obj_n {n m} {C D} 
  (Fo : Obj_n n C C) (Go : Obj_n (S m) C D) {struct n} :
  Obj_n (n + m) C D.
Proof.
  destruct n.
  - exact (Go Fo).
  - exact (fun A =>
    precompose_Obj_n n m C D (Fo A) Go).
Defined.

Fixpoint precompose_Mor_n {n m} {C D} `{cC : Category C} `{cD : Category D}
  {Fo Fp : Obj_n n C C} (Fm : Mor_n Fo Fp)
  {Go Gp : Obj_n (S m) C D} (Gm : Mor_n Go Gp) {struct n} : 
  Mor_n (precompose_Obj_n Fo Go) (precompose_Obj_n Fp Gp).
Proof.
  destruct n.
  - exact (Gm Fo Fp Fm).
  - exact (fun A B f =>
    precompose_Mor_n n m C D cC cD
    (Fo A) (Fp B) (Fm A B f) Go Gp Gm).
Defined.


(* Fixpoint relation_n {n} {C D} (RC : relation C) (RD : relation D) :
  relation (Obj_n n C D) :=
  match n with  *)

(* Fixpoint relation_n {n} {C D} {RC} {RD} 
  (eC : equivalence C RC) (eD : equivalence D RD)  *)

(* Fixpoint Obj_n_ptwise {n} {C D} {struct n} : relation (Obj_n n C D) :=
  match n with 
  | O => fun Fo Go => Fo = Go
  | S n' => fun Fo Go A B (H : A = ) *)

Fixpoint Mor_n_ptwise {n} {C D} `{cC : Category C} `{cD : Category D} 
  (Fo Fp : Obj_n n C D) {struct n} : relation (Mor_n Fo Fp).
Proof.
  destruct n.
  - exact (fun Fm Gm => Fm ≃ Gm).
  - exact (fun Fm Gm => forall A B (f : A ~> B),
  Mor_n_ptwise n C D cC cD (Fo A) (Fp B) (Fm A B f) (Gm A B f)).
Defined.

Lemma Mor_n_ptwise_refl {n} {C D} `{cC : Category C} `{cD : Category D} 
  {cDh : CategoryCoherence cD}
  {Fo Fp : Obj_n n C D} : forall Fm, Mor_n_ptwise Fo Fp Fm Fm.
Proof.
  induction n.
  - easy.
  - intros Fm A B f.
    apply IHn.
Qed.

Lemma Mor_n_ptwise_trans {n} {C D} `{cC : Category C} `{cD : Category D} 
  {cDh : CategoryCoherence cD}
  {Fo Fp : Obj_n n C D} : forall Fa Fb Fc, 
  Mor_n_ptwise Fo Fp Fa Fb -> Mor_n_ptwise Fo Fp Fb Fc ->
  Mor_n_ptwise Fo Fp Fa Fc.
Proof.
  induction n.
  - simpl. intros; etransitivity; eassumption.
  - intros Fa Fb Fc Hab Hbc A B f.
    eapply IHn.
    apply (Hab A B f).
    apply (Hbc A B f).
Qed.

Lemma Mor_n_ptwise_sym {n} {C D} `{cC : Category C} `{cD : Category D} 
  {cDh : CategoryCoherence cD}
  {Fo Fp : Obj_n n C D} : forall Fa Fb, 
  Mor_n_ptwise Fo Fp Fa Fb -> Mor_n_ptwise Fo Fp Fb Fa.
Proof.
  induction n.
  - easy.
  - intros Fa Fb Hab A B f.
    apply IHn, Hab.
Qed.



Add Parametric Relation {n} {C D} `{cC : Category C} `{cD : Category D} 
  {cDh : CategoryCoherence cD}
  {Fo Fp : Obj_n n C D} : (Mor_n Fo Fp) (Mor_n_ptwise Fo Fp)
  reflexivity proved by Mor_n_ptwise_refl
  symmetry proved by Mor_n_ptwise_sym
  transitivity proved by Mor_n_ptwise_trans
  as mor_n_equiv_rel.

Add Parametric Morphism {n} {C D} `{cC : Category C} `{cD : Category D} 
  {cDh : CategoryCoherence cD}
  {Fo : Obj_n n C D} : (@n_id_map n C D cC cD Fo)
  with signature
  (Mor_n_ptwise Fo Fo) ==> iff
  as n_id_map_mor_n_equiv_morphism.
Proof.
  induction n.
  - simpl. 
    intros x y Hxy.
    rewrite Hxy.
    easy.
  - simpl.
    intros Fn Fm Hnm.
    split; intros H A.
    + rewrite IHn.
      apply H.
      symmetry.
      apply Hnm.
    + rewrite IHn.
      apply H.
      apply Hnm.
Qed.

Lemma mor_n_ptwise_of_compat {n} {C D} `{cC : Category C} `{cD : Category D} 
  {cCh : CategoryCoherence cC}
  (Fo Fp : Obj_n n C D) (Fm Fn : Mor_n Fo Fp) 
  (Hcompat : n_map_compat Fo Fp Fm Fn) : 
  Mor_n_ptwise Fo Fp Fm Fn.
  (* forall A B f g (H : f ≃ g),
  Mor_n_ptwise (Fo A) (Fp B) (Fm A B f) (Fm A B g). *)
Proof.
  induction n.
  - apply Hcompat; easy.
  - intros A B f.
    apply IHn.
    apply Hcompat.
    easy.
Qed.

Lemma n_map_compat_rec {n} {C D} `{cC : Category C} `{cD : Category D} 
  (Fo Fp : Obj_n (S n) C D) (Fm : Mor_n Fo Fp) 
  (Hcompat : n_map_compat Fo Fp Fm Fm) : 
  forall A B f g (H : f ≃ g),
  n_map_compat (Fo A) (Fp B) (Fm A B f) (Fm A B g).
Proof.
  intros.
  apply Hcompat; easy.
Qed.


Lemma mor_n_ptwise_ind {n} {C D} `{cC : Category C} `{cD : Category D} 
  {cCh : CategoryCoherence cC}
  (Fo Fp : Obj_n (S n) C D) (Fm : Mor_n Fo Fp) 
  (Hcompat : n_map_compat Fo Fp Fm Fm) : 
  forall A B f g (H : f ≃ g),
  Mor_n_ptwise (Fo A) (Fp B) (Fm A B f) (Fm A B g).
Proof.
  intros.
  apply mor_n_ptwise_of_compat.
  apply n_map_compat_rec; easy.
Qed.

Add Parametric Morphism {n} {C D} `{cC : Category C} `{cD : Category D} 
  {cCh : CategoryCoherence cC}
  {Fo : Obj_n (S n) C D} {Fm : Mor_n Fo Fo} 
  (Hcompat : n_map_compat Fo Fo Fm Fm) {A B : C} : (Fm A B)
  with signature 
  cC.(c_equiv) ==> Mor_n_ptwise (Fo A) (Fo B)
  as compat_mor_n_mor_n_morphism.
Proof.
  apply mor_n_ptwise_ind.
  apply Hcompat.
Qed.

Add Parametric Morphism {n} {C D} `{cC : Category C} `{cD : Category D} 
  {cCh : CategoryCoherence cC}
  {F : Nary_Functor (S n) cC cD} {A B : C} : (F.(morphism_nmap) A B)
  with signature 
  cC.(c_equiv) ==> Mor_n_ptwise (F.(obj_nmap) A) (F.(obj_nmap) B)
  as nary_functor_mor_n_morphism.
Proof.
  apply mor_n_ptwise_ind, F.(compat_nmap).
Qed.

Lemma precompose_n_id_map {n m} {C D} `{cC : Category C} `{cD : Category D}
  {cCh : CategoryCoherence cC} {cDh : CategoryCoherence cD}
  (Fo : Obj_n n C C) (Fm : Mor_n Fo Fo) (HFid : n_id_map Fo Fm)
  (Go : Obj_n (S m) C D) (Gm : Mor_n Go Go) (HGid : n_id_map Go Gm) 
  (HGcompat : n_map_compat Go Go Gm Gm) :
  n_id_map (precompose_Obj_n Fo Go) (precompose_Mor_n Fm Gm).
Proof.
  induction n.
  - simpl.
    simpl in HFid.
    rewrite compat_mor_n_mor_n_morphism.
    + apply HGid.
    + assumption.
    + apply HGcompat.
    + apply HFid.
  - simpl.
    intros A.
    apply IHn, HFid.
Qed.


Local Notation n_map_compat' Fo Fm := 
  (n_map_compat Fo Fo Fm Fm).
Local Notation n_compose_map' Fo Fm := 
  (n_compose_map Fo Fo Fo Fm Fm Fm).

Add Parametric Morphism {n} {C D} `{cC : Category C} `{cD : Category D} 
  {cDh : CategoryCoherence cD}
  (Fo Fp Fq : Obj_n n C D) :
  (@n_compose_map n C D cC cD Fo Fp Fq) with signature
  (Mor_n_ptwise Fo Fq) ==> (Mor_n_ptwise Fo Fp) ==> (Mor_n_ptwise Fp Fq)
  ==> iff
  as n_compose_map_mor_n_morphism.
Proof.
  intros Foq Foq' HFoq Fop Fop' HFop Fpq Fpq' HFpq.
  induction n.
  - simpl. rewrite HFop, HFpq, HFoq.
    easy.
  - split; intros H.
    + intros A B M f g.
      rewrite <- IHn.
      * apply H.
      * apply HFoq.
      * apply HFop.
      * apply HFpq.
    + intros A B M f g.
      rewrite IHn.
      * apply H.
      * apply HFoq.
      * apply HFop.
      * apply HFpq.
Qed.


(* Add Parametric Morphism {n} {C D} `{cC : Category C} `{cD : Category D} 
  (Fo Fp Fq : Obj_n (S n) C D) 
  (Fm : Mor_n Fo Fq) (Fm' : Mor_n Fo Fp) (Fm'' : Mor_n Fp Fq) 
  (Hm Hn : n_map_compat Fo Fq Fm Fm)
  (Hm' : n_map_compat Fo Fp Fm' Fm')
  (Hm'' : n_map_compat Fp Fq Fm'' Fm'') (A B M : C) :
  (*(fun (A B M : C) => (* fun f g h => *)  *)
   ((fun (g : A ~> B) (h : B ~> M) => 
    @n_compose_map n C D cC cD (Fo A) (Fp B) (Fq M) 
      (Fm A M ( g∘ h)) (Fm' A B g) (Fm'' B M h))) with signature
  (* eq ==> eq ==> eq ==> *) (* cC.(equiv) ==> *) cC.(equiv) ==> cC.(equiv) ==> iff
  as n_compose_map_equiv_morphism.
Proof. *)

Add Parametric Morphism {n} {C D} `{cC : Category C} `{cD : Category D} 
  {cCh : CategoryCoherence cC} {cDh : CategoryCoherence cD}
  (Fo Fp Fq : Obj_n (S n) C D) 
  (Fm : Mor_n Fo Fq) (Fm' : Mor_n Fo Fp) (Fm'' : Mor_n Fp Fq) 
  (Hm : n_map_compat Fo Fq Fm Fm)
  (Hm' : n_map_compat Fo Fp Fm' Fm')
  (Hm'' : n_map_compat Fp Fq Fm'' Fm'') (A B M : C) :
  (*(fun (A B M : C) => (* fun f g h => *)  *)
   ((fun (f : A ~> M) (g : A ~> B) (h : B ~> M) => 
    @n_compose_map n C D cC cD (Fo A) (Fp B) (Fq M) 
      (Fm A M f) (Fm' A B g) (Fm'' B M h))) with signature
  (* eq ==> eq ==> eq ==> *) cC.(c_equiv) ==> cC.(c_equiv) ==> cC.(c_equiv) ==> iff
  as n_compose_map_equiv_morphism.
Proof.
  (* revert A B M. *)
  intros f f' Hf g g' Hg h h' Hh.
  split; intros H;
   (rewrite n_compose_map_mor_n_morphism; auto;
    [apply H | | | ];
    apply mor_n_ptwise_of_compat;
    [apply Hm | apply Hm' | apply Hm'']; easy).
Qed.

Add Parametric Morphism {n} {C D} `{cC : Category C} `{cD : Category D} 
  {cCh : CategoryCoherence cC} {cDh : CategoryCoherence cD}
  (F : Nary_Functor (S n) cC cD) (A B M : C) :
  (*(fun (A B M : C) => (* fun f g h => *)  *)
  (fun (f : A ~> M) (g : A ~> B) (h : B ~> M) => 
  @n_compose_map n C D cC cD (F.(obj_nmap) A) (F.(obj_nmap) B) (F.(obj_nmap) M) 
  (F.(morphism_nmap) A M f) (F.(morphism_nmap) A B g) (F.(morphism_nmap) B M h))
    with signature
  (* eq ==> eq ==> eq ==> *) cC.(c_equiv) ==> cC.(c_equiv) ==> cC.(c_equiv) ==> iff
  as n_compose_map_functor_equiv_morphism.
Proof.
  apply n_compose_map_equiv_morphism; auto;
  apply F.(compat_nmap).
Qed.

 


Lemma n_compose_map_ind {n} {C D} `{cC : Category C} `{cD : Category D}
  (Fo : Obj_n (S n) C C) (Fm : Mor_n Fo Fo) 
  (HFid : n_id_map Fo Fm) (HFcomp : n_compose_map' Fo Fm) (A B M : C) f g : 
  n_compose_map (Fo A) (Fo B) (Fo M) (Fm A M (f ∘ g)) (Fm A B f) (Fm B M g).
Proof.
  apply HFcomp.
Qed.

Lemma n_compose_map_id {n} {C D} `{cC : Category C} `{cD : Category D}
  {cCh : CategoryCoherence cC}
  (Fo : Obj_n (S n) C C) (Fm : Mor_n Fo Fo) 
  (* (HFid : n_id_map Fo Fm)  *)
  (HFcompat : n_map_compat' Fo Fm)
  (HFcomp : n_compose_map' Fo Fm) (A : C) : 
  n_compose_map' (Fo A) (Fm A A (id_ A)).
Proof.
  simpl in HFcomp.
  rewrite n_compose_map_mor_n_morphism.
  apply (HFcomp A A A (id_ A) (id_ A)).
  all: try easy.
  simpl in HFcompat.
  apply mor_n_ptwise_of_compat.
  apply HFcompat.
  rewrite left_unit. 
  easy.
Qed.



Lemma precompose_n_compose_map_gen {n m} {C D} `{cC : Category C} `{cD : Category D}
  {cCh : CategoryCoherence cC} {cDh : CategoryCoherence cD}
  (Fo Fp Fq : Obj_n n C C) 
  (Fm : Mor_n Fo Fq) (Fm' : Mor_n Fo Fp) (Fm'' : Mor_n Fp Fq)
  (Go Gp Gq : Obj_n (S m) C D) 
  (Gm : Mor_n Go Gq) (Gm' : Mor_n Go Gp) (Gm'' : Mor_n Gp Gq)
  (HFcompat : n_map_compat Fo Fq Fm Fm)
  (HFcompat' : n_map_compat Fo Fp Fm' Fm')
  (HFcompat'' : n_map_compat Fp Fq Fm'' Fm'')
  (HGcompat : n_map_compat Go Gq Gm Gm)
  (HGcompat' : n_map_compat Go Gp Gm' Gm')
  (HGcompat'' : n_map_compat Gp Gq Gm'' Gm'')
  (HFcomp : n_compose_map Fo Fp Fq Fm Fm' Fm'')
  (HGcomp : n_compose_map Go Gp Gq Gm Gm' Gm'') :
  n_compose_map 
    (precompose_Obj_n Fo Go) (precompose_Obj_n Fp Gp) (precompose_Obj_n Fq Gq)
    (precompose_Mor_n Fm Gm) (precompose_Mor_n Fm' Gm') (precompose_Mor_n Fm'' Gm'').
Proof.
  induction n.
  - simpl in *.
    rewrite n_compose_map_mor_n_morphism; auto;
    apply mor_n_ptwise_of_compat;
    [ apply HGcompat, HFcomp | apply HGcompat' | apply HGcompat''];
    easy.
  - intros A B M f g.
    apply IHn;
    [apply HFcompat | apply HFcompat' | apply HFcompat'' | ]; easy.
Qed.

Lemma precompose_n_map_compat_gen {n m} {C D} `{cC : Category C} `{cD : Category D}
  (* {cCh : CategoryCoherence cC} {cDh : CategoryCoherence cD} *)
  (Fo Fp : Obj_n n C C) 
  (Fm Fm' : Mor_n Fo Fp) (* (Fm' : Mor_n Fo Fp) (Fm'' : Mor_n Fp Fq) *)
  (Go Gp : Obj_n (S m) C D) 
  (Gm Gm' : Mor_n Go Gp) (* (Gm' : Mor_n Go Gp) (Gm'' : Mor_n Gp Gq) *)
  (HFcompat : n_map_compat Fo Fp Fm Fm')
  (* (HFcompat' : n_map_compat Fo Fp Fm' Fm') *)
  (* (HFcompat'' : n_map_compat Fp Fq Fm'' Fm'') *)
  (HGcompat : n_map_compat Go Gp Gm Gm')
  (* (HGcompat' : n_map_compat Go Gp Gm' Gm') *)
  (* (HGcompat'' : n_map_compat Gp Gq Gm'' Gm'') *) :
  n_map_compat (precompose_Obj_n Fo Go) (precompose_Obj_n Fp Gp)
    (precompose_Mor_n Fm Gm) (precompose_Mor_n Fm' Gm').
Proof.
  induction n.
  - simpl.
    apply HGcompat, HFcompat.
  - intros A B f f' Hf.
    apply IHn, HFcompat, Hf.
Qed.

Definition PreCompose_Nary_Functor {n m} {C D}
  `{cC : Category C} `{cD : Category D}
  {cCh : CategoryCoherence cC} {cDh : CategoryCoherence cD}
  (F : Nary_Functor n cC cC) (G : Nary_Functor (S m) cC cD) :
  Nary_Functor (n + m) cC cD.
refine {|
  obj_nmap := precompose_Obj_n F G;
  morphism_nmap := precompose_Mor_n F.(morphism_nmap) G.(morphism_nmap);
|}.
Proof.
  - apply precompose_n_id_map.
    + apply F.(id_nmap).
    + apply G.(id_nmap).
    + apply G.(compat_nmap).
  - apply (precompose_n_compose_map_gen 
      F F F F F F G G G G G G
      compat_nmap compat_nmap compat_nmap compat_nmap compat_nmap compat_nmap
      compose_nmap compose_nmap).
  - apply precompose_n_map_compat_gen;
    [apply F.(compat_nmap) | apply G.(compat_nmap)].
Defined.

Fixpoint precompose_drop_Obj_n {n k m} {C D} 
  (Fo : Obj_n n C C) (Go : Obj_n (k + S m) C D) {struct k} :
  Obj_n (k + n + m) C D.
Proof.
  destruct k.
  - exact (precompose_Obj_n Fo Go).
  - exact (fun A =>
    precompose_drop_Obj_n n k m C D Fo (Go A)).
Defined.

Fixpoint precompose_drop_Mor_n {n k m} {C D} 
  `{cC : Category C} `{cD : Category D}
  {Fo Fp : Obj_n n C C} (Fm : Mor_n Fo Fp)
  {Go Gp : Obj_n (k + S m) C D} (Gm : Mor_n Go Gp) {struct k} : 
  Mor_n (precompose_drop_Obj_n Fo Go) (precompose_drop_Obj_n Fp Gp).
Proof.
  destruct k.
  - exact (precompose_Mor_n Fm Gm).
  - exact (fun A B f =>
    precompose_drop_Mor_n n k m C D cC cD
    Fo Fp Fm (Go A) (Gp B) (Gm A B f)).
Defined.

Lemma precompose_drop_n_id_map {n k m} {C D} 
  `{cC : Category C} `{cD : Category D}
  {cCh : CategoryCoherence cC} {cDh : CategoryCoherence cD}
  (Fo : Obj_n n C C) (Fm : Mor_n Fo Fo) (HFid : n_id_map Fo Fm)
  (Go : Obj_n (k + S m) C D) (Gm : Mor_n Go Go) (HGid : n_id_map Go Gm) 
  (HGcompat : n_map_compat Go Go Gm Gm) :
  n_id_map (precompose_drop_Obj_n Fo Go) (precompose_drop_Mor_n Fm Gm).
Proof.
  induction k.
  - apply precompose_n_id_map; easy.
  - intros A.
    apply IHk.
    + apply HGid. 
    + apply HGcompat; easy.
Qed.

Lemma precompose_drop_n_compose_map_gen {n k m} {C D} 
  `{cC : Category C} `{cD : Category D}
  {cCh : CategoryCoherence cC} {cDh : CategoryCoherence cD}
  (Fo Fp Fq : Obj_n n C C) 
  (Fm : Mor_n Fo Fq) (Fm' : Mor_n Fo Fp) (Fm'' : Mor_n Fp Fq)
  (Go Gp Gq : Obj_n (k + S m) C D) 
  (Gm : Mor_n Go Gq) (Gm' : Mor_n Go Gp) (Gm'' : Mor_n Gp Gq)
  (HFcompat : n_map_compat Fo Fq Fm Fm)
  (HFcompat' : n_map_compat Fo Fp Fm' Fm')
  (HFcompat'' : n_map_compat Fp Fq Fm'' Fm'')
  (HGcompat : n_map_compat Go Gq Gm Gm)
  (HGcompat' : n_map_compat Go Gp Gm' Gm')
  (HGcompat'' : n_map_compat Gp Gq Gm'' Gm'')
  (HFcomp : n_compose_map Fo Fp Fq Fm Fm' Fm'')
  (HGcomp : n_compose_map Go Gp Gq Gm Gm' Gm'') :
  n_compose_map 
    (precompose_drop_Obj_n Fo Go) 
    (precompose_drop_Obj_n Fp Gp)
    (precompose_drop_Obj_n Fq Gq)
    (precompose_drop_Mor_n Fm Gm)
    (precompose_drop_Mor_n Fm' Gm')
    (precompose_drop_Mor_n Fm'' Gm'').
Proof.
  induction k.
  - apply precompose_n_compose_map_gen; easy.
  - intros A B M f g.
    apply IHk;
    [apply HGcompat | apply HGcompat' | apply HGcompat'' |]; easy.
Qed.

Lemma precompose_drop_n_map_compat_gen {n k m} {C D}
 `{cC : Category C} `{cD : Category D}
  (Fo Fp : Obj_n n C C) 
  (Fm Fm' : Mor_n Fo Fp) (* (Fm' : Mor_n Fo Fp) (Fm'' : Mor_n Fp Fq) *)
  (Go Gp : Obj_n (k + S m) C D) 
  (Gm Gm' : Mor_n Go Gp) (* (Gm' : Mor_n Go Gp) (Gm'' : Mor_n Gp Gq) *)
  (HFcompat : n_map_compat Fo Fp Fm Fm')
  (HGcompat : n_map_compat Go Gp Gm Gm') :
  n_map_compat (precompose_drop_Obj_n Fo Go) (precompose_drop_Obj_n Fp Gp)
    (precompose_drop_Mor_n Fm Gm) (precompose_drop_Mor_n Fm' Gm').
Proof.
  induction k.
  - apply precompose_n_map_compat_gen; easy. 
  - intros A B f f' Hf.
    apply IHk, HGcompat, Hf.
Qed.

Definition PreCompose_drop_Nary_Functor {n m} (k : nat) {C D}
  `{cC : Category C} `{cD : Category D}
  {cCh : CategoryCoherence cC} {cDh : CategoryCoherence cD}
  (F : Nary_Functor n cC cC) (G : Nary_Functor (k + S m) cC cD) :
  Nary_Functor (k + n + m) cC cD.
refine {|
  obj_nmap := precompose_drop_Obj_n F G;
  morphism_nmap := precompose_drop_Mor_n F.(morphism_nmap) G.(morphism_nmap);
|}.
Proof.
  - apply precompose_drop_n_id_map.
    + apply F.(id_nmap).
    + apply G.(id_nmap).
    + apply G.(compat_nmap).
  - apply (precompose_drop_n_compose_map_gen 
      F F F F F F G G G G G G
      compat_nmap compat_nmap compat_nmap compat_nmap compat_nmap compat_nmap
      compose_nmap compose_nmap).
  - apply precompose_drop_n_map_compat_gen; apply compat_nmap.
Defined. 


End N_Functors.









Require Import Coq.Vectors.Vector.

Section NCategory.


Section VectorExtras.

Local Notation "[ ]" := (nil _) (format "[ ]").
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

(* Copied (and modified) from VectorDef: *)
Definition rect3 {A B C} (P:forall {n}, t A n -> t B n -> t C n -> Type)
  (bas : P [] [] []) (rect : forall {n v1 v2 v3}, @P n v1 v2 v3 ->
    forall a b c, P (a :: v1) (b :: v2) (c :: v3)) : forall {n} v1 v2 v3, @P n v1 v2 v3 :=
  fix rect3_fix {n} (v1 : t A n) : forall (v2 : t B n) (v3 : t C n), P v1 v2 v3 :=
  match v1 with
  | [] => fun v2 => case0 _ (fun v3 => case0 _ bas v3) v2
  | @cons _ h1 n' t1 => fun v2 =>
    caseS' v2 (fun v2' => forall v3, P (h1::t1) v2' v3) 
      (fun h2 t2 => 
      (fun v3 => caseS' v3 (fun v3' => P (h1::t1) (h2::t2) v3') 
        (fun h3 t3 => rect (rect3_fix t1 t2 t3) h1 h2 h3)))
  end.

Definition rect4 {A B C D} 
  (P:forall {n}, t A n -> t B n -> t C n -> t D n -> Type) (bas : P [] [] [] []) 
  (rect : forall {n v1 v2 v3 v4}, @P n v1 v2 v3 v4 ->
     forall a b c d, P (a :: v1) (b :: v2) (c :: v3) (d :: v4)) : 
    forall {n} v1 v2 v3 v4, @P n v1 v2 v3 v4 :=
  fix rect4_fix {n} (v1 : t A n) 
    : forall (v2 : t B n) (v3 : t C n) (v4 : t D n), P v1 v2 v3 v4 :=
  match v1 with
  | [] => fun v2 => case0 _ (fun v3 => case0 _ (fun v4 => case0 _ bas v4) v3) v2
  | @cons _ h1 n' t1 => fun v2 =>
    caseS' v2 (fun v2' => forall v3 v4, P (h1::t1) v2' v3 v4) 
      (fun h2 t2 => 
      (fun v3 => caseS' v3 (fun v3' => forall v4, P (h1::t1) (h2::t2) v3' v4) 
        (fun h3 t3 => 
        (fun v4 => caseS' v4 (fun v4' => P (h1::t1) (h2::t2) (h3::t3) v4')
          (fun h4 t4 => rect (rect4_fix t1 t2 t3 t4) h1 h2 h3 h4)))))
  end.

Definition rect6 {A B C D E F} 
  (P:forall {n}, t A n -> t B n -> t C n -> t D n -> t E n -> t F n -> Type) 
  (bas : P [] [] [] [] [] []) 
  (rect : forall {n v1 v2 v3 v4 v5 v6}, @P n v1 v2 v3 v4 v5 v6->
     forall a b c d e f, 
      P (a :: v1) (b :: v2) (c :: v3) (d :: v4) (e :: v5) (f :: v6)) : 
    forall {n} v1 v2 v3 v4 v5 v6, @P n v1 v2 v3 v4 v5 v6 :=
  fix rect6_fix {n} (v1 : t A n) 
    : forall (v2 : t B n) (v3 : t C n) (v4 : t D n) (v5 : t E n) (v6 : t F n), 
      P v1 v2 v3 v4 v5 v6 :=
  match v1 with
  | [] => fun v2 => case0 _ (fun v3 => case0 _ (fun v4 => 
      case0 _ (fun v5 => case0 _ (fun v6 => case0 _ bas v6) v5) v4) v3) v2
  | @cons _ h1 n' t1 => fun v2 =>
    caseS' v2 (fun v2' => forall v3 v4 v5 v6, P (h1::t1) v2' v3 v4 v5 v6) 
      (fun h2 t2 => 
      (fun v3 => caseS' v3 (fun v3' => forall v4 v5 v6, P (h1::t1) (h2::t2) v3' v4 v5 v6) 
      (fun h3 t3 => 
      (fun v4 => caseS' v4 (fun v4' => forall v5 v6, P (h1::t1) (h2::t2) (h3::t3) v4' v5 v6)
      (fun h4 t4 =>
      (fun v5 => caseS' v5 (fun v5' => forall v6, P (h1::t1) (h2::t2) (h3::t3) (h4::t4) v5' v6)
      (fun h5 t5 =>
      (fun v6 => caseS' v6 (fun v6' => P (h1::t1) (h2::t2) (h3::t3) (h4::t4) (h5::t5) v6')
          (fun h6 t6 => rect (rect6_fix t1 t2 t3 t4 t5 t6) h1 h2 h3 h4 h5 h6)))))))))
  end.

Class perm (n : nat) : Type := {
  function : Fin.t n -> Fin.t n;
  invfunction : Fin.t n -> Fin.t n;
  perm_linv : forall (i : Fin.t n), invfunction (function i) = i;
  perm_rinv : forall (i : Fin.t n), function (invfunction i) = i;
}.

Coercion function : perm >-> Funclass.

Fixpoint iota0 (n : nat) : t (Fin.t n) n :=
  match n with
  | O => nil _
  | S n' => cons _ (Fin.F1) n' (map Fin.FS (iota0 n'))
  end.

Lemma nth_iota0 {n : nat} (i : Fin.t n) : nth (iota0 n) i = i.
Proof.
  induction i.
  - easy.
  - simpl.
    erewrite nth_map by reflexivity.
    now rewrite IHi.
Qed.

Definition perm_vec {A : Type} {n} (f : Fin.t n -> Fin.t n) (v : t A n) : t A n :=
  VectorDef.map (fun i => nth v (f i)) (iota0 n).

Lemma perm_vec_comp {A} {n} (f g : Fin.t n -> Fin.t n) (v : t A n) :
  perm_vec (fun i => f (g i)) v = perm_vec g (perm_vec f v).
Proof.
  unfold perm_vec.
  apply eq_nth_iff; intros; subst.
  (* change map with VectorDef.map. *)
  erewrite !nth_map by reflexivity.
  rewrite !nth_iota0.
  easy.
Qed.




(* Fixpoint T_fold_l (n : nat) (f : Type -> Type -> Type) 
  (C D : Type) : Type :=
  match n with 
  | O => D
  | S n' => f C (T_fold_l n' f C D)
  end.

Definition Obj_n (n : nat) (C D : Type) : Type :=
  T_fold_l n (fun T U => T -> U) C D. 
*)

Definition App_n (n : nat) {A B} (P : Obj_n n A B) (a : A) : B.
induction n.
- apply P.
- apply (IHn (P a)).
Defined.

Definition Forall_n (n : nat) {A} (P : Obj_n n A Type) : Type.
induction n.
- exact P.
- exact (forall (a : A), IHn (P a)).
Defined.

Definition Comp_n {n m : nat} {A B C} (P : Obj_n n A B) (Q : Obj_n m B C) :
  Obj_n n A (Obj_n m B C).
induction n.
- exact Q. 
- exact (fun a => IHn (P a)).
Defined.

Definition Precomp_func_n (n : nat) {A B C} (f : A -> B) 
  (P : Obj_n n B C) : Obj_n n A C.
Proof.
  induction n.
  - apply P.
  - exact (fun a => IHn (P (f a))).
Defined.

(* Definition rect_tk {A} (k : nat) 
  (P : forall {n}, forall (v : t (t A n) k), Type) (bas : P (const [] k)) 
  (rect : forall {n} (v : t (t A n) k), P v ->
    forall (ts : t A k), P (map2 (fun a v => cons A a n v) ts v)) :
    forall {n} (v : t (t A n) k), P v.
Proof.
  induction k.
  - simpl in *. 
    induction n. 
    + apply case0, bas.
    + apply rect, IHn. 
*)


(* Definition rectk {A} (k : nat) 
  (P : forall {n}, Obj_n k (t A n) Type) (bas : App_n k P []) 
  (rect : forall {n}, Forall_n (Precomp_n () (@P (S n)))):= 0. *)


End VectorExtras.


Section NCatDefn.

Context {C : Type} (cC : Category C) {cCh : CategoryCoherence cC}.

Local Open Scope Cat_scope.

Definition nmor : forall {n : nat} (A B : t C n), Type :=
  fun _ => rect2 (fun n A B => Type) True (fun n A B ind a b =>
    prod (cC.(morphism) a b) ind).

Definition nmor_equiv (n : nat) := rect2 (n:=n) (fun n A B => 
  relation (nmor A B)) 
  (fun _ _ => True) 
  (fun n A B ind a b fS gS => let (f, fs) := fS in let (g, gs) := gS in
    (f ≃ g /\ ind fs gs)).

Definition nmor_compose (n : nat) := rect3 (n:=n) (fun n A B C => 
  (nmor A B) -> (nmor B C) -> (nmor A C)) 
  (fun f g => Logic.I)
  (fun n A B C ind a b c fS gS => let (f, fs) := fS in let (g, gs) := gS in
    (f ∘ g, ind fs gs)).

Definition nmor_id (n : nat) := t_rect _ (fun n A => nmor A A) Logic.I 
  (fun a n A idA => (id_ a, idA)) n.

#[export, program] Instance NprodCategory (n : nat) : Category (t C n) := {
  morphism := nmor;
  c_equiv := nmor_equiv n;
  compose := nmor_compose n;
  c_identity := nmor_id n;
}.

#[export, program] Instance NprodCategoryCoherence (n : nat) : 
  CategoryCoherence (NprodCategory n) := {
  c_equiv_rel := rect2 (fun n A B => equivalence (A ~> B) (c_equiv _)) _ _;
  compose_compat := rect3 (fun n A B C => forall (f g : A ~> B), f ≃ g -> 
    forall (h j : B ~> C), h ≃ j -> f ∘ h ≃ g ∘ j) _ _;
  assoc := rect4 (fun n A B M N => forall (f : A ~> B) (g : B ~> M) (h : M ~> N),
  f ∘ g ∘ h ≃ f ∘ (g ∘ h)) (fun f g h => Logic.I) _;
  left_unit := rect2 (fun n A B => forall (f : A ~> B), id_ A ∘ f ≃ f) _ _;
  right_unit := rect2 (fun n A B => forall (f : A ~> B), f ∘ id_ B ≃ f) _ _;
}.
Next Obligation. easy. Qed.
Next Obligation. 
  split.
  - intros [f fs]; split; [apply cCh | apply H].
  - intros [f fs] [g gs] [h hs] [Hfg Hfsgs] [Hgh Hgshs]; split; 
    [apply cCh with g | apply H.(equiv_trans _ _) with gs]; easy.
  - intros [f fs] [g gs] [Hfg Hfsgs]; split;
    [symmetry | apply H.(equiv_sym _ _)]; easy.
Qed.
Next Obligation.
  split; [apply compose_compat; easy|].
  apply H; easy.
Qed.
Next Obligation.
  split; [apply assoc | apply H].
Qed.
Next Obligation.
  split; [apply left_unit | apply H].
Qed.
Next Obligation.
  split; [apply right_unit | apply H].
Qed.


Context {mC : MonoidalCategory cC} {mCh : MonoidalCategoryCoherence mC}.

Notation ntens := (map2 mC.(obj_tensor)).

Definition nmor_tens (n : nat) := rect4 (n:=n) (fun n A1 B1 A2 B2 => 
  nmor A1 B1 -> nmor A2 B2 -> nmor (ntens A1 A2) (ntens B1 B2)) 
  (fun f g => Logic.I)
  (fun n A1 B1 A2 B2 ind a1 b1 a2 b2 => 
  fun fS gS => let (f, fs) := fS in let (g, gs) := gS in 
    (f ⧆ g, ind fs gs)).

#[export, program] Instance NprodMonoidalCategory (n : nat) : 
  MonoidalCategory (NprodCategory n) := {
  obj_tensor := ntens;
  mor_tensor := nmor_tens n;
  mon_I := const mC.(mon_I) n;
}.
Next Obligation.
  induction n, A, B, M using rect3.
  - exists Logic.I Logic.I; easy.
  - exists (forward (associator a b c), forward IHM1) 
    ((associator a b c)⁻¹, reverse IHM1).
    repeat split; try apply associator; apply IHM1.
Defined.
Next Obligation.
  induction A.
  - apply IdentityIsomorphism.
  - exists (forward (left_unitor h), forward IHA) 
      (reverse (left_unitor h), reverse IHA).
      repeat split; try apply left_unitor; apply IHA.
Defined.
Next Obligation.
  induction A.
  - apply IdentityIsomorphism.
  - exists (forward (right_unitor h), forward IHA) 
      (reverse (right_unitor h), reverse IHA).
      repeat split; try apply right_unitor; apply IHA.
Defined.

#[export, program] Instance NprodMonoidalCategoryCoherence (n : nat) : 
  MonoidalCategoryCoherence (NprodMonoidalCategory n) := {
  tensor_id := rect2 (fun n A B => id_ A ⧆ id_ B ≃ id_ (A ∗ B)) _ _;
  tensor_compose := rect6 (fun n A1 B1 M1 A2 B2 M2 => forall
    (f1 : A1 ~> B1) (g1 : B1 ~> M1) (f2 : A2 ~> B2) (g2 : B2 ~> M2),
    (f1 ∘ g1) ⧆ (f2 ∘ g2) ≃ f1 ⧆ f2 ∘ g1 ⧆ g2) _ _;
  tensor_compat := rect4 (fun n A1 B1 A2 B2 => forall (f f' : A1 ~> B1)
    (g g' : A2 ~> B2), f ≃ f' -> g ≃ g' -> f ⧆ g ≃ f' ⧆ g') _ _;
  associator_cohere := rect6 (fun n A B M N P Q => forall
    (f : A ~> B) (g : M ~> N) (h : P ~> Q),
    α_ A, M, P ∘ f ⧆ (g ⧆ h) ≃ f ⧆ g ⧆ h ∘ α_ B, N, Q) _ _;
  left_unitor_cohere := rect2 (fun n A B => forall (f : A ~> B),
    λ_ A ∘ f ≃ id_ catI ⧆ f ∘ λ_ B) _ _;
  right_unitor_cohere := rect2 (fun n A B => forall (f : A ~> B),
    ρ_ A ∘ f ≃ f ⧆ id_ catI ∘ ρ_ B) _ _;
  triangle := rect2 (fun n A B => 
    α_ A, catI, B ∘ id_ A ⧆ λ_ B ≃ ρ_ A ⧆ id_ B) _ _;
  pentagon := rect4 (fun n A B M N => 
    α_ A, B, M ⧆ id_ N ∘ α_ A, B ∗ M, N ∘ id_ A ⧆ α_ B, M, N
    ≃ α_ A ∗ B, M, N ∘ α_ A, B, (M ∗ N)) _ _;
}.
Next Obligation.
  split; [apply tensor_id | apply H].
Qed.
Next Obligation.
  split; [apply tensor_compose | apply H].
Qed.
Next Obligation.
  split; [apply tensor_compat | apply H]; easy.
Qed.
Next Obligation.
  split; [apply associator_cohere | apply H].
Qed.
Next Obligation.
  split; [apply left_unitor_cohere | apply H].
Qed.
Next Obligation.
  split; [apply right_unitor_cohere | apply H].
Qed.
Next Obligation.
  split; [apply triangle | apply H].
Qed.
Next Obligation.
  split; [apply pentagon | apply H].
Qed.

Fixpoint eval_fin_bw {n : nat} (w : MonoidalCoherence.bw (Fin.t n))
  (A : t C n) : C :=
  match w with
  | MonoidalCoherence.e _ => catI
  | MonoidalCoherence.var _ i => VectorDef.nth A i
  | MonoidalCoherence.tens _ a' b' => (eval_fin_bw a' A) ∗ (eval_fin_bw b' A)
  end.

Definition nth_mor {n} : forall {A B : t C n} (f : nmor A B) (i : Fin.t n), 
  VectorDef.nth A i ~> VectorDef.nth B i.
(* revert n. *)
refine (rect2 (fun n A B => nmor A B -> 
  forall i : Fin.t n, VectorDef.nth A i ~> VectorDef.nth B i) _ _); clear n.
- easy.
- intros n A B ind a b [f fs] i.
  apply (Fin.caseS' i).
  + exact f.
  + apply ind, fs.
Defined.

(* Definition nth_mor' {n} : forall {A B : t C n} (f : nmor A B) (i : Fin.t n), 
  VectorDef.nth A i ~> VectorDef.nth B i.
intros A B f i; revert A B f.
induction i.
- intros A B.
  apply (caseS' A), (caseS' B).
  intros a A' b B' [f fs].
  exact f.
- intros A B.
  apply (caseS' A), (caseS' B).
  intros a A' b B' [f fs].
  apply IHi, fs.
Defined. *)

Lemma nth_mor_id {n} (A : t C n) (i : Fin.t n) : 
  cC.(c_equiv) (nth_mor (id_ A) i) (cC.(c_identity) (VectorDef.nth A i)).
Proof.
  induction i; apply (caseS' A); easy.
Qed.

Lemma nth_mor_compose {n} {A B M : t C n}
  (f : nmor A B) (g : nmor B M) (i : Fin.t n):
  cC.(c_equiv) (nth_mor (f ∘ g) i) (nth_mor f i ∘ nth_mor g i). 
Proof.
  revert f g.
  induction i;
  apply (caseS' A), (caseS' B), (caseS' M);
  clear A B M;
  intros a A b B m M [f fs] [g gs];
  [easy | apply IHi].
Qed.

Lemma nth_mor_compat_iff : forall {n} {A B : t C n} (f g : nmor A B),
  f ≃ g <-> forall (i : Fin.t n), 
    (cC.(c_equiv) (nth_mor f i) (nth_mor g i)).
Proof.
  refine (fun m => rect2 (fun n (A : t C n) B => 
    forall (f g : nmor A B), f ≃ g <-> forall (i : Fin.t n), 
    (cC.(c_equiv) (nth_mor f i) (nth_mor g i))) _ _).
  - easy.
  - intros n A B ind a b [f fs] [g gs]; split.
    + intros [Hf Hfs].
      intros i; apply (Fin.caseS' i); [easy | apply ind, Hfs].
    + intros H; split.
      * apply (H Fin.F1).
      * apply ind, (fun i => H (Fin.FS i)).
Qed.

#[export, program] Instance proji_functor {n} (i : Fin.t n) : 
  Functor (NprodCategory n) cC := {
  obj_map := fun A => VectorDef.nth A i;
  morphism_map := fun A B f => nth_mor f i;
  id_map := fun A => @nth_mor_id n A i;
  compose_map := fun A B M f g => @nth_mor_compose n A B M f g i;
  morphism_compat := fun A B f g H => (proj1 (nth_mor_compat_iff f g) H i);
}.

Fixpoint eval_fin_nmor {n : nat} (w : MonoidalCoherence.bw (Fin.t n))
  {A B : t C n} (f : nmor A B) : eval_fin_bw w A ~> eval_fin_bw w B :=
  match w with
  | MonoidalCoherence.e _ => c_identity catI
  | MonoidalCoherence.var _ i => nth_mor f i
  | MonoidalCoherence.tens _ a' b' => (eval_fin_nmor a' f) ⧆ (eval_fin_nmor b' f)
  end.

#[export, program] Instance bw_Fin_functor (n : nat) 
  (w : MonoidalCoherence.bw (Fin.t n)) : Functor (NprodCategory n) cC := {
  obj_map := eval_fin_bw w;
  morphism_map := @eval_fin_nmor n w
}.
Next Obligation.
  induction w; [easy | simpl..].
  - apply nth_mor_id.
  - rewrite IHw1, IHw2.
    apply tensor_id.
Qed.
Next Obligation.
  induction w; [now rewrite left_unit | simpl..].
  - apply nth_mor_compose.
  - rewrite IHw1, IHw2; apply tensor_compose.
Qed.
Next Obligation.
  induction w; [easy | simpl..].
  - apply nth_mor_compat_iff; easy. 
  - now rewrite IHw1, IHw2.
Qed.

Fixpoint eval_fin_finmor {n : nat} (A : t C n) {v w : bw (Fin.t n)} 
  (f : bwarr _ v w) {struct f} : eval_fin_bw v A ~> eval_fin_bw w A := 
  match f with
  | arrid _ a => id_ (eval_fin_bw a A)
  | arrcomp _ f g => (eval_fin_finmor A f) ∘ (eval_fin_finmor A g)
  | arrtens _ f g => (eval_fin_finmor A f) ⧆ (eval_fin_finmor A g)
  | arrassoc _ a b c => reverse (associator _ _ _)
  | arrinvassoc _ a b c => associator _ _ _
  | arrlunitor _ a => left_unitor _
  | arrinvlunitor _ a => reverse (left_unitor _)
  | arrrunitor _ a => right_unitor _
  | arrinvrunitor _ a => reverse (right_unitor _)
  end.


Lemma eval_fin_finmor_compat {n} (A : t C n) {v w : bw (Fin.t n)}
  (f f' : bwarr _ v w) : bwarrequiv _ v w f f' -> 
    eval_fin_finmor A f ≃ eval_fin_finmor A f'.
Proof.
  intros H.
  induction H.
  - easy.
  - etransitivity; eauto.
  - apply compose_compat; auto.
  - symmetry; apply assoc.
  - apply assoc.
  - apply left_unit. 
  - symmetry; apply left_unit. 
  - apply right_unit. 
  - symmetry; apply right_unit. 
  - apply tensor_compat; auto.
  - apply tensor_id.
  - symmetry; apply tensor_id. 
  - apply tensor_compose.
  - symmetry; apply tensor_compose.
  - apply associator. 
  - symmetry; apply associator.
  - apply associator.
  - symmetry; apply associator.
  - apply left_unitor.
  - symmetry; apply left_unitor.
  - apply left_unitor.
  - symmetry; apply left_unitor.
  - apply right_unitor.
  - symmetry; apply right_unitor.
  - apply right_unitor.
  - symmetry; apply right_unitor.
  - apply invassociator_cohere.
  - symmetry; apply invassociator_cohere.
  - apply left_unitor_cohere.
  - symmetry; apply left_unitor_cohere.
  - apply right_unitor_cohere.
  - symmetry; apply right_unitor_cohere.
  - symmetry; apply invpentagon.
  - apply invpentagon.
  - symmetry; apply inv_triangle'.
  - apply inv_triangle'.
Qed.

Add Parametric Morphism {n} (A : t C n) (v w : bw (Fin.t n)): 
  (@eval_fin_finmor n A v w)
  with signature
  (bwarrequiv _ v w) ==> cC.(c_equiv)
  as eval_fin_finmor_mor.
Proof. 
  apply eval_fin_finmor_compat. 
Qed.

Lemma bw_case_fin0 (P : bw (Fin.t 0) -> Type) (base : P (e (Fin.t 0))) 
  (rec : forall (a b : bw (Fin.t 0)), P a -> P b -> P (tens _ a b)) :
  forall a, P a.
Proof.
  intros a.
  induction a; auto; easy.
Qed.

(* TODO: Faithful functor (bw (Fin.t 0)) ==> mC for every mC *)


Lemma eval_fin_finmor_nmor_comm {n : nat} {w1 w2 : bw (Fin.t n)}
  (v1 v2 : t C n) (fw : bwarr _ w1 w2) (fv : nmor v1 v2) :
  eval_fin_finmor v1 fw ∘ eval_fin_nmor w2 fv 
  ≃ eval_fin_nmor w1 fv ∘ eval_fin_finmor v2 fw.
Proof.
  induction fw; simpl.
  - now rewrite assoc, IHfw2, <- assoc, IHfw1, assoc.
  - now rewrite <- tensor_compose, IHfw1, IHfw2, tensor_compose.
  - now rewrite left_unit, right_unit.
  - apply invassociator_cohere.
  - apply associator_cohere.
  - apply left_unitor_cohere.
  - apply invleft_unitor_cohere.
  - apply right_unitor_cohere.
  - apply invright_unitor_cohere.
Qed.

(* Require Import Coq.Program.Equality.

Lemma bwarr_case_e {X : Type} (g : bwarr X (e X) (e X))
  (P : forall (a b : bw X) (f : bwarr X a b), Type)
  (base : P (e X) (e X) (arrid X (e X))) : P (e X) (e X) g.
Proof.
  dependent induction g.
  - 
  remember g as h eqn:Hg.
  induction g.
  admit.*)


(* Lemma bwarr_case_to_e {X : Type} {a : bw X} (g : bwarr X a (e X))
  (P : forall (a b : bw X) (f : bwarr X a b), Type)
  (base : P (e X) (e X) (arrid X (e X))) : P a (e X) g.
Proof.
  revert g P base.
  induction a.
  - intros g. *)

Lemma nmor_case_nil (f : nmor (nil C) (nil C)) 
  (P : forall (f : nmor (nil C) (nil C)), Type)
  (base : P (Logic.I)) : P f.
Proof.
  simpl in f.
  destruct f; easy.
Qed.

Require Import Coq.Program.Equality.

Fixpoint bwsize {X : Type} (a : bw X) : nat :=
  match a with
  | e _ => 0
  | var _ _ => 1
  | tens _ a' b' => bwsize a' + bwsize b'
  end.

Inductive bwempty {X} : bw X -> Prop :=
  | bwempty_e : bwempty (e X)
  | bwempty_tens {a b} : bwempty a -> bwempty b -> bwempty (tens X a b).

Lemma bwsize_eq_of_bweq {X : Type} {a b : bw X} : 
  bweq X a b -> bwsize a = bwsize b.
Proof.
  intros H; induction H; simpl; lia.
Qed.

Lemma bwsize_eq_of_arr {X : Type} {a b : bw X} : 
  bwarr X a b -> bwsize a = bwsize b.
Proof.
  intros; apply bwsize_eq_of_bweq; apply bweq_of_arr; easy.
Qed.

Lemma bwempty_of_size0 {X : Type} (a : bw X) : bwsize a = 0 -> bwempty a.
Proof.
  induction a; [|easy|].
  - constructor.
  - simpl; constructor; [apply IHa1 | apply IHa2]; lia.
Qed.

Lemma bwempty_case {X : Type} (a : bw X) (Ha : bwempty a)
  (P : bw X -> Prop) (base : P (e X)) 
  (rec : forall a b, P a -> P b -> P (tens X a b)) : P a.
Proof.
  induction a.
  - apply base.
  - inversion Ha.
  - inversion Ha; auto. 
Defined.

(* Lemma bwarr_from_e_ind {X : Type} {a} (f : bwarr X (e _) a) 
  (P : forall {a b} (f : bwarr X a b)) 
  (base : P (e X) (e X)) (rec : ):
  exists (g : bwarr _ (e _) a) (h : bwarr _ (e _) b),
    bwarrequiv _ _ _ f (arrcomp _ (arrinvlunitor _ (e _)) (arrtens _ g h)).
Proof.
  assert (H : bwsize (tens (Fin.t 0) a b) = 0)
    by (pose proof (bwsize_eq_of_arr f); easy).
  apply (bwempty_rec _ (bwempty_of_size0 _ H)).
  pattern (tens (Fin.t 0) a b).
  induction f. *)

Lemma bw_fin0_size0 (a : bw (Fin.t 0)) : bwsize a = 0.
Proof.
  induction a; simpl; try lia; inversion x.
Qed.

Lemma bw_fin0_empty (a : bw (Fin.t 0)) : bwempty a.
Proof.
  induction a; try inversion x; constructor; assumption.
Qed.

Lemma bw_Fin_thin {n} {a b : bw (Fin.t n)} (f g : bwarr _ a b) : 
  bwarrequiv _ a b f g.
Proof.
  apply bw_thin, (Fin.eq_dec).
Qed.

Lemma ex_arr_from_e_of_empty {X : Type} (a : bw X) (Ha : bwempty a) :
  exists (f : bwarr X (e X) a), True.
Proof.
  induction Ha.
  - exists (arrid _ _); easy.
  - destruct IHHa1 as [f _], IHHa2 as [g _].
    exists (arrcomp X (arrinvlunitor X (e X)) (arrtens X f g)); easy.
Qed.

Lemma ex_arr_to_e_of_empty {X : Type} (a : bw X) (Ha : bwempty a) :
  exists (f : bwarr X a (e X)), True.
Proof.
  induction Ha.
  - exists (arrid _ _); easy.
  - destruct IHHa1 as [f _], IHHa2 as [g _].
    exists (arrcomp X (arrtens X f g) (arrlunitor X (e X))); easy.
Qed.

Arguments e {_}.
Arguments tens {_}.
Arguments arrcomp {_ _ _ _}.
Arguments arrtens {_ _ _ _ _}.
Arguments arrid {_}.
Arguments arrlunitor {_}.
Arguments arrinvlunitor {_}.
Arguments arrrunitor {_}.
Arguments arrinvrunitor {_}.
Arguments arrassoc {_}.
Arguments bwarrequiv {_}.
Arguments bwarr {_}.

Lemma eval_fin_nmor_nil (b : bw (Fin.t 0)) (J : True): 
  @eval_fin_nmor 0 b (nil C) (nil C) J ≃ id_ _.
Proof.
  induction b; simpl; try inversion x; try easy.
  now rewrite IHb1, IHb2, tensor_id.
Qed.

Lemma eval_fin_nmor_compose {n} (b : bw (Fin.t n)) {A B M : t C n}
  (f : nmor A B) (g : nmor B M) : 
  cC.(c_equiv) (eval_fin_nmor b (f ∘ g)) 
    (eval_fin_nmor b f ∘ eval_fin_nmor b g).
Proof.
  revert f g.
  induction b; intros f g.
  - symmetry; apply left_unit.
  - apply nth_mor_compose.
  - simpl.
    rewrite <- tensor_compose.
    rewrite <- IHb1, <- IHb2.
    easy.
Qed.

Lemma eval_fin_nmor_compat {n} (w : bw (Fin.t n)) {A B : t C n}
  (f g : nmor A B) : f ≃ g -> eval_fin_nmor w f ≃ eval_fin_nmor w g.
Proof.
  revert f g; induction w; intros f g.
  - easy.
  - intros; apply nth_mor_compat_iff; easy.
  - intros H. simpl.
    now rewrite IHw1, IHw2 by (apply H).
Qed.

Add Parametric Morphism {n} (w : bw (Fin.t n)) (A B : t C n) :
  (@eval_fin_nmor n w A B) with signature
  (NprodCategory n).(c_equiv) ==> cC.(c_equiv)
  as eval_fin_nmor_mor.
Proof.
  apply eval_fin_nmor_compat.
Qed.





#[export, program] Instance bw_Fin_bifunctor (n : nat) : 
  Bifunctor (MonoidalCoherence.bwcat (Fin.t n)) (NprodCategory n) cC := {
  obj_bimap := eval_fin_bw;
  morphism_bimap := fun w1 w2 v1 v2 fw fv => 
    eval_fin_finmor v1 fw ∘ eval_fin_nmor w2 fv
}.
Next Obligation.
  rewrite left_unit; induction A1; try easy; simpl.
  - apply nth_mor_id.
  - now rewrite IHA1_1, IHA1_2, tensor_id.
Qed.
Next Obligation.
  (* revert n A1 B1 M1 A2 B2 M2 f1 g1 f2 g2. *)
  revert A1 B1 M1 f1 g1 f2 g2.
  induction n, A2, B2, M2 using rect3.
  - intros.
    rewrite !eval_fin_nmor_nil, !right_unit.
    easy. 
  - intros A B M v w f g. (* [f fs] [g gs]. *)
    epose proof eval_fin_nmor_compose as e;
    simpl in e; rewrite e.
    rewrite assoc, <- (assoc (eval_fin_finmor _ w)).
    rewrite eval_fin_finmor_nmor_comm.
    rewrite !assoc; easy.
Qed.
Next Obligation.
  rewrite H, H0.
  easy.
Qed.

Definition nmor_alt {n : nat} (A B : t C n) : Type := forall i, 
  cC.(morphism) (nth A i) (nth B i).

Definition nmor_to_nmor_alt: forall {n : nat} {A B : t C n}
  (f : nmor A B), nmor_alt A B.
refine( fun _ =>
  rect2 (fun n A B => nmor A B -> nmor_alt A B) 
  (fun f i => match i with end) 
  (fun m A B ind a b fS => 
  let (f, fs) := fS in fun i => _)).
apply (Fin.caseS' i).
exact f.
exact (ind fs).
Defined.

Definition nmor_alt_to_nmor : forall {n : nat} {A B : t C n}
  (f : nmor_alt A B), nmor A B := fun _ =>
  rect2 (fun n A B => nmor_alt A B -> nmor A B) 
  (fun _ => Logic.I)
  (fun m A B ind a b fs_alt => 
    (fs_alt Fin.F1, ind (fun i => fs_alt (Fin.FS i)))).

Lemma nmor_to_nmor_alt_to_nmor {n} {A B : t C n} (f : nmor A B) :
  nmor_alt_to_nmor (nmor_to_nmor_alt f) = f.
Proof.
  revert n A B f.
  refine (fun m => rect2 (fun n A B => forall f : nmor A B, 
  nmor_alt_to_nmor (nmor_to_nmor_alt f) = f
  ) _ _).
  - intros f.
    destruct f.
    easy.
  - intros n A B ind a b [f fs].
    simpl.
    rewrite ind.
    easy.
Qed.

Lemma nmor_alt_to_nmor_to_nmor_alt {n} {A B : t C n} (f : nmor_alt A B) :
  forall i, nmor_to_nmor_alt (nmor_alt_to_nmor f) i = f i.
Proof.
  revert n A B f.
  refine (fun m => rect2 (fun n A B => forall f : nmor_alt A B, 
  forall i, nmor_to_nmor_alt (nmor_alt_to_nmor f) i = f i
  ) _ _).
  - easy.
  - intros n A B ind a b f i.
    apply (Fin.caseS' i).
    + auto.
    + intros j.
      simpl.
      apply ind.
Qed.


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

#[export, program] Instance SubpermNprodFunctor {n} (f : Fin.t n -> Fin.t n) :
  Functor (NprodCategory n) (NprodCategory n) := {
  obj_map := perm_vec f;
  morphism_map := fun A B fs => nmor_alt_to_nmor (
    fun i => nmor_to_nmor_alt fs (f i) )
}.
Next Obligation.
  unfold perm_vec.
  erewrite nth_map, nth_iota0 by reflexivity.
  reflexivity.
Qed.
Next Obligation.
  unfold perm_vec.
  erewrite nth_map, nth_iota0 by reflexivity.
  reflexivity.
Qed.
Next Obligation.
  induction A using t_rect; [easy|].
  split.
  - geneqrect.
    clear IHA.
    generalize dependent (nth (cons C h n A) (f Fin.F1)).

  easy.

  induction n.
  - constructor.
  - 



Section FreeBraidedMonoid_nat.

(* We will define the braid category, the category over nat
  whose morphisms (all automorphisms) are braids. Note we 
  define braids imhomogeneously for convenience, and simply
  prove all dimensions end up equal.
*)

Inductive braid : nat -> nat -> Type :=
  | braid_id (n : nat) : braid n n (* TODO: should this only be a braid 1? *)
  | braid_assoc (n m o : nat) : braid (n + (m + o)) (n + m + o)
  | braid_invassoc (n m o : nat) : braid (n + m + o) (n + (m + o))
  (* TODO: do we want a left unit, even though it's the identity? *)
  | braid_runit (n : nat) : braid (n + 0) n
  | braid_invrunit (n : nat) : braid n (n + 0)
  | braid_braid : braid 2 2
  | braid_invbraid : braid 2 2

  | braid_comp {n m o} (a : braid n m) (b : braid m o) : braid n o
  | braid_stack {n m o p} 
    (a : braid n m) (b : braid o p) : braid (n + o) (m + p).

Lemma bd_discrete {n m} (a : braid n m) : n = m.
Proof.
  induction a; lia.
Qed.

Inductive braid_eq := 
  | bdeq




Inductive bw :=
  | e : bw
  | var (x : nat) : bw
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
  | bw_swap (a b : bw) : bweq (tens a b) (tens b a)
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

Fixpoint bw_list (a : bw) : list nat :=
  match a with
  | e => nil
  | 


Lemma DECEQ
Require Import List.

Fixpoint is_sorted {A : Type} (l : list A) (len : A -> A -> bool) {struct l} : bool :=
  match l with
  | nil => true
  | a::ls => match ls with
    | nil => true
    | b::ls' => len a b
    end && is_sorted ls len
  end.

Definition bwnorm := {xs : list X | is_sorted xs lexb = true}.



Fixpoint bwmax (a : bw) (bot : X) : X :=
  match a with
  | e => bot
  | var x => x
  | tens a' b' => xmax (bwmax a' bot) (bwmax b' bot)
  end.

Fixpoint bw_nondec (a : bw) : bool :=
  match a with
  | e => true
  | var x => true
  | tens a' (var x) => lexb (bwmax a' x) x && bw_nondec a'
  | _ => false
  end.




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

Create HintDb bwarrdb.

Section bwcat_Category.

#[local] Existing Instance bwcat.

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
      partner (α_ realize_bw a, b, c ⁻¹ ⊗ id_ realize_bw d) (α_ realize_bw a, b, c ⊗ id_ realize_bw d).
      rewrite <- tensor_compose, iso_inv_l, right_unit, tensor_id, left_unit.
      cancel_isos.
      now rewrite <- tensor_compose, iso_inv_l, left_unit, tensor_id.
    - symmetry. 
      rewrite <- left_unit, <- assoc.
      rewrite <- 2!compose_iso_r'.
      rewrite !assoc.
      rewrite <- pentagon.
      partner (α_ realize_bw a, b, c ⁻¹ ⊗ id_ realize_bw d) (α_ realize_bw a, b, c ⊗ id_ realize_bw d).
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

Theorem monoidal_coherence' {a b : bw} (f g : a ⟶ b) :
  real_arr f ≃ real_arr g.
Proof.
  apply monoidal_coherence.
Qed.

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