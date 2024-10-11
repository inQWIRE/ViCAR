Require Import Setoid.
Require MCDefinitions UIP_facts MCbw.



Section MonoidalCoherenceConsequences.

Set Universe Polymorphism.

Import CategoryTypeclass MCDefinitions 
  MC_notations MCClasses MC_setoids UIP_facts MCbw.

Context {X : Type} {UIPX : UIP X}.
Context {cC : Category X} {cCh : CategoryCoherence cC} 
  {mC : MonoidalCategory cC} {mCh : MonoidalCategoryCoherence mC}.

Local Notation bw := (bw X).
Local Notation bwnorm := (bwnorm X).

Section bwconsequences.

Import bwarr_notation.

Open Scope bw_scope.

Lemma bwarr_tens_cancel_l_equiv {a b c : bw} (f : a ⨂ b ⟶ a ⨂ c) :
  f ≅ arrid a ⊠ bwarr_tens_cancel_l f.
Proof. apply bw_thin. Qed.

Lemma bwarr_tens_cancel_r_equiv {a b c : bw} (f : b ⨂ a ⟶ c ⨂ a) :
  f ≅ bwarr_tens_cancel_r f ⊠ arrid a.
Proof. apply bw_thin. Qed.

End bwconsequences.

Section MonoidalCoherence.

Local Open Scope Cat_scope.

Local Obligation Tactic := Tactics.program_simpl; simpl; eauto 3 with bwarrdb; try easy.

Local Definition realize_bw' := (@realize_bw X cC mC).

(* Local Coercion realize_bw' : bw >-> X. *)

Local Notation "a '⟶' b" := (@bwarr X a b) 
  (at level 60) : type_scope. (* \longrightarrow *)


#[export, program] Instance RealizationFunctor : 
  Functor bwcat cC := {
  obj_map := realize_bw;
  morphism_map := @realize_bwarr X cC mC;
}.
Next Obligation.
  induction H; simpl; 
    rewrite ?iso_inv_l, ?iso_inv_r;
    try ((idtac + symmetry); solve [eauto using assoc, compose_compat, 
    left_unit, right_unit, tensor_id, tensor_compose, tensor_compat,
    associator_cohere, left_unitor_cohere, right_unitor_cohere,
    (equiv_refl _ _ c_equiv_rel); try easy]).
  - rewrite <- compose_iso_l', <- assoc, <- compose_iso_r.
    symmetry. 
    apply associator_cohere.
  - rewrite <- left_unit, <- assoc.
    rewrite <- 2!compose_iso_r'.
    rewrite !assoc.
    rewrite <- pentagon.
    rewrite <- 2!(assoc (α_ realize_bw a, _, _ ⁻¹ ⊗ id_ realize_bw d)).
    rewrite <- tensor_compose, iso_inv_l, right_unit, tensor_id, left_unit.
    rewrite <- (assoc _ (α_ _, _ ,_)).
    rewrite iso_inv_l, left_unit.
    now rewrite <- tensor_compose, iso_inv_l, left_unit, tensor_id.
  - rewrite <- triangle.
    now rewrite <- assoc, iso_inv_l, left_unit.
  - etransitivity; eassumption.
Qed.


Theorem monoidal_coherence {a b : bw} (f g : a ⟶ b) :
  realize_bwarr f ≃ realize_bwarr g.
Proof.
  apply RealizationFunctor.(morphism_compat).
  apply bw_thin.
Qed.

End MonoidalCoherence.

Section monarr_theory.

Section monarr_cat.

Local Open Scope bw_scope.
Import monarr_notation.

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
  Tactics.program_simpl; eauto 4 with monarrdb bwarrdb; try easy.
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
  mor_tensor := @monarrtens X cC mC;
  associator := monassoc_iso;
  left_unitor := monlunitor_iso;
  right_unitor := monrunitor_iso;
}.

#[export, program] Instance monbwmcath : 
  MonoidalCategoryCoherence monbwmcat := {}.
Next Obligation.
  apply (compose_iso_l (monassoc_iso _ _ _)).
  simpl.
  rewrite monarr_assoc.
  rewrite monarr_assoc_nat.
  rewrite <- monarr_assoc, monarr_arrcomp, (monarr_struct _ (arrid _)).
  now rewrite monarr_runit.
Qed.
Next Obligation.
  rewrite !monarr_arrtens, monarr_arrcomp.
  apply monarr_struct.
Qed.
Next Obligation.
  rewrite !monarr_arrtens, !monarr_arrcomp.
  apply monarr_struct.
Qed.

#[export, program] Instance GeneralRealizationFunctor : 
  Functor monbwcat cC := {
  obj_map := realize_bw;
  morphism_map := @realize_monarr X cC mC;
}.
Next Obligation.
  induction H; try reflexivity; simpl.
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
  - symmetry; easy.
  - etransitivity; eauto.
Qed.

#[global] Add Parametric Morphism {a b} : (@realize_monarr X cC mC a b) 
  with signature 
  monarrequiv a b ==> cC.(c_equiv)
  as realize_monarr_mor.
Proof.
  apply GeneralRealizationFunctor.(morphism_compat).
Qed.

Section monarr_lemmas.

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

Lemma monarr_struct_Nf_eq {a b} (f : bwarr a b) :
  f ≊ bwarr_of_Nf_eq (Nf_eq_of_arr f).
Proof.
  apply monarr_struct.
Qed.

(* Section monarr_struct_builders.

Local Notation "a → b" := (bwarr a b) (at level 70) : type_scope.

Lemma __monarr_struct_assoc {a b c d} 
  (f : a ⨂ (b ⨂ c) → d) (g : ) *)

Lemma monarr_struct_id {a} (f : bwarr a a) : 
  f ≊ arrid a.
Proof. apply monarr_struct. Qed.

Lemma monarr_struct_assoc {a b c} (f : bwarr _ _) : 
  f ≊ arrassoc a b c.
Proof. apply monarr_struct. Qed.

Lemma monarr_struct_invassoc {a b c} (f : bwarr _ _) : 
  f ≊ arrinvassoc a b c.
Proof. apply monarr_struct. Qed.

Lemma monarr_struct_lunitor {a} (f : bwarr _ _) : 
  f ≊ arrlunitor a.
Proof. apply monarr_struct. Qed.

Lemma monarr_struct_invlunitor {a} (f : bwarr _ _) : 
  f ≊ arrinvlunitor a.
Proof. apply monarr_struct. Qed.

Lemma monarr_struct_runitor {a} (f : bwarr _ _) : 
  f ≊ arrrunitor a.
Proof. apply monarr_struct. Qed.

Lemma monarr_struct_invrunitor {a} (f : bwarr _ _) : 
  f ≊ arrinvrunitor a.
Proof. apply monarr_struct. Qed.



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

Lemma monarr_struct_inv {a b} (f : bwarr a b) (g : bwarr b a) : 
  f ◌ g ≊ arrid a.
Proof.
  eauto with monarrdb.
Qed.

Lemma monarr_id_l {a b} (f : a ⟶ b) (g : bwarr a a) :
  g ◌ f ≊ f.
Proof. now rewrite monarr_struct_id, monarr_lunit. Qed.

Lemma monarr_id_r {a b} (f : a ⟶ b) (g : bwarr b b) :
  f ◌ g ≊ f.
Proof. now rewrite monarr_struct_id, monarr_runit. Qed.

Lemma monarr_assoc_nat_l {a b m n p q} (f : a ⟶ b) (g : m ⟶ n) 
  (h : p ⟶ q) (assoc' : bwarr (a ⨂ (m ⨂ p)) (a ⨂ m ⨂ p)) : 
  assoc' ◌ f ⧆ g ⧆ h
  ≊ f ⧆ (g ⧆ h) ◌ arrassoc b n q.
Proof.
  rewrite <- monarr_assoc_nat.
  eauto with monarrdb.
Qed.

Lemma monarr_assoc_nat_r {a b m n p q} (f : a ⟶ b) (g : m ⟶ n) 
  (h : p ⟶ q) (assoc' : bwarr (b ⨂ (n ⨂ q)) (b ⨂ n ⨂ q)) : 
  f ⧆ (g ⧆ h) ◌ assoc'
  ≊ arrassoc a m p ◌ f ⧆ g ⧆ h.
Proof.
  rewrite monarr_assoc_nat.
  eauto with monarrdb.
Qed.

Lemma monarr_invassoc_nat_l {a b m n p q} (f : a ⟶ b) (g : m ⟶ n) 
  (h : p ⟶ q) (assoc' : bwarr (a ⨂ m ⨂ p) (a ⨂ (m ⨂ p))) : 
  assoc' ◌ f ⧆ (g ⧆ h)
  ≊ f ⧆ g ⧆ h ◌ arrinvassoc b n q.
Proof.
  rewrite monarrcomp_struct_l, monarr_assoc, monarr_assoc_nat_l.
  rewrite <- monarr_assoc, monarr_struct_inv.
  eauto with monarrdb.
Qed.

Lemma monarr_invassoc_nat_r {a b m n p q} (f : a ⟶ b) (g : m ⟶ n) 
  (h : p ⟶ q) (assoc' : bwarr (b ⨂ n ⨂ q) (b ⨂ (n ⨂ q))) : 
  f ⧆ g ⧆ h ◌ assoc'
  ≊ arrinvassoc a m p ◌ f ⧆ (g ⧆ h).
Proof.
  rewrite monarr_invassoc_nat_l.
  eauto with monarrdb.
Qed.

Lemma monarr_lunitor_nat_l {a b} (f : a ⟶ b) (unitor' : bwarr (e ⨂ a) a) : 
  unitor' ◌ f ≊ arrid e ⧆ f ◌ arrlunitor b.
Proof.
  rewrite <- monarr_lunitor_nat.
  eauto with monarrdb.
Qed.

Lemma monarr_lunitor_nat_r {a b} (f : a ⟶ b) (unitor' : bwarr (e ⨂ b) b) : 
  arrid e ⧆ f ◌ unitor' ≊ arrlunitor a ◌ f.
Proof.
  rewrite monarr_lunitor_nat.
  eauto with monarrdb.
Qed.

Lemma monarr_invlunitor_nat_l {a b} (f : a ⟶ b) (unitor' : bwarr _ _) : 
  unitor' ◌ arrid e ⧆ f ≊ f ◌ arrinvlunitor b.
Proof.
  rewrite monarrcomp_struct_l, monarr_assoc, monarrcomp_struct_r'.
  eauto with monarrdb.
Qed.

Lemma monarr_invlunitor_nat_r {a b} (f : a ⟶ b) (unitor' : bwarr _ _) : 
  f ◌ unitor' ≊ arrinvlunitor a ◌ arrid e ⧆ f.
Proof.
  rewrite monarrcomp_struct_l', monarr_assoc, monarrcomp_struct_r.
  eauto with monarrdb.
Qed.

Lemma monarr_runitor_nat_l {a b} (f : a ⟶ b) (unitor' : bwarr _ _) : 
  unitor' ◌ f ≊ f ⧆ arrid e ◌ arrrunitor b.
Proof.
  rewrite <- monarr_runitor_nat.
  eauto with monarrdb.
Qed.

Lemma monarr_runitor_nat_r {a b} (f : a ⟶ b) (unitor' : bwarr _ _) : 
  f ⧆ arrid e ◌ unitor' ≊ arrrunitor a ◌ f.
Proof.
  rewrite monarr_runitor_nat.
  eauto with monarrdb.
Qed.

Lemma monarr_invrunitor_nat_l {a b} (f : a ⟶ b) (unitor' : bwarr _ _) : 
  unitor' ◌ f ⧆ arrid e ≊ f ◌ arrinvrunitor b.
Proof.
  rewrite monarrcomp_struct_l, monarr_assoc, monarrcomp_struct_r'.
  eauto with monarrdb.
Qed.

Lemma monarr_invrunitor_nat_r {a b} (f : a ⟶ b) (unitor' : bwarr _ _) : 
  f ◌ unitor' ≊ arrinvrunitor a ◌ f ⧆ arrid e.
Proof.
  rewrite monarrcomp_struct_l', monarr_assoc, monarrcomp_struct_r.
  eauto with monarrdb.
Qed.

Lemma monarr_tens_id_split_bot {a b c d} 
  (f : a ⟶ b) (g : b ⟶ c) (arrid' : bwarr d d) :
  monarrtens arrid' (monarrcomp f g) 
  ≊ monarrcomp (monarrtens arrid' f) (monarrtens (arrid d) g).
Proof.
  now rewrite <- monarr_tens_comp, monarr_id_r.
Qed.

Lemma monarr_tens_id_split_top {a b c d} 
  (f : a ⟶ b) (g : b ⟶ c) (arrid' : bwarr d d):
  monarrtens (monarrcomp f g) arrid'
  ≊ monarrcomp (monarrtens f arrid') (monarrtens g (arrid d)).
Proof.
  now rewrite <- monarr_tens_comp, monarr_runit.
Qed.

Lemma monarr_comp_tens_struct_r {a b c d n m} (f : a ⟶ b) (g : c ⟶ d)
  (h : bwarr (b ⨂ d) (n ⨂ m)) (htop : bwarr b n) (hbot : bwarr d m) :
  f ⧆ g ◌ h ≊ (f ◌ htop) ⧆ (g ◌ hbot).
Proof.
  rewrite monarr_tens_comp, monarr_arrtens.
  auto with monarrdb.
Qed.

Lemma monarr_comp_tens_struct_l {a b c d n m} (f : a ⟶ b) (g : c ⟶ d)
  (h : bwarr (n ⨂ m) (a ⨂ c)) (htop : bwarr n a) (hbot : bwarr m c) :
  h ◌ f ⧆ g ≊ (htop ◌ f) ⧆ (hbot ◌ g).
Proof.
  rewrite monarr_tens_comp, monarr_arrtens.
  auto with monarrdb.
Qed.

Lemma monarr_comp_tens_id_top_struct_r {a b c d n} 
  (f : a ⟶ b) (g : c ⟶ d)
  (h : bwarr (b ⨂ d) (b ⨂ n)) : 
  f ⧆ g ◌ h ≊ f ⧆ (g ◌ bwarr_tens_cancel_l h).
Proof.
  erewrite monarr_struct, <- monarr_arrtens.
  rewrite <- monarr_tens_comp.
  rewrite monarr_runit.
  easy.
Qed.

Lemma monarr_comp_tens_id_bot_struct_r {a b c d n} 
  (f : a ⟶ b) (g : c ⟶ d)
  (h : bwarr (b ⨂ d) (n ⨂ d)) : 
  f ⧆ g ◌ h ≊ (f ◌ bwarr_tens_cancel_r h) ⧆ g.
Proof.
  erewrite monarr_struct, <- monarr_arrtens.
  rewrite <- monarr_tens_comp.
  rewrite monarr_runit.
  easy.
Qed.

Lemma monarr_comp_tens_id_top_struct_l {a b c d n} 
  (f : a ⟶ b) (g : c ⟶ d)
  (h : bwarr (a ⨂ n) (a ⨂ c)) : 
  h ◌ f ⧆ g ≊ f ⧆ (bwarr_tens_cancel_l h ◌ g).
Proof.
  erewrite monarr_struct, <- monarr_arrtens.
  rewrite <- monarr_tens_comp.
  rewrite monarr_lunit.
  easy.
Qed.

Lemma monarr_comp_tens_id_bot_struct_l {a b c d n} 
  (f : a ⟶ b) (g : c ⟶ d)
  (h : bwarr (n ⨂ c) (a ⨂ c)) : 
  h ◌ f ⧆ g ≊ (bwarr_tens_cancel_r h ◌ f) ⧆ g.
Proof.
  erewrite monarr_struct, <- monarr_arrtens.
  rewrite <- monarr_tens_comp.
  rewrite monarr_lunit.
  easy.
Qed.

End monarr_lemmas.

Section monarr_transformations.


Fixpoint monarr_rassoc_app {a b c} (f : a ⟶ b) : b ⟶ c -> a ⟶ c :=
  match f with
  | monarrcomp h f' => fun g => monarrcomp h (monarr_rassoc_app f' g)
  | f' => fun g => monarrcomp f' g
  end.

Fixpoint rassoc_monarr {a b} (f : a ⟶ b) : a ⟶ b :=
  match f with
  | monarrcomp g h => monarr_rassoc_app (rassoc_monarr g) (rassoc_monarr h)
  | monarrtens g h => monarrtens (rassoc_monarr g) (rassoc_monarr h)
  | monarrstruct g => monarrstruct g
  | mongeneric g => mongeneric g 
  end.

Lemma monarr_rassoc_app_correct {a b c} (f : a ⟶ b) (g : b ⟶ c) :
  monarr_rassoc_app f g ≊ monarrcomp f g.
Proof.
  induction f; eauto with monarrdb.
Qed.

Lemma rassoc_monarr_correct {a b} (f : a ⟶ b) : 
  rassoc_monarr f ≊ f.
Proof.
  induction f; simpl; [rewrite monarr_rassoc_app_correct|..];
  eauto 2 with monarrdb.
Qed.

Definition structify_acc_structs {a b} (f : a ⟶ b) : forall {c}, b ⟶ c -> a ⟶ c :=
  match f in a' ⟶ b' return forall {c}, b' ⟶ c -> a' ⟶ c with
  | monarrstruct f' => fun c g => (match g in b' ⟶ c' return forall {a'}, bwarr a' b' -> a' ⟶ c' with
    | monarrstruct g' => fun _ f' => monarrstruct (f' ○ g')
    | monarrcomp g1 g2 =>
      (match g1 in b' ⟶ c' return forall {d'} (_ : c' ⟶ d') {a'}, bwarr a' b' -> a' ⟶ d' with
      | monarrstruct h => fun d' g' a' f' => monarrcomp (f' ○ h) g'
      | g1' => fun d' g' a' f' => monarrcomp f' (g1' ◌ g')
      end) _ g2
    | monarrtens g1 g2 => fun a' f' => monarrcomp f' (g1 ⧆ g2)
    | mongeneric g' => fun a' f' => monarrcomp f' (mongeneric g')
    end) _ f'
  | monarrtens f1 f2 => fun c g => monarrcomp (monarrtens f1 f2) g
  | monarrcomp f1 f2 => fun c g => monarrcomp (monarrcomp f1 f2) g
  | mongeneric f' => fun c g => monarrcomp (mongeneric f') g
  end.

Fixpoint structify_rassoc_monarr {a b} (f : a ⟶ b) : a ⟶ b :=
  match f with
  | monarrcomp g1 g2 => 
    structify_acc_structs (structify_rassoc_monarr g1) (structify_rassoc_monarr g2)
  | monarrtens g1 g2 => 
    match structify_rassoc_monarr g1, structify_rassoc_monarr g2 with
    | monarrstruct h1, monarrstruct h2 => monarrstruct (arrtens h1 h2)
    | h1, h2 => monarrtens h1 h2
    end
  | monarrstruct g => monarrstruct g
  | mongeneric g => mongeneric g
  end.

Lemma structify_acc_structs_correct {a b c} (f : a ⟶ b) (g : b ⟶ c) :
  structify_acc_structs f g ≊ f ◌ g.
Proof.
  induction f; [easy..|].
  destruct g; [|easy..|].
  - destruct g1; [easy..|].
    simpl.
    rewrite <- monarr_arrcomp.
    symmetry; apply monarr_assoc.
  - symmetry; apply monarr_arrcomp.
Qed.

Lemma structify_rassoc_monarr_correct {a b} (f : a ⟶ b) : 
  structify_rassoc_monarr f ≊ f.
Proof.
  induction f; [| |easy..].
  - eauto using structify_acc_structs_correct with monarrdb.
  - simpl.
    revert IHf1 IHf2.
    destruct (structify_rassoc_monarr f1); [eauto 2 with monarrdb..|].
    destruct (structify_rassoc_monarr f2); eauto with monarrdb.
Qed.

Definition structify_monarr {a b} (f : a ⟶ b) : a ⟶ b :=
  structify_rassoc_monarr (rassoc_monarr f).

Lemma structify_monarr_correct {a b} (f : a ⟶ b) :
  structify_monarr f ≊ f.
Proof.
  transitivity (rassoc_monarr f).
  - apply structify_rassoc_monarr_correct.
  - apply rassoc_monarr_correct.
Qed.


End monarr_transformations.

End monarr_cat.
End monarr_theory.
End MonoidalCoherenceConsequences.