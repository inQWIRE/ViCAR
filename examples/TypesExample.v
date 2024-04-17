Require Import Setoid.
Require Import Logic.
From ViCaR Require Export CategoryTypeclass.

Local Notation "f '\o' g" := (fun A => g (f A)) 
  (at level 45, left associativity).

Local Notation "f ~ g" := (forall a, f a = g a) 
  (at level 80, no associativity).

Definition fun_equiv {A B : Type} (f g : A -> B) := 
  f ~ g.

Local Notation "⊤" := Datatypes.unit.
Local Notation "⊥" := False.

Definition fun_sum {A B A' B' : Type} (f : A -> B) (g : A' -> B') :
  (A + A') -> (B + B') :=
  fun i =>
  match i with
  | inl a => inl (f a)
  | inr a' => inr (g a')
  end.

Local Notation "f '\+' g" := (fun_sum f g) (at level 43, left associativity).

Definition fun_prod {A B A' B' : Type} (f : A -> B) (g : A' -> B') :
  (A * A') -> (B * B') :=
  fun i =>
  match i with
  | (a, a') => (f a, g a')
  end.

Local Notation "f '\*' g" := (fun_prod f g) (at level 41, left associativity).

Ltac print_state :=
  try (match reverse goal with | H : ?p |- _ => idtac H ":" p; fail end);
  idtac "---------------------------------------------------------";
  match reverse goal with |- ?P => idtac P 
  end.

(* From Adam Chipala's excellent CPDT, in Match *)
Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ =>
      match P with
        | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
      end
  end.
Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.

Ltac __saturate_funs Hf :=
  match type of Hf with ?f ?i =>
  repeat match goal with
  | H : f ~ ?g |- _ => 
    let Hg := constr:(H i) in
      extend Hg; __saturate_funs (g i)
  | H : ?g ~ f |- _ => 
    let Hg := constr:(H i) in
      extend Hg; __saturate_funs (g i)
  end
end.

Ltac __solve_functions_end_forward := 
  repeat match goal with
  | H : ?f ?i = ?g ?j |- _ => match type of f with ?A -> ?B =>
      revert H
      end
  end;
  repeat (let Hf := fresh "Hf" in intros Hf;
    match type of Hf with
    | ?f ?i = ?g ?j =>
      __saturate_funs (f i); __saturate_funs (g j)
    end);
  easy.

(* Begin tactics *)
Ltac __solve_functions_end := 
  try eassumption;
  try reflexivity;
  try easy;
  auto;  
  try (match goal with
  | |- ?f ?x => match type of f with ?n -> ?m => eassumption end
  (* | H : ?A ?i ?j |- ?A ?i' ?j' =>
    match type of A with 
    | fun ?n ?m => 
      (eapply H || ( idtac "needed rewrite";
      replace i' with i by auto; replace j' with j by auto; eapply H))
    end *)
  | H : ?A ~ ?A' |- ?A ?i = ?A' ?i => idtac "hitexact"; apply H
  | H : ?A ~ ?A' |- ?A' ?i = ?A ?i => idtac "hitsym"; symmetry; apply H
  | H : ?A ~ ?A' |- _ => apply H
  | H : ?A ~ ?A' |- _ => symmetry; apply H
  | H : ?A ~ ?A' |- context[?A ?i] => 
    (rewrite H; clear H; print_state; solve [__solve_functions_end])
    || (rewrite <- H; clear H; print_state; solve [__solve_functions_end])
    || (clear H; solve [__solve_functions_end])
  | H : ?A ~ ?A' |- context[?A' ?i] =>   
    (rewrite <- H; clear H; print_state; solve [__solve_functions_end])
    || (rewrite H; clear H; print_state; solve [__solve_functions_end])
    || (clear H; solve [__solve_functions_end])
  end || idtac (* " no match" *)).


Ltac solve_functions := idtac. (* Hack to allow "mutual recursion" *)

Ltac __setup_solve_functions :=
  simpl;
  unfold fun_equiv, id, fun_sum, 
    fun_prod in *;
  simpl.

Ltac __solve_functions_mid_step := 
  repeat (intros ?); intros; subst; auto.

Lemma exists_prod {A B} : forall P,
  (exists ab : A * B, P ab) <-> (exists (a : A) (b : B), P (a, b)).
Proof.
  intros P.
  split.
  - intros [[a b] HPab].
    exists a, b; exact HPab.
  - intros [a [b HPab]].
    exists (a, b); exact HPab.
Qed.

Lemma exists_sum {A B} : forall P,
  (exists ab : A + B, P ab) <-> 
  ((exists (a : A), P (inl a)) \/ exists (b : B), P (inr b)).
Proof.
  intros P.
  split.
  - intros [[a | b] HPab]; [left | right];
    eexists; eassumption.
  - intros [[a HPa] | [b HPb]]; 
    eexists; eassumption.
Qed.


Ltac __process_solve_functions_cleanup_vars :=
  repeat match goal with
  | a : ?A * ?B |- _ => destruct a
  | a : ⊤ |- _ => destruct a
  | a : ?A + ?B |- _ => destruct a
  end.

Ltac __process_solve_functions_step :=
  __process_solve_functions_cleanup_vars;
  try easy;
  match goal with
  | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
  | H : @eq (_ + _) _ _ |- _ => inversion H; subst; clear H

  | H : (exists _, _) |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | |- _ <-> _ => split
  | |- _ /\ _ => split
  | H : _ \/ _ |- _ => destruct H; [solve_functions | solve_functions]
  | |- _ \/ _ => 
       (left; solve [solve_functions; auto]) 
    || (right; solve [solve_functions; auto]) 
    || (* print_state; *) fail 2
  | |- exists (_ : ?A), _ => 
    match A with 
    | ?B * ?C => rewrite exists_prod
    | ?B + ?C => rewrite exists_sum
    | ⊤ => exists tt
    | _ => 
      (* idtac "trying vars"; print_state;  *)
      match goal with
        | x : A |- _ => 
          exists x; (* idtac "yes" x; *) (solve [solve_functions; auto])
        end; match goal with
        | |- _ => (* idtac "none worked"; *) eexists
      end
    end
  | |- (_, _) = (_, _) => f_equal
  | |- inl _ = inl _ => f_equal
  | |- inr _ = inr _ => f_equal
  end.

Ltac __process_solve_functions := 
  repeat (
  __solve_functions_mid_step;
  __process_solve_functions_step).

Ltac solve_functions ::= 
  __setup_solve_functions;
  __process_solve_functions;
  __solve_functions_mid_step;
  __solve_functions_end || __solve_functions_end_forward.
(* End tactics *)

Lemma fun_equiv_refl {A B : Type} (f : A -> B) :
  f ~ f.
Proof. easy. Qed.

Lemma fun_equiv_sym {A B : Type} (f g : A -> B) :
  f ~ g -> g ~ f.
Proof. easy. Qed.

Lemma fun_equiv_trans {A B : Type} (f g h : A -> B) :
  f ~ g -> g ~ h -> f ~ h.
Proof. 
  intros.
  rewrite H; easy.
Qed.

Lemma fun_equiv_equivalence (A B : Type) : 
  equivalence (A -> B) (@fun_equiv A B).
Proof.
  unfold fun_equiv. split.
  - intros ?; apply fun_equiv_refl.
  - intros ?; apply fun_equiv_trans.
  - intros ?; apply fun_equiv_sym.
Qed.


Lemma compose_funs_assoc {A B C D : Type} : forall
  (f : A -> B) (g : B -> C) (h : C -> D), 
  f \o g \o h ~ f \o (g \o h).
Proof.
  easy.
Qed.

Lemma compose_id_l {A B} (f : A -> B) :
  id \o f ~ f.
Proof. easy. Qed.

Lemma compose_id_r {A B} (f : A -> B) :
  f \o id ~ f.
Proof. easy. Qed.

Lemma compose_funs_compat {A B C : Type} : forall (f f' : A -> B),
  f ~ f' -> forall (g g' : B -> C), g ~ g' -> 
  f \o g ~ f' \o g'.
Proof.
  intros f f' Hf g g' Hg x. 
  simpl.
  rewrite Hf; easy.
Qed.

#[export] Instance Typ : Category Type := {
  morphism := fun A B => A -> B;
  c_equiv := @fun_equiv;
  compose := fun A B C f g => f \o g;
  c_identity := @id;
}.

#[export] Instance TypC : CategoryCoherence Typ := {
  c_equiv_rel := fun_equiv_equivalence;
  compose_compat := @compose_funs_compat;
  assoc := @compose_funs_assoc;
  left_unit := @compose_id_l;
  right_unit := @compose_id_r;
}.

Lemma prod_jd {A B} : 
  id \* id ~ @id (A*B).
Proof.
  intros [a b].
  easy.
Qed.

Lemma prod_compose {A B C A' B' C'} : 
  forall (f : A -> B) (g : B -> C) (f' : A' -> B') (g' : B' -> C'),
  (f \o g) \* (f' \o g') ~ f \* f' \o g \* g'.
Proof.
  solve_functions.
Qed.

Lemma prod_compat {A B C D} :
  forall (f f' : A -> B) (g g' : C -> D),
  f ~ f' -> g ~ g' ->
  f \* g ~ f' \* g'.
Proof.
  intros f f' g g' Hf Hg [a c].
  simpl.
  rewrite Hf, Hg.
  easy.
Qed.

#[export] Instance ProductFunction : Bifunctor Typ Typ Typ := {
  obj_bimap := prod;
  morphism_bimap := @fun_prod;
  id_bimap := @prod_jd;
  compose_bimap := @prod_compose;
  morphism_bicompat := @prod_compat;
}.

#[export] Instance TypAssociator {A B C : Type} : 
  Isomorphism (A * B * C) (A * (B * C)) := {
  forward := fun ab_c => let '((a, b), c) := ab_c in (a, (b, c));
  reverse := fun a_bc => let '(a, (b, c)) := a_bc in ((a, b), c);
  isomorphism_inverse := ltac:(abstract(solve_functions));
}.

(* Set Printing Universes. *)

#[export] Instance TypLeftUnitor {A : Type} :
  @Isomorphism Type Typ (⊤ * A) (A) := {
  forward := fun topa => let (_, a) := topa in a;
  reverse := fun a => (tt, a);
  isomorphism_inverse := ltac:(abstract(solve_functions))
}.

#[export] Instance TypRightUnitor {A : Type} :
  @Isomorphism Type Typ (A * ⊤) (A) := {
    forward := fun topa => let (a, _) := topa in a;
    reverse := fun a => (a, tt);
    isomorphism_inverse := ltac:(abstract(solve_functions))
}.

#[export] Instance TypMonoidal : MonoidalCategory Typ := {
  obj_tensor := prod;
  mor_tensor := @fun_prod;
  mon_I := ⊤;
  associator := @TypAssociator;
  left_unitor := @TypLeftUnitor;
  right_unitor := @TypRightUnitor;
}.

Obligation Tactic := try (hnf; solve_functions).

#[export, program] Instance TypMonoidalC 
  : MonoidalCategoryCoherence TypMonoidal := {}.

#[export, program] Instance TypBraidingIsomorphism {A B} : 
  Isomorphism (A * B) (B * A) := {
  forward := fun ab => let (a, b) := ab in (b, a);
  reverse := fun ba => let (b, a) := ba in (a, b)
}.

#[export] Instance TypBraiding : 
  NaturalBiIsomorphism ProductFunction (CommuteBifunctor ProductFunction) := {
  component_biiso := @TypBraidingIsomorphism;
  component_biiso_natural := ltac:(abstract(solve_functions))
}.

#[export] Instance TypBraidedMonoidal : BraidedMonoidalCategory TypMonoidal := {
  braiding := TypBraiding; }.
#[export, program] Instance TypBraidedMonoidalC : 
  BraidedMonoidalCategoryCoherence TypBraidedMonoidal := {}.

#[export, program] Instance TypSymmetricMonoidal : 
  SymmetricMonoidalCategory TypBraidedMonoidal := {}.





Lemma sum_id {A B} : 
  id \+ id ~ @id (A + B).
Proof. solve_functions. Qed.

Lemma sum_compose {A B C A' B' C'} : 
  forall (f : A -> B) (g : B -> C) (f' : A' -> B') (g' : B' -> C'),
  (f \o g) \+ (f' \o g') ~ f \+ f' \o g \+ g'.
Proof.
  solve_functions.
Qed.
  
#[program, export] Instance SumFunction : Bifunctor Typ Typ Typ | 10 := {
  obj_bimap := sum;
  morphism_bimap := @fun_sum;
  id_bimap := @sum_id;
  compose_bimap := @sum_compose;
}.

#[export] Instance TypSumAssociator {A B C : Type} : 
  Isomorphism (A + B + C) (A + (B + C)) := {
  forward := fun ab_c =>
    match ab_c with
    | inl (inl a) => inl a
    | inl (inr b) => inr (inl b)
    | inr c => inr (inr c)
    end;
  reverse := fun a_bc =>
    match a_bc with
    | inl a => inl (inl a)
    | inr (inl b) => inl (inr b)
    | inr (inr c) => inr c
    end;
  isomorphism_inverse := ltac:(abstract(solve_functions));
}.


#[export] Instance TypSumLeftUnitor {A : Type} :
  @Isomorphism Type Typ (⊥ + A) (A) := {
  forward := fun bota => match bota with
    | inr a => a
    | inl bot => match bot with end
    end;
  reverse := fun a => inr a;
  isomorphism_inverse := ltac:(abstract(solve_functions))
}.

#[export] Instance TypSumRightUnitor {A : Type} :
  @Isomorphism Type Typ (A + ⊥) (A) := {
  forward := fun bota => match bota with
    | inl a => a
    | inr bot => match bot with end 
    end;
  reverse := fun a => inl a;
  isomorphism_inverse := ltac:(abstract(solve_functions))
}.

#[export] Instance TypSumMonoidal : MonoidalCategory Typ | 10 := {
  obj_tensor := sum;
  mor_tensor := @fun_sum;
  mon_I := ⊥;
  associator := @TypSumAssociator;
  left_unitor := @TypSumLeftUnitor;
  right_unitor := @TypSumRightUnitor;
}.

#[export, program] Instance TypSumMonoidalC 
  : MonoidalCategoryCoherence TypSumMonoidal := {}.

#[export] Instance TypSumBraidingIsomorphism {A B} : 
  Isomorphism (A + B) (B + A) := {
  forward := fun a_b => 
    match a_b with
    | inl a => inr a
    | inr b => inl b
    end;
  reverse := fun b_a => 
    match b_a with
    | inr a => inl a
    | inl b => inr b
    end;
  isomorphism_inverse := ltac:(abstract(solve_functions))
}.

#[export] Instance TypSumBraiding : 
  NaturalBiIsomorphism SumFunction (CommuteBifunctor SumFunction) := {
  component_biiso := @TypSumBraidingIsomorphism;
  component_biiso_natural := ltac:(abstract(solve_functions))
}.

#[export] Instance TypSumBraidedMonoidal 
  : BraidedMonoidalCategory TypSumMonoidal | 10 := {
  braiding := TypSumBraiding;
}.

#[export, program] Instance TypSumBraidedMonoidalC
  : BraidedMonoidalCategoryCoherence TypSumBraidedMonoidal := {}.

#[export, program] Instance TypSumSymmetricMonoidal : 
  SymmetricMonoidalCategory TypSumBraidedMonoidal | 10 := {}.

#[export] Instance TypLeftDistributivityIsomorphism (A B M : Type) :
  @Isomorphism Type Typ (A * (B + M)) ((A * B) + (A * M)) := {
  forward := fun abm => match abm with
    | (a, inl b) => inl (a, b)
    | (a, inr m) => inr (a, m)
    end;
  reverse := fun abam => match abam with
    | inl (a, b) => (a, inl b)
    | inr (a, m) => (a, inr m)
    end;
  isomorphism_inverse := ltac:(abstract(solve_functions));
}.

#[export] Instance TypRightDistributivityIsomorphism (A B M : Type) :
  @Isomorphism Type Typ ((A + B) * M) ((A * M) + (B * M)) := {
    forward := fun abm => match abm with
    | (inl a, m) => inl (a, m)
    | (inr b, m) => inr (b, m)
    end;
  reverse := fun abam => match abam with
    | inl (a, m) => (inl a, m)
    | inr (b, m) => (inr b, m)
    end;
  isomorphism_inverse := ltac:(abstract(solve_functions));
}.

Lemma rel_left_distributivity_isomorphism_natural {A B M A' B' M' : Type}
  (f : A -> A') (g : B -> B') (h : M -> M') :
  (TypLeftDistributivityIsomorphism A B M
  ∘ (fun_sum (fun_prod f g) (fun_prod f h))
  ≃ fun_prod f (fun_sum g h)
  ∘ TypLeftDistributivityIsomorphism A' B' M')%Cat.
Proof.
  solve_functions.
Qed.

Lemma rel_right_distributivity_isomorphism_natural {A B M A' B' M' : Type}
  (f : A -> A') (g : B -> B') (h : M -> M') :
  (TypRightDistributivityIsomorphism A B M
  ∘ (fun_sum (fun_prod f h) (fun_prod g h))
  ≃ fun_prod (fun_sum f g) h
  ∘ TypRightDistributivityIsomorphism A' B' M')%Cat.
Proof.
  solve_functions.
Qed.

#[export] Instance TypLeftAbsorbtion (A : Type) :
  (⊥ * A <~> ⊥)%Cat := {
  forward := fun bota => match bota with | (bot, a) => match bot with end end;
  reverse := fun bot => match bot with end;
  isomorphism_inverse := ltac:(abstract(solve_functions));
}.

#[export] Instance TypRightAbsorbtion (A : Type) :
  (A * ⊥ <~> ⊥)%Cat := {
  forward := fun abot => match abot with | (a, bot) => match bot with end end;
  reverse := fun bot => match bot with end;
  isomorphism_inverse := ltac:(abstract(solve_functions));
}.

Require Import CategoryConstructions.
Require Import FunctionalExtensionality.
Require Import Eqdep.

Section TypProperties.

Local Open Scope Cat_scope.

Definition big_prod {J} (obj : J -> Type) := forall (i : J), obj i.

#[export, program] Instance TypBigProd {J} {obj : J -> Type} : 
  CategoryBigProd obj (big_prod obj) := {
  p_i := fun i => fun f => f i;
  big_prod_mor := fun Q fQ_ => fun q => fun i => fQ_ i q;
}.
Next Obligation.
  unfold big_prod.
  __setup_solve_functions.
  __solve_functions_mid_step.
  apply functional_extensionality_dep.
  intros i.
  symmetry.
  apply H.
Qed.

Inductive big_sum {J} (obj : J -> Type) :=
  | in_i i (a : obj i) : big_sum obj.

Arguments in_i {_ _} _ _.

#[export, program] Instance TypBigCoprod {J} {obj : J -> Type} : 
  CategoryBigCoprod obj (big_sum obj) := {
  iota_i := fun i => fun oi => in_i i oi;
  big_coprod_mor := fun Q fQ_ => fun oi => match oi with
  | in_i i ai => fQ_ i ai
  end;
}.
Next Obligation.
  intros J obj Q fQ_ fAB' H [i ai].
  symmetry.
  apply H.
Qed.

#[export, program] Instance TypCartesianMonoidalCategory :
  CartesianMonoidalCategory TypMonoidal := {
    tensor_cartesian := fun A B => {| 
      p_A := fun ab => let (a, _) := ab in a;
      p_B := fun ab => let (_, b) := ab in b;
      prod_mor := fun Q fA fB =>
        fun q => (fA q, fB q)
    |}
  }.
Next Obligation. 
  intros ** q.
  simpl.   
  rewrite H, H0.
  simpl.
  destruct (fAB' q).
  easy. 
Qed.

#[program, export] Instance TypExponential {A B : Type} :
  CategoryExponential A B (B -> A) := {
  eval_mor := fun fb => let (f, b) := fb in f b;
  eval_mor_transpose := fun M f => fun m b => f (m, b);
}.
Next Obligation.
  intros ** i.
  apply functional_extensionality.
  intros b.
  rewrite H.
  easy.
Qed.

Definition typ_limit_obj {D} {cD : Category D} (F : Functor cD Typ) : Type :=
  { s : big_prod F.(obj_map) | 
    forall (d d' : D) (f : d ~> d'), (F @ f) (s d) = s d' }.

Definition typ_limit_obj_cone_mor {D} {cD : Category D} (F : Functor cD Typ) :
  forall (d : D), typ_limit_obj F ~> F d 
  := fun d sP => let (s, _) := sP in s d.

Lemma typ_limit_obj_cone_mor_prop {D} {cD : Category D} (F : Functor cD Typ) :
  forall {d d' : D} (f : d ~> d'), 
  typ_limit_obj_cone_mor F d ∘ F @ f ≃ typ_limit_obj_cone_mor F d'.
Proof.
  intros d d' f.
  intros [s Hs].
  apply Hs.
Qed.

#[export] Instance TypLimitCone {D} {cD : Category D} (F : Functor cD Typ) 
  : Cone F := {
  cone_obj := typ_limit_obj F;
  cone_mor := typ_limit_obj_cone_mor F;
  cone_mor_prop := fun d d' => typ_limit_obj_cone_mor_prop F;
}.

#[export, program] Instance TypLimit {D} {cD : Category D} (F : Functor cD Typ) 
  : Limit F := {
  limit_cone := TypLimitCone F;
}.
Next Obligation.
  intros D cD F N X.
  exists (fun d => N.(cone_mor) d X).
  intros d d' f.
  apply N.
Defined.
Next Obligation.
  intros ** c.
  unfold TypLimit_obligation_1.
  simpl.
  destruct (f' c) as [s' P'] eqn:e.
  match goal with
  |- exist _ ?s ?P = exist _ ?s' ?P' => assert (Hs: s = s')
  end.
  - apply functional_extensionality_dep.
    intros d.
    specialize (H d c).
    rewrite <- H.
    simpl.
    unfold typ_limit_obj_cone_mor.
    rewrite e.
    easy.
  - subst s'.
    f_equal.
    unfold cone_mor_prop.
    destruct N as [Nobj Nmor Nmor_prop]; simpl in *.
    apply functional_extensionality_dep; intros d;
    apply functional_extensionality_dep; intros d';
    apply functional_extensionality_dep; intros f.
    apply UIP.
Qed.

End TypProperties.


    



