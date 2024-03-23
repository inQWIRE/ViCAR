Require Import Setoid.
Require Import Logic.
From ViCaR Require Export CategoryTypeclass.
(* From ViCaR Require Import RigCategory. *)

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
  c_equiv_rel := fun_equiv_equivalence;
  compose := fun A B C f g => f \o g;
  compose_compat := @compose_funs_compat;
  assoc := @compose_funs_assoc;
  c_identity := @id;
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
  tensor := ProductFunction;
	mon_I := ⊤;
  associator := @TypAssociator;
  left_unitor := @TypLeftUnitor;
  right_unitor := @TypRightUnitor;
  associator_cohere := ltac:(abstract(solve_functions));
  left_unitor_cohere := ltac:(abstract(solve_functions));
  right_unitor_cohere := ltac:(abstract(solve_functions));
  triangle := ltac:(abstract(solve_functions));
  pentagon := ltac:(abstract(solve_functions));
}.

#[export] Instance TypBraidingIsomorphism {A B} : 
  Isomorphism (A * B) (B * A) := {
  forward := fun ab => let (a, b) := ab in (b, a);
  reverse := fun ba => let (b, a) := ba in (a, b);
  isomorphism_inverse := ltac:(abstract(solve_functions))
}.

#[export] Instance TypBraiding : 
  NaturalBiIsomorphism ProductFunction (CommuteBifunctor ProductFunction) := {
  component_biiso := @TypBraidingIsomorphism;
  component_biiso_natural := ltac:(abstract(solve_functions))
}.

#[export] Instance TypBraidedMonoidal : BraidedMonoidalCategory TypMonoidal := {
  braiding := TypBraiding;
  hexagon_1 := ltac:(abstract(solve_functions));
  hexagon_2 := ltac:(abstract(solve_functions));
}.

#[export] Instance TypSymmetricMonoidal : 
  SymmetricMonoidalCategory TypBraidedMonoidal := {
  symmetry := ltac:(abstract(solve_functions));
}.

(* #[export] Instance TypCompactClosed : CompactClosedCategory Type := {
  dual := fun A => A;
  unit := @fun_unit;
  counit := fun A => flip fun_unit;
  triangle_1 := ltac:(abstract(solve_functions));
  triangle_2 := ltac:(abstract(solve_functions));
}. *)

(* #[export] Instance TypDagger : DaggerCategory Type := {
  adjoint := fun A B => @flip A B Prop;
  adjoint_involutive := ltac:(easy);
  adjoint_id := ltac:(easy);
  adjoint_contravariant := ltac:(abstract(solve_functions));
  adjoint_compat := ltac:(abstract(solve_functions));
}.

#[export] Instance TypDaggerMonoidal : DaggerMonoidalCategory Type := {
  dagger_tensor_compat := ltac:(abstract(solve_functions));
  associator_unitary := ltac:(abstract(solve_functions));
  left_unitor_unitary := ltac:(abstract(solve_functions));
  right_unitor_unitary := ltac:(abstract(solve_functions));
}. *)





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
Next Obligation.
  intros [a | b]; simpl; [rewrite H | rewrite H0]; easy.
Qed.

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
  tensor := SumFunction;
	mon_I := ⊥;
  associator := @TypSumAssociator;
  left_unitor := @TypSumLeftUnitor;
  right_unitor := @TypSumRightUnitor;
  associator_cohere := ltac:(abstract(solve_functions));
  left_unitor_cohere := ltac:(abstract(solve_functions));
  right_unitor_cohere := ltac:(abstract(solve_functions));
  triangle := ltac:(abstract(solve_functions));
  pentagon := ltac:(abstract(solve_functions));
}.

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
  hexagon_1 := ltac:(abstract(solve_functions));
  hexagon_2 := ltac:(abstract(solve_functions));
}.

#[export] Instance TypSumSymmetricMonoidal : 
  SymmetricMonoidalCategory TypSumBraidedMonoidal | 10 := {
  symmetry := ltac:(abstract(solve_functions));
}.

Lemma not_TypSumCompactClosed :
  @CompactClosedCategory Type Typ TypSumMonoidal 
  TypSumBraidedMonoidal TypSumSymmetricMonoidal -> False.
Proof.
  intros [].
  destruct (counit ⊤ (inl tt)).
Qed.

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

#[export] Instance TypPreDistr : 
  PreDistributiveBimonoidalCategory TypSumSymmetricMonoidal
  TypMonoidal := {
    left_distr_iso := TypLeftDistributivityIsomorphism;
    right_distr_iso := TypRightDistributivityIsomorphism;
    left_distr_natural := @rel_left_distributivity_isomorphism_natural;
    right_distr_natural := @rel_right_distributivity_isomorphism_natural;
}.

#[export] Instance TypDistrBimonoidal : 
  DistributiveBimonoidalCategory TypPreDistr := {
  left_absorbtion_iso := TypLeftAbsorbtion;
  right_absorbtion_iso := TypRightAbsorbtion;
  left_absorbtion_natural := ltac:(abstract(solve_functions));
  right_absorbtion_natural := ltac:(abstract(solve_functions));
}.

#[export] Instance TypSemiCoherent :
  SemiCoherent_DistributiveBimonoidalCategory TypDistrBimonoidal := {
  cond_I (A B C : Type) := ltac:(abstract(solve_functions));
  cond_III (A B C : Type) := ltac:(abstract(solve_functions));
  cond_IV (A B C D : Type) := ltac:(abstract(solve_functions));
  cond_V (A B C D : Type) := ltac:(abstract(solve_functions));
  cond_VI (A B C D : Type) := ltac:(abstract(solve_functions));
  cond_VII (A B C D : Type) := ltac:(abstract(solve_functions));
  cond_VIII (A B C D : Type) := ltac:(abstract(solve_functions));
  cond_IX  (A B C D : Type) := ltac:(abstract(solve_functions));
  cond_X := ltac:(abstract(solve_functions));
  cond_XI (A B : Type) := ltac:(abstract(solve_functions));
  cond_XII (A B : Type) := ltac:(abstract(solve_functions));
  cond_XIII := ltac:(abstract(solve_functions));
  cond_XIV := ltac:(abstract(solve_functions));
  cond_XVI (A B : Type) := ltac:(abstract(solve_functions));
  cond_XVII (A B : Type) := ltac:(abstract(solve_functions));
  cond_XVIII (A B : Type) := ltac:(abstract(solve_functions));
  cond_XIX (A B : Type) := ltac:(abstract(solve_functions));
  cond_XX (A B : Type) := ltac:(abstract(solve_functions));
  cond_XXI (A B : Type) := ltac:(abstract(solve_functions));
  cond_XXII (A B : Type) := ltac:(abstract(solve_functions));
  cond_XXIII (A B : Type) := ltac:(abstract(solve_functions));
  cond_XXIV (A B : Type) := ltac:(abstract(solve_functions));
(* 
  condition_I (A B C : Type) := ltac:(abstract(solve_functions));
  condition_III (A B C : Type) := ltac:(abstract(solve_functions));
  condition_IV (A B C D : Type) := ltac:(abstract(solve_functions));
  condition_V (A B C D : Type) := ltac:(abstract(solve_functions));
  condition_VI (A B C D : Type) := ltac:(abstract(solve_functions));
  condition_VII (A B C D : Type) := ltac:(abstract(solve_functions));
  condition_VIII (A B C D : Type) := ltac:(abstract(solve_functions));
  condition_IX  (A B C D : Type) := ltac:(abstract(solve_functions));
  condition_X := ltac:(abstract(solve_functions));
  condition_XI (A B : Type) := ltac:(abstract(solve_functions));
  condition_XII (A B : Type) := ltac:(abstract(solve_functions));
  condition_XIII := ltac:(abstract(solve_functions));
  condition_XIV := ltac:(abstract(solve_functions));
  condition_XVI (A B : Type) := ltac:(abstract(solve_functions));
  condition_XVII (A B : Type) := ltac:(abstract(solve_functions));
  condition_XVIII (A B : Type) := ltac:(abstract(solve_functions));
  condition_XIX (A B : Type) := ltac:(abstract(solve_functions));
  condition_XX (A B : Type) := ltac:(abstract(solve_functions));
  condition_XXI (A B : Type) := ltac:(abstract(solve_functions));
  condition_XXII (A B : Type) := ltac:(abstract(solve_functions));
  condition_XXIII (A B : Type) := ltac:(abstract(solve_functions));
  condition_XXIV (A B : Type) := ltac:(abstract(solve_functions)); 
*)
}.

#[export] Instance TypSemiCoherentBraided :
  SemiCoherent_BraidedDistributiveBimonoidalCategory TypDistrBimonoidal TypBraidedMonoidal := {
  cond_II (A B C : Type) := ltac:(abstract(solve_functions));
  cond_XV (A : Type) := ltac:(abstract(solve_functions));
}.








Local Open Scope Cat_scope.
Generalizable Variable C.

Set Universe Polymorphism.


Class CategoryProduct `{cC : Category C} (A B : C) (AB : C) := {
  p_A : AB ~> A;
  p_B : AB ~> B;
  prod_mor : 
    forall (Q : C) (fA : Q ~> A) (fB : Q ~> B), Q ~> AB;
  prod_mor_prop: 
    forall (Q : C) (fA : Q ~> A) (fB : Q ~> B),
    (prod_mor Q fA fB) ∘ p_A ≃ fA /\
    (prod_mor Q fA fB) ∘ p_B ≃ fB;
  prod_mor_unique : 
    forall (Q : C) (fA : Q ~> A) (fB : Q ~> B) 
    (fAB' : Q ~> AB), 
    fA ≃ fAB' ∘ p_A -> fB ≃ fAB' ∘ p_B -> 
    fAB' ≃ prod_mor Q fA fB
}.

Arguments CategoryProduct {_} {_}%Cat (_ _ _)%Obj.

(* Local Notation "'@' AB" := (AB.(prod_AB)) (at level 8) : Cat_scope. *)



Lemma prod_mor_unique' `{cC : Category C} {A B AB : C} 
  (HAB : CategoryProduct A B AB) {Q} (fA : Q ~> A) (fB : Q ~> B) : 
  forall (fAB fAB' : Q ~> AB),
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
  forall {AB AB'} (HAB : CategoryProduct A B AB) 
  (HAB' : CategoryProduct A B AB'), Isomorphism AB AB' :=
  fun AB AB' HAB HAB' =>
  {|
    forward := HAB'.(prod_mor) AB p_A p_B;
    reverse := HAB.(prod_mor) AB' p_A p_B;
  |}.
Obligations.
Next Obligation.
  split; eapply (prod_mor_unique' _ p_A p_B); rewrite 1?assoc.
  1,5: rewrite 2!(proj1 (prod_mor_prop _ _ _)); easy.
  1,4: rewrite 2!(proj2 (prod_mor_prop _ _ _)); easy.
  all: rewrite left_unit; easy.
Qed.



Class CartesianMonoidalCategory `(mC : MonoidalCategory C) := {
  tensor_cartesian : forall (A B : C),
    CategoryProduct A B (A × B)%Mon;
}.

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
  easy.
Qed.
Next Obligation. 
  intros q.   
  rewrite H, H0.
  destruct (fAB' q).
  easy. 
Qed.

Class CategoryBigProd `{cC : Category C} {J : Type} 
  (obj : J -> C) (prod_J : C) := {
  p_i : forall i, prod_J ~> obj i;
  big_prod_mor : 
    forall (Q : C) (fQ_ : forall i, Q ~> obj i), Q ~> prod_J;
  big_prod_mor_prop: 
    forall (Q : C) (fQ_ : forall i, Q ~> obj i),
    forall i, 
    (big_prod_mor Q fQ_) ∘ p_i i ≃ fQ_ i;
  big_prod_mor_unique : 
    forall (Q : C) (fQ_ : forall i, Q ~> obj i)
    (fAB' : Q ~> prod_J), 
    (forall i, fQ_ i ≃ fAB' ∘ p_i i) ->
    fAB' ≃ big_prod_mor Q fQ_
}.

Lemma big_prod_mor_unique' `{cC : Category C} {J} {obj : J -> C} {pJ : C} 
  (HI : CategoryBigProd obj pJ) {Q} (fQ_ : forall i, Q ~> obj i) :
  forall (fAB fAB' : Q ~> pJ),
  (forall i, fAB  ∘ p_i i ≃ fQ_ i) ->
  (forall i, fAB' ∘ p_i i ≃ fQ_ i) ->
  fAB ≃ fAB'.
Proof.
  intros.
  rewrite (big_prod_mor_unique Q fQ_) by easy.
  symmetry;
  rewrite (big_prod_mor_unique Q fQ_) by easy.
  easy.
Qed. 

Program Definition category_big_prod_unique `{cC : Category C} {J} {obj : J->C} :
  forall {pJ pJ'} (HI : CategoryBigProd obj pJ) (HI' : CategoryBigProd obj pJ'), 
    Isomorphism pJ pJ' :=
  fun pJ pJ' HI HI' =>
  {|
    forward := HI'.(big_prod_mor) pJ p_i;
    reverse := HI.(big_prod_mor) pJ' p_i;
  |}.
Next Obligation.
  split; eapply (big_prod_mor_unique' _ p_i); rewrite 1?assoc.
  1,3: intros i; rewrite assoc, 2!(big_prod_mor_prop _ _); easy.
  all: intros; rewrite left_unit; easy.
Qed.

Require Import FunctionalExtensionality.

Definition big_prod {J} (obj : J -> Type) := forall (i : J), obj i.

#[export, program] Instance TypBigProd {J} {obj : J -> Type} : 
  CategoryBigProd obj (big_prod obj) := {
  p_i := fun i => fun f => f i;
  big_prod_mor := fun Q fQ_ => fun q => fun i => fQ_ i q;
}.
Next Obligation.
  easy.
Qed.
Next Obligation.
  intros q.
  unfold big_prod in *.
  apply functional_extensionality_dep.
  intros i.
  symmetry.
  apply H.
Qed.



Class CategoryCoproduct `{cC : Category C} (A B : C) (A_B : C) := {
  coprod_obj := A_B;
  iota_A : A ~> A_B;
  iota_B : B ~> A_B;
  coprod_mor : 
    forall (Q : C) (fA : A ~> Q) (fB : B ~> Q), A_B ~> Q;
  coprod_mor_prop: 
    forall (Q : C) (fA : A ~> Q) (fB : B ~> Q),
    iota_A ∘ (coprod_mor Q fA fB) ≃ fA /\
    iota_B ∘ (coprod_mor Q fA fB) ≃ fB;
  coprod_mor_unique : 
    forall (Q : C) (fA : A ~> Q) (fB : B ~> Q) 
    (fAB' : A_B ~> Q), 
    fA ≃ iota_A ∘ fAB' -> fB ≃ iota_B ∘ fAB' -> 
    fAB' ≃ coprod_mor Q fA fB
}.

Lemma coprod_mor_unique' `{cC : Category C} {A B A_B : C} 
  (HAB : CategoryCoproduct A B A_B) {Q} (fA : A ~> Q) (fB : B ~> Q) : 
  forall (fAB fAB' : A_B ~> Q),
  iota_A ∘ fAB ≃ fA  -> iota_B ∘ fAB  ≃ fB -> 
  iota_A ∘ fAB' ≃ fA -> iota_B ∘ fAB' ≃ fB -> 
  fAB ≃ fAB'.
Proof.
  intros.
  rewrite (coprod_mor_unique Q fA fB) by easy.
  symmetry;
  rewrite (coprod_mor_unique Q fA fB) by easy.
  easy.
Qed.

Program Definition category_coproduct_unique `{cC : Category C} (A B : C) :
  forall {A_B A_B'} (HA_B : CategoryCoproduct A B A_B) 
  (HA_B' : CategoryCoproduct A B A_B'), Isomorphism A_B A_B' :=
  fun A_B A_B' HA_B HA_B' =>
  {|
    forward := HA_B.(coprod_mor) A_B' iota_A iota_B;
    reverse := HA_B'.(coprod_mor) A_B iota_A iota_B;
  |}.
Next Obligation.
  split; eapply (coprod_mor_unique' _ iota_A iota_B); rewrite <- 1?assoc.
  1,5: rewrite 2!(proj1 (coprod_mor_prop _ _ _)); easy.
  1,4: rewrite 2!(proj2 (coprod_mor_prop _ _ _)); easy.
  all: rewrite right_unit; easy.
Qed.

Class CategoryBigCoprod `{cC : Category C} {J : Type} 
  (obj : J -> C) (coprod_J : C) := {
  big_coprod_obj := coprod_J;
  iota_i : forall i, obj i ~> coprod_J;
  big_coprod_mor : 
    forall (Q : C) (fQ_ : forall i, obj i ~> Q), coprod_J ~> Q;
  big_coprod_mor_prop: 
    forall (Q : C) (fQ_ : forall i, obj i ~> Q),
    forall i, 
    iota_i i ∘ (big_coprod_mor Q fQ_) ≃ fQ_ i;
  big_coprod_mor_unique : 
    forall (Q : C) (fQ_ : forall i, obj i ~> Q)
    (fAB' : coprod_J ~> Q), 
    (forall i, fQ_ i ≃ iota_i i ∘ fAB') ->
    fAB' ≃ big_coprod_mor Q fQ_
}.

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
  easy.
Qed.
Next Obligation.
  intros [i ai].
  rewrite H.
  easy.
Qed.

Reserved Notation "A ∏ B" (at level 40).
Reserved Notation "f @∏ g" (at level 40).

Class Category_with_Products {C} (cC : Category C) := {
  cat_prod : C -> C -> C
    where "A ∏ B" := (cat_prod A B);
  cat_prod_product : forall {A B}, CategoryProduct A B (A ∏ B);
  cat_mor_prod : 
    forall {A A' B B'} (fA : A ~> B) (fB : A' ~> B'), 
      A ∏ A' ~> B ∏ B' := fun A A' B B' fA fB =>
      cat_prod_product.(prod_mor) 
        (A ∏ A') (p_A ∘ fA) (p_B ∘ fB)
    where "f @∏ g" := (cat_mor_prod f g);
}.

Notation "A ∏ B" := (cat_prod A B) (at level 40).
Notation "f @∏ g" := (cat_mor_prod f g) (at level 40).

#[program, export] Instance Category_with_Products_of_CartesianMonoidalCategory {C cC mC}
  (ccc : @CartesianMonoidalCategory C cC mC) : Category_with_Products cC := {|
  cat_prod := mC.(tensor).(obj_bimap);
  cat_prod_product := tensor_cartesian;
|}.

Coercion Category_with_Products_of_CartesianMonoidalCategory :
  CartesianMonoidalCategory >-> Category_with_Products.


Reserved Notation "'λ' g" (at level 20).
Class CategoryExponential `{cC : Category C} {pC : Category_with_Products cC}
  (A B A_B : C) := {
  exp_obj := A_B;
  eval_mor : A_B ∏ B ~> A;
  eval_mor_transpose : forall {M : C} (f : M ∏ B ~> A), 
    M ~> A_B
    where "'λ' g" := (eval_mor_transpose g);
  eval_mor_transpose_prop : forall (M : C) (f : M ∏ B ~> A),
    f ≃ (λ f @∏ id_ B) ∘ eval_mor;
  eval_mor_transpose_unique : forall (M : C) (f : M ∏ B ~> A)
    (lf' : M ~> A_B), f ≃ (lf' @∏ id_ B) ∘ eval_mor -> λ f ≃ lf';
}.


#[program, export] Instance TypExponential {A B : Type} :
  CategoryExponential A B (B -> A) := {
  eval_mor := fun fb => let (f, b) := fb in f b;
  eval_mor_transpose := fun M f => fun m b => f (m, b);
}.
Next Obligation.
  solve_functions.
Qed.
Next Obligation.
  intros i.
  apply functional_extensionality.
  intros b.
  rewrite H.
  easy.
Qed.


Class Cone {C D} {cC : Category C} {cD : Category D} 
  (F : Functor cD cC) := {
  cone_obj : C;
  cone_mor : forall (d : D), cone_obj ~> F d;
  cone_mor_prop : forall {d d' : D} (f : d ~> d'),
    cone_mor d ∘ F @ f ≃ cone_mor d';
}.

Coercion cone_mor : Cone >-> Funclass.

Reserved Notation "'lim' F" (at level 30).

Class Limit {C D} {cC : Category C} {cD : Category D} 
  (F : Functor cD cC) := {
  limit_cone : Cone F;
  limit_cone_factor :
    forall (N : Cone F), N.(cone_obj) ~> limit_cone.(cone_obj);
  limit_cone_factor_prop : forall (N : Cone F) (d : D),
    limit_cone_factor N ∘ limit_cone d ≃ N d;
  limit_cone_factor_unique : forall (N : Cone F) 
    (f' : N.(cone_obj) ~> limit_cone.(cone_obj)),
    (forall (d : D), f' ∘ limit_cone d ≃ N d) -> f' ≃ limit_cone_factor N;
}.

Lemma limit_cone_factor_unique' {C D} {cC : Category C} {cD : Category D} 
  {F : Functor cD cC} (L : Limit F) : forall (N : Cone F) 
  (f f' : N.(cone_obj) ~> L.(limit_cone).(cone_obj)),
  (forall (d : D), f ∘ limit_cone d ≃ N d) -> 
  (forall (d : D), f' ∘ limit_cone d ≃ N d) -> 
  f ≃ f'.
Proof.
  intros.
  rewrite limit_cone_factor_unique by easy.
  symmetry.
  rewrite limit_cone_factor_unique by easy.
  easy.
Qed.

Coercion limit_cone : Limit >-> Cone.

Notation "'lim' F" := (limit_cone (F:=F)).(cone_obj) (at level 30).

#[program] Definition limit_unique {C D} {cC : Category C} {cD : Category D} 
  {F : Functor cD cC} (L L' : Limit F) : L.(cone_obj) <~> L'.(cone_obj) := {|
    forward := L'.(limit_cone_factor) L;
    reverse := L.(limit_cone_factor) L'
  |}.
Next Obligation.
  split; (apply limit_cone_factor_unique'; 
    [| intros; rewrite left_unit; easy]);
  intros; rewrite assoc, 2!limit_cone_factor_prop; easy.
Qed.


Class Cocone {C D} {cC : Category C} {cD : Category D} 
  (F : Functor cD cC) := {
  cocone_obj : C;
  cocone_mor : forall (d : D), F d ~> cocone_obj;
  cocone_mor_prop : forall {d d' : D} (f : d ~> d'),
    F @ f ∘ cocone_mor d' ≃ cocone_mor d;
}.

Coercion cocone_mor : Cocone >-> Funclass.

Reserved Notation "'colim' F" (at level 30).

Class Colimit {C D} {cC : Category C} {cD : Category D} 
  (F : Functor cD cC) := {
  colimit_cocone : Cocone F;
  colimit_cocone_factor : forall (N : Cocone F), 
    colimit_cocone.(cocone_obj) ~> N.(cocone_obj);
  colimit_cocone_factor_prop : forall (N : Cocone F) (d : D),
    colimit_cocone d ∘ colimit_cocone_factor N ≃ N d;
  colimit_cocone_factor_unique : forall (N : Cocone F) 
    (f' : colimit_cocone.(cocone_obj) ~> N.(cocone_obj)),
      (forall (d : D), colimit_cocone d ∘ f' ≃ N d) -> 
      f' ≃ colimit_cocone_factor N;
}.

Lemma colimit_cocone_factor_unique' {C D} {cC : Category C} {cD : Category D} 
  {F : Functor cD cC} (L : Colimit F) : forall (N : Cocone F) 
  (f f' : L.(colimit_cocone).(cocone_obj) ~> N.(cocone_obj)),
  (forall (d : D), colimit_cocone d ∘ f ≃ N d) -> 
  (forall (d : D), colimit_cocone d ∘ f' ≃ N d) -> 
  f ≃ f'.
Proof.
  intros.
  rewrite colimit_cocone_factor_unique by easy.
  symmetry.
  rewrite colimit_cocone_factor_unique by easy.
  easy.
Qed.

Coercion colimit_cocone : Colimit >-> Cocone.

Notation "'colim' F" := (colimit_cocone (F:=F)).(cocone_obj) (at level 30).

#[program] Definition colimit_unique {C D} {cC : Category C} {cD : Category D} 
  {F : Functor cD cC} (L L' : Colimit F) : L.(cocone_obj) <~> L'.(cocone_obj) := {|
    forward := L.(colimit_cocone_factor) L';
    reverse := L'.(colimit_cocone_factor) L
  |}.
Next Obligation.
  split; (apply colimit_cocone_factor_unique'; 
    [| intros; rewrite right_unit; easy]);
  intros; rewrite <- assoc, 2!colimit_cocone_factor_prop; easy.
Qed.


Class Category_with_Small_Limits {C} (cC : Category C) := {
  take_set_limit : forall {D : Set} (cD : Category D) (F : Functor cD cC), Limit F;
}.

Class Category_with_Limits {C} (cC : Category C) := {
  take_limit : forall {D : Type} (cD : Category D) (F : Functor cD cC), Limit F;
}.

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

Require Import Eqdep.

#[export, program] Instance TypLimit {D} {cD : Category D} (F : Functor cD Typ) 
  : Limit F := {
  limit_cone := TypLimitCone F;
}.
Next Obligation.
  exists (fun d => N.(cone_mor) d X).
  intros d d' f.
  apply N.
Defined.
Next Obligation.
  easy.
Qed.
Next Obligation.
  intros c.
  unfold TypLimit_obligation_1.
  destruct (f' c) as [s' P'] eqn:e.
  match goal with
  |- exist _ ?s ?P = exist _ ?s' ?P' => assert (Hs: s = s')
  end.
  - apply functional_extensionality_dep.
    intros d.
    specialize (H d c).
    rewrite <- H.
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


    



