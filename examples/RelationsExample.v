Require Import Setoid.
Require Import Logic.
Require Import Basics.
From ViCaR Require Export CategoryTypeclass.
From ViCaR Require Import RigCategory.


Definition reln (A B : Type) : Type := A -> B -> Prop.

Definition compose_relns {A B C : Type} (f : reln A B) (g : reln B C) : reln A C 
  := fun a c => exists b, f a b /\ g b c.

Definition idn {A : Type} : reln A A :=
  fun i j => i = j.

Local Notation "f '\o' g" := (compose_relns f g) 
  (at level 45, left associativity).

Local Notation "f ~ g" := (forall a b, f a b <-> g a b) 
  (at level 80, no associativity).

Definition reln_equiv {A B : Type} (f g : reln A B) := 
  f ~ g.

Local Notation "⊤" := Datatypes.unit.
Local Notation "⊥" := Datatypes.Empty_set.

Definition reln_sum {A B A' B' : Type} (f : reln A B) (g : reln A' B') :
  reln (A + A') (B + B') :=
  fun i j =>
  match i, j with
  | inl a, inl b => f a b
  | inr a', inr b' => g a' b'
  | _, _ => False
  end.

Local Notation "f '\+' g" := (reln_sum f g) (at level 43, left associativity).

Definition reln_prod {A B A' B' : Type} (f : reln A B) (g : reln A' B') :
  reln (A * A') (B * B') :=
  fun i j =>
  match i, j with
  | (a, a'), (b, b') => f a b /\ g a' b'
  end.

Local Notation "f '\*' g" := (reln_prod f g) (at level 41, left associativity).

Definition reln_unit {A} : reln ⊤ (A*A) :=
  fun i j =>
  match j with
  | (a, b) => a = b
  end.




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

Ltac __saturate_relns Hf :=
  match type of Hf with ?f ?i ?j =>
  repeat match goal with
  | H : f ~ ?g |- _ => 
    let Hg := constr:(proj1 (H i j) Hf) in
      extend Hg; __saturate_relns Hg
  | H : ?g ~ f |- _ => 
    let Hg := constr:(proj2 (H i j) Hf) in
      extend Hg; __saturate_relns Hg
  end
end.

Ltac __solve_relations_end_forward := 
  repeat match goal with
  | H : ?f ?i ?j |- _ => match type of f with reln ?A ?B =>
      revert H
      end
  end;
  repeat (let Hf := fresh "Hf" in intros Hf;
    __saturate_relns Hf);
  easy.

(* Begin tactics *)
Ltac __solve_relations_end := 
  try eassumption;
  try reflexivity;
  try easy;
  auto;  
  try (match goal with
  | |- ?f ?x ?y => match type of f with reln ?n ?m => eassumption end
  (* | H : ?A ?i ?j |- ?A ?i' ?j' =>
    match type of A with 
    | reln ?n ?m => 
      (eapply H || ( idtac "needed rewrite";
      replace i' with i by auto; replace j' with j by auto; eapply H))
    end *)
  | H : ?A ~ ?A' |- ?A ?i ?j => 
    (apply H; clear H; solve __solve_relations_end) 
    || (clear H; solve __solve_relations_end)
  | H : ?A ~ ?A' |- ?A' ?i ?j => 
    (apply H; clear H; solve __solve_relations_end)
    || (clear H; solve __solve_relations_end)
  end || idtac (* " no match" *)).


Ltac solve_relations := idtac. (* Hack to allow "mutual recursion" *)

Ltac __setup_solve_relations :=
  simpl; unfold unitary; simpl;
  unfold compose_relns, reln_equiv, idn, reln_sum, 
    reln_prod, reln_unit, flip in *;
  simpl.

Ltac __solve_relations_mid_step := 
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


Ltac __process_solve_relations_cleanup_vars :=
  repeat match goal with
  | a : ?A * ?B |- _ => destruct a
  | a : ⊤ |- _ => destruct a
  | a : ?A + ?B |- _ => destruct a
  end.

Ltac __process_solve_relations_step :=
  __process_solve_relations_cleanup_vars;
  try easy;
  match goal with
  | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
  | H : @eq (_ + _) _ _ |- _ => inversion H; subst; clear H

  | H : (exists _, _) |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | |- _ <-> _ => split
  | |- _ /\ _ => split
  | H : _ \/ _ |- _ => destruct H; [solve_relations | solve_relations]
  | |- _ \/ _ => 
       (left; solve [solve_relations; auto]) 
    || (right; solve [solve_relations; auto]) 
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
          exists x; (* idtac "yes" x; *) (solve [solve_relations; auto])
        end; match goal with
        | |- _ => (* idtac "none worked"; *) eexists
      end
    end
  end.

Ltac __process_solve_relations := 
  repeat (
  __solve_relations_mid_step;
  __process_solve_relations_step).

Ltac solve_relations ::= 
  __setup_solve_relations;
  __process_solve_relations;
  __solve_relations_mid_step;
  __solve_relations_end || __solve_relations_end_forward.
(* End tactics *)

Lemma reln_equiv_refl {A B : Type} (f : reln A B) :
  f ~ f.
Proof. easy. Qed.

Lemma reln_equiv_sym {A B : Type} (f g : reln A B) :
  f ~ g -> g ~ f.
Proof. easy. Qed.

Lemma reln_equiv_trans {A B : Type} (f g h : reln A B) :
  f ~ g -> g ~ h -> f ~ h.
Proof. solve_relations. Qed.

Lemma reln_equiv_equivalence (A B : Type) : 
  equivalence (reln A B) (@reln_equiv A B).
Proof.
  unfold reln_equiv. split.
  - intros ?; apply reln_equiv_refl.
  - intros ?; apply reln_equiv_trans.
  - intros ?; apply reln_equiv_sym.
Qed.


Lemma compose_relns_assoc {A B C D : Type} : forall
  (f : reln A B) (g : reln B C) (h : reln C D), 
  f \o g \o h ~ f \o (g \o h).
Proof.
  solve_relations.
Qed.

Lemma compose_idn_l {A B} (f : reln A B) :
  idn \o f ~ f.
Proof. solve_relations. Qed.

Lemma compose_idn_r {A B} (f : reln A B) :
  f \o idn ~ f.
Proof. solve_relations. Qed.

Lemma compose_relns_compat {A B C : Type} : forall (f f' : reln A B),
  f ~ f' -> forall (g g' : reln B C), g ~ g' -> 
  f \o g ~ f' \o g'.
Proof.
  solve_relations.
Qed.

#[export] Instance Rel : Category Type := {
  morphism := reln;
  c_equiv := @reln_equiv;
  c_equiv_rel := reln_equiv_equivalence;
  compose := @compose_relns;
  compose_compat := @compose_relns_compat;
  assoc := @compose_relns_assoc;
  c_identity := @idn;
  left_unit := @compose_idn_l;
  right_unit := @compose_idn_r;
}.

Lemma prod_idn {A B} : 
  idn \* idn ~ @idn (A*B).
Proof.
  solve_relations.
Qed.

Lemma prod_compose {A B C A' B' C'} : 
  forall (f : reln A B) (g : reln B C) (f' : reln A' B') (g' : reln B' C'),
  (f \o g) \* (f' \o g') ~ f \* f' \o g \* g'.
Proof.
  solve_relations.
Qed.

Lemma prod_compat {A B C D} :
  forall (f f' : reln A B) (g g' : reln C D),
  f ~ f' -> g ~ g' ->
  f \* g ~ f' \* g'.
Proof.
  solve_relations.
Qed.

#[export] Instance ProductRelation : Bifunctor Rel Rel Rel := {
  obj_bimap := prod;
  morphism_bimap := @reln_prod;
  id_bimap := @prod_idn;
  compose_bimap := @prod_compose;
  morphism_bicompat := @prod_compat;
}.

#[export] Instance RelAssociator {A B C : Type} : 
  Isomorphism (A * B * C) (A * (B * C)) := {
  forward := fun ab_c a_bc =>
    match ab_c with ((a, b), c) => 
    match a_bc with (a',(b',c')) =>
      a = a' /\ b = b' /\ c = c'
    end end;
  reverse := fun a_bc ab_c =>
    match ab_c with ((a, b), c) => 
    match a_bc with (a',(b',c')) =>
      a = a' /\ b = b' /\ c = c'
    end end;
  isomorphism_inverse := ltac:(abstract(solve_relations));
}.

(* Set Printing Universes. *)

#[export] Instance RelLeftUnitor {A : Type} :
  @Isomorphism Type Rel (⊤ * A) (A) := {
  forward := fun topa b => match topa with (_, a) => a = b end;
  reverse := fun a topb => match topb with (_, b) => a = b end;
  isomorphism_inverse := ltac:(abstract(solve_relations))
}.

#[export] Instance RelRightUnitor {A : Type} :
  @Isomorphism Type Rel (A * ⊤) (A) := {
  forward := fun atop b => match atop with (a, _) => a = b end;
  reverse := fun a btop => match btop with (b, _) => a = b end;
  isomorphism_inverse := ltac:(abstract(solve_relations))
}.

#[export] Instance RelMonoidal : MonoidalCategory Type | 0 := {
  tensor := ProductRelation;
	I := ⊤;
  associator := @RelAssociator;
  left_unitor := @RelLeftUnitor;
  right_unitor := @RelRightUnitor;
  associator_cohere := ltac:(abstract(solve_relations));
  left_unitor_cohere := ltac:(abstract(solve_relations));
  right_unitor_cohere := ltac:(abstract(solve_relations));
  triangle := ltac:(abstract(solve_relations));
  pentagon := ltac:(abstract(solve_relations));
}.

#[export] Instance RelBraidingIsomorphism {A B} : 
  Isomorphism (A * B) (B * A) := {
  forward := fun ab ba' => match ab with (a, b) => match ba' with (b', a') =>
    a = a' /\ b = b'
    end end;
  reverse := fun ba ab' => match ba with (b, a) => match ab' with (a', b') => 
    a = a' /\ b = b'
    end end;
  isomorphism_inverse := ltac:(abstract(solve_relations))
}.

#[export] Instance RelBraiding : 
  NaturalBiIsomorphism ProductRelation (CommuteBifunctor ProductRelation) := {
  component_biiso := @RelBraidingIsomorphism;
  component_biiso_natural := ltac:(abstract(solve_relations))
}.

#[export] Instance RelBraidedMonoidal : BraidedMonoidalCategory Type | 0 := {
  braiding := RelBraiding;
  hexagon_1 := ltac:(abstract(solve_relations));
  hexagon_2 := ltac:(abstract(solve_relations));
}.

#[export] Instance RelSymmetricMonoidal : 
  SymmetricMonoidalCategory Type | 0 := {
  symmetry := ltac:(abstract(solve_relations));
}.

#[export] Instance RelCompactClosed : CompactClosedCategory Type := {
  dual := fun A => A;
  unit := @reln_unit;
  counit := fun A => flip reln_unit;
  triangle_1 := ltac:(abstract(solve_relations));
  triangle_2 := ltac:(abstract(solve_relations));
}.

#[export] Instance RelDagger : DaggerCategory Type := {
  adjoint := fun A B => @flip A B Prop;
  adjoint_involutive := ltac:(easy);
  adjoint_id := ltac:(easy);
  adjoint_contravariant := ltac:(abstract(solve_relations));
  adjoint_compat := ltac:(abstract(solve_relations));
}.

#[export] Instance RelDaggerMonoidal : DaggerMonoidalCategory Type := {
  dagger_tensor_compat := ltac:(abstract(solve_relations));
  associator_unitary := ltac:(abstract(solve_relations));
  left_unitor_unitary := ltac:(abstract(solve_relations));
  right_unitor_unitary := ltac:(abstract(solve_relations));
}.





Lemma sum_idn {A B} : 
  idn \+ idn ~ @idn (A + B).
Proof. solve_relations. Qed.

Lemma sum_compose {A B C A' B' C'} : 
  forall (f : reln A B) (g : reln B C) (f' : reln A' B') (g' : reln B' C'),
  (f \o g) \+ (f' \o g') ~ f \+ f' \o g \+ g'.
Proof.
  solve_relations.
Qed.
  
#[export] Instance SumRelation : Bifunctor Rel Rel Rel := {
  obj_bimap := sum;
  morphism_bimap := @reln_sum;
  id_bimap := @sum_idn;
  compose_bimap := @sum_compose;
  morphism_bicompat := ltac:(abstract(solve_relations));
}.

#[export] Instance RelSumAssociator {A B C : Type} : 
  Isomorphism (A + B + C) (A + (B + C)) := {
  forward := fun ab_c a_bc =>
    match ab_c, a_bc with 
    | inl (inl a), inl a' => a = a'
    | inl (inr b), inr (inl b') => b = b'
    | inr c, inr (inr c') => c = c'
    | _, _ => False
    end;
  reverse := fun a_bc ab_c =>
    match ab_c, a_bc with 
    | inl (inl a), inl a' => a = a'
    | inl (inr b), inr (inl b') => b = b'
    | inr c, inr (inr c') => c = c'
    | _, _ => False
    end;
  isomorphism_inverse := ltac:(abstract(solve_relations));
}.


#[export] Instance RelSumLeftUnitor {A : Type} :
  @Isomorphism Type Rel (⊥ + A) (A) := {
  forward := fun bota b => match bota with
    | inr a => a = b
    | _ => False 
    end;
  reverse := fun a botb => match botb with 
    | inr b => a = b 
    | _ => False end;
  isomorphism_inverse := ltac:(abstract(solve_relations))
}.

#[export] Instance RelSumRightUnitor {A : Type} :
  @Isomorphism Type Rel (A + ⊥) (A) := {
  forward := fun bota b => match bota with
    | inl a => a = b
    | _ => False 
    end;
  reverse := fun a botb => match botb with 
    | inl b => a = b 
    | _ => False end;
  isomorphism_inverse := ltac:(abstract(solve_relations))
}.

#[export] Instance RelSumMonoidal : MonoidalCategory Type | 10 := {
  tensor := SumRelation;
	I := ⊥;
  associator := @RelSumAssociator;
  left_unitor := @RelSumLeftUnitor;
  right_unitor := @RelSumRightUnitor;
  associator_cohere := ltac:(abstract(solve_relations));
  left_unitor_cohere := ltac:(abstract(solve_relations));
  right_unitor_cohere := ltac:(abstract(solve_relations));
  triangle := ltac:(abstract(solve_relations));
  pentagon := ltac:(abstract(solve_relations));
}.

#[export] Instance RelSumBraidingIsomorphism {A B} : 
  Isomorphism (A + B) (B + A) := {
  forward := fun ab ba' => 
    match ab, ba' with
    | inl a, inr a' => a = a'
    | inr b, inl b' => b = b'
    | _, _ => False
    end;
  reverse := fun ba ab' => 
    match ba, ab' with
    | inr a, inl a' => a = a'
    | inl b, inr b' => b = b'
    | _, _ => False
    end;
  isomorphism_inverse := ltac:(abstract(solve_relations))
}.

#[export] Instance RelSumBraiding : 
  NaturalBiIsomorphism SumRelation (CommuteBifunctor SumRelation) := {
  component_biiso := @RelSumBraidingIsomorphism;
  component_biiso_natural := ltac:(abstract(solve_relations))
}.

#[export] Instance RelSumBraidedMonoidal : 
  @BraidedMonoidalCategory Type Rel RelSumMonoidal | 10 := {
  braiding := RelSumBraiding;
  hexagon_1 := ltac:(abstract(solve_relations));
  hexagon_2 := ltac:(abstract(solve_relations));
}.

#[export] Instance RelSumSymmetricMonoidal : 
  @SymmetricMonoidalCategory Type Rel RelSumMonoidal
  RelSumBraidedMonoidal | 10 := {
  symmetry := ltac:(abstract(solve_relations));
}.

Lemma not_RelSumCompactClosed :
  @CompactClosedCategory Type Rel RelSumMonoidal 
  RelSumBraidedMonoidal RelSumSymmetricMonoidal -> False.
Proof.
  intros [].
  pose proof (triangle_1 ⊤) as Hfalse.
  simpl in Hfalse.
  specialize (Hfalse tt tt).
  specialize (proj2 Hfalse eq_refl).
  clear Hfalse.
  solve_relations.
Qed.

#[export] Instance RelSumDagger : DaggerCategory Type | 10 := {
  adjoint := fun A B => @flip A B Prop;
  adjoint_involutive := ltac:(easy);
  adjoint_id := ltac:(easy);
  adjoint_contravariant := ltac:(abstract(solve_relations));
  adjoint_compat := ltac:(abstract(solve_relations));
}.

#[export] Instance RelSumDaggerMonoidal : DaggerMonoidalCategory Type | 10 := {
  dagger_tensor_compat := ltac:(abstract(solve_relations));
  associator_unitary := ltac:(abstract(solve_relations));
  left_unitor_unitary := ltac:(abstract(solve_relations));
  right_unitor_unitary := ltac:(abstract(solve_relations));
}.

#[export] Instance RelLeftDistributivityIsomorphism (A B M : Type) :
  @Isomorphism Type Rel (A * (B + M))
  ((A * B) + (A * M)) := {
  forward := fun abm abam => match abm, abam with
    | (a, inl b), inl (a', b') => a = a' /\ b = b'
    | (a, inr m), inr (a', m') => a = a' /\ m = m'
    | _, _ => False
    end;
  reverse := fun abam abm => match abm, abam with
    | (a, inl b), inl (a', b') => a = a' /\ b = b'
    | (a, inr m), inr (a', m') => a = a' /\ m = m'
    | _, _ => False
    end;
  isomorphism_inverse := ltac:(abstract(solve_relations));
}.

#[export] Instance RelRightDistributivityIsomorphism (A B M : Type) :
  @Isomorphism Type Rel ((A + B) * M)
  ((A * M) + (B * M)) := {
  forward := fun abm ambm => match abm, ambm with
    | (inl a, m), inl (a', m') => a = a' /\ m = m'
    | (inr b, m), inr (b', m') => b = b' /\ m = m'
    | _, _ => False
    end;
  reverse := fun ambm abm => match abm, ambm with
    | (inl a, m), inl (a', m') => a = a' /\ m = m'
    | (inr b, m), inr (b', m') => b = b' /\ m = m'
    | _, _ => False
    end;
  isomorphism_inverse := ltac:(abstract(solve_relations));
}.

Lemma rel_left_distributivity_isomorphism_natural {A B M A' B' M' : Type}
  (f : reln A A') (g : reln B B') (h : reln M M') :
  (RelLeftDistributivityIsomorphism A B M
  ∘ (reln_sum (reln_prod f g) (reln_prod f h))
  ≃ reln_prod f (reln_sum g h)
	∘ RelLeftDistributivityIsomorphism A' B' M')%Cat.
Proof.
  solve_relations.
Qed.

Lemma rel_right_distributivity_isomorphism_natural {A B M A' B' M' : Type}
  (f : reln A A') (g : reln B B') (h : reln M M') :
  (RelRightDistributivityIsomorphism A B M
  ∘ (reln_sum (reln_prod f h) (reln_prod g h))
  ≃ reln_prod (reln_sum f g) h
	∘ RelRightDistributivityIsomorphism A' B' M')%Cat.
Proof.
  solve_relations.
Qed.

#[export] Instance RelLeftAbsorbtion (A : Type) :
  (⊥ * A <~> ⊥)%Cat := {
  forward := fun bota => match bota with | (bot, a) => match bot with end end;
  reverse := fun bot => match bot with end;
  isomorphism_inverse := ltac:(abstract(solve_relations));
}.

#[export] Instance RelRightAbsorbtion (A : Type) :
  (A * ⊥ <~> ⊥)%Cat := {
  forward := fun abot => match abot with | (a, bot) => match bot with end end;
  reverse := fun bot => match bot with end;
  isomorphism_inverse := ltac:(abstract(solve_relations));
}.

#[export] Instance RelPreDistr : 
  PreDistributiveBimonoidalCategory RelSumSymmetricMonoidal
  RelMonoidal := {
    left_distr_iso := RelLeftDistributivityIsomorphism;
    right_distr_iso := RelRightDistributivityIsomorphism;
    left_distr_natural := @rel_left_distributivity_isomorphism_natural;
    right_distr_natural := @rel_right_distributivity_isomorphism_natural;
}.

#[export] Instance RelDistrBimonoidal : 
  DistributiveBimonoidalCategory RelSumSymmetricMonoidal RelMonoidal := {
  left_absorbtion_iso := RelLeftAbsorbtion;
  right_absorbtion_iso := RelRightAbsorbtion;
  left_absorbtion_natural := ltac:(abstract(solve_relations));
  right_absorbtion_natural := ltac:(abstract(solve_relations));
}.

(* #[export] Instance RelSemiCoherent :
  SemiCoherent_DistributiveBimonoidalCategory RelDistrBimonoidal := {
  condition_I (A B C : Type) := ltac:(abstract(solve_relations));
  condition_III (A B C : Type) := ltac:(abstract(solve_relations));
  condition_IV (A B C D : Type) := ltac:(abstract(solve_relations));
  condition_V (A B C D : Type) := ltac:(abstract(solve_relations));
  condition_VI (A B C D : Type) := ltac:(abstract(solve_relations));
  condition_VII (A B C D : Type) := ltac:(abstract(solve_relations));
  condition_VIII (A B C D : Type) := ltac:(abstract(solve_relations));
  condition_IX  (A B C D : Type) := ltac:(abstract(solve_relations));
  condition_X := ltac:(abstract(solve_relations));
  condition_XI (A B : Type) := ltac:(abstract(solve_relations));
  condition_XII (A B : Type) := ltac:(abstract(solve_relations));
  condition_XIII := ltac:(abstract(solve_relations));
  condition_XIV := ltac:(abstract(solve_relations));
  condition_XVI (A B : Type) := ltac:(abstract(solve_relations));
  condition_XVII (A B : Type) := ltac:(abstract(solve_relations));
  condition_XVIII (A B : Type) := ltac:(abstract(solve_relations));
  condition_XIX (A B : Type) := ltac:(abstract(solve_relations));
  condition_XX (A B : Type) := ltac:(abstract(solve_relations));
  condition_XXI (A B : Type) := ltac:(abstract(solve_relations));
  condition_XXII (A B : Type) := ltac:(abstract(solve_relations));
  condition_XXIII (A B : Type) := ltac:(abstract(solve_relations));
  condition_XXIV (A B : Type) := ltac:(abstract(solve_relations));
}. *)

#[export] Instance RelSemiCoherentBraided :
  SemiCoherent_BraidedDistributiveBimonoidalCategory RelDistrBimonoidal RelBraidedMonoidal := {
  condition_II (A B C : Type) := ltac:(abstract(solve_relations));
  condition_XV (A : Type) := ltac:(abstract(solve_relations));
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
    CategoryProduct A B (A × B);
}.

#[export, program] Instance RelCartesianMonoidalCategory :
  CartesianMonoidalCategory RelSumMonoidal := {
    tensor_cartesian := fun A B => {| 
      p_A := fun ab a => match ab with | inl a' => a = a' | _ => False end;
      p_B := fun ab b => match ab with | inr b' => b = b' | _ => False end;
      prod_mor := fun Q fA fB =>
        fun q ab => match ab with
        | inl a => fA q a
        | inr b => fB q b
        end
    |}
  }.
Obligation 4. (* Only uniqueness can't be (fully) automated *)
  __setup_solve_relations.
  intros q [a | b].
  - rewrite H.
    solve_relations.
  - rewrite H0.
    solve_relations.
Qed.
Solve All Obligations with solve_relations.

Module BigPredProd.
Class CategoryBigProd `{cC : Category C} (I : C -> Prop) (prod_I : C) := {
  p_i : forall i, I i -> prod_I ~> i;
  big_prod_mor : 
    forall (Q : C) (fQ_ : forall i, I i -> Q ~> i), Q ~> prod_I;
  big_prod_mor_prop: 
    forall (Q : C) (fQ_ : forall i, I i -> Q ~> i),
    forall i (Hi : I i), 
    (big_prod_mor Q fQ_) ∘ p_i i Hi ≃ fQ_ i Hi;
  big_prod_mor_unique : 
    forall (Q : C) (fQ_ : forall i, I i -> Q ~> i)
    (fAB' : Q ~> prod_I), 
    (forall i (Hi : I i), fQ_ i Hi ≃ fAB' ∘ p_i i Hi) ->
    fAB' ≃ big_prod_mor Q fQ_
}.

Lemma big_prod_mor_unique' `{cC : Category C} {I} {pI : C} 
  (HI : CategoryBigProd I pI) {Q} (fQ_ : forall i, I i -> Q ~> i) : 
  forall (fAB fAB' : Q ~> pI),
  (forall i (Hi : I i), fAB ∘ p_i i Hi ≃ fQ_ i Hi) ->
  (forall i (Hi : I i), fAB' ∘ p_i i Hi ≃ fQ_ i Hi) ->
  fAB ≃ fAB'.
Proof.
  intros.
  rewrite (big_prod_mor_unique Q fQ_) by easy.
  symmetry;
  rewrite (big_prod_mor_unique Q fQ_) by easy.
  easy.
Qed.

Program Definition category_big_prod_unique `{cC : Category C} I :
  forall {pI pI'} (HI : CategoryBigProd I pI) (HI' : CategoryBigProd I pI'), 
    Isomorphism pI pI' :=
  fun pI pI' HI HI' =>
  {|
    forward := HI'.(big_prod_mor) pI p_i;
    reverse := HI.(big_prod_mor) pI' p_i;
  |}.
Obligations.
Next Obligation.
  split; eapply (big_prod_mor_unique' _ p_i); rewrite 1?assoc.
  1,3: intros i Hi; rewrite assoc, 2!(big_prod_mor_prop _ _); easy.
  all: intros; rewrite left_unit; easy.
Qed.
End BigPredProd.


Class CategoryBigProd `{cC : Category C} {I : Type} 
  (obj : I -> C) (prod_I : C) := {
  p_i : forall i, prod_I ~> obj i;
  big_prod_mor : 
    forall (Q : C) (fQ_ : forall i, Q ~> obj i), Q ~> prod_I;
  big_prod_mor_prop: 
    forall (Q : C) (fQ_ : forall i, Q ~> obj i),
    forall i, 
    (big_prod_mor Q fQ_) ∘ p_i i ≃ fQ_ i;
  big_prod_mor_unique : 
    forall (Q : C) (fQ_ : forall i, Q ~> obj i)
    (fAB' : Q ~> prod_I), 
    (forall i, fQ_ i ≃ fAB' ∘ p_i i) ->
    fAB' ≃ big_prod_mor Q fQ_
}.

Lemma big_prod_mor_unique' `{cC : Category C} {I} {obj : I -> C} {pI : C} 
  (HI : CategoryBigProd obj pI) {Q} (fQ_ : forall i, Q ~> obj i) :
  forall (fAB fAB' : Q ~> pI),
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

Program Definition category_big_prod_unique `{cC : Category C} {I} {obj : I->C} :
  forall {pI pI'} (HI : CategoryBigProd obj pI) (HI' : CategoryBigProd obj pI'), 
    Isomorphism pI pI' :=
  fun pI pI' HI HI' =>
  {|
    forward := HI'.(big_prod_mor) pI p_i;
    reverse := HI.(big_prod_mor) pI' p_i;
  |}.
Obligations.
Next Obligation.
  split; eapply (big_prod_mor_unique' _ p_i); rewrite 1?assoc.
  1,3: intros i; rewrite assoc, 2!(big_prod_mor_prop _ _); easy.
  all: intros; rewrite left_unit; easy.
Qed.


Inductive big_sum (I : Type -> Type) :=
  | in_i i (a : I i) : big_sum I.

Arguments in_i {_} _ _.
(* Set Printing Universes. *)

Definition my_f_equal [A B : Type] (f : A -> B) [x y : A] (H : x = y) :
  f x = f y := 
  match H in (_ = y') return (f x = f y') with eq_refl => eq_refl end.

#[ export, program] Instance RelBigProd (I : Type -> Type) : 
  CategoryBigProd I (big_sum I) := {
    p_i := fun i => fun somei a => match somei with
    | in_i i' a' => exists (H: i = i'), _
      (* let Hi := my_f_equal I H in
        match Hi in (_ = Ii') return Ii' with eq_refl => a end = a' *)
    end;
    big_prod_mor := fun Q fQ_ => fun q somei => match somei with
    | in_i i a => fQ_ i q a
    end

  }.
Next Obligation.
  exact (a = a').
Defined.
Next Obligation.
  __setup_solve_relations.
  intros q a.
  split.
  - intros [[i' a'] [HfQi'a' [Hi Ha]]].
    subst.
    rewrite Ha.
    easy.
  - intros H.
    exists (in_i i a).
    split; [easy|].
    exists eq_refl.
    reflexivity.
Qed.
Next Obligation.
  __setup_solve_relations.

  intros q [i a].
  rewrite H.
  split.
  - intros Ha.
    exists (in_i i a).
    split; [| exists eq_refl]; easy.
  - intros [[i' a'] [HfQi'a' [Hi Ha]]].
    subst.
    rewrite Ha.
    easy.
Qed.


Section TransitiveClosure.

Local Open Scope Rig_scope.

(* Definition encup {A A' B : Type} (R : reln (A + B) (A' + B)) : reln (A + ⊤) _ (*  (A' + ⊤) *) :=
  (id_ A ⊞ reln_unit) ∘ (α'_ A, B, B ∘ (R ⊞ id_ B) ∘ associator ∘ (id_ A ⊞ unit †). *)



(* Definition dec_and_R {A : Type} (R : reln A A) : reln (A * nat) (A * nat) :=
  fun an bm =>
    let (a, n) := an in let (b, m) := bm in 
    R a b /\ (m + 1 = n)%nat. *)
  
(* Definition dec : reln nat nat :=
  fun i j => (i = j + 1)%nat.


Definition if_0 : reln nat (⊤ + nat) :=
  fun i j => match i, j with
  | O, inl _ => True
  | S n', inr m => m = *)

Definition dec_if0 : reln nat (⊤ + nat) :=
  fun i j => match i, j with
  | O, inl _ => True
  | S n', inr m => n' = m
  | _, _ => False
  end.

(* TODO: generalize? *)
Definition REPNZ {A : Type}
  : reln (A * nat) (A + (A * nat)) :=
  (id_ A ⊠ dec_if0) ∘ δ_ A, ⊤, nat ∘ (ρ_ A ⊞ id_ (A * nat)).


(* Note: this is in fact a property of coproducts *)
Definition join_plus {B : Type} : reln (B + B) B :=
  fun b_or_b c => match b_or_b with
  | inl b | inr b => b = c
  end.

(* Note: I _believe_ we can get this with (categorical) sums and products? *)
Definition prod_to_sum {A B : Type} : reln (A*B) (A + B) :=
  fun ab a'_or_b' => match ab, a'_or_b' with
  | (a, _), inl a' => a = a'
  | (_, b), inr b' => b = b'
  end.

Definition repn_top {A : Type} (R : reln A A) 
  : reln (A * nat + A * nat) (A + (A * nat)) :=
  join_plus ∘ REPNZ ∘ (id_ A ⊞ (R ⊠ id_ _)).

(* Actually a property of cartesian category: *)
Definition proj_l {A B : Type} : reln (A * B) A :=
  fun ab a' => let (a, _) := ab in a = a'.

(* Note: quite suspect! Maybe we get it bc we have all trivial morphisms? *)
Definition only_l {A B : Type} : reln (A + B) A :=
  fun a_or_b a' => match a_or_b with
  | inl a => a = a'
  | inr b => False
  end.

(* Q: Given R : A + B ~> A' + B, can we form Rconn : A ~> A'? *)

Definition REPN {A : Type} (R : reln A A) : reln (A * nat) _ := 
  ρ_ _ ^-1 ∘ (id_ _ ⊠ reln_unit) ∘ α_ _, _, _ 
  ∘ ((prod_to_sum ∘ repn_top R) ⊠ id_ _) ∘ δ#_ _, _, _ 
  ∘ (proj_l ⊞ flip reln_unit) ∘ only_l.

Fixpoint compose_n {C} {cC : Category C} (n : nat) 
  {A : C} (f : A ~> A) : A ~> A :=
  match n with 
  | O => id_ A
  | S n' => compose_n n' f ∘ f
  end.

Theorem REPN_correct {A : Type} (R : reln A A) : 
  REPN R ≃ fun an a' => let (a, n) := an in (compose_n n R) a a'.
Proof.
  intros [a n]; revert a.
  induction n.
  - intros a b. simpl.
    unfold REPN. 
    rewrite ?compose_relns_assoc.
    (* repn_top, only_l, proj_l, 
      prod_to_sum, join_plus, REPNZ, dec_if0. *)
    
    split.
    + __setup_solve_relations.
      __process_solve_relations.
      unfold prod_to_sum, repn_top, proj_l, join_plus, REPNZ, only_l in *.
      revert H2;
      __setup_solve_relations.
      solve_relations.

      solve_relations.
      solve_relations.
      __solve_relations_mid_step.
      __process_solve_relations_step; __process_solve_relations_cleanup_vars; [|easy].
      __process_solve_relations_step.
      __process_solve_relations_step; __process_solve_relations_cleanup_vars; [|easy].



    solve_relations.
    




Definition anynat : reln ⊤ nat := 
  fun t n => True.



Definition anynat_alt : reln ⊤ nat :=
  reln_unit ∘ proj_l.

Lemma anynat_alt_correct : anynat ≃ anynat_alt.
Proof.
  unfold anynat, anynat_alt.
  solve_relations.
Qed.


Definition if_0 (A : Type) : reln (A * nat) (A + (A * nat)) :=
  fun an b_or_bm => match an, b_or_bm with
    | (a, O), inl b => a = b
    | (a, S n'), inr (b, m) => a = b /\ S n' = m
    | _, _ => False
    end.

Definition either (B : Type) : reln (B * B) B :=
  fun bb' c => let (b, b') := bb' in 
    b = c \/ b' = c.

Definition transitive_closure_setup {A : Type} (R : reln A A) 
  : reln A ((A * nat) * (A * nat)) :=
  right_unitor ^-1 ∘ (id_ A ⊗ anynat) ∘ right_unitor^-1 
    ∘ (id_ _ ⊗ reln_unit) ∘ associator ^-1 
    ∘ (either _ ⊗ id_ _).

Definition transitive_closure {A : Type} (R : reln A A) : reln A _ :=
  transitive_closure_setup R ∘ (R ⊗ dec ⊗ id_ _) ∘
  (if_0 A ⊗ id_ _) ∘ RelRightDistributivityIsomorphism A (A*nat) (A*nat)
  ∘ (proj_l ⊞ (flip reln_unit ∘ @reln_unit ⊥ ∘ proj_l))%Rig
  ∘ RelSumMonoidal.(right_unitor).(forward).

Require Import Lia.

Ltac __solve_relations_mid_step ::= 
  repeat (intros ?); intros; subst; auto; try lia.

Lemma test_trans_clo : 
  (transitive_closure (fun i j => (i + 1 = j)%nat)) 2 3.
Proof.
  unfold transitive_closure, transitive_closure_setup, either,
    anynat, dec, proj_l, if_0.
  __setup_solve_relations.
  (* straight through, so... *)
  exists (inl 3); split; [|easy].
  eexists (inl (_, (_, _))); split; [|reflexivity].
  eexists ((inl 3, (_, _))); split; [|split; reflexivity].
  eexists ((_, 0), (_, _)); split; [|split].
  eexists ((_, _), (_, _)); split; [|split; [split|]; reflexivity].
  eexists ((_, _), (_, _), (_, _)).
  split; [|split; [|reflexivity]].
  eexists ((_, _), ((_, _), (_, _))).
  split; [|split; [|split]; reflexivity].
  eexists ((_, _), tt).
  split; [|split; reflexivity].
  eexists (_, _).
  split; [|reflexivity].
  eexists (_, tt).
  split; [|split]; reflexivity.
  left.
  all: reflexivity.
  Unshelve. all: constructor.
Qed.

Lemma test_trans_clo_2 : 
  (transitive_closure (fun i j => (i + 1 = j)%nat)) 2 1 -> False.
Proof.
  unfold transitive_closure, transitive_closure_setup, either,
    anynat, dec, proj_l, if_0.
  __setup_solve_relations.
  intros Hbad.
  __process_solve_relations.
  destruct H1.
  destruct n7; [|easy].
  inversion H1.
  lia.
  destruct n7; [|easy].
  
  __process_solve_relations_cleanup_vars.
  (* straight through, so... *)
  eexists (inl _); split; [|easy].
  eexists (inl (_, (_, _))); split; [|reflexivity].
  eexists ((inl 3, (_, _))); split; [|split; reflexivity].
  eexists ((_, 0), (_, _)); split; [|split].
  eexists ((_, _), (_, _)); split; [|split; [split|]; reflexivity].
  eexists ((_, _), (_, _), (_, _)).
  split; [|split; [|reflexivity]].
  eexists ((_, _), ((_, _), (_, _))).
  split; [|split; [|split]; reflexivity].
  eexists ((_, _), tt).
  split; [|split; reflexivity].
  eexists (_, _).
  split; [|reflexivity].
  eexists (_, tt).
  split; [|split]; reflexivity.
  left.
  all: reflexivity.
  Unshelve. all: constructor.
Qed.

Lemma test_trans_clo_2 : 
  (transitive_closure (fun i j => (i + 1 = j)%nat)) 2 4.
Proof.
  unfold transitive_closure, transitive_closure_setup, either, anynat, dec.
  __setup_solve_relations.
  do 2 (eexists ((_, _), (_, _)); split).
  2: split; [split|]; reflexivity.
  eexists ((_, _), (_, _), (_, _)).
  split; [|split; [|reflexivity]].
  eexists ((_, _), ((_, _), (_, _))).
  split; [|split; [|split]; reflexivity].
  eexists ((_, _), tt).
  split; [|split; reflexivity].
  eexists (_, _).
  split; [|reflexivity].
  eexists (_, tt).
  split; [|split]; reflexivity.
  2: {
    eexists ((_, _), ((_, _), (_, _))).
    split; [|split; [|split]; reflexivity].
    eexists ((_, _), tt).
    split; [|split; reflexivity].
    eexists (_, _).
    split; [|reflexivity].
    eexists (_, tt).
    split; [|split]; reflexivity.
  }
  left; reflexivity.
  split; [right|]; reflexivity.
  Unshelve.
  all: constructor.
Qed.

Lemma test_trans_clo_3 : 
  (transitive_closure (fun i j => (i + 1 = j)%nat)) 2 1.
Proof.
  unfold transitive_closure, transitive_closure_setup, either, anynat, dec.
  __setup_solve_relations.
  do 2 (eexists ((_, _), (_, _)); split).
  2: split; [split|]; reflexivity.
  eexists ((_, _), (_, _), (_, _)).
  split; [|split; [|reflexivity]].
  eexists ((_, _), ((_, _), (_, _))).
  split; [|split; [|split]; reflexivity].
  eexists ((_, _), tt).
  split; [|split; reflexivity].
  eexists (_, _).
  split; [|reflexivity].
  eexists (_, tt).
  split; [|split]; reflexivity.
  2: {
    eexists ((_, _), ((_, _), (_, _))).
    split; [|split; [|split]; reflexivity].
    eexists ((_, _), tt).
    split; [|split; reflexivity].
    eexists (_, _).
    split; [|reflexivity].
    eexists (_, tt).
    split; [|split]; reflexivity.
  }
  left; reflexivity.
  split; [right|]; reflexivity.
  Unshelve.
  all: constructor.
Qed.


Definition trans_join (A : Type) : reln (A*A) A :=
  fun ii' j => let (i, i') := ii' in 
    i = j \/ i' = j.

Definition trans_split (A : Type) : reln A (A*A) :=
  fun i jj' => let (j, j') := jj' in i = j /\ i = j'.

Definition trans_clo (A : Type) (R : reln A A) :=
  (@RelRightUnitor A) ^-1 ∘ (RelMonoidal.(tensor) @@ (id_ A), reln_unit) 
    ∘ (associator ^-1) ∘ (RelMonoidal.(tensor) @@ trans_join A, id_ A) 
    ∘ (RelMonoidal.(tensor) @@ R, id_ A) ∘ (RelMonoidal.(tensor) @@ trans_split A, id_ A) 
    ∘ associator ∘ (RelMonoidal.(tensor) @@ id_ A, flip reln_unit) 
    ∘ RelMonoidal.(right_unitor).(forward).

Lemma trans_clo_test : (trans_clo nat (fun i j => (i + 1 = j)%nat)) 2 3.
Proof.
  unfold trans_clo, trans_join, trans_split.
  simpl.
  __setup_solve_relations.
  exists (3, tt).
  split; [|easy].
  eexists (_, (_, _)); split; [|split; reflexivity].
  eexists ((_, _), _); split; [|split; [|split]; reflexivity].
  eexists (_, _); split; [|split; [split|]; reflexivity].
  eexists (2, 3); split; [|easy].
  eexists ((_, _), _); split; [|split; [left|]; reflexivity].
  eexists (_, (_, _)); split; [|split; [|split]; reflexivity].
  eexists (_, tt).
  easy.
Qed.

Lemma trans_clo_test_2 : (trans_clo nat (fun i j => (i + 1 = j)%nat)) 2 4.
Proof.
  unfold trans_clo, trans_join, trans_split.
  simpl.
  unfold compose_relns.
  __setup_solve_relations.
  exists (4, tt).
  split; [|easy].
  eexists (_, (_, _)); split; [|split; reflexivity].
  eexists ((_, _), _); split; [|split; [|split]; reflexivity].
  eexists (_, _); split; [|split; [split|]; reflexivity].
  eexists (3, 4); split; [|easy].
  eexists ((_, _), _); split; [|split; [left|]; reflexivity].
  eexists (_, (_, _)); split; [|split; [|split]; reflexivity].
  eexists (_, tt).
  easy.
Qed.

End TransitiveClosure.



From ViCaR Require Import CategoryAutomation.


Lemma test {A} : forall (f : reln A (A★)%Cat) (g : reln (A★)%Cat A), 
  ((unit (A:=A) \o (braiding (H:=RelMonoidal) _ A).(forward) \o (f \* g) \o counit) † ~ 
  (unit (A:=A) \o g \* f \o (braiding (H:=RelMonoidal) A _).(forward) \o counit) †)%Cat.
Proof.
  simpl.
  intros f g.
  to_Cat.
  Admitted.


Lemma test2 {A B} : forall (f g : reln A B) (h : reln ⊤ A) (i : reln (⊤ * (A*A)) _), 
  (RelMonoidal.(left_unitor).(forward) \o (idn \o f \* g) ~ i \o f \* g)%Cat.
Proof.
  intros f g h i.
  simpl.
  to_Cat.
  Admitted.
