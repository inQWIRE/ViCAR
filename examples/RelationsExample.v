Require Import Setoid.
Require Import Logic.
Require Import Basics (flip).
From ViCaR Require Export CategoryTypeclass.


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
  simpl;
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

Obligation Tactic := (hnf; solve_relations).
Unset Program Cases.

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
  compose := @compose_relns;
  c_identity := @idn;
}.

#[export] Instance RelC : CategoryCoherence Rel := {
  c_equiv_rel := reln_equiv_equivalence;
  compose_compat := @compose_relns_compat;
  assoc := @compose_relns_assoc;
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

#[export, program] Instance RelAssociator {A B C : Type} : 
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
}.

(* Set Printing Universes. *)

#[export, program] Instance RelLeftUnitor {A : Type} :
  @Isomorphism Type Rel (⊤ * A) (A) := {
  forward := fun topa b => match topa with (_, a) => a = b end;
  reverse := fun a topb => match topb with (_, b) => a = b end;
}.

#[export, program] Instance RelRightUnitor {A : Type} :
  @Isomorphism Type Rel (A * ⊤) (A) := {
  forward := fun atop b => match atop with (a, _) => a = b end;
  reverse := fun a btop => match btop with (b, _) => a = b end;
}.

#[export, program] Instance RelMonoidal : MonoidalCategory Rel | 0 := {
  obj_tensor := prod;
  mor_tensor := @reln_prod;
	mon_I := ⊤;
  associator := @RelAssociator;
  left_unitor := @RelLeftUnitor;
  right_unitor := @RelRightUnitor;
}.

#[export, program] Instance RelMonoidalC
  : MonoidalCategoryCoherence RelMonoidal := {}.


#[export, program] Instance RelBraidingIsomorphism {A B} : 
  Isomorphism (A * B) (B * A) := {
  forward := fun ab ba' => match ab with (a, b) => match ba' with (b', a') =>
    a = a' /\ b = b'
    end end;
  reverse := fun ba ab' => match ba with (b, a) => match ab' with (a', b') => 
    a = a' /\ b = b'
    end end;
}.

#[export, program] Instance RelBraiding : 
  NaturalBiIsomorphism ProductRelation (CommuteBifunctor ProductRelation) := {
  component_biiso := @RelBraidingIsomorphism;
}.

#[export, program] Instance RelBraidedMonoidal 
  : BraidedMonoidalCategory RelMonoidal | 0 := {
  braiding := RelBraiding;
}.

#[export, program] Instance RelSymmetricMonoidal : 
  SymmetricMonoidalCategory RelBraidedMonoidal | 0 := {
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
  
#[export, program] Instance SumRelation : Bifunctor Rel Rel Rel := {
  obj_bimap := sum;
  morphism_bimap := @reln_sum;
  id_bimap := @sum_idn;
  compose_bimap := @sum_compose;
}.

#[export, program] Instance RelSumAssociator {A B C : Type} : 
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
}.


#[export, program] Instance RelSumLeftUnitor {A : Type} :
  @Isomorphism Type Rel (⊥ + A) (A) := {
  forward := fun bota b => match bota with
    | inr a => a = b
    | _ => False 
    end;
  reverse := fun a botb => match botb with 
    | inr b => a = b 
    | _ => False end;
}.

#[export, program] Instance RelSumRightUnitor {A : Type} :
  @Isomorphism Type Rel (A + ⊥) (A) := {
  forward := fun bota b => match bota with
    | inl a => a = b
    | _ => False 
    end;
  reverse := fun a botb => match botb with 
    | inl b => a = b 
    | _ => False end;
}.

#[export, program] Instance RelSumMonoidal : MonoidalCategory Rel | 10 := {
  obj_tensor := sum;
  mor_tensor := @reln_sum;
	mon_I := ⊥;
  associator := @RelSumAssociator;
  left_unitor := @RelSumLeftUnitor;
  right_unitor := @RelSumRightUnitor;
}.

#[export, program] Instance RelSumMonoidalC 
  : MonoidalCategoryCoherence RelSumMonoidal := {}.


#[export, program] Instance RelSumBraidingIsomorphism {A B} : 
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
}.

#[export, program] Instance RelSumBraiding : 
  NaturalBiIsomorphism SumRelation (CommuteBifunctor SumRelation) := {
  component_biiso := @RelSumBraidingIsomorphism;
}.

#[export, program] Instance RelSumBraidedMonoidal : 
  BraidedMonoidalCategory RelSumMonoidal | 10 := {
  braiding := RelSumBraiding;
}.

#[export, program] Instance RelSumSymmetricMonoidal : 
  SymmetricMonoidalCategory RelSumBraidedMonoidal | 10 := {
}.

#[export, program] Instance RelLeftDistributivityIsomorphism (A B M : Type) :
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
}.

#[export, program] Instance RelRightDistributivityIsomorphism (A B M : Type) :
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

#[export, program] Instance RelLeftAbsorbtion (A : Type) :
  (⊥ * A <~> ⊥)%Cat := {
  forward := fun bota => match bota with | (bot, a) => match bot with end end;
  reverse := fun bot => match bot with end;
}.

#[export, program] Instance RelRightAbsorbtion (A : Type) :
  (A * ⊥ <~> ⊥)%Cat := {
  forward := fun abot => match abot with | (a, bot) => match bot with end end;
  reverse := fun bot => match bot with end;
}.


Obligation Tactic := try (hnf; solve_relations).

Require Import CategoryConstructions.

Section RelProperties.

Local Open Scope Cat_scope.


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
Next Obligation.
  __setup_solve_relations.
  intros A B Q fA fB fAB'.
  repeat split;
  __process_solve_relations_cleanup_vars;
  rewrite 1?H, 1?H0;
  solve_relations.
Qed.


Inductive big_sum (J : Type -> Type) :=
  | in_i i (a : J i) : big_sum J.

Arguments in_i {_} _ _.
(* Set Printing Universes. *)

Obligation Tactic := Tactics.program_simpl.

#[export, program] Instance RelBigProd (J : Type -> Type) : 
  CategoryBigProd J (big_sum J) := {
    p_i := fun i => fun somei a => match somei with
    | in_i i' a' => exists (H: i = i'), _
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

End RelProperties.