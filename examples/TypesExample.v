Require Import Setoid.
Require Import Logic.
Require Import Basics.
From ViCaR Require Export CategoryTypeclass.
From ViCaR Require Import RigCategory.



Local Notation "f '\o' g" := (fun A => g (f A)) 
  (at level 45, left associativity).

Local Notation "f ~ g" := (forall a, f a = g a) 
  (at level 80, no associativity).

Definition fun_equiv {A B : Type} (f g : A -> B) := 
  f ~ g.

Local Notation "⊤" := Datatypes.unit.
Local Notation "⊥" := Datatypes.Empty_set.

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
    | reln ?n ?m => 
      (eapply H || ( idtac "needed rewrite";
      replace i' with i by auto; replace j' with j by auto; eapply H))
    end *)
  | H : ?A ~ ?A' |- ?A ?i = ?A' ?i => idtac "hitexact"; apply H
  | H : ?A ~ ?A' |- ?A' ?i = ?A ?i => idtac "hitsym"; symmetry; apply H
  | H : ?A ~ ?A' |- _ => apply H
  | H : ?A ~ ?A' |- _ => symmetry; apply H
  | H : ?A ~ ?A' |- context[?A ?i] => 
    (rewrite H; clear H; print_state; solve __solve_functions_end)
    || (rewrite <- H; clear H; print_state; solve __solve_functions_end)
    || (clear H; solve __solve_functions_end)
  | H : ?A ~ ?A' |- context[?A' ?i] =>   
    (rewrite <- H; clear H; print_state; solve __solve_functions_end)
    || (rewrite H; clear H; print_state; solve __solve_functions_end)
    || (clear H; solve __solve_functions_end)
  end || idtac (* " no match" *)).


Ltac solve_functions := idtac. (* Hack to allow "mutual recursion" *)

Ltac __setup_solve_functions :=
  simpl; unfold unitary; simpl;
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

(* Lemma fun_equiv_trans {A B : Type} (f g h : A -> B) :
  f ~ g -> g ~ h -> f ~ h.
Proof. 
  intros.
  try eassumption; try reflexivity; try easy; auto;
   try
	match goal with
    | |- ?f ?x => match type of f with
                  | ?n -> ?m => eassumption
                  end
    (* | H: ?A ~ ?A' |- ?A ?i = ?A' ?i => idtac "hitexact"; apply H
    | H: ?A ~ ?A' |- ?A' ?i = ?A ?i => idtac "hitsym"; symmetry; apply H *)
    | H: ?A ~ ?A' |- _ => apply H
    | H: ?A ~ ?A' |- _ => symmetry; apply H
    | H: ?A ~ ?A'
      |- context [ ?A ?i ] =>
          (rewrite H; clear H; print_state;
            solve __solve_functions_end) ||
            (rewrite <- H; clear H; print_state;
              solve __solve_functions_end) ||
              (clear H; solve __solve_functions_end)
    | H:?A ~ ?A'
      |- context [ ?A' ?i ] =>
          (rewrite <- H; clear H; print_state;
            solve __solve_functions_end) ||
            (rewrite H; clear H; print_state;
              solve __solve_functions_end) ||
              (clear H; solve __solve_functions_end)
    end.
  etransitivity.
  
  
  repeat __solve_functions_end.
  rewrite H.
  
  solve_functions. Qed.

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
  equiv := @reln_equiv;
  equiv_rel := reln_equiv_equivalence;
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
  obj2_map := prod;
  morphism2_map := @reln_prod;
  id2_map := @prod_idn;
  compose2_map := @prod_compose;
  morphism2_compat := @prod_compat;
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

#[export] Instance RelMonoidal : MonoidalCategory Type := {
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
  component2_iso := @RelBraidingIsomorphism;
  component2_iso_natural := ltac:(abstract(solve_relations))
}.

#[export] Instance RelBraidedMonoidal : BraidedMonoidalCategory Type := {
  braiding := RelBraiding;
  hexagon_1 := ltac:(abstract(solve_relations));
  hexagon_2 := ltac:(abstract(solve_relations));
}.

#[export] Instance RelSymmetricMonoidal : 
  SymmetricMonoidalCategory Type := {
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
  dagger_compat := ltac:(abstract(solve_relations));
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
  obj2_map := sum;
  morphism2_map := @reln_sum;
  id2_map := @sum_idn;
  compose2_map := @sum_compose;
  morphism2_compat := ltac:(abstract(solve_relations));
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

#[export] Instance RelSumMonoidal : MonoidalCategory Type := {
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
  component2_iso := @RelSumBraidingIsomorphism;
  component2_iso_natural := ltac:(abstract(solve_relations))
}.

#[export] Instance RelSumBraidedMonoidal : BraidedMonoidalCategory Type := {
  braiding := RelSumBraiding;
  hexagon_1 := ltac:(abstract(solve_relations));
  hexagon_2 := ltac:(abstract(solve_relations));
}.

#[export] Instance RelSumSymmetricMonoidal : 
  SymmetricMonoidalCategory Type := {
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

#[export] Instance RelSumDagger : DaggerCategory Type := {
  adjoint := fun A B => @flip A B Prop;
  adjoint_involutive := ltac:(easy);
  adjoint_id := ltac:(easy);
  adjoint_contravariant := ltac:(abstract(solve_relations));
  adjoint_compat := ltac:(abstract(solve_relations));
}.

#[export] Instance RelSumDaggerMonoidal : DaggerMonoidalCategory Type := {
  dagger_compat := ltac:(abstract(solve_relations));
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

#[export] Instance RelSemiCoherent :
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
}.

#[export] Instance RelSemiCoherentBraided :
  SemiCoherent_BraidedDistributiveBimonoidalCategory RelDistrBimonoidal RelBraidedMonoidal := {
  condition_II (A B C : Type) := ltac:(abstract(solve_relations));
  condition_XV (A : Type) := ltac:(abstract(solve_relations));
}. *)
