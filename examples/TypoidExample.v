Require Import Setoid Morphisms. (* Morphisms_Prop may be added? *)
Require Import Logic.
From ViCaR Require Export CategoryTypeclass.
From ViCaR Require Import RigCategory.



Unset Program Cases. 
(* This makes term sizes much, much smaller, as more is abstracted.
   It was necessary to make the proof of being a Rig category go through. *)



Class Setoid : Type := {
  base_type : Type;
  s_equiv : relation base_type;
  s_equiv_refl :> Reflexive s_equiv;
  s_equiv_sym :> Symmetric s_equiv;
  s_equiv_trans :> Transitive s_equiv;
}.

Arguments base_type _ : clear implicits.
Coercion base_type : Setoid >-> Sortclass.

#[export] Instance Setoid_equiv_Equivalence (A : Setoid) : 
  Equivalence A.(s_equiv) := ltac:(split; apply A).

Add Parametric Relation (A : Setoid) : A s_equiv
  reflexivity proved by s_equiv_refl
  symmetry proved by s_equiv_sym
  transitivity proved by s_equiv_trans
  as Setoid_relation.

Local Notation "x '≡' y" := (s_equiv x y) (at level 70).

Class Morphism (A B : Setoid) := {
  base_fn : A -> B;
  base_compat : forall (x y : A), x ≡ y -> base_fn x ≡ base_fn y;
}.

Arguments base_fn {_ _} _.
Coercion base_fn : Morphism >-> Funclass.

Add Parametric Morphism {A B} (f : Morphism A B) : (@base_fn A B f)
  with signature A.(s_equiv) ==> B.(s_equiv) as Morphism_morphism.
Proof. exact base_compat. Qed.

Notation "A '→' B" := (Morphism A B) (at level 90 ): type_scope.

Lemma compose_morphisms_base_compat {A B C} (f : A → B) (g : B → C) :
  forall x y : A, x ≡ y -> g (f x) ≡ g (f y).
Proof.
  intros.
  apply base_compat, base_compat, H.
Qed.


Definition compose_morphisms {A B C} (f : A → B) (g : B → C) 
  : A → C := 
  {|
  base_fn := fun a => g (f a);
  base_compat := compose_morphisms_base_compat f g;
|}.

Local Notation "f '\o' g" := (compose_morphisms f g) 
  (at level 45, left associativity).

Definition mor_equiv {A B} : relation (A → B) :=
  fun f f' => forall x, f x ≡ f' x.

Local Notation "f ~ g" := (forall a, f a ≡ g a) 
  (at level 80, no associativity).

Lemma mor_equiv_refl {A B} (f : A → B) : mor_equiv f f.
Proof. intros ?; reflexivity. Qed.

Lemma mor_equiv_sym {A B} (f f' : A → B) : mor_equiv f f' -> mor_equiv f' f.
Proof. intros Hf ?; now symmetry. Qed.

Lemma mor_equiv_trans {A B} (f f' f'' : A → B) : 
  mor_equiv f f' -> mor_equiv f' f'' -> mor_equiv f f''.
Proof. intros Hf Hf' ?; now etransitivity. Qed.

Add Parametric Relation {A B} : (A → B) (@mor_equiv A B) 
  reflexivity proved by mor_equiv_refl
  symmetry proved by mor_equiv_sym
  transitivity proved by mor_equiv_trans
  as mor_equiv_relation.

Add Parametric Morphism {A B C} : (@compose_morphisms A B C)
  with signature mor_equiv ==> mor_equiv ==> mor_equiv
  as compose_morphisms_morphism.
Proof.
  intros f f' Hf g g' Hg x.
  simpl.
  transitivity (g (f' x)).
  - now apply g.
  - apply Hg.
Qed.

#[program] Definition Setoid_top : Setoid := {| 
  base_type := Datatypes.unit;
  s_equiv := fun _ _ => True;
  |}.
Solve All Obligations with auto.

#[program] Definition Setoid_bot : Setoid := {| 
  base_type := False;
  s_equiv := fun _ _ => False;
  |}.
Solve All Obligations with auto.

Local Notation "⊤" := Setoid_top.
Local Notation "⊥" := Setoid_bot.

#[export, program] Instance SumSetoid (A B : Setoid) : Setoid := {
  base_type := A + B;
  s_equiv := fun a_b a'_b' => match a_b, a'_b' with
  | inl a, inl a' => a ≡ a'
  | inr b, inr b' => b ≡ b'
  | inl a, inr b' => False
  | inr b, inl a' => False
  end;
}.
Next Obligation. intros [a | b]; reflexivity. Qed.
Next Obligation. intros [a | b] [a' | b']; easy. Qed.
Next Obligation. intros [a | b] [a' | b'] [a'' | b''] Ha Ha';
  easy || etransitivity; eassumption. Qed.

#[export, program] Instance ProdSetoid (A B : Setoid) : Setoid := {
  base_type := A * B;
  s_equiv := fun ab a'b' => 
    let (a, b) := ab in let (a', b') := a'b' in a ≡ a' /\ b ≡ b'
}.
Next Obligation. intros [a b]; easy. Qed.
Next Obligation. intros [a b] [a' b']; easy. Qed.
Next Obligation. 
  intros [a b] [a' b'] [a'' b''] Ha Ha'; split;
  etransitivity; try apply Ha; apply Ha'. Qed.

Local Notation "A '.+' B" := (SumSetoid A B) (at level 50).
Local Notation "A '.*' B" := (ProdSetoid A B) (at level 40).

#[program] Definition mor_sum {A B A' B'} (f : A → B) (g : A' → B') :
  (A .+ A') → (B .+ B') := {|
  base_fn := fun i =>
    match i with
    | inl a => inl (f a)
    | inr a' => inr (g a')
    end;
|}.
Next Obligation.
  do 2 match goal with 
  | x : ?A + ?A' |- _ => destruct x
  end; easy || apply f || apply g; easy.
Qed.

Local Notation "f '\+' g" := (mor_sum f g) (at level 43, left associativity).

#[export, program] Instance mor_prod {A B A' B'} (f : A → B) (g : A' → B') :
  (A .* A') → (B .* B') := {|
  base_fn := fun aa' => let (a, a') := aa' in (f a, g a')
|}.
Next Obligation.
  split; apply f || apply g; easy.
Qed.



Local Notation "f '\*' g" := (mor_prod f g) (at level 41, left associativity).

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

Ltac __solve_morphisms_end_forward := 
  repeat match goal with
  | H : ?f ?i ≡ ?g ?j |- _ => (* match type of f with ?A → ?B => *)
      revert H
      (* end *)
  end;
  repeat (let Hf := fresh "Hf" in intros Hf;
    match type of Hf with
    | ?f ?i ≡ ?g ?j =>
      __saturate_funs (f i); __saturate_funs (g j)
    end);
  easy.

Ltac __solve_morphisms_end := idtac.
Ltac __solve_morphisms_end_match se := 
  match goal with
  (* | |- ?f ?x => 
      match type of f with ?n → ?m => eassumption end *)
  | |- base_fn ?f ?i ≡ base_fn ?f ?j => 
      (* idtac "hitsame"; *)
      apply f; solve [se]
  (* | |- base_fn ?f ?i ≡ base_fn ?g ?j => (* idtac "equiv"; *) 
      fail (* match goal with 
      | |-  
      let H := fresh in assert (H : i ≡ j) by solve_morphisms; *) *)
  | H : base_fn ?A ~ base_fn ?A' |- base_fn ?A ?i ≡ base_fn ?A' ?i => 
      (* idtac "hitexact";  *)
      apply H
  | H : base_fn ?A ~ base_fn ?A' |- base_fn ?A' ?i ≡ base_fn ?A ?i => 
      (* idtac "hitsym";  *)
      symmetry; apply H
  | H : base_fn ?A ~ base_fn ?A' |- base_fn ?A ?i ≡ base_fn ?A' ?j => 
      (* idtac "hitbase"; *)
      rewrite H; try apply A'; 
      solve [se]
  | H : base_fn ?A ~ base_fn ?A' |- base_fn ?A' ?i ≡ base_fn ?A ?j => 
      (* idtac "hitbasesym"; *)
      rewrite <- H; print_state; solve [se]
  | H : base_fn ?A ~ base_fn ?A' |- _ => apply H
      (* ; idtac "hitdesparate" *)
  | H : base_fn ?A ~ base_fn ?A' |- _ => symmetry; apply H
      (* ; idtac "hitdesparatesym" *)
  | H : base_fn ?A ~ base_fn ?A' |- context[?A ?i] => 
      (* idtac "hitrew"; *)
      (rewrite H; clear H; 
        (* print_state;  *)
        solve [se])
      || (rewrite <- H; clear H; 
        (* print_state;  *)
        solve [se])
      || (clear H; solve [se])
  | H : base_fn ?A ~ base_fn ?A' |- context[base_fn ?A' ?i] =>   
      (* idtac "hitrewsym"; *)
      (rewrite <- H; clear H; 
        (* print_state;  *)
        solve [se])
      || (rewrite H; clear H; 
        (* print_state;  *)
        solve [se])
      || (clear H; solve [se])
  | H : _ |- _ => apply H; clear H; solve [se]
  (* | _ => constructor; solve [__solve_morphisms_end] *)
  | |- ?x ≡ ?y => 
      let H := fresh in enough (H: x = y) by (rewrite H; reflexivity);
      solve [se]
  end.

(* Begin tactics *)

Ltac __solve_morphisms_end_no_constr := 
  try eassumption;
  try (etransitivity; eauto);
  try reflexivity;
  try easy;
  auto;  
  try (__solve_morphisms_end_match __solve_morphisms_end_no_constr 
    || idtac (* " no match" *)).

Ltac __solve_morphisms_end ::= 
  try eassumption;
  try (etransitivity; eauto);
  try reflexivity;
  try easy;
  auto;  
  try (__solve_morphisms_end_match __solve_morphisms_end 
    || constructor; solve [__solve_morphisms_end_no_constr]
    || econstructor; solve [__solve_morphisms_end_no_constr]).


Ltac solve_morphisms := idtac. (* Hack to allow "mutual recursion" *)

Ltac __setup_solve_morphisms :=
  simpl; 
  unfold mor_equiv, id, compose_morphisms,
  mor_sum, mor_prod in *;
  simpl.

Ltac __solve_morphisms_mid_step := 
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


Ltac __process_solve_morphisms_cleanup_vars :=
  repeat match goal with
  | a : ?A * ?B |- _ => destruct a
  | a : ⊤ |- _ => destruct a
  | a : ?A + ?B |- _ => destruct a
  | a : sig _ |- _ => destruct a
  | a : sigT _ |- _ => destruct a
  | a : sig2 _ _ |- _ => destruct a
  | a : sigT2 _ _ |- _ => destruct a
  end.

Ltac __process_solve_morphisms_step :=
  __process_solve_morphisms_cleanup_vars;
  try easy;
  match goal with
  | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
  | H : (_, _) ≡ (_, _) |- _ => inversion H; subst; clear H
  | H : @eq (_ + _) _ _ |- _ => inversion H; subst; clear H

  | H : (exists _, _) |- _ => destruct H
  | H : _ /\ _ |- _ => destruct H
  | |- _ <-> _ => split
  | |- _ /\ _ => split
  | H : _ \/ _ |- _ => destruct H; [solve_morphisms | solve_morphisms]
  | |- _ \/ _ => 
       (left; solve [solve_morphisms; auto]) 
    || (right; solve [solve_morphisms; auto]) 
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
          exists x; (* idtac "yes" x; *) (solve [solve_morphisms; auto])
        end; match goal with
        | |- _ => (* idtac "none worked"; *) eexists
      end
    end
  end.

Ltac __process_solve_morphisms := 
  repeat (
  __solve_morphisms_mid_step;
  try __process_solve_morphisms_step);
  repeat (try __solve_morphisms_mid_step;
  try __process_solve_morphisms_cleanup_vars).

Ltac solve_morphisms ::= 
  __setup_solve_morphisms;
  __process_solve_morphisms;
  __solve_morphisms_mid_step;
  __solve_morphisms_end || __solve_morphisms_end_forward.
(* End tactics *)

#[export] Instance IdentityMorphism (A : Setoid) : Morphism A A := {|
  base_fn := fun a => a;
  base_compat := fun _ _ => id
|}.

Definition Id := IdentityMorphism.
Arguments Id {_}.

Lemma compose_morphisms_assoc {A B C D} : forall
  (f : A → B) (g : B → C) (h : C → D), 
  f \o g \o h ~ f \o (g \o h).
Proof.
  easy.
Qed.

Lemma compose_id_l {A B} (f : A → B) :
  Id \o f ~ f.
Proof. easy. Qed.

Lemma compose_id_r {A B} (f : A → B) :
  f \o Id ~ f.
Proof. easy. Qed.

Lemma compose_morphisms_compat {A B C} : forall (f f' : A → B),
  f ~ f' -> forall (g g' : B → C), g ~ g' -> 
  f \o g ~ f' \o g'.
Proof.
  solve_morphisms.
Qed.

Lemma mor_equiv_equivalence {A B} : equivalence (A → B) mor_equiv.
Proof.
  split; apply mor_equiv_relation.
Qed.

#[export] Instance Std : Category Setoid := {
  morphism := Morphism;
  c_equiv := @mor_equiv;
  c_equiv_rel := @mor_equiv_equivalence;
  compose := @compose_morphisms;
  compose_compat := @compose_morphisms_compat;
  assoc := @compose_morphisms_assoc;
  c_identity := @IdentityMorphism;
  left_unit := @compose_id_l;
  right_unit := @compose_id_r;
}.

Lemma prod_id {A B} : 
  Id \* Id ~ @Id (A .* B).
Proof. solve_morphisms. Qed.

Lemma prod_compose {A B C A' B' C'} : 
  forall (f : A → B) (g : B → C) (f' : A' → B') (g' : B' → C'),
  (f \o g) \* (f' \o g') ~ f \* f' \o g \* g'.
Proof.
  solve_morphisms.
Qed.

Lemma prod_compat {A B C D} :
  forall (f f' : A → B) (g g' : C → D),
  f ~ f' -> g ~ g' ->
  f \* g ~ f' \* g'.
Proof.
  intros f f' g g' Hf Hg [a c].
  simpl.
  rewrite Hf, Hg.
  easy.
Qed.

#[export] Instance ProductMorphism : Bifunctor Std Std Std := {
  obj_bimap := ProdSetoid;
  morphism_bimap := @mor_prod;
  id_bimap := @prod_id;
  compose_bimap := @prod_compose;
  morphism_bicompat := @prod_compat;
}.

(* This lets us omit all obligation statements *)
Obligation Tactic := (hnf; solve_morphisms).

#[export, program] Instance StdAssociator (A B C : Setoid) : 
  Isomorphism (A .* B .* C) (A .* (B .* C)) := {
  forward := {| 
    base_fn := fun ab_c : (A*B*C) => let '((a, b), c) := ab_c in (a, (b, c))
    |};
  reverse := {| 
    base_fn := fun a_bc:(A*(B*C)) => let '(a, (b, c)) := a_bc in ((a, b), c)
    |};
}.

#[export, program] Instance StdLeftUnitor (A : Setoid) :
  @Isomorphism Setoid Std (⊤ .* A) (A) := {
  forward := {| base_fn := fun (topa : ⊤ * A) => let (_, a) := topa in a|};
  reverse := {| base_fn := fun (a : A) => (tt, a)|};
}.

#[export, program] Instance StdRightUnitor (A : Setoid) :
  Isomorphism (A .* ⊤) (A) := {
    forward := {| base_fn := fun atop : A*⊤ => let (a, _) := atop in a|};
    reverse := {| base_fn := fun a : A => (a, tt)|};
}.

#[export, program] Instance StdMonoidal : MonoidalCategory Std := {
  tensor := ProductMorphism;
	mon_I := ⊤;
  associator := @StdAssociator;
  left_unitor := @StdLeftUnitor;
  right_unitor := @StdRightUnitor;
  (* associator_cohere := ltac:(abstract(solve_morphisms));
  left_unitor_cohere := ltac:(abstract(solve_morphisms));
  right_unitor_cohere := ltac:(abstract(solve_morphisms));
  triangle := ltac:(abstract(solve_morphisms));
  pentagon := ltac:(abstract(solve_morphisms)); *)
}.


#[export, program] Instance StdBraidingIsomorphism (A B : Setoid) : 
  Isomorphism (A .* B) (B .* A) := {
  forward := {| base_fn := fun ab : A*B => let (a, b) := ab in (b, a) |};
  reverse := {| base_fn := fun ba : B*A => let (b, a) := ba in (a, b) |};
}.

#[export, program] Instance StdBraiding : 
  NaturalBiIsomorphism ProductMorphism (CommuteBifunctor ProductMorphism) := {
  component_biiso := @StdBraidingIsomorphism;
  (* component_biiso_natural := ltac:(abstract(solve_morphisms)) *)
}.

#[export, program] Instance StdBraidedMonoidal : BraidedMonoidalCategory StdMonoidal := {
  braiding := StdBraiding;
  (* hexagon_1 := ltac:(abstract(solve_morphisms));
  hexagon_2 := ltac:(abstract(solve_morphisms)); *)
}.

#[export, program] Instance StdSymmetricMonoidal : 
  SymmetricMonoidalCategory StdBraidedMonoidal := {
  (* symmetry := ltac:(abstract(solve_morphisms)); *)
}.

(* #[export] Instance StdCompactClosed : CompactClosedCategory Type := {
  dual := fun A => A;
  unit := @fun_unit;
  counit := fun A => flip fun_unit;
  triangle_1 := ltac:(abstract(solve_morphisms));
  triangle_2 := ltac:(abstract(solve_morphisms));
}. *)

(* #[export] Instance StdDagger : DaggerCategory Type := {
  adjoint := fun A B => @flip A B Prop;
  adjoint_involutive := ltac:(easy);
  adjoint_id := ltac:(easy);
  adjoint_contravariant := ltac:(abstract(solve_morphisms));
  adjoint_compat := ltac:(abstract(solve_morphisms));
}.

#[export] Instance StdDaggerMonoidal : DaggerMonoidalCategory Type := {
  dagger_tensor_compat := ltac:(abstract(solve_morphisms));
  associator_unitary := ltac:(abstract(solve_morphisms));
  left_unitor_unitary := ltac:(abstract(solve_morphisms));
  right_unitor_unitary := ltac:(abstract(solve_morphisms));
}. *)





Lemma sum_id {A B} : 
  Id \+ Id ~ @Id (A .+ B).
Proof. solve_morphisms. Qed.

Lemma sum_compose {A B C A' B' C'} : 
  forall (f : A → B) (g : B → C) (f' : A' → B') (g' : B' → C'),
  (f \o g) \+ (f' \o g') ~ f \+ f' \o g \+ g'.
Proof.
  solve_morphisms.
Qed.
  
#[export, program] Instance SumMorphism : Bifunctor Std Std Std | 10 := {
  obj_bimap := SumSetoid;
  morphism_bimap := @mor_sum;
  id_bimap := @sum_id;
  compose_bimap := @sum_compose;
}.

#[export, program] Instance StdSumAssociator {A B C : Setoid} : 
  Isomorphism (A .+ B .+ C) (A .+ (B .+ C)) := {
  forward := {|
    base_fn := fun ab_c : A.+B.+C =>
    match ab_c with
    | inl (inl a) => inl a : A.+(B.+C)
    | inl (inr b) => inr (inl b)
    | inr c => inr (inr c)
    end|};
  reverse := {|
    base_fn := fun a_bc : A.+(B.+C) =>
    match a_bc with
    | inl a => inl (inl a) : A.+B.+C
    | inr (inl b) => inl (inr b)
    | inr (inr c) => inr c
    end|}
  }.


#[export, program] Instance StdSumLeftUnitor {A : Setoid} :
  Isomorphism (⊥ .+ A) (A) := {
  forward := {| base_fn := fun bota : ⊥.+A => match bota with
    | inr a => a : A
    | inl bot => match bot with end
    end |};
  reverse := {| base_fn := fun a => inr a : ⊥.+A |};
}.

#[export, program] Instance StdSumRightUnitor {A : Setoid} :
  Isomorphism (A .+ ⊥) (A) := {
  forward := {| base_fn := fun abot : A.+⊥ => match abot with
    | inl a => a : A
    | inr bot => match bot with end
    end |};
  reverse := {| base_fn := fun a => inl a : A.+⊥ |};
}.

#[export, program] Instance StdSumMonoidal : MonoidalCategory Std := {
  tensor := SumMorphism;
	mon_I := ⊥;
  associator := @StdSumAssociator;
  left_unitor := @StdSumLeftUnitor;
  right_unitor := @StdSumRightUnitor;
  (* associator_cohere := ltac:(abstract(solve_morphisms));
  left_unitor_cohere := ltac:(abstract(solve_morphisms));
  right_unitor_cohere := ltac:(abstract(solve_morphisms));
  triangle := ltac:(abstract(solve_morphisms));
  pentagon := ltac:(abstract(solve_morphisms)); *)
}.

#[export, program] Instance StdSumBraidingIsomorphism {A B} : 
  Isomorphism (A .+ B) (B .+ A) := {
  forward := {| base_fn := fun a_b : A.+B => 
    match a_b with
    | inl a => inr a
    | inr b => inl b
    end : B.+A |};
  reverse := {| base_fn := fun b_a : B.+A => 
    match b_a with
    | inr a => inl a
    | inl b => inr b 
    end : A.+B |};
}.

#[export, program] Instance StdSumBraiding : 
  NaturalBiIsomorphism SumMorphism (CommuteBifunctor SumMorphism) := {
  component_biiso := @StdSumBraidingIsomorphism;
  (* component_biiso_natural := ltac:(abstract(solve_morphisms)) *)
}.

#[export, program] Instance StdSumBraidedMonoidal 
  : BraidedMonoidalCategory StdSumMonoidal := {
  braiding := StdSumBraiding;
  (* hexagon_1 := ltac:(abstract(solve_morphisms));
  hexagon_2 := ltac:(abstract(solve_morphisms)); *)
}.

#[export, program] Instance StdSumSymmetricMonoidal : 
  SymmetricMonoidalCategory StdSumBraidedMonoidal := {
  (* symmetry := ltac:(abstract(solve_morphisms)); *)
}.

Lemma not_StdSumCompactClosed :
  @CompactClosedCategory Setoid Std StdSumMonoidal 
  StdSumBraidedMonoidal StdSumSymmetricMonoidal -> False.
Proof.
  intros [].
  destruct (counit ⊤ (inl tt)).
Qed.

#[export, program] Instance StdLeftDistributivityIsomorphism (A B M : Setoid) :
  Isomorphism (A .* (B .+ M)) ((A .* B) .+ (A .* M)) := {
  forward := {| base_fn := fun abm : A .* (B .+ M) => match abm with
    | (a, inl b) => inl (a, b)
    | (a, inr m) => inr (a, m)
    end : (A .* B) .+ (A .* M) |};
  reverse := {| base_fn := fun abam : (A .* B) .+ (A .* M) => match abam with
    | inl (a, b) => (a, inl b)
    | inr (a, m) => (a, inr m)
    end : A .* (B .+ M) |};
}.

#[export, program] Instance StdRightDistributivityIsomorphism (A B M : Setoid) :
  Isomorphism ((A .+ B) .* M) ((A .* M) .+ (B .* M)) := {
    forward := {| base_fn := fun abm : (A .+ B) .* M => match abm with
    | (inl a, m) => inl (a, m)
    | (inr b, m) => inr (b, m)
    end : (A .* M) .+ (B .* M) |};
  reverse := {| base_fn := fun abam => match abam : (A .* M) .+ (B .* M) with
    | inl (a, m) => (inl a, m)
    | inr (b, m) => (inr b, m)
    end : (A .+ B) .* M |};
}.

Lemma rel_left_distributivity_isomorphism_natural {A B M A' B' M' : Setoid}
  (f : A → A') (g : B → B') (h : M → M') :
  (StdLeftDistributivityIsomorphism A B M
  ∘ (mor_sum (mor_prod f g) (mor_prod f h))
  ≃ mor_prod f (mor_sum g h)
	∘ StdLeftDistributivityIsomorphism A' B' M')%Cat.
Proof.
  solve_morphisms.
Qed.

Lemma rel_right_distributivity_isomorphism_natural {A B M A' B' M' : Setoid}
  (f : A → A') (g : B → B') (h : M → M') :
  (StdRightDistributivityIsomorphism A B M
  ∘ (mor_sum (mor_prod f h) (mor_prod g h))
  ≃ mor_prod (mor_sum f g) h
	∘ StdRightDistributivityIsomorphism A' B' M')%Cat.
Proof.
  solve_morphisms.
Qed.

#[export, program] Instance StdLeftAbsorbtion (A : Setoid) :
  (⊥ .* A <~> ⊥)%Cat := {
  forward := {| base_fn := fun bota : ⊥ .* A => 
    match bota with 
    | (bot, a) => match bot with end 
    end : ⊥ |};
  reverse := {| base_fn := fun bot : ⊥ => 
    match bot with end : ⊥ .* A |};
}.

#[export, program] Instance StdRightAbsorbtion (A : Setoid) :
  (A .* ⊥ <~> ⊥)%Cat := {
  forward := {| base_fn := fun abot : A .* ⊥ => 
    match abot with 
    | (a, bot) => match bot with end 
    end : ⊥ |};
  reverse := {| base_fn := fun bot : ⊥ => 
    match bot with end : A .* ⊥ |};
}.

#[export, program] Instance StdPreDistr : 
  PreDistributiveBimonoidalCategory StdSumSymmetricMonoidal
  StdMonoidal := {
    left_distr_iso := StdLeftDistributivityIsomorphism;
    right_distr_iso := StdRightDistributivityIsomorphism;
    left_distr_natural := @rel_left_distributivity_isomorphism_natural;
    right_distr_natural := @rel_right_distributivity_isomorphism_natural;
}.

#[export, program] Instance StdDistrBimonoidal : 
  DistributiveBimonoidalCategory StdPreDistr := {
  left_absorbtion_iso := StdLeftAbsorbtion;
  right_absorbtion_iso := StdRightAbsorbtion;
}.



#[export, program] Instance StdSemiCoherent :
  SemiCoherent_DistributiveBimonoidalCategory StdDistrBimonoidal.




#[export, program] Instance StdSemiCoherentBraided :
  SemiCoherent_BraidedDistributiveBimonoidalCategory StdDistrBimonoidal StdBraidedMonoidal := {
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

Definition category_product_unique `{cC : Category C} (A B : C) :
  forall {AB AB'} (HAB : CategoryProduct A B AB) 
  (HAB' : CategoryProduct A B AB'), Isomorphism AB AB'.
  refine (fun AB AB' HAB HAB' =>
  {|
    forward := HAB'.(prod_mor) AB p_A p_B;
    reverse := HAB.(prod_mor) AB' p_A p_B;
  |}).
  split; eapply (prod_mor_unique' _ p_A p_B); rewrite 1?assoc.
  1,5: rewrite 2!(proj1 (prod_mor_prop _ _ _)); easy.
  1,4: rewrite 2!(proj2 (prod_mor_prop _ _ _)); easy.
  all: rewrite left_unit; easy.
Qed.

Class CartesianMonoidalCategory `(mC : MonoidalCategory C) := {
  tensor_cartesian : forall (A B : C),
    CategoryProduct A B (A × B)%Mon;
}.

Obligation Tactic := (try (hnf; solve_morphisms)).

#[export, program] Instance StdCartesianMonoidalCategory :
  CartesianMonoidalCategory StdMonoidal := {
    tensor_cartesian := fun A B => {| 
      p_A := {| base_fn := fun ab : A*B => let (a, _) := ab in a : A |};
      p_B := {| base_fn := fun ab => let (_, b) := ab in b |};
      prod_mor := fun Q fA fB => {| base_fn :=
        fun q => (fA q, fB q) |}
    |}
  }.
Next Obligation. 
  __setup_solve_morphisms.
  intros A B Q fA fB fAB' HA HB q.
  destruct (fAB' q) eqn:e.
  rewrite HA, HB, e.
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

(* Require Import FunctionalExtensionality. *)

#[program] Definition big_setoid_prod {J} (obj : J -> Setoid) :=  {|
  base_type := forall (i : J), obj i;
  s_equiv := fun is js => forall (i : J), is i ≡ js i;
|}.

#[export, program] Instance StdBigProd {J} {obj : J -> Setoid} : 
  CategoryBigProd obj (big_setoid_prod obj) := {
  p_i := fun i => {| base_fn := fun f => f i |};
  big_prod_mor := fun Q fQ_ => 
    {| base_fn := fun q => fun i => fQ_ i q |};
}.


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

Inductive big_sum {J} (obj : J -> Setoid) :=
  | in_i i (a : obj i) : big_sum obj.

Arguments in_i {_ _} _ _.

Inductive big_sum_relation {J} (obj : J -> Setoid) : relation (big_sum obj) :=
  | rel_i (i : J) (a b : obj i) (Hab : (obj i).(s_equiv) a b) 
    : big_sum_relation obj (in_i i a) (in_i i b)
  | rel_trans (ia jb kc : big_sum obj) : 
    big_sum_relation obj ia jb -> big_sum_relation obj jb kc ->
    big_sum_relation obj ia kc.

Require Import Coq.Program.Equality.
  
  


#[export, program] Instance big_setoid_sum {J} (obj : J -> Setoid) : Setoid := {
  base_type := big_sum obj;
  s_equiv := big_sum_relation obj;
}.
Next Obligation.
  intros J obj [i a]. 
  constructor; solve_morphisms.
Qed.
Next Obligation.
  intros J obj [i a] [j b] Hab.
  induction Hab; subst.
  - apply rel_i; easy.
  - eapply rel_trans; eassumption.
Qed.
Next Obligation.
  intros; intros ? **.
  eapply rel_trans; eauto.
Qed.


#[export, program] Instance StdBigCoprod {J} {obj : J -> Setoid} : 
  CategoryBigCoprod obj (big_setoid_sum obj) := {
  iota_i := fun i => {| base_fn := fun oi => in_i i oi : big_setoid_sum obj |};
  big_coprod_mor := fun Q fQ_ => {| base_fn := fun oi => match oi with
  | in_i i ai => fQ_ i ai
  end |};
}.
Next Obligation.
  intros. simpl.
  induction H.
  - apply fQ_; easy.
  - rewrite IHbig_sum_relation1, IHbig_sum_relation2.
    easy.
Qed.
Next Obligation.
  __setup_solve_morphisms.
  intros J obj Q fQ_ fAB H x.
  induction x.
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

#[program, export] Instance MorphismSetoid (A B : Setoid) : Setoid := {
  base_type := A → B;
  s_equiv := mor_equiv;
}.

#[program, export] Instance StdExponential {A B : Setoid} :
  CategoryExponential A B (MorphismSetoid B A) := {
  eval_mor := {| base_fn := fun fb => let (f, b) := fb in f b |};
  eval_mor_transpose := fun M f => {| base_fn := fun m =>
  {| base_fn := fun b => f (m, b) |} |};
}.



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

#[export, program] Instance std_limit_setoid 
  {D} {cD : Category D} (F : Functor cD Std) : Setoid := {
  base_type := { s : big_setoid_prod F.(obj_map) | 
    forall (d d' : D) (f : d ~> d'), (F @ f) (s d) ≡ s d' };
  s_equiv := fun sP s'P => let (s, _) := sP in let (s', _) := s'P in 
    s ≡ s';
}.

#[export, program] Instance std_limit_setoid_cone_mor 
  {D} {cD : Category D} (F : Functor cD Std) :
  forall (d : D), std_limit_setoid F → F d := fun d => {|
  base_fn := fun sP => let (s, _) := sP in s d
|}.

#[export, program] Instance StdLimitCone {D} {cD : Category D} (F : Functor cD Std) 
  : Cone F := {
  cone_obj := std_limit_setoid F;
  cone_mor := std_limit_setoid_cone_mor F;
  (* cone_mor_prop := fun d d' => typ_limit_obj_cone_mor_prop F; *)
}.  

#[export, program] Instance StdLimit {D} {cD : Category D} (F : Functor cD Std) 
  : Limit F := {
  limit_cone := StdLimitCone F;
  limit_cone_factor := fun N => {| 
    base_fn := fun n : N.(cone_obj) => 
      exist _ (fun d : D => N d n) _ : std_limit_setoid F |}
}.
Next Obligation.
  __setup_solve_morphisms.
  __process_solve_morphisms.
  (* rewrite <- H. *)
  destruct (f' x) as [s P] eqn:e.
  intros i.
  rewrite <- H.
  rewrite e.
  easy.
Qed.



Inductive make_equiv {A} (R : relation A) : relation A :=
  | make_rel {a b : A} : R a b -> make_equiv R a b
  | make_refl (a : A) : make_equiv R a a
  | make_sym {a b : A} : make_equiv R a b -> make_equiv R b a
  | make_trans {a b c : A} : 
      make_equiv R a b -> make_equiv R b c ->
      make_equiv R a c.

#[export] Instance make_equiv_equivalance {A} (R : relation A) :
  Equivalence (make_equiv R) := {
  Equivalence_Reflexive := @make_refl A R;
  Equivalence_Symmetric := @make_sym A R;
  Equivalence_Transitive := @make_trans A R;
}.

Definition std_colimit_rel {D} {cD : Category D} (F : Functor cD Std) :
  relation (big_setoid_sum F.(obj_map)) := 
    make_equiv (
      fun (ia jb : big_setoid_sum F.(obj_map))
        => let (i, a) := ia in let (j, b) := jb in 
        exists f : i ~> j, (F @ f) a ≡ b
  ).

(* Obligation Tactic := idtac. *)

#[export, program] Instance std_colimit_setoid 
  {D} {cD : Category D} (F : Functor cD Std) : Setoid := {
  base_type := big_setoid_sum F.(obj_map);
  s_equiv := std_colimit_rel F;
}.


#[export, program] Instance std_colimit_setoid_cocone_mor 
  {D} {cD : Category D} (F : Functor cD Std) :
  forall (d : D), F d → std_colimit_setoid F := fun d => {|
  base_fn := fun a => in_i d a
|}.

#[export, program] Instance StdColimitCocone {D} {cD : Category D} (F : Functor cD Std) 
  : Cocone F := {
  cocone_obj := std_colimit_setoid F;
  cocone_mor := std_colimit_setoid_cocone_mor F;
  (* cone_mor_prop := fun d d' => typ_limit_obj_cone_mor_prop F; *)
}.
Next Obligation. 
  simpl.
  intros.
  intros x.
  simpl.
  apply make_sym.
  apply make_rel.
  exists f.
  easy.
Qed.

#[export, program] Instance StdColimit {D} {cD : Category D} (F : Functor cD Std) 
  : Colimit F := {
  colimit_cocone := StdColimitCocone F;
  colimit_cocone_factor := fun N => {| 
    base_fn := fun ia : big_setoid_sum F => let (i, a) := ia in 
      N.(cocone_mor) i a |}
}.
Next Obligation.
  __setup_solve_morphisms.
  __process_solve_morphisms.
  
  dependent induction H.
  destruct a as [i a];
  destruct b as [j b].
  - destruct H as [f Hf].
    epose proof (N.(cocone_mor_prop) f) as HN.
    revert HN;
    __setup_solve_morphisms;
    intros HN.
    rewrite <- HN, Hf.
    easy.
  - easy.
  - rewrite IHmake_equiv.
    easy.
  - etransitivity; eauto.
Qed.
Next Obligation.
  __setup_solve_morphisms.
  intros D cD F N f' Hf'.
  intros [i a].
  easy.
Qed.

  

