Require Import Setoid Morphisms. (* Morphisms_Prop may be added? *)
Require Import Logic.
From ViCaR Require Export CategoryTypeclass.




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

Ltac __saturate_s_equiv Hf :=
  match type of Hf with s_equiv ?x ?y =>
  let Hsym := constr:(s_equiv_sym x y Hf) in 
  extend (Hsym);
  repeat match goal with
  | H : s_equiv ?z x |- _ =>
    let Hg := constr:(s_equiv_trans z x y H Hf) in
      extend Hg; __saturate_s_equiv Hg
  | H : s_equiv x ?z |- _ => 
    let Hg := constr:(s_equiv_trans y x z Hsym H) in
      extend Hg; __saturate_s_equiv Hg
  | H : s_equiv ?z y |- _ =>
    let Hg := constr:(s_equiv_trans z y x H Hsym) in
      extend Hg; __saturate_s_equiv Hg
  | H : s_equiv y ?z |- _ => 
    let Hg := constr:(s_equiv_trans x y z Hf H) in
      extend Hg; __saturate_s_equiv Hg
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

Ltac __solve_morphisms_end_extra := idtac.

Ltac __solve_morphisms_end ::= 
  try eassumption;
  try (etransitivity; eauto);
  try reflexivity;
  try easy;
  auto;  
  __solve_morphisms_end_extra;
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
  | H : _ \/ _ |- _ => destruct H; [try (left; solve_morphisms) | try (right; solve_morphisms)]
  | H : context[exists _, _] |- _ => edestruct H; try clear H; solve_morphisms
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

Ltac __process_solve_morphisms_extra := idtac.

Ltac __process_solve_morphisms := 
  repeat (
  __solve_morphisms_mid_step;
  try __process_solve_morphisms_step;
  try __process_solve_morphisms_extra);
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
  compose := @compose_morphisms;
  c_identity := @IdentityMorphism;
}.

#[export] Instance StdC : CategoryCoherence Std := {
  c_equiv_rel := @mor_equiv_equivalence;
  compose_compat := @compose_morphisms_compat;
  assoc := @compose_morphisms_assoc;
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
  obj_tensor := ProdSetoid;
  mor_tensor := fun _ _ _ _ => mor_prod;
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

#[export, program] Instance StdMonoidalC 
  : MonoidalCategoryCoherence StdMonoidal := {}.


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
}.

#[export, program] Instance StdBraidedMonoidalC 
  : BraidedMonoidalCategoryCoherence StdBraidedMonoidal := {
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
  obj_tensor := SumSetoid;
  mor_tensor := fun _ _ _ _ => mor_sum;
  (* tensor := SumMorphism; *)
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

#[export, program] Instance StdSumMonoidalC : 
  MonoidalCategoryCoherence StdSumMonoidal := {}.

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





Require Import CategoryConstructions.

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

Open Scope Cat_scope.


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

  

