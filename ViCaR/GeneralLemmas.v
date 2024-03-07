Require Import Category.
Require Import Monoidal.
Require Import Setoid.

Local Open Scope Cat.

Lemma compose_simplify_general : forall {C : Type} {Cat : Category C}
  {A B M : C} (f1 f3 : A ~> B) (f2 f4 : B ~> M),
  f1 ≃ f3 -> f2 ≃ f4 -> (f1 ∘ f2) ≃ (f3 ∘ f4).
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma stack_simplify_general : forall {C : Type} 
  {Cat : Category C} {MonCat : MonoidalCategory C}
  {A B M N : C} (f1 f3 : A ~> B) (f2 f4 : M ~> N),
  f1 ≃ f3 -> f2 ≃ f4 -> (f1 ⊗ f2) ≃ (f3 ⊗ f4).
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma stack_compose_distr_test : forall {C : Type}
  `{Cat : Category C} `{MonCat : MonoidalCategory C}
  {A B D M N P : C} (f : A ~> B) (g : B ~> D) 
  (h : M ~> N) (i : N ~> P),
  (f ∘ g) ⊗ (h ∘ i) ≃ (f ⊗ h) ∘ (g ⊗ i).
Proof.
  intros.
  rewrite compose2_map.
  easy.
Qed.

(* Local Notation "A ⨂ B" := (morphism2_map (Bifunctor:=tensor) A B) (only printing). *)


Lemma stack_distr_pushout_r_bot : forall {C : Type}
  `{Cat : Category C} `{MonCat : MonoidalCategory C}
  {a b d m n} (f : a ~> b) (g : b ~> d) (h : m ~> n),
  f ∘ g ⊗ h ≃ f ⊗ h ∘ (g ⊗ (id_ n)).
Proof.
  intros.
  rewrite <- compose2_map, right_unit.
  easy.
Qed.

(* TODO: the other two; _l_bot and _l_top *)

Lemma stack_distr_pushout_r_top : forall {C : Type}
  `{Cat : Category C} `{MonCat : MonoidalCategory C}
  {a b m n o} (f : a ~> b) (g : m ~> n) (h : n ~> o),
  f ⊗ (g ∘ h) ≃ f ⊗ g ∘ (id_ b ⊗ h).
Proof.
  intros.
  rewrite <- compose2_map, right_unit.
  easy.
Qed.

Ltac fencestep :=
  let test_simple t := match t with
    | context[(_ ⊗ _) ∘ _] => fail 2
    | context[_ ∘ (_ ⊗ _)] => fail 2
    | context[(_ ∘ _) ⊗ _] => fail 2
    | context[_ ⊗ (_ ∘ _)] => fail 2
    | _ => idtac
    end
  in
  first [ match goal with
  |- context[(?f ∘ ?g) ⊗ (?h ∘ ?i)] =>
      test_simple f; test_simple g; test_simple h; test_simple i;
      rewrite (compose2_map f g h i)
  end | match goal with
  |- context[(?f) ⊗ (?g ∘ ?h)] =>
      test_simple f; test_simple g; test_simple h;
      rewrite (stack_distr_pushout_r_top f g h)
  end | match goal with
  |- context[(?f ∘ ?g) ⊗ (?h)] =>
      test_simple f; test_simple g; test_simple h;
      rewrite (stack_distr_pushout_r_bot f g h)
  end].



(* Ltac fencepost :=
  
  let rec process_term term :=
    match term with 
    | ?A ⊗ ?B => match A, B with
      | ?A' ⊗ B', _ => process_term A
      | ?f ∘ ?g (* TODO: test if these are "simple", in some sense. 
      Also see if I can come up with an (even informal) algorithm, or
      even as much as an explicit spec (e.g., strict fenceposing may 
      be required to have functions go in descending order, so 
      f   id  id  i                           id  f
      id  g   id  id                          g   id
      id  id  h   id  , etc. is good, but not id  id ...
      id  id  id  id                          id  id
      ). I suspect the strict spec will make reasoning
      much easier, i.e. to process f⊗g, we *must* push it out
      to f⊗id ∘ id⊗g. *) *)



Lemma nwire_stack_compose_topleft_general : forall {C : Type}
  {Cat : Category C} {MonCat : MonoidalCategory C}
  {topIn botIn topOut botOut : C} 
  (f0 : botIn ~> botOut) (f1 : topIn ~> topOut),
  ((c_identity topIn) ⊗ f0) ∘ (f1 ⊗ (c_identity botOut)) ≃ (f1 ⊗ f0).
Proof.
  intros.
  rewrite <- compose2_map.
  rewrite left_unit; rewrite right_unit.
  easy.
Qed.

Lemma nwire_stackcompose_topright_general : forall {C : Type}
  {Cat: Category C} {MonCat : MonoidalCategory C}
  {topIn botIn topOut botOut : C} 
  (f0 : topIn ~> topOut) (f1 : botIn ~> botOut),
  (f0 ⊗ (c_identity botIn)) ∘ ((c_identity topOut) ⊗ f1) ≃ (f0 ⊗ f1).
Proof.
  intros.
  rewrite <- compose2_map.
  rewrite right_unit, left_unit.
  easy.
Qed.

Require Import ExamplesAutomation.

Lemma stack_id_compose_split_top : forall {C : Type}
  {Cat: Category C} {MonCat : MonoidalCategory C}
  {topIn topMid topOut bot : C} 
  (f0 : topIn ~> topMid) (f1 : topMid ~> topOut),
  (f0 ∘ f1) ⊗ (id_ bot) ≃ f0 ⊗ id_ bot ∘ (f1 ⊗ id_ bot).
Proof.
  intros.
  rewrite <- compose2_map, left_unit.
  easy.
Qed.

Lemma stack_id_compose_split_bot : forall {C : Type}
  {Cat: Category C} {MonCat : MonoidalCategory C}
  {top botIn botMid botOut : C} 
  (f0 : botIn ~> botMid) (f1 : botMid ~> botOut),
  (id_ top) ⊗ (f0 ∘ f1) ≃ id_ top ⊗ f0 ∘ (id_ top ⊗ f1).
Proof.
  intros.
  rewrite <- compose2_map, left_unit.
  easy.
Qed.

(* Ignore this stuff for now: *)

Ltac _fencepost term :=
  match term with
  | id_ ?A => idtac
  | ?f ⊗ id_ _ => _fencepost f; idtac "fix:"; print_state
  | id_ _ ⊗ ?f => _fencepost f; idtac "fix:"; print_state
  | ?f ∘ ?g => idtac f "∘" g; _fencepost f; _fencepost g
  | ?f ⊗ ?g => idtac f "⊗" g; match type of f with
    | ?topIn ~> ?topOut => match type of g with
    | ?botIn ~> ?botOut => rewrite <- (nwire_stackcompose_topright_general f g);
      _fencepost (f ⊗ c_identity botIn); _fencepost (c_identity topOut ⊗ g)
    end end
  | ?f => idtac "should be clean:" f
  end.

Ltac __fencepost term :=
  match term with
  | id_ ?A => idtac
  | ?f ∘ ?g => (* idtac f "∘" g; *) __fencepost f; __fencepost g
  | ?f ⊗ id_ _ => __fencepost f  (* ; idtac "fix:"; print_state *)
  | id_ _ ⊗ ?f => __fencepost f  (* ; idtac "fix:"; print_state *)
  | (?f ∘ ?g) ⊗ (?h ∘ ?i) => first [
    first [progress __fencepost f; rewrite ?assoc |
    progress __fencepost g; rewrite ?assoc |
    progress __fencepost h; rewrite ?assoc |
    progress __fencepost i; rewrite ?assoc];
    idtac "hit1"; __fencepost term; idtac "hit2" |
    rewrite (compose2_map f g h i); __fencepost (f⊗h); __fencepost (g⊗i)]
  | (?f ∘ ?g) ⊗ ?h => first [
    progress __fencepost f; rewrite ?assoc |
    progress __fencepost g; rewrite ?assoc |
    progress __fencepost h; rewrite ?assoc |
    rewrite (stack_distr_pushout_r_bot f g h)]
  | ?f ⊗ (?g ∘ ?h) => first [
    progress __fencepost f; rewrite ?assoc |
    progress __fencepost g; rewrite ?assoc |
    progress __fencepost h; rewrite ?assoc |
    rewrite (stack_distr_pushout_r_top f g h)]
  | ?f ⊗ ?g => first [
    progress __fencepost f; rewrite ?assoc |
    progress __fencepost g; rewrite ?assoc |
    rewrite <- (nwire_stackcompose_topright_general f g)]
  (* | ?f ⊗ ?g => idtac f "⊗" g; match type of f with
    | ?topIn ~> ?topOut => match type of g with
    | ?botIn ~> ?botOut => rewrite <- (nwire_stackcompose_topright_general f g);
      __fencepost (f ⊗ c_identity botIn); __fencepost (c_identity topOut ⊗ g)
    end end *)
  | ?f => idtac "should be clean:" f
  end.

Ltac weak_fencepost term := 
  let fence f := progress (weak_fencepost f) in
  match term with
  | id_ ?A => idtac
  | ?f ∘ ?g => (* idtac f "∘" g; *) weak_fencepost f; weak_fencepost g
  (* | ?f ⊗ id_ _ => fence f  (* ; idtac "fix:"; print_state *)
  | id_ _ ⊗ ?f => fence f  (* ; idtac "fix:"; print_state *) *)
  | (?f ∘ ?g) ⊗ (?h ∘ ?i) => first [
    (* first [fence f | fence g | fence h | fence i]; 
      rewrite ?assoc; weak_fencepost term | *)
    rewrite (compose2_map f g h i); 
      weak_fencepost (f⊗h); weak_fencepost (g⊗i)]
  | (?f ∘ ?g) ⊗ ?h => first [
    (* first [fence f | fence g | fence h]; 
      rewrite ?assoc; weak_fencepost term | *)
    rewrite (stack_distr_pushout_r_bot f g h)]
  | ?f ⊗ (?g ∘ ?h) => first [
    (* first [fence f | fence g | fence h]; 
      idtac term; rewrite ?assoc; idtac term; weak_fencepost term | *)
    rewrite (stack_distr_pushout_r_top f g h)]
  | ?f ⊗ ?g => first [
    (* first [fence f | fence g]; 
      rewrite ?assoc; weak_fencepost term | *)
    rewrite <- (nwire_stackcompose_topright_general f g)]
  (* | ?f ⊗ ?g => idtac f "⊗" g; match type of f with
    | ?topIn ~> ?topOut => match type of g with
    | ?botIn ~> ?botOut => rewrite <- (nwire_stackcompose_topright_general f g);
      __fencepost (f ⊗ c_identity botIn); __fencepost (c_identity topOut ⊗ g)
    end end *)
  | ?f => idtac "should be clean:" f
  end.

Ltac weak_fencepost' term := 
  match term with
  | id_ ?A => idtac
  | ?f ∘ ?g => (* idtac f "∘" g; *) weak_fencepost f; weak_fencepost g
  (* | ?f ⊗ id_ _ => fence f  (* ; idtac "fix:"; print_state *)
  | id_ _ ⊗ ?f => fence f  (* ; idtac "fix:"; print_state *) *)
  | (?f ∘ ?g) ⊗ (?h ∘ ?i) => first [
    (* first [fence f | fence g | fence h | fence i]; 
      rewrite ?assoc; weak_fencepost term | *)
    rewrite (compose2_map f g h i); 
      weak_fencepost (f⊗h); weak_fencepost (g⊗i)]
  | (?f ∘ ?g) ⊗ ?h => first [
    (* first [fence f | fence g | fence h]; 
      rewrite ?assoc; weak_fencepost term | *)
    rewrite (stack_distr_pushout_r_bot f g h)]
  | ?f ⊗ (?g ∘ ?h) => first [
    (* first [fence f | fence g | fence h]; 
      idtac term; rewrite ?assoc; idtac term; weak_fencepost term | *)
    rewrite (stack_distr_pushout_r_top f g h)]
  | ?f ⊗ ?g => first [
    (* first [fence f | fence g]; 
      rewrite ?assoc; weak_fencepost term | *)
    rewrite <- (nwire_stackcompose_topright_general f g)]
  (* | ?f ⊗ ?g => idtac f "⊗" g; match type of f with
    | ?topIn ~> ?topOut => match type of g with
    | ?botIn ~> ?botOut => rewrite <- (nwire_stackcompose_topright_general f g);
      __fencepost (f ⊗ c_identity botIn); __fencepost (c_identity topOut ⊗ g)
    end end *)
  | ?f => idtac "should be clean:" f
  end.

Definition cast_fn {C : Type} `{Category C} (A B : C) {A' B' : C} 
  (prfA : A = A') (prfB : B = B') (f : A' ~> B') : A ~> B.
Proof.
  destruct prfA.
  destruct prfB.
  exact f.
Defined.

Add Parametric Morphism {C : Type} `{cC : Category C} {A B : C} {A' B' : C}
  {prfA : A = A'} {prfB : B = B'} : (@cast_fn C cC A B A' B' prfA prfB)
  with signature
  (@Category.equiv C cC A' B') ==> (@Category.equiv C cC A B) as cast_fn_equiv_morphism.
Proof.
  intros. 
  subst.
  easy.
Qed.

Local Close Scope Cat.
