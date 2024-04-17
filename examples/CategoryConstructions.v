From ViCaR Require Import CategoryTypeclass.

Section Constructions.

Local Open Scope Cat_scope.
Generalizable Variable C.

Context {C : Type} {cC : Category C}.

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

Context {cCh : CategoryCoherence cC}.

Lemma prod_mor_unique' {A B AB : C} 
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

Definition category_product_unique (A B : C) :
  forall {AB AB'} (HAB : CategoryProduct A B AB) 
  (HAB' : CategoryProduct A B AB'), Isomorphism AB AB'.
  refine (fun AB AB' HAB HAB' =>
  {|
    forward := HAB'.(prod_mor) AB p_A p_B;
    reverse := HAB.(prod_mor) AB' p_A p_B;
  |}).
  split; eapply (prod_mor_unique' _ p_A p_B); rewrite 1?cCh.(assoc).
  1,5: rewrite 2!(proj1 (prod_mor_prop _ _ _)); easy.
  1,4: rewrite 2!(proj2 (prod_mor_prop _ _ _)); easy.
  all: rewrite cCh.(left_unit); easy.
Qed.

Class CartesianMonoidalCategory (mC : MonoidalCategory cC) := {
  tensor_cartesian : forall (A B : C),
    CategoryProduct A B (A × B);
}.


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

Lemma big_prod_mor_unique' {J} {obj : J -> C} {pJ : C} 
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

Obligation Tactic := idtac.

Program Definition category_big_prod_unique {J} {obj : J->C} :
  forall {pJ pJ'} (HI : CategoryBigProd obj pJ) (HI' : CategoryBigProd obj pJ'), 
    Isomorphism pJ pJ' :=
  fun pJ pJ' HI HI' =>
  {|
    forward := HI'.(big_prod_mor) pJ p_i;
    reverse := HI.(big_prod_mor) pJ' p_i;
  |}.
Next Obligation.
  split; eapply (big_prod_mor_unique' _ p_i); rewrite 1?assoc.
  1,3: intros i; rewrite cCh.(assoc), 2!(big_prod_mor_prop _ _); easy.
  all: intros; rewrite cCh.(left_unit); easy.
Qed.

(* Require Import FunctionalExtensionality. *)


Class CategoryCoproduct (A B : C) (A_B : C) := {
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

Lemma coprod_mor_unique' {A B A_B : C} 
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

Program Definition category_coproduct_unique (A B : C) :
  forall {A_B A_B'} (HA_B : CategoryCoproduct A B A_B) 
  (HA_B' : CategoryCoproduct A B A_B'), Isomorphism A_B A_B' :=
  fun A_B A_B' HA_B HA_B' =>
  {|
    forward := HA_B.(coprod_mor) A_B' iota_A iota_B;
    reverse := HA_B'.(coprod_mor) A_B iota_A iota_B;
  |}.
Next Obligation.
  split; eapply (coprod_mor_unique' _ iota_A iota_B); rewrite <- 1?cCh.(assoc).
  1,5: rewrite 2!(proj1 (coprod_mor_prop _ _ _)); easy.
  1,4: rewrite 2!(proj2 (coprod_mor_prop _ _ _)); easy.
  all: rewrite cCh.(right_unit); easy.
Qed.

Class CategoryBigCoprod {J : Type} 
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


Reserved Notation "A ∏ B" (at level 34).
Reserved Notation "f @∏ g" (at level 34).

Class Category_with_Products (cC : Category C) := {
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

Notation "A ∏ B" := (cat_prod A B) (at level 34).
Notation "f @∏ g" := (cat_mor_prod f g) (at level 34).

#[program, export] Instance Category_with_Products_of_CartesianMonoidalCategory
  {mC : MonoidalCategory cC}
  (ccc : @CartesianMonoidalCategory mC) : Category_with_Products cC := {|
  cat_prod := mC.(obj_tensor);
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

Lemma limit_cone_factor_unique' {D} {cD : Category D} 
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

#[program] Definition limit_unique {D} {cD : Category D} 
  {F : Functor cD cC} (L L' : Limit F) : L.(cone_obj) <~> L'.(cone_obj) := {|
    forward := L'.(limit_cone_factor) L;
    reverse := L.(limit_cone_factor) L'
  |}.
Next Obligation.
  split; (apply limit_cone_factor_unique'; 
    [| intros; rewrite cCh.(left_unit); easy]);
  intros; rewrite cCh.(assoc), 2!limit_cone_factor_prop; easy.
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

Lemma colimit_cocone_factor_unique' {D} {cD : Category D} 
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

#[program] Definition colimit_unique {D} {cD : Category D} 
  {F : Functor cD cC} (L L' : Colimit F) : L.(cocone_obj) <~> L'.(cocone_obj) := {|
    forward := L.(colimit_cocone_factor) L';
    reverse := L'.(colimit_cocone_factor) L
  |}.
Next Obligation.
  split; (apply colimit_cocone_factor_unique'; 
    [| intros; rewrite cCh.(right_unit); easy]);
  intros; rewrite <- cCh.(assoc), 2!colimit_cocone_factor_prop; easy.
Qed.


Class Category_with_Small_Limits {C} (cC : Category C) := {
  take_set_limit : forall {D : Set} (cD : Category D) (F : Functor cD cC), Limit F;
}.

Class Category_with_Limits {C} (cC : Category C) := {
  take_limit : forall {D : Type} (cD : Category D) (F : Functor cD cC), Limit F;
}.

End Constructions.