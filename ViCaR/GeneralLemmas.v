Require Import Category.
Require Import Monoidal.
Require Import Setoid.

Section GeneralLemmas.

Local Open Scope Cat.

Context {C : Type} {cC : Category C} {cCh : CategoryCoherence cC}
  {mC : MonoidalCategory cC} {mCh : MonoidalCategoryCoherence mC}.

Lemma compose_simplify_general : forall 
  {A B M : C} (f1 f3 : A ~> B) (f2 f4 : B ~> M),
  f1 ≃ f3 -> f2 ≃ f4 -> (f1 ∘ f2) ≃ (f3 ∘ f4).
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma stack_simplify_general : forall 
  {A B M N : C} (f1 f3 : A ~> B) (f2 f4 : M ~> N),
  f1 ≃ f3 -> f2 ≃ f4 -> (f1 ⊗ f2) ≃ (f3 ⊗ f4).
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma stack_distr_pushout_r_bot : forall
  {a b d m n} (f : a ~> b) (g : b ~> d) (h : m ~> n),
  (f ∘ g) ⊗ h ≃ f ⊗ h ∘ (g ⊗ (id_ n)).
Proof.
  intros.
  rewrite <- tensor_compose, right_unit.
  easy.
Qed.

Lemma stack_distr_pushout_r_top : forall
  {a b m n o} (f : a ~> b) (g : m ~> n) (h : n ~> o),
  f ⊗ (g ∘ h) ≃ f ⊗ g ∘ (id_ b ⊗ h).
Proof.
  intros.
  rewrite <- tensor_compose, right_unit.
  easy.
Qed.

Lemma stack_distr_pushout_l_bot : forall
  {a b d m n} (f : a ~> b) (g : b ~> d) (h : m ~> n),
  (f ∘ g) ⊗ h ≃ f ⊗ (id_ m) ∘ (g ⊗ h).
Proof.
  intros.
  rewrite <- tensor_compose, left_unit.
  easy.
Qed.

Lemma stack_distr_pushout_l_top : forall 
  {a b m n o} (f : a ~> b) (g : m ~> n) (h : n ~> o),
  f ⊗ (g ∘ h) ≃ id_ a ⊗ g ∘ (f ⊗ h).
Proof.
  intros.
  rewrite <- tensor_compose, left_unit.
  easy.
Qed.






Lemma nwire_stack_compose_topleft_general : forall
  {topIn botIn topOut botOut : C} 
  (f0 : botIn ~> botOut) (f1 : topIn ~> topOut),
  ((c_identity topIn) ⊗ f0) ∘ (f1 ⊗ (c_identity botOut)) ≃ (f1 ⊗ f0).
Proof.
  intros.
  rewrite <- tensor_compose.
  rewrite left_unit; rewrite right_unit.
  easy.
Qed.

Lemma nwire_stackcompose_topright_general : forall
  {topIn botIn topOut botOut : C} 
  (f0 : topIn ~> topOut) (f1 : botIn ~> botOut),
  (f0 ⊗ (c_identity botIn)) ∘ ((c_identity topOut) ⊗ f1) ≃ (f0 ⊗ f1).
Proof.
  intros.
  rewrite <- tensor_compose.
  rewrite right_unit, left_unit.
  easy.
Qed.

Lemma stack_id_compose_split_top : forall 
  {topIn topMid topOut bot : C} 
  (f0 : topIn ~> topMid) (f1 : topMid ~> topOut),
  (f0 ∘ f1) ⊗ (id_ bot) ≃ f0 ⊗ id_ bot ∘ (f1 ⊗ id_ bot).
Proof.
  intros.
  rewrite <- tensor_compose, left_unit.
  easy.
Qed.

Lemma stack_id_compose_split_bot : forall 
  {top botIn botMid botOut : C} 
  (f0 : botIn ~> botMid) (f1 : botMid ~> botOut),
  (id_ top) ⊗ (f0 ∘ f1) ≃ id_ top ⊗ f0 ∘ (id_ top ⊗ f1).
Proof.
  intros.
  rewrite <- tensor_compose, left_unit.
  easy.
Qed.

Local Close Scope Cat.

End GeneralLemmas. 
