Require Export Category.
Require Import ExamplesAutomation.

Local Open Scope Cat.

Class CastCategory {C : Type} (cC : Category C) : Type := {
  cast {A B A' B' : C} (HA : A = A') (HB : B = B') :
    A' ~> B' -> A ~> B;
  (* Will need some coherence conditions, probably 
    cast_id, cast_compose? Might be it. Oh, we may want 
    cast HA HB (cast (eq_sym HA) (eq_sym HB) f) ≃ f as 
    well, just giving bijectivity. All should be trivial
    for any sensible cast. This seems sufficient on no 
    reflection, so let's see how far it can go: *)
  cast_invertible {A B A' B' : C} 
  (HA : A' = A) (HB : B' = B) (HA' : A = A') (HB' : B = B') f : 
    cast HA' HB' (cast HA HB f) ≃ f;
}.

Definition CastCategory_of_DecEq_Category {C : Type} (cC: Category C) 
  (dec : forall A B : C, {A = B} + {A <> B}) :
  CastCategory cC := {|
  cast := fun A B A' B' HA HB =>
    match HA in (_ = a) return (a ~> B' -> A ~> B) with (* Tell coq that A = A' *)
    | eq_refl =>
      fun f => 
      match HB in (_ = a) return (A ~> a -> A ~> B) with 
      | eq_refl => fun f' => f'
      end f
    end;
  cast_invertible := ltac:(intros A B A' B' HA HB; 
    destruct HA, HB; intros HA' HB';
    rewrite (@Eqdep_dec.UIP_dec C dec A' _ _ (eq_refl));
    rewrite (@Eqdep_dec.UIP_dec C dec B' _ _ (eq_refl));
    reflexivity);
|}.