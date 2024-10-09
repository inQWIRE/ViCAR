From ViCaR Require CategoryTypeclass.
From Examples Require CatExample. (* FunctorCategory *)



Section DiscreteCategory.

Set Universe Polymorphism.

Import CategoryTypeclass.

#[universes(polymorphic=yes),
  program] Definition DiscreteCategory (N : Type) : Category N := {|
  morphism := @eq N;
  c_equiv := fun _ _ _ _ => True;
  c_identity := @eq_refl N
|}.

#[universes(polymorphic=yes),
 export, program] Instance DiscreteCategoryCoherence (N : Type) 
  : CategoryCoherence (DiscreteCategory N) := {
}.
Solve All Obligations with easy.

End DiscreteCategory.

Section Bifunctor_of_FunctorCategoryFunctor.

Import CategoryTypeclass CatExample (FunctorCategory).

Set Universe Polymorphism.

#[export, program] 
  Instance Bifunctor_of_FunctorCategoryFunctor 
  {C D E : Type} {cC : Category C} {cD : Category D} {cE : Category E}
  (* {cCh : CategoryCoherence cC} *) 
  {cDh : CategoryCoherence cD} {cEh : CategoryCoherence cE} 
  (F : Functor cC (FunctorCategory (cC:=cD) (cD:=cE))) :
  Bifunctor cC cD cE := {
  obj_bimap := F.(obj_map);
  morphism_bimap := fun A1 B1 A2 B2 f1 f2 => 
    (F A1 @ f2 ∘ component_map (F.(morphism_map) f1) B2)%Cat
}.
Next Obligation.
  (* rewrite (F A1).(id_map), left_unit. *)
  rewrite component_map_natural.
  rewrite (F A1).(id_map), right_unit.
  apply F.
Qed.
Next Obligation.
  symmetry.
  rewrite assoc, <- (assoc _ (F B1 @ g2)%Cat).
  rewrite <- component_map_natural.
  rewrite compose_map.
  rewrite 2!assoc.
  apply compose_cancel_l, compose_cancel_l.
  symmetry.
  apply F.
Qed.
Next Obligation.
  rewrite H0.
  pose proof (F.(morphism_compat) f f' ltac:(assumption)) as e.
  simpl in e.
  hnf in e.
  rewrite e.
  easy.
Qed.

Unset Universe Polymorphism.

End Bifunctor_of_FunctorCategoryFunctor.

Section Groupoid.

(* Set Universe Polymorphism. *)

Import CategoryTypeclass.

#[universes(polymorphic=yes,cumulative=yes)]
Class IsGroupoid {C} (cC : Category C) := {
  groupoid_inv {A B : C} (f : (A ~> B)%Cat) : (B ~> A)%Cat;
  groupoid_inv_is_inv {A B : C} (f : (A ~> B)%Cat) : 
    (is_inverse f (groupoid_inv f))%Cat
}. 

End Groupoid.