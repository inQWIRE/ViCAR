Require CategoryTypeclass.
Import -(notations) CategoryTypeclass.
Delimit Scope Cat_scope with Cat.

Notation "'id_' A" := (c_identity A%Cat) 
  (at level 15, A at next level, no associativity) : Cat_scope.
Notation "A ~> B" := (morphism _%Cat A%Cat B%Cat)
  (at level 70, B at next level, no associativity) : Cat_scope.
Notation "f ≃ g" := (c_equiv _%Cat f%Cat g%Cat) 
  (at level 70, g at next level) : Cat_scope. (* \simeq *)
Notation "f ∘ g" := (compose _%Cat f%Cat g%Cat) 
  (at level 40, g at next level, left associativity) : Cat_scope. (* \circ *)

Notation "'catI'" := (mon_I _%Cat) (at level 0) : Cat_scope.
Notation "A '∗' B" := (obj_tensor _%Cat A%Cat B%Cat)
  (at level 34, left associativity) : Cat_scope. (* \ast *)
Notation "f '⧆' g" := (mor_tensor _%Cat f%Cat g%Cat) 
  (at level 34, left associativity) : Cat_scope . (* \otimes *)  
Notation "'α_' A , B , M" := 
  (associator A%Cat B%Cat M%Cat)
  (at level 20, no associativity) : Cat_scope. (* \alpha *)
Notation "'λ_' x" := (left_unitor x) 
  (at level 20, no associativity) : Cat_scope. (* \lambda \^- \^1 *) 
Notation "'ρ_' x" := (right_unitor x)
  (at level 20, no associativity) : Cat_scope. (* \rho \^- \^1 *) 
Notation "'β_' x , y" := (braiding _%Cat x%Cat y%Cat) 
  (at level 20) : Cat_scope.
Notation "f '⁻¹'" := (reverse f%Cat) (at level 25) : Cat_scope. (* \^- \^1 *)

Notation "A '<~>' B" := (Isomorphism A%Cat B%Cat) (at level 70) : Cat_scope.
