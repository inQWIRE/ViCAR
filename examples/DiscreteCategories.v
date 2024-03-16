From ViCaR Require Import CategoryTypeclass.

Close Scope Cat_scope.

From mathcomp Require Import fintype eqtype ssrnat.

Open Scope Cat_scope.
Require Import TypesExample.
Open Scope bool_scope.

#[program] Definition DiscreteCategory {n} : Category ('I_ n) := {|
  morphism := fun m k => if m == k then True else False;
  c_equiv := fun n m f g => 
    if (n == m) then True else False;
  compose := fun n m k f g => 
    if (n==m) && (m == k) then _ else _
|}.
Next Obligation.
  split.
  - intros ?.
    destruct (A =P B) as [H|H]; easy.
  - intros f g h.
    destruct ( A =P B) as [H | H]; easy.
  - intros f.
    destruct (A =P B) as [H'|H']; easy.
Qed.
Admit Obligations.