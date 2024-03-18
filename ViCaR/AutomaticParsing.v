Require Import CategoryTypeclass.

Open Scope Cat_scope.
Open Scope Mor_scope.
Open Scope Mon_scope.

Inductive cat_expr {C} {cC : Category C}
    : forall {A B : C}, A ~> B -> Prop := 
  | cat_id {A : C} : cat_expr (id_ A)
  | cat_const {A B : C} (f : A ~> B) 
    : cat_expr f
  | cat_compose {A B M : C} (f : A ~> M) (g : M ~> B) 
    : cat_expr (f ∘ g).

Arguments cat_expr {_} _%Cat {_ _}%Obj _%Mor.

Inductive moncat_expr {C} {cC : Category C} {mC : MonoidalCategory cC}
    : forall {A B : C}, A ~> B -> Prop :=
  | moncat_id (A : C) 
    : moncat_expr (id_ A)
  | moncat_assoc_for (A B M : C)
    : moncat_expr (associator A B M).(forward)
  | moncat_assoc_rev (A B M : C)
    : moncat_expr (associator A B M).(reverse)
  | moncat_lunit_for (A : C)
    : moncat_expr (left_unitor A).(forward)
  | moncat_lunit_rev (A : C)
    : moncat_expr (left_unitor A).(reverse)
  | moncat_runit_for (A : C) 
    : moncat_expr (right_unitor A).(forward)
  | moncat_runit_rev (A : C) 
    : moncat_expr (right_unitor A).(reverse)
  | moncat_compose {A B M : C} {f : A ~> B} {g : B ~> M}
    : moncat_expr f -> moncat_expr g -> moncat_expr (f ∘ g)
  | moncat_tensor {A1 A2 B1 B2 : C} {f : A1 ~> A2} {g : B1 ~> B2}
    : moncat_expr f -> moncat_expr g -> moncat_expr (f ⊗ g)
  | moncat_const {A B : C} (f : A ~> B) 
    : moncat_expr f.

Arguments moncat_expr {_} {_}%Cat _%Cat {_ _}%Obj _%Mor.

Ltac make_moncat_expr (* mC *) t :=
  let rec make_mon (* mC *) t :=
  (* lazymatch type of mC with
  | @MonoidalCategory ?C ?cC => *)
  match t with
  | id_ ?A => constr:(moncat_id A)
  | (associator ?A ?B ?C).(forward) => constr:(moncat_assoc_for A B C)
  | (associator ?A ?B ?C).(forward) => constr:(moncat_assoc_for A B C)
  | (left_unitor ?A).(forward) => constr:(moncat_lunit_for A)
  | (left_unitor ?A).(reverse) => constr:(moncat_lunit_rev A)
  | (right_unitor ?A).(forward) => constr:(moncat_runit_for A)
  | (right_unitor ?A).(reverse) => constr:(moncat_runit_rev A)
  | (?g ∘ ?h)%Mor => let mcg := make_mon g in let mch := make_mon h in 
      constr:(moncat_compose mcg mch)
  | (?g ⊗ ?h)%Mon => let mcg := make_mon g in let mch := make_mon h in 
      constr:(moncat_tensor mcg mch)
  | _ => constr:(moncat_const t)
  end
  (* end *)
  in make_mon (* mC *) t.

Ltac make_moncat_expr_debug (* mC *) t :=
  let rec make_mon (* mC *) t :=
  (* lazymatch type of mC with
  | @MonoidalCategory ?C ?cC => *)
  lazymatch t with
  | id_ ?A => 
      
    constr:(moncat_id A)
  | (associator ?A ?B ?C).(forward) => 
    constr:(moncat_assoc_for A B C)
  | (associator ?A ?B ?C).(forward) => 
    constr:(moncat_assoc_for A B C)
  | (left_unitor ?A).(forward) => constr:(moncat_lunit_for A)
  | (left_unitor ?A).(reverse) => constr:(moncat_lunit_rev A)
  | (right_unitor ?A).(forward) => constr:(moncat_runit_for A)
  | (right_unitor ?A).(reverse) => constr:(moncat_runit_rev A)
  | (?g ∘ ?h)%Mor => let mcg := make_mon g in let mch := make_mon h in 
      constr:(moncat_compose mcg mch)
  | (?g ⊗ ?h)%Mon => let mcg := make_mon g in let mch := make_mon h in 
      constr:(moncat_tensor mcg mch)
  | _ => constr:(moncat_const t)
  end
  (* end *)
  in make_mon (* mC *) t.

Require Import String.

(* Definition moncat_to_str :  *)

Lemma parse_test_0 : forall {C : Type}
  {cC : Category C} {mC : MonoidalCategory cC}
  {top botIn botMid botOut : C} 
  (f0 : botIn ~> botMid) (f1 : botMid ~> botOut),
  (id_ top) ⊗ (f0 ∘ f1) ≃ id_ top ⊗ f0 ∘ (id_ top ⊗ f1).
Proof.
  intros.
  match goal with 
  |- (?t ≃ ?t')%Cat => let mct := make_moncat_expr_debug t in pose mct;
    let mct' := make_moncat_expr_debug t' in pose mct'
  end.
  Admitted.

Lemma parse_test_1 : forall {C : Type}
  {cC : Category C} {mC : MonoidalCategory cC}
  {top botIn botMid botOut : C} 
  (f0 : botIn ~> botMid) (f1 : botMid ~> botOut),
  (id_ top) ⊗ (f0 ∘ f1) ∘ (λ_ _)^-1 ≃ id_ top ⊗ f0 ∘ (id_ top ⊗ f1) ∘ (λ_ _)^-1.
Proof.
  intros.
  match goal with 
  |- (?t ≃ ?t')%Cat => let mct := make_moncat_expr_debug t in pose mct;
    let mct' := make_moncat_expr_debug t' in pose mct'
  end.
  Admitted.


Ltac print_moncat_expr m :=
  first [lazymatch m with
  | moncat_id ?A => 
    idtac "['id', (1), (1), ['" A "'], 'id_{&1}']"
    (* : moncat_expr (id_ A) *)
  | moncat_assoc_for ?A ?B ?M => 
    idtac "['assoc_for', ((1,2),3), (1,(2,3)), ['" A "','" B "','" M "'], 'α^-1_{&1,&2,&3}']"
    (* : moncat_expr (associator A B M).(forward) *)
  | moncat_assoc_rev ?A ?B ?M => 
    idtac "['assoc_rev', ((1,2),3), (1,(2,3)), ['" A "','" B "','" M "'], 'α_{&1,&2,&3}']"
    (* : moncat_expr (associator A B M).(reverse) *)
  | moncat_lunit_for ?A =>
    idtac "['lunit_for', ('I',1), (1), ['" A "'], 'λ_{&1}']"
    (* : moncat_expr (left_unitor A).(forward) *)
  | moncat_lunit_rev ?A => 
    idtac "['lunit_rev', (1), ('I',1), ['" A "'], 'λ^-1_{&1}']"
    (* : moncat_expr (left_unitor A).(reverse) *)
  | moncat_runit_for ?A =>
    idtac "['runit_for', (1,'I'), (1), ['" A "'], 'ρ_{&1}']"
    (* : moncat_expr (right_unitor A).(forward) *)
  | moncat_runit_rev ?A =>
    idtac "['runit_rev', (1), (1,'I'), ['" A "'], 'ρ^-1_{&1}']"
    (* : moncat_expr (right_unitor A).(reverse) *)
  | @moncat_compose _ _ _ ?A ?B ?M _ _ ?mcf ?mcg =>
    idtac "['*compose', (1), (2), ['" A "','" M "'], [";
    print_moncat_expr mcf; idtac ","; print_moncat_expr mcg; idtac "]]"
    (* : moncat_expr f -> moncat_expr g -> moncat_expr (f ∘ g) *)
  | @moncat_tensor _ _ _ ?A1 ?A2 ?B1 ?B2 _ _ ?mcf ?mcg =>
    idtac "['*tensor', (1,2), (3,4), ['" A1 "','" B1 "','" A2 "','" B2 "'], [";
    print_moncat_expr mcf; idtac ","; print_moncat_expr mcg; idtac "]]"
    (* : moncat_expr g -> moncat_expr h -> moncat_expr (g ⊗ h) *)
  | @moncat_const _ _ _ ?A ?B ?f =>
    idtac "['const', ('" A "'), ('" A "'), '" f "']"
    (* : moncat_expr f. *)
  end | idtac "BAD EXPR" m].


Ltac print_moncat_expr_JSON m :=
  first [lazymatch m with
  | moncat_id ?A => 
    idtac "['id', [1], [1], ['"A"'], 'id_{&1}']"
    (* : moncat_expr (id_ A) *)
  | moncat_assoc_for ?A ?B ?M => 
    idtac "['assoc_for', [[1,2],3], [1,[2,3]], ['"A"','"B"','"M"'], 'α^-1_{&1,&2,&3}']"
    (* : moncat_expr (associator A B M).(forward) *)
  | moncat_assoc_rev ?A ?B ?M => 
    idtac "['assoc_rev', [[1,2],3], [1,[2,3]], ['"A"','"B"','"M"'], 'α_{&1,&2,&3}']"
    (* : moncat_expr (associator A B M).(reverse) *)
  | moncat_lunit_for ?A =>
    idtac "['lunit_for', ['I',1], [1], ['"A"'], 'λ_{&1}']"
    (* : moncat_expr (left_unitor A).(forward) *)
  | moncat_lunit_rev ?A => 
    idtac "['lunit_rev', [1], ['I',1], ['"A"'], 'λ^-1_{&1}']"
    (* : moncat_expr (left_unitor A).(reverse) *)
  | moncat_runit_for ?A =>
    idtac "['runit_for', [1,'I'], [1], ['"A"'], 'ρ_{&1}']"
    (* : moncat_expr (right_unitor A).(forward) *)
  | moncat_runit_rev ?A =>
    idtac "['runit_rev', [1], [1,'I'], ['"A"'], 'ρ^-1_{&1}']"
    (* : moncat_expr (right_unitor A).(reverse) *)
  | @moncat_compose _ _ _ ?A ?B ?M _ _ ?mcf ?mcg =>
    idtac "['*compose', [1], [2], ['"A"','"M"'], [";
    print_moncat_expr mcf; idtac ","; print_moncat_expr mcg; idtac "]]"
    (* : moncat_expr f -> moncat_expr g -> moncat_expr (f ∘ g) *)
  | @moncat_tensor _ _ _ ?A1 ?A2 ?B1 ?B2 _ _ ?mcf ?mcg =>
    idtac "['*tensor', [1,2], [3,4], ['"A1"','"B1"','"A2"','"B2"'], [";
    print_moncat_expr mcf; idtac ","; print_moncat_expr mcg; idtac "]]"
    (* : moncat_expr g -> moncat_expr h -> moncat_expr (g ⊗ h) *)
  | @moncat_const _ _ _ ?A ?B ?f =>
    idtac "['const', ['"A"'], ['"A"'], '"f"']"
    (* : moncat_expr f. *)
  end | idtac "BAD EXPR" m].

Lemma print_test_0 : forall {C : Type}
  {cC : Category C} {mC : MonoidalCategory cC}
  {top botIn botMid botOut : C} 
  (f0 : botIn ~> botMid) (f1 : botMid ~> botOut),
  (id_ top) ⊗ (f0 ∘ f1) ≃ id_ top ⊗ f0 ∘ (id_ top ⊗ f1).
Proof.
  intros.
  match goal with 
  |- (?t ≃ ?t')%Cat => let mct := make_moncat_expr_debug t in print_moncat_expr_JSON mct
    (* let mct' := make_moncat_expr_debug t' in pose mct' *)
  end.
  Admitted.

Lemma print_test_1 : forall {C : Type}
  {cC : Category C} {mC : MonoidalCategory cC}
  {top botIn botMid botOut : C} 
  (f0 : botIn ~> botMid) (f1 : botMid ~> botOut),
  (id_ top) ⊗ (f0 ∘ f1) ∘ (λ_ _)^-1 ≃ id_ top ⊗ f0 ∘ (id_ top ⊗ f1) ∘ (λ_ _)^-1.
Proof.
  intros.
  match goal with 
  |- (?t ≃ ?t')%Cat => let mct := make_moncat_expr_debug t in pose mct;
    let mct' := make_moncat_expr_debug t' in pose mct'
  end.
  Admitted.
