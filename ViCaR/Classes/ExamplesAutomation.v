From VyZX Require Import PermutationAutomation.
Require Import String.

Ltac print_state :=
  try (match goal with | H : ?p |- _ => idtac H ":" p; fail end);
  idtac "---------------------------------------------------------";
  match goal with |- ?P => idtac P; idtac "" 
end.

Ltac is_C0 x := assert (x = C0) by (cbv; lca).

Ltac is_C1 x := assert (x = C1) by (cbv; lca).

Tactic Notation "print_C" constr(x) := (tryif is_C0 x then constr:("0"%string) else
  tryif is_C1 x then constr:("1"%string) else constr:("X"%string)).

Ltac print_LHS_matU :=
  intros;
  (let i := fresh "i" in
  let j := fresh "j" in
  let Hi := fresh "Hi" in
  let Hj := fresh "Hj" in
  intros i j Hi Hj; try solve_end;
    repeat (* Enumerate rows and columns; see `by_cell` *)
    (destruct i as [| i]; [  | apply <- Nat.succ_lt_mono in Hi ];
    try solve_end); clear Hi;
    repeat
    (destruct j as [| j]; [  | apply <- Nat.succ_lt_mono in Hj ];
    try solve_end); clear Hj
  );
  match goal with |- ?x = ?y ?i ?j => autounfold with U_db; simpl; 
  match goal with
  | |- ?x = _ => 
    tryif is_C0 x then idtac "A[" i "," j "] = 0" else
    tryif is_C1 x then idtac "A[" i "," j "] = 1" else
      idtac "A[" i "," j "] = X"
  end
end.

Ltac simpl_bools :=
  repeat (simpl; rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r). 

Ltac simplify_bools_lia_one_free :=
  let act_T b := ((replace_bool_lia b true || replace_bool_lia b false); simpl) in 
  let act_F b := ((replace_bool_lia b false || replace_bool_lia b true); simpl) in 
  match goal with
  | |- context[?b && _] => act_F b; rewrite ?andb_true_l, ?andb_false_l
  | |- context[_ && ?b] => act_F b; rewrite ?andb_true_r, ?andb_false_r
  | |- context[?b || _] => act_T b; rewrite ?orb_true_l, ?orb_false_l
  | |- context[_ || ?b] => act_T b; rewrite ?orb_true_r, ?orb_false_r
  | |- context[negb ?b] => act_T b; simpl negb
  | |- context[if ?b then _ else _] => act_T b
  end; simpl_bools.

Ltac simplify_bools_lia_one_kernel :=
  let fail_if_iffy H :=
    match H with
    | context [ if _ then _ else _ ] => fail 1
    | _ => idtac
    end
  in
  let fail_if_compound H := 
    fail_if_iffy H;
    match H with
    | context [ ?a && ?b   ] => fail 1
    | context [ ?a || ?b   ] => fail 1
    | _ => idtac
    end
  in 
  let act_T b := (fail_if_compound b; 
    (replace_bool_lia b true || replace_bool_lia b false); simpl) in 
  let act_F b := (fail_if_compound b; 
    (replace_bool_lia b false || replace_bool_lia b true); simpl) in 
  match goal with
  | |- context[?b && _] => act_F b; rewrite ?andb_true_l, ?andb_false_l
  | |- context[_ && ?b] => act_F b; rewrite ?andb_true_r, ?andb_false_r
  | |- context[?b || _] => act_T b; rewrite ?orb_true_l, ?orb_false_l
  | |- context[_ || ?b] => act_T b; rewrite ?orb_true_r, ?orb_false_r
  | |- context[negb ?b] => act_T b; simpl negb
  | |- context[if ?b then _ else _] => act_T b
  end; simpl_bools.

Ltac simplify_bools_lia_one :=
  simplify_bools_lia_one_kernel || simplify_bools_lia_one.

Ltac simplify_bools_lia :=
  repeat simplify_bools_lia_one.

Ltac bdestruct_one_old := 
  let fail_if_iffy H :=
  match H with
  | context [ if _ then _ else _ ] => fail 1
  | _ => idtac
  end
  in
  match goal with
  | |- context [ ?a <? ?b ] =>
      fail_if_iffy a; fail_if_iffy b; bdestruct (a <? b)
  | |- context [ ?a <=? ?b ] =>
        fail_if_iffy a; fail_if_iffy b; bdestruct (a <=? b)
  | |- context [ ?a =? ?b ] =>
        fail_if_iffy a; fail_if_iffy b; bdestruct (a =? b)
  | |- context [ if ?b then _ else _ ] => fail_if_iffy b; destruct b eqn:?
  end.

Ltac bdestruct_one_new :=
  let fail_if_iffy H :=
    match H with
    | context [ if _ then _ else _ ] => fail 1
    | _ => idtac
    end
  in
  let fail_if_booley H := 
    fail_if_iffy H;
    match H with
    | context [ ?a <? ?b   ] => fail 1
    | context [ ?a <=? ?b  ] => fail 1
    | context [ ?a =? ?b   ] => fail 1
    | context [ ?a && ?b   ] => fail 1
    | context [ ?a || ?b   ] => fail 1
    | context [ negb ?a    ] => fail 1
    | context [ xorb ?a ?b ] => fail 1
    | _ => idtac
    end
  in 
  let rec destruct_kernel H :=
    match H with
    | context [ if ?b then _ else _ ] => destruct_kernel b
    | context [ ?a <? ?b   ] => 
      tryif fail_if_booley a then 
      (tryif fail_if_booley b then bdestruct (a <? b)
       else destruct_kernel b) else (destruct_kernel a)
    | context [ ?a <=? ?b  ] => 
      tryif fail_if_booley a then 
      (tryif fail_if_booley b then bdestruct (a <=? b)
       else destruct_kernel b) else (destruct_kernel a)
    | context [ ?a =? ?b   ] => 
      tryif fail_if_booley a then 
      (tryif fail_if_booley b then bdestruct (a =? b); try subst
       else destruct_kernel b) else (destruct_kernel a)
    | context [ ?a && ?b   ] => 
      destruct_kernel a || destruct_kernel b
    | context [ ?a || ?b   ] => 
      destruct_kernel a || destruct_kernel b
    | context [ xorb ?a ?b ] => 
      destruct_kernel a || destruct_kernel b
    | context [ negb ?a    ] =>
      destruct_kernel a
    | _ => idtac
    end
  in 
  simpl_bools;
  match goal with
  | |- context [ ?a =? ?b ] =>
        fail_if_iffy a; fail_if_iffy b; bdestruct (a =? b); try subst
  | |- context [ ?a <? ?b ] =>
      fail_if_iffy a; fail_if_iffy b; bdestruct (a <? b)
  | |- context [ ?a <=? ?b ] =>
        fail_if_iffy a; fail_if_iffy b; bdestruct (a <=? b)
  | |- context [ if ?b then _ else _ ] => fail_if_iffy b; destruct b eqn:?
  end;
  simpl_bools.

Ltac bdestruct_one' := bdestruct_one_new || bdestruct_one_old.

Ltac bdestructΩ'simp :=
  let tryeasylia := try easy; try lca; try lia in
  tryeasylia;
  repeat (bdestruct_one; subst; simpl_bools; simpl; tryeasylia); tryeasylia.


Ltac simplify_mods_one :=
  let __fail_if_has_mods a :=
   match a with
   | context [ _ mod _ ] => fail 1
   | _ => idtac
   end
  in
  match goal with
  | |- context [ ?a mod ?b ] =>
        __fail_if_has_mods a; __fail_if_has_mods b;
        simplify_mods_of a b
  | H:context [ ?a mod ?b ] |- _ =>
        __fail_if_has_mods a; __fail_if_has_mods b;
        simplify_mods_of a b
  end.

Ltac case_mods_one := 
  match goal with
  | |- context [ ?a mod ?b ] =>
        bdestruct (a <? b);
        [ rewrite (Nat.mod_small a b) by lia
        | try rewrite (mod_n_to_2n a b) by lia ]
  end.



#[export] Hint Extern 4 (WF_Matrix (@Mmult ?m ?n ?o ?A ?B)) => (
  match type of A with Matrix ?m' ?n' =>
  match type of B with Matrix ?n'' ?o'' =>
  let Hm' := fresh "Hm'" in let Hn' := fresh "Hn'" in
  let Hn'' := fresh "Hn''" in let Ho'' := fresh "Hoo'" in
  assert (Hm' : m = m') by lia;
  assert (Hn' : n = n') by lia;
  assert (Hn'' : n = n'') by lia;
  assert (Ho' : o = o'') by lia;
  replace (@Mmult m n o A B) with (@Mmult m' n' o A B) 
    by (first [try (rewrite Hm' at 1); try (rewrite Hn' at 1); reflexivity | f_equal; lia]);
  apply WF_mult; [
    auto with wf_db |
    apply WF_Matrix_dim_change;
    auto with wf_db
  ]
  end end) : wf_db.