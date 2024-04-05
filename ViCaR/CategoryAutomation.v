Require Export CategoryTypeclass.

#[local] Set Universe Polymorphism.

Local Close Scope Cat_scope. (* We do _not_ want to be relying on the scope for 
  this automation to work! This will easily break things, as Ltac is not
  type-checked (so is functionally a macro and thus notation is 
  context-dependent). *)

Ltac print_state :=
  try (match goal with | H : ?p |- _ => idtac H ":" p; fail end);
  idtac "---------------------------------------------------------";
  match goal with |- ?P => idtac P 
end.

Ltac assert_not_dup x := 
  (* try match goal with *)
  try match goal with
  | f := ?T : ?T', g := ?T : ?T' |- _ => tryif unify x f then fail 2 else fail 1
  end.

Ltac saturate_instances class :=
  (progress repeat ( (* TODO: test to make sure, but || is supposed to progress, so this shouldn't need progress explicitly?*)
    let x:= fresh in let o := open_constr:(class _) in
    unshelve evar (x:o); [typeclasses eauto|]; 
    (* let t:= type of x in idtac x ":" t; *) assert_not_dup x))
  || (progress repeat (
    let x:= fresh in let o := open_constr:(class _ _) in
    unshelve evar (x:o); [typeclasses eauto|]; assert_not_dup x))
  || (progress repeat (
    let x:= fresh in let o := open_constr:(class _ _ _) in
    unshelve evar (x:o); [typeclasses eauto|]; assert_not_dup x))
  || (progress repeat (
    let x:= fresh in let o := open_constr:(class _ _ _ _) in
    unshelve evar (x:o); [typeclasses eauto|]; assert_not_dup x))
  || (progress repeat (
    let x:= fresh in let o := open_constr:(class _ _ _ _ _) in
    unshelve evar (x:o); [typeclasses eauto|]; assert_not_dup x))
  || (progress repeat (
    let x:= fresh in let o := open_constr:(class _ _ _ _ _ _) in
    unshelve evar (x:o); [typeclasses eauto|]; assert_not_dup x))
  || idtac.

Ltac fold_Category cC :=
  match type of cC with Category ?C =>
  let catify f := constr:(@f C cC) in
  let base_fn f := (let raw := catify f in
    let t := eval cbn in raw in constr:(t)) in
  let cat_fold f :=
    (let base := base_fn @f in 
    let catted := catify @f in
    change base with catted in * ) in
  try cat_fold @morphism; (* has issues, e.g., with ZX - 
    might be fixable, but likely not necessary *)
  cat_fold @compose;
  cat_fold @c_identity;
  let cid := base_fn @c_identity in
    (repeat progress (
      let H := fresh in let x := fresh in evar (x : C); 
        let x' := eval unfold x in x in 
        let cidx := eval cbn in (cid x') in 
        pose (eq_refl : cidx = cC.(c_identity) x') as H;
        erewrite H in *; clear x H));
  let eqbase := base_fn @c_equiv in
  let eqcat := catify @c_equiv in
  change eqbase with eqcat in *; (* I think this is a no-op *)
  repeat (progress match goal with
  |- eqbase ?A ?B ?f ?g 
    => change (eqbase A B f g) with (eqcat A B f g) in *
  end);
  try let H' := fresh in 
    enough (H':(@c_equiv _ _ _ _ _ _)) by (eapply H')
  end.

Ltac fold_all_categories :=
  saturate_instances Category;
  repeat match goal with
  | x := ?cC : Category ?C |- _ => (* idtac x ":=" cC ": Category" C ; *) 
      fold_Category cC; subst x
  (* | x : Category ?C |- _ => idtac x; fold_Category x; subst x *)
  end.

Ltac fold_MonoidalCategory mC :=
  match type of mC with @MonoidalCategory ?C ?cC =>
  let catify f := constr:(@f C cC) in
  let mcatify f := constr:(@f C cC mC) in
  let base_fn f := 
    (let t := eval cbn in f in constr:(t)) in
  let cbase_fn f := (let raw := catify f in
    let t := eval cbn in raw in constr:(t)) in
  let mbase_fn f := (let raw := mcatify f in
    let t := eval cbn in raw in constr:(t)) in
  let f_fold f :=
    (let base := base_fn @f in 
     change base with f in *) in
  let cat_fold f :=
    (let base := cbase_fn @f in 
    let catted := catify @f in
    change base with catted in * ) in
  let mcat_fold f :=
    (let base := mbase_fn @f in 
    let catted := mcatify @f in
    change base with catted in * ) in
  let tens_obj := base_fn (@obj_tensor C cC mC) in
    change tens_obj with (@obj_tensor C cC mC) in *;
  let tens_mor := base_fn (@mor_tensor C cC mC) in
    change tens_mor with (@mor_tensor C cC mC) in *;
  mcat_fold @mon_I;
  let lunit := mbase_fn @left_unitor in
    repeat progress (
      let H := fresh in let x := fresh in 
      evar (x : C);  (* TODO: Test this - last I tried it was uncooperative *)
      let x' := eval unfold x in x in 
      let lunitx := eval cbn in ((lunit x').(forward)) in
      pose (eq_refl : lunitx = (mC.(left_unitor) x').(forward)) as H;
      erewrite H in *; clear x H);
  let runit := mbase_fn @right_unitor in 
    repeat progress (
      let H := fresh in let x := fresh in 
      evar (x : C);  (* TODO: Test this - last I tried it was uncooperative *)
      let x' := eval unfold x in x in 
      let runitx := eval cbn in ((runit x').(forward)) in
      pose (eq_refl : runitx = (mC.(right_unitor) x').(forward)) as H;
      erewrite H in *; clear x H)
  end.

Ltac fold_all_monoidal_categories :=
  saturate_instances MonoidalCategory;
  repeat match goal with
  | x := ?mC : MonoidalCategory ?C |- _ => (* idtac x ":=" cC ": Category" C ; *) 
      fold_MonoidalCategory mC; subst x
  (* | x : Category ?C |- _ => idtac x; fold_Category x; subst x *)
  end.

Ltac fold_BraidedMonoidalCategory bC :=
  match type of bC with @BraidedMonoidalCategory ?C ?cC ?mC =>
  let catify f := constr:(@f C cC) in
  let mcatify f := constr:(@f C cC mC) in
  let bcatify f := constr:(@f C cC mC bC) in
  let base_fn f := 
    (let t := eval cbn in f in constr:(t)) in
  let cbase_fn f := (let raw := catify f in
    let t := eval cbn in raw in constr:(t)) in
  let mbase_fn f := (let raw := mcatify f in
    let t := eval cbn in raw in constr:(t)) in
  let bbase_fn f := (let raw := bcatify f in
    let t := eval cbn in raw in constr:(t)) in
  let f_fold f :=
    (let base := base_fn @f in 
     change base with f) in
  let cat_fold f :=
    (let base := cbase_fn @f in 
    let catted := catify @f in
    change base with catted in * ) in
  let mcat_fold f :=
    (let base := mbase_fn @f in 
    let catted := mcatify @f in
    change base with catted in * ) in
  let bcat_fold f :=
    (let base := bbase_fn @f in 
    let catted := bcatify @f in
    change base with catted in * ) in
  let braid := bbase_fn @braiding in
    change braid with (@braiding C cC mC bC);
    let braidbase := constr:(
      ltac:(first [exact (ltac:(eval unfold braid in braid)) 
      | exact braid])) in
    
    let braidforw := eval simpl in 
      (fun A B => (braidbase A B).(forward)) in
    first [
      progress (
        match braidforw with
        | fun n m => ?f n m => 
          change (f ?k ?l) with ((bC.(braiding) k l).(forward))
        end
      ) 
    | repeat progress (let H := fresh in let y := fresh in let x := fresh in
        evar (y : C); evar (x : C); 
        let x' := eval unfold x in x in let y' := eval unfold y in y in
        let braidforwxy := eval simpl in (braidforw x' y') in
        pose (eq_refl : braidforwxy = 
          (bC.(braiding) x' y').(forward)) as H;
        erewrite H; clear x y H)
    ];

    let braidrev := eval simpl in 
      (fun A B => (braidbase A B).(reverse)) in
    first [
      progress (
        match braidrev with
        | fun n m => ?f n m =>
          change (f ?k ?l) with ((bC.(braiding) k l).(reverse))
        end
      ) 
    | repeat progress (let H := fresh in let y := fresh in let x := fresh in
        evar (y : C); evar (x : C); 
        let x' := eval unfold x in x in let y' := eval unfold y in y in
        let braidrevxy := eval simpl in (braidrev x' y') in
        pose (eq_refl : braidrevxy = 
          (bC.(braiding) x' y').(reverse)) as H;
        erewrite H; clear x y H)
    ]
  end.

Ltac fold_all_braided_monoidal_categories :=
  saturate_instances BraidedMonoidalCategory;
  repeat match goal with
  | x := ?bC : BraidedMonoidalCategory ?C |- _ => 
      fold_BraidedMonoidalCategory bC; subst x
  end.

Ltac to_Cat :=
  fold_all_categories; fold_all_monoidal_categories;
  fold_all_braided_monoidal_categories.



Ltac fold_Category_in cC H :=
  match type of cC with Category ?C =>
  let catify f := constr:(@f C cC) in
  let base_fn f := (let raw := catify f in
    let t := eval cbn in raw in constr:(t)) in
  let cat_fold f :=
    (let base := base_fn @f in 
    let catted := catify @f in
    change base with catted in H) in
  try cat_fold @morphism; 
  cat_fold @compose;
  cat_fold @c_identity;
  let cid := base_fn @c_identity in
    (repeat progress (
      let H := fresh in let x := fresh in evar (x : C); 
        let x' := eval unfold x in x in 
        let cidx := eval cbn in (cid x') in 
        pose (eq_refl : cidx = cC.(c_identity) x') as H;
        erewrite H in *; clear x H));
  let eqbase := base_fn @c_equiv in
  let eqcat := catify @c_equiv in
  change eqbase with eqcat in H; (* I think this is a no-op *)
  repeat (progress match goal with
  |- eqbase ?A ?B ?f ?g 
    => change (eqbase A B f g) with (eqcat A B f g) in H
  end);
  try let H' := fresh in 
    enough (H':(@c_equiv _ _ _ _ _ _)) by (eapply H')
  end.

Ltac fold_all_categories_in H :=
  saturate_instances Category;
  repeat match goal with
  | x := ?cC : Category ?C |- _ => (* idtac x ":=" cC ": Category" C ; *) 
      fold_Category_in cC H; subst x
  (* | x : Category ?C |- _ => idtac x; fold_Category x; subst x *)
  end.

Ltac fold_MonoidalCategory_in mC H :=
  match type of mC with @MonoidalCategory ?C ?cC =>
  let catify f := constr:(@f C cC) in
  let mcatify f := constr:(@f C cC mC) in
  let base_fn f := 
    (let t := eval cbn in f in constr:(t)) in
  let cbase_fn f := (let raw := catify f in
    let t := eval cbn in raw in constr:(t)) in
  let mbase_fn f := (let raw := mcatify f in
    let t := eval cbn in raw in constr:(t)) in
  let f_fold f :=
    (let base := base_fn @f in 
     change base with f in H) in
  let cat_fold f :=
    (let base := cbase_fn @f in 
    let catted := catify @f in
    change base with catted in H) in
  let mcat_fold f :=
    (let base := mbase_fn @f in 
    let catted := mcatify @f in
    change base with catted in H) in
  let tens_obj := base_fn (@obj_tensor C cC mC) in
    change tens_obj with (@obj_tensor C cC mC) in H;
  let tens_mor := base_fn (@mor_tensor C cC mC) in
    change tens_mor with (@mor_tensor C cC mC) in H;
  mcat_fold @mon_I;
  let lunit := mbase_fn @left_unitor in
    repeat progress (
      let Hx := fresh in let x := fresh in 
      evar (x : C);  (* TODO: Test this - last I tried it was uncooperative *)
      let x' := eval unfold x in x in 
      let lunitx := eval cbn in ((lunit x').(forward)) in
      pose (eq_refl : lunitx = (mC.(left_unitor) x').(forward)) as Hx;
      erewrite Hx in H; clear x Hx);
    repeat progress (
      let Hx := fresh in let x := fresh in 
      evar (x : C);  (* TODO: Test this - last I tried it was uncooperative *)
      let x' := eval unfold x in x in 
      let lunitx := eval cbn in ((lunit x').(reverse)) in
      pose (eq_refl : lunitx = (mC.(left_unitor) x').(reverse)) as Hx;
      erewrite Hx in H; clear x Hx);
  let runit := mbase_fn @right_unitor in 
    repeat progress (
      let Hx := fresh in let x := fresh in 
      evar (x : C);  (* TODO: Test this - last I tried it was uncooperative *)
      let x' := eval unfold x in x in 
      let runitx := eval cbn in ((runit x').(forward)) in
      pose (eq_refl : runitx = (mC.(right_unitor) x').(forward)) as Hx;
      erewrite Hx in H; clear x Hx);
    repeat progress (
      let Hx := fresh in let x := fresh in 
      evar (x : C);  (* TODO: Test this - last I tried it was uncooperative *)
      let x' := eval unfold x in x in 
      let runitx := eval cbn in ((runit x').(reverse)) in
      pose (eq_refl : runitx = (mC.(right_unitor) x').(reverse)) as Hx;
      erewrite Hx in H; clear x Hx)
  end.

Ltac fold_all_monoidal_categories_in H :=
  saturate_instances MonoidalCategory;
  repeat match goal with
  | x := ?mC : MonoidalCategory ?C |- _ => (* idtac x ":=" cC ": Category" C ; *) 
      fold_MonoidalCategory_in mC H; subst x
  (* | x : Category ?C |- _ => idtac x; fold_Category x; subst x *)
  end.

Ltac fold_BraidedMonoidalCategory_in bC H :=
  match type of bC with @BraidedMonoidalCategory ?C ?cC ?mC =>
  let catify f := constr:(@f C cC) in
  let mcatify f := constr:(@f C cC mC) in
  let bcatify f := constr:(@f C cC mC bC) in
  let base_fn f := 
    (let t := eval cbn in f in constr:(t)) in
  let cbase_fn f := (let raw := catify f in
    let t := eval cbn in raw in constr:(t)) in
  let mbase_fn f := (let raw := mcatify f in
    let t := eval cbn in raw in constr:(t)) in
  let bbase_fn f := (let raw := bcatify f in
    let t := eval cbn in raw in constr:(t)) in
  let f_fold f :=
    (let base := base_fn @f in 
     change base with f in H) in
  let cat_fold f :=
    (let base := cbase_fn @f in 
    let catted := catify @f in
    change base with catted in H) in
  let mcat_fold f :=
    (let base := mbase_fn @f in 
    let catted := mcatify @f in
    change base with catted in H) in
  let bcat_fold f :=
    (let base := bbase_fn @f in 
    let catted := bcatify @f in
    change base with catted in H) in
  let braid := bbase_fn @braiding in
    change braid with (@braiding C cC mC bC);
    let braidbase := constr:(
      ltac:(first [exact (ltac:(eval unfold braid in braid)) 
      | exact braid])) in
    
    let braidforw := eval simpl in 
      (fun A B => (braidbase A B).(forward)) in
    first [
      progress (
        match braidforw with
        | fun n m => ?f n m => 
          change (f ?k ?l) with ((bC.(braiding) k l).(forward)) in H
        end
      ) 
    | repeat progress (let Hx := fresh in let y := fresh in let x := fresh in
        evar (y : C); evar (x : C); 
        let x' := eval unfold x in x in let y' := eval unfold y in y in
        let braidforwxy := eval simpl in (braidforw x' y') in
        pose (eq_refl : braidforwxy = 
          (bC.(braiding) x' y').(forward)) as Hx;
        erewrite Hx in H; clear x y Hx)
    ];

    let braidrev := eval simpl in 
      (fun A B => (braidbase A B).(reverse)) in
    first [
      progress (
        match braidrev with
        | fun n m => ?f n m =>
          change (f ?k ?l) with ((bC.(braiding) k l).(reverse)) in H
        end
      ) 
    | repeat progress (let Hx := fresh in let y := fresh in let x := fresh in
        evar (y : C); evar (x : C); 
        let x' := eval unfold x in x in let y' := eval unfold y in y in
        let braidrevxy := eval simpl in (braidrev x' y') in
        pose (eq_refl : braidrevxy = 
          (bC.(braiding) x' y').(reverse)) as Hx;
        erewrite Hx in H; clear x y Hx)
    ]
  end.

Ltac fold_all_braided_monoidal_categories_in H :=
  saturate_instances BraidedMonoidalCategory;
  repeat match goal with
  | x := ?bC : BraidedMonoidalCategory ?C |- _ => 
      fold_BraidedMonoidalCategory_in bC H; subst x
  end.

Ltac to_Cat_in H :=
  fold_all_categories_in H; fold_all_monoidal_categories_in H;
  fold_all_braided_monoidal_categories_in H.



(* Section on foliateing *)

Ltac tensor_free f :=
  try match f with
  | context[@mor_tensor _ _ _ _ _ _ _] => fail 2
  end.

Ltac compose_free f :=
  try match f with
  | context[@compose _ _ _ _] => fail 2
  end.

Ltac pseudo_const f :=
  tensor_free f; compose_free f.

(* 
TODO: I used to have explicit patterns, like this, for compose and tensor.
  In testing, I found no difference, but this warrants consideration.
Ltac tensor_only f :=
  first [
    pseudo_const f
  | lazymatch f with 
    | @morphism_bimap _ _ _ _ _ _ (@tensor _ _ _) _ _ _ _ ?f ?g =>
        tensor_only f; tensor_only g
    end]. *)

Ltac tensor_only f :=
  first [
    pseudo_const f
  | lazymatch f with (* TODO: Does lazy matter here? Pretty sure it doesn't hurt, but idk if it'd ever match more than once anyways*)
    | (?g ⊗ ?h)%Cat => tensor_only g; tensor_only h
    end].

Ltac compose_only f :=
  first [pseudo_const f
  | lazymatch f with 
    | (?g ∘ ?h)%Cat => 
        compose_only g; compose_only h
    end].

Ltac is_weak_fenced f :=
  lazymatch f with
  | (?g ∘ ?h)%Cat => tensor_only g; is_weak_fenced h
  | (?g ⊗ ?h)%Cat =>
      tensor_only g; tensor_only h
  | _ => pseudo_const f
  end.

(* (Semi-Informal) Specification: 
  Inductive is_weak_fence f :=
  | const : tensor_only f 
      -> is_weak_fence f
  | comp g h : tensor_only g -> is_weak_fence h
     -> is_weak_fence (g ∘ h).
*)

Ltac right_associate_term f := 
  match f with 
  | ((?g ∘ ?h) ∘ ?i)%Cat => right_associate_term (g ∘ (h ∘ i))%Cat
  | (?g ∘ ?h)%Cat => (* g shouldn't be a composition *)
      let RAh := right_associate_term h in
        constr:((g ∘ RAh)%Cat)
  | _ => constr:(f)
  end.

(* TODO: Test this! *)
Ltac left_associate_term f := 
  match f with 
  | (?g ∘ (?h ∘ ?i))%Cat => left_associate_term ((g ∘ h) ∘ i)%Cat
  | (?g ∘ ?h)%Cat => (* h shouldn't be a composition *)
      let LAg := left_associate_term g in
        constr:((LAg ∘ h)%Cat)
  | _ => constr:(f)
  end.



Ltac merge_stacked_composition_debug gh := 
  let rec merge_stacked_composition gh :=
  match type of gh with @morphism ?C ?cC _ _ =>
  match gh with
    @mor_tensor C cC ?mC ?gA ?gB ?hA ?hB ?g ?h =>
  lazymatch g with
  | (?g0 ∘ ?g1)%Cat => 
    let _ := match goal with _ => 
      idtac "found decomp of first as" g0 "∘" g1 end in
    lazymatch h with 
    | (?h0 ∘ ?h1)%Cat =>
        let _ := match goal with _ => 
          idtac "found decomp of second as" h0 "∘" h1 end in
        let rest := merge_stacked_composition ((mC.(mor_tensor) g1 h1)%Cat) in
        let _ := match goal with _ => 
          idtac "remaining terms became" rest end in
        let res := constr:(cC.(compose) (mC.(mor_tensor) g0 h0) rest) in
        let _ := match goal with _ => 
          idtac "    which combined to" res end in
        constr:(res)
    | _ => 
        let _ := match goal with _ => 
          idtac "found second to be atomic:" h end in
        match type of h with @morphism _ _ ?A ?B =>
          let _ := match goal with _ => 
            idtac "resolved second as type" hA "~>" hB end in
          let rest := merge_stacked_composition ((mC.(mor_tensor) g1 (cC.(c_identity) hB))%Cat) in
          let _ := match goal with _ => 
            idtac "remaining terms became" rest end in
          let res := constr:(cC.(compose) (mC.(mor_tensor) g0 h) rest) in
          let _ := match goal with _ => 
            idtac "    which combined to" res end in
          constr:(res)
        end
    end
  | _ => 
    let _ := match goal with _ => 
      idtac "found first to be atomic:" g end in
    lazymatch h with 
    | (?h0 ∘ ?h1)%Cat =>
        let _ := match goal with _ => 
          idtac "found decomp of second as" h0 "∘" h1 end in
        match type of g with @morphism _ _ ?A ?B =>
          let _ := match goal with _ => 
            idtac "resolved second as type" gA "~>" gB end in
          let rest := merge_stacked_composition ((mC.(mor_tensor) (cC.(c_identity) gB) h1)%Cat) in
          let _ := match goal with _ => 
            idtac "remaining terms became" rest end in
          let res := constr:(cC.(compose) (mC.(mor_tensor) g h0) rest) in
          let _ := match goal with _ => 
            idtac "    which combined to" res end in
          constr:(res)
        end
    | _ => 
        let _ := match goal with _ => 
          idtac "found second to be atomic as well:" h end in
        constr:((mC.(mor_tensor) g h)%Cat)
    end
  end
  end end
  in merge_stacked_composition gh. 

Ltac merge_stacked_composition gh := 
  let rec merge_stacked_composition gh :=
  match type of gh with @morphism ?C ?cC _ _ =>
  match gh with
    @mor_tensor C cC ?mC ?gA ?gB ?hA ?hB ?g ?h =>
  lazymatch g with
  | (?g0 ∘ ?g1)%Cat => 
    lazymatch h with 
    | (?h0 ∘ ?h1)%Cat =>
        let rest := merge_stacked_composition ((mC.(mor_tensor) g1 h1)%Cat) in
        constr:(cC.(compose) (mC.(mor_tensor) g0 h0) rest)
    | _ => 
        let rest :=
          merge_stacked_composition 
            ((mC.(mor_tensor) g1 (cC.(c_identity) hB))%Cat)in
        constr:(cC.(compose) (mC.(mor_tensor) g0 h) rest)
    end
  | _ => 
    lazymatch h with 
    | (?h0 ∘ ?h1)%Cat =>
        let rest := 
          merge_stacked_composition
            ((mC.(mor_tensor) (cC.(c_identity) gB) h1)%Cat) in
        constr:(cC.(compose) (mC.(mor_tensor) g h0) rest)
    | _ => 
        constr:((mC.(mor_tensor) g h)%Cat)
    end
  end
  end end
  in merge_stacked_composition gh. 

Ltac weak_foliate_form_debug f :=
  let rec weak_foliate f :=
  match f with
  | @compose ?C ?cC _ _ _ ?g ?h => 
      let _ := match goal with _ => 
        idtac "splitting on ∘ into" g "and" h "..." end in
      let Ng := weak_foliate g in
      let Nh := weak_foliate h in 
      let _ := match goal with _ => 
        idtac "... getting" g "∘" h "into" end in
      let res := right_associate_term (cC.(compose) Ng Nh) in
      let _ := match goal with _ => 
        idtac "    " res end in
      constr:(res)
  | @mor_tensor ?C ?cC ?mC _ _ _ _ ?g ?h =>
      let _ := match goal with _ => 
        idtac "splitting on ⊗ into" g "and" h "..." end in
      let Ng := weak_foliate g in
      let Nh := weak_foliate h in 
      let _ := match goal with _ => 
        idtac "... getting" g "⊗" h "into" end in
      let res := merge_stacked_composition ((mC.(mor_tensor) Ng Nh)%Cat) in
      let _ := match goal with _ => 
        idtac "    " res end in
      constr:(res)
  | _ => 
      let _ := match goal with _ => 
        idtac "INFO:" f "is const or unsupported" end in
      constr:(f)
  end
  in weak_foliate f.

Ltac weak_foliate_form f :=
  let rec weak_foliate f :=
  match f with
  | @compose ?C ?cC _ _ _ ?g ?h => 
      let Ng := weak_foliate g in
      let Nh := weak_foliate h in 
      right_associate_term (cC.(compose) Ng Nh)
  | @mor_tensor ?C ?cC ?mC _ _ _ _ ?g ?h =>
      let Ng := weak_foliate g in
      let Nh := weak_foliate h in 
      merge_stacked_composition ((mC.(mor_tensor) Ng Nh)%Cat)
  | _ => (* f "is const or unsupported" *)
      constr:(f)
  end
  in weak_foliate f.

Section HelperLemmas.

Context {C} {cC : Category C} {cCh : CategoryCoherence cC}.

Local Open Scope Cat_scope.

Lemma assoc_compat_helper {A B M N : C} :
  forall (f : A ~> B) (g : B ~> M) (h : M ~> N) (fgh : A ~> N),
  f ∘ (g ∘ h) ≃ fgh -> (f ∘ g) ∘ h ≃ fgh.
Proof.
  intros; rewrite assoc; easy.
Qed.

Lemma assoc_compat_helper' {A B M N : C}
  : forall  (f : A ~> B) 
  (g : B ~> M) (h : M ~> N) (fgh : A ~> N),
  (f ∘ g) ∘ h ≃ fgh -> f ∘ (g ∘ h) ≃ fgh.
Proof. intros; rewrite <- assoc; easy. Qed.

Lemma compose_compat_right {A B M : C} :
  forall (f : A ~> B) (g g' : B ~> M),
  g ≃ g' -> f ∘ g ≃ f ∘ g'.
Proof.
  intros.
  apply compose_compat; easy.
Qed.

Lemma compose_compat_trans_helper {A B M : C} : forall
  (f f' : A ~> B) (g g' : B ~> M) (fg : A ~> M),
  f ≃ f' -> g ≃ g' -> f' ∘ g' ≃ fg -> f ∘ g ≃ fg.
Proof.
  intros.
  transitivity (f' ∘ g')%Cat; [|easy].
  apply compose_compat; easy.
Qed.

Context {mC : MonoidalCategory cC} {mCh : MonoidalCategoryCoherence mC}.

Lemma stack_compose_distr_compat {A B M A' B' M': C} :
  forall (f : A ~> B) (g : B ~> M) (h : A' ~> B') (i : B' ~> M')
  (gi : B × B' ~> M × M'),
  g ⊗ i ≃ gi -> (f ∘ g) ⊗ (h ∘ i) ≃ f ⊗ h ∘ gi.
Proof.
  intros.
  rewrite tensor_compose.
  apply compose_compat; easy.
Qed.

Lemma stack_distr_pushout_r_top_compat
  {a b m n o} : forall (f : a ~> b) (g : m ~> n) (h : n ~> o)
  (ih : b × n ~> b × o),
  id_ b ⊗ h ≃ ih -> f ⊗ (g ∘ h) ≃ f ⊗ g ∘ ih.
Proof.
  intros.
  (* `rewrite stack_distr_pushout_r_top.` is replaced here manually 
  to simplify dependencies *)
  rewrite <- (right_unit f) at 1.
  rewrite tensor_compose.
  apply compose_compat; easy.
Qed.

Lemma stack_distr_pushout_r_bot_compat 
  {a b c n o : C} : forall (f : a ~> b) (g : b ~> c) (h : n ~> o)
  (gi : b × o ~> c × o),
  g ⊗ id_ o ≃ gi -> (f ∘ g) ⊗ h ≃ f ⊗ h ∘ gi.
Proof.
  intros.
  (* `rewrite stack_distr_pushout_r_bot.` is replaced here manually 
  to simplify dependencies *)
  rewrite <- (right_unit h) at 1.
  rewrite tensor_compose.
  apply compose_compat; easy.
Qed.

Lemma stack_compat_trans_helper {A A' B B' : C} : 
  forall (f f' : A ~> A') (g g' : B ~> B') (fg : A × B ~> A' × B'),
  f ≃ f' -> g ≃ g' -> f' ⊗ g' ≃ fg -> f ⊗ g ≃ fg.
Proof.
  intros.
  transitivity (f' ⊗ g'); [|easy].
  apply tensor_compat; easy.
Qed.

Lemma show_equiv_stack_comp_id_bot_helper {A M A' B : C} : 
  forall (g : A ~> M) (gs : M ~> A') (gsB : M × B ~> A' × B),
  gs ⊗ id_ B ≃ gsB -> (g ∘ gs) ⊗ id_ B ≃ g ⊗ id_ B ∘ gsB.
Proof.
  intros.
  rewrite <- (right_unit (id_ B)) at 1.
  rewrite tensor_compose.
  apply compose_compat; easy.
Qed.

Lemma show_equiv_stack_comp_id_top_helper {A B M B' : C} : 
  forall (g : B ~> M) (gs : M ~> B') (Ags : A × M ~> A × B'),
  id_ A ⊗ gs ≃ Ags -> id_ A ⊗ (g ∘ gs) ≃ id_ A ⊗ g ∘ Ags.
Proof.
  intros.
  rewrite <- (right_unit (id_ A)) at 1.
  rewrite tensor_compose.
  apply compose_compat; easy.
Qed.

Lemma show_equiv_unfold_tensor_stack_helper
  {fA fB gA gB : C} (f uf : fA ~> fB) (g ug : gA ~> gB) 
  (ufs : fA × gA ~> fB × gA) (ugs : fB × gA ~> fB × gB) :
  f ≃ uf -> g ≃ ug -> 
  uf ⊗ id_ gA ≃ ufs -> id_ fB ⊗ ug ≃ ugs ->
  f ⊗ g ≃ ufs ∘ ugs.
Proof.
  intros Hf Hg Huf Hug.
  rewrite Hf, Hg.
  rewrite <- (right_unit uf), <- (left_unit ug), tensor_compose.
  apply compose_compat; easy.
Qed.

Close Scope Cat_scope.

End HelperLemmas.


(* Shows the goal f ≃ right_associate_term f by mirroring the code
   path of right_associate_term with `apply`s. *)
Ltac show_equiv_right_associate_term f :=
  let rec show_equiv_right_associate_term f :=
  match f with 
  | ((?g ∘ ?h) ∘ ?i)%Cat => 
    (* RHS is `right_associate_term (g ∘ (h ∘ i))` *)
    apply assoc_compat_helper;
    show_equiv_right_associate_term ((g ∘ (h ∘ i))%Cat)
  | (?g ∘ ?h)%Cat => (* g shouldn't be a composition *)
      (* RHS is `(g ∘ right_associate_term h)` *)
      apply compose_compat_right;
      show_equiv_right_associate_term h
  | _ => 
    (* RHS is `constr:(f)` *)
    reflexivity
  end
  in show_equiv_right_associate_term f.

(* Shows the goal f ≃ left_associate_term f by mirroring the code
   path of left_associate_term with `apply`s. *)
Ltac show_equiv_left_associate_term f :=
  let rec show_left f :=
  match f with  
  | (?g ∘ (?h ∘ ?i))%Cat => 
    (* RHS is `left_associate_term ((g ∘ h) ∘ i)%Cat` *)
    apply assoc_compat_helper';
    show_left (((g ∘ h) ∘ i)%Cat)
  | (?g ∘ ?h)%Cat => (* h shouldn't be a composition *)
    (* RHS is `(left_associate_term g ∘ h)` *) 
    apply compose_cancel_r;
    show_left g
  | _ => 
    (* RHS is `constr:(f)` *)
    reflexivity
  end
  in show_left f.

Ltac rassoc t :=
  let H := fresh in 
  let rt := right_associate_term t in
  assert (H: (t ≃ rt)%Cat) by (show_equiv_right_associate_term t);
  rewrite H; clear H.

Ltac lassoc t :=
  let H := fresh in 
  let rt := left_associate_term t in
  assert (H: (t ≃ rt)%Cat) by (show_equiv_left_associate_term t);
  rewrite H; clear H.


(* Shows the goal f ≃ merge_stack_composition f by mirroring the 
   code path of merge_stacked_composition with `apply`s. *)
Ltac show_equiv_merge_stacked_composition gh := 
  let rec show_equiv_merge_stacked_composition gh :=
  match type of gh with @morphism ?C ?cC _ _ =>
  match gh with
    @mor_tensor C cC ?mC ?gA ?gB ?hA ?hB ?g ?h =>
  lazymatch g with
  | (?g0 ∘ ?g1)%Cat => 
    lazymatch h with 
    | (?h0 ∘ ?h1)%Cat =>
        (* RHS is g0 ⊗ h0 ∘ merge_stacked_composition (g1 ⊗ h1) *)
        apply stack_compose_distr_compat;
        show_equiv_merge_stacked_composition ((mC.(mor_tensor) g1 h1)%Cat)
    | _ => 
        (* RHS is g0 ⊗ h0 ∘ merge_stacked_composition (g1 ⊗ id_ hB) *)
        apply stack_distr_pushout_r_bot_compat;
        show_equiv_merge_stacked_composition ((mC.(mor_tensor) g1 (cC.(c_identity) hB))%Cat)
    end
  | _ => 
    lazymatch h with 
    | (?h0 ∘ ?h1)%Cat =>
        (* RHS is g0 ⊗ h0 ∘ merge_stacked_composition (id_ gB ⊗ h1) *)
        apply stack_distr_pushout_r_top_compat;
        show_equiv_merge_stacked_composition ((mC.(mor_tensor) (cC.(c_identity) gB) h1)%Cat)
    | _ => 
        (* RHS is g ⊗ h *)
        reflexivity
    end
  end
  end end
  in show_equiv_merge_stacked_composition gh. 

(* Shows the goal f ≃ weak_foliate_form f by mirroring the code
   path of weak_foliate_form with `apply`s. *)
Ltac show_equiv_weak_foliate_form f :=
  let weak_foliate := weak_foliate_form in 
  let rec show_equiv_weak_foliate_form f :=
  match f with
  | @compose ?C ?cC _ _ _ ?g ?h => 
      let Ng := weak_foliate g in
      let Nh := weak_foliate h in 
      let res := right_associate_term (cC.(compose) Ng Nh) in
      apply (compose_compat_trans_helper (cC:=cC) g Ng h Nh res 
        ltac:(show_equiv_weak_foliate_form g)
        ltac:(show_equiv_weak_foliate_form h)
        ltac:(show_equiv_right_associate_term (cC.(compose) Ng Nh)))
  | @mor_tensor ?C ?cC ?mC _ _ _ _ ?g ?h =>
      let Ng := weak_foliate g in
      let Nh := weak_foliate h in 
      let res := merge_stacked_composition ((mC.(mor_tensor) Ng Nh)%Cat) in
      apply (stack_compat_trans_helper (cC:=cC) g Ng h Nh res 
        ltac:(show_equiv_weak_foliate_form g)
        ltac:(show_equiv_weak_foliate_form h)
        ltac:(show_equiv_merge_stacked_composition ((mC.(mor_tensor) Ng Nh))%Cat))
  | _ => (* f "is const or unsupported" *)
      (* constr:(f) *)
      reflexivity
  end
  in show_equiv_weak_foliate_form f.

(* TODO: Generalize these to fold_compose base *)
(* If f = f0 ∘ (f1 ∘ (...)), this gives f0 ⊗ id_ B ∘ (f1 ⊗ id_ B ∘ (...))
   in the given monoidal category mC. *)
Ltac stack_comp_id_bot f B mC :=
  let base g :=
    constr:((mC.(mor_tensor) g (id_ B))%Cat) in
  let rec stack_comp h :=
  match h with
  | (?g ∘ ?gs)%Cat => 
      let stg := base g in
      let stgs := stack_comp gs in
      constr:((stg ∘ stgs)%Cat)
  | ?g => 
      base h
  end
  in stack_comp f.

(* If f = f0 ∘ (f1 ∘ (...)), this gives id_ A ⊗ f0 ∘ (id_ A ⊗ f1 ∘ (...))
   in the given monoidal category mC. *)
Ltac stack_comp_id_top f A mC :=
  let base g :=
    constr:((mC.(mor_tensor) (id_ A) g)%Cat) in
  let rec stack_comp h :=
  match h with
  | (?g ∘ ?gs)%Cat => 
      let stg := base g in
      let stgs := stack_comp gs in
      constr:((stg ∘ stgs)%Cat)
  | ?g => 
      base h
  end
  in stack_comp f.



(* Given f ⊗ g ⊗ h ⊗ ..., gives f ⊗ id ⊗ ... ∘ id ⊗ g ⊗ ...
   (this tactic allows for irregularly-associated ⊗, which 
   that example may not suggest). *)
Ltac unfold_tensor_stack f :=
  let rec unfold_tensor_stack f :=
  lazymatch f with 
  | @mor_tensor _ _ ?mC ?gA ?gB ?hA ?hB ?g ?h =>
      let ug := unfold_tensor_stack g in 
      let uh := unfold_tensor_stack h in 
      let sg := stack_comp_id_bot ug hA mC in
      let sh := stack_comp_id_top uh gB mC in
      constr:((sg ∘ sh)%Cat)
  | _ => constr:(f)
  end
  in unfold_tensor_stack f.


Ltac unfold_tensor_stack_no_id f :=
  let rec unfold_tensor_stack f :=
  lazymatch f with 
    (* TODO: is this case smart to have? *)
  (* | @mor_tensor _ ?cC ?mC 
    ?gA _ ?hA _ (id_ ?gA)%Cat (id_ ?hA)%Cat => 
      constr:(cC.(c_identity) (mC.(obj_tensor) gA hA)) *)
  
  | @mor_tensor _ ?cC ?mC  
    ?gA ?gA ?hA ?hB (id_ ?gA)%Cat ?h => 
      let uh := unfold_tensor_stack h in 
      let sh := stack_comp_id_top uh gA mC in
      constr:(sh)
      
  | @mor_tensor _ ?cC ?mC 
    ?gA ?gB ?hA ?hA ?g (id_ ?hA)%Cat => 
      let ug := unfold_tensor_stack g in 
      let sg := stack_comp_id_bot ug hA mC in
      constr:(sg)

  | @mor_tensor _ ?cC ?mC 
    ?gA ?gB ?hA ?hB ?g ?h =>
      let ug := unfold_tensor_stack g in 
      let uh := unfold_tensor_stack h in 
      let sg := stack_comp_id_bot ug hA mC in
      let sh := stack_comp_id_top uh gB mC in
      constr:((sg ∘ sh)%Cat)
  | _ => constr:(f)
  end
  in unfold_tensor_stack f.

(* Returns the strong foliate term of a weakly foliateed term 
   (in fact, not even requiring the term be right-associated, though
    the resulting foliate will be. )*)
Ltac strong_foliate_form_of_weak f :=
  let rec strong_fence f :=
  lazymatch f with
  | (?g ∘ ?h)%Cat => 
      let ug := strong_fence g in
      let uh := strong_fence h in
      right_associate_term (ug ∘ uh)%Cat
  | _ => 
      unfold_tensor_stack f
  end
  in strong_fence f.

(* Additionally avoids taking id ⊗ id to id ⊗ id ∘ id ⊗ id and similar *)
Ltac strong_foliate_form_of_weak_no_id f :=
  let rec strong_fence f :=
  lazymatch f with
  | (?g ∘ ?h)%Cat => 
      let ug := strong_fence g in
      let uh := strong_fence h in
      right_associate_term (ug ∘ uh)%Cat
  | _ => 
      unfold_tensor_stack_no_id f
  end
  in strong_fence f.


Ltac show_equiv_stack_comp_id_bot f B mC :=
  let base g :=
    constr:((mC.(mor_tensor) g (id_ B))%Cat) in
  let rec show_stack_comp h :=
  match h with
  | (?g ∘ ?gs)%Cat => 
      (* let stg := base g in
      let stgs := stack_comp gs in
      constr:(stg ∘ stgs)%Cat *)
      apply show_equiv_stack_comp_id_bot_helper;
      show_stack_comp gs
  | ?g => 
      (* base h *)
      reflexivity
  end
  in show_stack_comp f.

Ltac show_equiv_stack_comp_id_top f A mC :=
  let base g :=
    constr:((mC.(mor_tensor) (id_ A) g)%Cat) in
  let rec show_stack_comp h :=
  match h with
  | (?g ∘ ?gs)%Cat => 
      (* let stg := base g in
      let stgs := stack_comp gs in
      constr:(stg ∘ stgs)%Cat *)
      apply show_equiv_stack_comp_id_top_helper;
      show_stack_comp gs
  | ?g => 
      (* base h *)
      reflexivity
  end
  in show_stack_comp f.
  

Ltac show_equiv_unfold_tensor_stack f :=
  let rec show_unfold f :=
  lazymatch f with 
  | @mor_tensor _ ?cC ?mC ?gA ?gB ?hA ?hB ?g ?h =>
      let ug := unfold_tensor_stack g in 
      let uh := unfold_tensor_stack h in 
      let sg := stack_comp_id_bot ug hA mC in
      let sh := stack_comp_id_top uh gB mC in
      (* constr:(sg ∘ sh)%Cat *)
      apply (show_equiv_unfold_tensor_stack_helper
        g ug h uh sg sh
        ltac:(show_unfold g) 
        ltac:(show_unfold h)
        ltac:(show_equiv_stack_comp_id_bot ug hA mC)
        ltac:(show_equiv_stack_comp_id_top uh gB mC)
      )
  | _ => (* constr:(f) *)
      reflexivity
  end
  in show_unfold f.

Ltac show_equiv_unfold_tensor_stack_no_id f :=
  let unfold_tensor_stack := unfold_tensor_stack_no_id in
  let rec show_unfold f :=
  lazymatch f with 
    (* TODO: is this case smart to have? *)
  (* | @mor_tensor _ ?cC ?mC  
    ?gA ?gA ?hA ?hA (id_ ?gA)%Cat (id_ ?hA)%Cat => 
      (* constr:(cC.(c_identity) (mC.(tensor) gA hA)) *)
      apply (tensor_id gA hA) *)
  
  | @mor_tensor _ ?cC ?mC ?gA ?gA ?hA ?hB (id_ ?gA)%Cat ?h => 
      let uh := unfold_tensor_stack h in 
      let sh := stack_comp_id_top uh gA mC in   (* constr:(sh) *)
      apply (stack_compat_trans_helper
        (cC.(c_identity) gA) (cC.(c_identity) gA) h uh sh
        ltac:(reflexivity) ltac:(show_unfold h)
        ltac:(show_equiv_stack_comp_id_top uh gA mC))
      
  | @mor_tensor _ ?cC ?mC  ?gA ?gB ?hA ?hA ?g (id_ ?hA)%Cat => 
      let ug := unfold_tensor_stack g in 
      let sg := stack_comp_id_bot ug hA mC in   (* constr:(sg) *)
      apply (stack_compat_trans_helper
        g ug (cC.(c_identity) hA) (cC.(c_identity) hA) sg
        ltac:(show_unfold g) ltac:(reflexivity)
        ltac:(show_equiv_stack_comp_id_bot ug hA mC))

  | @mor_tensor _ ?cC ?mC  ?gA ?gB ?hA ?hB ?g ?h =>
      let ug := unfold_tensor_stack g in 
      let uh := unfold_tensor_stack h in 
      let sg := stack_comp_id_bot ug hA mC in
      let sh := stack_comp_id_top uh gB mC in   (* constr:((sg ∘ sh)%Cat) *)
      apply (show_equiv_unfold_tensor_stack_helper
        g ug h uh sg sh
        ltac:(show_unfold g) 
        ltac:(show_unfold h)
        ltac:(show_equiv_stack_comp_id_bot ug hA mC)
        ltac:(show_equiv_stack_comp_id_top uh gB mC)
      )
  | _ => (* constr:(f) *)
      reflexivity
  end
  in show_unfold f.

Ltac show_equiv_unfold_tensor_stack_no_id_debug f :=
  let unfold_tensor_stack := unfold_tensor_stack_no_id in 
  let rec show_unfold f :=
  lazymatch f with 
    (* TODO: is this case smart to have? *)
  (* | @mor_tensor _ ?cC ?mC ?gA _ ?hA _ (id_ ?gA)%Cat (id_ ?hA)%Cat => 
      idtac "id id case:"; print_state;
      (* constr:(cC.(c_identity) (mC.(tensor) gA hA)) *)
      apply (tensor_id gA hA)
      ; idtac "worked" *)
  
  | @mor_tensor _ ?cC ?mC ?gA ?gA ?hA ?hB (id_ ?gA)%Cat ?h => 
      let uh := unfold_tensor_stack h in 
      let sh := stack_comp_id_top uh gA mC in   (* constr:(sh) *)
      idtac "left id case:"; print_state;
      apply (stack_compat_trans_helper
        (cC.(c_identity) gA) (cC.(c_identity) gA) h uh sh
        ltac:(reflexivity) ltac:(show_unfold h)
        ltac:(show_equiv_stack_comp_id_top uh gA mC))
      ; idtac "worked"
      
  | @mor_tensor _ ?cC ?mC ?gA ?gB ?hA ?hA ?g (id_ ?hA)%Cat => 
      let ug := unfold_tensor_stack g in 
      let sg := stack_comp_id_bot ug hA mC in   (* constr:(sg) *)
      idtac "right id case:"; print_state;
      apply (stack_compat_trans_helper
        g ug (cC.(c_identity) hA) (cC.(c_identity) hA) sg
        ltac:(show_unfold g) ltac:(reflexivity)
        ltac:(show_equiv_stack_comp_id_bot ug hA mC))
      (* ); idtac "applied" g hA mC; print_state; show_equiv_stack_comp_id_bot ug hA mC;
      print_state
      ; idtac "worked" *)

  | @mor_tensor _ ?cC ?mC ?gA ?gB ?hA ?hB ?g ?h =>
      let ug := unfold_tensor_stack g in let uh := unfold_tensor_stack h in 
      let sg := stack_comp_id_bot ug hA mC in
      let sh := stack_comp_id_top uh gB mC in
      idtac "true compose case:"; print_state;
      apply (show_equiv_unfold_tensor_stack_helper
        g ug h uh sg sh   ltac:(show_unfold g) ltac:(show_unfold h)
        ltac:(show_equiv_stack_comp_id_bot ug hA mC)
        ltac:(show_equiv_stack_comp_id_top uh gB mC)
      )
      ; idtac "worked"
  | _ => (* constr:(f) *) reflexivity
  end
  in show_unfold f.


Ltac show_equiv_strong_foliate_form_of_weak f :=
  let strong_fence := strong_foliate_form_of_weak in
  let rec show_strong_fence f :=
  lazymatch f with
  | (?g ∘ ?h)%Cat => 
      let ug := strong_fence g in
      let uh := strong_fence h in
      let rassoc := right_associate_term (ug ∘ uh)%Cat in
      (* right_associate_term (ug ∘ uh)%Cat *)
      apply (compose_compat_trans_helper
        g ug  h uh rassoc
        ltac:(show_strong_fence g)
        ltac:(show_strong_fence h)
        ltac:(show_equiv_right_associate_term (ug ∘ uh)%Cat)
      )
  | _ => 
      (* unfold_tensor_stack f *)
      show_equiv_unfold_tensor_stack f
  end
  in show_strong_fence f.


Ltac show_equiv_strong_foliate_form_of_weak_no_id f :=
  let strong_fence := strong_foliate_form_of_weak_no_id in
  let rec show_strong_fence f :=
  lazymatch f with
  | (?g ∘ ?h)%Cat => 
      let ug := strong_fence g in
      let uh := strong_fence h in
      let rassoc := right_associate_term (ug ∘ uh)%Cat in
      (* right_associate_term (ug ∘ uh)%Cat *)
      apply (compose_compat_trans_helper
        g ug  h uh rassoc
        ltac:(show_strong_fence g)
        ltac:(show_strong_fence h)
        ltac:(show_equiv_right_associate_term (ug ∘ uh)%Cat)
      )
  | _ => 
      (* unfold_tensor_stack f *)
      show_equiv_unfold_tensor_stack_no_id f
  end
  in show_strong_fence f.

Ltac show_equiv_strong_foliate_form_of_weak_no_id_debug f :=
  let strong_fence := strong_foliate_form_of_weak_no_id in
  let rec show_strong_fence f :=
  lazymatch f with
  | (?g ∘ ?h)%Cat => 
      let ug := strong_fence g in
      let uh := strong_fence h in
      let rassoc := right_associate_term (ug ∘ uh)%Cat in
      (* right_associate_term (ug ∘ uh)%Cat *)
      apply (compose_compat_trans_helper
        g ug  h uh rassoc
        ltac:(show_strong_fence g)
        ltac:(show_strong_fence h)
        ltac:(show_equiv_right_associate_term (ug ∘ uh)%Cat)
      )
  | _ => 
      (* unfold_tensor_stack f *)
      show_equiv_unfold_tensor_stack_no_id_debug f
  end
  in show_strong_fence f.

Ltac weak_foliate f :=
  let wf := weak_foliate_form f in
  let H := fresh in 
  assert (H: (f ≃ wf)%Cat) by (show_equiv_weak_foliate_form f);
  setoid_rewrite H;
  clear H.

Ltac strong_foliate f :=
  let wf := weak_foliate_form f in
  let sf := strong_foliate_form_of_weak wf in
  let H := fresh in 
  assert (H: (f ≃ sf)%Cat) by (
    transitivity wf;
    [ show_equiv_weak_foliate_form f 
    | show_equiv_strong_foliate_form_of_weak wf]);
  setoid_rewrite H;
  clear H.

Ltac strong_foliate_no_id f :=
  let wf := weak_foliate_form f in
  let sf := strong_foliate_form_of_weak_no_id wf in
  let H := fresh in 
  assert (H: (f ≃ sf)%Cat) by (
    transitivity wf;
    [ show_equiv_weak_foliate_form f 
    | show_equiv_strong_foliate_form_of_weak_no_id wf]);
  setoid_rewrite H;
  clear H.

Ltac strong_foliate_no_id_debug f :=
  let wf := weak_foliate_form f in
  let sf := strong_foliate_form_of_weak_no_id wf in
  let H := fresh in 
  assert (H: (f ≃ sf)%Cat) by (
    transitivity wf;
    [ show_equiv_weak_foliate_form f 
    | show_equiv_strong_foliate_form_of_weak_no_id_debug wf]);
  setoid_rewrite H;
  clear H.


Ltac right_associate_term' f := 
  let rec rassoc f := 
  lazymatch f with 
  | ((?g ∘ ?h) ∘ ?i)%Cat => rassoc (g ∘ (h ∘ i))%Cat
  | (?g ∘ ?h)%Cat => (* g shouldn't be a composition *)
      let RAh := rassoc h in
        constr:((g ∘ RAh)%Cat)
  | @mor_tensor _ ?cC ?mC _ _ _ _ ?g ?h =>
       let RAg := rassoc g in let RAh := rassoc h in 
         constr:(mC.(mor_tensor) RAg RAh)
  | _ => constr:(f)
  end
  in rassoc f.

Ltac show_equiv_right_associate_term' term :=
  let rec show_equiv_right_associate_term f :=
  try easy;
  lazymatch f with 
  | ((?g ∘ ?h) ∘ ?i)%Cat => 
    (* RHS is `right_associate_term (g ∘ (h ∘ i))` *)
    apply assoc_compat_helper;
    show_equiv_right_associate_term ((g ∘ (h ∘ i))%Cat)
  | (?g ∘ ?h)%Cat => (* g shouldn't be a composition *)
      (* RHS is `(g ∘ right_associate_term h)` *)
      apply compose_compat_right;
      show_equiv_right_associate_term h
  | @mor_tensor _ ?cC ?mC _ _ _ _ ?g ?h =>
      apply (tensor_compat);
        [ltac:(show_equiv_right_associate_term g) |
        ltac:(show_equiv_right_associate_term h)]
  | _ => 
    (* RHS is `constr:(f)` *)
    reflexivity
  end
  in show_equiv_right_associate_term term.

Ltac rassoc' t :=
  let H := fresh in 
  let rt := right_associate_term' t in
  assert (H: (t ≃ rt)%Cat) by (show_equiv_right_associate_term' t);
  rewrite H; clear H.


Ltac partnered_in_RA_term_nofail t s term :=
  let rec partnered t s term :=
  match term with
  | (?g ∘ (?h ∘ ?i))%Cat => 
    let _ := lazymatch goal with _ => 
      unify t g; unify s h end
    in constr:((g ∘ h ∘ i)%Cat)
  | (?g ∘ (?h ∘ ?i))%Cat => 
    let subpart := constr:((h ∘ i)%Cat) in 
    let ptnered := partnered t s subpart in
    constr:((g ∘ ptnered)%Cat)
  | _ => constr:(term)
  end
  in partnered t s term.

Ltac partnered_in_term_nofail t s term :=
  let raterm := right_associate_term' term in 
  partnered_in_RA_term_nofail t s raterm.



Ltac partnered_in_RA_term t s term :=
  let rec partnered t s term :=
  match term with
  | (?g ∘ (?h ∘ ?i))%Cat => 
    let _ := lazymatch goal with _ => 
      unify t g; unify s h end in
    constr:((g ∘ h ∘ i)%Cat)
  | (?g ∘ (?h ∘ ?i))%Cat => 
    let subpart := constr:((h ∘ i)%Cat) in 
    let ptnered := partnered t s subpart in
    constr:((g ∘ ptnered)%Cat)
  | (?g ∘ ?h)%Cat => 
    let _ := lazymatch goal with _ => 
      unify t g; unify s h end in
    constr:((g ∘ h)%Cat)
  | @mor_tensor _ ?cC ?mC _ _ _ _ ?f ?g =>
    let out := match goal with 
    | _ => let mf := partnered f in 
      constr:(mC.(mor_tensor) mf g)
    | _ => let mg := partnered g in 
      constr:(mC.(mor_tensor) f mg)
    end
    in constr:(out)
  end
  in partnered t s term.

Ltac partnered_in_term t s term :=
  let raterm := right_associate_term' term in 
  partnered_in_RA_term t s raterm.

Ltac try_partnered_in_term t s term :=
  let out := match goal with
  | |- _ => 
    let raterm := right_associate_term' term in 
    partnered_in_RA_term t s raterm
  | |- _ => constr:(term)
  end in constr:(out).
  
Ltac show_equiv_partnered_in_RA_term t s term :=
  let rec show_part t s term := 
  match term with
  | (?g ∘ (?h ∘ ?i))%Cat => 
    let _ := lazymatch goal with _ => 
      unify t g; unify s h end in
    (* constr:((g ∘ h ∘ i)%Cat) *)
    symmetry; apply assoc
  | (?g ∘ (?h ∘ ?i))%Cat => 
    let subpart := constr:((h ∘ i)%Cat) in 
    (* constr:((g ∘ ptnered)%Cat) *)
    apply compose_cancel_l;
    show_part t s subpart
  | (?g ∘ ?h)%Cat => 
    (* let _ := lazymatch goal with _ => 
      unify t g; unify s h end in
    constr:((g ∘ h)%Cat) *)
    reflexivity
  | @mor_tensor _ ?cC ?mC _ _ _ _ ?f ?g =>
    apply (tensor_compat); 
    [ first [reflexivity | show_part f] | first [reflexivity | show_part g] ]
  end
  in show_part t s term.

Ltac show_equiv_partnered_in_term t s term :=
  let raterm := right_associate_term' term in 
  transitivity raterm;
  [ show_equiv_right_associate_term' term
  | show_equiv_partnered_in_RA_term t s raterm ].

Ltac partner_in_term t s term := 
  let ptnered := partnered_in_term t s term in
  let H := fresh in 
  assert (H : (term ≃ ptnered)%Cat) 
    by (show_equiv_partnered_in_term t s term);
  setoid_rewrite H;
  clear H.


Ltac show_equiv_partnered_in_RA_term_debug t s term :=
  let rec show_part t s term := 
  match term with
  | (?g ∘ (?h ∘ ?i))%Cat => 
    let _ := lazymatch goal with _ => 
      unify t g; unify s h end in
    (* constr:((g ∘ h ∘ i)%Cat) *)
    idtac "unified; associating"; 
    print_state;
    symmetry; apply assoc
  | (?g ∘ (?h ∘ ?i))%Cat => 
    idtac "starting cancelling";
    let subpart := constr:((h ∘ i)%Cat) in 
    (* constr:((g ∘ ptnered)%Cat) *)
    idtac "cancelling" g "down to" subpart; 
    apply compose_cancel_l;
    print_state;
    show_part t s subpart
  | (?g ∘ ?h)%Cat => 
    (* let _ := lazymatch goal with _ => 
      unify t g; unify s h end in
    constr:((g ∘ h)%Cat) *)
    idtac "ended; reflexivity"; 
    print_state;
    reflexivity
  | @mor_tensor _ ?cC ?mC _ _ _ _ ?f ?g =>
    apply (tensor_compat); 
    [ first [reflexivity | show_part f] | first [reflexivity | show_part g] ]
  end
  in show_part t s term.

Ltac show_equiv_partnered_in_term_debug t s term :=
  let raterm := right_associate_term' term in 
  transitivity raterm;
  [ 
    (* idtac "rassoc:"; 
    print_state;  *)
    show_equiv_right_associate_term' term 
  | 
    idtac "partnr:"; 
    print_state; 
    show_equiv_partnered_in_RA_term_debug t s raterm ].

Ltac partner_in_term_debug t s term := 
  let ptnered := partnered_in_term t s term in
  let H := fresh in 
  assert (H : (term ≃ ptnered)%Cat) 
    by (show_equiv_partnered_in_term_debug t s term);
  setoid_rewrite H;
  clear H.


Ltac gen_partnered_in_RA_term test term :=
  let rec partnered test term :=
  match term with
  | (?g ∘ (?h ∘ ?i))%Cat => 
    let _ := lazymatch goal with _ => 
      test g h end in
    constr:((g ∘ h ∘ i)%Cat)
  | (?g ∘ (?h ∘ ?i))%Cat => 
    let subpart := constr:((h ∘ i)%Cat) in 
    let ptnered := partnered test subpart in
    constr:((g ∘ ptnered)%Cat)
  | (?g ∘ ?h)%Cat => 
    let _ := lazymatch goal with _ => 
      test g h end in
    constr:((g ∘ h)%Cat)
  | @mor_tensor _ ?cC ?mC _ _ _ _ ?f ?g =>
    let out := match goal with 
    | _ => let mf := partnered test f in 
      constr:(mC.(mor_tensor) mf g)
    | _ => let mg := partnered test g in 
      constr:(mC.(mor_tensor) f mg)
    end
    in constr:(out)
  end
  in partnered test term.

Ltac gen_partnered_in_term test term :=
  let raterm := right_associate_term' term in 
  gen_partnered_in_RA_term test raterm.

Ltac try_gen_partnered_in_term test term :=
  let out := match goal with
  | |- _ => 
    let raterm := right_associate_term' term in 
    gen_partnered_in_RA_term test raterm
  | |- _ => constr:(term)
  end in constr:(out).
  
Ltac show_equiv_gen_partnered_in_RA_term test term :=
  let rec show_part test term := 
  match term with
  | (?g ∘ (?h ∘ ?i))%Cat => 
    let _ := lazymatch goal with _ => 
      test g h end in
    (* constr:((g ∘ h ∘ i)%Cat) *)
    symmetry; apply assoc
  | (?g ∘ (?h ∘ ?i))%Cat => 
    let subpart := constr:((h ∘ i)%Cat) in 
    (* constr:((g ∘ ptnered)%Cat) *)
    apply compose_cancel_l;
    show_part test subpart
  | (?g ∘ ?h)%Cat => 
    (* let _ := lazymatch goal with _ => 
      unify t g; unify s h end in
    constr:((g ∘ h)%Cat) *)
    reflexivity
  | @mor_tensor _ ?cC ?mC _ _ _ _ ?f ?g =>
    apply (tensor_compat); 
    [ first [reflexivity | show_part test f] | first [reflexivity | show_part test g] ]
  end
  in show_part test term.

Ltac show_equiv_gen_partnered_in_term test term :=
  let raterm := right_associate_term' term in 
  transitivity raterm;
  [ show_equiv_right_associate_term' term
  | show_equiv_gen_partnered_in_RA_term test raterm ].

Ltac gen_partner_in_term test term := 
  let ptnered := gen_partnered_in_term test term in
  let H := fresh in 
  assert (H : (term ≃ ptnered)%Cat) 
    by (show_equiv_gen_partnered_in_term test term);
  setoid_rewrite H;
  clear H.

Ltac gen_partner_in_term_then test term tac := 
  let ptnered := gen_partnered_in_term test term in
  let H := fresh in 
  assert (H : (term ≃ ptnered)%Cat) 
    by (show_equiv_gen_partnered_in_term test term);
  setoid_rewrite H;
  clear H;
  tac ptnered.

Ltac rep_gen_partner_in_term test term tac := 
  let ptnered := gen_partnered_in_term test term in
  let H := fresh in 
  assert (H : (term ≃ ptnered)%Cat) 
    by (show_equiv_gen_partnered_in_term test term);
  setoid_rewrite H;
  clear H;
  first [rep_gen_partner_in_term test term | tac term].

Ltac test_iso_inv_l t s :=
  let comp := constr:((t ∘ s)%Cat) in 
  lazymatch comp with
  | (reverse ?f ∘ forward ?f)%Cat => idtac
  end.

Ltac test_iso_inv_r t s :=
  let comp := constr:((t ∘ s)%Cat) in 
  lazymatch comp with
  | (forward ?f ∘ reverse ?f)%Cat => idtac
  end.

Ltac test_iso_inv_lr t s :=
  let comp := constr:((t ∘ s)%Cat) in 
  lazymatch comp with
  | (reverse ?f ∘ forward ?f)%Cat => idtac
  | (forward ?f ∘ reverse ?f)%Cat => idtac
  end.


Ltac cancel_ids_term term :=
  let rec clean term :=
  lazymatch term with
  | (compose ?cC (id_ _) (id_ ?A))%Cat => 
      constr:(cC.(c_identity) A)
  | (id_ _ ∘ ?g)%Cat => 
      let r := clean g in constr:(r)
  | (?g ∘ id_ _)%Cat => 
      let r := clean g in constr:(r)
  | (?f ∘ ?g)%Cat => 
      let fr := clean f in let gr := clean g in 
      constr:((fr ∘ gr)%Cat)
  | @mor_tensor ?C ?cC ?mC _ _ _ _ ?f ?g =>
      let fr := clean f in let gr := clean g in 
      constr:((mC.(mor_tensor) fr gr)%Cat)
  | _ => constr:(term)
  end
  in clean term.

Ltac show_equiv_cancel_ids_term term := 
  let rec show_clean term :=
  lazymatch term with
  | (id_ _ ∘ id_ ?A)%Cat => 
      (* constr:((id_ A)%Cat) *)
      apply left_unit
  | (id_ _ ∘ ?g)%Cat => 
      (* let r := clean g in constr:(r) *)
      transitivity g;
      [ apply left_unit | show_clean g ]
  | (?g ∘ id_ _)%Cat => 
      (* let r := clean g in constr:(r) *)
      transitivity g;
      [ apply right_unit | show_clean g ]
  | (id_ _ ∘ ?g)%Cat => 
      (* let r := clean g in constr:(r) *)
      transitivity g;
      [ apply left_unit | show_clean g ]
      (* constr:((id_ A)%Cat) *)
  | (?f ∘ ?g)%Cat => 
      (* let fr := clean f in let gr := clean g in 
      constr:((fr ∘ gr)%Cat) *)
      apply compose_compat;
      [ show_clean f | show_clean g ]
  | @mor_tensor ?C ?cC ?mC _ _ _ _ ?f ?g =>
      (* let fr := clean f in let gr := clean g in 
      constr:((mC.(mor_tensor) fr gr)%Cat) *)
      apply tensor_compat;
      [ show_clean f | show_clean g ]
  | _ => reflexivity
  end
  in show_clean term.

Ltac cancel_ids_in term :=
  let c := cancel_ids_term term in 
  let H := fresh in 
  assert (H : (term ≃ c)%Cat) by (show_equiv_cancel_ids_term term);
  setoid_rewrite H;
  clear H.

Ltac cancel_all_ids_term term :=
  let clean := cancel_ids_term in 
  let rec deep_clean term :=
  let r := clean term in 
  let out := match goal with 
  | _ => let _ := match goal with _ => unify r term end in
    constr:(term)
  | _ => let rr := deep_clean r in constr:(rr)
  end in constr:(out)
  in deep_clean term.


(* This ends up being faster than the functionally-equivlant 
  "repeat (cancel_ids_in term)" 
  (found ~20% faster on small example with 2 rounds needed)*)
Ltac cancel_all_ids term :=
  let c := cancel_ids_term term in 
  tryif unify c term then idtac else
  let H := fresh in 
  assert (H : (term ≃ c)%Cat) by (show_equiv_cancel_ids_term term);
  setoid_rewrite H;
  clear H;
  cancel_all_ids c.

Ltac cancel_liso term := 
  gen_partner_in_term test_iso_inv_l term;
  rewrite ?iso_inv_l.

Ltac cancel_lisos term := 
  repeat cancel_liso term.

(* These don't work because term changes before cancel_all_ids. 
   This could be fixed with a highly-modified gen_partner, but 
   for now the cases we care about (LHS, RHS) can be done specially. *)
(* Ltac cancel_lisos' term := 
  cancel_lisos term; cancel_all_ids term. *)

Ltac cancel_riso term := 
  gen_partner_in_term test_iso_inv_r term;
  rewrite ?iso_inv_r.

Ltac cancel_risos term := 
  repeat cancel_riso term.

(* Ltac cancel_risos' term := 
  cancel_risos term; cancel_all_ids term. *)

Ltac cancel_lriso term := 
  gen_partner_in_term test_iso_inv_lr term;
  rewrite ?iso_inv_l, ?iso_inv_r.

Ltac cancel_lrisos term := 
  repeat cancel_lriso term.

(* Ltac cancel_lrisos' term := 
  cancel_lrisos term; cancel_all_ids term. *)




Ltac lassoc_n_term_rec n base t :=
  match n with 
  | O => constr:((base ∘ t)%Cat)
  | S ?n' => match t with
    | (?g ∘ ?h)%Cat =>
        let base' := constr:((base ∘ g)%Cat) in
        (* let rest := constr:((h ∘ i)%Cat) in  *)
        lassoc_n_term_rec n' base' h
    | _ => constr:((base ∘ t)%Cat)
    end
  end.

Ltac lassoc_n_term n t :=
  match n with 
  | O => constr:(t)
  | S ?n' => match t with
    | (?g ∘ ?h)%Cat =>
        lassoc_n_term_rec n' g h
    end
  end.


Ltac lassoc_n_term_rec_debug n base t :=
  match n with 
  | O => constr:((base ∘ t)%Cat)
  | S ?n' => 
    let _ := match goal with _ => idtac "at" n' base t end in
    match t with
    | (?g ∘ ?h)%Cat =>
        let base' := constr:((base ∘ g)%Cat) in
        (* let rest := constr:((h ∘ i)%Cat) in  *)
        lassoc_n_term_rec n' base' h
    | _ => constr:((base ∘ t)%Cat)
    end
  end.

Ltac lassoc_n_term_debug n t :=
  match n with 
  | O => constr:(t)
  | S ?n' => match t with
    | (?g ∘ ?h)%Cat =>
        lassoc_n_term_rec_debug n' g h
    end
  end.

(* Shows base ∘ t ≃ lassoc_n_term_rec n base t 
  (relies on there being enough compositions of t, of course)*)
Ltac show_equiv_lassoc_n_term_rec n base t :=
  match n with 
  | O => (* constr:((base ∘ t)%Cat) *)
    reflexivity
  | S ?n' => match t with
    | (?g ∘ ?h)%Cat =>
      let base' := constr:((base ∘ g)%Cat) in
      (* let rest := constr:((h ∘ i)%Cat) in  *)
      (* lassoc_n_term_rec n' base' h *)
      transitivity ((base ∘ g ∘ h)%Cat);
      [ symmetry; apply assoc | 
        show_equiv_lassoc_n_term_rec n' base' h]
    | _ => reflexivity
    end
  end.

Ltac show_equiv_lassoc_n_term n t := 
  match n with 
  | O => (* constr:(t) *)
    reflexivity
  | S ?n' => match t with
    | (?g ∘ ?h)%Cat =>
        show_equiv_lassoc_n_term_rec n g h
    end
  end.



Ltac __next_Sn_of_comp n t := 
  lazymatch t with
  | (?g ∘ ?h)%Cat =>
    match n with
    | O => constr:(g)
    | S ?n' => let rest := __next_Sn_of_comp n' h in 
        constr:((g ∘ rest)%Cat)
    end
  | ?g => match n with O => constr:(g) end
  end.

Ltac __next_n_of_comp n t := 
  match n with
  | S ?n' => __next_Sn_of_comp n' t
  end.

Ltac n_partnered_in_RA_term pat n term :=
  let rec n_partnered term :=
  match term with
  | _ => let nextn := __next_n_of_comp n term in 
    let _ := match goal with _ => unify nextn pat end in
    lassoc_n_term n term 
  | (?g ∘ ?h)%Cat => let npart := n_partnered h in 
      constr:((g ∘ npart)%Cat)
  | mor_tensor ?mC ?f ?g =>
    let out :=
    match goal with
    | _ => let mf := n_partnered f in
      constr:((mC.(mor_tensor) mf g))
    | _ => let mg := n_partnered g in
      constr:((mC.(mor_tensor) f mg))
    end in constr:(out)
  end in 
  n_partnered term.

Ltac n_partnered_in_term pat n term :=
  let raterm := right_associate_term' term in 
  n_partnered_in_RA_term pat n raterm.

Ltac n_partnered_in_RA_term_debug pat n term :=
  let rec n_partnered term :=
  match term with
  | _ => let nextn := __next_n_of_comp n term in 
    let _ := match goal with _ => 
      idtac "trying" nextn; 
      unify nextn pat; 
      idtac "unified" end in
    lassoc_n_term_debug n term 
  | (?g ∘ ?h)%Cat => 
    let _ := match goal with _ => idtac "moving into" h end in 
    let npart := n_partnered h in 
      constr:((g ∘ npart)%Cat)
  | mor_tensor ?mC ?f ?g =>
    let _ := match goal with _ => idtac "searching tensor" end in   
    let out :=
    match goal with
    | _ => let mf := n_partnered f in
      let _ := match goal with _ => idtac "found in top" f "=~=>" mf end in 
      constr:((mC.(mor_tensor) mf g))
    | _ => let mg := n_partnered g in
      let _ := match goal with _ => idtac "found in bot" g "=~=>" mg end in 
      constr:((mC.(mor_tensor) f mg))
    end in constr:(out)
  end in 
  n_partnered term.

Ltac n_partnered_in_term_debug pat n term :=
  let raterm := right_associate_term' term in 
  n_partnered_in_RA_term_debug pat n raterm.

Ltac show_equiv_n_partnered_in_RA_term pat n term :=
  let rec show_n_partnered term :=
  match term with
  | _ => 
    show_equiv_lassoc_n_term n term  
    (* let nextn := __next_n_of_comp n term in 
    let _ := match goal with _ => unify nextn pat end in
    lassoc_n_term n term  *)
  | (?g ∘ ?h)%Cat => 
    apply compose_cancel_l;
    show_n_partnered h
  | mor_tensor ?mC ?f ?g =>
    first [
      apply tensor_cancel_r; show_n_partnered f
    | apply tensor_cancel_l; show_n_partnered g ]
  end in 
  show_n_partnered term.

Ltac show_equiv_n_partnered_in_term pat n term :=
  let raterm := right_associate_term' term in 
  transitivity raterm;
  [ show_equiv_right_associate_term' term
  | show_equiv_n_partnered_in_RA_term pat n raterm ].

Ltac n_partner_in_term pat n term :=
  let npart := n_partnered_in_term pat n term in 
  tryif unify npart term then idtac else
  let H := fresh in 
  assert (H : (term ≃ npart)%Cat) by 
    (show_equiv_n_partnered_in_term pat n term);
  setoid_rewrite H;
  clear H.

Ltac n_partner_in_term_debug pat n term :=
  let npart := n_partnered_in_term_debug pat n term in 
  tryif unify npart term then idtac else
  let H := fresh in 
  assert (H : (term ≃ npart)%Cat) by 
    (show_equiv_n_partnered_in_term pat n term);
  setoid_rewrite H;
  clear H.

Ltac __count_comps t :=
  lazymatch t with
  | (?g ∘ ?h)%Cat => let n' := __count_comps h in constr:(S n')
  | _ => constr:(O)
  end.

Ltac __count_comp_terms t :=
  lazymatch t with
  | (?g ∘ ?h)%Cat => let n' := __count_comp_terms h in constr:(S n')
  | _ => constr:(S O)
  end.

(* Section on handy versions of these tactics: *)

Ltac apply_to_LHS tac :=
  lazymatch goal with |- (?LHS ≃ ?RHS)%Cat => tac LHS end.

Ltac apply_to_RHS tac := 
  lazymatch goal with |- (?LHS ≃ ?RHS)%Cat => tac RHS end.

Ltac apply_to_LRHS tac := 
  lazymatch goal with |- (?LHS ≃ ?RHS)%Cat => 
  (try tac LHS); (try tac RHS) end.
  

Ltac rassoc_LHS := apply_to_LHS rassoc.
  (* match goal with |- (?LHS ≃ ?RHS)%Cat => rassoc LHS end. *)
Ltac rassoc_RHS := apply_to_RHS rassoc.
  (* match goal with |- (?LHS ≃ ?RHS)%Cat => rassoc RHS end. *)
Ltac rassoc_LRHS := apply_to_LRHS rassoc.

Ltac rassoc'_LHS := apply_to_LHS rassoc'.
Ltac rassoc'_RHS := apply_to_RHS rassoc'.
Ltac rassoc'_LRHS := apply_to_LRHS rassoc'.

Ltac lassoc_LHS := apply_to_LHS lassoc.
  (* match goal with |- (?LHS ≃ ?RHS)%Cat => lassoc LHS end. *)
Ltac lassoc_RHS := apply_to_RHS lassoc.
  (* match goal with |- (?LHS ≃ ?RHS)%Cat => lassoc RHS end. *)
Ltac lassoc_LRHS := apply_to_LRHS lassoc.


Ltac partner_LHS t s := 
  let func := partner_in_term t s in   
  apply_to_LHS func.

Ltac partner_RHS t s := 
  let func := partner_in_term t s in   
  apply_to_RHS func.

Ltac partner_LRHS t s := 
  let func := partner_in_term t s in   
  apply_to_LRHS func.

Ltac partner t s :=
  first 
    [ partner_LHS t s
    | partner_RHS t s].

Ltac gen_partner_LHS test := 
  let func := gen_partner_in_term test in   
  apply_to_LHS func.

Ltac gen_partner_RHS test := 
  let func := gen_partner_in_term test in   
  apply_to_RHS func.

Ltac gen_partner_LRHS test := 
  let func := gen_partner_in_term test in   
  apply_to_LRHS func.

Ltac cancel_id_LHS := apply_to_LHS cancel_ids_in.
Ltac cancel_id_RHS := apply_to_RHS cancel_ids_in.
Ltac cancel_id_LRHS := apply_to_LRHS cancel_ids_in.

Ltac cancel_ids_LHS := apply_to_LHS cancel_all_ids.
Ltac cancel_ids_RHS := apply_to_RHS cancel_all_ids.
Ltac cancel_ids_LRHS := apply_to_LRHS cancel_all_ids.

Ltac cancel_lisos_LHS := apply_to_LHS cancel_lisos; cancel_ids_LHS.
Ltac cancel_lisos_RHS := apply_to_RHS cancel_lisos; cancel_ids_RHS.
Ltac cancel_lisos_LRHS := apply_to_LRHS cancel_lisos; cancel_ids_LRHS.

Ltac cancel_risos_LHS := apply_to_LHS cancel_risos; cancel_ids_LHS.
Ltac cancel_risos_RHS := apply_to_RHS cancel_risos; cancel_ids_RHS.
Ltac cancel_risos_LRHS := apply_to_LRHS cancel_risos; cancel_ids_LRHS.

Ltac cancel_lrisos_LHS := apply_to_LHS cancel_lrisos; cancel_ids_LHS.
Ltac cancel_lrisos_RHS := apply_to_RHS cancel_lrisos; cancel_ids_RHS.
Ltac cancel_lrisos_LRHS := apply_to_LRHS cancel_lrisos; cancel_ids_LRHS.

Ltac weak_foliate_LHS := apply_to_LHS weak_foliate.
Ltac weak_foliate_RHS := apply_to_RHS weak_foliate.
Ltac weak_foliate_LRHS := apply_to_LRHS weak_foliate.

Ltac strong_foliate_LHS := apply_to_LHS strong_foliate_no_id.
Ltac strong_foliate_RHS := apply_to_RHS strong_foliate_no_id.
Ltac strong_foliate_LRHS := apply_to_LRHS strong_foliate_no_id.


Ltac cancel_ids := cancel_ids_LRHS.
Ltac cancel_isos := cancel_lrisos_LRHS.
Ltac weak_foliate_goal := weak_foliate_LRHS.
Ltac strong_foliate_goal := strong_foliate_LRHS.

Ltac foliate := (fun t => ltac:(strong_foliate t; rewrite ?tensor_id; cancel_ids)).
Ltac foliate_LHS := strong_foliate_LHS.
Ltac foliate_RHS := strong_foliate_RHS.
Ltac foliate_LRHS := strong_foliate_LRHS.

Ltac cat_cleanup := repeat (cancel_isos; cancel_ids).

Ltac cat_easy := cat_cleanup; try easy; rassoc_LRHS; try easy;
  rewrite ?tensor_id; try easy; weak_foliate_LRHS; easy.



Tactic Notation "LHS" tactic(tac) := apply_to_LHS tac.
Tactic Notation "RHS" tactic(tac) := apply_to_RHS tac.
Tactic Notation "LRHS" tactic(tac) := apply_to_LRHS tac.

Tactic Notation "assoc_rw" open_constr(lem) "within" constr(term) :=
  let e := fresh in let e' := fresh in 
  epose proof @lem as e;
  repeat (rename e into e'; epose proof (e' _) as e; clear e');
  match type of e with
  | (?g ≃ _)%Cat =>
  let rg := right_associate_term g in 
  let n := __count_comp_terms rg in 
  n_partner_in_term rg n term;
  let lg := left_associate_term g in 
  tryif unify g lg then idtac else (
    let H := fresh in 
    print_state;
    assert (H : (g ≃ lg)%Cat) by (show_equiv_left_associate_term g);
    try setoid_rewrite H in e;
    clear H);
  setoid_rewrite e;
  clear e
  end.

Tactic Notation "assoc_rw" open_constr(lem) :=
  match goal with 
  |- (?LHS ≃ ?RHS)%Cat =>
  first [
    assoc_rw lem within LHS 
  | assoc_rw lem within RHS ]
  end.

Tactic Notation "assoc_rw_to_Cat" open_constr(lem) "within" constr(term) :=
  let e := fresh in let e' := fresh in 
  epose proof @lem as e;
  to_Cat_in e;
  repeat (rename e into e'; epose proof (e' _) as e; clear e');
  match type of e with
  | (?g ≃ _)%Cat =>
  let rg := right_associate_term g in 
  let n := __count_comp_terms rg in 
  n_partner_in_term rg n term;
  let lg := left_associate_term g in 
  tryif unify g lg then idtac else (
    let H := fresh in 
    print_state;
    assert (H : (g ≃ lg)%Cat) by (show_equiv_left_associate_term g);
    try setoid_rewrite H in e;
    clear H);
  setoid_rewrite e;
  clear e
  end.


Tactic Notation "assoc_rw_to_Cat" open_constr(lem) :=
  match goal with 
  |- (?LHS ≃ ?RHS)%Cat =>
  first [
    assoc_rw_to_Cat lem within LHS 
  | assoc_rw_to_Cat lem within RHS ]
  end.


Section VizualizationExamples.

Context {CC : Type} {cC : Category CC} {cCh : CategoryCoherence cC}
  {mC : MonoidalCategory cC} {mCh : MonoidalCategoryCoherence mC}
  {bC : BraidedMonoidalCategory mC} {bCh : BraidedMonoidalCategoryCoherence bC}.
Local Open Scope Cat_scope.

Lemma weak_foliation_example {A B M N P Q R : CC}
  (f : A <~> B) (g : B ~> B) (h : N ~> M) (j : P ~> Q)
  (k : M × Q ~> I × R): 
  (f ∘ g ∘ f^-1) ⊗ (h ⊗ j ∘ k ∘ λ_ R) ≃
  f ⊗ (h ⊗ j) ∘ (g ⊗ k ∘ f^-1 ⊗ λ_ R).
Proof.
  (* RHS is weak foliation of LHS *)
  LHS weak_foliate.
  cat_easy. (* reflexivity *)
Qed.

Lemma assoc_rw_example {A B C M N : CC}
  (h : A ~> B) (j: A ~> C) (f : B ~> M) (g : C ~> N)  : 
  (β_ _, _)^-1 ∘ h ⊗ j ∘ f ⊗ g ∘ β_ _, _
  ≃ (j ∘ g) ⊗ (h ∘ f).
Proof. (* 1 *)
  assoc_rw braiding_natural. (* 2 *)
  assoc_rw braiding_natural. (* 3 *)
  (* cat_easy solves this immediately, but explicitly: *)
  cancel_isos. (* 4 *)
  RHS weak_foliate. (* 5 *)
  reflexivity.
Qed.

Lemma assoc_rw_example_alt {A B C M N : CC}
  (f : A ~> B) (g : M ~> N)  : 
  (β_ A, M)^-1 ∘ f ⊗ g ∘ β_ B, N
  ≃ g ⊗ f.
Proof. (* 1 *)
  assoc_rw braiding_natural. (* 2 *)
  (* cat_easy solves this immediately, but explicitly: *)
  cancel_isos. (* 3 *)
  reflexivity.
Qed.

Lemma associator_viz {A B C M N P : CC}
  (f : A ~> M) (g : B ~> N) (h : C ~> P) :
  f ⊗ g ⊗ h ∘ α_ M, N, P ≃ α_ A, B, C ∘ f ⊗ (g ⊗ h).
Proof.
  rewrite associator_cohere.
  easy.
Qed.

Lemma assoc_lunit_viz {A B M N : CC}
  (f : A ~> M) (g : B ~> N):
  (f ∘ (ρ_ _)^-1) ⊗ g ∘ (α_ _, _, _) ∘ id_ _ ⊗ λ_ _ ≃ f ⊗ g.
Proof.
Abort.

Lemma assoc_lunit_viz_2 {A B M N : CC}
  (f : A ~> M) (g : B ~> N) n:
  ( (ρ_ A)^-1) ⊗ g ∘ (α_ _, _, _) ∘ id_ _ ⊗ λ_ _ ≃ n.
Proof.
Abort.

Lemma assoc_lunit_viz_alt {A B C M N P : CC}
  (f : A ~> M) (g : B ~> N) (h : C ~> P) :
  (f ∘ (ρ_ _)^-1) ⊗ g ∘ (α_ _, _, _) ≃ f ⊗ (g ∘ (λ_ _)^-1).
Proof.
Abort.

Lemma assoc_lunit_viz_alt {A B C M N P : CC}
  (f : A ~> M) (g : B ~> N) (h : C ~> P) :
  ((ρ_ A)^-1) ⊗ g ∘ (α_ _, _, _) ≃ id_ _ ⊗ (g ∘ (λ_ _)^-1).
Proof.
Abort.

Lemma compose_assoc_viz {A B C D : CC}
  (f : A ~> B) (g : B ~> C) (h : C ~> D):
  f ∘ g ∘ h ≃ f ∘ (g ∘ h).
Abort.



Lemma accoc_units_viz_new {A B C D : CC} :
  ((ρ_ A)^-1 ∘ β_ A, I) ⊗ id_ B ∘ (α_ I, A, B ∘ λ_ (A × B)) ≃ id_ (A × B).
  let ty := type of (mCh.(triangle) A B)
  in assert (H: ty); [admit |]; clear H.
  let ty := type of (mCh.(pentagon) A B C D)
  in assert (H: ty); [admit |]; clear H.
  let ty := type of (bCh.(hexagon_1) A B C)
  in assert (H: ty); [> admit |]; clear H.
  assert nat.
  Abort.

Lemma accoc_units_viz {A B} :
  (ρ_ A)^-1 ⊗ id_ B ∘ α_ A, I, B ∘ id_ A ⊗ λ_ B ≃ id_ (A × B).
  Abort.


Lemma assoc_lunit_viz_bad {A B C M N P : CC}
  (f : A ~> M) (g : B ~> N) (h : C ~> P) :
  f ⊗ (g ∘ (λ_ _)^-1) ∘ (α_ _, _, _) ^-1 ∘ ρ_ _ ⊗ id_ _ ≃ f ⊗ g.
Proof.
Abort.

Lemma laura_1 {A B C D M N P Q: CC} 
  (f : M × N <~> A × B) (g : M ~> C)
  (h : N × P ~> Q) n : 
  f^-1 ⊗ id_ P ∘ α_ M, N, P ∘ g ⊗ h ≃ n.
Abort.

Lemma mx_viz_thing {n m o p q r : CC}
  (A : n ~> m) (B : m ~> o)
  (C : p ~> q) (D : q ~> r):
  (A ⊗ C) ∘ (B ⊗ D) ≃ (A ∘ B) ⊗ (C ∘ D).
Abort.


Lemma uncle_relation {person : CC}
  (brother : person ~> person)
  (parent : person ~> person) :
  parent ∘ brother ≃ id_ person.
  Admitted.



Lemma weak_foliation_example_2 {A B M N P Q R : CC}
  (f : A <~> B) (g : B ~> B) (h : N ~> M) (j : P ~> Q)
  (k : M × Q ~> I × R): 
  (f ∘ g ∘ f^-1) ⊗ (h ⊗ j ∘ k ∘ λ_ R) ≃
  f ⊗ (h ⊗ j) ∘ g ⊗ k ∘ f^-1 ⊗ λ_ R.
Proof.
  LHS weak_foliate.
  cat_easy.
  (* LHS foliate.
  RHS foliate.
  cat_easy.
  LHS lassoc.
  RHS 
  triangle
  cat_easy.  *)
Qed.

Lemma weak_foliation_example_2' {A B M N P Q R : CC}
  (f : A <~> B) (g : B ~> B) (h : N ~> M)
  (k : M × Q ~> I × R) n: 
  (f ∘ g ∘ f^-1) ⊗ (k ∘ λ_ R) ≃
  n.
Proof.
  LHS foliate.
  Abort.

Lemma foliation_example_test {A B C M N P : CC} 
  (f : A ~> B) (g : B ~> C) (h : M ~> N) (j : N ~> P) n :
  (f ∘ g) ⊗ (h ∘ j) ≃ n.
Proof.
  LHS foliate.
  Abort.





End VizualizationExamples.

Section Testing.
Local Open Scope Cat_scope.

Lemma TODO_fix_assoc_rw 
  {C : Type} {cC : Category C} {cCh : CategoryCoherence cC}
  {mC : MonoidalCategory cC} {mCh : MonoidalCategoryCoherence mC}
  {bC : BraidedMonoidalCategory mC} {bCh : BraidedMonoidalCategoryCoherence bC}
  {A B M N P Q R : C}
  (h : A ~> B) (f : B ~> M) (g : B ~> N) 
  (m : Q ~> R) (k : R × N ~> Q) (j : M ~> A) n : 
  α_ _, _, _ ∘ m ⊗ ((h ∘ f) ⊗ (h ∘ g) ∘ β_ _, _) ∘ (α_ _, _, _)^-1 ∘ k ⊗ j
  ≃ n.
Proof.
  LHS rassoc.
  
  Fail assoc_rw braiding_natural. (* ??? *)
  Abort.

Variables (C : Type) (cC cC' cC'' : Category C)
  (cCh : CategoryCoherence cC) (cC'h : CategoryCoherence cC') (cC''h : CategoryCoherence cC'')
  (mC0   mC1   : @MonoidalCategory C cC) (mC0'  mC1'  : @MonoidalCategory C cC') (mC0'' mC1'' : @MonoidalCategory C cC'')
  (mC0h   : MonoidalCategoryCoherence mC0) (mC0'h  : MonoidalCategoryCoherence mC0') (mC0''h : MonoidalCategoryCoherence mC0'')
  (mC1h   : MonoidalCategoryCoherence mC1) (mC1'h  : MonoidalCategoryCoherence mC1') (mC1''h : MonoidalCategoryCoherence mC1'')
  (A B M N : C)
  (f   f0   : cC.(morphism)   A B) (g   g0   : cC.(morphism)   B M)  (h   h0   : cC.(morphism)   A M) (i   i0   : cC.(morphism)   M N)
  (* (j   j0   : cC.(morphism)   B M) (k   k0   : cC.(morphism)   A M) (f'  f0'  : cC'.(morphism)  A B) (g'  g0'  : cC'.(morphism)  B M) 
  (h'  h0'  : cC'.(morphism)  A M) (i'  i0'  : cC'.(morphism)  M N) (j'  j0'  : cC'.(morphism)  B M) (k'  k0'  : cC'.(morphism)  A M)
  (f'' f0'' : cC''.(morphism) A B) (g'' g0'' : cC''.(morphism) B M) (h'' h0'' : cC''.(morphism) A M) (i'' i0'' : cC''.(morphism) M N)
  (j'' j0'' : cC''.(morphism) B M) (k'' k0'' : cC''.(morphism) A M) *)
  .
(* Goal True. *)

Existing Instance cC. Existing Instance cC'. Existing Instance cC''.
Existing Instance mC0.   Existing Instance mC1.
Existing Instance mC0'.  Existing Instance mC1'.
Existing Instance mC0''. Existing Instance mC1''.


(* Goal (f ⊗ g ⊗ h) ≃ (f ⊗ g ⊗ h). *)
(* easy. *)


(* Goal (f ⊗ (g ⊗ h)) ≃ (f ⊗ (g ⊗ h)). *)
(* easy. *)


(* Goal (f ⊗ (g ⊗ h)) ≃ (f ⊗ (g ⊗ h)). *)
(* easy. *)

(* Goal (f ∘ g) ⊗ h ≃ f ⊗ h ∘ g ⊗ id_ M. *)
(* Admitted. *)

(* Goal (f ∘ g) ⊗ h ≃ f ⊗ id_ A ∘ (id_ B ⊗ h ∘ g ⊗ id_ M). *)
(* Admitted. *)

Lemma test_weak_foliate : forall
  {a b m n o} (f : a ~> b) (g : m ~> n) (h : n ~> o),
  f ⊗ (g ∘ h) ≃ f ⊗ g ∘ (id_ b ⊗ h).
Proof.
  intros.
  match goal with
  |- ?T ≃ _ => weak_foliate T
    (* let wf := weak_foliate_form T in
    let H := fresh in
    assert (H : T ≃ wf) by show_equiv_weak_foliate_form T *)
    (* setoid_rewrite H *)
  end.
  easy.
Qed.

Lemma test_strong_foliate : forall 
  {a b m n o} (f : a ~> b) (g : m ~> n) (h : n ~> o),
  f ⊗ (g ∘ h) ≃ f ⊗ g ∘ (id_ b ⊗ h).
Proof.
  intros.
  match goal with
  |- ?T ≃ ?T' => strong_foliate T; strong_foliate T'
  end.
  easy.
Qed.

Lemma test_strong_foliate_no_id_1 : forall 
  {a b m n o} (f : a ~> b) (g : m ~> n) (h : n ~> o),
  f ⊗ (g ∘ h) ≃ f ⊗ g ∘ (id_ b ⊗ h).
Proof.
  intros.
  match goal with
  |- ?T ≃ ?T' => strong_foliate_no_id T; strong_foliate_no_id T'
  end.
  easy.
Qed.

(* Require Import Program.Tactics. *)



Lemma test_strong_foliate_no_id_2' : forall 
  {a b m n o} (f : a ~> b) (g : m ~> n) (h : n ~> o),
  f ⊗ (g ∘ id_ _ ∘ h ∘ id_ _) ⊗ (id_ a ⊗ id_ b) ≃ 
  f ⊗ g ⊗ (id_ a ⊗ id_ b) ∘ ((id_ b ⊗ h) ⊗ (id_ a ⊗ id_ b)).
Proof.
  intros.
  do 2 assoc_rw right_unit.
  LHS weak_foliate.
  rewrite tensor_id.
  easy.
Qed.

Lemma test_strong_foliate_no_id_2 : forall 
  {a b m n o} (f : a ~> b) (g : m ~> n) (h : n ~> o),
  f ⊗ (g ∘ (id_ _ ∘ h) ∘ (id_ _ ∘ id_ _)) ⊗ (id_ a ⊗ id_ b) ≃ 
  f ⊗ g ⊗ (id_ a ⊗ id_ b) ∘ ((id_ b ⊗ h) ⊗ (id_ a ⊗ id_ b)).
Proof.
  intros.
  rewrite !right_unit.
  assoc_rw right_unit.
  LHS weak_foliate.
  cat_easy.
Qed.

Lemma gen_partner_test : forall {C} {cC:Category C} 
  {cCh : CategoryCoherence cC} {A B1 M1 B2 M2 : C} 
  (g1 : B1 <~> M1) (f: M1 ~> B2) (g2 : B2 <~> M2),
    g1 ∘ f ∘ g2 ∘ g2^-1 ≃ g1 ∘ f.
Proof.
  intros.
  cancel_isos.
  cat_easy.
Qed.

Goal True.


assert ((id_ _ ∘ id_ _ ∘ id_ _ ∘ f ∘ (g ∘ i)) ≃ f ∘ g ∘ i) by cat_easy.


Ltac test_show_partnered t s term :=
  let ptnered := partnered_in_term t s term in
  let H := fresh in 
  assert (H : (term ≃ ptnered)%Cat) by (show_equiv_partnered_in_term t s term);
  (* setoid_rewrite H; *)
  clear H.
Ltac test_show_partnered_debug t s term :=
  let ptnered := partnered_in_term t s term in
  let H := fresh in 
  assert (H : (term ≃ ptnered)%Cat) by (show_equiv_partnered_in_term_debug t s term);
  (* setoid_rewrite H; *)
  clear H.

test_show_partnered f g (f ∘ g).
test_show_partnered g i (f ∘ (g ∘ i)).
test_show_partnered f g (f ∘ (g ∘ i)).

test_show_partnered f g (id_ _ ∘ id_ _ ∘ id_ _ ∘ f ∘ (g ∘ i)).
test_show_partnered f g (id_ _ ∘ id_ _ ∘ id_ _ ∘ f ∘ g ∘ i).
test_show_partnered f g (id_ _ ∘ id_ _ ∘ id_ _ ∘ f ∘ g ∘ i ∘ id_ _ ∘ id_ _).


Ltac test_partnered t s term :=
  let ptnrd := partnered_in_term t s term in
  (* idtac term "≈≈>" ptnrd. *)
  (* For compile: *)
  idtac.

test_partnered f g (f ∘ g).
test_partnered g i (f ∘ (g ∘ i)).
Fail test_partnered f i (f ∘ (g ∘ i)).
test_partnered f g (f ∘ (g ∘ i)).

test_partnered f g (id_ _ ∘ id_ _ ∘ id_ _ ∘ f ∘ (g ∘ i)).
test_partnered f g (id_ _ ∘ id_ _ ∘ id_ _ ∘ f ∘ g ∘ i).
test_partnered f g (id_ _ ∘ id_ _ ∘ id_ _ ∘ f ∘ g ∘ i ∘ id_ _ ∘ id_ _).


Ltac test_partnered_nf t s term :=
  let ptnrd := partnered_in_term_nofail t s term in
  (* idtac term "≈≈>" ptnrd. *)
  (* For compile: *)
  idtac.

test_partnered_nf f g (f ∘ g).
test_partnered_nf g i (f ∘ (g ∘ i)).
test_partnered_nf f i (f ∘ (g ∘ i)).
test_partnered_nf f g (f ∘ (g ∘ i)).

test_partnered_nf f g (id_ _ ∘ id_ _ ∘ id_ _ ∘ f ∘ (g ∘ i)).
test_partnered_nf f g (id_ _ ∘ id_ _ ∘ id_ _ ∘ f ∘ g ∘ i).
test_partnered_nf f g (id_ _ ∘ id_ _ ∘ id_ _ ∘ f ∘ g ∘ i ∘ id_ _ ∘ id_ _).





Local Ltac test_show_unfold_no_id_of_wf f :=
  let wf := weak_foliate_form f in
  let sf := unfold_tensor_stack_no_id wf in
  (* idtac sf; *)
  let H := fresh in 
  assert (H : wf ≃ sf) by (show_equiv_unfold_tensor_stack_no_id wf);
  clear H.

test_show_unfold_no_id_of_wf (f ⊗ (f0 ∘ g0 ∘ id_ _) ⊗ (id_ A ⊗ id_ B))%Cat.


Local Ltac test_show_unfold_no_id f :=
  let sf := unfold_tensor_stack_no_id f in
  (* idtac sf; *)
  let H := fresh in 
  assert (H : f ≃ sf) by 
    (show_equiv_unfold_tensor_stack_no_id f);
  (* (show_equiv_unfold_tensor_stack_no_id f; print_state); *)
  clear H.

test_show_unfold_no_id ((id_ B ⊗ id_ M ⊗ id_ (A × B)))%Cat.
test_show_unfold_no_id ((f0 ∘ g0 ∘ id_ _) ⊗ (id_ A))%Cat.
test_show_unfold_no_id (f ⊗ (f0 ∘ g0 ∘ id_ _))%Cat.



test_show_unfold_no_id (f ⊗ (f0 ∘ g0) ⊗ (id_ A))%Cat.
test_show_unfold_no_id (f ⊗ (f0 ∘ g0 ∘ id_ _) ⊗ (id_ A ⊗ id_ B))%Cat.
test_show_unfold_no_id (f ⊗ (f0 ∘ g0 ∘ id_ _) ⊗ (id_ (A × B)))%Cat.
test_show_unfold_no_id (f ⊗ f0 ⊗ (id_ A ⊗ id_ B))%Cat.
test_show_unfold_no_id (id_ B ⊗ g0 ⊗ id_ (A × B))%Cat.



Local Ltac test_show_st_of_wk f :=
  let wf := weak_foliate_form f in
  let sf := strong_foliate_form_of_weak wf in
  let H := fresh in 
  assert (H: (wf ≃ sf)%Cat) by (show_equiv_strong_foliate_form_of_weak wf);
  clear H.

test_show_st_of_wk f.
test_show_st_of_wk (f ∘ g)%Cat.
test_show_st_of_wk (f ⊗ g)%Cat.

test_show_st_of_wk (f ⊗ (f ∘ g))%Cat.
test_show_st_of_wk ((f ⊗ ((f ∘ g) ⊗ (f0 ∘ g0))))%Cat.




Local Ltac test_show_unfold f :=
  let sf := unfold_tensor_stack f in
  let H := fresh in 
  assert (H : f ≃ sf) by (show_equiv_unfold_tensor_stack f);
  clear H.

test_show_unfold f.
test_show_unfold (f ∘ g)%Cat.
test_show_unfold (f ⊗ g)%Cat.
test_show_unfold ((f ⊗ (f ∘ g) ⊗ (f0 ∘ g0))).

test_show_unfold ((f ∘ g) ⊗ (f0 ∘ g0)).
test_show_unfold ((f ∘ g) ⊗ (f0)).
test_show_unfold ((f ⊗ ((f ∘ g) ⊗ (f0 ∘ g0)))).



Local Ltac test_show_st_bot f B mC :=
  let sf := stack_comp_id_bot f B mC in
  (* idtac f sf; *)
  let H := fresh in 
  assert (H : f ⊗ id_ B ≃ sf) by (show_equiv_stack_comp_id_bot f B mC);
  clear H.

Local Ltac test_show_st_top f A mC :=
  let sf := stack_comp_id_top f A mC in
  let H := fresh in 
  assert (H : id_ A ⊗ f ≃ sf) by (show_equiv_stack_comp_id_top f A mC);
  clear H.

Local Ltac test_show_st_top_bot f A mC :=
  test_show_st_bot f A mC;
  test_show_st_top f A mC.

test_show_st_top_bot f B mC0.
test_show_st_top_bot (f ∘ g) B mC0.
test_show_st_top_bot (f ∘ g ∘ i) B mC0.
test_show_st_top_bot (f ∘ g ∘ i ∘ id_ _ ∘ id_ _) B mC0.
test_show_st_top_bot (f ∘ (g ∘ id_ _) ∘ i ∘ id_ _ ∘ id_ _) B mC0.
test_show_st_top_bot (f ∘ (g ∘ id_ _) ∘ (i ∘ id_ _) ∘ id_ _) B mC0.
test_show_st_top_bot ((f ⊗ g) ∘ (g ⊗ i)) B mC0.

test_show_st_bot ((f ⊗ id_ A ∘ (id_ B ⊗ f0 ∘ id_ B ⊗ g0))) A mC1.


Local Ltac test_st_of_wk f :=
  let wf := weak_foliate_form f in
  let sf := strong_foliate_form_of_weak wf in
  (* idtac wf "=~=>" sf. *)
  (* For compile: *)
  idtac.

test_st_of_wk f.
test_st_of_wk (f ∘ g).
test_st_of_wk (f ⊗ g).


Local Ltac test_ust g :=
  let u := unfold_tensor_stack g in
  (* idtac u. *)
  (* For compile: *)
  idtac.

test_ust f.
test_ust (f ∘ g).
test_ust (f ⊗ g).
test_ust ((f ⊗ (f ∘ g) ⊗ (f0 ∘ g0))).








Local Ltac test_show_wf f :=
  let H := fresh in 
  let wf := weak_foliate_form f in 
  assert (H: f ≃ wf) by (show_equiv_weak_foliate_form f);
  clear H.

test_show_wf f.


test_show_wf (f ∘ g).
test_show_wf (f ⊗ g).
test_show_wf ((f ∘ g) ⊗ (id_ A)).
test_show_wf ((f ⊗ id_ _) ∘ (g ⊗ h)).
test_show_wf (f ⊗ (f0 ∘ g0)).
test_show_wf (f ⊗ (id_ _ ∘ (g ⊗ h))).
test_show_wf ((f ⊗ (f ∘ g) ⊗ (f0 ∘ g0))).

test_show_wf ((f ∘ g) ⊗ (f0 ∘ g0)).
test_show_wf ((f ∘ g) ⊗ (f0)).
test_show_wf ((f ⊗ ((f ∘ g) ⊗ (f0 ∘ g0)))).
test_show_wf ((f ⊗ ((f ⊗ g) ∘ (g ⊗ id_ _)))).

test_show_wf ((f ∘ id_ _ ∘ id_ _ ∘ id_ _ ∘ id_ _) 
  ⊗ ((f ⊗ f0 ∘ g ⊗ g0) ⊗ (f0 ∘ g0 ∘ id_ _))).








Local Ltac test_merge gh :=
  (* let Mg := merge_stacked_composition_debug gh in
    idtac "merged:" Mg;
  let Mg := merge_stacked_composition gh in
    idtac "merged:" Mg. *)
  (* For compile: *)
  let Mg := merge_stacked_composition gh in
  idtac.

test_merge (mC0.(mor_tensor) f g).
test_merge (mC0.(mor_tensor) (mC0.(mor_tensor) f g) (cC.(compose) f0 g0)).



Local Ltac test_fence f :=
  (* let Nf := weak_foliate_form_debug f in 
    idtac "foliateed:" Nf. *)
  (* For compile: *)
  let Nf := weak_foliate_form f in 
  idtac. 

test_fence ((f ⊗ g ⊗ h) ∘ id_ _).
test_fence ((f ⊗ g ⊗ h) ∘ id_ _ ∘ id_ _).
test_fence ((f ⊗ g ⊗ (f0 ∘ g0)) ∘ id_ _ ∘ id_ _).
test_fence ((f ⊗ g ⊗ (f0 ∘ g0))).
test_fence ((f ⊗ (f ∘ g) ⊗ (f0 ∘ g0))).
test_fence ((f ⊗ (f ∘ g) ⊗ (f0 ∘ g0 ∘ id_ _))).
test_fence (((f ∘ id_ _ ∘ id_ _ ∘ id_ _ ∘ id_ _) 
  ⊗ (f ∘ g) ⊗ (f0 ∘ g0 ∘ id_ _))).
test_fence ((f ∘ id_ _ ∘ id_ _ ∘ id_ _ ∘ id_ _) 
  ⊗ ((f ⊗ f0 ∘ g ⊗ g0) ⊗ (f0 ∘ g0 ∘ id_ _))).



tensor_free f.
Fail tensor_free (f ⊗ g).
tensor_free (f ∘ g).

tensor_only f.
tensor_only (f ⊗ g).
Fail tensor_only (f ∘ g).
tensor_only ((g⊗h) ⊗ f ⊗ (g⊗(g⊗(g⊗h)))).
Fail tensor_only ((g⊗h) ⊗ f ⊗ (g⊗(g⊗(g⊗h ∘ id_ _)))).
(* Note this will match any tensor products, so less useful in Rig category *)
tensor_only (mC0.(mor_tensor) f (mC1.(mor_tensor) g h)).



is_weak_fenced f.
is_weak_fenced (f ∘ g).
is_weak_fenced (f ⊗ g).
Fail is_weak_fenced ((f ∘ g) ⊗ g).
is_weak_fenced ((f ⊗ g ⊗ h) ∘ id_ _).
is_weak_fenced ((f ⊗ (g ⊗ h)) ∘ id_ _).
is_weak_fenced ((f ⊗ (g ⊗ h)) ∘ (id_ _ ⊗ id_ _)).
(* We require left_associativity: *)
Fail is_weak_fenced ((f ⊗ (g ⊗ h)) ∘ (id_ _ ⊗ id_ _) ∘ id_ _).
     is_weak_fenced ((f ⊗ (g ⊗ h)) ∘ ((id_ _ ⊗ id_ _) ∘ id_ _)).
(* Note this also works over multiple tensors at once, perhaps undesirably: *)
is_weak_fenced (mC0.(mor_tensor) (mC1.(mor_tensor) g h) f).
is_weak_fenced (mC0.(mor_tensor) f (mC1.(mor_tensor) g h)).


exact Logic.I.
Qed.

End Testing.

Local Close Scope Cat_scope.

Module FutureDirections.

Local Open Scope Cat_scope.

Section CatExpr_orig.

Inductive cat_expr_o {C} `{cC : Category C}
    : forall {A B : C}, A ~> B -> Prop := 
      (* This _might_ want to be to Type instead? *)
  | expr_const {A B : C} (f : A ~> B) 
    : cat_expr_o f
  | expr_compose {A B M : C} (f : A ~> M) (g : M ~> B) 
    : cat_expr_o (f ∘ g)
  | expr_tensor {A1 A2 B1 B2 : C} {mC : @MonoidalCategory C cC} 
      (g : A1 ~> A2) (h : B1 ~> B2) 
    : cat_expr_o (g ⊗ h).
  (* Optionally, 
  | expr_cast `{ccC: CastCategory C} {A B A' B'} 
      (HA : A = A') (HB : B = B') (f : A' ~> B')
    : cat_expr (cast A B HA HB f) *)

End CatExpr_orig.

(* Dependency cycle:

Require Import RigCategory.

Section CatExpr_hierarchy.

Local Open Scope Rig_scope.

Inductive cat_expr {C} `{cC : Category C}
    : forall {A B : C}, A ~> B -> Prop := 
  | cat_id {A : C} : cat_expr (id_ A)
  | cat_const {A B : C} (f : A ~> B) 
    : cat_expr f
  | cat_compose {A B M : C} (f : A ~> M) (g : M ~> B) 
    : cat_expr (f ∘ g). 

Inductive moncat_expr {C} `{mC : MonoidalCategory C}
    : forall {A B : C}, A ~> B -> Prop :=
  | moncat_cat {A B} {f : A ~> B} 
      : cat_expr f -> moncat_expr f
  | moncat_tensor {A1 A2 B1 B2 : C} (g : A1 ~> A2) (h : B1 ~> B2) 
      : moncat_expr (g ⊗ h)
  | moncat_assoc_for {A B M : C}
      : moncat_expr (associator (A:=A) (B:=B) (M:=M)).(forward)
  | moncat_assoc_rev {A B M : C}
      : moncat_expr (associator (A:=A) (B:=B) (M:=M)).(reverse)
  (* ... and so on with left_unit, etc. *).

Inductive rigcat_expr {C} `{mC : PreDistributiveBimonoidalCategory C}
    : forall {A B : C}, A ~> B -> Prop :=
  | rigcat_cat {A B} {f : A ~> B} 
    : cat_expr f -> rigcat_expr f
  | rigcat_plus {A1 A2 B1 B2 : C} (g : A1 ~> A2) (h : B1 ~> B2) 
    : rigcat_expr (g ⊞ h)
  | rigcat_times {A1 A2 B1 B2 : C} (g : A1 ~> A2) (h : B1 ~> B2) 
    : rigcat_expr (g ⊠ h).

End CatExpr_hierarchy. *)

End FutureDirections.

