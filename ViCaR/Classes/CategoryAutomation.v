Require Export CategoryTypeclass.

Ltac assert_not_dup x := 
  (* try match goal with *)
  try match goal with
  | f := ?T : ?T', g := ?T : ?T' |- _ => tryif unify x f then fail 2 else fail 1
  end.

Ltac saturate_instances class :=
  (progress repeat (
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
    change base with catted in *) in
  try cat_fold @morphism; (* has issues, e.g., with ZX - 
    might be fixable, but likely not necessary*)
  cat_fold @compose;
  cat_fold @c_identity;
  let cid := base_fn @c_identity in
    (repeat progress (
      let H := fresh in let x := fresh in evar (x : C); 
        let x' := eval unfold x in x in 
        let cidx := eval cbn in (cid x') in 
        pose (eq_refl : cidx = cC.(c_identity) x') as H;
        erewrite H; clear x H));
  let eqbase := base_fn @equiv in
  let eqcat := catify @equiv in
  change eqbase with eqcat; (* I think this is a no-op *)
  repeat (progress match goal with
  |- eqbase ?A ?B ?f ?g 
    => change (eqbase A B f g) with (eqcat A B f g)
  end);
  try let H' := fresh in 
    enough (H':(@equiv _ _ _ _ _ _)) by (eapply H')
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
     change base with f) in
  let cat_fold f :=
    (let base := cbase_fn @f in 
    let catted := catify @f in
    change base with catted in *) in
  let mcat_fold f :=
    (let base := mbase_fn @f in 
    let catted := mcatify @f in
    change base with catted in *) in
  let tens := mbase_fn @tensor in
    let ob_base := base_fn (@obj2_map C C C cC cC cC tens) in
      change ob_base with mC.(tensor).(obj2_map);
    let mor_base := base_fn (@morphism2_map C C C cC cC cC tens) in
      change mor_base with (@morphism2_map C C C cC cC cC mC.(tensor))
      (* (@tensor C cC mC).(@morphism2_map C C C cC cC cC) *);
  mcat_fold @I;
  let lunit := mbase_fn @left_unitor in
    repeat progress (
      let H := fresh in let x := fresh in 
      evar (x : C);  (* TODO: Test this - last I tried it was uncooperative *)
      let x' := eval unfold x in x in 
      let lunitx := eval cbn in ((lunit x').(forward)) in
      pose (eq_refl : lunitx = (mC.(left_unitor) (A:=x')).(forward)) as H;
      erewrite H; clear x H);
  let runit := mbase_fn @right_unitor in 
    repeat progress (
      let H := fresh in let x := fresh in 
      evar (x : C);  (* TODO: Test this - last I tried it was uncooperative *)
      let x' := eval unfold x in x in 
      let runitx := eval cbn in ((runit x').(forward)) in
      pose (eq_refl : runitx = (mC.(right_unitor) (A:=x')).(forward)) as H;
      erewrite H; clear x H)
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
    change base with catted in *) in
  let mcat_fold f :=
    (let base := mbase_fn @f in 
    let catted := mcatify @f in
    change base with catted in *) in
  let bcat_fold f :=
    (let base := bbase_fn @f in 
    let catted := bcatify @f in
    change base with catted in *) in
  let braid := bbase_fn @braiding in
    let braidbase := constr:(ltac:(first [exact (ltac:(eval unfold braid in braid)) | exact braid])) in
    let braidforw := eval cbn in 
      (fun A B => (braidbase.(component2_iso) A B).(forward)) in
    repeat progress (let H := fresh in let y := fresh in let x := fresh in
      evar (y : C); evar (x : C); 
      let x' := eval unfold x in x in let y' := eval unfold y in y in
      let braidforwxy := eval cbn in (braidforw x' y') in
      pose (eq_refl : braidforwxy = 
        (bC.(braiding).(component2_iso) x' y').(forward)) as H;
      erewrite H; clear x y H);
    
    let braidrev := eval cbn in
      (fun A B => (braidbase.(component2_iso) A B).(reverse)) in
    repeat progress (let H := fresh in let y := fresh in let x := fresh in
      evar (y : C); evar (x : C); 
      let x' := eval unfold x in x in let y' := eval unfold y in y in
      let braidrevxy := eval cbn in (braidrev x' y') in
      pose (eq_refl : braidrevxy = 
        (bC.(braiding).(component2_iso) x' y').(reverse)) as H;
      erewrite H; clear x y H)
  end.

Ltac fold_all_braided_monoidal_categories :=
  saturate_instances BraidedMonoidalCategory;
  repeat match goal with
  | x := ?bC : BraidedMonoidalCategory ?C |- _ => 
      fold_BraidedMonoidalCategory bC; subst x
  end.

Ltac fold_CompactClosedCategory ccC :=
  match type of ccC with @CompactClosedCategory ?C ?cC ?mC ?bC ?sC =>
  let catify f := constr:(@f C cC) in
  let mcatify f := constr:(@f C cC mC) in
  let bcatify f := constr:(@f C cC mC bC) in
  let cccatify f := constr:(@f C cC mC bC sC ccC) in
  let base_fn f := 
    (let t := eval cbn in f in constr:(t)) in
  let cbase_fn f := (let raw := catify f in
    let t := eval cbn in raw in constr:(t)) in
  let mbase_fn f := (let raw := mcatify f in
    let t := eval cbn in raw in constr:(t)) in
  let bbase_fn f := (let raw := bcatify f in
    let t := eval cbn in raw in constr:(t)) in
  let ccbase_fn f := (let raw := cccatify f in
    let t := eval cbn in raw in constr:(t)) in
  let f_fold f :=
    (let base := base_fn @f in 
     change base with f) in
  let cat_fold f :=
    (let base := cbase_fn @f in 
    let catted := catify @f in
    change base with catted in *) in
  let mcat_fold f :=
    (let base := mbase_fn @f in 
    let catted := mcatify @f in
    change base with catted in *) in
  let bcat_fold f :=
    (let base := bbase_fn @f in 
    let catted := bcatify @f in
    change base with catted in *) in
  let cccat_fold f :=
    (let base := ccbase_fn @f in 
    let catted := cccatify @f in
    change base with catted in *) in
  
  let dua := ccbase_fn @dual in
    (unify dua (@id C) (*; idtac "would loop" *) ) || (
    repeat progress (
      let H := fresh in let x := fresh in 
        evar (x : C);  (* TODO: Test this - last I tried it was uncooperative *)
        let x' := eval unfold x in x in 
        let duax := eval cbn in (dua x') in
        pose (eq_refl : duax = ccC.(dual) x') as H;
        erewrite H; clear x H));
  
  cccat_fold @unit;
  cccat_fold @counit;

  let uni := ccbase_fn @unit in
    repeat progress (let H := fresh in let x := fresh in
      evar (x : C); 
      let x' := eval unfold x in x in 
      let unix := eval cbn in (uni x') in
      pose (eq_refl : unix = 
        ccC.(unit) (A:=x')) as H;
      erewrite H; clear x H);
  
  let couni := ccbase_fn @counit in
    repeat progress (let H := fresh in let x := fresh in
      evar (x : C); 
      let x' := eval unfold x in x in 
      let counix := eval cbn in (couni x') in
      pose (eq_refl : counix = 
        ccC.(counit) (A:=x')) as H;
      erewrite H; clear x H)
  end.

Ltac fold_all_compact_closed_categories :=
  saturate_instances CompactClosedCategory;
  repeat match goal with
  | x := ?ccC : CompactClosedCategory ?C |- _ => 
      fold_CompactClosedCategory ccC; subst x
  end.


Ltac fold_DaggerCategory dC :=
  match type of dC with @DaggerCategory ?C ?cC =>
  let catify f := constr:(@f C cC) in
  let dcatify f := constr:(@f C cC dC) in
  let base_fn f := 
    (let t := eval cbn in f in constr:(t)) in
  let cbase_fn f := (let raw := catify f in
    let t := eval cbn in raw in constr:(t)) in
  let dbase_fn f := (let raw := dcatify f in
    let t := eval cbn in raw in constr:(t)) in
  let f_fold f :=
    (let base := base_fn @f in 
     change base with f) in
  let cat_fold f :=
    (let base := cbase_fn @f in 
    let catted := catify @f in
    change base with catted in *) in
  let dcat_fold f :=
    (let base := dbase_fn @f in 
    let catted := dcatify @f in
    change base with catted in *) in
  
  dcat_fold @adjoint;

  let adj := dbase_fn @adjoint in
    repeat progress (let H := fresh in 
    let x := fresh in let y := fresh in
      evar (x : C); evar (y : C);
      let x' := eval unfold x in x in 
      let y' := eval unfold y in y in 
      let adjxy := eval cbn in (adj x' y') in
      pose (eq_refl : adjxy = 
        dC.(adjoint) (A:=x') (B:=y')) as H;
      erewrite H; clear x y H)
  end.

Ltac fold_all_dagger_categories :=
  saturate_instances DaggerCategory;
  repeat match goal with
  | x := ?dC : DaggerCategory ?C |- _ => 
      fold_DaggerCategory dC; subst x
  end.

Ltac to_Cat :=
  fold_all_categories; fold_all_monoidal_categories;
  fold_all_braided_monoidal_categories; 
  fold_all_compact_closed_categories;
  fold_all_dagger_categories.