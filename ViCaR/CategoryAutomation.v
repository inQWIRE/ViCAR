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
    first [
      (unify dua (@id C) (*; idtac "would loop" *) )
      | (
    repeat progress (
      let H := fresh in let x := fresh in 
        evar (x : C);  (* TODO: Test this - last I tried it was uncooperative *)
        let x' := eval unfold x in x in 
        let duax := eval cbn in (dua x') in
        pose (eq_refl : duax = ccC.(dual) x') as H;
        erewrite H; clear x H))];
  
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



(* Section on Fenceposting *)

Ltac tensor_free f :=
  try match f with
  | context[@morphism2_map _ _ _ _ _ _ (@tensor _ _ _)] => fail 2
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
    | @morphism2_map _ _ _ _ _ _ (@tensor _ _ _) _ _ _ _ ?f ?g =>
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
  | lazymatch f with (* TODO: Does lazy matter here? Pretty sure it doesn't hurt, but idk if it'd ever match more than once anyways*)
    | (?g ∘ ?h)%Cat =>  (* old: @compose _ _ _ _ _ ?g ?h *)
        compose_only g; compose_only h
    end].

(* Old:
| @compose _ _ _ _ _ ?g ?h => tensor_only g; is_weak_fenced h
| @morphism2_map _ _ _ _ _ _ (@tensor _ _ _) _ _ _ _ ?g ?h =>
    tensor_only g; tensor_only h
| _ => pseudo_const f
  *)
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
(* NOTE: This old partial implementation took a very step-like approach. I'd
   rather progress in big stes (i.e. strongly recurse) *)
Ltac weak_fencepost_form_debug_old f :=
  let rec weak_fencepost_form f :=
  match f with
  | (?g ∘ ?h)%Cat => 
      let _ := match goal with _ => tensor_only g end in (* test for tensor-only while returning constr *)
      let _ := match goal with _ => idtac "left composite" g "is tensor-only" end in
      let Nh := weak_fencepost_form h in 
      (* let _ := match goal with _ => idtac h "normalizes to" Nh end in *)
      constr:((g ∘ Nh)%Cat)
  | (?g ∘ ?h)%Cat => 
    match g with 
    | (?g' ∘ ?h')%Cat => 
      (* We _can_ do this, but we can also just recurse:
      let _ := tensor_only g' in 
      let _ := match goal with _ => idtac "associating as" g' "is tensor-only" end in
      let Ng'h := weak_fencepost_form (g' ∘ h) in *)
      (* Ditto for this... 
      let _ := match goal with _ => idtac "associating to " g' "∘ (" h' "∘" h ")" end in
      let Ng' := weak_fencepost_form g' in
      let Nh'h := weak_fencepost_form (h' ∘ h) in
      let Nf := weak_fencepost_form (Ng' ∘ Nh'h) in
      constr:(Nf)*)
      let _ := match goal with _ => idtac "associating to " g' "∘ (" h' "∘" h ")" end in
      let Nf := weak_fencepost_form (g' ∘ (h' ∘ h))%Cat in
      constr:(Nf)
    | _ => 
      let _ := match goal with _ => 
        idtac "WARNING:" g "is not tensor-only or a composition" end in
        let Nh := weak_fencepost_form h in
        constr:((g ∘ h)%Cat)
    end
  | _ => let _ := match goal with _ => tensor_only f end in 
    let _ := match goal with _ => 
      idtac f "is tensor-only" end in
    constr:(f)
  | _ => 
      let _ := match goal with _ => 
        idtac "INFO:" f "is const or unsupported" end in
      constr:(f)
  end
  in weak_fencepost_form f.



Ltac right_associate f := 
  match f with 
  | ((?g ∘ ?h) ∘ ?i)%Cat => right_associate (g ∘ (h ∘ i))%Cat
  | (?g ∘ ?h)%Cat => (* g shouldn't be a composition *)
      let RAh := right_associate h in
        constr:((g ∘ RAh)%Cat)
  | _ => constr:(f)
  end.

(* TODO: Test this! *)
Ltac left_associate f := 
  match f with 
  | (?g ∘ (?h ∘ ?i))%Cat => left_associate ((g ∘ h) ∘ i)%Cat
  | (?g ∘ ?h)%Cat => (* h shouldn't be a composition *)
      let LAg := left_associate g in
        constr:((LAg ∘ h)%Cat)
  | _ => constr:(f)
  end.

Ltac merge_stacked_composition_old g h := 
  (* g ⊗ h = (g0 ∘ (g1 ∘ ...)) ⊗ (h0 ∘ (h1 ∘ ...)) 
     ===> (g0 ⊗ h0) ∘ (g1 ⊗ h1) ∘ ...
     with id_ inserted as needed. *)
  (* In gallina: 
  match g, h with
  | ?g0 ∘ ?g1, ?h0 ∘ ?h1 => 
      let rest := merge_stacked_composition g1 h1 in
      constr:(g0 ⊗ h0 ∘ rest)
  | ?g0 ∘ ?g1, ?h0 => 
      match type of h0 with ?A ~> ?B =>
        let rest := merge_stacked_composition g1 (id_ B) in
        constr:(g0 ⊗ h0 ∘ rest)
      end
  | ?g0, ?h0 ∘ ?h1 => 
    match type of g0 with ?A ~> ?B =>
      let rest := merge_stacked_composition (id_ B) h1 in
      constr:(g0 ⊗ h0 ∘ rest)
    end
  | _, _ => constr:(g ⊗ h)
  end.*)
  (* With ltac restrictions, *)
  let rec merge_stacked_composition g h :=
  match g with
  | (?g0 ∘ ?g1)%Cat => 
    match h with 
    | (?h0 ∘ ?h1)%Cat =>
        let rest := merge_stacked_composition g1 h1 in
        constr:((g0 ⊗ h0 ∘ rest)%Cat)
    | _ => 
        match type of h with (?A ~> ?B)%Cat =>
          let rest := merge_stacked_composition g1 (id_ B) in
          constr:((g0 ⊗ h ∘ rest)%Cat)
        end
    end
  | _ => 
    match h with 
    | (?h0 ∘ ?h1)%Cat =>
        match type of g with (?A ~> ?B)%Cat =>
          let rest := merge_stacked_composition (id_ B) h1 in
          constr:((g ⊗ h0 ∘ rest)%Cat)
        end
    | _ => 
        constr:((g ⊗ h)%Cat)
    end
  end
  in merge_stacked_composition g h. 



Ltac merge_stacked_composition_debug gh := 
  let rec merge_stacked_composition gh :=
  match type of gh with @morphism ?C ?cC _ _ =>
  match gh with
    @morphism2_map C _ _ cC _ _ (@tensor C cC ?mC) ?gA ?gB ?hA ?hB ?g ?h =>
  lazymatch g with
  | (?g0 ∘ ?g1)%Cat => 
    let _ := match goal with _ => 
      idtac "found decomp of first as" g0 "∘" g1 end in
    lazymatch h with 
    | (?h0 ∘ ?h1)%Cat =>
        let _ := match goal with _ => 
          idtac "found decomp of second as" h0 "∘" h1 end in
        let rest := merge_stacked_composition (mC.(tensor) @@ g1, h1) in
        let _ := match goal with _ => 
          idtac "remaining terms became" rest end in
        let res := constr:(cC.(compose) (mC.(tensor) @@ g0, h0) rest) in
        let _ := match goal with _ => 
          idtac "    which combined to" res end in
        constr:(res)
    | _ => 
        let _ := match goal with _ => 
          idtac "found second to be atomic:" h end in
        match type of h with @morphism _ _ ?A ?B =>
          let _ := match goal with _ => 
            idtac "resolved second as type" hA "~>" hB end in
          let rest := merge_stacked_composition (mC.(tensor) @@ g1, (cC.(c_identity) hB)) in
          let _ := match goal with _ => 
            idtac "remaining terms became" rest end in
          let res := constr:(cC.(compose) (mC.(tensor) @@ g0, h) rest) in
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
          let rest := merge_stacked_composition (mC.(tensor) @@ (cC.(c_identity) gB), h1) in
          let _ := match goal with _ => 
            idtac "remaining terms became" rest end in
          let res := constr:(cC.(compose) (mC.(tensor) @@ g, h0) rest) in
          let _ := match goal with _ => 
            idtac "    which combined to" res end in
          constr:(res)
        end
    | _ => 
        let _ := match goal with _ => 
          idtac "found second to be atomic as well:" h end in
        constr:(mC.(tensor) @@ g, h)
    end
  end
  end end
  in merge_stacked_composition gh. 

Ltac merge_stacked_composition gh := 
  let rec merge_stacked_composition gh :=
  match type of gh with @morphism ?C ?cC _ _ =>
  match gh with
    @morphism2_map C _ _ cC _ _ (@tensor C cC ?mC) ?gA ?gB ?hA ?hB ?g ?h =>
  lazymatch g with
  | (?g0 ∘ ?g1)%Cat => 
    lazymatch h with 
    | (?h0 ∘ ?h1)%Cat =>
        let rest := merge_stacked_composition (mC.(tensor) @@ g1, h1) in
        constr:(cC.(compose) (mC.(tensor) @@ g0, h0) rest)
    | _ => 
        let rest :=
          merge_stacked_composition 
            (mC.(tensor) @@ g1, (cC.(c_identity) hB)) in
        constr:(cC.(compose) (mC.(tensor) @@ g0, h) rest)
    end
  | _ => 
    lazymatch h with 
    | (?h0 ∘ ?h1)%Cat =>
        let rest := 
          merge_stacked_composition
            (mC.(tensor) @@ (cC.(c_identity) gB), h1) in
        constr:(cC.(compose) (mC.(tensor) @@ g, h0) rest)
    | _ => 
        constr:(mC.(tensor) @@ g, h)
    end
  end
  end end
  in merge_stacked_composition gh. 

Ltac weak_fencepost_form_debug f :=
  let rec weak_fencepost f :=
  match f with
  | @compose ?C ?cC _ _ _ ?g ?h => 
      let _ := match goal with _ => 
        idtac "splitting on ∘ into" g "and" h "..." end in
      let Ng := weak_fencepost g in
      let Nh := weak_fencepost h in 
      let _ := match goal with _ => 
        idtac "... getting" g "∘" h "into" end in
      let res := right_associate (cC.(compose) Ng Nh) in
      let _ := match goal with _ => 
        idtac "    " res end in
      constr:(res)
  | @morphism2_map ?C _ _ ?cC _ _ (@tensor ?C ?cC ?mC) _ _ _ _ ?g ?h =>
      let _ := match goal with _ => 
        idtac "splitting on ⊗ into" g "and" h "..." end in
      let Ng := weak_fencepost g in
      let Nh := weak_fencepost h in 
      let _ := match goal with _ => 
        idtac "... getting" g "⊗" h "into" end in
      let res := merge_stacked_composition (mC.(tensor) @@ Ng, Nh) in
      let _ := match goal with _ => 
        idtac "    " res end in
      constr:(res)
  | _ => 
      let _ := match goal with _ => 
        idtac "INFO:" f "is const or unsupported" end in
      constr:(f)
  end
  in weak_fencepost f.

Ltac weak_fencepost_form f :=
  let rec weak_fencepost f :=
  match f with
  | @compose ?C ?cC _ _ _ ?g ?h => 
      let Ng := weak_fencepost g in
      let Nh := weak_fencepost h in 
      right_associate (cC.(compose) Ng Nh)
  | @morphism2_map ?C _ _ ?cC _ _ (@tensor ?C ?cC ?mC) _ _ _ _ ?g ?h =>
      let Ng := weak_fencepost g in
      let Nh := weak_fencepost h in 
      merge_stacked_composition (mC.(tensor) @@ Ng, Nh)
  | _ => (* f "is const or unsupported" *)
      constr:(f)
  end
  in weak_fencepost f.

Local Open Scope Cat_scope.
Lemma assoc_compat_helper {C} `{Category C} {A B M N : C} :
  forall (f : A ~> B) (g : B ~> M) (h : M ~> N) (fgh : A ~> N),
  f ∘ (g ∘ h) ≃ fgh -> (f ∘ g) ∘ h ≃ fgh.
Proof.
  intros; rewrite assoc; easy.
Qed.

Lemma compose_compat_right {C} `{Category C} {A B M : C} :
  forall (f : A ~> B) (g g' : B ~> M),
  g ≃ g' -> f ∘ g ≃ f ∘ g'.
Proof.
  intros.
  apply compose_compat; easy.
Qed.

Lemma stack_compose_distr_compat {C} `{MonoidalCategory C}
{A B M A' B' M': C} :
  forall (f : A ~> B) (g : B ~> M) (h : A' ~> B') (i : B' ~> M')
  (gi : B × B' ~> M × M'),
  g ⊗ i ≃ gi -> (f ∘ g) ⊗ (h ∘ i) ≃ f ⊗ h ∘ gi.
Proof.
  intros.
  rewrite compose2_map.
  apply compose_compat; easy.
Qed.

Lemma stack_distr_pushout_r_top_compat {C} `{MonoidalCategory C}
  {a b m n o} : forall (f : a ~> b) (g : m ~> n) (h : n ~> o)
  (ih : b × n ~> b × o),
  id_ b ⊗ h ≃ ih -> f ⊗ (g ∘ h) ≃ f ⊗ g ∘ ih.
Proof.
  intros.
  (* `rewrite stack_distr_pushout_r_top.` is replaced here manually 
  to simplify dependencies *)
  rewrite <- (right_unit (f:=f)) at 1.
  rewrite compose2_map.
  apply compose_compat; easy.
Qed.

Lemma stack_distr_pushout_r_bot_compat {C} `{MonoidalCategory C}
  {a b c n o : C} : forall (f : a ~> b) (g : b ~> c) (h : n ~> o)
  (gi : b × o ~> c × o),
  g ⊗ id_ o ≃ gi -> (f ∘ g) ⊗ h ≃ f ⊗ h ∘ gi.
Proof.
  intros.
  (* `rewrite stack_distr_pushout_r_bot.` is replaced here manually 
  to simplify dependencies *)
  rewrite <- (right_unit (f:=h)) at 1.
  rewrite compose2_map.
  apply compose_compat; easy.
Qed.

Lemma compose_compat_trans_helper {C} `{cC:Category C} {A B M : C} : forall
  (f f' : A ~> B) (g g' : B ~> M) (fg : A ~> M),
  f ≃ f' -> g ≃ g' -> f' ∘ g' ≃ fg -> f ∘ g ≃ fg.
Proof.
  intros.
  transitivity (f' ∘ g'); [|easy].
  apply compose_compat; easy.
Qed.

Lemma stack_compat_trans_helper {C} `{mC : MonoidalCategory C} {A A' B B' : C} : 
  forall (f f' : A ~> A') (g g' : B ~> B') (fg : A × B ~> A' × B'),
  f ≃ f' -> g ≃ g' -> f' ⊗ g' ≃ fg -> f ⊗ g ≃ fg.
Proof.
  intros.
  transitivity (f' ⊗ g'); [|easy].
  apply morphism2_compat; easy.
Qed.

Lemma show_equiv_stack_comp_id_bot_helper {C} `{MonoidalCategory C} 
  {A M A' B : C} : forall (g : A ~> M) (gs : M ~> A') (gsB : M × B ~> A' × B),
  gs ⊗ id_ B ≃ gsB -> (g ∘ gs) ⊗ id_ B ≃ g ⊗ id_ B ∘ gsB.
Proof.
  intros.
  rewrite <- (right_unit (f:=id_ B)) at 1.
  rewrite compose2_map.
  apply compose_compat; easy.
Qed.

Lemma show_equiv_stack_comp_id_top_helper {C} `{MonoidalCategory C} 
  {A B M B' : C} : forall (g : B ~> M) (gs : M ~> B') (Ags : A × M ~> A × B'),
  id_ A ⊗ gs ≃ Ags -> id_ A ⊗ (g ∘ gs) ≃ id_ A ⊗ g ∘ Ags.
Proof.
  intros.
  rewrite <- (right_unit (f:=id_ A)) at 1.
  rewrite compose2_map.
  apply compose_compat; easy.
Qed.

Lemma show_equiv_unfold_tensor_stack_helper {C} `{MonoidalCategory C} 
  {fA fB gA gB : C} (f uf : fA ~> fB) (g ug : gA ~> gB) 
  (ufs : fA × gA ~> fB × gA) (ugs : fB × gA ~> fB × gB) :
  f ≃ uf -> g ≃ ug -> 
  uf ⊗ id_ gA ≃ ufs -> id_ fB ⊗ ug ≃ ugs ->
  f ⊗ g ≃ ufs ∘ ugs.
Proof.
  intros Hf Hg Huf Hug.
  rewrite Hf, Hg.
  rewrite <- (right_unit (f:=uf)), <- (left_unit (f:=ug)), compose2_map.
  apply compose_compat; easy.
Qed.

Close Scope Cat_scope.


(* Shows the goal f ≃ right_associate f by mirroring the code
   path of right_associate with `apply`s. *)
Ltac show_equiv_right_associate f :=
  let rec show_equiv_right_associate f :=
  match f with 
  | ((?g ∘ ?h) ∘ ?i)%Cat => 
    (* RHS is `right_associate (g ∘ (h ∘ i))` *)
    apply assoc_compat_helper;
    show_equiv_right_associate ((g ∘ (h ∘ i))%Cat)
  | (?g ∘ ?h)%Cat => (* g shouldn't be a composition *)
      (* RHS is `(g ∘ right_associate h)` *)
      apply compose_compat_right;
      show_equiv_right_associate h
  | _ => 
    (* RHS is `constr:(f)` *)
    reflexivity
  end
  in show_equiv_right_associate f.

(* Shows the goal f ≃ merge_stack_composition f by mirroring the 
   code path of merge_stacked_composition with `apply`s. *)
Ltac show_equiv_merge_stacked_composition gh := 
  let rec show_equiv_merge_stacked_composition gh :=
  match type of gh with @morphism ?C ?cC _ _ =>
  match gh with
    @morphism2_map C _ _ cC _ _ (@tensor C cC ?mC) ?gA ?gB ?hA ?hB ?g ?h =>
  lazymatch g with
  | (?g0 ∘ ?g1)%Cat => 
    lazymatch h with 
    | (?h0 ∘ ?h1)%Cat =>
        (* RHS is g0 ⊗ h0 ∘ merge_stacked_composition (g1 ⊗ h1) *)
        apply stack_compose_distr_compat;
        show_equiv_merge_stacked_composition (mC.(tensor) @@ g1, h1)
    | _ => 
        (* RHS is g0 ⊗ h0 ∘ merge_stacked_composition (g1 ⊗ id_ hB) *)
        apply stack_distr_pushout_r_bot_compat;
        show_equiv_merge_stacked_composition (mC.(tensor) @@ g1, (cC.(c_identity) hB))
    end
  | _ => 
    lazymatch h with 
    | (?h0 ∘ ?h1)%Cat =>
        (* RHS is g0 ⊗ h0 ∘ merge_stacked_composition (id_ gB ⊗ h1) *)
        apply stack_distr_pushout_r_top_compat;
        show_equiv_merge_stacked_composition (mC.(tensor) @@ (cC.(c_identity) gB), h1)
    | _ => 
        (* RHS is g ⊗ h *)
        reflexivity
    end
  end
  end end
  in show_equiv_merge_stacked_composition gh. 

(* Shows the goal f ≃ weak_fencepost_form f by mirroring the code
   path of weak_fencepost_form with `apply`s. *)
Ltac show_equiv_weak_fencepost_form f :=
  let weak_fencepost := weak_fencepost_form in 
  let rec show_equiv_weak_fencepost_form f :=
  match f with
  | @compose ?C ?cC _ _ _ ?g ?h => 
      let Ng := weak_fencepost g in
      let Nh := weak_fencepost h in 
      let res := right_associate (cC.(compose) Ng Nh) in
      apply (compose_compat_trans_helper (cC:=cC) g Ng h Nh res 
        ltac:(show_equiv_weak_fencepost_form g)
        ltac:(show_equiv_weak_fencepost_form h)
        ltac:(show_equiv_right_associate (cC.(compose) Ng Nh)))
  | @morphism2_map ?C _ _ ?cC _ _ (@tensor ?C ?cC ?mC) _ _ _ _ ?g ?h =>
      let Ng := weak_fencepost g in
      let Nh := weak_fencepost h in 
      let res := merge_stacked_composition (mC.(tensor) @@ Ng, Nh) in
      apply (stack_compat_trans_helper (cC:=cC) g Ng h Nh res 
        ltac:(show_equiv_weak_fencepost_form g)
        ltac:(show_equiv_weak_fencepost_form h)
        ltac:(show_equiv_merge_stacked_composition (mC.(tensor) @@ Ng, Nh)))
  | _ => (* f "is const or unsupported" *)
      (* constr:(f) *)
      reflexivity
  end
  in show_equiv_weak_fencepost_form f.

(* TODO: Generalize these to fold_compose base *)
(* If f = f0 ∘ (f1 ∘ (...)), this gives f0 ⊗ id_ B ∘ (f1 ⊗ id_ B ∘ (...))
   in the given monoidal category mC. *)
Ltac stack_comp_id_bot f B mC :=
  let base g :=
    constr:(mC.(tensor) @@ g, id_ B) in
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
    constr:(mC.(tensor) @@ id_ A, g) in
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
  | @morphism2_map _ _ _ _ _ _ (@tensor _ _ ?mC) ?gA ?gB ?hA ?hB ?g ?h =>
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
  | @morphism2_map _ _ _ _ _ _ (@tensor _ ?cC ?mC) 
    ?gA ?gA ?hA ?hA (id_ ?gA)%Cat (id_ ?hA) => 
      constr:(cC.(c_identity) (mC.(tensor) gA hA))
  
  | @morphism2_map _ _ _ _ _ _ (@tensor _ _ ?mC) ?gA ?gA ?hA ?hB (id_ ?gA)%Cat ?h => 
      let uh := unfold_tensor_stack h in 
      let sh := stack_comp_id_top uh gA mC in
      constr:(sh)
      
  | @morphism2_map _ _ _ _ _ _ (@tensor _ _ ?mC) ?gA ?gB ?hA ?hA ?g (id_ ?hA)%Cat => 
      let ug := unfold_tensor_stack g in 
      let sg := stack_comp_id_bot ug hA mC in
      constr:(sg)

  | @morphism2_map _ _ _ _ _ _ (@tensor _ _ ?mC) ?gA ?gB ?hA ?hB ?g ?h =>
      let ug := unfold_tensor_stack g in 
      let uh := unfold_tensor_stack h in 
      let sg := stack_comp_id_bot ug hA mC in
      let sh := stack_comp_id_top uh gB mC in
      constr:((sg ∘ sh)%Cat)
  | _ => constr:(f)
  end
  in unfold_tensor_stack f.

(* Returns the strong fencepost term of a weakly fenceposted term 
   (in fact, not even requiring the term be right-associated, though
    the resulting fencepost will be. )*)
Ltac strong_fencepost_form_of_weak f :=
  let rec strong_fence f :=
  lazymatch f with
  | (?g ∘ ?h)%Cat => 
      let ug := strong_fence g in
      let uh := strong_fence h in
      right_associate (ug ∘ uh)%Cat
  | _ => 
      unfold_tensor_stack f
  end
  in strong_fence f.

(* Additionally avoids taking id ⊗ id to id ⊗ id ∘ id ⊗ id and similar *)
Ltac strong_fencepost_form_of_weak_no_id f :=
  let rec strong_fence f :=
  lazymatch f with
  | (?g ∘ ?h)%Cat => 
      let ug := strong_fence g in
      let uh := strong_fence h in
      right_associate (ug ∘ uh)%Cat
  | _ => 
      unfold_tensor_stack_no_id f
  end
  in strong_fence f.


Ltac show_equiv_stack_comp_id_bot f B mC :=
  let base g :=
    constr:(mC.(tensor) @@ g, id_ B) in
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
    constr:(mC.(tensor) @@ id_ A, g) in
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
  | @morphism2_map _ _ _ _ _ _ (@tensor _ ?cC ?mC) ?gA ?gB ?hA ?hB ?g ?h =>
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
  | @morphism2_map _ _ _ _ _ _ (@tensor _ _ ?mC) 
    ?gA ?gA ?hA ?hA (id_ ?gA)%Cat (id_ ?hA) => 
      (* constr:(cC.(c_identity) (mC.(tensor) gA hA)) *)
      apply (mC.(tensor).(id2_map) (A1:=gA) (A2:=hA))
  
  | @morphism2_map _ _ _ _ _ _ (@tensor _ ?cC ?mC) ?gA ?gA ?hA ?hB (id_ ?gA)%Cat ?h => 
      let uh := unfold_tensor_stack h in 
      let sh := stack_comp_id_top uh gA mC in   (* constr:(sh) *)
      apply (stack_compat_trans_helper
        (cC.(c_identity) gA) (cC.(c_identity) gA) h uh sh
        ltac:(reflexivity) ltac:(show_unfold h)
        ltac:(show_equiv_stack_comp_id_top h gA mC))
      
  | @morphism2_map _ _ _ _ _ _ (@tensor _ ?cC ?mC) ?gA ?gB ?hA ?hA ?g (id_ ?hA)%Cat => 
      let ug := unfold_tensor_stack g in 
      let sg := stack_comp_id_bot ug hA mC in   (* constr:(sg) *)
      apply (stack_compat_trans_helper
        g ug (cC.(c_identity) hA) (cC.(c_identity) hA) sg
        ltac:(show_unfold g) ltac:(reflexivity)
        ltac:(show_equiv_stack_comp_id_bot g hA mC))

  | @morphism2_map _ _ _ _ _ _ (@tensor _ _ ?mC) ?gA ?gB ?hA ?hB ?g ?h =>
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
  | @morphism2_map _ _ _ _ _ _ (@tensor _ _ ?mC) ?gA _ ?hA _ (id_ ?gA)%Cat (id_ ?hA) => 
      idtac "id id case:"; print_state;
      (* constr:(cC.(c_identity) (mC.(tensor) gA hA)) *)
      apply (mC.(tensor).(id2_map) (A1:=gA) (A2:=hA))
  
  | @morphism2_map _ _ _ _ _ _ (@tensor _ ?cC ?mC) ?gA ?gA ?hA ?hB (id_ ?gA)%Cat ?h => 
      let uh := unfold_tensor_stack h in 
      let sh := stack_comp_id_top uh gA mC in   (* constr:(sh) *)
      idtac "left id case:"; print_state;
      apply (stack_compat_trans_helper
        (cC.(c_identity) gA) (cC.(c_identity) gA) h uh sh
        ltac:(reflexivity) ltac:(show_unfold h)
        ltac:(show_equiv_stack_comp_id_top h gA mC))
      
  | @morphism2_map _ _ _ _ _ _ (@tensor _ ?cC ?mC) ?gA ?gB ?hA ?hA ?g (id_ ?hA)%Cat => 
      let ug := unfold_tensor_stack g in 
      let sg := stack_comp_id_bot ug hA mC in   (* constr:(sg) *)
      idtac "right id case:"; print_state;
      apply (stack_compat_trans_helper
        g ug (cC.(c_identity) hA) (cC.(c_identity) hA) sg
        ltac:(show_unfold g) ltac:(reflexivity)
        ltac:(show_equiv_stack_comp_id_bot g hA mC))

  | @morphism2_map _ _ _ _ _ _ (@tensor _ _ ?mC) ?gA ?gB ?hA ?hB ?g ?h =>
      let ug := unfold_tensor_stack g in let uh := unfold_tensor_stack h in 
      let sg := stack_comp_id_bot ug hA mC in
      let sh := stack_comp_id_top uh gB mC in
      idtac "true compose case:"; print_state;
      apply (show_equiv_unfold_tensor_stack_helper
        g ug h uh sg sh   ltac:(show_unfold g) ltac:(show_unfold h)
        ltac:(show_equiv_stack_comp_id_bot ug hA mC)
        ltac:(show_equiv_stack_comp_id_top uh gB mC)
      )
  | _ => (* constr:(f) *) reflexivity
  end
  in show_unfold f.


Ltac show_equiv_strong_fencepost_form_of_weak f :=
  let strong_fence := strong_fencepost_form_of_weak in
  let rec show_strong_fence f :=
  lazymatch f with
  | (?g ∘ ?h)%Cat => 
      let ug := strong_fence g in
      let uh := strong_fence h in
      let rassoc := right_associate (ug ∘ uh)%Cat in
      (* right_associate (ug ∘ uh)%Cat *)
      apply (compose_compat_trans_helper
        g ug  h uh rassoc
        ltac:(show_strong_fence g)
        ltac:(show_strong_fence h)
        ltac:(show_equiv_right_associate (ug ∘ uh)%Cat)
      )
  | _ => 
      (* unfold_tensor_stack f *)
      show_equiv_unfold_tensor_stack f
  end
  in show_strong_fence f.


Ltac show_equiv_strong_fencepost_form_of_weak_no_id f :=
  let strong_fence := strong_fencepost_form_of_weak_no_id in
  let rec show_strong_fence f :=
  lazymatch f with
  | (?g ∘ ?h)%Cat => 
      let ug := strong_fence g in
      let uh := strong_fence h in
      let rassoc := right_associate (ug ∘ uh)%Cat in
      (* right_associate (ug ∘ uh)%Cat *)
      apply (compose_compat_trans_helper
        g ug  h uh rassoc
        ltac:(show_strong_fence g)
        ltac:(show_strong_fence h)
        ltac:(show_equiv_right_associate (ug ∘ uh)%Cat)
      )
  | _ => 
      (* unfold_tensor_stack f *)
      show_equiv_unfold_tensor_stack_no_id f
  end
  in show_strong_fence f.

Ltac show_equiv_strong_fencepost_form_of_weak_no_id_debug f :=
  let strong_fence := strong_fencepost_form_of_weak_no_id in
  let rec show_strong_fence f :=
  lazymatch f with
  | (?g ∘ ?h)%Cat => 
      let ug := strong_fence g in
      let uh := strong_fence h in
      let rassoc := right_associate (ug ∘ uh)%Cat in
      (* right_associate (ug ∘ uh)%Cat *)
      apply (compose_compat_trans_helper
        g ug  h uh rassoc
        ltac:(show_strong_fence g)
        ltac:(show_strong_fence h)
        ltac:(show_equiv_right_associate (ug ∘ uh)%Cat)
      )
  | _ => 
      (* unfold_tensor_stack f *)
      show_equiv_unfold_tensor_stack_no_id_debug f
  end
  in show_strong_fence f.

Ltac weak_fencepost f :=
  let wf := weak_fencepost_form f in
  let H := fresh in 
  assert (H: (f ≃ wf)%Cat) by (show_equiv_weak_fencepost_form f);
  setoid_rewrite H;
  clear H.

Ltac strong_fencepost f :=
  let wf := weak_fencepost_form f in
  let sf := strong_fencepost_form_of_weak wf in
  let H := fresh in 
  assert (H: (f ≃ sf)%Cat) by (
    transitivity wf;
    [ show_equiv_weak_fencepost_form f 
    | show_equiv_strong_fencepost_form_of_weak wf]);
  setoid_rewrite H;
  clear H.

Ltac strong_fencepost_no_id f :=
  let wf := weak_fencepost_form f in
  let sf := strong_fencepost_form_of_weak_no_id wf in
  let H := fresh in 
  assert (H: (f ≃ sf)%Cat) by (
    transitivity wf;
    [ show_equiv_weak_fencepost_form f 
    | show_equiv_strong_fencepost_form_of_weak_no_id wf]);
  setoid_rewrite H;
  clear H.

Ltac strong_fencepost_no_id_debug f :=
  let wf := weak_fencepost_form f in
  let sf := strong_fencepost_form_of_weak_no_id wf in
  let H := fresh in 
  assert (H: (f ≃ sf)%Cat) by (
    transitivity wf;
    [ show_equiv_weak_fencepost_form f 
    | show_equiv_strong_fencepost_form_of_weak_no_id_debug wf]);
  setoid_rewrite H;
  clear H.

Section Testing.
Local Open Scope Cat_scope.
Variables (C : Type) (cC cC' cC'' : Category C)
  (mC0   mC1   : @MonoidalCategory C cC)
  (mC0'  mC1'  : @MonoidalCategory C cC')
  (mC0'' mC1'' : @MonoidalCategory C cC'')
  (A B M N : C)
  (f   f0   : cC.(morphism)   A B) 
  (g   g0   : cC.(morphism)   B M) 
  (h   h0   : cC.(morphism)   A M)
  (i   i0   : cC.(morphism)   M N)
  (j   j0   : cC.(morphism)   B M)
  (k   k0   : cC.(morphism)   A M)
  (f'  f0'  : cC'.(morphism)  A B) 
  (g'  g0'  : cC'.(morphism)  B M) 
  (h'  h0'  : cC'.(morphism)  A M)
  (i'  i0'  : cC'.(morphism)  M N)
  (j'  j0'  : cC'.(morphism)  B M)
  (k'  k0'  : cC'.(morphism)  A M)
  (f'' f0'' : cC''.(morphism) A B) 
  (g'' g0'' : cC''.(morphism) B M) 
  (h'' h0'' : cC''.(morphism) A M)
  (i'' i0'' : cC''.(morphism) M N)
  (j'' j0'' : cC''.(morphism) B M)
  (k'' k0'' : cC''.(morphism) A M).
(* Goal True. *)

Existing Instance cC.
Existing Instance cC'.
Existing Instance cC''.
Existing Instance mC0.   Existing Instance mC1.
Existing Instance mC0'.  Existing Instance mC1'.
Existing Instance mC0''. Existing Instance mC1''.

Lemma test_weak_fencepost : forall {C : Type}
  `{Cat : Category C} `{MonCat : MonoidalCategory C}
  {a b m n o} (f : a ~> b) (g : m ~> n) (h : n ~> o),
  f ⊗ (g ∘ h) ≃ f ⊗ g ∘ (id_ b ⊗ h).
Proof.
  intros.
  match goal with
  |- ?T ≃ _ => weak_fencepost T
  end.
  easy.
Qed.

Lemma test_strong_fencepost : forall {C : Type}
  `{Cat : Category C} `{MonCat : MonoidalCategory C}
  {a b m n o} (f : a ~> b) (g : m ~> n) (h : n ~> o),
  f ⊗ (g ∘ h) ≃ f ⊗ g ∘ (id_ b ⊗ h).
Proof.
  intros.
  match goal with
  |- ?T ≃ ?T' => strong_fencepost T; strong_fencepost T'
  end.
  easy.
Qed.

Lemma test_strong_fencepost_no_id_1 : forall {C : Type}
  `{Cat : Category C} `{MonCat : MonoidalCategory C}
  {a b m n o} (f : a ~> b) (g : m ~> n) (h : n ~> o),
  f ⊗ (g ∘ h) ≃ f ⊗ g ∘ (id_ b ⊗ h).
Proof.
  intros.
  match goal with
  |- ?T ≃ ?T' => strong_fencepost_no_id T; strong_fencepost_no_id T'
  end.
  easy.
Qed.

(* Lemma test_strong_fencepost_no_id_2 : forall {C : Type}
  `{Cat : Category C} `{MonCat : MonoidalCategory C}
  {a b m n o} (f : a ~> b) (g : m ~> n) (h : n ~> o),
  f ⊗ (g ∘ h ∘ id_ _) ⊗ (id_ a ⊗ id_ b) ≃ 
  f ⊗ g ⊗ (id_ a ⊗ id_ b) ∘ ((id_ b ⊗ h) ⊗ (id_ a ⊗ id_ b)).
Proof.
  intros.
  match goal with
  |- ?T ≃ ?T' => strong_fencepost_no_id_debug T
  (* ; strong_fencepost_no_id T' *)
  end.
  easy.
Qed. *)

Goal True.


Local Ltac test_show_unfold_no_id_of_wf f :=
  let wf := weak_fencepost_form f in
  let sf := unfold_tensor_stack_no_id wf in
  (* idtac sf; *)
  let H := fresh in 
  assert (H : wf ≃ sf) by (show_equiv_unfold_tensor_stack_no_id wf);
  clear H.

test_show_unfold_no_id_of_wf (f ⊗ (f0 ∘ g0 ∘ id_ _) ⊗ (id_ A ⊗ id_ B)).




Local Ltac test_show_unfold_no_id f :=
  let sf := unfold_tensor_stack_no_id f in
  (* idtac sf; *)
  let H := fresh in 
  assert (H : f ≃ sf) by (show_equiv_unfold_tensor_stack_no_id f; print_state);
  clear H.

test_show_unfold_no_id ((id_ B ⊗ id_ M ⊗ id_ (A × B))).
test_show_unfold_no_id (f ⊗ (f0 ∘ g0 ∘ id_ _) ⊗ (id_ A ⊗ id_ B)).
test_show_unfold_no_id (f ⊗ f0 ⊗ (id_ A ⊗ id_ B)).
test_show_unfold_no_id (id_ B ⊗ g0 ⊗ id_ (A × B)).



Local Ltac test_show_st_of_wk f :=
  let wf := weak_fencepost_form f in
  let sf := strong_fencepost_form_of_weak wf in
  let H := fresh in 
  assert (H: wf ≃ sf) by (show_equiv_strong_fencepost_form_of_weak wf);
  clear H.

test_show_st_of_wk f.
test_show_st_of_wk (f ∘ g).
test_show_st_of_wk (f ⊗ g).

test_show_st_of_wk (f ⊗ (f ∘ g)).
test_show_st_of_wk ((f ⊗ ((f ∘ g) ⊗ (f0 ∘ g0)))).




Local Ltac test_show_unfold f :=
  let sf := unfold_tensor_stack f in
  let H := fresh in 
  assert (H : f ≃ sf) by (show_equiv_unfold_tensor_stack f);
  clear H.

test_show_unfold f.
test_show_unfold (f ∘ g).
test_show_unfold (f ⊗ g).

test_show_unfold ((f ⊗ (f ∘ g) ⊗ (f0 ∘ g0))).

test_show_unfold ((f ∘ g) ⊗ (f0 ∘ g0)).
test_show_unfold ((f ∘ g) ⊗ (f0)).
test_show_unfold ((f ⊗ ((f ∘ g) ⊗ (f0 ∘ g0)))).



Local Ltac test_show_st_bot f B mC :=
  let sf := stack_comp_id_bot f B mC in
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
test_show_st_top_bot ((f ⊗ g) ∘ (g ⊗ i)) B mC0.


Local Ltac test_st_of_wk f :=
  let wf := weak_fencepost_form f in
  let sf := strong_fencepost_form_of_weak wf in
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
  let wf := weak_fencepost_form f in 
  assert (H: f ≃ wf) by (show_equiv_weak_fencepost_form f);
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
  ⊗ ((f ⊗ f0) ∘ (g ⊗ g0) ⊗ (f0 ∘ g0 ∘ id_ _))).








Local Ltac test_merge gh :=
  (* let Mg := merge_stacked_composition_debug gh in
    idtac "merged:" Mg;
  let Mg := merge_stacked_composition gh in
    idtac "merged:" Mg. *)
  (* For compile: *)
  let Mg := merge_stacked_composition gh in
  idtac.

test_merge (mC0.(tensor) @@ f, g).
test_merge (mC0.(tensor) @@ (mC0.(tensor) @@ f, g), (cC.(compose) f0 g0)).



Local Ltac test_fence f :=
  (* let Nf := weak_fencepost_form_debug f in 
    idtac "fenceposted:" Nf. *)
  (* For compile: *)
  let Nf := weak_fencepost_form f in 
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
  ⊗ ((f ⊗ f0) ∘ (g ⊗ g0) ⊗ (f0 ∘ g0 ∘ id_ _))).



tensor_free f.
Fail tensor_free (f ⊗ g).
tensor_free (f ∘ g).

tensor_only f.
tensor_only (f ⊗ g).
Fail tensor_only (f ∘ g).
tensor_only ((g⊗h) ⊗ f ⊗ (g⊗(g⊗(g⊗h)))).
Fail tensor_only ((g⊗h) ⊗ f ⊗ (g⊗(g⊗(g⊗h ∘ id_ _)))).
(* Note this will match any tensor products, so less useful in Rig category *)
tensor_only (mC0.(tensor) @@ f, (mC1.(tensor) @@ g, h)).



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
is_weak_fenced (mC0.(tensor) @@ (mC1.(tensor) @@ g, h), f).
is_weak_fenced (mC0.(tensor) @@ f, (mC1.(tensor) @@ g, h)).


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

End CatExpr_hierarchy.

End FutureDirections.

