Require Import Setoid.
Require MCprocessing.

Section monarr_under_over.

Open Scope bw_scope.

Set Universe Polymorphism.

Import MCDefinitions MCClasses MC_setoids
  MC_notations UIP_facts MCbw 
  MCconsequences MCmonarrlist 
  MCproperop MCprocessing.
Import CategoryTypeclass.
Import List ListNotations.

(* Polymorphic  *)Context {X : Type} {UIPX : UIP X}.
(* Polymorphic  *)Context {cC : Category X} {cCh : CategoryCoherence cC} 
  {mC : MonoidalCategory cC} {mCh : MonoidalCategoryCoherence mC}.

Local Notation bw := (bw X).
Local Notation "a ⟶ b" := (@monarr X cC mC a b) (at level 60).

Definition realize_equiv (a b : bw) (f g : a ⟶ b) :=
  (realize_monarr f ≃ realize_monarr g)%Cat.

Arguments realize_equiv _ _ _ _/.

Definition realize_equiv' := @realize_equiv.

Global Arguments realize_equiv' _ _ _ _ : simpl never.

Local Notation "f '≡' g" := (realize_equiv' _ _ f g) (at level 70) : bw_scope.

#[global] Add Parametric Relation (a b : bw) : (monarr a b) (realize_equiv' a b)
  reflexivity proved by 
    ltac:(intros ?; unfold realize_equiv'; simpl; reflexivity)
  symmetry proved by 
    ltac:(unfold realize_equiv'; intros ?; simpl; symmetry; easy)
  transitivity proved by 
    ltac:(unfold realize_equiv'; intros ?; simpl; etransitivity; eauto) 
    as realize_equiv_setoid.

#[program] Instance realize_equiv_subrel {x y} : 
  subrelation (monarrequiv x y) (realize_equiv' x y).
Next Obligation.
  unfold realize_equiv'; simpl.
  rewrite H.
  reflexivity.
Qed.

#[global] Add Parametric Morphism (a b c : bw) : (@monarrcomp X cC mC a b c)
  with signature 
  (realize_equiv' a b) ==> (realize_equiv' b c) ==> (realize_equiv' a c)
  as monarrcomp_mor_real.
Proof. intros; apply compose_compat; easy. Qed.

#[global] Add Parametric Morphism (a a' b b' : bw) : (@monarrtens X cC mC a a' b b')
  with signature 
  (realize_equiv' a a') ==> (realize_equiv' b b') ==> (realize_equiv' (a⨂b) (a'⨂b'))
  as monarrtens_mor_real.
Proof. intros; apply tensor_compat; easy. Qed.

#[global] Add Parametric Morphism (a b : bw) : (realize_equiv' a b) 
  with signature 
  monarrequiv a b ==> monarrequiv a b ==> iff
  as realize_equiv_mor.
Proof.
  intros * H * H0; 
  rewrite H, H0.
  easy.
Qed.

Lemma mon_struct_l {a a' b} (f : bwarr a a') (g : a' ⟶ b) (h : a ⟶ b) :
  f ◌ g ≡ h <-> g ≡ monarrstruct (a:=a') (b:=a) f ^-  ◌ h.
Proof.
  now split; [intros <-|intros ->];
  rewrite monarr_assoc, monarr_struct_inv, monarr_id_l.
Qed.

Lemma mon_struct_r {a a' b} (f : bwarr a' b) (g : a ⟶ a') (h : a ⟶ b) :
  g ◌ f ≡ h <-> g ≡ h ◌ monarrstruct (a:=b) (b:=a') f ^-.
Proof.
  now split; [intros <-|intros ->];
  rewrite <- monarr_assoc, monarr_struct_inv, monarr_id_r.
Qed.

Lemma mon_struct_l' {a a' b} (f : bwarr a a') (g : a' ⟶ b) (h : a ⟶ b) :
  h ≡ f ◌ g <-> monarrstruct (a:=a') (b:=a) f ^- ◌ h ≡ g.
Proof.
  now split; [intros ->|intros <-];
  rewrite monarr_assoc, monarr_struct_inv, monarr_id_l.
Qed.

Lemma mon_struct_r' {a a' b} (f : bwarr a' b) (g : a ⟶ a') (h : a ⟶ b) :
  h ≡ g ◌ f <-> h ◌ monarrstruct (a:=b) (b:=a') f ^- ≡ g.
Proof.
  now split; [intros ->|intros <-];
  rewrite <- monarr_assoc, monarr_struct_inv, monarr_id_r.
Qed.

Lemma by_all_equiv_foliation {a b} (f g : a ⟶ b) :
  all_monarrlist_list_equiv (foliate_monarr f) (foliate_monarr g) ->
  f ≡ g.
Proof.
  intros Hequiv.
  apply realize_equiv_subrel.
  apply monarrequiv_iff_monarr_norm_equiv.
  apply (monarr_norm_equiv_trans' (foliate_correct' f) (foliate_correct' g)).
  apply (compose_composable_monarrlist_list_equiv Hequiv).
Qed.

Lemma by_reflexive_foliation {a b} (f g : a ⟶ b) : 
  foliate_monarr f = foliate_monarr g ->
  f ≡ g.
Proof.
  intros H; apply by_all_equiv_foliation.
  rewrite H.
  easy.
Qed.

Lemma by_reflexive_trim_foliation {a b} (f g : a ⟶ b) :
  trim_foliate_monarr f = trim_foliate_monarr g ->
  f ≡ g.
Proof.
  intro H.
  apply realize_equiv_subrel.
  apply monarrequiv_iff_monarr_norm_equiv.
  apply (monarr_norm_equiv_trans' 
    (trim_foliate_correct' f) (trim_foliate_correct' g)).
  (* revert H. *)
  lazymatch goal with
  |- monarr_norm_equiv (compose_totally_composable ?termf ?pf) _ => 
    pose proof (H : termf = _) as H'; 
    clear H; revert H';
    generalize termf pf (* idtac term
    change term with
    (trim_foliate_monarr f) *)
  end.
  intros; subst.
  erewrite compose_totally_composable_indep. easy.
Qed.

Lemma by_reflexive_trim_foliation_no_empty {a b} (f g : a ⟶ b) :
  trim_foliate_monarr_no_empty f = trim_foliate_monarr_no_empty g ->
  f ≡ g.
Proof.
  intro H.
  apply realize_equiv_subrel.
  apply monarrequiv_iff_monarr_norm_equiv.
  apply (monarr_norm_equiv_trans' 
    (trim_foliate_no_empty_correct' f) (trim_foliate_no_empty_correct' g)).
  lazymatch goal with
  |- monarr_norm_equiv (compose_totally_composable ?termf ?pf) _ => 
    pose proof (H : termf = _) as H'; 
    clear H; revert H';
    generalize termf pf
  end.
  intros; subst.
  erewrite compose_totally_composable_indep. 
  easy.
Qed.

(* Lemma realize_monarr_mor_under {a b c d : bw} (g g' : a ⟶ b) 
  (f f' : c ⟶ d) :
  (* (f ≊ g <-> f' ≊ g') ->  *)
  (g ≡ g' -> f ≡ f') ->
  g ≡ g' -> f ≡ f'.
Proof.
  auto.
Qed.

Definition monarr_under_rel {x y z w} (g g' : z ⟶ w) (f f' : x ⟶ y) :=
  g ≡ g' -> f ≡ f'.

Arguments monarr_under_rel : simpl never.

#[global] Add Parametric Morphism {x y z w} : (@monarr_under_rel x y z w) 
  with signature
  monarrequiv _ _ ==> monarrequiv _ _ ==> 
  monarrequiv _ _ ==> monarrequiv _ _ ==> iff
  as monarr_under_rel_mor.
Proof.
  unfold monarr_under_rel.
  intros * H * H' * H'' * H'''.
  rewrite H, H', H'', H'''.
  easy.
Qed.

#[global] Add Parametric Relation {x y z w} g g' : 
  (x ⟶ y) (@monarr_under_rel x y z w g g')
  reflexivity proved by ltac:(intros []; easy)
  symmetry proved by ltac:(unfold monarr_under_rel in *; intros **; 
    (* match goal with |- ?g => idtac g end; *)
    try symmetry; eauto; intros ? **; symmetry; auto)
  transitivity proved by 
    ltac:(unfold monarr_under_rel in *; intros **;
    try etransitivity; eauto;
    intros ? **; etransitivity; eauto)
  as monarr_under_rel_relation.

#[program] Instance monarr_under_subrel {x y} : 
  subrelation (monarrequiv x y) (realize_equiv x y).
Next Obligation.
  rewrite H.
  reflexivity.
Qed.

Lemma monarr_under_struct_r {x x' y z w} (g g' : z ⟶ w)
  f (f' : bwarr x' y) (h : x ⟶ y): 
  monarr_under_rel g g' (f ◌ f') h <->
  monarr_under_rel g g' f (h ◌ f' ^-).
Proof.
  unfold monarr_under_rel.
  split; intros H Hg; specialize (H Hg);
  [rewrite <- H | rewrite H];
  rewrite <- monarr_assoc, monarr_arrcomp,
    ?monarr_id_l, ?monarr_id_r; easy.
Qed.

Lemma monarr_under_struct_l {x x' y z w} (g g' : z ⟶ w)
  (f : bwarr x x') f' (h : x ⟶ y): 
  monarr_under_rel g g' (f ◌ f') h <->
  monarr_under_rel g g' f' (f ^- ◌ h).
Proof.
  unfold monarr_under_rel.
  split; intros H Hg; specialize (H Hg);
  [rewrite <- H | rewrite H];
  rewrite monarr_assoc, monarr_arrcomp,
    ?monarr_id_l, ?monarr_id_r; easy.
Qed.

Lemma monarr_under_struct_r' {x x' y z w} (g g' : z ⟶ w)
  f (f' : bwarr x' y) (h : x ⟶ y): 
  monarr_under_rel g g' h (f ◌ f') <->
  monarr_under_rel g g' (h ◌ f' ^-) f.
Proof.
  split; symmetry; now apply monarr_under_struct_r.
Qed.

Lemma monarr_under_struct_l' {x x' y z w} (g g' : z ⟶ w)
  (f : bwarr x x') f' (h : x ⟶ y): 
  monarr_under_rel g g' h (f ◌ f') <->
  monarr_under_rel g g' (f ^- ◌ h) f'.
Proof.
  split; symmetry; now apply monarr_under_struct_l.
Qed.

Lemma monarr_under_cancel_struct_l {x x' y z w} {g g' : z ⟶ w}
  (h : bwarr x x') (f f' : x' ⟶ y) :
  monarr_under_rel g g' (h ◌ f) (h ◌ f') <->
  monarr_under_rel g g' f f'.
Proof.
  now rewrite monarr_under_struct_l, 
    monarr_assoc, monarr_struct_inv, monarr_id_l.
Qed.

Lemma monarr_under_cancel_struct_r {x x' y z w} {g g' : z ⟶ w}
  (h : bwarr x' y) (f f' : x ⟶ x') :
  monarr_under_rel g g' (f ◌ h) (f' ◌ h) <->
  monarr_under_rel g g' f f'.
Proof.
  now rewrite monarr_under_struct_r, 
    <- monarr_assoc, monarr_struct_inv, monarr_id_r.
Qed.

Lemma monarr_under_cancel_l {x x' y z w} {g g' : z ⟶ w}
  (h : x ⟶ x') (f f' : x' ⟶ y) :
  monarr_under_rel g g' f f' ->
  monarr_under_rel g g' (h ◌ f) (h ◌ f').
Proof.
  now intros H Hg; rewrite (H Hg).
Qed.

Lemma monarr_under_cancel_r {x x' y z w} {g g' : z ⟶ w}
  (h : x' ⟶ y) (f f' : x ⟶ x') :
  monarr_under_rel g g' f f' ->
  monarr_under_rel g g' (f ◌ h) (f' ◌ h).
Proof.
  now intros H Hg; rewrite (H Hg).
Qed.

Lemma monarr_under_rel_trans {s t u v x y z w} (g g' : u ⟶ v) 
  (h h' : x ⟶ y) (i i' : s ⟶ t) (fmid f f' : z ⟶ w) :
  monarr_under_rel h h' f fmid ->
  monarr_under_rel i i' fmid f' ->
  h ≡ h' -> i ≡ i' -> 
  monarr_under_rel g g' f f'.
Proof.
  unfold monarr_under_rel.
  intros; etransitivity; eauto.
Qed.

Lemma monarr_under_rel_trans_no_evars {u v x y z w}
  {h h' : u ⟶ v} {i i' : x ⟶ y} (fmid f f' : z ⟶ w) :
  monarr_under_rel h h' f fmid ->
  monarr_under_rel i i' fmid f' ->
  h ≡ h' -> i ≡ i' -> 
  monarr_under_rel f f f f'.
Proof.
  apply monarr_under_rel_trans.
Qed. *)

(* Lemma under_by_norm_equiv *)

Unset Universe Polymorphism.

End monarr_under_over.

(* Arguments monarrstruct {_ _ _} _ _.

Notation "'α_' a ',' b ',' c" := 
  (monarrstruct (a%monarr_scope ⨂ b%monarr_scope ⨂ c%monarr_scope) 
    (a%monarr_scope ⨂ (b%monarr_scope ⨂ c%monarr_scope)) _)
  (in custom mon at level 20, 
  a custom mon_bw, b custom mon_bw, c custom mon_bw) : monarr_scope.
Notation "'α_' a ',' b ',' c ⁻¹" := 
  (monarrstruct (a%monarr_scope ⨂ (b%monarr_scope ⨂ c%monarr_scope)) 
    (a%monarr_scope ⨂ b%monarr_scope ⨂ c%monarr_scope) _)
  (in custom mon at level 20, 
  a custom mon_bw, b custom mon_bw, c custom mon_bw) : monarr_scope.
Notation "'λ_' a" := (monarrstruct (e ⨂ a%monarr_scope) a%monarr_scope _)
  (in custom mon at level 20, a custom mon_bw) : monarr_scope.
Notation "'λ_' a ⁻¹" := (monarrstruct a%monarr_scope (e ⨂ a%monarr_scope) _)
  (in custom mon at level 20, a custom mon_bw) : monarr_scope.
Notation "'ρ_' a" := (monarrstruct (a%monarr_scope ⨂ e) a%monarr_scope _)
  (in custom mon at level 20, a custom mon_bw) : monarr_scope.
Notation "'ρ_' a ⁻¹" := (monarrstruct a%monarr_scope (a%monarr_scope ⨂ e) _)
  (in custom mon at level 20, a custom mon_bw) : monarr_scope.
Notation "'{' a '⟶' b '}'" := 
  (monarrstruct a%monarr_scope b%monarr_scope _) 
  (in custom mon at level 5, 
  a custom mon_bw (* at level 99 *), b custom mon_bw (* at level 99 *), 
  only printing) : monarr_scope.
Notation "'id_' a" := (monarrstruct a%monarr_scope a%monarr_scope _)
  (in custom mon at level 20, a custom mon_bw, only printing) : monarr_scope.
Notation "a" := (var a%monarr_scope) 
  (in custom mon_bw at level 10, a constr at level 9, 
  only printing) : monarr_scope.
Notation "a × b" := (tens a%monarr_scope b%monarr_scope) 
  (in custom mon_bw at level 20, 
  a custom mon_bw, b custom mon_bw,
  left associativity,
  only printing) : monarr_scope.
Notation "'(' a ')'" := a%monarr_scope 
  (in custom mon_bw at level 0, 
  a custom mon_bw at level 200) : monarr_scope.
Notation "'(' a ')'" := a%monarr_scope 
  (in custom mon at level 0, 
  a custom mon at level 200) : monarr_scope.
Notation "f ⊗ g" := (monarrtens f%monarr_scope g%monarr_scope) 
  (in custom mon at level 34, 
    f custom mon, g custom mon,
    left associativity) : monarr_scope.
Notation "{ a }" := (mongeneric a%monarr_scope) 
  (in custom mon at level 10) : monarr_scope.
Notation "f ∘ g" := (monarrcomp f%monarr_scope g%monarr_scope) 
  (in custom mon at level 40, 
  f custom mon, g custom mon (* at level 40 *),
  left associativity) : monarr_scope.
Notation "f ≊ g" := (monarrequiv _ _ f%monarr_scope g%monarr_scope)
  (in custom mon at level 70, f custom mon, g custom mon) : monarr_scope.
Notation "a" := a (in custom mon at level 0, a constr) : monarr_scope.

Notation "''Monarr[' f '≊' g ']'" :=
  (_ ≡ _ /\ monarr_under_rel _ _ f%monarr_scope g%monarr_scope) 
  (f custom mon, g custom mon, only printing).  *)

Import MCDefinitions.

Declare Custom Entry mon.
Declare Custom Entry mon_bw.

Declare Scope monarr_scope.
Delimit Scope monarr_scope with monarr_scope.
Close Scope monarr_scope.

Import MC_notations.

(* Arguments monarrstruct {_ _ _} _ _. *)

Notation "'α_' a ',' b ',' c" := 
  (@monarrstruct _ _ _ 
    (tens (tens 
    a%monarr_scope b%monarr_scope) c%monarr_scope) 
    (tens a%monarr_scope 
    (tens b%monarr_scope c%monarr_scope)) _)
  (in custom mon at level 20, 
  a custom mon_bw, b custom mon_bw, c custom mon_bw) : monarr_scope.
Notation "'α_' a ',' b ',' c ⁻¹" := 
  (@monarrstruct _ _ _  
  (tens a%monarr_scope (tens b%monarr_scope c%monarr_scope)) 
    (tens (tens a%monarr_scope b%monarr_scope) c%monarr_scope) _)
  (in custom mon at level 20, 
  a custom mon_bw, b custom mon_bw, c custom mon_bw) : monarr_scope.
Notation "'λ_' a" := (@monarrstruct _ _ _  (tens e a%monarr_scope) a%monarr_scope _)
  (in custom mon at level 20, a custom mon_bw) : monarr_scope.
Notation "'λ_' a ⁻¹" := (@monarrstruct _ _ _  a%monarr_scope (tens e a%monarr_scope) _)
  (in custom mon at level 20, a custom mon_bw) : monarr_scope.
Notation "'ρ_' a" := (@monarrstruct _ _ _  (tens a%monarr_scope e) a%monarr_scope _)
  (in custom mon at level 20, a custom mon_bw) : monarr_scope.
Notation "'ρ_' a ⁻¹" := (@monarrstruct _ _ _  a%monarr_scope (tens a%monarr_scope e) _)
  (in custom mon at level 20, a custom mon_bw) : monarr_scope.
Notation "'{' a '⟶' b '}'" := 
  (@monarrstruct _ _ _ a%monarr_scope b%monarr_scope _) 
  (in custom mon at level 5, 
  a custom mon_bw (* at level 99 *), b custom mon_bw (* at level 99 *), 
  only printing) : monarr_scope.
Notation "'id_' a" := (@monarrstruct _ _ _ a%monarr_scope a%monarr_scope _)
  (in custom mon at level 20, a custom mon_bw, only printing) : monarr_scope.
Notation "a" := (var a%monarr_scope) 
  (in custom mon_bw at level 10, a constr at level 9, 
  only printing) : monarr_scope.
Notation "'e'" := (@e _)
  (in custom mon_bw at level 0, only printing) : monarr_scope.
Notation "a × b" := (tens a%monarr_scope b%monarr_scope) 
  (in custom mon_bw at level 20, 
  a custom mon_bw, b custom mon_bw,
  left associativity,
  only printing) : monarr_scope.
Notation "'(' a ')'" := a%monarr_scope 
  (in custom mon_bw at level 0, 
  a custom mon_bw at level 200) : monarr_scope.
Notation "'(' a ')'" := a%monarr_scope 
  (in custom mon at level 0, 
  a custom mon at level 200) : monarr_scope.
Notation "f ⊗ g" := (monarrtens f%monarr_scope g%monarr_scope) 
  (in custom mon at level 34, 
    f custom mon, g custom mon,
    left associativity) : monarr_scope.
Notation "{ a }" := (mongeneric a%monarr_scope) 
  (in custom mon at level 10) : monarr_scope.
Notation "f ∘ g" := (monarrcomp f%monarr_scope g%monarr_scope) 
  (in custom mon at level 40, 
  f custom mon, g custom mon (* at level 40 *),
  left associativity) : monarr_scope.
Notation "f ≊ g" := (monarrequiv _ _ f%monarr_scope g%monarr_scope)
  (in custom mon at level 70, f custom mon, g custom mon) : monarr_scope.
Notation "a" := a (in custom mon at level 0, a constr) : monarr_scope.

(* Notation "''Monarr[' f '≊' g ']'" :=
  (realize_equiv' f%monarr_scope g%monarr_scope) 
  (f custom mon, g custom mon, only printing).  *)

Notation "''Cat[' f '≃' g ']'" :=
  (realize_equiv' _ _ f%monarr_scope g%monarr_scope) 
  (f custom mon, g custom mon, only printing). 

Section Testing.

Import MCClasses CategoryTypeclass.

Context {X : Type} {UIPX : UIP X}.
Context {cC : Category X} {cCh : CategoryCoherence cC} 
  {mC : MonoidalCategory cC} {mCh : MonoidalCategoryCoherence mC}.


(* Print Grammar tactic. *)
(* Ltac monarr_etransitivity :=
  match goal with
  | |- monarr_under_rel _ _ _ _ => eapply monarr_under_rel_trans_no_evars
  | _ => fail 1 "Not a monarr goal (of the form 'Monarr[ _ ≊ _ ])"
  end.

Ltac monarr_over := 
  match goal with 
  |- monarr_under_rel _ _ _ _ => exact (fun x => x)
  end.

Ltac monarr_under :=
  refine (realize_monarr_mor_under _ _ _ _ (_ : monarr_under_rel _ _ _ _) _).  *)

Import MCprocessing MCconsequences MCmonarrlist List.

Ltac full_process t :=
  let proc := eval compute in (full_process_monarr t) in 
  match type of proc with
  | @monarr ?X ?cC ?mC ?from_proc ?to_proc =>
  match type of t with
  | monarr ?A ?B =>
    let RHS := constr:(monarrcomp (monarrcomp 
      (@monarrstruct X cC mC A from_proc (bwarr_of_Nf_eq (full_process_in_pf t)))
      proc) (@monarrstruct X cC mC to_proc A (bwarr_of_Nf_eq (full_process_out_pf t)))) in
    let rw := constr:(MCprocessing.full_process_monarr_equiv t : monarrequiv _ _ t RHS) in
    rewrite rw
  end
  end.


(* Goal forall (A B M N P Q : X) (f : (A×A ~> B×B)%Cat) (g : (M ~> N)%Cat)
(h : (P ~> Q)%Cat), (α_ (A×A), M, P ∘ f ⊗ (g ⊗ h) ≃ f ⊗ g ⊗ h ∘ α_ (B×B), N, Q)%Cat.
intros.
change
  (realize_equiv' _ _ (arrinvassoc _ _ _ ◌ 
  mongeneric (a := tens (var A) (var A)) (b := tens (var B) (var B)) f 
    ⧆ (mongeneric (a:=var M) (b:=var N) g 
    ⧆ mongeneric (a:=var P) (b:=var Q) h))
    ( 
  mongeneric (a := tens (var A) (var A)) (b := tens (var B) (var B)) f 
    ⧆ mongeneric (a:=var M) (b:=var N) g 
    ⧆ mongeneric (a:=var P) (b:=var Q) h ◌ arrinvassoc _ _ _))%bw.
rewrite monarr_invassoc_nat_l.
 *)

(*Ltac full_process t :=
  let pf := constr:(MCprocessing.full_process_monarr_equiv t) in
  (* let T := type of pf in idtac T; *)
  lazymatch type of pf with
  | monarrequiv ?a ?b ?LHS ?RHS => 
    match RHS with
    | monarrcomp (monarrcomp 
      (@monarrstruct ?X ?cC ?mC ?inL ?outL ?pfL) 
      ?center)
      (@monarrstruct _ _ _ ?inR ?outR ?pfR) =>
      let cinL := eval vm_compute in inL in
      let coutL := eval vm_compute in outL in
      let cinR := eval vm_compute in inR in
      let coutR := eval vm_compute in outR in
      let ccenter := eval vm_compute in center in
      let rw := constr:(pf : monarrequiv a b LHS 
      (monarrcomp (monarrcomp 
        (@monarrstruct X cC mC cinL coutL pfL)
        ccenter)
        (@monarrstruct X cC mC cinR coutR pfR))) in
      rewrite rw
    end
  end.

Ltac full_process' t :=
  let pf := constr:(MCprocessing.full_process_monarr_equiv t) in
  (* let T := type of pf in idtac T; *)
  lazymatch type of pf with
  | monarrequiv ?a ?b ?LHS ?RHS => 
    let cRHS := eval vm_compute in RHS in
    let rw := constr:(pf : monarrequiv a b LHS cRHS) in 
    rewrite rw
  end.


Ltac full_process'' t :=
  (* match type of t with
  | monarr ?A ?B =>
       *)
  let pf := constr:(MCprocessing.full_process_monarr_equiv t) in
  let T := type of pf in
  let cbnT := eval vm_compute in T in 
  let rw := constr:(pf : cbnT) in 
  rewrite rw. *)

(* Require Import CategoryAutomation. *)

(* Import MCprocessing MCconsequences MCmonarrlist List.

Goal forall (A B M N P Q : X) (f : (A×A ~> B×B)%Cat) (g : (M ~> N)%Cat)
(h : (P ~> Q)%Cat), (α_ (A×A), M, P ∘ f ⊗ (g ⊗ h) ≃ f ⊗ g ⊗ h ∘ α_ (B×B), N, Q)%Cat.
intros.
change
  (realize_equiv' _ _ (arrinvassoc _ _ _ ◌ 
  mongeneric (a := tens (var A) (var A)) (b := tens (var B) (var B)) f 
    ⧆ (mongeneric (a:=var M) (b:=var N) g 
    ⧆ mongeneric (a:=var P) (b:=var Q) h))
    ( 
  mongeneric (a := tens (var A) (var A)) (b := tens (var B) (var B)) f 
    ⧆ mongeneric (a:=var M) (b:=var N) g 
    ⧆ mongeneric (a:=var P) (b:=var Q) h ◌ arrinvassoc _ _ _))%bw.
(* change
  (realize_monarr (arrinvassoc _ _ _ ◌ 
  mongeneric (a := tens (var A) (var A)) (b := tens (var B) (var B)) f 
    ⧆ (mongeneric (a:=var M) (b:=var N) g 
    ⧆ mongeneric (a:=var P) (b:=var Q) h))
    ≃ realize_monarr ( 
  mongeneric (a := tens (var A) (var A)) (b := tens (var B) (var B)) f 
    ⧆ mongeneric (a:=var M) (b:=var N) g 
    ⧆ mongeneric (a:=var P) (b:=var Q) h ◌ arrinvassoc _ _ _))%Cat%bw. *)

(* rewrite mon_struct_l, monarr_assoc_nat_r. *)

time (match goal with
|- realize_equiv' _ _ ?t ?g =>
let proc := eval compute in (full_process_monarr t) in 
match type of proc with
| @monarr ?X ?cC ?mC ?from_proc ?to_proc =>
match type of t with
| monarr ?A ?B =>
  let RHS := constr:(monarrcomp (monarrcomp 
    (@monarrstruct X cC mC A from_proc (bwarr_of_Nf_eq (full_process_in_pf t)))
    proc) (@monarrstruct X cC mC to_proc B (bwarr_of_Nf_eq (full_process_out_pf t)))) in
  let rw := constr:(MCprocessing.full_process_monarr_equiv t : monarrequiv _ _ t RHS) in
  time "rw" (rewrite rw)
end
end
end).

(* time *) (do 10 (try (match goal with
|- realize_equiv' _ _ ?f ?g =>
  full_process f
  (* let t := eval compute in (full_process_monarr f) in 
  idtac *)
end; fail))).

(* time *) (do 10 (try (match goal with
|- realize_equiv' _ _ ?f ?g =>
  full_process_new f
  (* let t := eval compute in (full_process_monarr f) in 
  idtac *)
end; fail))).

time (do 10 (try (match goal with
|- realize_equiv' _ _ ?f ?g =>
  let t := eval compute in (full_process_monarr f) in 
  idtac
end; fail))).


(* match goal with
|- realize_equiv' _ _ ?f ?g =>
  let t := eval compute in (foliate_monarr f) in 
  idtac t
end. *)

time (do 10 (try (match goal with
|- realize_equiv' _ _ ?f ?g =>
  let t := eval compute in (foliate_monarr f) in 
  idtac
end; fail))).

let f := match goal with
  |- realize_equiv' _ _ ?f ?g => constr:(f)
  end in 
let fol := eval compute in (foliate_monarr f) 
in 
time (do 10 (
  let t := eval compute in (map structify_monarrlist fol) in 
  idtac)).

let f := match goal with
  |- realize_equiv' _ _ ?f ?g => constr:(f)
  end in 
let fol := eval compute in (map structify_monarrlist (foliate_monarr f))
in 
time (do 10 (
  let t := eval compute in (map remove_structs fol) in 
  idtac)).


let f := match goal with
  |- realize_equiv' _ _ ?f ?g => constr:(f)
  end in 
let fol := eval compute in 
  (map remove_structs (map structify_monarrlist (foliate_monarr f)))
in 
time (do 10 (
  let t := eval compute in (map split_ids fol) in 
  idtac)).


let f := match goal with
  |- realize_equiv' _ _ ?f ?g => constr:(f)
  end in 
let fol := eval compute in 
  (map split_ids (map remove_structs (map structify_monarrlist (foliate_monarr f))))
in 
time (do 10 (
  let t := eval compute in (full_right_shift fol) in 
  idtac)).

  

  
apply MCconsequences.monarrcomp_struct_l.
monarr_under.

Time (do 10 (try (match goal with
|- monarr_under_rel _ _ ?f ?g =>
  full_process f
  (* full_process f; full_process g *)
end; fail))).

(* epose MCprocessing.full_process_monarr as T.
unfold MCprocessing.full_process_monarr in T. *)

(* rewrite <- MCmonarrlist.monarrequiv_iff_monarr_norm_equiv. *)

match goal with
|- monarr_under_rel _ _ ?f ?g =>
  full_process f
  (* full_process f; full_process g *)
end.

Time (do 10 (try (match goal with
|- monarr_under_rel _ _ ?f ?g =>
  full_process f
  (* full_process f; full_process g *)
end; fail))).


rewrite monarr_under_struct_l.
rewrite monarr_invassoc_nat_r.
rewrite monarr_assoc.
rewrite monarr_arrcomp. 
rewrite monarr_id_l.
monarr_over.
easy.
Qed.


Goal forall (A B M N : X), 
(α_ A, B, M ⊗ id_ N ∘ α_ A, B × M, N ∘ id_ A ⊗ α_ B, M, N
 ≃ α_ A × B, M, N ∘ α_ A, B, (M × N))%Cat.
 intros.
 change
   (realize_monarr (monarrcomp (arrid (var M))
     (mongeneric (a:=var M) (b:=var N) g))
     ≃ realize_monarr (mongeneric (a:=var M) (b:=var N) g))%Cat.
 monarr_under.
 

Goal forall (A B M N P Q : X) (f : (A×A ~> B×B)%Cat) (g : (M ~> N)%Cat)
  (h : (P ~> Q)%Cat), (id_ M ∘ g ≃ g)%Cat.
intros.
change
  (realize_monarr (monarrcomp (arrid (var M))
    (mongeneric (a:=var M) (b:=var N) g))
    ≃ realize_monarr (mongeneric (a:=var M) (b:=var N) g))%Cat.
monarr_under.
pentagon
full_process (@monarrcomp X cC mC (@var X M) (@var X M) (@var X N) 
(@arrid X (@var X M)) (@mongeneric X cC mC (@var X M) (@var X N) g)).

cbn.

repeat match goal with 
|- context[MCmonarrlist.monarrlist_list_source ?l] =>
  let simpled := eval cbn in (MCmonarrlist.monarrlist_list_source l) in
  change (MCmonarrlist.monarrlist_list_source l) with simpled

|- context[MCmonarrlist.monarrlist_list_source ?l] =>
let simpled := eval cbn in (MCmonarrlist.monarrlist_list_source l) in
change (MCmonarrlist.monarrlist_list_source l) with simpled
end.
cbn [MCmonarrlist.monarrlist_list_source
  MCprocessing.full_process_monarrlist_list
  MCprocessing.foliate_monarr
  (* MCmonarrlist.monarrlist_arr *)].
simpl.
rewrite MCprocessing.full_process_monarr_equiv.
cbn [MCprocessing.full_process_monarr].
monarr_etransitivity.
rewrite monarr_id_l.
monarr_over.
easy.
Qed.


Goal forall (A B M N P Q : X) (f : (A×A ~> B×B)%Cat) (g : (M ~> N)%Cat)
(h : (P ~> Q)%Cat), (α_ (A×A), M, P ∘ f ⊗ (g ⊗ h) ≃ f ⊗ g ⊗ h ∘ α_ (B×B), N, Q)%Cat.
intros.
change
  (realize_monarr (arrinvassoc _ _ _ ◌ 
  mongeneric (a := tens (var A) (var A)) (b := tens (var B) (var B)) f 
    ⧆ (mongeneric (a:=var M) (b:=var N) g 
    ⧆ mongeneric (a:=var P) (b:=var Q) h))
    ≃ realize_monarr ( 
  mongeneric (a := tens (var A) (var A)) (b := tens (var B) (var B)) f 
    ⧆ mongeneric (a:=var M) (b:=var N) g 
    ⧆ mongeneric (a:=var P) (b:=var Q) h ◌ arrinvassoc _ _ _))%Cat.
monarr_under.
rewrite monarr_under_struct_l.
rewrite monarr_invassoc_nat_r.
rewrite monarr_assoc.
rewrite monarr_arrcomp. 
rewrite monarr_id_l.
monarr_over.
easy.
Qed.



(* Arguments monarrstruct {_ _ _ _ _}. *)

Section Testing.
(*
Local Ltac monarr_over := 
  match goal with 
  |- monarr_under_rel _ _ _ _ => exact (fun x => x); try reflexivity
  end.

Local Ltac monarr_under :=
  refine (realize_monarr_mor_under _ _ _ _ (_ : monarr_under_rel _ _ _ _) _). 


Goal forall (A B M N P Q : X) (f : (A×A ~> B×B)%Cat) (g : (M ~> N)%Cat)
  (h : (P ~> Q)%Cat), (id_ M ∘ g ≃ g)%Cat.
intros.
change
  (realize_monarr (arrid (var M) ◌ 
    mongeneric (a:=var M) (b:=var N) g)
    ≃ realize_monarr (mongeneric (a:=var M) (b:=var N) g))%Cat.
monarr_under.
rewrite monarr_id_l.
monarr_over.
easy.
Qed.


Goal forall (A B M N P Q : X) (f : (A×A ~> B×B)%Cat) (g : (M ~> N)%Cat)
(h : (P ~> Q)%Cat), (α_ (A×A), M, P ∘ f ⊗ (g ⊗ h) ≃ f ⊗ g ⊗ h ∘ α_ (B×B), N, Q)%Cat.
intros.
change
  (realize_monarr (arrinvassoc _ _ _ ◌ 
  mongeneric (a := tens (var A) (var A)) (b := tens (var B) (var B)) f 
    ⧆ (mongeneric (a:=var M) (b:=var N) g 
    ⧆ mongeneric (a:=var P) (b:=var Q) h))
    ≃ realize_monarr ( 
  mongeneric (a := tens (var A) (var A)) (b := tens (var B) (var B)) f 
    ⧆ mongeneric (a:=var M) (b:=var N) g 
    ⧆ mongeneric (a:=var P) (b:=var Q) h ◌ arrinvassoc _ _ _))%Cat.
monarr_under.
rewrite monarr_under_struct_l.
rewrite monarr_invassoc_nat_r.
rewrite monarr_assoc.
rewrite monarr_arrcomp. 
rewrite monarr_id_l.
monarr_over.
easy.
Qed.
*) *)
End Testing.

Set Universe Polymorphism.

Import -(notations) Category Monoidal.

Ltac evarT f T :=
  let _ := match goal with 
  |- _ =>
     evar (f : T)
  end in 
  let x' := eval unfold f in f in 
  uconstr:(x').

Ltac quote_to_bw term C cC mC :=
  let rec quote term :=  
  match term with
  | mC.(mon_I) => constr:(@e C)
  | mC.(obj_tensor) ?a ?b =>
    let qa := quote a in
    let qb := quote b in 
    constr:(@tens C qa qb)
  | ?t => 
    let a := fresh in let b := fresh in 
    let _ := match goal with 
    |- _ => evar (a : C); evar (b : C)
    end in 
    let a' := eval unfold a in a in 
    let b' := eval unfold b in b in 
    let _ := match goal with
    | |- _ => unify (mC.(obj_tensor) a' b') t
    (* | |- _ => clear a b; fail 1 *)
      (* ; idtac "unified as tensor of" a' "and" b' *)
    end in 
    let qa' := quote a' in 
    let qb' := quote b' in 
    let _ := match goal with 
    |- _ => clear a b
    end in
    constr:(@tens C qa' qb')
  | ?t => constr:(@var C t)
  end in 
  quote term.

Ltac quote_to_bwarr term C cC mC :=
  let bw_quote A := quote_to_bw A C cC mC in 
  let rec quote term := 
  match term with 
  | cC.(compose) ?f ?g => 
    let qf := quote f in 
    let qg := quote g in 
    constr:(@arrcomp C _ _ _ qf qg)
  | mC.(mor_tensor) ?f ?g =>
    let qf := quote f in 
    let qg := quote g in 
    constr:(@arrtens C _ _ _ qf qg)
  | cC.(c_identity) ?A => 
    let qA := bw_quote A in
    constr:(arrid (* C *) qA)
  | forward (mC.(associator) ?A ?B ?M) => 
    let _ := match goal with |- _ => idtac "found assoc directly" term end in
    let qA := bw_quote A in
    let qB := bw_quote B in
    let qM := bw_quote M in
    let _ := match goal with |- _ => idtac "quoted successfully" end in
    constr:(arrinvassoc (* C *) qA qB qM)
  | reverse (mC.(associator) ?A ?B ?M) =>
    let _ := match goal with |- _ => idtac "found reverse assoc directly" term end in
    let qA := bw_quote A in
    let qB := bw_quote B in
    let qM := bw_quote M in
    let _ := match goal with |- _ => idtac "quoted successfully" end in
    constr:(arrassoc (* C *) qA qB qM)
  | forward (mC.(left_unitor) ?A) => 
    let qA := bw_quote A in
    constr:(arrlunitor (* C *) qA)
  | reverse (mC.(left_unitor) ?A) => 
    let qA := bw_quote A in
    constr:(arrinvlunitor (* C *) qA)
  | forward (mC.(right_unitor) ?A) => 
    let qA := bw_quote A in
    constr:(arrrunitor (* C *) qA)
  | reverse (mC.(right_unitor) ?A) => 
    let qA := bw_quote A in
    constr:(arrinvrunitor (* C *) qA)
  | ?t =>
    let A' := fresh in let B' := fresh in 
    let A := evarT A' C in 
    let B := evarT B' C in 
    let _ := match goal with 
    |- _ => 
      let T := type of t in 
      unify (cC.(morphism) A B) T
    end in
    let qA := bw_quote A in 
    let qB := bw_quote B in 
    let _ := match goal with |- _ => clear A' B' end in 
    match t with
    | ?t => 
      let _ := match goal with
      |- _ => unify (cC.(c_identity) A) t
        (* ; clear A' B' *)
      end in 
      constr:(arrid (* C *) qA)
    | ?t => 
      let _ := match goal with
      |- _ => unify (forward (mC.(left_unitor) B)) t
        (* ; clear A' B' *)
      end in 
      constr:(arrlunitor (* C *) qB)
    | ?t => 
      let _ := match goal with
      |- _ => unify (reverse (mC.(left_unitor) A)) t
        (* ; clear A' B' *)
      end in 
      constr:(arrinvlunitor (* C *) qA)
    | ?t => 
      let _ := match goal with
      |- _ => unify (forward (mC.(right_unitor) B)) t
        (* ; clear A' B' *)
      end in 
      constr:(arrrunitor (* C *) qB)
    | ?t => 
      let _ := match goal with
      |- _ => unify (reverse (mC.(right_unitor) A)) t
        (* ; clear A' B' *)
      end in 
      constr:(arrinvrunitor (* C *) qA)
    | ?t => 
      let M' := fresh in let f' := fresh in let g' := fresh in
      let M := evarT M' C in 
      let f := evarT f' (cC.(morphism) A M) in 
      let g := evarT g' (cC.(morphism) M B) in 
      let _ := match goal with
      | |- _ => unify (cC.(compose) f g) t
      (* | |- _ => clear M' f' g'; fail 1 *)
      end in 
      let qf := quote f in 
      let qg := quote g in 
      let _ := match goal with 
      |- _ => clear M' f' g'
      end in
      constr:(arrcomp (* C *) qf qg)
    | ?t => 
      let A1' := fresh in let B1' := fresh in let A2' := fresh in 
      let B2' := fresh in let f' := fresh in let g' := fresh in
      let A1 := evarT A1' C in 
      let B1 := evarT B1' C in 
      let A2 := evarT A2' C in 
      let B2 := evarT B2' C in 
      let f := evarT f' (cC.(morphism) A1 B1) in 
      let g := evarT g' (cC.(morphism) A2 B2) in 
      let _ := match goal with
      | |- _ => unify (mC.(mor_tensor) f g) t
      (* | |- _ => clear A1' B1' A2' B2' f' g' *)
      end in 
      let qf := quote f in 
      let qg := quote g in 
      let _ := match goal with 
      |- _ => clear A1' B1' A2' B2' f' g'
      end in
      constr:(arrtens (* C *) qf qg)
    | ?t => 
      let A'' := fresh in let B'' := fresh in let M'' := fresh in 
      let A' := evarT A'' C in 
      let B' := evarT B'' C in 
      let M' := evarT M'' C in 
      let _ := match goal with 
      | |- _ => unify (forward (mC.(associator) A' B' M')) t
        (* ; idtac "found associator" t *)
      (* | |- _ => clear A'' B'' M'' *)
      end in 
      let qA' := bw_quote A' in 
      let qB' := bw_quote B' in 
      let qM' := bw_quote M' in 
      let _ := match goal with 
      |- _ => clear A'' B'' M''
      end in
      constr:(arrinvassoc (* C *) qA' qB' qM')
    | ?t => 
      let A'' := fresh in let B'' := fresh in let M'' := fresh in 
      let A' := evarT C in 
      let B' := evarT C in 
      let M' := evarT C in 
      let _ := match goal with 
      | |- _ => unify (reverse (mC.(associator) A' B' M')) t
      (* | |- _ => clear A'' B'' M'' *)
      end in 
      let qA' := bw_quote A' in 
      let qB' := bw_quote B' in 
      let qM' := bw_quote M' in  
      let _ := match goal with 
      |- _ => clear A'' B'' M''
      end in
      constr:(arrassoc (* C *) qA' qB' qM')
    end
  end
  in quote term.

Ltac quote_to_monarr term C cC mC :=
  let quote ter := quote_to_monarr ter C cC mC in 
  let bw_quote A := quote_to_bw A C cC mC in 
  let bwarr_quote f := quote_to_bwarr f C cC mC in
  (* let _ := match goal with |- _ => idtac "quoting" term "to monarr in" C cC mC end in  *)
  let t' := constr:(term) in 
  (* let _ := match goal with |- _ => idtac "quoting" t' "to monarr in" C cC mC end in  *)
  match t' with
  | ?t => 
    (* let _ := match goal with |- _ => idtac "try bwarr..." end in  *)
    let qt := bwarr_quote t in 
    let _ := match goal with |- _ => idtac "found bwarr" qt end in 
    constr:(@monarrstruct C cC mC _ _ qt)
  | cC.(compose) ?f ?g => 
    (* let _ := match goal with |- _ => idtac "compose match for monarr" end in  *)
    let qf := quote f in 
    let qg := quote g in 
    constr:(@monarrcomp C cC mC _ _ _ qf qg)
  | mC.(mor_tensor) ?f ?g =>
    (* let _ := match goal with |- _ => idtac "tensor match for monarr" end in  *)
    let qf := quote f in 
    let qg := quote g in 
    constr:(@monarrtens C cC mC _ _ _ qf qg)
  | ?t =>
    (* let _ := match goal with |- _ => idtac "nonsimple match for monarr" end in  *)
    let A' := fresh in 
    let B' := fresh in 
    let _ := match goal with 
    |- _ => evar (A' : C); evar (B' : C)
    (* ; idtac "made A' and B'" *)
    end in  
    let A := eval unfold A' in A' in
    let B := eval unfold B' in B' in 
    let _ := match goal with 
    | |- _ => 
      (* idtac A B A' B'; *)
      let T := type of t in 
      unify (cC.(morphism) A B) T
    (* | |- _ => clear A' B'; fail 2 t "not a morphism" *)
      (* ;idtac "unified as morphism" A "to" B *)
    end in 
    (* let _ := match goal with |- _ => idtac A B A' B' end in  *)
    let qA := bw_quote A in 
    let qB := bw_quote B in 
    let _ := match goal with |- _ => clear A' B' end in 
    (* let _ := match goal with |- _ => idtac "here" end in  *)
    match t with 
    | ?t => 
      let M' := fresh in let f' := fresh in let g' := fresh in 
      let _ := match goal with 
      |- _ => evar (M' : C)
      end in 
      let M := eval unfold M' in M' in 
      let _ := match goal with 
      |- _ => evar (f' : (cC.(morphism) A M));
        evar (g' : cC.(morphism) M B)
      end in 
      let f := eval unfold f' in f' in 
      let g := eval unfold g' in g' in 
      let _ := match goal with
      | |- _ => unify (cC.(compose) f g) t
      (* | |- _ => clear M' f' g'; fail 1 *)
        (* ; idtac "unified as composition of" f "and" g *)
      end in 
      let qf := quote f in 
      let qg := quote g in 
      let _ := match goal with |- _ => clear M' f' g' end in
      constr:(@monarrcomp C cC mC _ _ _ qf qg)
    | ?t => 
      let A1' := fresh in let B1' := fresh in
      let A2' := fresh in let B2' := fresh in
      let f' := fresh in let g' := fresh in
      let A1 := evarT A1' C in 
      let B1 := evarT B1' C in 
      let A2 := evarT A2' C in 
      let B2 := evarT B2' C in 
      let f := evarT f' (cC.(morphism) A1 B1) in 
      let g := evarT g' (cC.(morphism) A2 B2) in 
      let _ := match goal with
      | |- _ => unify (mC.(mor_tensor) f g) t
      (* | |- _ => clear A1' A2' B1' B2' f' g'; fail 1 *)
        (* ; idtac "unified as tensor of" f "and" g *)
      end in 
      (* let _ := match goal with 
      |- _ => idtac f g
      end in *)
      let qf := quote f in 
      (* let _ := match goal with 
      |- _ => idtac qf
      end in *)
      let qg := quote g in 
      (* let _ := match goal with 
      |- _ => idtac qf qg
      end in *)
      let _ := match goal with |- _ => clear A1' A2' B1' B2' f' g' end in
      constr:(@monarrtens C cC mC _ _ _ _ qf qg)
    | ?t => 
      (* let _ := match goal with |- _ => idtac qA qB end in  *)
      constr:(@mongeneric C cC mC qA qB t)
    end
  end.

Ltac quote_equiv_to_monarr mC :=
  lazymatch type of mC with
  | @MonoidalCategory ?X ?cC =>
    let monarr_quote ter := quote_to_monarr ter X cC mC in 
    let bw_quote A := quote_to_bw A X cC mC in 
    let bwarr_quote f := quote_to_bwarr f X cC mC in
    let A := fresh "A" in 
    let B := fresh "B" in 
    let f := fresh "f" in 
    let g := fresh "g" in 
    evar (A : X); evar (B : X);
    let A' := eval unfold A in A in 
    let B' := eval unfold B in B in 
    evar (f : cC.(morphism) A' B');
    evar (g : cC.(morphism) A' B');
    let f' := eval unfold f in f in 
    let g' := eval unfold g in g in 
    let GOAL := lazymatch goal with |- ?G => constr:(G) end in
    unify (@c_equiv X cC A' B' f' g') GOAL;
    let qA := bw_quote A' in
    let qB := bw_quote B' in
    let qf := monarr_quote f' in 
    let qg := monarr_quote g' in
    clear f g A B; 
    change (@realize_equiv' X cC mC qA qB qf qg)
  | ?T => fail "couldn't see as MonoidalCategory instance:" mC "(with type" T ")"
  end.
    
Tactic Notation "monoidal" constr(mC) :=
  quote_equiv_to_monarr mC;
  apply by_reflexive_trim_foliation_no_empty; easy.

Tactic Notation "monoidal" :=
  let x := fresh in 
  let o := open_constr:(MonoidalCategory _) in
  unshelve evar (x:o); 
  [typeclasses eauto|..];
  let x' := eval unfold x in x in 
  monoidal x'.