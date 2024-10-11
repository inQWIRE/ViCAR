Require Import Setoid.
Require MCDefinitions MCbw MCconsequences Lia.

Section monarrlist_theory.

Set Universe Polymorphism.

Import MCDefinitions MC_setoids MCbw 
  MCconsequences MC_notations MCClasses UIP_facts.
Import CategoryTypeclass.

Open Scope bw_scope.

Context {X : Type} {UIPX : UIP X}.
Context {cC : Category X} {cCh : CategoryCoherence cC} 
  {mC : MonoidalCategory cC} {mCh : MonoidalCategoryCoherence mC}.

Local Notation bw := (bw X).
Local Notation "a ⟶ b" := (@monarr X cC mC a b) (at level 60).

Section monarr_norm_equiv_theory.

Definition monarr_norm_equiv {a a' b b' : bw}
  (f : a ⟶ a') (g : b ⟶ b') : Prop :=
  exists (Hin : Nf b = Nf a) (Hout : Nf a' = Nf b'),
  bwarr_of_Nf_eq Hin ◌ f ◌ bwarr_of_Nf_eq Hout ≊ g.

Lemma monarr_norm_equiv_refl {a b : bw} : 
  reflexive _ (@monarr_norm_equiv a b a b).
Proof.
  intros f.
  exists eq_refl, eq_refl.
  rewrite monarr_id_l, monarr_id_r.
  easy.
Qed.

Lemma monarr_norm_equiv_symm {a a' b b' : bw} 
  (f : monarr a a') (g : monarr b b') : 
  monarr_norm_equiv f g -> monarr_norm_equiv g f.
Proof.
  intros (H & H' & Hequiv).
  exists (eq_sym H), (eq_sym H').
  rewrite <- Hequiv.
  rewrite <- 2!monarr_assoc, monarr_arrcomp, monarr_id_r.
  rewrite monarr_assoc, monarr_arrcomp, monarr_id_l.
  easy.
Qed.

Lemma monarr_norm_equiv_symmetric {a a' b b' : bw} 
  (f : monarr a a') (g : monarr b b') : 
  monarr_norm_equiv f g <-> monarr_norm_equiv g f.
Proof.
  split; apply monarr_norm_equiv_symm.
Qed.

Lemma monarr_norm_equiv_trans {a a' b b' c c' : bw} 
  {f : monarr a a'} {g : monarr b b'} {h : monarr c c'} :
  monarr_norm_equiv f g -> monarr_norm_equiv g h ->
  monarr_norm_equiv f h.
Proof.
  rewrite (monarr_norm_equiv_symmetric f g), 
    (monarr_norm_equiv_symmetric g h).
  intros (Hab & Hba' & Hgf) (Hbc & Hcb' & Hhg).
  exists (eq_sym (eq_trans Hab Hbc)), (eq_sym (eq_trans Hcb' Hba')).
  rewrite <- Hgf, <- Hhg.
  rewrite <- 4!monarr_assoc, 2!monarr_arrcomp, monarr_id_r.
  rewrite 2!monarr_assoc, 2!monarr_arrcomp, monarr_id_l.
  easy.
Qed.

Lemma monarr_norm_equiv_trans' {a b a' b' c d c' d' : bw} 
  {f : monarr a b} {f' : monarr a' b'} 
  {g : monarr c d} {g' : monarr c' d'} 
  (Hf : monarr_norm_equiv f f')
  (Hg : monarr_norm_equiv g g')
  (Hfg : monarr_norm_equiv f' g') :
  monarr_norm_equiv f g.
Proof.
  exact (monarr_norm_equiv_trans
    (monarr_norm_equiv_trans Hf Hfg) 
    (monarr_norm_equiv_symm _ _ Hg)).
Qed.

#[global] Add Parametric Relation {a b : bw} : (a ⟶ b) (@monarr_norm_equiv a b a b)
  reflexivity proved by monarr_norm_equiv_refl
  symmetry proved by monarr_norm_equiv_symm
  transitivity proved by (fun _ _ _ => monarr_norm_equiv_trans)
  as monarr_norm_equiv_rel.

#[global] Add Parametric Morphism {a a' b b' : bw} : (@monarr_norm_equiv a a' b b')
  with signature
  monarrequiv a a' ==> monarrequiv b b' ==> iff
  as monarr_norm_equiv_mor.
Proof.
  intros ? ? H ? ? H'.
  unfold monarr_norm_equiv.
  setoid_rewrite H.
  setoid_rewrite H'.
  easy.
Qed.

#[export] Instance monarr_norm_equiv_subrel (a b : bw) : 
  subrelation (@monarr_norm_equiv a b a b) (monarrequiv a b).
Proof.
  intros f g (? & ? & <-).
  now rewrite monarr_id_l, monarr_id_r.
Qed.

#[export] Instance subrel_monarr_norm_equiv (a b : bw) : 
  subrelation (monarrequiv a b) (@monarr_norm_equiv a b a b).
Proof.
  intros f g ->.
  easy.
Qed.

Lemma monarr_norm_equiv_of_monarrequiv {a b} 
  {f g : a ⟶ b} (H : f ≊ g) : 
  monarr_norm_equiv f g.
Proof.
  exists eq_refl, eq_refl; now rewrite monarr_id_l, monarr_id_r.
Qed.

Lemma Nf_eq_in_of_norm_equiv {a a' b b' : bw}
  {f : a ⟶ a'} {g : b ⟶ b'} :
  monarr_norm_equiv f g -> Nf a = Nf b.
Proof.
  intros (? & _ & _); easy.
Qed.

Lemma Nf_eq_out_of_norm_equiv {a a' b b' : bw}
  {f : monarr a a'} {g : monarr b b'} :
  monarr_norm_equiv f g -> Nf a' = Nf b'.
Proof.
  intros (_ & ? & _); easy.
Qed.

Lemma monarr_norm_equiv_struct_l {a b c : bw} (f : bwarr a b) (g : b ⟶ c) : 
  monarr_norm_equiv (monarrcomp f g) g.
Proof.
  exists (eq_sym (Nf_eq_of_arr f)), eq_refl.
  rewrite monarr_id_r.
  rewrite monarr_assoc, monarr_arrcomp, monarr_id_l.
  easy.
Qed.

Lemma monarr_norm_equiv_struct_r {a b c : bw} (f : a ⟶ b) (g : bwarr b c) : 
  monarr_norm_equiv (monarrcomp f g) f.
Proof.
  exists eq_refl, (eq_sym (Nf_eq_of_arr g)).
  rewrite monarr_id_l.
  rewrite <- monarr_assoc, monarr_arrcomp, monarr_id_r.
  easy.
Qed.

Lemma monarr_norm_equiv_struct_l_iff {a b c m n : bw} 
  (f : bwarr a b) (g : b ⟶ c) (h : m ⟶ n) : 
  monarr_norm_equiv (monarrcomp f g) h <-> monarr_norm_equiv g h.
Proof.
  split; intros (H & H' & Hrw).
  - exists (eq_trans H (Nf_eq_of_arr f)), H'.
    rewrite monarr_assoc, monarr_arrcomp in Hrw.
    erewrite monarr_struct.
    apply Hrw.
  - exists (eq_trans H (eq_sym (Nf_eq_of_arr f))), H'.
    rewrite monarr_assoc, monarr_arrcomp.
    erewrite monarr_struct.
    apply Hrw.
Qed.

Lemma monarr_norm_equiv_struct_r_iff {a b c m n : bw} 
  (f : bwarr b c) (g : a ⟶ b) (h : m ⟶ n) : 
  monarr_norm_equiv (monarrcomp g f) h <-> monarr_norm_equiv g h.
Proof.
  split; intros (H & H' & Hrw).
  - exists H, (eq_trans (Nf_eq_of_arr f) H').
    rewrite <- 2!monarr_assoc, monarr_arrcomp, monarr_assoc in Hrw.
    rewrite <- Hrw.
    eauto with monarrdb.
  - exists H, (eq_trans (eq_sym (Nf_eq_of_arr f)) H').
    rewrite <- 2!monarr_assoc, monarr_arrcomp.
    rewrite <- Hrw.
    eauto with monarrdb.
Qed.

Lemma monarr_norm_equiv_struct_l'_iff {a b c m n : bw} 
  (f : bwarr a b) (g : b ⟶ c) (h : m ⟶ n) : 
  monarr_norm_equiv h (monarrcomp f g) <-> monarr_norm_equiv h g.
Proof.
  rewrite monarr_norm_equiv_symmetric, monarr_norm_equiv_struct_l_iff.
  apply monarr_norm_equiv_symmetric.
Qed.

Lemma monarr_norm_equiv_struct_r'_iff {a b c m n : bw} 
  (f : bwarr b c) (g : a ⟶ b) (h : m ⟶ n) : 
  monarr_norm_equiv h (monarrcomp g f) <-> monarr_norm_equiv h g.
Proof.
  rewrite monarr_norm_equiv_symmetric, monarr_norm_equiv_struct_r_iff.
  apply monarr_norm_equiv_symmetric.
Qed.

Lemma monarr_norm_equiv_conj_struct_iff {a b c d m n : bw} 
  (f : bwarr a b) (g : b ⟶ c) (f' : bwarr c d) (h : m ⟶ n) :
  monarr_norm_equiv (f ◌ g ◌ f') h <-> monarr_norm_equiv g h.
Proof.
  now rewrite monarr_norm_equiv_struct_r_iff, monarr_norm_equiv_struct_l_iff.
Qed.

Lemma monarr_norm_equiv_conj_struct'_iff {a b c d m n : bw} 
  (f : bwarr a b) (g : b ⟶ c) (f' : bwarr c d) (h : m ⟶ n) :
  monarr_norm_equiv h (f ◌ g ◌ f') <-> monarr_norm_equiv h g.
Proof.
  now rewrite monarr_norm_equiv_symmetric,
    monarr_norm_equiv_conj_struct_iff, monarr_norm_equiv_symmetric.
Qed.

Lemma monarr_norm_equiv_comp {a a' a'' b b' b''} 
  (f : a ⟶ a') (f' : a' ⟶ a'') 
  (g : b ⟶ b') (g' : b' ⟶ b'') : 
  monarr_norm_equiv f g ->
  monarr_norm_equiv f' g' ->
  monarr_norm_equiv (f ◌ f') (g ◌ g'). 
Proof.
  intros (Hin & Hout & Hfg) (Hin' & Hout' & Hfg').
  rewrite <- Hfg, <- Hfg'.
  rewrite monarr_assoc, monarr_norm_equiv_struct_r'_iff.
  rewrite <- 2!monarr_assoc, monarr_norm_equiv_struct_l'_iff.
  rewrite (monarr_assoc (monarrstruct _)), monarr_arrcomp, monarr_id_l.
  apply monarr_norm_equiv_refl.
Qed.

Lemma monarr_norm_equiv_tens {a a' b b' c c' d d'} 
  (f : monarr a a') (f' : monarr b b') 
  (g : monarr c c') (g' : monarr d d') : 
  monarr_norm_equiv f g ->
  monarr_norm_equiv f' g' ->
  monarr_norm_equiv (monarrtens f f') (monarrtens g g'). 
Proof.
  intros (Hin & Hout & Hfg) (Hin' & Hout' & Hfg').
  rewrite <- Hfg, <- Hfg'.
  rewrite 2!monarr_tens_comp, 2!monarr_arrtens.
  rewrite monarr_norm_equiv_conj_struct'_iff.
  reflexivity.
Qed.

Lemma monarr_norm_equiv_arrid_e {a b} (hd : a ⟶ b) : 
  monarr_norm_equiv (arrid e) hd ->
  forall (g : bwarr a b), hd ≊ g.
Proof.
  intros (Ha & Hb & Hhid).
  intros g.
  rewrite <- Hhid.
  rewrite !monarr_arrcomp.
  apply monarr_struct.
Qed.

Lemma monarrequiv_iff_monarr_norm_equiv {a b} (f g : a ⟶ b) : 
  f ≊ g <-> monarr_norm_equiv f g.
Proof.
  split; [intros ->; easy|].
  intros (? & ? & <-).
  now rewrite monarr_id_l, monarr_id_r.
Qed.

Lemma monarr_norm_equiv_of_Nfs_eq_equiv {a b a' b'} {f : a ⟶ b} {g : a' ⟶ b'}
  (Ha : Nf a = Nf a') (Hb : Nf b = Nf b') :
    f ≊ bwarr_of_Nf_eq Ha ◌ g ◌ bwarr_of_Nf_eq (eq_sym Hb)
  -> monarr_norm_equiv f g.
Proof.
  intros H; symmetry in H; apply monarr_norm_equiv_symmetric.
  eexists; eexists; eauto.
Qed.

Lemma monarr_norm_equiv_tens_bwarr_e_l {a b c} (f : a ⟶ b) (h : bwarr e c) : 
  monarr_norm_equiv (h ⧆ f) f.
Proof.
  exists eq_refl, (f_equal (⟦ b ⟧) (eq_sym (Nf_eq_of_arr h))).
  rewrite (monarr_struct _ (h ^- ⊠ arrid b ○ arrlunitor b)).
  rewrite <- monarr_arrcomp, <- monarr_assoc, (monarr_assoc (h ⧆ f)).
  rewrite <- monarr_arrtens, <- monarr_tens_comp, monarr_struct_inv.
  rewrite monarr_id_r, monarr_lunitor_nat_r, monarr_assoc.
  now rewrite monarr_arrcomp, monarr_id_l.
Qed.

Lemma monarr_norm_equiv_tens_bwarr_e_r {a b c} (f : a ⟶ b) (h : bwarr e c) : 
  monarr_norm_equiv (f ⧆ h) f.
Proof.
  exists eq_refl.
  unshelve (eexists).
  - rewrite Nf_tens_bwnormapp, <- (Nf_eq_of_arr h).
    easy.
  - rewrite (monarr_struct _ (arrid b ⊠ h ^- ○ arrrunitor b)).
    rewrite <- monarr_arrcomp, <- monarr_assoc, (monarr_assoc (f ⧆ h)).
    rewrite <- monarr_arrtens, <- monarr_tens_comp, monarr_struct_inv.
    rewrite monarr_id_r, monarr_runitor_nat_r, monarr_assoc.
    now rewrite monarr_arrcomp, monarr_id_l.
Qed.

Lemma monarr_norm_equiv_tens_assoc {a b c d m n}
  (f : a ⟶ b) (g : c ⟶ d) (h : m ⟶ n) :
  monarr_norm_equiv (f ⧆ g ⧆ h) (f ⧆ (g ⧆ h)).
Proof.
  rewrite <- (monarr_norm_equiv_struct_r'_iff (arrassoc _ _ _)).
  rewrite monarr_assoc_nat_r.
  apply monarr_norm_equiv_struct_l'_iff.
  easy.
Qed.

Lemma monarr_norm_equiv_struct_eq_in 
  {a b a' b'} (f : bwarr a b) (g : bwarr a' b')
  (H : Nf a = Nf a') :
  monarr_norm_equiv f g.
Proof.
  exists (eq_sym H), 
    (eq_trans (eq_trans (eq_sym (Nf_eq_of_arr f)) H) (Nf_eq_of_arr g)).
  rewrite !monarr_arrcomp; apply monarr_struct.
Qed.

Lemma monarr_norm_equiv_struct_eq_out
  {a b a' b'} (f : bwarr a b) (g : bwarr a' b')
  (H : Nf b = Nf b') :
  monarr_norm_equiv f g.
Proof.
  exists 
    (eq_sym (eq_trans (eq_trans (Nf_eq_of_arr f) H) 
      (eq_sym (Nf_eq_of_arr g)))), H.
  rewrite !monarr_arrcomp; apply monarr_struct.
Qed.

Lemma equiv_conj_of_monarr_norm_equiv {a b m n} (f : a ⟶ b)
  (g : m ⟶ n) (h : bwarr a m) (h' : bwarr n b) :
  monarr_norm_equiv f g ->
  f ≊ h ◌ g ◌ h'.
Proof.
  rewrite monarr_norm_equiv_symmetric.
  intros (Hin & Hout & Hfg).
  rewrite <- Hfg.
  eauto with monarrdb.
Qed.

End monarr_norm_equiv_theory.

Section monarrlist_definitions.

Import List ListNotations.

#[universes(polymorphic=yes,cumulative=yes)]
Inductive monarrlistelt :=
  | monarrlist_id (a : bw) : monarrlistelt
  | monarrlist_arr (a b : bw) (f : a ⟶ b) : monarrlistelt.

Definition source (f : monarrlistelt) : bw := 
  match f with
  | monarrlist_id a => a
  | monarrlist_arr a b g => a
  end.

Definition target (f : monarrlistelt) : bw := 
  match f with
  | monarrlist_id a => a
  | monarrlist_arr a b g => b
  end.

Definition realize_monarrlistelt (f : monarrlistelt) : 
  monarr (source f) (target f) :=
  match f with
  | monarrlist_id a => arrid a
  | monarrlist_arr a b g => g
  end.

Definition monarrlist := (list monarrlistelt).

Definition monarrlist_source (f : monarrlist) : bw :=
  fold_right (fun a n => tens n a) e (map source f).

Definition monarrlist_target (f : monarrlist) : bw :=
  fold_right (fun a n => tens n a) e (map target f).

Definition source_vars (fs : monarrlist) := 
  flat_map (Basics.compose bw_to_varlist source) fs.

Definition target_vars (fs : monarrlist) := 
  flat_map (Basics.compose bw_to_varlist target) fs.

Fixpoint stack_monarrlist (f : monarrlist) : 
  monarr (monarrlist_source f) (monarrlist_target f) :=
  match f with
  | nil => arrid norm_e
  | mae :: f' => 
      monarrtens 
        (stack_monarrlist f') 
        (realize_monarrlistelt mae)
  end.

Definition composable (fs gs : monarrlist) :=
  Nf (monarrlist_target fs) = Nf (monarrlist_source gs).

Definition compose_composable_monarr {a a' b b'}
  (f : a ⟶ a') (g : b ⟶ b') 
  (H : Nf a' = Nf b) :=
  f ◌ bwarr_of_Nf_eq H ◌ g.

Definition compose_composable (fs gs : monarrlist)
  (H : composable fs gs) :=
  stack_monarrlist fs ◌ bwarr_of_Nf_eq H
  ◌ stack_monarrlist gs.

Definition monarrlistelt_map (f : forall a b : bw, a ⟶ b -> a ⟶ b) 
  (g : monarrlistelt) := 
  match g with
  | monarrlist_id a => monarrlist_id a
  | monarrlist_arr a b g' => monarrlist_arr a b (f a b g')
  end.

Definition monarrlist_list_source (fss : list monarrlist) : bw :=
  match fss with 
  | nil => e
  | fs :: fss' => monarrlist_source fs
  end.

Fixpoint monarrlist_list_target (fss : list monarrlist) : bw :=
  match fss with 
  | nil => e
  | fs :: nil => monarrlist_target fs
  | fs :: fss' => monarrlist_list_target fss'
  end.

Fixpoint totally_composable_helper 
  (fst : monarrlist) (fss : list monarrlist) :=
  match fss with 
  | nil => True
  | fst' :: fss' => composable fst fst' /\ 
      totally_composable_helper fst' fss'
  end.

Definition totally_composable (fss : list monarrlist) :=
  match fss with
  | nil => True
  | fst :: fss' => totally_composable_helper fst fss'
  end.

Fixpoint compose_totally_composable_helper
  fs (fss : list monarrlist) : totally_composable_helper fs fss ->
  (monarrlist_list_source (fs::fss)) ⟶ (monarrlist_list_target (fs :: fss)) :=
  match fss with
  | nil => fun _ => stack_monarrlist fs
  | fs' :: fss =>
    fun H => 
    compose_composable_monarr
      (stack_monarrlist fs)
      (compose_totally_composable_helper fs' fss (proj2 H))
      (proj1 H)
  end.

Definition compose_totally_composable
  (fss : list monarrlist) : totally_composable fss ->
  monarr
    (monarrlist_list_source fss)
    (monarrlist_list_target fss) :=
  match fss with
  | nil => fun _ => arrid e
  | fs :: fss' =>
    compose_totally_composable_helper fs fss'
  end.

Definition zip_with_default_l {A B C} (f : A -> B -> C)
  (xs : list A) (ydef : B) : list C :=
  map (fun x => f x ydef) xs.

Definition zip_with_default_r {A B C} (f : A -> B -> C)
  (xdef : A) (ys : list B) : list C :=
  map (f xdef) ys.

Fixpoint zip_defaults {A B C} (f : A -> B -> C)
  (xs : list A) (ys : list B) (xdef : A) (ydef : B) : list C :=
  match xs, ys with
  | nil, ys' => zip_with_default_r f xdef ys'
  | xs', nil => zip_with_default_l f xs' ydef
  | x::xs', y::ys' => (f x y) :: zip_defaults f xs' ys' xdef ydef
  end.

Definition monarrlistelt_equiv (f g : monarrlistelt) :=
  monarr_norm_equiv 
    (realize_monarrlistelt f)
    (realize_monarrlistelt g).

Fixpoint ForallF {A} (P : A -> Prop) (l : list A) : Prop :=
  match l with
  | nil => True
  | a :: l' => P a /\ ForallF P l'
  end.
  
Definition all_monarrlist_equiv (fs gs : monarrlist) :=
  ForallF (uncurry monarrlistelt_equiv) 
    (zip_defaults pair fs gs (monarrlist_id e) (monarrlist_id e)).

Definition all_monarrlist_list_equiv (fss gss : list monarrlist) :=
  ForallF (uncurry all_monarrlist_equiv)
    (zip_defaults pair fss gss nil nil).

End monarrlist_definitions.

Import List ListNotations.

(* Notation monarrlist := (list monarrlistelt). *)

Section composable_theory.

Lemma composable_iff_bweq (fs gs : monarrlist) :
  composable fs gs <-> bweq (monarrlist_target fs) (monarrlist_source gs).
Proof.
  apply Nf_eq_iff_bweq.
Qed.

Lemma composable_iff_varlist_eq (fs gs : monarrlist) : 
  composable fs gs <-> target_vars fs = source_vars gs.
Proof.
  unfold composable.
  rewrite Nf_eq_iff_varlist_eq.
  unfold monarrlist_target, monarrlist_source.
  rewrite 2!bw_to_varlist_fold_right.
  rewrite 2!map_map.
  rewrite <- 2!flat_map_concat_map.
  easy.
Qed.

Lemma composable_of_app_composable {fs fs' gs gs' : monarrlist} : 
  composable (fs ++ fs') (gs ++ gs') ->
  composable fs gs -> composable fs' gs'.
Proof.
  rewrite 3!composable_iff_varlist_eq.
  unfold source_vars, target_vars.
  rewrite 2!flat_map_app.
  intros H H'.
  rewrite H' in H.
  apply app_inv_head in H.
  easy.
Qed.

Lemma composable_independence {fs gs : monarrlist} (H H' : composable fs gs) :
  H = H'.
Proof. apply uip. Qed.

Lemma compose_composable_indep {fs gs : monarrlist} (H H' : composable fs gs) :
  compose_composable fs gs H = compose_composable fs gs H'.
Proof.
  f_equal; apply uip.
Qed.

Lemma compose_composable_monarr_indep {a a' b b'}
  (fs : a ⟶ b) (gs : a' ⟶ b') (H G : Nf b = Nf a') :
  compose_composable_monarr fs gs H = 
  compose_composable_monarr fs gs G.
Proof.
  f_equal; apply uip.
Qed.

#[global] Add Parametric Morphism (a a' b b' : bw) : 
  (@compose_composable_monarr a a' b b')
  with signature 
  (monarrequiv a a') ==> (monarrequiv b b') ==> true_rel ==> 
  (monarrequiv a b') as compose_composable_monarr_mor.
Proof.
  intros f f' Hf g g' Hg H1 H2 _.
  unfold compose_composable_monarr.
  apply monarr_comp; [apply monarr_comp|]; 
  assumption + apply monarr_struct.
Qed.

Lemma forall_composable_map {f} (Hc : forall fs gs, 
  composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs))) 
  {fsgs} (Hfsgs : Forall (uncurry composable) fsgs) : 
  Forall (uncurry composable) (map (uncurry f) fsgs).
Proof.
  induction fsgs as [|[g g'] fsgs IHfsgs]; [easy|].
  simpl.
  inversion Hfsgs; subst.
  constructor; [|apply IHfsgs; assumption].
  - rewrite (surjective_pairing (f g g')).
    apply Hc; assumption.
Qed.


Lemma totally_composable_of_cons {fst : monarrlist} {fss : list monarrlist} : 
  totally_composable (fst :: fss) -> totally_composable fss.
Proof.
  destruct fss; easy + intros H; apply H.
Qed.

Lemma totally_composable_indep (fss : list monarrlist) 
  (H G : totally_composable fss) : H = G.
Proof.
  induction fss; [now destruct H, G|].
  destruct fss; [now destruct H, G|].
  simpl in H, G.
  destruct H, G.
  f_equal.
  * apply uip.
  * apply IHfss.
Qed.

Lemma compose_totally_composable_indep 
  (fss : list monarrlist) (H G : totally_composable fss) :
  compose_totally_composable fss H = 
  compose_totally_composable fss G.
Proof.
  rewrite (totally_composable_indep fss H G).
  easy.
Qed.

Lemma totally_composable_app_restrict_r {fsts fss} :
  totally_composable (fsts ++ fss) ->
  totally_composable fss.
Proof.
  destruct fss; [easy|].
  induction fsts; [easy|].
  intros H; apply IHfsts.
  simpl in H.
  destruct fsts; apply H.
Qed.

Lemma totally_composable_app_restrict_l {fsts fss} :
  totally_composable (fsts ++ fss) ->
  totally_composable fsts.
Proof.
  (* destruct fss; [rewrite app_nil_r; easy|]. *)
  induction fsts; [easy|].
  destruct fsts; [easy|]. 
  intros H; split.
  - apply H.
  - apply IHfsts, H.
Qed.

Lemma middle_arr_composable_of_totally_composable 
  {a b fss fss'} (H : totally_composable ((a :: fss) ++ (b :: fss'))) : 
  Nf (monarrlist_list_target (a :: fss)) 
  = Nf (monarrlist_list_source (b :: fss')).
Proof.
  simpl monarrlist_list_source.
  revert a H;
  induction fss as [|fst fss IHfss];
  intros a H; [apply H|].
  simpl totally_composable in *.
  specialize (IHfss _ (proj2 H)).
  apply IHfss.
Qed.

Lemma monarrlist_list_target_app {fss b fss'} :
  monarrlist_list_target (fss ++ b :: fss') =
  monarrlist_list_target (b :: fss').
Proof.
  induction fss; [easy|].
  destruct fss;
  apply IHfss.
Qed.

Lemma monarrlist_list_source_app fss fss' :
  monarrlist_list_source (fss ++ fss') =
  match fss with
  | nil => monarrlist_list_source fss'
  | x::_ => monarrlist_source x
  end.
Proof.
  destruct fss; easy.
Qed.

Lemma Nf_monarrlist_source_app hd tl : 
  Nf (monarrlist_source (hd ++ tl)) = 
  bwnormapp (Nf (monarrlist_source tl))
    (Nf (monarrlist_source hd)).
Proof.
  unfold monarrlist_source.
  rewrite map_app.
  apply Nf_fold_right_tens.
Qed.

Lemma Nf_monarrlist_target_app hd tl : 
  Nf (monarrlist_target (hd ++ tl)) = 
  bwnormapp (Nf (monarrlist_target tl))
    (Nf (monarrlist_target hd)).
Proof.
  unfold monarrlist_target.
  rewrite map_app.
  apply Nf_fold_right_tens.
Qed.
  
Lemma Nf_monarrlist_source_app' hd tl : 
  Nf (monarrlist_source (hd ++ tl)) = 
  Nf (monarrlist_source tl ⨂ monarrlist_source hd).
Proof.
  rewrite Nf_tens_bwnormapp.
  apply Nf_monarrlist_source_app.
Qed.

Lemma Nf_monarrlist_target_app' hd tl : 
  Nf (monarrlist_target (hd ++ tl)) = 
  Nf (monarrlist_target tl ⨂ monarrlist_target hd).
Proof.
  rewrite Nf_tens_bwnormapp.
  apply Nf_monarrlist_target_app.
Qed.

Lemma composable_app {hd1 hd2 tl1 tl2}
  (Hh : composable hd1 hd2)
  (Ht : composable tl1 tl2) : 
  composable (hd1 ++ tl1) (hd2 ++ tl2).
Proof.
  unfold composable in *.
  rewrite Nf_monarrlist_source_app, Nf_monarrlist_target_app.
  f_equal; easy.
Qed.

Lemma app_composable_of_composable_mid {fss gss} 
  (Hf : totally_composable fss) (Hg : totally_composable gss) 
  (Hfg : Nf (monarrlist_list_target fss) = Nf (monarrlist_list_source gss)) :
  totally_composable (fss ++ gss).
Proof.
  induction fss.
  - apply Hg.
  - simpl.
    destruct fss.
    + simpl.
      destruct gss; [easy|].
      split;
      [apply Hfg|].
      apply Hg.
    + split;
      [apply Hf|].
      apply IHfss; [apply Hf|].
      apply Hfg.
Qed.

Lemma zip_defaults_cons {A B C} (f : A -> B -> C) x y xs ys xdef ydef :
  zip_defaults f (x :: xs) (y :: ys) xdef ydef =
  (f x y) :: zip_defaults f xs ys xdef ydef.
Proof.
  easy.
Qed.

Lemma monarrlist_list_target_cons_cons f f' fs :
  monarrlist_list_target (f :: f' :: fs) = monarrlist_list_target (f' :: fs).
Proof.
  easy.
Qed.

Lemma middle_arr_composable_of_totally_composable_nonempty 
  {fss fss'} (H : totally_composable (fss ++ fss')) 
  (Hfss : fss <> []) (Hfss' : fss' <> []) : 
  Nf (monarrlist_list_target fss)
  = Nf (monarrlist_list_source fss').
Proof.
  destruct fss, fss'; [easy..|].
  apply middle_arr_composable_of_totally_composable; assumption.
Qed.

Lemma monarrlist_list_source_app_not_nil {fss} (H : fss <> []) gss : 
  monarrlist_list_source (fss ++ gss) = monarrlist_list_source fss.
Proof.
  rewrite monarrlist_list_source_app.
  destruct fss; easy.
Qed.

Lemma monarrlist_list_target_app_not_nil {gss} (H : gss <> []) fss : 
  monarrlist_list_target (fss ++ gss) = monarrlist_list_target gss.
Proof.
  destruct gss; [easy|].
  now rewrite monarrlist_list_target_app.
Qed.

Lemma monarrlist_target_singleton fss : 
  monarrlist_target [fss] = e ⨂ target fss.
Proof.
  easy.
Qed.

Lemma monarrlist_source_cons f fs :
  monarrlist_source (f :: fs) = monarrlist_source fs ⨂ source f.
Proof.
  easy.
Qed.

Lemma monarrlist_target_cons f fs :
  monarrlist_target (f :: fs) = monarrlist_target fs ⨂ target f.
Proof.
  easy.
Qed.

Lemma zip_with_default_l_totally_composable {fss} 
  (Hf : totally_composable fss) a :
  totally_composable 
    (zip_with_default_l (@app monarrlistelt) fss [monarrlist_id a]).
Proof.
  induction fss; [easy|destruct fss; [easy|]].
  split.
  - apply composable_app; [apply Hf | easy].
  - apply IHfss, Hf.
Qed.

Lemma zip_with_default_r_totally_composable {fss} 
  (Hf : totally_composable fss) a :
  totally_composable 
    (zip_with_default_r (@app monarrlistelt) [monarrlist_id a] fss).
Proof.
  induction fss; [easy|destruct fss; [easy|]].
  split.
  - apply composable_app; [easy | apply Hf].
  - apply IHfss, Hf.
Qed.

Lemma zip_with_default_l_source_nonempty {fss} (H : fss <> []) a :
  Nf (monarrlist_list_source (zip_with_default_l (@app monarrlistelt) fss a))
  = Nf (monarrlist_source a ⨂ monarrlist_list_source fss).
Proof.
  destruct fss; [easy|].
  apply Nf_monarrlist_source_app'.
Qed.

Lemma zip_with_default_l_target_nonempty {fss} (H : fss <> []) a :
  Nf (monarrlist_list_target (zip_with_default_l (@app monarrlistelt) fss a))
  = Nf (monarrlist_target a ⨂ monarrlist_list_target fss).
Proof.
  induction fss; [easy|].
  destruct fss; [apply Nf_monarrlist_target_app'|].
  apply IHfss; easy.
Qed.

Lemma zip_with_default_r_source_nonempty {fss} (H : fss <> []) a :
  Nf (monarrlist_list_source (zip_with_default_r (@app monarrlistelt) a fss))
  = Nf (monarrlist_list_source fss ⨂ monarrlist_source a).
Proof.
  destruct fss; [easy|].
  apply Nf_monarrlist_source_app'.
Qed.

Lemma zip_with_default_r_target_nonempty {fss} (H : fss <> []) a :
  Nf (monarrlist_list_target (zip_with_default_r (@app monarrlistelt) a fss))
  = Nf (monarrlist_list_target fss ⨂ monarrlist_target a).
Proof.
  induction fss; [easy|].
  destruct fss; [apply Nf_monarrlist_target_app'|].
  apply IHfss; easy.
Qed.

Lemma zip_defaults_target_nonempty {fss gss} (Hf : fss <> []) (Hg : gss <> []) : 
  Nf (monarrlist_list_target (zip_defaults (@app monarrlistelt)
    fss gss 
    [monarrlist_id (monarrlist_list_target fss)]
    [monarrlist_id (monarrlist_list_target gss)])) 
  = Nf (monarrlist_list_target gss ⨂ monarrlist_list_target fss).
Proof.
  revert gss Hg;
  induction fss; 
  intros gss Hg; [
  apply (zip_with_default_r_target_nonempty Hg)|]. 
  destruct fss.
  - destruct gss; [easy|].
    destruct gss; [apply Nf_monarrlist_target_app'|].
    rewrite zip_defaults_cons.
    change (?a :: ?l) with ((a::nil) ++ l).
    rewrite monarrlist_list_target_app_not_nil by easy.
    etransitivity.
    apply zip_with_default_r_target_nonempty; easy.
    rewrite monarrlist_list_target_app.
    easy.
  - destruct gss; [easy|].
    destruct gss.
    + rewrite zip_defaults_cons.
      change (?a :: ?l) with ((a::nil) ++ l).
      rewrite monarrlist_list_target_app_not_nil by easy.
      etransitivity.
      apply zip_with_default_l_target_nonempty; easy.
      rewrite monarrlist_list_target_app.
      easy.
    + rewrite zip_defaults_cons.
      change (?a :: ?l) with ((a::nil) ++ l).
      rewrite monarrlist_list_target_app_not_nil by easy.
      rewrite 2!monarrlist_list_target_cons_cons.
      etransitivity;
      [apply (IHfss ltac:(easy) (l1 :: gss) ltac:(easy))|].
      easy.
Qed.

Lemma zip_defaults_target_defaults_indep {fss gss df dg} 
  (Hf : fss <> []) (Hg : gss <> []) 
  (Hdf : Nf df = Nf (monarrlist_list_target fss))
  (Hdg : Nf dg = Nf (monarrlist_list_target gss)) : 
  Nf (monarrlist_list_target (zip_defaults (@app monarrlistelt)
    fss gss 
    [monarrlist_id df]
    [monarrlist_id dg])) 
  = Nf (monarrlist_list_target (zip_defaults (@app monarrlistelt)
    fss gss 
    [monarrlist_id (monarrlist_list_target fss)]
    [monarrlist_id (monarrlist_list_target gss)])).
Proof.
  revert gss Hg Hdg;
  induction fss; intros gss Hg Hdg; [induction gss; [easy|]|destruct gss].
  - destruct gss.
    + cbn -[app Nf].
      rewrite 2!Nf_monarrlist_target_app; f_equal.
      easy.
    + apply IHgss; easy.
  - destruct fss.
    + cbn -[monarrlist_target app Nf].
      rewrite 2!Nf_monarrlist_target_app; f_equal.
      easy.
    + refine (IHfss _ _ [] _ _); easy.
  - destruct fss.
    + cbn -[monarrlist_target app Nf].
      destruct gss; [easy|].
      simpl.
      etransitivity;
      [apply (zip_with_default_r_target_nonempty 
        (fss:=m0::gss) ltac:(easy))|
      etransitivity;
      [|symmetry; apply (zip_with_default_r_target_nonempty 
      (fss:=m0::gss) ltac:(easy))]].
      rewrite 2!Nf_tens_bwnormapp.
      f_equal; easy.
    + destruct gss.
      * simpl.
        etransitivity;
        [apply (zip_with_default_l_target_nonempty 
          (fss:=m0::fss) ltac:(easy))|
        etransitivity;
        [|symmetry; apply (zip_with_default_l_target_nonempty 
        (fss:=m0::fss) ltac:(easy))]].
        rewrite 2!Nf_tens_bwnormapp.
        f_equal; easy.
      * refine (IHfss _ _ (m1 :: gss) _ _); easy.
Qed.

Lemma zip_defaults_source_nonempty {fss gss} (Hf : fss <> []) (Hg : gss <> []) : 
  Nf (monarrlist_list_source (zip_defaults (@app monarrlistelt)
    fss gss 
    [monarrlist_id (monarrlist_list_target fss)]
    [monarrlist_id (monarrlist_list_target gss)])) 
  = Nf (monarrlist_list_source gss ⨂ monarrlist_list_source fss).
Proof.
  destruct fss, gss; try easy.
  apply Nf_monarrlist_source_app'.
Qed.

Lemma totally_composable_helper_swap {a b fss} :
  Nf (monarrlist_target a) = Nf (monarrlist_target b) ->
  totally_composable_helper a fss ->
  totally_composable_helper b fss.
Proof.
  intros Heq.
  destruct fss; [easy|].
  intros [Hl Hr].
  split; [|apply Hr].
  unfold composable in *.
  rewrite <- Heq.
  easy.
Qed.

End composable_theory.

Section composition_theory.

Lemma monarr_norm_equiv_comp_composable {a b c d a' b' c' d'}
  (f : a ⟶ b) (g : c ⟶ d) (f' : a' ⟶ b') (g' : c' ⟶ d') Hc Hc' :
  monarr_norm_equiv f f' ->
  monarr_norm_equiv g g' ->
  monarr_norm_equiv
    (compose_composable_monarr f g Hc)
    (compose_composable_monarr f' g' Hc').
Proof.
  intros Hf Hg.
  unfold compose_composable_monarr.
  apply monarr_norm_equiv_comp; 
  [apply monarr_norm_equiv_struct_r_iff, 
    monarr_norm_equiv_struct_r'_iff|];
  assumption.
Qed.

Lemma ForallFE {A} (P : A -> Prop) (l : list A) :
  ForallF P l = fold_right and True (map P l).
Proof.
  induction l; [easy|].
  simpl.
  f_equal; apply IHl.
Qed.

Lemma ForallF_iff_Forall {A} (P : A -> Prop) (l : list A) :
  ForallF P l <-> Forall P l.
Proof.
  induction l; [easy|].
  rewrite Forall_cons_iff, <- IHl.
  easy.
Qed.

Lemma zip_defaults_nil_r {A B C} (f : A -> B -> C) xs xdef ydef :
  zip_defaults f xs [] xdef ydef = 
  zip_with_default_l f xs ydef.
Proof.
  destruct xs; easy.
Qed.

Lemma stack_monarrlist_app' fs fss :
  monarr_norm_equiv 
    (stack_monarrlist (fs ++ fss))
    (stack_monarrlist fss ⧆ stack_monarrlist fs).
Proof.
  apply monarr_norm_equiv_symm.
  induction fs.
  - apply monarr_norm_equiv_tens_bwarr_e_r.
  - simpl.
    eapply monarr_norm_equiv_trans;
    [apply monarr_norm_equiv_symm, monarr_norm_equiv_tens_assoc|].
    apply monarr_norm_equiv_tens; easy.
Qed.

Lemma stack_monarrlist_app fs fss : 
  stack_monarrlist (fs ++ fss) 
  ≊ bwarr_of_Nf_eq (Nf_monarrlist_source_app' fs fss) ◌
    stack_monarrlist fss ⧆ stack_monarrlist fs ◌
    bwarr_of_Nf_eq (eq_sym (Nf_monarrlist_target_app' fs fss)).
Proof.
  apply equiv_conj_of_monarr_norm_equiv.
  apply stack_monarrlist_app'.
Qed.

Lemma tens_stack_monarrlist fs fss : 
  stack_monarrlist fss ⧆ stack_monarrlist fs
  ≊ bwarr_of_Nf_eq (eq_sym (Nf_monarrlist_source_app' fs fss)) ◌
    stack_monarrlist (fs ++ fss) ◌
    bwarr_of_Nf_eq (Nf_monarrlist_target_app' fs fss).
Proof.
  apply equiv_conj_of_monarr_norm_equiv.
  apply monarr_norm_equiv_symm.
  apply stack_monarrlist_app'.
Qed.



Lemma compose_composable_monarr_comp_l {a a' a'' b b'} (f : a ⟶ a')
  (g : a' ⟶ a'') (h : b ⟶ b') H :
  compose_composable_monarr (f ◌ g) h H ≊
  f ◌ compose_composable_monarr g h H.
Proof.
  unfold compose_composable_monarr.
  now rewrite !monarr_assoc.
Qed.

Lemma compose_composable_monarr_comp_r {a a' a'' b b'} (f : a ⟶ a')
  (g : a' ⟶ a'') (h : b ⟶ b') H :
  compose_composable_monarr h (f ◌ g) H ≊
  compose_composable_monarr h f H ◌ g.
Proof.
  unfold compose_composable_monarr.
  now rewrite !monarr_assoc.
Qed.

Lemma compose_composable_monarr_struct_l' {a a' a'' b b'} (f : bwarr a a')
  (g : a' ⟶ a'') (h : b ⟶ b') H :
  compose_composable_monarr h (f ◌ g) H ≊
  compose_composable_monarr h g (eq_trans H (Nf_eq_of_arr f)).
Proof.
  unfold compose_composable_monarr.
  rewrite !monarr_assoc.
  apply monarr_comp; [|easy].
  rewrite <- monarr_assoc, monarr_arrcomp.
  auto with monarrdb.
Qed.

Lemma compose_composable_monarr_struct_r {a a' a'' b b'} (f : a ⟶ a')
  (g : bwarr a' a'') (h : b ⟶ b') H :
  compose_composable_monarr (f ◌ g) h H ≊
  compose_composable_monarr f h (eq_trans (Nf_eq_of_arr g) H).
Proof.
  unfold compose_composable_monarr.
  apply monarr_comp; [|easy].
  rewrite <- monarr_assoc, monarr_arrcomp.
  auto with monarrdb.
Qed.

Lemma compose_totally_composable_cons
  {a b fss} (H : totally_composable (a :: b :: fss)) : 
  (compose_totally_composable _ H)
  ≊
  compose_composable_monarr (stack_monarrlist a)
    (compose_totally_composable (b::fss) (proj2 H))
    (proj1 H).
Proof.
  revert a b H.
  induction fss as [|fst fss IHfss];
  intros a b H; [easy|].
  simpl in *.
  specialize (IHfss _ _ (proj2 H)).
  easy.
Qed.

Lemma compose_totally_composable_app_helper
  {a b fss fss'} (H : totally_composable ((a :: fss) ++ (b :: fss'))) : 
  monarrequiv _ _ 
    (compose_totally_composable _ H)
    (monarrcomp
      (compose_composable_monarr
        (compose_totally_composable (a :: fss)
          (totally_composable_app_restrict_l H))
        (compose_totally_composable (b :: fss')
          (totally_composable_app_restrict_r H))
        (middle_arr_composable_of_totally_composable H))
      (cast_bwarr eq_refl (eq_sym monarrlist_list_target_app) (arrid _))).
Proof.
  revert a H;
  induction fss as [|fst fss IHfss]; 
  intros a H.
  - simpl app.
    rewrite compose_totally_composable_cons.
    unfold compose_composable_monarr.
    rewrite <- !monarr_assoc.
    apply monarr_comp; [easy|].
    apply monarr_comp; [apply monarr_struct|].
    rewrite (monarr_struct _ (arrid _)), monarr_runit.
    erewrite compose_totally_composable_indep.
    reflexivity.
  - simpl app.
    rewrite compose_totally_composable_cons.
    unfold compose_composable_monarr.
    rewrite compose_totally_composable_cons.
    unfold compose_composable_monarr.
    rewrite <- !monarr_assoc.
    apply monarr_comp; [easy|].
    apply monarr_comp; [apply monarr_struct|].
    change (fst :: fss ++ b :: fss') with ((fst :: fss) ++ b :: fss').
    rewrite IHfss.
    unfold compose_composable_monarr.
    rewrite <- !monarr_assoc.
    repeat apply monarr_comp; 
    apply monarr_struct + 
    (erewrite compose_totally_composable_indep;
    reflexivity).
Qed.

Lemma compose_monarrlist_list_cancel_suffix_helper_nil
  hd fss 
  (H1 : totally_composable fss)
  (H2 : totally_composable (hd ++ fss))
  (Hh : totally_composable hd) : 
  monarr_norm_equiv 
    (arrid e)
    (compose_totally_composable 
      hd Hh) ->
  monarr_norm_equiv
    (compose_totally_composable _ H1)
    (compose_totally_composable _ H2).
Proof.
  destruct hd; [|destruct fss].
  - intros _.
    apply monarr_norm_equiv_of_monarrequiv.
    erewrite compose_totally_composable_indep.
    reflexivity.
  - revert H2.
    rewrite app_nil_r.
    intros H2.
    intros H.
    erewrite (compose_totally_composable_indep (_::hd)).
    apply H.
  - intros H.
    rewrite compose_totally_composable_app_helper.
    rewrite monarr_norm_equiv_struct_r'_iff.
    unfold compose_composable_monarr.
    rewrite <- monarr_lunit.
    apply monarr_norm_equiv_comp;
    [|erewrite compose_totally_composable_indep; easy].
    rewrite monarr_norm_equiv_struct_r'_iff.
    erewrite compose_totally_composable_indep.
    eapply monarr_norm_equiv_trans; [|apply H].
    apply monarr_norm_equiv_struct_eq_in.
    rewrite <- (middle_arr_composable_of_totally_composable H2).
    symmetry.
    apply (Nf_eq_out_of_norm_equiv H).
Qed.

Lemma compose_monarrlist_list_cancel_suffix_helper 
  hd1 hd2 fss 
  (H1 : totally_composable (hd1 ++ fss))
  (H2 : totally_composable (hd2 ++ fss))
  (H1h : totally_composable hd1)
  (H2h : totally_composable hd2) : 
  monarr_norm_equiv 
    (compose_totally_composable 
      hd1 H1h)
    (compose_totally_composable 
      hd2 H2h) ->
  monarr_norm_equiv
    (compose_totally_composable _ H1)
    (compose_totally_composable _ H2).
Proof.
  revert H1 H2.
  induction fss as [|fst fss].
  1: {
    rewrite 2!app_nil_r.
    intros H1 H2.
    rewrite (compose_totally_composable_indep _ H1 H1h).
    rewrite (compose_totally_composable_indep _ H2 H2h).
    easy.
  }
  destruct hd1.
  1: {
    clear IHfss.
    simpl app.
    simpl (compose_totally_composable [] _).
    intros H1 H2.
    apply compose_monarrlist_list_cancel_suffix_helper_nil.
  } 
  destruct hd2.
  1: {
    clear IHfss.
    simpl app.
    setoid_rewrite monarr_norm_equiv_symmetric.
    simpl (compose_totally_composable [] _).
    intros H1 H2.
    apply compose_monarrlist_list_cancel_suffix_helper_nil.
  }
  intros H1 H2.
  rewrite 2!compose_totally_composable_app_helper.
  intros (Hl & Hhd & Hequiv).
  clear IHfss.
  symmetry in Hequiv.
  erewrite compose_totally_composable_indep in Hequiv.
  rewrite Hequiv.
  rewrite monarr_norm_equiv_struct_r_iff, monarr_norm_equiv_struct_r'_iff.
  exists Hl, eq_refl. 
  rewrite monarr_id_r.
  rewrite compose_composable_monarr_struct_r, compose_composable_monarr_comp_l.
  apply monarr_comp; [easy|].
  apply compose_composable_monarr_mor; [..|easy];
  erewrite compose_totally_composable_indep; easy.
Qed.

Lemma compose_monarrlist_list_cancel_suffix
  hd1 hd2 fss 
  (H1 : totally_composable (hd1 ++ fss))
  (H2 : totally_composable (hd2 ++ fss)) : 
  monarr_norm_equiv 
    (compose_totally_composable 
      hd1 (totally_composable_app_restrict_l H1))
    (compose_totally_composable 
      hd2 (totally_composable_app_restrict_l H2)) ->
  monarr_norm_equiv
    (compose_totally_composable _ H1)
    (compose_totally_composable _ H2).
Proof.
  intros H.
  eapply compose_monarrlist_list_cancel_suffix_helper.
  apply H.
Qed.

Lemma compose_monarrlist_list_cancel_prefix_helper 
  hd1 hd2 fss 
  (H1 : totally_composable (fss ++ hd1))
  (H2 : totally_composable (fss ++ hd2))
  (H1h : totally_composable hd1)
  (H2h : totally_composable hd2) : 
  monarr_norm_equiv 
    (compose_totally_composable 
      hd1 H1h)
    (compose_totally_composable 
      hd2 H2h) ->
  monarr_norm_equiv
    (compose_totally_composable _ H1)
    (compose_totally_composable _ H2).
Proof.
  intros H.
  induction fss.
  - rewrite (compose_totally_composable_indep _ _ H1h).
    rewrite (compose_totally_composable_indep _ _ H2h).
    easy.
  - destruct fss.
    1: {
      destruct hd1, hd2.
      1: easy.
      1: {
        specialize (IHfss (Logic.I) (proj2 H2)).
        simpl app.
        rewrite compose_totally_composable_cons.
        rewrite <- monarr_runit.
        unfold compose_composable_monarr.
        apply monarr_norm_equiv_comp.
        - rewrite monarr_norm_equiv_struct_r'_iff.
          easy.
        - eapply monarr_norm_equiv_trans;
          [|apply IHfss].
          apply monarr_norm_equiv_struct_eq_in.
          simpl.
          rewrite (proj1 H2).
          apply Nf_eq_in_of_norm_equiv in H.
          symmetry; apply H.
      }
      1: {
        specialize (IHfss (proj2 H1) (Logic.I)).
        simpl app.
        rewrite compose_totally_composable_cons.
        apply monarr_norm_equiv_symm.
        rewrite <- monarr_runit.
        unfold compose_composable_monarr.
        apply monarr_norm_equiv_comp.
        - rewrite monarr_norm_equiv_struct_r'_iff.
          easy.
        - eapply monarr_norm_equiv_trans;
          [|apply monarr_norm_equiv_symm, IHfss].
          apply monarr_norm_equiv_struct_eq_in.
          simpl.
          rewrite (proj1 H1).
          apply (Nf_eq_in_of_norm_equiv H).
      }
      simpl app.
      rewrite 2!compose_totally_composable_cons.
      apply monarr_norm_equiv_comp_composable; [easy|].
      erewrite (compose_totally_composable_indep (m0 :: _)),
        compose_totally_composable_indep.
      apply H.
    } 
    simpl app.
    rewrite 2!compose_totally_composable_cons.
    apply monarr_norm_equiv_comp_composable; [easy|].
    apply IHfss.
Qed.

Lemma compose_monarrlist_list_cancel_prefix
  hd1 hd2 fss 
  (H1 : totally_composable (fss ++ hd1))
  (H2 : totally_composable (fss ++ hd2)) : 
  monarr_norm_equiv 
    (compose_totally_composable 
      hd1 (totally_composable_app_restrict_r H1))
    (compose_totally_composable 
      hd2 (totally_composable_app_restrict_r H2)) ->
  monarr_norm_equiv
    (compose_totally_composable _ H1)
    (compose_totally_composable _ H2).
Proof.
  intros H.
  eapply compose_monarrlist_list_cancel_prefix_helper.
  apply H.
Qed.

Lemma compose_totally_composable_app_nonempty
  {fss fss'} (H : totally_composable (fss ++ fss')) 
  (Hfss : fss <> []) (Hfss' : fss' <> []) : 
  compose_totally_composable _ H
  ≊ (cast_bwarr eq_refl 
    (monarrlist_list_source_app_not_nil Hfss _) (arrid _))
    ◌ (compose_composable_monarr
      (compose_totally_composable fss
        (totally_composable_app_restrict_l H))
      (compose_totally_composable fss'
        (totally_composable_app_restrict_r H))
      (middle_arr_composable_of_totally_composable_nonempty H Hfss Hfss'))
    ◌ (cast_bwarr eq_refl 
      (eq_sym (monarrlist_list_target_app_not_nil Hfss' _)) (arrid _)).
Proof.
  destruct fss, fss'; [easy..|].
  rewrite compose_totally_composable_app_helper.
  rewrite monarr_struct_id, monarr_lunit.
  apply monarr_comp; [|apply monarr_struct].
  erewrite compose_composable_monarr_indep.
  easy.
Qed.

End composition_theory.


Section monarrlist_equivalences.



Lemma all_monarrlist_cons_equiv_nil {a fs} : 
  all_monarrlist_equiv (a :: fs) [] ->
  all_monarrlist_equiv fs [].
Proof.
  unfold all_monarrlist_equiv.
  rewrite 2!zip_defaults_nil_r.
  simpl.
  easy.
Qed.

Lemma all_monarrlist_list_cons_equiv_nil {a fss} : 
  all_monarrlist_list_equiv (a :: fss) [] ->
  all_monarrlist_list_equiv fss [].
Proof.
  unfold all_monarrlist_list_equiv.
  rewrite 2!zip_defaults_nil_r.
  simpl.
  easy.
Qed.

Lemma stack_monarrlist_equiv {fs gs} 
  (H : all_monarrlist_equiv fs gs) : 
  monarr_norm_equiv 
    (stack_monarrlist fs)
    (stack_monarrlist gs).
Proof.
  revert gs H;
  induction fs; intros gs H.
  - induction gs.
    + apply monarr_norm_equiv_refl.
    + change [] with (@nil monarrlistelt ++ nil).
      rewrite stack_monarrlist_app.
      change (a :: gs) with ((a::nil) ++ gs).
      rewrite stack_monarrlist_app.
      rewrite monarr_norm_equiv_conj_struct_iff,
        monarr_norm_equiv_conj_struct'_iff.
      apply monarr_norm_equiv_tens;
      [apply IHgs, H|].
      destruct H.
      simpl.
      eapply monarr_norm_equiv_trans;
      [apply H|].
      apply monarr_norm_equiv_symm.
      apply monarr_norm_equiv_tens_bwarr_e_l.
  - destruct gs.
    + change [] with (@nil monarrlistelt ++ nil).
      change (a :: fs) with ((a::nil) ++ fs).
      rewrite 2!stack_monarrlist_app.
      rewrite monarr_norm_equiv_conj_struct_iff, 
        monarr_norm_equiv_conj_struct'_iff.
      apply monarr_norm_equiv_tens;
      [apply IHfs, (all_monarrlist_cons_equiv_nil H)|].
      eapply monarr_norm_equiv_trans;
      [| apply H].
      apply monarr_norm_equiv_tens_bwarr_e_l.
    + apply monarr_norm_equiv_tens;
      [apply IHfs, H|].
      apply H.
Qed.

Lemma compose_composable_app_helper {fs gs} 
  (Hfg : composable fs gs) {fss gss} 
  (Hfsgs : composable (fs ++ fss) (gs ++ gss))
  (Hfssgss : composable fss gss) : 
  monarr_norm_equiv 
    (compose_composable (fs ++ fss) (gs ++ gss) Hfsgs)
    (monarrtens 
      (compose_composable fss gss Hfssgss)
      (compose_composable fs gs Hfg)).
Proof.
  unfold compose_composable.
  rewrite 2!monarr_tens_comp.
  rewrite 2!tens_stack_monarrlist.
  rewrite <- !monarr_assoc.
  rewrite monarr_norm_equiv_struct_l'_iff.
  apply monarr_norm_equiv_comp; [easy|].
  rewrite monarr_arrtens.
  rewrite !monarr_norm_equiv_struct_l'_iff,
    monarr_norm_equiv_struct_l_iff,
    monarr_norm_equiv_struct_r'_iff.
  easy.
Qed.

Lemma compose_composable_app {fs gs} 
  (Hfg : composable fs gs) {fss gss} 
  (Hfsgs : composable (fs ++ fss) (gs ++ gss)): 
  monarr_norm_equiv 
    (compose_composable (fs ++ fss) (gs ++ gss) Hfsgs)
    (monarrtens 
      (compose_composable fss gss 
        (composable_of_app_composable Hfsgs Hfg))
      (compose_composable fs gs Hfg)).
Proof.
  apply compose_composable_app_helper.
Qed.

Lemma monarrlistelt_equiv_refl : 
  Reflexive monarrlistelt_equiv.
Proof.
  intros a;
  apply monarr_norm_equiv_refl.
Qed.

Lemma monarrlistelt_equiv_symm : 
  Symmetric monarrlistelt_equiv.
Proof.
  intros a b;
  apply monarr_norm_equiv_symm.
Qed.

Lemma monarrlistelt_equiv_trans : 
  Transitive monarrlistelt_equiv.
Proof.
  intros a b c;
  apply monarr_norm_equiv_trans.
Qed.


Lemma monarrlist_equiv_refl :
  Reflexive all_monarrlist_equiv.
Proof.
  intros f.
  induction f; [easy|].
  split; [apply monarrlistelt_equiv_refl|].
  apply IHf.
Qed.

Lemma monarrlist_equiv_symm :
  Symmetric all_monarrlist_equiv.
Proof.
  intros fss.
  induction fss; intros gss H; [|destruct gss].
  - induction gss; [easy|].
    split.
    + apply monarr_norm_equiv_symm, H. 
    + specialize (IHgss (proj2 H)).
      destruct gss;
      apply IHgss.
  - split.
    + apply monarr_norm_equiv_symm, H. 
    + apply (IHfss nil).
      destruct fss; apply H.
  - split.
    + apply monarr_norm_equiv_symm.
      apply H.
    + apply IHfss, H.
Qed.

Import Lia.

Lemma monarrlist_equiv_trans :
  Transitive all_monarrlist_equiv.
Proof.
  intros fs gs hs.
  remember (length fs + length gs + length hs) as k eqn:Heqk.
  assert (Hle : length fs + length gs + length hs <= k) by (subst; easy).
  clear Heqk.
  revert fs gs hs Hle.
  induction k;
  [intros [] [] []; easy|].
  intros [|f fs] [|g gs] [|h hs]; try reflexivity + (intros; assumption).
  - simpl.
    intros Hle Hnil Hgh.
    split.
    + eapply monarrlistelt_equiv_trans; [apply Hnil|].
      apply Hgh.
    + apply (IHk [] gs hs); [simpl; lia|apply Hnil|apply Hgh].
  - intros Hle Hnil Hgh.
    split.
    + eapply monarrlistelt_equiv_trans; [apply Hnil|].
      apply Hgh.
    + apply (IHk fs [] hs); [simpl in *; lia| |apply Hgh].
      apply (all_monarrlist_cons_equiv_nil Hnil).
  - intros Hle Hnil Hgh.
    split.
    + eapply monarrlistelt_equiv_trans; [apply Hnil|].
      apply Hgh.
    + pose proof (IHk fs gs [] ltac:(simpl in *;lia) (proj2 Hnil) 
        (all_monarrlist_cons_equiv_nil Hgh)) as e.
      destruct fs; apply e.
  - simpl.
    intros Hle Hfg Hgh.
    split.
    + eapply monarrlistelt_equiv_trans; [apply Hfg|apply Hgh].
    + apply (IHk fs gs hs); [lia|..].
      * apply Hfg.
      * apply Hgh.
Qed.


Lemma monarrlist_list_equiv_refl : 
  Reflexive all_monarrlist_list_equiv.
Proof.
  intros fss.
  induction fss; [easy|].
  split; [| apply IHfss].
  apply monarrlist_equiv_refl.
Qed.


Lemma monarrlist_list_equiv_symm : 
  Symmetric all_monarrlist_list_equiv.
Proof.
  intros fss.
  induction fss; intros gss H; [|destruct gss].
  - induction gss; [easy|].
    split.
    + apply monarrlist_equiv_symm, H. 
    + specialize (IHgss (proj2 H)).
      destruct gss;
      apply IHgss.
  - split.
    + apply monarrlist_equiv_symm, H. 
    + apply (IHfss nil).
      destruct fss; apply H.
  - split.
    + apply monarrlist_equiv_symm.
      apply H.
    + apply IHfss, H.
Qed.

Lemma monarrlist_list_equiv_trans:
  Transitive all_monarrlist_list_equiv.
Proof.
  intros fss gss hss.
  remember (length fss + length gss + length hss) as k eqn:Heqk.
  assert (Hle : length fss + length gss + length hss <= k) by lia.
  clear Heqk.
  revert fss gss hss Hle.
  induction k;
  [intros [] [] []; easy|].
  intros [|fs fss] [|gs gss] [|hs hss]; try reflexivity + (intros; assumption).
  - simpl.
    intros Hle Hnil Hgh.
    split.
    + eapply monarrlist_equiv_trans; [apply Hnil|].
      apply Hgh.
    + apply (IHk [] gss hss); [simpl; lia|apply Hnil|apply Hgh].
  - intros Hle Hnil Hgh.
    split.
    + eapply monarrlist_equiv_trans; [apply Hnil|].
      apply Hgh.
    + apply (IHk fss [] hss); [simpl in *; lia| |apply Hgh].
      apply (all_monarrlist_list_cons_equiv_nil Hnil).
  - intros Hle Hnil Hgh.
    split.
    + eapply monarrlist_equiv_trans; [apply Hnil|].
      apply Hgh.
    + pose proof (IHk fss gss [] ltac:(simpl in *;lia) (proj2 Hnil) 
        (all_monarrlist_list_cons_equiv_nil Hgh)) as e.
      unfold all_monarrlist_list_equiv in e.
      rewrite zip_defaults_nil_r in e.
      apply e.
  - simpl.
    intros Hle Hfg Hgh.
    split.
    + eapply monarrlist_equiv_trans; [apply Hfg|apply Hgh].
    + apply (IHk fss gss hss); [lia|..].
      * apply Hfg.
      * apply Hgh.
Qed.

Lemma compose_composable_monarrlist_list_equiv_nil {fss} 
  (H : all_monarrlist_list_equiv fss []) 
  (Hf : totally_composable fss) : 
  monarr_norm_equiv 
    (compose_totally_composable fss Hf)
    (arrid e).
Proof.
  induction fss;
  [ apply monarr_norm_equiv_refl | destruct fss;
    [apply (stack_monarrlist_equiv (proj1 H))|]].
  rewrite compose_totally_composable_cons.
  unfold compose_composable_monarr.
  rewrite <- (monarr_lunit (arrid e)).
  apply monarr_norm_equiv_comp.
  + eapply monarr_norm_equiv_trans;
    [apply monarr_norm_equiv_struct_r|].
    apply (stack_monarrlist_equiv (proj1 H)).
  + apply IHfss, H.
Qed.

#[global] Add Parametric Relation : monarrlistelt monarrlistelt_equiv
  reflexivity proved by monarrlistelt_equiv_refl
  symmetry proved by monarrlistelt_equiv_symm
  transitivity proved by monarrlistelt_equiv_trans
  as monarrlistelt_equiv_equivalence.

#[global] Add Parametric Relation : monarrlist all_monarrlist_equiv
  reflexivity proved by monarrlist_equiv_refl
  symmetry proved by monarrlist_equiv_symm
  transitivity proved by monarrlist_equiv_trans
  as monarrlist_equiv_equivalence.

#[global] Add Parametric Relation : (list monarrlist) all_monarrlist_list_equiv
  reflexivity proved by monarrlist_list_equiv_refl
  symmetry proved by monarrlist_list_equiv_symm
  transitivity proved by monarrlist_list_equiv_trans
  as monarrlist_list_equiv_equivalence.



Lemma all_monarrlist_list_equiv_iff_ex {fss gss} : 
  all_monarrlist_list_equiv fss gss <->
  exists fshd fsnil gshd gsnil, 
    fss = fshd ++ fsnil /\ gss = gshd ++ gsnil /\
    all_monarrlist_list_equiv fsnil [] /\
    all_monarrlist_list_equiv gsnil [] /\
    length fshd = length gshd /\
    all_monarrlist_list_equiv fshd gshd.
Proof.
  split.
  2: {
    intros (fshd & fsnil & gshd & gsnil & Hfss & Hgss & Hfnil & Hgnil & Hlen & Hfg).
    subst.
    revert gshd Hlen Hfg;
    induction fshd; intros gshd Hlen Hfg.
    - destruct gshd; [|easy].
      etransitivity; eauto using monarrlist_list_equiv_symm.
    - destruct gshd; [easy|].
      simpl in Hlen.
      injection Hlen; clear Hlen; intros Hlen.
      specialize (IHfshd _ Hlen).
      specialize (IHfshd (proj2 Hfg)).
      split; [apply Hfg | apply IHfshd].
  } 
  revert gss;
  induction fss as [|fs fss IHfss]; 
  intros gss; [|destruct gss as [|gs gss]].
  - intros Hgss.
    exists [], [], [], gss.
    repeat split; easy + symmetry; easy.
  - intros Hfss.
    exists [], (fs :: fss), [], [].
    rewrite app_nil_r.
    repeat easy + split.
  - intros [Hfgs Hfgss].
    destruct (IHfss gss Hfgss) as 
      (fshd & fsnil & gshd & gsnil 
      & Hfss & Hgss & Hfnil & Hgnil & Hlen & Hequiv).
    exists (fs :: fshd), fsnil, (gs :: gshd), gsnil.
    (repeat first [easy | split]); simpl; subst; easy + f_equal; easy.
Qed.

Lemma compose_composable_monarrlist_list_equiv {fss gss} 
  (H : all_monarrlist_list_equiv fss gss) 
  (Hf : totally_composable fss)
  (Hg : totally_composable gss) : 
  monarr_norm_equiv 
    (compose_totally_composable fss Hf)
    (compose_totally_composable gss Hg).
Proof.
  remember (length fss + length gss) as k.
  assert (Hk : length fss + length gss <= k) by (subst; easy).
  clear Heqk.
  revert fss gss H Hf Hg Hk.
  induction k; intros fss gss;
  destruct fss, gss; 
  try (solve [simpl; intros; easy]);
  intros H Hf Hg Hk;
  [..|destruct fss, gss].
  - apply monarr_norm_equiv_symm.
    apply compose_composable_monarrlist_list_equiv_nil.
    apply monarrlist_list_equiv_symm, H.
  - apply compose_composable_monarrlist_list_equiv_nil, H.
  - apply stack_monarrlist_equiv, H.
  - rewrite <- monarr_runit.
    rewrite compose_totally_composable_cons.
    apply monarr_norm_equiv_comp.
    + rewrite monarr_norm_equiv_struct_r'_iff.
      apply stack_monarrlist_equiv, H.
    + eapply monarr_norm_equiv_trans;
      [|apply (IHk [] (m1::gss) (proj2 H) ltac:(easy) (proj2 Hg))];
      [|simpl in *; lia].
      apply monarr_norm_equiv_struct_eq_in.
      simpl.
      etransitivity;
      [apply ( (Nf_eq_out_of_norm_equiv 
        (stack_monarrlist_equiv (proj1 H))))|].
      specialize (IHk [] (m1::gss) (proj2 H) ltac:(easy) 
        (proj2 Hg) ltac:(simpl in Hk |- *; lia)).
      apply (Nf_eq_in_of_norm_equiv) in IHk.
      simpl in IHk.
      rewrite IHk.
      apply Hg.
  - apply monarr_norm_equiv_symm.
    rewrite <- monarr_runit.
    rewrite compose_totally_composable_cons.
    apply monarr_norm_equiv_comp.
    + eapply monarr_norm_equiv_symm, monarr_norm_equiv_trans;
      [apply monarr_norm_equiv_struct_r|];
      apply stack_monarrlist_equiv, H.
    + eapply monarr_norm_equiv_trans;
      [|apply (IHk [] (m1::fss) 
        (monarrlist_list_equiv_symm (m1::fss) [] (proj2 H)) 
        ltac:(easy) (proj2 Hf) )];
      [|simpl in *; lia].
      apply monarr_norm_equiv_struct_eq_in.
      simpl.
      etransitivity;
      [apply (eq_sym (Nf_eq_out_of_norm_equiv 
        (stack_monarrlist_equiv (proj1 H))))|].
      specialize (IHk (m1::fss) [] (proj2 H) (proj2 Hf)
        ltac:(easy) ltac:(simpl in Hk |- *; lia)).
      apply (Nf_eq_in_of_norm_equiv) in IHk.
      simpl in IHk.
      rewrite <- IHk.
      apply Hf.
  - rewrite 2!compose_totally_composable_cons.
    apply monarr_norm_equiv_comp.
    + eapply monarr_norm_equiv_trans;
      [|apply monarr_norm_equiv_symm; 
      eapply monarr_norm_equiv_trans];
    [apply monarr_norm_equiv_struct_r.. |].
    apply monarr_norm_equiv_symm.
    apply stack_monarrlist_equiv, H.
    + apply (IHk (m1 :: fss) (m2 :: gss)); [|simpl in *; lia].
      apply H.
Qed.

End monarrlist_equivalences.

End monarrlist_theory.