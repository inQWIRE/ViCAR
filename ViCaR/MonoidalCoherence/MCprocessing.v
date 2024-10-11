Require Import Setoid.
Require MCproperop.

Section ProperOperationInstances.

Set Universe Polymorphism.

Open Scope bw_scope.

Import MCDefinitions MCClasses MC_setoids
  MC_notations UIP_facts MCbw 
  MCconsequences MCmonarrlist MCproperop.
Import CategoryTypeclass.
Import List ListNotations.

Context {X : Type} {UIPX : UIP X}.
Context {cC : Category X} {cCh : CategoryCoherence cC} 
  {mC : MonoidalCategory cC} {mCh : MonoidalCategoryCoherence mC}.

Local Notation bw := (bw X).
Local Notation "a ⟶ b" := (@monarr X cC mC a b) (at level 60).
Local Notation monarrlist := (@monarrlist X cC mC).
Local Notation monarrlistelt := (@monarrlistelt X cC mC).

Section proper_map_definitions.

Fixpoint foliate_monarr {a b} (f : a ⟶ b) : list monarrlist :=
  match f with
  | monarrcomp g h => foliate_monarr g ++ foliate_monarr h
  | monarrtens g h => 
    zip_defaults (@app monarrlistelt) (foliate_monarr h) (foliate_monarr g)
      [monarrlist_id (monarrlist_list_target (foliate_monarr h))]
      [monarrlist_id (monarrlist_list_target (foliate_monarr g))]
  | monarrstruct f => [[monarrlist_arr _ _ (monarrstruct f)]]
  | mongeneric f => [[monarrlist_arr _ _ (mongeneric f)]]
  end.

Definition sum_to_bool {A B} (x : A + B) : bool :=
  match x with
  | inl _ => true
  | inr _ => false
  end.

Definition proj_to_monarrlist_list (f : (list monarrlist) * bw) : list monarrlist :=
  match fst f with
  | [] => [[monarrlist_id (snd f)]]
  | fs :: fss => fs :: fss
  end.

Definition trim_foliate_monarr_helper_compose (f g : (list monarrlist) * bw) : 
    (list monarrlist) * bw := 
  (fst f ++ fst g, snd g).

Global Arguments trim_foliate_monarr_helper_compose !_ !_ /.

Definition trim_foliate_monarr_helper_stack (f g : (list monarrlist) * bw) :
    (list monarrlist) * bw :=
  (zip_defaults (@app monarrlistelt) (fst g) (fst f)
    [monarrlist_id (snd g)]
    [monarrlist_id (snd f)], tens (snd f) (snd g)).

Global Arguments trim_foliate_monarr_helper_stack !_ !_ /.

Fixpoint trim_foliate_monarr_helper {a b} (f : a ⟶ b) : 
  (list monarrlist) * bw := 
    (* inl lst is the usual output, 
       inr a means a structural arrow starting at a *)
  match f with
  | monarrcomp g h => 
    trim_foliate_monarr_helper_compose
      (trim_foliate_monarr_helper g) 
      (trim_foliate_monarr_helper h)
  | monarrtens g h => 
    trim_foliate_monarr_helper_stack
      (trim_foliate_monarr_helper g)
      (trim_foliate_monarr_helper h)
  | @monarrstruct _ _ _ a b f => ([], b)
  | @mongeneric _ _ _ a b f => ([[monarrlist_arr _ _ (mongeneric f)]], b)
  end.

Definition trim_foliate_monarr {a b} (f : a ⟶ b) : list monarrlist :=
  proj_to_monarrlist_list (trim_foliate_monarr_helper f).

Fixpoint is_empty (a : bw) : bool :=
  match a with
  | e => true
  | var _ => false
  | tens a' b' => is_empty a' && is_empty b'
  end.

Fixpoint remove_empty_structs (fs : monarrlist) : monarrlist := 
  match fs with
  | nil => nil
  | monarrlist_id a :: fs' => 
    (if is_empty a then [] else [monarrlist_id a])
    ++ remove_empty_structs fs'
  | f :: fs' => f :: remove_empty_structs fs'
  end.

Definition trim_foliate_monarr_no_empty {a b} (f : a ⟶ b) : list monarrlist :=
  map remove_empty_structs (trim_foliate_monarr f).
(*
Definition proj_to_monarrlist_list (f : (list monarrlist) * bw) : list monarrlist :=
  match fst f with
  | inl fs => fs
  | inr a => [[monarrlist_id a]]
  end.

Definition trim_foliate_monarr_helper_compose (f g : (list monarrlist) + bw) : 
    (list monarrlist) + bw :=
  match f, g with
  | inl fs, inl gs => inl (fs ++ gs)
  | inl fs, inr b  => inl fs
  | inr a,  inl gs => inl gs
  | inr a,  inr b  => inr a
  end.

Definition trim_foliate_monarr_helper_stack (f g : (list monarrlist) + bw) :
    (list monarrlist) + bw :=
  match f, g with
  | inl fs, inl gs => inl (
     zip_defaults (@app monarrlistelt) gs fs
      [monarrlist_id (monarrlist_list_target gs)]
      [monarrlist_id (monarrlist_list_target fs)])
  | inl fs, inr b  => inl (
    zip_with_default_l (@app monarrlistelt) 
      fs [monarrlist_id b])
  | inr a,  inl gs => inl (
    zip_with_default_r (@app monarrlistelt) 
      [monarrlist_id a] gs)
  | inr a,  inr b  => inr (tens a b)
  end.

Fixpoint trim_foliate_monarr_helper {a b} (f : a ⟶ b) : 
  (list monarrlist) + bw := 
    (* inl lst is the usual output, 
       inr a means a structural arrow starting at a *)
  match f with
  | monarrcomp g h => 
    trim_foliate_monarr_helper_compose
      (trim_foliate_monarr_helper g) 
      (trim_foliate_monarr_helper h)
  | monarrtens g h => 
    trim_foliate_monarr_helper_stack
      (trim_foliate_monarr_helper g)
      (trim_foliate_monarr_helper h)
  | @monarrstruct _ _ _ a b f => inr a
  | mongeneric f => inl [[monarrlist_arr _ _ (mongeneric f)]]
  end.

Definition trim_foliate_monarr {a b} (f : a ⟶ b) : list monarrlist :=
  proj_to_monarrlist_list (trim_foliate_monarr_helper f).
*)

(*
Fixpoint foliate_monarr_alt {a b} (f : a ⟶ b) : list monarrlist :=
  match f with
  | monarrcomp g h => foliate_monarr g ++ foliate_monarr h
  | monarrtens g h => 
    zip_defaults (@app monarrlistelt) (foliate_monarr h) (foliate_monarr g)
      (monarrlist_id (monarrlist_list_target (foliate_monarr h)) :: nil)
      (monarrlist_id (monarrlist_list_target (foliate_monarr g)) :: nil)
  | monarrstruct f => (monarrlist_arr _ _ (monarrstruct f) :: nil) :: nil
  | mongeneric f => (monarrlist_arr _ _ (mongeneric f) :: nil) :: nil
  end 
  (* with foliate_monarr_alt_def {a b} (f : a ⟶ b) : list monarrlist *)
  . *)

Definition is_idarr (fs : monarrlistelt) :=
  match fs with
  | monarrlist_id _ => true
  | monarrlist_arr _ _ _ => false
  end.

Definition is_idarrlist (fs : monarrlist) :=
  forallb is_idarr fs.

Definition idarr_of_vars (xs : list X) : monarrlist :=
  map (fun x => monarrlist_id (var x)) xs.

Definition shift_left (fs gs : monarrlist) := 
  if is_idarrlist fs then 
  (gs, idarr_of_vars (target_vars gs))
  else (fs, gs).

Definition shift_right (fs gs : monarrlist) := 
  if is_idarrlist gs then 
  (idarr_of_vars (source_vars fs), fs)
  else (fs, gs).

Fixpoint is_struct {a b} (f : a ⟶ b) : bool := 
  match f with 
  | mongeneric _ => false
  | monarrstruct _ => true
  | monarrcomp f' g' => is_struct f' && is_struct g'
  | monarrtens f' g' => is_struct f' && is_struct g'
  end.

Fixpoint struct_of_is_struct {a b} (f : a ⟶ b) 
  (H : is_struct f = true) : bwarr a b.
  destruct f.
  - refine (struct_of_is_struct _ _ _ _ ○ struct_of_is_struct _ _ _ _).
    apply (proj1 (proj1 (Bool.andb_true_iff _ _) H)).
    apply (proj2 (proj1 (Bool.andb_true_iff _ _) H)).
  - refine (struct_of_is_struct _ _ _ _ ⊠ struct_of_is_struct _ _ _ _).
    apply (proj1 (proj1 (Bool.andb_true_iff _ _) H)).
    apply (proj2 (proj1 (Bool.andb_true_iff _ _) H)).
  - discriminate H.
  - apply f.
Defined.

Fixpoint structify {a b} (f : a ⟶ b) : a ⟶ b :=
  match f with
  | mongeneric f' => mongeneric f'
  | monarrstruct f' => monarrstruct f'
  | monarrcomp f' g' => 
      let fs := structify f' in 
      let gs := structify g' in 
      match Bool.bool_dec (is_struct fs) true with
      | right _ => monarrcomp fs gs
      | left Hfstruct => 
        match Bool.bool_dec (is_struct gs) true with
        | right _ => monarrcomp fs gs
        | left Hgstruct => 
          arrcomp 
            (struct_of_is_struct fs Hfstruct) 
            (struct_of_is_struct gs Hgstruct) 
        end
      end
  | monarrtens f' g' => 
      let fs := structify f' in 
      let gs := structify g' in 
      match Bool.bool_dec (is_struct fs) true with
      | right _ => monarrtens fs gs
      | left Hfstruct => 
        match Bool.bool_dec (is_struct gs) true with
        | right _ => monarrtens fs gs
        | left Hgstruct => 
          arrtens 
            (struct_of_is_struct fs Hfstruct) 
            (struct_of_is_struct gs Hgstruct) 
        end
      end
  end.

Definition remove_struct (g : monarrlistelt) :=
  match g with
  | monarrlist_id a => monarrlist_id a
  | monarrlist_arr a b f => 
      match f with
      | monarrstruct _ => monarrlist_id a
      | f' => monarrlist_arr a b f'
      end
  end.

Definition remove_structs := map remove_struct.

Fixpoint struct_to_id (fss : monarrlist) := 
  match fss with
  | nil => nil
  | fs :: fss' => match fs with
      | monarrlist_id a => monarrlist_id a
      | monarrlist_arr a b (monarrstruct f) => monarrlist_id a
      | monarrlist_arr a b f => monarrlist_arr a b f
      end :: struct_to_id fss'
  end.

Fixpoint split_ids (fss : monarrlist) := 
  match fss with
  | nil => nil
  | fs :: fss' => match fs with
      | monarrlist_id a => map monarrlist_id (map var (bw_to_varlist a))
      | monarrlist_arr a b f => monarrlist_arr a b f :: nil
      end ++ split_ids fss'
  end.

Fixpoint combine_ids_helper (a : bw) (fss : monarrlist) :=
  match fss with
  | nil => monarrlist_id a :: nil
  | monarrlist_id b :: fss' => combine_ids_helper (tens b a) fss'
  | fs :: fss' => monarrlist_id a :: fs :: combine_ids fss'
  end
with combine_ids (fss : monarrlist) :=
  match fss with
  | nil => nil
  | monarrlist_id a :: fss' => combine_ids_helper a fss'
  | fs :: fss' => fs :: combine_ids fss'
  end.

Definition is_idarr_singleton (fs : monarrlist) :=
  match fs with 
  | monarrlist_id _ :: nil => true
  | _ => false
  end.

Definition filter_idarrs (fss : list monarrlist) :=
  match fss with
  | nil => nil
  | fs :: fss' => 
    fs :: filter (fun x => negb (is_idarrlist x)) fss'
    (* if is_idarrlist fs then
    (if length (filter_idarrs fss') > 0 then filter_idarrs fss' else fs :: nil)
    else fs :: (filter_idarrs fss') *)
  end.

Fixpoint trim_idarrs_helper (fs : monarrlist) (fss : list monarrlist) :=
  match fss with
  | nil => [fs]
  | fs' :: fss' => if is_idarrlist fs' 
    then trim_idarrs_helper fs fss'
    else fs :: fss
  end.

Definition trim_idarrs (fss : list monarrlist) :=
  match fss with
  | nil => nil
  | fs :: fss' => trim_idarrs_helper fs fss'
  end.

Definition trim_idarr (fss : list monarrlist) :=
  match fss with
  | nil => nil
  | fs :: nil => [fs]
  | fs :: fs' :: fss' =>
    if is_idarrlist fs then fs' :: fss' else fs :: fs' :: fss'
  end.

Definition structify_monarrlistelt (f : monarrlistelt) :=
  monarrlistelt_map (@structify) f.

Definition structify_monarrlist (fs : monarrlist) :=
  map structify_monarrlistelt fs.

Local Notation "g |> f" := (Basics.compose f g) 
  (at level 40, left associativity).

Definition full_right_shift (fss : list monarrlist) :=
  Nat.iter (pred (length fss)) (
    pairwise_apply (pairify_apply shift_right) |>
    map split_ids
  ) fss.

Definition full_process_monarrlist_list :=
  map structify_monarrlist |>
  map remove_structs |>
  map split_ids |>
  full_right_shift |>
  trim_idarrs |>
  trim_idarr.

End proper_map_definitions.

Section foliation.

Section zip_with_defaults.

Lemma tens_comp_composable_split_bot_r {a b c d x y} (f : a ⟶ b) (g : c ⟶ d) 
  (H : Nf b = Nf c) (h : x ⟶ y) :
  h ⧆ compose_composable_monarr f g H ≊
  compose_composable_monarr (h ⧆ f) (arrid y ⧆ g)
  (Nf_tens_eq eq_refl H).
Proof.
  unfold compose_composable_monarr.
  rewrite !monarr_tens_comp_split_bot_r.
  rewrite monarr_arrtens.
  eauto with monarrdb.
Qed.

Lemma tens_comp_composable_split_bot_l {a b c d x y} (f : a ⟶ b) (g : c ⟶ d) 
  (H : Nf b = Nf c) (h : x ⟶ y) :
  h ⧆ compose_composable_monarr f g H ≊
  compose_composable_monarr (arrid x ⧆ f) (h ⧆ g)
  (Nf_tens_eq eq_refl H).
Proof.
  unfold compose_composable_monarr.
  rewrite !monarr_tens_comp_split_bot_l.
  rewrite monarr_arrtens.
  eauto with monarrdb.
Qed.

Lemma tens_comp_composable_split_top_pf {a b} (H : Nf a = Nf b) (x : bw) : 
  Nf (a ⨂ x) = Nf (b ⨂ x).
Proof.
  cbn.
  f_equal.
  apply H.
Qed.

Lemma tens_comp_composable_split_top_l {a b c d x y} (f : a ⟶ b) (g : c ⟶ d) 
  (H : Nf b = Nf c) (h : x ⟶ y):
  compose_composable_monarr f g H ⧆ h ≊
  compose_composable_monarr (f ⧆ arrid x) (g ⧆ h)
  (Nf_tens_eq H eq_refl).
Proof.
  unfold compose_composable_monarr.
  rewrite !monarr_tens_comp_split_top_l.
  rewrite monarr_arrtens.
  eauto with monarrdb.
Qed.

Lemma tens_comp_composable_split_top_r {a b c d x y} (f : a ⟶ b) (g : c ⟶ d) 
  (H : Nf b = Nf c) (h : x ⟶ y):
  compose_composable_monarr f g H ⧆ h ≊
  compose_composable_monarr (f ⧆ h) (g ⧆ arrid y)
  (Nf_tens_eq H eq_refl).
Proof.
  unfold compose_composable_monarr.
  rewrite !monarr_tens_comp_split_top_r.
  rewrite monarr_arrtens.
  eauto with monarrdb.
Qed.

Lemma monarr_tens_comp_composable {a b c d m n o p} (f : a ⟶ b) (g : c ⟶ d)
  (h : m ⟶ n) (k : o ⟶ p) (H : Nf b = Nf c) (H' : Nf n = Nf o) :
  compose_composable_monarr f g H ⧆ compose_composable_monarr h k H' ≊
  compose_composable_monarr (f ⧆ h) (g ⧆ k) (Nf_tens_eq H H').
Proof.
  unfold compose_composable_monarr.
  rewrite !monarr_tens_comp, monarr_arrtens.
  eauto with monarrdb.
Qed.

Lemma zip_with_default_l_norm_equiv_nonempty {fss} (Hne : fss <> []) 
  (Hf : totally_composable fss) a :
  monarr_norm_equiv (compose_totally_composable
    _ (zip_with_default_l_totally_composable Hf a))
    (arrid (e⨂a) ⧆ compose_totally_composable fss Hf).
Proof.
  induction fss; [|destruct fss]; [easy|..].
  - simpl.
    apply (monarr_norm_equiv_trans (stack_monarrlist_app' _ _)).
    simpl.
    apply monarrequiv_iff_monarr_norm_equiv.
    apply monarr_tens; [|easy].
    rewrite monarr_arrtens.
    apply monarr_struct.
  - simpl zip_with_default_l in *.
    rewrite 2!compose_totally_composable_cons.
    (* erewrite compose_totally_composable_indep. *)
    eapply monarr_norm_equiv_trans.
    1:{
      eapply monarr_norm_equiv_comp_composable;
      [apply stack_monarrlist_app'|].
      erewrite compose_totally_composable_indep.
      refine (IHfss _ (proj2 Hf)).
      easy.
    }
    rewrite tens_comp_composable_split_bot_l.
    unshelve (instantiate (1:=_)); 
    [rewrite 2!Nf_tens_bwnormapp; f_equal; apply Hf|].
    apply monarr_norm_equiv_comp_composable; [|easy].
    apply monarr_norm_equiv_tens; [|easy].
    cbn.
    now rewrite monarr_arrtens, monarr_struct_id.
Qed.

Lemma zip_with_default_l_equiv_nonempty {fss} (Hne : fss <> []) 
  (Hf : totally_composable fss) a :
  compose_totally_composable
    _ (zip_with_default_l_totally_composable Hf a)
  ≊ bwarr_of_Nf_eq (zip_with_default_l_source_nonempty Hne [monarrlist_id a])
    ◌ arrid (e⨂a) ⧆ compose_totally_composable fss Hf
    ◌ bwarr_of_Nf_eq (eq_sym 
      (zip_with_default_l_target_nonempty Hne [monarrlist_id a])).
Proof.
  apply equiv_conj_of_monarr_norm_equiv.
  apply zip_with_default_l_norm_equiv_nonempty, Hne.
Qed.

Lemma zip_with_default_r_norm_equiv_nonempty {fss} (Hne : fss <> []) 
  (Hf : totally_composable fss) a :
  monarr_norm_equiv (compose_totally_composable
    _ (zip_with_default_r_totally_composable Hf a))
  (compose_totally_composable fss Hf ⧆ arrid (e ⨂ a)).
Proof.
  induction fss; [easy|destruct fss].
  - simpl.
    exists eq_refl.
    exists eq_refl.
    cbn.
    rewrite monarr_comp_tens_id_top_struct_l, monarr_comp_tens_id_top_struct_r.
    apply monarr_tens; [easy|].
    rewrite !monarr_arrcomp; apply monarr_struct.
  - simpl zip_with_default_r in *.
    rewrite 2!compose_totally_composable_cons.
    (* erewrite compose_totally_composable_indep. *)
    eapply monarr_norm_equiv_trans.
    1:{
      eapply monarr_norm_equiv_comp_composable;
      [apply (stack_monarrlist_app' [_] _)|].
      erewrite compose_totally_composable_indep.
      refine (IHfss _ (proj2 Hf)).
      easy.
    }
    rewrite tens_comp_composable_split_top_l.
    unshelve (instantiate (1:=_));
    [rewrite 2!Nf_tens_bwnormapp; f_equal; apply Hf|].
    apply monarr_norm_equiv_comp_composable; [|easy].
    apply monarr_norm_equiv_tens; [easy|].
    cbn.
    now rewrite monarr_arrtens, monarr_struct_id.
Qed.

Lemma zip_with_default_r_equiv_nonempty {fss} (Hne : fss <> []) 
  (Hf : totally_composable fss) a :
  compose_totally_composable
    _ (zip_with_default_r_totally_composable Hf a)
  ≊ bwarr_of_Nf_eq (zip_with_default_r_source_nonempty Hne [monarrlist_id a])
    ◌ compose_totally_composable fss Hf ⧆ arrid (e ⨂ a)
    ◌ bwarr_of_Nf_eq (eq_sym 
      (zip_with_default_r_target_nonempty Hne [monarrlist_id a])).
Proof.
  apply equiv_conj_of_monarr_norm_equiv,
    zip_with_default_r_norm_equiv_nonempty, Hne.
Qed.

Lemma zip_defaults_totally_composable' {fss gss df dg} 
  (Hf : totally_composable fss) 
  (Hg : totally_composable gss) 
  (Hdf : Nf df = Nf (monarrlist_list_target fss))
  (Hdg : Nf dg = Nf (monarrlist_list_target gss)) : 
  totally_composable 
    (zip_defaults (@app monarrlistelt)
      fss gss
      (monarrlist_id df :: nil)
      (monarrlist_id dg :: nil)).
Proof.
  revert gss Hg Hdg;
  induction fss; intros gss Hg Hdg; 
  [|revert a Hf Hdf; induction gss as [|l gss IHgss]; 
    intros a Hf Hdf; [|destruct fss; [|destruct gss]]];
  [..|destruct fss, gss].
  - apply zip_with_default_r_totally_composable, Hg.
  - apply zip_with_default_l_totally_composable, Hf.
  - destruct gss; [easy|].
    split.
    + apply composable_app; [easy | apply Hg].
    + apply (zip_with_default_r_totally_composable (fss:=m :: gss) (proj2 Hg)).
  - split.
    + apply composable_app; [apply Hf | easy].
    + apply (zip_with_default_l_totally_composable (fss:=m :: fss) (proj2 Hf)).
  - split; [|easy]. apply composable_app; [apply Hf | apply Hg].
  - split; [apply composable_app; [apply Hf | apply Hg]|].
    split.
    + apply composable_app; [|apply Hg].
      unfold composable.
      cbn.
      change (⟦ df ⟧ norm_e) with (Nf df).
      rewrite Hdf; easy.
    + apply (zip_with_default_r_totally_composable 
      (fss:=m1 :: gss) (proj2 (proj2 Hg))).
  - split; [apply composable_app; [apply Hf | apply Hg]|].
    split.
    + apply composable_app; [apply Hf|].
      unfold composable.
      cbn.
      change (⟦ dg ⟧ norm_e) with (Nf dg).
      rewrite Hdg; easy.
    + apply (zip_with_default_l_totally_composable 
      (fss:=m1 :: fss) (proj2 (proj2 Hf))).
  - split; [apply composable_app; [apply Hf | apply Hg]|].
    apply (IHfss (proj2 Hf) Hdf (m0 :: m2 :: gss) (proj2 Hg) Hdg).
Qed.

Lemma zip_defaults_totally_composable {fss gss} 
  (Hf : totally_composable fss) 
  (Hg : totally_composable gss) : 
  totally_composable 
    (zip_defaults (@app monarrlistelt)
      fss gss
      (monarrlist_id (monarrlist_list_target fss) :: nil)
      (monarrlist_id (monarrlist_list_target gss) :: nil)).
Proof.
  revert gss Hg;
  induction fss; intros gss Hg; [|revert a Hf; induction gss as [|l gss IHgss]; 
    intros a Hf; [|destruct fss; [|destruct gss]]].
  - apply zip_with_default_r_totally_composable, Hg.
  - apply zip_with_default_l_totally_composable, Hf.
  - destruct gss; [easy|].
    split.
    + apply composable_app; [easy | apply Hg].
    + apply (zip_with_default_r_totally_composable (fss:=m :: gss) (proj2 Hg)).
  - split.
    + apply composable_app; [apply Hf | easy].
    + apply (zip_with_default_l_totally_composable (fss:=m :: fss) (proj2 Hf)).
  - split.
    + apply composable_app; [apply Hf | apply Hg].
    + rewrite 2!monarrlist_list_target_cons_cons.
      apply (IHfss (proj2 Hf) (m0 :: gss)), Hg.
Qed.

Lemma tens_zip_defaults_correct_helper'' {fss gss} 
  (Hnf : fss <> []) (Hng : gss <> [])
  (Hf : totally_composable fss) (Hg : totally_composable gss) {df dg} 
  (Hdf : Nf df = _) (Hdg : Nf dg = _) :
  monarr_norm_equiv (compose_totally_composable
    _ (zip_defaults_totally_composable' Hf Hg Hdf Hdg))
    (compose_totally_composable gss Hg ⧆ compose_totally_composable fss Hf).
Proof.
  revert gss Hg Hng Hdg;
  induction fss;
  intros gss Hg Hng Hdg; [easy|destruct gss; [easy|]].
  destruct fss, gss(* ; [..|destruct fss, gss] *).
  - apply stack_monarrlist_app'.
  - simpl zip_defaults.
    rewrite 2!compose_totally_composable_cons.
    rewrite tens_comp_composable_split_top_r.
    apply monarr_norm_equiv_comp_composable;
    [apply stack_monarrlist_app'|].
    pose proof (@zip_with_default_r_norm_equiv_nonempty (m0 :: gss) 
      (fun x => nil_cons (eq_sym x)) (proj2 Hg) df) as H.
    simpl zip_with_default_r in H.
    erewrite compose_totally_composable_indep.
    apply (monarr_norm_equiv_trans H).
    apply monarr_norm_equiv_tens; [easy|].
    apply monarr_norm_equiv_struct_eq_in.
    easy.
  - simpl zip_defaults.
    rewrite 2!compose_totally_composable_cons.
    rewrite tens_comp_composable_split_bot_r.
    apply monarr_norm_equiv_comp_composable;
    [apply stack_monarrlist_app'|].
    pose proof (@zip_with_default_l_norm_equiv_nonempty (m0 :: fss) 
      (fun x => nil_cons (eq_sym x)) (proj2 Hf) dg) as H.
    simpl zip_with_default_l in H.
    erewrite compose_totally_composable_indep.
    apply (monarr_norm_equiv_trans H).
    apply monarr_norm_equiv_tens; [|easy].
    apply monarr_norm_equiv_struct_eq_in.
    easy.
  - simpl zip_defaults.
    rewrite 3!compose_totally_composable_cons.
    rewrite monarr_tens_comp_composable.
    apply monarr_norm_equiv_comp_composable;
    [apply stack_monarrlist_app'|].
    (* erewrite (compose_totally_composable_indep (_::_) (proj2 Hg)).
    erewrite (compose_totally_composable_indep (_::_) (proj2 Hf)). *)
    refine (monarr_norm_equiv_trans _ (IHfss ltac:(easy) 
      (proj2 Hf) Hdf (m1::gss) (proj2 Hg) ltac:(easy) Hdg)).
    erewrite compose_totally_composable_indep.
    easy.
Qed.
    
Lemma tens_zip_defaults_correct_helper' {fss gss} 
  (Hnf : fss <> []) (Hng : gss <> [])
  (Hf : totally_composable fss) (Hg : totally_composable gss) :
  monarr_norm_equiv (compose_totally_composable
    _ (zip_defaults_totally_composable Hf Hg))
    (compose_totally_composable gss Hg ⧆ compose_totally_composable fss Hf).
Proof.
  erewrite compose_totally_composable_indep.
  apply (tens_zip_defaults_correct_helper'' Hnf Hng Hf Hg eq_refl eq_refl).
Qed.

Lemma tens_zip_defaults_correct_helper {fss gss} (Hnf : fss <> []) (Hng : gss <> [])
  (Hf : totally_composable fss) (Hg : totally_composable gss) :
  compose_totally_composable
    _ (zip_defaults_totally_composable Hf Hg)
  ≊ bwarr_of_Nf_eq (zip_defaults_source_nonempty Hnf Hng)
    ◌ compose_totally_composable gss Hg ⧆ compose_totally_composable fss Hf
    ◌ bwarr_of_Nf_eq (eq_sym (zip_defaults_target_nonempty Hnf Hng)).
Proof.
  apply equiv_conj_of_monarr_norm_equiv,
    tens_zip_defaults_correct_helper'; easy.
Qed.

Lemma tens_zip_defaults_correct' {fss gss} (Hnf : fss <> []) (Hng : gss <> [])
  (Hf : totally_composable fss) (Hg : totally_composable gss) 
  Hcomp :
  monarr_norm_equiv (compose_totally_composable
    (zip_defaults (app (A:=monarrlistelt)) fss gss
	    [monarrlist_id (monarrlist_list_target fss)]
      [monarrlist_id (monarrlist_list_target gss)])
    Hcomp)
    (compose_totally_composable gss Hg ⧆ compose_totally_composable fss Hf).
Proof.
  erewrite compose_totally_composable_indep.
  apply tens_zip_defaults_correct_helper'; easy.
Qed.

Lemma tens_zip_defaults_correct {fss gss} (Hnf : fss <> []) (Hng : gss <> [])
  (Hf : totally_composable fss) (Hg : totally_composable gss) 
  Hcomp :
  compose_totally_composable
    (zip_defaults (app (A:=monarrlistelt)) fss gss
	    [monarrlist_id (monarrlist_list_target fss)]
      [monarrlist_id (monarrlist_list_target gss)]) 
    Hcomp
  ≊ bwarr_of_Nf_eq (zip_defaults_source_nonempty Hnf Hng)
    ◌ compose_totally_composable gss Hg ⧆ compose_totally_composable fss Hf
    ◌ bwarr_of_Nf_eq (eq_sym (zip_defaults_target_nonempty Hnf Hng)).
Proof.
  erewrite compose_totally_composable_indep.
  apply tens_zip_defaults_correct_helper.
Qed.

End zip_with_defaults.

Lemma foliate_monarr_not_nil {a b} (f : a ⟶ b) : 
  foliate_monarr f <> [].
Proof.
  induction f; try easy; simpl;
  destruct (foliate_monarr f1); 
  destruct (foliate_monarr f2); easy.
Qed.

Lemma monarrlist_list_source_foliate {a b} (f : a ⟶ b) :
  Nf (monarrlist_list_source (foliate_monarr f)) = Nf a.
Proof.
  induction f; simpl; try easy.
  - rewrite monarrlist_list_source_app_not_nil by apply foliate_monarr_not_nil.
    easy.
  - pose proof (foliate_monarr_not_nil f1).
    pose proof (foliate_monarr_not_nil f2).
    destruct (foliate_monarr f1); 
    destruct (foliate_monarr f2); try easy.
    simpl in *.
    rewrite Nf_monarrlist_source_app, Nf_tens_bwnormapp.
    f_equal; easy.
Qed.

Lemma monarrlist_list_target_foliate_helper fss gss :
  Nf (monarrlist_list_target
     (zip_defaults (app (A:=monarrlistelt)) gss fss
        [monarrlist_id (monarrlist_list_target gss)]
        [monarrlist_id (monarrlist_list_target fss)])) = 
  bwnormapp 
    (Nf (monarrlist_list_target fss)) (Nf (monarrlist_list_target gss)).
Proof.
  revert fss;
  induction gss; intro fss.
  - simpl. 
    induction fss; [easy|].
    simpl.
    destruct fss; [easy|].
    apply IHfss.
  - destruct gss.
    + induction fss.
      * simpl.
        rewrite Nf_monarrlist_target_app.
        easy.
      * simpl.
        destruct fss;
        [apply Nf_monarrlist_target_app|].
        simpl (monarrlist_list_target [a]) in IHfss.
        rewrite <- IHfss.
        simpl.
        destruct (zip_with_default_r (app (A:=monarrlistelt)) [monarrlist_id (monarrlist_target a)] fss).
        change (?x :: l) with ((x::nil) ++ l).
        rewrite 2!Nf_monarrlist_target_app.
        easy.
        easy.
    + destruct fss;
      [apply (IHgss nil)|].
      rewrite zip_defaults_cons.
      change (monarrlist_list_target (?a :: ?l :: ?gss))
        with (monarrlist_list_target (l :: gss)).
      destruct fss.
      simpl zip_defaults.
      simpl monarrlist_list_target.
      destruct gss.
      simpl.
      rewrite Nf_monarrlist_target_app; easy.
      destruct gss.
      simpl.
      rewrite Nf_monarrlist_target_app; easy.
      do 2 change (monarrlist_list_target (?a :: ?l :: ?gss))
        with (monarrlist_list_target (l :: gss)) in *.
      (* rewrite 2!monarrlist_list_target_cons_cons in *. *)
      specialize (IHgss (l0::nil)).
      simpl (monarrlist_list_target (l0 :: nil)) in IHgss.
      rewrite <- IHgss.
      easy.
      change (monarrlist_list_target (?a :: ?l :: ?gss))
        with (monarrlist_list_target (l :: gss)).
      rewrite <- IHgss.
      easy.
Qed.

Lemma monarrlist_list_target_foliate {a b} (f : a ⟶ b) :
  Nf (monarrlist_list_target (foliate_monarr f)) = Nf b.
Proof.
  induction f; simpl; try easy.
  - rewrite monarrlist_list_target_app_not_nil by apply foliate_monarr_not_nil.
    easy.
  - rewrite monarrlist_list_target_foliate_helper.
    rewrite Nf_tens_bwnormapp.
    f_equal; easy.
Qed.

Lemma foliate_monarr_totally_composable {a b} (f : a ⟶ b) :
  totally_composable (foliate_monarr f).
Proof.
  induction f; try easy.
  simpl.
  apply app_composable_of_composable_mid; try easy.
  rewrite monarrlist_list_target_foliate, monarrlist_list_source_foliate.
  easy.
  simpl.
  revert IHf1 IHf2.
  generalize (foliate_monarr f2).
  generalize (foliate_monarr f1).
  clear f1 f2.
  intros fss.
  induction fss; intros gss; [|destruct fss]; intros Hf Hg.
  - induction gss; [easy|].
    simpl. 
    destruct gss; [easy|].
    split; [|apply IHgss, Hg].
    apply composable_app;
    [apply Hg|].
    easy.
  - induction gss; [easy|].
    simpl.
    destruct gss; [easy|].
    split;
    [apply composable_app; [apply Hg| easy]|].
    simpl in IHgss.
    destruct gss; try (apply IHgss); try assumption + easy.
    split; [|apply IHgss].
    apply composable_app.
    apply Hg.
    easy.
    intros.
    apply Hg.
  - induction gss; [|destruct gss].
    + clear IHfss.
      split; [apply composable_app; [easy|apply Hf]|].
      apply (totally_composable_app_restrict_r (fsts:=a0::nil)) in Hf.
      revert m Hf.
      induction fss;
      intros l Hf; [easy|].
      split; [apply composable_app; [easy|apply Hf]|].
      apply IHfss, Hf.
    + clear IHfss IHgss.
      split; [apply composable_app; [easy|apply Hf]|].
      apply (totally_composable_app_restrict_r (fsts:=a0::nil)) in Hf.
      revert m Hf.
      induction fss;
      split; [apply composable_app; [easy|apply Hf]|].
      apply IHfss, Hf.
    + split; [apply composable_app; [apply Hg|apply Hf]|].
      rewrite 2!monarrlist_list_target_cons_cons.
      apply (IHfss (m0 :: gss));
      [apply Hf | apply Hg].
Qed.

Lemma foliate_correct' {a b} (f : a ⟶ b) : 
  monarr_norm_equiv f 
    (compose_totally_composable (foliate_monarr f)
      (foliate_monarr_totally_composable f)).
Proof.
  induction f.
  - simpl.
    rewrite (compose_totally_composable_app_nonempty
    (fss:=foliate_monarr f1) (fss':=foliate_monarr f2)
    (foliate_monarr_totally_composable (monarrcomp f1 f2))
    (foliate_monarr_not_nil f1) 
    (foliate_monarr_not_nil f2)).
    rewrite monarr_norm_equiv_conj_struct'_iff.
    apply monarr_norm_equiv_comp; 
    [|erewrite (compose_totally_composable_indep (_ _));
      eassumption].
    rewrite monarr_norm_equiv_struct_r'_iff.
    erewrite (compose_totally_composable_indep (_ _));
    eassumption.
  - simpl.
    rewrite (tens_zip_defaults_correct 
      (foliate_monarr_not_nil f2) (foliate_monarr_not_nil f1)
      (foliate_monarr_totally_composable f2)
      (foliate_monarr_totally_composable f1)).
    rewrite monarr_norm_equiv_conj_struct'_iff.
    apply monarr_norm_equiv_tens; easy.
  - apply monarr_norm_equiv_symm.
    apply monarr_norm_equiv_tens_bwarr_e_l.
  - apply monarr_norm_equiv_symm.
    apply monarr_norm_equiv_tens_bwarr_e_l.
Qed.


Lemma foliate_correct {a b} (f : a ⟶ b) :
  f ≊
  bwarr_of_Nf_eq (eq_sym (monarrlist_list_source_foliate f)) ◌
  compose_totally_composable (foliate_monarr f)
      (foliate_monarr_totally_composable f) ◌
  bwarr_of_Nf_eq (monarrlist_list_target_foliate f).
Proof.
  apply equiv_conj_of_monarr_norm_equiv.
  apply foliate_correct'.
Qed.

Lemma compose_equiv_of_eq {fss gss} (H : fss = gss)
  (Hf : totally_composable fss) (Hg : totally_composable gss) : 
  compose_totally_composable _ Hf ≊
  cast_bwarr eq_refl (f_equal monarrlist_list_source H) (arrid _) ◌
  compose_totally_composable _ Hg ◌
  cast_bwarr eq_refl (f_equal monarrlist_list_target (eq_sym H)) (arrid _).
Proof.
  subst.
  rewrite monarr_struct_id, monarr_lunit.
  rewrite monarr_struct_id, monarr_runit.
  erewrite compose_totally_composable_indep.
  easy.
Qed.

Lemma equiv_of_foliate_eq {a b} (f g : a ⟶ b) : 
  foliate_monarr f = foliate_monarr g ->
  f ≊ g.
Proof.
  intros Heq.
  rewrite foliate_correct, (foliate_correct g).
  rewrite monarrcomp_struct_r, monarrcomp_struct_l.
  rewrite <- monarr_assoc, monarr_arrcomp.
  rewrite !monarr_assoc, monarr_arrcomp.
  erewrite (compose_equiv_of_eq Heq _ (foliate_monarr_totally_composable g)).
  apply monarr_comp; [apply monarr_comp|];
  easy + apply monarr_struct.
Qed.

Lemma equiv_of_foliate_equiv {a b} (f g : a ⟶ b) : 
  monarr_norm_equiv 
    (compose_totally_composable 
      (foliate_monarr f) 
      (foliate_monarr_totally_composable f))
    (compose_totally_composable 
      (foliate_monarr g) 
      (foliate_monarr_totally_composable g)) ->
  f ≊ g.
Proof.
  intros Heq.
  rewrite foliate_correct, (foliate_correct g).
  apply monarrequiv_iff_monarr_norm_equiv.
  apply monarr_norm_equiv_conj_struct'_iff, 
    monarr_norm_equiv_conj_struct_iff.
  apply Heq.
Qed.

Lemma equiv_of_foliate_all_equiv {a b} (f g : a ⟶ b) : 
  all_monarrlist_list_equiv (foliate_monarr f) (foliate_monarr g) ->
  f ≊ g.
Proof.
  intros Heq.
  apply equiv_of_foliate_equiv.
  apply compose_composable_monarrlist_list_equiv, Heq.
Qed.

End foliation.

Section trim_foliation.

Lemma totally_composable_of_middle_arr {fss gss} 
  (Hf : totally_composable fss) (Hg : totally_composable gss) 
  (Hmid : Nf (monarrlist_list_target fss) = Nf (monarrlist_list_source gss)) :
  totally_composable (fss ++ gss).
Proof.
  revert gss Hg Hmid; induction fss; intros gss Hg Hmid; [easy|].
  destruct fss.
  - destruct gss; [easy|].
    split; 
    [apply Hmid | apply Hg].
  - split; [apply Hf|].
    apply IHfss; apply Hf + easy.
Qed.

Lemma trim_foliate_spec {a b} (f : a ⟶ b) :
  snd (trim_foliate_monarr_helper f) = b /\
  Nf (monarrlist_list_target (trim_foliate_monarr f)) 
    = Nf (snd (trim_foliate_monarr_helper f)) /\
  exists H : totally_composable (trim_foliate_monarr f),
  monarr_norm_equiv f 
    (compose_totally_composable (trim_foliate_monarr f) H).
Proof.
  unfold trim_foliate_monarr.
  induction f.
  - split; [easy|]. 
    simpl.
    destruct (trim_foliate_monarr_helper f1) as [f1s f1_targ].
    destruct (trim_foliate_monarr_helper f2) as [f2s f2_targ].
    simpl in *.
    destruct IHf1 as (Hf1targ & H1targ & H1comp & Heq1).
    destruct IHf2 as (Hf2targ & H2targ & H2comp & Heq2).
    destruct f1s as [|f1h f1s], f2s as[|f2h f2s];
    (split; [try easy|]);
    cbn [proj_to_monarrlist_list fst] in *.
    + simpl in *.
      exists Logic.I.
      rewrite <- (monarr_lunit (_ ⧆ _)).
      apply monarr_norm_equiv_comp; [|apply Heq2].
      apply (monarr_norm_equiv_trans Heq1).
      rewrite monarr_arrtens.
      apply monarr_norm_equiv_struct_eq_in.
      cbn.
      rewrite Hf1targ.
      apply (eq_trans (Nf_eq_in_of_norm_equiv Heq2)).
      easy.
    + simpl in *.
      exists H2comp.
      rewrite <- (monarr_lunit (compose_totally_composable_helper _ _ _)).
      apply monarr_norm_equiv_comp; [|apply Heq2].
      apply (monarr_norm_equiv_trans Heq1).
      rewrite monarr_arrtens.
      apply monarr_norm_equiv_struct_eq_in.
      cbn.
      rewrite Hf1targ.
      apply (eq_trans (Nf_eq_in_of_norm_equiv Heq2)).
      easy.
    + simpl in *.
      rewrite !app_nil_r.
      etransitivity; 
      [|apply (Nf_eq_in_of_norm_equiv Heq2)].
      rewrite <- Hf1targ.
      apply H1targ.
    + simpl in *.
      rewrite app_nil_r.
      exists H1comp.
      rewrite <- (monarr_runit (compose_totally_composable_helper _ _ _)).
      apply monarr_norm_equiv_comp; [apply Heq1|].
      apply (monarr_norm_equiv_trans Heq2).
      rewrite monarr_arrtens.
      apply monarr_norm_equiv_struct_eq_in.
      simpl.
      rewrite H1targ.
      symmetry.
      etransitivity; [|apply (Nf_eq_in_of_norm_equiv Heq2)].
      now rewrite Hf1targ.
    + simpl in *.
      rewrite monarrlist_list_target_app.
      destruct f1s; apply H2targ.
    + unshelve (eexists).
      1: {
        abstract (apply (totally_composable_of_middle_arr 
        (fss:=_::_) (gss:=_::_) H1comp H2comp);
        rewrite H1targ, Hf1targ;
        apply (Nf_eq_in_of_norm_equiv Heq2)).
      }
      cbn [app proj_to_monarrlist_list fst].
      change (?x :: ?l ++ ?l') with ((x :: l) ++ l').
      unshelve (rewrite compose_totally_composable_app_nonempty);
      [abstract(easy)..|].
      apply monarr_norm_equiv_conj_struct'_iff.
      unfold compose_composable_monarr.
      apply monarr_norm_equiv_comp.
      * apply monarr_norm_equiv_struct_r'_iff.
        erewrite compose_totally_composable_indep.
        apply Heq1.
      * erewrite compose_totally_composable_indep.
        apply Heq2.
  - split; [simpl; f_equal; easy|].
    simpl.
    destruct (trim_foliate_monarr_helper f1) as [f1s f1_targ].
    destruct (trim_foliate_monarr_helper f2) as [f2s f2_targ].
    simpl in *.
    destruct IHf1 as (Hf1targ & H1targ & H1comp & Heq1).
    destruct IHf2 as (Hf2targ & H2targ & H2comp & Heq2).
    destruct f1s as [|f1h f1s], f2s as[|f2h f2s];
    (split; [try easy|]);
    cbn [proj_to_monarrlist_list fst snd zip_defaults] in *.
    + simpl in *.
      cbn [monarrlist_target fold_right map] in *.
      exists Logic.I.
      simpl in *.
      apply (monarr_norm_equiv_trans
        (monarr_norm_equiv_tens _ _ _ _ Heq1 Heq2)).
      rewrite 4!monarr_arrtens.
      apply monarr_norm_equiv_struct_eq_in.
      easy.
    + simpl.
      clear -H2targ.
      induction f2s; simpl.
      * etransitivity;
        [apply Nf_monarrlist_target_app'|].
        apply Nf_tens_eq; easy.
      * destruct f2s; 
        [|apply IHf2s,H2targ].
        etransitivity;
        [apply Nf_monarrlist_target_app'|].
        apply Nf_tens_eq; easy.
    + unfold proj_to_monarrlist_list at 2.
      exists (zip_with_default_l_totally_composable H2comp _).
      change (proj_to_monarrlist_list (?f, ?g)) with f.
      apply (monarr_norm_equiv_trans 
        (monarr_norm_equiv_tens _ _ _ _ Heq1 Heq2)).
      (* simpl (compose_totally_composable [[_]]). *)
      (* cbn beta. *)
      (* apply (monarr_norm_equiv_trans (monarr_norm_equiv_tens_assoc _ _ _)). *)
      refine (monarr_norm_equiv_trans _ 
        (monarr_norm_equiv_symm _ _
        (zip_with_default_l_norm_equiv_nonempty (fss:=_::_) 
          ltac:(easy) H2comp f1_targ))).
      apply monarr_norm_equiv_tens; [|easy].
      simpl.
      rewrite monarr_arrtens.
      apply monarr_norm_equiv_struct_eq_in; easy.
    + change (proj_to_monarrlist_list (?f, ?g)) with f.
      clear -H1targ.
      induction f1s; simpl.
      * etransitivity;
        [apply (Nf_monarrlist_target_app' [_])|].
        apply Nf_tens_eq; easy.
      * destruct f1s; 
        [|apply IHf1s,H1targ].
        etransitivity;
        [apply (Nf_monarrlist_target_app' [_])|].
        apply Nf_tens_eq; easy.
    + change (proj_to_monarrlist_list (?f, ?g)) with f.
      exists (zip_with_default_r_totally_composable H1comp _).
      apply (monarr_norm_equiv_trans 
        (monarr_norm_equiv_tens _ _ _ _ Heq1 Heq2)).
      simpl (compose_totally_composable [[_]]).
      cbn beta.
      (* apply (monarr_norm_equiv_trans (
          monarr_norm_equiv_symm _ _ (monarr_norm_equiv_tens_assoc _ _ _))). *)
      refine (monarr_norm_equiv_trans _ 
        (monarr_norm_equiv_symm _ _
        (zip_with_default_r_norm_equiv_nonempty (fss:=_::_) 
          ltac:(easy) H1comp f2_targ))).
      apply monarr_norm_equiv_tens; [easy|].
      rewrite monarr_arrtens.
      apply monarr_norm_equiv_struct_eq_in; easy.
    + rewrite <- zip_defaults_cons.
      pose proof (zip_defaults_target_nonempty
        (fss:=f2h::f2s) (gss:=f1h::f1s) ltac:(easy) ltac:(easy)) as e.
      rewrite Nf_tens_bwnormapp, H1targ, H2targ, <- Nf_tens_bwnormapp in e.
      rewrite <- e.
      apply zip_defaults_target_defaults_indep; easy.
    + eexists (zip_defaults_totally_composable' H2comp H1comp 
        (eq_sym H2targ) (eq_sym H1targ)).
      apply (monarr_norm_equiv_trans 
        (monarr_norm_equiv_tens _ _ _ _ Heq1 Heq2)).
      apply (
        (monarr_norm_equiv_symm _ _
        (tens_zip_defaults_correct_helper'' (fss:=f2h::f2s) (gss:=f1h::f1s) 
        ltac:(easy) ltac:(easy) H2comp H1comp 
        (eq_sym H2targ) (eq_sym H1targ)))).
  - repeat split; try easy.
    exists Logic.I.
    apply monarr_norm_equiv_symm.
    apply monarr_norm_equiv_tens_bwarr_e_l.
  - repeat split; try easy.
    exists Logic.I.
    apply monarr_norm_equiv_symm.
    simpl.
    rewrite monarr_arrtens.
    apply monarr_norm_equiv_struct_eq_out; easy.
Qed.

Import Lia.

Lemma trim_foliate_totally_composable {a b} (f : a ⟶ b) : 
  totally_composable (trim_foliate_monarr f).
Proof.
  apply trim_foliate_spec.
Qed.

Lemma trim_foliate_correct' {a b} (f : a ⟶ b) : 
  monarr_norm_equiv f
  (compose_totally_composable (trim_foliate_monarr f)
    (trim_foliate_totally_composable f)).
Proof.
  destruct (trim_foliate_spec f) as (? & ? & ? & ?).
  erewrite compose_totally_composable_indep.
  eassumption.
Qed.

Lemma trim_foliate_correct {a b} (f : a ⟶ b) : 
  f ≊
  bwarr_of_Nf_eq (Nf_eq_in_of_norm_equiv (trim_foliate_correct' f))
  ◌ compose_totally_composable (trim_foliate_monarr f)
    (trim_foliate_totally_composable f)
  ◌ bwarr_of_Nf_eq (eq_sym 
    (Nf_eq_out_of_norm_equiv (trim_foliate_correct' f))).
Proof.
  apply equiv_conj_of_monarr_norm_equiv, trim_foliate_correct'.
Qed.

Lemma is_empty_iff (a : bw) : is_empty a = true <-> Nf a = norm_e.
Proof.
  induction a; simpl in *; try easy.
  rewrite Bool.andb_true_iff.
  rewrite IHa1, IHa2.
  split.
  - rewrite Nf_tens_bwnormapp.
    intros [-> ->]; easy.
  - rewrite Nf_tens_bwnormapp.
    destruct (Nf a1), (Nf a2); easy.
Qed.

Lemma remove_empty_structs_proper : 
  unary_monarrlist_proper remove_empty_structs.
Proof.
  intros fs.
  induction fs as [|[] fs' IHfs]; [easy|..].
  - simpl.
    destruct (is_empty a) eqn:E.
    + apply (monarr_norm_equiv_trans
      (monarr_norm_equiv_symm _ _ 
      (monarr_norm_equiv_tens_bwarr_e_r _ (arrid e)))).
      apply monarr_norm_equiv_tens; [easy|].
      apply monarr_norm_equiv_struct_eq_in.
      simpl.
      rewrite is_empty_iff in E; rewrite E.
      easy.
    + apply monarr_norm_equiv_tens; easy.
  - apply monarr_norm_equiv_tens; easy.
Qed.

Lemma trim_foliate_no_empty_composable {a b} (f : a ⟶ b) :
  totally_composable (trim_foliate_monarr_no_empty f).
Proof.
  unfold trim_foliate_monarr_no_empty.
  apply monarrlist_list_proper_composable;
  [|apply trim_foliate_totally_composable].
  apply map_unary_proper_monarrlist_list_proper,
  remove_empty_structs_proper.
Qed.

Lemma trim_foliate_no_empty_correct' {a b} (f : a ⟶ b) : 
  monarr_norm_equiv f 
    (compose_totally_composable (trim_foliate_monarr_no_empty f)
    (trim_foliate_no_empty_composable f)).
Proof.
  apply (monarr_norm_equiv_trans (trim_foliate_correct' f)).
  erewrite (compose_totally_composable_indep (trim_foliate_monarr_no_empty f)).
  unfold trim_foliate_monarr_no_empty.
  refine (proper_preserves _ _).
  apply map_unary_proper_monarrlist_list_proper,
    remove_empty_structs_proper.
Qed.

End trim_foliation.

Section idarrs.

Lemma source_idarr_of_vars (xs : list X) : 
  source_vars (idarr_of_vars xs) = xs.
Proof.
  induction xs; [easy|].
  simpl; f_equal; easy.
Qed.

Lemma target_idarr_of_vars (xs : list X) : 
  target_vars (idarr_of_vars xs) = xs.
Proof.
  induction xs; [easy|].
  simpl; f_equal; easy.
Qed.

Lemma composable_idarr_of_target (fs : monarrlist) : 
  composable fs (idarr_of_vars (target_vars fs)).
Proof.
  rewrite composable_iff_varlist_eq.
  now rewrite source_idarr_of_vars.
Qed.

Lemma composable_idarr_of_source (fs : monarrlist) : 
  composable (idarr_of_vars (source_vars fs)) fs.
Proof.
  rewrite composable_iff_varlist_eq.
  now rewrite target_idarr_of_vars.
Qed.

Lemma target_source_idarr_of_vars (xs : list X) :
  monarrlist_target (idarr_of_vars xs)
  = monarrlist_source (idarr_of_vars xs).
Proof.
  induction xs; [easy|].
  simpl.
  unfold monarrlist_target, monarrlist_source in *.
  simpl.
  f_equal; easy.
Qed.

Lemma source_target_idarr_of_vars (xs : list X) :
  monarrlist_source (idarr_of_vars xs)
  = monarrlist_target (idarr_of_vars xs).
Proof.
  now rewrite target_source_idarr_of_vars.
Qed.

Lemma realize_idarr (xs : list X) : 
  stack_monarrlist (idarr_of_vars xs) ≊ 
  cast_bwarr eq_refl (source_target_idarr_of_vars xs) (arrid _).
Proof.
  induction xs; [apply monarr_struct|].
  simpl.
  rewrite IHxs.
  rewrite monarr_arrtens.
  apply monarr_struct.
Qed.

Lemma compose_composable_monarr_idarr_r 
  (gs : monarrlist) (xs : list X) (H : composable gs (idarr_of_vars xs)) : 
  monarr_norm_equiv 
    (compose_composable gs (idarr_of_vars xs) H)
    (stack_monarrlist gs).
Proof.
  exists eq_refl. 
  unshelve (eexists).
  rewrite target_source_idarr_of_vars; apply (eq_sym H).
  unfold compose_composable.
  rewrite monarr_id_l.
  rewrite realize_idarr.
  rewrite <- !monarr_assoc, !monarr_arrcomp.
  apply monarr_id_r.
Qed.

Lemma compose_composable_monarr_idarr_l
  (gs : monarrlist) (xs : list X) (H : composable (idarr_of_vars xs) gs) : 
  monarr_norm_equiv 
    (compose_composable (idarr_of_vars xs) gs H)
    (stack_monarrlist gs).
Proof.
  unshelve (eexists _, eq_refl).
  rewrite source_target_idarr_of_vars; apply (eq_sym H).
  unfold compose_composable.
  rewrite monarr_id_r.
  rewrite realize_idarr.
  rewrite !monarr_assoc, !monarr_arrcomp.
  apply monarr_id_l.
Qed.

Lemma source_target_is_idarrlist (fs : monarrlist) 
  (H : is_idarrlist fs = true) :
  monarrlist_source fs
  = monarrlist_target fs.
Proof.
  induction fs as [|a fs IHfs]; [easy|].
  destruct a; [|easy].
  simpl in H.
  unfold monarrlist_source, monarrlist_target in *.
  simpl.
  f_equal; auto.
Qed.

Lemma input_output_is_idarrlist {fs} (H : is_idarrlist fs = true) :
  monarrlist_source fs = monarrlist_target fs.
Proof.
  induction fs as [|[] fs]; [easy|..]; simpl in *; [|easy].
  unfold monarrlist_source, monarrlist_target.
  simpl.
  f_equal.
  apply IHfs, H.
Qed.

Lemma realize_idarrlist (fs : monarrlist) 
  (H : is_idarrlist fs = true) :
  stack_monarrlist fs ≊ 
  cast_bwarr eq_refl (source_target_is_idarrlist fs H) (arrid _). 
Proof.
  induction fs as [|a fs IHfs]; [apply monarr_struct|].
  simpl.
  destruct a; [|easy].
  simpl in H.
  rewrite (IHfs H).
  simpl.
  rewrite monarr_arrtens.
  apply monarr_struct.
Qed.

Lemma compose_composable_monarr_is_idarr_r {fs} (Hfs : is_idarrlist fs = true)
  {a b} (gs : a ⟶ b) (H : Nf b = Nf (monarrlist_source fs)) : 
  monarr_norm_equiv 
    (compose_composable_monarr gs (stack_monarrlist fs) H)
    gs.
Proof.
  exists eq_refl. 
  unshelve (eexists).
  rewrite <- (source_target_is_idarrlist _ Hfs); apply (eq_sym H).
  unfold compose_composable_monarr.
  rewrite (realize_idarrlist fs Hfs).
  rewrite <- !monarr_assoc, !monarr_arrcomp, monarr_id_l.
  apply monarr_id_r.
Qed.

Lemma compose_composable_monarr_is_idarr_l {fs} (Hfs : is_idarrlist fs = true)
  {a b} (gs : a ⟶ b) (H : Nf (monarrlist_target fs) = Nf a) : 
  monarr_norm_equiv 
    (compose_composable_monarr (stack_monarrlist fs) gs H)
    gs.
Proof.
  unshelve (eexists _, eq_refl).
  rewrite (source_target_is_idarrlist _ Hfs); apply (eq_sym H).
  unfold compose_composable_monarr.
  rewrite (realize_idarrlist fs Hfs).
  rewrite !monarr_assoc, !monarr_arrcomp, monarr_id_r.
  apply monarr_id_l.
Qed.

Lemma split_id_norm_equiv (a : bw) : 
  monarr_norm_equiv
    (stack_monarrlist (map monarrlist_id (map var (bw_to_varlist a))))
    (arrid a).
Proof.
  induction a;
  [apply monarr_norm_equiv_refl | apply monarr_norm_equiv_tens_bwarr_e_l | ].
  simpl.
  rewrite 2!map_app.
  apply (monarr_norm_equiv_trans (stack_monarrlist_app' _ _)).
  rewrite (monarr_struct _ (arrid a1 ⊠ arrid a2)).
  rewrite <- monarr_arrtens.
  apply monarr_norm_equiv_tens;
  assumption.
Qed.

Lemma split_ids_proper_unary : 
  unary_monarrlist_proper split_ids.
Proof.
  intros fss.
  induction fss as [|[] fss];
  [apply monarr_norm_equiv_refl|..];
  simpl;
  [|apply monarr_norm_equiv_tens;
    assumption + apply monarr_norm_equiv_refl].
  apply (monarr_norm_equiv_trans (stack_monarrlist_app' _ _)).
  apply monarr_norm_equiv_tens; [apply IHfss|].
  apply split_id_norm_equiv.
Qed.

End idarrs.

Section shift_left_right.

Lemma shift_left_proper : binary_monarrlist_proper shift_left.
Proof.
  intros fs gs H.
  unfold shift_left.
  destruct (is_idarrlist fs) eqn:E;
  [|exists H; easy].
  exists (composable_idarr_of_target gs).
  simpl.
  eapply (monarr_norm_equiv_trans);
  [apply (compose_composable_monarr_is_idarr_l E)|].
  apply monarr_norm_equiv_symm.
  apply compose_composable_monarr_idarr_r.
Qed.

Lemma shift_right_proper : binary_monarrlist_proper shift_right.
Proof.
  intros fs gs H.
  unfold shift_right.
  destruct (is_idarrlist gs) eqn:E;
  [|exists H; easy].
  exists (composable_idarr_of_source fs).
  simpl.
  eapply (monarr_norm_equiv_trans);
  [apply (compose_composable_monarr_is_idarr_r E)|].
  apply monarr_norm_equiv_symm.
  apply compose_composable_monarr_idarr_l.
Qed.

Lemma full_right_shift_proper :
  monarrlist_list_proper full_right_shift.
Proof.
  apply monarrlist_list_proper_iter'.
  apply monarrlist_list_proper_compose.
  + apply pairwise_apply_proper_binary_proper,
      pairify_apply_proper, shift_right_proper.
  + apply map_unary_proper_monarrlist_list_proper,
      split_ids_proper_unary.
Qed.

End shift_left_right.

Section structify.

Import Bool.

Lemma struct_of_is_struct_indep {a b} (f : a ⟶ b) 
  (H G : is_struct f = true) : 
  struct_of_is_struct f H = struct_of_is_struct f G.
Proof.
  rewrite (uip H G).
  easy.
Qed.

Lemma is_struct_structify {a b} (f : a ⟶ b) : 
  is_struct f = is_struct (structify f).
Proof.
  induction f; try reflexivity;
    simpl;
    destruct (bool_dec (is_struct (structify f1)) true);
    destruct (bool_dec (is_struct (structify f2)) true);
    simpl; try congruence;
    apply andb_true_iff; split; congruence.
Qed.

Lemma structify_of_is_struct {a b} (f : a ⟶ b) 
  (H : is_struct f = true) :
  structify f = struct_of_is_struct f H.
Proof.
  induction f; try reflexivity + discriminate;
  simpl in H;
  pose proof H as G;
  rewrite (andb_true_iff _ _) in G;
  destruct G as [Hl Hr];
  simpl structify;
  rewrite (IHf1 Hl), (IHf2 Hr);
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab; [|pose proof @is_struct_structify; congruence]
  end;
  simpl;
  erewrite struct_of_is_struct_indep, (struct_of_is_struct_indep f2);
  reflexivity.
Qed.


Lemma struct_of_is_struct_equiv {a b} (f : a ⟶ b) 
  (H : is_struct f = true) : 
  struct_of_is_struct f H ≊ f.
Proof.
  symmetry.
  induction f; [..|discriminate|reflexivity];
  pose proof H as G;
  simpl in G;
  rewrite andb_true_iff in G; destruct G as [Hl Hr];
  rewrite (IHf1 Hl), (IHf2 Hr) at 1;
  simpl;
  [ rewrite <- monarr_arrcomp
  | rewrite <- monarr_arrtens ];
  erewrite struct_of_is_struct_indep, (struct_of_is_struct_indep f2);
  reflexivity.
Qed.

Lemma structify_equiv {a b} (f : a ⟶ b) : 
  f ≊ structify f.
Proof.
  induction f; try reflexivity;
  rewrite IHf1, IHf2 at 1;
  simpl;
  repeat match goal with 
  |- context[match ?eqab with | left _ => _ | right _ => _ end] =>
      destruct eqab
  end; try reflexivity.
  - rewrite <- monarr_arrcomp.
    rewrite 2!struct_of_is_struct_equiv by easy.
    easy.
  - rewrite <- monarr_arrtens.
    rewrite 2!struct_of_is_struct_equiv by easy.
    easy.
Qed.

Lemma structify_proper : unary_monarrlist_proper structify_monarrlist.
Proof.
  apply map_monarr_proper_unary_proper.
  intros; apply structify_equiv.
Qed.

Lemma remove_struct_proper (g : monarrlistelt) : 
  monarr_norm_equiv 
  (realize_monarrlistelt (remove_struct g)) 
  (realize_monarrlistelt g).
Proof.
  destruct g; [apply monarr_norm_equiv_refl|].
  simpl.
  destruct f; [apply monarr_norm_equiv_refl..|].
  unfold monarr_norm_equiv.
  exists eq_refl, (Nf_eq_of_arr f).
  simpl.
  rewrite !monarr_arrcomp.
  apply monarr_struct.
Qed.

Lemma remove_structs_proper : 
  unary_monarrlist_proper remove_structs.
Proof.
  apply map_elt_proper_unary_proper.
  exact remove_struct_proper.
Qed.

End structify.

Section trim_idarrs.

Lemma source_trim_idarrs_helper fs fss : 
  monarrlist_list_source (trim_idarrs_helper fs fss)
  = monarrlist_list_source (fs :: fss).
Proof.
  revert fs;
  induction fss; intros fs; [easy|simpl].
  destruct (is_idarrlist a); 
  easy + apply IHfss.
Qed.

Lemma target_trim_idarrs_helper fs fss (H : totally_composable (fs :: fss)) : 
  Nf (monarrlist_list_target (trim_idarrs_helper fs fss))
  = Nf (monarrlist_list_target (fs :: fss)).
Proof.
  revert fs H;
  induction fss; intros fs H; [easy|simpl].
  destruct (is_idarrlist a) eqn:e; [|easy].
  apply source_target_is_idarrlist in e.
  rewrite <- e. 
  rewrite IHfss.
  - destruct fss; easy + apply H.
  - apply (totally_composable_helper_swap 
      (eq_sym (eq_trans (proj1 H) (f_equal Nf e)))).
    apply H.
Qed.

Lemma trim_idarrs_helper_composable {fs fss} 
  (H : totally_composable (fs :: fss)) : 
  totally_composable (trim_idarrs_helper fs fss).
Proof.
  revert fs H; induction fss; intros fs H; [easy|].
  simpl.
  destruct (is_idarrlist a) eqn:e; [|apply H].
  apply source_target_is_idarrlist in e.
  apply IHfss.
  apply (totally_composable_helper_swap 
    (eq_sym (eq_trans (proj1 H) (f_equal Nf e)))).
  apply H.
Qed.

Lemma trim_idarrs_helper_equiv {fs fss} 
  (H : totally_composable (fs :: fss)) :
  monarr_norm_equiv
    (compose_totally_composable _ H)
    (compose_totally_composable _ (trim_idarrs_helper_composable H)).
Proof.
  revert fs H; induction fss; intros fs H; [easy|].
  generalize (trim_idarrs_helper_composable H).
  destruct fss.
  - simpl.
    destruct (is_idarrlist a) eqn:e.
    + simpl.
      intros _.
      apply (compose_composable_monarr_is_idarr_r e).
    + intros ?.
      simpl.
      erewrite compose_composable_monarr_indep; easy.
  - simpl.
    destruct (is_idarrlist a) eqn:e; intros Hc.
    + erewrite (totally_composable_indep _ Hc).
      eapply monarr_norm_equiv_trans;
      [|refine (IHfss fs _)].
      2: {
        abstract (split; [|apply H];
        unfold composable;
        rewrite (proj1 H);
        rewrite (source_target_is_idarrlist _ e);
        apply H).
      }
      simpl.
      apply monarr_norm_equiv_comp_composable; [easy|].
      erewrite (totally_composable_indep (m::fss) (proj2 (proj2 H))).
      apply (compose_composable_monarr_is_idarr_l e).
    + erewrite (totally_composable_indep _ H Hc).
      easy.
Qed.

Lemma trim_idarrs_composable {fss} (H : totally_composable fss) :
  totally_composable (trim_idarrs fss).
Proof.
  destruct fss; [easy|apply trim_idarrs_helper_composable, H].
Qed.

Lemma trim_idarrs_equiv {fss} (H : totally_composable fss) :
  monarr_norm_equiv
    (compose_totally_composable fss H)
    (compose_totally_composable (trim_idarrs fss) (trim_idarrs_composable H)).
Proof.
  destruct fss; [easy|]. 
  erewrite (compose_totally_composable_indep (trim_idarrs _)).
  apply trim_idarrs_helper_equiv.
Qed.

Lemma trim_idarrs_proper : monarrlist_list_proper trim_idarrs.
Proof.
  intros fss H.
  exists (trim_idarrs_composable H).
  apply trim_idarrs_equiv.
Qed.

Lemma trim_idarr_proper : monarrlist_list_proper trim_idarr.
Proof.
  intros fs Hfs.
  unshelve (eexists).
  - abstract (destruct fs; [easy|]; destruct fs; [easy|];
    simpl;
    destruct (is_idarrlist m);
    apply Hfs).
  - destruct fs; [easy|]; destruct fs; [easy|];
    simpl.
    generalize (trim_idarr_proper_subproof (m::m0::fs) Hfs).
    simpl.
    destruct (is_idarrlist m) eqn:e;
    [|intros; erewrite (compose_totally_composable_indep _ t Hfs); easy].
    intros.
    erewrite (compose_totally_composable_indep _ t (proj2 Hfs)).
    apply compose_composable_monarr_is_idarr_l, e.
Qed.

End trim_idarrs.

Section filter_idarrs.

Lemma totally_composable_filter_idarrs {fss} :
  totally_composable (fss) -> 
  totally_composable (filter_idarrs fss).
Proof.
  destruct fss as [|fs fss]; [easy|].
  revert fs.
  (* intros H. *)
  induction fss as [|fs' fss]; [easy|];
  intros fs H.
  simpl.
  destruct (is_idarrlist fs') eqn:e; simpl.
  - apply IHfss.
    refine (totally_composable_helper_swap _ (proj2 H)).
    rewrite <- (input_output_is_idarrlist e).
    symmetry.
    apply H.
  - split; [apply H|].
    apply IHfss, H.
Qed.

Fixpoint list_iter_map {A} (f : list A -> list A) (l : list A) := 
  match l with
  | nil => nil
  | a :: l' => f (a :: list_iter_map f l')
  end.

Lemma trim_idarrs_helper_filter_not_idarrlist fs fss :
  trim_idarrs_helper fs (filter (fun x => negb (is_idarrlist x)) fss) =
  fs :: filter (fun x => negb (is_idarrlist x)) fss.
Proof.
  revert fs;
  induction fss; [easy|]; intros fs.
  simpl.
  destruct (is_idarrlist a) eqn:e;
  [apply IHfss|].
  simpl.
  rewrite e.
  easy.
Qed.

Lemma filter_idarrs_trim fss :
  filter_idarrs fss = list_iter_map trim_idarrs fss.
Proof.
  induction fss as [|fs fss IHfss]; [easy|].
  simpl.
  rewrite <- IHfss.
  clear IHfss.
  destruct fss as [|fs' fss]; [easy|].
  simpl.
  destruct (is_idarrlist fs') eqn:e; simpl; [|easy].
  now rewrite trim_idarrs_helper_filter_not_idarrlist.
Qed.

Lemma totally_composable_helper_of_totally_composable {a fs} :
  totally_composable fs -> 
  Nf (monarrlist_target a) = Nf (monarrlist_list_source fs) ->
  totally_composable_helper a fs.
Proof.
  destruct fs; easy.
Qed.

Lemma list_iter_map_proper {f} (Hf : monarrlist_list_proper f) :
  monarrlist_list_proper (list_iter_map f).
Proof.
  intros fss Hfss.
  match goal with |- ?G => enough (
  (forall a, totally_composable (a :: fss) -> 
  totally_composable (a :: list_iter_map f fss)) /\ G)
  by easy
  end.
  induction fss; [intros; split; try exists Logic.I; easy|].
  split; [|unshelve (eexists)].
  - intros b. 
    intros Hcompba. 
    destruct (Hf (a :: fss) Hfss) as (Hcomp & Hin & _).
    apply totally_composable_helper_of_totally_composable.
    + apply Hf.
      apply (IHfss (totally_composable_of_cons Hfss)), Hfss.
    + simpl.
      destruct (Hf _ (proj1 (IHfss (totally_composable_of_cons Hfss)) a Hfss))
        as (Hcomp' & Hin' & Hout' & _).
      rewrite Hin'.
      apply Hcompba.
  - abstract (destruct (IHfss (totally_composable_of_cons Hfss)) as 
    [_ (Hcomp & Hin & Hout & Heq)];
    simpl;
    apply Hf;
    destruct fss; [easy|];
    apply (totally_composable_helper_of_totally_composable Hcomp);
    rewrite Hin;
    apply Hfss).
  - specialize (IHfss (totally_composable_of_cons Hfss)) as IHfss'.
    destruct (Hf _ (proj1 IHfss' a Hfss)) as 
      (Hcomp & Hequiv).
    erewrite (compose_totally_composable_indep _ (_ _)). 
    refine (monarr_norm_equiv_trans _ Hequiv).
    generalize (proj1 IHfss' a Hfss).
    destruct (list_iter_map f fss) eqn:e.
    + destruct fss; [easy|].
      intros ?.
      rewrite compose_totally_composable_cons.
      rewrite <- (monarr_runit (compose_totally_composable [a] _)).
      unfold compose_composable_monarr.
      apply monarr_norm_equiv_comp.
      * apply monarr_norm_equiv_struct_r.
      * destruct (proj2 (IHfss (proj2 Hfss))) as [? Heq].
        refine (monarr_norm_equiv_trans Heq _).
        apply monarr_norm_equiv_struct_eq_in.
        pose proof (proj2 (IHfss (proj2 Hfss))) as H.
        rewrite <- e in H.
        destruct H as (? & Hin & _).
        rewrite e in Hin.
        rewrite Hin.
        symmetry.
        apply Hfss.
    + destruct fss; [easy|].
      intros t.
      rewrite 2!compose_totally_composable_cons.
      apply monarr_norm_equiv_comp_composable; [easy|].
      destruct (proj2 IHfss') as [? Heq].
      erewrite (compose_totally_composable_indep (m::l) (proj2 t)).
      erewrite (compose_totally_composable_indep (m0::fss) (proj2 Hfss)).
      apply Heq.
Qed.

Lemma filter_idarrs_proper :
  monarrlist_list_proper filter_idarrs.
Proof.
  intros fss.
  rewrite filter_idarrs_trim.
  apply list_iter_map_proper.
  apply trim_idarrs_proper.
Qed.

End filter_idarrs.

Section full_process.

Lemma full_process_monarrlist_list_proper : 
  monarrlist_list_proper full_process_monarrlist_list.
Proof.
  unfold full_process_monarrlist_list.
  repeat match goal with
  | |- monarrlist_list_proper (Basics.compose _ _) =>
    apply monarrlist_list_proper_compose
  | |- monarrlist_list_proper (map _) => 
    apply map_unary_proper_monarrlist_list_proper
  end.
  - apply structify_proper.
  - apply remove_structs_proper.
  - apply split_ids_proper_unary.
  - apply full_right_shift_proper.
  - apply trim_idarrs_proper.
  - apply trim_idarr_proper.
Qed.

Lemma full_process_in_pf {a b} (f : a ⟶ b) : 
  Nf a = Nf (monarrlist_list_source 
  (full_process_monarrlist_list (foliate_monarr f))).
Proof.
  rewrite <- (Nf_eq_in_of_norm_equiv 
    (proper_preserves full_process_monarrlist_list_proper
      (foliate_monarr_totally_composable f))).
  rewrite monarrlist_list_source_foliate.
  easy.
Qed.

Lemma full_process_out_pf {a b} (f : a ⟶ b) : 
  Nf (monarrlist_list_target 
  (full_process_monarrlist_list (foliate_monarr f)))
  = Nf b.
Proof.
  rewrite <- (Nf_eq_out_of_norm_equiv 
    (proper_preserves full_process_monarrlist_list_proper
      (foliate_monarr_totally_composable f))).
  rewrite monarrlist_list_target_foliate.
  easy.
Qed.

Definition full_process_monarr {a b} (f : a ⟶ b) :=
  compose_totally_composable (full_process_monarrlist_list (foliate_monarr f))
    (monarrlist_list_proper_composable full_process_monarrlist_list_proper
      (foliate_monarr_totally_composable f)).

Lemma full_process_monarr_equiv {a b} (f : a ⟶ b) :
  f ≊
  bwarr_of_Nf_eq (full_process_in_pf f)
  ◌ full_process_monarr f
  ◌ bwarr_of_Nf_eq (full_process_out_pf f).
Proof.
  apply equiv_conj_of_monarr_norm_equiv.
  unfold full_process_monarr.
  apply (monarr_norm_equiv_trans (foliate_correct' f)).
  apply proper_preserves.
Qed.

End full_process.

End ProperOperationInstances.