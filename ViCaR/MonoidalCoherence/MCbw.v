Require Import MCDefinitions.
Require UIP_facts.
Require MC_Cat_Thy_temp.
Require CatExample. (* FunctorCategory *)


Section bw_theory.

Set Universe Polymorphism.

Import MC_notations MC_setoids.

Open Scope bw_scope.

Polymorphic Context {X : Type}.
#[local] Set Universe Polymorphism.
Local Notation bw := (bw X).
Local Notation bwnorm := (bwnorm X).
Local Notation cast_bwarr := (@cast_bwarr X).

Section bwnorm_theory.

Lemma varlist_to_bwnorm_app (l l' : list X) :
  varlist_to_bwnorm (l ++ l') = 
  bwnormapp (varlist_to_bwnorm l') (varlist_to_bwnorm l).
Proof.
  induction l; [easy|].
  now simpl; f_equal.
Qed.

Lemma Nf_tens (b c : bw) : 
  Nf (b ⨂ c) = ⟦c⟧ (Nf b).
Proof.
  easy.
Qed.

Lemma Nf_tens_assoc (b c d : bw) : 
  Nf (b ⨂ (c ⨂ d)) = Nf (b ⨂ c ⨂ d).
Proof.
  easy.
Qed.

Lemma bwnormapp_lnorme (n : bwnorm) : 
  bwnormapp norm_e n = n.
Proof.
  now induction n; auto; simpl; f_equal.
Qed.

Lemma bwnormapp_assoc (n m o : bwnorm) : 
  bwnormapp n (bwnormapp m o) = bwnormapp (bwnormapp n m) o.
Proof.
  induction o; [easy|].
  now simpl; f_equal.
Qed.

Lemma bwnorm_to_varlist_to_bwnorm (a : bwnorm) : 
  varlist_to_bwnorm (bwnorm_to_varlist a) = a.
Proof.
  induction a; [easy|].
  now simpl; f_equal.
Qed.

Lemma varlist_to_bwnorm_to_varlist (a : list X) : 
bwnorm_to_varlist (varlist_to_bwnorm a) = a.
Proof.
  induction a; [easy|].
  now simpl; f_equal.
Qed.

Lemma varlist_to_bwnorm_inj (a b : list X) : 
  varlist_to_bwnorm a = varlist_to_bwnorm b -> a = b.
Proof.
  intros H;
  apply (f_equal bwnorm_to_varlist) in H.
  rewrite !varlist_to_bwnorm_to_varlist in H.
  easy.
Qed.

Lemma bwnorm_to_varlist_inj (a b : bwnorm) :
  bwnorm_to_varlist a = bwnorm_to_varlist b -> a = b.
Proof.
  intros H; 
  apply (f_equal varlist_to_bwnorm) in H.
  rewrite !bwnorm_to_varlist_to_bwnorm in H.
  easy.
Qed.


Lemma varlist_to_bwnorm_eq_iff (a b : list X) : 
  varlist_to_bwnorm a = varlist_to_bwnorm b <-> a = b.
Proof.
  split.
  - apply varlist_to_bwnorm_inj.
  - intros; subst; easy.
Qed.

Lemma bwnorm_eq_iff_varlist_eq {a b : bwnorm} : 
  a = b <-> bwnorm_to_varlist a = bwnorm_to_varlist b.
Proof.
  rewrite <- varlist_to_bwnorm_eq_iff.
  rewrite !bwnorm_to_varlist_to_bwnorm.
  easy.
Qed.

Lemma Nf_tens_bwnormapp (b c : bw) : 
  Nf (b ⨂ c) = bwnormapp (Nf b) (Nf c).
Proof.
  revert b; induction c; intros b; [easy..|].
  rewrite Nf_tens_assoc.
  rewrite Nf_tens, IHc1, IHc2.
  rewrite bwnormapp_assoc.
  rewrite <- IHc1, <- IHc2.
  easy.
Qed.

Lemma Nf_tens_eq {a b c d : bw} (H : Nf a = Nf b) (H' : Nf c = Nf d) : 
  Nf (a ⨂ c) = Nf (b ⨂ d).
Proof.
  rewrite 2!Nf_tens_bwnormapp, H, H'.
  easy.
Qed.

Lemma Nf_eq_bwnorm_of_varlist (b : bw) :
  Nf b = varlist_to_bwnorm (bw_to_varlist b).
Proof.
  induction b as [|a|b IHb c IHc]; [easy.. |].
  rewrite Nf_tens_bwnormapp.
  simpl.
  rewrite varlist_to_bwnorm_app.
  now f_equal.
Qed.

Lemma bwnorm_to_varlist_Nf (b : bw) : 
  bwnorm_to_varlist (Nf b) = bw_to_varlist b.
Proof.
  rewrite (f_equal bwnorm_to_varlist (Nf_eq_bwnorm_of_varlist b)).
  now rewrite varlist_to_bwnorm_to_varlist.
Qed.


Lemma bwbrac_bwnorm (a b : bwnorm) : ⟦a⟧ b = bwnormapp b a.
Proof.
  induction a; [easy|].
  simpl; f_equal; easy.
Qed.

Lemma Nf_bwnorm (a : bwnorm) : Nf a = a.
Proof.
  unfold Nf.
  now rewrite bwbrac_bwnorm, bwnormapp_lnorme.
Qed.

Lemma bw_of_bwnorm_inj (n m : bwnorm) : @eq bw n m -> n = m.
Proof.
  intros H.
  apply (f_equal Nf) in H.
  rewrite !Nf_bwnorm in H.
  easy.
Qed.

Lemma Nf_eq_iff_varlist_eq (a b : bw) : 
  Nf a = Nf b <-> bw_to_varlist a = bw_to_varlist b.
Proof.
  rewrite 2!Nf_eq_bwnorm_of_varlist.
  apply varlist_to_bwnorm_eq_iff.
Qed.

Import List ListNotations.

Lemma bw_to_varlist_fold_right (fs : list bw) :
  bw_to_varlist (fold_right (fun a n => n ⨂ a) e fs) = 
  concat (map bw_to_varlist fs).
Proof.
  induction fs; [easy|].
  simpl.
  f_equal.
  easy.
Qed.

Lemma varlist_fold_right_tens hd tl : 
  bw_to_varlist (X:=X) (fold_right (fun a n => n ⨂ a) e (hd ++ tl)) =
  bw_to_varlist (fold_right (fun a n => n ⨂ a) e hd)
  ++ bw_to_varlist (fold_right (fun a n => n ⨂ a) e tl).
Proof.
  induction hd; [easy|].
  simpl. 
  rewrite IHhd.
  apply app_assoc.
Qed.

Lemma Nf_fold_right_tens hd tl : 
  Nf (fold_right (fun a n => n ⨂ a) e (hd ++ tl)) =
  bwnormapp (X:=X) 
    (Nf (fold_right (fun a n => n ⨂ a) e tl))
    (Nf (fold_right (fun a n => n ⨂ a) e hd)).
Proof.
  rewrite 3!Nf_eq_bwnorm_of_varlist.
  rewrite 3!bw_to_varlist_fold_right.
  rewrite map_app, concat_app.
  rewrite varlist_to_bwnorm_app.
  easy.
Qed.

(* Lemma bwnormapp_tens_l a b x :
  bwnormapp (X:=X) (norm_rtens a x) b = 
  bwnormapp a (bwnormapp (norm_rtens norm_e x) b).
Proof.
  now rewrite bwnormapp_assoc.
Qed.

Lemma bwnormapp_cancel_var_l {x} {b c : bwnorm} : 
  bwnormapp (bwnormapp (norm_rtens norm_e x) b)
  = bwnormapp (bwnormapp (norm_rtens norm_e x) c) -> b = c.
Proof.
   *)

Lemma bwnorm_to_varlist_app (a b : bwnorm) :
  bwnorm_to_varlist (bwnormapp a b) = 
  bwnorm_to_varlist b ++ bwnorm_to_varlist a.
Proof.
  apply varlist_to_bwnorm_inj.
  rewrite varlist_to_bwnorm_app.
  rewrite !bwnorm_to_varlist_to_bwnorm.
  easy.
Qed.

Lemma bwnormapp_cancel_l {a b c : bwnorm} : 
  bwnormapp a b = bwnormapp a c -> b = c.
Proof.
  rewrite !bwnorm_eq_iff_varlist_eq.
  rewrite !bwnorm_to_varlist_app.
  apply app_inv_tail.
Qed.

Lemma bwnormapp_cancel_r {a b c : bwnorm} : 
  bwnormapp b a = bwnormapp c a -> b = c.
Proof.
  rewrite !bwnorm_eq_iff_varlist_eq.
  rewrite !bwnorm_to_varlist_app.
  apply app_inv_head.
Qed.

Lemma Nf_cancel_tens_l {a b c : bw} : 
  Nf (a ⨂ b) = Nf (a ⨂ c) -> Nf b = Nf c.
Proof.
  rewrite !Nf_tens_bwnormapp.
  apply bwnormapp_cancel_l.
Qed.

Lemma Nf_cancel_tens_r {a b c : bw} : 
  Nf (b ⨂ a) = Nf (c ⨂ a) -> Nf b = Nf c.
Proof.
  rewrite !Nf_tens_bwnormapp.
  apply bwnormapp_cancel_r.
Qed.

End bwnorm_theory.


Lemma bwbrac_of_bweq (a b : bw) : a ~ b ->
  forall n : bwnorm, ⟦a⟧ n = ⟦b⟧ n.
Proof.
  intros H.
  induction H; 
    auto;
    intros n.
  - simpl.
    rewrite IHbweq1.
    apply IHbweq2.
  - etransitivity; eauto.
Qed.

Lemma bwnorm_ltens_bw_eq (a : bw) : forall n : bwnorm,
  (tens n a) ~ (bwbrac a n).
Proof.
  induction a; [repeat constructor..|].
  eauto using IHa1, IHa2 with bwdb.
Qed.

Lemma bweq_Nf (a : bw) : a ~ (Nf a).
Proof.
  transitivity (tens e a);
  [do 2 constructor |].
  apply (bwnorm_ltens_bw_eq a (norm_e)).
Qed.

Lemma Nf_eq_iff_bweq (a b : bw) : 
  Nf a = Nf b <-> a ~ b.
Proof.
  split.
  - intros Heq.
    transitivity (Nf a).
    1: apply bweq_Nf.
    rewrite Heq.
    symmetry.
    apply bweq_Nf.
  - intros H; induction H; try easy + (etransitivity; eauto).
    rewrite 2!Nf_tens_bwnormapp.
    f_equal; easy.
Qed.


Section bwarr_theory.

Local Notation "a '⟶' b" := (@bwarr X a b) 
  (at level 60) : type_scope. (* \longrightarrow *)

Lemma bweq_of_arr {a b : bw} : a ⟶ b -> a ~ b.
Proof.
  intros f.
  induction f; eauto with bwdb.
Qed.

Lemma ex_arr_of_bweq {a b : bw} : a ~ b -> exists (f:a ⟶ b), True.
Proof.
  intros H.
  induction H; try (destruct IHbweq); try (destruct IHbweq1, IHbweq2); 
  eexists; eauto 2 using bwarrinv with bwdb.
Qed.

Lemma bweq_iff_ex_arr {a b : bw} : a ~ b <-> exists (f:a ⟶ b), True.
Proof.
  split; [apply ex_arr_of_bweq|].
  intros [f _]; apply bweq_of_arr; easy.
Qed.


Lemma bwarrinv_invol {A B} (h : A ⟶ B) : 
  bwarrinv (bwarrinv h) = h.
Proof.
  induction h; try easy; simpl; rewrite IHh1, IHh2; easy.
Qed.

Lemma bwarrinv_linv {A B} (h : A ⟶ B) : arrcomp (bwarrinv h) h ≅ arrid B.
Proof.
  induction h; [eauto 3 with bwarrdb .. ]; simpl.
  - rewrite bwarr_assoc, <- (bwarr_assoc (bwarrinv h1)), IHh1; eauto with bwarrdb.
  - rewrite <- bwarr_tens_comp, <- bwarr_tens_id.
    apply bwarr_tens; auto.
Qed.

Lemma bwarrinv_rinv {A B} (h : A ⟶ B) : arrcomp h (bwarrinv h) ≅ arrid A.
Proof.
  induction h; [eauto 3 with bwarrdb .. ]; simpl.
  - rewrite bwarr_assoc, <- (bwarr_assoc h2), IHh2; eauto with bwarrdb.
  - rewrite <- bwarr_tens_comp, <- bwarr_tens_id.
    apply bwarr_tens; auto.
Qed.

Lemma bwinv_unique {a b} (f : a ⟶ b) (g g' : b ⟶ a) : 
  arrcomp f g ≅ arrid a -> arrcomp g' f ≅ arrid b ->
  g ≅ g'.
Proof.
  intros Hfg Hg'f.
  rewrite <- (bwarr_lunit g), <- Hg'f.
  rewrite bwarr_assoc, Hfg.
  eauto 3 with bwarrdb.
Qed.

Lemma bwinv_unique' {a b} (f : a ⟶ b) (g g' : b ⟶ a) : 
  arrcomp g f ≅ arrid b -> arrcomp f g' ≅ arrid a ->
  g ≅ g'.
Proof.
  intros Hgf Hfg'.
  symmetry.
  eapply bwinv_unique; eauto.
Qed.

#[global] Add Parametric Morphism {A B} : (@bwarrinv X A B) 
  with signature
  (bwarrequiv A B) ==> (bwarrequiv B A)
  as bwarrinv_mor.
Proof.
  intros x y Hxy.
  apply bwinv_unique with x.
  - apply bwarrinv_rinv.
  - rewrite Hxy.
    apply bwarrinv_linv.
Qed.

Lemma by_bwarrinv {a b : bw} (f f' : a ⟶ b) :
  bwarrinv f ≅ bwarrinv f' -> f ≅ f'.
Proof.
  intros H.
  rewrite <- (bwarrinv_invol f), <- (bwarrinv_invol f').
  rewrite H.
  easy.
Qed.



Lemma bwarr_invassoc_natl {a b c a' b' c'} (f : a' ⟶ a) 
  (g : b' ⟶ b) (h : c' ⟶ c) :
  arrcomp (arrtens (arrtens f g) h) (arrinvassoc a b c) 
  ≅ arrcomp (arrinvassoc a' b' c') (arrtens f (arrtens g h)).
Proof.
  apply by_bwarrinv, bwarr_assoc_nat.
Qed.

Lemma bwarr_invlunitor_natl {a b} (f : b ⟶ a) :
  arrcomp f (arrinvlunitor a)
  ≅ arrcomp (arrinvlunitor b) (arrtens (arrid e) f).
Proof.
  apply by_bwarrinv, bwarr_lunitor_nat.
Qed.

Lemma bwarr_invrunitor_natl {a b} (f : b ⟶ a) :
  arrcomp f (arrinvrunitor a)
  ≅ arrcomp (arrinvrunitor b) (arrtens f (arrid e)).
Proof.
  apply by_bwarrinv, bwarr_runitor_nat.
Qed.

Lemma bwarr_invpentagonl (a b c d : bw) : 
  arrcomp (arrinvassoc (a ⨂ b) c d) (arrinvassoc a b (c ⨂ d))
  ≅ arrcomp (arrtens (arrinvassoc a b c) (arrid d))
    (arrcomp (arrinvassoc a (b ⨂ c) d)
       (arrtens (arrid a) (arrinvassoc b c d))).
Proof.
  apply by_bwarrinv, bwarr_pentagon.
Qed.

Lemma bwarr_invtrianglel' (a b : bw) : 
  arrcomp (arrinvassoc a e b) (arrtens (arrid a) (arrlunitor b))
  ≅ arrtens (arrrunitor a) (arrid b).
Proof.
  rewrite <- (bwarr_triangle a b).
  rewrite <- bwarr_assoc, bwarr_assoc_linv, bwarr_lunit.
  easy.
Qed.

Lemma arrtens_pushout_top {a b c d e : bw} (f : a ⟶ b) (g : b ⟶ c) (h : d ⟶ e) :
  arrtens (arrcomp f g) h
  ≅ arrcomp (arrtens f h) (arrtens g (arrid e)).
Proof.
  rewrite <- bwarr_tens_comp, bwarr_runit.
  easy.
Qed.

Lemma arrtens_pushin_top {a b c d e : bw} (f : a ⟶ b) (g : b ⟶ c) (h : d ⟶ e) :
  arrtens (arrcomp f g) h
  ≅ arrcomp (arrtens f (arrid d)) (arrtens g h).
Proof.
  rewrite <- bwarr_tens_comp, bwarr_lunit.
  easy.
Qed.

  Lemma arrtens_pushout_bot {a b c d e : bw} (f : a ⟶ b) (g : c ⟶ d) (h : d ⟶ e) :
  arrtens f (arrcomp g h) 
  ≅ arrcomp (arrtens f g) (arrtens (arrid b) h).
Proof.
  rewrite <- bwarr_tens_comp, bwarr_runit.
  easy.
Qed.

Lemma arrtens_pushin_bot {a b c d e : bw} (f : a ⟶ b) (g : c ⟶ d) (h : d ⟶ e) :
  arrtens f (arrcomp g h) 
  ≅ arrcomp (arrtens (arrid a) g) (arrtens f h).
Proof.
  rewrite <- bwarr_tens_comp, bwarr_lunit.
  easy.
Qed.

Lemma arrtens_split_diag {a b a' b'} (f : a ⟶ a') (g : b ⟶ b') :
  f ⊠ g ≅ f ⊠ arrid b ○ arrid a' ⊠ g.
Proof.
  rewrite <- bwarr_tens_comp, bwarr_lunit, bwarr_runit.
  easy.
Qed.



Lemma bwarr_trianglel' (a b : bw) :
  arrassoc a e b ≅ arrid a ⊠ arrlunitor b ○ arrinvrunitor a ⊠ arrid b.
Proof.
  rewrite <- (bwarr_runit (arrassoc a e b)), <- bwarr_tens_id,
    <- (bwarr_runitor_rinv), arrtens_pushout_top, <- bwarr_assoc,
    bwarr_triangle.
  easy.
Qed.

Lemma bwarr_compose_l {a b c} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) :
  f ○ g ≅ h <-> g ≅ bwarrinv f ○ h.
Proof.
  split; intros H; [rewrite <- H | rewrite H];
  rewrite <- bwarr_assoc, ?bwarrinv_linv, ?bwarrinv_rinv, bwarr_lunit;
  easy.
Qed.

Lemma bwarr_compose_l' {a b c} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) :
  h ≅ f ○ g <-> bwarrinv f ○ h ≅ g.
Proof.
  split; symmetry; apply bwarr_compose_l; symmetry; assumption.
Qed.

Lemma bwarr_compose_r {a b c} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) :
  f ○ g ≅ h <-> f ≅ h ○ bwarrinv g.
Proof.
  split; intros H; [rewrite <- H | rewrite H];
  rewrite bwarr_assoc, ?bwarrinv_linv, ?bwarrinv_rinv, bwarr_runit;
  easy.
Qed.

Lemma bwarr_compose_r' {a b c} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) :
  h ≅ f ○ g <-> h ○ bwarrinv g ≅ f.
Proof.
  split; symmetry; apply bwarr_compose_r; symmetry; assumption.
Qed.

Lemma bwarr_compose_cancel_l {a b c} (f : a ⟶ b) (g h : b ⟶ c) :
  f ○ g ≅ f ○ h -> g ≅ h.
Proof.
  intros H.
  rewrite  <- (bwarr_lunit g),  <- (bwarr_lunit h), 
    <- (bwarrinv_linv f), bwarr_assoc, H.
  eauto with bwarrdb.
Qed.

Lemma bwarr_compose_cancel_r {a b c} (f g : a ⟶ b) (h : b ⟶ c) :
  f ○ h ≅ g ○ h -> f ≅ g.
Proof.
  intros H.
  rewrite <- (bwarr_runit f), <- (bwarr_runit g), <- (bwarrinv_rinv h), 
    <- bwarr_assoc, H.
  eauto with bwarrdb.
Qed.

Lemma bwarr_compose_cancel_l_iff {a b c} (f : a ⟶ b) (g h : b ⟶ c) :
  f ○ g ≅ f ○ h <-> g ≅ h.
Proof.
  split; [apply bwarr_compose_cancel_l|now intros ->].
Qed.

Lemma bwarr_compose_cancel_r_iff {a b c} (f g : a ⟶ b) (h : b ⟶ c) :
  f ○ h ≅ g ○ h <-> f ≅ g.
Proof.
  split; [apply bwarr_compose_cancel_r|now intros ->].
Qed.

Lemma bwarr_tensor_cancel_e_top {a b} (f g : a ⟶ b) (h : e ⟶ e) :
  h ⊠ f ≅ h ⊠ g -> f ≅ g.
Proof.
  intros H.
  apply bwinv_unique with (f^-);
  [now rewrite bwarrinv_linv|].
  rewrite <-  bwarr_lunit, bwarr_compose_r, <- bwarr_tens_id in H.
  simpl in H.
  rewrite <- bwarr_tens_comp, bwarrinv_rinv in H.
  rewrite <- (bwarr_compose_cancel_r_iff _ _ (arrlunitor _)) in H.
  rewrite <- 2!bwarr_lunitor_nat in H.
  rewrite bwarr_compose_cancel_l_iff in H.
  easy.
Qed.

Lemma bwarr_tensor_cancel_e_bot {a b} (f g : a ⟶ b) (h : e ⟶ e) :
  f ⊠ h ≅ g ⊠ h -> f ≅ g.
Proof.
  intros H.
  apply bwinv_unique with (f^-);
  [now rewrite bwarrinv_linv|].
  rewrite <-  bwarr_lunit, bwarr_compose_r, <- bwarr_tens_id in H.
  simpl in H.
  rewrite <- bwarr_tens_comp, bwarrinv_rinv in H.
  rewrite <- (bwarr_compose_cancel_r_iff _ _ (arrrunitor _)) in H.
  rewrite <- 2!bwarr_runitor_nat in H.
  rewrite bwarr_compose_cancel_l_iff in H.
  easy.
Qed.

Lemma bwarr_tensor_cancel_e_top_iff {a b} (f g : a ⟶ b) (h : e ⟶ e) :
  h ⊠ f ≅ h ⊠ g <-> f ≅ g.
Proof.
  split; [apply bwarr_tensor_cancel_e_top|now intros ->].
Qed.

Lemma bwarr_tensor_cancel_e_bot_iff {a b} (f g : a ⟶ b) (h : e ⟶ e) :
  f ⊠ h ≅ g ⊠ h <-> f ≅ g.
Proof.
  split; [apply bwarr_tensor_cancel_e_bot|now intros ->].
Qed.


Lemma bwarr_assoc_nat_alt {a b c a' b' c' : bw} 
  (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
  arrassoc a b c ≅ f ⊠ (g ⊠ h) ○ arrassoc a' b' c' ○ ((f ⊠ g) ⊠ h)^-.
Proof.
  rewrite bwarr_compose_r'.
  simpl.
  rewrite 3!bwarrinv_invol.
  apply bwarr_assoc_nat.
Qed.

Lemma bwarr_assoc_nat_alt' {a b c a' b' c' : bw} 
  (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
  arrassoc a b c ≅ f ⊠ (g ⊠ h) ○ arrassoc a' b' c' ○ (f^- ⊠ g^-) ⊠ h^-.
Proof.
  rewrite bwarr_compose_r'.
  simpl.
  rewrite 3!bwarrinv_invol.
  apply bwarr_assoc_nat.
Qed.

Lemma bwarr_invassoc_nat_alt {a b c a' b' c' : bw} 
  (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
  arrinvassoc a b c ≅ (f ⊠ g) ⊠ h ○ arrinvassoc a' b' c' ○ (f ⊠ (g ⊠ h))^-.
Proof.
  apply by_bwarrinv.
  simpl.
  rewrite !bwarrinv_invol, <- bwarr_assoc.
  apply bwarr_assoc_nat_alt.
Qed.

Lemma bwarr_invassoc_nat_alt' {a b c a' b' c' : bw} 
  (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
  arrinvassoc a b c ≅ (f ⊠ g) ⊠ h ○ arrinvassoc a' b' c' ○ f^- ⊠ (g^- ⊠ h^-).
Proof.
  apply by_bwarrinv.
  simpl.
  rewrite !bwarrinv_invol, <- bwarr_assoc.
  apply bwarr_assoc_nat_alt.
Qed.

Lemma bwarr_triangle_alt (a b : bw) : 
  arrassoc a e b ≅ 
  arrid a ⊠ arrlunitor b ○ arrinvrunitor a ⊠ arrid b.
Proof.
  rewrite bwarr_compose_r'.
  apply bwarr_triangle.
Qed.

Lemma bwarr_invtriangle_alt (a b : bw) : 
  arrinvassoc a e b ≅ 
  arrrunitor a ⊠ arrid b ○ arrid a ⊠ arrinvlunitor b.
Proof.
  apply by_bwarrinv.
  simpl.
  apply bwarr_triangle_alt.
Qed.


Lemma bwarr_lunitor_tri (b c : bw) : 
  arrassoc e b c ○ arrlunitor b ⊠ arrid c ≅ arrlunitor (b ⨂ c).
Proof.
  pose proof (bwarr_pentagon e e b c) as p.
  rewrite (bwarr_triangle_alt e b) in p.
  rewrite (bwarr_triangle_alt e (b ⨂ c)) in p.
  rewrite (bwarr_assoc_nat_alt (arrrunitor e) (arrid b) (arrid c)) in p.
  rewrite (bwarr_assoc_nat_alt (arrid e) (arrlunitor b) (arrid c)) in p.
  rewrite !arrtens_pushout_top, <- !bwarr_assoc, bwarr_compose_cancel_r_iff in p.
  rewrite !bwarr_assoc, bwarrinv_linv, bwarr_runit in p.
  rewrite <- !bwarr_assoc, bwarr_compose_cancel_r_iff in p.
  rewrite bwarr_assoc, <- bwarr_tens_comp, bwarr_runitor_linv in p.
  rewrite bwarr_lunit, 2!bwarr_tens_id, bwarr_runit in p.
  rewrite <- bwarr_tens_comp, bwarr_lunit in p.
  rewrite bwarr_tensor_cancel_e_top_iff in p.
  symmetry.
  exact p.
Qed.


Lemma bwarr_runitor_tri (b c : bw) : 
  arrid b ⊠ arrrunitor c ≅ arrassoc b c e ○ arrrunitor (b ⨂ c).
Proof.
  pose proof (bwarr_invpentagonl b c e e) as p.
  rewrite (bwarr_invtriangle_alt c e) in p.
  rewrite (bwarr_invtriangle_alt (b ⨂ c) e) in p.
  rewrite (bwarr_invassoc_nat_alt (arrid b) (arrid c) (arrlunitor e)) in p. (* sure about runitor? *)
  rewrite (bwarr_invassoc_nat_alt (arrid b) (arrrunitor c) (arrid e)) in p. (* runitor?? *)
  simpl in p.
  rewrite !arrtens_pushout_bot, <- !bwarr_assoc, bwarr_compose_cancel_r_iff in p.
  rewrite !bwarr_assoc, <- 2!bwarr_tens_comp, bwarr_runitor_linv in p.
  rewrite !bwarr_lunit, !bwarr_tens_id, bwarr_runit, <- !bwarr_assoc in p.
  rewrite bwarr_compose_cancel_r_iff in p.
  rewrite bwarr_assoc, <- bwarr_tens_comp, bwarr_lunitor_linv in p.
  rewrite bwarr_lunit, bwarr_tens_id, bwarr_runit in p.
  rewrite <- bwarr_tens_comp, bwarr_lunit in p.
  rewrite bwarr_tensor_cancel_e_bot_iff in p.
  rewrite p, <- bwarr_assoc, bwarr_assoc_rinv, bwarr_lunit.
  easy.
Qed.


Section bwcast.

Import UIP_facts MCClasses.

Context {UIPX : UIP X}.

Lemma bw_cast_id {n m} (Hn : n = n) (Hm : m = m) f :
  cast_bwarr Hn Hm f = f.
Proof.
  unfold cast_bwarr.
  rewrite 2!eq_rect_eq.
  easy.
Qed.

Lemma cast_bwarr_indep {n n' m m'} 
  (Hn Hn' : n = n') (Hm Hm' : m = m') (f : n ⟶ m) : 
  cast_bwarr Hn Hm f = cast_bwarr Hn' Hm' f.
Proof.
  f_equal; apply uip.
Qed.

#[global] Add Parametric Morphism {n n' m m'}  : 
  (@cast_bwarr n n' m m') with signature
  true_rel ==> true_rel ==> bwarrequiv n m ==> bwarrequiv n' m'
  as cast_bwarr_mor.
Proof.
  intros; subst; rewrite 2!bw_cast_id.
  easy.
Qed.

Lemma bw_compose_cast_r {n n' m m' m'' p p'} 
  (Hn : n = n') (Hm : m = m') 
  (Hm' : m'' = m') (Hp : p = p') f g :
  cast_bwarr Hn Hm f ○ cast_bwarr Hm' Hp g
  ≅ cast_bwarr Hn eq_refl
    (f ○ cast_bwarr (eq_trans Hm' (eq_sym Hm)) Hp g).
Proof.
  subst.
  easy.
Qed.

Lemma bw_cast_cast {n n' n'' m m' m''} (f : n ⟶ m) Hn Hm 
  (Hn' : n' = n'') (Hm' : m' = m'') :
  cast_bwarr Hn' Hm' (cast_bwarr Hn Hm f) =
  cast_bwarr (eq_trans Hn Hn') (eq_trans Hm Hm') f.
Proof.
  subst; easy.
Qed.

Lemma bw_compose_cast_l {n n' m m' m'' p p'} 
  (Hn : n = n') (Hm : m = m') 
  (Hm' : m'' = m') (Hp : p = p') f g :
  cast_bwarr Hn Hm f ○ cast_bwarr Hm' Hp g
  ≅ cast_bwarr eq_refl Hp
    (cast_bwarr Hn (eq_trans Hm (eq_sym Hm')) f ○ g).
Proof.
  subst.
  easy.
Qed.

Lemma bw_cast_compose_split {n n' m p p'} (f : n ⟶ m) (g : m ⟶ p)
  (Hn : n = n') (Hp : p = p') :
  cast_bwarr Hn Hp (f ○ g) = 
  cast_bwarr Hn eq_refl f ○ cast_bwarr eq_refl Hp g.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma bw_cast_equiv_iff {n n' m m'} (f : n ⟶ m) (g : n' ⟶ m') Hn Hm :
  cast_bwarr Hn Hm f ≅ g <-> f ≅ cast_bwarr (eq_sym Hn) (eq_sym Hm) g.
Proof.
  subst.
  easy.
Qed.

Lemma bw_cast_arrid {n n'} H H' :
  cast_bwarr H H' (arrid n) = arrid n'.
Proof.
  now subst; rewrite bw_cast_id.
Qed.

Lemma bw_cast_tens_top {n n' m m' p q} (Hn : n = n') (Hm : m = m')
  f (g : p ⟶ q) :
  cast_bwarr Hn Hm f ⊠ g = 
  cast_bwarr 
    (f_equal (fun a => a ⨂ p) Hn)
    (f_equal (fun a => a ⨂ q) Hm)
    (f ⊠ g).
Proof.
  subst; easy.
Qed.

Lemma bw_cast_comp_l {n n' m p q} (Hn : n = n') (Hm : m = p)
  f (g : p ⟶ q) :
  cast_bwarr Hn Hm f ○ g = 
  cast_bwarr Hn eq_refl
    (f ○ cast_bwarr (eq_sym Hm) eq_refl g).
Proof.
  subst; easy.
Qed.

Lemma bw_cast_comp_r {n m p q q'} (Hp : p = m) (Hq : q = q')
  (f : n ⟶ m) g :
  f ○ cast_bwarr Hp Hq g = 
  cast_bwarr eq_refl Hq
    (cast_bwarr eq_refl (eq_sym Hp) f ○ g).
Proof.
  subst; easy.
Qed.

End bwcast.

End bwarr_theory.

Hint Resolve bwarrinv_linv bwarrinv_rinv : bwarrdb.
Hint Resolve bwarr_invassoc_natl bwarr_invlunitor_natl 
  bwarr_invrunitor_natl bwarr_invpentagonl bwarr_invtrianglel' : bwarrdb.
Hint Rewrite @bwarr_invassoc_natl 
  @bwarr_invlunitor_natl @bwarr_invrunitor_natl : bwarrdb.
(* Hint Rewrite <- @bwarr_invassoc_natl 
  @bwarr_invlunitor_natl @bwarr_invrunitor_natl : bwarrdb_rev. *)


Section bw_cat.

Import CategoryTypeclass.

#[export] Instance bwcat : Category bw | 10 := {|
  morphism := bwarr;
  c_equiv := bwarrequiv;
  compose := fun _ _ _ => arrcomp;
  c_identity := arrid;
|}.

Obligation Tactic := Tactics.program_simpl; simpl; eauto 3 with bwarrdb.

#[export, program] Instance bwcath : CategoryCoherence bwcat.
Next Obligation.
split; apply bwarrequiv_setoid.
Qed.
Solve All Obligations.

#[export, program] Instance bwassoc_iso (a b c : bw) 
  : Isomorphism (a ⨂ b ⨂ c) (a ⨂ (b ⨂ c)) := {
  forward := arrinvassoc a b c;
  reverse := arrassoc a b c;
}.

#[export, program] Instance bwlunitor_iso (a : bw) 
  : Isomorphism (e ⨂ a) a := {
  forward := arrlunitor a;
  reverse := arrinvlunitor a;
}.

#[export, program] Instance bwrunitor_iso (a : bw) 
  : Isomorphism (a ⨂ e) a := {
  forward := arrrunitor a;
  reverse := arrinvrunitor a;
}.

#[export] Instance bwmcat : MonoidalCategory bwcat | 10 := {
  obj_tensor := tens;
  mor_tensor := @arrtens X;
  associator := bwassoc_iso;
  left_unitor := bwlunitor_iso;
  right_unitor := bwrunitor_iso;
}.

#[export, program] Instance bwmcath : MonoidalCategoryCoherence bwmcat := {}.


(* #[export, program] Instance bwgroupoid : IsGroupoid bwcat := {
  groupoid_inv := @bwarrinv
}. *)

End bw_cat.


Section bw_thin.

(* Note: We only need EQ_RECT_EQ bw and EQ_RECT_EQ bwnorm, but either 
   of these is equivalent to EQ_RECT_EQ X and thus UIP X, so we just 
   ask for the latter for convenience. It *may* be possible to use 
   only EQ_REC_EQ bw for the case of X a set, but this seems to 
   require a full rewrite to take advantage of (bw lies in Type, 
   not Set, at present). Moreover, I am not aware of any types for 
   which we know EQ_REC_EQ but not EQ_RECT_EQ to motivate doing 
   this work. (I have not even found examples of types for which we 
   have UIP but not decidable equality.) *)

Import CategoryTypeclass MCClasses 
  UIP_facts MC_Cat_Thy_temp.
Import CatExample (FunctorCategory).

Context {UIPX : UIP X}.

(* This is intended to make typeclass resolution faster; 
   I do not know if it does. *)
#[local] Instance Eq_rect_eq_bw : EQ_RECT_EQ bw.
typeclasses eauto.
Qed.

#[local] Instance Eq_rect_eq_bwnorm : EQ_RECT_EQ bwnorm.
typeclasses eauto.
Qed.

Definition Eq_rect_bw :=
  fun x P a h => eq_sym (Eq_rect_eq_bw.(eq_rect_eq) x P a h).

Definition Eq_rect_bwnorm :=
  fun x P a h => eq_sym (Eq_rect_eq_bwnorm.(eq_rect_eq) x P a h).

#[global] Add Parametric Morphism {n n' m m'} Hn Hm : 
  (@cast_bwarr n n' m m' Hn Hm) with signature
  bwarrequiv n m ==> bwarrequiv n' m'
  as cast_bwarr_mor'.
Proof.
  intros; subst.
  easy.
Qed.


Local Notation "'𝒩'" := (DiscreteCategory bwnorm).
Local Notation "'𝒩h'" := (DiscreteCategoryCoherence bwnorm).

Local Notation "a '⟶' b" := (@bwarr X a b) 
  (at level 60) : type_scope. (* \longrightarrow *)

Obligation Tactic := idtac.

#[export, program] Instance norm_bw_bifunc : 
  Bifunctor 𝒩 bwcat bwcat := {
  obj_bimap := fun n a => n ⨂ a;
  morphism_bimap := fun n n' a b neq f => 
    cast_bwarr eq_refl _ (arrtens (arrid n) f)
}.
Next Obligation.
  simpl.
  intros; subst.
  reflexivity.
Defined.
Next Obligation.
  simpl.
  intros.
  apply bwarr_tens_id.
Qed.
Next Obligation.
  simpl.
  intros.
  subst.
  simpl.
  unfold eq_ind_r.
  simpl.
  apply arrtens_pushout_bot.
Qed.
Next Obligation.
  simpl.
  intros.
  subst.
  rewrite !bw_cast_id.
  eauto 2 with bwarrdb.
Qed.

Fixpoint bwbrac_eq_of_arr {a b} (f : a ⟶ b) {struct f} : forall n, ⟦a⟧ n = ⟦b⟧ n.
  induction f; intros n.
  all: try reflexivity.
  - etransitivity; [apply IHf1 | apply IHf2].
  - simpl.
    etransitivity; [| apply IHf2].
    apply f_equal.
    apply IHf1.
Defined.

Definition Nf_eq_of_arr {a b : bw} (f : bwarr a b) : Nf a = Nf b :=
  bwbrac_eq_of_arr f norm_e.

Arguments Nf_eq_of_arr {_ _} !f /.

Definition bwarr_tens_cancel_l {a b c : bw} 
  (f : a ⨂ b ⟶ a ⨂ c) : b ⟶ c :=
  bwarr_of_Nf_eq (Nf_cancel_tens_l (Nf_eq_of_arr f)).

Definition bwarr_tens_cancel_r {a b c : bw} 
  (f : b ⨂ a ⟶ c ⨂ a) : b ⟶ c :=
  bwarr_of_Nf_eq (Nf_cancel_tens_r (Nf_eq_of_arr f)).

Obligation Tactic := Tactics.program_simpl; simpl; eauto 3 with bwarrdb.

#[export, program] Instance Nf_functor : Functor bwcat 𝒩 := {
  obj_map := Nf;
  morphism_map := fun a b f => (bwbrac_of_bweq a b (bweq_of_arr f) norm_e)
}.

#[export, program] Instance bwbrac_functor : 
  Functor bwcat (@FunctorCategory _ _ 𝒩 𝒩h 𝒩 𝒩h) := {
  obj_map := fun a => {|obj_map := bwbrac a|};
  morphism_map := fun a b f => 
    {| component_map := fun c => _ |};
  (* morphism_map := fun a b f => (bwbrac_of_bweq a b (bweq_of_arr f) norm_e) *)
}.
Next Obligation.
  apply bwbrac_eq_of_arr, f.
Defined.
(* FIXME: Polymorphism issue. *)
Admit Obligations.
(* Solve All Obligations with constructor. *)

Definition bwbrac_mor_bimap_pf (n m : bwnorm) (a b : bw) 
  (H : 𝒩.(morphism) n m) (f : a ⟶ b) : ⟦a⟧ n = ⟦b⟧ m :> bw.
Proof.
  rewrite <- (bwbrac_eq_of_arr f m).
  f_equal.
  f_equal.
  apply  H.
Defined.


Definition bwbrac_mor_bimap (n m : bwnorm) (a b : bw) 
  (H : 𝒩.(morphism) n m) (f : a ⟶ b) : ⟦a⟧ n ⟶ ⟦b⟧ m :=
  cast_bwarr eq_refl (bwbrac_mor_bimap_pf n m a b H f) (arrid _).
Arguments bwbrac_mor_bimap _ _ _ _ _ / _.
Arguments eq_rect_r [_] [_] _ _ [_] / _.

Obligation Tactic := simpl; intros; eauto 3 with bwarrdb.


#[export, program] Instance bwbrac_bifunctor : 
  Bifunctor 𝒩 bwcat bwcat := {
  obj_bimap := fun n a => ⟦a⟧ n;
  morphism_bimap := bwbrac_mor_bimap;
}.
Next Obligation.
  rewrite bw_compose_cast_r.
  simpl.
  rewrite bwarr_lunit.
  rewrite bw_cast_equiv_iff, !bw_cast_cast.
  rewrite bw_cast_arrid.
  easy.
Qed.
Next Obligation.
  apply cast_bwarr_mor; easy.
Qed.

Obligation Tactic := simpl; eauto 3 with bwarrdb.



#[export, program] Instance bwbinat_trans : 
  NaturalBiIsomorphism norm_bw_bifunc bwbrac_bifunctor  := {
  component_biiso := fun n a => {| 
      forward := xi_comp_map n a; 
      reverse := (xi_comp_map n a) ^-;
    |};
  component_biiso_natural := fun n m a b hnm f => _
}.
Next Obligation.
  Local Ltac gen_casts := 
    repeat match goal with 
    |- context[cast_bwarr ?pf1 ?pf2 _] => 
      assert_fails (is_evar pf1); generalize pf1 pf2
    end.
  intros.
  subst.
  simpl.
  revert m;
  induction f; intros m.
  all : rewrite ?bw_cast_arrid, ?bwarr_tens_id, 
    ?bwarr_runit, ?bwarr_lunit; simpl.
  - rewrite arrtens_pushout_bot, bwarr_assoc, IHf2, 
      <- bwarr_assoc, IHf1, bwarr_assoc.
    apply bwarr_comp; [easy|].
    rewrite bw_compose_cast_r, bwarr_lunit.
    simpl.
    rewrite bw_cast_equiv_iff, bw_cast_cast, bw_cast_arrid.
    easy.
  - simpl.
    rewrite <- !bwarr_assoc.
    rewrite <- bwarr_assoc_nat, (bwarr_assoc (arrassoc _ _ _)).
    rewrite <- bwarr_tens_comp, IHf1, bwarr_runit.
    rewrite arrtens_pushin_top, !bwarr_assoc.
    repeat apply bwarr_compose_cancel_l_iff.
    rewrite bw_cast_tens_top.
    rewrite bw_cast_comp_l.
    simpl.
    specialize (IHf2 (⟦a⟧ m)).
    rewrite bwarr_compose_r in IHf2.
    rewrite IHf2.
    rewrite !bwarr_assoc.
    apply bwarr_compose_cancel_l_iff.
    symmetry.
    rewrite bw_cast_equiv_iff.
    rewrite !bw_cast_comp_r, !bw_cast_comp_l, bwarr_lunit.
    simpl.
    rewrite !bw_cast_cast.
    pose proof (bw_of_bwnorm_inj _ _ 
      (bwbrac_mor_bimap_pf m m a a' eq_refl f1)) as H.
    gen_casts.
    clear f1 f2 IHf1 IHf2.
    revert H.
    generalize (⟦a⟧ m).
    generalize (⟦a'⟧ m).
    intros; subst.
    now rewrite !bw_cast_id, bwarrinv_linv, bw_cast_arrid.
  - easy. 
  - rewrite !arrtens_pushin_top.
    rewrite <- !bwarr_assoc.
    repeat apply bwarr_compose_cancel_r_iff.
    rewrite bwarr_compose_r. simpl.
    rewrite !bwarr_assoc, bwarr_assoc_nat.
    rewrite <- 2!(bwarr_assoc (_ ⊠ _)), bwarr_tens_id.
    rewrite bwarrinv_rinv, bwarr_lunit.
    now rewrite bwarr_pentagon.
  - rewrite !arrtens_pushin_top.
    rewrite <- !bwarr_assoc.
    repeat apply bwarr_compose_cancel_r_iff.
    rewrite bwarr_compose_r. simpl.
    rewrite !bwarr_assoc, bwarr_invassoc_natl.
    rewrite <- !bwarr_assoc, bwarr_tens_id.
    repeat apply bwarr_compose_cancel_r_iff.
    rewrite bwarr_compose_r', bwarr_assoc, bwarr_compose_l.
    now rewrite bwarr_pentagon, bwarr_assoc.
  - now rewrite bwarr_triangle.
  - rewrite bwarr_triangle.
    rewrite <- bwarr_assoc.
    rewrite <- bwarr_tens_comp.
    rewrite (bwarrinv_linv (arrlunitor a)).
    now rewrite bwarr_lunit, bwarr_tens_id, bwarr_lunit.
  - rewrite bwarr_assoc, <- bwarr_runitor_nat, <- bwarr_assoc.
    now rewrite <- bwarr_runitor_tri.
  - rewrite bwarr_assoc, bwarr_compose_l, 
    <- bwarr_runitor_nat, <- bwarr_assoc.
    now rewrite <- bwarr_runitor_tri.
Qed.


#[export, program] Instance Nf_bwcat_functor : Functor bwcat bwcat := {
  obj_map := Nf;
  morphism_map := fun a b f => 
    cast_bwarr eq_refl (f_equal _ (bwbrac_eq_of_arr f norm_e)) (arrid _)
}.
Next Obligation.
  intros.
  rewrite bw_cast_equiv_iff, bw_cast_comp_l, bwarr_lunit, !bw_cast_cast.
  now rewrite bw_cast_arrid.
Qed.
Next Obligation.
  intros.
  apply cast_bwarr_mor; easy.
Qed.

#[export, program] Instance toNf_natiso : 
  NaturalIsomorphism (CatExample.IdentityFunctor bwcat) Nf_bwcat_functor := {
  component_iso := fun a =>
    CatExample.ComposeIsomorphisms
    {| forward := arrinvlunitor a : bwcat.(morphism) _ _; reverse := arrlunitor a |}
    (bwbinat_trans norm_e a)
}.
Next Obligation.
  intros.
  (* rewrite bw_cast_comp_r, bwarr_runit. *)
  simpl.
  rewrite <- bwarr_assoc. 
  rewrite bwarr_invlunitor_natl, 2!bwarr_assoc.
  rewrite bwarr_compose_cancel_l_iff.
  epose proof (bwbinat_trans.(component_biiso_natural) norm_e norm_e 
    A B eq_refl f) as en.
  simpl in en.
  rewrite en.
  erewrite cast_bwarr_indep.
  reflexivity.
Qed.

Theorem bw_thin {a b : bw} (f g : a ⟶ b) : f ≅ g.
Proof.
  pose proof ((toNf_natiso).(component_iso_natural) f) as Hf.
  rewrite compose_iso_r in Hf.
  pose proof ((toNf_natiso).(component_iso_natural) g) as Hg.
  rewrite compose_iso_r in Hg.
  simpl in *.
  rewrite Hf, Hg.
  rewrite bwarr_compose_cancel_r_iff,
    bwarr_compose_cancel_l_iff.
  erewrite cast_bwarr_indep; reflexivity.
Qed.

End bw_thin.

End bw_theory.