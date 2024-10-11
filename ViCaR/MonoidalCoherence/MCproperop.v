Require Import Setoid.
Require MCmonarrlist.

Section ProperOperation.

Set Universe Polymorphism.

Open Scope bw_scope.

Import MCDefinitions MCClasses MC_setoids
  MC_notations UIP_facts MCbw MCconsequences MCmonarrlist.
Import CategoryTypeclass.
Import List ListNotations.

Context {X : Type} {UIPX : UIP X}.
Context {cC : Category X} {cCh : CategoryCoherence cC} 
  {mC : MonoidalCategory cC} {mCh : MonoidalCategoryCoherence mC}.

Local Notation bw := (bw X).
Local Notation "a ⟶ b" := (@monarr X cC mC a b) (at level 60).
Local Notation monarrlist := (@monarrlist X cC mC).
Local Notation monarrlistelt := (@monarrlistelt X cC mC).

Section properop_definitions.

Definition monarrlistelt_proper (f : monarrlistelt -> monarrlistelt) : Prop :=
  forall g : monarrlistelt, 
  monarr_norm_equiv (realize_monarrlistelt (f g)) (realize_monarrlistelt g).

Definition unary_monarrlist_proper (f : monarrlist -> monarrlist) : Prop :=
  forall fs : monarrlist, monarr_norm_equiv 
  (stack_monarrlist (f fs)) (stack_monarrlist fs).

Definition binary_monarrlist_proper 
  (f : monarrlist -> monarrlist -> monarrlist * monarrlist) : Prop :=
  forall (fs gs : monarrlist) (Hfg : composable fs gs),
  exists (H : composable (fst (f fs gs)) (snd (f fs gs))),
  monarr_norm_equiv 
    (compose_composable fs gs Hfg) 
    (compose_composable _ _ H).

Definition bin_to_kary_monarrlist_proper 
  (f : monarrlist -> monarrlist -> monarrlist * list monarrlist) :=
  forall fs gs (Hfg : composable fs gs),
    exists H : totally_composable (fst (f fs gs) :: snd (f fs gs)),
    monarr_norm_equiv
      (compose_composable_monarr 
        (stack_monarrlist fs) 
        (stack_monarrlist gs) Hfg)
      (compose_totally_composable
        (fst (f fs gs) :: snd (f fs gs)) H).

Definition monarrlist_list_proper (f : list monarrlist -> list monarrlist) :=
  forall (fss : list monarrlist) (Hfss : totally_composable fss),
  exists (H : totally_composable (f fss)),
  monarr_norm_equiv 
    (compose_totally_composable fss Hfss)
    (compose_totally_composable (f fss) H).

Fixpoint pairwise_apply_helper 
  (f : monarrlist -> monarrlist -> monarrlist * monarrlist) 
  (fs : monarrlist) (fss : list monarrlist) := 
  match fss with
  | nil => fs::nil
  | fs' :: fss' =>   
      fst (f fs fs') :: (pairwise_apply_helper f (snd (f fs fs')) fss')
  end.

Definition pairwise_apply f (fss : list monarrlist) :=
  match fss with
  | nil => nil
  | fs :: fss' => pairwise_apply_helper f fs fss'
  end.

End properop_definitions.

Section elt_properop.

Lemma map_elt_proper_unary_proper (f : monarrlistelt -> monarrlistelt) 
  (Hf : monarrlistelt_proper f) :
  unary_monarrlist_proper (map f).
Proof.
  intros fs; induction fs; [easy|].
  apply monarr_norm_equiv_tens; easy.
Qed.

Lemma map_monarr_proper_unary_proper 
  (f : forall a b : bw, a ⟶ b -> a ⟶ b)
  (Hf : forall {a b : bw} (g : a ⟶ b), g ≊ f a b g) : 
  unary_monarrlist_proper 
  (map (monarrlistelt_map f)).
Proof.
  apply map_elt_proper_unary_proper.
  intros []; apply monarr_norm_equiv_of_monarrequiv; 
  simpl; easy.
Qed.

End elt_properop.

Section unary_properop.

Lemma unary_proper_id : unary_monarrlist_proper id.
Proof.
  unfold id. easy.
Qed.

Lemma unary_proper_compose {f g}
  (Hf : unary_monarrlist_proper f) 
  (Hg : unary_monarrlist_proper g) :
  unary_monarrlist_proper (Basics.compose f g).
Proof.
  intros fs.
  apply (monarr_norm_equiv_trans (g := stack_monarrlist (g fs)));
  apply Hf + apply Hg.
Qed.

Lemma unary_proper_iter {f} (Hf : unary_monarrlist_proper f) n :
  unary_monarrlist_proper (Nat.iter n f).
Proof.
  induction n; [apply unary_proper_id|].
  apply unary_proper_compose; assumption.
Qed.

Lemma unary_proper_iter' {f} (Hf : unary_monarrlist_proper f) 
  (fn : monarrlist -> nat) :
  unary_monarrlist_proper (fun fs => Nat.iter (fn fs) f fs).
Proof.
  intros fs; apply (unary_proper_iter Hf).
Qed.

Lemma unary_proper_composable {f} (H : unary_monarrlist_proper f)
  {fs gs} : 
  composable fs gs -> composable (f fs) (f gs).
Proof.
  unfold composable.
  intros Hc.
  rewrite (Nf_eq_out_of_norm_equiv (H fs)).
  rewrite (Nf_eq_in_of_norm_equiv (H gs)).
  apply Hc.
Qed.

Lemma unary_proper_totally_composable {f} (H : unary_monarrlist_proper f)  
  {fss : list monarrlist} (Hf : totally_composable fss) :
  totally_composable (map f fss).
Proof.
  induction fss; [easy|].
  destruct fss; [easy|].
  specialize (IHfss (proj2 Hf)).
  split.
  - apply (unary_proper_composable H), Hf.
  - apply IHfss.
Qed.

Lemma unary_proper_preserves {f} (H : unary_monarrlist_proper f) 
  {fss : list monarrlist} (Hf : totally_composable fss) : 
  monarr_norm_equiv 
    (compose_totally_composable fss Hf)
    (compose_totally_composable (map f fss) 
      (unary_proper_totally_composable H Hf)).
Proof.
  induction fss; [apply monarr_norm_equiv_refl|]; destruct fss.
  - apply monarr_norm_equiv_symm.
    apply H.
  - simpl map.
    rewrite 2!compose_totally_composable_cons.
    apply monarr_norm_equiv_comp_composable;
    [apply monarr_norm_equiv_symm, (H a)|].
    erewrite (compose_totally_composable_indep (f _ :: _)).
    apply IHfss.
Qed.

Lemma map_unary_proper_monarrlist_list_proper {f} 
  (Hf : unary_monarrlist_proper f) :
  monarrlist_list_proper (map f).
Proof.
  intros fss Hfss.
  exists (unary_proper_totally_composable Hf Hfss).
  apply unary_proper_preserves.
Qed.

End unary_properop.


Section binary_properop.

Lemma binary_proper_composable f (Hf : binary_monarrlist_proper f) 
  (fs gs : monarrlist) (H : composable fs gs) : 
  composable (fst (f fs gs)) (snd (f fs gs)).
Proof.
  destruct (Hf fs gs H); easy.
Qed.

Lemma Nf_in_eq_of_proper_binary_op f (Hf : binary_monarrlist_proper f) 
  (fs gs : monarrlist) (H : composable fs gs) : 
    Nf (monarrlist_source (fst (f fs gs))) = Nf (monarrlist_source fs).
Proof.
  destruct (Hf fs gs H) as (? & ? & _); easy.
Qed.

Lemma Nf_out_eq_of_proper_binary_op f (Hf : binary_monarrlist_proper f) 
  (fs gs : monarrlist) (H : composable fs gs) : 
    Nf (monarrlist_target (snd (f fs gs))) = Nf (monarrlist_target gs).
Proof.
  destruct (Hf fs gs H) as (? & ? & ? & _); easy.
Qed.

Lemma binary_proper_composable_prefix f (Hf : binary_monarrlist_proper f)
  fs fs' fss (H : totally_composable (fs :: fs' :: fss)) : 
  totally_composable (fst (f fs fs') :: snd (f fs fs') :: fss).
Proof.
  destruct (Hf fs fs' (proj1 H)) as (? & ? & Hout & ?).
  split; [easy|].
  apply (totally_composable_helper_swap Hout).
  apply H.
Qed.

Lemma binary_proper_of_composable_proper 
  (f : monarrlist -> monarrlist -> monarrlist * monarrlist)
  (Hc : forall fs gs, composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs))) 
  (Hprop : forall fs gs (Hfg : composable fs gs)
    (Hc' : forall fs gs, composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs))),
    monarr_norm_equiv 
      (compose_composable fs gs Hfg)
      (compose_composable (fst (f fs gs)) (snd (f fs gs)) 
        (Hc' fs gs Hfg))
      ): 
  binary_monarrlist_proper f.
Proof.
  intros fs gs H; exists (Hc fs gs H).
  apply Hprop.
Qed.

Lemma binary_proper_iff_composable_proper 
  (f : monarrlist -> monarrlist -> monarrlist * monarrlist) :
  binary_monarrlist_proper f <-> 
  (forall fs gs, composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs)))
  /\  forall fs gs (Hfg : composable fs gs)
  (Hc' : forall fs gs, composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs))),
  monarr_norm_equiv 
    (compose_composable fs gs Hfg)
    (compose_composable (fst (f fs gs)) (snd (f fs gs)) 
      (Hc' fs gs Hfg)).
Proof.
  split; [|intros []; apply binary_proper_of_composable_proper; easy].
  intros Hf.
  split.
  - intros; apply Hf; easy. 
  - intros.
    destruct (Hf fs gs Hfg) as (? & H).
    erewrite (composable_independence (_ _)).
    apply H.
Qed.

Lemma binary_proper_id : binary_monarrlist_proper pair.
Proof.
  intros fs gs H.
  exists H; easy.
Qed.

Lemma binary_proper_compose {f g} (Hf : binary_monarrlist_proper f)
  (Hg : binary_monarrlist_proper g) : 
  binary_monarrlist_proper (fun fs gs => uncurry g (f fs gs)).
Proof.
  intros fs gs H.
  destruct (Hf fs gs H) as [Hcf Heqf].
  destruct (Hg _ _ Hcf) as [Hcg Heqg].
  unfold uncurry.
  rewrite (surjective_pairing (f fs gs)).
  exists Hcg.
  eapply monarr_norm_equiv_trans; eassumption.
Qed.

Lemma binary_proper_iter {f} (Hf : binary_monarrlist_proper f) n :
  binary_monarrlist_proper (curry (Nat.iter n (uncurry f))).
Proof.
  induction n.
  - apply binary_proper_id.
  - apply binary_proper_compose; assumption.
Qed.

Section pairwise_proper.

Lemma pairwise_apply_helper_totally_composable fs fss f 
  (Hf : binary_monarrlist_proper f) : 
  totally_composable_helper fs fss ->
  totally_composable (pairwise_apply_helper f fs fss).
Proof.
  revert fs; induction fss; intros fs; [easy|].
  intros H; pose proof H as G; destruct G as [Hl Hr].
  simpl. 
  destruct fss as [|fs' fss].
  - split; [|easy].
    apply Hf; easy.
  - split.
    + simpl in Hr.
      destruct (Hf _ _ (proj1 H)) as [H' Heq].
      unfold composable in *.
      rewrite H'.
      symmetry.
      apply (Nf_in_eq_of_proper_binary_op f Hf _ fs').
      unfold composable.
      rewrite (Nf_out_eq_of_proper_binary_op f Hf _ _ (proj1 H)).
      apply H.
    + apply IHfss.
      eapply totally_composable_helper_swap; [|apply Hr].
      symmetry.
      apply (Nf_out_eq_of_proper_binary_op f Hf _ _ Hl).
Qed.

Lemma pairwise_apply_totally_composable fss f 
  (Hf : binary_monarrlist_proper f) : 
  totally_composable fss ->
  totally_composable (pairwise_apply f fss).
Proof.
  destruct fss; [easy|].
  apply pairwise_apply_helper_totally_composable, Hf.
Qed.

Lemma pairwise_apply_proper_binary_proper f 
  (Hf : binary_monarrlist_proper f) : 
  monarrlist_list_proper (pairwise_apply f).
Proof.
  intros fss Hfss.
  exists (pairwise_apply_totally_composable fss f Hf Hfss).
  destruct fss as [|fs fss]; [easy|].
  simpl.
  revert fs Hfss;
  induction fss; intros fs H; [apply monarr_norm_equiv_refl|].
  pose proof (binary_proper_composable_prefix f Hf fs a fss H) as Hc'.
  apply (monarr_norm_equiv_trans (g:=compose_totally_composable _ Hc')).
  - apply (compose_monarrlist_list_cancel_suffix [fs;a] [fst _;snd _] fss).
    simpl.
    destruct (Hf fs a (proj1 H)) as (? & H').
    erewrite (compose_composable_monarr_indep (stack_monarrlist (fst _))),
      compose_composable_monarr_indep.
    apply H'.
  - apply (compose_monarrlist_list_cancel_prefix (snd _ ::fss) 
      (pairwise_apply_helper f _ fss) [_]).
    apply monarr_norm_equiv_symm.
    erewrite compose_totally_composable_indep.
    apply monarr_norm_equiv_symm.
    erewrite compose_totally_composable_indep.
    apply (IHfss _ (proj2 Hc')).
Qed.

End pairwise_proper.
End binary_properop.

Section monarrlist_list_proper.

Lemma monarrlist_list_proper_composable {f} 
  (Hf : monarrlist_list_proper f) {fss} 
  (H : totally_composable fss) : 
  totally_composable (f fss).
Proof.
  apply Hf, H.
Qed.

Lemma proper_preserves {f} (Hf : monarrlist_list_proper f) 
  {fss} (H : totally_composable fss) :
  monarr_norm_equiv 
    (compose_totally_composable fss H)
    (compose_totally_composable (f fss) 
      (monarrlist_list_proper_composable Hf H)).
Proof.
  destruct (Hf fss H) as (? & H').
  erewrite (compose_totally_composable_indep (f fss)).
  apply H'.
Qed.

(* Making these special cases to make terms look more palatable
   when applying proper_preserves'. *)
Lemma monarrlist_list_proper_in_pf {f} (Hf : monarrlist_list_proper f) 
  {fss} (H : totally_composable fss) : 
  Nf (monarrlist_list_source fss) = 
  Nf (monarrlist_list_source (f fss)).
Proof.
  exact (Nf_eq_in_of_norm_equiv (proper_preserves Hf H)).
Qed.

Lemma monarrlist_list_proper_out_pf {f} (Hf : monarrlist_list_proper f) 
  {fss} (H : totally_composable fss) : 
  Nf (monarrlist_list_target (f fss)) = 
  Nf (monarrlist_list_target fss).
Proof.
  symmetry.
  exact (Nf_eq_out_of_norm_equiv (proper_preserves Hf H)).
Qed.

Lemma proper_preserves' {f} (Hf : monarrlist_list_proper f) 
  {fss} (H : totally_composable fss) :
  compose_totally_composable fss H ≊
  bwarr_of_Nf_eq (monarrlist_list_proper_in_pf Hf H) ◌
  compose_totally_composable (f fss) (monarrlist_list_proper_composable Hf H) ◌
  bwarr_of_Nf_eq (monarrlist_list_proper_out_pf Hf H).
Proof.
  destruct (monarr_norm_equiv_symm _ _ (proper_preserves Hf H)) 
    as (Hin & Hout & Heq).
  rewrite <- Heq.
  eauto with monarrdb.
Qed.

Lemma monarrlist_list_proper_totally_composable {f} 
  (Hf : monarrlist_list_proper f) {fss} :
  totally_composable fss -> totally_composable (f fss).
Proof.
  intros Hfss.
  destruct (Hf fss Hfss);
  easy.
Qed.

Lemma monarrlist_list_proper_iff {f} : 
  monarrlist_list_proper f <->
  {Hc : forall fss, totally_composable fss ->
    totally_composable (f fss) &
   forall fss (Hfss : totally_composable fss)
   (Hffss : totally_composable (f fss)),
    monarr_norm_equiv
      (compose_totally_composable fss Hfss)
      (compose_totally_composable (f fss) Hffss)}.
Proof.
  split.
  - intros Hf.
    exists (@monarrlist_list_proper_totally_composable f Hf).
    intros fss Hfss Hc.
    destruct (Hf fss Hfss).
    erewrite (compose_totally_composable_indep (f fss)).
    eassumption.
  - intros [Hc Hprop].
    intros fss Hfss.
    exists (Hc fss Hfss).
    apply Hprop.
Qed.

Lemma monarrlist_list_proper_preserves {f} (Hf : monarrlist_list_proper f) 
  {fss} (Hfss : totally_composable fss) : 
  monarr_norm_equiv 
    (compose_totally_composable fss Hfss)
    (compose_totally_composable (f fss) 
      (monarrlist_list_proper_totally_composable Hf Hfss)).
Proof.
  destruct (proj1 monarrlist_list_proper_iff Hf) as [Hc Hprop].
  apply Hprop.
Qed.


Lemma monarrlist_list_proper_id :
  monarrlist_list_proper id.
Proof.
  unfold id.
  intros fss Hfss; exists Hfss; easy.
Qed.

Lemma monarrlist_list_proper_compose' {f g} :
  monarrlist_list_proper f ->
  monarrlist_list_proper g ->
  monarrlist_list_proper (fun fss => g (f fss)).
Proof.
  intros Hf Hg fss Hfss.
  destruct (Hf fss Hfss) as [Hcf Heqf].
  destruct (Hg (f fss) Hcf) as [Hcg Heqg].
  exists Hcg.
  eapply monarr_norm_equiv_trans; eassumption.
Qed.

Lemma monarrlist_list_proper_compose {f g} :
  monarrlist_list_proper f ->
  monarrlist_list_proper g ->
  monarrlist_list_proper (Basics.compose g f).
Proof.
  unfold Basics.compose.
  apply monarrlist_list_proper_compose'.
Qed.

Lemma monarrlist_list_proper_iter {f} (Hf : monarrlist_list_proper f) n :
  monarrlist_list_proper (Nat.iter n f).
Proof.
  induction n.
  - apply monarrlist_list_proper_id.
  - apply monarrlist_list_proper_compose;
    [apply IHn | apply Hf].
Qed.

Lemma monarrlist_list_proper_iter' {f} (Hf : monarrlist_list_proper f)
  (fn : list monarrlist -> nat) :
  monarrlist_list_proper (fun fs => Nat.iter (fn fs) f fs).
Proof.
  intros fs Hfs.
  apply monarrlist_list_proper_iter, Hf.
Qed.

End monarrlist_list_proper.

Section pairify.

Import Lia.

Definition compble_lengths (fs gs : monarrlist) :=
  length (bw_to_varlist (monarrlist_target fs))
  = length (bw_to_varlist (monarrlist_source gs)).
  
Definition compble_lengths_dec (fs gs : monarrlist) :
  {compble_lengths fs gs} + {~ compble_lengths fs gs} :=
  PeanoNat.Nat.eq_dec 
    (length (bw_to_varlist (monarrlist_target fs)))
    (length (bw_to_varlist (monarrlist_source gs))).

Fixpoint pairify_helper (facc gacc fs gs : monarrlist) : 
  list (monarrlist * monarrlist) :=
  match fs, gs with 
  | nil, gs' => (facc, gacc ++ gs') :: nil
  | fs', nil => (facc ++ fs', gacc) :: nil
  | f::fs', g::gs' => 
      let facc' := facc ++ [f] in 
      let gacc' := gacc ++ [g] in 
      if (compble_lengths_dec facc' gacc') 
      then (facc', gacc') :: pairify_helper [] [] fs' gs'
      else pairify_helper facc' gacc' fs' gs'
  end.

Definition pairify (fs gs : monarrlist) := 
  pairify_helper [] [] fs gs.

Fixpoint depairify (fsgs : list (monarrlist * monarrlist)) 
  : monarrlist * monarrlist :=
  match fsgs with 
  | nil => (nil, nil)
  | fg :: fsgs' =>
      (* let '(fs, gs) := depairify fsgs' in  *)
      (fst fg ++ fst (depairify fsgs'), snd fg ++ snd (depairify fsgs'))
  end.

Definition pairify_apply 
  (f : monarrlist -> monarrlist -> monarrlist * monarrlist)
  (fs : monarrlist) (gs : monarrlist) : monarrlist * monarrlist :=
  depairify (map (uncurry f) (pairify fs gs)).

Lemma app_inj_len {A} {x1 x2 y1 y2 : list A} :
  length x1 = length y1 -> x1 ++ x2 = y1 ++ y2 ->
  x1 = y1 /\ x2 = y2.
Proof.
  intros Hlen Heq.
  destruct (app_eq_app _ _ _ _ Heq) as (lnil & H).
  destruct lnil; cycle 1.
  - destruct H as [H | H];
    destruct H as [Hl Hr];
    apply (f_equal (@length A)) in Hl;
    apply (f_equal (@length A)) in Hr;
    rewrite !app_length in *;
    simpl in *; lia.
  - rewrite !app_nil_r in *; simpl in *.
    destruct H as [H | H];
    destruct H; easy.
Qed.

Lemma composable_of_composable_lengths {fs gs fss gss : monarrlist}
  (Hc : composable (fs ++ fss) (gs ++ gss)) 
  (Hlen : compble_lengths fs gs) : 
  composable fs gs /\ composable fss gss.
Proof.
  unfold composable in *.
  rewrite Nf_monarrlist_target_app,
    Nf_monarrlist_source_app in Hc.
  rewrite bwnorm_eq_iff_varlist_eq in Hc.
  rewrite 2!bwnorm_to_varlist_app in Hc.
  unfold compble_lengths in Hlen.
  apply app_inj_len in Hc.
  - destruct Hc as [Hl Hr].
    apply bwnorm_to_varlist_inj in Hl, Hr.
    easy.
  - rewrite 2!bwnorm_to_varlist_Nf.
    easy.
Qed.

Lemma app_cons {A} (l1 l2 : list A) a : 
  l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof.
  rewrite <- app_assoc; easy.
Qed.

Lemma pairify_helper_composable (facc gacc fs gs : monarrlist) 
  (H : composable (facc ++ fs) (gacc ++ gs)) :
  Forall (uncurry composable) (pairify_helper facc gacc fs gs).
Proof.
  revert gs facc gacc H;
  induction fs as [| f fs' Hfs]; 
  intros gs facc gacc H;
  [|destruct gs as [|g gs']].
  - constructor; [|easy].
    rewrite app_nil_r in H.
    apply H.
  - constructor; [|easy].
    rewrite app_nil_r in H.
    apply H.
  - simpl. 
    destruct (compble_lengths_dec (facc ++ [f]) (gacc ++ [g])) as [Hc | Hnc]. 
    + rewrite (app_cons gacc), app_cons in H.
      destruct (composable_of_composable_lengths H Hc).
      constructor; [easy|].
      apply Hfs; easy.
    + apply Hfs.
      rewrite <- 2!app_assoc.
      apply H.
Qed.

Lemma pairify_composable (fs gs : monarrlist) : 
  composable fs gs ->
  Forall (uncurry composable) (pairify fs gs).
Proof.
  intros H. 
  apply pairify_helper_composable.
  apply H.
Qed.

Lemma depairify_composable fsgs 
  (H : Forall (uncurry composable) fsgs) : 
  composable (fst (depairify fsgs)) (snd (depairify fsgs)).
Proof.
  induction fsgs as [|[f g] fsgs IHfsgs]; [easy|].
  simpl.
  destruct (depairify fsgs) as (fs, gs).
  simpl.
  inversion H; subst.
  apply composable_app; [assumption|].
  apply IHfsgs; assumption.
Qed.

Lemma pairify_apply_composable f (Hc : forall fs gs, 
  composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs))) : 
  forall fs gs, composable fs gs -> 
  composable (fst (pairify_apply f fs gs)) (snd (pairify_apply f fs gs)).
Proof.
  intros fs gs Hfg.
  unfold pairify_apply.
  apply depairify_composable.
  apply (forall_composable_map Hc).
  apply pairify_composable; assumption.
Qed.

Lemma depairify_apply_compat f (Hf : binary_monarrlist_proper f)
  (Hc : forall fs gs, composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs))) 
  (Hprop : forall fs gs (Hfg : composable fs gs)
    (Hc' : forall fs gs, composable fs gs -> composable (fst (f fs gs)) (snd (f fs gs))),
    monarr_norm_equiv 
      (compose_composable fs gs Hfg)
      (compose_composable (fst (f fs gs)) (snd (f fs gs)) 
        (Hc' fs gs Hfg))) 
  fsgs (Hfsgs : Forall (uncurry composable) fsgs) :
  monarr_norm_equiv 
    (compose_composable 
      (fst (depairify fsgs)) (snd (depairify fsgs)) 
      (depairify_composable fsgs Hfsgs))
    
    (compose_composable 
      _ _
      (depairify_composable _
        (forall_composable_map Hc Hfsgs))).
Proof.
  induction fsgs as [|[fs gs] fsgs IHfsgs].
  - apply monarr_norm_equiv_of_monarrequiv.
    unfold compose_composable.
    simpl.
    rewrite !monarr_arrcomp.
    apply monarr_struct.
  - simpl.
    inversion Hfsgs; subst.
    simpl in * |-.
    eapply monarr_norm_equiv_trans.
    apply (@compose_composable_app _ _ _ fs gs ltac:(assumption)).
    eapply monarr_norm_equiv_trans.
    2: {
      apply monarr_norm_equiv_symm.
      apply (compose_composable_app (Hc fs gs ltac:(easy))).
    }
    apply monarr_norm_equiv_tens.
    + erewrite compose_composable_indep.
      apply monarr_norm_equiv_symm.
      erewrite compose_composable_indep.
      apply monarr_norm_equiv_symm.
      apply (IHfsgs ltac:(easy)).
    + apply Hprop.
Qed.

Lemma depairify_pairify_helper_id {fs fss gs gss} 
  (H : composable (fs ++ fss) (gs ++ gss)) :
  depairify (pairify_helper fs gs fss gss) = (fs ++ fss, gs ++ gss).
Proof.
  revert fs gs gss H.
  induction fss; intros fs gs gss H;
  [|destruct gss].
  - simpl.
    now rewrite !app_nil_r.
  - simpl.
    now rewrite !app_nil_r.
  - simpl.
    change (fs ++ a :: fss) with (fs ++ [a] ++ fss) in *.
    change (gs ++ m :: gss) with (gs ++ [m] ++ gss) in *.
    rewrite 2!app_assoc in *.
    destruct (compble_lengths_dec (fs ++ [a]) (gs ++ [m])) as [c | c].
    + simpl.
      pose proof (composable_of_composable_lengths H c) as [Hc Hc'].
      change fss with (nil ++ fss) in Hc'.
      change gss with (nil ++ gss) in Hc'.
      rewrite (IHfss _ _ _ Hc').
      easy.
    + rewrite (IHfss _ _ _ H).
      easy.
Qed.

Lemma depairify_pairify_id {fss gss} 
  (H : composable fss gss) : 
  depairify (pairify fss gss) = (fss, gss).
Proof.
  unfold pairify. 
  rewrite depairify_pairify_helper_id; easy.
Qed.

Lemma depairify_pairify_monarr_norm_equiv {fss gss} 
  (H : composable fss gss) : 
  monarr_norm_equiv
    (compose_composable fss gss H)
    (compose_composable 
      (fst (depairify (pairify fss gss)))
      (snd (depairify (pairify fss gss)))
      (depairify_composable _ (pairify_composable _ _ H))).
Proof.
  generalize 
  (depairify_composable (pairify fss gss) (pairify_composable fss gss H)).
  rewrite (depairify_pairify_id H).
  simpl.
  intros ?.
  erewrite compose_composable_indep.
  easy.
Qed.

Lemma pairify_apply_proper f (Hf : binary_monarrlist_proper f) :
  binary_monarrlist_proper (pairify_apply f).
Proof.
  pose proof Hf as Hf'.
  rewrite binary_proper_iff_composable_proper in Hf.
  apply binary_proper_of_composable_proper.
  - intros fs gs Hfg.
    apply pairify_apply_composable; [apply Hf | apply Hfg].
  - intros fs gs Hfg Hc.
    eapply monarr_norm_equiv_trans.
    apply depairify_pairify_monarr_norm_equiv.
    apply monarr_norm_equiv_symm.
    erewrite compose_composable_indep.
    apply monarr_norm_equiv_symm.
    erewrite compose_composable_indep.
    apply (depairify_apply_compat _ Hf').
    intros.
    apply Hf.
    Unshelve.
    + apply pairify_composable, Hfg.
    + apply Hf.
Qed.

End pairify.

End ProperOperation.
