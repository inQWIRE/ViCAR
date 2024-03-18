Require Import String.
Require Import Psatz.
Require Import CategoryTypeclass.
Require Import Arith.

Section BWord.

Inductive W :=
  | e0 : W
  | var : W
  | tens : W -> W -> W.

Inductive W0 :=
  | var0 : W0
  | tens0 : W0 -> W0 -> W0.

Fixpoint W_eqb (b b' : W) : bool :=
  match b, b' with
  | e0, e0 => true
  | var, var => true
  | tens b0 b1, tens b0' b1' => W_eqb b0 b0' && W_eqb b1 b1'
  | _, _ => false
  end.

Fixpoint W0_eqb (b b' : W0) : bool :=
  match b, b' with
  | var0, var0 => true
  | tens0 b0 b1, tens0 b0' b1' => W0_eqb b0 b0' && W0_eqb b1 b1'
  | _, _ => false
  end.



Require Import Bool.

Lemma W_eqbP : forall b b', b = b' <-> W_eqb b b' = true.
Proof.
  intros b b'.
  split.
  - intros H; subst b'; induction b; 
    simpl; try apply andb_true_intro; easy.
  - revert b'.
    induction b;
    intros b' H; destruct b'; try easy.
    simpl in H.
    rewrite andb_true_iff in H.
    erewrite IHb1, IHb2 by apply H.
    easy.
Qed.

Lemma W0_eqbP : forall b b', b = b' <-> W0_eqb b b' = true.
Proof.
  intros b b'.
  split.
  - intros H; subst b'; induction b; 
    simpl; try apply andb_true_intro; easy.
  - revert b'.
    induction b;
    intros b' H; destruct b'; try easy.
    simpl in H.
    rewrite andb_true_iff in H.
    erewrite IHb1, IHb2 by apply H.
    easy.
Qed.

Lemma bw_eq_dec : forall b b' : W, {b = b'} + {b <> b'}.
Proof.
  intros b b'.
  destruct (W_eqb b b') eqn:e.
  - rewrite <- W_eqbP in e.
    left; exact e.
  - right.
    intros Heq.
    rewrite (proj1 (W_eqbP b b') Heq) in e.
    discriminate e.
Qed.


Fixpoint eval_W {A} (a : A) (zero : A) 
  (bind : A -> A -> A) (b : W) : A :=
  match b with
  | e0 => zero
  | var => a
  | tens b0 b1 => 
    bind (eval_W a zero bind b0) (eval_W a zero bind b0)
  end.

Fixpoint print_word (b : W) : string :=
  match b with
  | e0 => "e"%string
  | var => "—"%string
  | tens b0 b1 => 
    ("(" ++ print_word b0 ++ ")⊗(" ++ print_word b1 ++ ")")%string
  end.



Fixpoint interp_W0 {C} {cC : Category C} {mC : MonoidalCategory cC}
  (c : C) (b : W0) := 
  match b with
  | var0 => c
  | tens0 b0 b1 => interp_W0 c b0 × interp_W0 c b1
  end.

End BWord.

Section Associativity.

Inductive aS :=
  | as_W0 : W0 -> aS
  | as_assoc : W0 -> W0 -> W0 -> aS
  | as_invassoc : W0 -> W0 -> W0 -> aS
  | as_tensor_l : aS -> W0 -> aS
  | as_tensor_r : aS -> W0 -> aS.

Fixpoint a_dom (s : aS) : W0 :=
  match s with
  | as_W0 b => b
  | as_assoc u v w => tens0 u (tens0 v w)
  | as_invassoc u v w => tens0 (tens0 u v) w
  | as_tensor_l a b =>
      tens0 b (a_dom a)
  | as_tensor_r a b =>
      tens0 (a_dom a) b
  end.

Fixpoint a_codom (s : aS) : W0 :=
  match s with
  | as_W0 b => b
  | as_assoc u v w => tens0 (tens0 u v) w
  | as_invassoc u v w => tens0 u (tens0 v w)
  | as_tensor_l a b =>
      tens0 b (a_codom a)
  | as_tensor_r a b =>
      tens0 (a_codom a) b
  end.

Fixpoint w_Sn (n : nat) : W0 :=
  match n with
  | 0 => var0
  | S n' => tens0 (w_Sn n') var0
  end.

Fixpoint len0 (b : W0) : nat :=
  match b with
  | var0 => 1
  | tens0 b0 b1 => len0 b0 + len0 b1
  end.

Lemma len0_pos : forall b, len0 b > 0.
Proof. induction b; simpl; lia. Qed.

Lemma len_w_Sn : forall n, len0 (w_Sn n) = S n.
Proof.
  induction n; simpl; lia.
Qed.

Fixpoint rho0 (b : W0) : nat :=
  match b with
  | var0 => 0
  | tens0 v w => rho0 v + rho0 w + len0 w - 1
  end.

Lemma rho0_w_Sn : forall n, 
  rho0 (w_Sn n) = 0.
Proof.
  induction n; simpl; lia.
Qed.

Lemma rho_eq0_iff : forall b : W0,
  rho0 b = 0 <-> b = w_Sn (len0 b - 1).
Proof.
  intros b.
  split.
  - induction b; [easy|].
    destruct b2.
    + simpl in *.
      intros.
      assert (rho0 b1 = 0) by lia.
      rewrite IHb1 at 1 by lia.
      assert (H':len0 b1 > 0) by (apply len0_pos); revert H'.
      generalize (len0 b1) as n.
      intros n. 
      induction n; [easy|].
      intros _.
      simpl; rewrite 2!Nat.sub_0_r, Nat.add_1_r.
      easy.
    + intros H.
      contradict H.
      simpl.
      pose (len0_pos b2_1); pose (len0_pos b2_2).
      lia.
  - intros H; rewrite H.
    apply rho0_w_Sn.
Qed.

Inductive a_dir : aS -> Prop :=
  | a_dir_assoc u v w : a_dir (as_assoc u v w)
  | a_dir_tens_l s b : a_dir s -> a_dir (as_tensor_l s b)
  | a_dir_tens_r s b : a_dir s -> a_dir (as_tensor_r s b).

Inductive a_antidir : aS -> Prop :=
  | a_antidir_invassoc u v w : a_antidir (as_invassoc u v w)
  | a_antidir_tens_l s b : a_antidir s -> a_antidir (as_tensor_l s b)
  | a_antidir_tens_r s b : a_antidir s -> a_antidir (as_tensor_r s b).

Lemma ne_tens0_l : forall b b' : W0,
  b <> tens0 b b'.
Proof.
  intros b.
  induction b; [easy|].
  intros b' H.
  inversion H.
  eapply IHb1; eassumption.
Qed.

Lemma ne_tens0_r : forall b b' : W0,
  b <> tens0 b' b.
Proof.
  intros b.
  induction b; [easy|].
  intros b' H.
  inversion H.
  eapply IHb2; eassumption.
Qed.

Lemma ne_tens0_assoc : forall b b' b'' : W0, 
  tens0 (tens0 b b') b'' <> tens0 b (tens0 b' b'').
Proof.
  intros b.
  induction b; [easy|].
  intros b' b'' H; inversion H.
  symmetry in H1.
  eapply ne_tens0_l, H1.
Qed.

Ltac W0cong :=
  simpl in *; subst; intros; try easy; try lia; first [
    exfalso; eapply ne_tens0_r; solve [eauto] |
    exfalso; eapply ne_tens0_l; solve [eauto] |
    exfalso; eapply ne_tens0_assoc; solve [eauto] |
    match goal with
    | H : ?f _ _ = ?g _ _ |- _ => inversion H; clear H; W0cong
    end |
    match goal with
    | H : forall _, _ |- _ => apply H; clear H; W0cong
    end |
    (progress f_equal); solve [eauto] |
    (progress hnf); W0cong
  ].

Ltac W0cong_debug :=
  simpl in *; subst; intros; try easy; try lia; first [
    exfalso; eapply ne_tens0_r; idtac "ner"; solve [eauto] |
    exfalso; eapply ne_tens0_l; idtac "nel"; solve [eauto] |
    exfalso; eapply ne_tens0_assoc; idtac "nea"; solve [eauto] |
    match goal with
    | H : ?f _ _ = ?g _ _ |- _ => inversion H; 
    idtac "invers" H; clear H; W0cong_debug
    end |
    match goal with
    | H : forall _, _ |- _ => apply H; idtac "apply" H; clear H; W0cong_debug
    end |
    (progress f_equal); idtac "feq"; solve [eauto] |
    (progress hnf); idtac "hnf"; W0cong_debug
  ].

Hint Resolve ne_tens0_r ne_tens0_l ne_tens0_assoc : tens0_db.

Lemma a_dir_not_id : forall s : aS, a_dir s -> a_dom s <> a_codom s.
Proof.
  intros s Hs.
  induction Hs; W0cong.
Qed.

Lemma a_dir_len_dom_codom : forall s : aS, 
  a_dir s ->
  len0 (a_dom s) = len0 (a_codom s).
Proof.
  intros s Hs; induction Hs; simpl; auto with arith.
Qed.

Lemma a_no_parallel_dir : forall s s' : aS,
  a_dir s -> a_dir s' ->
  a_dom s = a_dom s' -> a_codom s = a_codom s' -> s = s'.
Proof.
  intros s s' Hs Hs'; revert s' Hs'.
  induction Hs.
  - simpl; intros s' Hs'; inversion Hs'; W0cong.
  - simpl. intros s' Hs'.
    inversion Hs'; try W0cong.
    pose proof a_dir_not_id.
    simpl.
    intros.
    subst.
    inversion H2; inversion H3.
    exfalso; eapply H1; eauto; subst; easy.
  - simpl. intros s' Hs'.
    inversion Hs'; try W0cong.
    pose proof a_dir_not_id.
    simpl.
    intros.
    subst.
    inversion H2; inversion H3.
    exfalso; eapply H1; eauto; subst; easy.
Qed.

Lemma rho0_dir_decreasing : forall s, 
  a_dir s ->
  rho0 (a_codom s) < rho0 (a_dom s).
Proof.
  intros s Hs.
  induction Hs.
  - simpl.
    pose (len0_pos u); 
    pose (len0_pos v);
    pose (len0_pos w).
    lia.
  - simpl. 
    pose (len0_pos (a_dom s)).
    rewrite <- a_dir_len_dom_codom by easy.
    lia.
  - simpl.
    pose (len0_pos b).
    lia.
Qed.

Fixpoint a_inv (s : aS) : aS :=
  match s with
  | as_W0 b => as_W0 b
  | as_assoc u v w => as_invassoc u v w
  | as_invassoc u v w => as_assoc u v w
  | as_tensor_l a b => as_tensor_l (a_inv a) b
  | as_tensor_r a b => as_tensor_r (a_inv a) b
  end.

Lemma a_inv_involutive : forall s, 
  a_inv (a_inv s) = s.
Proof. induction s; simpl; rewrite ?IHs; easy. Qed.

Lemma a_inv_dom : forall s,
  a_dom (a_inv s) = a_codom s.
Proof. induction s; simpl; rewrite ?IHs; easy. Qed.

Lemma a_inv_codom : forall s,
  a_codom (a_inv s) = a_dom s.
Proof. induction s; simpl; rewrite ?IHs; easy. Qed.

Lemma a_inv_dir : forall s, 
  a_dir s -> a_antidir (a_inv s).
Proof.
  intros s Hs.
  induction Hs; constructor; assumption.
Qed.

Lemma a_inv_antidir : forall s, 
  a_antidir s -> a_dir (a_inv s).
Proof.
  intros s Hs.
  induction Hs; constructor; assumption.
Qed.


Inductive a_lst :=
  | a_lst_init : aS -> a_lst
  | a_lst_cons : aS -> a_lst -> a_lst.

Definition a_lst_dom (ls : a_lst) : W0 :=
  match ls with
  | a_lst_init s
  | a_lst_cons s _ => a_dom s
  end.

Fixpoint a_lst_codom (ls : a_lst) : W0 :=
  match ls with
  | a_lst_init s => a_codom s
  | a_lst_cons _ l => a_lst_codom l
  end.

Fixpoint a_path (ls : a_lst) : bool :=
  match ls with
  | a_lst_init s => true
  | a_lst_cons s l => W0_eqb (a_codom s) (a_lst_dom l) && a_path l
  end.

Fixpoint a_path_prop (ls : a_lst) : Prop :=
  match ls with
  | a_lst_init s => True
  | a_lst_cons s l => (a_codom s) = (a_lst_dom l) /\ a_path_prop l
  end.

Fixpoint assoc_free (b : W0) : bool :=
  match b with 
  | var0 => true
  | tens0 b' b'' => match b'' with
    | var0 => assoc_free b'
    | tens0 _ _ => false
    end
  end.

Lemma assoc_free_iff_rho0_eq_0 : forall b, 
  assoc_free b = true <-> rho0 b = 0.
Proof.
  intros b.
  rewrite rho_eq0_iff.
  split.
  - intros H.
    induction b; [easy|].
    simpl in H.
    destruct b2; [|easy].
    simpl.
    rewrite Nat.add_sub.
    rewrite IHb1 at 1 by easy.
    pose proof (len0_pos b1) as e ; revert e.
    generalize (len0 b1) as n; induction n; [easy|].
    intros _.
    simpl; rewrite Nat.sub_0_r; easy.
  - generalize (len0 b).
    intros n Hb; subst b.
    destruct n; [easy|].
    simpl; rewrite Nat.sub_0_r.
    induction n; easy.
Qed.

Fixpoint a_can_next_step (b : W0) : aS :=
  match b with
  | var0 => as_W0 var0
  | tens0 c d => match d with
    | var0 => as_tensor_r (a_can_next_step c) var0
    | tens0 d' d'' => as_assoc c d' d''
    end 
  end.

Lemma a_can_next_step_dom : forall b, 
  a_dom (a_can_next_step b) = b.
Proof.
  intros b; induction b; [easy|]; simpl.
  induction b2; [|easy].
  simpl; rewrite IHb1; easy.
Qed.

Lemma a_can_next_step_dir : forall b,
  rho0 b <> 0 ->
  a_dir (a_can_next_step b).
Proof.
  intros b H.
  induction b as [|b0 b1]; [easy|].
  intros. simpl.
  destruct b2; constructor.
  apply b1.
  simpl in H.
  lia.
Qed.

Lemma rho0_a_can_next_step_codom : forall b,
  assoc_free b = false ->
  rho0 (a_codom (a_can_next_step b)) < rho0 b.
Proof.
  intros.
  rewrite <- (a_can_next_step_dom b) at 2.
  apply rho0_dir_decreasing, a_can_next_step_dir.
  rewrite <- assoc_free_iff_rho0_eq_0.
  rewrite H; easy.
Qed.

Require Coq.Program.Wf.
Require Import FunInd Recdef.

Function a_can_path (b : W0) {measure rho0 b} : a_lst :=
  match assoc_free b as H with
  | true => a_lst_init (as_W0 b)
  | false =>
    let cns := a_can_next_step b in 
    a_lst_cons (cns) (a_can_path (a_codom cns))
  end.
apply rho0_a_can_next_step_codom.
Qed.


(* Function a_can_path (b : W0) {measure (rho0 b)} : a_lst :=
  match assoc_free b as H with
  | true => a_lst_init (as_W0 b)
  | false =>
    let cns := a_can_next_step b in 
    a_lst_cons (cns) (a_can_path (a_codom cns))
  end.
Next Obligation.
  apply rho0_a_can_next_step_codom; easy.
Qed. *)

Lemma a_can_path_dom : forall b, a_lst_dom (a_can_path b) = b.
Proof.
  intros b.
  pattern (a_can_path b).
  revert b.
  apply a_can_path_ind; [easy|].
  intros b Hb.
  simpl.
  intros _.
  apply a_can_next_step_dom.
Qed.

Lemma a_can_path_codom_rho0 : forall b, 
  rho0 (a_lst_codom (a_can_path b)) = 0.
Proof.
  intros b;
  pattern (a_can_path b);
  revert b.
  apply a_can_path_ind; [|easy].
  intros b Hb.
  rewrite assoc_free_iff_rho0_eq_0 in Hb.
  easy.
Qed.

Lemma a_can_next_step_codom_len : forall b,
  len0 (a_codom (a_can_next_step b)) = len0 b.
Proof.
  induction b; [easy|].
  simpl.
  destruct b2; simpl; lia.
Qed.

Lemma a_can_path_codom_len : forall b,
  len0 (a_lst_codom (a_can_path b)) = len0 b.
Proof.
  intros b; 
  pattern (a_can_path b);
  revert b.
  apply a_can_path_ind; [easy|].
  simpl; intros.
  rewrite <- (a_can_next_step_codom_len b).
  easy.
Qed.

Lemma a_can_path_codom : forall b, 
  a_lst_codom (a_can_path b) = w_Sn (len0 b - 1).
Proof.
  intros b.
  pose proof (a_can_path_codom_rho0 b) as H.
  rewrite rho_eq0_iff in H.
  rewrite H, a_can_path_codom_len.
  easy.
Qed.

Lemma a_can_path_path : forall b, a_path_prop (a_can_path b).
Proof.
  apply a_can_path_ind.
  - easy.
  - intros b Hb.
    simpl.
    intros Hpath; split; [|easy].
    rewrite a_can_path_dom.
    easy.
Qed.



Fixpoint interp_aS {C} {cC : Category C} {mC : MonoidalCategory cC}
  (c : C) (s : aS) 
  : cC.(morphism) (interp_W0 c (a_dom s)) (interp_W0 c (a_codom s)) :=
  match s with
  | as_W0 b => id_ _
  | as_assoc u v w => (associator _ _ _)^-1
  | as_invassoc u v w => (associator _ _ _)
  | as_tensor_l a b => (id_ _) ⊗ (interp_aS c a)
  | as_tensor_r a b => (interp_aS c a) ⊗ (id_ _)
  end%Mor.

Fixpoint a_dir_lst (l : a_lst) : Prop :=
  match l with
  | a_lst_init s => a_dir s
  | a_lst_cons s ls => a_dir s /\ a_dir_lst ls
  end.

Definition a_dir_path (l : a_lst) := a_path_prop l /\ a_dir_lst l.

Fixpoint interp_a_path_prop {C} {cC : Category C}
  {mC : MonoidalCategory cC} (c : C) (l : a_lst) 
  (H : a_path_prop l) {struct l} : 
  (interp_W0 c (a_lst_dom l) ~> interp_W0 c (a_lst_codom l))%Cat.
destruct l.
- apply interp_aS.
- simpl.
  eapply compose.
  + apply interp_aS.
  + destruct H as [Ha Hl].
    rewrite Ha.
    apply interp_a_path_prop, Hl.
Defined.

Definition unique_directed_path_image_prop : Prop.
  refine ( forall C (cC : Category C)
  (mC : MonoidalCategory cC) (c : C) (v : W0) (l l' : a_lst)
    (Hl : a_dir_path l) (Hl' : a_dir_path l')
    (Hdoml : a_lst_dom l = v) (Hdoml' : a_lst_dom l' = v)
    (Hcodoml : a_lst_codom l = w_Sn (len0 v - 1))
    (Hcodoml' : a_lst_codom l' = w_Sn (len0 v - 1)),
    (interp_a_path_prop c l (proj1 Hl) ≃ _)%Cat).
  rewrite Hdoml, <- Hdoml', Hcodoml, <- Hcodoml'.
  exact (interp_a_path_prop c l' (proj1 Hl')).
Defined.

Lemma generalized_induction {T} {P : T -> Prop} 
  (f : T -> nat) : 
  (forall t, f t = 0 -> P t) ->
  (forall t, (forall s, f s < f t -> P s) -> P t) ->
  forall t, P t.
Proof.
  intros Hbase Hrec.
  enough (Hen: forall n, forall t, f t <= n -> P t)
  by (intros t; apply (Hen (f t) t (le_n _))).
  intros n.
  induction n.
  - intros t Hft.
    apply Hbase; lia.
  - intros t Hft.
    destruct (Nat.lt_trichotomy (f t) (S n)) 
      as [Hlt | [Heq | Hfalse]]; [| | lia].
    + apply IHn; lia.
    + apply Hrec. 
      intros s Hs.
      apply IHn; lia.
Qed.

Lemma generalized_induction_base {T} {P : T -> Prop} 
  (f : T -> nat) (base : nat) : 
  (forall t, f t <= base -> P t) ->
  (forall t, (forall s, f s < f t -> P s) -> P t) ->
  forall t, P t.
Proof.
  intros Hbase Hrec.
  apply (generalized_induction (fun t => f t - base)).
  - intros t Ht; apply Hbase; lia.
  - intros t Hless.
    apply Hrec.
    intros s Hs.
    destruct (Nat.lt_trichotomy (f s) base) as [Hlt | [Heq | Hgt]];
    [apply Hbase; lia | apply Hbase; lia |].
    apply Hless; lia.
Qed.

Require Import Coq.Init.Wf.

Lemma generalized_double_induction {T} {P : T -> Prop} 
  (f g : T -> nat) : 
  (forall t, f t = 0 -> P t) ->
  (forall t, g t = 0 -> P t) ->
  (forall t, 
    (forall s, f s = f t -> g s < g t -> P s) ->
    (forall s, f s < f t -> P s) -> P t) ->
  forall t, P t.
Proof.

  intros Hbasef Hbaseg Hrec.
  enough (Hpair:forall s t : T, P s /\ P t) by 
  (intros t; apply (Hpair t t)).
  set (lexico_rel (* : nat * nat -> nat * nat -> Prop *) :=
    fun ab cd :nat*nat=> let (a,b) := ab in let (c,d):=cd in
      a < c \/ (a = c /\ b < d)).
  intros s t; pattern t; revert t; pattern s; revert s.
  apply well_founded_induction_type_2 with lexico_rel.
  - intros (a, b).
    induction a; induction b.
    + constructor.
      intros (c, d) Hy; unfold lexico_rel in *.
      lia.
    + constructor.
      intros (c, d).
      intros [Hfalse | [Hc Hd]]; [unfold lexico_rel in *; lia|]. subst c.
      destruct (Nat.lt_trichotomy d b) as [Hlt | [Heq | Hf]];
      [ | | lia].
      * apply Acc_inv with (0, b). 
        apply IHb.
        hnf; lia.
      * subst d; easy. 
    + constructor.
      intros (a', b').
      unfold lexico_rel.
      intros [Ha' | Hf]; [|lia].
      destruct (Nat.lt_trichotomy a' a) as [Hlt | [Heq | Hf]];
      [ | | lia].
      * apply Acc_inv with (a, 0); easy || lia.
      * subst a'.
        induction b'; [easy|].
        constructor.
        intros (a'', b'').
        intros [Has | [Haeq Hb]];
        [ apply Acc_inv with (a, b'); easy || lia | ].
        subst a''.
        destruct (Nat.lt_trichotomy b'' b') as [Hlt | [Heq | Hf]];
        [ | | lia].
        --apply Acc_inv with (a, b'); easy || lia.
        --subst b''; easy.
    + specialize (IHb ltac:(apply Acc_inv with (a, S b); hnf; easy || lia)).
      constructor.
      intros (c, d).
      intros [Halt | [Haeq Hblt]].
      * apply Acc_inv with (S a, b); hnf; easy || lia.
      * subst c. 
        induction d.
        --destruct b; [easy|].
          apply Acc_inv with (S a, S b); hnf; easy || lia.
        --constructor.
          intros (c', d').
          intros [Hclt | [Hceq Hdlt]].
          ++apply Acc_inv with (S a, b); hnf; easy || lia.
          ++destruct (Nat.lt_trichotomy d' d) as [Hlt | [Heq | Hf]];
            [ | | lia].
            **apply Acc_inv with (S a, d); hnf; apply IHd || lia; lia.
            **subst; apply IHd; lia.
  - intros x x' Hind.
    Abort.


Lemma unique_directed_path_image : unique_directed_path_image_prop.
Proof.
  unfold unique_directed_path_image_prop.
  intros C cC mC c v.
  pattern v.
  match goal with |- ?f ?v => set (gP := f) end.
  assert (HwSn: forall w, (exists n, w = w_Sn n) -> gP w). 1:{
    subst gP.
    intros w [n Hn].
    subst w.
    intros.
    unfold a_dir_path in Hl.
    destruct l.
    + simpl in *.
      pose proof (rho0_dir_decreasing a (proj2 Hl)) as H.
      replace (a_dom a) in H.
      rewrite rho0_w_Sn in H.
      easy.
    + simpl in *.
      pose proof (rho0_dir_decreasing a (proj1 (proj2 Hl))) as H.
      replace (a_dom a) in H.
      rewrite rho0_w_Sn in H; easy.
  }
  apply (generalized_induction rho0).
  - intros t.
    rewrite rho_eq0_iff.
    intros Ht.
    apply HwSn.
    exists (len0 t - 1); easy.
  - intros t;
    pattern t; revert t.
    apply (generalized_induction_base len0 1).
    + intros t Ht.
      destruct t; try (simpl in Ht; lia).
      * intros _.
        apply HwSn.
        exists 0; easy.
      * simpl in Ht.
        pose (len0_pos t1); pose (len0_pos t2); lia.
    + 
  
































  Search "a_can_path".
  apply (generalized_induction rho0).
  - intros b Hb.
    
    destruct (assoc_free b).
  
  Search "a_can_path".
  






Inductive arrow_S' :=
  | arr_W (b : W)
  | arr_assoc (u v w : W)
  | arr_invassoc (u v w : W)
  | arr_lunit (b : W)
  | arr_invlunit (b : W)
  | arr_runit (b : W)
  | arr_invrunit (b : W)
  | arr_tensor_l : arrow_S' -> W -> arrow_S'
  | arr_tensor_r : arrow_S' -> W -> arrow_S'.

Class Quiver := {
  q_edges : Type;
  q_verts : Type;
  dom : q_edges -> q_verts;
  codom : q_edges -> q_verts;
}.

Fixpoint arrow_dom (a : arrow_S') : W :=
  match a with
  | arr_W b => b
  | arr_assoc u v w => tens (tens u v) w
  | arr_invassoc u v w => tens u (tens v w)
  | arr_lunit b => tens e0 b
  | arr_invlunit b => b
  | arr_runit b => tens b e0
  | arr_invrunit b => b
  | arr_tensor_l a b =>
      tens b (arrow_dom a)
  | arr_tensor_r a b =>
      tens (arrow_dom a) b
  end.

Fixpoint arrow_codom (a : arrow_S') : W :=
  match a with
  | arr_W b => b
  | arr_assoc u v w => tens u (tens v w)
  | arr_invassoc u v w => tens (tens u v) w
  | arr_lunit b => b
  | arr_invlunit b => tens e0 b
  | arr_runit b => b
  | arr_invrunit b => tens b e0
  | arr_tensor_l s b =>
      tens b (arrow_codom s)
  | arr_tensor_r s b =>
      tens (arrow_codom s) b
  end.

#[export] Instance quiver_S' : Quiver := {
  q_edges := arrow_S';
  q_verts := W;
  dom := arrow_dom;
  codom := arrow_codom;
}.

Fixpoint len (b : W) : nat :=
  match b with
  | e0 => 0
  | var => 1
  | tens b0 b1 => len b0 + len b1
  end.

Lemma len_dom_codom : forall s,
  len (arrow_dom s) = len (arrow_codom s).
Proof.
  induction s; simpl; lia.
Qed.


Fixpoint word_to_mc {C} {cC : Category C} (mC : MonoidalCategory cC) 
  (b : W) : C -> C :=
  fun c => 
  match b with
  | e0 => mC.(mon_I)
  | var => c
  | tens b0 b1 => (word_to_mc mC b0 c) × (word_to_mc mC b1 c)
  end.


(* Local Open Scope Mor_scope. *)
Fixpoint arr_to_mc {C} {cC : Category C} (mC : MonoidalCategory cC) 
  (s : arrow_S') (c : C) : 
    ((word_to_mc mC (arrow_dom s) c) ~> 
      (word_to_mc mC (arrow_codom s) c))%Cat :=
  match s with 
  | arr_W b => id_ _
  | arr_assoc u v w => 
      associator (word_to_mc mC u c) (word_to_mc mC v c) (word_to_mc mC w c)
  | arr_invassoc u v w =>
      (associator (word_to_mc mC u c) (word_to_mc mC v c) (word_to_mc mC w c))^-1
  | arr_lunit b => 
      λ_ _
  | arr_invlunit b => (λ_ _)^-1
  | arr_runit b => (ρ_ _)
  | arr_invrunit b => (ρ_ _)^-1
  | arr_tensor_l s' b =>
      id_ (word_to_mc mC b c) ⊗ (arr_to_mc mC s' c)
  | arr_tensor_r s' b =>
      (arr_to_mc mC s' c) ⊗ id_ (word_to_mc mC b c)
  end%Mor.

Inductive arr_lst :=
  | lst_init : arrow_S' -> arr_lst
  | lst_cons : arrow_S' -> arr_lst -> arr_lst.

Definition arr_lst_dom (ls : arr_lst) : W :=
  match ls with
  | lst_init s
  | lst_cons s _ => dom s
  end.

Fixpoint arr_lst_codom (ls : arr_lst) : W :=
  match ls with
  | lst_init s => codom s
  | lst_cons _ l => arr_lst_codom l
  end.

Fixpoint arr_path (ls : arr_lst) : bool :=
  match ls with
  | lst_init s => true
  | lst_cons s l => W_eqb (codom s) (arr_lst_dom l) && arr_path l
  end.

Fixpoint arr_path_prop (ls : arr_lst) : Prop :=
  match ls with
  | lst_init s => True
  | lst_cons s l => (codom s) = (arr_lst_dom l) /\ arr_path_prop l
  end.

Lemma arr_lst_pathP (ls : arr_lst) : 
  arr_path_prop ls <-> arr_path ls = true.
Proof.
  induction ls; [easy|].
  - simpl.
    rewrite andb_true_iff, W_eqbP.
    split; intros []; split; easy || apply IHls; easy.
Qed.

Definition morphism_of_arr_path {C} {cC : Category C} (mC : MonoidalCategory cC)
  (c : C) (ls : arr_lst) (H : arr_path_prop ls) : 
    (word_to_mc mC (arr_lst_dom ls) c ~> word_to_mc mC (arr_lst_codom ls) c)%Cat.
induction ls.
- apply arr_to_mc.
- eapply compose.
  + apply arr_to_mc.
  + simpl in H. rewrite (proj1 H).
    apply IHls, H.
Defined.

  

Definition coherence_theorem_v1 : Prop.
refine (
  forall {C} {cC : Category C} (mC : MonoidalCategory cC) (c : C)
  (v w : W) (Hlen : len v = len w) (ls ls' : arr_lst) 
  (Hls : arr_path_prop ls) (Hls' : arr_path_prop ls')
  (Hdom : arr_lst_dom ls = arr_lst_dom ls') 
  (Hcodom : arr_lst_codom ls = arr_lst_codom ls'),
  _ : Prop).
pose (morphism_of_arr_path mC c ls Hls) as morls;
pose (morphism_of_arr_path mC c ls' Hls') as morls'.
rewrite Hdom, Hcodom in morls.
exact (morls ≃ morls')%Cat.
Defined.

Section VersionTwo.

Require Import Arith.

#[export, program] Instance WordCat : Category W := {
  morphism := fun b b' => if len b =? len b' then True else False;
  c_equiv := fun b b' f f' => True;
  compose := fun b b' b'' f g => _;
}.
Next Obligation.
  split; destruct (len A =? len B); easy.
Qed.
Next Obligation.
  destruct (len b =? len b') eqn:e.
  - rewrite Nat.eqb_eq in e.
    rewrite e.
    apply g.
  - destruct f.
Defined.
Next Obligation.
  rewrite Nat.eqb_refl.
  exact Logic.I.
Defined.

Local Open Scope Cat_scope.


Context {C : Type} {cC : Category C} {D : Type} {cD : Category D}.

Class StrictMonoidalFunctor 
  (mC : MonoidalCategory cC) (mD : MonoidalCategory cD) : Type := {
  strict_functor : Functor cC cD;
  mon_I_eq : strict_functor I = I;
  tensor_eq (c c' : C) : 
    strict_functor (c × c') = strict_functor c × strict_functor c';
  mon_mu_ij (i j : C) : 
  strict_functor i × strict_functor j <~> strict_functor (i × j) := 
    eq_rect_r (fun d : D => strict_functor i × strict_functor j <~> d) 
    (IdentityIsomorphism (strict_functor i × strict_functor j))
    (tensor_eq i j);
  mon_eps : I <~> strict_functor I :=
    eq_rect_r (fun d : D => I <~> d)
    (IdentityIsomorphism I)
    mon_I_eq;
}.

Coercion strict_functor : StrictMonoidalFunctor >-> Functor.

Context {mC : MonoidalCategory cC} {mD : MonoidalCategory cD}.

(* Definition mu_ij (F : StrictMonoidalFunctor mC mD) : forall (i j : C),
F i × F j <~> F (i × j).
intros.
rewrite tensor_eq.
apply IdentityIsomorphism.
Defined. *)

Lemma strict_monoidal_functor_assoc (F : StrictMonoidalFunctor mC mD)
  : forall (x y z : C), 
  associator (F x) (F y) (F z) ∘ id_ (F x) ⊗ mon_mu_ij y z ∘ mon_mu_ij x (y × z)
  ≃ mon_mu_ij x y ⊗ id_ (F z) ∘ mon_mu_ij (x × y) z ∘ F @ associator x y z.
Proof.
  intros.
  generalize (y × z).
  unfold mon_mu_ij.
  generalize dependent (F y × F z). as Fyz.
  rewrite <- (tensor_eq y z).

  rewrite tensor_eq.
  simpl.





  
