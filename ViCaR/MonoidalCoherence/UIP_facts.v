Require MCDefinitions List.
Import MCDefinitions.MCClasses.

Section Eq_rect_facts.

Set Universe Polymorphism.

Lemma eq_rect_comp {A} (x : A) (P : A -> Type) y z p Hxy Hyz :
  eq_rect y P (eq_rect x P p y Hxy) z Hyz = 
  eq_rect x P p z (eq_trans Hxy Hyz).
Proof.
  revert z Hyz.
  case Hxy.
  intros z Hyz.
  case Hyz.
  easy.
Qed.

End Eq_rect_facts.


Section UIP_list.

Set Universe Polymorphism.

Context {X : Type} {UIPX : UIP X}.

Import List.ListNotations.

Local Open Scope list_scope.

Definition list_eq_proj_ty (a b : list X) : Prop := 
  match a, b with
  | nil, nil => True
  | x :: a', y :: b' => x = y /\ a' = b'
  | _, _ => False
  end.

Definition list_eq_proj {a : list X} : forall {b} (H : a = b), 
  list_eq_proj_ty a b.
  refine (
    match a with
    | nil => fun b =>
      match b with
      | nil => fun _ => Logic.I
      | y :: b' => fun H => False_ind _ _
      end
    | x :: a' => fun b =>
      match b with 
      | nil => fun H => False_ind _ _
      | y :: b' => fun H => 
        conj
          (f_equal (fun c => match c with 
            | nil => x
            | z :: c' => z
            end) H)
          (f_equal (fun c => match c with 
            | nil => nil
            | z :: c' => c'
            end) H)
      end
    end);
    congruence.
Defined.

Definition list_eq_proj_inv {a : list X} : forall {b} 
  (H : list_eq_proj_ty a b), a = b :=
  match a with
  | nil => fun b => 
    match b with
    | nil => fun _ => eq_refl
    | y :: b' => False_ind _
    end
  | x :: a' => fun b => 
    match b with 
    | nil => False_ind _
    | y :: b' => fun H => 
      eq_trans
        (f_equal (cons x) (proj2' H))
        (f_equal (fun z => cons z b') (proj1' H))
    end
  end.

Lemma list_nu_linv {a b} (H : a = b) : 
  list_eq_proj_inv (list_eq_proj H) = H.
Proof.
  case H, a; easy.
Qed.

Lemma list_eq_proj_const_of_UIP_on {a b : list X} (y : X)
  (HUIP : EqdepFacts.UIP_refl_on_ (list X) b)
  (H H' : a = y :: b) : 
  list_eq_proj H = list_eq_proj H'.
Proof.
  destruct a; [easy|].
  simpl.
  f_equal.
  - apply uip.
  - pose proof (eq_sym (proj2 (list_eq_proj H))) as Hs.
    induction Hs.
    etransitivity;
    [|symmetry];
    apply HUIP.
Qed.

Lemma UIP_refl_list : EqdepFacts.UIP_refl_ (list X).
Proof.
  intros a; induction a; intros H;
  match goal with
  |- ?LHS = ?RHS => 
    rewrite <- (list_nu_linv LHS), <- (list_nu_linv RHS); f_equal
  end.
  apply (list_eq_proj_const_of_UIP_on _ IHa).
Qed.

Lemma UIP_list : UIP (list X).
Proof.
  constructor.
  intros a b H H'.
  pose proof H as Hs;
  induction Hs.
  etransitivity;
  [|symmetry];
  apply UIP_refl_list.
Qed.

End UIP_list.

Section UIP_bw.

Set Universe Polymorphism.

Import MCDefinitions.

Context {X : Type} {UIPX : UIP X}.

Local Notation bw := (@bw X).
Local Notation bwnorm := (@bwnorm X).

(* Definition bwnorm_norm_e_eq (a : bwnorm) : {a = norm_e} + {~ a = norm_e}.
destruct a; (left; reflexivity) + (right; congruence).
Defined.

Definition norm_e_nu {b : bwnorm} : forall {a : bwnorm} (H : a = b), a = b :=
  match b with 
  | norm_e => 
    fun a H => 
    match bwnorm_norm_e_eq a with
    | left Heq => Heq
    | right Hneq => False_ind _ (Hneq H)
    end
  | _ => fun a H => H
  end.

Definition norm_e_nu_inv {b : bwnorm} : forall {a : bwnorm} (H : a = b), a = b := 
  match b with 
  | norm_e => fun a H => eq_ind _ (fun a => a = norm_e) H _ eq_refl
  | _ => fun a H => H
  end.

Lemma norm_e_nu_linv {a b : bwnorm} (H : a = b) : 
  norm_e_nu_inv (norm_e_nu H) = H.
Proof.
  case H.
  destruct a; easy.
Qed.

Lemma norm_e_nu_const {a : bwnorm} (H H' : a = norm_e) : 
  norm_e_nu H = norm_e_nu H'.
Proof.
  unfold norm_e_nu.
  destruct (bwnorm_norm_e_eq a); easy.
Qed.

Lemma norm_e_UIP {a : bwnorm} (H H' : a = norm_e) : 
  H = H'.
Proof.
  rewrite <- (norm_e_nu_linv H), <- (norm_e_nu_linv H').
  f_equal.
  apply norm_e_nu_const.
Qed. *)

Definition bwnorm_rtens_eq_l_r {a b : bwnorm} {x y : X} 
  (H : norm_rtens a x = norm_rtens b y) :
  a = b /\ x = y := 
  conj (f_equal
    (fun e =>
    match e with
    | norm_e => a
    | norm_rtens n _ => n
    end) H)
    (f_equal
    (fun e : bwnorm =>
    match e with
    | norm_e => x
    | norm_rtens _ x0 => x0
    end) H).

Definition bwnorm_rtens_eq_l_r_inv {a b : bwnorm} {x y : X} 
  (H : a = b /\ x = y) :
  norm_rtens a x = norm_rtens b y :=
  eq_trans (f_equal (fun a => norm_rtens a x) (proj1' H))
    (f_equal (norm_rtens b) (proj2' H)).
  (* f_equal2 norm_rtens (proj1' H) (proj2' H).  *)

Definition bwnorm_eq_proj_type (b a : bwnorm) : Prop :=
  match b with 
  | norm_e =>
    match a with
    | norm_e => True
    | norm_rtens a' x =>
        False
    end
  | norm_rtens b' y =>
    match a with
    | norm_e => False
    | norm_rtens a' x =>
        a' = b' /\ x = y
    end
  end.

Definition bwnorm_proj_eq {b : bwnorm} : forall {a : bwnorm} (H : a = b),
   bwnorm_eq_proj_type b a.
  refine (
  match b as _b return forall a (H : a = _b), bwnorm_eq_proj_type _b a with
  | norm_e => 
    fun a => match a as _a return forall (H : _a = norm_e), 
      bwnorm_eq_proj_type norm_e _a with
    | norm_e => fun _ => Logic.I
    | norm_rtens a' y' => _
    end
  | norm_rtens b' x => 
    fun a => 
    match a as _a return forall (H : _a = norm_rtens b' x), 
      bwnorm_eq_proj_type (norm_rtens b' x) _a with
    | norm_e => _
    | norm_rtens a' y' => fun H =>
      conj (f_equal
        (fun e =>
        match e with
        | norm_e => a
        | norm_rtens n _ => n
        end) H)
        (f_equal
        (fun e : bwnorm =>
        match e with
        | norm_e => x
        | norm_rtens _ x0 => x0
        end) H)
    end
  end);
  congruence.
Defined.

Definition bwnorm_proj_eq_inv {b : bwnorm} : forall {a : bwnorm}
  (H: bwnorm_eq_proj_type b a), a = b :=
  match b with 
  | norm_e =>
    fun a => 
    match a with
    | norm_e => fun _ => eq_refl
    | norm_rtens _ _ => False_ind _
    end
  | norm_rtens b' y => 
    fun a => 
    match a with 
    | norm_e => False_ind _
    | norm_rtens a' y => fun H =>
      bwnorm_rtens_eq_l_r_inv H
    end
  end.

Lemma bwnorm_proj_eq_linv {a b : bwnorm} (H : a = b) : 
  bwnorm_proj_eq_inv (bwnorm_proj_eq H) = H.
Proof.
  case H.
  destruct a, b; easy.
Qed.

Lemma bwnorm_proj_eq_const_norm_e {a : bwnorm} (H H' : a = norm_e) : 
  bwnorm_proj_eq H = bwnorm_proj_eq H'.
Proof.
  generalize (bwnorm_proj_eq H) (bwnorm_proj_eq H').
  destruct a; intros [] []; easy.
Qed.

Lemma bwnorm_proj_eq_const_of_UIP_on {a b : bwnorm} (y : X)
  (HUIP : EqdepFacts.UIP_refl_on_ bwnorm b)
  (H H' : a = norm_rtens b y) : 
  bwnorm_proj_eq H = bwnorm_proj_eq H'.
Proof.
  destruct a; [easy|].
  simpl.
  unfold bwnorm_rtens_eq_l_r.
  f_equal; simpl.
  - pose proof (eq_sym (proj1 (bwnorm_rtens_eq_l_r H))) as Hab.
    induction Hab.
    etransitivity; [|symmetry]; apply HUIP.
  - apply UIPX.
Qed.

Lemma UIP_on_norm_rtens_of_UIP_on {b : bwnorm} (y : X)
  (HUIP : EqdepFacts.UIP_refl_on_ bwnorm b) : 
  EqdepFacts.UIP_refl_on_ bwnorm (norm_rtens b y).
Proof.
  intros H.
  match goal with 
  |- ?LHS = ?RHS =>
    rewrite <- (bwnorm_proj_eq_linv LHS), <- (bwnorm_proj_eq_linv RHS)
  end.
  f_equal.
  apply bwnorm_proj_eq_const_of_UIP_on; easy.
Qed.

Lemma UIP_refl_bwnorm (b : bwnorm) : EqdepFacts.UIP_refl_on_ bwnorm b.
Proof.
  induction b.
  - intros H.
    match goal with 
    |- ?LHS = ?RHS =>
      rewrite <- (bwnorm_proj_eq_linv LHS), <- (bwnorm_proj_eq_linv RHS)
    end.
    f_equal; apply bwnorm_proj_eq_const_norm_e.
  - apply UIP_on_norm_rtens_of_UIP_on, IHb.
Qed.

#[export, program] Instance UIP_bwnorm : UIP bwnorm := {}.
Next Obligation.
  etransitivity;
  [|symmetry]; 
  apply UIP_refl_bwnorm.
Qed.

Definition bw_eq_proj_type (b a : bw) : Prop :=
  match b with 
  | e =>
    match a with
    | e => True
    | var x => False
    | tens a0 a1 => False
    end
  | var y =>
    match a with
    | e => False
    | var x => x = y
    | tens a0 a1 => False
    end
  | tens b0 b1 =>
    match a with
    | e => False
    | var x => False
    | tens a0 a1 => a0 = b0 /\ a1 = b1
    end
  end.

Definition bw_eq_proj {b : bw} : forall {a : bw} (H : a = b), 
  bw_eq_proj_type b a.
  refine (
  match b as _b return forall a, a = _b -> bw_eq_proj_type _b a with
  | e => fun a =>
    match a with
    | e => fun _ => Logic.I
    | var x => fun H => _
    | tens a0 a1 => fun H => _
    end
  | var y => fun a =>
    match a as _a return _a = var y -> bw_eq_proj_type (var y) _a with
    | e => fun H => _
    | var x => fun H =>
      f_equal (fun c : bw => 
        match c with 
        | e => x
        | var z => z
        | tens a' b' => x
        end) H
    | tens a0 a1 => fun H => _
    end
  | tens b0 b1 => fun a =>
    match a with
    | e => fun H => _
    | var x => fun H => _
    | tens a0 a1 => fun H => 
      conj 
        (f_equal (fun c : bw => 
          match c with
          | e => a0
          | var z => a0
          | tens a' b' => a'
          end) H)
        (f_equal (fun c : bw => 
          match c with
          | e => a0
          | var z => a0
          | tens a' b' => b'
          end) H)
    end
  end);
  congruence.
Defined.

Definition bw_eq_proj_inv {b : bw} : forall {a : bw} 
  (H : bw_eq_proj_type b a), a = b :=
  match b with
  | e => fun a =>
    match a with
    | e => fun _ => eq_refl
    | var x => fun H => False_ind _ H
    | tens a0 a1 => fun H => False_ind _ H
    end
  | var y => fun a => 
    match a with
    | e => fun H => False_ind _ H
    | var x => fun H => f_equal var H
    | tens a0 a1 => fun H => False_ind _ H
    end
  | tens b0 b1 => fun a =>
    match a with
    | e => fun H => False_ind _ H
    | var x => fun H => False_ind _ H
    | tens a0 a1 => fun H =>     
      eq_trans (f_equal (fun a => tens a a1) (proj1' H))
      (f_equal (tens b0) (proj2' H))
    end
  end.

Lemma bw_eq_proj_linv {a b : bw} (H : a = b) : 
  bw_eq_proj_inv (bw_eq_proj H) = H.
Proof.
  case H.
  destruct a, b; easy.
Qed.

Lemma UIP_refl_bw : EqdepFacts.UIP_refl_ bw.
Proof.
  intros b.
  induction b.
  - intros H. 
    rewrite <- (bw_eq_proj_linv H), <- (bw_eq_proj_linv eq_refl).
    f_equal.
  - intros H.
    rewrite <- (bw_eq_proj_linv H), <- (bw_eq_proj_linv eq_refl).
    f_equal.
    apply UIPX.
  - intros H.
    rewrite <- (bw_eq_proj_linv H), <- (bw_eq_proj_linv eq_refl).
    f_equal.
    simpl.
    f_equal.
    + apply IHb1.
    + apply IHb2.
Qed.

#[export, program] Instance UIP_bw : UIP bw.
Next Obligation.
  etransitivity; 
  [|symmetry];
  apply UIP_refl_bw.
Qed.

End UIP_bw.

(* Section UIP_isomorphism.

Context {X Y : Type} {UIPX : UIP X}
  (f : X -> Y) (g : Y -> X)
  (Hfg : forall y, f (g y) = y)
  (Hgf : forall x, g (f x) = x). *)

(* Definition normalize_eq {x y : X} (H : f x = f y) : f x = f y :=
  eq_ind _ (fun a => f a = f y) (H y) _ _.
pose (f_equal f (f_equal g H)) as H'.
rewrite 2!Hgf in H'.
exact H'.
Defined.

Definition normalize_eq_inv {x y : X} (H : f x = f y) : f x = f y :=
  eq_ind _ (fun a => a = f y) H _ (normalize_eq eq_refl).

Lemma eq_ind_eq_rect {A} (x : A) (P : A -> Prop) (p : P x) (y : A) (H : x = y) :
  eq_ind x P p y H = eq_rect x P p y H.
Proof.
  easy.
Qed.

Lemma normalize_eq_linv {x y : X} (H : f x = f y) :
  normalize_eq_inv (normalize_eq H) = H.
Proof.
  pose proof H as H'. 
  apply (f_equal g) in H'.
  rewrite 2!Hgf in H'.
  induction H'.
  unfold normalize_eq_inv, normalize_eq.
  induction H.
  rewrite (UIPX.(uip) _ eq_refl).
  simpl.
  rewrite !eq_ind_eq_rect.
  generalize (Hgf x).
  generalize (g (f x)).
  intros ? e; induction (eq_sym e).
  rewrite 2!(eq_rect_eq (X:=X)).
  revert H.
  generalize (f x).
  intros y H.
  induction H.
  
  lazymatch goal with
  |- context[ ?T ] => lazymatch type of T with
    | @eq X _ _ => generalize T
    end
  end.
  generalize (Hgf x) (Hgf y).
  generalize (f x) (f y).
  unfold normalize_eq_inv
  case H.
  simpl.
  case (Hfg x).
  simpl.
  unfold eq_ind.
  (* rewrite eq_rect_eq. *)
  rewrite (UIPX.(uip) _ eq_refl).
  

Lemma f_equal_inj 

Lemma UIP_of_isomorphism {X Y} {UIPX : UIP X}
  (f : X -> Y) (g : Y -> X)
  (Hfg : forall y, f (g y) = y)
  (Hgf : forall x, g (f x) = x) :
  UIP Y.
Proof.
  constructor. *)
  
