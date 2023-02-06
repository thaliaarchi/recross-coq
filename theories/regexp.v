Require Import Bool.
Require Import Ascii String. Open Scope string_scope.
Require Import List. Import ListNotations.
Require Import Program.Equality.
Require Import Setoid.

Local Ltac invert H := inversion H; subst; clear H.

Definition char_set := list ascii.

Inductive regexp :=
  | Void
  | Nil
  | Char (c : ascii)
  | Class (cs : char_set)
  | Star (re : regexp)
  | Cat (re1 re2 : regexp)
  | Alt (re1 re2 : regexp)
  | And (re1 re2 : regexp).

Declare Custom Entry regexp.
Declare Scope regexp_scope.
Notation "// re //" := re (at level 0, re custom regexp at level 99) : regexp_scope.
Notation "( re )" := re (in custom regexp, re at level 99) : regexp_scope.
Notation "x" := x (in custom regexp at level 0, x constr at level 0) : regexp_scope.
Notation "'∅'" := Void (in custom regexp) : regexp_scope.
Notation "'ε'" := Nil (in custom regexp) : regexp_scope.
Notation "[ c1 , c2 , .. , cn ]" := (Class (cons c1 (cons c2 .. (cons cn nil) ..))) (in custom regexp) : regexp_scope.
Notation "re *" := (Star re) (in custom regexp at level 35, left associativity, format "re *") : regexp_scope.
Notation "re1 ; re2" := (Cat re1 re2) (in custom regexp at level 40, left associativity) : regexp_scope.
Notation "re1 | re2" := (Alt re1 re2) (in custom regexp at level 50, left associativity) : regexp_scope.
Notation "re1 & re2" := (And re1 re2) (in custom regexp at level 45, left associativity) : regexp_scope.

Fixpoint regexp_of_string (s : string) : regexp :=
  match s with
  | String c "" => Char c
  | String c s' => Cat (Char c) (regexp_of_string s')
  | "" => Nil
  end.

Coercion Char : ascii >-> regexp.
Coercion regexp_of_string : string >-> regexp.

Reserved Notation "s =~ re" (at level 80).

Inductive regexp_match : list ascii -> regexp -> Prop :=
  | MNil :
      [] =~ Nil
  | MChar c :
      [c] =~ Char c
  | MClass c cs :
      In c cs ->
      [c] =~ Class cs
  | MStar0 re :
      [] =~ Star re
  | MStarCat s1 s2 re :
      s1 =~ re ->
      s2 =~ Star re ->
      s1 ++ s2 =~ Star re
  | MCat s1 re1 s2 re2 :
      s1 =~ re1 ->
      s2 =~ re2 ->
      s1 ++ s2 =~ Cat re1 re2
  | MAltL s1 re1 re2 :
      s1 =~ re1 ->
      s1 =~ Alt re1 re2
  | MAltR s2 re1 re2 :
      s2 =~ re2 ->
      s2 =~ Alt re1 re2
  | MAnd s re1 re2 :
      s =~ re1 ->
      s =~ re2 ->
      s =~ And re1 re2

  where "s =~ re" := (regexp_match s re).

Definition equiv (re re' : regexp) := forall s,
  s =~ re <-> s =~ re'.

Lemma equiv_refl : forall re, equiv re re.
Proof. now split. Qed.

Lemma equiv_sym : forall re1 re2,
  equiv re1 re2 -> equiv re2 re1.
Proof.
  split; intros; now apply H. Qed.

Lemma equiv_trans : forall re1 re2 re3,
  equiv re1 re2 -> equiv re2 re3 -> equiv re1 re3.
Proof.
  split; intros.
  - apply H0. now apply H.
  - apply H. now apply H0. Qed.

Definition cs_equiv (cs1 cs2 : char_set) := forall c,
  In c cs1 <-> In c cs2.

Lemma cs_equiv_refl : forall cs, cs_equiv cs cs.
Proof. now split. Qed.

Lemma cs_equiv_sym : forall cs1 cs2,
  cs_equiv cs1 cs2 -> cs_equiv cs2 cs1.
Proof.
  split; intros; now apply H. Qed.

Lemma cs_equiv_trans : forall cs1 cs2 cs3,
  cs_equiv cs1 cs2 -> cs_equiv cs2 cs3 -> cs_equiv cs1 cs3.
Proof.
  split; intros.
  - apply H0. now apply H.
  - apply H. now apply H0. Qed.

Add Relation regexp equiv
  reflexivity proved by equiv_refl
  symmetry proved by equiv_sym
  transitivity proved by equiv_trans
  as equiv_rel.

Add Relation char_set cs_equiv
  reflexivity proved by cs_equiv_refl
  symmetry proved by cs_equiv_sym
  transitivity proved by cs_equiv_trans
  as cs_equiv_rel.

Add Morphism Class
  with signature cs_equiv ==> equiv as Class_compat.
Proof.
  split; intros;
  invert H0; apply H in H3; now apply MClass. Qed.

Add Morphism Star
  with signature equiv ==> equiv as Star_compat.
Proof.
  split; intros.
  - dependent induction H0.
    + apply MStar0.
    + apply MStarCat. now apply H. now apply IHregexp_match2 with x.
  - dependent induction H0.
    + apply MStar0.
    + apply MStarCat. now apply H. now apply IHregexp_match2 with y.
Qed.

Add Morphism Cat
  with signature equiv ==> equiv ==> equiv as Cat_compat.
Proof.
  split; intros;
  invert H1; (apply MCat; [now apply H | now apply H0]). Qed.

Add Morphism Alt
  with signature equiv ==> equiv ==> equiv as Alt_compat.
Proof.
  split; intros;
  (invert H1; [now apply MAltL, H | now apply MAltR, H0]). Qed.

Add Morphism And
  with signature equiv ==> equiv ==> equiv as And_compat.
Proof.
  split; intros;
  invert H1; (apply MAnd; [now apply H | now apply H0]). Qed.

Lemma Void_not : forall s,
  ~ (s =~ Void).
Proof.
  unfold not. intros. inversion H. Qed.

Lemma Nil_nil : forall s,
  s =~ Nil <-> s = [].
Proof.
  split; intros. now invert H. subst. apply MNil. Qed.

Lemma Class0 :
  equiv (Class []) Void.
Proof.
  split; intros; now invert H. Qed.

Lemma Class1 : forall c,
  equiv (Class [c]) (Char c).
Proof.
  split; intros; invert H.
  - invert H2. apply MChar. invert H.
  - apply MClass, in_eq. Qed.

Lemma Class1_Alt : forall c cs,
  equiv (Class (c :: cs)) (Alt (Char c) (Class cs)).
Proof.
  split; intros; invert H; invert H2.
  - apply MAltL, MChar.
  - now apply MAltR, MClass.
  - apply MClass, in_eq.
  - now apply MClass, in_cons. Qed.

Lemma ClassN : forall cs,
  equiv (Class cs) (fold_right (fun c => Alt (Char c)) Void cs).
Proof.
  split; intros;
  induction cs; cbn; try now invert H.
  - invert H. invert H2.
    + apply MAltL, MChar.
    + now apply MAltR, IHcs, MClass.
  - invert H.
    + now apply Class1_Alt, MAltL.
    + now apply Class1_Alt, MAltR, IHcs.
Qed.

Lemma Star1 : forall re s,
  s =~ re -> s =~ Star re.
Proof.
  intros. rewrite <- (app_nil_r _). now apply MStarCat, MStar0. Qed.

Lemma Star_Void :
  equiv (Star Void) Nil.
Proof.
  split; intros.
  - invert H. apply MNil. invert H1.
  - invert H. apply MStar0. Qed.

Lemma Star_Nil :
  equiv (Star Nil) Nil.
Proof.
  split; intros.
  - dependent induction H.
    + apply MNil.
    + invert H. now apply IHregexp_match2.
  - invert H. apply MStar0.
Qed.

Lemma Star_Cat : forall re s1 s2,
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros re s1 s2 H. generalize dependent s2.
  dependent induction H; intros.
  - assumption.
  - rewrite <- app_assoc. apply MStarCat. assumption.
    now apply IHregexp_match2.
Qed.

Lemma Star_idemp : forall re,
  equiv (Star (Star re)) (Star re).
Proof.
  split; intros.
  - dependent induction H.
    + apply MStar0.
    + apply Star_Cat. assumption. now apply IHregexp_match2.
  - dependent induction H.
    + apply MStar0.
    + apply MStarCat. now apply Star1. now apply IHregexp_match2.
Qed.

Lemma Star_Alt_Nil_l : forall re,
  equiv (Star (Alt Nil re)) (Star re).
Proof.
  split; intros;
  dependent induction H; try apply MStar0.
  - invert H.
    + invert H3. now apply IHregexp_match2.
    + apply MStarCat. assumption. now apply IHregexp_match2.
  - apply MStarCat.
    + now apply MAltR.
    + now apply IHregexp_match2.
Qed.

Lemma Star_Alt_Nil_r : forall re,
  equiv (Star (Alt re Nil)) (Star re).
Proof.
  split; intros;
  dependent induction H; try apply MStar0.
  - invert H.
    + apply MStarCat. assumption. now apply IHregexp_match2.
    + invert H3. now apply IHregexp_match2.
  - apply MStarCat.
    + now apply MAltL.
    + now apply IHregexp_match2.
Qed.

Lemma Cat_Void_l : forall re,
  equiv (Cat Void re) Void.
Proof.
  split; intros; invert H. invert H3. Qed.

Lemma Cat_Void_r : forall re,
  equiv (Cat re Void) Void.
Proof.
  split; intros; invert H. invert H4. Qed.

Lemma Cat_Nil_l : forall re,
  equiv (Cat Nil re) re.
Proof.
  split; intros.
  - invert H. now invert H3.
  - rewrite <- (app_nil_l _). apply MCat. apply MNil. assumption. Qed.

Lemma Cat_Nil_r : forall re,
  equiv (Cat re Nil) re.
Proof.
  split; intros.
  - invert H. invert H4. now rewrite app_nil_r.
  - rewrite <- (app_nil_r _). now apply MCat, MNil. Qed.

Lemma Cat_Star : forall re,
  equiv (Cat (Star re) (Star re)) (Star re).
Proof.
  split; intros.
  - invert H. now apply Star_Cat.
  - rewrite <- (app_nil_r _). now apply MCat, MStar0. Qed.

Lemma Cat_Alt_distr_l : forall re1 re2 re3,
  equiv (Cat re1 (Alt re2 re3)) (Alt (Cat re1 re2) (Cat re1 re3)).
Proof.
  split; intros.
  - invert H; invert H4; [apply MAltL | apply MAltR]; now apply MCat.
  - invert H; invert H2; [now apply MCat, MAltL | now apply MCat, MAltR].
Qed.

Lemma Cat_Alt_distr_r : forall re1 re2 re3,
  equiv (Cat (Alt re1 re2) re3) (Alt (Cat re1 re3) (Cat re2 re3)).
Proof.
  split; intros.
  - invert H; invert H3; [apply MAltL | apply MAltR]; now apply MCat.
  - invert H; invert H2; apply MCat; try assumption; [now apply MAltL | now apply MAltR].
Qed.

Lemma Cat_nil : forall re1 re2,
  [] =~ Cat re1 re2 <-> [] =~ re1 /\ [] =~ re2.
Proof.
  split; intros.
  - split; invert H; apply app_eq_nil in H0 as []; now subst.
  - invert H. rewrite <- (app_nil_r _). now apply MCat. Qed.

Lemma Alt_or : forall re1 re2 s,
  s =~ Alt re1 re2 <-> s =~ re1 \/ s =~ re2.
Proof.
  split; intros.
  - invert H; [left | right]; assumption.
  - destruct H; [apply MAltL | apply MAltR]; assumption. Qed.

Lemma Alt_comm : forall re1 re2,
  equiv (Alt re1 re2) (Alt re2 re1).
Proof.
  split; intros; (invert H; [now apply MAltR | now apply MAltL]). Qed.

Lemma Alt_assoc : forall re1 re2 re3,
  equiv (Alt re1 (Alt re2 re3)) (Alt (Alt re1 re2) re3).
Proof.
  split; intros.
  - invert H. now apply MAltL, MAltL.
    invert H2. now apply MAltL, MAltR. now apply MAltR.
  - invert H. invert H2. now apply MAltL.
    now apply MAltR, MAltL. now apply MAltR, MAltR.
Qed.

Lemma Alt_Void_l : forall re,
  equiv (Alt Void re) re.
Proof.
  split; intros. now invert H. now apply MAltR. Qed.

Lemma Alt_Void_r : forall re,
  equiv (Alt re Void) re.
Proof.
  intros. now rewrite Alt_comm, Alt_Void_l. Qed.

Lemma Alt_Class : forall cs1 cs2,
  equiv (Alt (Class cs1) (Class cs2)) (Class (cs1 ++ cs2)).
Proof.
  split; intros.
  - invert H; invert H2;
    apply MClass; apply in_app_iff; [now left | now right].
  - invert H; apply in_app_iff in H2 as [];
    [apply MAltL | apply MAltR]; now apply MClass.
Qed.

Lemma And_comm : forall re1 re2,
  equiv (And re1 re2) (And re2 re1).
Proof.
  split; intros; invert H; now apply MAnd. Qed.

Lemma And_assoc : forall re1 re2 re3,
  equiv (And re1 (And re2 re3)) (And (And re1 re2) re3).
Proof.
  split; intros.
  - invert H. invert H4. repeat apply MAnd; assumption.
  - invert H. invert H3. repeat apply MAnd; assumption. Qed.

Lemma And_Void_l : forall re,
  equiv (And Void re) Void.
Proof.
  split; intros. now invert H. now apply MAnd. Qed.

Lemma And_Void_r : forall re,
  equiv (And re Void) Void.
Proof.
  intros. now rewrite And_comm, And_Void_l. Qed.

Fixpoint is_void (re : regexp) : bool :=
  match re with
  | Void | Class [] => true
  | Nil | Char _ | Class _ | Star _ => false
  | Cat re1 re2 => is_void re1 || is_void re2
  | Alt re1 re2 => is_void re1 && is_void re2
  | And re1 re2 => is_void re1 || is_void re2
  end.

Fixpoint is_nil (re : regexp) : bool :=
  match re with
  | Nil => true
  | Void | Char _ | Class _ => false
  | Star re => is_void re
  | Cat re1 re2 => is_nil re1 && is_nil re2
  | Alt re1 re2 => is_nil re1 && is_nil re2
  | And re1 re2 => is_nil re1 && is_nil re2
  end.

Fixpoint matches_nil (re : regexp) : bool :=
  match re with
  | Void | Char _ | Class _ => false
  | Nil | Star _ => true
  | Cat re1 re2 => matches_nil re1 && matches_nil re2
  | Alt re1 re2 => matches_nil re1 || matches_nil re2
  | And re1 re2 => matches_nil re1 && matches_nil re2
  end.

Theorem match_void : forall re,
  is_void re = true -> equiv re Void.
Proof.
  split; generalize dependent s.
  - induction re; cbn in *; intros; try intuition.
    + destruct cs.
      * invert H0. destruct (in_nil H3).
      * discriminate.
    + invert H0.
      apply orb_true_iff in H as [].
      * apply (IHre1 H _) in H4. invert H4.
      * apply (IHre2 H _) in H5. invert H5.
    + apply andb_true_iff in H as [H1 H2].
      invert H0.
      * apply (IHre1 H1 _) in H4. invert H4.
      * apply (IHre2 H2 _) in H4. invert H4.
    + invert H0.
      apply orb_true_iff in H as [].
      * now apply (IHre1 H).
      * now apply (IHre2 H).
  - intros. invert H0.
Qed.

Theorem match_nil : forall re,
  is_nil re = true -> equiv re Nil.
Proof.
  split; generalize dependent s.
  - induction re; cbn in *; intros; try intuition.
    + invert H0.
      * apply MNil.
      * apply (match_void _ H) in H2. invert H2.
    + invert H0.
      apply andb_true_iff in H as [H1 H2].
      apply (IHre1 H1 _) in H4. invert H4.
      apply (IHre2 H2 _) in H5. invert H5. apply MNil.
    + apply andb_true_iff in H as [H1 H2].
      invert H0; [now apply (IHre1 H1 ) | now apply (IHre2 H2)].
    + invert H0.
      apply andb_true_iff in H as [H1 H2].
      now apply (IHre1 H1).
  - induction re; cbn in *; intros; try intuition;
    invert H0.
    + apply MStar0.
    + apply andb_true_iff in H as [H1 H2].
      rewrite <- (app_nil_r _).
      apply MCat; [apply (IHre1 H1) | apply (IHre2 H2)]; apply MNil.
    + apply andb_true_iff in H as [H1 H2].
      apply MAltL, (IHre1 H1 _), MNil.
    + apply andb_true_iff in H as [H1 H2].
      apply MAnd.
      * now apply IHre1, MNil.
      * now apply IHre2, MNil.
Qed.

Lemma is_nil_matches_nil : forall re,
  is_nil re = true -> matches_nil re = true.
Proof.
  induction re; cbn; intros; try discriminate; try reflexivity;
  apply andb_true_iff in H as [H1 H2];
  try (apply andb_true_iff; split); try (apply orb_true_iff; left);
  try apply IHre2, H2; apply IHre1, H1.
Qed.

Theorem matches_nil_true : forall re,
  matches_nil re = true <-> [] =~ re.
Proof.
  split.
  - induction re; cbn; intros; try discriminate.
    + apply MNil.
    + apply MStar0.
    + apply andb_true_iff in H as [H1 H2].
      rewrite <- (app_nil_r _). apply MCat.
      apply IHre1, H1. apply IHre2, H2.
    + apply orb_true_iff in H as [].
      apply MAltL, IHre1, H. apply MAltR, IHre2, H.
    + apply andb_true_iff in H as [H1 H2].
      apply MAnd.
      apply IHre1, H1. apply IHre2, H2.
  - induction re; cbn; intros; try reflexivity;
    try apply andb_true_iff; try apply orb_true_iff;
    invert H.
    + apply app_eq_nil in H0 as []. subst.
      split. now apply IHre1. now apply IHre2.
    + left. now apply IHre1.
    + right. now apply IHre2.
    + split. now apply IHre1. now apply IHre2.
Qed.

Theorem matches_nil_false : forall re,
  matches_nil re = false <-> ~ ([] =~ re).
Proof.
  unfold not. split.
  - induction re; cbn; intros; try discriminate;
    invert H0; try (apply app_eq_nil in H1 as []; subst);
    try apply andb_false_iff in H as [];
    try apply orb_false_iff in H as [];
    try (now apply IHre1); try (now apply IHre2).
  - induction re; cbn; intros; try reflexivity.
    + exfalso. apply H. apply MNil.
    + exfalso. apply H. apply MStar0.
    + apply andb_false_iff.
      induction re1; try (now left).
      * right. apply IHre2. intros. apply H, Cat_nil.
        split. apply MNil. assumption.
      * right. apply IHre2. intros. apply H, Cat_nil.
        split. apply MStar0. assumption.
      * left. apply IHre1. intros. apply H. apply Cat_nil.
        split. assumption.
Admitted.

Theorem matches_nil_Alt : forall re,
  matches_nil re = true -> equiv (Alt Nil re) re.
Proof.
  split; intros.
  - invert H0. invert H3. now apply matches_nil_true. assumption.
  - now apply MAltR. Qed.
