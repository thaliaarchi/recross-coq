Require Import Ascii Bool List String.
Import ListNotations.
Open Scope string_scope.

Inductive regexp :=
  | EmptySet
  | EmptyStr
  | Lit (c : ascii)
  | Cat (re1 re2 : regexp)
  | Alt (re1 re2 : regexp)
  | Star (re : regexp)
  | Class (cs : list ascii).

Declare Custom Entry regexp.
Declare Scope regexp_scope.
Notation "// re //" := re (at level 0, re custom regexp at level 99) : regexp_scope.
Notation "( re )" := re (in custom regexp, re at level 99) : regexp_scope.
Notation "x" := x (in custom regexp at level 0, x constr at level 0) : regexp_scope.
Notation "'∅'" := EmptySet (in custom regexp) : regexp_scope.
Notation "'ε'" := EmptyStr (in custom regexp) : regexp_scope.
Notation "re1 ; re2" := (Cat re1 re2) (in custom regexp at level 40, left associativity) : regexp_scope.
Notation "re1 | re2" := (Alt re1 re2) (in custom regexp at level 50, left associativity) : regexp_scope.
Notation "re *" := (Star re) (in custom regexp at level 35, right associativity, format "re *") : regexp_scope.
Notation "[ c1 , c2 , .. , cn ]" := (Class (cons c1 (cons c2 .. (cons cn nil) ..))) (in custom regexp) : regexp_scope.

Fixpoint regexp_of_string (s : string) : regexp :=
  match s with
  | String c "" => Lit c
  | String c s' => Cat (Lit c) (regexp_of_string s')
  | "" => EmptyStr
  end.

Coercion Lit : ascii >-> regexp.
Coercion regexp_of_string : string >-> regexp.

Reserved Notation "s =~ re" (at level 80).

Inductive regexp_match : list ascii -> regexp -> Prop :=
  | MEmpty :
      [] =~ EmptyStr
  | MLit c :
      [c] =~ Lit c
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
  | MStar0 re :
      [] =~ Star re
  | MStarCat s1 s2 re :
      s1 =~ re ->
      s2 =~ Star re ->
      s1 ++ s2 =~ Star re
  | MClass0 :
      [] =~ Class []
  | MClass c cs :
      In c cs ->
      [c] =~ Class cs

  where "s =~ re" := (regexp_match s re).

Lemma MStar1 : forall s re,
  s =~ re -> s =~ Star re.
Proof.
  intros. rewrite <- (app_nil_r _).
  repeat constructor. assumption. Qed.

Lemma MAlt : forall s re1 re2,
  s =~ re1 \/ s =~ re2 ->
  s =~ Alt re1 re2.
Proof.
  intros. destruct H; constructor; assumption. Qed.

Fixpoint is_empty_set (re : regexp) : bool :=
  match re with
  | EmptySet => true
  | EmptyStr => false
  | Lit _ => false
  | Cat re1 re2 => is_empty_set re1 && is_empty_set re2
  | Alt re1 re2 => is_empty_set re1 && is_empty_set re2
  | Star _ => false
  | Class [] => true
  | Class _ => false
  end.

Fixpoint is_empty_str (re : regexp) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Lit _ => false
  | Cat re1 re2 => is_empty_str re1 && is_empty_str re2
  | Alt re1 re2 => is_empty_str re1 && is_empty_str re2
  | Star EmptySet => true
  | Star re => is_empty_str re
  | Class _ => false
  end.

Theorem match_empty_str : forall re,
  is_empty_str re = true <-> forall s, s =~ re -> s = [].
Proof.
  split.
  - induction re; cbn; intros; try discriminate;
    inversion H0; subst;
    try apply andb_true_iff in H as [H1 H2].
    + reflexivity.
    + rewrite (IHre1 H1 _ H4), (IHre2 H2 _ H5). reflexivity.
    + apply (IHre1 H1 _ H3).
    + apply (IHre2 H2 _ H3).
    + reflexivity.
    + Admitted.

Fixpoint split_first (re : regexp) : option (ascii * regexp).
Admitted.

Fixpoint combine_classes (re : regexp) : regexp.
Admitted.
