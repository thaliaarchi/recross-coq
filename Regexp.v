Require Import Ascii String.
Open Scope string_scope.

Inductive regexp :=
  | EmptySet
  | EmptyStr
  | Lit (a : ascii)
  | Cat (re1 re2 : regexp)
  | Alt (re1 re2 : regexp)
  | Star (re : regexp).

Declare Custom Entry regexp.
Declare Scope regexp_scope.
Notation "// re //" := re (at level 0, re custom regexp at level 99) : regexp_scope.
Notation "( re )" := re (in custom regexp, re at level 99) : regexp_scope.
Notation "x" := x (in custom regexp at level 0, x constr at level 0) : regexp_scope.
Notation "'∅'" := EmptySet (in custom regexp).
Notation "'ε'" := EmptyStr (in custom regexp).
Notation "re1 ; re2" := (Cat re1 re2) (in custom regexp at level 40, left associativity) : regexp_scope.
Notation "re1 | re2" := (Alt re1 re2) (in custom regexp at level 50, left associativity) : regexp_scope.
Notation "re *" := (Star re) (in custom regexp at level 35, right associativity, format "re *") : regexp_scope.
Open Scope regexp_scope.

Local Notation "a :: s" := (String a s) : string_scope.

Fixpoint regexp_of_string (s : string) : regexp :=
  match s with
  | a :: "" => Lit a
  | a :: s' => Cat (Lit a) (regexp_of_string s')
  | "" => EmptyStr
  end.

Coercion Lit : ascii >-> regexp.
Coercion regexp_of_string : string >-> regexp.

Reserved Notation "s =~ re" (at level 80).

Inductive regexp_match : string -> regexp -> Prop :=
  | MEmpty :
      "" =~ EmptyStr
  | MLit a :
      String a "" =~ Lit a
  | MCat s1 re1 s2 re2 :
      s1 =~ re1 ->
      s2 =~ re2 ->
      s1 ++ s2 =~ // re1; re2 //
  | MAltL s1 re1 re2 :
      s1 =~ re1 ->
      s1 =~ // re1 | re2 //
  | MAltR s2 re1 re2 :
      s2 =~ re2 ->
      s2 =~ // re1 | re2 //
  | MStar0 re :
      "" =~ // re* //
  | MStarCat s1 s2 re :
      s1 =~ re ->
      s2 =~ // re* // ->
      s1 ++ s2 =~ // re* //

  where "s =~ re" := (regexp_match s re).
