Inductive regexp (A : Type) :=
  | EmptySet
  | EmptyStr
  | Lit (a : A)
  | Cat (re1 re2 : regexp A)
  | Alt (re1 re2 : regexp A)
  | Star (re : regexp A).

Arguments EmptySet {_}.
Arguments EmptyStr {_}.
Arguments Lit {_}.
Arguments Cat {_} _ _.
Arguments Alt {_} _ _.
Arguments Star {_} _.

Declare Custom Entry regexp.
Declare Scope regexp_scope.
Notation "/ re /" := re (at level 0, re custom regexp at level 99) : regexp_scope.
Notation "( re )" := re (in custom regexp, re at level 99) : regexp_scope.
Notation "'∅'" := EmptySet (in custom regexp).
Notation "'ε'" := EmptyStr (in custom regexp).
Notation "re1 : re2" := (Cat re1 re2) (in custom regexp at level 40, left associativity) : regexp_scope.
Notation "re1 | re2" := (Alt re1 re2) (in custom regexp at level 50, left associativity) : regexp_scope.
Notation "re *" := (Star re) (in custom regexp at level 35, right associativity, format "re *") : regexp_scope.
Open Scope regexp_scope.

Definition lit_of_nat (n : nat) : regexp nat := Lit n.
Coercion lit_of_nat : nat >-> regexp.
