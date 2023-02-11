Parameter bound : Type.

Parameter succ : bound -> bound. (* Saturating *)

Parameter le : bound -> bound -> Prop.
Parameter le_dec : forall x y, {le x y} + {~ le x y}.
Parameter le_refl : forall x, le x x.
Parameter le_trans : forall x y z, le x y -> le y z -> le x z.
Parameter lt_le_incl : forall x y, ~ le y x -> le x y.

Definition leb x y := if le_dec x y then true else false.

Declare Scope bound_scope.
Bind Scope bound_scope with bound.
Open Scope bound_scope.

Local Notation "x >= y" := (le y x) (at level 70) : bound_scope.
Local Notation "x <= y" := (le x y) (at level 70) : bound_scope.
Local Notation "x > y" := (~ le x y) (at level 70) : bound_scope.
Local Notation "x < y" := (~ le y x) (at level 70) : bound_scope.
Local Notation "x <= y <= z" := (le x y /\ le y z) (at level 70, y at next level) : bound_scope.

Local Notation "x >=? y" := (leb y x) (at level 70) : bound_scope.
Local Notation "x <=? y" := (leb x y) (at level 70) : bound_scope.
Local Notation "x >? y" := (negb (leb x y)) (at level 70) : bound_scope.
Local Notation "x <? y" := (negb (leb y x)) (at level 70) : bound_scope.
Local Notation "x <=? y <=? z" := (andb (leb x y) (leb y z)) (at level 70, y at next level) : bound_scope.

Definition min x y := if x <=? y then x else y.
Definition max x y := if y <=? x then x else y.

Lemma min_refl : forall x, min x x = x.
Proof.
  unfold min, leb. intros. now destruct (le_dec x x). Qed.
Lemma max_refl : forall x, max x x = x.
Proof.
  unfold max, leb. intros. now destruct (le_dec x x). Qed.

Lemma min_trans : forall x y z,
  y <= x -> min y z <= x.
Proof.
  unfold min, leb. intros. destruct (le_dec y z). assumption.
  apply lt_le_incl in n. apply (le_trans _ _ _ n H). Qed.

Lemma max_trans : forall x y z,
  x <= y -> x <= max y z.
Proof.
  unfold max, leb. intros. destruct (le_dec z y). assumption.
  apply lt_le_incl in n. apply (le_trans _ _ _ H n). Qed.

Lemma min_max_trans : forall w x y z,
  w <= x -> y <= z -> min w y <= max x z.
Proof.
  intros. now apply min_trans, max_trans. Qed.

Record interval := Interval {
  lo: bound;
  hi: bound;
  ordered: le lo hi;
}.

Definition singleton (x : bound) : interval :=
  Interval x x (le_refl _).

Definition is_contiguous (i1 i2 : interval) : bool :=
  max i1.(lo) i2.(lo) <=? succ (min i1.(hi) i2.(hi)).

Definition is_intersection_empty (i1 i2 : interval) : bool :=
  max i1.(lo) i2.(lo) >? min i1.(hi) i2.(hi).

Definition is_subset (i1 i2 : interval) : bool :=
  (i2.(lo) <=? i1.(lo) <=? i2.(hi)) && (i2.(lo) <=? i1.(hi) <=? i2.(hi)).

Definition union (i1 i2 : interval) (H : is_contiguous i1 i2 = true) : interval :=
  Interval (min i1.(lo) i2.(lo))
           (max i1.(hi) i2.(hi))
           (min_max_trans _ _ _ _ i1.(ordered) i2.(ordered)).

Definition interval_set := list interval.
