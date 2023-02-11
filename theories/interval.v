Parameter bound : Type.

(* Saturating *)
Parameter succ : bound -> bound.
Parameter pred : bound -> bound.

Parameter le : bound -> bound -> Prop.
Parameter le_dec : forall x y, {le x y} + {~ le x y}.
Parameter le_refl : forall x, le x x.
Parameter le_trans : forall x y z, le x y -> le y z -> le x z.
Parameter lt_le_incl : forall x y, ~ le y x -> le x y.
Parameter lt_le_succ : forall x y, ~ le y x -> le (succ x) y.
Parameter lt_le_pred : forall x y, ~ le y x -> le x (pred y).

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

Definition lt_dec : forall x y, {x < y} + {y <= x}.
Proof. intros. destruct (le_dec y x). now right. now left. Defined.

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

Definition union (i1 i2 : interval) : option interval :=
  if is_contiguous i1 i2 then
    Some (Interval (min i1.(lo) i2.(lo))
                   (max i1.(hi) i2.(hi))
                   (min_max_trans _ _ _ _ i1.(ordered) i2.(ordered))) else None.

Definition intersect (i1 i2 : interval) : option interval :=
  let lo3 := max i1.(lo) i2.(lo) in
  let hi3 := min i1.(hi) i2.(hi) in
  match le_dec lo3 hi3 with
  | left pf => Some (Interval lo3 hi3 pf)
  | right _ => None
  end.

Lemma intersect_not_empty : forall i1 i2,
  (exists i3, intersect i1 i2 = Some i3) <-> is_intersection_empty i1 i2 = false.
Proof.
  unfold intersect, is_intersection_empty, leb. intros [] []. cbn.
  split.
  - intros [[]]. now destruct (le_dec (max lo0 lo1) (min hi0 hi1)).
  - intros. destruct (le_dec (max lo0 lo1) (min hi0 hi1)).
    now eexists. discriminate. Qed.

Lemma intersect_is_empty : forall i1 i2,
  intersect i1 i2 = None <-> is_intersection_empty i1 i2 = true.
Proof.
  unfold intersect, is_intersection_empty, leb. intros [] []. cbn.
  now destruct (le_dec (max lo0 lo1) (min hi0 hi1)). Qed.

Definition difference (i1 i2 : interval) : option interval * option interval :=
  match lt_dec i1.(lo) i2.(lo), lt_dec i2.(hi) i1.(hi) with
  | left pflo, left pfhi =>
      (Some (Interval i1.(lo) (pred i2.(lo)) (lt_le_pred _ _ pflo)),
       Some (Interval (succ i2.(hi)) i1.(hi) (lt_le_succ _ _ pfhi)))
  | left pflo, right _ =>
      (Some (Interval i1.(lo) (pred i2.(lo)) (lt_le_pred _ _ pflo)), None)
  | right _, left pfhi =>
      (None, Some (Interval (succ i2.(hi)) i1.(hi) (lt_le_succ _ _ pfhi)))
  | right _, right _ => (None, None) (* i1 is a subset of i2 *)
  end.

Lemma subset_difference_is_empty : forall i1 i2,
  is_subset i1 i2 = true <-> difference i1 i2 = (None, None).
Admitted.

Definition interval_set := list interval.
