Require Import Bool.
Require Import Ascii String. Open Scope string_scope.
Require Import List. Import ListNotations.

Local Ltac invert H := inversion H; subst; clear H.

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
  | MEmptyStr :
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
  | MClass c cs :
      In c cs ->
      [c] =~ Class cs

  where "s =~ re" := (regexp_match s re).

Lemma MEmptySet_not : forall s,
  ~ (s =~ EmptySet).
Proof.
  unfold not. intros. inversion H. Qed.

Lemma MEmptyStr_nil : forall s,
  s =~ EmptyStr <-> s = [].
Proof.
  split; intros.
  - invert H. reflexivity.
  - subst. apply MEmptyStr. Qed.

Lemma MCat_EmptySet_l : forall re s,
  ~ (s =~ Cat EmptySet re).
Proof.
  unfold not. intros. invert H. invert H3. Qed.

Lemma MCat_EmptySet_r : forall re s,
  ~ (s =~ Cat re EmptySet).
Proof.
  unfold not. intros. invert H. invert H4. Qed.

Lemma MCat_EmptyStr_l : forall re s,
  s =~ Cat EmptyStr re <-> s =~ re.
Proof.
  split; intros.
  - invert H. invert H3. assumption.
  - rewrite <- (app_nil_l _). apply MCat. apply MEmptyStr. assumption. Qed.

Lemma MCat_EmptyStr_r : forall re s,
  s =~ Cat re EmptyStr <-> s =~ re.
Proof.
  split; intros.
  - invert H. invert H4. rewrite app_nil_r. assumption.
  - rewrite <- (app_nil_r _). apply MCat. assumption. apply MEmptyStr. Qed.

Lemma MAlt : forall s re1 re2,
  s =~ Alt re1 re2 <-> s =~ re1 \/ s =~ re2.
Proof.
  split; intros.
  - invert H; [left | right]; assumption.
  - destruct H; [apply MAltL | apply MAltR]; assumption. Qed.

Lemma MAlt_EmptySet_l : forall re s,
  s =~ Alt EmptySet re <-> s =~ re.
Proof.
  split; intros.
  - invert H. invert H2. assumption.
  - apply MAltR. assumption. Qed.

Lemma MAlt_EmptySet_r : forall re s,
  s =~ Alt re EmptySet <-> s =~ re.
Proof.
  split; intros.
  - invert H. assumption. invert H2.
  - apply MAltL. assumption. Qed.

Lemma MStar1 : forall s re,
  s =~ re -> s =~ Star re.
Proof.
  intros. rewrite <- (app_nil_r _). apply MStarCat, MStar0. assumption. Qed.

Lemma MStar_EmptySet : forall s,
  s =~ Star EmptySet <-> s =~ EmptyStr.
Proof.
  split; intros.
  - invert H. apply MEmptyStr. invert H1.
  - invert H. apply MStar0. Qed.

Lemma MClass0 : forall s,
  s =~ Class [] <-> s =~ EmptySet.
Proof.
  split; intros; invert H. invert H2. Qed.

Lemma MClass1 : forall c s,
  s =~ Class [c] <-> s =~ Lit c.
Proof.
  split; intros; invert H.
  - invert H2. apply MLit. invert H.
  - apply MClass, in_eq. Qed.

Lemma MClassN : forall c cs s,
  s =~ Class (c :: cs) <-> s =~ Alt (Lit c) (Class cs).
Proof.
  split; intros;
  invert H; invert H2.
  - apply MAltL, MLit.
  - apply MAltR, MClass. assumption.
  - apply MClass, in_eq.
  - apply MClass, in_cons. assumption. Qed.

Fixpoint is_empty_set (re : regexp) : bool :=
  match re with
  | EmptySet => true
  | EmptyStr => false
  | Lit _ => false
  | Cat re1 re2 => is_empty_set re1 || is_empty_set re2
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
  | Star re => is_empty_set re
  | Class _ => false
  end.

Theorem match_empty_set : forall re s,
  is_empty_set re = true ->
  s =~ re <-> s =~ EmptySet.
Proof.
  split; generalize dependent s.
  - induction re; cbn in *; intros; try discriminate.
    + assumption.
    + invert H0.
      apply orb_true_iff in H as [].
      * apply (IHre1 H _) in H4. invert H4.
      * apply (IHre2 H _) in H5. invert H5.
    + apply andb_true_iff in H as [H1 H2].
      invert H0.
      * apply (IHre1 H1 _) in H4. invert H4.
      * apply (IHre2 H2 _) in H4. invert H4.
    + destruct cs.
      * invert H0. destruct (in_nil H3).
      * discriminate.
  - intros. invert H0.
Qed.

Theorem match_empty_str : forall re s,
  is_empty_str re = true ->
  s =~ re <-> s =~ EmptyStr.
Proof.
  split; generalize dependent s.
  - induction re; cbn in *; intros; try discriminate.
    + assumption.
    + apply andb_true_iff in H as [H1 H2].
      invert H0.
      apply (IHre1 H1 _) in H5. invert H5.
      apply (IHre2 H2 _) in H6. invert H6.
      apply MEmptyStr.
    + apply andb_true_iff in H as [H1 H2].
      invert H0; [apply (IHre1 H1 _ H4) | apply (IHre2 H2 _ H4)].
    + invert H0.
      * apply MEmptyStr.
      * apply (match_empty_set _ s1 H) in H2. invert H2.
  - induction re; cbn in *; intros; try discriminate;
    invert H0.
    + apply MEmptyStr.
    + apply andb_true_iff in H as [H1 H2].
      rewrite <- (app_nil_r _).
      apply MCat; [apply (IHre1 H1 _) | apply (IHre2 H2 _)]; apply MEmptyStr.
    + apply andb_true_iff in H as [H1 H2].
      apply MAltL, (IHre1 H1 _), MEmptyStr.
    + apply MStar0.
Qed.

Fixpoint split_first (re : regexp) : option (list ascii * regexp) :=
  match re with
  | EmptySet => None
  | EmptyStr => None
  | Lit c => Some ([c], EmptyStr)
  | Cat re1 re2 =>
      if is_empty_str re1 then split_first re2 else
      match split_first re1 with
      | Some (cs, re1') => Some (cs, Cat re1' re2)
      | _ => None
      end
  | Alt re1 re2 =>
      match split_first re1, split_first re2 with
      | Some (cs1, re1'), Some (cs2, re2') => Some (cs1 ++ cs2, Alt re1' re2')
      | _, _ => None
      end
  | Star re => None
  | Class cs => Some (cs, EmptyStr)
  end.

Fixpoint split_last (re : regexp) : option (list ascii * regexp) :=
  match re with
  | EmptySet => None
  | EmptyStr => None
  | Lit c => Some ([c], EmptyStr)
  | Cat re1 re2 =>
      if is_empty_str re2 then split_last re1 else
      match split_last re2 with
      | Some (cs, re2') => Some (cs, Cat re1 re2')
      | _ => None
      end
  | Alt re1 re2 =>
      match split_last re1, split_last re2 with
      | Some (cs1, re1'), Some (cs2, re2') => Some (cs1 ++ cs2, Alt re1' re2')
      | _, _ => None
      end
  | Star re => None
  | Class cs => Some (cs, EmptyStr)
  end.

Lemma cat_split_first : forall re cs re' s,
  split_first re = Some (cs, re') ->
  s =~ re <-> s =~ Cat (Class cs) re'.
Proof.
  split;
  generalize dependent s; generalize dependent re'; generalize dependent cs.
  - induction re; cbn; intros; try discriminate.
    + invert H. apply MCat_EmptyStr_r, MClass1. assumption.
    + destruct (is_empty_str re1) eqn:Hempty.
      * apply IHre2. assumption.
        invert H0.
        apply (match_empty_str _ s1 Hempty) in H4. invert H4.
        assumption.
      * destruct (split_first re1) eqn:Hsplit; try discriminate.
        destruct p. invert H. admit.
    + destruct (split_first re1) eqn:Hsplit; try discriminate.
      invert H0.
      * Admitted.

Fixpoint combine_classes (re : regexp) : regexp.
Admitted.
