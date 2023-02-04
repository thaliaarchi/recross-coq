Require Import Bool.
Require Import Ascii String. Open Scope string_scope.
Require Import List. Import ListNotations.
Require Import Program.Equality.

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
Notation "re *" := (Star re) (in custom regexp at level 35, left associativity, format "re *") : regexp_scope.
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

Definition equiv (re re' : regexp) := forall s,
  s =~ re <-> s =~ re'.

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

Lemma MCat_EmptyStr_l : forall re,
  equiv (Cat EmptyStr re) re.
Proof.
  split; intros.
  - invert H. invert H3. assumption.
  - rewrite <- (app_nil_l _). apply MCat. apply MEmptyStr. assumption. Qed.

Lemma MCat_EmptyStr_r : forall re,
  equiv (Cat re EmptyStr) re.
Proof.
  split; intros.
  - invert H. invert H4. now rewrite app_nil_r.
  - rewrite <- (app_nil_r _). now apply MCat, MEmptyStr. Qed.

Theorem Cat_Alt_distr_l : forall re1 re2 re3,
  equiv (Cat re1 (Alt re2 re3)) (Alt (Cat re1 re2) (Cat re1 re3)).
Proof.
  split; intros.
  - invert H; invert H4; [apply MAltL | apply MAltR]; now apply MCat.
  - invert H; invert H2; [apply MCat, MAltL | apply MCat, MAltR]; assumption.
Qed.

Theorem Cat_Alt_distr_r : forall re1 re2 re3,
  equiv (Cat (Alt re1 re2) re3) (Alt (Cat re1 re3) (Cat re2 re3)).
Proof.
  split; intros.
  - invert H; invert H3; [apply MAltL | apply MAltR]; now apply MCat.
  - invert H; invert H2; apply MCat; try assumption; [now apply MAltL | now apply MAltR].
Qed.

Lemma MAlt : forall re1 re2 s,
  s =~ Alt re1 re2 <-> s =~ re1 \/ s =~ re2.
Proof.
  split; intros.
  - invert H; [left | right]; assumption.
  - destruct H; [apply MAltL | apply MAltR]; assumption. Qed.

Theorem Alt_comm : forall re1 re2,
  equiv (Alt re1 re2) (Alt re2 re1).
Proof.
  split; intros;
  (invert H; [apply MAltR | apply MAltL]); assumption. Qed.

Theorem Alt_assoc : forall re1 re2 re3,
  equiv (Alt re1 (Alt re2 re3)) (Alt (Alt re1 re2) re3).
Proof.
  split; intros.
  - invert H. now apply MAltL, MAltL.
    invert H2. now apply MAltL, MAltR. now apply MAltR.
  - invert H. invert H2. now apply MAltL.
    now apply MAltR, MAltL. now apply MAltR, MAltR.
Qed.

Lemma MAlt_EmptySet_l : forall re,
  equiv (Alt EmptySet re) re.
Proof.
  split; intros.
  - invert H. invert H2. assumption.
  - apply MAltR. assumption. Qed.

Lemma MAlt_EmptySet_r : forall re,
  equiv (Alt re EmptySet) re.
Proof.
  split; intros.
  - invert H. assumption. invert H2.
  - apply MAltL. assumption. Qed.

Theorem MStar1 : forall re s,
  s =~ re -> s =~ Star re.
Proof.
  intros. rewrite <- (app_nil_r _). now apply MStarCat, MStar0. Qed.

Theorem Star_idemp : forall re,
  equiv (Star (Star re)) (Star re).
Admitted.

Lemma MStar_EmptySet :
  equiv (Star EmptySet) (EmptyStr).
Proof.
  split; intros.
  - invert H. apply MEmptyStr. invert H1.
  - invert H. apply MStar0. Qed.

Theorem Star_Alt_EmptyStr_l : forall re,
  equiv (Star (Alt EmptyStr re)) (Star re).
Proof.
  split; intros;
  dependent induction H; try apply MStar0.
  - invert H.
    + invert H3. apply IHregexp_match2. reflexivity.
    + apply MStarCat. assumption. apply IHregexp_match2. reflexivity.
  - apply MStarCat.
    + now apply MAltR.
    + apply IHregexp_match2. reflexivity.
Qed.

Theorem Star_Alt_EmptyStr_r : forall re,
  equiv (Star (Alt re EmptyStr)) (Star re).
Proof.
  split; intros;
  dependent induction H; try apply MStar0.
  - invert H.
    + apply MStarCat. assumption. apply IHregexp_match2. reflexivity.
    + invert H3. apply IHregexp_match2. reflexivity.
  - apply MStarCat.
    + now apply MAltL.
    + apply IHregexp_match2. reflexivity.
Qed.

Lemma MClass0 :
  equiv (Class []) (EmptySet).
Proof.
  split; intros; invert H. invert H2. Qed.

Lemma MClass1 : forall c,
  equiv (Class [c]) (Lit c).
Proof.
  split; intros; invert H.
  - invert H2. apply MLit. invert H.
  - apply MClass, in_eq. Qed.

Lemma MClassN : forall c cs,
  equiv (Class (c :: cs)) (Alt (Lit c) (Class cs)).
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

Lemma MCat_empty_set_l : forall re1 re2 s,
  is_empty_str re1 = true ->
  s =~ Cat re1 re2 <-> s =~ re2.
Proof.
  split; intros.
  - invert H0. apply (match_empty_str _ s1 H) in H4. invert H4. assumption.
  - apply (match_empty_str _ []) in H.
    rewrite <- (app_nil_l _). apply MCat.
    + apply H, MEmptyStr.
    + assumption.
Qed.

Lemma MCat_empty_set_r : forall re1 re2 s,
  is_empty_str re2 = true ->
  s =~ Cat re1 re2 <-> s =~ re1.
Proof.
  split; intros.
  - invert H0. apply (match_empty_str _ s2 H) in H5. invert H5.
    rewrite app_nil_r. assumption.
  - apply (match_empty_str _ []) in H.
    rewrite <- (app_nil_r _). apply MCat.
    + assumption.
    + apply H, MEmptyStr.
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
      * destruct (split_first re1) eqn:Hsplit1; try discriminate. destruct p.
        invert H. admit.
    + destruct (split_first re1) eqn:Hsplit1; try discriminate. destruct p.
      destruct (split_first re2) eqn:Hsplit2; try discriminate. destruct p.
      invert H. invert H0.
      * apply IHre1. Admitted.

Fixpoint combine_classes (re : regexp) : regexp.
Admitted.
