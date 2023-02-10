Require Import Setoid.
From recross Require Import util.

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

Fixpoint regexp_of_string (s : string) : regexp :=
  match s with
  | String c "" => Char c
  | String c s' => Cat (Char c) (regexp_of_string s')
  | "" => Nil
  end.

Reserved Notation "s =~ re" (at level 80).

Inductive re_match : list ascii -> regexp -> Prop :=
  | MNil :
      [] =~ Nil
  | MChar c :
      [c] =~ Char c
  | MClass c cs :
      In c cs ->
      [c] =~ Class cs
  | MStar0 re :
      [] =~ Star re
  | MStarApp s1 s2 re :
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

  where "s =~ re" := (re_match s re).

Definition re_equiv (re re' : regexp) := forall s,
  s =~ re <-> s =~ re'.

Infix "<=>" := re_equiv (at level 90, right associativity).

Lemma re_equiv_refl : forall re, re <=> re.
Proof. now split. Qed.

Lemma re_equiv_sym : forall re1 re2,
  re1 <=> re2 -> re2 <=> re1.
Proof.
  split; intros; now apply H. Qed.

Lemma re_equiv_trans : forall re1 re2 re3,
  re1 <=> re2 -> re2 <=> re3 -> re1 <=> re3.
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

Add Relation regexp re_equiv
  reflexivity proved by re_equiv_refl
  symmetry proved by re_equiv_sym
  transitivity proved by re_equiv_trans
  as re_equiv_rel.

Add Relation char_set cs_equiv
  reflexivity proved by cs_equiv_refl
  symmetry proved by cs_equiv_sym
  transitivity proved by cs_equiv_trans
  as cs_equiv_rel.

Add Morphism Class
  with signature cs_equiv ==> re_equiv as Class_compat.
Proof.
  split; intros;
  invert H0; apply H in H3; now apply MClass. Qed.

Add Morphism Star
  with signature re_equiv ==> re_equiv as Star_compat.
Proof.
  split; intros.
  - dependent induction H0.
    + apply MStar0.
    + apply MStarApp. now apply H. now apply IHre_match2 with x.
  - dependent induction H0.
    + apply MStar0.
    + apply MStarApp. now apply H. now apply IHre_match2 with y.
Qed.

Add Morphism Cat
  with signature re_equiv ==> re_equiv ==> re_equiv as Cat_compat.
Proof.
  split; intros;
  invert H1; (apply MCat; [now apply H | now apply H0]). Qed.

Add Morphism Alt
  with signature re_equiv ==> re_equiv ==> re_equiv as Alt_compat.
Proof.
  split; intros;
  (invert H1; [now apply MAltL, H | now apply MAltR, H0]). Qed.

Add Morphism And
  with signature re_equiv ==> re_equiv ==> re_equiv as And_compat.
Proof.
  split; intros;
  invert H1; (apply MAnd; [now apply H | now apply H0]). Qed.

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

Fixpoint re_chars (re : regexp) : list ascii :=
  match re with
  | Nil => []
  | Void => []
  | Char c => [c]
  | Class cs => cs
  | Star re => re_chars re
  | Cat re1 re2 => re_chars re1 ++ re_chars re2
  | Alt re1 re2 => re_chars re1 ++ re_chars re2
  | And re1 re2 => re_chars re1 ++ re_chars re2
  end.
