Require Import Bool.
Require Import Ascii String. Open Scope string_scope.
Require Import List. Import ListNotations.
Require Import Program.Equality.

Local Ltac invert H := inversion H; subst; clear H.

Inductive regexp :=
  | Void
  | Nil
  | Lit (c : ascii)
  | Class (cs : list ascii)
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
  | String c "" => Lit c
  | String c s' => Cat (Lit c) (regexp_of_string s')
  | "" => Nil
  end.

Coercion Lit : ascii >-> regexp.
Coercion regexp_of_string : string >-> regexp.

Reserved Notation "s =~ re" (at level 80).

Inductive regexp_match : list ascii -> regexp -> Prop :=
  | MNil :
      [] =~ Nil
  | MLit c :
      [c] =~ Lit c
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

Lemma MStar1 : forall re s,
  s =~ re -> s =~ Star re.
Proof.
  intros. rewrite <- (app_nil_r _). now apply MStarCat, MStar0. Qed.

Lemma MAlt : forall re1 re2 s,
  s =~ Alt re1 re2 <-> s =~ re1 \/ s =~ re2.
Proof.
  split; intros.
  - invert H; [left | right]; assumption.
  - destruct H; [apply MAltL | apply MAltR]; assumption. Qed.

Definition equiv (re re' : regexp) := forall s,
  s =~ re <-> s =~ re'.

Lemma equiv_refl : forall re,
  equiv re re.
Proof. now split. Qed.

Lemma equiv_trans : forall re1 re2 re3,
  equiv re1 re2 -> equiv re2 re3 -> equiv re1 re3.
Proof.
  split; intros.
  - apply H0. now apply H.
  - apply H. now apply H0. Qed.

Lemma equiv_assoc : forall re1 re2,
  equiv re1 re2 <-> equiv re2 re1.
Proof.
  split; split; intros; now apply H. Qed.

Lemma Class_subst : forall cs cs',
  (forall c, In c cs <-> In c cs') ->
  equiv (Class cs) (Class cs').
Proof.
  split; intros;
  invert H0; apply H in H3; now apply MClass. Qed.

Lemma Star_subst : forall re re',
  equiv re re' ->
  equiv (Star re) (Star re').
Proof.
  split; intros.
  - dependent induction H0.
    + apply MStar0.
    + apply MStarCat. now apply H. now apply IHregexp_match2 with re.
  - dependent induction H0.
    + apply MStar0.
    + apply MStarCat. now apply H. now apply IHregexp_match2 with re'.
Qed.

Lemma Cat_subst : forall re1 re1' re2 re2',
  equiv re1 re1' ->
  equiv re2 re2' ->
  equiv (Cat re1 re2) (Cat re1' re2').
Proof.
  split; intros;
  invert H1; (apply MCat; [now apply H | now apply H0]). Qed.

Lemma Alt_subst : forall re1 re1' re2 re2',
  equiv re1 re1' ->
  equiv re2 re2' ->
  equiv (Alt re1 re2) (Alt re1' re2').
Proof.
  split; intros;
  (invert H1; [now apply MAltL, H | now apply MAltR, H0]). Qed.

Lemma And_subst : forall re1 re1' re2 re2',
  equiv re1 re1' ->
  equiv re2 re2' ->
  equiv (And re1 re2) (And re1' re2').
Proof.
  split; intros;
  invert H1; (apply MAnd; [now apply H | now apply H0]). Qed.

Lemma op2_subst_l Op
  (Op_subst : forall re1 re1' re2 re2', equiv re1 re1' -> equiv re2 re2' ->
                equiv (Op re1 re2) (Op re1' re2')) :
  forall re1 re1' re2,
    equiv re1 re1' ->
    equiv (Op re1 re2) (Op re1' re2).
Proof.
  split; intros;
  now apply (Op_subst _ _ _ _ H (equiv_refl _)) in H0. Qed.

Lemma op2_subst_r Op
  (Op_subst : forall re1 re1' re2 re2', equiv re1 re1' -> equiv re2 re2' ->
                equiv (Op re1 re2) (Op re1' re2')) :
  forall re1 re2 re2',
    equiv re2 re2' ->
    equiv (Op re1 re2) (Op re1 re2').
Proof.
  split; intros;
  now apply (Op_subst _ _ _ _ (equiv_refl _) H) in H0. Qed.

Definition Cat_subst_l := op2_subst_l Cat Cat_subst.
Definition Cat_subst_r := op2_subst_r Cat Cat_subst.
Definition Alt_subst_l := op2_subst_l Alt Alt_subst.
Definition Alt_subst_r := op2_subst_r Alt Alt_subst.
Definition And_subst_l := op2_subst_l And And_subst.
Definition And_subst_r := op2_subst_r And And_subst.

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
  equiv (Class [c]) (Lit c).
Proof.
  split; intros; invert H.
  - invert H2. apply MLit. invert H.
  - apply MClass, in_eq. Qed.

Lemma Class1_Alt : forall c cs,
  equiv (Class (c :: cs)) (Alt (Lit c) (Class cs)).
Proof.
  split; intros; invert H; invert H2.
  - apply MAltL, MLit.
  - now apply MAltR, MClass.
  - apply MClass, in_eq.
  - now apply MClass, in_cons. Qed.

Lemma ClassN : forall cs,
  equiv (Class cs) (fold_right (fun c => Alt (Lit c)) Void cs).
Proof.
  split; intros;
  induction cs; cbn; try now invert H.
  - invert H. invert H2.
    + apply MAltL, MLit.
    + now apply MAltR, IHcs, MClass.
  - invert H.
    + now apply Class1_Alt, MAltL.
    + now apply Class1_Alt, MAltR, IHcs.
Qed.

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
    + apply MStarCat. now apply MStar1. now apply IHregexp_match2.
Qed.

Lemma Star_Alt_Nil_l : forall re,
  equiv (Star (Alt Nil re)) (Star re).
Proof.
  split; intros;
  dependent induction H; try apply MStar0.
  - invert H.
    + invert H3. now apply IHregexp_match2.
    + apply MStarCat. assumption. apply IHregexp_match2. reflexivity.
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
  split; intros. now invert H. now apply MAltL. Qed.

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
  split; intros. now invert H. now apply MAnd. Qed.

Fixpoint is_void (re : regexp) : bool :=
  match re with
  | Void | Class [] => true
  | Nil | Lit _ | Class _ | Star _ => false
  | Cat re1 re2 => is_void re1 || is_void re2
  | Alt re1 re2 => is_void re1 && is_void re2
  | And re1 re2 => is_void re1 || is_void re2
  end.

Fixpoint is_nil (re : regexp) : bool :=
  match re with
  | Nil => true
  | Void | Lit _ | Class _ => false
  | Star re => is_void re
  | Cat re1 re2 => is_nil re1 && is_nil re2
  | Alt re1 re2 => is_nil re1 && is_nil re2
  | And re1 re2 => is_nil re1 && is_nil re2
  end.

Fixpoint matches_nil (re : regexp) : bool :=
  match re with
  | Void | Lit _ | Class _ => false
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

Fixpoint split_first (re : regexp) : option (list ascii * regexp) :=
  match re with
  | Void => None
  | Nil => None
  | Lit c => Some ([c], Nil)
  | Class cs => Some (cs, Nil)
  | Star re => None
  | Cat re1 re2 =>
      if is_nil re1 then split_first re2 else
      match split_first re1 with
      | Some (cs, re1') => Some (cs, Cat re1' re2)
      | _ => None
      end
  | Alt re1 re2 =>
      match split_first re1, split_first re2 with
      | Some (cs1, re1'), Some (cs2, re2') => Some (cs1 ++ cs2, Alt re1' re2')
      | _, _ => None
      end
  | And re1 re2 => (* TODO *) None
  end.

Fixpoint split_last (re : regexp) : option (list ascii * regexp) :=
  match re with
  | Void => None
  | Nil => None
  | Lit c => Some ([c], Nil)
  | Class cs => Some (cs, Nil)
  | Star re => None
  | Cat re1 re2 =>
      if is_nil re2 then split_last re1 else
      match split_last re2 with
      | Some (cs, re2') => Some (cs, Cat re1 re2')
      | _ => None
      end
  | Alt re1 re2 =>
      match split_last re1, split_last re2 with
      | Some (cs1, re1'), Some (cs2, re2') => Some (cs1 ++ cs2, Alt re1' re2')
      | _, _ => None
      end
  | And re1 re2 => (* TODO *) None
  end.

Lemma split_first_not_nil : forall re cs re',
  split_first re = Some (cs, re') ->
  matches_nil re = false.
Proof.
  induction re; cbn; intros; try discriminate; try reflexivity.
  - apply andb_false_iff. destruct (is_nil re1).
    + right. eapply IHre2, H.
    + destruct (split_first re1).
      * destruct p. left. now eapply IHre1.
      * discriminate.
  - apply orb_false_iff. destruct (split_first re1).
    + destruct p. destruct (split_first re2) eqn:Hs2.
      * destruct p. split. now eapply IHre1. now eapply IHre2.
      * discriminate.
    + discriminate.
Qed.

Lemma cat_split_first : forall re cs re',
  split_first re = Some (cs, re') ->
  equiv re (Cat (Class cs) re').
Proof.
  split; intros.
  - dependent induction H0; cbn in *; try discriminate.
    + invert H. apply Cat_Nil_r, Class1, MLit.
    + invert H. now apply Cat_Nil_r, MClass.
    + destruct (is_nil re1) eqn:Hnil.
      * destruct s1.
        -- now apply IHregexp_match2.
        -- apply (match_nil _ Hnil) in H0_. invert H0_.
      * destruct (split_first re1) eqn:Hsplit1; try discriminate. destruct p.
        invert H. destruct s1.
        -- apply split_first_not_nil, matches_nil_false in Hsplit1.
           destruct (Hsplit1 H0_).
        -- replace ((a :: s1) ++ s2) with ([a] ++ s1 ++ s2) by reflexivity.
           apply MCat. apply MClass. admit. admit.
    + destruct (split_first re1) eqn:Hsplit1; try discriminate. destruct p.
      destruct (split_first re2) eqn:Hsplit2; try discriminate. destruct p.
      invert H. admit.
    + destruct (split_first re1) eqn:Hsplit1; try discriminate. destruct p.
      destruct (split_first re2) eqn:Hsplit2; try discriminate. destruct p.
      invert H. apply IHregexp_match. admit.
  - admit.
Admitted.

Reserved Notation "re -->n re'" (at level 40).
Reserved Notation "re -->*n re'" (at level 40).

Inductive normalize_step : regexp -> regexp -> Prop :=
  | NVoid :                                  Void                      -->n Void

  | NNil :                                   Nil                       -->n Nil

  | NLit c :                                 Lit c                     -->n Lit c

  | NClass0 :                                Class []                  -->n Void
  | NClassN cs :                 cs <> [] -> Class cs                  -->n Class cs

  | NStarVoid :                              Star Void                 -->n Nil
  | NStarNil :                               Star Nil                  -->n Nil
  | NStarStar re :                           Star (Star re)            -->n Star re

  | NCatVoidL re :                           Cat Void re               -->n Void
  | NCatVoidR re :                           Cat re Void               -->n Void
  | NCatNilL re :                            Cat Nil re                -->n re
  | NCatNilR re :                            Cat re Nil                -->n re
  | NCatStarEquiv re1 re2 : equiv re1 re2 -> Cat (Star re1) (Star re2) -->n Star re1

  | NAltEquiv re1 re2 :     equiv re1 re2 -> Alt re1 re2               -->n re1
  | NAltVoidL re :                           Alt Void re               -->n re
  | NAltVoidR re :                           Alt re Void               -->n re
  | NAltNilR re :                            Alt re Nil                -->n Alt Nil re
  | NAltNilStar re :                         Alt Nil (Star re)         -->n Star re
  | NAltAltNil re1 re2 :                     Alt (Alt Nil re1) re2     -->n Alt Nil (Alt re1 re2)

  | NAndEquiv re1 re2 :     equiv re1 re2 -> And re1 re2               -->n re1
  | NAndVoidL re :                           And Void re               -->n Void
  | NAndVoidR re :                           And re Void               -->n Void

  where "re -->n re'" := (normalize_step re re').

Inductive normalize : regexp -> regexp -> Prop :=
  | normalize_refl re :
      re -->*n re
  | normalize_trans re1 re2 re3 :
      re1 -->n re2 ->
      re2 -->*n re3 ->
      re1 -->*n re3
  where "re -->*n re'" := (normalize re re').

Fixpoint is_normalized (re : regexp) : bool :=
  match re with
  | Void | Nil | Lit _ => true
  | Class [] => false
  | Class _ => true
  | Star (Void | Nil | Star _) => false
  (* | Star (Alt Nil _ | Alt _ Nil) => false *)
  | Star re => is_normalized re
  | Cat (Void | Nil) _ | Cat _ (Void | Nil) => false
  | Cat re1 re2 => is_normalized re1 || is_normalized re2
  | Alt Void _ | Alt _ Void
  | Alt Nil (Nil | Star _) | Alt (Star _) Nil => false
  (* | Alt Nil re | Alt re Nil => negb (matches_nil re) && is_normalized re *)
  | Alt (Lit _ | Class _) (Lit _ | Class _) => false
  | Alt re1 re2 => is_normalized re1 && is_normalized re2
  | And Void _ | And _ Void => false
  | And re1 re2 => is_normalized re1 && is_normalized re2
  end.

Definition Class_norm (cs : list ascii) : regexp :=
  match cs with
  | [] => Void
  | _ => Class cs
  end.

Definition Star_norm (re : regexp) (Hnorm : is_normalized re = true) : regexp :=
  match re with
  | Void | Nil => Nil
  | Star re => Star re
  (* | Alt Nil re | Alt re Nil => Star re *)
  | _ => Star re
  end.

Definition Cat_norm (re1 re2 : regexp) (Hnorm1 : is_normalized re1 = true)
                                       (Hnorm2 : is_normalized re2 = true) : regexp :=
  match re1, re2 with
  | Void, _ | _, Void => Void
  | Nil, re | re, Nil => re
  | _, _ => Cat re1 re2
  end.

Definition Alt_norm (re1 re2 : regexp) (Hnorm1 : is_normalized re1 = true)
                                       (Hnorm2 : is_normalized re2 = true) : regexp :=
  match re1, re2 with
  | Void, re | re, Void => re
  | Nil, Nil => Nil
  | Nil, Star re | Star re, Nil => Star re
  (* | Nil, re | re, Nil => if matches_nil re then re else Alt Nil re *)
  | Lit c1, Lit c2 => Class [c1; c2]
  | Lit c1, Class cs2 => Class (c1 :: cs2)
  | Class cs1, Lit c2 => Class (cs1 ++ [c2])
  | Class cs1, Class cs2 => Class (cs1 ++ cs2)
  | _, _ => Alt re1 re2
  end.

Definition And_norm (re1 re2 : regexp) (Hnorm1 : is_normalized re1 = true)
                                       (Hnorm2 : is_normalized re2 = true) : regexp :=
  match re1, re2 with
  | Void, _ | _, Void => Void
  | _, _ => And re1 re2
  end.

Lemma Class_norm_is_normalized : forall cs,
  is_normalized (Class_norm cs) = true.
Proof. now destruct cs. Qed.

Lemma Star_norm_is_normalized : forall re
  (Hnorm : is_normalized re = true),
  is_normalized (Star_norm re Hnorm) = true.
Proof. now destruct re. Qed.

Lemma Cat_norm_is_normalized : forall re1 re2
  (Hnorm1 : is_normalized re1 = true)
  (Hnorm2 : is_normalized re2 = true),
  is_normalized (Cat_norm re1 re2 Hnorm1 Hnorm2) = true.
Proof.
  intros. destruct re1, re2;
  try destruct cs; try (cbn in *; rewrite Hnorm1); intuition.
Qed.

Lemma Alt_norm_is_normalized : forall re1 re2
  (Hnorm1 : is_normalized re1 = true)
  (Hnorm2 : is_normalized re2 = true),
  is_normalized (Alt_norm re1 re2 Hnorm1 Hnorm2) = true.
Proof.
  intros. destruct re1, re2;
  try destruct cs; try (cbn in *; rewrite Hnorm1); intuition.
Qed.

Lemma And_norm_is_normalized : forall re1 re2
  (Hnorm1 : is_normalized re1 = true)
  (Hnorm2 : is_normalized re2 = true),
  is_normalized (And_norm re1 re2 Hnorm1 Hnorm2) = true.
Proof.
  intros. destruct re1, re2;
  try destruct cs; try (cbn in *; rewrite Hnorm1); intuition.
Qed.
