Require Import Bool.
From recross Require Import util regexp.

Theorem chars_in_re : forall re c s,
  s =~ re ->
  In c s ->
  In c (re_chars re).
Proof.
  intros. induction H; cbn in *.
  - destruct H0.
  - apply H0.
  - destruct H0 as [| []]. now subst.
  - destruct H0.
  - apply in_app_iff in H0 as [].
    + now apply IHre_match1.
    + now apply IHre_match2.
  - apply in_app_iff. apply in_app_iff in H0 as [].
    + left. now apply IHre_match1.
    + right. now apply IHre_match2.
  - apply in_app_iff. left. now apply IHre_match.
  - apply in_app_iff. right. now apply IHre_match.
  - apply in_app_iff. left. now apply IHre_match1.
Qed.

Theorem is_void_true : forall re,
  is_void re = true -> re <=> Void.
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

(* Not iff, because of And *)
Theorem is_void_false : forall re,
  (exists s, s =~ re) -> is_void re = false.
Proof.
  induction re; cbn; intros [s]; try reflexivity.
  - invert H.
  - invert H. destruct cs.
    + invert H2.
    + reflexivity.
  - invert H. apply orb_false_iff. split.
    + apply IHre1. now exists s1.
    + apply IHre2. now exists s2.
  - apply andb_false_iff. invert H.
    + left. apply IHre1. now exists s.
    + right. apply IHre2. now exists s.
  - invert H. apply orb_false_iff. split.
    + apply IHre1. now exists s.
    + apply IHre2. now exists s.
Qed.

Theorem is_nil_true : forall re,
  is_nil re = true -> re <=> Nil.
Proof.
  split; generalize dependent s.
  - induction re; cbn in *; intros; try intuition.
    + invert H0.
      * apply MNil.
      * apply (is_void_true _ H) in H2. invert H2.
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
  matches_nil re = false -> ~ ([] =~ re).
Proof.
  unfold not.
  induction re; cbn; intros; try discriminate;
  invert H0; try (apply app_eq_nil in H1 as []; subst);
  try apply andb_false_iff in H as [];
  try apply orb_false_iff in H as [];
  try (now apply IHre1); try (now apply IHre2).
Qed.

Lemma Void_not : forall s,
  ~ (s =~ Void).
Proof.
  unfold not. intros. inversion H. Qed.

Lemma Nil_nil : forall s,
  s =~ Nil <-> s = [].
Proof.
  split; intros. now invert H. subst. apply MNil. Qed.

Lemma Class0 : Class [] <=> Void.
Proof.
  split; intros; now invert H. Qed.

Lemma Class1 : forall c,
  Class [c] <=> Char c.
Proof.
  split; intros; invert H.
  - invert H2. apply MChar. invert H.
  - apply MClass, in_eq. Qed.

Lemma Class1_Alt : forall c cs,
  Class (c :: cs) <=> Alt (Char c) (Class cs).
Proof.
  split; intros; invert H; invert H2.
  - apply MAltL, MChar.
  - now apply MAltR, MClass.
  - apply MClass, in_eq.
  - now apply MClass, in_cons. Qed.

Lemma ClassN : forall cs,
  Class cs <=> fold_right (fun c => Alt (Char c)) Void cs.
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
  intros. rewrite <- (app_nil_r _). now apply MStarApp, MStar0. Qed.

Lemma Star_Void : Star Void <=> Nil.
Proof.
  split; intros.
  - invert H. apply MNil. invert H1.
  - invert H. apply MStar0. Qed.

Lemma Star_Nil : Star Nil <=> Nil.
Proof.
  split; intros.
  - dependent induction H.
    + apply MNil.
    + invert H. now apply IHre_match2.
  - invert H. apply MStar0.
Qed.

Lemma Star_app : forall re s1 s2,
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros. dependent induction H; intros.
  - assumption.
  - rewrite <- app_assoc. now apply MStarApp, IHre_match2.
Qed.

Lemma Star_concat : forall re ss,
  (forall s, In s ss -> s =~ re) ->
  concat ss =~ Star re.
Proof.
  intros. induction ss.
  - apply MStar0.
  - cbn. apply MStarApp.
    + apply H. now left.
    + apply IHss. intros. apply H. now right.
Qed.

Lemma Star_split : forall re s,
  s =~ Star re ->
  exists ss,
    s = concat ss /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros. dependent induction H.
  - exists []. split.
    + reflexivity.
    + intros. invert H.
  - assert (Star re = Star re) by reflexivity.
    apply IHre_match2 in H1 as [ss []]. subst.
    exists (s1 :: ss). split. reflexivity.
    intros. invert H1.
    + assumption.
    + apply H2, H3.
Qed.

Lemma Star_idemp : forall re,
  Star (Star re) <=> Star re.
Proof.
  split; intros.
  - dependent induction H.
    + apply MStar0.
    + now apply Star_app, IHre_match2.
  - dependent induction H.
    + apply MStar0.
    + apply MStarApp. now apply Star1. now apply IHre_match2.
Qed.

Lemma Star_Alt_Nil_l : forall re,
  Star (Alt Nil re) <=> Star re.
Proof.
  split; intros;
  dependent induction H; try apply MStar0.
  - invert H.
    + invert H3. now apply IHre_match2.
    + now apply MStarApp, IHre_match2.
  - apply MStarApp.
    + now apply MAltR.
    + now apply IHre_match2.
Qed.

Lemma Star_Alt_Nil_r : forall re,
  Star (Alt re Nil) <=> Star re.
Proof.
  split; intros;
  dependent induction H; try apply MStar0.
  - invert H.
    + now apply MStarApp, IHre_match2.
    + invert H3. now apply IHre_match2.
  - apply MStarApp.
    + now apply MAltL.
    + now apply IHre_match2.
Qed.

Lemma Cat_Void_l : forall re,
  Cat Void re <=> Void.
Proof.
  split; intros; invert H. invert H3. Qed.

Lemma Cat_Void_r : forall re,
  Cat re Void <=> Void.
Proof.
  split; intros; invert H. invert H4. Qed.

Lemma Cat_Nil_l : forall re,
  Cat Nil re <=> re.
Proof.
  split; intros.
  - invert H. now invert H3.
  - rewrite <- (app_nil_l _). apply MCat. apply MNil. assumption. Qed.

Lemma Cat_Nil_r : forall re,
  Cat re Nil <=> re.
Proof.
  split; intros.
  - invert H. invert H4. now rewrite app_nil_r.
  - rewrite <- (app_nil_r _). now apply MCat, MNil. Qed.

Lemma Cat_Char_l : forall re c s,
  c :: s =~ Cat (Char c) re <-> s =~ re.
Proof.
  split; intros.
  - invert H. invert H3. now invert H0.
  - replace (c :: s) with ([c] ++ s) by reflexivity.
    apply MCat. apply MChar. assumption. Qed.

Lemma Cat_Char_r : forall re c s,
  s ++ [c] =~ Cat re (Char c) <-> s =~ re.
Proof.
  split; intros.
  - invert H. invert H4. apply app_inv_tail_iff in H0. now subst.
  - now apply MCat, MChar. Qed.

Lemma Cat_Class_l : forall re c cs s,
  In c cs ->
  c :: s =~ Cat (Class cs) re <-> s =~ re.
Proof.
  split; intros.
  - invert H0. invert H4. now invert H1.
  - replace (c :: s) with ([c] ++ s) by reflexivity.
    apply MCat. now apply MClass. assumption. Qed.

Lemma Cat_Class_r : forall re c cs s,
  In c cs ->
  s ++ [c] =~ Cat re (Class cs) <-> s =~ re.
Proof.
  split; intros.
  - invert H0. invert H5. apply app_inj_tail_iff in H1 as []. now subst.
  - now apply MCat, MClass. Qed.

Lemma Cat_Star : forall re,
  Cat (Star re) (Star re) <=> Star re.
Proof.
  split; intros.
  - invert H. now apply Star_app.
  - rewrite <- (app_nil_r _). now apply MCat, MStar0. Qed.

Lemma Cat_Alt_distr_l : forall re1 re2 re3,
  Cat re1 (Alt re2 re3) <=> Alt (Cat re1 re2) (Cat re1 re3).
Proof.
  split; intros.
  - invert H; invert H4. now apply MAltL, MCat. now apply MAltR, MCat.
  - invert H; invert H2. now apply MCat, MAltL. now apply MCat, MAltR.
Qed.

Lemma Cat_Alt_distr_r : forall re1 re2 re3,
  Cat (Alt re1 re2) re3 <=> Alt (Cat re1 re3) (Cat re2 re3).
Proof.
  split; intros.
  - invert H; invert H3. now apply MAltL, MCat. now apply MAltR, MCat.
  - invert H; invert H2; apply MCat; try assumption.
    now apply MAltL. now apply MAltR.
Qed.

Lemma Cat_And_distr_l : forall re1 re2 re3 s,
  s =~ Cat re1 (And re2 re3) -> s =~ And (Cat re1 re2) (Cat re1 re3).
Proof.
  intros. invert H. invert H4. apply MAnd; now apply MCat. Qed.

Lemma Cat_And_distr_r : forall re1 re2 re3 s,
  s =~ Cat (And re1 re2) re3 -> s =~ And (Cat re1 re3) (Cat re2 re3).
Proof.
  intros. invert H. invert H3. apply MAnd; now apply MCat. Qed.

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
  Alt re1 re2 <=> Alt re2 re1.
Proof.
  split; intros; (invert H; [now apply MAltR | now apply MAltL]). Qed.

Lemma Alt_assoc : forall re1 re2 re3,
  Alt re1 (Alt re2 re3) <=> Alt (Alt re1 re2) re3.
Proof.
  split; intros.
  - invert H. now apply MAltL, MAltL.
    invert H2. now apply MAltL, MAltR. now apply MAltR.
  - invert H. invert H2. now apply MAltL.
    now apply MAltR, MAltL. now apply MAltR, MAltR.
Qed.

Lemma Alt_Void_l : forall re,
  Alt Void re <=> re.
Proof.
  split; intros. now invert H. now apply MAltR. Qed.

Lemma Alt_Void_r : forall re,
  Alt re Void <=> re.
Proof.
  intros. now rewrite Alt_comm, Alt_Void_l. Qed.

Lemma Alt_Nil_l : forall re,
  matches_nil re = true -> Alt Nil re <=> re.
Proof.
  split; intros.
  - invert H0. invert H3. now apply matches_nil_true. assumption.
  - now apply MAltR. Qed.

Lemma Alt_Nil_r : forall re,
  matches_nil re = true -> Alt re Nil <=> re.
Proof.
  intros. now rewrite Alt_comm, Alt_Nil_l. Qed.

Lemma Alt_Class : forall cs1 cs2,
  Alt (Class cs1) (Class cs2) <=> Class (cs1 ++ cs2).
Proof.
  split; intros.
  - invert H; invert H2;
    apply MClass; apply in_app_iff; [now left | now right].
  - invert H; apply in_app_iff in H2 as [];
    [apply MAltL | apply MAltR]; now apply MClass.
Qed.

Lemma And_comm : forall re1 re2,
  And re1 re2 <=> And re2 re1.
Proof.
  split; intros; invert H; now apply MAnd. Qed.

Lemma And_assoc : forall re1 re2 re3,
  And re1 (And re2 re3) <=> And (And re1 re2) re3.
Proof.
  split; intros.
  - invert H. invert H4. repeat apply MAnd; assumption.
  - invert H. invert H3. repeat apply MAnd; assumption. Qed.

Lemma And_Void_l : forall re,
  And Void re <=> Void.
Proof.
  split; intros. now invert H. now apply MAnd. Qed.

Lemma And_Void_r : forall re,
  And re Void <=> Void.
Proof.
  intros. now rewrite And_comm, And_Void_l. Qed.

Lemma And_Nil_true_l : forall re,
  matches_nil re = true -> And Nil re <=> Nil.
Proof.
  split; intros.
  - invert H0. invert H4. apply MNil.
  - invert H0. apply MAnd. apply MNil. now apply matches_nil_true in H. Qed.

Lemma And_Nil_true_r : forall re,
  matches_nil re = true -> And re Nil <=> Nil.
Proof.
  intros. now rewrite And_comm, And_Nil_true_l. Qed.

Lemma And_Nil_false_l : forall re,
  matches_nil re = false -> And Nil re <=> Void.
Proof.
  split; intros.
  - invert H0. invert H4. exfalso. now apply (matches_nil_false _ H).
  - invert H0. Qed.

Lemma And_Nil_false_r : forall re,
  matches_nil re = false -> And re Nil <=> Void.
Proof.
  intros. now rewrite And_comm, And_Nil_false_l. Qed.

Lemma And_Alt_distr_l : forall re1 re2 re3,
  And re1 (Alt re2 re3) <=> Alt (And re1 re2) (And re1 re3).
Proof.
  split; intros.
  - invert H. invert H4. now apply MAltL, MAnd. now apply MAltR, MAnd.
  - invert H; invert H2. now apply MAnd, MAltL. now apply MAnd, MAltR.
Qed.

Lemma And_Alt_distr_r : forall re1 re2 re3,
  And (Alt re1 re2) re3 <=> Alt (And re1 re3) (And re2 re3).
Proof.
  split; intros.
  - invert H. invert H3. now apply MAltL, MAnd. now apply MAltR, MAnd.
  - invert H; invert H2; apply MAnd; try assumption.
    now apply MAltL. now apply MAltR.
Qed.

Lemma str_matches_regexp_of_str : forall s s',
  s' =~ regexp_of_string s <-> s' = list_ascii_of_string s.
Proof.
  split; generalize dependent s'.
  - induction s; intros.
    + now invert H.
    + destruct s.
      * now invert H.
      * invert H. invert H3. cbn. f_equal. now apply IHs.
  - induction s; intros; subst.
    + apply MNil.
    + destruct s.
      * apply MChar.
      * cbn. now apply Cat_Char_l, IHs.
Qed.
