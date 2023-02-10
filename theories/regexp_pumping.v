Require Import Arith.
From recross Require Import util regexp.

Fixpoint pumping_constant (re : regexp) : nat :=
  match re with
  | Void | Nil | Class [] => 1
  | Char _ | Class _ => 2
  | Star re => pumping_constant re
  | Cat re1 re2 | Alt re1 re2 | And re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  end.

Lemma pumping_constant_ge_1 : forall re,
  pumping_constant re >= 1.
Proof.
  induction re; cbn; try destruct cs; intuition. Qed.

Lemma pumping_constant_ne_0 : forall re,
  pumping_constant re <> 0.
Proof.
  intros re H.
  assert (pumping_constant re >= 1) by apply pumping_constant_ge_1.
  inversion H0.
  - rewrite H in H2. discriminate.
  - rewrite H in H1. discriminate.
Qed.

Fixpoint napp {T} (l : list T) (n : nat) : list T :=
  match n with
  | S n' => l ++ napp l n'
  | 0 => []
  end.

Lemma napp_plus : forall T (l : list T) n m,
  napp l (n + m) = napp l n ++ napp l m.
Proof.
  induction n; cbn; intros.
  - reflexivity.
  - now rewrite IHn, app_assoc. Qed.

Lemma Star_napp : forall re n s1 s2,
  s1 =~ re ->
  s2 =~ Star re ->
  napp s1 n ++ s2 =~ Star re.
Proof.
  induction n; cbn; intros.
  - assumption.
  - rewrite <- app_assoc. now apply MStarApp, IHn. Qed.

Lemma add_le : forall n m p,
  n + m <= p -> n <= p /\ m <= p.
Proof.
  intros. induction H.
  - split. apply Nat.le_add_r. apply Nat.le_add_l.
  - destruct IHle. apply Nat.le_le_succ_r in H0. apply Nat.le_le_succ_r in H1.
    now split.
Qed.

Lemma pumping : forall re s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall n, s1 ++ napp s2 n ++ s3 =~ re.
Proof.
  intros re s H Hlen. induction H; cbn in *.
  - invert Hlen.
  - invert Hlen. invert H0.
  - destruct cs.
    + invert H.
    + invert Hlen. invert H1.
  - invert Hlen. apply pumping_constant_ne_0 in H0 as [].
  - rewrite app_length in Hlen.
    destruct (le_lt_dec (pumping_constant re) (length s1)) as [Hlen1 | Hlen1].
    + apply IHre_match1 in Hlen1 as [s11 [s12 [s13 [? [? []]]]]]. subst.
      exists s11, s12, (s13 ++ s2). repeat split.
      * now rewrite <- (app_assoc s11 _ _), <- app_assoc.
      * assumption.
      * assumption.
      * intros. rewrite (app_assoc _ _ s2), app_assoc. now apply MStarApp.
    + destruct (Nat.eq_dec (length s1) 0) as [Heq | Heq].
      * apply length_zero_iff_nil in Heq. subst. apply IHre_match2, Hlen.
      * exists [], s1, s2. repeat split.
        -- intro. destruct s1. now apply Heq. discriminate.
        -- now apply Nat.lt_le_incl.
        -- intros. now apply Star_napp.
  - rewrite app_length in Hlen.
    apply Nat.add_le_cases in Hlen as [Hlen1 | Hlen2].
    + apply IHre_match1 in Hlen1 as [s11 [s12 [s13 [? [? []]]]]]. subst.
      exists s11, s12, (s13 ++ s2). repeat split.
      * now rewrite <- app_assoc, <- app_assoc.
      * assumption.
      * now apply Arith_prebase.le_plus_trans_stt.
      * intros. rewrite (app_assoc _ _ s2), app_assoc. now apply MCat.
    + destruct (le_lt_dec (pumping_constant re1) (length s1)) as [Hlen1 | Hlen1].
      * apply IHre_match1 in Hlen1 as [s11 [s12 [s13 [? [? []]]]]]. subst.
        exists s11, s12, (s13 ++ s2). repeat split.
        -- now repeat rewrite <- app_assoc.
        -- assumption.
        -- now apply Arith_prebase.le_plus_trans_stt.
        -- intros. rewrite (app_assoc _ _ s2), app_assoc. apply MCat.
          ++ apply H4.
          ++ assumption.
      * apply IHre_match2 in Hlen2 as [s21 [s22 [s23 [? [? []]]]]]. subst.
        exists (s1 ++ s21), s22, s23. repeat split.
        -- now rewrite app_assoc.
        -- assumption.
        -- rewrite app_length, <- Nat.add_assoc.
           apply Nat.le_trans with (length s1 + pumping_constant re2).
           ++ now apply Nat.add_le_mono_l.
           ++ now apply Nat.add_le_mono_r, Nat.lt_le_incl.
        -- intros. rewrite <- app_assoc. now apply MCat.
  - apply add_le in Hlen as [Hlen1 _].
    apply IHre_match in Hlen1 as [s11 [s12 [s13 [? [? []]]]]]. subst.
    exists s11, s12, s13. repeat split.
    + assumption.
    + now apply Arith_prebase.le_plus_trans_stt.
    + intros. now apply MAltL.
  - apply add_le in Hlen as [_ Hlen2].
    apply IHre_match in Hlen2 as [s21 [s22 [s23 [? [? []]]]]]. subst.
    exists s21, s22, s23. repeat split.
    + assumption.
    + rewrite (Nat.add_comm (pumping_constant re1) _).
      now apply Arith_prebase.le_plus_trans_stt.
    + intros. now apply MAltR.
  - apply add_le in Hlen as [Hlen1 Hlen2].
    apply IHre_match1 in Hlen1 as [s11 [s12 [s13 [? [? []]]]]].
    apply IHre_match2 in Hlen2 as [s21 [s22 [s23 [? [? []]]]]].
    exists s11, s12, s13. repeat split.
    + assumption.
    + assumption.
    + now apply Arith_prebase.le_plus_trans_stt.
    + intros. apply MAnd. apply H4. admit.
Admitted.
