From recross Require Import util regexp.

Local Notation "a ::: s" := (String a s) (at level 60, right associativity) : string_scope.
Local Notation "a || b" := (if a then true else if b then true else false).

Definition hex_to_nibble (c : ascii) : option (bool * bool * bool * bool) :=
  if ascii_dec c "0" then Some (false, false, false, false)
  else if ascii_dec c "1" then Some (true, false, false, false)
  else if ascii_dec c "2" then Some (false, true, false, false)
  else if ascii_dec c "3" then Some (true, true, false, false)
  else if ascii_dec c "4" then Some (false, false, true, false)
  else if ascii_dec c "5" then Some (true, false, true, false)
  else if ascii_dec c "6" then Some (false, true, true, false)
  else if ascii_dec c "7" then Some (true, true, true, false)
  else if ascii_dec c "8" then Some (false, false, false, true)
  else if ascii_dec c "9" then Some (true, false, false, true)
  else if ascii_dec c "a" || ascii_dec c "A" then Some (false, true, false, true)
  else if ascii_dec c "b" || ascii_dec c "B" then Some (true, true, false, true)
  else if ascii_dec c "c" || ascii_dec c "C" then Some (false, false, true, true)
  else if ascii_dec c "d" || ascii_dec c "D" then Some (true, false, true, true)
  else if ascii_dec c "e" || ascii_dec c "E" then Some (false, true, true, true)
  else if ascii_dec c "f" || ascii_dec c "F" then Some (true, true, true, true)
  else None.

Definition nibble_to_hex (b0 b1 b2 b3 : bool) : ascii :=
  match b0, b1, b2, b3 with
  | false, false, false, false => "0"
  | true,  false, false, false => "1"
  | false, true,  false, false => "2"
  | true,  true,  false, false => "3"
  | false, false, true,  false => "4"
  | true,  false, true,  false => "5"
  | false, true,  true,  false => "6"
  | true,  true,  true,  false => "7"
  | false, false, false, true  => "8"
  | true,  false, false, true  => "9"
  | false, true,  false, true  => "a"
  | true,  true,  false, true  => "b"
  | false, false, true,  true  => "c"
  | true,  false, true,  true  => "d"
  | false, true,  true,  true  => "e"
  | true,  true,  true,  true  => "f"
  end.

Definition hex_to_byte (c1 c2 : ascii) : option ascii :=
  match hex_to_nibble c1, hex_to_nibble c2 with
  | Some (b4, b5, b6, b7), Some (b0, b1, b2, b3) => Some (Ascii b0 b1 b2 b3 b4 b5 b6 b7)
  | _, _ => None
  end.

Definition byte_to_hex (c : ascii) : ascii * ascii :=
  let (b0, b1, b2, b3, b4, b5, b6, b7) := c in
  (nibble_to_hex b4 b5 b6 b7, nibble_to_hex b0 b1 b2 b3).

Lemma byte_to_hex_to_byte : forall c d1 d2,
  byte_to_hex c = (d1, d2) ->
  hex_to_byte d1 d2 = Some c.
Proof.
  intros. destruct c as [[] [] [] [] [] [] [] []]; now invert H. Qed.

Definition needs_slash (c : ascii) : bool :=
  if ascii_dec c "(" || ascii_dec c ")" || ascii_dec c "[" || ascii_dec c "]" ||
     ascii_dec c "*" || ascii_dec c "|" || ascii_dec c "&" || ascii_dec c "\" then true else false.

Definition is_digit (c : ascii) : bool :=
  if ascii_dec c "0" || ascii_dec c "1" || ascii_dec c "2" || ascii_dec c "3" ||
     ascii_dec c "4" || ascii_dec c "5" || ascii_dec c "6" || ascii_dec c "7" ||
     ascii_dec c "8" || ascii_dec c "9" then true else false.

Definition is_non_printable (c : ascii) : bool :=
  if match c with
     | Ascii _ _ _ _ _ false false false | Ascii _ _ _ _ _ _ _ true => true
     | _ => false
     end || ascii_dec c "127" then true else false.

Definition escape_byte_hex (c : ascii) : string :=
  "\" ::: "x" ::: let (h1, h2) := byte_to_hex c in h1 ::: h2 ::: "".

Definition escape_byte (c : ascii) : string :=
  if needs_slash c then "\" ::: c ::: ""
  else if ascii_dec c "007" then "\a"
  else if ascii_dec c "012" then "\f"
  else if ascii_dec c "009" then "\t"
  else if ascii_dec c "010" then "\n"
  else if ascii_dec c "013" then "\r"
  else if ascii_dec c "011" then "\v"
  else if is_non_printable c then escape_byte_hex c
  else c ::: "".

Definition unescape_byte (c : ascii) : option ascii :=
  (if needs_slash c then Some c
  else if ascii_dec c "a" then Some "007"
  else if ascii_dec c "f" then Some "012"
  else if ascii_dec c "t" then Some "009"
  else if ascii_dec c "n" then Some "010"
  else if ascii_dec c "r" then Some "013"
  else if ascii_dec c "v" then Some "011"
  else None)%char.

Fixpoint escape_string (s : string) : string :=
  match s with
  | c ::: s' => escape_byte c ++ escape_string s'
  | "" => ""
  end.

Lemma escape_byte_hex_length : forall c,
  String.length (escape_byte_hex c) = 4.
Proof. now destruct c as [[] [] [] [] [] [] [] []]. Qed.

Lemma escape_unescape_byte : forall u e,
  escape_byte u = "\" ::: e ::: "" <-> unescape_byte e = Some u.
Proof.
  unfold escape_byte, unescape_byte.
  split; intros.
  - destruct (needs_slash u) eqn:Hs. { invert H. now rewrite Hs. }
    destruct (ascii_dec u "007"). { now invert H. }
    destruct (ascii_dec u "012"). { now invert H. }
    destruct (ascii_dec u "009"). { now invert H. }
    destruct (ascii_dec u "010"). { now invert H. }
    destruct (ascii_dec u "013"). { now invert H. }
    destruct (ascii_dec u "011"). { now invert H. }
    destruct (is_non_printable u) eqn:Hp.
    { apply (f_equal String.length) in H.
      rewrite escape_byte_hex_length in H. discriminate H. }
    discriminate H.
  - destruct (needs_slash e) eqn:Hs. { invert H. now rewrite Hs. }
    destruct (ascii_dec e "a"). { now invert H. }
    destruct (ascii_dec e "f"). { now invert H. }
    destruct (ascii_dec e "t"). { now invert H. }
    destruct (ascii_dec e "n"). { now invert H. }
    destruct (ascii_dec e "r"). { now invert H. }
    destruct (ascii_dec e "v"). { now invert H. }
    discriminate H.
Qed.

Inductive token :=
  | TNil
  | TChar (c : ascii)
  | TClass (cs : list ascii)
  | TStar
  | TCat
  | TAlt
  | TAnd
  | TParenL
  | TParenR
  | TErr.

Inductive regexp_op :=
  | OGroup
  | OCat
  | OAlt
  | OAnd
  | OStar.

(*
  Operator precedence (lowest to highest):
  - OAnd (right)
  - OAlt (right)
  - OCat (right)
  - OStar (left)
  - OGroup (right)

  Left associative: greater than or equal
  Right associative: greater than
*)
Definition greater_precedence (op1 op2 : regexp_op) : bool :=
  match op1, op2 with
  | OAnd, _ => false
  | OAlt, OAnd => true
  | OCat, (OAlt | OAnd) => true
  | OStar, (OStar | OCat | OAlt | OAnd) => true
  | OGroup, _ => true
  | _, _ => false
  end.

Definition re_op (re : regexp) : option regexp_op :=
  match re with
  | Void | Nil | Char _ | Class _ => None
  | Star _ => Some OStar
  | Cat _ _ => Some OCat
  | Alt _ _ => Some OAlt
  | And _ _ => Some OAnd
  end.

Definition re_greater_precedence (op1 : regexp_op) (re2 : regexp) : bool :=
  if re_op re2 is Some op2 then greater_precedence op1 op2 else false.

Fixpoint regexp_to_tokens (re : regexp) : list token :=
  let fix maybe_paren op re :=
    if re_greater_precedence op re then
      [TParenL] ++ regexp_to_tokens re ++ [TParenR]
    else regexp_to_tokens re in
  match re with
  | Void => [TClass []]
  | Nil => [TNil]
  | Char c => [TChar c]
  | Class cs => [TClass cs]
  | Star re => maybe_paren OStar re ++ [TStar]
  | Cat re1 re2 => maybe_paren OCat re1 ++ [TCat] ++ maybe_paren OCat re2
  | Alt re1 re2 => maybe_paren OAlt re1 ++ [TAlt] ++ maybe_paren OAlt re2
  | And re1 re2 => maybe_paren OAnd re1 ++ [TAnd] ++ maybe_paren OAnd re2
  end.

Definition token_to_string (t : token) : string :=
  match t with
  | TNil => ""
  | TChar c => escape_byte c
  | TClass cs => "[" ++ escape_string (string_of_list_ascii cs) ++ "]"
  | TStar => "*"
  | TCat => ""
  | TAlt => "|"
  | TAnd => "&"
  | TParenL => "("
  | TParenR => ")"
  | TErr => ""
  end.

Fixpoint tokens_to_string (ts : list token) : string :=
  match ts with
  | t :: ts' => token_to_string t ++ tokens_to_string ts'
  | [] => ""
  end.

Definition regexp_to_string (re : regexp) : string :=
  tokens_to_string (regexp_to_tokens re).

Fixpoint lex_tokens (s : string) : list token :=
  match s with
  | "*" ::: s' => TStar :: lex_tokens s'
  | "|" ::: s' => TAlt :: lex_tokens s'
  | "&" ::: s' => TAnd :: lex_tokens s'
  | "(" ::: s' => TParenL :: lex_tokens s'
  | ")" ::: s' => TParenR :: lex_tokens s'
  | "[" ::: s' => lex_class s' []
  | "]" ::: s' => [TErr]
  | "\" ::: s' => lex_escape s' None
  | c ::: s' => TChar c :: lex_tokens s'
  | "" => []
  end
with lex_class s cs :=
  match s with
  | "]" ::: s' => TClass (rev cs) :: lex_tokens s'
  | "\" ::: s' => lex_escape s' (Some cs)
  | c ::: s' => lex_class s' (c :: cs)
  | "" => [TErr]
  end
with lex_escape s maybe_cs :=
  match s with
  | "x" ::: c1 ::: c2 ::: s' =>
      if hex_to_byte c1 c2 is Some c then
        match maybe_cs with
        | Some cs => lex_class s' (c :: cs)
        | None => TChar c :: lex_tokens s'
        end
      else [TErr]
  | c ::: s' =>
      if unescape_byte c is Some c'
      then TChar c' :: lex_tokens s' else [TErr]
  | "" => [TErr]
  end.

Fixpoint insert_invisible (ts : list token) : list token :=
  match ts with
  | t1 :: (t2 :: _) as ts' =>
      match t1, t2 with
      | TParenL, (TAlt | TAnd) | (TAlt | TAnd), TParenR =>
          t1 :: TNil :: insert_invisible ts'
      | (TChar _ | TClass _ | TStar | TParenR), (TChar _ | TClass _ | TParenL) =>
          t1 :: TCat :: insert_invisible ts'
      | _, _ => t1 :: insert_invisible ts'
      end
  | t :: ts' => t :: insert_invisible ts'
  | [] => []
  end.

Definition lex (s : string) : list token :=
  insert_invisible (lex_tokens s).

Definition apply_op op rs : option (list regexp) :=
  match op, rs with
  | OGroup, _ => Some rs
  | OCat, re2 :: re1 :: rs' => Some (Cat re1 re2 :: rs')
  | OAlt, re2 :: re1 :: rs' => Some (Alt re1 re2 :: rs')
  | OAnd, re2 :: re1 :: rs' => Some (And re1 re2 :: rs')
  | OStar, re :: rs' => Some (Star re :: rs')
  | _, _ => None
  end.

Definition parse_token (t : token) (rs : list regexp) (ops : list regexp_op) : option (list regexp * list regexp_op) :=
  let fix close_group rs ops :=
    match ops with
    | OGroup :: ops' => Some (rs, ops')
    | op :: ops' =>
        if apply_op op rs is Some rs' then close_group rs' ops' else None
    | [] => None
    end in
  let fix push_op op rs ops :=
    match ops with
    | OGroup :: _ | [] => Some (rs, op :: ops)
    | op2 :: ops' =>
        if greater_precedence op2 op then
          if apply_op op2 rs is Some rs' then push_op op rs' ops' else None
        else Some (rs, op :: ops)
    end in
  match t with
  | TNil => Some (Nil :: rs, ops)
  | TChar c => Some (Char c :: rs, ops)
  | TClass cs => Some (Class cs :: rs, ops)
  | TParenL => Some (rs, OGroup :: ops)
  | TParenR => close_group rs ops
  | TCat => push_op OCat rs ops
  | TAlt => push_op OAlt rs ops
  | TAnd => push_op OAnd rs ops
  | TStar => push_op OStar rs ops
  | TErr => None
  end%char.

Definition parse_tokens (ts : list token) : option regexp :=
  let fix fold_ops rs ops :=
    match ops, rs with
    | op :: ops', _ =>
        if apply_op op rs is Some rs'
        then fold_ops rs' ops' else None
    | [], [re] => Some re
    | [], _ => None
    end in
  let fix parse_rec ts rs ops :=
    match ts with
    | t :: ts' =>
        if parse_token t rs ops is Some (rs', ops')
        then parse_rec ts' rs' ops' else None
    | [] => fold_ops rs ops
    end in
  parse_rec ts [] [].

Definition parse (s : string) : option regexp :=
  parse_tokens (lex s).

Goal parse "ab(cd|e*f|)*g&abcd"
= Some (And (Cat (Char "a") (Cat (Char "b") (Cat (Star (Alt (Cat (Char "c") (Char "d"))
                                                            (Alt (Cat (Star (Char "e")) (Char "f")) Nil)))
                                                 (Char "g"))))
            (Cat (Char "a") (Cat (Char "b") (Cat (Char "c") (Char "d"))))).
Proof. reflexivity. Qed.
