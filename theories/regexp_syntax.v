From recross Require Import util regexp.
Local Open Scope string_scope.

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

Definition hex_to_byte (c1 c2 : ascii) : option ascii :=
  match hex_to_nibble c1, hex_to_nibble c2 with
  | Some (b4, b5, b6, b7), Some (b0, b1, b2, b3) => Some (Ascii b0 b1 b2 b3 b4 b5 b6 b7)
  | _, _ => None
  end.

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

Definition byte_to_hex (c : ascii) : ascii * ascii :=
  let (b0, b1, b2, b3, b4, b5, b6, b7) := c in
  (nibble_to_hex b4 b5 b6 b7, nibble_to_hex b0 b1 b2 b3).

Lemma byte_to_hex_to_byte : forall c d1 d2,
  byte_to_hex c = (d1, d2) ->
  hex_to_byte d1 d2 = Some c.
Proof.
  intros. destruct c as [[] [] [] [] [] [] [] []]; now invert H. Qed.

Fixpoint regexp_to_string (re : regexp) : string :=
  let paren_star := fun re s =>
    match re with
    | Nil => "()*"
    | Cat _ _ | Alt _ _ | And _ _ => "(" ++ s ++ ")*"
    | _ => s ++ "*"
    end in
  let paren_cat := fun re s =>
    match re with
    | Alt _ _ | And _ _ => "(" ++ s ++ ")"
    | _ => s
    end in
  let paren_alt := fun re s =>
    if re is And _ _ then "(" ++ s ++ ")" else s in
  let paren_and := fun re s =>
    if re is Alt _ _ then "(" ++ s ++ ")" else s in
  match re with
  | Void => "[]"
  | Nil => ""
  | Char c => String c ""
  | Class cs => "[" ++ string_of_list_ascii cs ++ "]"
  | Star re => paren_star re (regexp_to_string re)
  | Cat re1 re2 => paren_cat re1 (regexp_to_string re1) ++
                   paren_cat re2 (regexp_to_string re2)
  | Alt re1 re2 => paren_alt re1 (regexp_to_string re1) ++ "|" ++
                   paren_alt re2 (regexp_to_string re2)
  | And re1 re2 => paren_and re1 (regexp_to_string re1) ++ "&" ++
                   paren_and re2 (regexp_to_string re2)
  end.

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
  | ("0" | "1" | "2" | "3" | "4" |
     "5" | "6" | "7" | "8" | "9") ::: _ => [TErr]
  | "x" ::: c1 ::: c2 ::: s' =>
      if hex_to_byte c1 c2 is Some c then
        match maybe_cs with
        | Some cs => lex_class s' (c :: cs)
        | None => TChar c :: lex_tokens s'
        end
      else [TErr]
  | "x" ::: _ => [TErr]
  | c ::: s' => TChar c :: lex_tokens s'
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

Fixpoint tokens_to_string (ts : list token) : string :=
  match ts with
  | TNil :: ts' => tokens_to_string ts'
  | TChar c :: ts' => String c (tokens_to_string ts')
  | TClass cs :: ts' => "[" ++ string_of_list_ascii cs ++ "]" ++ tokens_to_string ts'
  | TStar :: ts' => String "*" (tokens_to_string ts')
  | TCat :: ts' => tokens_to_string ts'
  | TAlt :: ts' => String "|" (tokens_to_string ts')
  | TAnd :: ts' => String "&" (tokens_to_string ts')
  | TParenL :: ts' => String "(" (tokens_to_string ts')
  | TParenR :: ts' => String ")" (tokens_to_string ts')
  | TErr :: ts' => tokens_to_string ts'
  | [] => ""
  end.

Inductive parse_op :=
  | OGroup
  | OCat
  | OAlt
  | OAnd
  | OStar.

Definition op_precedence (op : parse_op) : nat :=
  match op with
  | OAnd => 0
  | OAlt => 1
  | OCat => 2
  | OStar => 3
  | OGroup => 4
  end.

Definition op_left_associative (op : parse_op) : bool :=
  match op with
  | OGroup => false
  | OStar => true
  | OCat | OAlt | OAnd => false
  end.

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
Definition greater_precedence (op1 op2 : parse_op) : bool :=
  match op1, op2 with
  | OAnd, _ => false
  | OAlt, OAnd => true
  | OCat, (OAlt | OAnd) => true
  | OStar, (OStar | OCat | OAlt | OAnd) => true
  | OGroup, _ => true
  | _, _ => false
  end.

Definition apply_op op rs : option (list regexp) :=
  match op, rs with
  | OGroup, _ => Some rs
  | OCat, re2 :: re1 :: rs' => Some (Cat re1 re2 :: rs')
  | OAlt, re2 :: re1 :: rs' => Some (Alt re1 re2 :: rs')
  | OAnd, re2 :: re1 :: rs' => Some (And re1 re2 :: rs')
  | OStar, re :: rs' => Some (Star re :: rs')
  | _, _ => None
  end.

Definition parse_token (t : token) (rs : list regexp) (ops : list parse_op) : option (list regexp * list parse_op) :=
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
