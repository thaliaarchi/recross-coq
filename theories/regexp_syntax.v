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

Inductive token_op :=
  | TStar
  | TAlt
  | TAnd
  | TParenL
  | TParenR.

Inductive token :=
  | TChar (c : ascii)
  | TClass (cs : list ascii)
  | TOp (op : token_op)
  | TErr.

Fixpoint lex (s : string) : list token :=
  match s with
  | "*" ::: s' => TOp TStar :: lex s'
  | "|" ::: s' => TOp TAlt :: lex s'
  | "&" ::: s' => TOp TAnd :: lex s'
  | "(" ::: s' => TOp TParenL :: lex s'
  | ")" ::: s' => TOp TParenR :: lex s'
  | "[" ::: s' => lex_class s' []
  | "]" ::: s' => [TErr]
  | "\" ::: s' => lex_escape s' None
  | c ::: s' => TChar c :: lex s'
  | "" => []
  end
with lex_class s cs :=
  match s with
  | "]" ::: s' => TClass (rev cs) :: lex s'
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
        | None => TChar c :: lex s'
        end
      else [TErr]
  | "x" ::: _ => [TErr]
  | c ::: s' => TChar c :: lex s'
  | "" => [TErr]
  end.

Definition token_op_to_ascii (op : token_op) : ascii :=
  match op with
  | TStar => "*"
  | TAlt => "|"
  | TAnd => "&"
  | TParenL => "("
  | TParenR => ")"
  end.

Fixpoint tokens_to_string (ts : list token) : string :=
  match ts with
  | TChar c :: ts' => String c (tokens_to_string ts')
  | TClass cs :: ts' => "[" ++ string_of_list_ascii cs ++ "]" ++ tokens_to_string ts'
  | TOp op :: ts' => String (token_op_to_ascii op) (tokens_to_string ts')
  | TErr :: ts' => tokens_to_string ts'
  | [] => ""
  end.

Inductive parse_op :=
  | OGroup
  | OStar
  | OCat
  | OAlt
  | OAnd.

Definition op_precedence (op : parse_op) : nat :=
  match op with
  | OGroup => 0
  | OStar => 1
  | OCat => 2
  | OAlt | OAnd => 3
  end.

Definition op_associativity (op : parse_op) : bool :=
  match op with
  | OGroup => true (* right associative *)
  | OStar => false (* left *)
  | OCat | OAlt | OAnd => true
  end.

(*
a(b|c*d)*e&f ==> a;(b|c*;d)*;e&f
a rs=[Lit "a"]
; rs=[Lit "a"] ops=[Cat]
( rs=[Lit "a"] ops=[Cat; Group]
b rs=[Lit "a"; Lit "b"] ops=[Cat; Group]
| rs=[Lit "a"; Lit "b"] ops=[Cat; Group; Alt]
c rs=[Lit "a"; Lit "b"; Lit "c"] ops=[Cat; Group; Alt]
* rs=[Lit "a"; Lit "b"; Lit "c"] ops=[Cat; Group; Alt; Star]
; rs=[Lit "a"; Lit "b"; Star (Lit "c")] ops=[Cat; Group; Alt; Cat]
d rs=[Lit "a"; Lit "b"; Star (Lit "c"); Lit "d"] ops=[Cat; Group; Alt; Cat]
) rs=[Lit "a"; Alt (Lit "b") (Cat (Star (Lit "c")) (Lit "d"))] ops=[Cat]
* rs=[Lit "a"; Alt (Lit "b") (Cat (Star (Lit "c")) (Lit "d"))] ops=[Cat; Star]
; rs=[Lit "a"; Star (Alt (Lit "b") (Cat (Star (Lit "c")) (Lit "d")))] ops=[Cat; Cat]
e rs=[Lit "a"; Star (Alt (Lit "b") (Cat (Star (Lit "c")) (Lit "d"))); Lit "e"] ops=[Cat; Cat]
& rs=[Cat (Lit "a") (Cat (Star (Alt (Lit "b") (Cat (Star (Lit "c")) (Lit "d")))) (Lit "e"))] ops=[And]
f rs=[Cat (Lit "a") (Cat (Star (Alt (Lit "b") (Cat (Star (Lit "c")) (Lit "d")))) (Lit "e")); Lit "f"] ops=[And]
And (Cat (Lit "a") (Cat (Star (Alt (Lit "b") (Cat (Star (Lit "c")) (Lit "d")))) (Lit "e"))) (Lit "f")
*)
