From recross Require Import util regexp.
Local Open Scope string_scope.

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
  | TErr (bad : string).

Fixpoint lex (s : string) : list token :=
  match s with
  | String "*" s' => TOp TStar :: lex s'
  | String "|" s' => TOp TAlt :: lex s'
  | String "&" s' => TOp TAnd :: lex s'
  | String "(" s' => TOp TParenL :: lex s'
  | String ")" s' => TOp TParenR :: lex s'
  | String "[" s' => lex_class s' []
  | String "]" s' => TErr "]" :: lex s'
  | String c s' => TChar c :: lex s'
  | "" => []
  end
with lex_class s cs :=
  match s with
  | String "]" s' => TClass (rev cs) :: lex s'
  | String c s' => lex_class s' (c :: cs)
  | "" => [TErr ""]
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
  | TErr err :: ts' => err ++ tokens_to_string ts'
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
