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
