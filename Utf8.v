Require Import Bool.
Require Import List. Import ListNotations.
Require Import Ascii String.
Require Import NArith.

Definition rune := N.

Local Notation "0" := false : bool_scope.
Local Notation "1" := true : bool_scope.
Local Notation "( b7 , b6 , b5 , b4 , b3 , b2 , b1 , b0 )" := (Ascii b0 b1 b2 b3 b4 b5 b6 b7) : char_scope.
Local Notation "a ::: s" := (String a s) (at level 60, right associativity) : string_scope.

Fixpoint decode_utf8 (s : string) : list rune * bool :=
  match s with
  | (0,b6,b5,b4,b3,b2,b1,b0) ::: s' =>
      let r := N_of_digits [b0;b1;b2;b3;b4;b5;b6] in
      let (rs, ok) := decode_utf8 s' in (r :: rs, ok)
  | (1,1,0,b10,b9,b8,b7,b6) :::
    (1,0,b5,b4,b3,b2,b1,b0) ::: s' =>
      let r := N_of_digits [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10] in
      if (r <? 128)%N then ([], false) else
      let (rs, ok) := decode_utf8 s' in (r :: rs, ok)
  | (1,1,1,0,b15,b14,b13,b12) :::
    (1,0,b11,b10,b9,b8,b7,b6) :::
    (1,0,b5,b4,b3,b2,b1,b0) ::: s' =>
      let r := N_of_digits [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15] in
      if ((r <? 2048) || ((55296 <=? r) && (r <=? 57343)))%N then ([], false) else
      let (rs, ok) := decode_utf8 s' in (r :: rs, ok)
  | (1,1,1,1,0,b20,b19,b18) :::
    (1,0,b17,b16,b15,b14,b13,b12) :::
    (1,0,b11,b10,b9,b8,b7,b6) :::
    (1,0,b5,b4,b3,b2,b1,b0) ::: s' =>
      let r := N_of_digits [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20] in
      if ((r <? 65536) || (1114111 <? r))%N then ([], false) else
      let (rs, ok) := decode_utf8 s' in (r :: rs, ok)
  | _ ::: _ => ([], false)
  | "" => ([], true)
  end%string.

Fixpoint string_is_ascii (s : string) : bool :=
  match s with
  | a ::: s' => (a <? "128")%char && string_is_ascii s'
  | "" => false
  end%string.
