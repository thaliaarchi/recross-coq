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
  | (0,b6,b5,b4,b3,b2,b1,b0) ::: s' => let (rs, ok) := decode_utf8 s' in
      (N_of_digits [b0;b1;b2;b3;b4;b5;b6] :: rs, ok)
  | (1,1,0,b10,b9,b8,b7,b6) :::
    (1,0,b5,b4,b3,b2,b1,b0) ::: s' => let (rs, ok) := decode_utf8 s' in
      (N_of_digits [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10] :: rs, ok)
  | (1,1,1,0,b15,b14,b13,b12) :::
    (1,0,b11,b10,b9,b8,b7,b6) :::
    (1,0,b5,b4,b3,b2,b1,b0) ::: s' => let (rs, ok) := decode_utf8 s' in
      (N_of_digits [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15] :: rs, ok)
  | (1,1,1,1,0,b20,b19,b18) :::
    (1,0,b17,b16,b15,b14,b13,b12) :::
    (1,0,b11,b10,b9,b8,b7,b6) :::
    (1,0,b5,b4,b3,b2,b1,b0) ::: s' => let (rs, ok) := decode_utf8 s' in
      (N_of_digits [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20] :: rs, ok)
  | _ ::: _ => ([], false)
  | "" => ([], true)
  end%string.
