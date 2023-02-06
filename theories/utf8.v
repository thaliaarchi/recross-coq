Require Import Bool.
Require Import List. Import ListNotations.
Require Import Ascii String.
Require Import NArith.

Definition rune := N.

Inductive rune_bits := RuneBits (b20 b19 b18 b17 b16 b15 b14 b13 b12 b11
                                 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 : bool).

Local Notation "0" := false : bool_scope.
Local Notation "1" := true : bool_scope.
Local Notation "b[ b7 , b6 , b5 , b4 , b3 , b2 , b1 , b0 ]" := (Ascii b0 b1 b2 b3 b4 b5 b6 b7) : char_scope.
Local Notation "a ::: s" := (String a s) (at level 60, right associativity) : string_scope.

Definition rune_to_bits (r : rune) : rune_bits :=
  RuneBits (N.testbit 0 r) (N.testbit 1 r) (N.testbit 2 r) (N.testbit 3 r)
           (N.testbit 4 r) (N.testbit 5 r) (N.testbit 6 r) (N.testbit 7 r)
           (N.testbit 8 r) (N.testbit 9 r) (N.testbit 10 r) (N.testbit 11 r)
           (N.testbit 12 r) (N.testbit 13 r) (N.testbit 14 r) (N.testbit 15 r)
           (N.testbit 16 r) (N.testbit 17 r) (N.testbit 18 r) (N.testbit 19 r)
           (N.testbit 20 r).

Definition rune_of_bits (bs : rune_bits) : rune :=
  let (b20, b19, b18, b17, b16, b15, b14, b13, b12, b11,
       b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0) := bs in
  N_of_digits [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10;
               b11; b12; b13; b14; b15; b16; b17; b18; b19; b20].

Fixpoint decode_utf8 (s : string) : list rune * bool :=
  match s with
  | b[0,b6,b5,b4,b3,b2,b1,b0] ::: s' =>
      let r := N_of_digits [b0;b1;b2;b3;b4;b5;b6] in
      let (rs, ok) := decode_utf8 s' in (r :: rs, ok)
  | b[1,1,0,b10,b9,b8,b7,b6] :::
    b[1,0,b5,b4,b3,b2,b1,b0] ::: s' =>
      let r := N_of_digits [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10] in
      if (r <? 0x80)%N then ([], false) else
      let (rs, ok) := decode_utf8 s' in (r :: rs, ok)
  | b[1,1,1,0,b15,b14,b13,b12] :::
    b[1,0,b11,b10,b9,b8,b7,b6] :::
    b[1,0,b5,b4,b3,b2,b1,b0] ::: s' =>
      let r := N_of_digits [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15] in
      if ((r <? 0x800) || ((0xD800 <=? r) && (r <=? 0xDFFF)))%N then ([], false) else
      let (rs, ok) := decode_utf8 s' in (r :: rs, ok)
  | b[1,1,1,1,0,b20,b19,b18] :::
    b[1,0,b17,b16,b15,b14,b13,b12] :::
    b[1,0,b11,b10,b9,b8,b7,b6] :::
    b[1,0,b5,b4,b3,b2,b1,b0] ::: s' =>
      let r := N_of_digits [b0;b1;b2;b3;b4;b5;b6;b7;b8;b9;b10;b11;b12;b13;b14;b15;b16;b17;b18;b19;b20] in
      if ((r <? 0x10000) || (0x10ffff <? r))%N then ([], false) else
      let (rs, ok) := decode_utf8 s' in (r :: rs, ok)
  | _ ::: _ => ([], false)
  | "" => ([], true)
  end%string.

Definition rune_encode_utf8 (r : rune) : string :=
  match rune_to_bits r with
  | RuneBits 0 0 0 0 0 0 0 0 0 0 0 0 0 0 b6 b5 b4 b3 b2 b1 b0 =>
      b[0,b6,b5,b4,b3,b2,b1,b0] ::: ""
  | RuneBits 0 0 0 0 0 0 0 0 0 0 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 =>
      b[1,1,0,b10,b9,b8,b7,b6] :::
      b[1,0,b5,b4,b3,b2,b1,b0] ::: ""
  | RuneBits 0 0 0 0 0 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 =>
      b[1,1,1,0,b15,b14,b13,b12] :::
      b[1,0,b11,b10,b9,b8,b7,b6] :::
      b[1,0,b5,b4,b3,b2,b1,b0] ::: ""
  | RuneBits b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 =>
      b[1,1,1,1,0,b20,b19,b18] :::
      b[1,0,b17,b16,b15,b14,b13,b12] :::
      b[1,0,b11,b10,b9,b8,b7,b6] :::
      b[1,0,b5,b4,b3,b2,b1,b0] ::: ""
  end.

Fixpoint encode_utf8 (rs : list rune) : string :=
  match rs with
  | r :: rs' => rune_encode_utf8 r ++ encode_utf8 rs'
  | [] => ""
  end.

Fixpoint string_is_ascii (s : string) : bool :=
  match s with
  | a ::: s' => (a <? "128")%char && string_is_ascii s'
  | "" => false
  end%string.
