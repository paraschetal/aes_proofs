(*Require Import Coq.Init.Byte.*)
Require Import Program.
Require Import Nat.
Inductive bit : Type :=
| s0
| s1
.

Inductive nibble: Type :=
| bits4 (b0 b1 b2 b3: bit)
.

Inductive byte : Type :=
| bits8 (b0 b1 b2 b3 b4 b5 b6 b7 : bit)
.

Definition ms_nibble (b:byte) : nibble :=
  match b with
  | bits8 b0 b1 b2 b3 _ _ _ _  => bits4 b0 b1 b2 b3
end.

Definition ls_nibble (b:byte) : nibble :=
  match b with
  | bits8 _ _ _ _ b4 b5 b6 b7 => bits4 b4 b5 b6 b7
  end.


Definition xor_bits (b1 b2: bit) : bit :=
  match b1 with
  | s0 => match b2 with
          | s0 => s0
          | s1 => s1
          end
  | s1 => match b2 with
          | s0 => s1
          | s1 => s0
          end
  end. 

Notation "a x*or b" := (xor_bits a b) (at level 75).
Definition xor_bytes (b a: byte) : byte :=
  match b with
  | bits8 b7 b6 b5 b4 b3 b2 b1 b0 =>
      match a with
      | bits8 a7 a6 a5 a4 a3 a2 a1 a0 =>
          bits8 (b7 x*or a7) (b6 x*or a6) (b5 x*or a5) (b4 x*or a4) (b3 x*or a3) (b2 x*or a2) (b1 x*or a1) (b0 x*or a0)
      end
  end.
Notation "A X*OR B" := (xor_bytes A B) (at level 75).

Inductive word : Type :=
| bytes4 (b0 b1 b2 b3: byte)
.

Inductive qword: Type :=
| words4 (w0 w1 w2 w3: word)
.


Inductive matrix : Type :=
| bytes16 (r0c0 r0c1 r0c2 r0c3
           r1c0 r1c1 r1c2 r1c3
           r2c0 r2c1 r2c2 r2c3
           r3c0 r3c1 r3c2 r3c3: byte)
.

Definition s_box (b: byte) : byte :=
  match (ms_nibble b) with
    | bits4 s0 s0 s0 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s1 s1 s0 s0 s0 s1 s1
        | bits4 s0 s0 s0 s1 => bits8 s0 s1 s1 s1 s1 s1 s0 s0
        | bits4 s0 s0 s1 s0 => bits8 s0 s1 s1 s1 s0 s1 s1 s1
        | bits4 s0 s0 s1 s1 => bits8 s0 s1 s1 s1 s1 s0 s1 s1
        | bits4 s0 s1 s0 s0 => bits8 s1 s1 s1 s1 s0 s0 s1 s0
        | bits4 s0 s1 s0 s1 => bits8 s0 s1 s1 s0 s1 s0 s1 s1
        | bits4 s0 s1 s1 s0 => bits8 s0 s1 s1 s0 s1 s1 s1 s1
        | bits4 s0 s1 s1 s1 => bits8 s1 s1 s0 s0 s0 s1 s0 s1
        | bits4 s1 s0 s0 s0 => bits8 s0 s0 s1 s1 s0 s0 s0 s0
        | bits4 s1 s0 s0 s1 => bits8 s0 s0 s0 s0 s0 s0 s0 s1
        | bits4 s1 s0 s1 s0 => bits8 s0 s1 s1 s0 s0 s1 s1 s1
        | bits4 s1 s0 s1 s1 => bits8 s0 s0 s1 s0 s1 s0 s1 s1
        | bits4 s1 s1 s0 s0 => bits8 s1 s1 s1 s1 s1 s1 s1 s0
        | bits4 s1 s1 s0 s1 => bits8 s1 s1 s0 s1 s0 s1 s1 s1
        | bits4 s1 s1 s1 s0 => bits8 s1 s0 s1 s0 s1 s0 s1 s1
        | bits4 s1 s1 s1 s1 => bits8 s0 s1 s1 s1 s0 s1 s1 s0
      end
    | bits4 s0 s0 s0 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s1 s1 s0 s0 s1 s0 s1 s0
        | bits4 s0 s0 s0 s1 => bits8 s1 s0 s0 s0 s0 s0 s1 s0
        | bits4 s0 s0 s1 s0 => bits8 s1 s1 s0 s0 s1 s0 s0 s1
        | bits4 s0 s0 s1 s1 => bits8 s0 s1 s1 s1 s1 s1 s0 s1
        | bits4 s0 s1 s0 s0 => bits8 s1 s1 s1 s1 s1 s0 s1 s0
        | bits4 s0 s1 s0 s1 => bits8 s0 s1 s0 s1 s1 s0 s0 s1
        | bits4 s0 s1 s1 s0 => bits8 s0 s1 s0 s0 s0 s1 s1 s1
        | bits4 s0 s1 s1 s1 => bits8 s1 s1 s1 s1 s0 s0 s0 s0
        | bits4 s1 s0 s0 s0 => bits8 s1 s0 s1 s0 s1 s1 s0 s1
        | bits4 s1 s0 s0 s1 => bits8 s1 s1 s0 s1 s0 s1 s0 s0
        | bits4 s1 s0 s1 s0 => bits8 s1 s0 s1 s0 s0 s0 s1 s0
        | bits4 s1 s0 s1 s1 => bits8 s1 s0 s1 s0 s1 s1 s1 s1
        | bits4 s1 s1 s0 s0 => bits8 s1 s0 s0 s1 s1 s1 s0 s0
        | bits4 s1 s1 s0 s1 => bits8 s1 s0 s1 s0 s0 s1 s0 s0
        | bits4 s1 s1 s1 s0 => bits8 s0 s1 s1 s1 s0 s0 s1 s0
        | bits4 s1 s1 s1 s1 => bits8 s1 s1 s0 s0 s0 s0 s0 s0
      end
    | bits4 s0 s0 s1 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s1 s0 s1 s1 s0 s1 s1 s1
        | bits4 s0 s0 s0 s1 => bits8 s1 s1 s1 s1 s1 s1 s0 s1
        | bits4 s0 s0 s1 s0 => bits8 s1 s0 s0 s1 s0 s0 s1 s1
        | bits4 s0 s0 s1 s1 => bits8 s0 s0 s1 s0 s0 s1 s1 s0
        | bits4 s0 s1 s0 s0 => bits8 s0 s0 s1 s1 s0 s1 s1 s0
        | bits4 s0 s1 s0 s1 => bits8 s0 s0 s1 s1 s1 s1 s1 s1
        | bits4 s0 s1 s1 s0 => bits8 s1 s1 s1 s1 s0 s1 s1 s1
        | bits4 s0 s1 s1 s1 => bits8 s1 s1 s0 s0 s1 s1 s0 s0
        | bits4 s1 s0 s0 s0 => bits8 s0 s0 s1 s1 s0 s1 s0 s0
        | bits4 s1 s0 s0 s1 => bits8 s1 s0 s1 s0 s0 s1 s0 s1
        | bits4 s1 s0 s1 s0 => bits8 s1 s1 s1 s0 s0 s1 s0 s1
        | bits4 s1 s0 s1 s1 => bits8 s1 s1 s1 s1 s0 s0 s0 s1
        | bits4 s1 s1 s0 s0 => bits8 s0 s1 s1 s1 s0 s0 s0 s1
        | bits4 s1 s1 s0 s1 => bits8 s1 s1 s0 s1 s1 s0 s0 s0
        | bits4 s1 s1 s1 s0 => bits8 s0 s0 s1 s1 s0 s0 s0 s1
        | bits4 s1 s1 s1 s1 => bits8 s0 s0 s0 s1 s0 s1 s0 s1
      end
    | bits4 s0 s0 s1 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s0 s0 s0 s0 s1 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s1 s1 s0 s0 s0 s1 s1 s1
        | bits4 s0 s0 s1 s0 => bits8 s0 s0 s1 s0 s0 s0 s1 s1
        | bits4 s0 s0 s1 s1 => bits8 s1 s1 s0 s0 s0 s0 s1 s1
        | bits4 s0 s1 s0 s0 => bits8 s0 s0 s0 s1 s1 s0 s0 s0
        | bits4 s0 s1 s0 s1 => bits8 s1 s0 s0 s1 s0 s1 s1 s0
        | bits4 s0 s1 s1 s0 => bits8 s0 s0 s0 s0 s0 s1 s0 s1
        | bits4 s0 s1 s1 s1 => bits8 s1 s0 s0 s1 s1 s0 s1 s0
        | bits4 s1 s0 s0 s0 => bits8 s0 s0 s0 s0 s0 s1 s1 s1
        | bits4 s1 s0 s0 s1 => bits8 s0 s0 s0 s1 s0 s0 s1 s0
        | bits4 s1 s0 s1 s0 => bits8 s1 s0 s0 s0 s0 s0 s0 s0
        | bits4 s1 s0 s1 s1 => bits8 s1 s1 s1 s0 s0 s0 s1 s0
        | bits4 s1 s1 s0 s0 => bits8 s1 s1 s1 s0 s1 s0 s1 s1
        | bits4 s1 s1 s0 s1 => bits8 s0 s0 s1 s0 s0 s1 s1 s1
        | bits4 s1 s1 s1 s0 => bits8 s1 s0 s1 s1 s0 s0 s1 s0
        | bits4 s1 s1 s1 s1 => bits8 s0 s1 s1 s1 s0 s1 s0 s1
      end
    | bits4 s0 s1 s0 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s0 s0 s0 s1 s0 s0 s1
        | bits4 s0 s0 s0 s1 => bits8 s1 s0 s0 s0 s0 s0 s1 s1
        | bits4 s0 s0 s1 s0 => bits8 s0 s0 s1 s0 s1 s1 s0 s0
        | bits4 s0 s0 s1 s1 => bits8 s0 s0 s0 s1 s1 s0 s1 s0
        | bits4 s0 s1 s0 s0 => bits8 s0 s0 s0 s1 s1 s0 s1 s1
        | bits4 s0 s1 s0 s1 => bits8 s0 s1 s1 s0 s1 s1 s1 s0
        | bits4 s0 s1 s1 s0 => bits8 s0 s1 s0 s1 s1 s0 s1 s0
        | bits4 s0 s1 s1 s1 => bits8 s1 s0 s1 s0 s0 s0 s0 s0
        | bits4 s1 s0 s0 s0 => bits8 s0 s1 s0 s1 s0 s0 s1 s0
        | bits4 s1 s0 s0 s1 => bits8 s0 s0 s1 s1 s1 s0 s1 s1
        | bits4 s1 s0 s1 s0 => bits8 s1 s1 s0 s1 s0 s1 s1 s0
        | bits4 s1 s0 s1 s1 => bits8 s1 s0 s1 s1 s0 s0 s1 s1
        | bits4 s1 s1 s0 s0 => bits8 s0 s0 s1 s0 s1 s0 s0 s1
        | bits4 s1 s1 s0 s1 => bits8 s1 s1 s1 s0 s0 s0 s1 s1
        | bits4 s1 s1 s1 s0 => bits8 s0 s0 s1 s0 s1 s1 s1 s1
        | bits4 s1 s1 s1 s1 => bits8 s1 s0 s0 s0 s0 s1 s0 s0
      end
    | bits4 s0 s1 s0 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s1 s0 s1 s0 s0 s1 s1
        | bits4 s0 s0 s0 s1 => bits8 s1 s1 s0 s1 s0 s0 s0 s1
        | bits4 s0 s0 s1 s0 => bits8 s0 s0 s0 s0 s0 s0 s0 s0
        | bits4 s0 s0 s1 s1 => bits8 s1 s1 s1 s0 s1 s1 s0 s1
        | bits4 s0 s1 s0 s0 => bits8 s0 s0 s1 s0 s0 s0 s0 s0
        | bits4 s0 s1 s0 s1 => bits8 s1 s1 s1 s1 s1 s1 s0 s0
        | bits4 s0 s1 s1 s0 => bits8 s1 s0 s1 s1 s0 s0 s0 s1
        | bits4 s0 s1 s1 s1 => bits8 s0 s1 s0 s1 s1 s0 s1 s1
        | bits4 s1 s0 s0 s0 => bits8 s0 s1 s1 s0 s1 s0 s1 s0
        | bits4 s1 s0 s0 s1 => bits8 s1 s1 s0 s0 s1 s0 s1 s1
        | bits4 s1 s0 s1 s0 => bits8 s1 s0 s1 s1 s1 s1 s1 s0
        | bits4 s1 s0 s1 s1 => bits8 s0 s0 s1 s1 s1 s0 s0 s1
        | bits4 s1 s1 s0 s0 => bits8 s0 s1 s0 s0 s1 s0 s1 s0
        | bits4 s1 s1 s0 s1 => bits8 s0 s1 s0 s0 s1 s1 s0 s0
        | bits4 s1 s1 s1 s0 => bits8 s0 s1 s0 s1 s1 s0 s0 s0
        | bits4 s1 s1 s1 s1 => bits8 s1 s1 s0 s0 s1 s1 s1 s1
      end
    | bits4 s0 s1 s1 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s1 s1 s0 s1 s0 s0 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s1 s1 s1 s0 s1 s1 s1 s1
        | bits4 s0 s0 s1 s0 => bits8 s1 s0 s1 s0 s1 s0 s1 s0
        | bits4 s0 s0 s1 s1 => bits8 s1 s1 s1 s1 s1 s0 s1 s1
        | bits4 s0 s1 s0 s0 => bits8 s0 s1 s0 s0 s0 s0 s1 s1
        | bits4 s0 s1 s0 s1 => bits8 s0 s1 s0 s0 s1 s1 s0 s1
        | bits4 s0 s1 s1 s0 => bits8 s0 s0 s1 s1 s0 s0 s1 s1
        | bits4 s0 s1 s1 s1 => bits8 s1 s0 s0 s0 s0 s1 s0 s1
        | bits4 s1 s0 s0 s0 => bits8 s0 s1 s0 s0 s0 s1 s0 s1
        | bits4 s1 s0 s0 s1 => bits8 s1 s1 s1 s1 s1 s0 s0 s1
        | bits4 s1 s0 s1 s0 => bits8 s0 s0 s0 s0 s0 s0 s1 s0
        | bits4 s1 s0 s1 s1 => bits8 s0 s1 s1 s1 s1 s1 s1 s1
        | bits4 s1 s1 s0 s0 => bits8 s0 s1 s0 s1 s0 s0 s0 s0
        | bits4 s1 s1 s0 s1 => bits8 s0 s0 s1 s1 s1 s1 s0 s0
        | bits4 s1 s1 s1 s0 => bits8 s1 s0 s0 s1 s1 s1 s1 s1
        | bits4 s1 s1 s1 s1 => bits8 s1 s0 s1 s0 s1 s0 s0 s0
      end
    | bits4 s0 s1 s1 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s1 s0 s1 s0 s0 s0 s1
        | bits4 s0 s0 s0 s1 => bits8 s1 s0 s1 s0 s0 s0 s1 s1
        | bits4 s0 s0 s1 s0 => bits8 s0 s1 s0 s0 s0 s0 s0 s0
        | bits4 s0 s0 s1 s1 => bits8 s1 s0 s0 s0 s1 s1 s1 s1
        | bits4 s0 s1 s0 s0 => bits8 s1 s0 s0 s1 s0 s0 s1 s0
        | bits4 s0 s1 s0 s1 => bits8 s1 s0 s0 s1 s1 s1 s0 s1
        | bits4 s0 s1 s1 s0 => bits8 s0 s0 s1 s1 s1 s0 s0 s0
        | bits4 s0 s1 s1 s1 => bits8 s1 s1 s1 s1 s0 s1 s0 s1
        | bits4 s1 s0 s0 s0 => bits8 s1 s0 s1 s1 s1 s1 s0 s0
        | bits4 s1 s0 s0 s1 => bits8 s1 s0 s1 s1 s0 s1 s1 s0
        | bits4 s1 s0 s1 s0 => bits8 s1 s1 s0 s1 s1 s0 s1 s0
        | bits4 s1 s0 s1 s1 => bits8 s0 s0 s1 s0 s0 s0 s0 s1
        | bits4 s1 s1 s0 s0 => bits8 s0 s0 s0 s1 s0 s0 s0 s0
        | bits4 s1 s1 s0 s1 => bits8 s1 s1 s1 s1 s1 s1 s1 s1
        | bits4 s1 s1 s1 s0 => bits8 s1 s1 s1 s1 s0 s0 s1 s1
        | bits4 s1 s1 s1 s1 => bits8 s1 s1 s0 s1 s0 s0 s1 s0
      end
    | bits4 s1 s0 s0 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s1 s1 s0 s0 s1 s1 s0 s1
        | bits4 s0 s0 s0 s1 => bits8 s0 s0 s0 s0 s1 s1 s0 s0
        | bits4 s0 s0 s1 s0 => bits8 s0 s0 s0 s1 s0 s0 s1 s1
        | bits4 s0 s0 s1 s1 => bits8 s1 s1 s1 s0 s1 s1 s0 s0
        | bits4 s0 s1 s0 s0 => bits8 s0 s1 s0 s1 s1 s1 s1 s1
        | bits4 s0 s1 s0 s1 => bits8 s1 s0 s0 s1 s0 s1 s1 s1
        | bits4 s0 s1 s1 s0 => bits8 s0 s1 s0 s0 s0 s1 s0 s0
        | bits4 s0 s1 s1 s1 => bits8 s0 s0 s0 s1 s0 s1 s1 s1
        | bits4 s1 s0 s0 s0 => bits8 s1 s1 s0 s0 s0 s1 s0 s0
        | bits4 s1 s0 s0 s1 => bits8 s1 s0 s1 s0 s0 s1 s1 s1
        | bits4 s1 s0 s1 s0 => bits8 s0 s1 s1 s1 s1 s1 s1 s0
        | bits4 s1 s0 s1 s1 => bits8 s0 s0 s1 s1 s1 s1 s0 s1
        | bits4 s1 s1 s0 s0 => bits8 s0 s1 s1 s0 s0 s1 s0 s0
        | bits4 s1 s1 s0 s1 => bits8 s0 s1 s0 s1 s1 s1 s0 s1
        | bits4 s1 s1 s1 s0 => bits8 s0 s0 s0 s1 s1 s0 s0 s1
        | bits4 s1 s1 s1 s1 => bits8 s0 s1 s1 s1 s0 s0 s1 s1
      end
    | bits4 s1 s0 s0 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s1 s1 s0 s0 s0 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s1 s0 s0 s0 s0 s0 s0 s1
        | bits4 s0 s0 s1 s0 => bits8 s0 s1 s0 s0 s1 s1 s1 s1
        | bits4 s0 s0 s1 s1 => bits8 s1 s1 s0 s1 s1 s1 s0 s0
        | bits4 s0 s1 s0 s0 => bits8 s0 s0 s1 s0 s0 s0 s1 s0
        | bits4 s0 s1 s0 s1 => bits8 s0 s0 s1 s0 s1 s0 s1 s0
        | bits4 s0 s1 s1 s0 => bits8 s1 s0 s0 s1 s0 s0 s0 s0
        | bits4 s0 s1 s1 s1 => bits8 s1 s0 s0 s0 s1 s0 s0 s0
        | bits4 s1 s0 s0 s0 => bits8 s0 s1 s0 s0 s0 s1 s1 s0
        | bits4 s1 s0 s0 s1 => bits8 s1 s1 s1 s0 s1 s1 s1 s0
        | bits4 s1 s0 s1 s0 => bits8 s1 s0 s1 s1 s1 s0 s0 s0
        | bits4 s1 s0 s1 s1 => bits8 s0 s0 s0 s1 s0 s1 s0 s0
        | bits4 s1 s1 s0 s0 => bits8 s1 s1 s0 s1 s1 s1 s1 s0
        | bits4 s1 s1 s0 s1 => bits8 s0 s1 s0 s1 s1 s1 s1 s0
        | bits4 s1 s1 s1 s0 => bits8 s0 s0 s0 s0 s1 s0 s1 s1
        | bits4 s1 s1 s1 s1 => bits8 s1 s1 s0 s1 s1 s0 s1 s1
      end
    | bits4 s1 s0 s1 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s1 s1 s1 s0 s0 s0 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s0 s0 s1 s1 s0 s0 s1 s0
        | bits4 s0 s0 s1 s0 => bits8 s0 s0 s1 s1 s1 s0 s1 s0
        | bits4 s0 s0 s1 s1 => bits8 s0 s0 s0 s0 s1 s0 s1 s0
        | bits4 s0 s1 s0 s0 => bits8 s0 s1 s0 s0 s1 s0 s0 s1
        | bits4 s0 s1 s0 s1 => bits8 s0 s0 s0 s0 s0 s1 s1 s0
        | bits4 s0 s1 s1 s0 => bits8 s0 s0 s1 s0 s0 s1 s0 s0
        | bits4 s0 s1 s1 s1 => bits8 s0 s1 s0 s1 s1 s1 s0 s0
        | bits4 s1 s0 s0 s0 => bits8 s1 s1 s0 s0 s0 s0 s1 s0
        | bits4 s1 s0 s0 s1 => bits8 s1 s1 s0 s1 s0 s0 s1 s1
        | bits4 s1 s0 s1 s0 => bits8 s1 s0 s1 s0 s1 s1 s0 s0
        | bits4 s1 s0 s1 s1 => bits8 s0 s1 s1 s0 s0 s0 s1 s0
        | bits4 s1 s1 s0 s0 => bits8 s1 s0 s0 s1 s0 s0 s0 s1
        | bits4 s1 s1 s0 s1 => bits8 s1 s0 s0 s1 s0 s1 s0 s1
        | bits4 s1 s1 s1 s0 => bits8 s1 s1 s1 s0 s0 s1 s0 s0
        | bits4 s1 s1 s1 s1 => bits8 s0 s1 s1 s1 s1 s0 s0 s1
      end
    | bits4 s1 s0 s1 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s1 s1 s1 s0 s0 s1 s1 s1
        | bits4 s0 s0 s0 s1 => bits8 s1 s1 s0 s0 s1 s0 s0 s0
        | bits4 s0 s0 s1 s0 => bits8 s0 s0 s1 s1 s0 s1 s1 s1
        | bits4 s0 s0 s1 s1 => bits8 s0 s1 s1 s0 s1 s1 s0 s1
        | bits4 s0 s1 s0 s0 => bits8 s1 s0 s0 s0 s1 s1 s0 s1
        | bits4 s0 s1 s0 s1 => bits8 s1 s1 s0 s1 s0 s1 s0 s1
        | bits4 s0 s1 s1 s0 => bits8 s0 s1 s0 s0 s1 s1 s1 s0
        | bits4 s0 s1 s1 s1 => bits8 s1 s0 s1 s0 s1 s0 s0 s1
        | bits4 s1 s0 s0 s0 => bits8 s0 s1 s1 s0 s1 s1 s0 s0
        | bits4 s1 s0 s0 s1 => bits8 s0 s1 s0 s1 s0 s1 s1 s0
        | bits4 s1 s0 s1 s0 => bits8 s1 s1 s1 s1 s0 s1 s0 s0
        | bits4 s1 s0 s1 s1 => bits8 s1 s1 s1 s0 s1 s0 s1 s0
        | bits4 s1 s1 s0 s0 => bits8 s0 s1 s1 s0 s0 s1 s0 s1
        | bits4 s1 s1 s0 s1 => bits8 s0 s1 s1 s1 s1 s0 s1 s0
        | bits4 s1 s1 s1 s0 => bits8 s1 s0 s1 s0 s1 s1 s1 s0
        | bits4 s1 s1 s1 s1 => bits8 s0 s0 s0 s0 s1 s0 s0 s0
      end
    | bits4 s1 s1 s0 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s1 s0 s1 s1 s1 s0 s1 s0
        | bits4 s0 s0 s0 s1 => bits8 s0 s1 s1 s1 s1 s0 s0 s0
        | bits4 s0 s0 s1 s0 => bits8 s0 s0 s1 s0 s0 s1 s0 s1
        | bits4 s0 s0 s1 s1 => bits8 s0 s0 s1 s0 s1 s1 s1 s0
        | bits4 s0 s1 s0 s0 => bits8 s0 s0 s0 s1 s1 s1 s0 s0
        | bits4 s0 s1 s0 s1 => bits8 s1 s0 s1 s0 s0 s1 s1 s0
        | bits4 s0 s1 s1 s0 => bits8 s1 s0 s1 s1 s0 s1 s0 s0
        | bits4 s0 s1 s1 s1 => bits8 s1 s1 s0 s0 s0 s1 s1 s0
        | bits4 s1 s0 s0 s0 => bits8 s1 s1 s1 s0 s1 s0 s0 s0
        | bits4 s1 s0 s0 s1 => bits8 s1 s1 s0 s1 s1 s1 s0 s1
        | bits4 s1 s0 s1 s0 => bits8 s0 s1 s1 s1 s0 s1 s0 s0
        | bits4 s1 s0 s1 s1 => bits8 s0 s0 s0 s1 s1 s1 s1 s1
        | bits4 s1 s1 s0 s0 => bits8 s0 s1 s0 s0 s1 s0 s1 s1
        | bits4 s1 s1 s0 s1 => bits8 s1 s0 s1 s1 s1 s1 s0 s1
        | bits4 s1 s1 s1 s0 => bits8 s1 s0 s0 s0 s1 s0 s1 s1
        | bits4 s1 s1 s1 s1 => bits8 s1 s0 s0 s0 s1 s0 s1 s0
      end
    | bits4 s1 s1 s0 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s1 s1 s1 s0 s0 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s0 s0 s1 s1 s1 s1 s1 s0
        | bits4 s0 s0 s1 s0 => bits8 s1 s0 s1 s1 s0 s1 s0 s1
        | bits4 s0 s0 s1 s1 => bits8 s0 s1 s1 s0 s0 s1 s1 s0
        | bits4 s0 s1 s0 s0 => bits8 s0 s1 s0 s0 s1 s0 s0 s0
        | bits4 s0 s1 s0 s1 => bits8 s0 s0 s0 s0 s0 s0 s1 s1
        | bits4 s0 s1 s1 s0 => bits8 s1 s1 s1 s1 s0 s1 s1 s0
        | bits4 s0 s1 s1 s1 => bits8 s0 s0 s0 s0 s1 s1 s1 s0
        | bits4 s1 s0 s0 s0 => bits8 s0 s1 s1 s0 s0 s0 s0 s1
        | bits4 s1 s0 s0 s1 => bits8 s0 s0 s1 s1 s0 s1 s0 s1
        | bits4 s1 s0 s1 s0 => bits8 s0 s1 s0 s1 s0 s1 s1 s1
        | bits4 s1 s0 s1 s1 => bits8 s1 s0 s1 s1 s1 s0 s0 s1
        | bits4 s1 s1 s0 s0 => bits8 s1 s0 s0 s0 s0 s1 s1 s0
        | bits4 s1 s1 s0 s1 => bits8 s1 s1 s0 s0 s0 s0 s0 s1
        | bits4 s1 s1 s1 s0 => bits8 s0 s0 s0 s1 s1 s1 s0 s1
        | bits4 s1 s1 s1 s1 => bits8 s1 s0 s0 s1 s1 s1 s1 s0
      end
    | bits4 s1 s1 s1 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s1 s1 s1 s0 s0 s0 s0 s1
        | bits4 s0 s0 s0 s1 => bits8 s1 s1 s1 s1 s1 s0 s0 s0
        | bits4 s0 s0 s1 s0 => bits8 s1 s0 s0 s1 s1 s0 s0 s0
        | bits4 s0 s0 s1 s1 => bits8 s0 s0 s0 s1 s0 s0 s0 s1
        | bits4 s0 s1 s0 s0 => bits8 s0 s1 s1 s0 s1 s0 s0 s1
        | bits4 s0 s1 s0 s1 => bits8 s1 s1 s0 s1 s1 s0 s0 s1
        | bits4 s0 s1 s1 s0 => bits8 s1 s0 s0 s0 s1 s1 s1 s0
        | bits4 s0 s1 s1 s1 => bits8 s1 s0 s0 s1 s0 s1 s0 s0
        | bits4 s1 s0 s0 s0 => bits8 s1 s0 s0 s1 s1 s0 s1 s1
        | bits4 s1 s0 s0 s1 => bits8 s0 s0 s0 s1 s1 s1 s1 s0
        | bits4 s1 s0 s1 s0 => bits8 s1 s0 s0 s0 s0 s1 s1 s1
        | bits4 s1 s0 s1 s1 => bits8 s1 s1 s1 s0 s1 s0 s0 s1
        | bits4 s1 s1 s0 s0 => bits8 s1 s1 s0 s0 s1 s1 s1 s0
        | bits4 s1 s1 s0 s1 => bits8 s0 s1 s0 s1 s0 s1 s0 s1
        | bits4 s1 s1 s1 s0 => bits8 s0 s0 s1 s0 s1 s0 s0 s0
        | bits4 s1 s1 s1 s1 => bits8 s1 s1 s0 s1 s1 s1 s1 s1
      end
    | bits4 s1 s1 s1 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s1 s0 s0 s0 s1 s1 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s1 s0 s1 s0 s0 s0 s0 s1
        | bits4 s0 s0 s1 s0 => bits8 s1 s0 s0 s0 s1 s0 s0 s1
        | bits4 s0 s0 s1 s1 => bits8 s0 s0 s0 s0 s1 s1 s0 s1
        | bits4 s0 s1 s0 s0 => bits8 s1 s0 s1 s1 s1 s1 s1 s1
        | bits4 s0 s1 s0 s1 => bits8 s1 s1 s1 s0 s0 s1 s1 s0
        | bits4 s0 s1 s1 s0 => bits8 s0 s1 s0 s0 s0 s0 s1 s0
        | bits4 s0 s1 s1 s1 => bits8 s0 s1 s1 s0 s1 s0 s0 s0
        | bits4 s1 s0 s0 s0 => bits8 s0 s1 s0 s0 s0 s0 s0 s1
        | bits4 s1 s0 s0 s1 => bits8 s1 s0 s0 s1 s1 s0 s0 s1
        | bits4 s1 s0 s1 s0 => bits8 s0 s0 s1 s0 s1 s1 s0 s1
        | bits4 s1 s0 s1 s1 => bits8 s0 s0 s0 s0 s1 s1 s1 s1
        | bits4 s1 s1 s0 s0 => bits8 s1 s0 s1 s1 s0 s0 s0 s0
        | bits4 s1 s1 s0 s1 => bits8 s0 s1 s0 s1 s0 s1 s0 s0
        | bits4 s1 s1 s1 s0 => bits8 s1 s0 s1 s1 s1 s0 s1 s1
        | bits4 s1 s1 s1 s1 => bits8 s0 s0 s0 s1 s0 s1 s1 s0
      end
  end.

Definition inv_s_box (b: byte) : byte :=
  match (ms_nibble b) with
    | bits4 s0 s0 s0 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s1 s0 s1 s0 s0 s1 s0
        | bits4 s0 s0 s0 s1 => bits8 s0 s0 s0 s0 s1 s0 s0 s1
        | bits4 s0 s0 s1 s0 => bits8 s0 s1 s1 s0 s1 s0 s1 s0
        | bits4 s0 s0 s1 s1 => bits8 s1 s1 s0 s1 s0 s1 s0 s1
        | bits4 s0 s1 s0 s0 => bits8 s0 s0 s1 s1 s0 s0 s0 s0
        | bits4 s0 s1 s0 s1 => bits8 s0 s0 s1 s1 s0 s1 s1 s0
        | bits4 s0 s1 s1 s0 => bits8 s1 s0 s1 s0 s0 s1 s0 s1
        | bits4 s0 s1 s1 s1 => bits8 s0 s0 s1 s1 s1 s0 s0 s0
        | bits4 s1 s0 s0 s0 => bits8 s1 s0 s1 s1 s1 s1 s1 s1
        | bits4 s1 s0 s0 s1 => bits8 s0 s1 s0 s0 s0 s0 s0 s0
        | bits4 s1 s0 s1 s0 => bits8 s1 s0 s1 s0 s0 s0 s1 s1
        | bits4 s1 s0 s1 s1 => bits8 s1 s0 s0 s1 s1 s1 s1 s0
        | bits4 s1 s1 s0 s0 => bits8 s1 s0 s0 s0 s0 s0 s0 s1
        | bits4 s1 s1 s0 s1 => bits8 s1 s1 s1 s1 s0 s0 s1 s1
        | bits4 s1 s1 s1 s0 => bits8 s1 s1 s0 s1 s0 s1 s1 s1
        | bits4 s1 s1 s1 s1 => bits8 s1 s1 s1 s1 s1 s0 s1 s1
      end
    | bits4 s0 s0 s0 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s1 s1 s1 s1 s1 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s1 s1 s1 s0 s0 s0 s1 s1
        | bits4 s0 s0 s1 s0 => bits8 s0 s0 s1 s1 s1 s0 s0 s1
        | bits4 s0 s0 s1 s1 => bits8 s1 s0 s0 s0 s0 s0 s1 s0
        | bits4 s0 s1 s0 s0 => bits8 s1 s0 s0 s1 s1 s0 s1 s1
        | bits4 s0 s1 s0 s1 => bits8 s0 s0 s1 s0 s1 s1 s1 s1
        | bits4 s0 s1 s1 s0 => bits8 s1 s1 s1 s1 s1 s1 s1 s1
        | bits4 s0 s1 s1 s1 => bits8 s1 s0 s0 s0 s0 s1 s1 s1
        | bits4 s1 s0 s0 s0 => bits8 s0 s0 s1 s1 s0 s1 s0 s0
        | bits4 s1 s0 s0 s1 => bits8 s1 s0 s0 s0 s1 s1 s1 s0
        | bits4 s1 s0 s1 s0 => bits8 s0 s1 s0 s0 s0 s0 s1 s1
        | bits4 s1 s0 s1 s1 => bits8 s0 s1 s0 s0 s0 s1 s0 s0
        | bits4 s1 s1 s0 s0 => bits8 s1 s1 s0 s0 s0 s1 s0 s0
        | bits4 s1 s1 s0 s1 => bits8 s1 s1 s0 s1 s1 s1 s1 s0
        | bits4 s1 s1 s1 s0 => bits8 s1 s1 s1 s0 s1 s0 s0 s1
        | bits4 s1 s1 s1 s1 => bits8 s1 s1 s0 s0 s1 s0 s1 s1
      end
    | bits4 s0 s0 s1 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s1 s0 s1 s0 s1 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s0 s1 s1 s1 s1 s0 s1 s1
        | bits4 s0 s0 s1 s0 => bits8 s1 s0 s0 s1 s0 s1 s0 s0
        | bits4 s0 s0 s1 s1 => bits8 s0 s0 s1 s1 s0 s0 s1 s0
        | bits4 s0 s1 s0 s0 => bits8 s1 s0 s1 s0 s0 s1 s1 s0
        | bits4 s0 s1 s0 s1 => bits8 s1 s1 s0 s0 s0 s0 s1 s0
        | bits4 s0 s1 s1 s0 => bits8 s0 s0 s1 s0 s0 s0 s1 s1
        | bits4 s0 s1 s1 s1 => bits8 s0 s0 s1 s1 s1 s1 s0 s1
        | bits4 s1 s0 s0 s0 => bits8 s1 s1 s1 s0 s1 s1 s1 s0
        | bits4 s1 s0 s0 s1 => bits8 s0 s1 s0 s0 s1 s1 s0 s0
        | bits4 s1 s0 s1 s0 => bits8 s1 s0 s0 s1 s0 s1 s0 s1
        | bits4 s1 s0 s1 s1 => bits8 s0 s0 s0 s0 s1 s0 s1 s1
        | bits4 s1 s1 s0 s0 => bits8 s0 s1 s0 s0 s0 s0 s1 s0
        | bits4 s1 s1 s0 s1 => bits8 s1 s1 s1 s1 s1 s0 s1 s0
        | bits4 s1 s1 s1 s0 => bits8 s1 s1 s0 s0 s0 s0 s1 s1
        | bits4 s1 s1 s1 s1 => bits8 s0 s1 s0 s0 s1 s1 s1 s0
      end
    | bits4 s0 s0 s1 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s0 s0 s0 s1 s0 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s0 s0 s1 s0 s1 s1 s1 s0
        | bits4 s0 s0 s1 s0 => bits8 s1 s0 s1 s0 s0 s0 s0 s1
        | bits4 s0 s0 s1 s1 => bits8 s0 s1 s1 s0 s0 s1 s1 s0
        | bits4 s0 s1 s0 s0 => bits8 s0 s0 s1 s0 s1 s0 s0 s0
        | bits4 s0 s1 s0 s1 => bits8 s1 s1 s0 s1 s1 s0 s0 s1
        | bits4 s0 s1 s1 s0 => bits8 s0 s0 s1 s0 s0 s1 s0 s0
        | bits4 s0 s1 s1 s1 => bits8 s1 s0 s1 s1 s0 s0 s1 s0
        | bits4 s1 s0 s0 s0 => bits8 s0 s1 s1 s1 s0 s1 s1 s0
        | bits4 s1 s0 s0 s1 => bits8 s0 s1 s0 s1 s1 s0 s1 s1
        | bits4 s1 s0 s1 s0 => bits8 s1 s0 s1 s0 s0 s0 s1 s0
        | bits4 s1 s0 s1 s1 => bits8 s0 s1 s0 s0 s1 s0 s0 s1
        | bits4 s1 s1 s0 s0 => bits8 s0 s1 s1 s0 s1 s1 s0 s1
        | bits4 s1 s1 s0 s1 => bits8 s1 s0 s0 s0 s1 s0 s1 s1
        | bits4 s1 s1 s1 s0 => bits8 s1 s1 s0 s1 s0 s0 s0 s1
        | bits4 s1 s1 s1 s1 => bits8 s0 s0 s1 s0 s0 s1 s0 s1
      end
    | bits4 s0 s1 s0 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s1 s1 s1 s0 s0 s1 s0
        | bits4 s0 s0 s0 s1 => bits8 s1 s1 s1 s1 s1 s0 s0 s0
        | bits4 s0 s0 s1 s0 => bits8 s1 s1 s1 s1 s0 s1 s1 s0
        | bits4 s0 s0 s1 s1 => bits8 s0 s1 s1 s0 s0 s1 s0 s0
        | bits4 s0 s1 s0 s0 => bits8 s1 s0 s0 s0 s0 s1 s1 s0
        | bits4 s0 s1 s0 s1 => bits8 s0 s1 s1 s0 s1 s0 s0 s0
        | bits4 s0 s1 s1 s0 => bits8 s1 s0 s0 s1 s1 s0 s0 s0
        | bits4 s0 s1 s1 s1 => bits8 s0 s0 s0 s1 s0 s1 s1 s0
        | bits4 s1 s0 s0 s0 => bits8 s1 s1 s0 s1 s0 s1 s0 s0
        | bits4 s1 s0 s0 s1 => bits8 s1 s0 s1 s0 s0 s1 s0 s0
        | bits4 s1 s0 s1 s0 => bits8 s0 s1 s0 s1 s1 s1 s0 s0
        | bits4 s1 s0 s1 s1 => bits8 s1 s1 s0 s0 s1 s1 s0 s0
        | bits4 s1 s1 s0 s0 => bits8 s0 s1 s0 s1 s1 s1 s0 s1
        | bits4 s1 s1 s0 s1 => bits8 s0 s1 s1 s0 s0 s1 s0 s1
        | bits4 s1 s1 s1 s0 => bits8 s1 s0 s1 s1 s0 s1 s1 s0
        | bits4 s1 s1 s1 s1 => bits8 s1 s0 s0 s1 s0 s0 s1 s0
      end
    | bits4 s0 s1 s0 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s1 s1 s0 s1 s1 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s0 s1 s1 s1 s0 s0 s0 s0
        | bits4 s0 s0 s1 s0 => bits8 s0 s1 s0 s0 s1 s0 s0 s0
        | bits4 s0 s0 s1 s1 => bits8 s0 s1 s0 s1 s0 s0 s0 s0
        | bits4 s0 s1 s0 s0 => bits8 s1 s1 s1 s1 s1 s1 s0 s1
        | bits4 s0 s1 s0 s1 => bits8 s1 s1 s1 s0 s1 s1 s0 s1
        | bits4 s0 s1 s1 s0 => bits8 s1 s0 s1 s1 s1 s0 s0 s1
        | bits4 s0 s1 s1 s1 => bits8 s1 s1 s0 s1 s1 s0 s1 s0
        | bits4 s1 s0 s0 s0 => bits8 s0 s1 s0 s1 s1 s1 s1 s0
        | bits4 s1 s0 s0 s1 => bits8 s0 s0 s0 s1 s0 s1 s0 s1
        | bits4 s1 s0 s1 s0 => bits8 s0 s1 s0 s0 s0 s1 s1 s0
        | bits4 s1 s0 s1 s1 => bits8 s0 s1 s0 s1 s0 s1 s1 s1
        | bits4 s1 s1 s0 s0 => bits8 s1 s0 s1 s0 s0 s1 s1 s1
        | bits4 s1 s1 s0 s1 => bits8 s1 s0 s0 s0 s1 s1 s0 s1
        | bits4 s1 s1 s1 s0 => bits8 s1 s0 s0 s1 s1 s1 s0 s1
        | bits4 s1 s1 s1 s1 => bits8 s1 s0 s0 s0 s0 s1 s0 s0
      end
    | bits4 s0 s1 s1 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s1 s0 s0 s1 s0 s0 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s1 s1 s0 s1 s1 s0 s0 s0
        | bits4 s0 s0 s1 s0 => bits8 s1 s0 s1 s0 s1 s0 s1 s1
        | bits4 s0 s0 s1 s1 => bits8 s0 s0 s0 s0 s0 s0 s0 s0
        | bits4 s0 s1 s0 s0 => bits8 s1 s0 s0 s0 s1 s1 s0 s0
        | bits4 s0 s1 s0 s1 => bits8 s1 s0 s1 s1 s1 s1 s0 s0
        | bits4 s0 s1 s1 s0 => bits8 s1 s1 s0 s1 s0 s0 s1 s1
        | bits4 s0 s1 s1 s1 => bits8 s0 s0 s0 s0 s1 s0 s1 s0
        | bits4 s1 s0 s0 s0 => bits8 s1 s1 s1 s1 s0 s1 s1 s1
        | bits4 s1 s0 s0 s1 => bits8 s1 s1 s1 s0 s0 s1 s0 s0
        | bits4 s1 s0 s1 s0 => bits8 s0 s1 s0 s1 s1 s0 s0 s0
        | bits4 s1 s0 s1 s1 => bits8 s0 s0 s0 s0 s0 s1 s0 s1
        | bits4 s1 s1 s0 s0 => bits8 s1 s0 s1 s1 s1 s0 s0 s0
        | bits4 s1 s1 s0 s1 => bits8 s1 s0 s1 s1 s0 s0 s1 s1
        | bits4 s1 s1 s1 s0 => bits8 s0 s1 s0 s0 s0 s1 s0 s1
        | bits4 s1 s1 s1 s1 => bits8 s0 s0 s0 s0 s0 s1 s1 s0
      end
    | bits4 s0 s1 s1 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s1 s1 s0 s1 s0 s0 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s0 s0 s1 s0 s1 s1 s0 s0
        | bits4 s0 s0 s1 s0 => bits8 s0 s0 s0 s1 s1 s1 s1 s0
        | bits4 s0 s0 s1 s1 => bits8 s1 s0 s0 s0 s1 s1 s1 s1
        | bits4 s0 s1 s0 s0 => bits8 s1 s1 s0 s0 s1 s0 s1 s0
        | bits4 s0 s1 s0 s1 => bits8 s0 s0 s1 s1 s1 s1 s1 s1
        | bits4 s0 s1 s1 s0 => bits8 s0 s0 s0 s0 s1 s1 s1 s1
        | bits4 s0 s1 s1 s1 => bits8 s0 s0 s0 s0 s0 s0 s1 s0
        | bits4 s1 s0 s0 s0 => bits8 s1 s1 s0 s0 s0 s0 s0 s1
        | bits4 s1 s0 s0 s1 => bits8 s1 s0 s1 s0 s1 s1 s1 s1
        | bits4 s1 s0 s1 s0 => bits8 s1 s0 s1 s1 s1 s1 s0 s1
        | bits4 s1 s0 s1 s1 => bits8 s0 s0 s0 s0 s0 s0 s1 s1
        | bits4 s1 s1 s0 s0 => bits8 s0 s0 s0 s0 s0 s0 s0 s1
        | bits4 s1 s1 s0 s1 => bits8 s0 s0 s0 s1 s0 s0 s1 s1
        | bits4 s1 s1 s1 s0 => bits8 s1 s0 s0 s0 s1 s0 s1 s0
        | bits4 s1 s1 s1 s1 => bits8 s0 s1 s1 s0 s1 s0 s1 s1
      end
    | bits4 s1 s0 s0 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s0 s1 s1 s1 s0 s1 s0
        | bits4 s0 s0 s0 s1 => bits8 s1 s0 s0 s1 s0 s0 s0 s1
        | bits4 s0 s0 s1 s0 => bits8 s0 s0 s0 s1 s0 s0 s0 s1
        | bits4 s0 s0 s1 s1 => bits8 s0 s1 s0 s0 s0 s0 s0 s1
        | bits4 s0 s1 s0 s0 => bits8 s0 s1 s0 s0 s1 s1 s1 s1
        | bits4 s0 s1 s0 s1 => bits8 s0 s1 s1 s0 s0 s1 s1 s1
        | bits4 s0 s1 s1 s0 => bits8 s1 s1 s0 s1 s1 s1 s0 s0
        | bits4 s0 s1 s1 s1 => bits8 s1 s1 s1 s0 s1 s0 s1 s0
        | bits4 s1 s0 s0 s0 => bits8 s1 s0 s0 s1 s0 s1 s1 s1
        | bits4 s1 s0 s0 s1 => bits8 s1 s1 s1 s1 s0 s0 s1 s0
        | bits4 s1 s0 s1 s0 => bits8 s1 s1 s0 s0 s1 s1 s1 s1
        | bits4 s1 s0 s1 s1 => bits8 s1 s1 s0 s0 s1 s1 s1 s0
        | bits4 s1 s1 s0 s0 => bits8 s1 s1 s1 s1 s0 s0 s0 s0
        | bits4 s1 s1 s0 s1 => bits8 s1 s0 s1 s1 s0 s1 s0 s0
        | bits4 s1 s1 s1 s0 => bits8 s1 s1 s1 s0 s0 s1 s1 s0
        | bits4 s1 s1 s1 s1 => bits8 s0 s1 s1 s1 s0 s0 s1 s1
      end
    | bits4 s1 s0 s0 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s1 s0 s0 s1 s0 s1 s1 s0
        | bits4 s0 s0 s0 s1 => bits8 s1 s0 s1 s0 s1 s1 s0 s0
        | bits4 s0 s0 s1 s0 => bits8 s0 s1 s1 s1 s0 s1 s0 s0
        | bits4 s0 s0 s1 s1 => bits8 s0 s0 s1 s0 s0 s0 s1 s0
        | bits4 s0 s1 s0 s0 => bits8 s1 s1 s1 s0 s0 s1 s1 s1
        | bits4 s0 s1 s0 s1 => bits8 s1 s0 s1 s0 s1 s1 s0 s1
        | bits4 s0 s1 s1 s0 => bits8 s0 s0 s1 s1 s0 s1 s0 s1
        | bits4 s0 s1 s1 s1 => bits8 s1 s0 s0 s0 s0 s1 s0 s1
        | bits4 s1 s0 s0 s0 => bits8 s1 s1 s1 s0 s0 s0 s1 s0
        | bits4 s1 s0 s0 s1 => bits8 s1 s1 s1 s1 s1 s0 s0 s1
        | bits4 s1 s0 s1 s0 => bits8 s0 s0 s1 s1 s0 s1 s1 s1
        | bits4 s1 s0 s1 s1 => bits8 s1 s1 s1 s0 s1 s0 s0 s0
        | bits4 s1 s1 s0 s0 => bits8 s0 s0 s0 s1 s1 s1 s0 s0
        | bits4 s1 s1 s0 s1 => bits8 s0 s1 s1 s1 s0 s1 s0 s1
        | bits4 s1 s1 s1 s0 => bits8 s1 s1 s0 s1 s1 s1 s1 s1
        | bits4 s1 s1 s1 s1 => bits8 s0 s1 s1 s0 s1 s1 s1 s0
      end
    | bits4 s1 s0 s1 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s1 s0 s0 s0 s1 s1 s1
        | bits4 s0 s0 s0 s1 => bits8 s1 s1 s1 s1 s0 s0 s0 s1
        | bits4 s0 s0 s1 s0 => bits8 s0 s0 s0 s1 s1 s0 s1 s0
        | bits4 s0 s0 s1 s1 => bits8 s0 s1 s1 s1 s0 s0 s0 s1
        | bits4 s0 s1 s0 s0 => bits8 s0 s0 s0 s1 s1 s1 s0 s1
        | bits4 s0 s1 s0 s1 => bits8 s0 s0 s1 s0 s1 s0 s0 s1
        | bits4 s0 s1 s1 s0 => bits8 s1 s1 s0 s0 s0 s1 s0 s1
        | bits4 s0 s1 s1 s1 => bits8 s1 s0 s0 s0 s1 s0 s0 s1
        | bits4 s1 s0 s0 s0 => bits8 s0 s1 s1 s0 s1 s1 s1 s1
        | bits4 s1 s0 s0 s1 => bits8 s1 s0 s1 s1 s0 s1 s1 s1
        | bits4 s1 s0 s1 s0 => bits8 s0 s1 s1 s0 s0 s0 s1 s0
        | bits4 s1 s0 s1 s1 => bits8 s0 s0 s0 s0 s1 s1 s1 s0
        | bits4 s1 s1 s0 s0 => bits8 s1 s0 s1 s0 s1 s0 s1 s0
        | bits4 s1 s1 s0 s1 => bits8 s0 s0 s0 s1 s1 s0 s0 s0
        | bits4 s1 s1 s1 s0 => bits8 s1 s0 s1 s1 s1 s1 s1 s0
        | bits4 s1 s1 s1 s1 => bits8 s0 s0 s0 s1 s1 s0 s1 s1
      end
    | bits4 s1 s0 s1 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s1 s1 s1 s1 s1 s1 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s0 s1 s0 s1 s0 s1 s1 s0
        | bits4 s0 s0 s1 s0 => bits8 s0 s0 s1 s1 s1 s1 s1 s0
        | bits4 s0 s0 s1 s1 => bits8 s0 s1 s0 s0 s1 s0 s1 s1
        | bits4 s0 s1 s0 s0 => bits8 s1 s1 s0 s0 s0 s1 s1 s0
        | bits4 s0 s1 s0 s1 => bits8 s1 s1 s0 s1 s0 s0 s1 s0
        | bits4 s0 s1 s1 s0 => bits8 s0 s1 s1 s1 s1 s0 s0 s1
        | bits4 s0 s1 s1 s1 => bits8 s0 s0 s1 s0 s0 s0 s0 s0
        | bits4 s1 s0 s0 s0 => bits8 s1 s0 s0 s1 s1 s0 s1 s0
        | bits4 s1 s0 s0 s1 => bits8 s1 s1 s0 s1 s1 s0 s1 s1
        | bits4 s1 s0 s1 s0 => bits8 s1 s1 s0 s0 s0 s0 s0 s0
        | bits4 s1 s0 s1 s1 => bits8 s1 s1 s1 s1 s1 s1 s1 s0
        | bits4 s1 s1 s0 s0 => bits8 s0 s1 s1 s1 s1 s0 s0 s0
        | bits4 s1 s1 s0 s1 => bits8 s1 s1 s0 s0 s1 s1 s0 s1
        | bits4 s1 s1 s1 s0 => bits8 s0 s1 s0 s1 s1 s0 s1 s0
        | bits4 s1 s1 s1 s1 => bits8 s1 s1 s1 s1 s0 s1 s0 s0
      end
    | bits4 s1 s1 s0 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s0 s0 s1 s1 s1 s1 s1
        | bits4 s0 s0 s0 s1 => bits8 s1 s1 s0 s1 s1 s1 s0 s1
        | bits4 s0 s0 s1 s0 => bits8 s1 s0 s1 s0 s1 s0 s0 s0
        | bits4 s0 s0 s1 s1 => bits8 s0 s0 s1 s1 s0 s0 s1 s1
        | bits4 s0 s1 s0 s0 => bits8 s1 s0 s0 s0 s1 s0 s0 s0
        | bits4 s0 s1 s0 s1 => bits8 s0 s0 s0 s0 s0 s1 s1 s1
        | bits4 s0 s1 s1 s0 => bits8 s1 s1 s0 s0 s0 s1 s1 s1
        | bits4 s0 s1 s1 s1 => bits8 s0 s0 s1 s1 s0 s0 s0 s1
        | bits4 s1 s0 s0 s0 => bits8 s1 s0 s1 s1 s0 s0 s0 s1
        | bits4 s1 s0 s0 s1 => bits8 s0 s0 s0 s1 s0 s0 s1 s0
        | bits4 s1 s0 s1 s0 => bits8 s0 s0 s0 s1 s0 s0 s0 s0
        | bits4 s1 s0 s1 s1 => bits8 s0 s1 s0 s1 s1 s0 s0 s1
        | bits4 s1 s1 s0 s0 => bits8 s0 s0 s1 s0 s0 s1 s1 s1
        | bits4 s1 s1 s0 s1 => bits8 s1 s0 s0 s0 s0 s0 s0 s0
        | bits4 s1 s1 s1 s0 => bits8 s1 s1 s1 s0 s1 s1 s0 s0
        | bits4 s1 s1 s1 s1 => bits8 s0 s1 s0 s1 s1 s1 s1 s1
      end
    | bits4 s1 s1 s0 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s1 s1 s0 s0 s0 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s0 s1 s0 s1 s0 s0 s0 s1
        | bits4 s0 s0 s1 s0 => bits8 s0 s1 s1 s1 s1 s1 s1 s1
        | bits4 s0 s0 s1 s1 => bits8 s1 s0 s1 s0 s1 s0 s0 s1
        | bits4 s0 s1 s0 s0 => bits8 s0 s0 s0 s1 s1 s0 s0 s1
        | bits4 s0 s1 s0 s1 => bits8 s1 s0 s1 s1 s0 s1 s0 s1
        | bits4 s0 s1 s1 s0 => bits8 s0 s1 s0 s0 s1 s0 s1 s0
        | bits4 s0 s1 s1 s1 => bits8 s0 s0 s0 s0 s1 s1 s0 s1
        | bits4 s1 s0 s0 s0 => bits8 s0 s0 s1 s0 s1 s1 s0 s1
        | bits4 s1 s0 s0 s1 => bits8 s1 s1 s1 s0 s0 s1 s0 s1
        | bits4 s1 s0 s1 s0 => bits8 s0 s1 s1 s1 s1 s0 s1 s0
        | bits4 s1 s0 s1 s1 => bits8 s1 s0 s0 s1 s1 s1 s1 s1
        | bits4 s1 s1 s0 s0 => bits8 s1 s0 s0 s1 s0 s0 s1 s1
        | bits4 s1 s1 s0 s1 => bits8 s1 s1 s0 s0 s1 s0 s0 s1
        | bits4 s1 s1 s1 s0 => bits8 s1 s0 s0 s1 s1 s1 s0 s0
        | bits4 s1 s1 s1 s1 => bits8 s1 s1 s1 s0 s1 s1 s1 s1
      end
    | bits4 s1 s1 s1 s0 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s1 s0 s1 s0 s0 s0 s0 s0
        | bits4 s0 s0 s0 s1 => bits8 s1 s1 s1 s0 s0 s0 s0 s0
        | bits4 s0 s0 s1 s0 => bits8 s0 s0 s1 s1 s1 s0 s1 s1
        | bits4 s0 s0 s1 s1 => bits8 s0 s1 s0 s0 s1 s1 s0 s1
        | bits4 s0 s1 s0 s0 => bits8 s1 s0 s1 s0 s1 s1 s1 s0
        | bits4 s0 s1 s0 s1 => bits8 s0 s0 s1 s0 s1 s0 s1 s0
        | bits4 s0 s1 s1 s0 => bits8 s1 s1 s1 s1 s0 s1 s0 s1
        | bits4 s0 s1 s1 s1 => bits8 s1 s0 s1 s1 s0 s0 s0 s0
        | bits4 s1 s0 s0 s0 => bits8 s1 s1 s0 s0 s1 s0 s0 s0
        | bits4 s1 s0 s0 s1 => bits8 s1 s1 s1 s0 s1 s0 s1 s1
        | bits4 s1 s0 s1 s0 => bits8 s1 s0 s1 s1 s1 s0 s1 s1
        | bits4 s1 s0 s1 s1 => bits8 s0 s0 s1 s1 s1 s1 s0 s0
        | bits4 s1 s1 s0 s0 => bits8 s1 s0 s0 s0 s0 s0 s1 s1
        | bits4 s1 s1 s0 s1 => bits8 s0 s1 s0 s1 s0 s0 s1 s1
        | bits4 s1 s1 s1 s0 => bits8 s1 s0 s0 s1 s1 s0 s0 s1
        | bits4 s1 s1 s1 s1 => bits8 s0 s1 s1 s0 s0 s0 s0 s1
      end
    | bits4 s1 s1 s1 s1 =>
        match (ls_nibble b) with
        | bits4 s0 s0 s0 s0 => bits8 s0 s0 s0 s1 s0 s1 s1 s1
        | bits4 s0 s0 s0 s1 => bits8 s0 s0 s1 s0 s1 s0 s1 s1
        | bits4 s0 s0 s1 s0 => bits8 s0 s0 s0 s0 s0 s1 s0 s0
        | bits4 s0 s0 s1 s1 => bits8 s0 s1 s1 s1 s1 s1 s1 s0
        | bits4 s0 s1 s0 s0 => bits8 s1 s0 s1 s1 s1 s0 s1 s0
        | bits4 s0 s1 s0 s1 => bits8 s0 s1 s1 s1 s0 s1 s1 s1
        | bits4 s0 s1 s1 s0 => bits8 s1 s1 s0 s1 s0 s1 s1 s0
        | bits4 s0 s1 s1 s1 => bits8 s0 s0 s1 s0 s0 s1 s1 s0
        | bits4 s1 s0 s0 s0 => bits8 s1 s1 s1 s0 s0 s0 s0 s1
        | bits4 s1 s0 s0 s1 => bits8 s0 s1 s1 s0 s1 s0 s0 s1
        | bits4 s1 s0 s1 s0 => bits8 s0 s0 s0 s1 s0 s1 s0 s0
        | bits4 s1 s0 s1 s1 => bits8 s0 s1 s1 s0 s0 s0 s1 s1
        | bits4 s1 s1 s0 s0 => bits8 s0 s1 s0 s1 s0 s1 s0 s1
        | bits4 s1 s1 s0 s1 => bits8 s0 s0 s1 s0 s0 s0 s0 s1
        | bits4 s1 s1 s1 s0 => bits8 s0 s0 s0 s0 s1 s1 s0 s0
        | bits4 s1 s1 s1 s1 => bits8 s0 s1 s1 s1 s1 s1 s0 s1
      end
  end.

Theorem sbox_inv_sbox: forall b: byte,
    inv_s_box (s_box (b)) = b.
Proof.
  intros b. destruct b.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Inductive round :=
| r1
| r2
| r3
| r4
| r5
| r6
| r7
| r8
| r9
| r10
.


Definition shift_rows (state: matrix) : matrix :=
  match state with
  | bytes16 r0c0 r0c1 r0c2 r0c3
            r1c0 r1c1 r1c2 r1c3
            r2c0 r2c1 r2c2 r2c3
            r3c0 r3c1 r3c2 r3c3 => bytes16 r0c0 r0c1 r0c2 r0c3
                                           r1c1 r1c2 r1c3 r1c0
                                           r2c2 r2c3 r2c0 r2c1
                                           r3c3 r3c0 r3c1 r3c2
  end.

Definition inv_shift_rows (state: matrix) : matrix :=
  match state with
  | bytes16 r0c0 r0c1 r0c2 r0c3
            r1c0 r1c1 r1c2 r1c3
            r2c0 r2c1 r2c2 r2c3
            r3c0 r3c1 r3c2 r3c3 => bytes16 r0c0 r0c1 r0c2 r0c3
                                           r1c3 r1c0 r1c1 r1c2
                                           r2c2 r2c3 r2c0 r2c1
                                           r3c1 r3c2 r3c3 r3c0
  end.

Theorem srows_inv_srows: forall state: matrix,
    inv_shift_rows (shift_rows (state)) = state.
Proof.
  intros s.
  destruct s.
  - simpl. reflexivity.
Qed.

Definition sub_bytes (state: matrix) : matrix :=
  match state with
  | bytes16 r0c0 r0c1 r0c2 r0c3
            r1c0 r1c1 r1c2 r1c3
            r2c0 r2c1 r2c2 r2c3
            r3c0 r3c1 r3c2 r3c3 => bytes16 (s_box r0c0) (s_box r0c1) (s_box r0c2) (s_box r0c3)
                                           (s_box r1c0) (s_box r1c1) (s_box r1c2) (s_box r1c3)
                                           (s_box r2c0) (s_box r2c1) (s_box r2c2) (s_box r2c3)
                                           (s_box r3c0) (s_box r3c1) (s_box r3c2) (s_box r3c3)
  end.

Definition inv_sub_bytes (state: matrix) : matrix :=
  match state with
  | bytes16 r0c0 r0c1 r0c2 r0c3
            r1c0 r1c1 r1c2 r1c3
            r2c0 r2c1 r2c2 r2c3
            r3c0 r3c1 r3c2 r3c3 => bytes16 (inv_s_box r0c0) (inv_s_box r0c1) (inv_s_box r0c2) (inv_s_box r0c3)
                                           (inv_s_box r1c0) (inv_s_box r1c1) (inv_s_box r1c2) (inv_s_box r1c3)
                                           (inv_s_box r2c0) (inv_s_box r2c1) (inv_s_box r2c2) (inv_s_box r2c3)
                                           (inv_s_box r3c0) (inv_s_box r3c1) (inv_s_box r3c2) (inv_s_box r3c3)
  end.

Theorem sbytes_inv_sbytes: forall state: matrix,
    inv_sub_bytes (sub_bytes (state)) = state.
Proof.
  intros s.
  destruct s.
  - simpl.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    rewrite sbox_inv_sbox.
    reflexivity.
Qed.

Theorem xor_xor_bit: forall b' b: bit,
    xor_bits b' (xor_bits b' b) = b.
Proof.
  intros b' b.
  destruct b.
  - destruct b'.
    + reflexivity.
    + reflexivity.
  - destruct b'.
    + reflexivity.
    + reflexivity.
Qed.

Theorem xor_xor_bit' : forall b' b : bit,
  xor_bits (xor_bits b b') b' = b.
Proof.
  intros b' b.
  destruct b.
  - destruct b'.
    + reflexivity.
    + reflexivity.
  - destruct b'.
    + reflexivity.
    + reflexivity.
Qed.

Theorem xor_xor_byte: forall b' b: byte,
    xor_bytes b' (xor_bytes b' b) = b.
Proof.
  intros b' b.
  destruct b'.
  destruct b.
  simpl.
  rewrite xor_xor_bit.
  rewrite xor_xor_bit.
  rewrite xor_xor_bit.
  rewrite xor_xor_bit.
  rewrite xor_xor_bit.
  rewrite xor_xor_bit.
  rewrite xor_xor_bit.
  rewrite xor_xor_bit.
  reflexivity.
Qed.

Theorem xor_xor_byte' : forall b' b: byte,
  xor_bytes (xor_bytes b b') b' = b.
Proof.
  intros b' b.
  destruct b'.
  destruct b.
  simpl.
  rewrite xor_xor_bit'.
  rewrite xor_xor_bit'.
  rewrite xor_xor_bit'.
  rewrite xor_xor_bit'.
  rewrite xor_xor_bit'.
  rewrite xor_xor_bit'.
  rewrite xor_xor_bit'.
  rewrite xor_xor_bit'.
  reflexivity.
Qed.
  


(*TODO: mix_columns, inv_mix_columns, mc_inv_mc*)

Definition xtime (b: byte) : byte :=
  match b with
  | bits8 s0 b6 b5 b4 b3 b2 b1 b0 => bits8 b6 b5 b4 b3 b2 b1 b0 s0
  | bits8 s1 b6 b5 b4 b3 b2 b1 b0 => xor_bytes (bits8 b6 b5 b4 b3 b2 b1 b0 s0) (bits8 s0 s0 s0 s1 s1 s0 s1 s1)
  end.

Definition mul01 (b: byte): byte :=
  b
.

Definition mul02 (b: byte): byte :=
  xtime b
.

Notation "01 GF* A" := (mul01 A) (at level 75).
Notation "02 GF* A" := (mul02 A) (at level 75).

Definition mul03 (b: byte): byte :=
  (02 GF* b) X*OR (b)
.    

Definition mul09 (b: byte): byte:=
  b X*OR (02 GF* (02 GF* (02 GF* b)))
.

Definition mul0b (b:byte): byte:=
  b X*OR ((02 GF* b) X*OR (02 GF* (02 GF* (02 GF* b))))
.

Definition mul0d (b: byte): byte:=
  b X*OR ((02 GF* (02 GF* b) X*OR (02 GF* (02 GF* (02 GF* b)))))
.

Definition mul0e (b: byte): byte:=
  (02 GF* b) X*OR ((02 GF* (02 GF* b) X*OR (02 GF* (02 GF* (02 GF* b)))))
.

Notation "03 GF* A" := (mul03 A) (at level 75).
Notation "09 GF* A" := (mul09 A) (at level 75).
Notation "0b GF* A" := (mul0b A) (at level 75).
Notation "0d GF* A" := (mul0d A) (at level 75).
Notation "0e GF* A" := (mul0e A) (at level 75).

Definition zb:=
  bits8 s0 s0 s0 s0 s0 s0 s0 s0.

Theorem xor_byte_zb: forall b: byte,
    (zb X*OR b) = b.
Proof.
  intros b. destruct b.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem xor_bits_comm: forall a b: bit,
    (a x*or b) = (b x*or a).
Proof.
  intros a b.
  destruct a.
  - reflexivity.
  - reflexivity.
Qed.
    
Theorem xor_bytes_comm: forall a b: byte,
    (a X*OR b) = (b X*OR a).
Proof.
  intros a b.
  unfold "X*OR".
  destruct a. destruct b.
  rewrite xor_bits_comm.
  pose proof (xor_bits_comm b1 b9).
  pose proof (xor_bits_comm b2 b10).
  pose proof (xor_bits_comm b3 b11).
  pose proof (xor_bits_comm b4 b12).
  pose proof (xor_bits_comm b5 b13).
  pose proof (xor_bits_comm b6 b14).
  pose proof (xor_bits_comm b7 b15).
  rewrite H. rewrite H0. rewrite H1.
  rewrite H2. rewrite H3. rewrite H4.
  rewrite H5.
  reflexivity.
Qed.

Theorem xor_bits_assoc: forall a b c: bit,
    (a x*or (b x*or c)) = ((a x*or b) x*or c).
Proof.
  intros a b c.
  simpl. unfold "x*or".
  destruct a.
  - destruct b.
    + destruct c.
      ++ reflexivity.
      ++ reflexivity.
    + destruct c.
      ++ reflexivity.
      ++ reflexivity.
  - destruct b.
    + destruct c.
      ++ reflexivity.
      ++ reflexivity.
    + destruct c.
      ++ reflexivity.
      ++ reflexivity.
Qed.

Theorem xor_bytes_assoc: forall a b c: byte,
    (a X*OR (b X*OR c)) = ((a X*OR b) X*OR c).
Proof.
  intros a b c.
  simpl. unfold "X*OR".
  destruct a. destruct b. destruct c.
  rewrite xor_bits_assoc. rewrite xor_bits_assoc.
  rewrite xor_bits_assoc. rewrite xor_bits_assoc.
  rewrite xor_bits_assoc. rewrite xor_bits_assoc.
  rewrite xor_bits_assoc. rewrite xor_bits_assoc.
  reflexivity.
Qed.

Theorem xor_bits_cancel: forall a b c: bit,
    ((a x*or c) x*or (b x*or c)) = (a x*or b).
Proof.
  intros a b c.
  unfold "x*or".
  destruct c.
  - destruct a.
    + destruct b.
      ++ reflexivity.
      ++ reflexivity.
    + destruct b.
      ++ reflexivity.
      ++ reflexivity.
  - destruct a.
    + destruct b.
      ++ reflexivity.
      ++ reflexivity.
    + destruct b.
      ++ reflexivity.
      ++ reflexivity.
Qed.

Theorem xor_bytes_cancel: forall a b c: byte,
    ((a X*OR c) X*OR (b X*OR c)) = (a X*OR b).
Proof.
  intros a b c.
  unfold "X*OR".
  destruct a. destruct b. destruct c.
  rewrite xor_bits_cancel. rewrite xor_bits_cancel.
  rewrite xor_bits_cancel. rewrite xor_bits_cancel.
  rewrite xor_bits_cancel. rewrite xor_bits_cancel.
  rewrite xor_bits_cancel. rewrite xor_bits_cancel.
  reflexivity.
Qed.

Theorem xor_bits_noorder: forall a b c d: bit,
    (a x*or b x*or c x*or d) = (a x*or c x*or b x*or d).
Proof.
  intros a b c d.
  unfold "x*or".
  destruct a; (destruct b; (destruct c; (destruct d; (reflexivity)))).
Qed.
         
Theorem xor_bytes_noorder: forall a b c d: byte,
    (a X*OR b X*OR c X*OR d) = (a X*OR c X*OR b X*OR d).
Proof.
  intros a b c d.
  destruct a. destruct b.
  destruct c. destruct d.
  unfold "X*OR".
  pose proof (xor_bits_noorder b0 b8 b16 b24).
  pose proof (xor_bits_noorder b1 b9 b17 b25).
  pose proof (xor_bits_noorder b2 b10 b18 b26).
  pose proof (xor_bits_noorder b3 b11 b19 b27).
  pose proof (xor_bits_noorder b4 b12 b20 b28).
  pose proof (xor_bits_noorder b5 b13 b21 b29).
  pose proof (xor_bits_noorder b6 b14 b22 b30).
  pose proof (xor_bits_noorder b7 b15 b23 b31).
  rewrite H. rewrite H0. rewrite H1. rewrite H2.
  rewrite H3. rewrite H4. rewrite H5. rewrite H6.
  reflexivity.
Qed.

Theorem a''_a_eq_a: forall a: byte,
    ((((0e GF* (02 GF* a)) X*OR (0b GF* a)) X*OR (0d GF* a)) X*OR (09 GF* (03 GF* a))) = a.
Proof.
  intros a. destruct a.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem a''_b_eq_zb: forall b: byte,
    ((((0e GF* (03 GF* b)) X*OR (0b GF* (02 GF* b))) X*OR (0d GF* b)) X*OR (09 GF* b)) = zb.
Proof.
  intros b. destruct b.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem a''_c_eq_zb: forall c: byte,
    (((0e GF* c) X*OR (0b GF* (03 GF* c)) X*OR (0d GF* (02 GF* c)) X*OR (09 GF* c))) = zb.
Proof.
  intros c. destruct c.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem a''_d_eq_zb: forall d: byte,
    (((0e GF* d) X*OR (0b GF* d)) X*OR (0d GF* (03 GF* d)) X*OR (09 GF* (02 GF* d))) = zb.
Proof.
  intros d. destruct d.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem a''_eq_a: forall a b c d: byte,
    ((((0e GF* (02 GF* a) X*OR (0b GF* a)) X*OR (0d GF* a)) X*OR (09 GF* (03 GF* a)))
      X*OR (((((0e GF* (03 GF* b)) X*OR (0b GF* (02 GF* b))) X*OR (0d GF* b)) X*OR (09 GF* b))
            X*OR ((((0e GF* c) X*OR (0b GF* (03 GF* c)) X*OR (0d GF* (02 GF* c)) X*OR (09 GF* c)))
                  X*OR ((((0e GF* d) X*OR (0b GF* d)) X*OR (0d GF* (03 GF* d)) X*OR (09 GF* (02 GF* d))))))) = a.
Proof.
  intros a b c d.
  rewrite a''_a_eq_a.
  rewrite a''_b_eq_zb.
  rewrite a''_c_eq_zb.
  rewrite a''_d_eq_zb.
  rewrite xor_byte_zb.
  rewrite xor_byte_zb.
  rewrite xor_bytes_comm.
  rewrite xor_byte_zb.
  reflexivity.
Qed.

Theorem b''_a_eq_zb: forall a: byte,
    ((((09 GF* (02 GF* a)) X*OR (0e GF* a)) X*OR (0b GF* a)) X*OR (0d GF* (03 GF* a))) = zb.
Proof.
  intros a. destruct a.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem b''_b_eq_b: forall b: byte,
    ((((09 GF* (03 GF* b)) X*OR (0e GF* (02 GF* b))) X*OR (0b GF* b)) X*OR (0d GF* b)) = b.
Proof.
  intros b. destruct b.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem b''_c_eq_zb: forall c: byte,
    (((09 GF* c) X*OR (0e GF* (03 GF* c)) X*OR (0b GF* (02 GF* c)) X*OR (0d GF* c))) = zb.
Proof.
  intros c. destruct c.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem b''_d_eq_zb: forall d: byte,
    (((09 GF* d) X*OR (0e GF* d)) X*OR (0b GF* (03 GF* d)) X*OR (0d GF* (02 GF* d))) = zb.
Proof.
  intros d. destruct d.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem b''_eq_b: forall a b c d: byte,
    (((((09 GF* (02 GF* a)) X*OR (0e GF* a)) X*OR (0b GF* a)) X*OR (0d GF* (03 GF* a)))
      X*OR (((((09 GF* (03 GF* b)) X*OR (0e GF* (02 GF* b))) X*OR (0b GF* b)) X*OR (0d GF* b))
            X*OR ((((09 GF* c) X*OR (0e GF* (03 GF* c)) X*OR (0b GF* (02 GF* c)) X*OR (0d GF* c)))
                  X*OR ((((09 GF* d) X*OR (0e GF* d)) X*OR (0b GF* (03 GF* d)) X*OR (0d GF* (02 GF* d))))
                )
          )
    ) = b.
Proof.
  intros a b c d.
  rewrite b''_a_eq_zb.
  rewrite b''_b_eq_b.
  rewrite b''_c_eq_zb.
  rewrite b''_d_eq_zb.
  rewrite xor_byte_zb.
  rewrite xor_byte_zb.
  rewrite xor_bytes_comm.
  rewrite xor_byte_zb.
  reflexivity.
Qed.

Theorem c''_a_eq_zb: forall a: byte,
    ((((0d GF* (02 GF* a)) X*OR (09 GF* a)) X*OR (0e GF* a)) X*OR (0b GF* (03 GF* a))) = zb.
Proof.
  intros a. destruct a.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem c''_b_eq_zb: forall b: byte,
    ((((0d GF* (03 GF* b)) X*OR (09 GF* (02 GF* b))) X*OR (0e GF* b)) X*OR (0b GF* b)) = zb.
Proof.
  intros b. destruct b.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem c''_c_eq_c: forall c: byte,
    (((0d GF* c) X*OR (09 GF* (03 GF* c)) X*OR (0e GF* (02 GF* c)) X*OR (0b GF* c))) = c.
Proof.
  intros c. destruct c.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem c''_d_eq_zb: forall d: byte,
    (((0d GF* d) X*OR (09 GF* d)) X*OR (0e GF* (03 GF* d)) X*OR (0b GF* (02 GF* d))) = zb.
Proof.
  intros d. destruct d.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem c''_eq_c: forall a b c d: byte,
    (((((0d GF* (02 GF* a)) X*OR (09 GF* a)) X*OR (0e GF* a)) X*OR (0b GF* (03 GF* a)))
      X*OR (((((0d GF* (03 GF* b)) X*OR (09 GF* (02 GF* b))) X*OR (0e GF* b)) X*OR (0b GF* b))
            X*OR ((((0d GF* c) X*OR (09 GF* (03 GF* c)) X*OR (0e GF* (02 GF* c)) X*OR (0b GF* c)))
                  X*OR ((((0d GF* d) X*OR (09 GF* d)) X*OR (0e GF* (03 GF* d)) X*OR (0b GF* (02 GF* d)))
                )
          )
    )) = c.
Proof.
  intros a b c d.
  rewrite c''_a_eq_zb.
  rewrite c''_b_eq_zb.
  rewrite c''_c_eq_c.
  rewrite c''_d_eq_zb.
  rewrite xor_byte_zb.
  rewrite xor_byte_zb.
  rewrite xor_bytes_comm.
  rewrite xor_byte_zb.
  reflexivity.
Qed.

Theorem d''_a_eq_zb: forall a: byte,
    ((((0b GF* (02 GF* a)) X*OR (0d GF* a)) X*OR (09 GF* a)) X*OR (0e GF* (03 GF* a))) = zb.
Proof.
  intros a. destruct a.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem d''_b_eq_zb: forall b: byte,
    ((((0b GF* (03 GF* b)) X*OR (0d GF* (02 GF* b))) X*OR (09 GF* b)) X*OR (0e GF* b)) = zb.
Proof.
  intros b. destruct b.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem d''_c_eq_zb: forall c: byte,
    (((0b GF* c) X*OR (0d GF* (03 GF* c)) X*OR (09 GF* (02 GF* c)) X*OR (0e GF* c))) = zb.
Proof.
  intros c. destruct c.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem d''_d_eq_d: forall d: byte,
    (((0b GF* d) X*OR (0d GF* d)) X*OR (09 GF* (03 GF* d)) X*OR (0e GF* (02 GF* d))) = d.
Proof.
  intros d. destruct d.
  destruct b0;
    (destruct b1;
     (destruct b2;
      (destruct b3;
       (destruct b4;
        (destruct b5;
         (destruct b6;
          (destruct b7;
           reflexivity))))))).
Qed.

Theorem d''_eq_c: forall a b c d: byte,
    (((((0b GF* (02 GF* a)) X*OR (0d GF* a)) X*OR (09 GF* a)) X*OR (0e GF* (03 GF* a)))
      X*OR (((((0b GF* (03 GF* b)) X*OR (0d GF* (02 GF* b))) X*OR (09 GF* b)) X*OR (0e GF* b))
            X*OR ((((0b GF* c) X*OR (0d GF* (03 GF* c)) X*OR (09 GF* (02 GF* c)) X*OR (0e GF* c)))
                  X*OR ((((0b GF* d) X*OR (0d GF* d)) X*OR (09 GF* (03 GF* d)) X*OR (0e GF* (02 GF* d)))
                )
          )
    )) = d.
Proof.
  intros a b c d.
  rewrite d''_a_eq_zb.
  rewrite d''_b_eq_zb.
  rewrite d''_c_eq_zb.
  rewrite d''_d_eq_d.
  rewrite xor_byte_zb.
  rewrite xor_byte_zb.
  rewrite xor_byte_zb.
  reflexivity.
Qed.


Theorem distr_gf_01: forall a b: byte,
    (01 GF* (a X*OR b)) = ((01 GF* a) X*OR (01 GF* b)).
Proof.
  intros a b.
  unfold "01 GF* s".
  reflexivity.
Qed.
(*
Theorem distr_gf_01_four: forall a b c d: byte,
    (01 GF* (a X*OR b X*OR c X*OR d)) = ((01 GF* a) X*OR (01 GF* b) X*OR (01 GF* c) X*OR (01 GF* d)).
Proof.
  intros a b c d.
  unfold "01 GF* s".
  reflexivity.
Qed.
*)
Theorem xtime_distr: forall a b: byte,
    (xtime (a X*OR b)) = ((xtime a) X*OR (xtime b)).
Proof.
  intros a b.
  unfold xtime.
  destruct a . destruct b.
  simpl.
  destruct b0.
  - destruct b8.
    + simpl. reflexivity.
    + simpl. rewrite <- xor_bits_assoc.
      rewrite <- xor_bits_assoc. rewrite <- xor_bits_assoc.
      rewrite <- xor_bits_assoc. rewrite <- xor_bits_assoc.
      rewrite <- xor_bits_assoc. rewrite <- xor_bits_assoc.
      reflexivity.
  - destruct b8.
    + simpl. rewrite <- xor_bits_assoc.
      rewrite <- xor_bits_assoc. rewrite <- xor_bits_assoc.
      rewrite <- xor_bits_assoc. rewrite <- xor_bits_assoc.
      rewrite <- xor_bits_assoc. rewrite <- xor_bits_assoc.
      rewrite <- xor_bits_assoc. rewrite <- xor_bits_assoc.
      rewrite <- xor_bits_assoc. rewrite <- xor_bits_assoc.
      rewrite <- xor_bits_assoc. rewrite <- xor_bits_assoc.
      rewrite <- xor_bits_assoc.
      pose proof (xor_bits_comm b9 s0).
      pose proof (xor_bits_comm b10 s0).
      pose proof (xor_bits_comm b11 s0).
      pose proof (xor_bits_comm b12 s1).
      pose proof (xor_bits_comm b13 s1).
      pose proof (xor_bits_comm b14 s0).
      pose proof (xor_bits_comm b15 s1).
      rewrite H. rewrite H0. rewrite H1.
      rewrite H2. rewrite H3. rewrite H4.
      rewrite H5. reflexivity.
    + simpl. rewrite xor_bits_cancel. rewrite xor_bits_cancel.
      rewrite xor_bits_cancel. rewrite xor_bits_cancel.
      rewrite xor_bits_cancel. rewrite xor_bits_cancel.
      rewrite xor_bits_cancel.
      reflexivity.
Qed.

Theorem distr_gf_02: forall a b: byte,
    (02 GF* (a X*OR b)) = ((02 GF* a) X*OR (02 GF* b)).
Proof.
  intros a b.
  unfold "02 GF* s".
  rewrite xtime_distr.
  reflexivity.
Qed.
(*
Theorem distr_gf_02_four: forall a b c d: byte,
    (02 GF* (a X*OR b X*OR c X*OR d)) = ((02 GF* a) X*OR (02 GF* b) X*OR (02 GF* c) X*OR (02 GF* d)).
Proof.
  intros a b c d.
  unfold "02 GF* s".
  rewrite xtime_distr.
  rewrite xtime_distr.
  rewrite xtime_distr.
  reflexivity.
Qed.

Theorem distr_gf_03: forall a b: byte,
    (03 GF* (a X*OR b)) = ((03 GF* a) X*OR (03 GF* b)).
Proof.
  intros a b.
  unfold "03 GF* s".
  rewrite distr_gf_02.
  pose proof (xor_bytes_assoc ((02 GF* a) X*OR a) (02 GF* b) b).
  rewrite H.
  rewrite xor_bytes_noorder.
  pose proof (xor_bytes_assoc ((02 GF* a) X*OR (02 GF* b)) a  b).
  rewrite H0.
  reflexivity.
Qed.  
 *)
Theorem distr_gf_09_four: forall a b c d: byte,
    (09 GF* (a X*OR b X*OR c X*OR d)) = ((09 GF* a) X*OR (09 GF* b) X*OR (09 GF* c) X*OR (09 GF* d)).
Proof.
Admitted.

Theorem distr_gf_0b_four: forall a b c d: byte,
    (0b GF* (a X*OR b X*OR c X*OR d)) = ((0b GF* a) X*OR (0b GF* b) X*OR (0b GF* c) X*OR (0b GF* d)).
Proof.
Admitted.

Theorem distr_gf_0d_four: forall a b c d: byte,
    (0d GF* (a X*OR b X*OR c X*OR d)) = ((0d GF* a) X*OR (0d GF* b) X*OR (0d GF* c) X*OR (0d GF* d)).
Proof.
Admitted.

Theorem distr_gf_0e_four: forall a b c d: byte,
    (0e GF* (a X*OR b X*OR c X*OR d)) = ((0e GF* a) X*OR (0e GF* b) X*OR (0e GF* c) X*OR (0e GF* d)).
Proof.
Admitted.

Theorem consolidate_16_xor_bytes: forall a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3: byte,
    ((((a0 X*OR b0 X*OR c0 X*OR d0) X*OR (a1 X*OR b1 X*OR c1 X*OR d1))
        X*OR (a2 X*OR b2 X*OR c2 X*OR d2)) X*OR (a3 X*OR b3 X*OR c3 X*OR d3))
    =
      ((((a0 X*OR a1 X*OR a2 X*OR a3) X*OR (b0 X*OR b1 X*OR b2 X*OR b3))
          X*OR (c0 X*OR c1 X*OR c2 X*OR c3)) X*OR (d0 X*OR d1 X*OR d2 X*OR d3)).
Proof.
Admitted.

  
Definition mix_column_transform (column: word): word :=
  match column with
  | bytes4 a b c d =>
      let a':= (02 GF* a) X*OR (03 GF* b) X*OR c X*OR d in
      let b':= a X*OR (02 GF* b) X*OR (03 GF* c) X*OR d in
      let c':= a X*OR b X*OR (02 GF* c) X*OR (03 GF* d) in
      let d':= (03 GF* a) X*OR b X*OR c X*OR (02 GF* d) in
      bytes4 a' b' c' d'
  end.

Definition inv_mix_column_transform (column: word): word :=
  match column with
  | bytes4 a' b' c' d' =>
      let a'':= (0e GF* a') X*OR (0b GF* b') X*OR (0d GF* c') X*OR (09 GF* d') in
      let b'':= (09 GF* a') X*OR (0e GF* b') X*OR (0b GF* c') X*OR (0d GF* d') in
      let c'':= (0d GF* a') X*OR (09 GF* b') X*OR (0e GF* c') X*OR (0b GF* d') in
      let d'':= (0b GF* a') X*OR (0d GF* b') X*OR (09 GF* c') X*OR (0e GF* d') in
      bytes4 a'' b'' c'' d''
  end.
                                            
Definition columns_to_matrix (c0 c1 c2 c3: word): matrix :=
  match c0 with
  | bytes4 c00 c10 c20 c30 =>
      match c1 with
      | bytes4 c01 c11 c21 c31 =>
          match c2 with
          | bytes4 c02 c12 c22 c32 =>
              match c3 with
              | bytes4 c03 c13 c23 c33 =>
                  bytes16 c00 c01 c02 c03
                          c10 c11 c12 c13
                          c20 c21 c22 c23
                          c30 c31 c32 c33
              end
          end
      end
  end.


Definition mix_columns_qw (state: qword): qword :=
  match state with
  | words4 w0 w1 w2 w3 => words4 (mix_column_transform w0) (mix_column_transform w1) (mix_column_transform w2) (mix_column_transform w3)
  end.

Definition inv_mix_columns_qw (state: qword): qword :=
  match state with
  | words4 w0 w1 w2 w3 => words4 (inv_mix_column_transform w0) (inv_mix_column_transform w1) (inv_mix_column_transform w2) (inv_mix_column_transform w3)
  end.

Definition mix_columns (state: matrix) : matrix :=
  match state with
  | bytes16 s00 s01 s02 s03
            s10 s11 s12 s13
            s20 s21 s22 s23
            s30 s31 s32 s33 => let ncol0 := (mix_column_transform (bytes4 s00 s10 s20 s30))
                               in
                               let ncol1 := (mix_column_transform (bytes4 s01 s11 s21 s31))
                               in
                               let ncol2 := (mix_column_transform (bytes4 s02 s12 s22 s32))
                               in
                               let ncol3 := (mix_column_transform (bytes4 s03 s13 s23 s33))
                               in
                               columns_to_matrix ncol0 ncol1 ncol2 ncol3
  end.

Definition inv_mix_columns (state: matrix) : matrix :=
  match state with
  | bytes16 s00 s01 s02 s03
            s10 s11 s12 s13
            s20 s21 s22 s23
            s30 s31 s32 s33 => let ncol0 := (inv_mix_column_transform (bytes4 s00 s10 s20 s30))
                               in
                               let ncol1 := (inv_mix_column_transform (bytes4 s01 s11 s21 s31))
                               in
                               let ncol2 := (inv_mix_column_transform (bytes4 s02 s12 s22 s32))
                               in
                               let ncol3 := (inv_mix_column_transform (bytes4 s03 s13 s23 s33))
                               in
                               columns_to_matrix ncol0 ncol1 ncol2 ncol3
  end.

Theorem mc_inv_mc: forall state: matrix,
    inv_mix_columns (mix_columns (state)) = state.
Proof.
  intros state.
  unfold mix_columns.
  unfold inv_mix_columns.
  destruct state. simpl.

  pose proof (distr_gf_0e_four (02 GF* r0c0) (03 GF* r1c0) r2c0 r3c0).
  pose proof (distr_gf_0b_four r0c0 (02 GF* r1c0) (03 GF* r2c0) r3c0).
  pose proof (distr_gf_0d_four r0c0 r1c0 (02 GF* r2c0) (03 GF* r3c0)).
  pose proof (distr_gf_09_four (03 GF* r0c0) r1c0 r2c0 (02 GF* r3c0)).
  rewrite H. rewrite H0. rewrite H1. rewrite H2.
  rewrite consolidate_16_xor_bytes.
  rewrite a''_a_eq_a. rewrite a''_b_eq_zb. rewrite a''_c_eq_zb.
  rewrite a''_d_eq_zb. rewrite xor_bytes_comm. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb. rewrite xor_bytes_comm.
  rewrite xor_byte_zb.

  pose proof (distr_gf_0e_four (02 GF* r0c1) (03 GF* r1c1) r2c1 r3c1).
  pose proof (distr_gf_0b_four r0c1 (02 GF* r1c1) (03 GF* r2c1) r3c1).
  pose proof (distr_gf_0d_four r0c1 r1c1 (02 GF* r2c1) (03 GF* r3c1)).
  pose proof (distr_gf_09_four (03 GF* r0c1) r1c1 r2c1 (02 GF* r3c1)).
  rewrite H3. rewrite H4. rewrite H5. rewrite H6.
  rewrite consolidate_16_xor_bytes.
  rewrite a''_a_eq_a. rewrite a''_b_eq_zb. rewrite a''_c_eq_zb.
  rewrite a''_d_eq_zb. rewrite xor_bytes_comm. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb. rewrite xor_bytes_comm.
  rewrite xor_byte_zb.
  
  pose proof (distr_gf_0e_four (02 GF* r0c2) (03 GF* r1c2) r2c2 r3c2).
  pose proof (distr_gf_0b_four r0c2 (02 GF* r1c2) (03 GF* r2c2) r3c2).
  pose proof (distr_gf_0d_four r0c2 r1c2 (02 GF* r2c2) (03 GF* r3c2)).
  pose proof (distr_gf_09_four (03 GF* r0c2) r1c2 r2c2 (02 GF* r3c2)).
  rewrite H7. rewrite H8. rewrite H9. rewrite H10.
  rewrite consolidate_16_xor_bytes.
  rewrite a''_a_eq_a. rewrite a''_b_eq_zb. rewrite a''_c_eq_zb.
  rewrite a''_d_eq_zb. rewrite xor_bytes_comm. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb. rewrite xor_bytes_comm.
  rewrite xor_byte_zb.

  pose proof (distr_gf_0e_four (02 GF* r0c3) (03 GF* r1c3) r2c3 r3c3).
  pose proof (distr_gf_0b_four r0c3 (02 GF* r1c3) (03 GF* r2c3) r3c3).
  pose proof (distr_gf_0d_four r0c3 r1c3 (02 GF* r2c3) (03 GF* r3c3)).
  pose proof (distr_gf_09_four (03 GF* r0c3) r1c3 r2c3 (02 GF* r3c3)).
  rewrite H11. rewrite H12. rewrite H13. rewrite H14.
  rewrite consolidate_16_xor_bytes.
  rewrite a''_a_eq_a. rewrite a''_b_eq_zb. rewrite a''_c_eq_zb.
  rewrite a''_d_eq_zb. rewrite xor_bytes_comm. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb. rewrite xor_bytes_comm.
  rewrite xor_byte_zb.

  pose proof (distr_gf_09_four (02 GF* r0c0) (03 GF* r1c0) r2c0 r3c0).
  pose proof (distr_gf_0e_four r0c0 (02 GF* r1c0) (03 GF* r2c0) r3c0).
  pose proof (distr_gf_0b_four r0c0 r1c0 (02 GF* r2c0) (03 GF* r3c0)).
  pose proof (distr_gf_0d_four (03 GF* r0c0) r1c0 r2c0 (02 GF* r3c0)).
  rewrite H15. rewrite H16. rewrite H17. rewrite H18.
  rewrite consolidate_16_xor_bytes.
  rewrite b''_a_eq_zb. rewrite b''_b_eq_b. rewrite b''_c_eq_zb.
  rewrite b''_d_eq_zb. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb. 

  pose proof (distr_gf_09_four (02 GF* r0c1) (03 GF* r1c1) r2c1 r3c1).
  pose proof (distr_gf_0e_four r0c1 (02 GF* r1c1) (03 GF* r2c1) r3c1).
  pose proof (distr_gf_0b_four r0c1 r1c1 (02 GF* r2c1) (03 GF* r3c1)).
  pose proof (distr_gf_0d_four (03 GF* r0c1) r1c1 r2c1 (02 GF* r3c1)).
  rewrite H19. rewrite H20. rewrite H21. rewrite H22.
  rewrite consolidate_16_xor_bytes.
  rewrite b''_a_eq_zb. rewrite b''_b_eq_b. rewrite b''_c_eq_zb.
  rewrite b''_d_eq_zb. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb. 

  pose proof (distr_gf_09_four (02 GF* r0c2) (03 GF* r1c2) r2c2 r3c2).
  pose proof (distr_gf_0e_four r0c2 (02 GF* r1c2) (03 GF* r2c2) r3c2).
  pose proof (distr_gf_0b_four r0c2 r1c2 (02 GF* r2c2) (03 GF* r3c2)).
  pose proof (distr_gf_0d_four (03 GF* r0c2) r1c2 r2c2 (02 GF* r3c2)).
  rewrite H23. rewrite H24. rewrite H25. rewrite H26.
  rewrite consolidate_16_xor_bytes.
  rewrite b''_a_eq_zb. rewrite b''_b_eq_b. rewrite b''_c_eq_zb.
  rewrite b''_d_eq_zb. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb. 

  pose proof (distr_gf_09_four (02 GF* r0c3) (03 GF* r1c3) r2c3 r3c3).
  pose proof (distr_gf_0e_four r0c3 (02 GF* r1c3) (03 GF* r2c3) r3c3).
  pose proof (distr_gf_0b_four r0c3 r1c3 (02 GF* r2c3) (03 GF* r3c3)).
  pose proof (distr_gf_0d_four (03 GF* r0c3) r1c3 r2c3 (02 GF* r3c3)).
  rewrite H27. rewrite H28. rewrite H29. rewrite H30.
  rewrite consolidate_16_xor_bytes.
  rewrite b''_a_eq_zb. rewrite b''_b_eq_b. rewrite b''_c_eq_zb.
  rewrite b''_d_eq_zb. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb.

  pose proof (distr_gf_0d_four (02 GF* r0c0) (03 GF* r1c0) r2c0 r3c0).
  pose proof (distr_gf_09_four r0c0 (02 GF* r1c0) (03 GF* r2c0) r3c0).
  pose proof (distr_gf_0e_four r0c0 r1c0 (02 GF* r2c0) (03 GF* r3c0)).
  pose proof (distr_gf_0b_four (03 GF* r0c0) r1c0 r2c0 (02 GF* r3c0)).
  rewrite H31. rewrite H32. rewrite H33. rewrite H34.
  rewrite consolidate_16_xor_bytes.
  rewrite c''_a_eq_zb. rewrite c''_b_eq_zb. rewrite c''_c_eq_c.
  rewrite c''_d_eq_zb. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb.

  pose proof (distr_gf_0d_four (02 GF* r0c1) (03 GF* r1c1) r2c1 r3c1).
  pose proof (distr_gf_09_four r0c1 (02 GF* r1c1) (03 GF* r2c1) r3c1).
  pose proof (distr_gf_0e_four r0c1 r1c1 (02 GF* r2c1) (03 GF* r3c1)).
  pose proof (distr_gf_0b_four (03 GF* r0c1) r1c1 r2c1 (02 GF* r3c1)).
  rewrite H35. rewrite H36. rewrite H37. rewrite H38.
  rewrite consolidate_16_xor_bytes.
  rewrite c''_a_eq_zb. rewrite c''_b_eq_zb. rewrite c''_c_eq_c.
  rewrite c''_d_eq_zb. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb.

  pose proof (distr_gf_0d_four (02 GF* r0c2) (03 GF* r1c2) r2c2 r3c2).
  pose proof (distr_gf_09_four r0c2 (02 GF* r1c2) (03 GF* r2c2) r3c2).
  pose proof (distr_gf_0e_four r0c2 r1c2 (02 GF* r2c2) (03 GF* r3c2)).
  pose proof (distr_gf_0b_four (03 GF* r0c2) r1c2 r2c2 (02 GF* r3c2)).
  rewrite H39. rewrite H40. rewrite H41. rewrite H42.
  rewrite consolidate_16_xor_bytes.
  rewrite c''_a_eq_zb. rewrite c''_b_eq_zb. rewrite c''_c_eq_c.
  rewrite c''_d_eq_zb. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb.

  pose proof (distr_gf_0d_four (02 GF* r0c3) (03 GF* r1c3) r2c3 r3c3).
  pose proof (distr_gf_09_four r0c3 (02 GF* r1c3) (03 GF* r2c3) r3c3).
  pose proof (distr_gf_0e_four r0c3 r1c3 (02 GF* r2c3) (03 GF* r3c3)).
  pose proof (distr_gf_0b_four (03 GF* r0c3) r1c3 r2c3 (02 GF* r3c3)).
  rewrite H43. rewrite H44. rewrite H45. rewrite H46.
  rewrite consolidate_16_xor_bytes.
  rewrite c''_a_eq_zb. rewrite c''_b_eq_zb. rewrite c''_c_eq_c.
  rewrite c''_d_eq_zb. rewrite xor_byte_zb.
  rewrite xor_bytes_comm. rewrite xor_byte_zb.

  pose proof (distr_gf_0b_four (02 GF* r0c0) (03 GF* r1c0) r2c0 r3c0).
  pose proof (distr_gf_0d_four r0c0 (02 GF* r1c0) (03 GF* r2c0) r3c0).
  pose proof (distr_gf_09_four r0c0 r1c0 (02 GF* r2c0) (03 GF* r3c0)).
  pose proof (distr_gf_0e_four (03 GF* r0c0) r1c0 r2c0 (02 GF* r3c0)).
  rewrite H47. rewrite H48. rewrite H49. rewrite H50.
  rewrite consolidate_16_xor_bytes.
  rewrite d''_a_eq_zb. rewrite d''_b_eq_zb. rewrite d''_c_eq_zb.
  rewrite d''_d_eq_d. rewrite xor_byte_zb.

  pose proof (distr_gf_0b_four (02 GF* r0c1) (03 GF* r1c1) r2c1 r3c1).
  pose proof (distr_gf_0d_four r0c1 (02 GF* r1c1) (03 GF* r2c1) r3c1).
  pose proof (distr_gf_09_four r0c1 r1c1 (02 GF* r2c1) (03 GF* r3c1)).
  pose proof (distr_gf_0e_four (03 GF* r0c1) r1c1 r2c1 (02 GF* r3c1)).
  rewrite H51. rewrite H52. rewrite H53. rewrite H54.
  rewrite consolidate_16_xor_bytes.
  rewrite d''_a_eq_zb. rewrite d''_b_eq_zb. rewrite d''_c_eq_zb.
  rewrite d''_d_eq_d. rewrite xor_byte_zb.

  pose proof (distr_gf_0b_four (02 GF* r0c2) (03 GF* r1c2) r2c2 r3c2).
  pose proof (distr_gf_0d_four r0c2 (02 GF* r1c2) (03 GF* r2c2) r3c2).
  pose proof (distr_gf_09_four r0c2 r1c2 (02 GF* r2c2) (03 GF* r3c2)).
  pose proof (distr_gf_0e_four (03 GF* r0c2) r1c2 r2c2 (02 GF* r3c2)).
  rewrite H55. rewrite H56. rewrite H57. rewrite H58.
  rewrite consolidate_16_xor_bytes.
  rewrite d''_a_eq_zb. rewrite d''_b_eq_zb. rewrite d''_c_eq_zb.
  rewrite d''_d_eq_d. rewrite xor_byte_zb.

  pose proof (distr_gf_0b_four (02 GF* r0c3) (03 GF* r1c3) r2c3 r3c3).
  pose proof (distr_gf_0d_four r0c3 (02 GF* r1c3) (03 GF* r2c3) r3c3).
  pose proof (distr_gf_09_four r0c3 r1c3 (02 GF* r2c3) (03 GF* r3c3)).
  pose proof (distr_gf_0e_four (03 GF* r0c3) r1c3 r2c3 (02 GF* r3c3)).
  rewrite H59. rewrite H60. rewrite H61. rewrite H62.
  rewrite consolidate_16_xor_bytes.
  rewrite d''_a_eq_zb. rewrite d''_b_eq_zb. rewrite d''_c_eq_zb.
  rewrite d''_d_eq_d. rewrite xor_byte_zb.

  reflexivity.
Qed.  

Definition rc (i: round) : byte :=
  match i with
  | r1 => bits8 s0 s0 s0 s0 s0 s0 s0 s1
  | r2 => bits8 s0 s0 s0 s0 s0 s0 s1 s0
  | r3 => bits8 s0 s0 s0 s0 s0 s1 s0 s0
  | r4 => bits8 s0 s0 s0 s0 s1 s0 s0 s0
  | r5 => bits8 s0 s0 s0 s1 s0 s0 s0 s0
  | r6 => bits8 s0 s0 s1 s0 s0 s0 s0 s0
  | r7 => bits8 s0 s1 s0 s0 s0 s0 s0 s0
  | r8 => bits8 s1 s0 s0 s0 s0 s0 s0 s0
  | r9 => bits8 s0 s0 s0 s1 s1 s0 s1 s1
  | r10 => bits8 s0 s0 s1 s1 s0 s1 s1 s0
  end.

Definition rc_inv (b : byte) : round :=
  match b with
  | bits8 s0 s0 s0 s0 s0 s0 s0 s1 => r1
  | bits8 s0 s0 s0 s0 s0 s0 s1 s0 => r2
  | bits8 s0 s0 s0 s0 s0 s1 s0 s0 => r3
  | bits8 s0 s0 s0 s0 s1 s0 s0 s0 => r4
  | bits8 s0 s0 s0 s1 s0 s0 s0 s0 => r5
  | bits8 s0 s0 s1 s0 s0 s0 s0 s0 => r6
  | bits8 s0 s1 s0 s0 s0 s0 s0 s0 => r7
  | bits8 s1 s0 s0 s0 s0 s0 s0 s0 => r8
  | bits8 s0 s0 s0 s1 s1 s0 s1 s1 => r9
  | bits8 s0 s0 s1 s1 s0 s1 s1 s0 => r10
  | bits8 _ _ _ _ _ _ _ _ => r1 (*default case to pass the Coq check *)
end.

Theorem rc_inv_inv : forall (i : round),
  rc_inv (rc i) = i.
Proof.
  intros i.
  destruct i.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


Definition rcon (i: round) : word :=
  bytes4 (rc i) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0)
.

Definition rcon_inv (w : word) : round :=
  match w with
  | bytes4 b1 b2 b3 b4 => rc_inv b1
  end.

Theorem rcon_inv_inv : forall (i : round),
  rcon_inv (rcon i) = i.
Proof.
  intros i.
  destruct i.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


Definition xor_words (w1 w2: word) : word :=
  match w1 with
  | bytes4 b0 b1 b2 b3 =>
      match w2 with bytes4 a0 a1 a2 a3 =>
                      bytes4 (xor_bytes b0 a0) (xor_bytes b1 a1) (xor_bytes b2 a2) (xor_bytes b3 a3)
      end
  end.

Theorem xor_xor_words : forall (w' w : word),
  xor_words w' (xor_words w' w) = w.
Proof.
  intros w' w.
  destruct w'.
  destruct w.
  simpl.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  reflexivity.
Qed.

Theorem xor_xor_words' : forall (w' w : word),
  xor_words (xor_words w w') w' = w.
Proof.
  intros w' w.
  destruct w'.
  destruct w.
  simpl.
  rewrite xor_xor_byte'.
  rewrite xor_xor_byte'.
  rewrite xor_xor_byte'.
  rewrite xor_xor_byte'.
  reflexivity.
Qed.

Definition rcon_word (i: round) (w: word): word :=
  xor_words w (rcon i)
.

Theorem rcon_word_inv : forall (i : round) (w : word),
  rcon_word i (rcon_word i w) = w.
Proof.
  intros i w.
  unfold rcon_word.
  unfold rcon.
  destruct i.
  - simpl. rewrite xor_xor_words'. reflexivity.
  - simpl. rewrite xor_xor_words'. reflexivity.
  - simpl. rewrite xor_xor_words'. reflexivity.
  - simpl. rewrite xor_xor_words'. reflexivity.
  - simpl. rewrite xor_xor_words'. reflexivity.
  - simpl. rewrite xor_xor_words'. reflexivity.
  - simpl. rewrite xor_xor_words'. reflexivity.
  - simpl. rewrite xor_xor_words'. reflexivity.
  - simpl. rewrite xor_xor_words'. reflexivity.
  - simpl. rewrite xor_xor_words'. reflexivity.
Qed.

Definition rot_word (w: word) : word :=
  match w with
  | bytes4 b0 b1 b2 b3 => bytes4 b1 b2 b3 b0
  end.

Definition rot_word_inv (w : word) : word :=
  match w with 
  | bytes4 b1 b2 b3 b0 => bytes4 b0 b1 b2 b3
  end.

Theorem rot_word_inv_inv : forall (w : word),
  rot_word_inv (rot_word w) = w.
Proof.
  intros w.
  destruct w.
  simpl.
  reflexivity.
Qed.

Definition sub_word (w:word) : word :=
  match w with
  | bytes4 b0 b1 b2 b3 => bytes4 (s_box b0) (s_box b1) (s_box b2) (s_box b3)
  end.

Definition sub_word_inv (w:word) : word :=
  match w with
  | bytes4 b0 b1 b2 b3 => bytes4 (inv_s_box b0) (inv_s_box b1) (inv_s_box b2) (inv_s_box b3)
  end.

Theorem sub_words_inv_inv : forall (w : word),
  sub_word_inv (sub_word w) = w.
Proof.
  intros w.
  destruct w.
  simpl.
  rewrite sbox_inv_sbox.
  rewrite sbox_inv_sbox.
  rewrite sbox_inv_sbox.
  rewrite sbox_inv_sbox.
  reflexivity.
Qed.


(* key type that contains 4 words. it's easier to use this than to manipulate matrices to craete round keys *)

Inductive key_t : Type :=
  | keywords (w1 w2 w3 w4 : word)
.

(*method to convert a matrix to type key_t*)

Definition matrix_to_keyt (k : matrix) : key_t :=
  match k with 
  | bytes16 b11 b12 b13 b14
            b21 b22 b23 b24
            b31 b32 b33 b34
            b41 b42 b43 b44 => keywords (bytes4 b11 b12 b13 b14) (bytes4 b21 b22 b23 b24) (bytes4 b31 b32 b33 b34) (bytes4 b41 b42 b43 b44)
  end.

(*method to convert from key_t to matrix*)

Definition keyt_to_matrix (k : key_t) : matrix :=
  match k with keywords w1 w2 w3 w4 =>
  match w1 with bytes4 b11 b12 b13 b14 =>
  match w2 with bytes4 b21 b22 b23 b24 =>
  match w3 with bytes4 b31 b32 b33 b34 =>
  match w4 with bytes4 b41 b42 b43 b44 => bytes16 b11 b12 b13 b14
                                                  b21 b22 b23 b24
                                                  b31 b32 b33 b34
                                                  b41 b42 b43 b44
  end end end end end.

(*proofs showing converting from matrix to key_t and vice versa is correct *)

Theorem matrix_to_keyt_inv : forall (k : matrix),
  keyt_to_matrix (matrix_to_keyt k) = k.
Proof.
  intros k.
  destruct k.
  simpl. reflexivity.
Qed.

Theorem keyt_to_matrix_inv : forall (k : key_t),
  matrix_to_keyt (keyt_to_matrix k) = k.
Proof.
  intros k.
  destruct k.
  destruct w1.
  destruct w2.
  destruct w3.
  destruct w4.
  simpl. reflexivity.
Qed.

(*function that applies rotate word, sub word and rcon word to the first word of the round key*)

Definition first_w_in_rk (i : round) (w : word) : word :=
  rot_word (sub_word (rcon_word i w))
.

Definition first_w_in_rk_inv (i : round) (w : word) : word :=
  rcon_word i (sub_word_inv (rot_word_inv w)).

Theorem first_w_in_rk_invertable : forall (i : round) (w : word),
  first_w_in_rk_inv i (first_w_in_rk i w) = w.
Proof.
  intros i w.
  unfold first_w_in_rk_inv.
  unfold first_w_in_rk.
  rewrite rot_word_inv_inv.
  rewrite sub_words_inv_inv.
  rewrite rcon_word_inv.
  reflexivity.
Qed.

(*round key 0, which just returns the key itself. serves as a reminder that the key itself is first xored with the plain text *)

Definition rk0 (k : matrix) : matrix :=
  k
.

(*This method takes the current round number, and the previous round key to generate the new round key. This doesn't apply to round 0. *)

Definition rk (i : round) (k : key_t) : key_t :=
  match k with
  | keywords w1 w2 w3 w4 => keywords (xor_words (first_w_in_rk i w4) w1)
                            (xor_words (xor_words (first_w_in_rk i w4) w1) w2)
                            (xor_words (xor_words (xor_words (first_w_in_rk i w4) w1) w2) w3)
                            (xor_words (xor_words (xor_words (xor_words (first_w_in_rk i w4) w1) w2) w3) w4)
  end.

(*the following methods takes the original key to produce the round key*)

Definition rk1 (k : matrix) : matrix :=
  keyt_to_matrix (rk r1 (matrix_to_keyt k)).

Definition rk2 (k : matrix) : matrix :=
  keyt_to_matrix (rk r2 (matrix_to_keyt (rk1 k))).

Definition rk3 (k : matrix) : matrix :=
  keyt_to_matrix (rk r3 (matrix_to_keyt (rk2 k))).

Definition rk4 (k : matrix) : matrix :=
  keyt_to_matrix (rk r4 (matrix_to_keyt (rk3 k))).

Definition rk5 (k : matrix) : matrix :=
  keyt_to_matrix (rk r5 (matrix_to_keyt (rk4 k))).

Definition rk6 (k : matrix) : matrix :=
  keyt_to_matrix (rk r6 (matrix_to_keyt (rk5 k))).

Definition rk7 (k : matrix) : matrix :=
  keyt_to_matrix (rk r7 (matrix_to_keyt (rk6 k))).

Definition rk8 (k : matrix) : matrix :=
  keyt_to_matrix (rk r8 (matrix_to_keyt (rk7 k))).

Definition rk9 (k : matrix) : matrix :=
  keyt_to_matrix (rk r9 (matrix_to_keyt (rk8 k))).

Definition rk10 (k : matrix) : matrix :=
  keyt_to_matrix (rk r10 (matrix_to_keyt (rk9 k))).

Definition add_round_key (k: matrix) (state: matrix) :=
  match k with
  | bytes16 k00 k01 k02 k03
            k10 k11 k12 k13
            k20 k21 k22 k23
            k30 k31 k32 k33 =>
      match state with
      | bytes16 s00 s01 s02 s03
                s10 s11 s12 s13
                s20 s21 s22 s23
                s30 s31 s32 s33 =>
          bytes16 (xor_bytes k00 s00) (xor_bytes k01 s01) (xor_bytes k02 s02) (xor_bytes k03 s03)
                  (xor_bytes k10 s10) (xor_bytes k11 s11) (xor_bytes k12 s12) (xor_bytes k13 s13)
                  (xor_bytes k20 s20) (xor_bytes k21 s21) (xor_bytes k22 s22) (xor_bytes k23 s23)
                  (xor_bytes k30 s30) (xor_bytes k31 s31) (xor_bytes k32 s32) (xor_bytes k33 s33)
      end
  end.

Definition xor_matrices (m1 m2: matrix) :=
  add_round_key m1 m2
.


Theorem xor_xor_matrix: forall state state': matrix,
    add_round_key state' (add_round_key state' state) = state.
Proof.
  intros s' s.
  destruct s'. destruct s.
  simpl.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  rewrite xor_xor_byte.
  reflexivity.
Qed.

Definition key0 (k:matrix) :=
  rk0 k
.

Definition key1 (k:matrix) :=
  rk1 k
.

Definition key2 (k:matrix) :=
  rk2 k
.

Definition key3 (k:matrix) :=
  rk3 k
.

Definition key4 (k:matrix) :=
  rk4 k
.

Definition key5 (k:matrix) :=
  rk5 k
.

Definition key6 (k:matrix) :=
  rk6 k
.

Definition key7 (k:matrix) :=
  rk7 k
.

Definition key8 (k:matrix) :=
  rk8 k
.

Definition key9 (k:matrix) :=
  rk9 k
.

Definition key10 (k:matrix) :=
  rk10 k
.

Definition enc_round1 (k s: matrix) : matrix :=
  add_round_key (key1 k) (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round2 (k s: matrix) : matrix :=
  add_round_key (key2 k) (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round3 (k s: matrix) : matrix :=
  add_round_key (key3 k) (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round4 (k s: matrix) : matrix :=
  add_round_key (key4 k) (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round5 (k s: matrix) : matrix :=
  add_round_key (key5 k) (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round6 (k s: matrix) : matrix :=
  add_round_key (key6 k) (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round7 (k s: matrix) : matrix :=
  add_round_key (key7 k) (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round8 (k s: matrix) : matrix :=
  add_round_key (key8 k) (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round9 (k s: matrix) : matrix :=
  add_round_key (key9 k) (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round10 (k s: matrix) : matrix :=
  add_round_key (key10 k) ((shift_rows (sub_bytes (s))))
.

Definition enc_aes (k m: matrix) : matrix :=
  enc_round10 k (enc_round9 k (enc_round8 k (enc_round7 k (enc_round6 k (enc_round5 k 
  (enc_round4 k (enc_round3 k (enc_round2 k (enc_round1 k (add_round_key (key0 k) m)))))))))) 
.


Definition dec_round1 (k s: matrix) : matrix :=
  inv_mix_columns (add_round_key (key9 k) (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round2 (k s: matrix) : matrix :=
  inv_mix_columns (add_round_key (key8 k) (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round3 (k s: matrix) : matrix :=
  inv_mix_columns (add_round_key (key7 k) (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round4 (k s: matrix) : matrix :=
  inv_mix_columns (add_round_key (key6 k) (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round5 (k s: matrix) : matrix :=
  inv_mix_columns (add_round_key (key5 k) (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round6 (k s: matrix) : matrix :=
  inv_mix_columns (add_round_key (key4 k) (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round7 (k s: matrix) : matrix :=
  inv_mix_columns (add_round_key (key3 k) (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round8 (k s: matrix) : matrix :=
  inv_mix_columns (add_round_key (key2 k) (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round9 (k s: matrix) : matrix :=
  inv_mix_columns (add_round_key (key1 k) (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round10 (k s: matrix) : matrix :=
  add_round_key (key0 k) (inv_sub_bytes (inv_shift_rows (s)))
.

Definition dec_aes (k c: matrix) : matrix :=
  dec_round10 k (dec_round9 k (dec_round8 k (dec_round7 k (dec_round6 k (dec_round5 k
  (dec_round4 k (dec_round3 k (dec_round2 k (dec_round1 k (add_round_key (key10 k) c))))))))))
.


Theorem aes_correctness: forall k: matrix, forall m: matrix,
    dec_aes k (enc_aes k m) = m.
Proof.
  intros k m.
  unfold enc_aes.
  unfold dec_aes.
  unfold enc_round10.
  rewrite xor_xor_matrix.
  unfold dec_round1.
  rewrite srows_inv_srows.
  rewrite sbytes_inv_sbytes.
  unfold enc_round9.
  rewrite xor_xor_matrix.
  rewrite mc_inv_mc.
  unfold dec_round2.
  rewrite srows_inv_srows.
  rewrite sbytes_inv_sbytes.
  unfold enc_round8.
  rewrite xor_xor_matrix.
  rewrite mc_inv_mc.
  unfold dec_round3.
  rewrite srows_inv_srows.
  rewrite sbytes_inv_sbytes.
  unfold enc_round7.
  rewrite xor_xor_matrix.
  rewrite mc_inv_mc.
  unfold dec_round4.
  rewrite srows_inv_srows.
  rewrite sbytes_inv_sbytes.
  unfold enc_round6.
  rewrite xor_xor_matrix.
  rewrite mc_inv_mc.
  unfold dec_round5.
  rewrite srows_inv_srows.
  rewrite sbytes_inv_sbytes.
  unfold enc_round5.
  rewrite xor_xor_matrix.
  rewrite mc_inv_mc.
  unfold dec_round6.
  rewrite srows_inv_srows.
  rewrite sbytes_inv_sbytes.
  unfold enc_round4.
  rewrite xor_xor_matrix.
  rewrite mc_inv_mc.
  unfold dec_round7.
  rewrite srows_inv_srows.
  rewrite sbytes_inv_sbytes.
  unfold enc_round3.
  rewrite xor_xor_matrix.
  rewrite mc_inv_mc.
  unfold dec_round8.
  rewrite srows_inv_srows.
  rewrite sbytes_inv_sbytes.
  unfold enc_round2.
  rewrite xor_xor_matrix.
  rewrite mc_inv_mc.
  unfold dec_round9.
  rewrite srows_inv_srows.
  rewrite sbytes_inv_sbytes.
  unfold enc_round1.
  rewrite xor_xor_matrix.
  rewrite mc_inv_mc.
  unfold dec_round10.
  rewrite srows_inv_srows.
  rewrite sbytes_inv_sbytes.
  rewrite xor_xor_matrix.
  reflexivity.
Qed.

Inductive blocks :=
| B0 (s: matrix)
| BS (s: matrix) (b: blocks)
.

Fixpoint enc_aes_ecb (key: matrix) (message: blocks):  blocks:=
  match message with
  | B0 s => B0 (enc_aes key s)
  | BS s b => BS (enc_aes key s) (enc_aes_ecb key b)
  end.

Fixpoint dec_aes_ecb (key: matrix) (ciphertext: blocks): blocks :=
  match ciphertext with
  | B0 s => B0 (dec_aes key s)
  | BS s b => BS (dec_aes key s) (dec_aes_ecb key b)
  end.

Theorem aes_ecb_correctness: forall key: matrix, forall message: blocks,
    dec_aes_ecb key (enc_aes_ecb key message) = message.
Proof.
  intros k m.
  induction m as [|ms mb Hm].
  - simpl. rewrite aes_correctness. reflexivity.
  - simpl. rewrite Hm. rewrite aes_correctness.
    reflexivity.
Qed.

Fixpoint enc_aes_cbc (key iv: matrix) (message: blocks): blocks :=
  match message with
  | B0 s => B0 (enc_aes key (xor_matrices iv s))
  | BS s b => let niv:=enc_aes key (xor_matrices iv s) in
              BS niv (enc_aes_cbc key niv b)
  end.

Fixpoint dec_aes_cbc (key iv: matrix) (ciphertext: blocks): blocks :=
  match ciphertext with
  | B0 s => B0 (xor_matrices iv (dec_aes key s))
  | BS s b => let d:=dec_aes key s in
              BS (xor_matrices iv d) (dec_aes_cbc key s b)
  end.
 
Theorem aes_cbc_correctness: forall key iv: matrix, forall message: blocks,
    dec_aes_cbc key iv (enc_aes_cbc key iv (message)) = message.
Proof.
  intros key iv message. generalize dependent iv.
  induction message as [|ms mb Hm].
  - simpl. intros iv. rewrite aes_correctness.
    rewrite xor_xor_matrix. reflexivity.
  - simpl. intros iv. rewrite aes_correctness.
    rewrite xor_xor_matrix.
    rewrite Hm. reflexivity.
Qed.
