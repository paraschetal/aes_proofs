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
         
Definition xor_bytes (b a: byte) : byte :=
  match b with
  | bits8 b7 b6 b5 b4 b3 b2 b1 b0 =>
      match a with
      | bits8 a7 a6 a5 a4 a3 a2 a1 a0 =>
          bits8 (xor_bits b7 a7) (xor_bits b6 a6) (xor_bits b5 a5) (xor_bits b4 a4) (xor_bits b3 a3) (xor_bits b2 a2) (xor_bits b1 a1) (xor_bits b0 a0)
      end
  end.


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
  intros b.
  destruct b.
  * destruct b0.
    ** destruct b1.
       *** destruct b2.
           **** destruct b3.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
           **** destruct b3.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
       *** destruct b2.
                **** destruct b3.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
           **** destruct b3.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
    ** destruct b1.
       *** destruct b2.
           **** destruct b3.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
           **** destruct b3.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
       *** destruct b2.
                **** destruct b3.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
           **** destruct b3.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ***** destruct b4.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ****** destruct b5.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******* destruct b6.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
                ******** destruct b7.
                ********* reflexivity.
                ********* reflexivity.
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

(*
Inductive iw :=
| i0 
| i1
| i2
| i3
| i4
| i5
| i6
| i7
| i8
| i9
| i10
| i11
| i12
| i13
| i14
| i15
| i16
| i17
| i18
| i19
| i20
| i21
| i22
| i23
| i24
| i25
| i26
| i27
| i28
| i29
| i30
| i31
| i32
| i33
| i34
| i35
| i36
| i37
| i38
| i39
| i40
| i41
| i42
| i43
.
*)                


(*
Program Fixpoint wi (k:key_t) (i: iw) : word :=
  match i with
  | i0 => match k with
          | kwords w0 _ _ _ => w0
          end
  | i1 => match k with
          | kwords _ w1 _ _ => w1
          end
  | i2 => match k with
          | kwords _ _ w2 _ => w2
          end
  | i3 => match k with
          | kwords _ _ _ w3 => w3
          end
  | i4 => rcon_word r1 (sub_word (rot_word (wi k i3)))
  | i5 => xor_words (wi k i4) (wi k i1)
  | i6 => xor_words (wi k i5) (wi k i2)
  | i7 => xor_words (wi k i6) (wi k i3)
  | i8 => rcon_word r2 (sub_word (rot_word (wi k i7)))
  | i9 => xor_words (wi k i8) (wi k i5)
  | i10 => xor_words (wi k i9) (wi k i6)
  | i11 => xor_words (wi k i10) (wi k i7)
  | i12 => rcon_word r3 (sub_word (rot_word (wi k i11)))
  | i13 => xor_words (wi k i12) (wi k i9)
  | i14 => xor_words (wi k i13) (wi k i10)
  | i15 => xor_words (wi k i14) (wi k i11)
  | i16 => rcon_word r4 (sub_word (rot_word (wi k i15)))
  | i17 => xor_words (wi k i16) (wi k i13)
  | i18 => xor_words (wi k i17) (wi k i14)
  | i19 => xor_words (wi k i18) (wi k i15)
  | i20 => rcon_word r5 (sub_word (rot_word (wi k i19)))
  | i21 => xor_words (wi k i20) (wi k i17)
  | i22 => xor_words (wi k i21) (wi k i18)
  | i23 => xor_words (wi k i22) (wi k i19)
  | i24 => rcon_word r6 (sub_word (rot_word (wi k i23)))
  | i25 => xor_words (wi k i24) (wi k i21)
  | i26 => xor_words (wi k i25) (wi k i22)
  | i27 => xor_words (wi k i26) (wi k i23)
  | i28 => rcon_word r7 (sub_word (rot_word (wi k i27)))
  | i29 => xor_words (wi k i28) (wi k i25)
  | i30 => xor_words (wi k i29) (wi k i26)
  | i31 => xor_words (wi k i30) (wi k i27)
  | i32 => rcon_word r8 (sub_word (rot_word (wi k i31)))
  | i33 => xor_words (wi k i32) (wi k i29)
  | i34 => xor_words (wi k i33) (wi k i30)
  | i35 => xor_words (wi k i34) (wi k i31)
  | i36 => rcon_word r9 (sub_word (rot_word (wi k i35)))
  | i37 => xor_words (wi k i36) (wi k i33)
  | i38 => xor_words (wi k i37) (wi k i34)
  | i39 => xor_words (wi k i38) (wi k i35)
  | i40 => rcon_word r10 (sub_word (rot_word (wi k i39)))
  | i41 => xor_words (wi k i40) (wi k i37)
  | i42 => xor_words (wi k i41) (wi k i38)
  | i43 => xor_words (wi k i42) (wi k i39)
  end.
*)
(*
Program Fixpoint wi (k:key_t) (i: nat) (i_bound: i <= 43) : word :=
  match i with
  | 0 => match k with
          | kwords w0 _ _ _ => w0
          end
  | 1 => match k with
          | kwords _ w1 _ _ => w1
          end
  | 2 => match k with
          | kwords _ _ w2 _ => w2
          end
  | 3 => match k with
          | kwords _ _ _ w3 => w3
          end
  | 4 => rcon_word r1 (sub_word (rot_word (wi k 3)))
  | 5 => xor_words (wi k 4) (wi k 1)
  | 6 => xor_words (wi k 5) (wi k 2)
  | 7 => xor_words (wi k 6) (wi k 3)
  | 8 => rcon_word r2 (sub_word (rot_word (wi k 7)))
  | 9 => xor_words (wi k 8) (wi k 5)
  | 10 => xor_words (wi k 9) (wi k 6)
  | 11 => xor_words (wi k 10) (wi k 7)
  | 12 => rcon_word r3 (sub_word (rot_word (wi k 11)))
  | 13 => xor_words (wi k 12) (wi k 9)
  | 14 => xor_words (wi k 13) (wi k 10)
  | 15 => xor_words (wi k 14) (wi k 11)
  | 16 => rcon_word r4 (sub_word (rot_word (wi k 15)))
  | 17 => xor_words (wi k 16) (wi k 13)
  | 18 => xor_words (wi k 17) (wi k 14)
  | 19 => xor_words (wi k 18) (wi k 15)
  | 20 => rcon_word r5 (sub_word (rot_word (wi k 19)))
  | 21 => xor_words (wi k 20) (wi k 17)
  | 22 => xor_words (wi k 21) (wi k 18)
  | 23 => xor_words (wi k 22) (wi k 19)
  | 24 => rcon_word r6 (sub_word (rot_word (wi k 23)))
  | 25 => xor_words (wi k 24) (wi k 21)
  | 26 => xor_words (wi k 25) (wi k 22)
  | 27 => xor_words (wi k 26) (wi k 23)
  | 28 => rcon_word r7 (sub_word (rot_word (wi k 27)))
  | 29 => xor_words (wi k 28) (wi k 25)
  | 30 => xor_words (wi k 29) (wi k 26)
  | 31 => xor_words (wi k 30) (wi k 27)
  | 32 => rcon_word r8 (sub_word (rot_word (wi k 31)))
  | 33 => xor_words (wi k 32) (wi k 29)
  | 34 => xor_words (wi k 33) (wi k 30)
  | 35 => xor_words (wi k 34) (wi k 31)
  | 36 => rcon_word r9 (sub_word (rot_word (wi k 35)))
  | 37 => xor_words (wi k 36) (wi k 33)
  | 38 => xor_words (wi k 37) (wi k 34)
  | 39 => xor_words (wi k 38) (wi k 35)
  | 40 => rcon_word r10 (sub_word (rot_word (wi k 39)))
  | 41 => xor_words (wi k 40) (wi k 37)
  | 42 => xor_words (wi k 41) (wi k 38)
  | 43 |_ => xor_words (wi k 42) (wi k 39)
  end.

*)

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
Definition mix_columns (state: matrix) : matrix :=
  state.

Definition inv_mix_columns (state: matrix) : matrix :=
  state.

Theorem mc_inv_mc: forall state: matrix,
    inv_mix_columns (mix_columns (state)) = state.
Proof.
Admitted.

(*TODO: round keys*)

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

Definition zb: byte :=
  bits8 s0 s0 s0 s0 s0 s0 s0 s0
.

 
(*this is the key to be used for AES encryption and decryption*)
Definition key : matrix :=
  bytes16 zb zb zb zb
          zb zb zb zb
          zb zb zb zb
          zb zb zb zb
.

Definition starkey: matrix :=
  bytes16 zb zb zb zb
          zb zb zb zb
          zb zb zb zb
          zb zb zb zb
.


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

Definition key0 :=
  rk0 key
.

Definition key1 :=
  rk1 key
.

Definition key2 :=
  rk2 key
.

Definition key3 :=
  rk3 key
.

Definition key4 :=
  rk4 key
.

Definition key5 :=
  rk5 key
.

Definition key6 :=
  rk6 key
.

Definition key7 :=
  rk7 key
.

Definition key8 :=
  rk8 key
.

Definition key9 :=
  rk9 key
.

Definition key10 :=
  rk10 key
.

Definition enc_round1 (s: matrix) : matrix :=
  add_round_key key1 (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round2 (s: matrix) : matrix :=
  add_round_key key2 (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round3 (s: matrix) : matrix :=
  add_round_key key3 (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round4 (s: matrix) : matrix :=
  add_round_key key4 (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round5 (s: matrix) : matrix :=
  add_round_key key5 (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round6 (s: matrix) : matrix :=
  add_round_key key6 (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round7 (s: matrix) : matrix :=
  add_round_key key7 (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round8 (s: matrix) : matrix :=
  add_round_key key8 (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round9 (s: matrix) : matrix :=
  add_round_key key9 (mix_columns (shift_rows (sub_bytes (s))))
.

Definition enc_round10 (s: matrix) : matrix :=
  add_round_key key10 ((shift_rows (sub_bytes (s))))
.

Definition enc_aes (k m: matrix) : matrix :=
  enc_round10 (enc_round9 (enc_round8 (enc_round7 (enc_round6 (enc_round5
  (enc_round4 (enc_round3 (enc_round2 (enc_round1 (add_round_key key0 m)))))))))) 
.

Definition message : matrix :=
  bytes16 zb zb zb zb
          zb zb zb zb
          zb zb zb zb
          zb zb zb zb
.

Compute enc_aes key message.

Definition cipher : matrix :=
  bytes16 (bits8 s1 s1 s0 s0 s1 s1 s0 s0) (bits8 s0 s0 s1 s0 s0 s1 s0 s1) (bits8 s0 s1 s1 s0 s0 s0 s0 s1)
         (bits8 s1 s1 s0 s1 s0 s1 s1 s1) (bits8 s1 s1 s1 s0 s0 s0 s0 s1) (bits8 s0 s1 s0 s1 s1 s1 s0 s1)
         (bits8 s1 s1 s0 s1 s1 s1 s0 s0) (bits8 s1 s1 s1 s0 s0 s0 s1 s1) (bits8 s0 s1 s1 s1 s1 s0 s1 s1)
         (bits8 s1 s1 s1 s1 s0 s0 s1 s1) (bits8 s0 s0 s0 s1 s0 s1 s0 s1) (bits8 s0 s1 s0 s1 s1 s1 s1 s0)
         (bits8 s0 s1 s1 s0 s1 s0 s1 s1) (bits8 s1 s1 s0 s1 s0 s0 s0 s0) (bits8 s0 s1 s1 s1 s1 s0 s0 s0)
         (bits8 s0 s1 s0 s1 s1 s0 s0 s1)
.

Definition dec_round1 (s: matrix) : matrix :=
  inv_mix_columns (add_round_key key9 (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round2 (s: matrix) : matrix :=
  inv_mix_columns (add_round_key key8 (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round3 (s: matrix) : matrix :=
  inv_mix_columns (add_round_key key7 (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round4 (s: matrix) : matrix :=
  inv_mix_columns (add_round_key key6 (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round5 (s: matrix) : matrix :=
  inv_mix_columns (add_round_key key5 (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round6 (s: matrix) : matrix :=
  inv_mix_columns (add_round_key key4 (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round7 (s: matrix) : matrix :=
  inv_mix_columns (add_round_key key3 (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round8 (s: matrix) : matrix :=
  inv_mix_columns (add_round_key key2 (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round9 (s: matrix) : matrix :=
  inv_mix_columns (add_round_key key1 (inv_sub_bytes (inv_shift_rows (s))))
.

Definition dec_round10 (s: matrix) : matrix :=
  add_round_key key0 (inv_sub_bytes (inv_shift_rows (s)))
.

Definition dec_aes (k c: matrix) : matrix :=
  dec_round10 (dec_round9 (dec_round8 (dec_round7 (dec_round6 (dec_round5
  (dec_round4 (dec_round3 (dec_round2 (dec_round1 (add_round_key key10 c))))))))))
.

Compute dec_aes key (enc_aes key message).

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

    