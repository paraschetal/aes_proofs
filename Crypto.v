(*Require Import Coq.Init.Byte.*)
Require Import Program.
Require Import Nat.
Inductive binary : Type :=
| s0
| s1
.

Inductive nibble: Type :=
| bits4 (b0 b1 b2 b3: binary)
.

Inductive byte : Type :=
| bits8 (b0 b1 b2 b3 b4 b5 b6 b7 : binary)
.

Definition ms_nibble (b:byte) : nibble :=
  match b with
  | bits8 b0 b1 b2 b3 _ _ _ _  => bits4 b0 b1 b2 b3
end.

Definition ls_nibble (b:byte) : nibble :=
  match b with
  | bits8 _ _ _ _ b4 b5 b6 b7 => bits4 b4 b5 b6 b7
  end.


Definition xor_bits (b1 b2: binary) : binary :=
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
| word8 (w0 w1 w2 w3: word)
.


Inductive state : Type :=
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

Inductive key_t :=
  kwords (w0 w1 w2 w3: word)
.


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
                
Definition rc (i: round) : byte :=
  match i with
  | r1 => bits8 s0 s0 s0 s0 s0 s0 s0 s1
  | r2 => bits8 s0 s0 s0 s0 s0 s0 s1 s0
  | r3 => bits8 s0 s0 s0 s0 s0 s1 s0 s0
  | r4 => bits8 s0 s0 s0 s0 s0 s1 s0 s0
  | r5 => bits8 s0 s0 s0 s1 s0 s0 s0 s0
  | r6 => bits8 s0 s0 s1 s0 s0 s0 s0 s0
  | r7 => bits8 s0 s1 s0 s0 s0 s0 s0 s0
  | r8 => bits8 s1 s0 s0 s0 s0 s0 s0 s0
  | r9 => bits8 s0 s0 s0 s1 s1 s0 s1 s1
  | r10 => bits8 s0 s0 s1 s1 s0 s1 s1 s0
  end.

Definition rcon (i: round) : word :=
  bytes4 (rc i) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0)
.

Definition xor_words (w1 w2: word) : word :=
  match w1 with
  | bytes4 b0 b1 b2 b3 =>
      match w2 with bytes4 a0 a1 a2 a3 =>
                      bytes4 (xor_bytes b0 a0) (xor_bytes b1 a1) (xor_bytes b2 a2) (xor_bytes b3 a3)
      end
  end.

Definition rot_word (w: word) : word :=
  match w with
  | bytes4 b0 b1 b2 b3 => bytes4 b1 b2 b3 b0
  end.

Definition sub_word (w:word) : word :=
  match w with
  | bytes4 b0 b1 b2 b3 => bytes4 (s_box b0) (s_box b1) (s_box b2) (s_box b3)
  end.

Definition rcon_word (i: round) (w: word): word :=
  xor_words w (rcon i)
.

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
Definition shift_rows (s: state) : state :=
  match s with
  | bytes16 r0c0 r0c1 r0c2 r0c3
            r1c0 r1c1 r1c2 r1c3
            r2c0 r2c1 r2c2 r2c3
            r3c0 r3c1 r3c2 r3c3 => bytes16 r0c0 r0c1 r0c2 r0c3
                                           r1c1 r1c2 r1c3 r1c0
                                           r2c2 r2c3 r2c0 r2c1
                                           r3c3 r3c0 r3c1 r3c2
  end.

Definition inv_shift_rows (s: state) : state :=
  match s with
  | bytes16 r0c0 r0c1 r0c2 r0c3
            r1c0 r1c1 r1c2 r1c3
            r2c0 r2c1 r2c2 r2c3
            r3c0 r3c1 r3c2 r3c3 => bytes16 r0c0 r0c1 r0c2 r0c3
                                           r1c3 r1c0 r1c1 r1c2
                                           r2c2 r2c3 r2c0 r2c1
                                           r3c1 r3c2 r3c3 r3c0
  end.

Theorem srows_inv_srows: forall s: state,
    inv_shift_rows (shift_rows (s)) = s.
Proof.
  intros s.
  destruct s.
  - simpl. reflexivity.
Qed.

Definition sub_bytes (s: state) : state :=
  match s with
  | bytes16 r0c0 r0c1 r0c2 r0c3
            r1c0 r1c1 r1c2 r1c3
            r2c0 r2c1 r2c2 r2c3
            r3c0 r3c1 r3c2 r3c3 => bytes16 (s_box r0c0) (s_box r0c1) (s_box r0c2) (s_box r0c3)
                                           (s_box r1c0) (s_box r1c1) (s_box r1c2) (s_box r1c3)
                                           (s_box r2c0) (s_box r2c1) (s_box r2c2) (s_box r2c3)
                                           (s_box r3c0) (s_box r3c1) (s_box r3c2) (s_box r3c3)
  end.

Definition inv_sub_bytes (s: state) : state :=
  match s with
  | bytes16 r0c0 r0c1 r0c2 r0c3
            r1c0 r1c1 r1c2 r1c3
            r2c0 r2c1 r2c2 r2c3
            r3c0 r3c1 r3c2 r3c3 => bytes16 (inv_s_box r0c0) (inv_s_box r0c1) (inv_s_box r0c2) (inv_s_box r0c3)
                                           (inv_s_box r1c0) (inv_s_box r1c1) (inv_s_box r1c2) (inv_s_box r1c3)
                                           (inv_s_box r2c0) (inv_s_box r2c1) (inv_s_box r2c2) (inv_s_box r2c3)
                                           (inv_s_box r3c0) (inv_s_box r3c1) (inv_s_box r3c2) (inv_s_box r3c3)
  end.

Theorem sbytes_inv_sbytes: forall s: state,
    inv_sub_bytes (sub_bytes (s)) = s.
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



