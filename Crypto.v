(*Require Import Coq.Init.Byte.*)

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


Inductive matrix : Type :=
| bytes16 (r0c0 r0c1 r0c2 r0c3
           r1c0 r1c1 r1c2 r1c3
           r2c0 r2c1 r2c2 r2c3
           r3c0 r3c1 r3c2 r3c3: byte)
.

Definition rot_word (w: word) : word :=
  match w with
  | bytes4 b0 b1 b2 b3 => bytes4 b1 b2 b3 b0
  end.

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
