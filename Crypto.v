(*Require Import Coq.Init.Byte.*)
Require Import Program.
Require Import Nat.
Require Import Arith.
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

Notation "A X*OR B" := (xor_bytes A B) (at level 75, right associativity).

Definition bit_to_nat(a: bit) : nat :=
  match a with
  | s0 => 0
  | s1 => 1
  end.

Definition byte_to_nat(a : byte) : nat := 
  match a with 
    | bits8 b7 b6 b5 b4 b3 b2 b1 b0 =>
      (2*(2*(2*(2*(2*(2*((2* (bit_to_nat b0))+bit_to_nat b1))+bit_to_nat b2)+bit_to_nat b3)+bit_to_nat b4)+bit_to_nat b5)+bit_to_nat b6)+bit_to_nat b7
  end.

Definition nat_to_byte(a : nat) : byte := 
match a with 
| 0 => bits8 s0 s0 s0 s0 s0 s0 s0 s0  
| 1 => bits8 s0 s0 s0 s0 s0 s0 s0 s1  
| 2 => bits8 s0 s0 s0 s0 s0 s0 s1 s0  
| 3 => bits8 s0 s0 s0 s0 s0 s0 s1 s1  
| 4 => bits8 s0 s0 s0 s0 s0 s1 s0 s0  
| 5 => bits8 s0 s0 s0 s0 s0 s1 s0 s1  
| 6 => bits8 s0 s0 s0 s0 s0 s1 s1 s0  
| 7 => bits8 s0 s0 s0 s0 s0 s1 s1 s1  
| 8 => bits8 s0 s0 s0 s0 s1 s0 s0 s0  
| 9 => bits8 s0 s0 s0 s0 s1 s0 s0 s1  
| 10 => bits8 s0 s0 s0 s0 s1 s0 s1 s0  
| 11 => bits8 s0 s0 s0 s0 s1 s0 s1 s1  
| 12 => bits8 s0 s0 s0 s0 s1 s1 s0 s0  
| 13 => bits8 s0 s0 s0 s0 s1 s1 s0 s1  
| 14 => bits8 s0 s0 s0 s0 s1 s1 s1 s0  
| 15 => bits8 s0 s0 s0 s0 s1 s1 s1 s1  
| 16 => bits8 s0 s0 s0 s1 s0 s0 s0 s0  
| 17 => bits8 s0 s0 s0 s1 s0 s0 s0 s1  
| 18 => bits8 s0 s0 s0 s1 s0 s0 s1 s0  
| 19 => bits8 s0 s0 s0 s1 s0 s0 s1 s1  
| 20 => bits8 s0 s0 s0 s1 s0 s1 s0 s0  
| 21 => bits8 s0 s0 s0 s1 s0 s1 s0 s1  
| 22 => bits8 s0 s0 s0 s1 s0 s1 s1 s0  
| 23 => bits8 s0 s0 s0 s1 s0 s1 s1 s1  
| 24 => bits8 s0 s0 s0 s1 s1 s0 s0 s0  
| 25 => bits8 s0 s0 s0 s1 s1 s0 s0 s1  
| 26 => bits8 s0 s0 s0 s1 s1 s0 s1 s0  
| 27 => bits8 s0 s0 s0 s1 s1 s0 s1 s1  
| 28 => bits8 s0 s0 s0 s1 s1 s1 s0 s0  
| 29 => bits8 s0 s0 s0 s1 s1 s1 s0 s1  
| 30 => bits8 s0 s0 s0 s1 s1 s1 s1 s0  
| 31 => bits8 s0 s0 s0 s1 s1 s1 s1 s1  
| 32 => bits8 s0 s0 s1 s0 s0 s0 s0 s0  
| 33 => bits8 s0 s0 s1 s0 s0 s0 s0 s1  
| 34 => bits8 s0 s0 s1 s0 s0 s0 s1 s0  
| 35 => bits8 s0 s0 s1 s0 s0 s0 s1 s1  
| 36 => bits8 s0 s0 s1 s0 s0 s1 s0 s0  
| 37 => bits8 s0 s0 s1 s0 s0 s1 s0 s1  
| 38 => bits8 s0 s0 s1 s0 s0 s1 s1 s0  
| 39 => bits8 s0 s0 s1 s0 s0 s1 s1 s1  
| 40 => bits8 s0 s0 s1 s0 s1 s0 s0 s0  
| 41 => bits8 s0 s0 s1 s0 s1 s0 s0 s1  
| 42 => bits8 s0 s0 s1 s0 s1 s0 s1 s0  
| 43 => bits8 s0 s0 s1 s0 s1 s0 s1 s1  
| 44 => bits8 s0 s0 s1 s0 s1 s1 s0 s0  
| 45 => bits8 s0 s0 s1 s0 s1 s1 s0 s1  
| 46 => bits8 s0 s0 s1 s0 s1 s1 s1 s0  
| 47 => bits8 s0 s0 s1 s0 s1 s1 s1 s1  
| 48 => bits8 s0 s0 s1 s1 s0 s0 s0 s0  
| 49 => bits8 s0 s0 s1 s1 s0 s0 s0 s1  
| 50 => bits8 s0 s0 s1 s1 s0 s0 s1 s0  
| 51 => bits8 s0 s0 s1 s1 s0 s0 s1 s1  
| 52 => bits8 s0 s0 s1 s1 s0 s1 s0 s0  
| 53 => bits8 s0 s0 s1 s1 s0 s1 s0 s1  
| 54 => bits8 s0 s0 s1 s1 s0 s1 s1 s0  
| 55 => bits8 s0 s0 s1 s1 s0 s1 s1 s1  
| 56 => bits8 s0 s0 s1 s1 s1 s0 s0 s0  
| 57 => bits8 s0 s0 s1 s1 s1 s0 s0 s1  
| 58 => bits8 s0 s0 s1 s1 s1 s0 s1 s0  
| 59 => bits8 s0 s0 s1 s1 s1 s0 s1 s1  
| 60 => bits8 s0 s0 s1 s1 s1 s1 s0 s0  
| 61 => bits8 s0 s0 s1 s1 s1 s1 s0 s1  
| 62 => bits8 s0 s0 s1 s1 s1 s1 s1 s0  
| 63 => bits8 s0 s0 s1 s1 s1 s1 s1 s1  
| 64 => bits8 s0 s1 s0 s0 s0 s0 s0 s0  
| 65 => bits8 s0 s1 s0 s0 s0 s0 s0 s1  
| 66 => bits8 s0 s1 s0 s0 s0 s0 s1 s0  
| 67 => bits8 s0 s1 s0 s0 s0 s0 s1 s1  
| 68 => bits8 s0 s1 s0 s0 s0 s1 s0 s0  
| 69 => bits8 s0 s1 s0 s0 s0 s1 s0 s1  
| 70 => bits8 s0 s1 s0 s0 s0 s1 s1 s0  
| 71 => bits8 s0 s1 s0 s0 s0 s1 s1 s1  
| 72 => bits8 s0 s1 s0 s0 s1 s0 s0 s0  
| 73 => bits8 s0 s1 s0 s0 s1 s0 s0 s1  
| 74 => bits8 s0 s1 s0 s0 s1 s0 s1 s0  
| 75 => bits8 s0 s1 s0 s0 s1 s0 s1 s1  
| 76 => bits8 s0 s1 s0 s0 s1 s1 s0 s0  
| 77 => bits8 s0 s1 s0 s0 s1 s1 s0 s1  
| 78 => bits8 s0 s1 s0 s0 s1 s1 s1 s0  
| 79 => bits8 s0 s1 s0 s0 s1 s1 s1 s1  
| 80 => bits8 s0 s1 s0 s1 s0 s0 s0 s0  
| 81 => bits8 s0 s1 s0 s1 s0 s0 s0 s1  
| 82 => bits8 s0 s1 s0 s1 s0 s0 s1 s0  
| 83 => bits8 s0 s1 s0 s1 s0 s0 s1 s1  
| 84 => bits8 s0 s1 s0 s1 s0 s1 s0 s0  
| 85 => bits8 s0 s1 s0 s1 s0 s1 s0 s1  
| 86 => bits8 s0 s1 s0 s1 s0 s1 s1 s0  
| 87 => bits8 s0 s1 s0 s1 s0 s1 s1 s1  
| 88 => bits8 s0 s1 s0 s1 s1 s0 s0 s0  
| 89 => bits8 s0 s1 s0 s1 s1 s0 s0 s1  
| 90 => bits8 s0 s1 s0 s1 s1 s0 s1 s0  
| 91 => bits8 s0 s1 s0 s1 s1 s0 s1 s1  
| 92 => bits8 s0 s1 s0 s1 s1 s1 s0 s0  
| 93 => bits8 s0 s1 s0 s1 s1 s1 s0 s1  
| 94 => bits8 s0 s1 s0 s1 s1 s1 s1 s0  
| 95 => bits8 s0 s1 s0 s1 s1 s1 s1 s1  
| 96 => bits8 s0 s1 s1 s0 s0 s0 s0 s0  
| 97 => bits8 s0 s1 s1 s0 s0 s0 s0 s1  
| 98 => bits8 s0 s1 s1 s0 s0 s0 s1 s0  
| 99 => bits8 s0 s1 s1 s0 s0 s0 s1 s1  
| 100 => bits8 s0 s1 s1 s0 s0 s1 s0 s0  
| 101 => bits8 s0 s1 s1 s0 s0 s1 s0 s1  
| 102 => bits8 s0 s1 s1 s0 s0 s1 s1 s0  
| 103 => bits8 s0 s1 s1 s0 s0 s1 s1 s1  
| 104 => bits8 s0 s1 s1 s0 s1 s0 s0 s0  
| 105 => bits8 s0 s1 s1 s0 s1 s0 s0 s1  
| 106 => bits8 s0 s1 s1 s0 s1 s0 s1 s0  
| 107 => bits8 s0 s1 s1 s0 s1 s0 s1 s1  
| 108 => bits8 s0 s1 s1 s0 s1 s1 s0 s0  
| 109 => bits8 s0 s1 s1 s0 s1 s1 s0 s1  
| 110 => bits8 s0 s1 s1 s0 s1 s1 s1 s0  
| 111 => bits8 s0 s1 s1 s0 s1 s1 s1 s1  
| 112 => bits8 s0 s1 s1 s1 s0 s0 s0 s0  
| 113 => bits8 s0 s1 s1 s1 s0 s0 s0 s1  
| 114 => bits8 s0 s1 s1 s1 s0 s0 s1 s0  
| 115 => bits8 s0 s1 s1 s1 s0 s0 s1 s1  
| 116 => bits8 s0 s1 s1 s1 s0 s1 s0 s0  
| 117 => bits8 s0 s1 s1 s1 s0 s1 s0 s1  
| 118 => bits8 s0 s1 s1 s1 s0 s1 s1 s0  
| 119 => bits8 s0 s1 s1 s1 s0 s1 s1 s1  
| 120 => bits8 s0 s1 s1 s1 s1 s0 s0 s0  
| 121 => bits8 s0 s1 s1 s1 s1 s0 s0 s1  
| 122 => bits8 s0 s1 s1 s1 s1 s0 s1 s0  
| 123 => bits8 s0 s1 s1 s1 s1 s0 s1 s1  
| 124 => bits8 s0 s1 s1 s1 s1 s1 s0 s0  
| 125 => bits8 s0 s1 s1 s1 s1 s1 s0 s1  
| 126 => bits8 s0 s1 s1 s1 s1 s1 s1 s0  
| 127 => bits8 s0 s1 s1 s1 s1 s1 s1 s1  
| 128 => bits8 s1 s0 s0 s0 s0 s0 s0 s0  
| 129 => bits8 s1 s0 s0 s0 s0 s0 s0 s1  
| 130 => bits8 s1 s0 s0 s0 s0 s0 s1 s0  
| 131 => bits8 s1 s0 s0 s0 s0 s0 s1 s1  
| 132 => bits8 s1 s0 s0 s0 s0 s1 s0 s0  
| 133 => bits8 s1 s0 s0 s0 s0 s1 s0 s1  
| 134 => bits8 s1 s0 s0 s0 s0 s1 s1 s0  
| 135 => bits8 s1 s0 s0 s0 s0 s1 s1 s1  
| 136 => bits8 s1 s0 s0 s0 s1 s0 s0 s0  
| 137 => bits8 s1 s0 s0 s0 s1 s0 s0 s1  
| 138 => bits8 s1 s0 s0 s0 s1 s0 s1 s0  
| 139 => bits8 s1 s0 s0 s0 s1 s0 s1 s1  
| 140 => bits8 s1 s0 s0 s0 s1 s1 s0 s0  
| 141 => bits8 s1 s0 s0 s0 s1 s1 s0 s1  
| 142 => bits8 s1 s0 s0 s0 s1 s1 s1 s0  
| 143 => bits8 s1 s0 s0 s0 s1 s1 s1 s1  
| 144 => bits8 s1 s0 s0 s1 s0 s0 s0 s0  
| 145 => bits8 s1 s0 s0 s1 s0 s0 s0 s1  
| 146 => bits8 s1 s0 s0 s1 s0 s0 s1 s0  
| 147 => bits8 s1 s0 s0 s1 s0 s0 s1 s1  
| 148 => bits8 s1 s0 s0 s1 s0 s1 s0 s0  
| 149 => bits8 s1 s0 s0 s1 s0 s1 s0 s1  
| 150 => bits8 s1 s0 s0 s1 s0 s1 s1 s0  
| 151 => bits8 s1 s0 s0 s1 s0 s1 s1 s1  
| 152 => bits8 s1 s0 s0 s1 s1 s0 s0 s0  
| 153 => bits8 s1 s0 s0 s1 s1 s0 s0 s1  
| 154 => bits8 s1 s0 s0 s1 s1 s0 s1 s0  
| 155 => bits8 s1 s0 s0 s1 s1 s0 s1 s1  
| 156 => bits8 s1 s0 s0 s1 s1 s1 s0 s0  
| 157 => bits8 s1 s0 s0 s1 s1 s1 s0 s1  
| 158 => bits8 s1 s0 s0 s1 s1 s1 s1 s0  
| 159 => bits8 s1 s0 s0 s1 s1 s1 s1 s1  
| 160 => bits8 s1 s0 s1 s0 s0 s0 s0 s0  
| 161 => bits8 s1 s0 s1 s0 s0 s0 s0 s1  
| 162 => bits8 s1 s0 s1 s0 s0 s0 s1 s0  
| 163 => bits8 s1 s0 s1 s0 s0 s0 s1 s1  
| 164 => bits8 s1 s0 s1 s0 s0 s1 s0 s0  
| 165 => bits8 s1 s0 s1 s0 s0 s1 s0 s1  
| 166 => bits8 s1 s0 s1 s0 s0 s1 s1 s0  
| 167 => bits8 s1 s0 s1 s0 s0 s1 s1 s1  
| 168 => bits8 s1 s0 s1 s0 s1 s0 s0 s0  
| 169 => bits8 s1 s0 s1 s0 s1 s0 s0 s1  
| 170 => bits8 s1 s0 s1 s0 s1 s0 s1 s0  
| 171 => bits8 s1 s0 s1 s0 s1 s0 s1 s1  
| 172 => bits8 s1 s0 s1 s0 s1 s1 s0 s0  
| 173 => bits8 s1 s0 s1 s0 s1 s1 s0 s1  
| 174 => bits8 s1 s0 s1 s0 s1 s1 s1 s0  
| 175 => bits8 s1 s0 s1 s0 s1 s1 s1 s1  
| 176 => bits8 s1 s0 s1 s1 s0 s0 s0 s0  
| 177 => bits8 s1 s0 s1 s1 s0 s0 s0 s1  
| 178 => bits8 s1 s0 s1 s1 s0 s0 s1 s0  
| 179 => bits8 s1 s0 s1 s1 s0 s0 s1 s1  
| 180 => bits8 s1 s0 s1 s1 s0 s1 s0 s0  
| 181 => bits8 s1 s0 s1 s1 s0 s1 s0 s1  
| 182 => bits8 s1 s0 s1 s1 s0 s1 s1 s0  
| 183 => bits8 s1 s0 s1 s1 s0 s1 s1 s1  
| 184 => bits8 s1 s0 s1 s1 s1 s0 s0 s0  
| 185 => bits8 s1 s0 s1 s1 s1 s0 s0 s1  
| 186 => bits8 s1 s0 s1 s1 s1 s0 s1 s0  
| 187 => bits8 s1 s0 s1 s1 s1 s0 s1 s1  
| 188 => bits8 s1 s0 s1 s1 s1 s1 s0 s0  
| 189 => bits8 s1 s0 s1 s1 s1 s1 s0 s1  
| 190 => bits8 s1 s0 s1 s1 s1 s1 s1 s0  
| 191 => bits8 s1 s0 s1 s1 s1 s1 s1 s1  
| 192 => bits8 s1 s1 s0 s0 s0 s0 s0 s0  
| 193 => bits8 s1 s1 s0 s0 s0 s0 s0 s1  
| 194 => bits8 s1 s1 s0 s0 s0 s0 s1 s0  
| 195 => bits8 s1 s1 s0 s0 s0 s0 s1 s1  
| 196 => bits8 s1 s1 s0 s0 s0 s1 s0 s0  
| 197 => bits8 s1 s1 s0 s0 s0 s1 s0 s1  
| 198 => bits8 s1 s1 s0 s0 s0 s1 s1 s0  
| 199 => bits8 s1 s1 s0 s0 s0 s1 s1 s1  
| 200 => bits8 s1 s1 s0 s0 s1 s0 s0 s0  
| 201 => bits8 s1 s1 s0 s0 s1 s0 s0 s1  
| 202 => bits8 s1 s1 s0 s0 s1 s0 s1 s0  
| 203 => bits8 s1 s1 s0 s0 s1 s0 s1 s1  
| 204 => bits8 s1 s1 s0 s0 s1 s1 s0 s0  
| 205 => bits8 s1 s1 s0 s0 s1 s1 s0 s1  
| 206 => bits8 s1 s1 s0 s0 s1 s1 s1 s0  
| 207 => bits8 s1 s1 s0 s0 s1 s1 s1 s1  
| 208 => bits8 s1 s1 s0 s1 s0 s0 s0 s0  
| 209 => bits8 s1 s1 s0 s1 s0 s0 s0 s1  
| 210 => bits8 s1 s1 s0 s1 s0 s0 s1 s0  
| 211 => bits8 s1 s1 s0 s1 s0 s0 s1 s1  
| 212 => bits8 s1 s1 s0 s1 s0 s1 s0 s0  
| 213 => bits8 s1 s1 s0 s1 s0 s1 s0 s1  
| 214 => bits8 s1 s1 s0 s1 s0 s1 s1 s0  
| 215 => bits8 s1 s1 s0 s1 s0 s1 s1 s1  
| 216 => bits8 s1 s1 s0 s1 s1 s0 s0 s0  
| 217 => bits8 s1 s1 s0 s1 s1 s0 s0 s1  
| 218 => bits8 s1 s1 s0 s1 s1 s0 s1 s0  
| 219 => bits8 s1 s1 s0 s1 s1 s0 s1 s1  
| 220 => bits8 s1 s1 s0 s1 s1 s1 s0 s0  
| 221 => bits8 s1 s1 s0 s1 s1 s1 s0 s1  
| 222 => bits8 s1 s1 s0 s1 s1 s1 s1 s0  
| 223 => bits8 s1 s1 s0 s1 s1 s1 s1 s1  
| 224 => bits8 s1 s1 s1 s0 s0 s0 s0 s0  
| 225 => bits8 s1 s1 s1 s0 s0 s0 s0 s1  
| 226 => bits8 s1 s1 s1 s0 s0 s0 s1 s0  
| 227 => bits8 s1 s1 s1 s0 s0 s0 s1 s1  
| 228 => bits8 s1 s1 s1 s0 s0 s1 s0 s0  
| 229 => bits8 s1 s1 s1 s0 s0 s1 s0 s1  
| 230 => bits8 s1 s1 s1 s0 s0 s1 s1 s0  
| 231 => bits8 s1 s1 s1 s0 s0 s1 s1 s1  
| 232 => bits8 s1 s1 s1 s0 s1 s0 s0 s0  
| 233 => bits8 s1 s1 s1 s0 s1 s0 s0 s1  
| 234 => bits8 s1 s1 s1 s0 s1 s0 s1 s0  
| 235 => bits8 s1 s1 s1 s0 s1 s0 s1 s1  
| 236 => bits8 s1 s1 s1 s0 s1 s1 s0 s0  
| 237 => bits8 s1 s1 s1 s0 s1 s1 s0 s1  
| 238 => bits8 s1 s1 s1 s0 s1 s1 s1 s0  
| 239 => bits8 s1 s1 s1 s0 s1 s1 s1 s1  
| 240 => bits8 s1 s1 s1 s1 s0 s0 s0 s0  
| 241 => bits8 s1 s1 s1 s1 s0 s0 s0 s1  
| 242 => bits8 s1 s1 s1 s1 s0 s0 s1 s0  
| 243 => bits8 s1 s1 s1 s1 s0 s0 s1 s1  
| 244 => bits8 s1 s1 s1 s1 s0 s1 s0 s0  
| 245 => bits8 s1 s1 s1 s1 s0 s1 s0 s1  
| 246 => bits8 s1 s1 s1 s1 s0 s1 s1 s0  
| 247 => bits8 s1 s1 s1 s1 s0 s1 s1 s1  
| 248 => bits8 s1 s1 s1 s1 s1 s0 s0 s0  
| 249 => bits8 s1 s1 s1 s1 s1 s0 s0 s1  
| 250 => bits8 s1 s1 s1 s1 s1 s0 s1 s0  
| 251 => bits8 s1 s1 s1 s1 s1 s0 s1 s1  
| 252 => bits8 s1 s1 s1 s1 s1 s1 s0 s0  
| 253 => bits8 s1 s1 s1 s1 s1 s1 s0 s1  
| 254 => bits8 s1 s1 s1 s1 s1 s1 s1 s0  
| 255 => bits8 s1 s1 s1 s1 s1 s1 s1 s1  
| _ => bits8 s1 s1 s1 s1 s1 s1 s1 s1  
  end.

Definition add_bytes (a b: byte) : byte :=
  match a, b with
  | bits8 s0 s0 s0 s0 s0 s0 s0 s0, b' => b'
  | a', bits8 s0 s0 s0 s0 s0 s0 s0 s0 => a'
  | _,_ => nat_to_byte((byte_to_nat a) + (byte_to_nat b)) 
end.
Inductive bit16 : Type :=
| bits16 (b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 : bit)
.

Definition xor_16bit (b a: bit16) : bit16 :=
  match b with
  | bits16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 =>
      match a with
      | bits16 a15 a14 a13 a12 a11 a10 a9 a8 a7 a6 a5 a4 a3 a2 a1 a0 =>
          bits16 (xor_bits b15 a15) (xor_bits b14 a14) (xor_bits b13 a13) (xor_bits b12 a12) (xor_bits b11 a11) (xor_bits b10 a10) (xor_bits b9 a9) (xor_bits b8 a8) (xor_bits b7 a7) (xor_bits b6 a6) (xor_bits b5 a5) (xor_bits b4 a4) (xor_bits b3 a3) (xor_bits b2 a2) (xor_bits b1 a1) (xor_bits b0 a0)
      end
  end.

Notation "A x16+or B" := (xor_16bit A B) (at level 75, right associativity).


(* Notation "A + B" := (add_bytes A B) .
 *)
Fixpoint mul_byte (a : byte)  (b : nat) : byte := 
  match a with
  | bits8 s0 s0 s0 s0 s0 s0 s0 s0 => bits8 s0 s0 s0 s0 s0 s0 s0 s0
  | _ =>  match b with 
          | 0 => bits8 s0 s0 s0 s0 s0 s0 s0 s0
          | 1 => a
          | S n => add_bytes a (mul_byte a n)
          end
  end.
 
(* Notation "A * B" := (mul_byte A B) .
 *)

Definition mul_nat_bit (a : nat) (b : bit) : nat :=
  match b with
  | s0 => 0
  | s1 => a
  end.

Definition GF_mul_byte1 (a: byte) (b:bit) (shift:nat) : bit16 :=
  match a with
      | bits8 a7 a6 a5 a4 a3 a2 a1 a0 =>
        match b with 
          | s0 => bits16 s0 s0 s0 s0 s0 s0 s0 s0 s0 s0 s0 s0 s0 s0 s0 s0
          | s1 => 
          match shift with
            | 0 => bits16 s0 s0 s0 s0 s0 s0 s0 s0 a7 a6 a5 a4 a3 a2 a1 a0
            | 1 => bits16 s0 s0 s0 s0 s0 s0 s0 a7 a6 a5 a4 a3 a2 a1 a0 s0
            | 2 => bits16 s0 s0 s0 s0 s0 s0 a7 a6 a5 a4 a3 a2 a1 a0 s0 s0
            | 3 => bits16 s0 s0 s0 s0 s0 a7 a6 a5 a4 a3 a2 a1 a0 s0 s0 s0
            | 4 => bits16 s0 s0 s0 s0 a7 a6 a5 a4 a3 a2 a1 a0 s0 s0 s0 s0
            | 5 => bits16 s0 s0 s0 a7 a6 a5 a4 a3 a2 a1 a0 s0 s0 s0 s0 s0
            | 6 => bits16 s0 s0 a7 a6 a5 a4 a3 a2 a1 a0 s0 s0 s0 s0 s0 s0
            | 7 => bits16 s0 a7 a6 a5 a4 a3 a2 a1 a0 s0 s0 s0 s0 s0 s0 s0
            | _ => bits16 s0 s0 s0 s0 s0 s0 s0 s0 a7 a6 a5 a4 a3 a2 a1 a0
            end
        end
  end.

(* Definition GF_mul_byte (a b: byte) : bytes :=
  match b with 
  | bits8 b7 b6 b5 b4 b3 b2 b1 b0 => 
    ((GF_mul_byte1 a b7 7) x16+or (GF_mul_byte1 a b6 6) x16+or (GF_mul_byte1 a b5 5) x16+or (GF_mul_byte1 a b4 4) x16+or (GF_mul_byte1 a b3 3) x16+or(GF_mul_byte1 a b2 2) x16+or (GF_mul_byte1 a b1 1) x16+or (GF_mul_byte1 a b0 0))
    end.
 *)
(* https://en.wikipedia.org/wiki/Rijndael_MixColumns#Galois_Multiplication_lookup_tables*)

Definition GF_mul_table (a : byte) (b : nat) : byte :=
match b with 

| 1 => a
| 2 => match a with 
| bits8 s0 s0 s0 s0 s0 s0 s0 s0  => bits8 s0 s0 s0 s0 s0 s0 s0 s0  | bits8 s0 s0 s0 s0 s0 s0 s0 s1  => bits8 s0 s0 s0 s0 s0 s0 s1 s0  | bits8 s0 s0 s0 s0 s0 s0 s1 s0  => bits8 s0 s0 s0 s0 s0 s1 s0 s0  | bits8 s0 s0 s0 s0 s0 s0 s1 s1  => bits8 s0 s0 s0 s0 s0 s1 s1 s0  | bits8 s0 s0 s0 s0 s0 s1 s0 s0  => bits8 s0 s0 s0 s0 s1 s0 s0 s0  | bits8 s0 s0 s0 s0 s0 s1 s0 s1  => bits8 s0 s0 s0 s0 s1 s0 s1 s0  | bits8 s0 s0 s0 s0 s0 s1 s1 s0  => bits8 s0 s0 s0 s0 s1 s1 s0 s0  | bits8 s0 s0 s0 s0 s0 s1 s1 s1  => bits8 s0 s0 s0 s0 s1 s1 s1 s0  | bits8 s0 s0 s0 s0 s1 s0 s0 s0  => bits8 s0 s0 s0 s1 s0 s0 s0 s0  | bits8 s0 s0 s0 s0 s1 s0 s0 s1  => bits8 s0 s0 s0 s1 s0 s0 s1 s0  | bits8 s0 s0 s0 s0 s1 s0 s1 s0  => bits8 s0 s0 s0 s1 s0 s1 s0 s0  | bits8 s0 s0 s0 s0 s1 s0 s1 s1  => bits8 s0 s0 s0 s1 s0 s1 s1 s0  | bits8 s0 s0 s0 s0 s1 s1 s0 s0  => bits8 s0 s0 s0 s1 s1 s0 s0 s0  | bits8 s0 s0 s0 s0 s1 s1 s0 s1  => bits8 s0 s0 s0 s1 s1 s0 s1 s0  | bits8 s0 s0 s0 s0 s1 s1 s1 s0  => bits8 s0 s0 s0 s1 s1 s1 s0 s0  | bits8 s0 s0 s0 s0 s1 s1 s1 s1  => bits8 s0 s0 s0 s1 s1 s1 s1 s0  | bits8 s0 s0 s0 s1 s0 s0 s0 s0  => bits8 s0 s0 s1 s0 s0 s0 s0 s0  | bits8 s0 s0 s0 s1 s0 s0 s0 s1  => bits8 s0 s0 s1 s0 s0 s0 s1 s0  | bits8 s0 s0 s0 s1 s0 s0 s1 s0  => bits8 s0 s0 s1 s0 s0 s1 s0 s0  | bits8 s0 s0 s0 s1 s0 s0 s1 s1  => bits8 s0 s0 s1 s0 s0 s1 s1 s0  | bits8 s0 s0 s0 s1 s0 s1 s0 s0  => bits8 s0 s0 s1 s0 s1 s0 s0 s0  | bits8 s0 s0 s0 s1 s0 s1 s0 s1  => bits8 s0 s0 s1 s0 s1 s0 s1 s0  | bits8 s0 s0 s0 s1 s0 s1 s1 s0  => bits8 s0 s0 s1 s0 s1 s1 s0 s0  | bits8 s0 s0 s0 s1 s0 s1 s1 s1  => bits8 s0 s0 s1 s0 s1 s1 s1 s0  | bits8 s0 s0 s0 s1 s1 s0 s0 s0  => bits8 s0 s0 s1 s1 s0 s0 s0 s0  | bits8 s0 s0 s0 s1 s1 s0 s0 s1  => bits8 s0 s0 s1 s1 s0 s0 s1 s0  | bits8 s0 s0 s0 s1 s1 s0 s1 s0  => bits8 s0 s0 s1 s1 s0 s1 s0 s0  | bits8 s0 s0 s0 s1 s1 s0 s1 s1  => bits8 s0 s0 s1 s1 s0 s1 s1 s0  | bits8 s0 s0 s0 s1 s1 s1 s0 s0  => bits8 s0 s0 s1 s1 s1 s0 s0 s0  | bits8 s0 s0 s0 s1 s1 s1 s0 s1  => bits8 s0 s0 s1 s1 s1 s0 s1 s0  | bits8 s0 s0 s0 s1 s1 s1 s1 s0  => bits8 s0 s0 s1 s1 s1 s1 s0 s0  | bits8 s0 s0 s0 s1 s1 s1 s1 s1  => bits8 s0 s0 s1 s1 s1 s1 s1 s0  | bits8 s0 s0 s1 s0 s0 s0 s0 s0  => bits8 s0 s1 s0 s0 s0 s0 s0 s0  | bits8 s0 s0 s1 s0 s0 s0 s0 s1  => bits8 s0 s1 s0 s0 s0 s0 s1 s0  | bits8 s0 s0 s1 s0 s0 s0 s1 s0  => bits8 s0 s1 s0 s0 s0 s1 s0 s0  | bits8 s0 s0 s1 s0 s0 s0 s1 s1  => bits8 s0 s1 s0 s0 s0 s1 s1 s0  | bits8 s0 s0 s1 s0 s0 s1 s0 s0  => bits8 s0 s1 s0 s0 s1 s0 s0 s0  | bits8 s0 s0 s1 s0 s0 s1 s0 s1  => bits8 s0 s1 s0 s0 s1 s0 s1 s0  | bits8 s0 s0 s1 s0 s0 s1 s1 s0  => bits8 s0 s1 s0 s0 s1 s1 s0 s0  | bits8 s0 s0 s1 s0 s0 s1 s1 s1  => bits8 s0 s1 s0 s0 s1 s1 s1 s0  | bits8 s0 s0 s1 s0 s1 s0 s0 s0  => bits8 s0 s1 s0 s1 s0 s0 s0 s0  | bits8 s0 s0 s1 s0 s1 s0 s0 s1  => bits8 s0 s1 s0 s1 s0 s0 s1 s0  | bits8 s0 s0 s1 s0 s1 s0 s1 s0  => bits8 s0 s1 s0 s1 s0 s1 s0 s0  | bits8 s0 s0 s1 s0 s1 s0 s1 s1  => bits8 s0 s1 s0 s1 s0 s1 s1 s0  | bits8 s0 s0 s1 s0 s1 s1 s0 s0  => bits8 s0 s1 s0 s1 s1 s0 s0 s0  | bits8 s0 s0 s1 s0 s1 s1 s0 s1  => bits8 s0 s1 s0 s1 s1 s0 s1 s0  | bits8 s0 s0 s1 s0 s1 s1 s1 s0  => bits8 s0 s1 s0 s1 s1 s1 s0 s0  | bits8 s0 s0 s1 s0 s1 s1 s1 s1  => bits8 s0 s1 s0 s1 s1 s1 s1 s0  | bits8 s0 s0 s1 s1 s0 s0 s0 s0  => bits8 s0 s1 s1 s0 s0 s0 s0 s0  | bits8 s0 s0 s1 s1 s0 s0 s0 s1  => bits8 s0 s1 s1 s0 s0 s0 s1 s0  | bits8 s0 s0 s1 s1 s0 s0 s1 s0  => bits8 s0 s1 s1 s0 s0 s1 s0 s0  | bits8 s0 s0 s1 s1 s0 s0 s1 s1  => bits8 s0 s1 s1 s0 s0 s1 s1 s0  | bits8 s0 s0 s1 s1 s0 s1 s0 s0  => bits8 s0 s1 s1 s0 s1 s0 s0 s0  | bits8 s0 s0 s1 s1 s0 s1 s0 s1  => bits8 s0 s1 s1 s0 s1 s0 s1 s0  | bits8 s0 s0 s1 s1 s0 s1 s1 s0  => bits8 s0 s1 s1 s0 s1 s1 s0 s0  | bits8 s0 s0 s1 s1 s0 s1 s1 s1  => bits8 s0 s1 s1 s0 s1 s1 s1 s0  | bits8 s0 s0 s1 s1 s1 s0 s0 s0  => bits8 s0 s1 s1 s1 s0 s0 s0 s0  | bits8 s0 s0 s1 s1 s1 s0 s0 s1  => bits8 s0 s1 s1 s1 s0 s0 s1 s0  | bits8 s0 s0 s1 s1 s1 s0 s1 s0  => bits8 s0 s1 s1 s1 s0 s1 s0 s0  | bits8 s0 s0 s1 s1 s1 s0 s1 s1  => bits8 s0 s1 s1 s1 s0 s1 s1 s0  | bits8 s0 s0 s1 s1 s1 s1 s0 s0  => bits8 s0 s1 s1 s1 s1 s0 s0 s0  | bits8 s0 s0 s1 s1 s1 s1 s0 s1  => bits8 s0 s1 s1 s1 s1 s0 s1 s0  | bits8 s0 s0 s1 s1 s1 s1 s1 s0  => bits8 s0 s1 s1 s1 s1 s1 s0 s0  | bits8 s0 s0 s1 s1 s1 s1 s1 s1  => bits8 s0 s1 s1 s1 s1 s1 s1 s0  | bits8 s0 s1 s0 s0 s0 s0 s0 s0  => bits8 s1 s0 s0 s0 s0 s0 s0 s0  | bits8 s0 s1 s0 s0 s0 s0 s0 s1  => bits8 s1 s0 s0 s0 s0 s0 s1 s0  | bits8 s0 s1 s0 s0 s0 s0 s1 s0  => bits8 s1 s0 s0 s0 s0 s1 s0 s0  | bits8 s0 s1 s0 s0 s0 s0 s1 s1  => bits8 s1 s0 s0 s0 s0 s1 s1 s0  | bits8 s0 s1 s0 s0 s0 s1 s0 s0  => bits8 s1 s0 s0 s0 s1 s0 s0 s0  | bits8 s0 s1 s0 s0 s0 s1 s0 s1  => bits8 s1 s0 s0 s0 s1 s0 s1 s0  | bits8 s0 s1 s0 s0 s0 s1 s1 s0  => bits8 s1 s0 s0 s0 s1 s1 s0 s0  | bits8 s0 s1 s0 s0 s0 s1 s1 s1  => bits8 s1 s0 s0 s0 s1 s1 s1 s0  | bits8 s0 s1 s0 s0 s1 s0 s0 s0  => bits8 s1 s0 s0 s1 s0 s0 s0 s0  | bits8 s0 s1 s0 s0 s1 s0 s0 s1  => bits8 s1 s0 s0 s1 s0 s0 s1 s0  | bits8 s0 s1 s0 s0 s1 s0 s1 s0  => bits8 s1 s0 s0 s1 s0 s1 s0 s0  | bits8 s0 s1 s0 s0 s1 s0 s1 s1  => bits8 s1 s0 s0 s1 s0 s1 s1 s0  | bits8 s0 s1 s0 s0 s1 s1 s0 s0  => bits8 s1 s0 s0 s1 s1 s0 s0 s0  | bits8 s0 s1 s0 s0 s1 s1 s0 s1  => bits8 s1 s0 s0 s1 s1 s0 s1 s0  | bits8 s0 s1 s0 s0 s1 s1 s1 s0  => bits8 s1 s0 s0 s1 s1 s1 s0 s0  | bits8 s0 s1 s0 s0 s1 s1 s1 s1  => bits8 s1 s0 s0 s1 s1 s1 s1 s0  | bits8 s0 s1 s0 s1 s0 s0 s0 s0  => bits8 s1 s0 s1 s0 s0 s0 s0 s0  | bits8 s0 s1 s0 s1 s0 s0 s0 s1  => bits8 s1 s0 s1 s0 s0 s0 s1 s0  | bits8 s0 s1 s0 s1 s0 s0 s1 s0  => bits8 s1 s0 s1 s0 s0 s1 s0 s0  | bits8 s0 s1 s0 s1 s0 s0 s1 s1  => bits8 s1 s0 s1 s0 s0 s1 s1 s0  | bits8 s0 s1 s0 s1 s0 s1 s0 s0  => bits8 s1 s0 s1 s0 s1 s0 s0 s0  | bits8 s0 s1 s0 s1 s0 s1 s0 s1  => bits8 s1 s0 s1 s0 s1 s0 s1 s0  | bits8 s0 s1 s0 s1 s0 s1 s1 s0  => bits8 s1 s0 s1 s0 s1 s1 s0 s0  | bits8 s0 s1 s0 s1 s0 s1 s1 s1  => bits8 s1 s0 s1 s0 s1 s1 s1 s0  | bits8 s0 s1 s0 s1 s1 s0 s0 s0  => bits8 s1 s0 s1 s1 s0 s0 s0 s0  | bits8 s0 s1 s0 s1 s1 s0 s0 s1  => bits8 s1 s0 s1 s1 s0 s0 s1 s0  | bits8 s0 s1 s0 s1 s1 s0 s1 s0  => bits8 s1 s0 s1 s1 s0 s1 s0 s0  | bits8 s0 s1 s0 s1 s1 s0 s1 s1  => bits8 s1 s0 s1 s1 s0 s1 s1 s0  | bits8 s0 s1 s0 s1 s1 s1 s0 s0  => bits8 s1 s0 s1 s1 s1 s0 s0 s0  | bits8 s0 s1 s0 s1 s1 s1 s0 s1  => bits8 s1 s0 s1 s1 s1 s0 s1 s0  | bits8 s0 s1 s0 s1 s1 s1 s1 s0  => bits8 s1 s0 s1 s1 s1 s1 s0 s0  | bits8 s0 s1 s0 s1 s1 s1 s1 s1  => bits8 s1 s0 s1 s1 s1 s1 s1 s0  | bits8 s0 s1 s1 s0 s0 s0 s0 s0  => bits8 s1 s1 s0 s0 s0 s0 s0 s0  | bits8 s0 s1 s1 s0 s0 s0 s0 s1  => bits8 s1 s1 s0 s0 s0 s0 s1 s0  | bits8 s0 s1 s1 s0 s0 s0 s1 s0  => bits8 s1 s1 s0 s0 s0 s1 s0 s0  | bits8 s0 s1 s1 s0 s0 s0 s1 s1  => bits8 s1 s1 s0 s0 s0 s1 s1 s0  | bits8 s0 s1 s1 s0 s0 s1 s0 s0  => bits8 s1 s1 s0 s0 s1 s0 s0 s0  | bits8 s0 s1 s1 s0 s0 s1 s0 s1  => bits8 s1 s1 s0 s0 s1 s0 s1 s0  | bits8 s0 s1 s1 s0 s0 s1 s1 s0  => bits8 s1 s1 s0 s0 s1 s1 s0 s0  | bits8 s0 s1 s1 s0 s0 s1 s1 s1  => bits8 s1 s1 s0 s0 s1 s1 s1 s0  | bits8 s0 s1 s1 s0 s1 s0 s0 s0  => bits8 s1 s1 s0 s1 s0 s0 s0 s0  | bits8 s0 s1 s1 s0 s1 s0 s0 s1  => bits8 s1 s1 s0 s1 s0 s0 s1 s0  | bits8 s0 s1 s1 s0 s1 s0 s1 s0  => bits8 s1 s1 s0 s1 s0 s1 s0 s0  | bits8 s0 s1 s1 s0 s1 s0 s1 s1  => bits8 s1 s1 s0 s1 s0 s1 s1 s0  | bits8 s0 s1 s1 s0 s1 s1 s0 s0  => bits8 s1 s1 s0 s1 s1 s0 s0 s0  | bits8 s0 s1 s1 s0 s1 s1 s0 s1  => bits8 s1 s1 s0 s1 s1 s0 s1 s0  | bits8 s0 s1 s1 s0 s1 s1 s1 s0  => bits8 s1 s1 s0 s1 s1 s1 s0 s0  | bits8 s0 s1 s1 s0 s1 s1 s1 s1  => bits8 s1 s1 s0 s1 s1 s1 s1 s0  | bits8 s0 s1 s1 s1 s0 s0 s0 s0  => bits8 s1 s1 s1 s0 s0 s0 s0 s0  | bits8 s0 s1 s1 s1 s0 s0 s0 s1  => bits8 s1 s1 s1 s0 s0 s0 s1 s0  | bits8 s0 s1 s1 s1 s0 s0 s1 s0  => bits8 s1 s1 s1 s0 s0 s1 s0 s0  | bits8 s0 s1 s1 s1 s0 s0 s1 s1  => bits8 s1 s1 s1 s0 s0 s1 s1 s0  | bits8 s0 s1 s1 s1 s0 s1 s0 s0  => bits8 s1 s1 s1 s0 s1 s0 s0 s0  | bits8 s0 s1 s1 s1 s0 s1 s0 s1  => bits8 s1 s1 s1 s0 s1 s0 s1 s0  | bits8 s0 s1 s1 s1 s0 s1 s1 s0  => bits8 s1 s1 s1 s0 s1 s1 s0 s0  | bits8 s0 s1 s1 s1 s0 s1 s1 s1  => bits8 s1 s1 s1 s0 s1 s1 s1 s0  | bits8 s0 s1 s1 s1 s1 s0 s0 s0  => bits8 s1 s1 s1 s1 s0 s0 s0 s0  | bits8 s0 s1 s1 s1 s1 s0 s0 s1  => bits8 s1 s1 s1 s1 s0 s0 s1 s0  | bits8 s0 s1 s1 s1 s1 s0 s1 s0  => bits8 s1 s1 s1 s1 s0 s1 s0 s0  | bits8 s0 s1 s1 s1 s1 s0 s1 s1  => bits8 s1 s1 s1 s1 s0 s1 s1 s0  | bits8 s0 s1 s1 s1 s1 s1 s0 s0  => bits8 s1 s1 s1 s1 s1 s0 s0 s0  | bits8 s0 s1 s1 s1 s1 s1 s0 s1  => bits8 s1 s1 s1 s1 s1 s0 s1 s0  | bits8 s0 s1 s1 s1 s1 s1 s1 s0  => bits8 s1 s1 s1 s1 s1 s1 s0 s0  | bits8 s0 s1 s1 s1 s1 s1 s1 s1  => bits8 s1 s1 s1 s1 s1 s1 s1 s0  | bits8 s1 s0 s0 s0 s0 s0 s0 s0  => bits8 s0 s0 s0 s1 s1 s0 s1 s1  | bits8 s1 s0 s0 s0 s0 s0 s0 s1  => bits8 s0 s0 s0 s1 s1 s0 s0 s1  | bits8 s1 s0 s0 s0 s0 s0 s1 s0  => bits8 s0 s0 s0 s1 s1 s1 s1 s1  | bits8 s1 s0 s0 s0 s0 s0 s1 s1  => bits8 s0 s0 s0 s1 s1 s1 s0 s1  | bits8 s1 s0 s0 s0 s0 s1 s0 s0  => bits8 s0 s0 s0 s1 s0 s0 s1 s1  | bits8 s1 s0 s0 s0 s0 s1 s0 s1  => bits8 s0 s0 s0 s1 s0 s0 s0 s1  | bits8 s1 s0 s0 s0 s0 s1 s1 s0  => bits8 s0 s0 s0 s1 s0 s1 s1 s1  | bits8 s1 s0 s0 s0 s0 s1 s1 s1  => bits8 s0 s0 s0 s1 s0 s1 s0 s1  | bits8 s1 s0 s0 s0 s1 s0 s0 s0  => bits8 s0 s0 s0 s0 s1 s0 s1 s1  | bits8 s1 s0 s0 s0 s1 s0 s0 s1  => bits8 s0 s0 s0 s0 s1 s0 s0 s1  | bits8 s1 s0 s0 s0 s1 s0 s1 s0  => bits8 s0 s0 s0 s0 s1 s1 s1 s1  | bits8 s1 s0 s0 s0 s1 s0 s1 s1  => bits8 s0 s0 s0 s0 s1 s1 s0 s1  | bits8 s1 s0 s0 s0 s1 s1 s0 s0  => bits8 s0 s0 s0 s0 s0 s0 s1 s1  | bits8 s1 s0 s0 s0 s1 s1 s0 s1  => bits8 s0 s0 s0 s0 s0 s0 s0 s1  | bits8 s1 s0 s0 s0 s1 s1 s1 s0  => bits8 s0 s0 s0 s0 s0 s1 s1 s1  | bits8 s1 s0 s0 s0 s1 s1 s1 s1  => bits8 s0 s0 s0 s0 s0 s1 s0 s1  | bits8 s1 s0 s0 s1 s0 s0 s0 s0  => bits8 s0 s0 s1 s1 s1 s0 s1 s1  | bits8 s1 s0 s0 s1 s0 s0 s0 s1  => bits8 s0 s0 s1 s1 s1 s0 s0 s1  | bits8 s1 s0 s0 s1 s0 s0 s1 s0  => bits8 s0 s0 s1 s1 s1 s1 s1 s1  | bits8 s1 s0 s0 s1 s0 s0 s1 s1  => bits8 s0 s0 s1 s1 s1 s1 s0 s1  | bits8 s1 s0 s0 s1 s0 s1 s0 s0  => bits8 s0 s0 s1 s1 s0 s0 s1 s1  | bits8 s1 s0 s0 s1 s0 s1 s0 s1  => bits8 s0 s0 s1 s1 s0 s0 s0 s1  | bits8 s1 s0 s0 s1 s0 s1 s1 s0  => bits8 s0 s0 s1 s1 s0 s1 s1 s1  | bits8 s1 s0 s0 s1 s0 s1 s1 s1  => bits8 s0 s0 s1 s1 s0 s1 s0 s1  | bits8 s1 s0 s0 s1 s1 s0 s0 s0  => bits8 s0 s0 s1 s0 s1 s0 s1 s1  | bits8 s1 s0 s0 s1 s1 s0 s0 s1  => bits8 s0 s0 s1 s0 s1 s0 s0 s1  | bits8 s1 s0 s0 s1 s1 s0 s1 s0  => bits8 s0 s0 s1 s0 s1 s1 s1 s1  | bits8 s1 s0 s0 s1 s1 s0 s1 s1  => bits8 s0 s0 s1 s0 s1 s1 s0 s1  | bits8 s1 s0 s0 s1 s1 s1 s0 s0  => bits8 s0 s0 s1 s0 s0 s0 s1 s1  | bits8 s1 s0 s0 s1 s1 s1 s0 s1  => bits8 s0 s0 s1 s0 s0 s0 s0 s1  | bits8 s1 s0 s0 s1 s1 s1 s1 s0  => bits8 s0 s0 s1 s0 s0 s1 s1 s1  | bits8 s1 s0 s0 s1 s1 s1 s1 s1  => bits8 s0 s0 s1 s0 s0 s1 s0 s1  | bits8 s1 s0 s1 s0 s0 s0 s0 s0  => bits8 s0 s1 s0 s1 s1 s0 s1 s1  | bits8 s1 s0 s1 s0 s0 s0 s0 s1  => bits8 s0 s1 s0 s1 s1 s0 s0 s1  | bits8 s1 s0 s1 s0 s0 s0 s1 s0  => bits8 s0 s1 s0 s1 s1 s1 s1 s1  | bits8 s1 s0 s1 s0 s0 s0 s1 s1  => bits8 s0 s1 s0 s1 s1 s1 s0 s1  | bits8 s1 s0 s1 s0 s0 s1 s0 s0  => bits8 s0 s1 s0 s1 s0 s0 s1 s1  | bits8 s1 s0 s1 s0 s0 s1 s0 s1  => bits8 s0 s1 s0 s1 s0 s0 s0 s1  | bits8 s1 s0 s1 s0 s0 s1 s1 s0  => bits8 s0 s1 s0 s1 s0 s1 s1 s1  | bits8 s1 s0 s1 s0 s0 s1 s1 s1  => bits8 s0 s1 s0 s1 s0 s1 s0 s1  | bits8 s1 s0 s1 s0 s1 s0 s0 s0  => bits8 s0 s1 s0 s0 s1 s0 s1 s1  | bits8 s1 s0 s1 s0 s1 s0 s0 s1  => bits8 s0 s1 s0 s0 s1 s0 s0 s1  | bits8 s1 s0 s1 s0 s1 s0 s1 s0  => bits8 s0 s1 s0 s0 s1 s1 s1 s1  | bits8 s1 s0 s1 s0 s1 s0 s1 s1  => bits8 s0 s1 s0 s0 s1 s1 s0 s1  | bits8 s1 s0 s1 s0 s1 s1 s0 s0  => bits8 s0 s1 s0 s0 s0 s0 s1 s1  | bits8 s1 s0 s1 s0 s1 s1 s0 s1  => bits8 s0 s1 s0 s0 s0 s0 s0 s1  | bits8 s1 s0 s1 s0 s1 s1 s1 s0  => bits8 s0 s1 s0 s0 s0 s1 s1 s1  | bits8 s1 s0 s1 s0 s1 s1 s1 s1  => bits8 s0 s1 s0 s0 s0 s1 s0 s1  | bits8 s1 s0 s1 s1 s0 s0 s0 s0  => bits8 s0 s1 s1 s1 s1 s0 s1 s1  | bits8 s1 s0 s1 s1 s0 s0 s0 s1  => bits8 s0 s1 s1 s1 s1 s0 s0 s1  | bits8 s1 s0 s1 s1 s0 s0 s1 s0  => bits8 s0 s1 s1 s1 s1 s1 s1 s1  | bits8 s1 s0 s1 s1 s0 s0 s1 s1  => bits8 s0 s1 s1 s1 s1 s1 s0 s1  | bits8 s1 s0 s1 s1 s0 s1 s0 s0  => bits8 s0 s1 s1 s1 s0 s0 s1 s1  | bits8 s1 s0 s1 s1 s0 s1 s0 s1  => bits8 s0 s1 s1 s1 s0 s0 s0 s1  | bits8 s1 s0 s1 s1 s0 s1 s1 s0  => bits8 s0 s1 s1 s1 s0 s1 s1 s1  | bits8 s1 s0 s1 s1 s0 s1 s1 s1  => bits8 s0 s1 s1 s1 s0 s1 s0 s1  | bits8 s1 s0 s1 s1 s1 s0 s0 s0  => bits8 s0 s1 s1 s0 s1 s0 s1 s1  | bits8 s1 s0 s1 s1 s1 s0 s0 s1  => bits8 s0 s1 s1 s0 s1 s0 s0 s1  | bits8 s1 s0 s1 s1 s1 s0 s1 s0  => bits8 s0 s1 s1 s0 s1 s1 s1 s1  | bits8 s1 s0 s1 s1 s1 s0 s1 s1  => bits8 s0 s1 s1 s0 s1 s1 s0 s1  | bits8 s1 s0 s1 s1 s1 s1 s0 s0  => bits8 s0 s1 s1 s0 s0 s0 s1 s1  | bits8 s1 s0 s1 s1 s1 s1 s0 s1  => bits8 s0 s1 s1 s0 s0 s0 s0 s1  | bits8 s1 s0 s1 s1 s1 s1 s1 s0  => bits8 s0 s1 s1 s0 s0 s1 s1 s1  | bits8 s1 s0 s1 s1 s1 s1 s1 s1  => bits8 s0 s1 s1 s0 s0 s1 s0 s1  | bits8 s1 s1 s0 s0 s0 s0 s0 s0  => bits8 s1 s0 s0 s1 s1 s0 s1 s1  | bits8 s1 s1 s0 s0 s0 s0 s0 s1  => bits8 s1 s0 s0 s1 s1 s0 s0 s1  | bits8 s1 s1 s0 s0 s0 s0 s1 s0  => bits8 s1 s0 s0 s1 s1 s1 s1 s1  | bits8 s1 s1 s0 s0 s0 s0 s1 s1  => bits8 s1 s0 s0 s1 s1 s1 s0 s1  | bits8 s1 s1 s0 s0 s0 s1 s0 s0  => bits8 s1 s0 s0 s1 s0 s0 s1 s1  | bits8 s1 s1 s0 s0 s0 s1 s0 s1  => bits8 s1 s0 s0 s1 s0 s0 s0 s1  | bits8 s1 s1 s0 s0 s0 s1 s1 s0  => bits8 s1 s0 s0 s1 s0 s1 s1 s1  | bits8 s1 s1 s0 s0 s0 s1 s1 s1  => bits8 s1 s0 s0 s1 s0 s1 s0 s1  | bits8 s1 s1 s0 s0 s1 s0 s0 s0  => bits8 s1 s0 s0 s0 s1 s0 s1 s1  | bits8 s1 s1 s0 s0 s1 s0 s0 s1  => bits8 s1 s0 s0 s0 s1 s0 s0 s1  | bits8 s1 s1 s0 s0 s1 s0 s1 s0  => bits8 s1 s0 s0 s0 s1 s1 s1 s1  | bits8 s1 s1 s0 s0 s1 s0 s1 s1  => bits8 s1 s0 s0 s0 s1 s1 s0 s1  | bits8 s1 s1 s0 s0 s1 s1 s0 s0  => bits8 s1 s0 s0 s0 s0 s0 s1 s1  | bits8 s1 s1 s0 s0 s1 s1 s0 s1  => bits8 s1 s0 s0 s0 s0 s0 s0 s1  | bits8 s1 s1 s0 s0 s1 s1 s1 s0  => bits8 s1 s0 s0 s0 s0 s1 s1 s1  | bits8 s1 s1 s0 s0 s1 s1 s1 s1  => bits8 s1 s0 s0 s0 s0 s1 s0 s1  | bits8 s1 s1 s0 s1 s0 s0 s0 s0  => bits8 s1 s0 s1 s1 s1 s0 s1 s1  | bits8 s1 s1 s0 s1 s0 s0 s0 s1  => bits8 s1 s0 s1 s1 s1 s0 s0 s1  | bits8 s1 s1 s0 s1 s0 s0 s1 s0  => bits8 s1 s0 s1 s1 s1 s1 s1 s1  | bits8 s1 s1 s0 s1 s0 s0 s1 s1  => bits8 s1 s0 s1 s1 s1 s1 s0 s1  | bits8 s1 s1 s0 s1 s0 s1 s0 s0  => bits8 s1 s0 s1 s1 s0 s0 s1 s1  | bits8 s1 s1 s0 s1 s0 s1 s0 s1  => bits8 s1 s0 s1 s1 s0 s0 s0 s1  | bits8 s1 s1 s0 s1 s0 s1 s1 s0  => bits8 s1 s0 s1 s1 s0 s1 s1 s1  | bits8 s1 s1 s0 s1 s0 s1 s1 s1  => bits8 s1 s0 s1 s1 s0 s1 s0 s1  | bits8 s1 s1 s0 s1 s1 s0 s0 s0  => bits8 s1 s0 s1 s0 s1 s0 s1 s1  | bits8 s1 s1 s0 s1 s1 s0 s0 s1  => bits8 s1 s0 s1 s0 s1 s0 s0 s1  | bits8 s1 s1 s0 s1 s1 s0 s1 s0  => bits8 s1 s0 s1 s0 s1 s1 s1 s1  | bits8 s1 s1 s0 s1 s1 s0 s1 s1  => bits8 s1 s0 s1 s0 s1 s1 s0 s1  | bits8 s1 s1 s0 s1 s1 s1 s0 s0  => bits8 s1 s0 s1 s0 s0 s0 s1 s1  | bits8 s1 s1 s0 s1 s1 s1 s0 s1  => bits8 s1 s0 s1 s0 s0 s0 s0 s1  | bits8 s1 s1 s0 s1 s1 s1 s1 s0  => bits8 s1 s0 s1 s0 s0 s1 s1 s1  | bits8 s1 s1 s0 s1 s1 s1 s1 s1  => bits8 s1 s0 s1 s0 s0 s1 s0 s1  | bits8 s1 s1 s1 s0 s0 s0 s0 s0  => bits8 s1 s1 s0 s1 s1 s0 s1 s1  | bits8 s1 s1 s1 s0 s0 s0 s0 s1  => bits8 s1 s1 s0 s1 s1 s0 s0 s1  | bits8 s1 s1 s1 s0 s0 s0 s1 s0  => bits8 s1 s1 s0 s1 s1 s1 s1 s1  | bits8 s1 s1 s1 s0 s0 s0 s1 s1  => bits8 s1 s1 s0 s1 s1 s1 s0 s1  | bits8 s1 s1 s1 s0 s0 s1 s0 s0  => bits8 s1 s1 s0 s1 s0 s0 s1 s1  | bits8 s1 s1 s1 s0 s0 s1 s0 s1  => bits8 s1 s1 s0 s1 s0 s0 s0 s1  | bits8 s1 s1 s1 s0 s0 s1 s1 s0  => bits8 s1 s1 s0 s1 s0 s1 s1 s1  | bits8 s1 s1 s1 s0 s0 s1 s1 s1  => bits8 s1 s1 s0 s1 s0 s1 s0 s1  | bits8 s1 s1 s1 s0 s1 s0 s0 s0  => bits8 s1 s1 s0 s0 s1 s0 s1 s1  | bits8 s1 s1 s1 s0 s1 s0 s0 s1  => bits8 s1 s1 s0 s0 s1 s0 s0 s1  | bits8 s1 s1 s1 s0 s1 s0 s1 s0  => bits8 s1 s1 s0 s0 s1 s1 s1 s1  | bits8 s1 s1 s1 s0 s1 s0 s1 s1  => bits8 s1 s1 s0 s0 s1 s1 s0 s1  | bits8 s1 s1 s1 s0 s1 s1 s0 s0  => bits8 s1 s1 s0 s0 s0 s0 s1 s1  | bits8 s1 s1 s1 s0 s1 s1 s0 s1  => bits8 s1 s1 s0 s0 s0 s0 s0 s1  | bits8 s1 s1 s1 s0 s1 s1 s1 s0  => bits8 s1 s1 s0 s0 s0 s1 s1 s1  | bits8 s1 s1 s1 s0 s1 s1 s1 s1  => bits8 s1 s1 s0 s0 s0 s1 s0 s1  | bits8 s1 s1 s1 s1 s0 s0 s0 s0  => bits8 s1 s1 s1 s1 s1 s0 s1 s1  | bits8 s1 s1 s1 s1 s0 s0 s0 s1  => bits8 s1 s1 s1 s1 s1 s0 s0 s1  | bits8 s1 s1 s1 s1 s0 s0 s1 s0  => bits8 s1 s1 s1 s1 s1 s1 s1 s1  | bits8 s1 s1 s1 s1 s0 s0 s1 s1  => bits8 s1 s1 s1 s1 s1 s1 s0 s1  | bits8 s1 s1 s1 s1 s0 s1 s0 s0  => bits8 s1 s1 s1 s1 s0 s0 s1 s1  | bits8 s1 s1 s1 s1 s0 s1 s0 s1  => bits8 s1 s1 s1 s1 s0 s0 s0 s1  | bits8 s1 s1 s1 s1 s0 s1 s1 s0  => bits8 s1 s1 s1 s1 s0 s1 s1 s1  | bits8 s1 s1 s1 s1 s0 s1 s1 s1  => bits8 s1 s1 s1 s1 s0 s1 s0 s1  | bits8 s1 s1 s1 s1 s1 s0 s0 s0  => bits8 s1 s1 s1 s0 s1 s0 s1 s1  | bits8 s1 s1 s1 s1 s1 s0 s0 s1  => bits8 s1 s1 s1 s0 s1 s0 s0 s1  | bits8 s1 s1 s1 s1 s1 s0 s1 s0  => bits8 s1 s1 s1 s0 s1 s1 s1 s1  | bits8 s1 s1 s1 s1 s1 s0 s1 s1  => bits8 s1 s1 s1 s0 s1 s1 s0 s1  | bits8 s1 s1 s1 s1 s1 s1 s0 s0  => bits8 s1 s1 s1 s0 s0 s0 s1 s1  | bits8 s1 s1 s1 s1 s1 s1 s0 s1  => bits8 s1 s1 s1 s0 s0 s0 s0 s1  | bits8 s1 s1 s1 s1 s1 s1 s1 s0  => bits8 s1 s1 s1 s0 s0 s1 s1 s1  | bits8 s1 s1 s1 s1 s1 s1 s1 s1  => bits8 s1 s1 s1 s0 s0 s1 s0 s1  end
| 3 => match a with 
| bits8 s0 s0 s0 s0 s0 s0 s0 s0  => bits8 s0 s0 s0 s0 s0 s0 s0 s0  | bits8 s0 s0 s0 s0 s0 s0 s0 s1  => bits8 s0 s0 s0 s0 s0 s0 s1 s1  | bits8 s0 s0 s0 s0 s0 s0 s1 s0  => bits8 s0 s0 s0 s0 s0 s1 s1 s0  | bits8 s0 s0 s0 s0 s0 s0 s1 s1  => bits8 s0 s0 s0 s0 s0 s1 s0 s1  | bits8 s0 s0 s0 s0 s0 s1 s0 s0  => bits8 s0 s0 s0 s0 s1 s1 s0 s0  | bits8 s0 s0 s0 s0 s0 s1 s0 s1  => bits8 s0 s0 s0 s0 s1 s1 s1 s1  | bits8 s0 s0 s0 s0 s0 s1 s1 s0  => bits8 s0 s0 s0 s0 s1 s0 s1 s0  | bits8 s0 s0 s0 s0 s0 s1 s1 s1  => bits8 s0 s0 s0 s0 s1 s0 s0 s1  | bits8 s0 s0 s0 s0 s1 s0 s0 s0  => bits8 s0 s0 s0 s1 s1 s0 s0 s0  | bits8 s0 s0 s0 s0 s1 s0 s0 s1  => bits8 s0 s0 s0 s1 s1 s0 s1 s1  | bits8 s0 s0 s0 s0 s1 s0 s1 s0  => bits8 s0 s0 s0 s1 s1 s1 s1 s0  | bits8 s0 s0 s0 s0 s1 s0 s1 s1  => bits8 s0 s0 s0 s1 s1 s1 s0 s1  | bits8 s0 s0 s0 s0 s1 s1 s0 s0  => bits8 s0 s0 s0 s1 s0 s1 s0 s0  | bits8 s0 s0 s0 s0 s1 s1 s0 s1  => bits8 s0 s0 s0 s1 s0 s1 s1 s1  | bits8 s0 s0 s0 s0 s1 s1 s1 s0  => bits8 s0 s0 s0 s1 s0 s0 s1 s0  | bits8 s0 s0 s0 s0 s1 s1 s1 s1  => bits8 s0 s0 s0 s1 s0 s0 s0 s1  | bits8 s0 s0 s0 s1 s0 s0 s0 s0  => bits8 s0 s0 s1 s1 s0 s0 s0 s0  | bits8 s0 s0 s0 s1 s0 s0 s0 s1  => bits8 s0 s0 s1 s1 s0 s0 s1 s1  | bits8 s0 s0 s0 s1 s0 s0 s1 s0  => bits8 s0 s0 s1 s1 s0 s1 s1 s0  | bits8 s0 s0 s0 s1 s0 s0 s1 s1  => bits8 s0 s0 s1 s1 s0 s1 s0 s1  | bits8 s0 s0 s0 s1 s0 s1 s0 s0  => bits8 s0 s0 s1 s1 s1 s1 s0 s0  | bits8 s0 s0 s0 s1 s0 s1 s0 s1  => bits8 s0 s0 s1 s1 s1 s1 s1 s1  | bits8 s0 s0 s0 s1 s0 s1 s1 s0  => bits8 s0 s0 s1 s1 s1 s0 s1 s0  | bits8 s0 s0 s0 s1 s0 s1 s1 s1  => bits8 s0 s0 s1 s1 s1 s0 s0 s1  | bits8 s0 s0 s0 s1 s1 s0 s0 s0  => bits8 s0 s0 s1 s0 s1 s0 s0 s0  | bits8 s0 s0 s0 s1 s1 s0 s0 s1  => bits8 s0 s0 s1 s0 s1 s0 s1 s1  | bits8 s0 s0 s0 s1 s1 s0 s1 s0  => bits8 s0 s0 s1 s0 s1 s1 s1 s0  | bits8 s0 s0 s0 s1 s1 s0 s1 s1  => bits8 s0 s0 s1 s0 s1 s1 s0 s1  | bits8 s0 s0 s0 s1 s1 s1 s0 s0  => bits8 s0 s0 s1 s0 s0 s1 s0 s0  | bits8 s0 s0 s0 s1 s1 s1 s0 s1  => bits8 s0 s0 s1 s0 s0 s1 s1 s1  | bits8 s0 s0 s0 s1 s1 s1 s1 s0  => bits8 s0 s0 s1 s0 s0 s0 s1 s0  | bits8 s0 s0 s0 s1 s1 s1 s1 s1  => bits8 s0 s0 s1 s0 s0 s0 s0 s1  | bits8 s0 s0 s1 s0 s0 s0 s0 s0  => bits8 s0 s1 s1 s0 s0 s0 s0 s0  | bits8 s0 s0 s1 s0 s0 s0 s0 s1  => bits8 s0 s1 s1 s0 s0 s0 s1 s1  | bits8 s0 s0 s1 s0 s0 s0 s1 s0  => bits8 s0 s1 s1 s0 s0 s1 s1 s0  | bits8 s0 s0 s1 s0 s0 s0 s1 s1  => bits8 s0 s1 s1 s0 s0 s1 s0 s1  | bits8 s0 s0 s1 s0 s0 s1 s0 s0  => bits8 s0 s1 s1 s0 s1 s1 s0 s0  | bits8 s0 s0 s1 s0 s0 s1 s0 s1  => bits8 s0 s1 s1 s0 s1 s1 s1 s1  | bits8 s0 s0 s1 s0 s0 s1 s1 s0  => bits8 s0 s1 s1 s0 s1 s0 s1 s0  | bits8 s0 s0 s1 s0 s0 s1 s1 s1  => bits8 s0 s1 s1 s0 s1 s0 s0 s1  | bits8 s0 s0 s1 s0 s1 s0 s0 s0  => bits8 s0 s1 s1 s1 s1 s0 s0 s0  | bits8 s0 s0 s1 s0 s1 s0 s0 s1  => bits8 s0 s1 s1 s1 s1 s0 s1 s1  | bits8 s0 s0 s1 s0 s1 s0 s1 s0  => bits8 s0 s1 s1 s1 s1 s1 s1 s0  | bits8 s0 s0 s1 s0 s1 s0 s1 s1  => bits8 s0 s1 s1 s1 s1 s1 s0 s1  | bits8 s0 s0 s1 s0 s1 s1 s0 s0  => bits8 s0 s1 s1 s1 s0 s1 s0 s0  | bits8 s0 s0 s1 s0 s1 s1 s0 s1  => bits8 s0 s1 s1 s1 s0 s1 s1 s1  | bits8 s0 s0 s1 s0 s1 s1 s1 s0  => bits8 s0 s1 s1 s1 s0 s0 s1 s0  | bits8 s0 s0 s1 s0 s1 s1 s1 s1  => bits8 s0 s1 s1 s1 s0 s0 s0 s1  | bits8 s0 s0 s1 s1 s0 s0 s0 s0  => bits8 s0 s1 s0 s1 s0 s0 s0 s0  | bits8 s0 s0 s1 s1 s0 s0 s0 s1  => bits8 s0 s1 s0 s1 s0 s0 s1 s1  | bits8 s0 s0 s1 s1 s0 s0 s1 s0  => bits8 s0 s1 s0 s1 s0 s1 s1 s0  | bits8 s0 s0 s1 s1 s0 s0 s1 s1  => bits8 s0 s1 s0 s1 s0 s1 s0 s1  | bits8 s0 s0 s1 s1 s0 s1 s0 s0  => bits8 s0 s1 s0 s1 s1 s1 s0 s0  | bits8 s0 s0 s1 s1 s0 s1 s0 s1  => bits8 s0 s1 s0 s1 s1 s1 s1 s1  | bits8 s0 s0 s1 s1 s0 s1 s1 s0  => bits8 s0 s1 s0 s1 s1 s0 s1 s0  | bits8 s0 s0 s1 s1 s0 s1 s1 s1  => bits8 s0 s1 s0 s1 s1 s0 s0 s1  | bits8 s0 s0 s1 s1 s1 s0 s0 s0  => bits8 s0 s1 s0 s0 s1 s0 s0 s0  | bits8 s0 s0 s1 s1 s1 s0 s0 s1  => bits8 s0 s1 s0 s0 s1 s0 s1 s1  | bits8 s0 s0 s1 s1 s1 s0 s1 s0  => bits8 s0 s1 s0 s0 s1 s1 s1 s0  | bits8 s0 s0 s1 s1 s1 s0 s1 s1  => bits8 s0 s1 s0 s0 s1 s1 s0 s1  | bits8 s0 s0 s1 s1 s1 s1 s0 s0  => bits8 s0 s1 s0 s0 s0 s1 s0 s0  | bits8 s0 s0 s1 s1 s1 s1 s0 s1  => bits8 s0 s1 s0 s0 s0 s1 s1 s1  | bits8 s0 s0 s1 s1 s1 s1 s1 s0  => bits8 s0 s1 s0 s0 s0 s0 s1 s0  | bits8 s0 s0 s1 s1 s1 s1 s1 s1  => bits8 s0 s1 s0 s0 s0 s0 s0 s1  | bits8 s0 s1 s0 s0 s0 s0 s0 s0  => bits8 s1 s1 s0 s0 s0 s0 s0 s0  | bits8 s0 s1 s0 s0 s0 s0 s0 s1  => bits8 s1 s1 s0 s0 s0 s0 s1 s1  | bits8 s0 s1 s0 s0 s0 s0 s1 s0  => bits8 s1 s1 s0 s0 s0 s1 s1 s0  | bits8 s0 s1 s0 s0 s0 s0 s1 s1  => bits8 s1 s1 s0 s0 s0 s1 s0 s1  | bits8 s0 s1 s0 s0 s0 s1 s0 s0  => bits8 s1 s1 s0 s0 s1 s1 s0 s0  | bits8 s0 s1 s0 s0 s0 s1 s0 s1  => bits8 s1 s1 s0 s0 s1 s1 s1 s1  | bits8 s0 s1 s0 s0 s0 s1 s1 s0  => bits8 s1 s1 s0 s0 s1 s0 s1 s0  | bits8 s0 s1 s0 s0 s0 s1 s1 s1  => bits8 s1 s1 s0 s0 s1 s0 s0 s1  | bits8 s0 s1 s0 s0 s1 s0 s0 s0  => bits8 s1 s1 s0 s1 s1 s0 s0 s0  | bits8 s0 s1 s0 s0 s1 s0 s0 s1  => bits8 s1 s1 s0 s1 s1 s0 s1 s1  | bits8 s0 s1 s0 s0 s1 s0 s1 s0  => bits8 s1 s1 s0 s1 s1 s1 s1 s0  | bits8 s0 s1 s0 s0 s1 s0 s1 s1  => bits8 s1 s1 s0 s1 s1 s1 s0 s1  | bits8 s0 s1 s0 s0 s1 s1 s0 s0  => bits8 s1 s1 s0 s1 s0 s1 s0 s0  | bits8 s0 s1 s0 s0 s1 s1 s0 s1  => bits8 s1 s1 s0 s1 s0 s1 s1 s1  | bits8 s0 s1 s0 s0 s1 s1 s1 s0  => bits8 s1 s1 s0 s1 s0 s0 s1 s0  | bits8 s0 s1 s0 s0 s1 s1 s1 s1  => bits8 s1 s1 s0 s1 s0 s0 s0 s1  | bits8 s0 s1 s0 s1 s0 s0 s0 s0  => bits8 s1 s1 s1 s1 s0 s0 s0 s0  | bits8 s0 s1 s0 s1 s0 s0 s0 s1  => bits8 s1 s1 s1 s1 s0 s0 s1 s1  | bits8 s0 s1 s0 s1 s0 s0 s1 s0  => bits8 s1 s1 s1 s1 s0 s1 s1 s0  | bits8 s0 s1 s0 s1 s0 s0 s1 s1  => bits8 s1 s1 s1 s1 s0 s1 s0 s1  | bits8 s0 s1 s0 s1 s0 s1 s0 s0  => bits8 s1 s1 s1 s1 s1 s1 s0 s0  | bits8 s0 s1 s0 s1 s0 s1 s0 s1  => bits8 s1 s1 s1 s1 s1 s1 s1 s1  | bits8 s0 s1 s0 s1 s0 s1 s1 s0  => bits8 s1 s1 s1 s1 s1 s0 s1 s0  | bits8 s0 s1 s0 s1 s0 s1 s1 s1  => bits8 s1 s1 s1 s1 s1 s0 s0 s1  | bits8 s0 s1 s0 s1 s1 s0 s0 s0  => bits8 s1 s1 s1 s0 s1 s0 s0 s0  | bits8 s0 s1 s0 s1 s1 s0 s0 s1  => bits8 s1 s1 s1 s0 s1 s0 s1 s1  | bits8 s0 s1 s0 s1 s1 s0 s1 s0  => bits8 s1 s1 s1 s0 s1 s1 s1 s0  | bits8 s0 s1 s0 s1 s1 s0 s1 s1  => bits8 s1 s1 s1 s0 s1 s1 s0 s1  | bits8 s0 s1 s0 s1 s1 s1 s0 s0  => bits8 s1 s1 s1 s0 s0 s1 s0 s0  | bits8 s0 s1 s0 s1 s1 s1 s0 s1  => bits8 s1 s1 s1 s0 s0 s1 s1 s1  | bits8 s0 s1 s0 s1 s1 s1 s1 s0  => bits8 s1 s1 s1 s0 s0 s0 s1 s0  | bits8 s0 s1 s0 s1 s1 s1 s1 s1  => bits8 s1 s1 s1 s0 s0 s0 s0 s1  | bits8 s0 s1 s1 s0 s0 s0 s0 s0  => bits8 s1 s0 s1 s0 s0 s0 s0 s0  | bits8 s0 s1 s1 s0 s0 s0 s0 s1  => bits8 s1 s0 s1 s0 s0 s0 s1 s1  | bits8 s0 s1 s1 s0 s0 s0 s1 s0  => bits8 s1 s0 s1 s0 s0 s1 s1 s0  | bits8 s0 s1 s1 s0 s0 s0 s1 s1  => bits8 s1 s0 s1 s0 s0 s1 s0 s1  | bits8 s0 s1 s1 s0 s0 s1 s0 s0  => bits8 s1 s0 s1 s0 s1 s1 s0 s0  | bits8 s0 s1 s1 s0 s0 s1 s0 s1  => bits8 s1 s0 s1 s0 s1 s1 s1 s1  | bits8 s0 s1 s1 s0 s0 s1 s1 s0  => bits8 s1 s0 s1 s0 s1 s0 s1 s0  | bits8 s0 s1 s1 s0 s0 s1 s1 s1  => bits8 s1 s0 s1 s0 s1 s0 s0 s1  | bits8 s0 s1 s1 s0 s1 s0 s0 s0  => bits8 s1 s0 s1 s1 s1 s0 s0 s0  | bits8 s0 s1 s1 s0 s1 s0 s0 s1  => bits8 s1 s0 s1 s1 s1 s0 s1 s1  | bits8 s0 s1 s1 s0 s1 s0 s1 s0  => bits8 s1 s0 s1 s1 s1 s1 s1 s0  | bits8 s0 s1 s1 s0 s1 s0 s1 s1  => bits8 s1 s0 s1 s1 s1 s1 s0 s1  | bits8 s0 s1 s1 s0 s1 s1 s0 s0  => bits8 s1 s0 s1 s1 s0 s1 s0 s0  | bits8 s0 s1 s1 s0 s1 s1 s0 s1  => bits8 s1 s0 s1 s1 s0 s1 s1 s1  | bits8 s0 s1 s1 s0 s1 s1 s1 s0  => bits8 s1 s0 s1 s1 s0 s0 s1 s0  | bits8 s0 s1 s1 s0 s1 s1 s1 s1  => bits8 s1 s0 s1 s1 s0 s0 s0 s1  | bits8 s0 s1 s1 s1 s0 s0 s0 s0  => bits8 s1 s0 s0 s1 s0 s0 s0 s0  | bits8 s0 s1 s1 s1 s0 s0 s0 s1  => bits8 s1 s0 s0 s1 s0 s0 s1 s1  | bits8 s0 s1 s1 s1 s0 s0 s1 s0  => bits8 s1 s0 s0 s1 s0 s1 s1 s0  | bits8 s0 s1 s1 s1 s0 s0 s1 s1  => bits8 s1 s0 s0 s1 s0 s1 s0 s1  | bits8 s0 s1 s1 s1 s0 s1 s0 s0  => bits8 s1 s0 s0 s1 s1 s1 s0 s0  | bits8 s0 s1 s1 s1 s0 s1 s0 s1  => bits8 s1 s0 s0 s1 s1 s1 s1 s1  | bits8 s0 s1 s1 s1 s0 s1 s1 s0  => bits8 s1 s0 s0 s1 s1 s0 s1 s0  | bits8 s0 s1 s1 s1 s0 s1 s1 s1  => bits8 s1 s0 s0 s1 s1 s0 s0 s1  | bits8 s0 s1 s1 s1 s1 s0 s0 s0  => bits8 s1 s0 s0 s0 s1 s0 s0 s0  | bits8 s0 s1 s1 s1 s1 s0 s0 s1  => bits8 s1 s0 s0 s0 s1 s0 s1 s1  | bits8 s0 s1 s1 s1 s1 s0 s1 s0  => bits8 s1 s0 s0 s0 s1 s1 s1 s0  | bits8 s0 s1 s1 s1 s1 s0 s1 s1  => bits8 s1 s0 s0 s0 s1 s1 s0 s1  | bits8 s0 s1 s1 s1 s1 s1 s0 s0  => bits8 s1 s0 s0 s0 s0 s1 s0 s0  | bits8 s0 s1 s1 s1 s1 s1 s0 s1  => bits8 s1 s0 s0 s0 s0 s1 s1 s1  | bits8 s0 s1 s1 s1 s1 s1 s1 s0  => bits8 s1 s0 s0 s0 s0 s0 s1 s0  | bits8 s0 s1 s1 s1 s1 s1 s1 s1  => bits8 s1 s0 s0 s0 s0 s0 s0 s1  | bits8 s1 s0 s0 s0 s0 s0 s0 s0  => bits8 s1 s0 s0 s1 s1 s0 s1 s1  | bits8 s1 s0 s0 s0 s0 s0 s0 s1  => bits8 s1 s0 s0 s1 s1 s0 s0 s0  | bits8 s1 s0 s0 s0 s0 s0 s1 s0  => bits8 s1 s0 s0 s1 s1 s1 s0 s1  | bits8 s1 s0 s0 s0 s0 s0 s1 s1  => bits8 s1 s0 s0 s1 s1 s1 s1 s0  | bits8 s1 s0 s0 s0 s0 s1 s0 s0  => bits8 s1 s0 s0 s1 s0 s1 s1 s1  | bits8 s1 s0 s0 s0 s0 s1 s0 s1  => bits8 s1 s0 s0 s1 s0 s1 s0 s0  | bits8 s1 s0 s0 s0 s0 s1 s1 s0  => bits8 s1 s0 s0 s1 s0 s0 s0 s1  | bits8 s1 s0 s0 s0 s0 s1 s1 s1  => bits8 s1 s0 s0 s1 s0 s0 s1 s0  | bits8 s1 s0 s0 s0 s1 s0 s0 s0  => bits8 s1 s0 s0 s0 s0 s0 s1 s1  | bits8 s1 s0 s0 s0 s1 s0 s0 s1  => bits8 s1 s0 s0 s0 s0 s0 s0 s0  | bits8 s1 s0 s0 s0 s1 s0 s1 s0  => bits8 s1 s0 s0 s0 s0 s1 s0 s1  | bits8 s1 s0 s0 s0 s1 s0 s1 s1  => bits8 s1 s0 s0 s0 s0 s1 s1 s0  | bits8 s1 s0 s0 s0 s1 s1 s0 s0  => bits8 s1 s0 s0 s0 s1 s1 s1 s1  | bits8 s1 s0 s0 s0 s1 s1 s0 s1  => bits8 s1 s0 s0 s0 s1 s1 s0 s0  | bits8 s1 s0 s0 s0 s1 s1 s1 s0  => bits8 s1 s0 s0 s0 s1 s0 s0 s1  | bits8 s1 s0 s0 s0 s1 s1 s1 s1  => bits8 s1 s0 s0 s0 s1 s0 s1 s0  | bits8 s1 s0 s0 s1 s0 s0 s0 s0  => bits8 s1 s0 s1 s0 s1 s0 s1 s1  | bits8 s1 s0 s0 s1 s0 s0 s0 s1  => bits8 s1 s0 s1 s0 s1 s0 s0 s0  | bits8 s1 s0 s0 s1 s0 s0 s1 s0  => bits8 s1 s0 s1 s0 s1 s1 s0 s1  | bits8 s1 s0 s0 s1 s0 s0 s1 s1  => bits8 s1 s0 s1 s0 s1 s1 s1 s0  | bits8 s1 s0 s0 s1 s0 s1 s0 s0  => bits8 s1 s0 s1 s0 s0 s1 s1 s1  | bits8 s1 s0 s0 s1 s0 s1 s0 s1  => bits8 s1 s0 s1 s0 s0 s1 s0 s0  | bits8 s1 s0 s0 s1 s0 s1 s1 s0  => bits8 s1 s0 s1 s0 s0 s0 s0 s1  | bits8 s1 s0 s0 s1 s0 s1 s1 s1  => bits8 s1 s0 s1 s0 s0 s0 s1 s0  | bits8 s1 s0 s0 s1 s1 s0 s0 s0  => bits8 s1 s0 s1 s1 s0 s0 s1 s1  | bits8 s1 s0 s0 s1 s1 s0 s0 s1  => bits8 s1 s0 s1 s1 s0 s0 s0 s0  | bits8 s1 s0 s0 s1 s1 s0 s1 s0  => bits8 s1 s0 s1 s1 s0 s1 s0 s1  | bits8 s1 s0 s0 s1 s1 s0 s1 s1  => bits8 s1 s0 s1 s1 s0 s1 s1 s0  | bits8 s1 s0 s0 s1 s1 s1 s0 s0  => bits8 s1 s0 s1 s1 s1 s1 s1 s1  | bits8 s1 s0 s0 s1 s1 s1 s0 s1  => bits8 s1 s0 s1 s1 s1 s1 s0 s0  | bits8 s1 s0 s0 s1 s1 s1 s1 s0  => bits8 s1 s0 s1 s1 s1 s0 s0 s1  | bits8 s1 s0 s0 s1 s1 s1 s1 s1  => bits8 s1 s0 s1 s1 s1 s0 s1 s0  | bits8 s1 s0 s1 s0 s0 s0 s0 s0  => bits8 s1 s1 s1 s1 s1 s0 s1 s1  | bits8 s1 s0 s1 s0 s0 s0 s0 s1  => bits8 s1 s1 s1 s1 s1 s0 s0 s0  | bits8 s1 s0 s1 s0 s0 s0 s1 s0  => bits8 s1 s1 s1 s1 s1 s1 s0 s1  | bits8 s1 s0 s1 s0 s0 s0 s1 s1  => bits8 s1 s1 s1 s1 s1 s1 s1 s0  | bits8 s1 s0 s1 s0 s0 s1 s0 s0  => bits8 s1 s1 s1 s1 s0 s1 s1 s1  | bits8 s1 s0 s1 s0 s0 s1 s0 s1  => bits8 s1 s1 s1 s1 s0 s1 s0 s0  | bits8 s1 s0 s1 s0 s0 s1 s1 s0  => bits8 s1 s1 s1 s1 s0 s0 s0 s1  | bits8 s1 s0 s1 s0 s0 s1 s1 s1  => bits8 s1 s1 s1 s1 s0 s0 s1 s0  | bits8 s1 s0 s1 s0 s1 s0 s0 s0  => bits8 s1 s1 s1 s0 s0 s0 s1 s1  | bits8 s1 s0 s1 s0 s1 s0 s0 s1  => bits8 s1 s1 s1 s0 s0 s0 s0 s0  | bits8 s1 s0 s1 s0 s1 s0 s1 s0  => bits8 s1 s1 s1 s0 s0 s1 s0 s1  | bits8 s1 s0 s1 s0 s1 s0 s1 s1  => bits8 s1 s1 s1 s0 s0 s1 s1 s0  | bits8 s1 s0 s1 s0 s1 s1 s0 s0  => bits8 s1 s1 s1 s0 s1 s1 s1 s1  | bits8 s1 s0 s1 s0 s1 s1 s0 s1  => bits8 s1 s1 s1 s0 s1 s1 s0 s0  | bits8 s1 s0 s1 s0 s1 s1 s1 s0  => bits8 s1 s1 s1 s0 s1 s0 s0 s1  | bits8 s1 s0 s1 s0 s1 s1 s1 s1  => bits8 s1 s1 s1 s0 s1 s0 s1 s0  | bits8 s1 s0 s1 s1 s0 s0 s0 s0  => bits8 s1 s1 s0 s0 s1 s0 s1 s1  | bits8 s1 s0 s1 s1 s0 s0 s0 s1  => bits8 s1 s1 s0 s0 s1 s0 s0 s0  | bits8 s1 s0 s1 s1 s0 s0 s1 s0  => bits8 s1 s1 s0 s0 s1 s1 s0 s1  | bits8 s1 s0 s1 s1 s0 s0 s1 s1  => bits8 s1 s1 s0 s0 s1 s1 s1 s0  | bits8 s1 s0 s1 s1 s0 s1 s0 s0  => bits8 s1 s1 s0 s0 s0 s1 s1 s1  | bits8 s1 s0 s1 s1 s0 s1 s0 s1  => bits8 s1 s1 s0 s0 s0 s1 s0 s0  | bits8 s1 s0 s1 s1 s0 s1 s1 s0  => bits8 s1 s1 s0 s0 s0 s0 s0 s1  | bits8 s1 s0 s1 s1 s0 s1 s1 s1  => bits8 s1 s1 s0 s0 s0 s0 s1 s0  | bits8 s1 s0 s1 s1 s1 s0 s0 s0  => bits8 s1 s1 s0 s1 s0 s0 s1 s1  | bits8 s1 s0 s1 s1 s1 s0 s0 s1  => bits8 s1 s1 s0 s1 s0 s0 s0 s0  | bits8 s1 s0 s1 s1 s1 s0 s1 s0  => bits8 s1 s1 s0 s1 s0 s1 s0 s1  | bits8 s1 s0 s1 s1 s1 s0 s1 s1  => bits8 s1 s1 s0 s1 s0 s1 s1 s0  | bits8 s1 s0 s1 s1 s1 s1 s0 s0  => bits8 s1 s1 s0 s1 s1 s1 s1 s1  | bits8 s1 s0 s1 s1 s1 s1 s0 s1  => bits8 s1 s1 s0 s1 s1 s1 s0 s0  | bits8 s1 s0 s1 s1 s1 s1 s1 s0  => bits8 s1 s1 s0 s1 s1 s0 s0 s1  | bits8 s1 s0 s1 s1 s1 s1 s1 s1  => bits8 s1 s1 s0 s1 s1 s0 s1 s0  | bits8 s1 s1 s0 s0 s0 s0 s0 s0  => bits8 s0 s1 s0 s1 s1 s0 s1 s1  | bits8 s1 s1 s0 s0 s0 s0 s0 s1  => bits8 s0 s1 s0 s1 s1 s0 s0 s0  | bits8 s1 s1 s0 s0 s0 s0 s1 s0  => bits8 s0 s1 s0 s1 s1 s1 s0 s1  | bits8 s1 s1 s0 s0 s0 s0 s1 s1  => bits8 s0 s1 s0 s1 s1 s1 s1 s0  | bits8 s1 s1 s0 s0 s0 s1 s0 s0  => bits8 s0 s1 s0 s1 s0 s1 s1 s1  | bits8 s1 s1 s0 s0 s0 s1 s0 s1  => bits8 s0 s1 s0 s1 s0 s1 s0 s0  | bits8 s1 s1 s0 s0 s0 s1 s1 s0  => bits8 s0 s1 s0 s1 s0 s0 s0 s1  | bits8 s1 s1 s0 s0 s0 s1 s1 s1  => bits8 s0 s1 s0 s1 s0 s0 s1 s0  | bits8 s1 s1 s0 s0 s1 s0 s0 s0  => bits8 s0 s1 s0 s0 s0 s0 s1 s1  | bits8 s1 s1 s0 s0 s1 s0 s0 s1  => bits8 s0 s1 s0 s0 s0 s0 s0 s0  | bits8 s1 s1 s0 s0 s1 s0 s1 s0  => bits8 s0 s1 s0 s0 s0 s1 s0 s1  | bits8 s1 s1 s0 s0 s1 s0 s1 s1  => bits8 s0 s1 s0 s0 s0 s1 s1 s0  | bits8 s1 s1 s0 s0 s1 s1 s0 s0  => bits8 s0 s1 s0 s0 s1 s1 s1 s1  | bits8 s1 s1 s0 s0 s1 s1 s0 s1  => bits8 s0 s1 s0 s0 s1 s1 s0 s0  | bits8 s1 s1 s0 s0 s1 s1 s1 s0  => bits8 s0 s1 s0 s0 s1 s0 s0 s1  | bits8 s1 s1 s0 s0 s1 s1 s1 s1  => bits8 s0 s1 s0 s0 s1 s0 s1 s0  | bits8 s1 s1 s0 s1 s0 s0 s0 s0  => bits8 s0 s1 s1 s0 s1 s0 s1 s1  | bits8 s1 s1 s0 s1 s0 s0 s0 s1  => bits8 s0 s1 s1 s0 s1 s0 s0 s0  | bits8 s1 s1 s0 s1 s0 s0 s1 s0  => bits8 s0 s1 s1 s0 s1 s1 s0 s1  | bits8 s1 s1 s0 s1 s0 s0 s1 s1  => bits8 s0 s1 s1 s0 s1 s1 s1 s0  | bits8 s1 s1 s0 s1 s0 s1 s0 s0  => bits8 s0 s1 s1 s0 s0 s1 s1 s1  | bits8 s1 s1 s0 s1 s0 s1 s0 s1  => bits8 s0 s1 s1 s0 s0 s1 s0 s0  | bits8 s1 s1 s0 s1 s0 s1 s1 s0  => bits8 s0 s1 s1 s0 s0 s0 s0 s1  | bits8 s1 s1 s0 s1 s0 s1 s1 s1  => bits8 s0 s1 s1 s0 s0 s0 s1 s0  | bits8 s1 s1 s0 s1 s1 s0 s0 s0  => bits8 s0 s1 s1 s1 s0 s0 s1 s1  | bits8 s1 s1 s0 s1 s1 s0 s0 s1  => bits8 s0 s1 s1 s1 s0 s0 s0 s0  | bits8 s1 s1 s0 s1 s1 s0 s1 s0  => bits8 s0 s1 s1 s1 s0 s1 s0 s1  | bits8 s1 s1 s0 s1 s1 s0 s1 s1  => bits8 s0 s1 s1 s1 s0 s1 s1 s0  | bits8 s1 s1 s0 s1 s1 s1 s0 s0  => bits8 s0 s1 s1 s1 s1 s1 s1 s1  | bits8 s1 s1 s0 s1 s1 s1 s0 s1  => bits8 s0 s1 s1 s1 s1 s1 s0 s0  | bits8 s1 s1 s0 s1 s1 s1 s1 s0  => bits8 s0 s1 s1 s1 s1 s0 s0 s1  | bits8 s1 s1 s0 s1 s1 s1 s1 s1  => bits8 s0 s1 s1 s1 s1 s0 s1 s0  | bits8 s1 s1 s1 s0 s0 s0 s0 s0  => bits8 s0 s0 s1 s1 s1 s0 s1 s1  | bits8 s1 s1 s1 s0 s0 s0 s0 s1  => bits8 s0 s0 s1 s1 s1 s0 s0 s0  | bits8 s1 s1 s1 s0 s0 s0 s1 s0  => bits8 s0 s0 s1 s1 s1 s1 s0 s1  | bits8 s1 s1 s1 s0 s0 s0 s1 s1  => bits8 s0 s0 s1 s1 s1 s1 s1 s0  | bits8 s1 s1 s1 s0 s0 s1 s0 s0  => bits8 s0 s0 s1 s1 s0 s1 s1 s1  | bits8 s1 s1 s1 s0 s0 s1 s0 s1  => bits8 s0 s0 s1 s1 s0 s1 s0 s0  | bits8 s1 s1 s1 s0 s0 s1 s1 s0  => bits8 s0 s0 s1 s1 s0 s0 s0 s1  | bits8 s1 s1 s1 s0 s0 s1 s1 s1  => bits8 s0 s0 s1 s1 s0 s0 s1 s0  | bits8 s1 s1 s1 s0 s1 s0 s0 s0  => bits8 s0 s0 s1 s0 s0 s0 s1 s1  | bits8 s1 s1 s1 s0 s1 s0 s0 s1  => bits8 s0 s0 s1 s0 s0 s0 s0 s0  | bits8 s1 s1 s1 s0 s1 s0 s1 s0  => bits8 s0 s0 s1 s0 s0 s1 s0 s1  | bits8 s1 s1 s1 s0 s1 s0 s1 s1  => bits8 s0 s0 s1 s0 s0 s1 s1 s0  | bits8 s1 s1 s1 s0 s1 s1 s0 s0  => bits8 s0 s0 s1 s0 s1 s1 s1 s1  | bits8 s1 s1 s1 s0 s1 s1 s0 s1  => bits8 s0 s0 s1 s0 s1 s1 s0 s0  | bits8 s1 s1 s1 s0 s1 s1 s1 s0  => bits8 s0 s0 s1 s0 s1 s0 s0 s1  | bits8 s1 s1 s1 s0 s1 s1 s1 s1  => bits8 s0 s0 s1 s0 s1 s0 s1 s0  | bits8 s1 s1 s1 s1 s0 s0 s0 s0  => bits8 s0 s0 s0 s0 s1 s0 s1 s1  | bits8 s1 s1 s1 s1 s0 s0 s0 s1  => bits8 s0 s0 s0 s0 s1 s0 s0 s0  | bits8 s1 s1 s1 s1 s0 s0 s1 s0  => bits8 s0 s0 s0 s0 s1 s1 s0 s1  | bits8 s1 s1 s1 s1 s0 s0 s1 s1  => bits8 s0 s0 s0 s0 s1 s1 s1 s0  | bits8 s1 s1 s1 s1 s0 s1 s0 s0  => bits8 s0 s0 s0 s0 s0 s1 s1 s1  | bits8 s1 s1 s1 s1 s0 s1 s0 s1  => bits8 s0 s0 s0 s0 s0 s1 s0 s0  | bits8 s1 s1 s1 s1 s0 s1 s1 s0  => bits8 s0 s0 s0 s0 s0 s0 s0 s1  | bits8 s1 s1 s1 s1 s0 s1 s1 s1  => bits8 s0 s0 s0 s0 s0 s0 s1 s0  | bits8 s1 s1 s1 s1 s1 s0 s0 s0  => bits8 s0 s0 s0 s1 s0 s0 s1 s1  | bits8 s1 s1 s1 s1 s1 s0 s0 s1  => bits8 s0 s0 s0 s1 s0 s0 s0 s0  | bits8 s1 s1 s1 s1 s1 s0 s1 s0  => bits8 s0 s0 s0 s1 s0 s1 s0 s1  | bits8 s1 s1 s1 s1 s1 s0 s1 s1  => bits8 s0 s0 s0 s1 s0 s1 s1 s0  | bits8 s1 s1 s1 s1 s1 s1 s0 s0  => bits8 s0 s0 s0 s1 s1 s1 s1 s1  | bits8 s1 s1 s1 s1 s1 s1 s0 s1  => bits8 s0 s0 s0 s1 s1 s1 s0 s0  | bits8 s1 s1 s1 s1 s1 s1 s1 s0  => bits8 s0 s0 s0 s1 s1 s0 s0 s1  | bits8 s1 s1 s1 s1 s1 s1 s1 s1  => bits8 s0 s0 s0 s1 s1 s0 s1 s0  end
| 9 => match a with 
| bits8 s0 s0 s0 s0 s0 s0 s0 s0  => bits8 s0 s0 s0 s0 s0 s0 s0 s0  | bits8 s0 s0 s0 s0 s0 s0 s0 s1  => bits8 s0 s0 s0 s0 s1 s0 s0 s1  | bits8 s0 s0 s0 s0 s0 s0 s1 s0  => bits8 s0 s0 s0 s1 s0 s0 s1 s0  | bits8 s0 s0 s0 s0 s0 s0 s1 s1  => bits8 s0 s0 s0 s1 s1 s0 s1 s1  | bits8 s0 s0 s0 s0 s0 s1 s0 s0  => bits8 s0 s0 s1 s0 s0 s1 s0 s0  | bits8 s0 s0 s0 s0 s0 s1 s0 s1  => bits8 s0 s0 s1 s0 s1 s1 s0 s1  | bits8 s0 s0 s0 s0 s0 s1 s1 s0  => bits8 s0 s0 s1 s1 s0 s1 s1 s0  | bits8 s0 s0 s0 s0 s0 s1 s1 s1  => bits8 s0 s0 s1 s1 s1 s1 s1 s1  | bits8 s0 s0 s0 s0 s1 s0 s0 s0  => bits8 s0 s1 s0 s0 s1 s0 s0 s0  | bits8 s0 s0 s0 s0 s1 s0 s0 s1  => bits8 s0 s1 s0 s0 s0 s0 s0 s1  | bits8 s0 s0 s0 s0 s1 s0 s1 s0  => bits8 s0 s1 s0 s1 s1 s0 s1 s0  | bits8 s0 s0 s0 s0 s1 s0 s1 s1  => bits8 s0 s1 s0 s1 s0 s0 s1 s1  | bits8 s0 s0 s0 s0 s1 s1 s0 s0  => bits8 s0 s1 s1 s0 s1 s1 s0 s0  | bits8 s0 s0 s0 s0 s1 s1 s0 s1  => bits8 s0 s1 s1 s0 s0 s1 s0 s1  | bits8 s0 s0 s0 s0 s1 s1 s1 s0  => bits8 s0 s1 s1 s1 s1 s1 s1 s0  | bits8 s0 s0 s0 s0 s1 s1 s1 s1  => bits8 s0 s1 s1 s1 s0 s1 s1 s1  | bits8 s0 s0 s0 s1 s0 s0 s0 s0  => bits8 s1 s0 s0 s1 s0 s0 s0 s0  | bits8 s0 s0 s0 s1 s0 s0 s0 s1  => bits8 s1 s0 s0 s1 s1 s0 s0 s1  | bits8 s0 s0 s0 s1 s0 s0 s1 s0  => bits8 s1 s0 s0 s0 s0 s0 s1 s0  | bits8 s0 s0 s0 s1 s0 s0 s1 s1  => bits8 s1 s0 s0 s0 s1 s0 s1 s1  | bits8 s0 s0 s0 s1 s0 s1 s0 s0  => bits8 s1 s0 s1 s1 s0 s1 s0 s0  | bits8 s0 s0 s0 s1 s0 s1 s0 s1  => bits8 s1 s0 s1 s1 s1 s1 s0 s1  | bits8 s0 s0 s0 s1 s0 s1 s1 s0  => bits8 s1 s0 s1 s0 s0 s1 s1 s0  | bits8 s0 s0 s0 s1 s0 s1 s1 s1  => bits8 s1 s0 s1 s0 s1 s1 s1 s1  | bits8 s0 s0 s0 s1 s1 s0 s0 s0  => bits8 s1 s1 s0 s1 s1 s0 s0 s0  | bits8 s0 s0 s0 s1 s1 s0 s0 s1  => bits8 s1 s1 s0 s1 s0 s0 s0 s1  | bits8 s0 s0 s0 s1 s1 s0 s1 s0  => bits8 s1 s1 s0 s0 s1 s0 s1 s0  | bits8 s0 s0 s0 s1 s1 s0 s1 s1  => bits8 s1 s1 s0 s0 s0 s0 s1 s1  | bits8 s0 s0 s0 s1 s1 s1 s0 s0  => bits8 s1 s1 s1 s1 s1 s1 s0 s0  | bits8 s0 s0 s0 s1 s1 s1 s0 s1  => bits8 s1 s1 s1 s1 s0 s1 s0 s1  | bits8 s0 s0 s0 s1 s1 s1 s1 s0  => bits8 s1 s1 s1 s0 s1 s1 s1 s0  | bits8 s0 s0 s0 s1 s1 s1 s1 s1  => bits8 s1 s1 s1 s0 s0 s1 s1 s1  | bits8 s0 s0 s1 s0 s0 s0 s0 s0  => bits8 s0 s0 s1 s1 s1 s0 s1 s1  | bits8 s0 s0 s1 s0 s0 s0 s0 s1  => bits8 s0 s0 s1 s1 s0 s0 s1 s0  | bits8 s0 s0 s1 s0 s0 s0 s1 s0  => bits8 s0 s0 s1 s0 s1 s0 s0 s1  | bits8 s0 s0 s1 s0 s0 s0 s1 s1  => bits8 s0 s0 s1 s0 s0 s0 s0 s0  | bits8 s0 s0 s1 s0 s0 s1 s0 s0  => bits8 s0 s0 s0 s1 s1 s1 s1 s1  | bits8 s0 s0 s1 s0 s0 s1 s0 s1  => bits8 s0 s0 s0 s1 s0 s1 s1 s0  | bits8 s0 s0 s1 s0 s0 s1 s1 s0  => bits8 s0 s0 s0 s0 s1 s1 s0 s1  | bits8 s0 s0 s1 s0 s0 s1 s1 s1  => bits8 s0 s0 s0 s0 s0 s1 s0 s0  | bits8 s0 s0 s1 s0 s1 s0 s0 s0  => bits8 s0 s1 s1 s1 s0 s0 s1 s1  | bits8 s0 s0 s1 s0 s1 s0 s0 s1  => bits8 s0 s1 s1 s1 s1 s0 s1 s0  | bits8 s0 s0 s1 s0 s1 s0 s1 s0  => bits8 s0 s1 s1 s0 s0 s0 s0 s1  | bits8 s0 s0 s1 s0 s1 s0 s1 s1  => bits8 s0 s1 s1 s0 s1 s0 s0 s0  | bits8 s0 s0 s1 s0 s1 s1 s0 s0  => bits8 s0 s1 s0 s1 s0 s1 s1 s1  | bits8 s0 s0 s1 s0 s1 s1 s0 s1  => bits8 s0 s1 s0 s1 s1 s1 s1 s0  | bits8 s0 s0 s1 s0 s1 s1 s1 s0  => bits8 s0 s1 s0 s0 s0 s1 s0 s1  | bits8 s0 s0 s1 s0 s1 s1 s1 s1  => bits8 s0 s1 s0 s0 s1 s1 s0 s0  | bits8 s0 s0 s1 s1 s0 s0 s0 s0  => bits8 s1 s0 s1 s0 s1 s0 s1 s1  | bits8 s0 s0 s1 s1 s0 s0 s0 s1  => bits8 s1 s0 s1 s0 s0 s0 s1 s0  | bits8 s0 s0 s1 s1 s0 s0 s1 s0  => bits8 s1 s0 s1 s1 s1 s0 s0 s1  | bits8 s0 s0 s1 s1 s0 s0 s1 s1  => bits8 s1 s0 s1 s1 s0 s0 s0 s0  | bits8 s0 s0 s1 s1 s0 s1 s0 s0  => bits8 s1 s0 s0 s0 s1 s1 s1 s1  | bits8 s0 s0 s1 s1 s0 s1 s0 s1  => bits8 s1 s0 s0 s0 s0 s1 s1 s0  | bits8 s0 s0 s1 s1 s0 s1 s1 s0  => bits8 s1 s0 s0 s1 s1 s1 s0 s1  | bits8 s0 s0 s1 s1 s0 s1 s1 s1  => bits8 s1 s0 s0 s1 s0 s1 s0 s0  | bits8 s0 s0 s1 s1 s1 s0 s0 s0  => bits8 s1 s1 s1 s0 s0 s0 s1 s1  | bits8 s0 s0 s1 s1 s1 s0 s0 s1  => bits8 s1 s1 s1 s0 s1 s0 s1 s0  | bits8 s0 s0 s1 s1 s1 s0 s1 s0  => bits8 s1 s1 s1 s1 s0 s0 s0 s1  | bits8 s0 s0 s1 s1 s1 s0 s1 s1  => bits8 s1 s1 s1 s1 s1 s0 s0 s0  | bits8 s0 s0 s1 s1 s1 s1 s0 s0  => bits8 s1 s1 s0 s0 s0 s1 s1 s1  | bits8 s0 s0 s1 s1 s1 s1 s0 s1  => bits8 s1 s1 s0 s0 s1 s1 s1 s0  | bits8 s0 s0 s1 s1 s1 s1 s1 s0  => bits8 s1 s1 s0 s1 s0 s1 s0 s1  | bits8 s0 s0 s1 s1 s1 s1 s1 s1  => bits8 s1 s1 s0 s1 s1 s1 s0 s0  | bits8 s0 s1 s0 s0 s0 s0 s0 s0  => bits8 s0 s1 s1 s1 s0 s1 s1 s0  | bits8 s0 s1 s0 s0 s0 s0 s0 s1  => bits8 s0 s1 s1 s1 s1 s1 s1 s1  | bits8 s0 s1 s0 s0 s0 s0 s1 s0  => bits8 s0 s1 s1 s0 s0 s1 s0 s0  | bits8 s0 s1 s0 s0 s0 s0 s1 s1  => bits8 s0 s1 s1 s0 s1 s1 s0 s1  | bits8 s0 s1 s0 s0 s0 s1 s0 s0  => bits8 s0 s1 s0 s1 s0 s0 s1 s0  | bits8 s0 s1 s0 s0 s0 s1 s0 s1  => bits8 s0 s1 s0 s1 s1 s0 s1 s1  | bits8 s0 s1 s0 s0 s0 s1 s1 s0  => bits8 s0 s1 s0 s0 s0 s0 s0 s0  | bits8 s0 s1 s0 s0 s0 s1 s1 s1  => bits8 s0 s1 s0 s0 s1 s0 s0 s1  | bits8 s0 s1 s0 s0 s1 s0 s0 s0  => bits8 s0 s0 s1 s1 s1 s1 s1 s0  | bits8 s0 s1 s0 s0 s1 s0 s0 s1  => bits8 s0 s0 s1 s1 s0 s1 s1 s1  | bits8 s0 s1 s0 s0 s1 s0 s1 s0  => bits8 s0 s0 s1 s0 s1 s1 s0 s0  | bits8 s0 s1 s0 s0 s1 s0 s1 s1  => bits8 s0 s0 s1 s0 s0 s1 s0 s1  | bits8 s0 s1 s0 s0 s1 s1 s0 s0  => bits8 s0 s0 s0 s1 s1 s0 s1 s0  | bits8 s0 s1 s0 s0 s1 s1 s0 s1  => bits8 s0 s0 s0 s1 s0 s0 s1 s1  | bits8 s0 s1 s0 s0 s1 s1 s1 s0  => bits8 s0 s0 s0 s0 s1 s0 s0 s0  | bits8 s0 s1 s0 s0 s1 s1 s1 s1  => bits8 s0 s0 s0 s0 s0 s0 s0 s1  | bits8 s0 s1 s0 s1 s0 s0 s0 s0  => bits8 s1 s1 s1 s0 s0 s1 s1 s0  | bits8 s0 s1 s0 s1 s0 s0 s0 s1  => bits8 s1 s1 s1 s0 s1 s1 s1 s1  | bits8 s0 s1 s0 s1 s0 s0 s1 s0  => bits8 s1 s1 s1 s1 s0 s1 s0 s0  | bits8 s0 s1 s0 s1 s0 s0 s1 s1  => bits8 s1 s1 s1 s1 s1 s1 s0 s1  | bits8 s0 s1 s0 s1 s0 s1 s0 s0  => bits8 s1 s1 s0 s0 s0 s0 s1 s0  | bits8 s0 s1 s0 s1 s0 s1 s0 s1  => bits8 s1 s1 s0 s0 s1 s0 s1 s1  | bits8 s0 s1 s0 s1 s0 s1 s1 s0  => bits8 s1 s1 s0 s1 s0 s0 s0 s0  | bits8 s0 s1 s0 s1 s0 s1 s1 s1  => bits8 s1 s1 s0 s1 s1 s0 s0 s1  | bits8 s0 s1 s0 s1 s1 s0 s0 s0  => bits8 s1 s0 s1 s0 s1 s1 s1 s0  | bits8 s0 s1 s0 s1 s1 s0 s0 s1  => bits8 s1 s0 s1 s0 s0 s1 s1 s1  | bits8 s0 s1 s0 s1 s1 s0 s1 s0  => bits8 s1 s0 s1 s1 s1 s1 s0 s0  | bits8 s0 s1 s0 s1 s1 s0 s1 s1  => bits8 s1 s0 s1 s1 s0 s1 s0 s1  | bits8 s0 s1 s0 s1 s1 s1 s0 s0  => bits8 s1 s0 s0 s0 s1 s0 s1 s0  | bits8 s0 s1 s0 s1 s1 s1 s0 s1  => bits8 s1 s0 s0 s0 s0 s0 s1 s1  | bits8 s0 s1 s0 s1 s1 s1 s1 s0  => bits8 s1 s0 s0 s1 s1 s0 s0 s0  | bits8 s0 s1 s0 s1 s1 s1 s1 s1  => bits8 s1 s0 s0 s1 s0 s0 s0 s1  | bits8 s0 s1 s1 s0 s0 s0 s0 s0  => bits8 s0 s1 s0 s0 s1 s1 s0 s1  | bits8 s0 s1 s1 s0 s0 s0 s0 s1  => bits8 s0 s1 s0 s0 s0 s1 s0 s0  | bits8 s0 s1 s1 s0 s0 s0 s1 s0  => bits8 s0 s1 s0 s1 s1 s1 s1 s1  | bits8 s0 s1 s1 s0 s0 s0 s1 s1  => bits8 s0 s1 s0 s1 s0 s1 s1 s0  | bits8 s0 s1 s1 s0 s0 s1 s0 s0  => bits8 s0 s1 s1 s0 s1 s0 s0 s1  | bits8 s0 s1 s1 s0 s0 s1 s0 s1  => bits8 s0 s1 s1 s0 s0 s0 s0 s0  | bits8 s0 s1 s1 s0 s0 s1 s1 s0  => bits8 s0 s1 s1 s1 s1 s0 s1 s1  | bits8 s0 s1 s1 s0 s0 s1 s1 s1  => bits8 s0 s1 s1 s1 s0 s0 s1 s0  | bits8 s0 s1 s1 s0 s1 s0 s0 s0  => bits8 s0 s0 s0 s0 s0 s1 s0 s1  | bits8 s0 s1 s1 s0 s1 s0 s0 s1  => bits8 s0 s0 s0 s0 s1 s1 s0 s0  | bits8 s0 s1 s1 s0 s1 s0 s1 s0  => bits8 s0 s0 s0 s1 s0 s1 s1 s1  | bits8 s0 s1 s1 s0 s1 s0 s1 s1  => bits8 s0 s0 s0 s1 s1 s1 s1 s0  | bits8 s0 s1 s1 s0 s1 s1 s0 s0  => bits8 s0 s0 s1 s0 s0 s0 s0 s1  | bits8 s0 s1 s1 s0 s1 s1 s0 s1  => bits8 s0 s0 s1 s0 s1 s0 s0 s0  | bits8 s0 s1 s1 s0 s1 s1 s1 s0  => bits8 s0 s0 s1 s1 s0 s0 s1 s1  | bits8 s0 s1 s1 s0 s1 s1 s1 s1  => bits8 s0 s0 s1 s1 s1 s0 s1 s0  | bits8 s0 s1 s1 s1 s0 s0 s0 s0  => bits8 s1 s1 s0 s1 s1 s1 s0 s1  | bits8 s0 s1 s1 s1 s0 s0 s0 s1  => bits8 s1 s1 s0 s1 s0 s1 s0 s0  | bits8 s0 s1 s1 s1 s0 s0 s1 s0  => bits8 s1 s1 s0 s0 s1 s1 s1 s1  | bits8 s0 s1 s1 s1 s0 s0 s1 s1  => bits8 s1 s1 s0 s0 s0 s1 s1 s0  | bits8 s0 s1 s1 s1 s0 s1 s0 s0  => bits8 s1 s1 s1 s1 s1 s0 s0 s1  | bits8 s0 s1 s1 s1 s0 s1 s0 s1  => bits8 s1 s1 s1 s1 s0 s0 s0 s0  | bits8 s0 s1 s1 s1 s0 s1 s1 s0  => bits8 s1 s1 s1 s0 s1 s0 s1 s1  | bits8 s0 s1 s1 s1 s0 s1 s1 s1  => bits8 s1 s1 s1 s0 s0 s0 s1 s0  | bits8 s0 s1 s1 s1 s1 s0 s0 s0  => bits8 s1 s0 s0 s1 s0 s1 s0 s1  | bits8 s0 s1 s1 s1 s1 s0 s0 s1  => bits8 s1 s0 s0 s1 s1 s1 s0 s0  | bits8 s0 s1 s1 s1 s1 s0 s1 s0  => bits8 s1 s0 s0 s0 s0 s1 s1 s1  | bits8 s0 s1 s1 s1 s1 s0 s1 s1  => bits8 s1 s0 s0 s0 s1 s1 s1 s0  | bits8 s0 s1 s1 s1 s1 s1 s0 s0  => bits8 s1 s0 s1 s1 s0 s0 s0 s1  | bits8 s0 s1 s1 s1 s1 s1 s0 s1  => bits8 s1 s0 s1 s1 s1 s0 s0 s0  | bits8 s0 s1 s1 s1 s1 s1 s1 s0  => bits8 s1 s0 s1 s0 s0 s0 s1 s1  | bits8 s0 s1 s1 s1 s1 s1 s1 s1  => bits8 s1 s0 s1 s0 s1 s0 s1 s0  | bits8 s1 s0 s0 s0 s0 s0 s0 s0  => bits8 s1 s1 s1 s0 s1 s1 s0 s0  | bits8 s1 s0 s0 s0 s0 s0 s0 s1  => bits8 s1 s1 s1 s0 s0 s1 s0 s1  | bits8 s1 s0 s0 s0 s0 s0 s1 s0  => bits8 s1 s1 s1 s1 s1 s1 s1 s0  | bits8 s1 s0 s0 s0 s0 s0 s1 s1  => bits8 s1 s1 s1 s1 s0 s1 s1 s1  | bits8 s1 s0 s0 s0 s0 s1 s0 s0  => bits8 s1 s1 s0 s0 s1 s0 s0 s0  | bits8 s1 s0 s0 s0 s0 s1 s0 s1  => bits8 s1 s1 s0 s0 s0 s0 s0 s1  | bits8 s1 s0 s0 s0 s0 s1 s1 s0  => bits8 s1 s1 s0 s1 s1 s0 s1 s0  | bits8 s1 s0 s0 s0 s0 s1 s1 s1  => bits8 s1 s1 s0 s1 s0 s0 s1 s1  | bits8 s1 s0 s0 s0 s1 s0 s0 s0  => bits8 s1 s0 s1 s0 s0 s1 s0 s0  | bits8 s1 s0 s0 s0 s1 s0 s0 s1  => bits8 s1 s0 s1 s0 s1 s1 s0 s1  | bits8 s1 s0 s0 s0 s1 s0 s1 s0  => bits8 s1 s0 s1 s1 s0 s1 s1 s0  | bits8 s1 s0 s0 s0 s1 s0 s1 s1  => bits8 s1 s0 s1 s1 s1 s1 s1 s1  | bits8 s1 s0 s0 s0 s1 s1 s0 s0  => bits8 s1 s0 s0 s0 s0 s0 s0 s0  | bits8 s1 s0 s0 s0 s1 s1 s0 s1  => bits8 s1 s0 s0 s0 s1 s0 s0 s1  | bits8 s1 s0 s0 s0 s1 s1 s1 s0  => bits8 s1 s0 s0 s1 s0 s0 s1 s0  | bits8 s1 s0 s0 s0 s1 s1 s1 s1  => bits8 s1 s0 s0 s1 s1 s0 s1 s1  | bits8 s1 s0 s0 s1 s0 s0 s0 s0  => bits8 s0 s1 s1 s1 s1 s1 s0 s0  | bits8 s1 s0 s0 s1 s0 s0 s0 s1  => bits8 s0 s1 s1 s1 s0 s1 s0 s1  | bits8 s1 s0 s0 s1 s0 s0 s1 s0  => bits8 s0 s1 s1 s0 s1 s1 s1 s0  | bits8 s1 s0 s0 s1 s0 s0 s1 s1  => bits8 s0 s1 s1 s0 s0 s1 s1 s1  | bits8 s1 s0 s0 s1 s0 s1 s0 s0  => bits8 s0 s1 s0 s1 s1 s0 s0 s0  | bits8 s1 s0 s0 s1 s0 s1 s0 s1  => bits8 s0 s1 s0 s1 s0 s0 s0 s1  | bits8 s1 s0 s0 s1 s0 s1 s1 s0  => bits8 s0 s1 s0 s0 s1 s0 s1 s0  | bits8 s1 s0 s0 s1 s0 s1 s1 s1  => bits8 s0 s1 s0 s0 s0 s0 s1 s1  | bits8 s1 s0 s0 s1 s1 s0 s0 s0  => bits8 s0 s0 s1 s1 s0 s1 s0 s0  | bits8 s1 s0 s0 s1 s1 s0 s0 s1  => bits8 s0 s0 s1 s1 s1 s1 s0 s1  | bits8 s1 s0 s0 s1 s1 s0 s1 s0  => bits8 s0 s0 s1 s0 s0 s1 s1 s0  | bits8 s1 s0 s0 s1 s1 s0 s1 s1  => bits8 s0 s0 s1 s0 s1 s1 s1 s1  | bits8 s1 s0 s0 s1 s1 s1 s0 s0  => bits8 s0 s0 s0 s1 s0 s0 s0 s0  | bits8 s1 s0 s0 s1 s1 s1 s0 s1  => bits8 s0 s0 s0 s1 s1 s0 s0 s1  | bits8 s1 s0 s0 s1 s1 s1 s1 s0  => bits8 s0 s0 s0 s0 s0 s0 s1 s0  | bits8 s1 s0 s0 s1 s1 s1 s1 s1  => bits8 s0 s0 s0 s0 s1 s0 s1 s1  | bits8 s1 s0 s1 s0 s0 s0 s0 s0  => bits8 s1 s1 s0 s1 s0 s1 s1 s1  | bits8 s1 s0 s1 s0 s0 s0 s0 s1  => bits8 s1 s1 s0 s1 s1 s1 s1 s0  | bits8 s1 s0 s1 s0 s0 s0 s1 s0  => bits8 s1 s1 s0 s0 s0 s1 s0 s1  | bits8 s1 s0 s1 s0 s0 s0 s1 s1  => bits8 s1 s1 s0 s0 s1 s1 s0 s0  | bits8 s1 s0 s1 s0 s0 s1 s0 s0  => bits8 s1 s1 s1 s1 s0 s0 s1 s1  | bits8 s1 s0 s1 s0 s0 s1 s0 s1  => bits8 s1 s1 s1 s1 s1 s0 s1 s0  | bits8 s1 s0 s1 s0 s0 s1 s1 s0  => bits8 s1 s1 s1 s0 s0 s0 s0 s1  | bits8 s1 s0 s1 s0 s0 s1 s1 s1  => bits8 s1 s1 s1 s0 s1 s0 s0 s0  | bits8 s1 s0 s1 s0 s1 s0 s0 s0  => bits8 s1 s0 s0 s1 s1 s1 s1 s1  | bits8 s1 s0 s1 s0 s1 s0 s0 s1  => bits8 s1 s0 s0 s1 s0 s1 s1 s0  | bits8 s1 s0 s1 s0 s1 s0 s1 s0  => bits8 s1 s0 s0 s0 s1 s1 s0 s1  | bits8 s1 s0 s1 s0 s1 s0 s1 s1  => bits8 s1 s0 s0 s0 s0 s1 s0 s0  | bits8 s1 s0 s1 s0 s1 s1 s0 s0  => bits8 s1 s0 s1 s1 s1 s0 s1 s1  | bits8 s1 s0 s1 s0 s1 s1 s0 s1  => bits8 s1 s0 s1 s1 s0 s0 s1 s0  | bits8 s1 s0 s1 s0 s1 s1 s1 s0  => bits8 s1 s0 s1 s0 s1 s0 s0 s1  | bits8 s1 s0 s1 s0 s1 s1 s1 s1  => bits8 s1 s0 s1 s0 s0 s0 s0 s0  | bits8 s1 s0 s1 s1 s0 s0 s0 s0  => bits8 s0 s1 s0 s0 s0 s1 s1 s1  | bits8 s1 s0 s1 s1 s0 s0 s0 s1  => bits8 s0 s1 s0 s0 s1 s1 s1 s0  | bits8 s1 s0 s1 s1 s0 s0 s1 s0  => bits8 s0 s1 s0 s1 s0 s1 s0 s1  | bits8 s1 s0 s1 s1 s0 s0 s1 s1  => bits8 s0 s1 s0 s1 s1 s1 s0 s0  | bits8 s1 s0 s1 s1 s0 s1 s0 s0  => bits8 s0 s1 s1 s0 s0 s0 s1 s1  | bits8 s1 s0 s1 s1 s0 s1 s0 s1  => bits8 s0 s1 s1 s0 s1 s0 s1 s0  | bits8 s1 s0 s1 s1 s0 s1 s1 s0  => bits8 s0 s1 s1 s1 s0 s0 s0 s1  | bits8 s1 s0 s1 s1 s0 s1 s1 s1  => bits8 s0 s1 s1 s1 s1 s0 s0 s0  | bits8 s1 s0 s1 s1 s1 s0 s0 s0  => bits8 s0 s0 s0 s0 s1 s1 s1 s1  | bits8 s1 s0 s1 s1 s1 s0 s0 s1  => bits8 s0 s0 s0 s0 s0 s1 s1 s0  | bits8 s1 s0 s1 s1 s1 s0 s1 s0  => bits8 s0 s0 s0 s1 s1 s1 s0 s1  | bits8 s1 s0 s1 s1 s1 s0 s1 s1  => bits8 s0 s0 s0 s1 s0 s1 s0 s0  | bits8 s1 s0 s1 s1 s1 s1 s0 s0  => bits8 s0 s0 s1 s0 s1 s0 s1 s1  | bits8 s1 s0 s1 s1 s1 s1 s0 s1  => bits8 s0 s0 s1 s0 s0 s0 s1 s0  | bits8 s1 s0 s1 s1 s1 s1 s1 s0  => bits8 s0 s0 s1 s1 s1 s0 s0 s1  | bits8 s1 s0 s1 s1 s1 s1 s1 s1  => bits8 s0 s0 s1 s1 s0 s0 s0 s0  | bits8 s1 s1 s0 s0 s0 s0 s0 s0  => bits8 s1 s0 s0 s1 s1 s0 s1 s0  | bits8 s1 s1 s0 s0 s0 s0 s0 s1  => bits8 s1 s0 s0 s1 s0 s0 s1 s1  | bits8 s1 s1 s0 s0 s0 s0 s1 s0  => bits8 s1 s0 s0 s0 s1 s0 s0 s0  | bits8 s1 s1 s0 s0 s0 s0 s1 s1  => bits8 s1 s0 s0 s0 s0 s0 s0 s1  | bits8 s1 s1 s0 s0 s0 s1 s0 s0  => bits8 s1 s0 s1 s1 s1 s1 s1 s0  | bits8 s1 s1 s0 s0 s0 s1 s0 s1  => bits8 s1 s0 s1 s1 s0 s1 s1 s1  | bits8 s1 s1 s0 s0 s0 s1 s1 s0  => bits8 s1 s0 s1 s0 s1 s1 s0 s0  | bits8 s1 s1 s0 s0 s0 s1 s1 s1  => bits8 s1 s0 s1 s0 s0 s1 s0 s1  | bits8 s1 s1 s0 s0 s1 s0 s0 s0  => bits8 s1 s1 s0 s1 s0 s0 s1 s0  | bits8 s1 s1 s0 s0 s1 s0 s0 s1  => bits8 s1 s1 s0 s1 s1 s0 s1 s1  | bits8 s1 s1 s0 s0 s1 s0 s1 s0  => bits8 s1 s1 s0 s0 s0 s0 s0 s0  | bits8 s1 s1 s0 s0 s1 s0 s1 s1  => bits8 s1 s1 s0 s0 s1 s0 s0 s1  | bits8 s1 s1 s0 s0 s1 s1 s0 s0  => bits8 s1 s1 s1 s1 s0 s1 s1 s0  | bits8 s1 s1 s0 s0 s1 s1 s0 s1  => bits8 s1 s1 s1 s1 s1 s1 s1 s1  | bits8 s1 s1 s0 s0 s1 s1 s1 s0  => bits8 s1 s1 s1 s0 s0 s1 s0 s0  | bits8 s1 s1 s0 s0 s1 s1 s1 s1  => bits8 s1 s1 s1 s0 s1 s1 s0 s1  | bits8 s1 s1 s0 s1 s0 s0 s0 s0  => bits8 s0 s0 s0 s0 s1 s0 s1 s0  | bits8 s1 s1 s0 s1 s0 s0 s0 s1  => bits8 s0 s0 s0 s0 s0 s0 s1 s1  | bits8 s1 s1 s0 s1 s0 s0 s1 s0  => bits8 s0 s0 s0 s1 s1 s0 s0 s0  | bits8 s1 s1 s0 s1 s0 s0 s1 s1  => bits8 s0 s0 s0 s1 s0 s0 s0 s1  | bits8 s1 s1 s0 s1 s0 s1 s0 s0  => bits8 s0 s0 s1 s0 s1 s1 s1 s0  | bits8 s1 s1 s0 s1 s0 s1 s0 s1  => bits8 s0 s0 s1 s0 s0 s1 s1 s1  | bits8 s1 s1 s0 s1 s0 s1 s1 s0  => bits8 s0 s0 s1 s1 s1 s1 s0 s0  | bits8 s1 s1 s0 s1 s0 s1 s1 s1  => bits8 s0 s0 s1 s1 s0 s1 s0 s1  | bits8 s1 s1 s0 s1 s1 s0 s0 s0  => bits8 s0 s1 s0 s0 s0 s0 s1 s0  | bits8 s1 s1 s0 s1 s1 s0 s0 s1  => bits8 s0 s1 s0 s0 s1 s0 s1 s1  | bits8 s1 s1 s0 s1 s1 s0 s1 s0  => bits8 s0 s1 s0 s1 s0 s0 s0 s0  | bits8 s1 s1 s0 s1 s1 s0 s1 s1  => bits8 s0 s1 s0 s1 s1 s0 s0 s1  | bits8 s1 s1 s0 s1 s1 s1 s0 s0  => bits8 s0 s1 s1 s0 s0 s1 s1 s0  | bits8 s1 s1 s0 s1 s1 s1 s0 s1  => bits8 s0 s1 s1 s0 s1 s1 s1 s1  | bits8 s1 s1 s0 s1 s1 s1 s1 s0  => bits8 s0 s1 s1 s1 s0 s1 s0 s0  | bits8 s1 s1 s0 s1 s1 s1 s1 s1  => bits8 s0 s1 s1 s1 s1 s1 s0 s1  | bits8 s1 s1 s1 s0 s0 s0 s0 s0  => bits8 s1 s0 s1 s0 s0 s0 s0 s1  | bits8 s1 s1 s1 s0 s0 s0 s0 s1  => bits8 s1 s0 s1 s0 s1 s0 s0 s0  | bits8 s1 s1 s1 s0 s0 s0 s1 s0  => bits8 s1 s0 s1 s1 s0 s0 s1 s1  | bits8 s1 s1 s1 s0 s0 s0 s1 s1  => bits8 s1 s0 s1 s1 s1 s0 s1 s0  | bits8 s1 s1 s1 s0 s0 s1 s0 s0  => bits8 s1 s0 s0 s0 s0 s1 s0 s1  | bits8 s1 s1 s1 s0 s0 s1 s0 s1  => bits8 s1 s0 s0 s0 s1 s1 s0 s0  | bits8 s1 s1 s1 s0 s0 s1 s1 s0  => bits8 s1 s0 s0 s1 s0 s1 s1 s1  | bits8 s1 s1 s1 s0 s0 s1 s1 s1  => bits8 s1 s0 s0 s1 s1 s1 s1 s0  | bits8 s1 s1 s1 s0 s1 s0 s0 s0  => bits8 s1 s1 s1 s0 s1 s0 s0 s1  | bits8 s1 s1 s1 s0 s1 s0 s0 s1  => bits8 s1 s1 s1 s0 s0 s0 s0 s0  | bits8 s1 s1 s1 s0 s1 s0 s1 s0  => bits8 s1 s1 s1 s1 s1 s0 s1 s1  | bits8 s1 s1 s1 s0 s1 s0 s1 s1  => bits8 s1 s1 s1 s1 s0 s0 s1 s0  | bits8 s1 s1 s1 s0 s1 s1 s0 s0  => bits8 s1 s1 s0 s0 s1 s1 s0 s1  | bits8 s1 s1 s1 s0 s1 s1 s0 s1  => bits8 s1 s1 s0 s0 s0 s1 s0 s0  | bits8 s1 s1 s1 s0 s1 s1 s1 s0  => bits8 s1 s1 s0 s1 s1 s1 s1 s1  | bits8 s1 s1 s1 s0 s1 s1 s1 s1  => bits8 s1 s1 s0 s1 s0 s1 s1 s0  | bits8 s1 s1 s1 s1 s0 s0 s0 s0  => bits8 s0 s0 s1 s1 s0 s0 s0 s1  | bits8 s1 s1 s1 s1 s0 s0 s0 s1  => bits8 s0 s0 s1 s1 s1 s0 s0 s0  | bits8 s1 s1 s1 s1 s0 s0 s1 s0  => bits8 s0 s0 s1 s0 s0 s0 s1 s1  | bits8 s1 s1 s1 s1 s0 s0 s1 s1  => bits8 s0 s0 s1 s0 s1 s0 s1 s0  | bits8 s1 s1 s1 s1 s0 s1 s0 s0  => bits8 s0 s0 s0 s1 s0 s1 s0 s1  | bits8 s1 s1 s1 s1 s0 s1 s0 s1  => bits8 s0 s0 s0 s1 s1 s1 s0 s0  | bits8 s1 s1 s1 s1 s0 s1 s1 s0  => bits8 s0 s0 s0 s0 s0 s1 s1 s1  | bits8 s1 s1 s1 s1 s0 s1 s1 s1  => bits8 s0 s0 s0 s0 s1 s1 s1 s0  | bits8 s1 s1 s1 s1 s1 s0 s0 s0  => bits8 s0 s1 s1 s1 s1 s0 s0 s1  | bits8 s1 s1 s1 s1 s1 s0 s0 s1  => bits8 s0 s1 s1 s1 s0 s0 s0 s0  | bits8 s1 s1 s1 s1 s1 s0 s1 s0  => bits8 s0 s1 s1 s0 s1 s0 s1 s1  | bits8 s1 s1 s1 s1 s1 s0 s1 s1  => bits8 s0 s1 s1 s0 s0 s0 s1 s0  | bits8 s1 s1 s1 s1 s1 s1 s0 s0  => bits8 s0 s1 s0 s1 s1 s1 s0 s1  | bits8 s1 s1 s1 s1 s1 s1 s0 s1  => bits8 s0 s1 s0 s1 s0 s1 s0 s0  | bits8 s1 s1 s1 s1 s1 s1 s1 s0  => bits8 s0 s1 s0 s0 s1 s1 s1 s1  | bits8 s1 s1 s1 s1 s1 s1 s1 s1  => bits8 s0 s1 s0 s0 s0 s1 s1 s0  end
| 11 => match a with 
| bits8 s0 s0 s0 s0 s0 s0 s0 s0  => bits8 s0 s0 s0 s0 s0 s0 s0 s0  | bits8 s0 s0 s0 s0 s0 s0 s0 s1  => bits8 s0 s0 s0 s0 s1 s0 s1 s1  | bits8 s0 s0 s0 s0 s0 s0 s1 s0  => bits8 s0 s0 s0 s1 s0 s1 s1 s0  | bits8 s0 s0 s0 s0 s0 s0 s1 s1  => bits8 s0 s0 s0 s1 s1 s1 s0 s1  | bits8 s0 s0 s0 s0 s0 s1 s0 s0  => bits8 s0 s0 s1 s0 s1 s1 s0 s0  | bits8 s0 s0 s0 s0 s0 s1 s0 s1  => bits8 s0 s0 s1 s0 s0 s1 s1 s1  | bits8 s0 s0 s0 s0 s0 s1 s1 s0  => bits8 s0 s0 s1 s1 s1 s0 s1 s0  | bits8 s0 s0 s0 s0 s0 s1 s1 s1  => bits8 s0 s0 s1 s1 s0 s0 s0 s1  | bits8 s0 s0 s0 s0 s1 s0 s0 s0  => bits8 s0 s1 s0 s1 s1 s0 s0 s0  | bits8 s0 s0 s0 s0 s1 s0 s0 s1  => bits8 s0 s1 s0 s1 s0 s0 s1 s1  | bits8 s0 s0 s0 s0 s1 s0 s1 s0  => bits8 s0 s1 s0 s0 s1 s1 s1 s0  | bits8 s0 s0 s0 s0 s1 s0 s1 s1  => bits8 s0 s1 s0 s0 s0 s1 s0 s1  | bits8 s0 s0 s0 s0 s1 s1 s0 s0  => bits8 s0 s1 s1 s1 s0 s1 s0 s0  | bits8 s0 s0 s0 s0 s1 s1 s0 s1  => bits8 s0 s1 s1 s1 s1 s1 s1 s1  | bits8 s0 s0 s0 s0 s1 s1 s1 s0  => bits8 s0 s1 s1 s0 s0 s0 s1 s0  | bits8 s0 s0 s0 s0 s1 s1 s1 s1  => bits8 s0 s1 s1 s0 s1 s0 s0 s1  | bits8 s0 s0 s0 s1 s0 s0 s0 s0  => bits8 s1 s0 s1 s1 s0 s0 s0 s0  | bits8 s0 s0 s0 s1 s0 s0 s0 s1  => bits8 s1 s0 s1 s1 s1 s0 s1 s1  | bits8 s0 s0 s0 s1 s0 s0 s1 s0  => bits8 s1 s0 s1 s0 s0 s1 s1 s0  | bits8 s0 s0 s0 s1 s0 s0 s1 s1  => bits8 s1 s0 s1 s0 s1 s1 s0 s1  | bits8 s0 s0 s0 s1 s0 s1 s0 s0  => bits8 s1 s0 s0 s1 s1 s1 s0 s0  | bits8 s0 s0 s0 s1 s0 s1 s0 s1  => bits8 s1 s0 s0 s1 s0 s1 s1 s1  | bits8 s0 s0 s0 s1 s0 s1 s1 s0  => bits8 s1 s0 s0 s0 s1 s0 s1 s0  | bits8 s0 s0 s0 s1 s0 s1 s1 s1  => bits8 s1 s0 s0 s0 s0 s0 s0 s1  | bits8 s0 s0 s0 s1 s1 s0 s0 s0  => bits8 s1 s1 s1 s0 s1 s0 s0 s0  | bits8 s0 s0 s0 s1 s1 s0 s0 s1  => bits8 s1 s1 s1 s0 s0 s0 s1 s1  | bits8 s0 s0 s0 s1 s1 s0 s1 s0  => bits8 s1 s1 s1 s1 s1 s1 s1 s0  | bits8 s0 s0 s0 s1 s1 s0 s1 s1  => bits8 s1 s1 s1 s1 s0 s1 s0 s1  | bits8 s0 s0 s0 s1 s1 s1 s0 s0  => bits8 s1 s1 s0 s0 s0 s1 s0 s0  | bits8 s0 s0 s0 s1 s1 s1 s0 s1  => bits8 s1 s1 s0 s0 s1 s1 s1 s1  | bits8 s0 s0 s0 s1 s1 s1 s1 s0  => bits8 s1 s1 s0 s1 s0 s0 s1 s0  | bits8 s0 s0 s0 s1 s1 s1 s1 s1  => bits8 s1 s1 s0 s1 s1 s0 s0 s1  | bits8 s0 s0 s1 s0 s0 s0 s0 s0  => bits8 s0 s1 s1 s1 s1 s0 s1 s1  | bits8 s0 s0 s1 s0 s0 s0 s0 s1  => bits8 s0 s1 s1 s1 s0 s0 s0 s0  | bits8 s0 s0 s1 s0 s0 s0 s1 s0  => bits8 s0 s1 s1 s0 s1 s1 s0 s1  | bits8 s0 s0 s1 s0 s0 s0 s1 s1  => bits8 s0 s1 s1 s0 s0 s1 s1 s0  | bits8 s0 s0 s1 s0 s0 s1 s0 s0  => bits8 s0 s1 s0 s1 s0 s1 s1 s1  | bits8 s0 s0 s1 s0 s0 s1 s0 s1  => bits8 s0 s1 s0 s1 s1 s1 s0 s0  | bits8 s0 s0 s1 s0 s0 s1 s1 s0  => bits8 s0 s1 s0 s0 s0 s0 s0 s1  | bits8 s0 s0 s1 s0 s0 s1 s1 s1  => bits8 s0 s1 s0 s0 s1 s0 s1 s0  | bits8 s0 s0 s1 s0 s1 s0 s0 s0  => bits8 s0 s0 s1 s0 s0 s0 s1 s1  | bits8 s0 s0 s1 s0 s1 s0 s0 s1  => bits8 s0 s0 s1 s0 s1 s0 s0 s0  | bits8 s0 s0 s1 s0 s1 s0 s1 s0  => bits8 s0 s0 s1 s1 s0 s1 s0 s1  | bits8 s0 s0 s1 s0 s1 s0 s1 s1  => bits8 s0 s0 s1 s1 s1 s1 s1 s0  | bits8 s0 s0 s1 s0 s1 s1 s0 s0  => bits8 s0 s0 s0 s0 s1 s1 s1 s1  | bits8 s0 s0 s1 s0 s1 s1 s0 s1  => bits8 s0 s0 s0 s0 s0 s1 s0 s0  | bits8 s0 s0 s1 s0 s1 s1 s1 s0  => bits8 s0 s0 s0 s1 s1 s0 s0 s1  | bits8 s0 s0 s1 s0 s1 s1 s1 s1  => bits8 s0 s0 s0 s1 s0 s0 s1 s0  | bits8 s0 s0 s1 s1 s0 s0 s0 s0  => bits8 s1 s1 s0 s0 s1 s0 s1 s1  | bits8 s0 s0 s1 s1 s0 s0 s0 s1  => bits8 s1 s1 s0 s0 s0 s0 s0 s0  | bits8 s0 s0 s1 s1 s0 s0 s1 s0  => bits8 s1 s1 s0 s1 s1 s1 s0 s1  | bits8 s0 s0 s1 s1 s0 s0 s1 s1  => bits8 s1 s1 s0 s1 s0 s1 s1 s0  | bits8 s0 s0 s1 s1 s0 s1 s0 s0  => bits8 s1 s1 s1 s0 s0 s1 s1 s1  | bits8 s0 s0 s1 s1 s0 s1 s0 s1  => bits8 s1 s1 s1 s0 s1 s1 s0 s0  | bits8 s0 s0 s1 s1 s0 s1 s1 s0  => bits8 s1 s1 s1 s1 s0 s0 s0 s1  | bits8 s0 s0 s1 s1 s0 s1 s1 s1  => bits8 s1 s1 s1 s1 s1 s0 s1 s0  | bits8 s0 s0 s1 s1 s1 s0 s0 s0  => bits8 s1 s0 s0 s1 s0 s0 s1 s1  | bits8 s0 s0 s1 s1 s1 s0 s0 s1  => bits8 s1 s0 s0 s1 s1 s0 s0 s0  | bits8 s0 s0 s1 s1 s1 s0 s1 s0  => bits8 s1 s0 s0 s0 s0 s1 s0 s1  | bits8 s0 s0 s1 s1 s1 s0 s1 s1  => bits8 s1 s0 s0 s0 s1 s1 s1 s0  | bits8 s0 s0 s1 s1 s1 s1 s0 s0  => bits8 s1 s0 s1 s1 s1 s1 s1 s1  | bits8 s0 s0 s1 s1 s1 s1 s0 s1  => bits8 s1 s0 s1 s1 s0 s1 s0 s0  | bits8 s0 s0 s1 s1 s1 s1 s1 s0  => bits8 s1 s0 s1 s0 s1 s0 s0 s1  | bits8 s0 s0 s1 s1 s1 s1 s1 s1  => bits8 s1 s0 s1 s0 s0 s0 s1 s0  | bits8 s0 s1 s0 s0 s0 s0 s0 s0  => bits8 s1 s1 s1 s1 s0 s1 s1 s0  | bits8 s0 s1 s0 s0 s0 s0 s0 s1  => bits8 s1 s1 s1 s1 s1 s1 s0 s1  | bits8 s0 s1 s0 s0 s0 s0 s1 s0  => bits8 s1 s1 s1 s0 s0 s0 s0 s0  | bits8 s0 s1 s0 s0 s0 s0 s1 s1  => bits8 s1 s1 s1 s0 s1 s0 s1 s1  | bits8 s0 s1 s0 s0 s0 s1 s0 s0  => bits8 s1 s1 s0 s1 s1 s0 s1 s0  | bits8 s0 s1 s0 s0 s0 s1 s0 s1  => bits8 s1 s1 s0 s1 s0 s0 s0 s1  | bits8 s0 s1 s0 s0 s0 s1 s1 s0  => bits8 s1 s1 s0 s0 s1 s1 s0 s0  | bits8 s0 s1 s0 s0 s0 s1 s1 s1  => bits8 s1 s1 s0 s0 s0 s1 s1 s1  | bits8 s0 s1 s0 s0 s1 s0 s0 s0  => bits8 s1 s0 s1 s0 s1 s1 s1 s0  | bits8 s0 s1 s0 s0 s1 s0 s0 s1  => bits8 s1 s0 s1 s0 s0 s1 s0 s1  | bits8 s0 s1 s0 s0 s1 s0 s1 s0  => bits8 s1 s0 s1 s1 s1 s0 s0 s0  | bits8 s0 s1 s0 s0 s1 s0 s1 s1  => bits8 s1 s0 s1 s1 s0 s0 s1 s1  | bits8 s0 s1 s0 s0 s1 s1 s0 s0  => bits8 s1 s0 s0 s0 s0 s0 s1 s0  | bits8 s0 s1 s0 s0 s1 s1 s0 s1  => bits8 s1 s0 s0 s0 s1 s0 s0 s1  | bits8 s0 s1 s0 s0 s1 s1 s1 s0  => bits8 s1 s0 s0 s1 s0 s1 s0 s0  | bits8 s0 s1 s0 s0 s1 s1 s1 s1  => bits8 s1 s0 s0 s1 s1 s1 s1 s1  | bits8 s0 s1 s0 s1 s0 s0 s0 s0  => bits8 s0 s1 s0 s0 s0 s1 s1 s0  | bits8 s0 s1 s0 s1 s0 s0 s0 s1  => bits8 s0 s1 s0 s0 s1 s1 s0 s1  | bits8 s0 s1 s0 s1 s0 s0 s1 s0  => bits8 s0 s1 s0 s1 s0 s0 s0 s0  | bits8 s0 s1 s0 s1 s0 s0 s1 s1  => bits8 s0 s1 s0 s1 s1 s0 s1 s1  | bits8 s0 s1 s0 s1 s0 s1 s0 s0  => bits8 s0 s1 s1 s0 s1 s0 s1 s0  | bits8 s0 s1 s0 s1 s0 s1 s0 s1  => bits8 s0 s1 s1 s0 s0 s0 s0 s1  | bits8 s0 s1 s0 s1 s0 s1 s1 s0  => bits8 s0 s1 s1 s1 s1 s1 s0 s0  | bits8 s0 s1 s0 s1 s0 s1 s1 s1  => bits8 s0 s1 s1 s1 s0 s1 s1 s1  | bits8 s0 s1 s0 s1 s1 s0 s0 s0  => bits8 s0 s0 s0 s1 s1 s1 s1 s0  | bits8 s0 s1 s0 s1 s1 s0 s0 s1  => bits8 s0 s0 s0 s1 s0 s1 s0 s1  | bits8 s0 s1 s0 s1 s1 s0 s1 s0  => bits8 s0 s0 s0 s0 s1 s0 s0 s0  | bits8 s0 s1 s0 s1 s1 s0 s1 s1  => bits8 s0 s0 s0 s0 s0 s0 s1 s1  | bits8 s0 s1 s0 s1 s1 s1 s0 s0  => bits8 s0 s0 s1 s1 s0 s0 s1 s0  | bits8 s0 s1 s0 s1 s1 s1 s0 s1  => bits8 s0 s0 s1 s1 s1 s0 s0 s1  | bits8 s0 s1 s0 s1 s1 s1 s1 s0  => bits8 s0 s0 s1 s0 s0 s1 s0 s0  | bits8 s0 s1 s0 s1 s1 s1 s1 s1  => bits8 s0 s0 s1 s0 s1 s1 s1 s1  | bits8 s0 s1 s1 s0 s0 s0 s0 s0  => bits8 s1 s0 s0 s0 s1 s1 s0 s1  | bits8 s0 s1 s1 s0 s0 s0 s0 s1  => bits8 s1 s0 s0 s0 s0 s1 s1 s0  | bits8 s0 s1 s1 s0 s0 s0 s1 s0  => bits8 s1 s0 s0 s1 s1 s0 s1 s1  | bits8 s0 s1 s1 s0 s0 s0 s1 s1  => bits8 s1 s0 s0 s1 s0 s0 s0 s0  | bits8 s0 s1 s1 s0 s0 s1 s0 s0  => bits8 s1 s0 s1 s0 s0 s0 s0 s1  | bits8 s0 s1 s1 s0 s0 s1 s0 s1  => bits8 s1 s0 s1 s0 s1 s0 s1 s0  | bits8 s0 s1 s1 s0 s0 s1 s1 s0  => bits8 s1 s0 s1 s1 s0 s1 s1 s1  | bits8 s0 s1 s1 s0 s0 s1 s1 s1  => bits8 s1 s0 s1 s1 s1 s1 s0 s0  | bits8 s0 s1 s1 s0 s1 s0 s0 s0  => bits8 s1 s1 s0 s1 s0 s1 s0 s1  | bits8 s0 s1 s1 s0 s1 s0 s0 s1  => bits8 s1 s1 s0 s1 s1 s1 s1 s0  | bits8 s0 s1 s1 s0 s1 s0 s1 s0  => bits8 s1 s1 s0 s0 s0 s0 s1 s1  | bits8 s0 s1 s1 s0 s1 s0 s1 s1  => bits8 s1 s1 s0 s0 s1 s0 s0 s0  | bits8 s0 s1 s1 s0 s1 s1 s0 s0  => bits8 s1 s1 s1 s1 s1 s0 s0 s1  | bits8 s0 s1 s1 s0 s1 s1 s0 s1  => bits8 s1 s1 s1 s1 s0 s0 s1 s0  | bits8 s0 s1 s1 s0 s1 s1 s1 s0  => bits8 s1 s1 s1 s0 s1 s1 s1 s1  | bits8 s0 s1 s1 s0 s1 s1 s1 s1  => bits8 s1 s1 s1 s0 s0 s1 s0 s0  | bits8 s0 s1 s1 s1 s0 s0 s0 s0  => bits8 s0 s0 s1 s1 s1 s1 s0 s1  | bits8 s0 s1 s1 s1 s0 s0 s0 s1  => bits8 s0 s0 s1 s1 s0 s1 s1 s0  | bits8 s0 s1 s1 s1 s0 s0 s1 s0  => bits8 s0 s0 s1 s0 s1 s0 s1 s1  | bits8 s0 s1 s1 s1 s0 s0 s1 s1  => bits8 s0 s0 s1 s0 s0 s0 s0 s0  | bits8 s0 s1 s1 s1 s0 s1 s0 s0  => bits8 s0 s0 s0 s1 s0 s0 s0 s1  | bits8 s0 s1 s1 s1 s0 s1 s0 s1  => bits8 s0 s0 s0 s1 s1 s0 s1 s0  | bits8 s0 s1 s1 s1 s0 s1 s1 s0  => bits8 s0 s0 s0 s0 s0 s1 s1 s1  | bits8 s0 s1 s1 s1 s0 s1 s1 s1  => bits8 s0 s0 s0 s0 s1 s1 s0 s0  | bits8 s0 s1 s1 s1 s1 s0 s0 s0  => bits8 s0 s1 s1 s0 s0 s1 s0 s1  | bits8 s0 s1 s1 s1 s1 s0 s0 s1  => bits8 s0 s1 s1 s0 s1 s1 s1 s0  | bits8 s0 s1 s1 s1 s1 s0 s1 s0  => bits8 s0 s1 s1 s1 s0 s0 s1 s1  | bits8 s0 s1 s1 s1 s1 s0 s1 s1  => bits8 s0 s1 s1 s1 s1 s0 s0 s0  | bits8 s0 s1 s1 s1 s1 s1 s0 s0  => bits8 s0 s1 s0 s0 s1 s0 s0 s1  | bits8 s0 s1 s1 s1 s1 s1 s0 s1  => bits8 s0 s1 s0 s0 s0 s0 s1 s0  | bits8 s0 s1 s1 s1 s1 s1 s1 s0  => bits8 s0 s1 s0 s1 s1 s1 s1 s1  | bits8 s0 s1 s1 s1 s1 s1 s1 s1  => bits8 s0 s1 s0 s1 s0 s1 s0 s0  | bits8 s1 s0 s0 s0 s0 s0 s0 s0  => bits8 s1 s1 s1 s1 s0 s1 s1 s1  | bits8 s1 s0 s0 s0 s0 s0 s0 s1  => bits8 s1 s1 s1 s1 s1 s1 s0 s0  | bits8 s1 s0 s0 s0 s0 s0 s1 s0  => bits8 s1 s1 s1 s0 s0 s0 s0 s1  | bits8 s1 s0 s0 s0 s0 s0 s1 s1  => bits8 s1 s1 s1 s0 s1 s0 s1 s0  | bits8 s1 s0 s0 s0 s0 s1 s0 s0  => bits8 s1 s1 s0 s1 s1 s0 s1 s1  | bits8 s1 s0 s0 s0 s0 s1 s0 s1  => bits8 s1 s1 s0 s1 s0 s0 s0 s0  | bits8 s1 s0 s0 s0 s0 s1 s1 s0  => bits8 s1 s1 s0 s0 s1 s1 s0 s1  | bits8 s1 s0 s0 s0 s0 s1 s1 s1  => bits8 s1 s1 s0 s0 s0 s1 s1 s0  | bits8 s1 s0 s0 s0 s1 s0 s0 s0  => bits8 s1 s0 s1 s0 s1 s1 s1 s1  | bits8 s1 s0 s0 s0 s1 s0 s0 s1  => bits8 s1 s0 s1 s0 s0 s1 s0 s0  | bits8 s1 s0 s0 s0 s1 s0 s1 s0  => bits8 s1 s0 s1 s1 s1 s0 s0 s1  | bits8 s1 s0 s0 s0 s1 s0 s1 s1  => bits8 s1 s0 s1 s1 s0 s0 s1 s0  | bits8 s1 s0 s0 s0 s1 s1 s0 s0  => bits8 s1 s0 s0 s0 s0 s0 s1 s1  | bits8 s1 s0 s0 s0 s1 s1 s0 s1  => bits8 s1 s0 s0 s0 s1 s0 s0 s0  | bits8 s1 s0 s0 s0 s1 s1 s1 s0  => bits8 s1 s0 s0 s1 s0 s1 s0 s1  | bits8 s1 s0 s0 s0 s1 s1 s1 s1  => bits8 s1 s0 s0 s1 s1 s1 s1 s0  | bits8 s1 s0 s0 s1 s0 s0 s0 s0  => bits8 s0 s1 s0 s0 s0 s1 s1 s1  | bits8 s1 s0 s0 s1 s0 s0 s0 s1  => bits8 s0 s1 s0 s0 s1 s1 s0 s0  | bits8 s1 s0 s0 s1 s0 s0 s1 s0  => bits8 s0 s1 s0 s1 s0 s0 s0 s1  | bits8 s1 s0 s0 s1 s0 s0 s1 s1  => bits8 s0 s1 s0 s1 s1 s0 s1 s0  | bits8 s1 s0 s0 s1 s0 s1 s0 s0  => bits8 s0 s1 s1 s0 s1 s0 s1 s1  | bits8 s1 s0 s0 s1 s0 s1 s0 s1  => bits8 s0 s1 s1 s0 s0 s0 s0 s0  | bits8 s1 s0 s0 s1 s0 s1 s1 s0  => bits8 s0 s1 s1 s1 s1 s1 s0 s1  | bits8 s1 s0 s0 s1 s0 s1 s1 s1  => bits8 s0 s1 s1 s1 s0 s1 s1 s0  | bits8 s1 s0 s0 s1 s1 s0 s0 s0  => bits8 s0 s0 s0 s1 s1 s1 s1 s1  | bits8 s1 s0 s0 s1 s1 s0 s0 s1  => bits8 s0 s0 s0 s1 s0 s1 s0 s0  | bits8 s1 s0 s0 s1 s1 s0 s1 s0  => bits8 s0 s0 s0 s0 s1 s0 s0 s1  | bits8 s1 s0 s0 s1 s1 s0 s1 s1  => bits8 s0 s0 s0 s0 s0 s0 s1 s0  | bits8 s1 s0 s0 s1 s1 s1 s0 s0  => bits8 s0 s0 s1 s1 s0 s0 s1 s1  | bits8 s1 s0 s0 s1 s1 s1 s0 s1  => bits8 s0 s0 s1 s1 s1 s0 s0 s0  | bits8 s1 s0 s0 s1 s1 s1 s1 s0  => bits8 s0 s0 s1 s0 s0 s1 s0 s1  | bits8 s1 s0 s0 s1 s1 s1 s1 s1  => bits8 s0 s0 s1 s0 s1 s1 s1 s0  | bits8 s1 s0 s1 s0 s0 s0 s0 s0  => bits8 s1 s0 s0 s0 s1 s1 s0 s0  | bits8 s1 s0 s1 s0 s0 s0 s0 s1  => bits8 s1 s0 s0 s0 s0 s1 s1 s1  | bits8 s1 s0 s1 s0 s0 s0 s1 s0  => bits8 s1 s0 s0 s1 s1 s0 s1 s0  | bits8 s1 s0 s1 s0 s0 s0 s1 s1  => bits8 s1 s0 s0 s1 s0 s0 s0 s1  | bits8 s1 s0 s1 s0 s0 s1 s0 s0  => bits8 s1 s0 s1 s0 s0 s0 s0 s0  | bits8 s1 s0 s1 s0 s0 s1 s0 s1  => bits8 s1 s0 s1 s0 s1 s0 s1 s1  | bits8 s1 s0 s1 s0 s0 s1 s1 s0  => bits8 s1 s0 s1 s1 s0 s1 s1 s0  | bits8 s1 s0 s1 s0 s0 s1 s1 s1  => bits8 s1 s0 s1 s1 s1 s1 s0 s1  | bits8 s1 s0 s1 s0 s1 s0 s0 s0  => bits8 s1 s1 s0 s1 s0 s1 s0 s0  | bits8 s1 s0 s1 s0 s1 s0 s0 s1  => bits8 s1 s1 s0 s1 s1 s1 s1 s1  | bits8 s1 s0 s1 s0 s1 s0 s1 s0  => bits8 s1 s1 s0 s0 s0 s0 s1 s0  | bits8 s1 s0 s1 s0 s1 s0 s1 s1  => bits8 s1 s1 s0 s0 s1 s0 s0 s1  | bits8 s1 s0 s1 s0 s1 s1 s0 s0  => bits8 s1 s1 s1 s1 s1 s0 s0 s0  | bits8 s1 s0 s1 s0 s1 s1 s0 s1  => bits8 s1 s1 s1 s1 s0 s0 s1 s1  | bits8 s1 s0 s1 s0 s1 s1 s1 s0  => bits8 s1 s1 s1 s0 s1 s1 s1 s0  | bits8 s1 s0 s1 s0 s1 s1 s1 s1  => bits8 s1 s1 s1 s0 s0 s1 s0 s1  | bits8 s1 s0 s1 s1 s0 s0 s0 s0  => bits8 s0 s0 s1 s1 s1 s1 s0 s0  | bits8 s1 s0 s1 s1 s0 s0 s0 s1  => bits8 s0 s0 s1 s1 s0 s1 s1 s1  | bits8 s1 s0 s1 s1 s0 s0 s1 s0  => bits8 s0 s0 s1 s0 s1 s0 s1 s0  | bits8 s1 s0 s1 s1 s0 s0 s1 s1  => bits8 s0 s0 s1 s0 s0 s0 s0 s1  | bits8 s1 s0 s1 s1 s0 s1 s0 s0  => bits8 s0 s0 s0 s1 s0 s0 s0 s0  | bits8 s1 s0 s1 s1 s0 s1 s0 s1  => bits8 s0 s0 s0 s1 s1 s0 s1 s1  | bits8 s1 s0 s1 s1 s0 s1 s1 s0  => bits8 s0 s0 s0 s0 s0 s1 s1 s0  | bits8 s1 s0 s1 s1 s0 s1 s1 s1  => bits8 s0 s0 s0 s0 s1 s1 s0 s1  | bits8 s1 s0 s1 s1 s1 s0 s0 s0  => bits8 s0 s1 s1 s0 s0 s1 s0 s0  | bits8 s1 s0 s1 s1 s1 s0 s0 s1  => bits8 s0 s1 s1 s0 s1 s1 s1 s1  | bits8 s1 s0 s1 s1 s1 s0 s1 s0  => bits8 s0 s1 s1 s1 s0 s0 s1 s0  | bits8 s1 s0 s1 s1 s1 s0 s1 s1  => bits8 s0 s1 s1 s1 s1 s0 s0 s1  | bits8 s1 s0 s1 s1 s1 s1 s0 s0  => bits8 s0 s1 s0 s0 s1 s0 s0 s0  | bits8 s1 s0 s1 s1 s1 s1 s0 s1  => bits8 s0 s1 s0 s0 s0 s0 s1 s1  | bits8 s1 s0 s1 s1 s1 s1 s1 s0  => bits8 s0 s1 s0 s1 s1 s1 s1 s0  | bits8 s1 s0 s1 s1 s1 s1 s1 s1  => bits8 s0 s1 s0 s1 s0 s1 s0 s1  | bits8 s1 s1 s0 s0 s0 s0 s0 s0  => bits8 s0 s0 s0 s0 s0 s0 s0 s1  | bits8 s1 s1 s0 s0 s0 s0 s0 s1  => bits8 s0 s0 s0 s0 s1 s0 s1 s0  | bits8 s1 s1 s0 s0 s0 s0 s1 s0  => bits8 s0 s0 s0 s1 s0 s1 s1 s1  | bits8 s1 s1 s0 s0 s0 s0 s1 s1  => bits8 s0 s0 s0 s1 s1 s1 s0 s0  | bits8 s1 s1 s0 s0 s0 s1 s0 s0  => bits8 s0 s0 s1 s0 s1 s1 s0 s1  | bits8 s1 s1 s0 s0 s0 s1 s0 s1  => bits8 s0 s0 s1 s0 s0 s1 s1 s0  | bits8 s1 s1 s0 s0 s0 s1 s1 s0  => bits8 s0 s0 s1 s1 s1 s0 s1 s1  | bits8 s1 s1 s0 s0 s0 s1 s1 s1  => bits8 s0 s0 s1 s1 s0 s0 s0 s0  | bits8 s1 s1 s0 s0 s1 s0 s0 s0  => bits8 s0 s1 s0 s1 s1 s0 s0 s1  | bits8 s1 s1 s0 s0 s1 s0 s0 s1  => bits8 s0 s1 s0 s1 s0 s0 s1 s0  | bits8 s1 s1 s0 s0 s1 s0 s1 s0  => bits8 s0 s1 s0 s0 s1 s1 s1 s1  | bits8 s1 s1 s0 s0 s1 s0 s1 s1  => bits8 s0 s1 s0 s0 s0 s1 s0 s0  | bits8 s1 s1 s0 s0 s1 s1 s0 s0  => bits8 s0 s1 s1 s1 s0 s1 s0 s1  | bits8 s1 s1 s0 s0 s1 s1 s0 s1  => bits8 s0 s1 s1 s1 s1 s1 s1 s0  | bits8 s1 s1 s0 s0 s1 s1 s1 s0  => bits8 s0 s1 s1 s0 s0 s0 s1 s1  | bits8 s1 s1 s0 s0 s1 s1 s1 s1  => bits8 s0 s1 s1 s0 s1 s0 s0 s0  | bits8 s1 s1 s0 s1 s0 s0 s0 s0  => bits8 s1 s0 s1 s1 s0 s0 s0 s1  | bits8 s1 s1 s0 s1 s0 s0 s0 s1  => bits8 s1 s0 s1 s1 s1 s0 s1 s0  | bits8 s1 s1 s0 s1 s0 s0 s1 s0  => bits8 s1 s0 s1 s0 s0 s1 s1 s1  | bits8 s1 s1 s0 s1 s0 s0 s1 s1  => bits8 s1 s0 s1 s0 s1 s1 s0 s0  | bits8 s1 s1 s0 s1 s0 s1 s0 s0  => bits8 s1 s0 s0 s1 s1 s1 s0 s1  | bits8 s1 s1 s0 s1 s0 s1 s0 s1  => bits8 s1 s0 s0 s1 s0 s1 s1 s0  | bits8 s1 s1 s0 s1 s0 s1 s1 s0  => bits8 s1 s0 s0 s0 s1 s0 s1 s1  | bits8 s1 s1 s0 s1 s0 s1 s1 s1  => bits8 s1 s0 s0 s0 s0 s0 s0 s0  | bits8 s1 s1 s0 s1 s1 s0 s0 s0  => bits8 s1 s1 s1 s0 s1 s0 s0 s1  | bits8 s1 s1 s0 s1 s1 s0 s0 s1  => bits8 s1 s1 s1 s0 s0 s0 s1 s0  | bits8 s1 s1 s0 s1 s1 s0 s1 s0  => bits8 s1 s1 s1 s1 s1 s1 s1 s1  | bits8 s1 s1 s0 s1 s1 s0 s1 s1  => bits8 s1 s1 s1 s1 s0 s1 s0 s0  | bits8 s1 s1 s0 s1 s1 s1 s0 s0  => bits8 s1 s1 s0 s0 s0 s1 s0 s1  | bits8 s1 s1 s0 s1 s1 s1 s0 s1  => bits8 s1 s1 s0 s0 s1 s1 s1 s0  | bits8 s1 s1 s0 s1 s1 s1 s1 s0  => bits8 s1 s1 s0 s1 s0 s0 s1 s1  | bits8 s1 s1 s0 s1 s1 s1 s1 s1  => bits8 s1 s1 s0 s1 s1 s0 s0 s0  | bits8 s1 s1 s1 s0 s0 s0 s0 s0  => bits8 s0 s1 s1 s1 s1 s0 s1 s0  | bits8 s1 s1 s1 s0 s0 s0 s0 s1  => bits8 s0 s1 s1 s1 s0 s0 s0 s1  | bits8 s1 s1 s1 s0 s0 s0 s1 s0  => bits8 s0 s1 s1 s0 s1 s1 s0 s0  | bits8 s1 s1 s1 s0 s0 s0 s1 s1  => bits8 s0 s1 s1 s0 s0 s1 s1 s1  | bits8 s1 s1 s1 s0 s0 s1 s0 s0  => bits8 s0 s1 s0 s1 s0 s1 s1 s0  | bits8 s1 s1 s1 s0 s0 s1 s0 s1  => bits8 s0 s1 s0 s1 s1 s1 s0 s1  | bits8 s1 s1 s1 s0 s0 s1 s1 s0  => bits8 s0 s1 s0 s0 s0 s0 s0 s0  | bits8 s1 s1 s1 s0 s0 s1 s1 s1  => bits8 s0 s1 s0 s0 s1 s0 s1 s1  | bits8 s1 s1 s1 s0 s1 s0 s0 s0  => bits8 s0 s0 s1 s0 s0 s0 s1 s0  | bits8 s1 s1 s1 s0 s1 s0 s0 s1  => bits8 s0 s0 s1 s0 s1 s0 s0 s1  | bits8 s1 s1 s1 s0 s1 s0 s1 s0  => bits8 s0 s0 s1 s1 s0 s1 s0 s0  | bits8 s1 s1 s1 s0 s1 s0 s1 s1  => bits8 s0 s0 s1 s1 s1 s1 s1 s1  | bits8 s1 s1 s1 s0 s1 s1 s0 s0  => bits8 s0 s0 s0 s0 s1 s1 s1 s0  | bits8 s1 s1 s1 s0 s1 s1 s0 s1  => bits8 s0 s0 s0 s0 s0 s1 s0 s1  | bits8 s1 s1 s1 s0 s1 s1 s1 s0  => bits8 s0 s0 s0 s1 s1 s0 s0 s0  | bits8 s1 s1 s1 s0 s1 s1 s1 s1  => bits8 s0 s0 s0 s1 s0 s0 s1 s1  | bits8 s1 s1 s1 s1 s0 s0 s0 s0  => bits8 s1 s1 s0 s0 s1 s0 s1 s0  | bits8 s1 s1 s1 s1 s0 s0 s0 s1  => bits8 s1 s1 s0 s0 s0 s0 s0 s1  | bits8 s1 s1 s1 s1 s0 s0 s1 s0  => bits8 s1 s1 s0 s1 s1 s1 s0 s0  | bits8 s1 s1 s1 s1 s0 s0 s1 s1  => bits8 s1 s1 s0 s1 s0 s1 s1 s1  | bits8 s1 s1 s1 s1 s0 s1 s0 s0  => bits8 s1 s1 s1 s0 s0 s1 s1 s0  | bits8 s1 s1 s1 s1 s0 s1 s0 s1  => bits8 s1 s1 s1 s0 s1 s1 s0 s1  | bits8 s1 s1 s1 s1 s0 s1 s1 s0  => bits8 s1 s1 s1 s1 s0 s0 s0 s0  | bits8 s1 s1 s1 s1 s0 s1 s1 s1  => bits8 s1 s1 s1 s1 s1 s0 s1 s1  | bits8 s1 s1 s1 s1 s1 s0 s0 s0  => bits8 s1 s0 s0 s1 s0 s0 s1 s0  | bits8 s1 s1 s1 s1 s1 s0 s0 s1  => bits8 s1 s0 s0 s1 s1 s0 s0 s1  | bits8 s1 s1 s1 s1 s1 s0 s1 s0  => bits8 s1 s0 s0 s0 s0 s1 s0 s0  | bits8 s1 s1 s1 s1 s1 s0 s1 s1  => bits8 s1 s0 s0 s0 s1 s1 s1 s1  | bits8 s1 s1 s1 s1 s1 s1 s0 s0  => bits8 s1 s0 s1 s1 s1 s1 s1 s0  | bits8 s1 s1 s1 s1 s1 s1 s0 s1  => bits8 s1 s0 s1 s1 s0 s1 s0 s1  | bits8 s1 s1 s1 s1 s1 s1 s1 s0  => bits8 s1 s0 s1 s0 s1 s0 s0 s0  | bits8 s1 s1 s1 s1 s1 s1 s1 s1  => bits8 s1 s0 s1 s0 s0 s0 s1 s1  end
| 13 => match a with 
| bits8 s0 s0 s0 s0 s0 s0 s0 s0  => bits8 s0 s0 s0 s0 s0 s0 s0 s0  | bits8 s0 s0 s0 s0 s0 s0 s0 s1  => bits8 s0 s0 s0 s0 s1 s1 s0 s1  | bits8 s0 s0 s0 s0 s0 s0 s1 s0  => bits8 s0 s0 s0 s1 s1 s0 s1 s0  | bits8 s0 s0 s0 s0 s0 s0 s1 s1  => bits8 s0 s0 s0 s1 s0 s1 s1 s1  | bits8 s0 s0 s0 s0 s0 s1 s0 s0  => bits8 s0 s0 s1 s1 s0 s1 s0 s0  | bits8 s0 s0 s0 s0 s0 s1 s0 s1  => bits8 s0 s0 s1 s1 s1 s0 s0 s1  | bits8 s0 s0 s0 s0 s0 s1 s1 s0  => bits8 s0 s0 s1 s0 s1 s1 s1 s0  | bits8 s0 s0 s0 s0 s0 s1 s1 s1  => bits8 s0 s0 s1 s0 s0 s0 s1 s1  | bits8 s0 s0 s0 s0 s1 s0 s0 s0  => bits8 s0 s1 s1 s0 s1 s0 s0 s0  | bits8 s0 s0 s0 s0 s1 s0 s0 s1  => bits8 s0 s1 s1 s0 s0 s1 s0 s1  | bits8 s0 s0 s0 s0 s1 s0 s1 s0  => bits8 s0 s1 s1 s1 s0 s0 s1 s0  | bits8 s0 s0 s0 s0 s1 s0 s1 s1  => bits8 s0 s1 s1 s1 s1 s1 s1 s1  | bits8 s0 s0 s0 s0 s1 s1 s0 s0  => bits8 s0 s1 s0 s1 s1 s1 s0 s0  | bits8 s0 s0 s0 s0 s1 s1 s0 s1  => bits8 s0 s1 s0 s1 s0 s0 s0 s1  | bits8 s0 s0 s0 s0 s1 s1 s1 s0  => bits8 s0 s1 s0 s0 s0 s1 s1 s0  | bits8 s0 s0 s0 s0 s1 s1 s1 s1  => bits8 s0 s1 s0 s0 s1 s0 s1 s1  | bits8 s0 s0 s0 s1 s0 s0 s0 s0  => bits8 s1 s1 s0 s1 s0 s0 s0 s0  | bits8 s0 s0 s0 s1 s0 s0 s0 s1  => bits8 s1 s1 s0 s1 s1 s1 s0 s1  | bits8 s0 s0 s0 s1 s0 s0 s1 s0  => bits8 s1 s1 s0 s0 s1 s0 s1 s0  | bits8 s0 s0 s0 s1 s0 s0 s1 s1  => bits8 s1 s1 s0 s0 s0 s1 s1 s1  | bits8 s0 s0 s0 s1 s0 s1 s0 s0  => bits8 s1 s1 s1 s0 s0 s1 s0 s0  | bits8 s0 s0 s0 s1 s0 s1 s0 s1  => bits8 s1 s1 s1 s0 s1 s0 s0 s1  | bits8 s0 s0 s0 s1 s0 s1 s1 s0  => bits8 s1 s1 s1 s1 s1 s1 s1 s0  | bits8 s0 s0 s0 s1 s0 s1 s1 s1  => bits8 s1 s1 s1 s1 s0 s0 s1 s1  | bits8 s0 s0 s0 s1 s1 s0 s0 s0  => bits8 s1 s0 s1 s1 s1 s0 s0 s0  | bits8 s0 s0 s0 s1 s1 s0 s0 s1  => bits8 s1 s0 s1 s1 s0 s1 s0 s1  | bits8 s0 s0 s0 s1 s1 s0 s1 s0  => bits8 s1 s0 s1 s0 s0 s0 s1 s0  | bits8 s0 s0 s0 s1 s1 s0 s1 s1  => bits8 s1 s0 s1 s0 s1 s1 s1 s1  | bits8 s0 s0 s0 s1 s1 s1 s0 s0  => bits8 s1 s0 s0 s0 s1 s1 s0 s0  | bits8 s0 s0 s0 s1 s1 s1 s0 s1  => bits8 s1 s0 s0 s0 s0 s0 s0 s1  | bits8 s0 s0 s0 s1 s1 s1 s1 s0  => bits8 s1 s0 s0 s1 s0 s1 s1 s0  | bits8 s0 s0 s0 s1 s1 s1 s1 s1  => bits8 s1 s0 s0 s1 s1 s0 s1 s1  | bits8 s0 s0 s1 s0 s0 s0 s0 s0  => bits8 s1 s0 s1 s1 s1 s0 s1 s1  | bits8 s0 s0 s1 s0 s0 s0 s0 s1  => bits8 s1 s0 s1 s1 s0 s1 s1 s0  | bits8 s0 s0 s1 s0 s0 s0 s1 s0  => bits8 s1 s0 s1 s0 s0 s0 s0 s1  | bits8 s0 s0 s1 s0 s0 s0 s1 s1  => bits8 s1 s0 s1 s0 s1 s1 s0 s0  | bits8 s0 s0 s1 s0 s0 s1 s0 s0  => bits8 s1 s0 s0 s0 s1 s1 s1 s1  | bits8 s0 s0 s1 s0 s0 s1 s0 s1  => bits8 s1 s0 s0 s0 s0 s0 s1 s0  | bits8 s0 s0 s1 s0 s0 s1 s1 s0  => bits8 s1 s0 s0 s1 s0 s1 s0 s1  | bits8 s0 s0 s1 s0 s0 s1 s1 s1  => bits8 s1 s0 s0 s1 s1 s0 s0 s0  | bits8 s0 s0 s1 s0 s1 s0 s0 s0  => bits8 s1 s1 s0 s1 s0 s0 s1 s1  | bits8 s0 s0 s1 s0 s1 s0 s0 s1  => bits8 s1 s1 s0 s1 s1 s1 s1 s0  | bits8 s0 s0 s1 s0 s1 s0 s1 s0  => bits8 s1 s1 s0 s0 s1 s0 s0 s1  | bits8 s0 s0 s1 s0 s1 s0 s1 s1  => bits8 s1 s1 s0 s0 s0 s1 s0 s0  | bits8 s0 s0 s1 s0 s1 s1 s0 s0  => bits8 s1 s1 s1 s0 s0 s1 s1 s1  | bits8 s0 s0 s1 s0 s1 s1 s0 s1  => bits8 s1 s1 s1 s0 s1 s0 s1 s0  | bits8 s0 s0 s1 s0 s1 s1 s1 s0  => bits8 s1 s1 s1 s1 s1 s1 s0 s1  | bits8 s0 s0 s1 s0 s1 s1 s1 s1  => bits8 s1 s1 s1 s1 s0 s0 s0 s0  | bits8 s0 s0 s1 s1 s0 s0 s0 s0  => bits8 s0 s1 s1 s0 s1 s0 s1 s1  | bits8 s0 s0 s1 s1 s0 s0 s0 s1  => bits8 s0 s1 s1 s0 s0 s1 s1 s0  | bits8 s0 s0 s1 s1 s0 s0 s1 s0  => bits8 s0 s1 s1 s1 s0 s0 s0 s1  | bits8 s0 s0 s1 s1 s0 s0 s1 s1  => bits8 s0 s1 s1 s1 s1 s1 s0 s0  | bits8 s0 s0 s1 s1 s0 s1 s0 s0  => bits8 s0 s1 s0 s1 s1 s1 s1 s1  | bits8 s0 s0 s1 s1 s0 s1 s0 s1  => bits8 s0 s1 s0 s1 s0 s0 s1 s0  | bits8 s0 s0 s1 s1 s0 s1 s1 s0  => bits8 s0 s1 s0 s0 s0 s1 s0 s1  | bits8 s0 s0 s1 s1 s0 s1 s1 s1  => bits8 s0 s1 s0 s0 s1 s0 s0 s0  | bits8 s0 s0 s1 s1 s1 s0 s0 s0  => bits8 s0 s0 s0 s0 s0 s0 s1 s1  | bits8 s0 s0 s1 s1 s1 s0 s0 s1  => bits8 s0 s0 s0 s0 s1 s1 s1 s0  | bits8 s0 s0 s1 s1 s1 s0 s1 s0  => bits8 s0 s0 s0 s1 s1 s0 s0 s1  | bits8 s0 s0 s1 s1 s1 s0 s1 s1  => bits8 s0 s0 s0 s1 s0 s1 s0 s0  | bits8 s0 s0 s1 s1 s1 s1 s0 s0  => bits8 s0 s0 s1 s1 s0 s1 s1 s1  | bits8 s0 s0 s1 s1 s1 s1 s0 s1  => bits8 s0 s0 s1 s1 s1 s0 s1 s0  | bits8 s0 s0 s1 s1 s1 s1 s1 s0  => bits8 s0 s0 s1 s0 s1 s1 s0 s1  | bits8 s0 s0 s1 s1 s1 s1 s1 s1  => bits8 s0 s0 s1 s0 s0 s0 s0 s0  | bits8 s0 s1 s0 s0 s0 s0 s0 s0  => bits8 s0 s1 s1 s0 s1 s1 s0 s1  | bits8 s0 s1 s0 s0 s0 s0 s0 s1  => bits8 s0 s1 s1 s0 s0 s0 s0 s0  | bits8 s0 s1 s0 s0 s0 s0 s1 s0  => bits8 s0 s1 s1 s1 s0 s1 s1 s1  | bits8 s0 s1 s0 s0 s0 s0 s1 s1  => bits8 s0 s1 s1 s1 s1 s0 s1 s0  | bits8 s0 s1 s0 s0 s0 s1 s0 s0  => bits8 s0 s1 s0 s1 s1 s0 s0 s1  | bits8 s0 s1 s0 s0 s0 s1 s0 s1  => bits8 s0 s1 s0 s1 s0 s1 s0 s0  | bits8 s0 s1 s0 s0 s0 s1 s1 s0  => bits8 s0 s1 s0 s0 s0 s0 s1 s1  | bits8 s0 s1 s0 s0 s0 s1 s1 s1  => bits8 s0 s1 s0 s0 s1 s1 s1 s0  | bits8 s0 s1 s0 s0 s1 s0 s0 s0  => bits8 s0 s0 s0 s0 s0 s1 s0 s1  | bits8 s0 s1 s0 s0 s1 s0 s0 s1  => bits8 s0 s0 s0 s0 s1 s0 s0 s0  | bits8 s0 s1 s0 s0 s1 s0 s1 s0  => bits8 s0 s0 s0 s1 s1 s1 s1 s1  | bits8 s0 s1 s0 s0 s1 s0 s1 s1  => bits8 s0 s0 s0 s1 s0 s0 s1 s0  | bits8 s0 s1 s0 s0 s1 s1 s0 s0  => bits8 s0 s0 s1 s1 s0 s0 s0 s1  | bits8 s0 s1 s0 s0 s1 s1 s0 s1  => bits8 s0 s0 s1 s1 s1 s1 s0 s0  | bits8 s0 s1 s0 s0 s1 s1 s1 s0  => bits8 s0 s0 s1 s0 s1 s0 s1 s1  | bits8 s0 s1 s0 s0 s1 s1 s1 s1  => bits8 s0 s0 s1 s0 s0 s1 s1 s0  | bits8 s0 s1 s0 s1 s0 s0 s0 s0  => bits8 s1 s0 s1 s1 s1 s1 s0 s1  | bits8 s0 s1 s0 s1 s0 s0 s0 s1  => bits8 s1 s0 s1 s1 s0 s0 s0 s0  | bits8 s0 s1 s0 s1 s0 s0 s1 s0  => bits8 s1 s0 s1 s0 s0 s1 s1 s1  | bits8 s0 s1 s0 s1 s0 s0 s1 s1  => bits8 s1 s0 s1 s0 s1 s0 s1 s0  | bits8 s0 s1 s0 s1 s0 s1 s0 s0  => bits8 s1 s0 s0 s0 s1 s0 s0 s1  | bits8 s0 s1 s0 s1 s0 s1 s0 s1  => bits8 s1 s0 s0 s0 s0 s1 s0 s0  | bits8 s0 s1 s0 s1 s0 s1 s1 s0  => bits8 s1 s0 s0 s1 s0 s0 s1 s1  | bits8 s0 s1 s0 s1 s0 s1 s1 s1  => bits8 s1 s0 s0 s1 s1 s1 s1 s0  | bits8 s0 s1 s0 s1 s1 s0 s0 s0  => bits8 s1 s1 s0 s1 s0 s1 s0 s1  | bits8 s0 s1 s0 s1 s1 s0 s0 s1  => bits8 s1 s1 s0 s1 s1 s0 s0 s0  | bits8 s0 s1 s0 s1 s1 s0 s1 s0  => bits8 s1 s1 s0 s0 s1 s1 s1 s1  | bits8 s0 s1 s0 s1 s1 s0 s1 s1  => bits8 s1 s1 s0 s0 s0 s0 s1 s0  | bits8 s0 s1 s0 s1 s1 s1 s0 s0  => bits8 s1 s1 s1 s0 s0 s0 s0 s1  | bits8 s0 s1 s0 s1 s1 s1 s0 s1  => bits8 s1 s1 s1 s0 s1 s1 s0 s0  | bits8 s0 s1 s0 s1 s1 s1 s1 s0  => bits8 s1 s1 s1 s1 s1 s0 s1 s1  | bits8 s0 s1 s0 s1 s1 s1 s1 s1  => bits8 s1 s1 s1 s1 s0 s1 s1 s0  | bits8 s0 s1 s1 s0 s0 s0 s0 s0  => bits8 s1 s1 s0 s1 s0 s1 s1 s0  | bits8 s0 s1 s1 s0 s0 s0 s0 s1  => bits8 s1 s1 s0 s1 s1 s0 s1 s1  | bits8 s0 s1 s1 s0 s0 s0 s1 s0  => bits8 s1 s1 s0 s0 s1 s1 s0 s0  | bits8 s0 s1 s1 s0 s0 s0 s1 s1  => bits8 s1 s1 s0 s0 s0 s0 s0 s1  | bits8 s0 s1 s1 s0 s0 s1 s0 s0  => bits8 s1 s1 s1 s0 s0 s0 s1 s0  | bits8 s0 s1 s1 s0 s0 s1 s0 s1  => bits8 s1 s1 s1 s0 s1 s1 s1 s1  | bits8 s0 s1 s1 s0 s0 s1 s1 s0  => bits8 s1 s1 s1 s1 s1 s0 s0 s0  | bits8 s0 s1 s1 s0 s0 s1 s1 s1  => bits8 s1 s1 s1 s1 s0 s1 s0 s1  | bits8 s0 s1 s1 s0 s1 s0 s0 s0  => bits8 s1 s0 s1 s1 s1 s1 s1 s0  | bits8 s0 s1 s1 s0 s1 s0 s0 s1  => bits8 s1 s0 s1 s1 s0 s0 s1 s1  | bits8 s0 s1 s1 s0 s1 s0 s1 s0  => bits8 s1 s0 s1 s0 s0 s1 s0 s0  | bits8 s0 s1 s1 s0 s1 s0 s1 s1  => bits8 s1 s0 s1 s0 s1 s0 s0 s1  | bits8 s0 s1 s1 s0 s1 s1 s0 s0  => bits8 s1 s0 s0 s0 s1 s0 s1 s0  | bits8 s0 s1 s1 s0 s1 s1 s0 s1  => bits8 s1 s0 s0 s0 s0 s1 s1 s1  | bits8 s0 s1 s1 s0 s1 s1 s1 s0  => bits8 s1 s0 s0 s1 s0 s0 s0 s0  | bits8 s0 s1 s1 s0 s1 s1 s1 s1  => bits8 s1 s0 s0 s1 s1 s1 s0 s1  | bits8 s0 s1 s1 s1 s0 s0 s0 s0  => bits8 s0 s0 s0 s0 s0 s1 s1 s0  | bits8 s0 s1 s1 s1 s0 s0 s0 s1  => bits8 s0 s0 s0 s0 s1 s0 s1 s1  | bits8 s0 s1 s1 s1 s0 s0 s1 s0  => bits8 s0 s0 s0 s1 s1 s1 s0 s0  | bits8 s0 s1 s1 s1 s0 s0 s1 s1  => bits8 s0 s0 s0 s1 s0 s0 s0 s1  | bits8 s0 s1 s1 s1 s0 s1 s0 s0  => bits8 s0 s0 s1 s1 s0 s0 s1 s0  | bits8 s0 s1 s1 s1 s0 s1 s0 s1  => bits8 s0 s0 s1 s1 s1 s1 s1 s1  | bits8 s0 s1 s1 s1 s0 s1 s1 s0  => bits8 s0 s0 s1 s0 s1 s0 s0 s0  | bits8 s0 s1 s1 s1 s0 s1 s1 s1  => bits8 s0 s0 s1 s0 s0 s1 s0 s1  | bits8 s0 s1 s1 s1 s1 s0 s0 s0  => bits8 s0 s1 s1 s0 s1 s1 s1 s0  | bits8 s0 s1 s1 s1 s1 s0 s0 s1  => bits8 s0 s1 s1 s0 s0 s0 s1 s1  | bits8 s0 s1 s1 s1 s1 s0 s1 s0  => bits8 s0 s1 s1 s1 s0 s1 s0 s0  | bits8 s0 s1 s1 s1 s1 s0 s1 s1  => bits8 s0 s1 s1 s1 s1 s0 s0 s1  | bits8 s0 s1 s1 s1 s1 s1 s0 s0  => bits8 s0 s1 s0 s1 s1 s0 s1 s0  | bits8 s0 s1 s1 s1 s1 s1 s0 s1  => bits8 s0 s1 s0 s1 s0 s1 s1 s1  | bits8 s0 s1 s1 s1 s1 s1 s1 s0  => bits8 s0 s1 s0 s0 s0 s0 s0 s0  | bits8 s0 s1 s1 s1 s1 s1 s1 s1  => bits8 s0 s1 s0 s0 s1 s1 s0 s1  | bits8 s1 s0 s0 s0 s0 s0 s0 s0  => bits8 s1 s1 s0 s1 s1 s0 s1 s0  | bits8 s1 s0 s0 s0 s0 s0 s0 s1  => bits8 s1 s1 s0 s1 s0 s1 s1 s1  | bits8 s1 s0 s0 s0 s0 s0 s1 s0  => bits8 s1 s1 s0 s0 s0 s0 s0 s0  | bits8 s1 s0 s0 s0 s0 s0 s1 s1  => bits8 s1 s1 s0 s0 s1 s1 s0 s1  | bits8 s1 s0 s0 s0 s0 s1 s0 s0  => bits8 s1 s1 s1 s0 s1 s1 s1 s0  | bits8 s1 s0 s0 s0 s0 s1 s0 s1  => bits8 s1 s1 s1 s0 s0 s0 s1 s1  | bits8 s1 s0 s0 s0 s0 s1 s1 s0  => bits8 s1 s1 s1 s1 s0 s1 s0 s0  | bits8 s1 s0 s0 s0 s0 s1 s1 s1  => bits8 s1 s1 s1 s1 s1 s0 s0 s1  | bits8 s1 s0 s0 s0 s1 s0 s0 s0  => bits8 s1 s0 s1 s1 s0 s0 s1 s0  | bits8 s1 s0 s0 s0 s1 s0 s0 s1  => bits8 s1 s0 s1 s1 s1 s1 s1 s1  | bits8 s1 s0 s0 s0 s1 s0 s1 s0  => bits8 s1 s0 s1 s0 s1 s0 s0 s0  | bits8 s1 s0 s0 s0 s1 s0 s1 s1  => bits8 s1 s0 s1 s0 s0 s1 s0 s1  | bits8 s1 s0 s0 s0 s1 s1 s0 s0  => bits8 s1 s0 s0 s0 s0 s1 s1 s0  | bits8 s1 s0 s0 s0 s1 s1 s0 s1  => bits8 s1 s0 s0 s0 s1 s0 s1 s1  | bits8 s1 s0 s0 s0 s1 s1 s1 s0  => bits8 s1 s0 s0 s1 s1 s1 s0 s0  | bits8 s1 s0 s0 s0 s1 s1 s1 s1  => bits8 s1 s0 s0 s1 s0 s0 s0 s1  | bits8 s1 s0 s0 s1 s0 s0 s0 s0  => bits8 s0 s0 s0 s0 s1 s0 s1 s0  | bits8 s1 s0 s0 s1 s0 s0 s0 s1  => bits8 s0 s0 s0 s0 s0 s1 s1 s1  | bits8 s1 s0 s0 s1 s0 s0 s1 s0  => bits8 s0 s0 s0 s1 s0 s0 s0 s0  | bits8 s1 s0 s0 s1 s0 s0 s1 s1  => bits8 s0 s0 s0 s1 s1 s1 s0 s1  | bits8 s1 s0 s0 s1 s0 s1 s0 s0  => bits8 s0 s0 s1 s1 s1 s1 s1 s0  | bits8 s1 s0 s0 s1 s0 s1 s0 s1  => bits8 s0 s0 s1 s1 s0 s0 s1 s1  | bits8 s1 s0 s0 s1 s0 s1 s1 s0  => bits8 s0 s0 s1 s0 s0 s1 s0 s0  | bits8 s1 s0 s0 s1 s0 s1 s1 s1  => bits8 s0 s0 s1 s0 s1 s0 s0 s1  | bits8 s1 s0 s0 s1 s1 s0 s0 s0  => bits8 s0 s1 s1 s0 s0 s0 s1 s0  | bits8 s1 s0 s0 s1 s1 s0 s0 s1  => bits8 s0 s1 s1 s0 s1 s1 s1 s1  | bits8 s1 s0 s0 s1 s1 s0 s1 s0  => bits8 s0 s1 s1 s1 s1 s0 s0 s0  | bits8 s1 s0 s0 s1 s1 s0 s1 s1  => bits8 s0 s1 s1 s1 s0 s1 s0 s1  | bits8 s1 s0 s0 s1 s1 s1 s0 s0  => bits8 s0 s1 s0 s1 s0 s1 s1 s0  | bits8 s1 s0 s0 s1 s1 s1 s0 s1  => bits8 s0 s1 s0 s1 s1 s0 s1 s1  | bits8 s1 s0 s0 s1 s1 s1 s1 s0  => bits8 s0 s1 s0 s0 s1 s1 s0 s0  | bits8 s1 s0 s0 s1 s1 s1 s1 s1  => bits8 s0 s1 s0 s0 s0 s0 s0 s1  | bits8 s1 s0 s1 s0 s0 s0 s0 s0  => bits8 s0 s1 s1 s0 s0 s0 s0 s1  | bits8 s1 s0 s1 s0 s0 s0 s0 s1  => bits8 s0 s1 s1 s0 s1 s1 s0 s0  | bits8 s1 s0 s1 s0 s0 s0 s1 s0  => bits8 s0 s1 s1 s1 s1 s0 s1 s1  | bits8 s1 s0 s1 s0 s0 s0 s1 s1  => bits8 s0 s1 s1 s1 s0 s1 s1 s0  | bits8 s1 s0 s1 s0 s0 s1 s0 s0  => bits8 s0 s1 s0 s1 s0 s1 s0 s1  | bits8 s1 s0 s1 s0 s0 s1 s0 s1  => bits8 s0 s1 s0 s1 s1 s0 s0 s0  | bits8 s1 s0 s1 s0 s0 s1 s1 s0  => bits8 s0 s1 s0 s0 s1 s1 s1 s1  | bits8 s1 s0 s1 s0 s0 s1 s1 s1  => bits8 s0 s1 s0 s0 s0 s0 s1 s0  | bits8 s1 s0 s1 s0 s1 s0 s0 s0  => bits8 s0 s0 s0 s0 s1 s0 s0 s1  | bits8 s1 s0 s1 s0 s1 s0 s0 s1  => bits8 s0 s0 s0 s0 s0 s1 s0 s0  | bits8 s1 s0 s1 s0 s1 s0 s1 s0  => bits8 s0 s0 s0 s1 s0 s0 s1 s1  | bits8 s1 s0 s1 s0 s1 s0 s1 s1  => bits8 s0 s0 s0 s1 s1 s1 s1 s0  | bits8 s1 s0 s1 s0 s1 s1 s0 s0  => bits8 s0 s0 s1 s1 s1 s1 s0 s1  | bits8 s1 s0 s1 s0 s1 s1 s0 s1  => bits8 s0 s0 s1 s1 s0 s0 s0 s0  | bits8 s1 s0 s1 s0 s1 s1 s1 s0  => bits8 s0 s0 s1 s0 s0 s1 s1 s1  | bits8 s1 s0 s1 s0 s1 s1 s1 s1  => bits8 s0 s0 s1 s0 s1 s0 s1 s0  | bits8 s1 s0 s1 s1 s0 s0 s0 s0  => bits8 s1 s0 s1 s1 s0 s0 s0 s1  | bits8 s1 s0 s1 s1 s0 s0 s0 s1  => bits8 s1 s0 s1 s1 s1 s1 s0 s0  | bits8 s1 s0 s1 s1 s0 s0 s1 s0  => bits8 s1 s0 s1 s0 s1 s0 s1 s1  | bits8 s1 s0 s1 s1 s0 s0 s1 s1  => bits8 s1 s0 s1 s0 s0 s1 s1 s0  | bits8 s1 s0 s1 s1 s0 s1 s0 s0  => bits8 s1 s0 s0 s0 s0 s1 s0 s1  | bits8 s1 s0 s1 s1 s0 s1 s0 s1  => bits8 s1 s0 s0 s0 s1 s0 s0 s0  | bits8 s1 s0 s1 s1 s0 s1 s1 s0  => bits8 s1 s0 s0 s1 s1 s1 s1 s1  | bits8 s1 s0 s1 s1 s0 s1 s1 s1  => bits8 s1 s0 s0 s1 s0 s0 s1 s0  | bits8 s1 s0 s1 s1 s1 s0 s0 s0  => bits8 s1 s1 s0 s1 s1 s0 s0 s1  | bits8 s1 s0 s1 s1 s1 s0 s0 s1  => bits8 s1 s1 s0 s1 s0 s1 s0 s0  | bits8 s1 s0 s1 s1 s1 s0 s1 s0  => bits8 s1 s1 s0 s0 s0 s0 s1 s1  | bits8 s1 s0 s1 s1 s1 s0 s1 s1  => bits8 s1 s1 s0 s0 s1 s1 s1 s0  | bits8 s1 s0 s1 s1 s1 s1 s0 s0  => bits8 s1 s1 s1 s0 s1 s1 s0 s1  | bits8 s1 s0 s1 s1 s1 s1 s0 s1  => bits8 s1 s1 s1 s0 s0 s0 s0 s0  | bits8 s1 s0 s1 s1 s1 s1 s1 s0  => bits8 s1 s1 s1 s1 s0 s1 s1 s1  | bits8 s1 s0 s1 s1 s1 s1 s1 s1  => bits8 s1 s1 s1 s1 s1 s0 s1 s0  | bits8 s1 s1 s0 s0 s0 s0 s0 s0  => bits8 s1 s0 s1 s1 s0 s1 s1 s1  | bits8 s1 s1 s0 s0 s0 s0 s0 s1  => bits8 s1 s0 s1 s1 s1 s0 s1 s0  | bits8 s1 s1 s0 s0 s0 s0 s1 s0  => bits8 s1 s0 s1 s0 s1 s1 s0 s1  | bits8 s1 s1 s0 s0 s0 s0 s1 s1  => bits8 s1 s0 s1 s0 s0 s0 s0 s0  | bits8 s1 s1 s0 s0 s0 s1 s0 s0  => bits8 s1 s0 s0 s0 s0 s0 s1 s1  | bits8 s1 s1 s0 s0 s0 s1 s0 s1  => bits8 s1 s0 s0 s0 s1 s1 s1 s0  | bits8 s1 s1 s0 s0 s0 s1 s1 s0  => bits8 s1 s0 s0 s1 s1 s0 s0 s1  | bits8 s1 s1 s0 s0 s0 s1 s1 s1  => bits8 s1 s0 s0 s1 s0 s1 s0 s0  | bits8 s1 s1 s0 s0 s1 s0 s0 s0  => bits8 s1 s1 s0 s1 s1 s1 s1 s1  | bits8 s1 s1 s0 s0 s1 s0 s0 s1  => bits8 s1 s1 s0 s1 s0 s0 s1 s0  | bits8 s1 s1 s0 s0 s1 s0 s1 s0  => bits8 s1 s1 s0 s0 s0 s1 s0 s1  | bits8 s1 s1 s0 s0 s1 s0 s1 s1  => bits8 s1 s1 s0 s0 s1 s0 s0 s0  | bits8 s1 s1 s0 s0 s1 s1 s0 s0  => bits8 s1 s1 s1 s0 s1 s0 s1 s1  | bits8 s1 s1 s0 s0 s1 s1 s0 s1  => bits8 s1 s1 s1 s0 s0 s1 s1 s0  | bits8 s1 s1 s0 s0 s1 s1 s1 s0  => bits8 s1 s1 s1 s1 s0 s0 s0 s1  | bits8 s1 s1 s0 s0 s1 s1 s1 s1  => bits8 s1 s1 s1 s1 s1 s1 s0 s0  | bits8 s1 s1 s0 s1 s0 s0 s0 s0  => bits8 s0 s1 s1 s0 s0 s1 s1 s1  | bits8 s1 s1 s0 s1 s0 s0 s0 s1  => bits8 s0 s1 s1 s0 s1 s0 s1 s0  | bits8 s1 s1 s0 s1 s0 s0 s1 s0  => bits8 s0 s1 s1 s1 s1 s1 s0 s1  | bits8 s1 s1 s0 s1 s0 s0 s1 s1  => bits8 s0 s1 s1 s1 s0 s0 s0 s0  | bits8 s1 s1 s0 s1 s0 s1 s0 s0  => bits8 s0 s1 s0 s1 s0 s0 s1 s1  | bits8 s1 s1 s0 s1 s0 s1 s0 s1  => bits8 s0 s1 s0 s1 s1 s1 s1 s0  | bits8 s1 s1 s0 s1 s0 s1 s1 s0  => bits8 s0 s1 s0 s0 s1 s0 s0 s1  | bits8 s1 s1 s0 s1 s0 s1 s1 s1  => bits8 s0 s1 s0 s0 s0 s1 s0 s0  | bits8 s1 s1 s0 s1 s1 s0 s0 s0  => bits8 s0 s0 s0 s0 s1 s1 s1 s1  | bits8 s1 s1 s0 s1 s1 s0 s0 s1  => bits8 s0 s0 s0 s0 s0 s0 s1 s0  | bits8 s1 s1 s0 s1 s1 s0 s1 s0  => bits8 s0 s0 s0 s1 s0 s1 s0 s1  | bits8 s1 s1 s0 s1 s1 s0 s1 s1  => bits8 s0 s0 s0 s1 s1 s0 s0 s0  | bits8 s1 s1 s0 s1 s1 s1 s0 s0  => bits8 s0 s0 s1 s1 s1 s0 s1 s1  | bits8 s1 s1 s0 s1 s1 s1 s0 s1  => bits8 s0 s0 s1 s1 s0 s1 s1 s0  | bits8 s1 s1 s0 s1 s1 s1 s1 s0  => bits8 s0 s0 s1 s0 s0 s0 s0 s1  | bits8 s1 s1 s0 s1 s1 s1 s1 s1  => bits8 s0 s0 s1 s0 s1 s1 s0 s0  | bits8 s1 s1 s1 s0 s0 s0 s0 s0  => bits8 s0 s0 s0 s0 s1 s1 s0 s0  | bits8 s1 s1 s1 s0 s0 s0 s0 s1  => bits8 s0 s0 s0 s0 s0 s0 s0 s1  | bits8 s1 s1 s1 s0 s0 s0 s1 s0  => bits8 s0 s0 s0 s1 s0 s1 s1 s0  | bits8 s1 s1 s1 s0 s0 s0 s1 s1  => bits8 s0 s0 s0 s1 s1 s0 s1 s1  | bits8 s1 s1 s1 s0 s0 s1 s0 s0  => bits8 s0 s0 s1 s1 s1 s0 s0 s0  | bits8 s1 s1 s1 s0 s0 s1 s0 s1  => bits8 s0 s0 s1 s1 s0 s1 s0 s1  | bits8 s1 s1 s1 s0 s0 s1 s1 s0  => bits8 s0 s0 s1 s0 s0 s0 s1 s0  | bits8 s1 s1 s1 s0 s0 s1 s1 s1  => bits8 s0 s0 s1 s0 s1 s1 s1 s1  | bits8 s1 s1 s1 s0 s1 s0 s0 s0  => bits8 s0 s1 s1 s0 s0 s1 s0 s0  | bits8 s1 s1 s1 s0 s1 s0 s0 s1  => bits8 s0 s1 s1 s0 s1 s0 s0 s1  | bits8 s1 s1 s1 s0 s1 s0 s1 s0  => bits8 s0 s1 s1 s1 s1 s1 s1 s0  | bits8 s1 s1 s1 s0 s1 s0 s1 s1  => bits8 s0 s1 s1 s1 s0 s0 s1 s1  | bits8 s1 s1 s1 s0 s1 s1 s0 s0  => bits8 s0 s1 s0 s1 s0 s0 s0 s0  | bits8 s1 s1 s1 s0 s1 s1 s0 s1  => bits8 s0 s1 s0 s1 s1 s1 s0 s1  | bits8 s1 s1 s1 s0 s1 s1 s1 s0  => bits8 s0 s1 s0 s0 s1 s0 s1 s0  | bits8 s1 s1 s1 s0 s1 s1 s1 s1  => bits8 s0 s1 s0 s0 s0 s1 s1 s1  | bits8 s1 s1 s1 s1 s0 s0 s0 s0  => bits8 s1 s1 s0 s1 s1 s1 s0 s0  | bits8 s1 s1 s1 s1 s0 s0 s0 s1  => bits8 s1 s1 s0 s1 s0 s0 s0 s1  | bits8 s1 s1 s1 s1 s0 s0 s1 s0  => bits8 s1 s1 s0 s0 s0 s1 s1 s0  | bits8 s1 s1 s1 s1 s0 s0 s1 s1  => bits8 s1 s1 s0 s0 s1 s0 s1 s1  | bits8 s1 s1 s1 s1 s0 s1 s0 s0  => bits8 s1 s1 s1 s0 s1 s0 s0 s0  | bits8 s1 s1 s1 s1 s0 s1 s0 s1  => bits8 s1 s1 s1 s0 s0 s1 s0 s1  | bits8 s1 s1 s1 s1 s0 s1 s1 s0  => bits8 s1 s1 s1 s1 s0 s0 s1 s0  | bits8 s1 s1 s1 s1 s0 s1 s1 s1  => bits8 s1 s1 s1 s1 s1 s1 s1 s1  | bits8 s1 s1 s1 s1 s1 s0 s0 s0  => bits8 s1 s0 s1 s1 s0 s1 s0 s0  | bits8 s1 s1 s1 s1 s1 s0 s0 s1  => bits8 s1 s0 s1 s1 s1 s0 s0 s1  | bits8 s1 s1 s1 s1 s1 s0 s1 s0  => bits8 s1 s0 s1 s0 s1 s1 s1 s0  | bits8 s1 s1 s1 s1 s1 s0 s1 s1  => bits8 s1 s0 s1 s0 s0 s0 s1 s1  | bits8 s1 s1 s1 s1 s1 s1 s0 s0  => bits8 s1 s0 s0 s0 s0 s0 s0 s0  | bits8 s1 s1 s1 s1 s1 s1 s0 s1  => bits8 s1 s0 s0 s0 s1 s1 s0 s1  | bits8 s1 s1 s1 s1 s1 s1 s1 s0  => bits8 s1 s0 s0 s1 s1 s0 s1 s0  | bits8 s1 s1 s1 s1 s1 s1 s1 s1  => bits8 s1 s0 s0 s1 s0 s1 s1 s1  end
| 14 => match a with 
| bits8 s0 s0 s0 s0 s0 s0 s0 s0  => bits8 s0 s0 s0 s0 s0 s0 s0 s0  | bits8 s0 s0 s0 s0 s0 s0 s0 s1  => bits8 s0 s0 s0 s0 s1 s1 s1 s0  | bits8 s0 s0 s0 s0 s0 s0 s1 s0  => bits8 s0 s0 s0 s1 s1 s1 s0 s0  | bits8 s0 s0 s0 s0 s0 s0 s1 s1  => bits8 s0 s0 s0 s1 s0 s0 s1 s0  | bits8 s0 s0 s0 s0 s0 s1 s0 s0  => bits8 s0 s0 s1 s1 s1 s0 s0 s0  | bits8 s0 s0 s0 s0 s0 s1 s0 s1  => bits8 s0 s0 s1 s1 s0 s1 s1 s0  | bits8 s0 s0 s0 s0 s0 s1 s1 s0  => bits8 s0 s0 s1 s0 s0 s1 s0 s0  | bits8 s0 s0 s0 s0 s0 s1 s1 s1  => bits8 s0 s0 s1 s0 s1 s0 s1 s0  | bits8 s0 s0 s0 s0 s1 s0 s0 s0  => bits8 s0 s1 s1 s1 s0 s0 s0 s0  | bits8 s0 s0 s0 s0 s1 s0 s0 s1  => bits8 s0 s1 s1 s1 s1 s1 s1 s0  | bits8 s0 s0 s0 s0 s1 s0 s1 s0  => bits8 s0 s1 s1 s0 s1 s1 s0 s0  | bits8 s0 s0 s0 s0 s1 s0 s1 s1  => bits8 s0 s1 s1 s0 s0 s0 s1 s0  | bits8 s0 s0 s0 s0 s1 s1 s0 s0  => bits8 s0 s1 s0 s0 s1 s0 s0 s0  | bits8 s0 s0 s0 s0 s1 s1 s0 s1  => bits8 s0 s1 s0 s0 s0 s1 s1 s0  | bits8 s0 s0 s0 s0 s1 s1 s1 s0  => bits8 s0 s1 s0 s1 s0 s1 s0 s0  | bits8 s0 s0 s0 s0 s1 s1 s1 s1  => bits8 s0 s1 s0 s1 s1 s0 s1 s0  | bits8 s0 s0 s0 s1 s0 s0 s0 s0  => bits8 s1 s1 s1 s0 s0 s0 s0 s0  | bits8 s0 s0 s0 s1 s0 s0 s0 s1  => bits8 s1 s1 s1 s0 s1 s1 s1 s0  | bits8 s0 s0 s0 s1 s0 s0 s1 s0  => bits8 s1 s1 s1 s1 s1 s1 s0 s0  | bits8 s0 s0 s0 s1 s0 s0 s1 s1  => bits8 s1 s1 s1 s1 s0 s0 s1 s0  | bits8 s0 s0 s0 s1 s0 s1 s0 s0  => bits8 s1 s1 s0 s1 s1 s0 s0 s0  | bits8 s0 s0 s0 s1 s0 s1 s0 s1  => bits8 s1 s1 s0 s1 s0 s1 s1 s0  | bits8 s0 s0 s0 s1 s0 s1 s1 s0  => bits8 s1 s1 s0 s0 s0 s1 s0 s0  | bits8 s0 s0 s0 s1 s0 s1 s1 s1  => bits8 s1 s1 s0 s0 s1 s0 s1 s0  | bits8 s0 s0 s0 s1 s1 s0 s0 s0  => bits8 s1 s0 s0 s1 s0 s0 s0 s0  | bits8 s0 s0 s0 s1 s1 s0 s0 s1  => bits8 s1 s0 s0 s1 s1 s1 s1 s0  | bits8 s0 s0 s0 s1 s1 s0 s1 s0  => bits8 s1 s0 s0 s0 s1 s1 s0 s0  | bits8 s0 s0 s0 s1 s1 s0 s1 s1  => bits8 s1 s0 s0 s0 s0 s0 s1 s0  | bits8 s0 s0 s0 s1 s1 s1 s0 s0  => bits8 s1 s0 s1 s0 s1 s0 s0 s0  | bits8 s0 s0 s0 s1 s1 s1 s0 s1  => bits8 s1 s0 s1 s0 s0 s1 s1 s0  | bits8 s0 s0 s0 s1 s1 s1 s1 s0  => bits8 s1 s0 s1 s1 s0 s1 s0 s0  | bits8 s0 s0 s0 s1 s1 s1 s1 s1  => bits8 s1 s0 s1 s1 s1 s0 s1 s0  | bits8 s0 s0 s1 s0 s0 s0 s0 s0  => bits8 s1 s1 s0 s1 s1 s0 s1 s1  | bits8 s0 s0 s1 s0 s0 s0 s0 s1  => bits8 s1 s1 s0 s1 s0 s1 s0 s1  | bits8 s0 s0 s1 s0 s0 s0 s1 s0  => bits8 s1 s1 s0 s0 s0 s1 s1 s1  | bits8 s0 s0 s1 s0 s0 s0 s1 s1  => bits8 s1 s1 s0 s0 s1 s0 s0 s1  | bits8 s0 s0 s1 s0 s0 s1 s0 s0  => bits8 s1 s1 s1 s0 s0 s0 s1 s1  | bits8 s0 s0 s1 s0 s0 s1 s0 s1  => bits8 s1 s1 s1 s0 s1 s1 s0 s1  | bits8 s0 s0 s1 s0 s0 s1 s1 s0  => bits8 s1 s1 s1 s1 s1 s1 s1 s1  | bits8 s0 s0 s1 s0 s0 s1 s1 s1  => bits8 s1 s1 s1 s1 s0 s0 s0 s1  | bits8 s0 s0 s1 s0 s1 s0 s0 s0  => bits8 s1 s0 s1 s0 s1 s0 s1 s1  | bits8 s0 s0 s1 s0 s1 s0 s0 s1  => bits8 s1 s0 s1 s0 s0 s1 s0 s1  | bits8 s0 s0 s1 s0 s1 s0 s1 s0  => bits8 s1 s0 s1 s1 s0 s1 s1 s1  | bits8 s0 s0 s1 s0 s1 s0 s1 s1  => bits8 s1 s0 s1 s1 s1 s0 s0 s1  | bits8 s0 s0 s1 s0 s1 s1 s0 s0  => bits8 s1 s0 s0 s1 s0 s0 s1 s1  | bits8 s0 s0 s1 s0 s1 s1 s0 s1  => bits8 s1 s0 s0 s1 s1 s1 s0 s1  | bits8 s0 s0 s1 s0 s1 s1 s1 s0  => bits8 s1 s0 s0 s0 s1 s1 s1 s1  | bits8 s0 s0 s1 s0 s1 s1 s1 s1  => bits8 s1 s0 s0 s0 s0 s0 s0 s1  | bits8 s0 s0 s1 s1 s0 s0 s0 s0  => bits8 s0 s0 s1 s1 s1 s0 s1 s1  | bits8 s0 s0 s1 s1 s0 s0 s0 s1  => bits8 s0 s0 s1 s1 s0 s1 s0 s1  | bits8 s0 s0 s1 s1 s0 s0 s1 s0  => bits8 s0 s0 s1 s0 s0 s1 s1 s1  | bits8 s0 s0 s1 s1 s0 s0 s1 s1  => bits8 s0 s0 s1 s0 s1 s0 s0 s1  | bits8 s0 s0 s1 s1 s0 s1 s0 s0  => bits8 s0 s0 s0 s0 s0 s0 s1 s1  | bits8 s0 s0 s1 s1 s0 s1 s0 s1  => bits8 s0 s0 s0 s0 s1 s1 s0 s1  | bits8 s0 s0 s1 s1 s0 s1 s1 s0  => bits8 s0 s0 s0 s1 s1 s1 s1 s1  | bits8 s0 s0 s1 s1 s0 s1 s1 s1  => bits8 s0 s0 s0 s1 s0 s0 s0 s1  | bits8 s0 s0 s1 s1 s1 s0 s0 s0  => bits8 s0 s1 s0 s0 s1 s0 s1 s1  | bits8 s0 s0 s1 s1 s1 s0 s0 s1  => bits8 s0 s1 s0 s0 s0 s1 s0 s1  | bits8 s0 s0 s1 s1 s1 s0 s1 s0  => bits8 s0 s1 s0 s1 s0 s1 s1 s1  | bits8 s0 s0 s1 s1 s1 s0 s1 s1  => bits8 s0 s1 s0 s1 s1 s0 s0 s1  | bits8 s0 s0 s1 s1 s1 s1 s0 s0  => bits8 s0 s1 s1 s1 s0 s0 s1 s1  | bits8 s0 s0 s1 s1 s1 s1 s0 s1  => bits8 s0 s1 s1 s1 s1 s1 s0 s1  | bits8 s0 s0 s1 s1 s1 s1 s1 s0  => bits8 s0 s1 s1 s0 s1 s1 s1 s1  | bits8 s0 s0 s1 s1 s1 s1 s1 s1  => bits8 s0 s1 s1 s0 s0 s0 s0 s1  | bits8 s0 s1 s0 s0 s0 s0 s0 s0  => bits8 s1 s0 s1 s0 s1 s1 s0 s1  | bits8 s0 s1 s0 s0 s0 s0 s0 s1  => bits8 s1 s0 s1 s0 s0 s0 s1 s1  | bits8 s0 s1 s0 s0 s0 s0 s1 s0  => bits8 s1 s0 s1 s1 s0 s0 s0 s1  | bits8 s0 s1 s0 s0 s0 s0 s1 s1  => bits8 s1 s0 s1 s1 s1 s1 s1 s1  | bits8 s0 s1 s0 s0 s0 s1 s0 s0  => bits8 s1 s0 s0 s1 s0 s1 s0 s1  | bits8 s0 s1 s0 s0 s0 s1 s0 s1  => bits8 s1 s0 s0 s1 s1 s0 s1 s1  | bits8 s0 s1 s0 s0 s0 s1 s1 s0  => bits8 s1 s0 s0 s0 s1 s0 s0 s1  | bits8 s0 s1 s0 s0 s0 s1 s1 s1  => bits8 s1 s0 s0 s0 s0 s1 s1 s1  | bits8 s0 s1 s0 s0 s1 s0 s0 s0  => bits8 s1 s1 s0 s1 s1 s1 s0 s1  | bits8 s0 s1 s0 s0 s1 s0 s0 s1  => bits8 s1 s1 s0 s1 s0 s0 s1 s1  | bits8 s0 s1 s0 s0 s1 s0 s1 s0  => bits8 s1 s1 s0 s0 s0 s0 s0 s1  | bits8 s0 s1 s0 s0 s1 s0 s1 s1  => bits8 s1 s1 s0 s0 s1 s1 s1 s1  | bits8 s0 s1 s0 s0 s1 s1 s0 s0  => bits8 s1 s1 s1 s0 s0 s1 s0 s1  | bits8 s0 s1 s0 s0 s1 s1 s0 s1  => bits8 s1 s1 s1 s0 s1 s0 s1 s1  | bits8 s0 s1 s0 s0 s1 s1 s1 s0  => bits8 s1 s1 s1 s1 s1 s0 s0 s1  | bits8 s0 s1 s0 s0 s1 s1 s1 s1  => bits8 s1 s1 s1 s1 s0 s1 s1 s1  | bits8 s0 s1 s0 s1 s0 s0 s0 s0  => bits8 s0 s1 s0 s0 s1 s1 s0 s1  | bits8 s0 s1 s0 s1 s0 s0 s0 s1  => bits8 s0 s1 s0 s0 s0 s0 s1 s1  | bits8 s0 s1 s0 s1 s0 s0 s1 s0  => bits8 s0 s1 s0 s1 s0 s0 s0 s1  | bits8 s0 s1 s0 s1 s0 s0 s1 s1  => bits8 s0 s1 s0 s1 s1 s1 s1 s1  | bits8 s0 s1 s0 s1 s0 s1 s0 s0  => bits8 s0 s1 s1 s1 s0 s1 s0 s1  | bits8 s0 s1 s0 s1 s0 s1 s0 s1  => bits8 s0 s1 s1 s1 s1 s0 s1 s1  | bits8 s0 s1 s0 s1 s0 s1 s1 s0  => bits8 s0 s1 s1 s0 s1 s0 s0 s1  | bits8 s0 s1 s0 s1 s0 s1 s1 s1  => bits8 s0 s1 s1 s0 s0 s1 s1 s1  | bits8 s0 s1 s0 s1 s1 s0 s0 s0  => bits8 s0 s0 s1 s1 s1 s1 s0 s1  | bits8 s0 s1 s0 s1 s1 s0 s0 s1  => bits8 s0 s0 s1 s1 s0 s0 s1 s1  | bits8 s0 s1 s0 s1 s1 s0 s1 s0  => bits8 s0 s0 s1 s0 s0 s0 s0 s1  | bits8 s0 s1 s0 s1 s1 s0 s1 s1  => bits8 s0 s0 s1 s0 s1 s1 s1 s1  | bits8 s0 s1 s0 s1 s1 s1 s0 s0  => bits8 s0 s0 s0 s0 s0 s1 s0 s1  | bits8 s0 s1 s0 s1 s1 s1 s0 s1  => bits8 s0 s0 s0 s0 s1 s0 s1 s1  | bits8 s0 s1 s0 s1 s1 s1 s1 s0  => bits8 s0 s0 s0 s1 s1 s0 s0 s1  | bits8 s0 s1 s0 s1 s1 s1 s1 s1  => bits8 s0 s0 s0 s1 s0 s1 s1 s1  | bits8 s0 s1 s1 s0 s0 s0 s0 s0  => bits8 s0 s1 s1 s1 s0 s1 s1 s0  | bits8 s0 s1 s1 s0 s0 s0 s0 s1  => bits8 s0 s1 s1 s1 s1 s0 s0 s0  | bits8 s0 s1 s1 s0 s0 s0 s1 s0  => bits8 s0 s1 s1 s0 s1 s0 s1 s0  | bits8 s0 s1 s1 s0 s0 s0 s1 s1  => bits8 s0 s1 s1 s0 s0 s1 s0 s0  | bits8 s0 s1 s1 s0 s0 s1 s0 s0  => bits8 s0 s1 s0 s0 s1 s1 s1 s0  | bits8 s0 s1 s1 s0 s0 s1 s0 s1  => bits8 s0 s1 s0 s0 s0 s0 s0 s0  | bits8 s0 s1 s1 s0 s0 s1 s1 s0  => bits8 s0 s1 s0 s1 s0 s0 s1 s0  | bits8 s0 s1 s1 s0 s0 s1 s1 s1  => bits8 s0 s1 s0 s1 s1 s1 s0 s0  | bits8 s0 s1 s1 s0 s1 s0 s0 s0  => bits8 s0 s0 s0 s0 s0 s1 s1 s0  | bits8 s0 s1 s1 s0 s1 s0 s0 s1  => bits8 s0 s0 s0 s0 s1 s0 s0 s0  | bits8 s0 s1 s1 s0 s1 s0 s1 s0  => bits8 s0 s0 s0 s1 s1 s0 s1 s0  | bits8 s0 s1 s1 s0 s1 s0 s1 s1  => bits8 s0 s0 s0 s1 s0 s1 s0 s0  | bits8 s0 s1 s1 s0 s1 s1 s0 s0  => bits8 s0 s0 s1 s1 s1 s1 s1 s0  | bits8 s0 s1 s1 s0 s1 s1 s0 s1  => bits8 s0 s0 s1 s1 s0 s0 s0 s0  | bits8 s0 s1 s1 s0 s1 s1 s1 s0  => bits8 s0 s0 s1 s0 s0 s0 s1 s0  | bits8 s0 s1 s1 s0 s1 s1 s1 s1  => bits8 s0 s0 s1 s0 s1 s1 s0 s0  | bits8 s0 s1 s1 s1 s0 s0 s0 s0  => bits8 s1 s0 s0 s1 s0 s1 s1 s0  | bits8 s0 s1 s1 s1 s0 s0 s0 s1  => bits8 s1 s0 s0 s1 s1 s0 s0 s0  | bits8 s0 s1 s1 s1 s0 s0 s1 s0  => bits8 s1 s0 s0 s0 s1 s0 s1 s0  | bits8 s0 s1 s1 s1 s0 s0 s1 s1  => bits8 s1 s0 s0 s0 s0 s1 s0 s0  | bits8 s0 s1 s1 s1 s0 s1 s0 s0  => bits8 s1 s0 s1 s0 s1 s1 s1 s0  | bits8 s0 s1 s1 s1 s0 s1 s0 s1  => bits8 s1 s0 s1 s0 s0 s0 s0 s0  | bits8 s0 s1 s1 s1 s0 s1 s1 s0  => bits8 s1 s0 s1 s1 s0 s0 s1 s0  | bits8 s0 s1 s1 s1 s0 s1 s1 s1  => bits8 s1 s0 s1 s1 s1 s1 s0 s0  | bits8 s0 s1 s1 s1 s1 s0 s0 s0  => bits8 s1 s1 s1 s0 s0 s1 s1 s0  | bits8 s0 s1 s1 s1 s1 s0 s0 s1  => bits8 s1 s1 s1 s0 s1 s0 s0 s0  | bits8 s0 s1 s1 s1 s1 s0 s1 s0  => bits8 s1 s1 s1 s1 s1 s0 s1 s0  | bits8 s0 s1 s1 s1 s1 s0 s1 s1  => bits8 s1 s1 s1 s1 s0 s1 s0 s0  | bits8 s0 s1 s1 s1 s1 s1 s0 s0  => bits8 s1 s1 s0 s1 s1 s1 s1 s0  | bits8 s0 s1 s1 s1 s1 s1 s0 s1  => bits8 s1 s1 s0 s1 s0 s0 s0 s0  | bits8 s0 s1 s1 s1 s1 s1 s1 s0  => bits8 s1 s1 s0 s0 s0 s0 s1 s0  | bits8 s0 s1 s1 s1 s1 s1 s1 s1  => bits8 s1 s1 s0 s0 s1 s1 s0 s0  | bits8 s1 s0 s0 s0 s0 s0 s0 s0  => bits8 s0 s1 s0 s0 s0 s0 s0 s1  | bits8 s1 s0 s0 s0 s0 s0 s0 s1  => bits8 s0 s1 s0 s0 s1 s1 s1 s1  | bits8 s1 s0 s0 s0 s0 s0 s1 s0  => bits8 s0 s1 s0 s1 s1 s1 s0 s1  | bits8 s1 s0 s0 s0 s0 s0 s1 s1  => bits8 s0 s1 s0 s1 s0 s0 s1 s1  | bits8 s1 s0 s0 s0 s0 s1 s0 s0  => bits8 s0 s1 s1 s1 s1 s0 s0 s1  | bits8 s1 s0 s0 s0 s0 s1 s0 s1  => bits8 s0 s1 s1 s1 s0 s1 s1 s1  | bits8 s1 s0 s0 s0 s0 s1 s1 s0  => bits8 s0 s1 s1 s0 s0 s1 s0 s1  | bits8 s1 s0 s0 s0 s0 s1 s1 s1  => bits8 s0 s1 s1 s0 s1 s0 s1 s1  | bits8 s1 s0 s0 s0 s1 s0 s0 s0  => bits8 s0 s0 s1 s1 s0 s0 s0 s1  | bits8 s1 s0 s0 s0 s1 s0 s0 s1  => bits8 s0 s0 s1 s1 s1 s1 s1 s1  | bits8 s1 s0 s0 s0 s1 s0 s1 s0  => bits8 s0 s0 s1 s0 s1 s1 s0 s1  | bits8 s1 s0 s0 s0 s1 s0 s1 s1  => bits8 s0 s0 s1 s0 s0 s0 s1 s1  | bits8 s1 s0 s0 s0 s1 s1 s0 s0  => bits8 s0 s0 s0 s0 s1 s0 s0 s1  | bits8 s1 s0 s0 s0 s1 s1 s0 s1  => bits8 s0 s0 s0 s0 s0 s1 s1 s1  | bits8 s1 s0 s0 s0 s1 s1 s1 s0  => bits8 s0 s0 s0 s1 s0 s1 s0 s1  | bits8 s1 s0 s0 s0 s1 s1 s1 s1  => bits8 s0 s0 s0 s1 s1 s0 s1 s1  | bits8 s1 s0 s0 s1 s0 s0 s0 s0  => bits8 s1 s0 s1 s0 s0 s0 s0 s1  | bits8 s1 s0 s0 s1 s0 s0 s0 s1  => bits8 s1 s0 s1 s0 s1 s1 s1 s1  | bits8 s1 s0 s0 s1 s0 s0 s1 s0  => bits8 s1 s0 s1 s1 s1 s1 s0 s1  | bits8 s1 s0 s0 s1 s0 s0 s1 s1  => bits8 s1 s0 s1 s1 s0 s0 s1 s1  | bits8 s1 s0 s0 s1 s0 s1 s0 s0  => bits8 s1 s0 s0 s1 s1 s0 s0 s1  | bits8 s1 s0 s0 s1 s0 s1 s0 s1  => bits8 s1 s0 s0 s1 s0 s1 s1 s1  | bits8 s1 s0 s0 s1 s0 s1 s1 s0  => bits8 s1 s0 s0 s0 s0 s1 s0 s1  | bits8 s1 s0 s0 s1 s0 s1 s1 s1  => bits8 s1 s0 s0 s0 s1 s0 s1 s1  | bits8 s1 s0 s0 s1 s1 s0 s0 s0  => bits8 s1 s1 s0 s1 s0 s0 s0 s1  | bits8 s1 s0 s0 s1 s1 s0 s0 s1  => bits8 s1 s1 s0 s1 s1 s1 s1 s1  | bits8 s1 s0 s0 s1 s1 s0 s1 s0  => bits8 s1 s1 s0 s0 s1 s1 s0 s1  | bits8 s1 s0 s0 s1 s1 s0 s1 s1  => bits8 s1 s1 s0 s0 s0 s0 s1 s1  | bits8 s1 s0 s0 s1 s1 s1 s0 s0  => bits8 s1 s1 s1 s0 s1 s0 s0 s1  | bits8 s1 s0 s0 s1 s1 s1 s0 s1  => bits8 s1 s1 s1 s0 s0 s1 s1 s1  | bits8 s1 s0 s0 s1 s1 s1 s1 s0  => bits8 s1 s1 s1 s1 s0 s1 s0 s1  | bits8 s1 s0 s0 s1 s1 s1 s1 s1  => bits8 s1 s1 s1 s1 s1 s0 s1 s1  | bits8 s1 s0 s1 s0 s0 s0 s0 s0  => bits8 s1 s0 s0 s1 s1 s0 s1 s0  | bits8 s1 s0 s1 s0 s0 s0 s0 s1  => bits8 s1 s0 s0 s1 s0 s1 s0 s0  | bits8 s1 s0 s1 s0 s0 s0 s1 s0  => bits8 s1 s0 s0 s0 s0 s1 s1 s0  | bits8 s1 s0 s1 s0 s0 s0 s1 s1  => bits8 s1 s0 s0 s0 s1 s0 s0 s0  | bits8 s1 s0 s1 s0 s0 s1 s0 s0  => bits8 s1 s0 s1 s0 s0 s0 s1 s0  | bits8 s1 s0 s1 s0 s0 s1 s0 s1  => bits8 s1 s0 s1 s0 s1 s1 s0 s0  | bits8 s1 s0 s1 s0 s0 s1 s1 s0  => bits8 s1 s0 s1 s1 s1 s1 s1 s0  | bits8 s1 s0 s1 s0 s0 s1 s1 s1  => bits8 s1 s0 s1 s1 s0 s0 s0 s0  | bits8 s1 s0 s1 s0 s1 s0 s0 s0  => bits8 s1 s1 s1 s0 s1 s0 s1 s0  | bits8 s1 s0 s1 s0 s1 s0 s0 s1  => bits8 s1 s1 s1 s0 s0 s1 s0 s0  | bits8 s1 s0 s1 s0 s1 s0 s1 s0  => bits8 s1 s1 s1 s1 s0 s1 s1 s0  | bits8 s1 s0 s1 s0 s1 s0 s1 s1  => bits8 s1 s1 s1 s1 s1 s0 s0 s0  | bits8 s1 s0 s1 s0 s1 s1 s0 s0  => bits8 s1 s1 s0 s1 s0 s0 s1 s0  | bits8 s1 s0 s1 s0 s1 s1 s0 s1  => bits8 s1 s1 s0 s1 s1 s1 s0 s0  | bits8 s1 s0 s1 s0 s1 s1 s1 s0  => bits8 s1 s1 s0 s0 s1 s1 s1 s0  | bits8 s1 s0 s1 s0 s1 s1 s1 s1  => bits8 s1 s1 s0 s0 s0 s0 s0 s0  | bits8 s1 s0 s1 s1 s0 s0 s0 s0  => bits8 s0 s1 s1 s1 s1 s0 s1 s0  | bits8 s1 s0 s1 s1 s0 s0 s0 s1  => bits8 s0 s1 s1 s1 s0 s1 s0 s0  | bits8 s1 s0 s1 s1 s0 s0 s1 s0  => bits8 s0 s1 s1 s0 s0 s1 s1 s0  | bits8 s1 s0 s1 s1 s0 s0 s1 s1  => bits8 s0 s1 s1 s0 s1 s0 s0 s0  | bits8 s1 s0 s1 s1 s0 s1 s0 s0  => bits8 s0 s1 s0 s0 s0 s0 s1 s0  | bits8 s1 s0 s1 s1 s0 s1 s0 s1  => bits8 s0 s1 s0 s0 s1 s1 s0 s0  | bits8 s1 s0 s1 s1 s0 s1 s1 s0  => bits8 s0 s1 s0 s1 s1 s1 s1 s0  | bits8 s1 s0 s1 s1 s0 s1 s1 s1  => bits8 s0 s1 s0 s1 s0 s0 s0 s0  | bits8 s1 s0 s1 s1 s1 s0 s0 s0  => bits8 s0 s0 s0 s0 s1 s0 s1 s0  | bits8 s1 s0 s1 s1 s1 s0 s0 s1  => bits8 s0 s0 s0 s0 s0 s1 s0 s0  | bits8 s1 s0 s1 s1 s1 s0 s1 s0  => bits8 s0 s0 s0 s1 s0 s1 s1 s0  | bits8 s1 s0 s1 s1 s1 s0 s1 s1  => bits8 s0 s0 s0 s1 s1 s0 s0 s0  | bits8 s1 s0 s1 s1 s1 s1 s0 s0  => bits8 s0 s0 s1 s1 s0 s0 s1 s0  | bits8 s1 s0 s1 s1 s1 s1 s0 s1  => bits8 s0 s0 s1 s1 s1 s1 s0 s0  | bits8 s1 s0 s1 s1 s1 s1 s1 s0  => bits8 s0 s0 s1 s0 s1 s1 s1 s0  | bits8 s1 s0 s1 s1 s1 s1 s1 s1  => bits8 s0 s0 s1 s0 s0 s0 s0 s0  | bits8 s1 s1 s0 s0 s0 s0 s0 s0  => bits8 s1 s1 s1 s0 s1 s1 s0 s0  | bits8 s1 s1 s0 s0 s0 s0 s0 s1  => bits8 s1 s1 s1 s0 s0 s0 s1 s0  | bits8 s1 s1 s0 s0 s0 s0 s1 s0  => bits8 s1 s1 s1 s1 s0 s0 s0 s0  | bits8 s1 s1 s0 s0 s0 s0 s1 s1  => bits8 s1 s1 s1 s1 s1 s1 s1 s0  | bits8 s1 s1 s0 s0 s0 s1 s0 s0  => bits8 s1 s1 s0 s1 s0 s1 s0 s0  | bits8 s1 s1 s0 s0 s0 s1 s0 s1  => bits8 s1 s1 s0 s1 s1 s0 s1 s0  | bits8 s1 s1 s0 s0 s0 s1 s1 s0  => bits8 s1 s1 s0 s0 s1 s0 s0 s0  | bits8 s1 s1 s0 s0 s0 s1 s1 s1  => bits8 s1 s1 s0 s0 s0 s1 s1 s0  | bits8 s1 s1 s0 s0 s1 s0 s0 s0  => bits8 s1 s0 s0 s1 s1 s1 s0 s0  | bits8 s1 s1 s0 s0 s1 s0 s0 s1  => bits8 s1 s0 s0 s1 s0 s0 s1 s0  | bits8 s1 s1 s0 s0 s1 s0 s1 s0  => bits8 s1 s0 s0 s0 s0 s0 s0 s0  | bits8 s1 s1 s0 s0 s1 s0 s1 s1  => bits8 s1 s0 s0 s0 s1 s1 s1 s0  | bits8 s1 s1 s0 s0 s1 s1 s0 s0  => bits8 s1 s0 s1 s0 s0 s1 s0 s0  | bits8 s1 s1 s0 s0 s1 s1 s0 s1  => bits8 s1 s0 s1 s0 s1 s0 s1 s0  | bits8 s1 s1 s0 s0 s1 s1 s1 s0  => bits8 s1 s0 s1 s1 s1 s0 s0 s0  | bits8 s1 s1 s0 s0 s1 s1 s1 s1  => bits8 s1 s0 s1 s1 s0 s1 s1 s0  | bits8 s1 s1 s0 s1 s0 s0 s0 s0  => bits8 s0 s0 s0 s0 s1 s1 s0 s0  | bits8 s1 s1 s0 s1 s0 s0 s0 s1  => bits8 s0 s0 s0 s0 s0 s0 s1 s0  | bits8 s1 s1 s0 s1 s0 s0 s1 s0  => bits8 s0 s0 s0 s1 s0 s0 s0 s0  | bits8 s1 s1 s0 s1 s0 s0 s1 s1  => bits8 s0 s0 s0 s1 s1 s1 s1 s0  | bits8 s1 s1 s0 s1 s0 s1 s0 s0  => bits8 s0 s0 s1 s1 s0 s1 s0 s0  | bits8 s1 s1 s0 s1 s0 s1 s0 s1  => bits8 s0 s0 s1 s1 s1 s0 s1 s0  | bits8 s1 s1 s0 s1 s0 s1 s1 s0  => bits8 s0 s0 s1 s0 s1 s0 s0 s0  | bits8 s1 s1 s0 s1 s0 s1 s1 s1  => bits8 s0 s0 s1 s0 s0 s1 s1 s0  | bits8 s1 s1 s0 s1 s1 s0 s0 s0  => bits8 s0 s1 s1 s1 s1 s1 s0 s0  | bits8 s1 s1 s0 s1 s1 s0 s0 s1  => bits8 s0 s1 s1 s1 s0 s0 s1 s0  | bits8 s1 s1 s0 s1 s1 s0 s1 s0  => bits8 s0 s1 s1 s0 s0 s0 s0 s0  | bits8 s1 s1 s0 s1 s1 s0 s1 s1  => bits8 s0 s1 s1 s0 s1 s1 s1 s0  | bits8 s1 s1 s0 s1 s1 s1 s0 s0  => bits8 s0 s1 s0 s0 s0 s1 s0 s0  | bits8 s1 s1 s0 s1 s1 s1 s0 s1  => bits8 s0 s1 s0 s0 s1 s0 s1 s0  | bits8 s1 s1 s0 s1 s1 s1 s1 s0  => bits8 s0 s1 s0 s1 s1 s0 s0 s0  | bits8 s1 s1 s0 s1 s1 s1 s1 s1  => bits8 s0 s1 s0 s1 s0 s1 s1 s0  | bits8 s1 s1 s1 s0 s0 s0 s0 s0  => bits8 s0 s0 s1 s1 s0 s1 s1 s1  | bits8 s1 s1 s1 s0 s0 s0 s0 s1  => bits8 s0 s0 s1 s1 s1 s0 s0 s1  | bits8 s1 s1 s1 s0 s0 s0 s1 s0  => bits8 s0 s0 s1 s0 s1 s0 s1 s1  | bits8 s1 s1 s1 s0 s0 s0 s1 s1  => bits8 s0 s0 s1 s0 s0 s1 s0 s1  | bits8 s1 s1 s1 s0 s0 s1 s0 s0  => bits8 s0 s0 s0 s0 s1 s1 s1 s1  | bits8 s1 s1 s1 s0 s0 s1 s0 s1  => bits8 s0 s0 s0 s0 s0 s0 s0 s1  | bits8 s1 s1 s1 s0 s0 s1 s1 s0  => bits8 s0 s0 s0 s1 s0 s0 s1 s1  | bits8 s1 s1 s1 s0 s0 s1 s1 s1  => bits8 s0 s0 s0 s1 s1 s1 s0 s1  | bits8 s1 s1 s1 s0 s1 s0 s0 s0  => bits8 s0 s1 s0 s0 s0 s1 s1 s1  | bits8 s1 s1 s1 s0 s1 s0 s0 s1  => bits8 s0 s1 s0 s0 s1 s0 s0 s1  | bits8 s1 s1 s1 s0 s1 s0 s1 s0  => bits8 s0 s1 s0 s1 s1 s0 s1 s1  | bits8 s1 s1 s1 s0 s1 s0 s1 s1  => bits8 s0 s1 s0 s1 s0 s1 s0 s1  | bits8 s1 s1 s1 s0 s1 s1 s0 s0  => bits8 s0 s1 s1 s1 s1 s1 s1 s1  | bits8 s1 s1 s1 s0 s1 s1 s0 s1  => bits8 s0 s1 s1 s1 s0 s0 s0 s1  | bits8 s1 s1 s1 s0 s1 s1 s1 s0  => bits8 s0 s1 s1 s0 s0 s0 s1 s1  | bits8 s1 s1 s1 s0 s1 s1 s1 s1  => bits8 s0 s1 s1 s0 s1 s1 s0 s1  | bits8 s1 s1 s1 s1 s0 s0 s0 s0  => bits8 s1 s1 s0 s1 s0 s1 s1 s1  | bits8 s1 s1 s1 s1 s0 s0 s0 s1  => bits8 s1 s1 s0 s1 s1 s0 s0 s1  | bits8 s1 s1 s1 s1 s0 s0 s1 s0  => bits8 s1 s1 s0 s0 s1 s0 s1 s1  | bits8 s1 s1 s1 s1 s0 s0 s1 s1  => bits8 s1 s1 s0 s0 s0 s1 s0 s1  | bits8 s1 s1 s1 s1 s0 s1 s0 s0  => bits8 s1 s1 s1 s0 s1 s1 s1 s1  | bits8 s1 s1 s1 s1 s0 s1 s0 s1  => bits8 s1 s1 s1 s0 s0 s0 s0 s1  | bits8 s1 s1 s1 s1 s0 s1 s1 s0  => bits8 s1 s1 s1 s1 s0 s0 s1 s1  | bits8 s1 s1 s1 s1 s0 s1 s1 s1  => bits8 s1 s1 s1 s1 s1 s1 s0 s1  | bits8 s1 s1 s1 s1 s1 s0 s0 s0  => bits8 s1 s0 s1 s0 s0 s1 s1 s1  | bits8 s1 s1 s1 s1 s1 s0 s0 s1  => bits8 s1 s0 s1 s0 s1 s0 s0 s1  | bits8 s1 s1 s1 s1 s1 s0 s1 s0  => bits8 s1 s0 s1 s1 s1 s0 s1 s1  | bits8 s1 s1 s1 s1 s1 s0 s1 s1  => bits8 s1 s0 s1 s1 s0 s1 s0 s1  | bits8 s1 s1 s1 s1 s1 s1 s0 s0  => bits8 s1 s0 s0 s1 s1 s1 s1 s1  | bits8 s1 s1 s1 s1 s1 s1 s0 s1  => bits8 s1 s0 s0 s1 s0 s0 s0 s1  | bits8 s1 s1 s1 s1 s1 s1 s1 s0  => bits8 s1 s0 s0 s0 s0 s0 s1 s1  | bits8 s1 s1 s1 s1 s1 s1 s1 s1  => bits8 s1 s0 s0 s0 s1 s1 s0 s1  end
| _ => bits8 s0 s0 s0 s0 s0 s0 s0 s0
  end.

Notation "A GF* B" := (GF_mul_table A B) (at level 75, right associativity).


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
(*

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

(*TODO: mix_columns, inv_mix_columns, mc_inv_mc*)

Definition mix_state_column (w: word) : word :=
  match w with
  | bytes4 s0_n s1_n s2_n s3_n=>
  bytes4 ((s0_n GF* 2) X*OR (s1_n GF* 3) X*OR s2_n X*OR s3_n)
   (s0_n X*OR (s1_n GF* 2) X*OR (s2_n GF* 3) X*OR s3_n)
   (s0_n X*OR s1_n X*OR (s2_n GF* 2) X*OR (s3_n GF* 3))
   ((s0_n GF* 3) X*OR s1_n X*OR s2_n X*OR (s3_n GF* 2))
end.

Definition mix_columns (s: state) : state :=
  match s with
  | bytes16 r0c0 r0c1 r0c2 r0c3
            r1c0 r1c1 r1c2 r1c3
            r2c0 r2c1 r2c2 r2c3
            r3c0 r3c1 r3c2 r3c3 => 
    match (mix_state_column (bytes4 r0c0 r1c0 r2c0 r3c0)) with 
          | ( bytes4 t00 t10 t20 t30) =>
        match (mix_state_column (bytes4 r0c1 r1c1 r2c1 r3c1)) with 
          | (bytes4 t01 t11 t21 t31) => 
              match (mix_state_column (bytes4 r0c2 r1c2 r2c2 r3c2)) with 
                | (bytes4 t02 t12 t22 t32) => 
                  match (mix_state_column (bytes4 r0c3 r1c3 r2c3 r3c3)) with 
                    | (bytes4 t03 t13 t23 t33) => 
                      bytes16 t00 t01 t02 t03
                              t10 t11 t12 t13
                              t20 t21 t22 t23
                              t30 t31 t32 t33
end
end
end
end
end.

 Example test_mix_columns1: 
(mix_columns (bytes16 
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s1))) = 
(bytes16 
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s1)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s1)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s1 s1)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s1 s0)).
Proof.
simpl. reflexivity.
Qed.
 
Definition inv_mix_state_column (w: word) : word :=
match w with
  | bytes4 s0_n s1_n s2_n s3_n=>
  bytes4 ((s0_n GF* 14) X*OR (s1_n GF* 11) X*OR (s2_n GF* 13) X*OR (s3_n GF* 9))
   ((s0_n GF* 9) X*OR (s1_n GF* 14) X*OR (s2_n GF* 11) X*OR (s3_n GF* 13))
   ((s0_n GF* 13) X*OR (s1_n GF* 9) X*OR (s2_n GF* 14) X*OR (s3_n GF* 11))
   ((s0_n GF* 11) X*OR (s1_n GF* 13) X*OR (s2_n GF* 9) X*OR (s3_n GF* 14))
end.

Definition inv_mix_columns (s: state) : state :=
  match s with
  | bytes16 r0c0 r0c1 r0c2 r0c3
            r1c0 r1c1 r1c2 r1c3
            r2c0 r2c1 r2c2 r2c3
            r3c0 r3c1 r3c2 r3c3 => 
    match (inv_mix_state_column (bytes4 r0c0 r1c0 r2c0 r3c0)) with 
          | (bytes4 t00 t10 t20 t30) =>
        match (inv_mix_state_column (bytes4 r0c1 r1c1 r2c1 r3c1)) with 
          | (bytes4 t01 t11 t21 t31) => 
              match (inv_mix_state_column (bytes4 r0c2 r1c2 r2c2 r3c2)) with 
                | (bytes4 t02 t12 t22 t32) => 
                  match (inv_mix_state_column (bytes4 r0c3 r1c3 r2c3 r3c3)) with 
                    | (bytes4 t03 t13 t23 t33) => 
                      bytes16 t00 t01 t02 t03
                              t10 t11 t12 t13
                              t20 t21 t22 t23
                              t30 t31 t32 t33
end
end
end
end
end.

Example test_inv_mix_columns1: 
(inv_mix_state_column  (bytes4
  (bits8 s0 s0 s0 s0 s0 s0 s0 s1)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s1)
  (bits8 s0 s0 s0 s0 s0 s0 s1 s1)
  (bits8 s0 s0 s0 s0 s0 s0 s1 s0))) = 
(bytes4 (bits8 s0 s0 s0 s0 s0 s0 s0 s0)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s1)).
Proof.
unfold inv_mix_state_column. reflexivity.
Qed.


 Example test_inv_mix_columns2: 
(inv_mix_columns (bytes16 
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s1)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s1)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s1 s1)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s1 s0))) = 
(bytes16 
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0)
  (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s0) (bits8 s0 s0 s0 s0 s0 s0 s0 s1)).
Proof.
simpl. reflexivity.
Qed.



Theorem mc_inv_mc_col: forall w: word,
    inv_mix_state_column (mix_state_column w) = w.
Proof.  
  intros. unfold inv_mix_columns. unfold mix_state_column. unfold mix_state_column. unfold inv_mix_state_column. destruct w. destruct b0. destruct b1. destruct b2. destruct b3.
destruct b0. destruct b1. destruct b2. destruct b3. destruct b4. destruct b5. destruct b6. destruct b7. destruct b8. destruct b9. destruct b10. destruct b11. destruct b12. destruct b13. destruct b14. destruct b15. destruct b16. 
 destruct b17. destruct b18. destruct b19. destruct b20. destruct b21. destruct b22. destruct b23. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. 
  unfold GF_mul_table. unfold xor_bytes. unfold xor_bits. reflexivity. 
  unfold GF_mul_table. unfold xor_bytes. unfold xor_bits. reflexivity. unfold GF_mul_table. unfold xor_bytes. unfold xor_bits. destruct b31. reflexivity. reflexivity. unfold GF_mul_table. unfold xor_bytes. unfold xor_bits. destruct b30. destruct b31. reflexivity. reflexivity. 
  destruct b31. reflexivity. reflexivity.
  destruct b29. destruct b30. destruct b31.  unfold xor_bytes. unfold xor_bits. unfold GF_mul_table. reflexivity. reflexivity. destruct b31. unfold xor_bytes. unfold xor_bits. unfold GF_mul_table.  reflexivity. 
  reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. 

  destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity.

destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity.  destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity.

destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. 
destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. 
destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. 
destruct b23. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. 
destruct b22. destruct b23. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b23. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. 
destruct b21. destruct b22. destruct b23. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b23. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b22. destruct b23. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b23. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b24. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b25. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b26. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b27. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b28. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b29. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. destruct b30. destruct b31. reflexivity. reflexivity. destruct b31. reflexivity. reflexivity. 


Admitted.
 


Theorem mc_inv_mc: forall state: matrix,
    inv_mix_columns (mix_columns (state)) = state.
Proof.
  intros s. unfold mix_columns. unfold inv_mix_columns. destruct s eqn:H0.
 destruct (mix_state_column (bytes4 r0c0 r1c0 r2c0 r3c0)) eqn:H1. destruct (mix_state_column (bytes4 r0c1 r1c1 r2c1 r3c1)) eqn:H2. destruct (mix_state_column (bytes4 r0c2 r1c2 r2c2 r3c2)) eqn:H3. destruct (mix_state_column (bytes4 r0c3 r1c3 r2c3 r3c3)) eqn:H4.
 rewrite <- H1. rewrite <- H2. rewrite <- H3. rewrite <- H4. rewrite -> mc_inv_mc_col. rewrite -> mc_inv_mc_col. rewrite -> mc_inv_mc_col. rewrite -> mc_inv_mc_col. reflexivity.
  Qed.

(*TODO: round keys*)

Definition zb: byte :=
  bits8 s0 s0 s0 s0 s0 s0 s0 s0
.


Definition starkey: matrix :=
  bytes16 zb zb zb zb
          zb zb zb zb
          zb zb zb zb
          zb zb zb zb
.


Definition add_round_key (key: matrix) (state: matrix) :=
  match key with
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
  starkey
.

Definition key1 :=
  starkey
.

Definition key2 :=
  starkey
.

Definition key3 :=
  starkey
.

Definition key4 :=
  starkey
.

Definition key5 :=
  starkey
.

Definition key6 :=
  starkey
.

Definition key7 :=
  starkey
.

Definition key8 :=
  starkey
.

Definition key9 :=
  starkey
.

Definition key10 :=
  starkey
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

    
