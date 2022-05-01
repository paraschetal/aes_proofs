
type bit =
| S0
| S1

type nibble =
| Bits4 of bit * bit * bit * bit

type byte =
| Bits8 of bit * bit * bit * bit * bit * bit * bit * bit

(** val ms_nibble : byte -> nibble **)

let ms_nibble = function
| Bits8 (b0, b1, b2, b3, _, _, _, _) -> Bits4 (b0, b1, b2, b3)

(** val ls_nibble : byte -> nibble **)

let ls_nibble = function
| Bits8 (_, _, _, _, b4, b5, b6, b7) -> Bits4 (b4, b5, b6, b7)

(** val xor_bits : bit -> bit -> bit **)

let xor_bits b1 b2 =
  match b1 with
  | S0 -> b2
  | S1 -> (match b2 with
           | S0 -> S1
           | S1 -> S0)

(** val xor_bytes : byte -> byte -> byte **)

let xor_bytes b a =
  let Bits8 (b7, b6, b5, b4, b3, b2, b1, b0) = b in
  let Bits8 (a7, a6, a5, a4, a3, a2, a1, a0) = a in
  Bits8 ((xor_bits b7 a7), (xor_bits b6 a6), (xor_bits b5 a5), (xor_bits b4 a4), (xor_bits b3 a3), (xor_bits b2 a2), (xor_bits b1 a1),
  (xor_bits b0 a0))

type word =
| Bytes4 of byte * byte * byte * byte

type matrix =
| Bytes16 of byte * byte * byte * byte * byte * byte * byte * byte * byte * byte * byte * byte * byte * byte * byte * byte

(** val s_box : byte -> byte **)

let s_box b =
  let Bits4 (b0, b1, b2, b3) = ms_nibble b in
  (match b0 with
   | S0 ->
     (match b1 with
      | S0 ->
        (match b2 with
         | S0 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S0, S0, S1, S1)
                              | S1 -> Bits8 (S0, S1, S1, S1, S1, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S1, S0, S1, S1, S1)
                              | S1 -> Bits8 (S0, S1, S1, S1, S1, S0, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S1, S0, S0, S1, S0)
                              | S1 -> Bits8 (S0, S1, S1, S0, S1, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S1, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S0, S0, S0, S1, S0, S1))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S0, S0, S0, S0)
                              | S1 -> Bits8 (S0, S0, S0, S0, S0, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S0, S1, S1, S1)
                              | S1 -> Bits8 (S0, S0, S1, S0, S1, S0, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S1, S1, S1, S1, S0)
                              | S1 -> Bits8 (S1, S1, S0, S1, S0, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S1, S0, S1, S1)
                              | S1 -> Bits8 (S0, S1, S1, S1, S0, S1, S1, S0)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S1, S0, S1, S0)
                              | S1 -> Bits8 (S1, S0, S0, S0, S0, S0, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S1, S0, S0, S1)
                              | S1 -> Bits8 (S0, S1, S1, S1, S1, S1, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S1, S1, S0, S1, S0)
                              | S1 -> Bits8 (S0, S1, S0, S1, S1, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S0, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S1, S1, S0, S0, S0, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S1, S1, S0, S1)
                              | S1 -> Bits8 (S1, S1, S0, S1, S0, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S0, S0, S1, S0)
                              | S1 -> Bits8 (S1, S0, S1, S0, S1, S1, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S1, S1, S0, S0)
                              | S1 -> Bits8 (S1, S0, S1, S0, S0, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S1, S0, S0, S1, S0)
                              | S1 -> Bits8 (S1, S1, S0, S0, S0, S0, S0, S0))))))
         | S1 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S0, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S1, S1, S1, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S0, S0, S1, S1)
                              | S1 -> Bits8 (S0, S0, S1, S0, S0, S1, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S0, S1, S1, S0)
                              | S1 -> Bits8 (S0, S0, S1, S1, S1, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S1, S0, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S0, S0, S1, S1, S0, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S0, S1, S0, S0)
                              | S1 -> Bits8 (S1, S0, S1, S0, S0, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S0, S0, S1, S0, S1)
                              | S1 -> Bits8 (S1, S1, S1, S1, S0, S0, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S1, S0, S0, S0, S1)
                              | S1 -> Bits8 (S1, S1, S0, S1, S1, S0, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S0, S0, S0, S1)
                              | S1 -> Bits8 (S0, S0, S0, S1, S0, S1, S0, S1)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S0, S0, S1, S0, S0)
                              | S1 -> Bits8 (S1, S1, S0, S0, S0, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S0, S0, S1, S1)
                              | S1 -> Bits8 (S1, S1, S0, S0, S0, S0, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S1, S0, S0, S0)
                              | S1 -> Bits8 (S1, S0, S0, S1, S0, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S0, S0, S1, S0, S1)
                              | S1 -> Bits8 (S1, S0, S0, S1, S1, S0, S1, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S0, S0, S1, S1, S1)
                              | S1 -> Bits8 (S0, S0, S0, S1, S0, S0, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S0, S0, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S1, S0, S0, S0, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S0, S1, S0, S1, S1)
                              | S1 -> Bits8 (S0, S0, S1, S0, S0, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S0, S0, S1, S0)
                              | S1 -> Bits8 (S0, S1, S1, S1, S0, S1, S0, S1)))))))
      | S1 ->
        (match b2 with
         | S0 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S0, S1, S0, S0, S1)
                              | S1 -> Bits8 (S1, S0, S0, S0, S0, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S1, S1, S0, S0)
                              | S1 -> Bits8 (S0, S0, S0, S1, S1, S0, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S1, S0, S1, S1)
                              | S1 -> Bits8 (S0, S1, S1, S0, S1, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S1, S0, S1, S0)
                              | S1 -> Bits8 (S1, S0, S1, S0, S0, S0, S0, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S0, S0, S1, S0)
                              | S1 -> Bits8 (S0, S0, S1, S1, S1, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S1, S0, S1, S1, S0)
                              | S1 -> Bits8 (S1, S0, S1, S1, S0, S0, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S1, S0, S0, S1)
                              | S1 -> Bits8 (S1, S1, S1, S0, S0, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S1, S1, S1, S1)
                              | S1 -> Bits8 (S1, S0, S0, S0, S0, S1, S0, S0)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S0, S0, S1, S1)
                              | S1 -> Bits8 (S1, S1, S0, S1, S0, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S0, S0, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S1, S0, S1, S1, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S0, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S1, S1, S1, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S0, S0, S0, S1)
                              | S1 -> Bits8 (S0, S1, S0, S1, S1, S0, S1, S1))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S1, S0, S1, S0)
                              | S1 -> Bits8 (S1, S1, S0, S0, S1, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S1, S1, S1, S0)
                              | S1 -> Bits8 (S0, S0, S1, S1, S1, S0, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S1, S0, S1, S0)
                              | S1 -> Bits8 (S0, S1, S0, S0, S1, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S1, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S0, S0, S1, S1, S1, S1))))))
         | S1 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S1, S0, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S1, S0, S1, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S1, S0, S1, S0)
                              | S1 -> Bits8 (S1, S1, S1, S1, S1, S0, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S0, S0, S1, S1)
                              | S1 -> Bits8 (S0, S1, S0, S0, S1, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S0, S0, S1, S1)
                              | S1 -> Bits8 (S1, S0, S0, S0, S0, S1, S0, S1))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S0, S1, S0, S1)
                              | S1 -> Bits8 (S1, S1, S1, S1, S1, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S0, S0, S0, S1, S0)
                              | S1 -> Bits8 (S0, S1, S1, S1, S1, S1, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S0, S0, S0, S0)
                              | S1 -> Bits8 (S0, S0, S1, S1, S1, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S1, S1, S1, S1)
                              | S1 -> Bits8 (S1, S0, S1, S0, S1, S0, S0, S0)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S0, S0, S0, S1)
                              | S1 -> Bits8 (S1, S0, S1, S0, S0, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S0, S0, S0, S0)
                              | S1 -> Bits8 (S1, S0, S0, S0, S1, S1, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S0, S0, S1, S0)
                              | S1 -> Bits8 (S1, S0, S0, S1, S1, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S1, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S1, S1, S0, S1, S0, S1))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S1, S1, S0, S0)
                              | S1 -> Bits8 (S1, S0, S1, S1, S0, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S1, S1, S0, S1, S0)
                              | S1 -> Bits8 (S0, S0, S1, S0, S0, S0, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S0, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S1, S1, S1, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S1, S0, S0, S1, S1)
                              | S1 -> Bits8 (S1, S1, S0, S1, S0, S0, S1, S0))))))))
   | S1 ->
     (match b1 with
      | S0 ->
        (match b2 with
         | S0 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S1, S1, S0, S1)
                              | S1 -> Bits8 (S0, S0, S0, S0, S1, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S0, S0, S1, S1)
                              | S1 -> Bits8 (S1, S1, S1, S0, S1, S1, S0, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S1, S1, S1, S1)
                              | S1 -> Bits8 (S1, S0, S0, S1, S0, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S0, S1, S0, S0)
                              | S1 -> Bits8 (S0, S0, S0, S1, S0, S1, S1, S1))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S0, S1, S0, S0)
                              | S1 -> Bits8 (S1, S0, S1, S0, S0, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S1, S1, S1, S1, S0)
                              | S1 -> Bits8 (S0, S0, S1, S1, S1, S1, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S0, S1, S0, S0)
                              | S1 -> Bits8 (S0, S1, S0, S1, S1, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S1, S0, S0, S1)
                              | S1 -> Bits8 (S0, S1, S1, S1, S0, S0, S1, S1)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S0, S0, S0, S0)
                              | S1 -> Bits8 (S1, S0, S0, S0, S0, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S1, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S0, S1, S1, S1, S0, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S0, S0, S1, S0)
                              | S1 -> Bits8 (S0, S0, S1, S0, S1, S0, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S0, S0, S0, S0)
                              | S1 -> Bits8 (S1, S0, S0, S0, S1, S0, S0, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S0, S1, S1, S0)
                              | S1 -> Bits8 (S1, S1, S1, S0, S1, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S1, S0, S0, S0)
                              | S1 -> Bits8 (S0, S0, S0, S1, S0, S1, S0, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S1, S1, S1, S1, S0)
                              | S1 -> Bits8 (S0, S1, S0, S1, S1, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S0, S1, S0, S1, S1)
                              | S1 -> Bits8 (S1, S1, S0, S1, S1, S0, S1, S1))))))
         | S1 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S0, S0, S0, S0, S0)
                              | S1 -> Bits8 (S0, S0, S1, S1, S0, S0, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S1, S0, S1, S0)
                              | S1 -> Bits8 (S0, S0, S0, S0, S1, S0, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S1, S0, S0, S1)
                              | S1 -> Bits8 (S0, S0, S0, S0, S0, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S0, S1, S0, S0)
                              | S1 -> Bits8 (S0, S1, S0, S1, S1, S1, S0, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S0, S0, S1, S0)
                              | S1 -> Bits8 (S1, S1, S0, S1, S0, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S1, S1, S0, S0)
                              | S1 -> Bits8 (S0, S1, S1, S0, S0, S0, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S0, S0, S0, S1)
                              | S1 -> Bits8 (S1, S0, S0, S1, S0, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S0, S0, S1, S0, S0)
                              | S1 -> Bits8 (S0, S1, S1, S1, S1, S0, S0, S1)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S0, S0, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S0, S0, S1, S0, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S0, S1, S1, S1)
                              | S1 -> Bits8 (S0, S1, S1, S0, S1, S1, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S0, S1, S1, S0, S1)
                              | S1 -> Bits8 (S1, S1, S0, S1, S0, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S1, S1, S1, S0)
                              | S1 -> Bits8 (S1, S0, S1, S0, S1, S0, S0, S1))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S1, S1, S0, S0)
                              | S1 -> Bits8 (S0, S1, S0, S1, S0, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S1, S0, S1, S0, S0)
                              | S1 -> Bits8 (S1, S1, S1, S0, S1, S0, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S0, S1, S0, S1)
                              | S1 -> Bits8 (S0, S1, S1, S1, S1, S0, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S1, S1, S1, S0)
                              | S1 -> Bits8 (S0, S0, S0, S0, S1, S0, S0, S0)))))))
      | S1 ->
        (match b2 with
         | S0 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S1, S0, S1, S0)
                              | S1 -> Bits8 (S0, S1, S1, S1, S1, S0, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S0, S1, S0, S1)
                              | S1 -> Bits8 (S0, S0, S1, S0, S1, S1, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S1, S1, S0, S0)
                              | S1 -> Bits8 (S1, S0, S1, S0, S0, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S0, S1, S0, S0)
                              | S1 -> Bits8 (S1, S1, S0, S0, S0, S1, S1, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S0, S1, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S0, S1, S1, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S1, S0, S1, S0, S0)
                              | S1 -> Bits8 (S0, S0, S0, S1, S1, S1, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S1, S0, S1, S1)
                              | S1 -> Bits8 (S1, S0, S1, S1, S1, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S0, S1, S0, S1, S1)
                              | S1 -> Bits8 (S1, S0, S0, S0, S1, S0, S1, S0)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S1, S0, S0, S0, S0)
                              | S1 -> Bits8 (S0, S0, S1, S1, S1, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S0, S1, S0, S1)
                              | S1 -> Bits8 (S0, S1, S1, S0, S0, S1, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S1, S0, S0, S0)
                              | S1 -> Bits8 (S0, S0, S0, S0, S0, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S1, S0, S1, S1, S0)
                              | S1 -> Bits8 (S0, S0, S0, S0, S1, S1, S1, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S0, S0, S0, S1)
                              | S1 -> Bits8 (S0, S0, S1, S1, S0, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S0, S1, S1, S1)
                              | S1 -> Bits8 (S1, S0, S1, S1, S1, S0, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S0, S0, S1, S1, S0)
                              | S1 -> Bits8 (S1, S1, S0, S0, S0, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S1, S1, S0, S1)
                              | S1 -> Bits8 (S1, S0, S0, S1, S1, S1, S1, S0))))))
         | S1 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S0, S0, S0, S0, S1)
                              | S1 -> Bits8 (S1, S1, S1, S1, S1, S0, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S1, S0, S0, S0)
                              | S1 -> Bits8 (S0, S0, S0, S1, S0, S0, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S1, S0, S0, S1)
                              | S1 -> Bits8 (S1, S1, S0, S1, S1, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S0, S1, S1, S1, S0)
                              | S1 -> Bits8 (S1, S0, S0, S1, S0, S1, S0, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S1, S0, S1, S1)
                              | S1 -> Bits8 (S0, S0, S0, S1, S1, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S0, S0, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S1, S0, S1, S0, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S1, S1, S1, S0)
                              | S1 -> Bits8 (S0, S1, S0, S1, S0, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S1, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S0, S1, S1, S1, S1, S1)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S0, S1, S1, S0, S0)
                              | S1 -> Bits8 (S1, S0, S1, S0, S0, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S0, S1, S0, S0, S1)
                              | S1 -> Bits8 (S0, S0, S0, S0, S1, S1, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S1, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S1, S0, S0, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S0, S0, S1, S0)
                              | S1 -> Bits8 (S0, S1, S1, S0, S1, S0, S0, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S0, S0, S0, S1)
                              | S1 -> Bits8 (S1, S0, S0, S1, S1, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S1, S1, S0, S1)
                              | S1 -> Bits8 (S0, S0, S0, S0, S1, S1, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S0, S0, S0, S0)
                              | S1 -> Bits8 (S0, S1, S0, S1, S0, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S1, S0, S1, S1)
                              | S1 -> Bits8 (S0, S0, S0, S1, S0, S1, S1, S0)))))))))

(** val inv_s_box : byte -> byte **)

let inv_s_box b =
  let Bits4 (b0, b1, b2, b3) = ms_nibble b in
  (match b0 with
   | S0 ->
     (match b1 with
      | S0 ->
        (match b2 with
         | S0 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S0, S0, S1, S0)
                              | S1 -> Bits8 (S0, S0, S0, S0, S1, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S1, S0, S1, S0)
                              | S1 -> Bits8 (S1, S1, S0, S1, S0, S1, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S0, S0, S0, S0)
                              | S1 -> Bits8 (S0, S0, S1, S1, S0, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S0, S1, S0, S1)
                              | S1 -> Bits8 (S0, S0, S1, S1, S1, S0, S0, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S1, S1, S1, S1)
                              | S1 -> Bits8 (S0, S1, S0, S0, S0, S0, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S0, S0, S1, S1)
                              | S1 -> Bits8 (S1, S0, S0, S1, S1, S1, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S0, S0, S0, S0, S1)
                              | S1 -> Bits8 (S1, S1, S1, S1, S0, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S1, S0, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S1, S1, S1, S0, S1, S1)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S1, S1, S1, S0, S0)
                              | S1 -> Bits8 (S1, S1, S1, S0, S0, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S1, S0, S0, S1)
                              | S1 -> Bits8 (S1, S0, S0, S0, S0, S0, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S1, S0, S1, S1)
                              | S1 -> Bits8 (S0, S0, S1, S0, S1, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S1, S1, S1, S1, S1)
                              | S1 -> Bits8 (S1, S0, S0, S0, S0, S1, S1, S1))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S0, S1, S0, S0)
                              | S1 -> Bits8 (S1, S0, S0, S0, S1, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S0, S0, S1, S1)
                              | S1 -> Bits8 (S0, S1, S0, S0, S0, S1, S0, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S0, S1, S0, S0)
                              | S1 -> Bits8 (S1, S1, S0, S1, S1, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S0, S1, S0, S0, S1)
                              | S1 -> Bits8 (S1, S1, S0, S0, S1, S0, S1, S1))))))
         | S1 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S0, S1, S0, S0)
                              | S1 -> Bits8 (S0, S1, S1, S1, S1, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S0, S1, S0, S0)
                              | S1 -> Bits8 (S0, S0, S1, S1, S0, S0, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S0, S1, S1, S0)
                              | S1 -> Bits8 (S1, S1, S0, S0, S0, S0, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S0, S0, S1, S1)
                              | S1 -> Bits8 (S0, S0, S1, S1, S1, S1, S0, S1))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S0, S1, S1, S1, S0)
                              | S1 -> Bits8 (S0, S1, S0, S0, S1, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S0, S1, S0, S1)
                              | S1 -> Bits8 (S0, S0, S0, S0, S1, S0, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S0, S0, S1, S0)
                              | S1 -> Bits8 (S1, S1, S1, S1, S1, S0, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S0, S0, S1, S1)
                              | S1 -> Bits8 (S0, S1, S0, S0, S1, S1, S1, S0)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S0, S1, S0, S0, S0)
                              | S1 -> Bits8 (S0, S0, S1, S0, S1, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S0, S0, S0, S1)
                              | S1 -> Bits8 (S0, S1, S1, S0, S0, S1, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S1, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S0, S1, S1, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S0, S1, S0, S0)
                              | S1 -> Bits8 (S1, S0, S1, S1, S0, S0, S1, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S1, S0, S1, S1, S0)
                              | S1 -> Bits8 (S0, S1, S0, S1, S1, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S0, S0, S1, S0)
                              | S1 -> Bits8 (S0, S1, S0, S0, S1, S0, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S1, S1, S0, S1)
                              | S1 -> Bits8 (S1, S0, S0, S0, S1, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S1, S0, S0, S0, S1)
                              | S1 -> Bits8 (S0, S0, S1, S0, S0, S1, S0, S1)))))))
      | S1 ->
        (match b2 with
         | S0 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S1, S0, S0, S1, S0)
                              | S1 -> Bits8 (S1, S1, S1, S1, S1, S0, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S1, S0, S1, S1, S0)
                              | S1 -> Bits8 (S0, S1, S1, S0, S0, S1, S0, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S0, S0, S1, S1, S0)
                              | S1 -> Bits8 (S0, S1, S1, S0, S1, S0, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S1, S0, S0, S0)
                              | S1 -> Bits8 (S0, S0, S0, S1, S0, S1, S1, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S1, S0, S1, S0, S0)
                              | S1 -> Bits8 (S1, S0, S1, S0, S0, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S1, S1, S0, S0)
                              | S1 -> Bits8 (S1, S1, S0, S0, S1, S1, S0, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S1, S1, S0, S1)
                              | S1 -> Bits8 (S0, S1, S1, S0, S0, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S0, S1, S1, S0)
                              | S1 -> Bits8 (S1, S0, S0, S1, S0, S0, S1, S0)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S1, S1, S0, S0)
                              | S1 -> Bits8 (S0, S1, S1, S1, S0, S0, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S1, S0, S0, S0)
                              | S1 -> Bits8 (S0, S1, S0, S1, S0, S0, S0, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S1, S1, S1, S0, S1)
                              | S1 -> Bits8 (S1, S1, S1, S0, S1, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S1, S0, S0, S1)
                              | S1 -> Bits8 (S1, S1, S0, S1, S1, S0, S1, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S1, S1, S1, S0)
                              | S1 -> Bits8 (S0, S0, S0, S1, S0, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S0, S1, S1, S0)
                              | S1 -> Bits8 (S0, S1, S0, S1, S0, S1, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S0, S1, S1, S1)
                              | S1 -> Bits8 (S1, S0, S0, S0, S1, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S1, S1, S0, S1)
                              | S1 -> Bits8 (S1, S0, S0, S0, S0, S1, S0, S0))))))
         | S1 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S0, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S0, S1, S1, S0, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S1, S0, S1, S1)
                              | S1 -> Bits8 (S0, S0, S0, S0, S0, S0, S0, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S0, S1, S1, S0, S0)
                              | S1 -> Bits8 (S1, S0, S1, S1, S1, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S1, S0, S0, S1, S1)
                              | S1 -> Bits8 (S0, S0, S0, S0, S1, S0, S1, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S1, S0, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S1, S0, S0, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S1, S0, S0, S0)
                              | S1 -> Bits8 (S0, S0, S0, S0, S0, S1, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S1, S0, S0, S0)
                              | S1 -> Bits8 (S1, S0, S1, S1, S0, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S0, S1, S0, S1)
                              | S1 -> Bits8 (S0, S0, S0, S0, S0, S1, S1, S0)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S1, S0, S0, S0, S0)
                              | S1 -> Bits8 (S0, S0, S1, S0, S1, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S1, S1, S1, S0)
                              | S1 -> Bits8 (S1, S0, S0, S0, S1, S1, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S1, S0, S1, S0)
                              | S1 -> Bits8 (S0, S0, S1, S1, S1, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S0, S1, S1, S1, S1)
                              | S1 -> Bits8 (S0, S0, S0, S0, S0, S0, S1, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S0, S0, S0, S1)
                              | S1 -> Bits8 (S1, S0, S1, S0, S1, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S1, S1, S0, S1)
                              | S1 -> Bits8 (S0, S0, S0, S0, S0, S0, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S0, S0, S0, S0, S1)
                              | S1 -> Bits8 (S0, S0, S0, S1, S0, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S0, S1, S0, S1, S0)
                              | S1 -> Bits8 (S0, S1, S1, S0, S1, S0, S1, S1))))))))
   | S1 ->
     (match b1 with
      | S0 ->
        (match b2 with
         | S0 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S1, S0, S1, S0)
                              | S1 -> Bits8 (S1, S0, S0, S1, S0, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S0, S0, S0, S1)
                              | S1 -> Bits8 (S0, S1, S0, S0, S0, S0, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S1, S1, S1, S1)
                              | S1 -> Bits8 (S0, S1, S1, S0, S0, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S1, S1, S1, S0, S0)
                              | S1 -> Bits8 (S1, S1, S1, S0, S1, S0, S1, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S0, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S1, S1, S0, S0, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S1, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S0, S0, S1, S1, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S1, S0, S0, S0, S0)
                              | S1 -> Bits8 (S1, S0, S1, S1, S0, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S0, S0, S1, S1, S0)
                              | S1 -> Bits8 (S0, S1, S1, S1, S0, S0, S1, S1)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S0, S1, S1, S0)
                              | S1 -> Bits8 (S1, S0, S1, S0, S1, S1, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S1, S0, S1, S0, S0)
                              | S1 -> Bits8 (S0, S0, S1, S0, S0, S0, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S0, S0, S1, S1, S1)
                              | S1 -> Bits8 (S1, S0, S1, S0, S1, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S0, S1, S0, S1)
                              | S1 -> Bits8 (S1, S0, S0, S0, S0, S1, S0, S1))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S0, S0, S0, S1, S0)
                              | S1 -> Bits8 (S1, S1, S1, S1, S1, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S0, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S1, S0, S1, S0, S0, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S1, S1, S0, S0)
                              | S1 -> Bits8 (S0, S1, S1, S1, S0, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S1, S1, S1, S1, S1)
                              | S1 -> Bits8 (S0, S1, S1, S0, S1, S1, S1, S0))))))
         | S1 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S0, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S1, S1, S0, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S1, S0, S1, S0)
                              | S1 -> Bits8 (S0, S1, S1, S1, S0, S0, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S1, S1, S0, S1)
                              | S1 -> Bits8 (S0, S0, S1, S0, S1, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S0, S1, S0, S1)
                              | S1 -> Bits8 (S1, S0, S0, S0, S1, S0, S0, S1))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S1, S1, S1, S1)
                              | S1 -> Bits8 (S1, S0, S1, S1, S0, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S0, S0, S1, S0)
                              | S1 -> Bits8 (S0, S0, S0, S0, S1, S1, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S1, S0, S1, S0)
                              | S1 -> Bits8 (S0, S0, S0, S1, S1, S0, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S1, S1, S1, S0)
                              | S1 -> Bits8 (S0, S0, S0, S1, S1, S0, S1, S1)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S1, S1, S1, S0, S0)
                              | S1 -> Bits8 (S0, S1, S0, S1, S0, S1, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S1, S1, S1, S0)
                              | S1 -> Bits8 (S0, S1, S0, S0, S1, S0, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S0, S1, S1, S0)
                              | S1 -> Bits8 (S1, S1, S0, S1, S0, S0, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S1, S1, S0, S0, S1)
                              | S1 -> Bits8 (S0, S0, S1, S0, S0, S0, S0, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S1, S0, S1, S0)
                              | S1 -> Bits8 (S1, S1, S0, S1, S1, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S0, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S1, S1, S1, S1, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S1, S1, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S0, S0, S1, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S1, S0, S1, S0)
                              | S1 -> Bits8 (S1, S1, S1, S1, S0, S1, S0, S0)))))))
      | S1 ->
        (match b2 with
         | S0 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S1, S1, S1, S1)
                              | S1 -> Bits8 (S1, S1, S0, S1, S1, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S1, S0, S0, S0)
                              | S1 -> Bits8 (S0, S0, S1, S1, S0, S0, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S0, S1, S0, S0, S0)
                              | S1 -> Bits8 (S0, S0, S0, S0, S0, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S0, S1, S1, S1)
                              | S1 -> Bits8 (S0, S0, S1, S1, S0, S0, S0, S1))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S0, S0, S0, S1)
                              | S1 -> Bits8 (S0, S0, S0, S1, S0, S0, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S0, S0, S0, S0)
                              | S1 -> Bits8 (S0, S1, S0, S1, S1, S0, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S0, S1, S1, S1)
                              | S1 -> Bits8 (S1, S0, S0, S0, S0, S0, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S0, S1, S1, S0, S0)
                              | S1 -> Bits8 (S0, S1, S0, S1, S1, S1, S1, S1)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S0, S0, S0, S0, S0)
                              | S1 -> Bits8 (S0, S1, S0, S1, S0, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S1, S1, S1, S1, S1)
                              | S1 -> Bits8 (S1, S0, S1, S0, S1, S0, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S1, S0, S0, S1)
                              | S1 -> Bits8 (S1, S0, S1, S1, S0, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S0, S1, S0, S1, S0)
                              | S1 -> Bits8 (S0, S0, S0, S0, S1, S1, S0, S1))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S0, S1, S1, S0, S1)
                              | S1 -> Bits8 (S1, S1, S1, S0, S0, S1, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S1, S1, S1, S0, S1, S0)
                              | S1 -> Bits8 (S1, S0, S0, S1, S1, S1, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S0, S0, S1, S1)
                              | S1 -> Bits8 (S1, S1, S0, S0, S1, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S1, S1, S0, S0)
                              | S1 -> Bits8 (S1, S1, S1, S0, S1, S1, S1, S1))))))
         | S1 ->
           (match b3 with
            | S0 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S0, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S1, S0, S0, S0, S0, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S1, S1, S1, S0, S1, S1)
                              | S1 -> Bits8 (S0, S1, S0, S0, S1, S1, S0, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S0, S1, S1, S1, S0)
                              | S1 -> Bits8 (S0, S0, S1, S0, S1, S0, S1, S0))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S1, S0, S1, S0, S1)
                              | S1 -> Bits8 (S1, S0, S1, S1, S0, S0, S0, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S0, S1, S0, S0, S0)
                              | S1 -> Bits8 (S1, S1, S1, S0, S1, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S1, S0, S1, S1)
                              | S1 -> Bits8 (S0, S0, S1, S1, S1, S1, S0, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S0, S0, S0, S1, S1)
                              | S1 -> Bits8 (S0, S1, S0, S1, S0, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S0, S1, S1, S0, S0, S1)
                              | S1 -> Bits8 (S0, S1, S1, S0, S0, S0, S0, S1)))))
            | S1 ->
              let Bits4 (b4, b5, b6, b7) = ls_nibble b in
              (match b4 with
               | S0 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S0, S1, S1, S1)
                              | S1 -> Bits8 (S0, S0, S1, S0, S1, S0, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S0, S0, S1, S0, S0)
                              | S1 -> Bits8 (S0, S1, S1, S1, S1, S1, S1, S0)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S0, S1, S1, S1, S0, S1, S0)
                              | S1 -> Bits8 (S0, S1, S1, S1, S0, S1, S1, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S0, S1, S0, S1, S1, S0)
                              | S1 -> Bits8 (S0, S0, S1, S0, S0, S1, S1, S0))))
               | S1 ->
                 (match b5 with
                  | S0 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S1, S1, S1, S0, S0, S0, S0, S1)
                              | S1 -> Bits8 (S0, S1, S1, S0, S1, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S1, S0, S1, S0, S0)
                              | S1 -> Bits8 (S0, S1, S1, S0, S0, S0, S1, S1)))
                  | S1 ->
                    (match b6 with
                     | S0 -> (match b7 with
                              | S0 -> Bits8 (S0, S1, S0, S1, S0, S1, S0, S1)
                              | S1 -> Bits8 (S0, S0, S1, S0, S0, S0, S0, S1))
                     | S1 -> (match b7 with
                              | S0 -> Bits8 (S0, S0, S0, S0, S1, S1, S0, S0)
                              | S1 -> Bits8 (S0, S1, S1, S1, S1, S1, S0, S1)))))))))

type round =
| R1
| R2
| R3
| R4
| R5
| R6
| R7
| R8
| R9
| R10

(** val inv_shift_rows : matrix -> matrix **)

let inv_shift_rows = function
| Bytes16 (r0c0, r0c1, r0c2, r0c3, r1c0, r1c1, r1c2, r1c3, r2c0, r2c1, r2c2, r2c3, r3c0, r3c1, r3c2, r3c3) ->
  Bytes16 (r0c0, r0c1, r0c2, r0c3, r1c3, r1c0, r1c1, r1c2, r2c2, r2c3, r2c0, r2c1, r3c1, r3c2, r3c3, r3c0)

(** val inv_sub_bytes : matrix -> matrix **)

let inv_sub_bytes = function
| Bytes16 (r0c0, r0c1, r0c2, r0c3, r1c0, r1c1, r1c2, r1c3, r2c0, r2c1, r2c2, r2c3, r3c0, r3c1, r3c2, r3c3) ->
  Bytes16 ((inv_s_box r0c0), (inv_s_box r0c1), (inv_s_box r0c2), (inv_s_box r0c3), (inv_s_box r1c0), (inv_s_box r1c1), (inv_s_box r1c2),
    (inv_s_box r1c3), (inv_s_box r2c0), (inv_s_box r2c1), (inv_s_box r2c2), (inv_s_box r2c3), (inv_s_box r3c0), (inv_s_box r3c1),
    (inv_s_box r3c2), (inv_s_box r3c3))

(** val xtime : byte -> byte **)

let xtime = function
| Bits8 (b7, b6, b5, b4, b3, b2, b1, b0) ->
  (match b7 with
   | S0 -> Bits8 (b6, b5, b4, b3, b2, b1, b0, S0)
   | S1 -> xor_bytes (Bits8 (b6, b5, b4, b3, b2, b1, b0, S0)) (Bits8 (S0, S0, S0, S1, S1, S0, S1, S1)))

(** val mul02 : byte -> byte **)

let mul02 =
  xtime

(** val mul09 : byte -> byte **)

let mul09 b =
  xor_bytes b (mul02 (mul02 (mul02 b)))

(** val mul0b : byte -> byte **)

let mul0b b =
  xor_bytes b (xor_bytes (mul02 b) (mul02 (mul02 (mul02 b))))

(** val mul0d : byte -> byte **)

let mul0d b =
  xor_bytes b (xor_bytes (mul02 (mul02 b)) (mul02 (mul02 (mul02 b))))

(** val mul0e : byte -> byte **)

let mul0e b =
  xor_bytes (mul02 b) (xor_bytes (mul02 (mul02 b)) (mul02 (mul02 (mul02 b))))

(** val inv_mix_column_transform : word -> word **)

let inv_mix_column_transform = function
| Bytes4 (a', b', c', d') ->
  let a'' = xor_bytes (xor_bytes (xor_bytes (mul0e a') (mul0b b')) (mul0d c')) (mul09 d') in
  let b'' = xor_bytes (xor_bytes (xor_bytes (mul09 a') (mul0e b')) (mul0b c')) (mul0d d') in
  let c'' = xor_bytes (xor_bytes (xor_bytes (mul0d a') (mul09 b')) (mul0e c')) (mul0b d') in
  let d'' = xor_bytes (xor_bytes (xor_bytes (mul0b a') (mul0d b')) (mul09 c')) (mul0e d') in Bytes4 (a'', b'', c'', d'')

(** val columns_to_matrix : word -> word -> word -> word -> matrix **)

let columns_to_matrix c0 c1 c2 c3 =
  let Bytes4 (c00, c10, c20, c30) = c0 in
  let Bytes4 (c01, c11, c21, c31) = c1 in
  let Bytes4 (c02, c12, c22, c32) = c2 in
  let Bytes4 (c03, c13, c23, c33) = c3 in Bytes16 (c00, c01, c02, c03, c10, c11, c12, c13, c20, c21, c22, c23, c30, c31, c32, c33)

(** val inv_mix_columns : matrix -> matrix **)

let inv_mix_columns = function
| Bytes16 (s00, s01, s02, s03, s10, s11, s12, s13, s20, s21, s22, s23, s30, s31, s32, s33) ->
  let ncol0 = inv_mix_column_transform (Bytes4 (s00, s10, s20, s30)) in
  let ncol1 = inv_mix_column_transform (Bytes4 (s01, s11, s21, s31)) in
  let ncol2 = inv_mix_column_transform (Bytes4 (s02, s12, s22, s32)) in
  let ncol3 = inv_mix_column_transform (Bytes4 (s03, s13, s23, s33)) in columns_to_matrix ncol0 ncol1 ncol2 ncol3

(** val rc : round -> byte **)

let rc = function
| R1 -> Bits8 (S0, S0, S0, S0, S0, S0, S0, S1)
| R2 -> Bits8 (S0, S0, S0, S0, S0, S0, S1, S0)
| R3 -> Bits8 (S0, S0, S0, S0, S0, S1, S0, S0)
| R4 -> Bits8 (S0, S0, S0, S0, S1, S0, S0, S0)
| R5 -> Bits8 (S0, S0, S0, S1, S0, S0, S0, S0)
| R6 -> Bits8 (S0, S0, S1, S0, S0, S0, S0, S0)
| R7 -> Bits8 (S0, S1, S0, S0, S0, S0, S0, S0)
| R8 -> Bits8 (S1, S0, S0, S0, S0, S0, S0, S0)
| R9 -> Bits8 (S0, S0, S0, S1, S1, S0, S1, S1)
| R10 -> Bits8 (S0, S0, S1, S1, S0, S1, S1, S0)

(** val rcon : round -> word **)

let rcon i =
  Bytes4 ((rc i), (Bits8 (S0, S0, S0, S0, S0, S0, S0, S0)), (Bits8 (S0, S0, S0, S0, S0, S0, S0, S0)), (Bits8 (S0, S0, S0, S0, S0, S0,
    S0, S0)))

(** val xor_words : word -> word -> word **)

let xor_words w1 w2 =
  let Bytes4 (b0, b1, b2, b3) = w1 in
  let Bytes4 (a0, a1, a2, a3) = w2 in Bytes4 ((xor_bytes b0 a0), (xor_bytes b1 a1), (xor_bytes b2 a2), (xor_bytes b3 a3))

(** val rcon_word : round -> word -> word **)

let rcon_word i w =
  xor_words w (rcon i)

(** val rot_word : word -> word **)

let rot_word = function
| Bytes4 (b0, b1, b2, b3) -> Bytes4 (b1, b2, b3, b0)

(** val sub_word : word -> word **)

let sub_word = function
| Bytes4 (b0, b1, b2, b3) -> Bytes4 ((s_box b0), (s_box b1), (s_box b2), (s_box b3))

type key_t =
| Keywords of word * word * word * word

(** val matrix_to_keyt : matrix -> key_t **)

let matrix_to_keyt = function
| Bytes16 (b11, b12, b13, b14, b21, b22, b23, b24, b31, b32, b33, b34, b41, b42, b43, b44) ->
  Keywords ((Bytes4 (b11, b12, b13, b14)), (Bytes4 (b21, b22, b23, b24)), (Bytes4 (b31, b32, b33, b34)), (Bytes4 (b41, b42, b43, b44)))

(** val keyt_to_matrix : key_t -> matrix **)

let keyt_to_matrix = function
| Keywords (w1, w2, w3, w4) ->
  let Bytes4 (b11, b12, b13, b14) = w1 in
  let Bytes4 (b21, b22, b23, b24) = w2 in
  let Bytes4 (b31, b32, b33, b34) = w3 in
  let Bytes4 (b41, b42, b43, b44) = w4 in Bytes16 (b11, b12, b13, b14, b21, b22, b23, b24, b31, b32, b33, b34, b41, b42, b43, b44)

(** val first_w_in_rk : round -> word -> word **)

let first_w_in_rk i w =
  rot_word (sub_word (rcon_word i w))

(** val rk0 : matrix -> matrix **)

let rk0 k =
  k

(** val rk : round -> key_t -> key_t **)

let rk i = function
| Keywords (w1, w2, w3, w4) ->
  Keywords ((xor_words (first_w_in_rk i w4) w1), (xor_words (xor_words (first_w_in_rk i w4) w1) w2),
    (xor_words (xor_words (xor_words (first_w_in_rk i w4) w1) w2) w3),
    (xor_words (xor_words (xor_words (xor_words (first_w_in_rk i w4) w1) w2) w3) w4))

(** val rk1 : matrix -> matrix **)

let rk1 k =
  keyt_to_matrix (rk R1 (matrix_to_keyt k))

(** val rk2 : matrix -> matrix **)

let rk2 k =
  keyt_to_matrix (rk R2 (matrix_to_keyt (rk1 k)))

(** val rk3 : matrix -> matrix **)

let rk3 k =
  keyt_to_matrix (rk R3 (matrix_to_keyt (rk2 k)))

(** val rk4 : matrix -> matrix **)

let rk4 k =
  keyt_to_matrix (rk R4 (matrix_to_keyt (rk3 k)))

(** val rk5 : matrix -> matrix **)

let rk5 k =
  keyt_to_matrix (rk R5 (matrix_to_keyt (rk4 k)))

(** val rk6 : matrix -> matrix **)

let rk6 k =
  keyt_to_matrix (rk R6 (matrix_to_keyt (rk5 k)))

(** val rk7 : matrix -> matrix **)

let rk7 k =
  keyt_to_matrix (rk R7 (matrix_to_keyt (rk6 k)))

(** val rk8 : matrix -> matrix **)

let rk8 k =
  keyt_to_matrix (rk R8 (matrix_to_keyt (rk7 k)))

(** val rk9 : matrix -> matrix **)

let rk9 k =
  keyt_to_matrix (rk R9 (matrix_to_keyt (rk8 k)))

(** val rk10 : matrix -> matrix **)

let rk10 k =
  keyt_to_matrix (rk R10 (matrix_to_keyt (rk9 k)))

(** val add_round_key : matrix -> matrix -> matrix **)

let add_round_key k state =
  let Bytes16 (k00, k01, k02, k03, k10, k11, k12, k13, k20, k21, k22, k23, k30, k31, k32, k33) = k in
  let Bytes16 (s00, s01, s02, s03, s10, s11, s12, s13, s20, s21, s22, s23, s30, s31, s32, s33) = state in
  Bytes16 ((xor_bytes k00 s00), (xor_bytes k01 s01), (xor_bytes k02 s02), (xor_bytes k03 s03), (xor_bytes k10 s10), (xor_bytes k11 s11),
  (xor_bytes k12 s12), (xor_bytes k13 s13), (xor_bytes k20 s20), (xor_bytes k21 s21), (xor_bytes k22 s22), (xor_bytes k23 s23),
  (xor_bytes k30 s30), (xor_bytes k31 s31), (xor_bytes k32 s32), (xor_bytes k33 s33))

(** val xor_matrices : matrix -> matrix -> matrix **)

let xor_matrices =
  add_round_key

(** val key0 : matrix -> matrix **)

let key0 =
  rk0

(** val key1 : matrix -> matrix **)

let key1 =
  rk1

(** val key2 : matrix -> matrix **)

let key2 =
  rk2

(** val key3 : matrix -> matrix **)

let key3 =
  rk3

(** val key4 : matrix -> matrix **)

let key4 =
  rk4

(** val key5 : matrix -> matrix **)

let key5 =
  rk5

(** val key6 : matrix -> matrix **)

let key6 =
  rk6

(** val key7 : matrix -> matrix **)

let key7 =
  rk7

(** val key8 : matrix -> matrix **)

let key8 =
  rk8

(** val key9 : matrix -> matrix **)

let key9 =
  rk9

(** val key10 : matrix -> matrix **)

let key10 =
  rk10

(** val dec_round1 : matrix -> matrix -> matrix **)

let dec_round1 k s =
  inv_mix_columns (add_round_key (key9 k) (inv_sub_bytes (inv_shift_rows s)))

(** val dec_round2 : matrix -> matrix -> matrix **)

let dec_round2 k s =
  inv_mix_columns (add_round_key (key8 k) (inv_sub_bytes (inv_shift_rows s)))

(** val dec_round3 : matrix -> matrix -> matrix **)

let dec_round3 k s =
  inv_mix_columns (add_round_key (key7 k) (inv_sub_bytes (inv_shift_rows s)))

(** val dec_round4 : matrix -> matrix -> matrix **)

let dec_round4 k s =
  inv_mix_columns (add_round_key (key6 k) (inv_sub_bytes (inv_shift_rows s)))

(** val dec_round5 : matrix -> matrix -> matrix **)

let dec_round5 k s =
  inv_mix_columns (add_round_key (key5 k) (inv_sub_bytes (inv_shift_rows s)))

(** val dec_round6 : matrix -> matrix -> matrix **)

let dec_round6 k s =
  inv_mix_columns (add_round_key (key4 k) (inv_sub_bytes (inv_shift_rows s)))

(** val dec_round7 : matrix -> matrix -> matrix **)

let dec_round7 k s =
  inv_mix_columns (add_round_key (key3 k) (inv_sub_bytes (inv_shift_rows s)))

(** val dec_round8 : matrix -> matrix -> matrix **)

let dec_round8 k s =
  inv_mix_columns (add_round_key (key2 k) (inv_sub_bytes (inv_shift_rows s)))

(** val dec_round9 : matrix -> matrix -> matrix **)

let dec_round9 k s =
  inv_mix_columns (add_round_key (key1 k) (inv_sub_bytes (inv_shift_rows s)))

(** val dec_round10 : matrix -> matrix -> matrix **)

let dec_round10 k s =
  add_round_key (key0 k) (inv_sub_bytes (inv_shift_rows s))

(** val dec_aes : matrix -> matrix -> matrix **)

let dec_aes k c =
  dec_round10 k
    (dec_round9 k
      (dec_round8 k
        (dec_round7 k
          (dec_round6 k (dec_round5 k (dec_round4 k (dec_round3 k (dec_round2 k (dec_round1 k (add_round_key (key10 k) c))))))))))

type blocks =
| B0 of matrix
| BS of matrix * blocks

(** val dec_aes_cbc : matrix -> matrix -> blocks -> blocks **)

let rec dec_aes_cbc key iv = function
| B0 s -> B0 (xor_matrices iv (dec_aes key s))
| BS (s, b) -> let d = dec_aes key s in BS ((xor_matrices iv d), (dec_aes_cbc key s b))
