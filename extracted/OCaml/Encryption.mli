
type bit =
| S0
| S1

type nibble =
| Bits4 of bit * bit * bit * bit

type byte =
| Bits8 of bit * bit * bit * bit * bit * bit * bit * bit

val ms_nibble : byte -> nibble

val ls_nibble : byte -> nibble

val xor_bits : bit -> bit -> bit

val xor_bytes : byte -> byte -> byte

type word =
| Bytes4 of byte * byte * byte * byte

type matrix =
| Bytes16 of byte * byte * byte * byte * byte * byte * byte * byte * byte * byte * 
   byte * byte * byte * byte * byte * byte

val s_box : byte -> byte

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

val shift_rows : matrix -> matrix

val sub_bytes : matrix -> matrix

val xtime : byte -> byte

val mul02 : byte -> byte

val mul03 : byte -> byte

val mix_column_transform : word -> word

val columns_to_matrix : word -> word -> word -> word -> matrix

val mix_columns : matrix -> matrix

val rc : round -> byte

val rcon : round -> word

val xor_words : word -> word -> word

val rcon_word : round -> word -> word

val rot_word : word -> word

val sub_word : word -> word

type key_t =
| Keywords of word * word * word * word

val matrix_to_keyt : matrix -> key_t

val keyt_to_matrix : key_t -> matrix

val first_w_in_rk : round -> word -> word

val rk0 : matrix -> matrix

val rk : round -> key_t -> key_t

val rk1 : matrix -> matrix

val rk2 : matrix -> matrix

val rk3 : matrix -> matrix

val rk4 : matrix -> matrix

val rk5 : matrix -> matrix

val rk6 : matrix -> matrix

val rk7 : matrix -> matrix

val rk8 : matrix -> matrix

val rk9 : matrix -> matrix

val rk10 : matrix -> matrix

val add_round_key : matrix -> matrix -> matrix

val xor_matrices : matrix -> matrix -> matrix

val key0 : matrix -> matrix

val key1 : matrix -> matrix

val key2 : matrix -> matrix

val key3 : matrix -> matrix

val key4 : matrix -> matrix

val key5 : matrix -> matrix

val key6 : matrix -> matrix

val key7 : matrix -> matrix

val key8 : matrix -> matrix

val key9 : matrix -> matrix

val key10 : matrix -> matrix

val enc_round1 : matrix -> matrix -> matrix

val enc_round2 : matrix -> matrix -> matrix

val enc_round3 : matrix -> matrix -> matrix

val enc_round4 : matrix -> matrix -> matrix

val enc_round5 : matrix -> matrix -> matrix

val enc_round6 : matrix -> matrix -> matrix

val enc_round7 : matrix -> matrix -> matrix

val enc_round8 : matrix -> matrix -> matrix

val enc_round9 : matrix -> matrix -> matrix

val enc_round10 : matrix -> matrix -> matrix

val enc_aes : matrix -> matrix -> matrix

type blocks =
| B0 of matrix
| BS of matrix * blocks

val enc_aes_cbc : matrix -> matrix -> blocks -> blocks
