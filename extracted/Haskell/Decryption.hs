module Decryption where

import qualified Prelude

data Bit =
   S0
 | S1

data Nibble =
   Bits4 Bit Bit Bit Bit

data Byte =
   Bits8 Bit Bit Bit Bit Bit Bit Bit Bit

ms_nibble :: Byte -> Nibble
ms_nibble b =
  case b of {
   Bits8 b0 b1 b2 b3 _ _ _ _ -> Bits4 b0 b1 b2 b3}

ls_nibble :: Byte -> Nibble
ls_nibble b =
  case b of {
   Bits8 _ _ _ _ b4 b5 b6 b7 -> Bits4 b4 b5 b6 b7}

xor_bits :: Bit -> Bit -> Bit
xor_bits b1 b2 =
  case b1 of {
   S0 -> b2;
   S1 -> case b2 of {
          S0 -> S1;
          S1 -> S0}}

xor_bytes :: Byte -> Byte -> Byte
xor_bytes b a =
  case b of {
   Bits8 b7 b6 b5 b4 b3 b2 b1 b0 ->
    case a of {
     Bits8 a7 a6 a5 a4 a3 a2 a1 a0 -> Bits8 (xor_bits b7 a7) (xor_bits b6 a6) (xor_bits b5 a5) (xor_bits b4 a4) (xor_bits b3 a3)
      (xor_bits b2 a2) (xor_bits b1 a1) (xor_bits b0 a0)}}

data Word =
   Bytes4 Byte Byte Byte Byte

data Matrix =
   Bytes16 Byte Byte Byte Byte Byte Byte Byte Byte Byte Byte Byte Byte Byte Byte Byte Byte

s_box :: Byte -> Byte
s_box b =
  case ms_nibble b of {
   Bits4 b0 b1 b2 b3 ->
    case b0 of {
     S0 ->
      case b1 of {
       S0 ->
        case b2 of {
         S0 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S0 S0 S1 S1;
                          S1 -> Bits8 S0 S1 S1 S1 S1 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S1 S0 S1 S1 S1;
                          S1 -> Bits8 S0 S1 S1 S1 S1 S0 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S1 S0 S0 S1 S0;
                          S1 -> Bits8 S0 S1 S1 S0 S1 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S1 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S0 S0 S0 S1 S0 S1}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S0 S0 S0 S0;
                          S1 -> Bits8 S0 S0 S0 S0 S0 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S0 S1 S1 S1;
                          S1 -> Bits8 S0 S0 S1 S0 S1 S0 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S1 S1 S1 S1 S0;
                          S1 -> Bits8 S1 S1 S0 S1 S0 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S1 S0 S1 S1;
                          S1 -> Bits8 S0 S1 S1 S1 S0 S1 S1 S0}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S1 S0 S1 S0;
                          S1 -> Bits8 S1 S0 S0 S0 S0 S0 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S1 S0 S0 S1;
                          S1 -> Bits8 S0 S1 S1 S1 S1 S1 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S1 S1 S0 S1 S0;
                          S1 -> Bits8 S0 S1 S0 S1 S1 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S0 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S1 S1 S0 S0 S0 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S1 S1 S0 S1;
                          S1 -> Bits8 S1 S1 S0 S1 S0 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S0 S0 S1 S0;
                          S1 -> Bits8 S1 S0 S1 S0 S1 S1 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S1 S1 S0 S0;
                          S1 -> Bits8 S1 S0 S1 S0 S0 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S1 S0 S0 S1 S0;
                          S1 -> Bits8 S1 S1 S0 S0 S0 S0 S0 S0}}}}}};
         S1 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S0 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S1 S1 S1 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S0 S0 S1 S1;
                          S1 -> Bits8 S0 S0 S1 S0 S0 S1 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S0 S1 S1 S0;
                          S1 -> Bits8 S0 S0 S1 S1 S1 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S1 S0 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S0 S0 S1 S1 S0 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S0 S1 S0 S0;
                          S1 -> Bits8 S1 S0 S1 S0 S0 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S0 S0 S1 S0 S1;
                          S1 -> Bits8 S1 S1 S1 S1 S0 S0 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S1 S0 S0 S0 S1;
                          S1 -> Bits8 S1 S1 S0 S1 S1 S0 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S0 S0 S0 S1;
                          S1 -> Bits8 S0 S0 S0 S1 S0 S1 S0 S1}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S0 S0 S1 S0 S0;
                          S1 -> Bits8 S1 S1 S0 S0 S0 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S0 S0 S1 S1;
                          S1 -> Bits8 S1 S1 S0 S0 S0 S0 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S1 S0 S0 S0;
                          S1 -> Bits8 S1 S0 S0 S1 S0 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S0 S0 S1 S0 S1;
                          S1 -> Bits8 S1 S0 S0 S1 S1 S0 S1 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S0 S0 S1 S1 S1;
                          S1 -> Bits8 S0 S0 S0 S1 S0 S0 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S0 S0 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S1 S0 S0 S0 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S0 S1 S0 S1 S1;
                          S1 -> Bits8 S0 S0 S1 S0 S0 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S0 S0 S1 S0;
                          S1 -> Bits8 S0 S1 S1 S1 S0 S1 S0 S1}}}}}}};
       S1 ->
        case b2 of {
         S0 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S0 S1 S0 S0 S1;
                          S1 -> Bits8 S1 S0 S0 S0 S0 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S1 S1 S0 S0;
                          S1 -> Bits8 S0 S0 S0 S1 S1 S0 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S1 S0 S1 S1;
                          S1 -> Bits8 S0 S1 S1 S0 S1 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S1 S0 S1 S0;
                          S1 -> Bits8 S1 S0 S1 S0 S0 S0 S0 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S0 S0 S1 S0;
                          S1 -> Bits8 S0 S0 S1 S1 S1 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S1 S0 S1 S1 S0;
                          S1 -> Bits8 S1 S0 S1 S1 S0 S0 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S1 S0 S0 S1;
                          S1 -> Bits8 S1 S1 S1 S0 S0 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S1 S1 S1 S1;
                          S1 -> Bits8 S1 S0 S0 S0 S0 S1 S0 S0}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S0 S0 S1 S1;
                          S1 -> Bits8 S1 S1 S0 S1 S0 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S0 S0 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S1 S0 S1 S1 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S0 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S1 S1 S1 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S0 S0 S0 S1;
                          S1 -> Bits8 S0 S1 S0 S1 S1 S0 S1 S1}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S1 S0 S1 S0;
                          S1 -> Bits8 S1 S1 S0 S0 S1 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S1 S1 S1 S0;
                          S1 -> Bits8 S0 S0 S1 S1 S1 S0 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S1 S0 S1 S0;
                          S1 -> Bits8 S0 S1 S0 S0 S1 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S1 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S0 S0 S1 S1 S1 S1}}}}}};
         S1 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S1 S0 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S1 S0 S1 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S1 S0 S1 S0;
                          S1 -> Bits8 S1 S1 S1 S1 S1 S0 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S0 S0 S1 S1;
                          S1 -> Bits8 S0 S1 S0 S0 S1 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S0 S0 S1 S1;
                          S1 -> Bits8 S1 S0 S0 S0 S0 S1 S0 S1}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S0 S1 S0 S1;
                          S1 -> Bits8 S1 S1 S1 S1 S1 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S0 S0 S0 S1 S0;
                          S1 -> Bits8 S0 S1 S1 S1 S1 S1 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S0 S0 S0 S0;
                          S1 -> Bits8 S0 S0 S1 S1 S1 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S1 S1 S1 S1;
                          S1 -> Bits8 S1 S0 S1 S0 S1 S0 S0 S0}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S0 S0 S0 S1;
                          S1 -> Bits8 S1 S0 S1 S0 S0 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S0 S0 S0 S0;
                          S1 -> Bits8 S1 S0 S0 S0 S1 S1 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S0 S0 S1 S0;
                          S1 -> Bits8 S1 S0 S0 S1 S1 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S1 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S1 S1 S0 S1 S0 S1}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S1 S1 S0 S0;
                          S1 -> Bits8 S1 S0 S1 S1 S0 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S1 S1 S0 S1 S0;
                          S1 -> Bits8 S0 S0 S1 S0 S0 S0 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S0 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S1 S1 S1 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S1 S0 S0 S1 S1;
                          S1 -> Bits8 S1 S1 S0 S1 S0 S0 S1 S0}}}}}}}};
     S1 ->
      case b1 of {
       S0 ->
        case b2 of {
         S0 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S1 S1 S0 S1;
                          S1 -> Bits8 S0 S0 S0 S0 S1 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S0 S0 S1 S1;
                          S1 -> Bits8 S1 S1 S1 S0 S1 S1 S0 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S1 S1 S1 S1;
                          S1 -> Bits8 S1 S0 S0 S1 S0 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S0 S1 S0 S0;
                          S1 -> Bits8 S0 S0 S0 S1 S0 S1 S1 S1}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S0 S1 S0 S0;
                          S1 -> Bits8 S1 S0 S1 S0 S0 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S1 S1 S1 S1 S0;
                          S1 -> Bits8 S0 S0 S1 S1 S1 S1 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S0 S1 S0 S0;
                          S1 -> Bits8 S0 S1 S0 S1 S1 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S1 S0 S0 S1;
                          S1 -> Bits8 S0 S1 S1 S1 S0 S0 S1 S1}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S0 S0 S0 S0;
                          S1 -> Bits8 S1 S0 S0 S0 S0 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S1 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S0 S1 S1 S1 S0 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S0 S0 S1 S0;
                          S1 -> Bits8 S0 S0 S1 S0 S1 S0 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S0 S0 S0 S0;
                          S1 -> Bits8 S1 S0 S0 S0 S1 S0 S0 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S0 S1 S1 S0;
                          S1 -> Bits8 S1 S1 S1 S0 S1 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S1 S0 S0 S0;
                          S1 -> Bits8 S0 S0 S0 S1 S0 S1 S0 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S1 S1 S1 S1 S0;
                          S1 -> Bits8 S0 S1 S0 S1 S1 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S0 S1 S0 S1 S1;
                          S1 -> Bits8 S1 S1 S0 S1 S1 S0 S1 S1}}}}}};
         S1 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S0 S0 S0 S0 S0;
                          S1 -> Bits8 S0 S0 S1 S1 S0 S0 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S1 S0 S1 S0;
                          S1 -> Bits8 S0 S0 S0 S0 S1 S0 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S1 S0 S0 S1;
                          S1 -> Bits8 S0 S0 S0 S0 S0 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S0 S1 S0 S0;
                          S1 -> Bits8 S0 S1 S0 S1 S1 S1 S0 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S0 S0 S1 S0;
                          S1 -> Bits8 S1 S1 S0 S1 S0 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S1 S1 S0 S0;
                          S1 -> Bits8 S0 S1 S1 S0 S0 S0 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S0 S0 S0 S1;
                          S1 -> Bits8 S1 S0 S0 S1 S0 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S0 S0 S1 S0 S0;
                          S1 -> Bits8 S0 S1 S1 S1 S1 S0 S0 S1}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S0 S0 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S0 S0 S1 S0 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S0 S1 S1 S1;
                          S1 -> Bits8 S0 S1 S1 S0 S1 S1 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S0 S1 S1 S0 S1;
                          S1 -> Bits8 S1 S1 S0 S1 S0 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S1 S1 S1 S0;
                          S1 -> Bits8 S1 S0 S1 S0 S1 S0 S0 S1}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S1 S1 S0 S0;
                          S1 -> Bits8 S0 S1 S0 S1 S0 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S1 S0 S1 S0 S0;
                          S1 -> Bits8 S1 S1 S1 S0 S1 S0 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S0 S1 S0 S1;
                          S1 -> Bits8 S0 S1 S1 S1 S1 S0 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S1 S1 S1 S0;
                          S1 -> Bits8 S0 S0 S0 S0 S1 S0 S0 S0}}}}}}};
       S1 ->
        case b2 of {
         S0 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S1 S0 S1 S0;
                          S1 -> Bits8 S0 S1 S1 S1 S1 S0 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S0 S1 S0 S1;
                          S1 -> Bits8 S0 S0 S1 S0 S1 S1 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S1 S1 S0 S0;
                          S1 -> Bits8 S1 S0 S1 S0 S0 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S0 S1 S0 S0;
                          S1 -> Bits8 S1 S1 S0 S0 S0 S1 S1 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S0 S1 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S0 S1 S1 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S1 S0 S1 S0 S0;
                          S1 -> Bits8 S0 S0 S0 S1 S1 S1 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S1 S0 S1 S1;
                          S1 -> Bits8 S1 S0 S1 S1 S1 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S0 S1 S0 S1 S1;
                          S1 -> Bits8 S1 S0 S0 S0 S1 S0 S1 S0}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S1 S0 S0 S0 S0;
                          S1 -> Bits8 S0 S0 S1 S1 S1 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S0 S1 S0 S1;
                          S1 -> Bits8 S0 S1 S1 S0 S0 S1 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S1 S0 S0 S0;
                          S1 -> Bits8 S0 S0 S0 S0 S0 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S1 S0 S1 S1 S0;
                          S1 -> Bits8 S0 S0 S0 S0 S1 S1 S1 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S0 S0 S0 S1;
                          S1 -> Bits8 S0 S0 S1 S1 S0 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S0 S1 S1 S1;
                          S1 -> Bits8 S1 S0 S1 S1 S1 S0 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S0 S0 S1 S1 S0;
                          S1 -> Bits8 S1 S1 S0 S0 S0 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S1 S1 S0 S1;
                          S1 -> Bits8 S1 S0 S0 S1 S1 S1 S1 S0}}}}}};
         S1 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S0 S0 S0 S0 S1;
                          S1 -> Bits8 S1 S1 S1 S1 S1 S0 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S1 S0 S0 S0;
                          S1 -> Bits8 S0 S0 S0 S1 S0 S0 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S1 S0 S0 S1;
                          S1 -> Bits8 S1 S1 S0 S1 S1 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S0 S1 S1 S1 S0;
                          S1 -> Bits8 S1 S0 S0 S1 S0 S1 S0 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S1 S0 S1 S1;
                          S1 -> Bits8 S0 S0 S0 S1 S1 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S0 S0 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S1 S0 S1 S0 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S1 S1 S1 S0;
                          S1 -> Bits8 S0 S1 S0 S1 S0 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S1 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S0 S1 S1 S1 S1 S1}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S0 S1 S1 S0 S0;
                          S1 -> Bits8 S1 S0 S1 S0 S0 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S0 S1 S0 S0 S1;
                          S1 -> Bits8 S0 S0 S0 S0 S1 S1 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S1 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S1 S0 S0 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S0 S0 S1 S0;
                          S1 -> Bits8 S0 S1 S1 S0 S1 S0 S0 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S0 S0 S0 S1;
                          S1 -> Bits8 S1 S0 S0 S1 S1 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S1 S1 S0 S1;
                          S1 -> Bits8 S0 S0 S0 S0 S1 S1 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S0 S0 S0 S0;
                          S1 -> Bits8 S0 S1 S0 S1 S0 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S1 S0 S1 S1;
                          S1 -> Bits8 S0 S0 S0 S1 S0 S1 S1 S0}}}}}}}}}}

inv_s_box :: Byte -> Byte
inv_s_box b =
  case ms_nibble b of {
   Bits4 b0 b1 b2 b3 ->
    case b0 of {
     S0 ->
      case b1 of {
       S0 ->
        case b2 of {
         S0 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S0 S0 S1 S0;
                          S1 -> Bits8 S0 S0 S0 S0 S1 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S1 S0 S1 S0;
                          S1 -> Bits8 S1 S1 S0 S1 S0 S1 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S0 S0 S0 S0;
                          S1 -> Bits8 S0 S0 S1 S1 S0 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S0 S1 S0 S1;
                          S1 -> Bits8 S0 S0 S1 S1 S1 S0 S0 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S1 S1 S1 S1;
                          S1 -> Bits8 S0 S1 S0 S0 S0 S0 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S0 S0 S1 S1;
                          S1 -> Bits8 S1 S0 S0 S1 S1 S1 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S0 S0 S0 S0 S1;
                          S1 -> Bits8 S1 S1 S1 S1 S0 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S1 S0 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S1 S1 S1 S0 S1 S1}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S1 S1 S1 S0 S0;
                          S1 -> Bits8 S1 S1 S1 S0 S0 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S1 S0 S0 S1;
                          S1 -> Bits8 S1 S0 S0 S0 S0 S0 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S1 S0 S1 S1;
                          S1 -> Bits8 S0 S0 S1 S0 S1 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S1 S1 S1 S1 S1;
                          S1 -> Bits8 S1 S0 S0 S0 S0 S1 S1 S1}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S0 S1 S0 S0;
                          S1 -> Bits8 S1 S0 S0 S0 S1 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S0 S0 S1 S1;
                          S1 -> Bits8 S0 S1 S0 S0 S0 S1 S0 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S0 S1 S0 S0;
                          S1 -> Bits8 S1 S1 S0 S1 S1 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S0 S1 S0 S0 S1;
                          S1 -> Bits8 S1 S1 S0 S0 S1 S0 S1 S1}}}}}};
         S1 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S0 S1 S0 S0;
                          S1 -> Bits8 S0 S1 S1 S1 S1 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S0 S1 S0 S0;
                          S1 -> Bits8 S0 S0 S1 S1 S0 S0 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S0 S1 S1 S0;
                          S1 -> Bits8 S1 S1 S0 S0 S0 S0 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S0 S0 S1 S1;
                          S1 -> Bits8 S0 S0 S1 S1 S1 S1 S0 S1}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S0 S1 S1 S1 S0;
                          S1 -> Bits8 S0 S1 S0 S0 S1 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S0 S1 S0 S1;
                          S1 -> Bits8 S0 S0 S0 S0 S1 S0 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S0 S0 S1 S0;
                          S1 -> Bits8 S1 S1 S1 S1 S1 S0 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S0 S0 S1 S1;
                          S1 -> Bits8 S0 S1 S0 S0 S1 S1 S1 S0}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S0 S1 S0 S0 S0;
                          S1 -> Bits8 S0 S0 S1 S0 S1 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S0 S0 S0 S1;
                          S1 -> Bits8 S0 S1 S1 S0 S0 S1 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S1 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S0 S1 S1 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S0 S1 S0 S0;
                          S1 -> Bits8 S1 S0 S1 S1 S0 S0 S1 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S1 S0 S1 S1 S0;
                          S1 -> Bits8 S0 S1 S0 S1 S1 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S0 S0 S1 S0;
                          S1 -> Bits8 S0 S1 S0 S0 S1 S0 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S1 S1 S0 S1;
                          S1 -> Bits8 S1 S0 S0 S0 S1 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S1 S0 S0 S0 S1;
                          S1 -> Bits8 S0 S0 S1 S0 S0 S1 S0 S1}}}}}}};
       S1 ->
        case b2 of {
         S0 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S1 S0 S0 S1 S0;
                          S1 -> Bits8 S1 S1 S1 S1 S1 S0 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S1 S0 S1 S1 S0;
                          S1 -> Bits8 S0 S1 S1 S0 S0 S1 S0 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S0 S0 S1 S1 S0;
                          S1 -> Bits8 S0 S1 S1 S0 S1 S0 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S1 S0 S0 S0;
                          S1 -> Bits8 S0 S0 S0 S1 S0 S1 S1 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S1 S0 S1 S0 S0;
                          S1 -> Bits8 S1 S0 S1 S0 S0 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S1 S1 S0 S0;
                          S1 -> Bits8 S1 S1 S0 S0 S1 S1 S0 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S1 S1 S0 S1;
                          S1 -> Bits8 S0 S1 S1 S0 S0 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S0 S1 S1 S0;
                          S1 -> Bits8 S1 S0 S0 S1 S0 S0 S1 S0}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S1 S1 S0 S0;
                          S1 -> Bits8 S0 S1 S1 S1 S0 S0 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S1 S0 S0 S0;
                          S1 -> Bits8 S0 S1 S0 S1 S0 S0 S0 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S1 S1 S1 S0 S1;
                          S1 -> Bits8 S1 S1 S1 S0 S1 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S1 S0 S0 S1;
                          S1 -> Bits8 S1 S1 S0 S1 S1 S0 S1 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S1 S1 S1 S0;
                          S1 -> Bits8 S0 S0 S0 S1 S0 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S0 S1 S1 S0;
                          S1 -> Bits8 S0 S1 S0 S1 S0 S1 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S0 S1 S1 S1;
                          S1 -> Bits8 S1 S0 S0 S0 S1 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S1 S1 S0 S1;
                          S1 -> Bits8 S1 S0 S0 S0 S0 S1 S0 S0}}}}}};
         S1 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S0 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S0 S1 S1 S0 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S1 S0 S1 S1;
                          S1 -> Bits8 S0 S0 S0 S0 S0 S0 S0 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S0 S1 S1 S0 S0;
                          S1 -> Bits8 S1 S0 S1 S1 S1 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S1 S0 S0 S1 S1;
                          S1 -> Bits8 S0 S0 S0 S0 S1 S0 S1 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S1 S0 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S1 S0 S0 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S1 S0 S0 S0;
                          S1 -> Bits8 S0 S0 S0 S0 S0 S1 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S1 S0 S0 S0;
                          S1 -> Bits8 S1 S0 S1 S1 S0 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S0 S1 S0 S1;
                          S1 -> Bits8 S0 S0 S0 S0 S0 S1 S1 S0}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S1 S0 S0 S0 S0;
                          S1 -> Bits8 S0 S0 S1 S0 S1 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S1 S1 S1 S0;
                          S1 -> Bits8 S1 S0 S0 S0 S1 S1 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S1 S0 S1 S0;
                          S1 -> Bits8 S0 S0 S1 S1 S1 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S0 S1 S1 S1 S1;
                          S1 -> Bits8 S0 S0 S0 S0 S0 S0 S1 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S0 S0 S0 S1;
                          S1 -> Bits8 S1 S0 S1 S0 S1 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S1 S1 S0 S1;
                          S1 -> Bits8 S0 S0 S0 S0 S0 S0 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S0 S0 S0 S0 S1;
                          S1 -> Bits8 S0 S0 S0 S1 S0 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S0 S1 S0 S1 S0;
                          S1 -> Bits8 S0 S1 S1 S0 S1 S0 S1 S1}}}}}}}};
     S1 ->
      case b1 of {
       S0 ->
        case b2 of {
         S0 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S1 S0 S1 S0;
                          S1 -> Bits8 S1 S0 S0 S1 S0 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S0 S0 S0 S1;
                          S1 -> Bits8 S0 S1 S0 S0 S0 S0 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S1 S1 S1 S1;
                          S1 -> Bits8 S0 S1 S1 S0 S0 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S1 S1 S1 S0 S0;
                          S1 -> Bits8 S1 S1 S1 S0 S1 S0 S1 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S0 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S1 S1 S0 S0 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S1 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S0 S0 S1 S1 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S1 S0 S0 S0 S0;
                          S1 -> Bits8 S1 S0 S1 S1 S0 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S0 S0 S1 S1 S0;
                          S1 -> Bits8 S0 S1 S1 S1 S0 S0 S1 S1}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S0 S1 S1 S0;
                          S1 -> Bits8 S1 S0 S1 S0 S1 S1 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S1 S0 S1 S0 S0;
                          S1 -> Bits8 S0 S0 S1 S0 S0 S0 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S0 S0 S1 S1 S1;
                          S1 -> Bits8 S1 S0 S1 S0 S1 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S0 S1 S0 S1;
                          S1 -> Bits8 S1 S0 S0 S0 S0 S1 S0 S1}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S0 S0 S0 S1 S0;
                          S1 -> Bits8 S1 S1 S1 S1 S1 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S0 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S1 S0 S1 S0 S0 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S1 S1 S0 S0;
                          S1 -> Bits8 S0 S1 S1 S1 S0 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S1 S1 S1 S1 S1;
                          S1 -> Bits8 S0 S1 S1 S0 S1 S1 S1 S0}}}}}};
         S1 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S0 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S1 S1 S0 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S1 S0 S1 S0;
                          S1 -> Bits8 S0 S1 S1 S1 S0 S0 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S1 S1 S0 S1;
                          S1 -> Bits8 S0 S0 S1 S0 S1 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S0 S1 S0 S1;
                          S1 -> Bits8 S1 S0 S0 S0 S1 S0 S0 S1}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S1 S1 S1 S1;
                          S1 -> Bits8 S1 S0 S1 S1 S0 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S0 S0 S1 S0;
                          S1 -> Bits8 S0 S0 S0 S0 S1 S1 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S1 S0 S1 S0;
                          S1 -> Bits8 S0 S0 S0 S1 S1 S0 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S1 S1 S1 S0;
                          S1 -> Bits8 S0 S0 S0 S1 S1 S0 S1 S1}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S1 S1 S1 S0 S0;
                          S1 -> Bits8 S0 S1 S0 S1 S0 S1 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S1 S1 S1 S0;
                          S1 -> Bits8 S0 S1 S0 S0 S1 S0 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S0 S1 S1 S0;
                          S1 -> Bits8 S1 S1 S0 S1 S0 S0 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S1 S1 S0 S0 S1;
                          S1 -> Bits8 S0 S0 S1 S0 S0 S0 S0 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S1 S0 S1 S0;
                          S1 -> Bits8 S1 S1 S0 S1 S1 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S0 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S1 S1 S1 S1 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S1 S1 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S0 S0 S1 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S1 S0 S1 S0;
                          S1 -> Bits8 S1 S1 S1 S1 S0 S1 S0 S0}}}}}}};
       S1 ->
        case b2 of {
         S0 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S1 S1 S1 S1;
                          S1 -> Bits8 S1 S1 S0 S1 S1 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S1 S0 S0 S0;
                          S1 -> Bits8 S0 S0 S1 S1 S0 S0 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S0 S1 S0 S0 S0;
                          S1 -> Bits8 S0 S0 S0 S0 S0 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S0 S1 S1 S1;
                          S1 -> Bits8 S0 S0 S1 S1 S0 S0 S0 S1}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S0 S0 S0 S1;
                          S1 -> Bits8 S0 S0 S0 S1 S0 S0 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S0 S0 S0 S0;
                          S1 -> Bits8 S0 S1 S0 S1 S1 S0 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S0 S1 S1 S1;
                          S1 -> Bits8 S1 S0 S0 S0 S0 S0 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S0 S1 S1 S0 S0;
                          S1 -> Bits8 S0 S1 S0 S1 S1 S1 S1 S1}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S0 S0 S0 S0 S0;
                          S1 -> Bits8 S0 S1 S0 S1 S0 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S1 S1 S1 S1 S1;
                          S1 -> Bits8 S1 S0 S1 S0 S1 S0 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S1 S0 S0 S1;
                          S1 -> Bits8 S1 S0 S1 S1 S0 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S0 S1 S0 S1 S0;
                          S1 -> Bits8 S0 S0 S0 S0 S1 S1 S0 S1}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S0 S1 S1 S0 S1;
                          S1 -> Bits8 S1 S1 S1 S0 S0 S1 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S1 S1 S1 S1 S0 S1 S0;
                          S1 -> Bits8 S1 S0 S0 S1 S1 S1 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S0 S0 S1 S1;
                          S1 -> Bits8 S1 S1 S0 S0 S1 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S1 S1 S0 S0;
                          S1 -> Bits8 S1 S1 S1 S0 S1 S1 S1 S1}}}}}};
         S1 ->
          case b3 of {
           S0 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S0 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S1 S0 S0 S0 S0 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S1 S1 S1 S0 S1 S1;
                          S1 -> Bits8 S0 S1 S0 S0 S1 S1 S0 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S0 S1 S1 S1 S0;
                          S1 -> Bits8 S0 S0 S1 S0 S1 S0 S1 S0};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S1 S0 S1 S0 S1;
                          S1 -> Bits8 S1 S0 S1 S1 S0 S0 S0 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S0 S1 S0 S0 S0;
                          S1 -> Bits8 S1 S1 S1 S0 S1 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S1 S0 S1 S1;
                          S1 -> Bits8 S0 S0 S1 S1 S1 S1 S0 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S0 S0 S0 S1 S1;
                          S1 -> Bits8 S0 S1 S0 S1 S0 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S0 S0 S1 S1 S0 S0 S1;
                          S1 -> Bits8 S0 S1 S1 S0 S0 S0 S0 S1}}}}};
           S1 ->
            case ls_nibble b of {
             Bits4 b4 b5 b6 b7 ->
              case b4 of {
               S0 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S0 S1 S1 S1;
                          S1 -> Bits8 S0 S0 S1 S0 S1 S0 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S0 S0 S1 S0 S0;
                          S1 -> Bits8 S0 S1 S1 S1 S1 S1 S1 S0}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S0 S1 S1 S1 S0 S1 S0;
                          S1 -> Bits8 S0 S1 S1 S1 S0 S1 S1 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S1 S1 S0 S1 S0 S1 S1 S0;
                          S1 -> Bits8 S0 S0 S1 S0 S0 S1 S1 S0}}};
               S1 ->
                case b5 of {
                 S0 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S1 S1 S1 S0 S0 S0 S0 S1;
                          S1 -> Bits8 S0 S1 S1 S0 S1 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S1 S0 S1 S0 S0;
                          S1 -> Bits8 S0 S1 S1 S0 S0 S0 S1 S1}};
                 S1 ->
                  case b6 of {
                   S0 -> case b7 of {
                          S0 -> Bits8 S0 S1 S0 S1 S0 S1 S0 S1;
                          S1 -> Bits8 S0 S0 S1 S0 S0 S0 S0 S1};
                   S1 -> case b7 of {
                          S0 -> Bits8 S0 S0 S0 S0 S1 S1 S0 S0;
                          S1 -> Bits8 S0 S1 S1 S1 S1 S1 S0 S1}}}}}}}}}}

data Round =
   R1
 | R2
 | R3
 | R4
 | R5
 | R6
 | R7
 | R8
 | R9
 | R10

inv_shift_rows :: Matrix -> Matrix
inv_shift_rows state =
  case state of {
   Bytes16 r0c0 r0c1 r0c2 r0c3 r1c0 r1c1 r1c2 r1c3 r2c0 r2c1 r2c2 r2c3 r3c0 r3c1 r3c2 r3c3 -> Bytes16 r0c0 r0c1 r0c2 r0c3 r1c3 r1c0 r1c1
    r1c2 r2c2 r2c3 r2c0 r2c1 r3c1 r3c2 r3c3 r3c0}

inv_sub_bytes :: Matrix -> Matrix
inv_sub_bytes state =
  case state of {
   Bytes16 r0c0 r0c1 r0c2 r0c3 r1c0 r1c1 r1c2 r1c3 r2c0 r2c1 r2c2 r2c3 r3c0 r3c1 r3c2 r3c3 -> Bytes16 (inv_s_box r0c0) (inv_s_box r0c1)
    (inv_s_box r0c2) (inv_s_box r0c3) (inv_s_box r1c0) (inv_s_box r1c1) (inv_s_box r1c2) (inv_s_box r1c3) (inv_s_box r2c0)
    (inv_s_box r2c1) (inv_s_box r2c2) (inv_s_box r2c3) (inv_s_box r3c0) (inv_s_box r3c1) (inv_s_box r3c2) (inv_s_box r3c3)}

xtime :: Byte -> Byte
xtime b =
  case b of {
   Bits8 b7 b6 b5 b4 b3 b2 b1 b0 ->
    case b7 of {
     S0 -> Bits8 b6 b5 b4 b3 b2 b1 b0 S0;
     S1 -> xor_bytes (Bits8 b6 b5 b4 b3 b2 b1 b0 S0) (Bits8 S0 S0 S0 S1 S1 S0 S1 S1)}}

mul02 :: Byte -> Byte
mul02 =
  xtime

mul09 :: Byte -> Byte
mul09 b =
  xor_bytes b (mul02 (mul02 (mul02 b)))

mul0b :: Byte -> Byte
mul0b b =
  xor_bytes b (xor_bytes (mul02 b) (mul02 (mul02 (mul02 b))))

mul0d :: Byte -> Byte
mul0d b =
  xor_bytes b (xor_bytes (mul02 (mul02 b)) (mul02 (mul02 (mul02 b))))

mul0e :: Byte -> Byte
mul0e b =
  xor_bytes (mul02 b) (xor_bytes (mul02 (mul02 b)) (mul02 (mul02 (mul02 b))))

inv_mix_column_transform :: Word -> Word
inv_mix_column_transform column =
  case column of {
   Bytes4 a' b' c' d' ->
    let {a'' = xor_bytes (xor_bytes (xor_bytes (mul0e a') (mul0b b')) (mul0d c')) (mul09 d')} in
    let {b'' = xor_bytes (xor_bytes (xor_bytes (mul09 a') (mul0e b')) (mul0b c')) (mul0d d')} in
    let {c'' = xor_bytes (xor_bytes (xor_bytes (mul0d a') (mul09 b')) (mul0e c')) (mul0b d')} in
    let {d'' = xor_bytes (xor_bytes (xor_bytes (mul0b a') (mul0d b')) (mul09 c')) (mul0e d')} in Bytes4 a'' b'' c'' d''}

columns_to_matrix :: Word -> Word -> Word -> Word -> Matrix
columns_to_matrix c0 c1 c2 c3 =
  case c0 of {
   Bytes4 c00 c10 c20 c30 ->
    case c1 of {
     Bytes4 c01 c11 c21 c31 ->
      case c2 of {
       Bytes4 c02 c12 c22 c32 ->
        case c3 of {
         Bytes4 c03 c13 c23 c33 -> Bytes16 c00 c01 c02 c03 c10 c11 c12 c13 c20 c21 c22 c23 c30 c31 c32 c33}}}}

inv_mix_columns :: Matrix -> Matrix
inv_mix_columns state =
  case state of {
   Bytes16 s00 s01 s02 s03 s10 s11 s12 s13 s20 s21 s22 s23 s30 s31 s32 s33 ->
    let {ncol0 = inv_mix_column_transform (Bytes4 s00 s10 s20 s30)} in
    let {ncol1 = inv_mix_column_transform (Bytes4 s01 s11 s21 s31)} in
    let {ncol2 = inv_mix_column_transform (Bytes4 s02 s12 s22 s32)} in
    let {ncol3 = inv_mix_column_transform (Bytes4 s03 s13 s23 s33)} in columns_to_matrix ncol0 ncol1 ncol2 ncol3}

rc :: Round -> Byte
rc i =
  case i of {
   R1 -> Bits8 S0 S0 S0 S0 S0 S0 S0 S1;
   R2 -> Bits8 S0 S0 S0 S0 S0 S0 S1 S0;
   R3 -> Bits8 S0 S0 S0 S0 S0 S1 S0 S0;
   R4 -> Bits8 S0 S0 S0 S0 S1 S0 S0 S0;
   R5 -> Bits8 S0 S0 S0 S1 S0 S0 S0 S0;
   R6 -> Bits8 S0 S0 S1 S0 S0 S0 S0 S0;
   R7 -> Bits8 S0 S1 S0 S0 S0 S0 S0 S0;
   R8 -> Bits8 S1 S0 S0 S0 S0 S0 S0 S0;
   R9 -> Bits8 S0 S0 S0 S1 S1 S0 S1 S1;
   R10 -> Bits8 S0 S0 S1 S1 S0 S1 S1 S0}

rcon :: Round -> Word
rcon i =
  Bytes4 (rc i) (Bits8 S0 S0 S0 S0 S0 S0 S0 S0) (Bits8 S0 S0 S0 S0 S0 S0 S0 S0) (Bits8 S0 S0 S0 S0 S0 S0 S0 S0)

xor_words :: Word -> Word -> Word
xor_words w1 w2 =
  case w1 of {
   Bytes4 b0 b1 b2 b3 ->
    case w2 of {
     Bytes4 a0 a1 a2 a3 -> Bytes4 (xor_bytes b0 a0) (xor_bytes b1 a1) (xor_bytes b2 a2) (xor_bytes b3 a3)}}

rcon_word :: Round -> Word -> Word
rcon_word i w =
  xor_words w (rcon i)

rot_word :: Word -> Word
rot_word w =
  case w of {
   Bytes4 b0 b1 b2 b3 -> Bytes4 b1 b2 b3 b0}

sub_word :: Word -> Word
sub_word w =
  case w of {
   Bytes4 b0 b1 b2 b3 -> Bytes4 (s_box b0) (s_box b1) (s_box b2) (s_box b3)}

data Key_t =
   Keywords Word Word Word Word

matrix_to_keyt :: Matrix -> Key_t
matrix_to_keyt k =
  case k of {
   Bytes16 b11 b12 b13 b14 b21 b22 b23 b24 b31 b32 b33 b34 b41 b42 b43 b44 -> Keywords (Bytes4 b11 b12 b13 b14) (Bytes4 b21 b22 b23 b24)
    (Bytes4 b31 b32 b33 b34) (Bytes4 b41 b42 b43 b44)}

keyt_to_matrix :: Key_t -> Matrix
keyt_to_matrix k =
  case k of {
   Keywords w1 w2 w3 w4 ->
    case w1 of {
     Bytes4 b11 b12 b13 b14 ->
      case w2 of {
       Bytes4 b21 b22 b23 b24 ->
        case w3 of {
         Bytes4 b31 b32 b33 b34 ->
          case w4 of {
           Bytes4 b41 b42 b43 b44 -> Bytes16 b11 b12 b13 b14 b21 b22 b23 b24 b31 b32 b33 b34 b41 b42 b43 b44}}}}}

first_w_in_rk :: Round -> Word -> Word
first_w_in_rk i w =
  rot_word (sub_word (rcon_word i w))

rk0 :: Matrix -> Matrix
rk0 k =
  k

rk :: Round -> Key_t -> Key_t
rk i k =
  case k of {
   Keywords w1 w2 w3 w4 -> Keywords (xor_words (first_w_in_rk i w4) w1) (xor_words (xor_words (first_w_in_rk i w4) w1) w2)
    (xor_words (xor_words (xor_words (first_w_in_rk i w4) w1) w2) w3)
    (xor_words (xor_words (xor_words (xor_words (first_w_in_rk i w4) w1) w2) w3) w4)}

rk1 :: Matrix -> Matrix
rk1 k =
  keyt_to_matrix (rk R1 (matrix_to_keyt k))

rk2 :: Matrix -> Matrix
rk2 k =
  keyt_to_matrix (rk R2 (matrix_to_keyt (rk1 k)))

rk3 :: Matrix -> Matrix
rk3 k =
  keyt_to_matrix (rk R3 (matrix_to_keyt (rk2 k)))

rk4 :: Matrix -> Matrix
rk4 k =
  keyt_to_matrix (rk R4 (matrix_to_keyt (rk3 k)))

rk5 :: Matrix -> Matrix
rk5 k =
  keyt_to_matrix (rk R5 (matrix_to_keyt (rk4 k)))

rk6 :: Matrix -> Matrix
rk6 k =
  keyt_to_matrix (rk R6 (matrix_to_keyt (rk5 k)))

rk7 :: Matrix -> Matrix
rk7 k =
  keyt_to_matrix (rk R7 (matrix_to_keyt (rk6 k)))

rk8 :: Matrix -> Matrix
rk8 k =
  keyt_to_matrix (rk R8 (matrix_to_keyt (rk7 k)))

rk9 :: Matrix -> Matrix
rk9 k =
  keyt_to_matrix (rk R9 (matrix_to_keyt (rk8 k)))

rk10 :: Matrix -> Matrix
rk10 k =
  keyt_to_matrix (rk R10 (matrix_to_keyt (rk9 k)))

add_round_key :: Matrix -> Matrix -> Matrix
add_round_key k state =
  case k of {
   Bytes16 k00 k01 k02 k03 k10 k11 k12 k13 k20 k21 k22 k23 k30 k31 k32 k33 ->
    case state of {
     Bytes16 s00 s01 s02 s03 s10 s11 s12 s13 s20 s21 s22 s23 s30 s31 s32 s33 -> Bytes16 (xor_bytes k00 s00) (xor_bytes k01 s01)
      (xor_bytes k02 s02) (xor_bytes k03 s03) (xor_bytes k10 s10) (xor_bytes k11 s11) (xor_bytes k12 s12) (xor_bytes k13 s13)
      (xor_bytes k20 s20) (xor_bytes k21 s21) (xor_bytes k22 s22) (xor_bytes k23 s23) (xor_bytes k30 s30) (xor_bytes k31 s31)
      (xor_bytes k32 s32) (xor_bytes k33 s33)}}

xor_matrices :: Matrix -> Matrix -> Matrix
xor_matrices =
  add_round_key

key0 :: Matrix -> Matrix
key0 =
  rk0

key1 :: Matrix -> Matrix
key1 =
  rk1

key2 :: Matrix -> Matrix
key2 =
  rk2

key3 :: Matrix -> Matrix
key3 =
  rk3

key4 :: Matrix -> Matrix
key4 =
  rk4

key5 :: Matrix -> Matrix
key5 =
  rk5

key6 :: Matrix -> Matrix
key6 =
  rk6

key7 :: Matrix -> Matrix
key7 =
  rk7

key8 :: Matrix -> Matrix
key8 =
  rk8

key9 :: Matrix -> Matrix
key9 =
  rk9

key10 :: Matrix -> Matrix
key10 =
  rk10

dec_round1 :: Matrix -> Matrix -> Matrix
dec_round1 k s =
  inv_mix_columns (add_round_key (key9 k) (inv_sub_bytes (inv_shift_rows s)))

dec_round2 :: Matrix -> Matrix -> Matrix
dec_round2 k s =
  inv_mix_columns (add_round_key (key8 k) (inv_sub_bytes (inv_shift_rows s)))

dec_round3 :: Matrix -> Matrix -> Matrix
dec_round3 k s =
  inv_mix_columns (add_round_key (key7 k) (inv_sub_bytes (inv_shift_rows s)))

dec_round4 :: Matrix -> Matrix -> Matrix
dec_round4 k s =
  inv_mix_columns (add_round_key (key6 k) (inv_sub_bytes (inv_shift_rows s)))

dec_round5 :: Matrix -> Matrix -> Matrix
dec_round5 k s =
  inv_mix_columns (add_round_key (key5 k) (inv_sub_bytes (inv_shift_rows s)))

dec_round6 :: Matrix -> Matrix -> Matrix
dec_round6 k s =
  inv_mix_columns (add_round_key (key4 k) (inv_sub_bytes (inv_shift_rows s)))

dec_round7 :: Matrix -> Matrix -> Matrix
dec_round7 k s =
  inv_mix_columns (add_round_key (key3 k) (inv_sub_bytes (inv_shift_rows s)))

dec_round8 :: Matrix -> Matrix -> Matrix
dec_round8 k s =
  inv_mix_columns (add_round_key (key2 k) (inv_sub_bytes (inv_shift_rows s)))

dec_round9 :: Matrix -> Matrix -> Matrix
dec_round9 k s =
  inv_mix_columns (add_round_key (key1 k) (inv_sub_bytes (inv_shift_rows s)))

dec_round10 :: Matrix -> Matrix -> Matrix
dec_round10 k s =
  add_round_key (key0 k) (inv_sub_bytes (inv_shift_rows s))

dec_aes :: Matrix -> Matrix -> Matrix
dec_aes k c =
  dec_round10 k
    (dec_round9 k
      (dec_round8 k
        (dec_round7 k
          (dec_round6 k (dec_round5 k (dec_round4 k (dec_round3 k (dec_round2 k (dec_round1 k (add_round_key (key10 k) c))))))))))

data Blocks =
   B0 Matrix
 | BS Matrix Blocks

dec_aes_cbc :: Matrix -> Matrix -> Blocks -> Blocks
dec_aes_cbc key iv ciphertext =
  case ciphertext of {
   B0 s -> B0 (xor_matrices iv (dec_aes key s));
   BS s b -> let {d = dec_aes key s} in BS (xor_matrices iv d) (dec_aes_cbc key s b)}

