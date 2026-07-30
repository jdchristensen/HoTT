From HoTT Require Import Basics.

Require Import Spaces.SInt Basics.Numerals.Decimal Basics.Numeral.

Definition test1 : sint_of_number_int (IntDec (Neg Decimal.zero)) = sint_zero := idpath.
