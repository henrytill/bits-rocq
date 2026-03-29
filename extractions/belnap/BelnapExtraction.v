Set Warnings "-extraction-default-directory".

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZBigInt.
From Stdlib Require ExtrOCamlInt63.
From Stdlib Require PArray.
From Stdlib Require Import NArith.
From Bits.Belnap Require Import BelnapModel BelnapArr.

(** Override the default PArray extraction to avoid the phantom type
    parameter bug where ['a1 'a Parray.t] is generated instead of
    ['a1 Parray.t]. *)
Extract Constant PrimArray.array "'a" => "'a Parray.t".
Extract Constant PrimArray.make => "Parray.make".
Extract Constant PrimArray.get => "Parray.get".
Extract Constant PrimArray.default => "Parray.default".
Extract Constant PrimArray.set => "Parray.set".
Extract Constant PrimArray.length => "Parray.length".
Extract Constant PrimArray.copy => "Parray.copy".

(** N bitwise operations: the standard ExtrOcamlZBigInt only extracts
    shifts, leaving land/lor/lxor/lnot as recursive Coq definitions.
    Map them to Zarith's native big-integer bitwise ops. *)
Extract Constant N.land => "Big_int_Z.and_big_int".
Extract Constant N.lor  => "Big_int_Z.or_big_int".
Extract Constant N.lxor => "Big_int_Z.xor_big_int".

(** N.lnot x width = N.lxor x (N.ones width) = x xor (2^width - 1). *)
Extract Constant N.lnot =>
          "fun x n ->
     Big_int_Z.xor_big_int x
       (Big_int_Z.pred_big_int
          (Big_int_Z.shift_left_big_int Big_int_Z.unit_big_int
             (Big_int_Z.int_of_big_int n)))".

(** Replace fuel-based parray_imap2_aux with Parray.init for O(n) without
    persistent-array bookkeeping overhead. *)
Extract Constant parray_imap2_aux =>
          "fun f a b _ fuel ->
     let sz = Uint63.of_int fuel in
     Parray.init sz
       (fun i -> f i (Parray.get a (Uint63.of_int i)) (Parray.get b (Uint63.of_int i)))
       Big_int_Z.zero_big_int".

Extraction "belnap"
  BelnapArr.BelnapArr
  BelnapArr.ba_get
  BelnapArr.ba_set
  BelnapArr.ba_and
  BelnapArr.ba_or
  BelnapArr.ba_consensus
  BelnapArr.ba_merge
  BelnapArr.ba_not
  BelnapArr.ba_all_unknown
  BelnapArr.ba_all_both
  BelnapArr.ba_all_true
  BelnapArr.ba_all_false
  BelnapModel.Belnap.
