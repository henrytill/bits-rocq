Set Warnings "-extraction-default-directory".

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZBigInt.
From Stdlib Require ExtrOCamlInt63.
From Stdlib Require PArray.

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

From Bits.Belnap Require Import BelnapModel BelnapArr.

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
