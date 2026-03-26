Set Warnings "-extraction-default-directory".

From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlIntConv.
From Bits.Cpdt Require Import StackMachine.

Extraction "stack_machine"
  Typed.Exp.compile
  Typed.Exp.denote
  Typed.Prog.denote
  ExtrOcamlIntConv.int_of_nat
  ExtrOcamlIntConv.nat_of_int.
