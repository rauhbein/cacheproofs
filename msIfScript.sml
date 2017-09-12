(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;
open cachememTheory;

val _ = new_theory "coreIf";

(* TODO: 
- ms record type
- accessor functions
- transition function / relation
- lift deriveability lemmas
- IC lemmas / invariant
*)

(*********** finish ************)

val _ = export_theory();
