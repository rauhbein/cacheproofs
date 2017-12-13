(* cacheLib - generated by L3 - Mon Dec 04 11:53:00 2017 *)
structure cacheLib :> cacheLib =
struct
open HolKernel boolLib bossLib
open utilsLib cacheTheory
val () = (numLib.prefer_num (); wordsLib.prefer_word ())
fun cache_compset thms =
   utilsLib.theory_compset (thms, cacheTheory.inventory)
end