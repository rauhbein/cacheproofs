(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;
open cacheIfTheory;

val _ = new_theory "cachemem";

(* memory state and memory view *)

val _ = Parse.type_abbrev("mem_state", ``:padr -> word``);

(* cacheless memory view *)
val MVcl_def = Define `MVcl (m:mem_state) = 
\(c:bool) pa. m pa
`;

(* cache-aware memory view *)
val MVca_def = Define `MVca ca m = 
\c pa. if c /\ chit_ ca pa then ccnt_ ca pa else m pa
`;

(* alternative memory view *)
val MValt_def = Define `MValt ca m = 
\c pa. if c /\ cdirty_ ca pa then ccnt_ ca pa else m pa
`;

(* memory semantics *)

(* cacheless *)
val mtfcl_def = Define `
   (mtfcl m (WT pa w c) = (pa =+ w) m)
/\ (mtfcl m _ = m)
`;

val wb_def = Define `
   (wb (ca:cache_state,NONE) (m:mem_state) = (ca,m))
/\ (wb (ca,SOME(pa,w)) m = (ca,(pa =+ w) m))
`;

(* cache-aware *)
val mtfca_def = Define `
   (mtfca ca m (RD pa T)   = wb (ctf ca (MVcl m) (RD pa T)) m)
/\ (mtfca ca m (WT pa w T) = wb (ctf ca (MVcl m) (WT pa w T)) m)
/\ (mtfca ca m (WT pa w F) = (ca,(pa =+ w) m))
/\ (mtfca ca m (CL pa)     = wb (ctf ca (MVcl m) (CL pa)) m)
/\ (mtfca ca m _           = (ca,m))
`;

(* TODO: add some useful lemmas *)


(*********** finish ************)

val _ = export_theory();
