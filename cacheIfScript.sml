(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;

val _ = new_theory "cacheIf";

(* dummy cache for now *)

val _ = Parse.type_abbrev("cache_state", 
			  ``:padr -> (word # bool) option``);

val hit_def = Define `
   (hit NONE = F)
/\ (hit (SOME (w:word,d:bool)) = T)
`;

val dirty_def = Define `
   (dirty NONE = F)
/\ (dirty (SOME (w:word,d:bool)) = d)
`;

val cnt_def = Define `
   (cnt (SOME (w:word,d:bool)) = w)
`;

val chit_def = Define `chit_ (ca:cache_state) pa = hit (ca pa)`;

val cdirty_def = Define `cdirty_ (ca:cache_state) pa = dirty (ca pa)`;

val ccnt_def = Define `ccnt_ (ca:cache_state) pa = cnt (ca pa)`;

val _ = new_constant("evpol", ``:cache_state -> padr -> padr option``);

val cfill_def = Define `
   (cfill ca (mv:mem_view) pa NONE = ((pa =+ SOME (mv T pa,F)) ca, NONE))
/\ (cfill ca (mv:mem_view) pa (SOME pa') = 
       ((pa =+ SOME (mv T pa,F)) ((pa' =+ NONE) ca), 
        if cdirty_ ca pa' then SOME (pa', ccnt_ ca pa')
	else NONE))
`;

val ctf_def = Define `
   (ctf ca mv (RD pa T)   = if chit_ ca pa then (ca, NONE) 
			    else cfill ca mv pa (evpol ca pa))
/\ (ctf ca mv (WT pa w T) = if chit_ ca pa 
			    then ((pa =+ SOME (w,T)) ca, NONE) 
			    else let 
			        (ca',wb) = cfill ca mv pa (evpol ca pa)
                            in ((pa =+ SOME (w,T)) ca', wb))
/\ (ctf ca mv (CL pa)     = ((pa =+ NONE) ca, 
                             if cdirty_ ca pa then SOME (pa, ccnt_ ca pa)
			     else NONE))
`;

(*********** finish ************)

val _ = export_theory();
