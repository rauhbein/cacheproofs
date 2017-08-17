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

val dirty_hit_lem = store_thm("dirty_hit_lem", ``
!l. dirty l ==> hit l
``,
  Cases >- ( RW_TAC std_ss [dirty_def, hit_def] ) >>
  `?w d. x = (w,d)` by ( RW_TAC std_ss [pairTheory.pair_CASES] ) >>
  RW_TAC std_ss [dirty_def, hit_def]
);

(* SPEC_ALL |> (CONV_RULE CONTRAPOS_CONV)  dirty_hit_lem *)

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

val cevict_def = Define `
   (cevict ca NONE = ca)
/\ (cevict ca (SOME pa) = (pa =+ NONE) ca)
`;

val cfill_ca_def = Define `
cfill_ca ca (mv:mem_view) pa ev = (pa =+ SOME (mv T pa,F)) (cevict ca ev)
`;

val levict_def = Define `
   (levict ca NONE = NONE)
/\ (levict ca (SOME pa) = if cdirty_ ca pa then SOME (pa, ccnt_ ca pa) else NONE)
`; 

val cfill_lem = store_thm("cfill_lem", ``
!ca mv pa ev. cfill ca mv pa ev = (cfill_ca ca mv pa ev, levict ca ev)
``,
  REPEAT STRIP_TAC >>
  Cases_on `ev` >> (
      RW_TAC std_ss [cfill_def, cfill_ca_def, cevict_def, levict_def]
  )
); 

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

(* proof obligations on any cache model *)

val chit_lem = store_thm("chit_lem", ``
!ca pa. chit_ ca pa <=> ?w d. ca pa = SOME (w,d)
``,
  RW_TAC std_ss [chit_def] >>
  Cases_on `ca pa` 
  >| [(* case: NONE *)
      RW_TAC std_ss [hit_def]
      , 
      (* case: SOME x *)
      `?w d. x = (w,d)` by (
          RW_TAC std_ss [pairTheory.pair_CASES]
      ) >>
      RW_TAC std_ss [hit_def]
     ]
);

val not_chit_lem = store_thm("not_chit_lem", ``
!ca pa. ~chit_ ca pa <=> (ca pa = NONE)
``,
  RW_TAC std_ss [chit_def] >>
  Cases_on `ca pa` 
  >| [(* case: NONE *)
      RW_TAC std_ss [hit_def]
      , 
      (* case: SOME x *)
      `?w d. x = (w,d)` by (
          RW_TAC std_ss [pairTheory.pair_CASES]
      ) >>
      RW_TAC std_ss [hit_def]
     ]
);

val cfill_chit_ = store_thm("cfill_chit_", ``
!ca mv pa x ca' y. (cfill ca mv pa x = (ca', y)) ==>
    chit_ ca' pa					     
``,
  RW_TAC std_ss [chit_lem] >>
  Cases_on `x` >> (
      FULL_SIMP_TAC std_ss [cfill_def] >>
      METIS_TAC [combinTheory.APPLY_UPDATE_THM]
  )
);

val ctf_chit_oblg = store_thm("ctf_chit_oblg", ``
!ca mv dop ca' y. CA dop /\ ~cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    chit_ ca' (PA dop)
``,
  RW_TAC std_ss [CA_lem, cl_lem] >> ( FULL_SIMP_TAC std_ss [ctf_def, PA_def] ) 
  >| [(* read *)
      Cases_on `chit_ ca pa` >> (
          FULL_SIMP_TAC std_ss [] >>
	  METIS_TAC [cfill_chit_]
      )
      ,
      (* write *)
      Cases_on `chit_ ca pa`
      >| [(* hit *)
          FULL_SIMP_TAC std_ss [] >>
	  REWRITE_TAC [chit_def, combinTheory.UPDATE_APPLY, hit_def]
	  ,
	  (* miss *)
	  `?ca2 wb. cfill ca mv pa (evpol ca pa) = (ca2, wb)` by (
	      METIS_TAC [pairTheory.pair_CASES]
	  ) >>
          FULL_SIMP_TAC std_ss [LET_THM] >> 
	  REWRITE_TAC [chit_def, combinTheory.UPDATE_APPLY, hit_def]
	 ]
     ]
);

(* TODO: add useful lemmas about cache semantics *)


(*********** finish ************)

val _ = export_theory();
