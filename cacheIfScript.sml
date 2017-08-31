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

val not_hit_not_dirty_lem = 
dirty_hit_lem |> SPEC_ALL |> (CONV_RULE CONTRAPOS_CONV) |> GEN_ALL;

val cnt_def = Define `
   (cnt (SOME (w:word,d:bool)) = w)
`;

val chit_def = Define `chit_ (ca:cache_state) pa = hit (ca pa)`;

val cdirty_def = Define `cdirty_ (ca:cache_state) pa = dirty (ca pa)`;

val not_cdirty_lem = store_thm("not_cdirty_lem", ``
!ca pa. ~cdirty_ ca pa <=> ((?w. ca pa = SOME (w,F)) \/ (ca pa = NONE))
``,
  RW_TAC std_ss [cdirty_def] >>
  Cases_on `ca pa`
  >| [(* NONE *)
      RW_TAC std_ss [dirty_def]
      ,
      (* SOME x *)
      `?v d. x = (v,d)` by ( METIS_TAC [pairTheory.pair_CASES] ) >>
      RW_TAC std_ss [dirty_def]
     ]
);

val ccnt_def = Define `ccnt_ (ca:cache_state) pa = cnt (ca pa)`;

(* add other properties of eviction policy here *)
val evpol_exists = prove(``
?evpol:cache_state -> padr -> padr option.
!ca pa. evpol ca pa <> SOME pa
``,
  EXISTS_TAC ``\c:cache_state a:padr. NONE:padr option`` >>
  RW_TAC std_ss []
);

val evpol_spec = new_specification("evpol_spec",["evpol"], evpol_exists);

val evict_def = Define `
   (evict ca NONE = (ca, NONE))
/\ (evict ca (SOME pa') = ((pa' =+ NONE) ca, 
			   if cdirty_ ca pa' 
			   then SOME (pa', ccnt_ ca pa')
			   else NONE))
`;

val cfill_def = Define `
cfill ca (mv:mem_view) pa ev = 
    if chit_ ca pa 
    then evict ca ev
    else let (ca', wb) = evict ca ev 
	 in ((pa =+ SOME (mv T pa,F)) ca', wb)
`;

val cevict_def = Define `
   (cevict ca NONE = ca)
/\ (cevict ca (SOME pa) = (pa =+ NONE) ca)
`;

val cevict_self_lem = store_thm("cevict_self_lem", ``
!ca pa. (cevict ca (evpol ca pa)) pa = ca pa
``,
  REPEAT STRIP_TAC >> 
  Cases_on `evpol ca pa` >> (
      RW_TAC std_ss [cevict_def]
  ) >>
  `x <> pa` by ( METIS_TAC [evpol_spec] ) >>
  RW_TAC std_ss [combinTheory.UPDATE_APPLY]
);

val cfill_ca_def = Define `
cfill_ca ca (mv:mem_view) pa ev = 
    if chit_ ca pa 
    then (cevict ca ev)
    else (pa =+ SOME (mv T pa,F)) (cevict ca ev)
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
      RW_TAC std_ss [cfill_def, cfill_ca_def, cevict_def, levict_def, evict_def]
  )
); 

val ctf_def = Define `
   (ctf ca mv (RD pa T)   = cfill ca mv pa (evpol ca pa))
/\ (ctf ca mv (WT pa w T) = let (ca',wb) = cfill ca mv pa (evpol ca pa)
			    in ((pa =+ SOME (w,T)) ca', wb))
/\ (ctf ca mv (CL pa)     = ((pa =+ NONE) ca, levict ca (SOME pa)))
`;

val ctf_ca_def = Define `
   (ctf_ca ca mv (RD pa T)   = cfill_ca ca mv pa (evpol ca pa))
/\ (ctf_ca ca mv (WT pa w T) = (pa =+ SOME (w,T)) 
				   (cfill_ca ca mv pa (evpol ca pa)))
/\ (ctf_ca ca mv (CL pa)     = (pa =+ NONE) ca)
`;

val ctf_wb_def = Define `
   (ctf_wb ca mv (RD pa T)   = levict ca (evpol ca pa))
/\ (ctf_wb ca mv (WT pa w T) = levict ca (evpol ca pa))
/\ (ctf_wb ca mv (CL pa)     = levict ca (SOME pa))
`;

val ctf_lem = store_thm("ctf_lem", ``
!ca mv dop. CA dop ==> (ctf ca mv dop = (ctf_ca ca mv dop, ctf_wb ca mv dop))
``,
  RW_TAC std_ss [CA_lem] >> (
      RW_TAC std_ss [ctf_def, ctf_ca_def, ctf_wb_def, cfill_lem]
  )
);

val ctf_ca_rd_lem = store_thm("ctf_ca_rd_lem", ``
!ca mv dop pa. rd dop /\ CA dop ==> 
    ((ctf_ca ca mv dop) pa = if pa = PA dop 
			     then (if chit_ ca pa 
				   then ca pa
				   else SOME (mv T pa,F))
			     else (if (evpol ca (PA dop) = SOME pa)
				   then NONE
			           else ca pa))
``,
  REPEAT STRIP_TAC >>
  `?pa'. dop = RD pa' T` by ( METIS_TAC [rd_CA_lem] ) >>
  FULL_SIMP_TAC std_ss [] >>
  RW_TAC std_ss [PA_def, ctf_ca_def, cfill_ca_def, 
		 combinTheory.UPDATE_APPLY, cevict_def] >- (
      RW_TAC std_ss [cevict_self_lem]
  ) >> (
      Cases_on `evpol ca pa'`
      >| [(* evict NONE *)
          RW_TAC std_ss [cevict_def]
          ,
          (* evict SOME x *)
          FULL_SIMP_TAC std_ss [optionTheory.SOME_11, cevict_def] >>
          RW_TAC std_ss [combinTheory.UPDATE_APPLY]
         ]
  )
);


val ctf_ca_wt_lem = store_thm("ctf_ca_wt_lem", ``
!ca mv dop pa. wt dop /\ CA dop ==> 
    ((ctf_ca ca mv dop) pa = if pa = PA dop 
			     then SOME (VAL dop,T)
			     else (if evpol ca (PA dop) = SOME pa
				   then NONE
			           else ca pa))
``,
  REPEAT STRIP_TAC >>
  `?pa' w. dop = WT pa' w T` by ( METIS_TAC [wt_CA_lem] ) >>
  FULL_SIMP_TAC std_ss [] >>
  RW_TAC std_ss [PA_def, ctf_ca_def, cfill_ca_def, 
		 combinTheory.UPDATE_APPLY, cevict_def, VAL_def] >> (
      Cases_on `evpol ca pa'`
      >| [(* evict NONE *)
          RW_TAC std_ss [cevict_def]
          ,
          (* evict SOME x *)
          FULL_SIMP_TAC std_ss [optionTheory.SOME_11, cevict_def] >>
          RW_TAC std_ss [combinTheory.UPDATE_APPLY]
         ]
  )
);

val ctf_ca_cl_lem = store_thm("ctf_ca_cl_lem", ``
!ca mv dop pa. cl dop ==> ((ctf_ca ca mv dop) pa = if pa = PA dop 
						   then NONE 
						   else ca pa)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [cl_lem] >>
  RW_TAC std_ss [PA_def] >> (
      RW_TAC std_ss [ctf_ca_def, combinTheory.UPDATE_APPLY]
  )
);

val ctf_ca_evict_other_lem = store_thm("ctf_ca_evict_other_lem", ``
!ca mv dop pa. CA dop /\ pa <> PA dop /\ 
	       (cl dop \/ (evpol ca (PA dop) <> SOME pa)) ==>
    ((ctf_ca ca mv dop) pa = ca pa)
``,
  REPEAT GEN_TAC >>
  MATCH_MP_TAC (prove(``(A /\ B /\ (C \/ ~C /\ D) ==> E)
                        ==>
   			(A /\ B /\ (C \/ D) ==> E)``, PROVE_TAC [])) >>
  RW_TAC std_ss [] >-( RW_TAC std_ss [ctf_ca_cl_lem] ) >>
  FULL_SIMP_TAC std_ss [not_cl_lem] >> (
      RW_TAC std_ss [ctf_ca_rd_lem, ctf_ca_wt_lem]
  )
);

val ctf_ca_evict_lem = store_thm("ctf_ca_evict_lem", ``
!ca mv dop pa. CA dop /\ ~cl dop /\ pa <> PA dop 
            /\ (evpol ca (PA dop) = SOME pa) ==>
    ((ctf_ca ca mv dop) pa = NONE)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [not_cl_lem] >> (
      RW_TAC std_ss [ctf_ca_rd_lem, ctf_ca_wt_lem]
  )
);

val ctf_wb_not_cl_lem = store_thm("ctf_wb_not_cl_lem", ``
!ca mv dop pa. CA dop /\ ~cl dop ==> 
    (ctf_wb ca mv dop = if evpol ca (PA dop) = NONE
			then NONE 
			else (if cdirty_ ca (THE (evpol ca (PA dop)))
			      then SOME(THE (evpol ca (PA dop)), 
					ccnt_ ca (THE(evpol ca (PA dop))))
			      else NONE))
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [not_cl_lem]
  >| [`?pa. dop = RD pa T` by ( METIS_TAC [rd_CA_lem] ),
      `?pa v. dop = WT pa v T` by ( METIS_TAC [wt_CA_lem] )
     ] >> (
      RW_TAC std_ss [PA_def, ctf_wb_def] >> (
          FULL_SIMP_TAC std_ss [PA_def, levict_def] 
      )
  ) >> ( 
      IMP_RES_TAC quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE >>
      IMP_RES_TAC optionTheory.IS_SOME_EXISTS >>
      FULL_SIMP_TAC std_ss [optionTheory.THE_DEF] >>
      RW_TAC std_ss [levict_def]
  )
);

val ctf_wb_cl_lem = store_thm("ctf_wb_cl_lem", ``
!ca mv dop. cl dop ==> 
    (ctf_wb ca mv dop = if cdirty_ ca (PA dop) 
			then SOME (PA dop, ccnt_ ca (PA dop)) 
                        else NONE)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [cl_lem] >> 
  RW_TAC std_ss [PA_def, ctf_wb_def, levict_def] 
);


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
!ca mv pa x ca' y. ((ca', y) = cfill ca mv pa x) /\ (x <> SOME pa) ==>
    chit_ ca' pa					     
``,
  RW_TAC std_ss [chit_lem] >>
  Cases_on `x` >> (
      Cases_on `chit_ ca pa`
      >| [(* hit *)
          FULL_SIMP_TAC std_ss [cfill_def, evict_def] >>
	  RW_TAC std_ss [combinTheory.UPDATE_APPLY] >>
	  METIS_TAC [chit_lem]
	  ,
          (* miss *)
	  FULL_SIMP_TAC std_ss [cfill_def, evict_def, boolTheory.LET_THM] >>
	  RW_TAC std_ss [combinTheory.UPDATE_APPLY]
	 ]
  )
);

(* proof obligations on any cache model *)

val chit_oblg = store_thm("chit_oblg", ``
!pa ca ca'. (ca pa = ca' pa) ==> (chit_ ca pa <=> chit_ ca' pa)
``,
  RW_TAC std_ss [chit_def]
);

val miss_oblg = store_thm("miss_oblg", ``
!ca pa. ~chit_ ca pa <=> (ca pa = NONE)
``,
  RW_TAC std_ss [chit_def] >>
  Cases_on `ca pa` 
  >| [(* ==> *)
      RW_TAC std_ss [hit_def]
      ,
      `?w b. x = (w,b)` by ( RW_TAC std_ss [pairTheory.pair_CASES] ) >>
      FULL_SIMP_TAC std_ss [hit_def]
      ]
);


val cdirty_oblg = store_thm("cdirty_oblg", ``
!pa ca ca'. (ca pa = ca' pa) ==> (cdirty_ ca pa <=> cdirty_ ca' pa)
``,
  RW_TAC std_ss [cdirty_def]
);

val cdirty_chit_oblg = store_thm("cdirty_chit_oblg", ``
!ca pa. cdirty_ ca pa ==> chit_ ca pa
``,
  RW_TAC std_ss [cdirty_def, chit_def, dirty_hit_lem]
);

val not_chit_not_cdirty_oblg = store_thm("not_chit_not_cdirty_oblg", ``
!ca pa. ~chit_ ca pa ==> ~cdirty_ ca pa 
``,
  RW_TAC std_ss [cdirty_def, chit_def, not_hit_not_dirty_lem]
);

val ctf_chit_oblg = store_thm("ctf_chit_oblg", ``
!ca mv dop ca' y. CA dop /\ ~cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    chit_ ca' (PA dop)
``,
  RW_TAC std_ss [CA_lem, cl_lem] >> ( FULL_SIMP_TAC std_ss [ctf_def, PA_def] ) 
  >| [(* read *)
      Cases_on `chit_ ca pa` >> (
          FULL_SIMP_TAC std_ss [] >>
	  METIS_TAC [cfill_chit_, evpol_spec]
      )
      ,
      (* write *)
      FULL_SIMP_TAC std_ss [cfill_lem, boolTheory.LET_THM] >>
      REWRITE_TAC [chit_def, combinTheory.UPDATE_APPLY, hit_def]
     ]
);

val ctf_cl_miss_oblg = store_thm("ctf_cl_miss_oblg", ``
!ca mv dop ca' y. cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    ~chit_ ca' (PA dop)
``,
  RW_TAC std_ss [] >>
  IMP_RES_TAC cl_CA_lem >>
  FULL_SIMP_TAC std_ss [ctf_lem] >>
  RW_TAC std_ss [not_chit_lem] >>
  RW_TAC std_ss [ctf_ca_cl_lem]
);

val ctf_cl_other_oblg = store_thm("ctf_cl_other_oblg", ``
!ca mv dop ca' y pa. cl dop /\ ((ca',y) = ctf ca mv dop) /\ (pa <> PA dop) ==>
    (ca' pa = ca pa)
``,
  RW_TAC std_ss [] >>
  IMP_RES_TAC cl_CA_lem >>
  FULL_SIMP_TAC std_ss [ctf_lem] >>
  RW_TAC std_ss [ctf_ca_cl_lem]
);

val ctf_cl_wb_oblg = store_thm("ctf_cl_wb_oblg", ``
!ca mv dop ca' y pa. cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    (y = if cdirty_ ca (PA dop)
	 then SOME (PA dop, ccnt_ ca (PA dop))
	 else NONE)
``,
  RW_TAC std_ss [] >> (
      IMP_RES_TAC cl_CA_lem >>
      FULL_SIMP_TAC std_ss [ctf_lem] >>
      RW_TAC std_ss [ctf_wb_cl_lem]
  )
);

val ctf_not_cl_other_oblg = store_thm("ctf_not_cl_other_oblg", ``
!ca mv dop ca' y pa. CA dop /\ ~cl dop /\ ((ca',y) = ctf ca mv dop) 
		  /\ (pa <> PA dop) ==>
    (ca' pa = if evpol ca (PA dop) = SOME pa 
	      then NONE
	      else ca pa)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [not_cl_lem]
  >| [(* rd *)
      REV_FULL_SIMP_TAC std_ss [ctf_lem] >>
      RW_TAC std_ss [ctf_ca_rd_lem]
      ,
      (* wt *)
      REV_FULL_SIMP_TAC std_ss [ctf_lem] >>
      RW_TAC std_ss [ctf_ca_wt_lem]
     ]
);


val ctf_not_cl_wb_oblg = store_thm("ctf_not_cl_wb_oblg", ``
!ca mv dop ca' y. CA dop /\ ~cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    (y = if evpol ca (PA dop) = NONE
	 then NONE
	 else (if cdirty_ ca (THE (evpol ca (PA dop))) 
	       then SOME (THE (evpol ca (PA dop)),
			  ccnt_ ca (THE (evpol ca (PA dop))))
	       else NONE)) 
``,
  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [ctf_lem] >>
  RW_TAC std_ss [ctf_wb_not_cl_lem]
);

val ctf_wt_cdirty_oblg = store_thm("ctf_wt_cdirty_oblg", ``
!ca mv dop ca' y. CA dop /\ wt dop /\ ((ca',y) = ctf ca mv dop) ==>
    cdirty_ ca' (PA dop)
``,
  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [ctf_lem] >>
  RW_TAC std_ss [cdirty_def, ctf_ca_wt_lem, dirty_def]
);

val ctf_rd_hit_oblg = store_thm("ctf_rd_hit_oblg", ``
!ca mv dop ca' y. CA dop /\ rd dop /\ chit_ ca (PA dop) 
	       /\ ((ca',y) = ctf ca mv dop) ==>
    (ca' (PA dop) = ca (PA dop))
``,
  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [ctf_lem] >>
  RW_TAC std_ss [ctf_ca_rd_lem]
);

val ctf_rd_miss_oblg = store_thm("ctf_rd_miss_oblg", ``
!ca mv dop ca' y. CA dop /\ rd dop /\ ~chit_ ca (PA dop) 
	       /\ ((ca',y) = ctf ca mv dop) ==>
    (ccnt_ ca' (PA dop) = mv T (PA dop)) /\ ~cdirty_ ca' (PA dop)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >> STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [ctf_lem] 
  >| [(* ccnt *)
      RW_TAC std_ss [ccnt_def, cnt_def, ctf_ca_rd_lem]
      ,
      (* not dirty *)
      RW_TAC std_ss [not_cdirty_lem, ctf_ca_rd_lem]
     ]      
);

val ctf_wt_ccnt_oblg = store_thm("ctf_wt_ccnt_oblg", ``
!ca mv dop ca' y. CA dop /\ wt dop /\ ((ca',y) = ctf ca mv dop) ==>
    (ccnt_ ca' (PA dop) = VAL dop)
``,
  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [ctf_lem] >>
  RW_TAC std_ss [ctf_ca_wt_lem, ccnt_def, cnt_def]
);

val evpol_oblg = save_thm("evpol_oblg", evpol_spec);

(*********** finish ************)

val _ = export_theory();
