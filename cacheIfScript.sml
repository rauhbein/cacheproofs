(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;

val _ = new_theory "cacheIf";

(* dummy cache for now *)

val _ = Datatype `line = CLINE word`;

val line_neq_lem = store_thm("line_neq_lem", ``
!l1 l2. l1 <> l2 ==> ?w1 w2. (l1 = CLINE w1) /\ (l2 = CLINE w2) /\ w1 <> w2
``,
  Cases >> Cases >> METIS_TAC []
);

val the_line_def = Define `the_line (CLINE w) = w`;

val _ = Parse.type_abbrev("tag", ``:bool[30]``);

val _ = Parse.type_abbrev("line_view", ``:bool -> tag -> word``);

val _ = Parse.type_abbrev("cache_state", 
			  ``:tag -> (line # bool) option``);

val tag_def = Define `tag (pa:padr) = the_adr pa`;

val lv_def = Define `lv (mv:mem_view) c (pa:padr) = CLINE (mv c pa)`;

val lw_def = Define `lw l (pa:padr) = the_line l`;

val lu_def = Define `lu (l:line) (pa:padr) (w:word) = CLINE w`;

val hit_def = Define `
   (hit NONE = F)
/\ (hit (SOME (w:line,d:bool)) = T)
`;

val dirty__def = Define `
   (dirty_ NONE = F)
/\ (dirty_ (SOME (w:line,d:bool)) = d)
`;

val dirty_hit_lem = store_thm("dirty_hit_lem", ``
!l. dirty_ l ==> hit l
``,
  Cases >- ( RW_TAC std_ss [dirty__def, hit_def] ) >>
  `?w d. x = (w,d)` by ( RW_TAC std_ss [pairTheory.pair_CASES] ) >>
  RW_TAC std_ss [dirty__def, hit_def]
);

val not_hit_not_dirty_lem = 
dirty_hit_lem |> SPEC_ALL |> (CONV_RULE CONTRAPOS_CONV) |> GEN_ALL;

val cnt_def = Define `
   (cnt (SOME (w:line,d:bool)) = w)
`;

val chit_def = Define `chit_ (ca:cache_state) (pa:padr) = hit (ca (tag pa))`;

val ldirty_def = Define `ldirty_ (ca:cache_state) t = 
dirty_ (ca t)`;
val cdirty_def = Define `cdirty_ (ca:cache_state) (pa:padr) = 
dirty_ (ca (tag pa))`;

val not_cdirty_lem = store_thm("not_cdirty_lem", ``
!ca pa. ~cdirty_ ca pa <=> (    (?w. ca (tag pa) = SOME (w,F)) 
			     \/ (ca (tag pa) = NONE))
``,
  RW_TAC std_ss [cdirty_def] >>
  Cases_on `ca (tag pa)`
  >| [(* NONE *)
      RW_TAC std_ss [dirty__def]
      ,
      (* SOME x *)
      `?v d. x = (v,d)` by ( METIS_TAC [pairTheory.pair_CASES] ) >>
      RW_TAC std_ss [dirty__def]
     ]
);

val lcnt_def = Define `lcnt_ (ca:cache_state) t = cnt (ca t)`;
val ccnt_def = Define `ccnt_ (ca:cache_state) pa = cnt (ca (tag pa))`;
val ccntw_def = Define `ccntw_ (ca:cache_state) pa = lw (ccnt_ ca pa) pa`;

(* add other properties of eviction policy here *)
val evpol_exists = prove(``
?evpol:cache_state -> padr -> tag option.
!ca pa pa'. (tag pa' = tag pa) ==> evpol ca pa <> SOME (tag pa')
``,
  EXISTS_TAC ``\c:cache_state a:padr. NONE:tag option`` >>
  RW_TAC std_ss []
);

val evpol_spec = new_specification("evpol_spec",["evpol"], evpol_exists);

val evict_def = Define `
   (evict ca NONE = (ca, NONE))
/\ (evict ca (SOME t) = ((t =+ NONE) ca, 
			   if ldirty_ ca t 
			   then SOME (t, lcnt_ ca t)
			   else NONE))
`;

val cfill_def = Define `
cfill ca (mv:mem_view) pa ev = 
    if chit_ ca pa 
    then evict ca ev
    else let (ca', wb) = evict ca ev 
	 in (((tag pa) =+ SOME ((lv mv T pa),F)) ca', wb)
`;

val cevict_def = Define `
   (cevict ca NONE = ca)
/\ (cevict ca (SOME t) = (t =+ NONE) ca)
`;

val cevict_self_lem = store_thm("cevict_self_lem", ``
!ca pa. (cevict ca (evpol ca pa)) (tag pa) = ca (tag pa)
``,
  REPEAT STRIP_TAC >> 
  Cases_on `evpol ca pa` >> (
      RW_TAC std_ss [cevict_def]
  ) >>
  `x <> tag pa` by ( METIS_TAC [evpol_spec] ) >>
  RW_TAC std_ss [combinTheory.UPDATE_APPLY]
);

val cfill_ca_def = Define `
cfill_ca ca (mv:mem_view) pa ev = 
    if chit_ ca pa 
    then (cevict ca ev)
    else (tag pa =+ SOME (lv mv T pa,F)) (cevict ca ev)
`;

val levict_def = Define `
   (levict ca NONE = NONE)
/\ (levict ca (SOME t) = if ldirty_ ca t then SOME (t, lcnt_ ca t) else NONE)
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
			    in ((tag pa =+ SOME (CLINE w,T)) ca', wb))
/\ (ctf ca mv (CL pa)     = ((tag pa =+ NONE) ca, levict ca (SOME (tag pa))))
`;

val ctf_ca_def = Define `
   (ctf_ca ca mv (RD pa T)   = cfill_ca ca mv pa (evpol ca pa))
/\ (ctf_ca ca mv (WT pa w T) = (tag pa =+ SOME (CLINE w,T)) 
				   (cfill_ca ca mv pa (evpol ca pa)))
/\ (ctf_ca ca mv (CL pa)     = (tag pa =+ NONE) ca)
`;

val ctf_wb_def = Define `
   (ctf_wb ca (mv:mem_view) (RD pa T)   = levict ca (evpol ca pa))
/\ (ctf_wb ca mv (WT pa w T) = levict ca (evpol ca pa))
/\ (ctf_wb ca mv (CL pa)     = levict ca (SOME (tag pa)))
`;

val ctf_lem = store_thm("ctf_lem", ``
!ca mv dop. CA dop ==> (ctf ca mv dop = (ctf_ca ca mv dop, ctf_wb ca mv dop))
``,
  RW_TAC std_ss [CA_lem] >> (
      RW_TAC std_ss [ctf_def, ctf_ca_def, ctf_wb_def, cfill_lem]
  )
);

val ctf_ca_rd_lem = store_thm("ctf_ca_rd_lem", ``
!ca mv dop t. rd dop /\ CA dop ==> 
    ((ctf_ca ca mv dop) t = if t = tag (PA dop)
			    then (if hit (ca t) 
				  then ca t
				  else SOME (lv mv T (PA dop),F))
			    else (if (evpol ca (PA dop) = SOME t)
				  then NONE
			          else ca t))
``,
  REPEAT STRIP_TAC >>
  `?pa'. dop = RD pa' T` by ( METIS_TAC [rd_CA_lem] ) >>
  FULL_SIMP_TAC std_ss [] >>
  RW_TAC std_ss [PA_def, ctf_ca_def, cfill_ca_def, 
		 combinTheory.UPDATE_APPLY, cevict_def, chit_def] >- (
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
!ca mv dop t. wt dop /\ CA dop ==> 
    ((ctf_ca ca mv dop) t = if t = tag (PA dop)
			    then SOME (CLINE (VAL dop),T)
			    else (if evpol ca (PA dop) = SOME t
				  then NONE
			          else ca t))
``,
  REPEAT STRIP_TAC >>
  `?pa' w. dop = WT pa' w T` by ( METIS_TAC [wt_CA_lem] ) >>
  FULL_SIMP_TAC std_ss [] >>
  RW_TAC std_ss [PA_def, ctf_ca_def, cfill_ca_def, 
		 combinTheory.UPDATE_APPLY, cevict_def, VAL_def, chit_def] >> (
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
!ca mv dop t. cl dop ==> ((ctf_ca ca mv dop) t = if t = tag (PA dop)
						 then NONE 
						 else ca t)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [cl_lem] >>
  RW_TAC std_ss [PA_def] >> (
      RW_TAC std_ss [ctf_ca_def, combinTheory.UPDATE_APPLY]
  )
);

val ctf_ca_evict_other_lem = store_thm("ctf_ca_evict_other_lem", ``
!ca mv dop t. CA dop /\ t <> tag (PA dop) 
           /\ (cl dop \/ (evpol ca (PA dop) <> SOME t)) ==>
    ((ctf_ca ca mv dop) t = ca t)
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
!ca mv dop t. CA dop /\ ~cl dop /\ t <> tag (PA dop)
           /\ (evpol ca (PA dop) = SOME t) ==>
    ((ctf_ca ca mv dop) t = NONE)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [not_cl_lem] >> (
      RW_TAC std_ss [ctf_ca_rd_lem, ctf_ca_wt_lem]
  )
);

val ctf_wb_not_cl_lem = store_thm("ctf_wb_not_cl_lem", ``
!ca mv dop. CA dop /\ ~cl dop ==> 
    (ctf_wb ca mv dop = if evpol ca (PA dop) = NONE
			then NONE 
			else (if ldirty_ ca (THE (evpol ca (PA dop))) /\
                                 THE (evpol ca (PA dop)) <> tag (PA dop)
			      then SOME(THE (evpol ca (PA dop)), 
					lcnt_ ca (THE(evpol ca (PA dop))))
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
  ) >> (
      METIS_TAC [evpol_spec]
  )
);

val ctf_wb_cl_lem = store_thm("ctf_wb_cl_lem", ``
!ca mv dop. cl dop ==> 
    (ctf_wb ca mv dop = if cdirty_ ca (PA dop) 
			then SOME (tag (PA dop), lcnt_ ca (tag (PA dop))) 
                        else NONE)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [cl_lem] >> 
  RW_TAC std_ss [PA_def, ctf_wb_def, levict_def, cdirty_def, 
		 lcnt_def, ldirty_def] 
);


val chit_lem = store_thm("chit_lem", ``
!ca pa. chit_ ca pa <=> ?w d. ca (tag pa) = SOME (w,d)
``,
  RW_TAC std_ss [chit_def] >>
  Cases_on `ca (tag pa)` 
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
!ca pa. ~chit_ ca pa <=> (ca (tag pa) = NONE)
``,
  RW_TAC std_ss [chit_def] >>
  Cases_on `ca (tag pa)` 
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
!ca mv pa x ca' y. ((ca', y) = cfill ca mv pa x) /\ (x <> SOME (tag pa)) ==>
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


(* memory cache line write-back and lookup *)

val mlwb_def = Define `mlwb m (t:tag) (CLINE w) = (PADR t =+ w) m`;

(* fetch line corresponding to pa according to line size *)
val mllu_def = Define `mllu m pa = CLINE (m pa)`;

(* proof obligations on the cache model, imported by generalized model *)

val mlwb_oblg = store_thm("mlwb_oblg", ``
!m t l pa. (tag pa = t) ==> (mlwb m t l pa = lw l pa)  
``,
  Cases_on `l` >>
  RW_TAC std_ss [mlwb_def, lw_def, tag_def] >>
  Cases_on `pa` >>
  RW_TAC std_ss [the_adr_def, the_line_def, combinTheory.UPDATE_APPLY]
); 

val mlwb_other_oblg = store_thm("mlwb_other_oblg", ``
!m t l pa. (tag pa <> t) ==> (mlwb m t l pa = m pa)  
``,
  Cases_on `l` >>
  RW_TAC std_ss [mlwb_def, tag_def] >>
  Cases_on `pa` >>
  FULL_SIMP_TAC std_ss [the_adr_def] >>
  RW_TAC std_ss [combinTheory.UPDATE_APPLY]
); 

val mllu_oblg = store_thm("mllu_oblg", ``
!m pa pa'. (tag pa = tag pa') ==> (lw (mllu m pa') pa = m pa)  
``,
  RW_TAC std_ss [mllu_def, lw_def, tag_def] >>
  Cases_on `pa` >>
  Cases_on `pa'` >>
  FULL_SIMP_TAC std_ss [the_adr_def, the_line_def]
); 

val tag_oblg = store_thm("tag_oblg", ``
!t. ?pa. t = tag pa
``,
  RW_TAC std_ss [tag_def] >>
  EXISTS_TAC ``PADR t`` >>
  RW_TAC std_ss [the_adr_def]
);

val chit_oblg = store_thm("chit_oblg", ``
!pa ca ca'. (ca (tag pa) = ca' (tag pa)) ==> (chit_ ca pa <=> chit_ ca' pa)
``,
  RW_TAC std_ss [chit_def]
);

val chit_other_oblg = store_thm("chit_other_oblg", ``
!pa pa' ca. (tag pa = tag pa') ==> (chit_ ca pa <=> chit_ ca pa')
``,
  RW_TAC std_ss [chit_def]
);

val ccnt_oblg = store_thm("ccnt_oblg", ``
!pa ca ca'. (ca (tag pa) = ca' (tag pa)) ==> (ccnt_ ca pa = ccnt_ ca' pa)
``,
  RW_TAC std_ss [ccnt_def]
);

val ccnt_other_oblg = store_thm("ccnt_other_oblg", ``
!pa pa' ca. (tag pa = tag pa') ==> (ccnt_ ca pa = ccnt_ ca pa')
``,
  RW_TAC std_ss [ccnt_def]
);

val ccntw_oblg = store_thm("ccntw_oblg", ``
!pa ca ca'. (ca (tag pa) = ca' (tag pa)) ==> (ccntw_ ca pa = ccntw_ ca' pa)
``,
  RW_TAC std_ss [ccntw_def] >>
  IMP_RES_TAC ccnt_oblg >>
  ASM_REWRITE_TAC []
);

val ccntw_ccnt_oblg = store_thm("ccntw_ccnt_oblg", ``
!pa ca ca'. chit_ ca pa /\ chit_ ca' pa /\ (ccnt_ ca pa = ccnt_ ca' pa) ==> 
    (ccntw_ ca pa = ccntw_ ca' pa)
``,
  RW_TAC std_ss [ccntw_def, ccnt_def] >>
  IMP_RES_TAC chit_lem >>
  FULL_SIMP_TAC std_ss [cnt_def]
);

val ccntw_ccnt_other_oblg = store_thm("ccntw_ccnt_other_oblg", ``
!pa ca ca'. chit_ ca pa /\ chit_ ca' pa /\ (ccnt_ ca pa = ccnt_ ca' pa) ==> 
    !pa'. (tag pa' = tag pa) ==> (ccntw_ ca pa' = ccntw_ ca' pa')
``,
  RW_TAC std_ss [ccntw_def, ccnt_def] >>
  IMP_RES_TAC chit_lem >>
  FULL_SIMP_TAC std_ss [cnt_def]
);

val ccntw_ccnt_diff_oblg = store_thm("ccntw_ccnt_diff_oblg", ``
!pa ca ca'. chit_ ca pa /\ chit_ ca' pa /\ (ccnt_ ca pa <> ccnt_ ca' pa) ==> 
    ?pa'. (tag pa' = tag pa) /\ (ccntw_ ca pa' <> ccntw_ ca' pa')
``,
  RW_TAC std_ss [ccntw_def, ccnt_def] >>
  IMP_RES_TAC chit_lem >>
  FULL_SIMP_TAC std_ss [cnt_def] >>
  EXISTS_TAC ``pa:padr`` >>
  RW_TAC std_ss [cnt_def, lw_def] >>
  IMP_RES_TAC line_neq_lem >>
  RW_TAC std_ss [the_line_def]
);

val ccnt_lcnt_oblg = store_thm("ccnt_lcnt_oblg", ``
!ca pa. ccnt_ ca pa = lcnt_ ca (tag pa)
``,
  RW_TAC std_ss [ccnt_def, lcnt_def]
);

val ccnt_not_eq_oblg = store_thm("ccnt_not_eq_oblg", ``
!pa ca ca'. chit_ ca pa /\ chit_ ca' pa /\ (cdirty_ ca pa <=> cdirty_ ca' pa)
         /\ (ca (tag pa) <> ca' (tag pa)) ==> 
    (ccnt_ ca pa <> ccnt_ ca' pa)
``,
  RW_TAC std_ss [ccnt_def] >>
  FULL_SIMP_TAC std_ss [chit_lem, cdirty_def] >>
  RW_TAC std_ss [cnt_def] >>
  REV_FULL_SIMP_TAC std_ss [dirty__def]
);

val miss_oblg = store_thm("miss_oblg", ``
!ca pa. ~chit_ ca pa <=> (ca (tag pa) = NONE)
``,
  RW_TAC std_ss [chit_def] >>
  Cases_on `ca (tag pa)` 
  >| [(* ==> *)
      RW_TAC std_ss [hit_def]
      ,
      `?w b. x = (w,b)` by ( RW_TAC std_ss [pairTheory.pair_CASES] ) >>
      FULL_SIMP_TAC std_ss [hit_def]
      ]
);


val cdirty_oblg = store_thm("cdirty_oblg", ``
!pa ca ca'. (ca (tag pa) = ca' (tag pa)) ==> (cdirty_ ca pa <=> cdirty_ ca' pa)
``,
  RW_TAC std_ss [cdirty_def]
);

val cdirty_chit_oblg = store_thm("cdirty_chit_oblg", ``
!ca pa. cdirty_ ca pa ==> chit_ ca pa
``,
  RW_TAC std_ss [cdirty_def, chit_def, dirty_hit_lem]
);

val cdirty_other_oblg = store_thm("cdirty_other_oblg", ``
!ca pa pa'. (tag pa = tag pa') ==> (cdirty_ ca pa <=> cdirty_ ca pa')
``,
  RW_TAC std_ss [cdirty_def]
);

val cdirty_ldirty_oblg = store_thm("cdirty_ldirty_oblg", ``
!ca pa. cdirty_ ca pa <=> ldirty_ ca (tag pa)
``,
  RW_TAC std_ss [cdirty_def, ldirty_def]
);

val not_chit_not_cdirty_oblg = store_thm("not_chit_not_cdirty_oblg", ``
!ca pa. ~chit_ ca pa ==> ~cdirty_ ca pa 
``,
  RW_TAC std_ss [cdirty_def, chit_def, not_hit_not_dirty_lem]
);

val lw_ccntw_oblg = store_thm("lw_ccntw_oblg", ``
!ca pa pa'. (tag pa = tag pa') ==> (lw (ccnt_ ca pa') pa = ccntw_ ca pa)
``,
  RW_TAC std_ss [lcnt_def, ccntw_def, ccnt_def]
);

val lw_lcnt_oblg = store_thm("lw_lcnt_oblg", ``
!ca pa. lw (lcnt_ ca (tag pa)) pa = ccntw_ ca pa
``,
  RW_TAC std_ss [lcnt_def, ccntw_def, ccnt_def]
);

val lw_lv_oblg = store_thm("lw_lv_oblg", ``
!mv pa. lw (lv mv T pa) pa = mv T pa
``,
  RW_TAC std_ss [lw_def, lv_def, the_line_def]
);

val lv_oblg = store_thm("lv_oblg", ``
!mv pa' pa. (tag pa = tag pa') ==> (lv mv T pa' = lv mv T pa)
``,
  RW_TAC std_ss [tag_def, lv_def, the_line_def] >>
  Cases_on `pa` >>
  Cases_on `pa'` >>
  FULL_SIMP_TAC std_ss [the_adr_def]
);

val mllu_lv_oblg = store_thm("mllu_lv_oblg", ``
!mv m pa pa'. (tag pa = tag pa') ==> 
    ((lv mv T pa' = mllu m pa) 
	 <=> 
     !pa''. (tag pa'' = tag pa) ==> 
         (lw (lv mv T pa') pa'' = lw (mllu m pa) pa''))
``,
  REPEAT STRIP_TAC >>
  EQ_TAC
  >| [(* ==> *)
      REPEAT STRIP_TAC >>
      RW_TAC std_ss [lw_lv_oblg, mllu_oblg]
      ,
      (* <== *)
      REPEAT STRIP_TAC >>
      RW_TAC std_ss [lv_def, mllu_def] >>
      PAT_X_ASSUM ``!pa. x`` (
          fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm )
      ) >>
      REV_FULL_SIMP_TAC std_ss [] >>
      Cases_on `pa` >>
      Cases_on `pa'` >>
      REV_FULL_SIMP_TAC std_ss [tag_def, the_adr_def] >>
      FULL_SIMP_TAC std_ss [lw_lv_oblg, mllu_oblg]
     ]
); 

val lu_oblg = store_thm("lu_oblg", ``
!l pa w. lw (lu l pa w) pa = w
``,
  RW_TAC std_ss [lw_def, lu_def, the_line_def]
);

val lu_other_oblg = store_thm("lu_other_oblg", ``
!l pa w pa'. (tag pa' = tag pa) /\ pa' <> pa ==> (lw (lu l pa w) pa' = lw l pa')
``,
  RW_TAC std_ss [tag_def, lw_def, lu_def, the_line_def] >>
  REV_FULL_SIMP_TAC std_ss [the_adr_inj]
);

(* transitions *)

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
    !pa. (tag pa = tag (PA dop)) ==> ~chit_ ca' pa
``,
  RW_TAC std_ss [] >>
  IMP_RES_TAC cl_CA_lem >>
  FULL_SIMP_TAC std_ss [ctf_lem] >>
  RW_TAC std_ss [not_chit_lem] >>
  RW_TAC std_ss [ctf_ca_cl_lem]
);

val ctf_cl_other_oblg = store_thm("ctf_cl_other_oblg", ``
!ca mv dop ca' y pa. cl dop /\ ((ca',y) = ctf ca mv dop) 
                  /\ (tag pa <> tag (PA dop)) ==>
    (ca' (tag pa) = ca (tag pa))
``,
  RW_TAC std_ss [] >>
  IMP_RES_TAC cl_CA_lem >>
  FULL_SIMP_TAC std_ss [ctf_lem] >>
  RW_TAC std_ss [ctf_ca_cl_lem]
);

val ctf_cl_wb_oblg = store_thm("ctf_cl_wb_oblg", ``
!ca mv dop ca' y pa. cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    (y = if cdirty_ ca (PA dop)
	 then SOME (tag (PA dop), ccnt_ ca (PA dop))
	 else NONE)
``,
  RW_TAC std_ss [] >> (
      IMP_RES_TAC cl_CA_lem >>
      FULL_SIMP_TAC std_ss [ctf_lem] >>
      RW_TAC std_ss [ctf_wb_cl_lem, ccnt_def, lcnt_def]
  )
);

val ctf_not_cl_other_oblg = store_thm("ctf_not_cl_other_oblg", ``
!ca mv dop ca' y t. CA dop /\ ~cl dop /\ ((ca',y) = ctf ca mv dop) 
		  /\ (t <> tag (PA dop)) ==>
    (ca' t = if evpol ca (PA dop) = SOME t 
	     then NONE
	     else ca t)
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
	 else (if ldirty_ ca (THE (evpol ca (PA dop))) /\
	          THE (evpol ca (PA dop)) <> tag (PA dop) 
	       then SOME (THE (evpol ca (PA dop)),
			  lcnt_ ca (THE (evpol ca (PA dop))))
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
  RW_TAC std_ss [cdirty_def, ctf_ca_wt_lem, dirty__def]
);

val ctf_rd_hit_oblg = store_thm("ctf_rd_hit_oblg", ``
!ca mv dop ca' y. CA dop /\ rd dop /\ chit_ ca (PA dop) 
	       /\ ((ca',y) = ctf ca mv dop) ==>
    (ca' (tag (PA dop)) = ca (tag (PA dop)))
``,
  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [ctf_lem] >>
  RW_TAC std_ss [ctf_ca_rd_lem] >>
  FULL_SIMP_TAC std_ss [chit_def]
);

val ctf_rd_miss_oblg = store_thm("ctf_rd_miss_oblg", ``
!ca mv dop ca' y. CA dop /\ rd dop /\ ~chit_ ca (PA dop) 
	       /\ ((ca',y) = ctf ca mv dop) ==>
    chit_ ca' (PA dop) 
 /\ (ccnt_ ca' (PA dop) = lv mv T (PA dop))
 /\ (ccntw_ ca' (PA dop) = mv T (PA dop))
 /\ ~cdirty_ ca' (PA dop)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [ctf_lem] >>
  STRIP_TAC >- (
      (* chit *)
      RW_TAC std_ss [chit_def, hit_def, ctf_ca_rd_lem]
  ) >> 
  STRIP_TAC >- (
      (* ccnt *)
      RW_TAC std_ss [ccnt_def, cnt_def, ctf_ca_rd_lem] >>
      FULL_SIMP_TAC std_ss [chit_def]
  ) >>
  STRIP_TAC >- (
      (* ccntw *)
      RW_TAC std_ss [ccntw_def, ccnt_def, ctf_ca_rd_lem]
      >| [(* miss -> contradiction *)
	  FULL_SIMP_TAC std_ss [chit_def]
	  ,
	  (* hit *) 
	  RW_TAC std_ss [cnt_def, lv_def, lw_def, the_line_def]
	 ]
  ) >>
      (* not_dirty *)
      RW_TAC std_ss [ctf_ca_rd_lem, not_cdirty_lem] >>
      FULL_SIMP_TAC std_ss [chit_def]
);

val ctf_wt_fill_oblg = store_thm("ctf_wt_fill_oblg", ``
!ca mv dop ca' y pa. CA dop /\ wt dop /\ pa <> PA dop /\ (tag pa = tag (PA dop))
	          /\ ~chit_ ca (PA dop) /\ ((ca',y) = ctf ca mv dop) ==>
    chit_ ca' pa 
 /\ (ccntw_ ca' pa = mv T pa)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [ctf_lem] >>
  STRIP_TAC >- (
      (* chit *)
      RW_TAC std_ss [chit_def, hit_def, ctf_ca_wt_lem]
  ) >> 
      (* ccntw *)
      Cases_on `pa` >>
      Cases_on `PA dop` >>
      FULL_SIMP_TAC std_ss [tag_def, the_adr_def]
);

val ctf_wt_ccnt_oblg = store_thm("ctf_wt_ccnt_oblg", ``
!ca mv dop ca' y. CA dop /\ wt dop /\ ((ca',y) = ctf ca mv dop) ==>
    (ccntw_ ca' (PA dop) = VAL dop) 
 /\ (!pa. chit_ ca pa /\ pa <> PA dop /\ (tag pa = tag (PA dop)) ==> 
	      (ccntw_ ca' pa = ccntw_ ca pa))
``,
  REPEAT GEN_TAC >> 
  STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [ctf_lem] >>
  RW_TAC std_ss [ctf_ca_wt_lem, ccntw_def, ccnt_def, ccntw_def]
  >| [(* written part *)
      RW_TAC std_ss [lw_def, cnt_def, the_line_def]
      ,
      (* other parts -> contradiction *)
      FULL_SIMP_TAC std_ss [tag_def, the_adr_inj]
     ]
);

val ctf_wb_not_cl_evpol_oblg = store_thm("ctf_wb_not_cl_evpol_oblg", ``
!ca mv dop ca' t v. CA dop /\ ~cl dop /\ ((ca',SOME(t,v)) = ctf ca mv dop) ==>
    (t = THE (evpol ca (PA dop))) /\ (v = lcnt_ ca t) /\ ldirty_ ca t 
``,
  REPEAT STRIP_TAC >> (
      REV_FULL_SIMP_TAC std_ss [ctf_lem, ctf_wb_not_cl_lem] >>
      FULL_SIMP_TAC std_ss [] >>
      REV_FULL_SIMP_TAC std_ss []
  )
);

val ctf_wb_not_cl_evpol_some_oblg = store_thm("ctf_wb_not_cl_evpol_some_oblg", ``
!ca mv dop ca' t v. CA dop /\ ~cl dop /\ ((ca',SOME(t,v)) = ctf ca mv dop) ==>
    (evpol ca (PA dop) = SOME t)
``,
  REPEAT STRIP_TAC >> 
  REV_FULL_SIMP_TAC std_ss [ctf_lem, ctf_wb_not_cl_lem] >>
  FULL_SIMP_TAC std_ss [GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE] >>
  FULL_SIMP_TAC std_ss [optionTheory.IS_SOME_EXISTS] >>
  METIS_TAC [optionTheory.THE_DEF]
);


val evpol_oblg = save_thm("evpol_oblg", evpol_spec);

(*********** finish ************)

val _ = export_theory();
