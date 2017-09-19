(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;
open cacheIfTheory;

val _ = new_theory "cachemem";

(* assumptions on the cache model:
- at most one write back per access 
- read/written addresses are not evicted / guaranteed hit in post state
- word granularity
*)

(* helper functions *)

val EQ_NOT_EQ = store_thm("EQ_NOT_EQ", ``(A = B) <=> (~A = ~B)``, PROVE_TAC []);

fun INV_EQ_RULE x = x |> CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV (EQ_NOT_EQ)))
		      |> REWRITE_RULE [boolTheory.NOT_CLAUSES];

(* imported cache lemmas *)

val chit_lem = store_thm("chit_lem", ``
!pa ca ca'. (ca pa = ca' pa) ==> (chit_ ca pa <=> chit_ ca' pa)
``,
  REWRITE_TAC [chit_oblg]
);

val ccnt_lem = store_thm("ccnt_lem", ``
!pa ca ca'. (ca pa = ca' pa) ==> (ccnt_ ca pa = ccnt_ ca' pa)
``,
  REWRITE_TAC [ccnt_oblg]
);

val ccnt_not_eq_lem = store_thm("ccnt_not_eq_lem", ``
!pa ca ca'. chit_ ca pa /\ chit_ ca' pa /\ (cdirty_ ca pa <=> cdirty_ ca' pa)
         /\ (ca pa <> ca' pa) ==> 
    (ccnt_ ca pa <> ccnt_ ca' pa)
``,
  REWRITE_TAC [ccnt_not_eq_oblg]
);

val miss_lem = store_thm("miss_lem", ``
!ca pa. ~chit_ ca pa <=> (ca pa = NONE)
``,
  REWRITE_TAC [miss_oblg]
);

val cdirty_lem = store_thm("cdirty_lem", ``
!pa ca ca'. (ca pa = ca' pa) ==> (cdirty_ ca pa <=> cdirty_ ca' pa)
``,
  REWRITE_TAC [cdirty_oblg]
);

val cdirty_chit_lem = store_thm("cdirty_chit_lem", ``
!ca pa. cdirty_ ca pa ==> chit_ ca pa
``,
  REWRITE_TAC [cdirty_chit_oblg]
);

val not_chit_not_cdirty_lem = store_thm("not_chit_not_cdirty_lem", ``
!ca pa. ~chit_ ca pa ==> ~cdirty_ ca pa 
``,
  REWRITE_TAC [not_chit_not_cdirty_oblg]
);

val ctf_chit_lem = store_thm("ctf_chit_lem", ``
!ca mv dop ca' y. CA dop /\ ~cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    chit_ ca' (PA dop)
``,
  REWRITE_TAC [ctf_chit_oblg]
);

val ctf_cl_miss_lem = store_thm("ctf_cl_miss_lem", ``
!ca mv dop ca' y. cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    ~chit_ ca' (PA dop)
``,
  REWRITE_TAC [ctf_cl_miss_oblg]
);

val ctf_cl_other_lem = store_thm("ctf_cl_other_lem", ``
!ca mv dop ca' y pa. cl dop /\ ((ca',y) = ctf ca mv dop) /\ (pa <> PA dop) ==>
    (ca' pa = ca pa)
``,
  REWRITE_TAC [ctf_cl_other_oblg]
);

val ctf_cl_wb_lem = store_thm("ctf_cl_wb_lem", ``
!ca mv dop ca' y pa. cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    (y = if cdirty_ ca (PA dop)
	 then SOME (PA dop, ccnt_ ca (PA dop))
	 else NONE)
``,
  REWRITE_TAC [ctf_cl_wb_oblg]
);

val ctf_not_cl_other_lem = store_thm("ctf_not_cl_other_lem", ``
!ca mv dop ca' y pa. CA dop /\ ~cl dop /\ ((ca',y) = ctf ca mv dop) 
		  /\ (pa <> PA dop) ==>
    (ca' pa = if evpol ca (PA dop) = SOME pa 
	      then NONE
	      else ca pa)
``,
  REWRITE_TAC [ctf_not_cl_other_oblg]
);

val clean_inv = Define `clean_inv ca = !pa. ~cdirty_ ca pa`;

val ctf_not_cl_wb_lem = store_thm("ctf_not_cl_wb_lem", ``
!ca mv dop ca' y. CA dop /\ ~cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    ((y = if evpol ca (PA dop) = NONE
	  then NONE
	  else (if cdirty_ ca (THE (evpol ca (PA dop))) /\
	  	   THE (evpol ca (PA dop)) <> PA dop
		then SOME (THE (evpol ca (PA dop)),
			   ccnt_ ca (THE (evpol ca (PA dop))))
		else NONE)) 
(* WT case *)
  \/ (y = if wt dop 
	  then SOME (PA dop, VAL dop)
	  else NONE) /\ clean_inv ca)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC ctf_not_cl_wb_oblg >>
  ASM_REWRITE_TAC []
);

val ctf_wt_cdirty_lem = store_thm("ctf_wt_cdirty_lem", ``
!ca mv dop ca' y. CA dop /\ wt dop /\ ((ca',y) = ctf ca mv dop) ==>
    (cdirty_ ca' (PA dop) 
(* WT case *)
  \/ ~cdirty_ ca' (PA dop) /\ (y = SOME (PA dop, VAL dop)))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC ctf_wt_cdirty_oblg >>
  ASM_REWRITE_TAC []
);

val ctf_rd_hit_lem = store_thm("ctf_rd_hit_lem", ``
!ca mv dop ca' y. CA dop /\ rd dop /\ chit_ ca (PA dop) 
	       /\ ((ca',y) = ctf ca mv dop) ==>
    (ca' (PA dop) = ca (PA dop))
``,
  REWRITE_TAC [ctf_rd_hit_oblg]
);

val ctf_rd_miss_lem = store_thm("ctf_rd_miss_lem", ``
!ca mv dop ca' y. CA dop /\ rd dop /\ ~chit_ ca (PA dop) 
	       /\ ((ca',y) = ctf ca mv dop) ==>
    chit_ ca' (PA dop) 
 /\ (ccnt_ ca' (PA dop) = mv T (PA dop))
 /\ ~cdirty_ ca' (PA dop)
``,
  REWRITE_TAC [ctf_rd_miss_oblg]
);

val ctf_wt_ccnt_lem = store_thm("ctf_wt_ccnt_lem", ``
!ca mv dop ca' y. CA dop /\ wt dop /\ ((ca',y) = ctf ca mv dop) ==>
    (ccnt_ ca' (PA dop) = VAL dop)
``,
  REWRITE_TAC [ctf_wt_ccnt_oblg]
);

val ctf_wb_not_cl_evpol_lem = store_thm("ctf_wb_evpol_lem", ``
!ca mv dop ca' pa v. CA dop /\ ~cl dop /\ ((ca',SOME(pa,v)) = ctf ca mv dop) ==>
    ((pa = THE (evpol ca (PA dop))) /\ (v = ccnt_ ca pa) /\ cdirty_ ca pa
(* WT case *)
  \/ wt dop /\ (pa = PA dop) /\ (v = VAL dop) /\ ~cdirty_ ca pa)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC ctf_wb_not_cl_evpol_oblg >>
  ASM_REWRITE_TAC []
);

val ctf_wb_not_cl_evpol_some_lem = store_thm("ctf_wb_not_cl_evpol_some_lem", ``
!ca mv dop ca' pa v. CA dop /\ ~cl dop /\ ((ca',SOME(pa,v)) = ctf ca mv dop) ==>
    ((evpol ca (PA dop) = SOME pa)
(* WT case *)
  \/ wt dop /\ (pa = PA dop))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC ctf_wb_not_cl_evpol_some_oblg >>
  ASM_REWRITE_TAC []
);

val evpol_lem = store_thm("evpol_lem", ``
!ca pa. evpol ca pa <> SOME pa
``,
  REWRITE_TAC [evpol_oblg]
);

(* some derived lemmas *)

val ctf_ca_cases_other = store_thm("ctf_ca_cases_other", ``
!ca mv dop ca' y pa. CA dop /\ ((ca',y) = ctf ca mv dop) /\ (pa <> PA dop) ==>
    ((ca' pa = NONE) \/ (ca' pa = ca pa))
``,
  REPEAT STRIP_TAC >>
  Cases_on `cl dop` 
  >| [(* cl *)
      IMP_RES_TAC ctf_cl_other_lem >>
      ASM_REWRITE_TAC []
      ,
      (* not cl *)
      METIS_TAC [ctf_not_cl_other_lem]
     ]
);

val wb_NONE_cases_def = Define `wb_NONE_cases ca dop = 
    clean_inv ca /\ ~wt dop 
 \/ (evpol ca (PA dop) = NONE)
 \/ (~cdirty_ ca (THE (evpol ca (PA dop))))
 \/ cl dop /\ (~cdirty_ ca (PA dop))
`;

val ctf_wb_cases = store_thm("ctf_wb_cases", ``
!ca mv dop ca' y. CA dop /\ ((ca',y) = ctf ca mv dop) ==>
    (   (y = NONE) /\ wb_NONE_cases ca dop
     \/ (?pa. (y = SOME(pa, ccnt_ ca pa)) /\ (if cl dop 
					      then pa = PA dop
					      else pa <> PA dop))
     \/ wt dop /\ (y = SOME (PA dop, VAL dop)) /\ clean_inv ca)
``,
  REPEAT STRIP_TAC >>
  Cases_on `cl dop` 
  >| [(* cl *)
      Cases_on `cdirty_ ca (PA dop)`
      >| [(* dirty *)
	  DISJ2_TAC >>
	  DISJ1_TAC >>
          EXISTS_TAC ``PA dop`` >>
	  IMP_RES_TAC ctf_cl_wb_lem >>
	  ASM_REWRITE_TAC []
	  ,
	  (* clean *) 
	  DISJ1_TAC >>
	  IMP_RES_TAC ctf_cl_wb_lem >>
	  ASM_REWRITE_TAC [wb_NONE_cases_def]
	 ]
      ,
      (* not cl *)
      IMP_RES_TAC ctf_not_cl_wb_lem >> (
          TRY ( METIS_TAC [wb_NONE_cases_def] )
      ) >>
      Cases_on `evpol ca (PA dop) = NONE`
      >| [(* NONE *)
	  FULL_SIMP_TAC std_ss [wb_NONE_cases_def]
	  ,
	  (* SOME pa *) 
	  `THE (evpol ca (PA dop)) <> PA dop` by (
	      METIS_TAC [quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,
			 optionTheory.IS_SOME_EXISTS, 
			 optionTheory.THE_DEF,
			 evpol_lem]
	  ) >>
	  Cases_on `cdirty_ ca (THE (evpol ca (PA dop)))`
	  >| [(* dirty *)
	      FULL_SIMP_TAC std_ss []
	      ,
	      FULL_SIMP_TAC std_ss [wb_NONE_cases_def]
	     ]
	 ]
     ]
);

val ctf_chit_evpol_lem = store_thm("ctf_chit_evpol_lem", ``
!ca mv dop ca' y pa. CA dop /\ ~cl dop /\ ((ca',y) = ctf ca mv dop) 
		  /\ (pa <> PA dop) /\ chit_ ca' pa ==>
    (evpol ca (PA dop) <> SOME pa)
``,
  RW_TAC std_ss [INV_EQ_RULE miss_lem] >>
  IMP_RES_TAC ctf_not_cl_other_lem >>
  FULL_SIMP_TAC std_ss []
);

val ctf_not_cl_chit_lem = store_thm("ctf_not_cl_chit_lem", ``
!ca mv dop ca' y pa. CA dop /\ ~cl dop /\ pa <> PA dop
		  /\ ((ca', y) = ctf ca mv dop) ==>
    (chit_ ca' pa <=> chit_ ca pa /\ evpol ca (PA dop) <> SOME pa)
``,
  RW_TAC std_ss [] >>
  EQ_TAC
  >| [(* ==> *)
      RW_TAC std_ss []
      >| [(* chit *)
	  CCONTR_TAC >>
	  IMP_RES_TAC miss_lem >>
	  `ca' pa <> NONE` by ( FULL_SIMP_TAC std_ss [INV_EQ_RULE miss_lem] ) >>
	  METIS_TAC [ctf_ca_cases_other]
	  ,
	  (* evpol <> pa *)
	  CCONTR_TAC >> 
	  IMP_RES_TAC ctf_not_cl_other_lem >>
	  `ca' pa <> NONE` by ( FULL_SIMP_TAC std_ss [INV_EQ_RULE miss_lem] ) >>
	  REV_FULL_SIMP_TAC std_ss []
	 ]
      ,
      (* <== *)
      RW_TAC std_ss [INV_EQ_RULE miss_lem] >>
      `ca pa <> NONE` by ( FULL_SIMP_TAC std_ss [INV_EQ_RULE miss_lem] ) >>
      IMP_RES_TAC ctf_not_cl_other_lem >>
      REV_FULL_SIMP_TAC std_ss []
     ]	  
);

val ctf_rd_cdirty_lem = store_thm("ctf_rd_cdirty_lem", ``
!ca mv dop ca' y. CA dop /\ rd dop /\ ((ca',y) = ctf ca mv dop) ==>
    (cdirty_ ca' (PA dop) <=> cdirty_ ca (PA dop))
``,
  REPEAT STRIP_TAC >>   
  Cases_on `chit_ ca (PA dop)` 
  >| [(* hit *)
      MATCH_MP_TAC cdirty_lem >>
      IMP_RES_TAC ctf_rd_hit_lem
      ,
      (* miss *)
      IMP_RES_TAC not_chit_not_cdirty_lem >>
      IMP_RES_TAC ctf_rd_miss_lem >>
      FULL_SIMP_TAC std_ss []
     ]
);

val ctf_not_cl_cdirty_lem = store_thm("ctf_not_cl_cdirty_lem", ``
!ca mv dop ca' y pa. CA dop /\ ~cl dop /\ pa <> PA dop
		  /\ ((ca', y) = ctf ca mv dop) ==>
    (cdirty_ ca' pa <=> cdirty_ ca pa /\ evpol ca (PA dop) <> SOME pa)
``,
  RW_TAC std_ss [] >>
  EQ_TAC
  >| [(* ==> *)
      RW_TAC std_ss []
      >| [(* cdirty *)
	  IMP_RES_TAC cdirty_chit_lem >> 
	  IMP_RES_TAC (INV_EQ_RULE miss_lem) >>
	  IMP_RES_TAC ctf_ca_cases_other >>
	  IMP_RES_TAC cdirty_lem
	  ,
	  (* evpol <> pa *)
	  IMP_RES_TAC cdirty_chit_lem >> 
	  IMP_RES_TAC ctf_chit_evpol_lem
	 ]
      ,
      (* <== *)
      RW_TAC std_ss [] >>
      IMP_RES_TAC cdirty_chit_lem >> 
      IMP_RES_TAC ctf_not_cl_other_lem >> 
      REV_FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC cdirty_lem 
     ]	  
);

val ctf_cl_chit_other_lem = store_thm("ctf_cl_chit_other_lem", ``
!ca mv dop ca' y pa. cl dop /\ ((ca',y) = ctf ca mv dop) /\ (pa <> PA dop) ==>
    (chit_ ca' pa <=> chit_ ca pa)
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC chit_lem >>
  IMP_RES_TAC ctf_cl_other_lem
);

val ctf_cl_cdirty_lem = store_thm("ctf_cl_cdirty_lem", ``
!ca mv dop ca' y. cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    ~cdirty_ ca' (PA dop)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC ctf_cl_miss_lem >>
  IMP_RES_TAC not_chit_not_cdirty_lem
);

val ctf_cl_cdirty_other_lem = store_thm("ctf_cl_cdirty_other_lem", ``
!ca mv dop ca' y pa. cl dop /\ ((ca',y) = ctf ca mv dop) /\ (pa <> PA dop) ==>
    (cdirty_ ca' pa <=> cdirty_ ca pa)
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC cdirty_lem >>
  IMP_RES_TAC ctf_cl_other_lem
);

val ctf_wb_dirty_lem = store_thm("ctf_wb_dirty_lem", ``
!ca mv dop ca' y pa v. CA dop /\ ((ca',SOME(pa,v)) = ctf ca mv dop) ==>
    (cdirty_ ca pa \/ wt dop /\ (pa = PA dop))
``,
  REPEAT STRIP_TAC >>
  Cases_on `cl dop` 
  >| [(* clean *)
      Cases_on `pa = PA dop` >> (
	  IMP_RES_TAC ctf_cl_wb_lem >>
	  REV_FULL_SIMP_TAC std_ss []
      )
      ,
      (* read or write *)
      IMP_RES_TAC ctf_not_cl_wb_lem >> ( 
          Cases_on `pa = THE (evpol ca (PA dop))` >> (
	      REV_FULL_SIMP_TAC std_ss [] >>
	      METIS_TAC []
	  )
      )
     ]
);

(* memory state and memory view *)

val _ = Parse.type_abbrev("mem_state", ``:padr -> word``);

(* cacheless memory view *)
val MVcl_def = Define `MVcl (m:mem_state) = 
\(c:bool) pa. m pa
`;

val MVcl_lem = store_thm("MVcl_lem", ``
!m m'. (MVcl m = MVcl m') <=> (m = m')
``,
  RW_TAC std_ss [MVcl_def, boolTheory.ETA_AX] >>
  EQ_TAC 
  >| [(* ==> *)
      METIS_TAC []
      ,
      (* <== *)
      RW_TAC std_ss []
     ]
);

(* cache-aware memory view *)
val MVca_def = Define `MVca ca m = 
\c pa. if c /\ chit_ ca pa then ccnt_ ca pa else m pa
`;

val MVca_lem = store_thm("MVca_lem", ``
!ca m pa c ca' m'. (ca' pa = ca pa) /\ (m' pa = m pa) ==>
    ((MVca ca' m') c pa = (MVca ca m) c pa)
``,
  RW_TAC std_ss [MVca_def]
  >| [(* ccnt *)
      IMP_RES_TAC ccnt_lem
      ,
      (* ~hit and hit' -> contradiction *)
      IMP_RES_TAC chit_lem >>
      FULL_SIMP_TAC std_ss []
      ,
      (* hit and ~hit' -> contradiction *)
      IMP_RES_TAC chit_lem >>
      FULL_SIMP_TAC std_ss []
     ]      
)

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

val wb_mem_def = Define `
   (wb_mem m NONE = m)
/\ (wb_mem m (SOME (pa,w)) = (pa =+ w) m)
`;

val wb_mem_upd_lem = store_thm("wb_mem_upd_lem", ``
!m pa w. wb_mem m (SOME (pa,w)) pa = w
``,
  RW_TAC std_ss [wb_mem_def, combinTheory.UPDATE_APPLY]
);

val wb_mem_upd_other_lem = store_thm("wb_mem_upd_other_lem", ``
!m pa pa' w. pa <> pa' ==> (wb_mem m (SOME (pa,w)) pa' = m pa')
``,
  RW_TAC std_ss [wb_mem_def, combinTheory.UPDATE_APPLY]
);

val wb_lem = store_thm("wb_lem", ``
!ca m w. wb (ca,w) m = (ca,wb_mem m w)
``,
  Cases_on `w`
  >| [(* NONE *)
      RW_TAC std_ss [wb_def, wb_mem_def]
      ,
      (* SOME x *)
      REPEAT STRIP_TAC >>
      `?c w. x = (c,w)` by (
          RW_TAC std_ss [pairTheory.pair_CASES]
      ) >>
      RW_TAC std_ss [wb_def, wb_mem_def]
     ]
);

val wb_ca_lem = store_thm("wb_ca_lem", ``
!ca m ca' y m'. ((ca,m) = wb (ca',y) m') ==> (ca = ca')
``,
  REPEAT STRIP_TAC >>  
  Cases_on `y` 
  >| [(* NONE *)
      FULL_SIMP_TAC std_ss [wb_def]
      ,
      (* SOME x *)
      `?pa w. x = (pa,w)` by ( RW_TAC std_ss [pairTheory.pair_CASES] ) >>
      FULL_SIMP_TAC std_ss [wb_def]
     ]  
);

(* cache-aware *)
val mtfca_def = Define `
   (mtfca (ca,m) (RD pa T)   = wb (ctf ca (MVcl m) (RD pa T)) m)
/\ (mtfca (ca,m) (WT pa w T) = wb (ctf ca (MVcl m) (WT pa w T)) m)
/\ (mtfca (ca,m) (WT pa w F) = (ca,(pa =+ w) m))
/\ (mtfca (ca,m) (CL pa)     = wb (ctf ca (MVcl m) (CL pa)) m)
/\ (mtfca (ca,m) _           = (ca,m))
`;

(* some useful lemmas *)

val mtfca_cacheable = store_thm("mtfca_cacheable", ``
!ca m dop. CA dop ==> (mtfca (ca,m) dop = wb (ctf ca (MVcl m) dop) m)
``,
  RW_TAC std_ss [CA_lem] >> (
      RW_TAC std_ss [mtfca_def]
  )
);


val cl_mem_unchanged = store_thm("cl_mem_unchanged", ``
!m dop m'. ~wt dop /\ (m' = mtfcl m dop) ==>
(MVcl m = MVcl m')
``,
  RW_TAC std_ss [not_wt_lem, rd_lem, cl_lem] >> (
      RW_TAC std_ss [mtfcl_def]
  )
);    

val cl_write_semantics = store_thm("cl_write_semantics", ``
!m m' pa w c. (mtfcl m (WT pa w c) = m') ==>
   (!c. (MVcl m') c pa = w) 
/\ (!pa' c. pa <> pa' ==> ((MVcl m) c pa' = (MVcl m') c pa'))
``,
  RW_TAC std_ss [MVcl_def, mtfcl_def] >> (
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  )
); 

val cl_other_unchanged_lem = store_thm("cl_other_unchanged_lem", ``
!m m' dop pa. (m' = mtfcl m dop) /\ (pa <> PA dop)  ==>
    (m' pa = m pa)
``,
  Cases_on `dop` >> (
      RW_TAC std_ss [mtfcl_def, combinTheory.APPLY_UPDATE_THM, PA_def]
  )
); 


val ca_uncacheable = store_thm("ca_uncacheable", ``
!ca m dop ca' m'. ~CA dop /\ ((ca',m') = mtfca (ca,m) dop) ==>
   (ca' = ca) /\ (m' = mtfcl m dop)
``,
  RW_TAC std_ss [not_CA_lem] >> (
      FULL_SIMP_TAC std_ss [mtfca_def, mtfcl_def]
  )
);

val ca_cl_reduction = store_thm("ca_cl_reduction", ``
!ca m c. MVca ca m F = MVcl m c 
``,
  RW_TAC std_ss [MVcl_def, MVca_def]
);

val ctf_pat = ``(x,y) = ctf a b c``; 

val SYM_CTF_TAC = PAT_X_ASSUM ctf_pat (fn thm => ASSUME_TAC (SYM thm));

val ctf_pat2 = ``ctf a b c = (x,y)``; 

val SYM_CTF_TAC2 = PAT_X_ASSUM ctf_pat2 (fn thm => ASSUME_TAC (SYM thm));

val ca_cacheable_mem = store_thm("ca_cacheable_mem", ``
!ca m dop ca' m'. CA dop /\ ((ca',m') = mtfca (ca,m) dop) ==>
    !pa. (m' pa = m pa) 
      \/ cdirty_ ca pa /\ (m' pa = ccnt_ ca pa) /\ 
	 (if cl dop then pa = PA dop else pa <> PA dop)
(* WT case *)
      \/ wt dop /\ (m' pa = ccnt_ ca' pa) /\ (pa = PA dop)
``,
  RW_TAC (std_ss++boolSimps.CONJ_ss) [mtfca_cacheable] >>
  `?ca'' y. (ca'',y) = ctf ca (MVcl m) dop` by (
      METIS_TAC [pairTheory.pair_CASES]
  ) >>
  Cases_on `cl dop`
  >| [(* clean *)
      `~wt dop` by ( METIS_TAC [dop_cases_lem2] ) >>
      IMP_RES_TAC ctf_wb_cases >> ( FULL_SIMP_TAC std_ss [] )
      >| [(* wb NONE *)
	  RW_TAC (srw_ss()) [] >>
          SYM_CTF_TAC >>
	  FULL_SIMP_TAC std_ss [wb_def]
	  ,
	  (* wb SOME (pa',v) *) 
	  RW_TAC std_ss [] >>
	  IMP_RES_TAC ctf_wb_dirty_lem >> 
          SYM_CTF_TAC >>
	  FULL_SIMP_TAC std_ss [wb_def] >>
	  REV_FULL_SIMP_TAC std_ss [] >>
	  Cases_on `pa = pa'` >> (
              RW_TAC std_ss [combinTheory.UPDATE_APPLY]
	  )
	 ]
      ,
      (* read or write *)
      Cases_on `wt dop`
      >| [(* write *)
	  RW_TAC std_ss [] >>
	  IMP_RES_TAC ctf_wt_ccnt_lem >>
          IMP_RES_TAC ctf_wb_cases >> ( FULL_SIMP_TAC std_ss [] ) >- (
	      (* wb NONE *)
	      RW_TAC (srw_ss()) [] >>
	      SYM_CTF_TAC >>
	      FULL_SIMP_TAC std_ss [wb_def]
	  ) >> (
	      (* wb SOME (pa',v) *) 
              IMP_RES_TAC ctf_wb_dirty_lem >> (
	          PAT_X_ASSUM ``(x, SOME (y,z)) = ctf a b c`` 
                              (fn thm => ASSUME_TAC (SYM thm)) >>
	          FULL_SIMP_TAC std_ss [wb_def] >>
	          REV_FULL_SIMP_TAC std_ss [] >>
		  Cases_on `pa = pa'` >> (
                      RW_TAC std_ss [combinTheory.UPDATE_APPLY]
		  ) >>
		  Cases_on `pa = PA dop` >> (
		      RW_TAC std_ss [combinTheory.UPDATE_APPLY]
		  )
	      )
	  )
	  ,
	  (* read *) 
	  IMP_RES_TAC ctf_wb_cases >> ( FULL_SIMP_TAC std_ss [] )
	  >| [(* wb NONE *)
	      RW_TAC (srw_ss()) [] >>
	      SYM_CTF_TAC >>
	      FULL_SIMP_TAC std_ss [wb_def]
	      ,
	      (* wb SOME (pa',v) *) 
	      RW_TAC std_ss [] >>
	      IMP_RES_TAC ctf_wb_dirty_lem >> 
              SYM_CTF_TAC >>
	      FULL_SIMP_TAC std_ss [wb_def] >>
	      REV_FULL_SIMP_TAC std_ss [] >>
	      Cases_on `pa = pa'` >> (
                  RW_TAC std_ss [combinTheory.UPDATE_APPLY]
	      )
	     ]
	 ]
     ]
);

val ca_cacheable_ca = store_thm("ca_cacheable_ca", ``
!ca m dop ca' m'. CA dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    !pa. chit_ ca pa /\ chit_ ca' pa /\ (ccnt_ ca' pa = ccnt_ ca pa) /\ 
	 (cdirty_ ca pa <=> cdirty_ ca' pa) /\ (rd dop \/ pa <> PA dop)
      \/ chit_ ca' pa /\ (ccnt_ ca' pa = m pa) /\ rd dop /\ (pa = PA dop)
      \/ chit_ ca' pa /\ (ccnt_ ca' pa = VAL dop) /\ wt dop /\ (pa = PA dop)
      \/ ~chit_ ca' pa /\ (cl dop \/ pa <> PA dop)
``,
  RW_TAC (std_ss++boolSimps.CONJ_ss) [mtfca_cacheable] >>
  `?ca'' y. (ca'',y) = ctf ca (MVcl m) dop` by (
      METIS_TAC [pairTheory.pair_CASES]
  ) >>
  SYM_CTF_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC wb_ca_lem >>
  SYM_CTF_TAC2 >>
  Cases_on `cl dop`
  >| [(* clean *)
      Cases_on `pa = PA dop` 
      >| [(* PA dop *)
	  IMP_RES_TAC ctf_cl_miss_lem >>
          FULL_SIMP_TAC std_ss []
	  ,
	  (* other pa *)
	  IMP_RES_TAC ctf_cl_other_lem >>
	  RW_TAC std_ss [ccnt_lem] >>
	  METIS_TAC [chit_lem, cdirty_lem]
	 ]
      ,
      (* read or write *)
      Cases_on `pa = PA dop` 
      >| [(* PA dop *)
	  IMP_RES_TAC ctf_chit_lem >>
	  FULL_SIMP_TAC std_ss [not_cl_lem]
	  >| [(* read *)
	      Cases_on `chit_ ca (PA dop)`
	      >| [(* hit *)
		  IMP_RES_TAC ctf_rd_hit_lem >>
	          RW_TAC std_ss [ccnt_lem, cdirty_lem]
		  ,
		  (* miss *)
		  IMP_RES_TAC ctf_rd_miss_lem >>
	          FULL_SIMP_TAC std_ss [MVcl_def]
		 ]
	      ,
	      (* write *)
	      IMP_RES_TAC ctf_wt_ccnt_lem >>
	      IMP_RES_TAC ctf_wt_cdirty_lem >>
	      RW_TAC std_ss []
	     ]
	  ,
	  (* other pa *)
	  IMP_RES_TAC ctf_not_cl_other_lem >>
          Cases_on `evpol ca (PA dop) = SOME pa`
	  >| [(* eviction -> no hit *)
	      FULL_SIMP_TAC std_ss [] >>
	      IMP_RES_TAC miss_lem >>
	      RW_TAC std_ss []
	      ,
	      FULL_SIMP_TAC std_ss [] >>
	      RW_TAC std_ss [ccnt_lem] >>
	      METIS_TAC [chit_lem, cdirty_lem]
	     ]
	 ]
     ]
);

val ca_cacheable_miss_lem = store_thm("ca_cacheable_miss_lem", ``
!ca m dop ca' m' pa. CA dop /\ ((ca',m') = mtfca (ca,m) dop) /\ ~chit_ ca' pa
        ==>
    (cl dop \/ pa <> PA dop)
``,
  RW_TAC std_ss [] >>
  IMP_RES_TAC ca_cacheable_ca >>
  PAT_X_ASSUM ``!pa. X`` (fn thm => ASSUME_TAC (ISPEC ``pa:padr`` thm)) >>
  METIS_TAC [cdirty_chit_lem]
);

val ca_cacheable_hit_lem = store_thm("ca_cacheable_hit_lem", ``
!ca m dop ca' m'. CA dop /\ ((ca',m') = mtfca (ca,m) dop) /\ ~cl dop 
        ==> 
    chit_ ca' (PA dop)
``,
  METIS_TAC [ca_cacheable_miss_lem]
);

val cacheable_cl_lem = store_thm("cacheable_cl_lem", ``
!ca m dop ca' m'. cl dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    ~chit_ ca' (PA dop) 
 /\ ((m' (PA dop) = m (PA dop)) \/ (m' (PA dop) = ccnt_ ca (PA dop)))
``,
  RW_TAC std_ss [] >> ( IMP_RES_TAC cl_CA_lem ) 
  >| [(* miss *)
      FULL_SIMP_TAC std_ss [mtfca_cacheable] >>
      `?ca'' y. (ca'',y) = ctf ca (MVcl m) dop` by (
          METIS_TAC [pairTheory.pair_CASES]
      ) >>
      IMP_RES_TAC ctf_cl_miss_lem >>
      SYM_CTF_TAC >>
      FULL_SIMP_TAC std_ss [wb_lem]
      ,
      (* mem equal or cache content *)
      `~rd dop /\ ~wt dop` by ( 
          METIS_TAC [not_cl_lem] 
      ) >>
      IMP_RES_TAC ca_cacheable_mem >>
      PAT_X_ASSUM ``!pa. X`` ( fn thm => ASSUME_TAC ( SPEC ``PA dop`` thm ) ) >>
      REV_FULL_SIMP_TAC std_ss []
     ]
);

val cacheable_cl_other_lem = store_thm("cacheable_cl_other_lem", ``
!ca m dop ca' m' pa. cl dop /\ ((ca',m') = mtfca (ca,m) dop) /\ (pa <> PA dop)
        ==>
    (ca' pa = ca pa) /\ (m' pa = m pa)
``,
  RW_TAC std_ss [] >> ( IMP_RES_TAC cl_CA_lem )
  >| [(* cache unchanged *)
      FULL_SIMP_TAC std_ss [mtfca_cacheable] >>
      `?ca'' y. (ca'',y) = ctf ca (MVcl m) dop` by (
          METIS_TAC [pairTheory.pair_CASES]
      ) >>
      IMP_RES_TAC ctf_cl_other_lem >>
      SYM_CTF_TAC >>
      FULL_SIMP_TAC std_ss [wb_lem]
      ,
      (* mem unchanged *)
      `~rd dop /\ ~wt dop` by ( 
          METIS_TAC [not_cl_lem] 
      ) >>
      IMP_RES_TAC ca_cacheable_mem >>
      PAT_X_ASSUM ``!pa. X`` ( fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) ) >>
      REV_FULL_SIMP_TAC std_ss [] 
     ]
);

val ca_cacheable_cl_lem = store_thm("ca_cacheable_cl_lem", ``
!ca m dop ca' m' pa. cl dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    (~chit_ ca' pa \/ (ca' pa = ca pa))
``,
  REPEAT STRIP_TAC >>
  Cases_on `pa = PA dop`
  >| [(* PA dop *)
      IMP_RES_TAC cacheable_cl_lem >> (
          FULL_SIMP_TAC std_ss []
      )
      ,
      (* other pa *)
      DISJ2_TAC >>
      IMP_RES_TAC cacheable_cl_other_lem
     ]
);

val mem_cacheable_cl_lem = store_thm("mem_cacheable_cl_lem", ``
!ca m dop ca' m' pa. cl dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    ((m' pa = m pa) \/ (m' pa = ccnt_ ca pa))
``,
  REPEAT STRIP_TAC >>
  Cases_on `pa = PA dop`
  >| [(* PA dop *)
      IMP_RES_TAC cacheable_cl_lem >> (
          FULL_SIMP_TAC std_ss []
      )
      ,
      (* other pa *)
      DISJ1_TAC >>
      IMP_RES_TAC cacheable_cl_other_lem
     ]
);

val mem_cacheable_cl_dirty_lem = store_thm("mem_cacheable_cl_dirty_lem", ``
!ca m dop ca' m'. cl dop /\ ((ca',m') = mtfca (ca,m) dop) /\ cdirty_ ca (PA dop)
        ==>
    (m' (PA dop) = ccnt_ ca (PA dop))
``,
  RW_TAC std_ss [] >> 
  IMP_RES_TAC cl_CA_lem >>
  FULL_SIMP_TAC std_ss [mtfca_cacheable] >>
  `?ca'' y. (ca'',y) = ctf ca (MVcl m) dop` by (
      METIS_TAC [pairTheory.pair_CASES]
  ) >>
  IMP_RES_TAC ctf_cl_wb_lem >>
  SYM_CTF_TAC >>
  FULL_SIMP_TAC std_ss [wb_lem, wb_mem_def] >>
  RW_TAC std_ss [combinTheory.UPDATE_APPLY]
);

val mem_cacheable_cl_miss_lem = store_thm("mem_cacheable_cl_miss_lem", ``
!ca m dop ca' m'. cl dop /\ ((ca',m') = mtfca (ca,m) dop) /\ ~chit_ ca (PA dop)
        ==>
    (m' (PA dop) = m (PA dop))
``,
  RW_TAC std_ss [] >> 
  IMP_RES_TAC cl_CA_lem >>
  `~wt dop` by ( METIS_TAC [not_cl_lem] ) >>
  IMP_RES_TAC not_chit_not_cdirty_lem >>
  IMP_RES_TAC ca_cacheable_mem >>
  PAT_X_ASSUM ``!pa. X`` ( fn thm => ASSUME_TAC ( SPEC ``PA dop`` thm) ) >>
  REV_FULL_SIMP_TAC std_ss []  
);

val mem_cacheable_not_cl_dirty_lem = 
store_thm("mem_cacheable_not_cl_dirty_lem", ``
!ca m dop ca' m' pa. CA dop /\ ~cl dop /\ ((ca',m') = mtfca (ca,m) dop) 
                  /\ (pa <> PA dop) /\ cdirty_ ca pa /\ ~chit_ ca' pa
        ==>
    (m' pa = ccnt_ ca pa)
``,
  RW_TAC std_ss [] >> 
  REV_FULL_SIMP_TAC std_ss [mtfca_cacheable] >>
  `?ca'' y. (ca'',y) = ctf ca (MVcl m) dop` by (
      METIS_TAC [pairTheory.pair_CASES]
  ) >>
  IMP_RES_TAC cdirty_chit_lem >>
  `evpol ca (PA dop) = SOME pa` by ( 
      IMP_RES_TAC ctf_not_cl_chit_lem >>
      SYM_CTF_TAC >>
      FULL_SIMP_TAC std_ss [wb_lem] >>
      METIS_TAC [] 
  ) >>
  IMP_RES_TAC ctf_wb_cases >> (
      FULL_SIMP_TAC std_ss [wb_NONE_cases_def, clean_inv] >>
      TRY ( METIS_TAC [optionTheory.NOT_SOME_NONE,
		       optionTheory.THE_DEF] )
  ) >>
  RW_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC ctf_wb_not_cl_evpol_lem >>
  FULL_SIMP_TAC std_ss [optionTheory.THE_DEF] >>
  SYM_CTF_TAC >>
  FULL_SIMP_TAC std_ss [wb_lem, wb_mem_def] >>
  REWRITE_TAC [combinTheory.UPDATE_APPLY]
);


(* deriveability lemmas *)

val ca_cacheable_other_lem = store_thm("ca_cacheable_other_lem", ``
!ca m dop ca' m' pa. CA dop /\ ((ca',m') = mtfca (ca,m) dop) /\ (pa <> PA dop)
                  /\ (ca' pa <> ca pa) ==> 
    ~chit_ ca' pa
``,
  RW_TAC std_ss [] >>
  IMP_RES_TAC ca_cacheable_ca >>
  PAT_X_ASSUM ``!pa. X`` (fn thm => ASSUME_TAC (ISPEC ``pa:padr`` thm)) >>
  FULL_SIMP_TAC std_ss [] >> (
      METIS_TAC [ccnt_not_eq_lem]
  )
);

val mem_cacheable_other_lem = store_thm("mem_cacheable_other_lem", ``
!ca m dop ca' m' pa. CA dop /\ ((ca',m') = mtfca (ca,m) dop) /\ (pa <> PA dop)
                  /\ (m' pa <> m pa) ==>
    cdirty_ ca pa /\ (m' pa = ccnt_ ca pa)
``,
  RW_TAC std_ss [] >>
  IMP_RES_TAC ca_cacheable_mem >> (
      PAT_X_ASSUM ``!pa. X`` (fn thm => ASSUME_TAC (ISPEC ``pa:padr`` thm)) >>
      FULL_SIMP_TAC std_ss [] >> 
      FULL_SIMP_TAC std_ss []
  )
);

val mem_cacheable_read_lem = store_thm("mem_cacheable_read_lem", ``
!ca m dop ca' m'. CA dop /\ rd dop /\ ((ca',m') = mtfca (ca,m) dop) ==>
    (m' (PA dop) = m (PA dop))
``,
  RW_TAC (std_ss++boolSimps.CONJ_ss) [mtfca_cacheable] >>
  `?ca'' y. (ca'',y) = ctf ca (MVcl m) dop` by (
      METIS_TAC [pairTheory.pair_CASES]
  ) >>
  SYM_CTF_TAC >>
  Cases_on `y`
  >| [(* NONE *)
      FULL_SIMP_TAC std_ss [wb_def]
      ,
      (* SOME (pa,v) *)
      `?pa v. x = (pa,v)` by (
          METIS_TAC [pairTheory.pair_CASES]
      ) >>
      FULL_SIMP_TAC std_ss [wb_def] >>
      SYM_CTF_TAC2 >>
      `~cl dop /\ ~wt dop` by ( METIS_TAC [dop_cases_lem2] ) >>
      IMP_RES_TAC ctf_wb_not_cl_evpol_lem >>
      IMP_RES_TAC ctf_wb_not_cl_evpol_some_lem >>
      `pa <> PA dop` by ( 
          METIS_TAC [evpol_lem, optionTheory.THE_DEF] 
      ) >>
      RW_TAC std_ss [combinTheory.UPDATE_APPLY]
     ]
);

val ca_cacheable_read_lem = store_thm("ca_cacheable_read_lem", ``
!ca m dop ca' m'. CA dop /\ rd dop /\ ((ca',m') = mtfca (ca,m) dop)
	       /\ (ca' (PA dop) <> ca (PA dop)) 
        ==>
    chit_ ca' (PA dop) 
 /\ ~cdirty_ ca' (PA dop)
 /\ (ccnt_ ca' (PA dop) = m (PA dop))
 /\ ~chit_ ca (PA dop)
``,
  REPEAT GEN_TAC >>
  MATCH_MP_TAC (
      prove(``(X ==> (D ==> A) /\ (D ==> B) /\ (D ==> C) /\ D) ==> 
	      (X ==> A /\ B /\ C /\ D)``, PROVE_TAC [])
  ) >>
  REPEAT STRIP_TAC >> (
      IMP_RES_TAC mtfca_cacheable >> 
      PAT_X_ASSUM ``!m ca. X`` (
          fn thm => ASSUME_TAC (ISPECL [``m:mem_state``, 
					``ca:cache_state``] thm)
      ) >>
      `?ca'' y. (ca'',y) = ctf ca (MVcl m) dop` by (
          METIS_TAC [pairTheory.pair_CASES]
      )
  )
  >| [(* chit_'*)
      IMP_RES_TAC ctf_rd_miss_lem >>
      SYM_CTF_TAC >>
      FULL_SIMP_TAC std_ss [wb_def, wb_lem] >>
      RW_TAC std_ss [MVcl_def]
      ,
      (* clean *)
      IMP_RES_TAC ctf_rd_miss_lem >>
      SYM_CTF_TAC >>
      FULL_SIMP_TAC std_ss [wb_def, wb_lem] >>
      RW_TAC std_ss [MVcl_def] >>
      REV_FULL_SIMP_TAC std_ss []
      ,
      (* ccnt_ *)
      IMP_RES_TAC ctf_rd_miss_lem >>
      SYM_CTF_TAC >>
      FULL_SIMP_TAC std_ss [wb_def, wb_lem] >>
      RW_TAC std_ss [MVcl_def]
      ,
      (* SOME (pa,v) *)
      IMP_RES_TAC ctf_rd_hit_lem >> 
      SYM_CTF_TAC >>
      FULL_SIMP_TAC std_ss [wb_def, wb_lem] >>
      REV_FULL_SIMP_TAC std_ss []
     ]
);

val ca_cacheable_write_lem = store_thm("ca_cacheable_write_lem", ``
!ca m dop ca' m'. CA dop /\ wt dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    (cdirty_ ca' (PA dop) 
(* WT case *)
  \/ ~cdirty_ ca' (PA dop) /\ (ccnt_ ca' (PA dop) = m' (PA dop)))
``,
  RW_TAC (std_ss++boolSimps.CONJ_ss) [mtfca_cacheable] >>
  `?ca'' y. (ca'',y) = ctf ca (MVcl m) dop` by (
      METIS_TAC [pairTheory.pair_CASES]
  ) >>
  IMP_RES_TAC ctf_wt_ccnt_lem >> 
  IMP_RES_TAC ctf_wt_cdirty_lem >> (
      SYM_CTF_TAC >>
      FULL_SIMP_TAC std_ss [wb_lem, wb_mem_def]
  ) >>
  RW_TAC std_ss [combinTheory.UPDATE_APPLY]
);

val mem_cacheable_not_cl_lem = store_thm("mem_cacheable_not_cl_lem", ``
!ca m dop ca' m'. CA dop /\ ~cl dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    ((m' (PA dop) = m (PA dop)) \/ (ccnt_ ca' (PA dop) = m' (PA dop)))
``,
  RW_TAC (std_ss++boolSimps.CONJ_ss) [mtfca_cacheable] >>
  `?ca'' y. (ca'',y) = ctf ca (MVcl m) dop` by (
      METIS_TAC [pairTheory.pair_CASES]
  ) >>
  IMP_RES_TAC ctf_wb_cases >> ( FULL_SIMP_TAC std_ss [] ) >> (
      RW_TAC (srw_ss()) [] >>
      SYM_CTF_TAC >>
      FULL_SIMP_TAC std_ss [wb_def] >>
      REV_FULL_SIMP_TAC std_ss [] >>
      RW_TAC std_ss [combinTheory.UPDATE_APPLY]
  ) >> 
  (* WT case *)
  SYM_CTF_TAC2 >>
  IMP_RES_TAC ctf_wt_ccnt_lem >>
  ASM_REWRITE_TAC []
);

val uncacheable_unchanged_lem = store_thm("uncacheable_unchanged_lem", ``
!ca m dop ca' m'. ~CA dop /\ ~wt dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    (ca' = ca) /\ (m' = m)
``,
  REPEAT STRIP_TAC >> ( IMP_RES_TAC ca_uncacheable ) >>
  IMP_RES_TAC cl_mem_unchanged >>
  IMP_RES_TAC MVcl_lem >>
  FULL_SIMP_TAC std_ss []
);

val mem_uncacheable_unchanged_lem = store_thm("mem_uncacheable_unchanged_lem", ``
!ca m dop ca' m'. ~CA dop /\ ~wt dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    (m' (PA dop) = m (PA dop))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC uncacheable_unchanged_lem >>
  ASM_REWRITE_TAC []
);

val mem_uncacheable_write_lem = store_thm("mem_uncacheable_write_lem", ``
!ca m dop ca' m'. wt dop /\ ((ca',m') = mtfca (ca,m) dop) 
	       /\ (m' (PA dop) <> m (PA dop))
        ==>
    (~CA dop \/ (ccnt_ ca' (PA dop) = m' (PA dop)))
``,
  REPEAT STRIP_TAC >>
  `~cl dop` by ( METIS_TAC [not_cl_lem] ) >>
  RW_TAC std_ss [GSYM IMP_DISJ_THM] >>
  IMP_RES_TAC mem_cacheable_not_cl_lem  
);

(* Coherency *)

val coh_def = Define `coh ca m pa = 
chit_ ca pa /\ (ccnt_ ca pa <> m pa) ==> cdirty_ ca pa`;

val Coh_def = Define `Coh ca m (Rs:padr set) = !pa. pa IN Rs ==> coh ca m pa`;

val coh_clean_lem = store_thm("coh_clean_lem", ``
!ca m pa. coh ca m pa /\ chit_ ca pa /\ ~cdirty_ ca pa ==> (ccnt_ ca pa = m pa)
``,
  RW_TAC std_ss [coh_def] >>
  CCONTR_TAC >>
  RES_TAC
);

val coh_equal_lem = store_thm("coh_equal_lem", ``
!ca m pa. chit_ ca pa /\ (ccnt_ ca pa = m pa) ==> coh ca m pa
``,
  RW_TAC std_ss [coh_def]
);

val coh_hit_lem = store_thm("coh_hit_lem", ``
!ca m pa. coh ca m pa /\ chit_ ca pa ==> 
    ((ccnt_ ca pa <> m pa) ==> cdirty_ ca pa)
``,
  RW_TAC std_ss [coh_def]
);

val coh_miss_lem = store_thm("coh_miss_lem", ``
!ca m pa. ~chit_ ca pa ==> coh ca m pa
``,
  RW_TAC std_ss [coh_def]
);

val coh_dirty_lem = store_thm("coh_dirty_lem", ``
!ca m pa. cdirty_ ca pa ==> coh ca m pa
``,
  RW_TAC std_ss [coh_def]
);

val coh_clean_cacheless_lem = store_thm("coh_clean_cacheless_lem", ``
!ca m pa c. coh ca m pa /\ ~cdirty_ ca pa ==> ((MVca ca m) c pa = (MVcl m) c pa)
``,
  RW_TAC std_ss [MVca_def, MVcl_def] >>
  FULL_SIMP_TAC std_ss [coh_clean_lem]
);

val cacheless_coh_lem = store_thm("cacheless_coh_lem", ``
!ca m pa c. ((MVca ca m) T pa = (MVcl m) c pa) ==> coh ca m pa
``,
  RW_TAC std_ss [MVca_def, MVcl_def] 
  >| [IMP_RES_TAC coh_equal_lem
      ,
      FULL_SIMP_TAC std_ss [coh_miss_lem]
     ]
);

val coh_alt_lem = store_thm("coh_alt_lem", ``
!ca m pa. ((MVca ca m) T pa = (MValt ca m) T pa) <=> coh ca m pa
``,
  RW_TAC std_ss [MVca_def, MValt_def] 
  >| [(* hit /\ dirty ==> coh *)
      FULL_SIMP_TAC std_ss [coh_dirty_lem]
      ,
      (* hit /\ clean ==> (ccnt = m <=> coh) *)
      EQ_TAC
      >| [(* ==> *)
	  FULL_SIMP_TAC std_ss [coh_equal_lem]
	  ,
	  FULL_SIMP_TAC std_ss [coh_clean_lem]
	 ]
      ,
      (* ~hit /\ dirty -> contradiction *)
      FULL_SIMP_TAC std_ss [cdirty_chit_lem]
      ,
      (* miss ==> coh *)
      FULL_SIMP_TAC std_ss [coh_miss_lem]
     ]
);

val coh_preserve_lem = store_thm("coh_preserve_lem", ``
!ca m pa ca' m'. coh ca m pa
	      /\ chit_ ca pa
	      /\ (ccnt_ ca' pa = ccnt_ ca pa)
	      /\ (m' pa = m pa)
	      /\ (cdirty_ ca pa = cdirty_ ca' pa)
        ==> 
    coh ca' m' pa
``,
  RW_TAC std_ss [coh_def] >>
  RES_TAC >>
  FULL_SIMP_TAC std_ss []
);

val Coh_alt_lem = store_thm("Coh_alt_lem", ``
!ca m Rs. Coh ca m Rs 
              <=> 
          !pa. pa IN Rs ==> ((MVca ca m) T pa = (MValt ca m) T pa)
``,
  RW_TAC std_ss [Coh_def] >>
  EQ_TAC >> (
      REPEAT STRIP_TAC >>
      RES_TAC >>
      FULL_SIMP_TAC std_ss [coh_alt_lem]
  )
);

(* coherent transitions *)

val coh_write_lem = store_thm("coh_write_lem", ``
!ca m dop ca' m'. CA dop /\ wt dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    coh ca' m' (PA dop)
``,
  REPEAT STRIP_TAC >>
  `~cl dop` by ( RW_TAC std_ss [not_cl_lem] ) >>
  IMP_RES_TAC ca_cacheable_hit_lem >>
  IMP_RES_TAC ca_cacheable_write_lem 
  >| [(* dirty *)
      FULL_SIMP_TAC std_ss [coh_dirty_lem]
      ,
      FULL_SIMP_TAC std_ss [coh_equal_lem]
     ]
);

val coh_ca_trans_lem = store_thm("coh_ca_trans_lem", ``
!ca m dop ca' m' pa. CA dop /\ coh ca m pa /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    coh ca' m' pa
``,
  REPEAT STRIP_TAC >>
  Cases_on `pa = PA dop`
  >| [(* PA dop *)
      IMP_RES_TAC ca_cacheable_ca >>
      PAT_X_ASSUM ``!pa. X`` (fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm )) >>
      REV_FULL_SIMP_TAC std_ss []
      >| [(* read hit *)
	  IMP_RES_TAC mem_cacheable_read_lem >>
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC coh_preserve_lem
	  ,
	  (* read miss *)
	  IMP_RES_TAC mem_cacheable_read_lem >>
          METIS_TAC [coh_equal_lem]
	  ,
	  (* write *)
	  IMP_RES_TAC coh_write_lem
	  ,
	  (* clean *)
	  FULL_SIMP_TAC std_ss [coh_miss_lem]
	 ]
      ,
      (* other pa *)
      Cases_on `ca' pa = ca pa`
      >| [Cases_on `m' pa = m pa`
          >| [(* cache and mem unchanged *)
	      IMP_RES_TAC cdirty_lem >>
	      IMP_RES_TAC ccnt_lem >>
	      Cases_on `chit_ ca' pa`
	      >| [(* hit *)
		  IMP_RES_TAC chit_lem >>
		  METIS_TAC [coh_preserve_lem]
		  ,
		  (* miss *)
		  FULL_SIMP_TAC std_ss [coh_miss_lem]
		 ]
	      ,
	      (* cache same, mem changed *)
	      IMP_RES_TAC mem_cacheable_other_lem >>
	      IMP_RES_TAC cdirty_lem >>
	      FULL_SIMP_TAC std_ss [coh_dirty_lem]
	     ]
	  ,
	  (* cache changed -> eviction *)
	  IMP_RES_TAC ca_cacheable_other_lem >>
          FULL_SIMP_TAC std_ss [coh_miss_lem]
	 ]
     ]
);

val ca_unchanged_lem = store_thm("ca_unchanged_lem", ``
!ca m dop ca' m'. CA dop /\ ~wt dop /\ coh ca m (PA dop)
	       /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    (MVca ca' m' T (PA dop) = MVca ca m T (PA dop))
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC ( SPEC ``dop:dop`` dop_cases_lem2 ) >>
  REV_FULL_SIMP_TAC std_ss []
  >| [(* read *)
      IMP_RES_TAC mem_cacheable_read_lem >>
      Cases_on `ca' (PA dop) = ca (PA dop)`
      >| [(* cache unchanged *)
	  FULL_SIMP_TAC std_ss [MVca_lem]
	  ,
	  (* cache changed -> miss *)
	  IMP_RES_TAC ca_cacheable_read_lem >>
	  RW_TAC std_ss [MVca_def]
	 ]
      ,
      (* clean *)
      `~chit_ ca' (PA dop)` by ( METIS_TAC [cacheable_cl_lem] ) >>
      `(m' (PA dop) = m (PA dop)) \/ (m' (PA dop) = ccnt_ ca (PA dop))` by (
          METIS_TAC [cacheable_cl_lem] )
      >| [(* mem unchanged *)
          RW_TAC std_ss [MVca_def] >>
	  Cases_on `cdirty_ ca (PA dop)`
	  >| [(* dirty *)
	      IMP_RES_TAC mem_cacheable_cl_dirty_lem >>
	      FULL_SIMP_TAC std_ss []
	      ,
	      (* clean *)
	      IMP_RES_TAC coh_clean_lem >>
	      FULL_SIMP_TAC std_ss []
	     ]
	  ,
	  (* mem' = cache content *)	  
	  RW_TAC std_ss [MVca_def] >>
	  IMP_RES_TAC mem_cacheable_cl_miss_lem >>
	  FULL_SIMP_TAC std_ss []
	 ]     
     ]
);

fun ASM_SYM_TAC pat = PAT_X_ASSUM pat (fn thm => ASSUME_TAC (GSYM thm));

val ca_other_unchanged_lem = store_thm("ca_other_unchanged_lem", ``
!ca m dop ca' m' pa. coh ca m pa /\ (pa <> PA dop)
		  /\ ((ca',m') = mtfca (ca,m) dop) 
        ==>
    (MVca ca' m' T pa = MVca ca m T pa)
``,
  REPEAT STRIP_TAC >>
  Cases_on `cl dop`
  >| [(* clean *)
      IMP_RES_TAC cacheable_cl_other_lem >>
      RW_TAC std_ss [MVca_def, ccnt_lem] >> (
          METIS_TAC [chit_lem]
      )
      ,
      (* not clean *)
      Cases_on `CA dop`
      >| [(* cacheable *)
	  IMP_RES_TAC ca_cacheable_mem >>
	  PAT_X_ASSUM ``!pa. X`` ( 
	      fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) 
	  ) >>
	  REV_FULL_SIMP_TAC std_ss []
	  >| [(* mem_unchanged *)
	      IMP_RES_TAC ca_cacheable_ca >>
	      PAT_X_ASSUM ``!pa. X`` ( 
	          fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) 
	      ) >>
	      REV_FULL_SIMP_TAC std_ss []
	      >| [(* hit and hit' *)
		  RW_TAC std_ss [MVca_def]
		  ,
		  (* hit and miss' *)
		  RW_TAC std_ss [MVca_def] >>
		  CCONTR_TAC >>
		  ASM_SYM_TAC ``m pa <> ccnt_ ca pa`` >>
		  IMP_RES_TAC coh_hit_lem >>
		  IMP_RES_TAC mem_cacheable_not_cl_dirty_lem >>
		  METIS_TAC []
		 ]
	      ,
	      IMP_RES_TAC ca_cacheable_ca >>
	      PAT_X_ASSUM ``!pa. X`` ( 
	          fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) 
	      ) >>
	      REV_FULL_SIMP_TAC std_ss []
	      >| [(* hit and hit' *)
		  RW_TAC std_ss [MVca_def]
		  ,
		  (* miss' *)
		  RW_TAC std_ss [MVca_def] >>
		  IMP_RES_TAC cdirty_chit_lem
		 ]
	     ]
	  ,
	  (* uncacheable *)
	  IMP_RES_TAC ca_uncacheable >>
	  IMP_RES_TAC cl_other_unchanged_lem >>
	  RW_TAC std_ss [MVca_def]
	 ]
     ]
);


(*********** finish ************)

val _ = export_theory();
