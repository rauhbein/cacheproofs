(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;
open cacheIfTheory;

val _ = new_theory "cachemem";

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


val ctf_not_cl_wb_lem = store_thm("ctf_not_cl_wb_lem", ``
!ca mv dop ca' y. CA dop /\ ~cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    (y = if evpol ca (PA dop) = NONE
	 then NONE
	 else (if cdirty_ ca (THE (evpol ca (PA dop))) 
	       then SOME (THE (evpol ca (PA dop)),
			  ccnt_ ca (THE (evpol ca (PA dop))))
	       else NONE)) 
``,
  REWRITE_TAC [ctf_not_cl_wb_oblg]
);

val ctf_wt_cdirty_lem = store_thm("ctf_wt_cdirty_lem", ``
!ca mv dop ca' y. CA dop /\ wt dop /\ ((ca',y) = ctf ca mv dop) ==>
    cdirty_ ca' (PA dop)
``,
  REWRITE_TAC [ctf_wt_cdirty_oblg]
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
    (ccnt_ ca' (PA dop) = mv T (PA dop)) /\ ~cdirty_ ca' (PA dop)
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
    (pa = THE (evpol ca (PA dop))) /\ (v = ccnt_ ca pa) /\ cdirty_ ca pa
``,
  REWRITE_TAC [ctf_wb_not_cl_evpol_oblg]
);

val ctf_wb_not_cl_evpol_some_lem = store_thm("ctf_wb_not_cl_evpol_some_lem", ``
!ca mv dop ca' pa v. CA dop /\ ~cl dop /\ ((ca',SOME(pa,v)) = ctf ca mv dop) ==>
    (evpol ca (PA dop) = SOME pa)
``,
  REWRITE_TAC [ctf_wb_not_cl_evpol_some_oblg]
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

val ctf_wb_cases = store_thm("ctf_wb_cases", ``
!ca mv dop ca' y. CA dop /\ ((ca',y) = ctf ca mv dop) ==>
    ((y = NONE) \/ ?pa. y = SOME(pa, ccnt_ ca pa))
``,
  REPEAT STRIP_TAC >>
  Cases_on `cl dop` 
  >| [(* cl *)
      Cases_on `cdirty_ ca (PA dop)`
      >| [(* dirty *)
	  DISJ2_TAC >>
          EXISTS_TAC ``PA dop`` >>
	  IMP_RES_TAC ctf_cl_wb_lem >>
	  ASM_REWRITE_TAC []
	  ,
	  (* clean *) 
	  DISJ1_TAC >>
	  IMP_RES_TAC ctf_cl_wb_lem >>
	  ASM_REWRITE_TAC []
	 ]
      ,
      (* not cl *)
      METIS_TAC [ctf_not_cl_wb_lem]
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

val ctf_cl_cdirty_lem = store_thm("ctf_cl_chit_other_lem", ``
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
    cdirty_ ca pa
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
      Cases_on `pa = THE (evpol ca (PA dop))` >> (
          IMP_RES_TAC ctf_not_cl_wb_lem >>
	  REV_FULL_SIMP_TAC std_ss []
      )
     ]
);

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

(* TODO: add some useful lemmas *)

val mtfca_cacheable = store_thm("mtfca_cacheable", ``
!ca m dop. CA dop ==> (mtfca (ca,m) dop = wb (ctf ca (MVcl m) dop) m)
``,
  RW_TAC std_ss [CA_lem] >> (
      RW_TAC std_ss [mtfca_def]
  )
);


val cl_mem_unchanged = store_thm("cl_mem_unchanged", ``
!m dop m'. ~wt dop /\ (mtfcl m dop = m') ==>
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

val ca_uncacheable = store_thm("ca_uncacheable", ``
!ca m dop ca' m'. ~CA dop /\ (mtfca (ca,m) dop = (ca',m')) ==>
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
    !pa. (m' pa = m pa) \/ cdirty_ ca pa /\ (m' pa = ccnt_ ca pa)
``,
  RW_TAC (std_ss++boolSimps.CONJ_ss) [mtfca_cacheable] >>
  `?ca'' y. (ca'',y) = ctf ca (MVcl m) dop` by (
      METIS_TAC [pairTheory.pair_CASES]
  ) >>
  IMP_RES_TAC ctf_wb_cases >> ( FULL_SIMP_TAC std_ss [] )
  >| [(* wb NONE *)
      RW_TAC (srw_ss()) [] >>
      SYM_CTF_TAC >>
      FULL_SIMP_TAC std_ss [wb_def]
      ,
      (* wb SOME (pa',v) *) 
      RW_TAC (srw_ss()) [] >>
      IMP_RES_TAC ctf_wb_dirty_lem >>
      SYM_CTF_TAC >>
      FULL_SIMP_TAC std_ss [wb_def] >>
      Cases_on `pa = pa'` >> (
          RW_TAC std_ss [combinTheory.UPDATE_APPLY]
      )
     ]
);

val ca_cacheable_ca = store_thm("ca_cacheable_ca", ``
!ca m dop ca' m'. CA dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    !pa. chit_ ca pa /\ chit_ ca' pa /\ (ccnt_ ca' pa = ccnt_ ca pa) /\ 
	 (cdirty_ ca pa <=> cdirty_ ca' pa) /\ (rd dop \/ pa <> PA dop)
      \/ chit_ ca' pa /\ (ccnt_ ca' pa = m pa) /\ rd dop /\ (pa = PA dop)
      \/ cdirty_ ca' pa /\ (ccnt_ ca' pa = VAL dop) /\ wt dop /\ (pa = PA dop)
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
      `~cl dop` by ( METIS_TAC [not_cl_lem] ) >>
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
    (ccnt_ ca' (PA dop) = m (PA dop)) /\ ~chit_ ca (PA dop)
``,
  REPEAT GEN_TAC >>
  MATCH_MP_TAC (
      prove(``(X ==> (B ==> A) /\ B) ==> (X ==> A /\ B)``, PROVE_TAC [])
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
  >| [(* ccnt_ *)
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


(*********** finish ************)

val _ = export_theory();
