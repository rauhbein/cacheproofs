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

val mlwb_lem = store_thm("mlwb_lem", ``
!m t l pa. (tag pa = t) ==> (mlwb m t l pa = lw l pa)  
``,
  REWRITE_TAC [mlwb_oblg]
); 

val mlwb_other_lem = store_thm("mlwb_other_lem", ``
!m t l pa. (tag pa <> t) ==> (mlwb m t l pa = m pa)  
``,
  REWRITE_TAC [mlwb_other_oblg]
); 

val mllu_lem = store_thm("mllu_lem", ``
!m pa pa'. (tag pa = tag pa') ==> (lw (mllu m pa') pa = m pa)  
``,
  REWRITE_TAC [mllu_oblg]
); 

val tag_lem = store_thm("tag_lem", ``
!t. ?pa. t = tag pa
``,
  REWRITE_TAC [tag_oblg]
);

val chit_lem = store_thm("chit_lem", ``
!pa ca ca'. (ca (tag pa) = ca' (tag pa)) ==> (chit_ ca pa <=> chit_ ca' pa)
``,
  REWRITE_TAC [chit_oblg]
);

val chit_other_lem = store_thm("chit_other_lem", ``
!pa pa' ca. (tag pa = tag pa') ==> (chit_ ca pa <=> chit_ ca pa')
``,
  REWRITE_TAC [chit_other_oblg]
);

val ccnt_lem = store_thm("ccnt_lem", ``
!pa ca ca'. (ca (tag pa) = ca' (tag pa)) ==> (ccnt_ ca pa = ccnt_ ca' pa)
``,
  REWRITE_TAC [ccnt_oblg]
);

val ccnt_other_lem = store_thm("ccnt_other_lem", ``
!pa pa' ca. (tag pa = tag pa') ==> (ccnt_ ca pa = ccnt_ ca pa')
``,
  REWRITE_TAC [ccnt_other_oblg]
);

val ccntw_lem = store_thm("ccntw_lem", ``
!pa ca ca'. (ca (tag pa) = ca' (tag pa)) ==> (ccntw_ ca pa = ccntw_ ca' pa)
``,
  REWRITE_TAC [ccntw_oblg]
);

val ccntw_ccnt_lem = store_thm("ccntw_ccnt_lem", ``
!pa ca ca'. chit_ ca pa /\ chit_ ca' pa /\ (ccnt_ ca pa = ccnt_ ca' pa) ==> 
    (ccntw_ ca pa = ccntw_ ca' pa)
``,
  REWRITE_TAC [ccntw_ccnt_oblg]
);

val ccntw_ccnt_diff_lem = store_thm("ccntw_ccnt_diff_lem", ``
!pa ca ca'. chit_ ca pa /\ chit_ ca' pa /\ (ccnt_ ca pa <> ccnt_ ca' pa) ==> 
    ?pa'. (tag pa' = tag pa) /\ (ccntw_ ca pa' <> ccntw_ ca' pa')
``,
  REWRITE_TAC [ccntw_ccnt_diff_oblg]
);

val ccnt_lcnt_lem = store_thm("ccnt_lcnt_lem", ``
!ca pa. ccnt_ ca pa = lcnt_ ca (tag pa)
``,
  REWRITE_TAC [ccnt_lcnt_oblg]
);

val ccnt_not_eq_lem = store_thm("ccnt_not_eq_lem", ``
!pa ca ca'. chit_ ca pa /\ chit_ ca' pa /\ (cdirty_ ca pa <=> cdirty_ ca' pa)
         /\ (ca (tag pa) <> ca' (tag pa)) ==> 
    (ccnt_ ca pa <> ccnt_ ca' pa)
``,
  REWRITE_TAC [ccnt_not_eq_oblg]
);

val miss_lem = store_thm("miss_lem", ``
!ca pa. ~chit_ ca pa <=> (ca (tag pa) = NONE)
``,
  REWRITE_TAC [miss_oblg]
);

val cdirty_lem = store_thm("cdirty_lem", ``
!pa ca ca'. (ca (tag pa) = ca' (tag pa)) ==> (cdirty_ ca pa <=> cdirty_ ca' pa)
``,
  REWRITE_TAC [cdirty_oblg]
);

val cdirty_chit_lem = store_thm("cdirty_chit_lem", ``
!ca pa. cdirty_ ca pa ==> chit_ ca pa
``,
  REWRITE_TAC [cdirty_chit_oblg]
);

val cdirty_other_lem = store_thm("cdirty_other_lem", ``
!ca pa pa'. (tag pa = tag pa') ==> (cdirty_ ca pa <=> cdirty_ ca pa')
``,
  REWRITE_TAC [cdirty_other_oblg]
);

val cdirty_ldirty_lem = store_thm("cdirty_ldirty_lem", ``
!ca pa. cdirty_ ca pa <=> ldirty_ ca (tag pa)
``,
  REWRITE_TAC [cdirty_ldirty_oblg]
);

val not_chit_not_cdirty_lem = store_thm("not_chit_not_cdirty_lem", ``
!ca pa. ~chit_ ca pa ==> ~cdirty_ ca pa 
``,
  REWRITE_TAC [not_chit_not_cdirty_oblg]
);

val lw_ccntw_lem = store_thm("lw_ccntw_lem", ``
!ca pa pa'. (tag pa = tag pa') ==> (lw (ccnt_ ca pa') pa = ccntw_ ca pa)
``,
  REWRITE_TAC [lw_ccntw_oblg]
);

val lw_lcnt_lem = store_thm("lw_lcnt_lem", ``
!ca pa. lw (lcnt_ ca (tag pa)) pa = ccntw_ ca pa
``,
  REWRITE_TAC [lw_lcnt_oblg]
);

val lw_lv_lem = store_thm("lw_lv_lem", ``
!mv pa. lw (lv mv T pa) pa = mv T pa
``,
  REWRITE_TAC [lw_lv_oblg]
);

val lv_lem = store_thm("lv_lem", ``
!mv pa' pa. (tag pa = tag pa') ==> (lv mv T pa' = lv mv T pa)
``,
  REWRITE_TAC [lv_oblg]
);

val mllu_lv_lem = store_thm("mllu_lv_lem", ``
!mv m pa pa'. (tag pa = tag pa') ==> 
    ((lv mv T pa' = mllu m pa) 
	 <=> 
     !pa''. (tag pa'' = tag pa) ==> 
         (lw (lv mv T pa') pa'' = lw (mllu m pa) pa''))
``,
  REWRITE_TAC [mllu_lv_oblg]
); 

val ctf_chit_lem = store_thm("ctf_chit_lem", ``
!ca mv dop ca' y. CA dop /\ ~cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    chit_ ca' (PA dop)
``,
  REWRITE_TAC [ctf_chit_oblg]
);

val ctf_cl_miss_lem = store_thm("ctf_cl_miss_lem", ``
!ca mv dop ca' y. cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    !pa. (tag pa = tag (PA dop)) ==> ~chit_ ca' pa
``,
  REWRITE_TAC [ctf_cl_miss_oblg]
);

val ctf_cl_other_lem = store_thm("ctf_cl_other_lem", ``
!ca mv dop ca' y pa. cl dop /\ ((ca',y) = ctf ca mv dop) 
                  /\ (tag pa <> tag (PA dop)) ==>
    (ca' (tag pa) = ca (tag pa))
``,
  REWRITE_TAC [ctf_cl_other_oblg]
);

val ctf_cl_wb_lem = store_thm("ctf_cl_wb_lem", ``
!ca mv dop ca' y pa. cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    (y = if cdirty_ ca (PA dop)
	 then SOME (tag (PA dop), ccnt_ ca (PA dop))
	 else NONE)
``,
  REWRITE_TAC [ctf_cl_wb_oblg]
);

val ctf_not_cl_other_lem = store_thm("ctf_not_cl_other_lem", ``
!ca mv dop ca' y t. CA dop /\ ~cl dop /\ ((ca',y) = ctf ca mv dop) 
		  /\ (t <> tag (PA dop)) ==>
    (ca' t = if evpol ca (PA dop) = SOME t 
	     then NONE
	     else ca t)
``,
  REWRITE_TAC [ctf_not_cl_other_oblg]
);

val clean_inv = Define `clean_inv ca = !pa. ~cdirty_ ca pa`;

val ctf_not_cl_wb_lem = store_thm("ctf_not_cl_wb_lem", ``
!ca mv dop ca' y. CA dop /\ ~cl dop /\ ((ca',y) = ctf ca mv dop) ==>
    ((y = if evpol ca (PA dop) = NONE
	  then NONE
	  else (if ldirty_ ca (THE (evpol ca (PA dop))) /\
		   THE (evpol ca (PA dop)) <> tag (PA dop) 
		then SOME (THE (evpol ca (PA dop)),
			   lcnt_ ca (THE (evpol ca (PA dop))))
		else NONE))
(* WT case *)
  \/ (y = if wt dop 
	  then SOME (tag (PA dop), ccnt_ ca' (PA dop))
	  else NONE) /\ clean_inv ca)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC ctf_not_cl_wb_oblg >>
  ASM_REWRITE_TAC []
);

val ctf_wt_cdirty_lem = store_thm("ctf_wt_cdirty_lem", ``
!ca mv dop ca' y. CA dop /\ wt dop /\ ((ca',y) = ctf ca mv dop) ==>
    cdirty_ ca' (PA dop) /\ (y <> SOME (tag (PA dop), ccnt_ ca' (PA dop)))
(* WT case *)
 \/ clean_inv ca /\ clean_inv ca' /\ 
    (y = SOME (tag (PA dop), ccnt_ ca' (PA dop))) /\
    (!pa. (tag pa = tag (PA dop)) ==> (ccntw_ ca pa = mv T pa))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC ctf_wt_cdirty_oblg >>
  ASM_REWRITE_TAC [] >>
  DISJ1_TAC >>
  CCONTR_TAC >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC not_cl_lem >>
  IMP_RES_TAC ctf_wb_not_cl_evpol_some_oblg >>
  FULL_SIMP_TAC std_ss [evpol_oblg]
);

val ctf_rd_hit_lem = store_thm("ctf_rd_hit_lem", ``
!ca mv dop ca' y. CA dop /\ rd dop /\ chit_ ca (PA dop) 
	       /\ ((ca',y) = ctf ca mv dop) ==>
    (ca' (tag (PA dop)) = ca (tag (PA dop)))
``,
  REWRITE_TAC [ctf_rd_hit_oblg]
);

val ctf_rd_miss_lem = store_thm("ctf_rd_miss_lem", ``
!ca mv dop ca' y. CA dop /\ rd dop /\ ~chit_ ca (PA dop) 
	       /\ ((ca',y) = ctf ca mv dop) ==>
    chit_ ca' (PA dop) 
 /\ (ccnt_ ca' (PA dop) = lv mv T (PA dop))
 /\ (ccntw_ ca' (PA dop) = mv T (PA dop))
 /\ ~cdirty_ ca' (PA dop)
``,
  REWRITE_TAC [ctf_rd_miss_oblg]
);

val ctf_wt_fill_lem = store_thm("ctf_wt_fill_lem", ``
!ca mv dop ca' y pa. CA dop /\ wt dop /\ pa <> PA dop /\ (tag pa = tag (PA dop))
	          /\ ~chit_ ca (PA dop) /\ ((ca',y) = ctf ca mv dop) ==>
    chit_ ca' pa 
 /\ (ccntw_ ca' pa = mv T pa)
``,
  REWRITE_TAC [ctf_wt_fill_oblg]
);

val ctf_wt_ccnt_lem = store_thm("ctf_wt_ccnt_lem", ``
!ca mv dop ca' y. CA dop /\ wt dop /\ ((ca',y) = ctf ca mv dop) ==>
    (ccntw_ ca' (PA dop) = VAL dop) 
 /\ (!pa. chit_ ca pa /\ pa <> PA dop /\ (tag pa = tag (PA dop)) ==> 
	      (ccntw_ ca' pa = ccntw_ ca pa))
``,
  REWRITE_TAC [ctf_wt_ccnt_oblg]
);

val ctf_wb_not_cl_evpol_lem = store_thm("ctf_wb_evpol_lem", ``
!ca mv dop ca' t v. CA dop /\ ~cl dop /\ ((ca',SOME(t,v)) = ctf ca mv dop) ==>
    (t = THE (evpol ca (PA dop))) /\ (v = lcnt_ ca t) /\ ldirty_ ca t 
(* WT case *)
  \/ wt dop /\ (t = tag (PA dop)) /\ ~ldirty_ ca t /\ (v = lcnt_ ca' t)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC ctf_wb_not_cl_evpol_oblg >>
  ASM_REWRITE_TAC []
);

val ctf_wb_not_cl_evpol_some_lem = store_thm("ctf_wb_not_cl_evpol_some_lem", ``
!ca mv dop ca' t v. CA dop /\ ~cl dop /\ ((ca',SOME(t,v)) = ctf ca mv dop) ==>
    (evpol ca (PA dop) = SOME t)
(* WT case *)
  \/ wt dop /\ (t = tag (PA dop))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC ctf_wb_not_cl_evpol_some_oblg >>
  ASM_REWRITE_TAC []
);

val evpol_lem = store_thm("evpol_lem", ``
!ca pa pa'. (tag pa' = tag pa) ==> evpol ca pa <> SOME (tag pa')
``,
  REWRITE_TAC [evpol_oblg]
);

(* some derived lemmas *)

val tag_neq_lem = store_thm("tag_neq_lem", ``
!pa pa'. tag pa <> tag pa' ==> pa <> pa'
``,
  RW_TAC std_ss [] >>
  CCONTR_TAC >>
  FULL_SIMP_TAC std_ss []
);

val double_not_chit_lem = store_thm("double_not_chit_lem", ``
!ca ca' pa. ~chit_ ca pa /\ ~chit_ ca' pa ==> (ca (tag pa) = ca' (tag pa))
``,
  REPEAT STRIP_TAC >> 
  IMP_RES_TAC not_chit_lem >>
  RW_TAC std_ss []
);

val ccnt_ccntw_lem = store_thm("ccnt_ccntw_lem", ``
!pa ca ca'. chit_ ca pa /\ chit_ ca' pa ==> 
    ((ccnt_ ca pa = ccnt_ ca' pa) <=> 
     !pa'. (tag pa' = tag pa) ==> (ccntw_ ca pa' = ccntw_ ca' pa'))
``,
  REPEAT STRIP_TAC >>
  EQ_TAC
  >| [(* ==> *)
      RW_TAC std_ss [] >>
      IMP_RES_TAC chit_other_lem >>
      `ccnt_ ca pa' = ccnt_ ca' pa'` by ( METIS_TAC [ccnt_other_lem] ) >>
      IMP_RES_TAC ccntw_ccnt_lem 
      ,
      (* <== *)
      RW_TAC std_ss [] >>
      CCONTR_TAC >>
      IMP_RES_TAC ccntw_ccnt_diff_lem >>
      REV_FULL_SIMP_TAC std_ss []
     ]
);

val ctf_ca_cases_other = store_thm("ctf_ca_cases_other", ``
!ca mv dop ca' y pa. CA dop /\ ((ca',y) = ctf ca mv dop) 
		  /\ (tag pa <> tag (PA dop)) ==>
    ((ca' (tag pa) = NONE) \/ (ca' (tag pa) = ca (tag pa)))
``,
  REPEAT STRIP_TAC >>
  Cases_on `cl dop` 
  >| [(* cl *)
      IMP_RES_TAC ctf_cl_other_lem >>
      ASM_REWRITE_TAC []
      ,
      (* not cl *)
      IMP_RES_TAC ctf_not_cl_other_lem >>
      Cases_on `evpol ca (PA dop) = SOME (tag pa)` >> (
          REV_FULL_SIMP_TAC std_ss []
      )
     ]
);

val wb_NONE_cases_def = Define `wb_NONE_cases ca dop = 
    clean_inv ca /\ ~wt dop 
 \/ (evpol ca (PA dop) = NONE)
 \/ (~ldirty_ ca (THE (evpol ca (PA dop))))
 \/ cl dop /\ (~cdirty_ ca (PA dop))
`;

val ctf_wb_cases = store_thm("ctf_wb_cases", ``
!ca mv dop ca' y. CA dop /\ ((ca',y) = ctf ca mv dop) ==>
    (   (y = NONE) /\ wb_NONE_cases ca dop
     \/ (?t. (y = SOME(t, lcnt_ ca t)) /\ (if cl dop 
					   then t = tag (PA dop)
					   else t <> tag (PA dop)))
     \/ wt dop /\ clean_inv ca /\ 
	(y = SOME (tag (PA dop), ccnt_ ca' (PA dop))))
``,
  REPEAT STRIP_TAC >>
  Cases_on `cl dop` 
  >| [(* cl *)
      Cases_on `cdirty_ ca (PA dop)`
      >| [(* dirty *)
	  DISJ2_TAC >>
	  DISJ1_TAC >>
          EXISTS_TAC ``tag (PA dop)`` >>
	  IMP_RES_TAC ctf_cl_wb_lem >>
	  ASM_REWRITE_TAC [ccnt_lcnt_lem]
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
	  `THE (evpol ca (PA dop)) <> tag (PA dop)` by (
	      METIS_TAC [quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,
			 optionTheory.IS_SOME_EXISTS, 
			 optionTheory.THE_DEF,
			 evpol_lem]
	  ) >>
	  Cases_on `ldirty_ ca (THE (evpol ca (PA dop)))`
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
    (evpol ca (PA dop) <> SOME (tag pa))
``,
  RW_TAC std_ss [INV_EQ_RULE miss_lem] >>
  Cases_on `tag pa = tag (PA dop)`
  >| [(* same tag -> never evicted *)
      RW_TAC std_ss [evpol_lem]
      ,
      (* other tag *)
      IMP_RES_TAC ctf_not_cl_other_lem >>
      FULL_SIMP_TAC std_ss []
     ]
);

val ctf_not_cl_chit_lem = store_thm("ctf_not_cl_chit_lem", ``
!ca mv dop ca' y pa. CA dop /\ ~cl dop /\ (tag pa <> tag (PA dop))
		  /\ ((ca', y) = ctf ca mv dop) ==>
    (chit_ ca' pa <=> chit_ ca pa /\ evpol ca (PA dop) <> SOME (tag pa))
``,
  RW_TAC std_ss [] >>
  EQ_TAC
  >| [(* ==> *)
      RW_TAC std_ss []
      >| [(* chit *)
	  CCONTR_TAC >>
	  IMP_RES_TAC miss_lem >>
	  `ca' (tag pa) <> NONE` by ( 
	      FULL_SIMP_TAC std_ss [INV_EQ_RULE miss_lem] 
	  ) >>
	  METIS_TAC [ctf_ca_cases_other]
	  ,
	  (* evpol <> pa *)
	  CCONTR_TAC >> 
	  IMP_RES_TAC ctf_not_cl_other_lem >>
	  `ca' (tag pa) <> NONE` by ( 
	      FULL_SIMP_TAC std_ss [INV_EQ_RULE miss_lem] 
	  ) >>
	  REV_FULL_SIMP_TAC std_ss []
	 ]
      ,
      (* <== *)
      RW_TAC std_ss [INV_EQ_RULE miss_lem] >>
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
!ca mv dop ca' y pa. CA dop /\ ~cl dop /\ (tag pa <> tag (PA dop))
		  /\ ((ca', y) = ctf ca mv dop) ==>
    (cdirty_ ca' pa <=> cdirty_ ca pa /\ evpol ca (PA dop) <> SOME (tag pa))
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
	  IMP_RES_TAC tag_neq_lem >>
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
!ca mv dop ca' y pa. cl dop /\ ((ca',y) = ctf ca mv dop)
		  /\ (tag pa <> tag (PA dop)) ==>
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
  PAT_X_ASSUM ``!pa. x`` (
      fn thm => ASSUME_TAC ( SPEC ``PA dop`` thm )
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC not_chit_not_cdirty_lem
);

val ctf_cl_cdirty_other_lem = store_thm("ctf_cl_cdirty_other_lem", ``
!ca mv dop ca' y pa. cl dop /\ ((ca',y) = ctf ca mv dop)
                  /\ (tag pa <> tag (PA dop)) ==>
    (cdirty_ ca' pa <=> cdirty_ ca pa)
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC cdirty_lem >>
  IMP_RES_TAC ctf_cl_other_lem
);

val ctf_wb_dirty_lem = store_thm("ctf_wb_dirty_lem", ``
!ca mv dop ca' y t v. CA dop /\ ((ca',SOME(t,v)) = ctf ca mv dop) ==>
    (ldirty_ ca t \/ wt dop /\ (t = tag (PA dop)))
``,
  REPEAT STRIP_TAC >>
  Cases_on `cl dop` 
  >| [(* clean *)
      Cases_on `t = tag (PA dop)` >> (
	  IMP_RES_TAC ctf_cl_wb_lem >>
	  REV_FULL_SIMP_TAC std_ss []
      ) >>
      IMP_RES_TAC cdirty_ldirty_lem >>
      ASM_REWRITE_TAC []
      ,
      (* read or write *)
      IMP_RES_TAC ctf_not_cl_wb_lem >> ( 
          Cases_on `t = THE (evpol ca (PA dop))` >> (
	      REV_FULL_SIMP_TAC std_ss [] >>
	      METIS_TAC []
	  )
      )
     ]
);

val ctf_other_hit_lem = store_thm("ctf_other_hit_lem", ``
!ca mv dop ca' y pa. 
    CA dop /\ (tag pa <> tag (PA dop))
 /\ chit_ ca pa /\ chit_ ca' pa
 /\ ((ca',y) = ctf ca mv dop) 
        ==>
    (ca' (tag pa) = ca (tag pa))
``,
  REPEAT STRIP_TAC >>
  Cases_on `cl dop` 
  >| [(* cl *)
      IMP_RES_TAC ctf_cl_other_lem
      ,
      (* not cl *)
      IMP_RES_TAC ctf_not_cl_other_lem >>
      Cases_on `evpol ca (PA dop) = SOME (tag pa)` 
      >| [(* evicted -> contradiction *)
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC miss_lem 
	  ,
	  (* not evicted, unchanged *)
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC ccntw_lem
	 ]
     ]     
);


val ctf_not_write_lem = store_thm("ctf_not_write_lem", ``
!ca mv dop ca' y pa. 
    CA dop /\ ~wt dop 
 /\ chit_ ca pa /\ chit_ ca' pa
 /\ ((ca',y) = ctf ca mv dop) 
        ==>
    (ccntw_ ca' pa = ccntw_ ca pa)
``,
  REPEAT STRIP_TAC >>
  Cases_on `tag pa = tag (PA dop)`
  >| [(* PA dop *)
      Cases_on `cl dop`
      >| [(* cl *)
          IMP_RES_TAC ctf_cl_miss_lem
	  ,
	  (* rd *)
	  IMP_RES_TAC not_wt_lem >>
          IMP_RES_TAC chit_other_lem >>   
	  IMP_RES_TAC ctf_rd_hit_lem >>
	  METIS_TAC [ccntw_lem]
	 ]
      ,
      (* other *)
      IMP_RES_TAC ctf_other_hit_lem >>
      IMP_RES_TAC ccntw_lem
     ]     
);

val ctf_write_other_lem = store_thm("ctf_write_other_lem", ``
!ca mv dop ca' y pa. 
    CA dop /\ wt dop /\ pa <> PA dop
 /\ chit_ ca pa /\ chit_ ca' pa
 /\ ((ca',y) = ctf ca mv dop) 
        ==>
    (ccntw_ ca' pa = ccntw_ ca pa)
``,
  REPEAT STRIP_TAC >>
  Cases_on `tag pa = tag (PA dop)`
  >| [(* same line *)
      IMP_RES_TAC ctf_wt_ccnt_lem
      ,
      (* other line *)
      IMP_RES_TAC ctf_other_hit_lem >>
      IMP_RES_TAC ccntw_lem
     ]
);


(**** memory views ****)

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
\c pa. if c /\ chit_ ca pa then ccntw_ ca pa else m pa
`;

val MVca_lem = store_thm("MVca_lem", ``
!ca m pa c ca' m'. (ca' (tag pa) = ca (tag pa)) /\ (m' pa = m pa) ==>
    ((MVca ca' m') c pa = (MVca ca m) c pa)
``,
  RW_TAC std_ss [MVca_def]
  >| [(* ccnt *)
      IMP_RES_TAC ccntw_lem
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
\c pa. if c /\ cdirty_ ca pa then ccntw_ ca pa else m pa
`;

val MValt_lem = store_thm("MValt_lem", ``
!ca m pa c ca' m'. (ca' (tag pa) = ca (tag pa)) /\ (m' pa = m pa) ==>
    ((MValt ca' m') c pa = (MValt ca m) c pa)
``,
  RW_TAC std_ss [MValt_def]
  >| [(* ccnt, ca unchanged *)
      IMP_RES_TAC ccntw_lem
      ,
      (* ~dirty and dirty' -> contradiction *)
      IMP_RES_TAC cdirty_lem >>
      FULL_SIMP_TAC std_ss []
      ,
      (* dirty and ~dirty' -> contradiction *)
      IMP_RES_TAC cdirty_lem >>
      FULL_SIMP_TAC std_ss []
     ]      
);


(* memory semantics *)

(* cacheless *)
val mtfcl_def = Define `
   (mtfcl m (WT pa w c) = (pa =+ w) m)
/\ (mtfcl m _ = m)
`;

val wb_def = Define `
   (wb (ca:cache_state,NONE) (m:mem_state) = (ca, m))
/\ (wb (ca,SOME(t,l)) m = (ca, mlwb m t l))
`;

val wb_mem_def = Define `
   (wb_mem m NONE = m)
/\ (wb_mem m (SOME (t,l)) = mlwb m t l)
`;

val wb_mem_upd_lem = store_thm("wb_mem_upd_lem", ``
!m t l pa. (tag pa = t) ==> (wb_mem m (SOME (t,l)) pa = lw l pa)
``,
  RW_TAC std_ss [wb_mem_def, mlwb_lem]
);

val wb_mem_upd_other_lem = store_thm("wb_mem_upd_other_lem", ``
!m t l pa. (tag pa <> t) ==> (wb_mem m (SOME (t,l)) pa = m pa)
``,
  RW_TAC std_ss [wb_mem_def, mlwb_other_lem]
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
      \/ cdirty_ ca pa /\ (m' pa = ccntw_ ca pa) /\ 
	 (if cl dop then (tag pa = tag (PA dop)) else tag pa <> tag (PA dop))
(* WT case *)
      \/ ~cdirty_ ca pa /\ ~cdirty_ ca' pa /\ (m' pa = ccntw_ ca' pa) /\
	 wt dop /\ (pa = PA dop)
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
	  Cases_on `tag pa = tag (PA dop)` 
	  >| [(* PA dop *)
	      DISJ2_TAC >>
	      IMP_RES_TAC cdirty_ldirty_lem >>
	      IMP_RES_TAC cdirty_other_lem >>
              RW_TAC std_ss [mlwb_lem] >>
	      METIS_TAC [lw_lcnt_lem]
	      ,
	      (* other line *)
	      DISJ1_TAC >>
              RW_TAC std_ss [mlwb_other_lem]
	     ]
	 ]
      ,
      (* read or write *)
      Cases_on `wt dop`
      >| [(* write *)
	  RW_TAC std_ss [] >>
          `(y = NONE) /\ wb_NONE_cases ca dop \/
           (?t. (y = SOME (t,lcnt_ ca t)) /\
            if cl dop then (t = tag (PA dop)) else t <> tag (PA dop)) \/
           wt dop /\ clean_inv ca /\
           (y = SOME (tag (PA dop), ccnt_ ca'' (PA dop)))`
	  by ( METIS_TAC [ctf_wb_cases] )
	  >| [(* wb NONE *)
	      RW_TAC (srw_ss()) [] >>
	      SYM_CTF_TAC >>
	      FULL_SIMP_TAC std_ss [wb_def]
	      ,
	      (* wb SOME, eviction *)
	      REV_FULL_SIMP_TAC std_ss [] >> 
	      FULL_SIMP_TAC std_ss [] >> 
              IMP_RES_TAC ctf_wb_dirty_lem >>
	      `?pa'. t = tag pa'` by ( RW_TAC std_ss [tag_lem] ) >>
	      FULL_SIMP_TAC std_ss [] >>
	      Cases_on `tag pa = tag pa'`
	      >| [(* evicted *)
		  DISJ2_TAC >>
		  IMP_RES_TAC cdirty_ldirty_lem >>
		  IMP_RES_TAC cdirty_other_lem >>
	          PAT_X_ASSUM ``(x, SOME (y,z)) = ctf a b c`` 
                              (fn thm => ASSUME_TAC (SYM thm)) >>
	          FULL_SIMP_TAC std_ss [wb_def] >>
		  RW_TAC std_ss [mlwb_lem] >>
		  METIS_TAC [lw_lcnt_lem]
		  ,
		  (* other address *)
		  DISJ1_TAC >>
	          PAT_X_ASSUM ``(x, SOME (y,z)) = ctf a b c`` 
                              (fn thm => ASSUME_TAC (SYM thm)) >>
	          FULL_SIMP_TAC std_ss [wb_def] >>
		  RW_TAC std_ss [mlwb_other_lem]
		 ]
	      ,
	      (* WT case *)
	      FULL_SIMP_TAC std_ss [clean_inv] >>
	      Cases_on `tag pa = tag (PA dop)`
	      >| [(* written line *)
		  Cases_on `pa = PA dop`
		  >| [(* written address *)
		      DISJ2_TAC >>
		      IMP_RES_TAC ctf_wt_cdirty_lem >> (
		          FULL_SIMP_TAC std_ss []
		      ) >>
		      PAT_X_ASSUM ``(x, SOME (y,z)) = ctf a b c`` 
                          (fn thm => ASSUME_TAC (SYM thm)) >>
		      FULL_SIMP_TAC std_ss [wb_def, clean_inv] >>
		      RW_TAC std_ss [mlwb_lem, lw_ccntw_lem]
		      ,
		      (* same line, different address *)
		      DISJ1_TAC >>
		      IMP_RES_TAC ctf_wt_cdirty_lem >> (
		          FULL_SIMP_TAC std_ss []
		      ) >>
		      Cases_on `chit_ ca pa`
		      >| [(* write hit *)
			  IMP_RES_TAC ctf_wt_ccnt_lem >>
			  PAT_X_ASSUM ``(x, SOME (y,z)) = ctf a b c`` 
                              (fn thm => ASSUME_TAC (SYM thm)) >>
			  FULL_SIMP_TAC std_ss [wb_def] >>
			  RW_TAC std_ss [mlwb_lem, lw_ccntw_lem, MVcl_def]
			  ,
			  (* write fill *)
			  `~chit_ ca (PA dop)` by ( 
			      METIS_TAC [chit_other_lem] 
			  ) >>
			  IMP_RES_TAC ctf_wt_fill_lem >>
			  PAT_X_ASSUM ``(x, SOME (y,z)) = ctf a b c`` 
                              (fn thm => ASSUME_TAC (SYM thm)) >>
			  FULL_SIMP_TAC std_ss [wb_def] >>
			  RW_TAC std_ss [mlwb_lem, lw_ccntw_lem, MVcl_def]
			 ]
		     ]
		  ,
		  (* other address *)
		  DISJ1_TAC >>
	          PAT_X_ASSUM ``(x, SOME (y,z)) = ctf a b c`` 
                              (fn thm => ASSUME_TAC (SYM thm)) >>
	          FULL_SIMP_TAC std_ss [wb_def] >>
		  RW_TAC std_ss [mlwb_other_lem]
		 ]
	     ]
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
	      `?pa'. t = tag pa'` by ( RW_TAC std_ss [tag_lem] ) >>
	      FULL_SIMP_TAC std_ss [] >>
	      Cases_on `tag pa = tag pa'`
	      >| [(* evicted *)
		  DISJ2_TAC >>
		  IMP_RES_TAC cdirty_ldirty_lem >>
		  IMP_RES_TAC cdirty_other_lem >>
		  RW_TAC std_ss [mlwb_lem] >>
		  METIS_TAC [lw_lcnt_lem]
		  ,
		  (* other address *)
		  DISJ1_TAC >>
		  RW_TAC std_ss [mlwb_other_lem]
		 ]
	     ]
	 ]
     ]
);

val ca_cacheable_ca = store_thm("ca_cacheable_ca", ``
!ca m dop ca' m'. CA dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    !pa. (* read hit or hitting other line not touched *)
         chit_ ca pa /\ chit_ ca' pa /\ (ccnt_ ca' pa = ccnt_ ca pa) /\ 
	 (cdirty_ ca pa <=> cdirty_ ca' pa) /\ 
	 (rd dop \/ tag pa <> tag (PA dop))
	 (* read fill *)
      \/ ~chit_ ca pa /\ chit_ ca' pa /\ (ccnt_ ca' pa = mllu m pa) /\ 
	 ~cdirty_ ca' pa /\ rd dop /\ (tag pa = tag (PA dop))
	 (* written address *)
      \/ chit_ ca' pa /\ (ccntw_ ca' pa = VAL dop) /\ wt dop /\ (pa = PA dop)
	 (* write hit, other address *)
      \/ chit_ ca pa /\ chit_ ca' pa /\ (ccntw_ ca' pa = ccntw_ ca pa) /\ 
	 wt dop /\ (pa <> PA dop) /\ (tag pa = tag (PA dop))
	 (* write fill, other address *)
      \/ ~chit_ ca pa /\ chit_ ca' pa /\ (ccntw_ ca' pa = m pa) /\ 
         wt dop /\ (pa <> PA dop) /\ (tag pa = tag (PA dop))
	 (* clean or eviction or missing other line *)
      \/ ~chit_ ca' pa /\ (cl dop \/ (tag pa <> tag (PA dop)))
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
      Cases_on `tag pa = tag (PA dop)` 
      >| [(* PA dop *)
	  IMP_RES_TAC ctf_cl_miss_lem >>
          FULL_SIMP_TAC std_ss []
	  ,
	  (* other pa *)
	  IMP_RES_TAC ctf_cl_other_lem >>
	  IMP_RES_TAC not_wt_lem >>
	  RW_TAC std_ss [ccnt_lem] >>
	  METIS_TAC [chit_lem, cdirty_lem]
	 ]
      ,
      (* read or write *)
      Cases_on `tag pa = tag (PA dop)` 
      >| [(* PA dop *)
	  IMP_RES_TAC ctf_chit_lem >>
	  IMP_RES_TAC chit_other_lem >>
	  FULL_SIMP_TAC std_ss [not_cl_lem]
	  >| [(* read *)
	      Cases_on `chit_ ca pa`
	      >| [(* hit *)
		  IMP_RES_TAC chit_other_lem >>
		  IMP_RES_TAC ctf_rd_hit_lem >>
	          METIS_TAC [ccnt_lem, cdirty_lem]
		  ,
		  (* miss *)
		  `~chit_ ca (PA dop)` by ( METIS_TAC [chit_other_lem] ) >>
		  IMP_RES_TAC ctf_rd_miss_lem >>
		  IMP_RES_TAC not_wt_lem >>
		  `ccnt_ ca'' pa = ccnt_ ca'' (PA dop)` by (
	              METIS_TAC [ccnt_other_lem]
	          ) >>
		  `~cdirty_ ca'' pa` by ( METIS_TAC [cdirty_other_lem] ) >>
	          FULL_SIMP_TAC std_ss [] >>
		  RW_TAC std_ss [mllu_lv_lem] >>
		  `lv (MVcl m) T (PA dop) = lv (MVcl m) T pa''` by (
		      RW_TAC std_ss [lv_lem]
		  ) >>
		  ASM_REWRITE_TAC [lw_lv_lem] >>
		  RW_TAC std_ss [mllu_lem, MVcl_def]
		 ]
	      ,
	      (* write *)
	      Cases_on `pa = PA dop`
	      >| [(* PA dop *)
		  IMP_RES_TAC ctf_wt_ccnt_lem >>
		  FULL_SIMP_TAC std_ss []
		  ,
		  (* other address on same line *)
		  IMP_RES_TAC not_rd_lem >>
		  Cases_on `chit_ ca pa`
		  >| [(* hit *)
		      FULL_SIMP_TAC std_ss [] >>
		      IMP_RES_TAC ctf_wt_ccnt_lem
		      ,
		      (* write fill *)
		      FULL_SIMP_TAC std_ss [] >>
		      `~chit_ ca (PA dop)` by ( METIS_TAC [chit_other_lem] ) >>
		      IMP_RES_TAC ctf_wt_fill_lem >>
		      RW_TAC std_ss [MVcl_def]
		     ]
		 ]
	     ]
	  ,
	  (* other pa *)
	  IMP_RES_TAC ctf_not_cl_other_lem >>
          Cases_on `evpol ca (PA dop) = SOME (tag pa)`
	  >| [(* eviction -> no hit *)
	      FULL_SIMP_TAC std_ss [] >>
	      IMP_RES_TAC miss_lem >>
	      RW_TAC std_ss []
	      ,
	      (* not evicted *)
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
    (cl dop \/ tag pa <> tag (PA dop))
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
 /\ ((m' (PA dop) = m (PA dop)) \/ (m' (PA dop) = ccntw_ ca (PA dop)))
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
!ca m dop ca' m' pa. cl dop /\ ((ca',m') = mtfca (ca,m) dop) 
		  /\ (tag pa <> tag (PA dop))
        ==>
    (ca' (tag pa) = ca (tag pa)) /\ (m' pa = m pa)
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
    (~chit_ ca' pa \/ (ca' (tag pa) = ca (tag pa)))
``,
  REPEAT STRIP_TAC >>
  Cases_on `tag pa = tag (PA dop)`
  >| [(* same line *)
      `~chit_ ca' (PA dop)` by (
          IMP_RES_TAC cacheable_cl_lem 
      ) >>
      METIS_TAC [chit_other_lem]
      ,
      (* other line *)
      DISJ2_TAC >>
      IMP_RES_TAC cacheable_cl_other_lem
     ]
);

val mem_cacheable_cl_lem = store_thm("mem_cacheable_cl_lem", ``
!ca m dop ca' m' pa. cl dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    ((m' pa = m pa) \/ (m' pa = ccntw_ ca pa))
``,
  REPEAT STRIP_TAC >>
  Cases_on `tag pa = tag (PA dop)`
  >| [(* same line *)
      Cases_on `pa = PA dop`
      >| [(* PA dop *)
	  IMP_RES_TAC cacheable_cl_lem >> (
              FULL_SIMP_TAC std_ss []
	  )
	  ,
	  (* other pa *)
	  IMP_RES_TAC not_wt_lem >>
	  IMP_RES_TAC cl_CA_lem >>
	  IMP_RES_TAC ca_cacheable_mem >>
	  PAT_X_ASSUM ``!pa. x`` (
	      fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm )
	  ) >>
	  REV_FULL_SIMP_TAC std_ss []
	 ]
      ,
      (* other line *)
      DISJ1_TAC >>
      IMP_RES_TAC cacheable_cl_other_lem
     ]
);

val mem_cacheable_cl_dirty_lem = store_thm("mem_cacheable_cl_dirty_lem", ``
!ca m dop ca' m'. cl dop /\ ((ca',m') = mtfca (ca,m) dop) /\ cdirty_ ca (PA dop)
        ==>
    !pa. (tag pa = tag (PA dop)) ==> (m' pa = ccntw_ ca pa)
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
  RW_TAC std_ss [mlwb_lem] >>
  `ccnt_ ca (PA dop) = ccnt_ ca pa` by ( RW_TAC std_ss [ccnt_other_lem] ) >>
  ASM_REWRITE_TAC [] >>
  REWRITE_TAC [ccnt_lcnt_lem, lw_lcnt_lem]
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
                  /\ (tag pa <> tag (PA dop)) /\ cdirty_ ca pa /\ ~chit_ ca' pa
        ==>
    (m' pa = ccntw_ ca pa)
``,
  RW_TAC std_ss [] >> 
  REV_FULL_SIMP_TAC std_ss [mtfca_cacheable] >>
  `?ca'' y. (ca'',y) = ctf ca (MVcl m) dop` by (
      METIS_TAC [pairTheory.pair_CASES]
  ) >>
  IMP_RES_TAC cdirty_chit_lem >>
  `evpol ca (PA dop) = SOME (tag pa)` by ( 
      IMP_RES_TAC ctf_not_cl_chit_lem >>
      SYM_CTF_TAC >>
      FULL_SIMP_TAC std_ss [wb_lem] >>
      METIS_TAC [] 
  ) >>
  IMP_RES_TAC ctf_wb_cases >> (
      FULL_SIMP_TAC std_ss [wb_NONE_cases_def, clean_inv] >>
      TRY ( METIS_TAC [optionTheory.NOT_SOME_NONE,
		       optionTheory.THE_DEF, cdirty_ldirty_lem] )
  ) >>
  RW_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC ctf_wb_not_cl_evpol_lem >>
  FULL_SIMP_TAC std_ss [optionTheory.THE_DEF] >>
  SYM_CTF_TAC >>
  FULL_SIMP_TAC std_ss [wb_lem, wb_mem_def] >>
  RW_TAC std_ss [mlwb_lem, lw_lcnt_lem]
);


(* deriveability lemmas *)

val ca_cacheable_other_lem = store_thm("ca_cacheable_other_lem", ``
!ca m dop ca' m' pa. CA dop /\ ((ca',m') = mtfca (ca,m) dop) /\ (pa <> PA dop)
                  /\ (ca' (tag pa) <> ca (tag pa)) ==> 
    (~chit_ ca' pa /\ (cdirty_ ca pa ==> (m' pa = ccntw_ ca pa))) \/
    (wt dop /\ chit_ ca pa /\ chit_ ca' pa 
        /\ (ccntw_ ca' pa = ccntw_ ca pa) /\ (tag pa = tag (PA dop))) \/
    (wt dop /\ ~chit_ ca pa /\ chit_ ca' pa 
        /\ (ccntw_ ca' pa = m pa) /\ (tag pa = tag (PA dop))) \/
    (rd dop /\ ~chit_ ca pa /\ chit_ ca' pa /\ ~cdirty_ ca' pa 
        /\ (ccntw_ ca' pa = m pa) /\ (tag pa = tag (PA dop)))
``,
  REPEAT STRIP_TAC >> 
  IMP_RES_TAC ca_cacheable_ca >>
  PAT_X_ASSUM ``!pa. x`` (
      fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm )
  ) >> 
  FULL_SIMP_TAC std_ss []
  >| [(* contradiction *)
      METIS_TAC [ccnt_not_eq_lem]
      ,
      (* contradiction *)
      METIS_TAC [ccnt_not_eq_lem]
      ,
      (* read fill *)
      IMP_RES_TAC not_wt_lem >>
      `ccntw_ ca' pa = lw (ccnt_ ca' pa) pa` by (
          RW_TAC std_ss [lw_ccntw_lem]
      ) >>
      ASM_REWRITE_TAC [] >>
      RW_TAC std_ss [mllu_lem]
      ,
      (* contradiction *)
      FULL_SIMP_TAC std_ss []
      ,
      (* dirty flush *)
      STRIP_TAC >>
      Cases_on `tag pa = tag (PA dop)`
      >| [(* same line *)
	  IMP_RES_TAC cdirty_other_lem >>
	  IMP_RES_TAC mem_cacheable_cl_dirty_lem
	  ,
	  (* other line *)
	  IMP_RES_TAC cacheable_cl_other_lem
	 ]
      ,
      (* dirty eviction *)
      STRIP_TAC >>
      Cases_on `cl dop`
      >| [(* contradiction *)
	  IMP_RES_TAC cacheable_cl_other_lem
	  ,
	  (* eviction *)
	  IMP_RES_TAC mem_cacheable_not_cl_dirty_lem
	 ]
     ]
);

val mem_cacheable_other_lem = store_thm("mem_cacheable_other_lem", ``
!ca m dop ca' m' pa. CA dop /\ ((ca',m') = mtfca (ca,m) dop) /\ (pa <> PA dop)
                  /\ (m' pa <> m pa) ==>
    cdirty_ ca pa /\ (m' pa = ccntw_ ca pa)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC ca_cacheable_mem >>
  PAT_X_ASSUM ``!pa. X`` (fn thm => ASSUME_TAC (ISPEC ``pa:padr`` thm)) >>
  FULL_SIMP_TAC std_ss [] >> ( 
      FULL_SIMP_TAC std_ss [] 
  )
);

val mem_cacheable_read_lem = store_thm("mem_cacheable_read_lem", ``
!ca m dop ca' m'. CA dop /\ rd dop /\ ((ca',m') = mtfca (ca,m) dop) ==>
    !pa. (tag pa = tag (PA dop)) ==> (m' pa = m pa)
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
      `?t v. x = (t,v)` by (
          METIS_TAC [pairTheory.pair_CASES]
      ) >>
      FULL_SIMP_TAC std_ss [wb_def] >>
      SYM_CTF_TAC2 >>
      `~cl dop /\ ~wt dop` by ( METIS_TAC [dop_cases_lem2] ) >>
      IMP_RES_TAC ctf_wb_not_cl_evpol_lem >>
      IMP_RES_TAC ctf_wb_not_cl_evpol_some_lem >>
      `t <> tag (PA dop)` by ( 
          METIS_TAC [evpol_lem, optionTheory.THE_DEF] 
      ) >>
      RW_TAC std_ss [mlwb_other_lem]
     ]
);

val ca_cacheable_read_lem = store_thm("ca_cacheable_read_lem", ``
!ca m dop ca' m'. CA dop /\ rd dop /\ ((ca',m') = mtfca (ca,m) dop)
	       /\ (ca' (tag (PA dop)) <> ca (tag (PA dop))) 
        ==>
    chit_ ca' (PA dop) 
 /\ ~cdirty_ ca' (PA dop)
 /\ (ccntw_ ca' (PA dop) = m (PA dop))
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
      (* ccntw_ *)
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
  \/ ~cdirty_ ca' (PA dop) /\ 
     (!pa. (tag pa = tag (PA dop)) ==> (ccntw_ ca' pa = m' pa)))
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
  RW_TAC std_ss [mlwb_lem, lw_ccntw_lem]
);

val mem_cacheable_not_cl_lem = store_thm("mem_cacheable_not_cl_lem", ``
!ca m dop ca' m'. CA dop /\ ~cl dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    ((m' (PA dop) = m (PA dop)) \/ (ccntw_ ca' (PA dop) = m' (PA dop)))
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
      RW_TAC std_ss [mlwb_other_lem]
  ) >> 
  (* WT case *)
  SYM_CTF_TAC2 >>
  IMP_RES_TAC ctf_wt_ccnt_lem >>
  DISJ2_TAC >>
  RW_TAC std_ss [mlwb_lem, lw_ccntw_lem]
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
    (~CA dop \/ (ccntw_ ca' (PA dop) = m' (PA dop)))
``,
  REPEAT STRIP_TAC >>
  `~cl dop` by ( METIS_TAC [not_cl_lem] ) >>
  RW_TAC std_ss [GSYM IMP_DISJ_THM] >>
  IMP_RES_TAC mem_cacheable_not_cl_lem  
);

(* Coherency *)

val coh_def = Define `coh ca m pa = 
chit_ ca pa /\ (?pa'. (tag pa' = tag pa) /\ ccntw_ ca pa' <> m pa') ==> 
cdirty_ ca pa`;

val Coh_def = Define `Coh ca m (Rs:padr set) = !pa. pa IN Rs ==> coh ca m pa`;

val coh_clean_lem = store_thm("coh_clean_lem", ``
!ca m pa. coh ca m pa /\ chit_ ca pa /\ ~cdirty_ ca pa ==> (ccntw_ ca pa = m pa)
``,
  RW_TAC std_ss [coh_def] >>
  CCONTR_TAC >>
  RES_TAC >>
  FULL_SIMP_TAC std_ss []
);

val coh_lem = store_thm("coh_lem", ``
!ca ca' m m' pa. coh ca m pa /\ (ca' (tag pa) = ca (tag pa)) 
              /\ (!pa'. (tag pa' = tag pa) ==> (m' pa' = m pa'))
        ==>
    coh ca' m' pa
``,
  RW_TAC std_ss [coh_def] >>
  IMP_RES_TAC chit_lem >>
  `ccntw_ ca pa' <> m pa'` by ( METIS_TAC [ccntw_lem] ) >>
  RES_TAC >>
  IMP_RES_TAC cdirty_lem
);

val coh_other_lem = store_thm("coh_other_lem", ``
!ca m pa pa'. (tag pa = tag pa') ==> (coh ca m pa <=> coh ca m pa')
``,
  RW_TAC std_ss [coh_def] >>
  METIS_TAC [chit_other_lem, cdirty_other_lem, ccntw_lem]
);


val coh_equal_lem = store_thm("coh_equal_lem", ``
!ca m pa. chit_ ca pa /\ (!pa'. (tag pa' = tag pa) ==> (ccntw_ ca pa' = m pa'))
	==> 
    coh ca m pa
``,
  RW_TAC std_ss [coh_def] >>
  RES_TAC
);

val coh_hit_lem = store_thm("coh_hit_lem", ``
!ca m pa. coh ca m pa /\ chit_ ca pa ==> 
    ((ccntw_ ca pa <> m pa) ==> cdirty_ ca pa)
``,
  RW_TAC std_ss [coh_def] >>
  RES_TAC >>
  FULL_SIMP_TAC std_ss []
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
!ca m pa c. (!pa'. (tag pa' = tag pa) ==> ((MVca ca m) T pa' = (MVcl m) c pa')) 
        ==> 
    coh ca m pa
``,
  RW_TAC std_ss [MVca_def, MVcl_def] >>
  Cases_on `chit_ ca pa`
  >| [MATCH_MP_TAC coh_equal_lem >>
      RW_TAC std_ss [] >>
      IMP_RES_TAC chit_other_lem >>
      RES_TAC >>
      METIS_TAC []
      ,
      FULL_SIMP_TAC std_ss [coh_miss_lem]
     ]
);

val coh_alt_lem = store_thm("coh_alt_lem", ``
!ca m pa. 
    (!pa'. (tag pa' = tag pa) ==> ((MVca ca m) T pa' = (MValt ca m) T pa'))
        <=> 
    coh ca m pa
``,
  REPEAT GEN_TAC >>
  Cases_on `chit_ ca pa`
  >| [(* hit *)
      Cases_on `cdirty_ ca pa`
      >| [(* hit /\ dirty ==> coh *)
	  FULL_SIMP_TAC std_ss [coh_dirty_lem] >>
	  RW_TAC std_ss [MVca_def, MValt_def] >> (
	      METIS_TAC [chit_other_lem, cdirty_other_lem]
	  )
	  ,
	  (* hit /\ clean ==> (ccnt = m <=> coh) *)
	  EQ_TAC
	  >| [(* ==> *)
	      RW_TAC std_ss [MVca_def, MValt_def] >>
	      MATCH_MP_TAC coh_equal_lem >>
	      RW_TAC std_ss [] >>
	      RES_TAC >>
	      IMP_RES_TAC chit_other_lem >>
	      METIS_TAC [cdirty_other_lem]
	      ,
	      (* <== *)
	      RW_TAC std_ss [] >>
	      IMP_RES_TAC chit_other_lem >>
	      `~cdirty_ ca pa'` by METIS_TAC [cdirty_other_lem] >>
	      IMP_RES_TAC coh_other_lem >>
	      IMP_RES_TAC coh_clean_lem >>
	      RW_TAC std_ss [MVca_def, MValt_def]
	     ]
	 ]
      ,
      (* miss *)
      FULL_SIMP_TAC std_ss [coh_miss_lem] >>
      RW_TAC std_ss [] >>
      `~chit_ ca pa'` by METIS_TAC [chit_other_lem] >>
      RW_TAC std_ss [MVca_def, MValt_def] >>
      IMP_RES_TAC not_chit_not_cdirty_lem
     ]
);

val coh_preserve_lem = store_thm("coh_preserve_lem", ``
!ca m pa ca' m'. coh ca m pa
	      /\ chit_ ca pa
	      /\ (ccnt_ ca' pa = ccnt_ ca pa)
	      /\ (!pa'. (tag pa' = tag pa) ==> (m' pa' = m pa'))
	      /\ (cdirty_ ca pa = cdirty_ ca' pa)
        ==> 
    coh ca' m' pa
``,
  RW_TAC std_ss [coh_def] >>
  METIS_TAC [ccnt_ccntw_lem]
);

val Coh_alt_lem = store_thm("Coh_alt_lem", ``
!ca m Rs. Coh ca m Rs 
              ==> 
          !pa. pa IN Rs ==> ((MVca ca m) T pa = (MValt ca m) T pa)
``,
  RW_TAC std_ss [Coh_def] >>
  RES_TAC >>
  IMP_RES_TAC coh_alt_lem >>
  FULL_SIMP_TAC std_ss []
);

val Coh_alt_lem2 = store_thm("Coh_alt_lem", ``
!ca m Rs. Coh ca m Rs 
              <=> 
          !pa pa'. pa IN Rs /\ (tag pa' = tag pa) ==> 
		   ((MVca ca m) T pa' = (MValt ca m) T pa')
``,
  RW_TAC std_ss [Coh_def] >>
  EQ_TAC >> (
      REPEAT STRIP_TAC >>
      RES_TAC >>
      IMP_RES_TAC coh_alt_lem 
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
      (* WT *)
      MATCH_MP_TAC coh_equal_lem >>
      RW_TAC std_ss []
     ]
);

val coh_ca_trans_lem = store_thm("coh_ca_trans_lem", ``
!ca m dop ca' m' pa. CA dop /\ coh ca m pa /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    coh ca' m' pa
``,
  REPEAT STRIP_TAC >>
  Cases_on `tag pa = tag (PA dop)`
  >| [(* same line *)
      IMP_RES_TAC ca_cacheable_ca >>
      PAT_X_ASSUM ``!pa. X`` (fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm )) >>
      REV_FULL_SIMP_TAC std_ss []
      >| [(* read hit *)
	  MATCH_MP_TAC coh_preserve_lem >>
          HINT_EXISTS_TAC >>
          HINT_EXISTS_TAC >>
	  RW_TAC std_ss [] >>
	  IMP_RES_TAC mem_cacheable_read_lem
	  ,
	  (* read miss *)
          MATCH_MP_TAC coh_equal_lem >>
	  RW_TAC std_ss [] >>
	  IMP_RES_TAC mem_cacheable_read_lem >>
	  `ccnt_ ca' pa' = ccnt_ ca' pa` by ( METIS_TAC [ccnt_other_lem] ) >>
	  `ccntw_ ca' pa' = lw (ccnt_ ca' pa') pa'` by ( 
	      METIS_TAC [lw_ccntw_lem] 
	  ) >>
	  RW_TAC std_ss [mllu_lem]
	  ,
	  (* write PA dop *)
	  IMP_RES_TAC coh_write_lem
	  ,
	  (* write hit, other addres on same line *)
	  IMP_RES_TAC coh_write_lem >>
	  IMP_RES_TAC coh_other_lem
	  ,
	  (* write miss, other addres on same line *)
	  IMP_RES_TAC coh_write_lem >>
	  IMP_RES_TAC coh_other_lem
	  ,
	  (* clean *)
	  FULL_SIMP_TAC std_ss [coh_miss_lem]
	 ]
      ,
      (* other line *)
      Cases_on `ca' (tag pa) = ca (tag pa)`
      >| [Cases_on `!pa'. (tag pa' = tag pa) ==> (m' pa' = m pa')`
          >| [(* cache and mem unchanged *)
	      IMP_RES_TAC coh_lem
	      ,
	      (* cache same, mem changed *)
	      FULL_SIMP_TAC std_ss [] >>
	      `pa' <> PA dop` by ( 
	          CCONTR_TAC >>
		  FULL_SIMP_TAC std_ss [] 
	      ) >>
	      IMP_RES_TAC mem_cacheable_other_lem >>
	      IMP_RES_TAC cdirty_other_lem >>
	      IMP_RES_TAC cdirty_lem >>
	      FULL_SIMP_TAC std_ss [coh_dirty_lem]
	     ]
	  ,
	  (* cache changed -> eviction *)
	  `pa <> PA dop` by ( 
	      CCONTR_TAC >>
	      FULL_SIMP_TAC std_ss [] 
	  ) >>
	  IMP_RES_TAC ca_cacheable_other_lem >>
          FULL_SIMP_TAC std_ss [coh_miss_lem]
	 ]
     ]
);

val coh_other_lem = store_thm("coh_other_lem", ``
!ca m dop ca' m' pa. coh ca m pa /\ ((ca',m') = mtfca (ca,m) dop) 
                  /\ (tag pa <> tag (PA dop))
        ==>
    coh ca' m' pa
``,
  REPEAT STRIP_TAC >>
  Cases_on `CA dop`  
  >| [(* cacheable *)
      IMP_RES_TAC coh_ca_trans_lem
      ,
      (* uncacheable *)
      IMP_RES_TAC ca_uncacheable >>
      MATCH_MP_TAC coh_lem >>
      EXISTS_TAC ``ca:cache_state`` >>
      HINT_EXISTS_TAC >>
      RW_TAC std_ss [] >>
      `pa' <> PA dop` by ( 
          CCONTR_TAC >>
          FULL_SIMP_TAC std_ss [] 
      ) >>
      IMP_RES_TAC cl_other_unchanged_lem >>
      METIS_TAC []
     ]
);

val coh_not_write_lem = store_thm("coh_not_write_lem", ``
!ca m dop ca' m' pa. coh ca m pa /\ ~wt dop /\ ((ca',m') = mtfca (ca,m) dop) 
        ==>
    coh ca' m' pa
``,
  REPEAT STRIP_TAC >>
  Cases_on `CA dop`  
  >| [(* cacheable *)
      IMP_RES_TAC coh_ca_trans_lem
      ,
      (* uncacheable *)
      IMP_RES_TAC ca_uncacheable >>
      `!pa'. (tag pa' = tag pa) ==> (MVcl m' T pa' = MVcl m T pa')` by (
          RW_TAC std_ss [] >>
          IMP_RES_TAC cl_mem_unchanged >>
	  METIS_TAC []
      ) >>
      FULL_SIMP_TAC std_ss [MVcl_def] >>
      MATCH_MP_TAC coh_lem >>
      EXISTS_TAC ``ca:cache_state`` >>
      HINT_EXISTS_TAC >>
      RW_TAC std_ss []
     ]
);


(* cacheable memory view *)

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

val ca_uncacheable_unchanged_lem = store_thm("ca_uncacheable_unchanged_lem", ``
!ca m dop ca' m'. ~CA dop /\ ~wt dop /\ coh ca m (PA dop)
	       /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    (MVca ca' m' T (PA dop) = MVca ca m T (PA dop))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC ca_uncacheable >>
  `MVcl m' T (PA dop) = MVcl m T (PA dop)` by (
      IMP_RES_TAC cl_mem_unchanged >>
      FULL_SIMP_TAC std_ss []
  ) >>
  FULL_SIMP_TAC std_ss [MVcl_def, MVca_def] >>
  RW_TAC std_ss []
);

val mvca_unchanged_lem = store_thm("mvca_unchanged_lem", ``
!ca m dop ca' m' pa. (~wt dop \/ pa <> PA dop) /\ coh ca m pa
		  /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    (MVca ca' m' T pa = MVca ca m T pa)
``,
  REPEAT GEN_TAC >>				    
  MATCH_MP_TAC ( 
      prove(``((A /\ ~B \/ B) /\ C /\ D ==> E) ==>
	      (A \/ B) /\ C /\ D ==> E``, PROVE_TAC [])
  ) >>
  REPEAT STRIP_TAC
  >| [(* not write, PA dop *)
      FULL_SIMP_TAC std_ss [] >>
      REV_FULL_SIMP_TAC std_ss [] >>
      Cases_on `CA dop`
      >| [(* cacheable *)
	  IMP_RES_TAC ca_unchanged_lem
	  ,
	  (* uncacheable *)
	  IMP_RES_TAC ca_uncacheable_unchanged_lem
	 ]
      ,
      (* other pa *)
      IMP_RES_TAC ca_other_unchanged_lem
     ]
);

val mvalt_unchanged_lem = store_thm("mvalt_unchanged_lem", ``
!ca m dop ca' m' pa. pa <> PA dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    (MValt ca' m' T pa = MValt ca m T pa)
``,
  REPEAT STRIP_TAC >>				    
  Cases_on `CA dop`
  >| [(* cacheable *)
      Cases_on `ca' pa = ca pa` 
      >| [(* cache unchanged *)
	  IMP_RES_TAC cdirty_lem >>
	  IMP_RES_TAC ccnt_lem >>
	  Cases_on `m' pa = m pa`
          >| [(* mem unchanged *)
	      RW_TAC std_ss [MValt_def]
	      ,
	      (* mem changed *)
	      IMP_RES_TAC mem_cacheable_other_lem >>
	      RW_TAC std_ss [MValt_def]
	     ]
	  ,
	  (* cache changed *)
	  IMP_RES_TAC ca_cacheable_other_lem >>
	  IMP_RES_TAC not_chit_not_cdirty_lem >>
	  RW_TAC std_ss [MValt_def] >>
	  CCONTR_TAC >>
	  IMP_RES_TAC mem_cacheable_other_lem
	 ]
      ,
      (* uncacheable *)
      IMP_RES_TAC ca_uncacheable >>
      IMP_RES_TAC cl_other_unchanged_lem >>
      RW_TAC std_ss [MValt_def]
     ]
);

val mvalt_not_write_lem = store_thm("mvalt_not_write_lem", ``
!ca m dop ca' m'. ~wt dop /\ ((ca',m') = mtfca (ca,m) dop)
        ==>
    (MValt ca' m' T (PA dop) = MValt ca m T (PA dop))
``,
  REPEAT STRIP_TAC >>				    
  Cases_on `CA dop`
  >| [(* cacheable *)
      Cases_on `ca' (PA dop) = ca (PA dop)` 
      >| [(* cache unchanged *)
	  IMP_RES_TAC cdirty_lem >>
	  IMP_RES_TAC ccnt_lem >>
	  Cases_on `m' (PA dop) = m (PA dop)`
          >| [(* mem unchanged *)
	      RW_TAC std_ss [MValt_def]
	      ,
	      (* mem changed *)
	      IMP_RES_TAC not_wt_lem
	      >| [(* read *)
		  IMP_RES_TAC mem_cacheable_read_lem
		  ,
		  (* clean *)
		  `~rd dop` by ( METIS_TAC [dop_cases_lem2] ) >>
		  IMP_RES_TAC ca_cacheable_ca >>
		  PAT_X_ASSUM ``!pa. x`` (
		      fn thm => ASSUME_TAC ( SPEC ``PA dop`` thm )
		  ) >>
		  REV_FULL_SIMP_TAC std_ss [] >>
		  `~chit_ ca (PA dop)` by ( METIS_TAC [chit_lem] ) >>
		  IMP_RES_TAC mem_cacheable_cl_miss_lem
		 ]
	     ]
	  ,
	  (* cache changed *)
	  IMP_RES_TAC not_wt_lem
	  >| [(* read *)
	      IMP_RES_TAC ca_cacheable_read_lem >>
	      IMP_RES_TAC not_chit_not_cdirty_lem >>
	      IMP_RES_TAC mem_cacheable_read_lem >>
	      RW_TAC std_ss [MValt_def]
	      ,
	      (* clean *)
	      IMP_RES_TAC ca_cacheable_cl_lem >>
	      PAT_X_ASSUM ``!pa. x`` (
	          fn thm => ASSUME_TAC ( SPEC ``PA dop`` thm )
	      ) >>
	      REV_FULL_SIMP_TAC std_ss [] >>
	      IMP_RES_TAC not_chit_not_cdirty_lem >>
	      RW_TAC std_ss [MValt_def]
	      >| [(* dirty eviction *)
		  IMP_RES_TAC mem_cacheable_cl_dirty_lem
		  ,
		  (* miss or clean eviction *)
		  Cases_on `chit_ ca (PA dop)`
		  >| [(* hit *)
		      IMP_RES_TAC ca_cacheable_mem >>
		      PAT_X_ASSUM ``!pa. x`` (
	                  fn thm => ASSUME_TAC ( SPEC ``PA dop`` thm )
		      ) >>
		      REV_FULL_SIMP_TAC std_ss []
		      ,
		      (* miss *)
		      IMP_RES_TAC mem_cacheable_cl_miss_lem
		     ]
		 ]
	     ]
	 ]
      ,
      (* uncacheable *)
      IMP_RES_TAC ca_uncacheable >>
      IMP_RES_TAC cl_mem_unchanged >>
      FULL_SIMP_TAC std_ss [MVcl_lem]
     ]
);


(*********** finish ************)

val _ = export_theory();
