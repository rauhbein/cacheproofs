(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;
open hwTheory;

val _ = new_theory "cacheless";

(********* cacheless state **********)

val _ = Datatype `cl_state = <| 
    cs  : core_state;
    M  : mem_state
|>`;

val cl_MD_def = Define `cl_MD s = MD_ (s.cs, MVcl s.M, UNIV:vadr set)`;
val cl_MDVA_def = Define `cl_MDVA s VAs = MD_ (s.cs, MVcl s.M, VAs)`;
val cl_Mon_def = Define `cl_Mon s r m ac = Mon_ (s.cs, MVcl s.M, r, m, ac)`;
val cl_Mmu_def = Define `cl_Mmu s va m ac = Mmu_ (s.cs, MVcl s.M, va, m, ac)`;
val cl_Cv_def = Define `cl_Cv s r = CV s.cs (MVcl s.M) r`;
val cl_mode_def = Define `cl_mode s = Mode s.cs`;
val cl_exentry_def = Define `cl_exentry s = exentry_ s.cs`;

val cl_Mon_lem = store_thm("cl_Mon_lem", ``
!s s'. (!r. r IN cl_MD s ==> (cl_Cv s r = cl_Cv s' r)) ==>
       (!r m ac. cl_Mon s r m ac <=> cl_Mon s' r m ac)
``,
  RW_TAC std_ss [cl_MD_def, cl_Mon_def, cl_Cv_def] >>
  RW_TAC std_ss [Mon__lem]
);

val cl_MD_lem = store_thm("cl_MD_lem", ``
!s s'. (!r. r IN cl_MD s ==> (cl_Cv s r = cl_Cv s' r)) ==> (cl_MD s = cl_MD s')
``,
  RW_TAC std_ss [cl_MD_def, cl_Cv_def, MD__lem]
);

val cl_MDVA_lem = store_thm("cl_MDVA_lem", ``
!s s' VAs. (!r. r IN cl_MDVA s VAs ==> (cl_Cv s r = cl_Cv s' r)) ==> 
    (cl_MDVA s VAs = cl_MDVA s' VAs)
``,
  RW_TAC std_ss [cl_MDVA_def, cl_Cv_def, MD__lem]
);

val cl_Cv_mem_lem = store_thm("cl_Cv_mem_lem", ``
!s pa. cl_Cv s (MEM pa) = MVcl s.M T pa
``,
  RW_TAC std_ss [cl_Cv_def, coreIfTheory.CV_def]
);

val cl_exentry_lem = store_thm("cl_exentry_lem", ``
!s. cl_exentry s ==> (cl_mode s = PRIV)
``,
  RW_TAC std_ss [cl_exentry_def, cl_mode_def, exentry__lem]
);

val (cl_trans_rules, cl_trans_ind, cl_trans_cases) = Hol_reln `
   (!s M dop cs' s'. 
	rd dop 
     /\ (M = Mode s.cs)
     /\ core_req (s.cs, M, MVcl s.M, DREQ dop, cs') 
     /\ (s'.M = mtfcl s.M dop)
     /\ core_rcv (cs', M, MVcl s.M (CA dop) (PA dop), s'.cs)
    ==>
    cl_trans s M (DREQ dop) s')
/\ (!s M dop s'. 
	~rd dop 
     /\ (M = Mode s.cs)
     /\ core_req (s.cs, M, MVcl s.M, DREQ dop, s'.cs) 
     /\ (s'.M = mtfcl s.M dop)
    ==>
    cl_trans s M (DREQ dop) s')
/\ (!s M pa cs' s'. 
        (M = Mode s.cs)
     /\ core_req (s.cs, M, MVcl s.M, FREQ pa, cs') 
     /\ (s'.M = mtfcl s.M (RD pa T))
     /\ core_rcv (cs', M, MVcl s.M T pa, s'.cs)
    ==>
    cl_trans s M (FREQ pa) s')
/\ (!s M pa s'. 
        (M = Mode s.cs)
     /\ core_req (s.cs, M, MVcl s.M, ICFR pa, s'.cs) 
     /\ (s'.M = s.M)
    ==>
    cl_trans s M (ICFR pa) s')
/\ (!s M s'. 
        (M = Mode s.cs)
     /\ core_req (s.cs, M, MVcl s.M, NOREQ, s'.cs)
     /\ (s'.M = s.M)
    ==>
    cl_trans s M NOREQ s')
`;

(* cl_trans lemmas *)

val cl_trans_mode_not_eq_lem = store_thm("cl_trans_mode_not_eq_lem", ``
!s M req s'. (M <> Mode s.cs) ==> ~cl_trans s M req s' 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC cl_trans_cases
); 

val cl_trans_mode_lem = 
cl_trans_mode_not_eq_lem |> SPEC_ALL 
			 |> CONTRAPOS 
			 |> GEN_ALL 
			 |> SIMP_RULE std_ss [];

val cl_trans_fetch_lem = store_thm("cl_trans_fetch_lem", ``
!s M req s'. Freq req /\ cl_trans s M req s' ==>
?cs'. core_req (s.cs, M, MVcl s.M, req, cs') 
   /\ (s'.M = mtfcl s.M (Dop req))
   /\ core_rcv (cs', M, MVcl s.M T (Adr req), s'.cs)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Freq_lem >>
  RW_TAC std_ss [Adr_def, Dop_def] >>
  IMP_RES_TAC cl_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct]
  ) >>
  FULL_SIMP_TAC std_ss [corereq_11] >>
  RW_TAC std_ss [] >>
  HINT_EXISTS_TAC >>
  RW_TAC std_ss []
);

val cl_trans_flush_lem = store_thm("cl_trans_flush_lem", ``
!s M req s'. Ireq req /\ cl_trans s M req s' ==>
    core_req (s.cs, M, MVcl s.M, req, s'.cs) 
 /\ (s'.M = s.M)
``,
  NTAC 5 STRIP_TAC >>
  IMP_RES_TAC Ireq_lem >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC cl_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct]
  ) >>
  FULL_SIMP_TAC std_ss [corereq_11] >>
  RW_TAC std_ss []
);

val cl_trans_data_lem = store_thm("cl_trans_data_lem", ``
!s M req s'. Dreq req /\ cl_trans s M req s' ==> 
    (s'.M = mtfcl s.M (Dop req))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Dreq_lem >>
  RW_TAC std_ss [Dop_def] >>
  IMP_RES_TAC cl_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct, corereq_11]
  )
);

val cl_trans_core_req_lem = store_thm("cl_trans_core_req_lem", ``
!s M req s'. cl_trans s M req s' ==> 
    ?cs'. core_req (s.cs, M, MVcl s.M, req, cs') 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC cl_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct] >>
      REV_FULL_SIMP_TAC std_ss [] >>
      HINT_EXISTS_TAC >>
      RW_TAC std_ss []
  )
);

val cl_trans_read_lem = store_thm("cl_trans_read_lem", ``
!s M req s'. Rreq req /\ cl_trans s M req s' ==>
?cs'. core_req (s.cs, M, MVcl s.M, req, cs') 
   /\ (s'.M = s.M)
   /\ core_rcv (cs', M, MVcl s.M (CAreq req) (Adr req), s'.cs)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rreq_lem >>
  RW_TAC std_ss [CAreq_def, Adr_def, Dop_def] >>
  IMP_RES_TAC cl_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct, corereq_11] >>
      REV_FULL_SIMP_TAC std_ss []
  ) >>
  HINT_EXISTS_TAC >>
  IMP_RES_TAC rd_lem >>
  RW_TAC std_ss [cachememTheory.mtfcl_def]
);

val cl_trans_write_lem = store_thm("cl_trans_write_lem", ``
!s M req s'. Wreq req /\ cl_trans s M req s' ==>
    core_req (s.cs, M, MVcl s.M, req, s'.cs) 
 /\ (s'.M = mtfcl s.M (Dop req))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC Wreq_lem >>
  ASM_REWRITE_TAC [Dop_def] >>
  IMP_RES_TAC not_rd_lem >>
  RW_TAC std_ss [] >> (
      IMP_RES_TAC cl_trans_cases >> (
          FULL_SIMP_TAC std_ss [corereq_distinct, corereq_11] >>
	  REV_FULL_SIMP_TAC std_ss []
      )
  )
);

val cl_trans_write_val_lem = store_thm("cl_trans_write_val_lem", ``
!s M req s'. Wreq req /\ cl_trans s M req s' /\ CAreq req ==>
    (cl_Cv s' (MEM (Adr req)) = VAL (Dop req))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC Wreq_lem >>
  ASM_REWRITE_TAC [Dop_def, Adr_def] >>
  IMP_RES_TAC not_rd_lem >>
  RW_TAC std_ss [] >> 
  `s'.M = mtfcl s.M dop` by ( 
      IMP_RES_TAC cl_trans_cases >> (
          FULL_SIMP_TAC std_ss [corereq_distinct, corereq_11] >>
	  REV_FULL_SIMP_TAC std_ss []
      )
  ) >>
  Cases_on `dop` >> (
      FULL_SIMP_TAC std_ss [wt_def]
  ) >>
  `MVcl (s'.M) b p = c` by (
      METIS_TAC [cachememTheory.cl_write_semantics]
  ) >>
  FULL_SIMP_TAC std_ss [cl_Cv_def, coreIfTheory.CV_def, 
			PA_def, VAL_def, CAreq_def, CA_def] >>
  REV_FULL_SIMP_TAC std_ss []
);


val cl_trans_clean_lem = store_thm("cl_trans_clean_lem", ``
!s M req s'. Creq req /\ cl_trans s M req s' ==>
    core_req (s.cs, M, MVcl s.M, req, s'.cs) 
 /\ (s'.M = s.M)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC Creq_lem >>
  ASM_REWRITE_TAC [] >>
  IMP_RES_TAC not_rd_lem >>
  RW_TAC std_ss [] >> (
      IMP_RES_TAC cl_trans_cases >> (
          FULL_SIMP_TAC std_ss [corereq_distinct, corereq_11] >>
          REV_FULL_SIMP_TAC std_ss []
      )
  ) >>
  IMP_RES_TAC cl_lem >>
  FULL_SIMP_TAC std_ss [cachememTheory.mtfcl_def]
);

val cl_trans_noreq_lem = store_thm("cl_trans_noreq_lem", ``
!s M s'. cl_trans s M NOREQ s' ==>
    core_req (s.cs, M, MVcl s.M, NOREQ, s'.cs) /\ (s'.M = s.M)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC cl_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct]
  )
);

val cl_trans_not_Dreq_lem = store_thm("cl_trans_not_Dreq_lem", ``
!s m req s'. ~Dreq req /\ cl_trans s m req s' ==>
    !pa. s'.M pa = s.M pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  `Freq req \/ Ireq req \/ (req = NOREQ)` by ( METIS_TAC [req_cases_lem] ) 
  >| [(* fetch *)
      IMP_RES_TAC cl_trans_fetch_lem >>
      IMP_RES_TAC Freq_lem >>
      FULL_SIMP_TAC std_ss [Dop_def] >>
      RW_TAC std_ss [cachememTheory.mtfcl_def]
      ,
      (* flush *)
      IMP_RES_TAC cl_trans_flush_lem >>
      FULL_SIMP_TAC std_ss [] 
      ,
      (* NOREQ *)
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC cl_trans_noreq_lem >>
      FULL_SIMP_TAC std_ss [] 
     ]
);

val cl_trans_not_write_lem = store_thm("cl_trans_not_write_lem", ``
!s m req s' pa. (Wreq req ==> Adr req <> pa) /\ cl_trans s m req s' ==>
    (cl_Cv s' (MEM pa) = cl_Cv s (MEM pa))
``,
  RW_TAC std_ss [cl_Cv_def, coreIfTheory.CV_def, cachememTheory.MVcl_def] >>
  Cases_on `Dreq req` 
  >| [(* Dreq *)
      IMP_RES_TAC Dreq_cases_lem 
      >| [(* read *)
	  IMP_RES_TAC cl_trans_read_lem >>
	  ASM_REWRITE_TAC []
	  ,
	  (* write *)
	  IMP_RES_TAC cl_trans_write_lem >>
	  RES_TAC >>
	  IMP_RES_TAC Wreq_lem >>
	  FULL_SIMP_TAC std_ss [Adr_def, Dop_def] >>
	  IMP_RES_TAC cachememTheory.cl_other_unchanged_lem >>
	  METIS_TAC []
	  ,
	  (* clean *)
	  IMP_RES_TAC cl_trans_clean_lem >>
	  ASM_REWRITE_TAC []
	 ]
      ,
      (* not Dreq *)
      IMP_RES_TAC cl_trans_not_Dreq_lem >>
      FULL_SIMP_TAC std_ss [] 
     ]
);

val cl_trans_not_write_lem2 = store_thm("cl_trans_not_write_lem2", ``
!s m req s' pa. ~(Wreq req /\ (Adr req = pa)) /\ cl_trans s m req s' ==>
    (cl_Cv s' (MEM pa) = cl_Cv s (MEM pa))
``,
  METIS_TAC [cl_trans_not_write_lem]
);

val cl_trans_mon_lem = store_thm("cl_trans_mon_lem", ``
!s M req s'. req <> NOREQ /\ cl_trans s M req s' ==>
    cl_Mon s (MEM (Adr req)) M (Acc req)
``,
  RW_TAC std_ss [cl_Mon_def] >>
  IMP_RES_TAC not_NOREQ_lem 
  >| [(* Dreq *)
      IMP_RES_TAC Dreq_cases_lem
      >| [(* read *)
	  IMP_RES_TAC cl_trans_read_lem
	  ,
	  (* write *)
	  IMP_RES_TAC cl_trans_write_lem
	  ,
	  (* clean *)
	  IMP_RES_TAC cl_trans_clean_lem 
	 ] >> (
          IMP_RES_TAC core_req_mem_req_lem
      )
      ,
      (* Freq *)
      IMP_RES_TAC cl_trans_fetch_lem >> 
      IMP_RES_TAC core_req_mem_req_lem
      ,
      (* Freq *)
      IMP_RES_TAC cl_trans_flush_lem >> 
      IMP_RES_TAC core_req_mem_req_lem
     ]
);

val cl_trans_progress_lem = store_thm("cl_trans_progress_lem", ``
!s. ?req s'. cl_trans s (cl_mode s) req s'
``,
  RW_TAC std_ss [cl_mode_def] >>
  ASSUME_TAC ( SPECL [``s.cs``,``MVcl s.M``] core_req_progress_lem ) >>
  FULL_SIMP_TAC std_ss [] >>
  ASSUME_TAC ( SPEC ``req:corereq`` req_cases_lem ) >>
  FULL_SIMP_TAC std_ss [] 
  >| [(* Freq *)
      `?M'. M' = mtfcl s.M (Dop req)` by ( RW_TAC std_ss [] ) >>
      `?cs'. core_rcv(c',Mode c',MVcl s.M T (Adr req),cs')` by (
          RW_TAC std_ss [core_rcv_progress_lem]
      ) >>
      IMP_RES_TAC core_req_mode_change_lem >>
      EXISTS_TAC ``req:corereq`` >>
      EXISTS_TAC ``<|cs := cs'; M := M'|>`` >>
      IMP_RES_TAC Freq_lem >>
      RW_TAC std_ss [cl_trans_cases] >> (
          FULL_SIMP_TAC std_ss [corereq_distinct, Adr_def, Dop_def]
      ) >>
      METIS_TAC []
      ,
      (* Ireq *)
      `?M'. M' = mtfcl s.M (Dop req)` by ( RW_TAC std_ss [] ) >>
      EXISTS_TAC ``req:corereq`` >>
      EXISTS_TAC ``<|cs := c'; M := s.M|>`` >>
      IMP_RES_TAC Ireq_lem >>
      RW_TAC std_ss [cl_trans_cases] >> (
          FULL_SIMP_TAC std_ss [corereq_distinct, Adr_def, Dop_def]
      )
      ,
      (* Dreq *)
      IMP_RES_TAC Dreq_cases_lem
      >| [(* read *)
	  `?cs'. core_rcv(c',Mode c',MVcl s.M (CAreq req) (Adr req),cs')` by (
	      RW_TAC std_ss [core_rcv_progress_lem]
	  ) >>
	  IMP_RES_TAC core_req_mode_change_lem >>
	  EXISTS_TAC ``req:corereq`` >>
	  EXISTS_TAC ``<|cs := cs'; M := s.M|>`` >>
	  IMP_RES_TAC Rreq_lem >>
	  RW_TAC std_ss [cl_trans_cases] >> (
	      FULL_SIMP_TAC std_ss [corereq_distinct, Adr_def, CAreq_def]
	  ) >>
	  IMP_RES_TAC rd_lem >>
	  RW_TAC std_ss [cachememTheory.mtfcl_def] >>
	  METIS_TAC []
	  ,
	  (* write *)
          `?M'. M' = mtfcl s.M (Dop req)` by ( RW_TAC std_ss [] ) >>
          EXISTS_TAC ``req:corereq`` >>
          EXISTS_TAC ``<|cs := c'; M := M'|>`` >>
          IMP_RES_TAC Wreq_lem >>
	  `~rd dop` by ( METIS_TAC [not_rd_lem] ) >>
          RW_TAC std_ss [cl_trans_cases] >> (
              FULL_SIMP_TAC std_ss [corereq_distinct, Adr_def, Dop_def]
          )
	  ,
	  (* clean *)
          EXISTS_TAC ``req:corereq`` >>
          EXISTS_TAC ``<|cs := c'; M := s.M|>`` >>
          IMP_RES_TAC Creq_lem >>
	  `~rd dop` by ( METIS_TAC [not_rd_lem] ) >>
          RW_TAC std_ss [cl_trans_cases] >> (
              FULL_SIMP_TAC std_ss [corereq_distinct, Adr_def, Dop_def]
          ) >>
	  IMP_RES_TAC cl_lem >>
	  RW_TAC std_ss [cachememTheory.mtfcl_def]
	 ]
      ,
      (* NOREQ *)
      EXISTS_TAC ``req:corereq`` >>
      EXISTS_TAC ``<|cs := c'; M := s.M|>`` >>
      RW_TAC std_ss [cl_trans_cases] >> (
          FULL_SIMP_TAC std_ss [corereq_distinct, Adr_def, Dop_def]
      )
     ]
);


(********* abstract cacheless transition **********)

val abs_cl_trans_def = Define `
   (abs_cl_trans s m [] s' = cl_trans s m NOREQ s' 
			  \/ ?pa. cl_trans s m (FREQ pa) s')
/\ (abs_cl_trans s m ((DOP d)::ds) s' = cl_trans s m (DREQ d) s' /\ (ds = []))
/\ (abs_cl_trans s m ((IFL pa)::ds) s' = cl_trans s m (ICFR pa) s' /\ (ds = []))
`;

val abs_cl_distinct_dl_lem = store_thm("abs_cl_distinct_dl_lem", ``
!s m dl s'. abs_cl_trans s m dl s' ==> ALL_DISTINCT dl
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl` 
  >| [(* empty *)
      FULL_SIMP_TAC std_ss [abs_cl_trans_def] >> (
          RW_TAC std_ss [listTheory.ALL_DISTINCT]
      )
      ,
      (* non-empty *)
      Cases_on `h` >> (
          FULL_SIMP_TAC std_ss [abs_cl_trans_def] >>
          RW_TAC std_ss [listTheory.ALL_DISTINCT_SING]
      )
     ]
);

val abs_cl_req_lem = store_thm("abs_ca_req_lem", ``
!s m dl s'. abs_cl_trans s m dl s' ==> 
    ?req. cl_trans s m req s' 
       /\ (dl <> [] ==> Adr req IN adrs dl /\ 
		        (    (?dop. (req = DREQ dop) /\ (dl = [DOP dop]))
	                  \/ (?pa. (req = ICFR pa) /\ (dl = [IFL pa]))))
       /\ ((dl = []) ==> (Freq req \/ (req = NOREQ)))
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl`
  >| [(* empty *)
      FULL_SIMP_TAC std_ss [abs_cl_trans_def] >> (
	  HINT_EXISTS_TAC >>
	  ASM_REWRITE_TAC [Freq_def]
      )
      ,
      (* non-empty *)
      Cases_on `h` >> (
          FULL_SIMP_TAC std_ss [abs_cl_trans_def] >> 
	  HINT_EXISTS_TAC >>
          RW_TAC list_ss [Adr_def, adrs_def, opd_def, PA_def]
      )
     ] 
);

val abs_cl_trans_no_dop_oblg = store_thm("abs_cl_trans_no_dop_oblg", ``
!s m s'. abs_cl_trans s m [] s' ==> 
    !pa. cl_Cv s' (MEM pa) = cl_Cv s (MEM pa)
``,
  RW_TAC std_ss [cl_Cv_def, coreIfTheory.CV_def, cachememTheory.MVcl_def] >>
  MATCH_MP_TAC cl_trans_not_Dreq_lem >>
  FULL_SIMP_TAC std_ss [abs_cl_trans_def] >> (
      METIS_TAC [Dreq_def]
  )
);

val abs_cl_trans_mode_oblg = store_thm("abs_cl_trans_mode_oblg", ``
!s m dl s'. abs_cl_trans s m dl s' ==> (cl_mode s = m) 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC abs_cl_req_lem >>
  IMP_RES_TAC cl_trans_core_req_lem >>
  IMP_RES_TAC core_req_curr_mode_lem >>
  ASM_REWRITE_TAC [cl_mode_def]
);

val abs_cl_trans_not_write_oblg = store_thm("abs_cl_trans_not_write_oblg", ``
!s m dl s' pa. abs_cl_trans s m dl s' /\ pa NOTIN writes dl ==> 
    (cl_Cv s' (MEM pa) = cl_Cv s (MEM pa))
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl`
  >| [(* empty *)
      IMP_RES_TAC abs_cl_trans_no_dop_oblg >>
      ASM_REWRITE_TAC []
      ,
      (* non-empty *)
      Cases_on `h` >> (
          FULL_SIMP_TAC std_ss [abs_cl_trans_def] >>
          REV_FULL_SIMP_TAC list_ss [] >>
          IMP_RES_TAC writes_lem >>
          MATCH_MP_TAC cl_trans_not_write_lem2 >>
          EXISTS_TAC ``m:mode`` )
      >| [(* DREQ *)
	  EXISTS_TAC ``DREQ d:corereq`` >>
          FULL_SIMP_TAC list_ss [opd_def, Wreq_def, Adr_def]
	  ,
	  (* ICFR *)
	  EXISTS_TAC ``ICFR p:corereq`` >>
          FULL_SIMP_TAC list_ss [opd_def, Wreq_def, Adr_def]
	 ]
     ]
);

val abs_cl_trans_not_adrs_oblg = store_thm("abs_cl_trans_not_adrs_oblg", ``
!s m dl s' pa. abs_cl_trans s m dl s' /\ pa NOTIN adrs dl ==> 
    (cl_Cv s' (MEM pa) = cl_Cv s (MEM pa))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC not_adrs_not_writes_lem >>
  IMP_RES_TAC abs_cl_trans_not_write_oblg
);

val abs_cl_progress_oblg = store_thm("abs_cl_progress_oblg", ``
!s. ?dl s'. abs_cl_trans s (cl_mode s) dl s'
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC ( SPEC ``s:cl_state`` cl_trans_progress_lem ) >>
  FULL_SIMP_TAC std_ss [] >>
  Cases_on `req` 
  >| [(* DREQ *)
      EXISTS_TAC ``[DOP d:mop]`` >>
      EXISTS_TAC ``s':cl_state`` >>
      RW_TAC std_ss [abs_cl_trans_def]
      ,
      (* FREQ *)
      EXISTS_TAC ``[]:mop list`` >>
      EXISTS_TAC ``s':cl_state`` >>
      RW_TAC std_ss [abs_cl_trans_def] >>
      METIS_TAC []
      ,
      (* ICFR *)
      EXISTS_TAC ``[IFL p]`` >>
      EXISTS_TAC ``s':cl_state`` >>
      RW_TAC std_ss [abs_cl_trans_def]
      ,
      (* FREQ and NOREQ *)
      EXISTS_TAC ``[]:mop list`` >>
      EXISTS_TAC ``s':cl_state`` >>
      RW_TAC std_ss [abs_cl_trans_def]
     ]
);

(* dependencies *)

val cl_Tr_def = Define `cl_Tr s va = Tr_ s.cs (MVcl s.M) va`;

val cl_vdeps_def = Define `cl_vdeps s = vdeps_ s.cs`;

val cl_deps_def = Define `cl_deps s = deps_ s.cs (MVcl s.M)`;

val cl_deps_pc_oblg = store_thm("cl_deps_pc_oblg", ``
!s. cl_Tr s (VApc s.cs) IN cl_deps s
``,
  RW_TAC std_ss [cl_Tr_def, cl_deps_def, coreIfTheory.deps__def] >>
  REWRITE_TAC [pred_setTheory.IN_UNION] >>
  DISJ1_TAC >>
  RW_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
  EXISTS_TAC ``VApc s.cs`` >>
  REWRITE_TAC [coreIfTheory.vdeps_spec]
);

val cl_deps_vdeps_oblg = store_thm("cl_deps_vdeps_oblg", ``
!s. cl_deps s SUBSET ({pa | ?va. (pa = cl_Tr s va) /\ va IN cl_vdeps s} UNION
                      {pa | MEM pa IN cl_MDVA s (cl_vdeps s)})
``,
  RW_TAC std_ss [cl_deps_def, coreIfTheory.deps__def] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF, pred_setTheory.IN_UNION] >>
  REPEAT STRIP_TAC
  >| [(* vdeps *)
      DISJ1_TAC >>
      RW_TAC std_ss [cl_vdeps_def, cl_Tr_def] >>
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC []
      ,
      (* MEM pa *)
      DISJ2_TAC >>
      RW_TAC std_ss [cl_vdeps_def, cl_MDVA_def]
     ]
);

val cl_deps_MD_oblg = store_thm("cl_deps_MD_oblg", ``
!s pa. MEM pa IN cl_MDVA s (cl_vdeps s) ==> pa IN cl_deps s
``,
  RW_TAC std_ss [cl_deps_def, cl_vdeps_def, cl_MDVA_def, 
		 coreIfTheory.deps__def] >>
  REWRITE_TAC [pred_setTheory.IN_UNION] >>
  DISJ2_TAC >>
  RW_TAC std_ss [pred_setTheory.IN_GSPEC_IFF]
);

val cl_deps_reads_oblg = store_thm("cl_deps_MD_oblg", ``
!s m dl s' pa. abs_cl_trans s m dl s' /\ pa IN reads dl ==> pa IN cl_deps s
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl` 
  >| [(* empty *)
      FULL_SIMP_TAC std_ss [reads_def, listTheory.FILTER, listTheory.MAP, 
			    listTheory.MEM]
      ,
      (* non-empty *)
      Cases_on `h`
      >| [(* Dreq *)
          FULL_SIMP_TAC std_ss [abs_cl_trans_def] >>
          REV_FULL_SIMP_TAC list_ss [] >>
          IMP_RES_TAC reads_lem >>
          IMP_RES_TAC cl_trans_mode_lem >>
          IMP_RES_TAC cl_trans_core_req_lem >>
          `Dreq (DREQ d)` by ( FULL_SIMP_TAC std_ss [Dreq_def] ) >>
          IMP_RES_TAC core_req_mmu_Dreq_lem >>
          RW_TAC std_ss [cl_deps_def, coreIfTheory.deps__def, 
          		 pred_setTheory.IN_UNION] >>
          DISJ1_TAC >>
          `~wt d` by ( FULL_SIMP_TAC std_ss [not_wt_lem, opd_def] ) >>
          FULL_SIMP_TAC std_ss [Acc_def, opd_def] >>
          RW_TAC std_ss [pred_setTheory.IN_GSPEC_IFF, coreIfTheory.Tr__def] >>
          HINT_EXISTS_TAC >>
          RW_TAC std_ss [Adr_def]
	  ,
	  (* Ireq *)
	  FULL_SIMP_TAC std_ss [abs_cl_trans_def] >>
	  REV_FULL_SIMP_TAC list_ss [] >>
	  IMP_RES_TAC reads_lem >>
	  FULL_SIMP_TAC std_ss [rd_def, opd_def]
	 ]
     ]
);

val cl_trans_fetch_deps_lem = store_thm("cl_trans_fetch_deps_lem", ``
!s M req s'. Freq req /\ cl_trans s M req s' ==> Adr req IN cl_deps s
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Freq_lem >>
  RW_TAC std_ss [Adr_def] >>
  IMP_RES_TAC cl_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct]
  ) >>
  FULL_SIMP_TAC std_ss [corereq_11] >>
  RW_TAC std_ss [] >>
  IMP_RES_TAC core_req_mmu_Freq_lem >>
  IMP_RES_TAC Mmu_read_fetch_lem >>
  `pa = cl_Tr s (VApc s.cs)` by (
      RW_TAC std_ss [cl_Tr_def, coreIfTheory.Tr__def, Adr_def]
  ) >>
  RW_TAC std_ss [cl_deps_pc_oblg]
);

val cl_trans_fetch_pc_lem = store_thm("cl_trans_fetch_pc_lem", ``
!s M req s'. Freq req /\ cl_trans s M req s' ==>
    (Adr req = cl_Tr s (VApc s.cs))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Freq_lem >>
  RW_TAC std_ss [Adr_def] >>
  IMP_RES_TAC cl_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct]
  ) >>
  FULL_SIMP_TAC std_ss [corereq_11] >>
  RW_TAC std_ss [] >>
  IMP_RES_TAC core_req_mmu_Freq_lem >>
  IMP_RES_TAC Mmu_read_fetch_lem >>
  RW_TAC std_ss [cl_Tr_def, coreIfTheory.Tr__def, Adr_def]
);

(* fix translation for privileged mode *)

val cl_fixmmu_def = Define `cl_fixmmu s VAs f = 
!va. va IN VAs ==> 
     (cl_Mmu s va PRIV R = SOME (f va, T))
  /\ (!pa c. (cl_Mmu s va PRIV W = SOME (pa,c)) ==> (pa = f va) /\ c)
  /\ (!pa c. (cl_Mmu s va PRIV EX = SOME (pa,c)) ==> (pa = f va) /\ c)
`;

val cl_fixmmu_Tr_oblg = store_thm("cl_fixmmu_Tr_oblg", ``
!s VAs va f. cl_fixmmu s VAs f /\ va IN VAs /\ (cl_mode s = PRIV) ==> 
    (cl_Tr s va = f va)
``,
  REWRITE_TAC [cl_fixmmu_def, cl_Tr_def, cl_Mmu_def, cl_mode_def,
	       coreIfTheory.Tr__def] >>
  REPEAT STRIP_TAC >>
  RES_TAC >>
  ASM_REWRITE_TAC [optionTheory.THE_DEF, pairTheory.FST]
);

val cl_fixmmu_CA_lem = store_thm("cl_fixmmu_CA_lem", ``
!s va acc pa c VAs f. 
    cl_fixmmu s VAs f 
 /\ va IN VAs
 /\ (cl_Mmu s va PRIV acc = SOME (pa,c))
	==>
    c
``,
  REWRITE_TAC [cl_fixmmu_def, cl_Mmu_def] >>
  REPEAT STRIP_TAC >>
  Cases_on `acc` >> (
      RES_TAC >>
      METIS_TAC [optionTheory.SOME_11, pairTheory.PAIR_EQ]
  )
);

val cl_fixmmu_MD_lem = store_thm("cl_fixmmu_MD_lem", ``
!s s' VAs f. 
    cl_fixmmu s VAs f 
 /\ (!r. r IN cl_MDVA s VAs ==> (cl_Cv s r = cl_Cv s' r))
	==>
    cl_fixmmu s' VAs f
``,
  REWRITE_TAC [cl_fixmmu_def, cl_Mmu_def, cl_Cv_def, cl_MDVA_def] >>
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC Mmu_lem >>
  METIS_TAC []
);

val abs_cl_trans_fixmmu_CA_oblg = store_thm("abs_cl_trans_fixmmu_CA_oblg", ``
!s dl s' VAs f. 
    cl_fixmmu s VAs f 
 /\ cl_vdeps s SUBSET VAs 
 /\ abs_cl_trans s PRIV dl s' 
	==>
    !d. MEM d dl ==> CA (opd d)
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl = []` 
  >| [(* [] *)
      FULL_SIMP_TAC list_ss []
      ,
      (* [d] *)
      IMP_RES_TAC abs_cl_req_lem >>
      REV_FULL_SIMP_TAC std_ss []
      >| [(* DREQ *)
          FULL_SIMP_TAC list_ss [opd_def] >>
          IMP_RES_TAC cl_trans_core_req_lem >>
          `Dreq (DREQ dop)` by ( REWRITE_TAC [Dreq_def] ) >>
          IMP_RES_TAC core_req_mmu_Dreq_lem >>
          FULL_SIMP_TAC std_ss [cl_vdeps_def, pred_setTheory.SUBSET_DEF,
          			CAreq_def] >>
          RES_TAC >>
          IMP_RES_TAC ( cl_fixmmu_CA_lem |> SIMP_RULE std_ss [cl_Mmu_def] ) 
	  ,
	  (* ICFR *)
	  FULL_SIMP_TAC list_ss [opd_def, CA_def]
	 ]
     ]
);

(********* bisimulation properties *********)

val deps_MD_lem = store_thm("deps_MD_lem", ``
!s sc. (s.cs = sc.cs)
    /\ (!pa. pa IN ca_deps sc ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (!r. r IN MDVA sc (ca_vdeps sc) ==> (cl_Cv s r = Cv sc r))
``,
  RW_TAC std_ss [cl_Cv_def, Cv_def] >>
  ASSUME_TAC ( SPEC ``r:resource`` coreIfTheory.res_cases ) >>
  FULL_SIMP_TAC std_ss []
  >| [(* MEM pa *)
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC ca_deps_MD_oblg >>
      RES_TAC >>
      METIS_TAC []
      ,
      (* register *)
      Cases_on `r` >> (
          FULL_SIMP_TAC std_ss [coreIfTheory.reg_res_def, coreIfTheory.CV_def]
      )
     ]
);

val cl_deps_MD_lem = store_thm("cl_deps_MD_lem", ``
!s sc. (s.cs = sc.cs)
    /\ (!pa. pa IN cl_deps s ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (!r. r IN cl_MDVA s (cl_vdeps s) ==> (cl_Cv s r = Cv sc r))
``,
  RW_TAC std_ss [cl_Cv_def, Cv_def] >>
  ASSUME_TAC ( SPEC ``r:resource`` coreIfTheory.res_cases ) >>
  FULL_SIMP_TAC std_ss []
  >| [(* MEM pa *)
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC cl_deps_MD_oblg >>
      RES_TAC >>
      METIS_TAC []
      ,
      (* register *)
      Cases_on `r` >> (
          FULL_SIMP_TAC std_ss [coreIfTheory.reg_res_def, coreIfTheory.CV_def]
      )
     ]
);

val deps_vdeps_eq_lem = store_thm("deps_vdeps_eq_lem", ``
!s sc. (s.cs = sc.cs)
    /\ (!pa. pa IN ca_deps sc ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (cl_vdeps s = ca_vdeps sc)
``,
  RW_TAC std_ss [cl_vdeps_def, ca_vdeps_def]
);

val cl_deps_vdeps_eq_lem = store_thm("cl_deps_vdeps_eq_lem", ``
!s sc. (s.cs = sc.cs)
    /\ (!pa. pa IN cl_deps s ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (cl_vdeps s = ca_vdeps sc)
``,
  RW_TAC std_ss [cl_vdeps_def, ca_vdeps_def]
);

val deps_MD_eq_lem = store_thm("deps_MD_eq_lem", ``
!s sc. (s.cs = sc.cs)
    /\ (!pa. pa IN ca_deps sc ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (cl_MDVA s (cl_vdeps s) = MDVA sc (ca_vdeps sc))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC deps_vdeps_eq_lem >>
  IMP_RES_TAC deps_MD_lem >>
  FULL_SIMP_TAC  std_ss [cl_MDVA_def, MDVA_def, cl_Cv_def, Cv_def] >>
  MATCH_MP_TAC EQ_SYM >>
  MATCH_MP_TAC MD__lem >>
  REPEAT STRIP_TAC >>
  RES_TAC >>
  REV_FULL_SIMP_TAC std_ss [] 
);

val cl_deps_MD_eq_lem = store_thm("cl_deps_MD_eq_lem", ``
!s sc. (s.cs = sc.cs)
    /\ (!pa. pa IN cl_deps s ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (cl_MDVA s (cl_vdeps s) = MDVA sc (ca_vdeps sc))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC cl_deps_vdeps_eq_lem >>
  IMP_RES_TAC cl_deps_MD_lem >>
  FULL_SIMP_TAC  std_ss [cl_MDVA_def, MDVA_def, cl_Cv_def, Cv_def] >>
  MATCH_MP_TAC MD__lem >>
  REPEAT STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [] 
);


val deps_Tr_eq_lem = store_thm("deps_Tr_eq_lem", ``
!s sc. (s.cs = sc.cs)
    /\ (!pa. pa IN ca_deps sc ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (!va. va IN ca_vdeps sc ==> (cl_Tr s va = ca_Tr sc va))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC deps_vdeps_eq_lem >>
  IMP_RES_TAC deps_MD_lem >>
  `MDVA sc (ca_vdeps sc) = cl_MDVA s (cl_vdeps s)` by (
      IMP_RES_TAC deps_MD_eq_lem >>
      FULL_SIMP_TAC std_ss []
  ) >>
  FULL_SIMP_TAC  std_ss [cl_MDVA_def, MDVA_def, cl_Cv_def, Cv_def, 
			 cl_Tr_def, ca_Tr_def, coreIfTheory.Tr__def] >>
  MATCH_MP_TAC (
      prove(``(x = y) ==> (FST x = FST y)``, PROVE_TAC [])
  ) >>
  MATCH_MP_TAC (
      prove(``(x = y) ==> (THE x = THE y)``, PROVE_TAC [])
  ) >>
  `va IN cl_vdeps s` by ( RW_TAC std_ss [] ) >>
  IMP_RES_TAC Mmu_lem >>
  REV_FULL_SIMP_TAC std_ss []  
);

val cl_deps_Tr_eq_lem = store_thm("cl_deps_Tr_eq_lem", ``
!s sc. (s.cs = sc.cs)
    /\ (!pa. pa IN cl_deps s ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (!va. va IN cl_vdeps s ==> (cl_Tr s va = ca_Tr sc va))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC cl_deps_vdeps_eq_lem >>
  IMP_RES_TAC cl_deps_MD_lem >>
  `cl_MDVA s (cl_vdeps s) = MDVA sc (ca_vdeps sc)` by (
      IMP_RES_TAC cl_deps_MD_eq_lem >>
      FULL_SIMP_TAC std_ss []
  ) >>
  FULL_SIMP_TAC  std_ss [cl_MDVA_def, MDVA_def, cl_Cv_def, Cv_def, 
			 cl_Tr_def, ca_Tr_def, coreIfTheory.Tr__def] >>
  MATCH_MP_TAC (
      prove(``(x = y) ==> (FST x = FST y)``, PROVE_TAC [])
  ) >>
  MATCH_MP_TAC (
      prove(``(x = y) ==> (THE x = THE y)``, PROVE_TAC [])
  ) >>
  `va IN cl_vdeps s` by ( RW_TAC std_ss [] ) >>
  METIS_TAC [Mmu_lem]  
);

val deps_eq_oblg = store_thm("deps_eq_oblg", ``
!s sc. (s.cs = sc.cs)
    /\ (!pa. pa IN ca_deps sc ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (cl_deps s = ca_deps sc)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC deps_MD_eq_lem >>
  IMP_RES_TAC deps_Tr_eq_lem >>
  FULL_SIMP_TAC std_ss [cl_deps_def, ca_deps_def, cl_Cv_def, Cv_def, 
			MDVA_def, cl_MDVA_def, coreIfTheory.deps__def,
		        pred_setTheory.IN_UNION] >>
  MATCH_MP_TAC (
      prove(``(A = C) /\ (B = D) ==> (A UNION B = C UNION D)``, PROVE_TAC [])
  ) >>
  RW_TAC std_ss [pred_setTheory.EXTENSION]
  >| [(* vdeps *)
      FULL_SIMP_TAC std_ss [cl_Tr_def, ca_Tr_def, ca_vdeps_def,
			    pred_setTheory.IN_GSPEC_IFF] >>
      METIS_TAC []
      ,
      (* MD *)
      FULL_SIMP_TAC std_ss [cl_vdeps_def, ca_vdeps_def,
			    pred_setTheory.IN_GSPEC_IFF] >>
      REV_FULL_SIMP_TAC std_ss []
     ]
);

val cl_deps_eq_oblg = store_thm("cl_deps_eq_oblg", ``
!s sc. (s.cs = sc.cs)
    /\ (!pa. pa IN cl_deps s ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (cl_deps s = ca_deps sc)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC cl_deps_MD_eq_lem >>
  IMP_RES_TAC cl_deps_Tr_eq_lem >>
  FULL_SIMP_TAC std_ss [cl_deps_def, ca_deps_def, cl_Cv_def, Cv_def, 
			MDVA_def, cl_MDVA_def, coreIfTheory.deps__def,
		        pred_setTheory.IN_UNION] >>
  MATCH_MP_TAC (
      prove(``(A = C) /\ (B = D) ==> (A UNION B = C UNION D)``, PROVE_TAC [])
  ) >>
  RW_TAC std_ss [pred_setTheory.EXTENSION]
  >| [(* vdeps *)
      FULL_SIMP_TAC std_ss [cl_Tr_def, ca_Tr_def, cl_vdeps_def,
			    pred_setTheory.IN_GSPEC_IFF] >>
      METIS_TAC []
      ,
      (* MD *)
      FULL_SIMP_TAC std_ss [cl_vdeps_def, ca_vdeps_def,
			    pred_setTheory.IN_GSPEC_IFF] >>
      REV_FULL_SIMP_TAC std_ss []
     ]
);

val core_bisim_req_lem = store_thm("core_bisim_req_lem", ``
!s sc m req req' cs' cs''. 
    (s.cs = sc.cs)
 /\ core_req (sc.cs,m,dmvca sc.ms,req,cs')
 /\ core_req (s.cs,m,MVcl s.M,req',cs'')
 /\ (!pa. pa IN ca_deps sc ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (cs' = cs'') /\ (req = req')  
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  `m = Mode sc.cs` by ( 
      IMP_RES_TAC core_req_curr_mode_lem >>
      RW_TAC std_ss []
  ) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [] >>
  `core_req(sc.cs,Mode sc.cs,dmvca sc.ms, req, cs') <=> 
   core_req(sc.cs,Mode sc.cs,MVcl s.M, req, cs')` suffices_by (
      STRIP_TAC >>
      RES_TAC >>
      IMP_RES_TAC core_req_det_lem >>
      RW_TAC std_ss []
  ) >>
  MATCH_MP_TAC core_req_MD_mv_lem >>
  IMP_RES_TAC deps_MD_lem >>
  FULL_SIMP_TAC std_ss [MDVA_def, cl_Cv_def, Cv_def, ca_vdeps_def] >>
  METIS_TAC []
);

val core_bisim_dl_oblg = store_thm("core_bisim_dl_oblg", ``
!s s' sc sc' m dl dlc. 
    abs_cl_trans s m dl s'
 /\ abs_ca_trans sc m dlc sc'
 /\ (s.cs = sc.cs)
 /\ (!pa. pa IN ca_deps sc ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (dl = dlc)
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl`
  >| [(* empty *)
      Cases_on `dlc`
      >| [(* empty *)
	  FULL_SIMP_TAC list_ss [writes_def]
	  ,
	  (* empty = non-empty not possible *)
	  REWRITE_TAC [listTheory.list_distinct] >>
	  Cases_on `h` >> (
	      FULL_SIMP_TAC std_ss [abs_ca_trans_def] >>
	      FULL_SIMP_TAC std_ss [abs_cl_trans_def] >> (
	          IMP_RES_TAC hw_trans_core_req_lem >>
	          IMP_RES_TAC cl_trans_core_req_lem >>
	          IMP_RES_TAC core_bisim_req_lem >>
	          FULL_SIMP_TAC std_ss [corereq_distinct]
	      )
	  )
	 ]
      ,
      Cases_on `dlc`
      >| [(* non-empty = empty -> not possible *)
	  REWRITE_TAC [GSYM listTheory.list_distinct] >>
	  Cases_on `h` >> (
	      FULL_SIMP_TAC std_ss [abs_ca_trans_def] >>
	      FULL_SIMP_TAC std_ss [abs_cl_trans_def] >> (
	          IMP_RES_TAC hw_trans_core_req_lem >>
	          IMP_RES_TAC cl_trans_core_req_lem >>
	          IMP_RES_TAC core_bisim_req_lem >>
	          FULL_SIMP_TAC std_ss [corereq_distinct]
	      )
	  )
	  ,
	  (* non-empty vs non-empty *)
	  FULL_SIMP_TAC list_ss [writes_def] >>
	  Cases_on `h` >> (
	      IMP_RES_TAC abs_cl_trans_def >>
	      Cases_on `h'` >> (
	          IMP_RES_TAC abs_ca_trans_def >>
	          IMP_RES_TAC hw_trans_core_req_lem >>
	          IMP_RES_TAC cl_trans_core_req_lem >>
	          IMP_RES_TAC core_bisim_req_lem >>
	          FULL_SIMP_TAC std_ss [corereq_distinct] 
	      ) >>
	      FULL_SIMP_TAC std_ss [corereq_11, mop_11]
	  )
	 ]
     ]
);


val core_bisim_oblg = store_thm("core_bisim_oblg", ``
!s s' sc sc' m dl dlc. 
    abs_cl_trans s m dl s'
 /\ abs_ca_trans sc m dlc sc'
 /\ (s.cs = sc.cs)
 /\ (!pa. pa IN ca_deps sc ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
 /\ (cl_Cv s (MEM (cl_Tr s (VApc s.cs))) = imv sc.ms T (ca_Tr sc (VApc sc.cs)))
 /\ (cl_deps s = ca_deps sc)
 /\ (!d. MEM d dl ==> CA (opd d))
        ==>
    (s'.cs = sc'.cs)
 /\ (dl = dlc)
 /\ (!pa. pa IN writes dl ==> (cl_Cv s' (MEM pa) = Cv sc' (MEM pa)))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >> 
  IMP_RES_TAC core_bisim_dl_oblg >>
  FULL_SIMP_TAC std_ss [] >>
  Cases_on `dlc`
  >| [(* empty *)
      FULL_SIMP_TAC list_ss [writes_def] >>
      IMP_RES_TAC abs_cl_trans_def >> (
          IMP_RES_TAC abs_ca_trans_def >>
	  IMP_RES_TAC hw_trans_core_req_lem >>
	  IMP_RES_TAC cl_trans_core_req_lem >>
	  IMP_RES_TAC core_bisim_req_lem >>
	  FULL_SIMP_TAC std_ss [corereq_distinct] )
      >| [(* NOREQ *) 
	  REV_FULL_SIMP_TAC std_ss [cl_trans_cases, corereq_distinct] >>
	  FULL_SIMP_TAC std_ss [hw_trans_cases, corereq_distinct] >>
	  RW_TAC list_ss [] >>
	  `(sc'.cs = s'.cs) /\ (NOREQ = NOREQ)` suffices_by (
	      RW_TAC std_ss []
	  ) >>
	  MATCH_MP_TAC core_bisim_req_lem >>
	  METIS_TAC []
	  ,
	  (* FREQ *)
	  `Freq (FREQ pa)` by ( REWRITE_TAC [Freq_def] ) >>
	  IMP_RES_TAC cl_trans_fetch_pc_lem >>
	  IMP_RES_TAC hw_trans_fetch_pc_lem >>
	  REV_FULL_SIMP_TAC std_ss [cl_trans_cases, corereq_distinct] >>
	  FULL_SIMP_TAC std_ss [hw_trans_cases, corereq_distinct] >>
	  RW_TAC list_ss [] >>
	  `(cs'''' = cs''') /\ (FREQ pa = FREQ pa)` by (
	      MATCH_MP_TAC core_bisim_req_lem >>
	      METIS_TAC []
	  ) >>
	  RW_TAC std_ss [] >>
	  FULL_SIMP_TAC std_ss [cl_Cv_def, coreIfTheory.CV_def, Adr_def] >>
	  REV_FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC core_rcv_det_lem
	 ]
      ,
      (* non-empty vs non-empty *)
      Cases_on `h` 
      >| [(* Dreq *)
          IMP_RES_TAC abs_cl_trans_def >> 
	  IMP_RES_TAC abs_ca_trans_def >>
          IMP_RES_TAC hw_trans_core_req_lem >>
          IMP_RES_TAC cl_trans_core_req_lem >>
          IMP_RES_TAC core_bisim_req_lem >>
          FULL_SIMP_TAC list_ss [writes_def, opd_def] >> 
          `Dreq (DREQ d)` by ( REWRITE_TAC [Dreq_def] ) >>
          IMP_RES_TAC Dreq_cases_lem
          >| [(* read *)
              IMP_RES_TAC cl_trans_read_lem >>
              IMP_RES_TAC hw_trans_read_lem >>
              FULL_SIMP_TAC std_ss [Rreq_def, Wreq_def] >>
              RW_TAC list_ss [] >>
              FULL_SIMP_TAC list_ss [CAreq_def] >>
              `(cs''''' = cs''') /\ (DREQ d = DREQ d)` by (
                  MATCH_MP_TAC core_bisim_req_lem >>
         	  METIS_TAC []
              ) >>
              RW_TAC std_ss [] >>
              REV_FULL_SIMP_TAC std_ss [] >>
              FULL_SIMP_TAC std_ss [cl_Cv_def, Cv_def,
         			    coreIfTheory.CV_def, Adr_def] >>
              `PA d IN reads [DOP d]` by (
                   RW_TAC list_ss [reads_def, opd_def]
              ) >>
              IMP_RES_TAC ca_deps_reads_oblg >>
              RES_TAC >>
              FULL_SIMP_TAC std_ss [] >>
              IMP_RES_TAC core_rcv_det_lem
              ,
              (* write *)
              IMP_RES_TAC cl_trans_write_lem >>
              IMP_RES_TAC hw_trans_write_lem >>
              FULL_SIMP_TAC std_ss [Rreq_def, Wreq_def] >>
              IMP_RES_TAC core_bisim_req_lem >>
              RW_TAC list_ss [] >>
              FULL_SIMP_TAC list_ss [CAreq_def] >>
              `Wreq (DREQ d)` by ( ASM_REWRITE_TAC [Wreq_def] ) >>
              `CAreq (DREQ d)` by ( ASM_REWRITE_TAC [CAreq_def] ) >>
              IMP_RES_TAC cl_trans_write_val_lem >>
              IMP_RES_TAC hw_trans_write_val_lem >>
              FULL_SIMP_TAC std_ss [Adr_def]
              ,
              (* clean *)
              IMP_RES_TAC cl_trans_clean_lem >>
	      IMP_RES_TAC hw_trans_clean_lem >>
              FULL_SIMP_TAC std_ss [Rreq_def, Wreq_def, Creq_def] >>
              IMP_RES_TAC core_bisim_req_lem >>
              RW_TAC list_ss []	      
             ]
	  ,
	  (* Ireq *)
          IMP_RES_TAC abs_cl_trans_def >> 
	  IMP_RES_TAC abs_ca_trans_def >>
          `Ireq (ICFR p)` by ( REWRITE_TAC [Ireq_def] ) >>
          IMP_RES_TAC cl_trans_flush_lem >>
	  IMP_RES_TAC hw_trans_flush_lem >>
          FULL_SIMP_TAC list_ss [writes_def, opd_def, wt_def] >> 
          IMP_RES_TAC core_bisim_req_lem >>
	  RW_TAC std_ss []	      
         ]
     ]
);

(********* cacheless computation **********)

val (cl_kcomp_rules, cl_kcomp_ind, cl_kcomp_cases) = Hol_reln `
   (!s. cl_exentry s ==> cl_kcomp s s 0)
/\ (!s s' s'' n. cl_kcomp s s' n /\ (?dl. abs_cl_trans s' PRIV dl s'')
        ==>
    cl_kcomp s s'' (SUC n))
`;

val cl_kcomp_exentry_lem = store_thm("cl_kcomp_exentry_lem", ``
!s s' n. cl_kcomp s s' n ==> cl_exentry s
``,
  Induct_on `n` 
  >| [(* n = 0 *)
      ONCE_REWRITE_TAC [cl_kcomp_cases] >>
      REPEAT STRIP_TAC >>
      FULL_SIMP_TAC std_ss [numTheory.NOT_SUC]
      ,
      (* n -> SUC n *)
      ONCE_REWRITE_TAC [cl_kcomp_cases] >>
      REPEAT STRIP_TAC >>
      FULL_SIMP_TAC std_ss [numTheory.INV_SUC] >>
      RW_TAC std_ss [] >>
      RES_TAC
     ]
);

val cl_kcomp_0_lem = store_thm("cl_kcomp_0_lem", ``
!s s'. cl_kcomp s s' 0 ==> cl_exentry s /\ (s' = s)
``,
  ONCE_REWRITE_TAC [cl_kcomp_cases] >>
  FULL_SIMP_TAC std_ss [numTheory.NOT_SUC]
);

val cl_kcomp_0_lem2 = store_thm("cl_kcomp_0_lem2", ``
!s s'. cl_kcomp s s' 0 <=> cl_exentry s /\ (s' = s)
``,
  ONCE_REWRITE_TAC [cl_kcomp_cases] >>
  FULL_SIMP_TAC std_ss [numTheory.NOT_SUC] >>
  METIS_TAC []
);

val cl_kcomp_SUC_lem = store_thm("cl_kcomp_SUC_lem", ``
!s s' n. 
cl_kcomp s s' (SUC n) 
    <=> 
?s'' dl. cl_kcomp s s'' n /\ abs_cl_trans s'' PRIV dl s'
``,
  REPEAT STRIP_TAC >>
  EQ_TAC 
  >| [(* ==> *)
      STRIP_TAC >>
      IMP_RES_TAC cl_kcomp_cases >> (
          FULL_SIMP_TAC std_ss [numTheory.NOT_SUC]
      ) >>
      METIS_TAC []
      ,
      (* <== *)
      STRIP_TAC >>
      ONCE_REWRITE_TAC [cl_kcomp_cases] >>
      FULL_SIMP_TAC std_ss [numTheory.NOT_SUC] >>
      METIS_TAC []
     ]      
);

val cl_kcomp_exists_lem = store_thm("cl_kcomp_exists_lem", ``
!s n. cl_exentry s ==> 
    ?m s'. m <= n /\ cl_kcomp s s' m /\ (m < n ==> (cl_mode s' = USER))
``,
  STRIP_TAC >>
  Induct
  >| [(* n = 0 *)
      STRIP_TAC >>
      EXISTS_TAC ``0`` >>
      EXISTS_TAC ``s:cl_state`` >>
      FULL_SIMP_TAC arith_ss [cl_kcomp_0_lem2]
      ,
      (* n -> SUC n *)
      STRIP_TAC >>
      RES_TAC >>
      Cases_on `m = n`
      >| [(* m = n *)
	  Cases_on `cl_mode s'`
	  >| [(* PRIV *)
	      EXISTS_TAC ``SUC n`` >>
	      FULL_SIMP_TAC arith_ss [cl_kcomp_SUC_lem] >>
	      ASSUME_TAC ( SPEC ``s':cl_state`` abs_cl_progress_oblg ) >>
	      REV_FULL_SIMP_TAC std_ss [] >>
	      METIS_TAC []
	      ,
	      (* USER *)
	      EXISTS_TAC ``m:num`` >>
	      FULL_SIMP_TAC arith_ss [cl_kcomp_SUC_lem] >>
	      METIS_TAC []
	     ]
	  ,
	  (* m <> n *)
	  `m < n` by ( DECIDE_TAC ) >>
	  EXISTS_TAC ``m:num`` >>
	  FULL_SIMP_TAC arith_ss [cl_kcomp_SUC_lem] >>
	  METIS_TAC []
	 ]	  
     ]      
);


val cl_wrel_def = Define` cl_wrel s s' = 
?n. cl_kcomp s s' n /\ (cl_mode s' = USER)`;

val cl_wrel_exentry_lem = store_thm("cl_wrel_exentry_lem", ``
!s s'. cl_wrel s s' ==> cl_exentry s
``,
  RW_TAC std_ss [cl_wrel_def] >>
  IMP_RES_TAC cl_kcomp_exentry_lem
);

val cl_wrel_mode_lem = store_thm("cl_wrel_mode_lem", ``
!s s'. cl_wrel s s' ==> (cl_mode s = PRIV) /\ (cl_mode s' = USER)
``,
  RW_TAC std_ss [cl_wrel_def]
  >| [(* PRIV *)
      IMP_RES_TAC cl_kcomp_exentry_lem >>
      FULL_SIMP_TAC std_ss [cl_exentry_def, cl_mode_def, 
			    coreIfTheory.exentry_spec]
      ,
      (* USER *)
      ASM_REWRITE_TAC []
     ]      
);



(*********** finish ************)

val _ = export_theory();
