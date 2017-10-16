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

val cl_MD_def = Define `cl_MD s = MD_ (s.cs, MVcl s.M)`;
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
  `Freq req \/ (req = NOREQ)` by ( METIS_TAC [req_cases_lem] ) 
  >| [(* fetch *)
      IMP_RES_TAC cl_trans_fetch_lem >>
      IMP_RES_TAC Freq_lem >>
      FULL_SIMP_TAC std_ss [Dop_def] >>
      RW_TAC std_ss [cachememTheory.mtfcl_def]
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
     ]
);

(********* cacheless computation **********)

val (cl_kcomp_rules, cl_kcomp_ind, cl_kcomp_cases) = Hol_reln `
   (!s. cl_exentry s ==> cl_kcomp s s 0)
/\ (!s s' s'' n. cl_kcomp s s' n /\ (?req. cl_trans s' PRIV req s'')
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
