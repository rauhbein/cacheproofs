(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

val _ = new_theory "basetypes";

val _ = Parse.type_abbrev("byte", ``:bool[8]``);
val _ = Parse.type_abbrev("word", ``:bool[32]``);

val _ = Datatype `padr = PADR bool[30]`;
val _ = Datatype `vadr = VADR bool[30]`;

val _ = Datatype `mode = PRIV | USER`;

val _ = Datatype `acc = R | W | EX`;

val _ = Parse.type_abbrev("mem_view", ``:bool -> padr -> word``);

val _ = Datatype `dop = RD padr bool | WT padr word bool | CL padr`;

val rd_def = Define `
   (rd (RD pa c) = T)
/\ (rd _ = F)
`;

val wt_def = Define `
   (wt (WT pa w c) = T)
/\ (wt _ = F)
`;

val cl_def = Define `
   (cl (CL pa) = T)
/\ (cl _ = F)
`;

val PA_def = Define `
   (PA (RD pa c) = pa)
/\ (PA (WT pa w c) = pa)
/\ (PA (CL pa) = pa)
`;

val VAL_def = Define `VAL (WT pa w c) = w`;

val CA_def = Define `
   (CA (RD pa c) = c)
/\ (CA (WT pa w c) = c)
/\ (CA (CL pa) = T)
`;

(* some useful lemmas *)

val dop_cases_lem = store_thm("dop_cases_lem", ``
!dop. rd dop \/ wt dop \/ cl dop
``,
  Cases >> ( RW_TAC std_ss [rd_def, wt_def, cl_def] )
);

val dop_cases_lem2 = store_thm("dop_cases_lem2", ``
!dop. rd dop /\ ~wt dop /\ ~cl dop
   \/ ~rd dop /\ wt dop /\ ~cl dop
   \/ ~rd dop /\ ~wt dop /\ cl dop
``,
  Cases >> ( RW_TAC std_ss [rd_def, wt_def, cl_def] )
);

val not_rd_lem = store_thm("not_rd_lem", ``
!dop. ~rd dop <=> (wt dop \/ cl dop)
``,
  Cases >> (
      RW_TAC std_ss [wt_def, rd_def, cl_def]
  )
);

val not_wt_lem = store_thm("not_wt_lem", ``
!dop. ~wt dop <=> (rd dop \/ cl dop)
``,
  Cases >> (
      RW_TAC std_ss [wt_def, rd_def, cl_def]
  )
);

val not_cl_lem = store_thm("not_cl_lem", ``
!dop. ~cl dop <=> (rd dop \/ wt dop)
``,
  Cases >> (
      RW_TAC std_ss [wt_def, rd_def, cl_def]
  )
);

val rd_lem = store_thm("rd_lem", ``
!dop. rd dop <=> ?pa c. dop = RD pa c
``,
  Cases >> (
      METIS_TAC [rd_def]
  )
);

val wt_lem = store_thm("wt_lem", ``
!dop. wt dop <=> ?pa w c. dop = WT pa w c
``,
  Cases >> (
      METIS_TAC [wt_def]
  )
);

val cl_lem = store_thm("cl_lem", ``
!dop. cl dop <=> ?pa. dop = CL pa
``,
  Cases >> (
      METIS_TAC [cl_def]
  )
);

val not_CA_lem = store_thm("not_CA_lem", ``
!dop. ~CA dop <=> (?pa. dop = RD pa F) \/ (?pa w. dop = WT pa w F)
``,
  Cases >> (
      RW_TAC std_ss [CA_def]
  )
);

val CA_lem = store_thm("CA_lem", ``
!dop. CA dop <=> (?pa. dop = RD pa T) \/ (?pa w. dop = WT pa w T) 
			              \/ (?pa. dop = CL pa)
``,
  Cases >> (
      RW_TAC std_ss [CA_def]
  )
);

val cl_CA_lem = store_thm("cl_CA_lem", ``
!dop. cl dop ==> CA dop
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [cl_lem, CA_def]
);

val rd_CA_lem = store_thm("rd_CA_lem", ``
!dop. rd dop /\ CA dop ==> ?pa. dop = RD pa T
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [rd_lem] >>
  EXISTS_TAC ``pa:padr`` >>
  RW_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [CA_def]
);

val wt_CA_lem = store_thm("wt_CA_lem", ``
!dop. wt dop /\ CA dop ==> ?pa v. dop = WT pa v T
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [wt_lem] >>
  EXISTS_TAC ``pa:padr`` >>
  RW_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [CA_def]
);

(* core requests to memory *)

val _ = Datatype `corereq = DREQ dop | FREQ padr | ICFR padr | NOREQ`;

val Adr_def = Define `
   (Adr (DREQ dop) = PA dop)
/\ (Adr (FREQ pa) = pa)
/\ (Adr (ICFR pa) = pa)
`;

val Freq_def = Define `
   (Freq (FREQ pa) = T)
/\ (Freq _ = F)
`;

val Ireq_def = Define `
   (Ireq (ICFR pa) = T)
/\ (Ireq _ = F)
`;

val Dreq_def = Define `
   (Dreq (DREQ dop) = T)
/\ (Dreq _ = F)
`;

val Rreq_def = Define `
   (Rreq (DREQ dop) = rd dop)
/\ (Rreq _ = F)
`;

val Wreq_def = Define `
   (Wreq (DREQ dop) = wt dop)
/\ (Wreq _ = F)
`;

val Creq_def = Define `
   (Creq (DREQ dop) = cl dop)
/\ (Creq _ = F)
`;

val CAreq_def = Define `
   (CAreq (DREQ dop) = CA dop)
/\ (CAreq NOREQ = F)
/\ (CAreq _ = T)
`;

val Acc_def = Define `
   (Acc (DREQ dop) = if wt dop then W else R)
/\ (Acc (FREQ pa) = EX)
/\ (Acc (ICFR pa) = R)
`;

val Dop_def = Define `
   (Dop (DREQ dop) = dop)
/\ (Dop (FREQ pa) = RD pa T)
/\ (Dop (ICFR pa) = CL pa)
`;

val Freq_lem = store_thm("Freq_lem", ``
!req. Freq req ==> ?pa. req = FREQ pa
``,
  Cases >> (
      RW_TAC std_ss [Freq_def]
  )
);

val Ireq_lem = store_thm("Ireq_lem", ``
!req. Ireq req ==> ?pa. req = ICFR pa
``,
  Cases >> (
      RW_TAC std_ss [Ireq_def]
  )
);

val Dreq_lem = store_thm("Dreq_lem", ``
!req. Dreq req ==> ?dop. req = DREQ dop
``,
  Cases >> (
      RW_TAC std_ss [Dreq_def]
  )
);

val Rreq_lem = store_thm("Rreq_lem", ``
!req. Rreq req ==> ?dop. (req = DREQ dop) /\ rd dop
``,
  Cases >> (
      RW_TAC std_ss [Rreq_def, rd_def]
  )
);

val Wreq_lem = store_thm("Wreq_lem", ``
!req. Wreq req ==> ?dop. (req = DREQ dop) /\ wt dop
``,
  Cases >> (
      RW_TAC std_ss [Wreq_def, wt_def]
  )
);

val Creq_lem = store_thm("Creq_lem", ``
!req. Creq req ==> ?dop. (req = DREQ dop) /\ cl dop
``,
  Cases >> (
      RW_TAC std_ss [Creq_def, cl_def]
  )
);

val not_Wreq_lem = store_thm("not_Wreq_lem", ``
!req. (Freq req \/ Ireq req \/ Rreq req \/ Creq req \/ (req = NOREQ)) ==>
    ~Wreq req
``,
  Cases >> (
      RW_TAC std_ss [Freq_def, Ireq_def, Rreq_def, Wreq_def, Creq_def] >>
      METIS_TAC [dop_cases_lem2]
  )
);

val req_cases_lem = store_thm("req_cases_lem", ``
!req. Freq req /\ ~Ireq req /\ ~Dreq req /\ req <> NOREQ
   \/ ~Freq req /\ Ireq req /\ ~Dreq req /\ req <> NOREQ
   \/ ~Freq req /\ ~Ireq req /\ Dreq req /\ req <> NOREQ
   \/ ~Freq req /\ ~Ireq req /\ ~Dreq req /\ (req = NOREQ)
``,
  Cases >> (
      RW_TAC std_ss [Freq_def, Ireq_def, Dreq_def]
  )
);

val Dreq_cases_lem = store_thm("Dreq_cases_lem", ``
!req. Dreq req ==> 
      Rreq req /\ ~Wreq req /\ ~Creq req
   \/ ~Rreq req /\ Wreq req /\ ~Creq req
   \/ ~Rreq req /\ ~Wreq req /\ Creq req
``,
  GEN_TAC >> STRIP_TAC >>
  IMP_RES_TAC Dreq_lem >>
  ASSUME_TAC ( SPEC ``dop:dop`` dop_cases_lem2 ) >>
  RW_TAC std_ss [Rreq_def, Wreq_def, Creq_def]
);

val not_NOREQ_lem = store_thm("not_NOREQ_lem", ``
!req. req <> NOREQ ==> Dreq req \/ Freq req \/ Ireq req
``,
  METIS_TAC [req_cases_lem]
);

(* op list *)

val _ = Datatype `mop = DOP dop | IFL padr`;

val opd_def = Define `
    (opd (DOP dop) = dop)
 /\ (opd (IFL pa) = CL pa)
`;

val adrs_def = Define `adrs dl = set (MAP PA (MAP opd dl))`;

val adrs_lem = store_thm("adrs_lem", ``
!d pa. pa NOTIN adrs [d] ==>  pa <> PA (opd d)
``,
  RW_TAC std_ss [adrs_def] >>
  FULL_SIMP_TAC std_ss [listTheory.MEM_MAP] >>
  FULL_SIMP_TAC std_ss [GSYM IMP_DISJ_THM] >>
  CCONTR_TAC >>
  PAT_X_ASSUM ``!y. x`` (
      fn thm => ASSUME_TAC ( SPEC ``opd d`` thm )
  ) >>
  FULL_SIMP_TAC std_ss [listTheory.MEM] 
);

val adrs_lem2 = store_thm("adrs_lem2", ``
!d pa. pa IN adrs [d] ==>  (pa = PA (opd d))
``,
  RW_TAC std_ss [adrs_def] >>
  FULL_SIMP_TAC std_ss [listTheory.MEM_MAP] >>
  FULL_SIMP_TAC std_ss [listTheory.MEM] 
);

val writes_def = Define `writes dl = set (MAP PA (FILTER wt (MAP opd dl)))`;

val writes_lem = store_thm("writes_lem", ``
!d pa. pa NOTIN writes [d] ==>  ~(wt (opd d) /\ (PA (opd d) = pa))
``,
  RW_TAC std_ss [writes_def] >>
  FULL_SIMP_TAC std_ss [listTheory.MEM_MAP] >>
  FULL_SIMP_TAC std_ss [listTheory.MEM_FILTER] >>
  CCONTR_TAC >>
  FULL_SIMP_TAC std_ss [GSYM IMP_DISJ_THM] >>
  PAT_X_ASSUM ``!y. x`` (
      fn thm => ASSUME_TAC ( SPEC ``opd d`` thm )
  ) >>
  REV_FULL_SIMP_TAC std_ss [listTheory.MEM, listTheory.MEM_MAP] 
);

val writes_lem2 = store_thm("writes_lem2", ``
!d pa. pa IN writes [d] ==>  wt (opd d) /\ (PA (opd d) = pa)
``,
  RW_TAC std_ss [writes_def] >> (
      FULL_SIMP_TAC std_ss [listTheory.MEM_MAP,
			    listTheory.MEM_FILTER,
			    listTheory.MEM]
  )
);

val reads_def = Define `reads dl = set (MAP PA (FILTER rd (MAP opd dl)))`;

val reads_lem = store_thm("reads_lem", ``
!d pa. pa IN reads [d] ==>  rd (opd d) /\ (PA (opd d) = pa)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  FULL_SIMP_TAC std_ss [reads_def] >>
  FULL_SIMP_TAC std_ss [listTheory.MEM_MAP] >>
  FULL_SIMP_TAC std_ss [listTheory.MEM_FILTER] >>
  FULL_SIMP_TAC std_ss [listTheory.MEM_MAP] >>
  IMP_RES_TAC rd_lem >>
  FULL_SIMP_TAC std_ss [listTheory.MEM] 
);

val adrs_writes_lem = store_thm("adrs_writes_lem", ``
!pa dl. pa IN writes dl ==> pa IN adrs dl
``,
  RW_TAC std_ss [adrs_def, writes_def, listTheory.MEM_MAP] >>
  FULL_SIMP_TAC std_ss [listTheory.MEM_FILTER] >>
  FULL_SIMP_TAC std_ss [listTheory.MEM_MAP] >>
  EXISTS_TAC ``y:dop`` >> 
  ASM_REWRITE_TAC [] >>
  HINT_EXISTS_TAC  >>
  ASM_REWRITE_TAC [] 
);

val not_adrs_not_writes_lem = save_thm("not_adrs_not_writes_lem", 
adrs_writes_lem |> SPEC_ALL |> CONTRAPOS |> GEN_ALL)
;

val dops_def = Define `dops dl = set dl`;

val ifl_def = Define `
    (ifl (IFL pa) = T)
 /\ (ifl _ = F)
`;

val ifl_lem = store_thm("ifl_lem", ``
!d. ifl d ==> ?pa. d = IFL pa
``,
  Cases_on `d` >> (
      RW_TAC std_ss [ifl_def]
  )
);

val not_ifl_lem = store_thm("not_ifl_lem", ``
!d. ~ifl d ==> ?dop. d = DOP dop
``,
  Cases_on `d` >> (
      RW_TAC std_ss [ifl_def]
  )
);

val cleans_def = Define `cleans dl = 
    set (MAP PA (FILTER cl (MAP opd dl)))
`;
val icleans_def = Define `icleans dl = 
    set (MAP PA (MAP opd ((FILTER ifl dl))))
`;
val dcleans_def = Define `dcleans dl = 
    set (MAP PA (FILTER cl (MAP opd (FILTER ($~ o ifl) dl))))
`;

val icleans_lem = store_thm("icleans_lem", ``
!d pa. pa IN icleans [d] ==>  ifl d /\ cl (opd d) /\ (PA (opd d) = pa)
``,
  REWRITE_TAC [icleans_def] >>
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  FULL_SIMP_TAC std_ss [listTheory.MEM_MAP] >>
  FULL_SIMP_TAC std_ss [listTheory.MEM_FILTER] >>
  REV_FULL_SIMP_TAC std_ss [listTheory.MEM] >>
  IMP_RES_TAC ifl_lem >>
  METIS_TAC [cl_def, opd_def]
);

val dcleans_lem = store_thm("dcleans_lem", ``
!d pa. pa IN dcleans [d] ==>  ~ifl d /\ cl (opd d) /\ (PA (opd d) = pa)
``,
  REWRITE_TAC [dcleans_def] >>
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  FULL_SIMP_TAC std_ss [listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  REV_FULL_SIMP_TAC std_ss [listTheory.MEM] >>
  IMP_RES_TAC not_ifl_lem >>
  METIS_TAC [cl_def, opd_def]
);

val not_writes_lem = store_thm("not_writes_lem", ``
!dl pa. pa IN adrs dl /\ pa NOTIN writes dl ==> 
    (pa IN reads dl \/ pa IN cleans dl) 
``,
  RW_TAC std_ss [adrs_def, writes_def, reads_def, cleans_def, 
		 listTheory.MEM_MAP] >>
  Cases_on `y'`
  >| [(* DOP *)
      Cases_on `d`
      >| [(* read *)
          DISJ1_TAC >>
          EXISTS_TAC ``RD p b`` >>
          RW_TAC std_ss [listTheory.MEM_FILTER, rd_def, opd_def,
			 listTheory.MEM_MAP] >>
	  HINT_EXISTS_TAC >>
	  ASM_REWRITE_TAC [opd_def]
          ,
          (* write *)
          PAT_X_ASSUM ``!y. x`` (
              fn thm => ASSUME_TAC ( SPEC ``WT p c b`` thm )
          ) >>
          FULL_SIMP_TAC std_ss [listTheory.MEM_FILTER, wt_def, opd_def] >>
	  FULL_SIMP_TAC std_ss [listTheory.MEM_MAP] >>
          PAT_X_ASSUM ``!y. x`` (
              fn thm => ASSUME_TAC ( SPEC ``DOP (WT p c b)`` thm )
          ) >>
	  FULL_SIMP_TAC std_ss [opd_def]
          ,
          (* clean *)
          DISJ2_TAC >>
          EXISTS_TAC ``CL p`` >>
          RW_TAC std_ss [listTheory.MEM_FILTER, cl_def, opd_def,
			 listTheory.MEM_MAP] >>
	  HINT_EXISTS_TAC >>
	  ASM_REWRITE_TAC [opd_def]
         ]
      ,
      (* IFL *)
      FULL_SIMP_TAC std_ss [opd_def] >>
      DISJ2_TAC >>
      EXISTS_TAC ``CL p``>>
      ASM_REWRITE_TAC [listTheory.MEM_FILTER] >>
      ASM_REWRITE_TAC [cl_def, listTheory.MEM_MAP] >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC [opd_def]
     ]
);

val dclnw_def = Define `
    (dclnw c (DOP d) = if cl d then (c UNION {PA d})
		       else if wt d then (c DIFF {PA d})
		       else c)
 /\ (dclnw c (IFL a) = c)
`;

val dclnw_subset_lem = store_thm("dclnw_subset_lem", ``
!dl A B. A SUBSET B ==> FOLDL dclnw A dl SUBSET FOLDL dclnw B dl
``,
  Induct_on `dl`
  >| [(* [] *)
      RW_TAC list_ss [pred_setTheory.EMPTY_SUBSET]
      ,
      (* h::dl *)
      Cases_on `h`
      >| [(* DOP *)
	  RW_TAC list_ss [dclnw_def] 
	  >| [(* cl /\ wt -> not possible *)
	      METIS_TAC [dop_cases_lem2]
	      ,
	      (* cl *)
	      `A UNION {PA d} SUBSET B UNION {PA d}` by (
	          FULL_SIMP_TAC std_ss [pred_setTheory.UNION_SUBSET,
				        pred_setTheory.SUBSET_UNION] >>
	          FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF,
				        pred_setTheory.IN_UNION]		  
	      ) >>
	      RES_TAC
	      ,
	      (* wt *)
	      `A DIFF {PA d} SUBSET B DIFF {PA d}` by (
	          FULL_SIMP_TAC std_ss [pred_setTheory.DIFF_SUBSET] >>
	          FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF,
				        pred_setTheory.IN_DIFF]		  
	      ) >>
	      RES_TAC
	     ]
	  ,
	  (* IFL *)
	  RW_TAC list_ss [dclnw_def]
	 ]
     ]	      
);


val UNION_DIFF_lem = store_thm("UNION_DIFF_lem", ``
!A B C. (A UNION B) DIFF C = A DIFF C UNION (B DIFF C)
``,
  RW_TAC std_ss [pred_setTheory.EXTENSION,
		 pred_setTheory.IN_DIFF,
		 pred_setTheory.IN_UNION] >>
  METIS_TAC []
);


val dclnw_union_lem = store_thm("dclnw_union_lem", ``
!dl A B a. a IN FOLDL dclnw (A UNION B) dl ==> 
    a IN FOLDL dclnw B dl UNION A
``,
  Induct_on `dl`
  >| [(* [] *)
      RW_TAC list_ss [] >> (
          RW_TAC std_ss []
      )
      ,
      (* h::dl *)
      Cases_on `h`
      >| [(* DOP *)
	  RW_TAC list_ss [dclnw_def] 
	  >| [(* cl /\ wt -> not possible *)
	      METIS_TAC [dop_cases_lem2]
	      ,
	      (* cl *)
	      `a IN FOLDL dclnw (A UNION (B UNION {PA d})) dl` by (
	          RW_TAC std_ss [pred_setTheory.UNION_ASSOC]
	      ) >>
	      RES_TAC >> 
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]		  
	      ,
	      (* wt *)
	      FULL_SIMP_TAC std_ss [UNION_DIFF_lem] >>
	      RES_TAC >>
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION, 
				    pred_setTheory.IN_DIFF]		  
	      ,
	      (* neither *)
	      RES_TAC >>
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]		  
	     ]
	  ,
	  (* IFL *)
	  RW_TAC list_ss [dclnw_def] >>
	  RES_TAC >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]		  
	 ]
     ]	      
);

val dclnws_def = Define `dclnws dl = FOLDL dclnw EMPTY dl`;

val dclnws_empty_lem = store_thm("dclnws_empty_lem", ``
dclnws [] = EMPTY
``,
  RW_TAC list_ss [dclnws_def]
);

val dclnws_IFL_lem = store_thm("dclnws_IFL_lem", ``
!ds a. 
    (dclnws ((IFL a)::ds) = dclnws ds)
``,
  RW_TAC list_ss [dclnws_def, dclnw_def]
);

val dclnws_subset_lem = store_thm("dclnws_subset_lem", ``
!ds d. dclnws ds SUBSET dclnws (d::ds)
``,
  Cases_on `d` 
  >| [(* DOP *)
      RW_TAC list_ss [dclnws_def, dclnw_def] 
      >| [(* cl *)
	  MATCH_MP_TAC dclnw_subset_lem >>
          REWRITE_TAC [pred_setTheory.UNION_EMPTY, pred_setTheory.EMPTY_SUBSET]
	  ,
	  (* wt *)
	  REWRITE_TAC [pred_setTheory.EMPTY_DIFF, pred_setTheory.SUBSET_REFL]
	  ,
	  (* neither *)
	  REWRITE_TAC [pred_setTheory.SUBSET_REFL]
	 ]
      ,
      (* IFL *)
      RW_TAC list_ss [dclnws_IFL_lem, pred_setTheory.SUBSET_REFL] 
     ]
);


val dclnws_DOP_lem = store_thm("dclnws_DOP_lem", ``
!ds d a. a IN dclnws ((DOP d)::ds) 
             <=> 
         (cl d /\ (a = PA d) /\ a IN FOLDL dclnw {a} ds
	   \/ a IN dclnws ds)
``,
  REPEAT STRIP_TAC >>
  EQ_TAC 
  >| [(* ==> *)
      RW_TAC list_ss [dclnws_def, dclnw_def] 
      >| [(* cl d *)
	  `a IN FOLDL dclnw ({PA d} UNION EMPTY) ds` by (
	      RW_TAC std_ss [pred_setTheory.UNION_COMM]
	  ) >>
	  IMP_RES_TAC dclnw_union_lem >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION,
			        pred_setTheory.IN_SING,
			        pred_setTheory.UNION_EMPTY] >> (
	      RW_TAC std_ss []
	  )
	  ,
	  (* wt d *)
	  FULL_SIMP_TAC std_ss [pred_setTheory.EMPTY_DIFF]
	 ]
      ,
      (* <== *)
      STRIP_TAC 
      >| [(* cl d *)
	  RW_TAC list_ss [dclnws_def, dclnw_def, pred_setTheory.UNION_EMPTY] 
	  ,
	  (* in ds *)
	  FULL_SIMP_TAC list_ss [dclnws_def] >>
	  `EMPTY SUBSET dclnw EMPTY (DOP d)` by (
	      RW_TAC std_ss [pred_setTheory.EMPTY_SUBSET]
	  ) >>
	  IMP_RES_TAC dclnw_subset_lem >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF]
	 ]
     ]
);


(*********** finish ************)

val _ = export_theory();
