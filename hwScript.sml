(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;
open coreIfTheory;
open msIfTheory;

val _ = new_theory "hw";

(************ importing interface lemmas **********)

val CR_lem = store_thm("CR_lem", ``
!c c' mv mv'. (!r. r IN CR_ (c,mv) ==> (CV c mv r = CV c' mv' r)) ==>
              (CR_ (c,mv) = CR_ (c',mv'))
``,
  REWRITE_TAC [CR_oblg]
);

val Mmu_lem = store_thm("Mmu_lem", ``
!c c' mv mv'. (!r. r IN MD_(c,mv) ==> (CV c mv r = CV c' mv' r)) ==>
	      (!va m ac. Mmu_(c,mv,va,m,ac) = Mmu_(c',mv',va,m,ac))
``,
  REWRITE_TAC [Mmu_oblg]
);

val MD__lem = store_thm("MD_lem", ``
!c c' mv mv'. (!r. r IN MD_(c,mv) ==> (CV c mv r = CV c' mv' r)) ==>
	      (MD_(c,mv) = MD_(c',mv'))
``,
  REWRITE_TAC [MD_oblg]
);

val Mon__mem_lem = store_thm("Mon__mem_lem", ``
!c mv pa m ac.
  (?va ca. Mmu_ (c,mv,va,m,ac) = SOME (pa,ca)) <=> Mon_ (c,mv,MEM pa,m,ac)
``,
  REWRITE_TAC [Mon_mem_oblg]
);

val Mon__reg_lem = store_thm("Mon__reg_lem", ``
!c mv r c' mv' m ac. reg_res r ==> (Mon_ (c,mv,r,m,ac) <=> Mon_ (c',mv',r,m,ac))
``,
  REWRITE_TAC [Mon_reg_oblg]
);

val core_req_user_MD_reg_lem = store_thm("core_req_user_MD_reg_lem", ``
!c mv req r c'. reg_res r /\ r IN MD_ (c,mv) 
	     /\ core_req (c,USER,mv,req,c') ==>
    (CV c mv r = CV c' mv r)
``,
  REWRITE_TAC [core_req_user_MD_reg_oblg]
);

val core_rcv_user_MD_reg_lem = store_thm("core_req_user_MD_reg_lem", ``
!c w mv r c'. reg_res r /\ r IN MD_ (c,mv) 
	   /\ core_rcv (c,USER,w,c') ==>
    (CV c mv r = CV c' mv r)
``,
  REWRITE_TAC [core_rcv_user_MD_reg_oblg]
);

val core_req_mem_req_lem = store_thm("core_req_mem_req_lem", ``
!c M mv req c'. core_req (c,M,mv,req,c') /\ req <> NOREQ ==> 
    Mon_(c,mv,MEM (Adr req),M,Acc req)
``,
  REWRITE_TAC [core_req_mem_req_oblg]
);

val core_req_exentry_lem = store_thm("core_req_exentry_lem", ``
!c mv req c'. core_req (c,USER,mv,req,c') /\ (Mode c' = PRIV) ==> 
    exentry_ c'
``,
  REWRITE_TAC [core_req_exentry_oblg]
);

val core_req_mode_lem = store_thm("core_req_mode_lem", ``
!c mv req c'. core_req (c,USER,mv,req,c') /\ req <> NOREQ ==> 
    Mode c' <> PRIV
``,
  REWRITE_TAC [core_req_mode_oblg]
);

val core_rcv_mode_lem = store_thm("core_rcv_mode_lem", ``
!c M w c'. core_rcv (c,M,w,c') ==> (Mode c' = Mode c)
``,
  REWRITE_TAC [core_rcv_mode_oblg]
);

val core_req_MD_mv_lem = store_thm("core_req_MD_mv_lem", ``
!c M mv mv' req c'. core_req (c,M,mv,req,c') 
		 /\ (!r. r IN MD_ (c,mv) ==> (CV c mv r = CV c mv' r))
        ==> 
    core_req(c,M,mv',req,c')
``,
  REWRITE_TAC [core_req_MD_mv_oblg]
);

val M_dmvcl_lem = store_thm("M_dmvcl_lem", ``
!ms pa c. M ms pa = dmvcl ms c pa
``,
  REWRITE_TAC [M_dmvcl_oblg]
);

val dc_cacheable_other_lem = store_thm("dc_cacheable_other_lem", ``
!ms dop ms' pa. CA dop /\ (ms' = msca_trans ms (DREQ dop)) /\ (pa <> PA dop)
             /\ (dw ms' pa <> dw ms pa) ==> 
    ~dhit ms' pa
``,
  REWRITE_TAC [dc_cacheable_other_oblg]
);

val M_cacheable_other_lem = store_thm("M_cacheable_other_lem", ``
!ms dop ms' pa. CA dop /\ (ms' = msca_trans ms (DREQ dop)) /\ (pa <> PA dop)
                  /\ (M ms' pa <> M ms pa) ==>
    dirty ms pa /\ (M ms' pa = dcnt ms pa)
``,
  REWRITE_TAC [M_cacheable_other_oblg]
);

val M_cacheable_read_lem = store_thm("M_cacheable_read_lem", ``
!ms dop ms'. CA dop /\ rd dop /\ (ms' = msca_trans ms (DREQ dop)) ==>
    (M ms' (PA dop) = M ms (PA dop))
``,
  REWRITE_TAC [M_cacheable_read_oblg]
);

val dc_cacheable_read_lem = store_thm("dc_cacheable_read_lem", ``
!ms dop ms'. CA dop /\ rd dop /\ (ms' = msca_trans ms (DREQ dop))
	  /\ (dw ms' (PA dop) <> dw ms (PA dop)) 
        ==>
    dhit ms' (PA dop) 
 /\ ~dirty ms' (PA dop)
 /\ (dcnt ms' (PA dop) = M ms (PA dop))
 /\ ~dhit ms (PA dop)
``,
  REWRITE_TAC [dc_cacheable_read_oblg]
);

val dc_cacheable_write_lem = store_thm("dc_cacheable_write_lem", ``
!ms dop ms'. CA dop /\ wt dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (dirty ms' (PA dop) 
(* WT case *)
  \/ ~dirty ms' (PA dop) /\ (dcnt ms' (PA dop) = M ms' (PA dop)))
``,
  REWRITE_TAC [dc_cacheable_write_oblg]
);

val M_cacheable_not_cl_lem = store_thm("M_cacheable_not_cl_lem", ``
!ms dop ms'. CA dop /\ ~cl dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    ((M ms' (PA dop) = M ms (PA dop)) \/ (dcnt ms' (PA dop) = M ms' (PA dop)))
``,
  REWRITE_TAC [M_cacheable_not_cl_oblg]
);

(* uncacheable accesses *)

val ms_uncacheable_unchanged_lem = store_thm("ms_uncacheable_unchanged_lem", ``
!ms dop ms'. ~CA dop /\ ~wt dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (dw ms' = dw ms) /\ (M ms' = M ms)
``,
  REWRITE_TAC [ms_uncacheable_unchanged_oblg]
);

val M_uncacheable_unchanged_lem = store_thm("M_uncacheable_unchanged_lem", ``
!ms dop ms'. ~CA dop /\ ~wt dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (M ms' (PA dop) = M ms (PA dop))
``,
  REWRITE_TAC [M_uncacheable_unchanged_oblg]
);

val M_uncacheable_write_lem = store_thm("M_uncacheable_write_lem", ``
!ms dop ms'. wt dop /\ (ms' = msca_trans ms (DREQ dop))
	  /\ (M ms' (PA dop) <> M ms (PA dop))
        ==>
    (~CA dop \/ (dcnt ms' (PA dop) = M ms' (PA dop)))
``,
  REWRITE_TAC [M_uncacheable_write_oblg]
);

val dCoh_alt_lem = store_thm("dCoh_alt_lem", ``
!ms Rs. dCoh ms Rs 
            <=> 
        !pa. pa IN Rs ==> ((dmvca ms) T pa = (dmvalt ms) T pa)
``,
  REWRITE_TAC [dCoh_alt_oblg]
);

val dcoh_write_lem = store_thm("dcoh_write_lem", ``
!ms dop ms'. CA dop /\ wt dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
   dcoh ms' (PA dop)
``,
  REWRITE_TAC [dcoh_write_oblg]
);

val dcoh_ca_trans_lem = store_thm("dcoh_ca_trans_lem", ``
!ms dop ms' pa. CA dop /\ dcoh ms pa /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    dcoh ms' pa
``,
  REWRITE_TAC [dcoh_ca_trans_oblg]
);

val dmv_unchanged_lem = store_thm("dmv_unchanged_lem", ``
!ms dop ms' pa. (~wt dop \/ pa <> PA dop) /\ dcoh ms pa
	     /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (dmvca ms' T pa = dmvca ms T pa)
``,
  REWRITE_TAC [dmv_unchanged_oblg]
);

val Invic_preserve_lem = store_thm("Invic_preserve_lem", ``
!ms req ms'. Invic ms /\ (ms' = msca_trans ms req) ==> Invic ms'
``,
  REWRITE_TAC [Invic_preserve_oblg]
);

val icoh_preserve_lem = store_thm("icoh_preserve_lem", ``
!ms req ms' pa. icoh ms pa /\ (ms' = msca_trans ms req)
	     /\ (Wreq req ==> (pa <> Adr req))
        ==>
    icoh ms' pa
``,
  REWRITE_TAC [icoh_preserve_oblg]
);

val imv_dmv_lem = store_thm("imv_dmv_lem", ``
!ms pa. icoh ms pa /\ dcoh ms pa ==> (imv ms T pa = dmvca ms T pa)
``,
  REWRITE_TAC [imv_dmv_oblg]
);

val imv_dmvcl_lem = store_thm("imv_dmvcl_lem", ``
!ms pa c. icoh ms pa ==> (imv ms T pa = dmvcl ms c pa)
``,
  REWRITE_TAC [imv_dmvcl_oblg]
);

val imv_fetch_lem = store_thm("imv_fetch_lem", ``
!ms pa ms' req. icoh ms pa /\ Freq req /\ (ms' = msca_trans ms req)
        ==>
    (imv ms' T pa = imv ms T pa)
``,
  REWRITE_TAC [imv_fetch_oblg]
);

val imv_preserve_lem = store_thm("imv_preserve_lem", ``
!ms req ms' pa. icoh ms pa /\ dcoh ms pa /\ (ms' = msca_trans ms req)
	     /\ (Wreq req ==> (pa <> Adr req))
        ==>
    (imv ms' T pa = imv ms T pa)
``,
  REWRITE_TAC [imv_preserve_oblg]
);

(******* some derived lemmas *******)

val Mon__lem = store_thm("Mon__lem", ``
!c c' mv mv'. (!r. r IN MD_(c,mv) ==> (CV c mv r = CV c' mv' r)) ==>
	      (!r m ac. Mon_(c,mv,r,m,ac) <=> Mon_(c',mv',r,m,ac))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Mmu_lem >>
  Cases_on `reg_res r`
  >| [(* register resource *)
      METIS_TAC [Mon__reg_lem] 
      ,
      (* memory resource *)
      `?pa. r = MEM pa` by METIS_TAC [res_cases] >>
      RW_TAC std_ss [GSYM Mon__mem_lem]
     ]
);


(******* HW semantics ********)

val _ = Datatype `hw_state = <| 
    cs  : core_state;
    ms  : memsys_state
|>`;

val MD_def = Define `MD s = MD_ (s.cs, dmvca s.ms)`;
val Mon_def = Define `Mon s r m ac = Mon_ (s.cs, dmvca s.ms, r, m, ac)`;
val Cv_def = Define `Cv s r = CV s.cs (dmvca s.ms) r`;
val mode_def = Define `mode s = Mode s.cs`;
val exentry_def = Define `exentry s = exentry_ s.cs`;

val Mon_lem = store_thm("Mon_lem", ``
!s s'. (!r. r IN MD s ==> (Cv s r = Cv s' r)) ==>
       (!r m ac. Mon s r m ac <=> Mon s' r m ac)
``,
  RW_TAC std_ss [MD_def, Mon_def, Cv_def] >>
  RW_TAC std_ss [Mon__lem]
);

val (hw_trans_rules, hw_trans_ind, hw_trans_cases) = Hol_reln `
   (!s M dop cs' s'. 
	rd dop 
     /\ (M = Mode s.cs)
     /\ core_req (s.cs, M, dmvca s.ms, DREQ dop, cs') 
     /\ (s'.ms = msca_trans s.ms (DREQ dop))
     /\ core_rcv (cs', M, dmvca s.ms (CA dop) (PA dop), s'.cs)
    ==>
    hw_trans s M (DREQ dop) s')
/\ (!s M dop s'. 
	~rd dop 
     /\ (M = Mode s.cs)
     /\ core_req (s.cs, M, dmvca s.ms, DREQ dop, s'.cs) 
     /\ (s'.ms = msca_trans s.ms (DREQ dop))
    ==>
    hw_trans s M (DREQ dop) s')
/\ (!s M pa cs' s'. 
        (M = Mode s.cs)
     /\ core_req (s.cs, M, dmvca s.ms, FREQ pa, cs') 
     /\ (s'.ms = msca_trans s.ms (FREQ pa))
     /\ core_rcv (cs', M, imv s.ms T pa, s'.cs)
    ==>
    hw_trans s M (FREQ pa) s')
/\ (!s M s'. 
        (M = Mode s.cs)
     /\ core_req (s.cs, M, dmvca s.ms, NOREQ, s'.cs)
     /\ (s'.ms = s.ms)
    ==>
    hw_trans s M NOREQ s')
`;

(* hw_trans lemmas *)

val hw_trans_mode_not_eq_lem = store_thm("hw_trans_mode_not_eq_lem", ``
!s M req s'. (M <> Mode s.cs) ==> ~hw_trans s M req s' 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC hw_trans_cases
); 

val hw_trans_mode_lem = 
hw_trans_mode_not_eq_lem |> SPEC_ALL 
			 |> CONTRAPOS 
			 |> GEN_ALL 
			 |> SIMP_RULE std_ss [];

val hw_trans_fetch_lem = store_thm("hw_trans_fetch_lem", ``
!s M req s'. Freq req /\ hw_trans s M req s' ==>
?cs'. core_req (s.cs, M, dmvca s.ms, req, cs') 
   /\ (s'.ms = msca_trans s.ms req)
   /\ core_rcv (cs', M, imv s.ms T (Adr req), s'.cs)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Freq_lem >>
  RW_TAC std_ss [Adr_def] >>
  IMP_RES_TAC hw_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct]
  ) >>
  FULL_SIMP_TAC std_ss [corereq_11] >>
  RW_TAC std_ss [] >>
  HINT_EXISTS_TAC >>
  RW_TAC std_ss []
);

val hw_trans_data_lem = store_thm("hw_trans_data_lem", ``
!s M req s'. Dreq req /\ hw_trans s M req s' ==> (s'.ms = msca_trans s.ms req)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Dreq_lem >>
  RW_TAC std_ss [] >>
  IMP_RES_TAC hw_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct]
  )
);

val hw_trans_read_lem = store_thm("hw_trans_read_lem", ``
!s M req s'. Rreq req /\ hw_trans s M req s' ==>
?cs'. core_req (s.cs, M, dmvca s.ms, req, cs') 
   /\ (s'.ms = msca_trans s.ms req)
   /\ core_rcv (cs', M, dmvca s.ms (CAreq req) (Adr req), s'.cs)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rreq_lem >>
  ASM_REWRITE_TAC [CAreq_def, Adr_def] >>
  IMP_RES_TAC hw_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct, corereq_11] >>
      REV_FULL_SIMP_TAC std_ss []
  ) >>
  HINT_EXISTS_TAC >>
  RW_TAC std_ss []
);

val hw_trans_write_lem = store_thm("hw_trans_write_lem", ``
!s M req s'. Wreq req /\ hw_trans s M req s' ==>
    core_req (s.cs, M, dmvca s.ms, req, s'.cs) 
 /\ (s'.ms = msca_trans s.ms req)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC Wreq_lem >>
  ASM_REWRITE_TAC [] >>
  IMP_RES_TAC not_rd_lem >>
  IMP_RES_TAC hw_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct, corereq_11] >>
      REV_FULL_SIMP_TAC std_ss []
  )
);

val hw_trans_clean_lem = store_thm("hw_trans_clean_lem", ``
!s M req s'. Creq req /\ hw_trans s M req s' ==>
    core_req (s.cs, M, dmvca s.ms, req, s'.cs) 
 /\ (s'.ms = msca_trans s.ms req)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC Creq_lem >>
  ASM_REWRITE_TAC [] >>
  IMP_RES_TAC not_rd_lem >>
  IMP_RES_TAC hw_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct, corereq_11] >>
      REV_FULL_SIMP_TAC std_ss []
  )
);

val hw_trans_noreq_lem = store_thm("hw_trans_noreq_lem", ``
!s M s'. hw_trans s M NOREQ s' ==>
    core_req (s.cs, M, dmvca s.ms, NOREQ, s'.cs) /\ (s'.ms = s.ms)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC hw_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct]
  )
);

(* lift core lemmas *)

val hw_trans_mon_lem = store_thm("hw_trans_mon_lem", ``
!s M req s'. req <> NOREQ /\ hw_trans s M req s' ==>
    Mon s (MEM (Adr req)) M (Acc req)
``,
  RW_TAC std_ss [Mon_def] >>
  IMP_RES_TAC not_NOREQ_lem 
  >| [(* Dreq *)
      IMP_RES_TAC Dreq_cases_lem
      >| [(* read *)
	  IMP_RES_TAC hw_trans_read_lem
	  ,
	  (* write *)
	  IMP_RES_TAC hw_trans_write_lem
	  ,
	  (* clean *)
	  IMP_RES_TAC hw_trans_clean_lem 
	 ] >> (
          IMP_RES_TAC core_req_mem_req_lem
      )
      ,
      (* Freq *)
      IMP_RES_TAC hw_trans_fetch_lem >> 
      IMP_RES_TAC core_req_mem_req_lem
     ]
);

val hw_trans_mode_lem = store_thm("hw_trans_mode_lem", ``
!s req s'. req <> NOREQ /\ hw_trans s USER req s' ==>
    (mode s' <> PRIV)
``,
  RW_TAC std_ss [mode_def] >>
  IMP_RES_TAC not_NOREQ_lem 
  >| [(* Dreq *)
      IMP_RES_TAC Dreq_cases_lem
      >| [(* read *)
	  IMP_RES_TAC hw_trans_read_lem
	  ,
	  (* write *)
	  IMP_RES_TAC hw_trans_write_lem
	  ,
	  (* clean *)
	  IMP_RES_TAC hw_trans_clean_lem 
	 ] >> (
          IMP_RES_TAC core_req_mode_lem >>
          IMP_RES_TAC core_rcv_mode_lem >>
          FULL_SIMP_TAC std_ss []
      )
      ,
      (* Freq *)
      IMP_RES_TAC hw_trans_fetch_lem >> 
      IMP_RES_TAC core_req_mode_lem >>
      IMP_RES_TAC core_rcv_mode_lem >>
      FULL_SIMP_TAC std_ss []
     ]
);

val hw_trans_switch_lem = store_thm("hw_trans_switch_lem", ``
!s req s'. hw_trans s USER req s' /\ (mode s' = PRIV) ==> exentry s'
``,
  RW_TAC std_ss [mode_def, exentry_def] >>
  Cases_on `req = NOREQ`
  >| [(* NOREQ *)
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC hw_trans_noreq_lem >>
      IMP_RES_TAC core_req_exentry_lem
      ,
      (* memory request *)
      IMP_RES_TAC hw_trans_mode_lem >> 
      FULL_SIMP_TAC std_ss [mode_def]
     ]
);

(*********** finish ************)

val _ = export_theory();
