(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;
open cachememTheory;

val _ = new_theory "msIf";

(* TODO: 
- ms record type
- accessor functions
- transition function / relation
- lift deriveability lemmas
- IC lemmas / invariant
*)

val _ = Datatype `memsys_state = <| 
    dc  : cache_state;
    ic  : cache_state;
    mem : mem_state 
|>`;

val dw_def = Define `dw ms pa = ms.dc pa`;
val dhit_def = Define `dhit ms pa = chit_ ms.dc pa`;
val dirty_def = Define `dirty ms pa = cdirty_ ms.dc pa`;
val dcnt_def = Define `dcnt ms pa = ccnt_ ms.dc pa`;
val M_def = Define `M ms pa = ms.mem pa`;

val iw_def = Define `iw ms pa = ms.ic pa`;
val ihit_def = Define `ihit ms pa = chit_ ms.ic pa`;
val icnt_def = Define `icnt ms pa = ccnt_ ms.ic pa`;

(* instruction cache invariant *)

val Invic_def = Define `Invic ms = !pa. ~cdirty_ ms.ic pa`;

val Invic_lem = store_thm("Invic_lem", ``
!ms ms'. (ms.ic = ms'.ic) ==> (Invic ms <=> Invic ms')
``,
  RW_TAC std_ss [Invic_def]
);


(* lookup functions / memory views *)

val dmvcl_def = Define `dmvcl ms = MVcl ms.mem`;
val dmvca_def = Define `dmvca ms = MVca ms.dc ms.mem`;
val dmvalt_def = Define `dmvalt ms = MValt ms.dc ms.mem`;
val imv_def = Define `imv ms = MVca ms.ic ms.mem`;

val M_dmvcl_oblg = store_thm("M_dmvcl_oblg", ``
!ms pa c. M ms pa = dmvcl ms c pa
``,
  RW_TAC std_ss [M_def, dmvcl_def, MVcl_def]
);

(* transition system *)

val ms_dupd_def = Define `
ms_dupd ms (ca,m) = ms with <| dc := ca; mem := m |>
`;

val ms_dupd_rw = store_thm("ms_dupd_rw", ``
!ms ca m. ((ms_dupd ms (ca,m)).dc = ca)
       /\ ((ms_dupd ms (ca,m)).ic = ms.ic)
       /\ ((ms_dupd ms (ca,m)).mem = m)
``,
  RW_TAC std_ss [ms_dupd_def]
);

val ms_iupd_def = Define `
ms_iupd ms (ca,m) = ms with <| ic := ca |>
`;

val ms_iupd_rw = store_thm("ms_iupd_rw", ``
!ms ca m. ((ms_iupd ms (ca,m)).dc = ms.dc)
       /\ ((ms_iupd ms (ca,m)).ic = ca)
       /\ ((ms_iupd ms (ca,m)).mem = ms.mem)
``,
  RW_TAC std_ss [ms_iupd_def]
);

val ms_mupd_def = Define `
ms_mupd ms m = ms with <| mem := m |>
`;

val ms_mupd_rw = store_thm("ms_mupd_rw", ``
!ms ca m. ((ms_mupd ms m).dc = ms.dc)
       /\ ((ms_mupd ms m).ic = ms.ic)
       /\ ((ms_mupd ms m).mem = m)
``,
  RW_TAC std_ss [ms_mupd_def]
);

val msca_trans_def = Define `
   (msca_trans ms (DREQ dop) = ms_dupd ms (mtfca (ms.dc, ms.mem) dop))
/\ (msca_trans ms (FREQ pa) = ms_iupd ms (mtfca (ms.ic, ms.mem) (RD pa T)))
/\ (msca_trans ms NOREQ = ms)
`;

val mtf_pat = ``(x,y) = mtfca (a,b) c``; 

val mtf_pat2 = ``mtfca (a,b) c = (x,y)``; 

fun ASM_SYM_TAC pat = PAT_X_ASSUM pat (fn thm => ASSUME_TAC (SYM thm));


val msca_DREQ_lem = store_thm("msca_DREQ_lem", ``
!ms dop ms'. (ms' = msca_trans ms (DREQ dop)) 
    ==>
?ca' m'. ((ca',m') = mtfca (ms.dc, ms.mem) dop) 
      /\ (ms'.dc = ca')
      /\ (ms'.ic = ms.ic)
      /\ (ms'.mem = m')
``,
  REWRITE_TAC [msca_trans_def] >> 
  REPEAT STRIP_TAC >>
  `?ca' m'. (ca',m') = mtfca (ms.dc, ms.mem) dop` by (
      METIS_TAC [pairTheory.pair_CASES]
  ) >>
  EXISTS_TAC ``ca':cache_state`` >>
  EXISTS_TAC ``m':mem_state`` >>
  ASM_SYM_TAC mtf_pat >>
  ASM_REWRITE_TAC [ms_dupd_rw]
);

val msca_FREQ_lem = store_thm("msca_FREQ_lem", ``
!ms pa ms'. (ms' = msca_trans ms (FREQ pa)) 
    ==>
?ca' m' dop. ((ca',m') = mtfca (ms.ic, ms.mem) dop) 
          /\ CA dop /\ rd dop /\ (pa = PA dop)
	  /\ (ms'.dc = ms.dc)
          /\ (ms'.ic = ca')
	  /\ (ms'.mem = ms.mem)
``,
  REWRITE_TAC [msca_trans_def] >> 
  REPEAT STRIP_TAC >>
  `?ca' m'. (ca',m') = mtfca (ms.ic, ms.mem) (RD pa T)` by (
      METIS_TAC [pairTheory.pair_CASES]
  ) >>
  EXISTS_TAC ``ca':cache_state`` >>
  EXISTS_TAC ``m':mem_state`` >>
  EXISTS_TAC ``RD pa T`` >>
  ASM_SYM_TAC mtf_pat >>
  ASM_REWRITE_TAC [ms_iupd_rw, CA_def, rd_def, PA_def]
);

val msca_NOREQ_lem = store_thm("msca_NOREQ_lem", ``
!ms pa ms'. (ms' = msca_trans ms NOREQ) 
    ==>
    (ms'.dc = ms.dc)
 /\ (ms'.ic = ms.ic)
 /\ (ms'.mem = ms.mem)
``,
  RW_TAC std_ss [msca_trans_def]
);


(* deriveability obligations *)

val dc_cacheable_other_oblg = store_thm("dc_cacheable_other_oblg", ``
!ms dop ms' pa. CA dop /\ (ms' = msca_trans ms (DREQ dop)) /\ (pa <> PA dop)
             /\ (dw ms' pa <> dw ms pa) ==> 
    ~dhit ms' pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dw_def, dhit_def] >>
  IMP_RES_TAC ca_cacheable_other_lem
);

val M_cacheable_other_oblg = store_thm("M_cacheable_other_oblg", ``
!ms dop ms' pa. CA dop /\ (ms' = msca_trans ms (DREQ dop)) /\ (pa <> PA dop)
                  /\ (M ms' pa <> M ms pa) ==>
    dirty ms pa /\ (M ms' pa = dcnt ms pa)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dirty_def, dcnt_def, M_def] >>
  IMP_RES_TAC mem_cacheable_other_lem >>
  ASM_REWRITE_TAC []
);

val M_cacheable_read_oblg = store_thm("mem_cacheable_read_oblg", ``
!ms dop ms'. CA dop /\ rd dop /\ (ms' = msca_trans ms (DREQ dop)) ==>
    (M ms' (PA dop) = M ms (PA dop))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [M_def] >>
  IMP_RES_TAC mem_cacheable_read_lem
);

val dc_cacheable_read_oblg = store_thm("dc_cacheable_read_oblg", ``
!ms dop ms'. CA dop /\ rd dop /\ (ms' = msca_trans ms (DREQ dop))
	  /\ (dw ms' (PA dop) <> dw ms (PA dop)) 
        ==>
    dhit ms' (PA dop) 
 /\ ~dirty ms' (PA dop)
 /\ (dcnt ms' (PA dop) = M ms (PA dop))
 /\ ~dhit ms (PA dop)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dhit_def, dirty_def, dw_def, dcnt_def, M_def] >>
  IMP_RES_TAC ca_cacheable_read_lem >>
  ASM_REWRITE_TAC []
);

val dc_cacheable_write_oblg = store_thm("dc_cacheable_write_oblg", ``
!ms dop ms'. CA dop /\ wt dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (dirty ms' (PA dop) 
(* WT case *)
  \/ ~dirty ms' (PA dop) /\ (dcnt ms' (PA dop) = M ms' (PA dop)))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dirty_def, dcnt_def, M_def] >>
  IMP_RES_TAC ca_cacheable_write_lem >> (
      ASM_REWRITE_TAC []
  )
);

val M_cacheable_not_cl_oblg = store_thm("M_cacheable_not_cl_oblg", ``
!ms dop ms'. CA dop /\ ~cl dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    ((M ms' (PA dop) = M ms (PA dop)) \/ (dcnt ms' (PA dop) = M ms' (PA dop)))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dcnt_def, M_def] >>
  IMP_RES_TAC mem_cacheable_not_cl_lem >> (
      ASM_REWRITE_TAC []
  )
);

(* uncacheable accesses *)

val ms_uncacheable_unchanged_oblg = store_thm("ms_uncacheable_unchanged_oblg", ``
!ms dop ms'. ~CA dop /\ ~wt dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (dw ms' = dw ms) /\ (M ms' = M ms)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  RW_TAC std_ss [FUN_EQ_THM] >> (
      FULL_SIMP_TAC std_ss [dw_def, M_def] >>
      IMP_RES_TAC uncacheable_unchanged_lem >> 
      ASM_REWRITE_TAC []
  )
);

val M_uncacheable_unchanged_oblg = store_thm("M_uncacheable_unchanged_oblg", ``
!ms dop ms'. ~CA dop /\ ~wt dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (M ms' (PA dop) = M ms (PA dop))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [M_def] >>
  IMP_RES_TAC mem_uncacheable_unchanged_lem
);

val M_uncacheable_write_oblg = store_thm("M_uncacheable_write_oblg", ``
!ms dop ms'. wt dop /\ (ms' = msca_trans ms (DREQ dop))
	  /\ (M ms' (PA dop) <> M ms (PA dop))
        ==>
    (~CA dop \/ (dcnt ms' (PA dop) = M ms' (PA dop)))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dcnt_def, M_def] >>
  IMP_RES_TAC mem_uncacheable_write_lem >> (
      ASM_REWRITE_TAC []
  )
);

(* Data Coherency *)

val dcoh_def = Define `dcoh ms pa = coh ms.dc ms.mem pa`;
val dCoh_def = Define `dCoh ms (Rs:padr set) = Coh ms.dc ms.mem Rs`;

val dCoh_alt_oblg = store_thm("dCoh_alt_oblg", ``
!ms Rs. dCoh ms Rs 
            <=> 
        !pa. pa IN Rs ==> ((dmvca ms) T pa = (dmvalt ms) T pa)
``,
  REWRITE_TAC [dCoh_def, dmvca_def, dmvalt_def, Coh_alt_lem]
);

val dcoh_write_oblg = store_thm("dcoh_write_oblg", ``
!ms dop ms'. CA dop /\ wt dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
   dcoh ms' (PA dop)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dcoh_def] >>
  IMP_RES_TAC coh_write_lem
);

val dcoh_ca_trans_oblg = store_thm("dcoh_ca_trans_oblg", ``
!ms dop ms' pa. CA dop /\ dcoh ms pa /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    dcoh ms' pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dcoh_def] >>
  IMP_RES_TAC coh_ca_trans_lem
);

val dcoh_other_lem = store_thm("dcoh_other_lem", ``
!ms dop ms' pa. dcoh ms pa /\ (ms' = msca_trans ms (DREQ dop)) /\ pa <> PA dop
        ==>
    dcoh ms' pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dcoh_def] >>
  IMP_RES_TAC coh_other_lem
);

val dcoh_not_write_lem = store_thm("dcoh_not_write_lem", ``
!ms dop ms' pa. dcoh ms pa /\ ~wt dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    dcoh ms' pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dcoh_def] >>
  IMP_RES_TAC coh_not_write_lem
);


(* cacheable memory view *)

val dmv_unchanged_oblg = store_thm("dmv_unchanged_oblg", ``
!ms dop ms' pa. (~wt dop \/ pa <> PA dop) /\ dcoh ms pa
	     /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (dmvca ms' T pa = dmvca ms T pa)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >> (
      IMP_RES_TAC msca_DREQ_lem >>
      FULL_SIMP_TAC std_ss [dcoh_def, dmvca_def] >>
      IMP_RES_TAC mvca_unchanged_lem 
  )
);

(* instruction cache *)

val Invic_fetch_lem = store_thm("Invic_fetch_lem", ``
!ms pa ms'. Invic ms /\ (ms' = msca_trans ms (FREQ pa)) 
         ==> 
    Invic ms'
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [Invic_def] >>
  IMP_RES_TAC msca_FREQ_lem >>
  STRIP_TAC >>
  PAT_X_ASSUM ``!pa. X`` ( fn thm => ASSUME_TAC ( SPEC ``pa':padr`` thm ) ) >>
  `~wt dop` by ( METIS_TAC [dop_cases_lem2] ) >>
  Cases_on `pa' = PA dop` 
  >| [(* PA dop *)
      RW_TAC std_ss [] >>
      Cases_on `(msca_trans ms (FREQ (PA dop))).ic (PA dop) = ms.ic (PA dop)`
      >| [(* cache hit *)
	  METIS_TAC [cdirty_lem]
	  ,
	  (* cache miss *)
	  IMP_RES_TAC ca_cacheable_read_lem
	 ]
      ,
      (* other pa' *)
      Cases_on `ca' pa' = ms.ic pa'` 
      >| [(* unchanged *)
	  METIS_TAC [cdirty_lem]
	  ,
	  (* eviction *)
	  RW_TAC std_ss [] >>
	  IMP_RES_TAC ca_cacheable_other_lem >>
	  IMP_RES_TAC not_chit_not_cdirty_lem
	 ]
     ]	  	  
);

val Invic_preserve_oblg = store_thm("Invic_preserve_oblg", ``
!ms req ms'. Invic ms /\ (ms' = msca_trans ms req) ==> Invic ms'
``,
  REPEAT STRIP_TAC >>
  Cases_on `req` 
  >| [(* DREQ *)
      IMP_RES_TAC msca_DREQ_lem >>
      IMP_RES_TAC Invic_lem
      ,
      (* FREQ *)
      IMP_RES_TAC Invic_fetch_lem
      ,
      (* NOREQ *)
      IMP_RES_TAC msca_NOREQ_lem >>
      IMP_RES_TAC Invic_lem
     ]
);

(* Instruction Cache Coherency *)

val icoh_def = Define `icoh ms pa = 
(ihit ms pa ==> (icnt ms pa = M ms pa)) /\ ~dirty ms pa`;
val dCoh_def = Define `iCoh ms (Rs:padr set) = !pa. pa IN Rs ==> icoh ms pa`;

val icoh_lem = store_thm("icoh_lem", ``
!ms pa. Invic ms ==> 
    (icoh ms pa <=> coh ms.ic ms.mem pa /\ ~cdirty_ ms.dc pa)
``,
  RW_TAC std_ss [Invic_def, icoh_def, coh_def, ihit_def, icnt_def, 
		 M_def, dirty_def] >>
  REWRITE_TAC [IMP_DISJ_THM]
);

val icoh_fetch_lem = store_thm("icoh_fetch_lem", ``
!ms req ms' pa. icoh ms pa /\ (ms' = msca_trans ms (FREQ pa))
        ==>
    icoh ms' pa
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC msca_FREQ_lem >>
  Cases_on `ca' pa = ms.ic pa`
  >| [(* hit *)
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def] >>
      STRIP_TAC 
      >| [(* icoh *)
	  RW_TAC std_ss [] >>
	  IMP_RES_TAC chit_lem >>
	  IMP_RES_TAC ccnt_lem >>
	  RW_TAC std_ss []
	  ,
	  (* not dirty in dc *)
	  FULL_SIMP_TAC std_ss [dirty_def] >>
	  RW_TAC std_ss [cdirty_lem]
	 ]
      ,
      (* miss *)
      RW_TAC std_ss [] >>
      IMP_RES_TAC ca_cacheable_read_lem >>
      RW_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def] >>
      FULL_SIMP_TAC std_ss [icoh_def, dirty_def] >>
      RW_TAC std_ss [cdirty_lem]
     ]
);

val icoh_fetch_other_lem = store_thm("icoh_fetch_other_lem", ``
!ms req ms' pa pa'. icoh ms pa' /\ (ms' = msca_trans ms (FREQ pa)) /\ pa' <> pa
        ==>
    icoh ms' pa'
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC msca_FREQ_lem >>
  Cases_on `ca' pa' = ms.ic pa'`
  >| [(* hit *)
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def] >>
      STRIP_TAC 
      >| [(* icoh *)
	  RW_TAC std_ss [] >>
	  IMP_RES_TAC chit_lem >>
	  IMP_RES_TAC ccnt_lem >>
	  RW_TAC std_ss []
	  ,
	  (* not dirty in dc *)
	  FULL_SIMP_TAC std_ss [dirty_def] >>
	  RW_TAC std_ss [cdirty_lem]
	 ]
      ,
      (* miss *)
      RW_TAC std_ss [] >>
      IMP_RES_TAC ca_cacheable_other_lem >>
      RW_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def] >>
      FULL_SIMP_TAC std_ss [icoh_def, dirty_def] >>
      RW_TAC std_ss [cdirty_lem]
     ]
);

val icoh_not_write_lem = store_thm("icoh_not_write_lem", ``
!ms dop ms' pa. icoh ms pa /\ ~wt dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    icoh ms' pa
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  Cases_on `CA dop`
  >| [(* cacheable *)
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def, dirty_def] >>
      IMP_RES_TAC ca_cacheable_mem >>
      PAT_X_ASSUM ``!pa. X`` ( fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) ) >>
      REV_FULL_SIMP_TAC std_ss [] >>
      Cases_on `ca' pa = ms.dc pa`
      >| [(* unchanged *)
	  METIS_TAC [cdirty_lem]
	  ,
	  (* changed *)
	  Cases_on `pa = PA dop`
	  >| [(* PA dop *)
	      FULL_SIMP_TAC std_ss [not_wt_lem]
	      >| [(* read miss *)
		  RW_TAC std_ss [] >>
		  IMP_RES_TAC ca_cacheable_read_lem
		  ,
		  (* clean *)
		  IMP_RES_TAC ca_cacheable_cl_lem >>
	          PAT_X_ASSUM ``!pa. X`` ( 
		      fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) 
		  ) >>
		  REV_FULL_SIMP_TAC std_ss [] >>
		  IMP_RES_TAC not_chit_not_cdirty_lem >>
		  RW_TAC std_ss []
		 ]
	      ,
	      (* other pa *)
	      IMP_RES_TAC ca_cacheable_other_lem >>
	      IMP_RES_TAC not_chit_not_cdirty_lem 
	     ]
	 ]
      ,
      (* uncacheable *)
      IMP_RES_TAC uncacheable_unchanged_lem >>
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def, dirty_def]
     ]
);

val icoh_write_other_lem = store_thm("icoh_write_other_lem", ``
!ms dop ms' pa. icoh ms pa /\ wt dop /\ (pa <> PA dop)
	     /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    icoh ms' pa
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  Cases_on `CA dop`
  >| [(* cacheable *)
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def, dirty_def] >>
      IMP_RES_TAC ca_cacheable_mem >>
      PAT_X_ASSUM ``!pa. X`` ( fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) ) >>
      REV_FULL_SIMP_TAC std_ss [] >>
      Cases_on `ca' pa = ms.dc pa`
      >| [(* unchanged *)
	  METIS_TAC [cdirty_lem]
	  ,
	  (* changed *)
	  IMP_RES_TAC ca_cacheable_other_lem >>
	  IMP_RES_TAC not_chit_not_cdirty_lem 
	 ]
      ,
      (* uncacheable *)
      IMP_RES_TAC ca_uncacheable >>
      IMP_RES_TAC cl_other_unchanged_lem >>
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def, dirty_def] >>
      RW_TAC std_ss []
     ]
);


val icoh_preserve_oblg = store_thm("icoh_preserve_oblg", ``
!ms req ms' pa. icoh ms pa /\ (ms' = msca_trans ms req)
	     /\ (Wreq req ==> (pa <> Adr req))
        ==>
    icoh ms' pa
``,
  REPEAT STRIP_TAC >>
  Cases_on `req`
  >| [(* DREQ *)
      Cases_on `Wreq (DREQ d)`
      >| [(* write *)
	  RES_TAC >>
	  `wt d` by ( FULL_SIMP_TAC std_ss [Wreq_def] ) >>
	  FULL_SIMP_TAC std_ss [Adr_def] >>
	  IMP_RES_TAC icoh_write_other_lem >>
	  RW_TAC std_ss []
	  ,
	  (* not write *)
	  `~wt d` by ( FULL_SIMP_TAC std_ss [Wreq_def] ) >>
	  IMP_RES_TAC icoh_not_write_lem 
	 ]
      ,
      (* FREQ *)
      Cases_on `pa = p`
      >| [(* fetched pa *)
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC icoh_fetch_lem >>
	  RW_TAC std_ss []
	  ,
	  (* other address *)
	  IMP_RES_TAC icoh_fetch_other_lem
	 ]
      ,
      (* NOREQ *)
      IMP_RES_TAC msca_NOREQ_lem >>
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def, dirty_def]
     ]
);

val imv_dmv_oblg = store_thm("imv_dmv_oblg", ``
!ms pa. icoh ms pa /\ dcoh ms pa ==> (imv ms T pa = dmvca ms T pa)
``,
  RW_TAC std_ss [icoh_def, ihit_def, icnt_def, imv_def, M_def,
		 dcoh_def, dirty_def, dmvca_def, MVca_def] >>
  IMP_RES_TAC coh_clean_lem >>
  RW_TAC std_ss []
);

val imv_dmvcl_oblg = store_thm("imv_dmvcl_oblg", ``
!ms pa c. icoh ms pa ==> (imv ms T pa = dmvcl ms c pa)
``,
  RW_TAC std_ss [icoh_def, ihit_def, icnt_def, imv_def, M_def,
		 dirty_def, dmvcl_def, MVcl_def, MVca_def]
);

val imv_fetch_oblg = store_thm("imv_fetch_oblg", ``
!ms pa ms' req. icoh ms pa /\ Freq req /\ (ms' = msca_trans ms req)
        ==>
    (imv ms' T pa = imv ms T pa)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC not_Wreq_lem >>
  IMP_RES_TAC icoh_preserve_oblg >>
  REV_FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Freq_lem >> 
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC msca_FREQ_lem >>
  RW_TAC std_ss [imv_def, MVca_def] >> (
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def, dirty_def]
  )
);

val imv_dreq_oblg = store_thm("imv_dreq_oblg", ``
!ms pa ms' req. icoh ms pa /\ dcoh ms pa /\ Dreq req 
	     /\ (ms' = msca_trans ms req)
	     /\ (Wreq req ==> (pa <> Adr req))
        ==>
    (imv ms' T pa = imv ms T pa)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC icoh_preserve_oblg >>
  IMP_RES_TAC Dreq_lem >>
  Cases_on `Wreq req`
  >| [(* write *)
      RES_TAC >>
      FULL_SIMP_TAC std_ss [] >>
      REV_FULL_SIMP_TAC std_ss [Adr_def] >>
      IMP_RES_TAC dcoh_other_lem >>
      `dmvca ms' T pa = dmvca ms T pa` by (
          IMP_RES_TAC dmv_unchanged_oblg
      ) >>
      REV_FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC imv_dmv_oblg >>
      RW_TAC std_ss []
      ,
      (* read or clean *)
      FULL_SIMP_TAC std_ss [] >>
      REV_FULL_SIMP_TAC std_ss [] >>
      `~wt dop` by ( FULL_SIMP_TAC std_ss [Wreq_def] ) >>
      `dmvca ms' T pa = dmvca ms T pa` by (
          IMP_RES_TAC dmv_unchanged_oblg
      ) >>
      IMP_RES_TAC dcoh_not_write_lem >>
      REV_FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC imv_dmv_oblg >>
      RW_TAC std_ss []
     ]      
);


val imv_preserve_oblg = store_thm("imv_preserve_oblg", ``
!ms req ms' pa. icoh ms pa /\ dcoh ms pa /\ (ms' = msca_trans ms req)
	     /\ (Wreq req ==> (pa <> Adr req))
        ==>
    (imv ms' T pa = imv ms T pa)
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC ( SPEC ``req:corereq`` req_cases_lem ) >>
  FULL_SIMP_TAC std_ss []
  >| [(* FREQ *)
      IMP_RES_TAC imv_fetch_oblg >>
      REV_FULL_SIMP_TAC std_ss []
      ,
      (* DREQ *)
      IMP_RES_TAC imv_dreq_oblg >>
      REV_FULL_SIMP_TAC std_ss []
      ,
      (* NOREQ *)
      REWRITE_TAC [msca_trans_def]
     ]
);

(*********** finish ************)

val _ = export_theory();
