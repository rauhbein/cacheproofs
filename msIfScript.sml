(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;
open cachememTheory;

val _ = new_theory "msIf";

(* memory system instantiation: L1 Data and Instruction cache *)

val _ = Datatype `memsys_state = <| 
    dc  : cache_state;
    ic  : cache_state;
    mem : mem_state 
|>`;

val dw_def = Define `dw ms pa = ms.dc (tag pa)`;
val dhit_def = Define `dhit ms pa = chit_ ms.dc pa`;
val dirty_def = Define `dirty ms pa = cdirty_ ms.dc pa`;
val dcnt_def = Define `dcnt ms pa = ccntw_ ms.dc pa`;
val M_def = Define `M ms pa = ms.mem pa`;

val iw_def = Define `iw ms pa = ms.ic (tag pa)`;
val ihit_def = Define `ihit ms pa = chit_ ms.ic pa`;
val icnt_def = Define `icnt ms pa = ccntw_ ms.ic pa`;

val clean_def = Define `clean ms pa = dirty ms pa ==> (dcnt ms pa = M ms pa)`;

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

val dmvca_hit_oblg = store_thm("dmvca_hit_oblg", ``
!ms pa. dhit ms pa ==> (dmvca ms T pa = dcnt ms pa)
``,
  RW_TAC std_ss [dhit_def, dmvca_def, dcnt_def, MVca_def] 
);

val dmvca_miss_oblg = store_thm("dmvca_miss_oblg", ``
!ms pa. ~dhit ms pa ==> (dmvca ms T pa = M ms pa)
``,
  RW_TAC std_ss [dhit_def, dmvca_def, M_def, MVca_def] 
);

val imv_hit_oblg = store_thm("imv_hit_oblg", ``
!ms pa. ihit ms pa ==> (imv ms T pa = icnt ms pa)
``,
  RW_TAC std_ss [ihit_def, imv_def, icnt_def, MVca_def] 
);

val imv_miss_oblg = store_thm("imv_miss_oblg", ``
!ms pa. ~ihit ms pa ==> (imv ms T pa = M ms pa)
``,
  RW_TAC std_ss [ihit_def, imv_def, M_def, MVca_def] 
);

val dhit_oblg = store_thm("dhit_oblg", ``
!ms ms' pa. (dw ms' pa = dw ms pa) ==> (dhit ms' pa <=> dhit ms pa)
``,
  RW_TAC std_ss [dhit_def, dw_def, chit_lem]
);

val double_not_dhit_oblg = store_thm("double_not_dhit_oblg", ``
!ms ms' pa. (~dhit ms' pa /\ ~dhit ms pa) ==> (dw ms' pa = dw ms pa)
``,
  RW_TAC std_ss [dhit_def, dw_def] >>
  IMP_RES_TAC double_not_chit_lem
);

val dirty_oblg = store_thm("dirty_oblg", ``
!ms ms' pa. (dw ms' pa = dw ms pa) ==> (dirty ms' pa <=> dirty ms pa)
``,
  RW_TAC std_ss [dirty_def, dw_def, cdirty_lem]
);

val not_dhit_not_dirty_oblg = store_thm("not_dhit_not_dirty_oblg", ``
!ms pa. ~dhit ms pa ==> ~dirty ms pa 
``,
  RW_TAC std_ss [dhit_def, dirty_def] >>
  IMP_RES_TAC not_chit_not_cdirty_lem
);

val dcnt_oblg = store_thm("dcnt_oblg", ``
!ms ms' pa. dhit ms pa /\ (dw ms' pa = dw ms pa) ==> (dcnt ms' pa = dcnt ms pa)
``,
  RW_TAC std_ss [dhit_def, dcnt_def, dw_def] >>
  IMP_RES_TAC ccnt_lem >>
  IMP_RES_TAC chit_lem >>
  IMP_RES_TAC ccntw_ccnt_lem 
);

val dirty_hit_oblg = store_thm("dirty_hit_oblg", ``
!ms pa. dirty ms pa ==> dhit ms pa
``,
  RW_TAC std_ss [dirty_def, dhit_def, cdirty_chit_lem]
);
		    
val ihit_oblg = store_thm("ihit_oblg", ``
!ms ms' pa. (iw ms' pa = iw ms pa) ==> (ihit ms' pa <=> ihit ms pa)
``,
  RW_TAC std_ss [ihit_def, iw_def, chit_lem]
);

val double_not_ihit_oblg = store_thm("double_not_ihit_oblg", ``
!ms ms' pa. (~ihit ms' pa /\ ~ihit ms pa) ==> (iw ms' pa = iw ms pa)
``,
  RW_TAC std_ss [ihit_def, iw_def] >>
  IMP_RES_TAC double_not_chit_lem
);

val icnt_oblg = store_thm("icnt_oblg", ``
!ms ms' pa. ihit ms pa /\ (iw ms' pa = iw ms pa) ==> (icnt ms' pa = icnt ms pa)
``,
  RW_TAC std_ss [ihit_def, icnt_def, iw_def] >>
  IMP_RES_TAC ccnt_lem >>
  IMP_RES_TAC chit_lem >>
  IMP_RES_TAC ccntw_ccnt_lem 
);

val clean_oblg = store_thm("clean_oblg", ``
!ms ms' pa. (dw ms' pa = dw ms pa) /\ (M ms' pa = M ms pa) ==> 
	(clean ms' pa <=> clean ms pa)
``,
  RW_TAC std_ss [clean_def] >>
  EQ_TAC >> (
      RW_TAC std_ss [] >>
      IMP_RES_TAC dirty_oblg >>
      IMP_RES_TAC dirty_hit_oblg >>
      IMP_RES_TAC dcnt_oblg >>
      RES_TAC >>
      RW_TAC std_ss []
  )
);

val clean_dirty_oblg = store_thm("clean_dirty_oblg", ``
!ms pa. clean ms pa /\ dirty ms pa ==> (dcnt ms pa = M ms pa)
``,
  RW_TAC std_ss [clean_def]
);

val clean_not_dirty_oblg = store_thm("clean_not_dirty_oblg", ``
!ms pa. ~dirty ms pa ==> clean ms pa
``,
  RW_TAC std_ss [clean_def]
);

val clean_equal_oblg = store_thm("clean_equal_oblg", ``
!ms pa. (dcnt ms pa = M ms pa) ==> clean ms pa
``,
  RW_TAC std_ss [clean_def]
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
/\ (msca_trans ms (ICFR pa) = ms_iupd ms (mtfca (ms.ic, ms.mem) (CL pa)))
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

val msca_ICFR_lem = store_thm("msca_ICFR_lem", ``
!ms pa ms'. (ms' = msca_trans ms (ICFR pa)) 
    ==>
?ca' m' dop. ((ca',m') = mtfca (ms.ic, ms.mem) dop) 
          /\ CA dop /\ cl dop /\ (pa = PA dop)
	  /\ (ms'.dc = ms.dc)
          /\ (ms'.ic = ca')
	  /\ (ms'.mem = ms.mem)
``,
  REWRITE_TAC [msca_trans_def] >> 
  REPEAT STRIP_TAC >>
  `?ca' m'. (ca',m') = mtfca (ms.ic, ms.mem) (CL pa)` by (
      METIS_TAC [pairTheory.pair_CASES]
  ) >>
  EXISTS_TAC ``ca':cache_state`` >>
  EXISTS_TAC ``m':mem_state`` >>
  EXISTS_TAC ``CL pa`` >>
  ASM_SYM_TAC mtf_pat >>
  ASM_REWRITE_TAC [ms_iupd_rw, CA_def, cl_def, PA_def]
);

val msca_NOREQ_lem = store_thm("msca_NOREQ_lem", ``
!ms ms'. (ms' = msca_trans ms NOREQ) 
    ==>
    (ms'.dc = ms.dc)
 /\ (ms'.ic = ms.ic)
 /\ (ms'.mem = ms.mem)
``,
  RW_TAC std_ss [msca_trans_def]
);

(* some obligations *)

val msca_DREQ_unchanged_oblg = store_thm("msca_DREQ_unchanged_oblg", ``
!ms dop ms'. (ms' = msca_trans ms (DREQ dop)) 
    ==>
(!pa. iw ms' pa = iw ms pa)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  RW_TAC std_ss [iw_def]
);

val msca_FREQ_unchanged_oblg = store_thm("msca_FREQ_unchanged_oblg", ``
!ms pa ms'. (ms' = msca_trans ms (FREQ pa)) 
    ==>
!pa. (dw ms' pa = dw ms pa) /\ (M ms' pa = M ms pa)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  GEN_TAC >>
  IMP_RES_TAC msca_FREQ_lem >>
  RW_TAC std_ss [dw_def, M_def]
);

val msca_ICFR_unchanged_oblg = store_thm("msca_ICFR_unchanged_oblg", ``
!ms pa ms'. (ms' = msca_trans ms (ICFR pa)) 
    ==>
!pa. (dw ms' pa = dw ms pa) /\ (M ms' pa = M ms pa)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  GEN_TAC >>
  IMP_RES_TAC msca_ICFR_lem >>
  RW_TAC std_ss [dw_def, M_def]
);

val msca_write_val_oblg = store_thm("msca_write_val_oblg", ``
!ms dop ms'. (ms' = msca_trans ms (DREQ dop)) /\ wt dop /\ CA dop 
    ==>
    (dmvca ms' T (PA dop) = VAL dop)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  `~rd dop /\ ~cl dop` by ( METIS_TAC [not_wt_lem] ) >>
  IMP_RES_TAC ca_cacheable_ca >>
  PAT_X_ASSUM ``!pa. x`` (
      fn thm => ASSUME_TAC ( SPEC ``PA dop`` thm )
  ) >>
  REV_FULL_SIMP_TAC std_ss [] >>
  RW_TAC std_ss [dmvca_def, MVca_def]
);


(* deriveability obligations *)

val dc_cacheable_other_oblg = store_thm("dc_cacheable_other_oblg", ``
!ms dop ms' pa. CA dop /\ (ms' = msca_trans ms (DREQ dop)) /\ (pa <> PA dop)
             /\ (dw ms' pa <> dw ms pa) ==> 
    (~dhit ms' pa  /\ (dirty ms pa ==> (M ms' pa = dcnt ms pa))) \/
    (wt dop /\ dhit ms pa /\ dhit ms' pa /\ (dcnt ms' pa = dcnt ms pa)) \/
    (wt dop /\ ~dhit ms pa /\ dhit ms' pa /\ (dcnt ms' pa = M ms pa)) \/
    (rd dop /\ ~dhit ms pa /\ dhit ms' pa /\ ~dirty ms' pa 
            /\ (dcnt ms' pa = M ms pa))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dw_def, dhit_def, dirty_def, dcnt_def, M_def] >>
  IMP_RES_TAC ca_cacheable_other_lem >>
  ASM_REWRITE_TAC []
);

val M_cacheable_other_oblg = store_thm("M_cacheable_other_oblg", ``
!ms dop ms' pa. CA dop /\ (ms' = msca_trans ms (DREQ dop)) /\ (pa <> PA dop)
                  /\ (M ms' pa <> M ms pa) ==>
    dirty ms pa /\ ~dhit ms' pa /\ (M ms' pa = dcnt ms pa)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dirty_def, dcnt_def, dhit_def, M_def] >>
  IMP_RES_TAC mem_cacheable_other_lem >>
  ASM_REWRITE_TAC []
);

val M_cacheable_read_oblg = store_thm("M_cacheable_read_oblg", ``
!ms dop ms'. CA dop /\ rd dop /\ (ms' = msca_trans ms (DREQ dop)) ==>
    (M ms' (PA dop) = M ms (PA dop))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [M_def] >>
  IMP_RES_TAC mem_cacheable_read_lem >>
  RW_TAC std_ss []
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
      RW_TAC std_ss []
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
      RW_TAC std_ss []
  )
);

val dc_cacheable_cl_oblg = store_thm("dc_cacheable_cl_oblg", ``
!ms dop ms'. CA dop /\ cl dop /\ (ms' = msca_trans ms (DREQ dop))
	  /\ (dw ms' (PA dop) <> dw ms (PA dop)) 
        ==>
    ~dhit ms' (PA dop) 
 /\ (dirty ms (PA dop) ==> (M ms' (PA dop) = dcnt ms (PA dop)))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dcnt_def, M_def, dirty_def, dhit_def] >>
  STRIP_TAC
  >| [(* miss *)
      IMP_RES_TAC cacheable_cl_lem
      ,
      (* dirty write back *)
      STRIP_TAC >>
      IMP_RES_TAC mem_cacheable_cl_dirty_lem >>
      RW_TAC std_ss []
     ]
);

val dc_cacheable_cl_miss_oblg = store_thm("dc_cacheable_cl_miss_oblg", ``
!ms dop ms'. cl dop /\ (ms' = msca_trans ms (DREQ dop)) ==> ~dhit ms' (PA dop) 
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC cl_CA_lem >>
  Cases_on `dw ms' (PA dop) = dw ms (PA dop)` 
  >| [(* equal *)
      IMP_RES_TAC msca_DREQ_lem >>
      FULL_SIMP_TAC std_ss [dw_def, dhit_def] >>
      IMP_RES_TAC cacheable_cl_lem
      ,
      (* different *)
      IMP_RES_TAC dc_cacheable_cl_oblg
     ]
);

val M_cacheable_cl_oblg = store_thm("M_cacheable_cl_oblg", ``
!ms dop ms'. CA dop /\ cl dop /\ (ms' = msca_trans ms (DREQ dop))
	  /\ (M ms' (PA dop) <> M ms (PA dop)) 
        ==>
    dirty ms (PA dop) /\ ~dhit ms' (PA dop) 
 /\ (M ms' (PA dop) = dcnt ms (PA dop))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dcnt_def, M_def, dirty_def, dhit_def] >>
  IMP_RES_TAC ca_cacheable_mem >>
  PAT_X_ASSUM ``!pa. X`` (
      fn thm => ASSUME_TAC ( SPEC ``PA dop`` thm )
  ) >>
  IMP_RES_TAC not_wt_lem >>
  FULL_SIMP_TAC std_ss [] >>
  REV_FULL_SIMP_TAC std_ss []
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

val dc_uncacheable_unchanged_oblg = store_thm("dc_uncacheable_unchanged_oblg", ``
!ms dop ms'. ~CA dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (dw ms' = dw ms)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  RW_TAC std_ss [FUN_EQ_THM] >> 
  FULL_SIMP_TAC std_ss [dw_def] >>
  IMP_RES_TAC ca_uncacheable >> 
  ASM_REWRITE_TAC []
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

val M_uncacheable_others_oblg = store_thm("M_uncacheable_others_oblg", ``
!ms dop ms' pa. ~CA dop /\ (pa <> PA dop) /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (M ms' pa = M ms pa)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [M_def] >>
  IMP_RES_TAC ca_uncacheable >> 
  IMP_RES_TAC cl_other_unchanged_lem
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

(* instruction fetch *)

val ic_cacheable_other_oblg = store_thm("ic_cacheable_other_oblg", ``
!ms pa ms' pa'. (ms' = msca_trans ms (FREQ pa')) /\ (pa <> pa')
             /\ (iw ms' pa <> iw ms pa) ==> 
    (~ihit ms' pa \/
     ~ihit ms pa /\ ihit ms' pa /\ (icnt ms' pa = M ms pa))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_FREQ_lem >>
  FULL_SIMP_TAC std_ss [iw_def, ihit_def] >>
  IMP_RES_TAC not_wt_lem >>
  IMP_RES_TAC ca_cacheable_other_lem >> (
      RW_TAC std_ss [icnt_def, M_def]
  )  
);

val ic_cacheable_read_oblg = store_thm("ic_cacheable_read_oblg", ``
!ms pa ms'. (ms' = msca_trans ms (FREQ pa)) /\ (iw ms' pa <> iw ms pa) 
        ==>
    ~ihit ms pa /\ ihit ms' pa /\ (icnt ms' pa = M ms pa)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_FREQ_lem >>
  FULL_SIMP_TAC std_ss [ihit_def, iw_def, icnt_def, M_def] >>
  IMP_RES_TAC ca_cacheable_read_lem >>
  ASM_REWRITE_TAC []
);

(* instruction cache flush *)

val ic_cacheable_cl_other_oblg = store_thm("ic_cacheable_cl_other_oblg", ``
!ms pa ms' pa'. (ms' = msca_trans ms (ICFR pa')) /\ (pa <> pa') ==>
    (iw ms' pa = iw ms pa) \/ ~ihit ms' pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_ICFR_lem >>
  FULL_SIMP_TAC std_ss [iw_def, ihit_def] >>
  Cases_on `tag pa = tag (PA dop)`
  >| [(* same line *)
      IMP_RES_TAC ca_cacheable_cl_lem >>
      METIS_TAC []
      ,
      (* other line *)
      IMP_RES_TAC cacheable_cl_other_lem >>
      RW_TAC std_ss []
     ]
);

val ic_cacheable_cl_oblg = store_thm("ic_cacheable_cl_oblg", ``
!ms pa ms'. (ms' = msca_trans ms (ICFR pa)) /\ (iw ms' pa <> iw ms pa) 
        ==>
    ~ihit ms' pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_ICFR_lem >>
  FULL_SIMP_TAC std_ss [ihit_def, iw_def, icnt_def, M_def] >>
  IMP_RES_TAC ca_cacheable_cl_lem >>
  PAT_X_ASSUM ``!pa. x`` (
      fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm )
  ) >>
  REV_FULL_SIMP_TAC std_ss []
);

(******* Data Coherency **********)

val dcoh_def = Define `dcoh ms pa = coh ms.dc ms.mem pa`;
val dCoh_def = Define `dCoh ms (Rs:padr set) = Coh ms.dc ms.mem Rs`;

val dcoh_oblg = store_thm("dcoh_oblg", ``
!ms ms' pa. dcoh ms pa /\ (dw ms' pa = dw ms pa) 
         /\ (!pa'. (tag pa' = tag pa) ==> (M ms' pa' = M ms pa'))
        ==>
    dcoh ms' pa
``,
  RW_TAC std_ss [dcoh_def, dw_def, M_def] >>
  IMP_RES_TAC coh_lem 
);

val dcoh_tag_oblg = store_thm("dcoh_tag_oblg", ``
!ms pa pa'. dcoh ms pa /\ (tag pa' = tag pa)
        ==>
    dcoh ms pa'
``,
  RW_TAC std_ss [dcoh_def] >>
  IMP_RES_TAC coh_other_lem
);

val dCoh_oblg = store_thm("dCoh_oblg", ``
!ms Rs pa. dCoh ms Rs /\ pa IN Rs ==> dcoh ms pa
``,
  RW_TAC std_ss [dCoh_def, dcoh_def, Coh_def]
);

val dCoh_oblg2 = store_thm("dCoh_oblg2", ``
!ms As. dCoh ms As <=> !pa. pa IN As ==> dcoh ms pa
``,
  RW_TAC std_ss [dCoh_def, dcoh_def, Coh_def]
);

val dCoh_alt_oblg = store_thm("dCoh_alt_oblg", ``
!ms Rs. dCoh ms Rs 
            ==> 
        !pa. pa IN Rs ==> ((dmvca ms) T pa = (dmvalt ms) T pa)
``,
  REWRITE_TAC [dCoh_def, dmvca_def, dmvalt_def, Coh_alt_lem] >>
  RW_TAC std_ss [] >>
  RES_TAC >>
  RW_TAC std_ss []
);

val dcoh_alt_oblg = store_thm("dcoh_alt_oblg", ``
!ms pa. dcoh ms pa ==> ((dmvca ms) T pa = (dmvalt ms) T pa)
``,
  RW_TAC std_ss [dcoh_def, dmvca_def, dmvalt_def] >>
  IMP_RES_TAC coh_alt_lem >>
  RW_TAC std_ss []
);

val dcoh_diff_oblg = store_thm("dcoh_diff_oblg", ``
!ms pa. dcoh ms pa ==> dhit ms pa /\ dcnt ms pa <> M ms pa ==> dirty ms pa
``,
  RW_TAC std_ss [dcoh_def, dw_def, M_def, dhit_def, 
		 dcnt_def, dirty_def, coh_def] >>
  RES_TAC >>
  FULL_SIMP_TAC std_ss []
);

val dcoh_unchanged_oblg = store_thm("dcoh_unchanged_oblg", ``
!ms ms' pa. dcoh ms pa /\ (dw ms' pa = dw ms pa) 
	 /\ (!pa'. (tag pa' = tag pa) ==> (M ms' pa' = M ms pa'))
        ==>
    dcoh ms' pa
``,
  RW_TAC std_ss [dcoh_def, dw_def, M_def] >>
  IMP_RES_TAC coh_lem
);

val dcoh_clean_oblg = store_thm("dcoh_clean_oblg", ``
!ms pa. dcoh ms pa /\ dhit ms pa /\ ~dirty ms pa ==> (M ms pa = dcnt ms pa)
``,
  RW_TAC std_ss [dcoh_def, dhit_def, dirty_def, M_def, dcnt_def] >>
  IMP_RES_TAC coh_clean_lem >>
  ASM_REWRITE_TAC []
);

val dcoh_dirty_oblg = store_thm("dcoh_dirty_oblg", ``
!ms pa. dirty ms pa ==> dcoh ms pa
``,
  RW_TAC std_ss [dirty_def, dcoh_def, coh_dirty_lem]
);

val dcoh_equal_oblg = store_thm("dcoh_equal_oblg", ``
!ms pa. dhit ms pa /\ (!pa'. (tag pa' = tag pa) ==> (dcnt ms pa' = M ms pa')) 
        ==> 
    dcoh ms pa
``,
  RW_TAC std_ss [dcoh_def, dhit_def, dcnt_def, M_def] >>
  IMP_RES_TAC coh_equal_lem
);

val dcoh_miss_oblg = store_thm("dcoh_miss_oblg", ``
!ms pa. ~dhit ms pa ==> dcoh ms pa
``,
  RW_TAC std_ss [dhit_def, dcoh_def, coh_miss_lem]
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

val dcoh_other_oblg = store_thm("dcoh_other_oblg", ``
!ms dop ms' pa. dcoh ms pa /\ (ms' = msca_trans ms (DREQ dop)) 
             /\ tag pa <> tag (PA dop)
        ==>
    dcoh ms' pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dcoh_def] >>
  IMP_RES_TAC coh_trans_other_lem
);

val dcoh_not_write_oblg = store_thm("dcoh_not_write_oblg", ``
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

val dmvca_oblg = store_thm("dmvca_oblg", ``
!ms ms' pa. (dw ms' pa = dw ms pa) /\ (M ms' pa = M ms pa) ==>
    (dmvca ms' T pa = dmvca ms T pa)
``,
  RW_TAC std_ss [dw_def, M_def, dmvca_def] >>
  MATCH_MP_TAC MVca_lem >>
  ASM_REWRITE_TAC []
);

val imv_oblg = store_thm("imv_oblg", ``
!ms ms' pa. (iw ms' pa = iw ms pa) /\ (M ms' pa = M ms pa) ==>
    (imv ms' T pa = imv ms T pa)
``,
  RW_TAC std_ss [iw_def, M_def, imv_def] >>
  MATCH_MP_TAC MVca_lem >>
  ASM_REWRITE_TAC []
);

val dmvalt_oblg = store_thm("dmvalt_oblg", ``
!ms ms' pa. (dw ms' pa = dw ms pa) /\ (M ms' pa = M ms pa) ==>
    (dmvalt ms' T pa = dmvalt ms T pa)
``,
  RW_TAC std_ss [dw_def, M_def, dmvalt_def] >>
  MATCH_MP_TAC MValt_lem >>
  ASM_REWRITE_TAC []
);

val dmvalt_unchanged_oblg = store_thm("dmvalt_unchanged_oblg", ``
!ms dop ms' pa. 
    pa <> PA dop 
 /\ (ms' = msca_trans ms (DREQ dop))
 /\ (wt dop ==> dcoh ms (PA dop))
        ==>
    (dmvalt ms' T pa = dmvalt ms T pa)
``,
  REPEAT STRIP_TAC >> 
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dcoh_def, dmvalt_def] >>
  IMP_RES_TAC mvalt_unchanged_lem
);

val dmvalt_not_write_oblg = store_thm("dmvalt_not_write_oblg", ``
!ms dop ms'. ~wt dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (dmvalt ms' T (PA dop) = dmvalt ms T (PA dop))
``,
  REPEAT STRIP_TAC >> 
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dmvalt_def] >>
  IMP_RES_TAC mvalt_not_write_lem
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
      Cases_on `(msca_trans ms (FREQ (PA dop))).ic (tag (PA dop)) = 
                ms.ic (tag (PA dop))`
      >| [(* cache hit *)
	  METIS_TAC [cdirty_lem]
	  ,
	  (* cache miss *)
	  IMP_RES_TAC ca_cacheable_read_lem
	 ]
      ,
      (* other pa' *)
      Cases_on `ca' (tag pa') = ms.ic (tag pa')` 
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

val Invic_flush_lem = store_thm("Invic_flush_lem", ``
!ms pa ms'. Invic ms /\ (ms' = msca_trans ms (ICFR pa)) 
         ==> 
    Invic ms'
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [Invic_def] >>
  STRIP_TAC >>
  PAT_X_ASSUM ``!pa. X`` ( fn thm => ASSUME_TAC ( SPEC ``pa':padr`` thm ) ) >>
  Cases_on `pa' = pa` 
  >| [(* pa *)
      Cases_on `iw ms' pa = iw ms pa` 
      >| [(* unchanged *)
	  FULL_SIMP_TAC std_ss [iw_def] >>
          IMP_RES_TAC cdirty_lem >>
	  RW_TAC std_ss []
	  ,
	  (* changed *)
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC ic_cacheable_cl_oblg >>
	  FULL_SIMP_TAC std_ss [ihit_def] >> 
	  IMP_RES_TAC not_chit_not_cdirty_lem >>
	  RW_TAC std_ss []
	 ]
      ,
      (* other pa' *)
      `(iw ms' pa' = iw ms pa') \/ ~ihit ms' pa'` by (
          METIS_TAC [ic_cacheable_cl_other_oblg] )
      >| [(* unchanged *)
	  FULL_SIMP_TAC std_ss [iw_def] >>
          IMP_RES_TAC cdirty_lem >>
	  RW_TAC std_ss []
	  ,
	  (* miss *)
	  FULL_SIMP_TAC std_ss [ihit_def] >> 
	  IMP_RES_TAC not_chit_not_cdirty_lem >>
	  RW_TAC std_ss []
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
      (* ICFR *)
      IMP_RES_TAC Invic_flush_lem
      ,
      (* NOREQ *)
      IMP_RES_TAC msca_NOREQ_lem >>
      IMP_RES_TAC Invic_lem
     ]
);

(* Instruction Cache Coherency *)

val icoh_def = Define `icoh ms pa = 
ihit ms pa ==> (icnt ms pa = M ms pa) /\ clean ms pa`;
val iCoh_def = Define `iCoh ms (Rs:padr set) = !pa. pa IN Rs ==> icoh ms pa`;

val iCoh_oblg = store_thm("iCoh_oblg", ``
!ms As pa. iCoh ms As /\ pa IN As ==> icoh ms pa
``,
  RW_TAC std_ss [iCoh_def]
);

val iCoh_oblg2 = store_thm("iCoh_oblg2", ``
!ms As. iCoh ms As <=> !pa. pa IN As ==> icoh ms pa
``,
  RW_TAC std_ss [iCoh_def]
);

val icoh_fetch_lem = store_thm("icoh_fetch_lem", ``
!ms ms' pa. icoh ms pa /\ clean ms pa /\ (ms' = msca_trans ms (FREQ pa))
        ==>
    icoh ms' pa
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC msca_FREQ_lem >>
  Cases_on `ca' (tag pa) = ms.ic (tag pa)`
  >| [(* hit *)
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def] >>
      REPEAT STRIP_TAC 
      >| [(* icoh *)
	  RW_TAC std_ss [] >>
	  IMP_RES_TAC chit_lem >>
	  RES_TAC >>
	  IMP_RES_TAC ccnt_lem >>
	  METIS_TAC [ccntw_ccnt_lem]
	  ,
	  (* not dirty in dc *)
	  `dw ms' (PA dop) = dw ms (PA dop)` by (
	      FULL_SIMP_TAC std_ss [dw_def] 
	  ) >>
	  `M ms' (PA dop) = M ms (PA dop)` by (
	      FULL_SIMP_TAC std_ss [M_def] 
	  ) >>
	  IMP_RES_TAC clean_oblg >>
	  RW_TAC std_ss []
	 ]
      ,
      (* miss *)
      `dw ms' pa = dw ms pa` by (
          FULL_SIMP_TAC std_ss [dw_def] 
      ) >>
      `M ms' pa = M ms pa` by (
          FULL_SIMP_TAC std_ss [M_def] 
      ) >>
      IMP_RES_TAC clean_oblg >>
      RW_TAC std_ss [] >>
      IMP_RES_TAC ca_cacheable_read_lem >>
      FULL_SIMP_TAC std_ss [icoh_def, dirty_def, icnt_def, ihit_def, M_def]
     ]
);

val icoh_fetch_other_lem = store_thm("icoh_fetch_other_lem", ``
!ms ms' pa pa'. icoh ms pa' /\ clean ms pa' 
             /\ (ms' = msca_trans ms (FREQ pa)) /\ pa' <> pa
        ==>
    icoh ms' pa'
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC msca_FREQ_lem >>
  Cases_on `ca' (tag pa') = ms.ic (tag pa')`
  >| [(* hit *)
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def, dirty_def] >>
      STRIP_TAC >>
      IMP_RES_TAC chit_lem >>
      IMP_RES_TAC ccnt_lem >>
      RES_TAC >>
      `dw ms' pa' = dw ms pa'` by (
          FULL_SIMP_TAC std_ss [dw_def] 
      ) >>
      `M ms' pa' = M ms pa'` by (
          FULL_SIMP_TAC std_ss [M_def] 
      ) >>
      IMP_RES_TAC clean_oblg >>
      RW_TAC std_ss [] >>
      METIS_TAC [ccntw_ccnt_lem]
      ,
      (* miss -> eviction or fill *)
      `dw ms' pa' = dw ms pa'` by (
          FULL_SIMP_TAC std_ss [dw_def] 
      ) >>
      `M ms' pa' = M ms pa'` by (
          FULL_SIMP_TAC std_ss [M_def] 
      ) >>
      IMP_RES_TAC clean_oblg >>
      RW_TAC std_ss [] >>
      IMP_RES_TAC not_wt_lem >>
      IMP_RES_TAC ca_cacheable_other_lem >> (
	  FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def, dirty_def]
      )
     ]
);

val icoh_flush_oblg = store_thm("icoh_flush_oblg", ``
!ms ms' pa. (ms' = msca_trans ms (ICFR pa))
        ==>
    icoh ms' pa
``,
  REPEAT STRIP_TAC >>
  Cases_on `ms'.ic (tag pa) = ms.ic (tag pa)`
  >| [(* unchanged -> no hit *)
      IMP_RES_TAC msca_ICFR_lem >>
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def] >>
      STRIP_TAC >>
      `~chit_ ca' (PA dop)` by ( IMP_RES_TAC cacheable_cl_lem )
      ,
      (* miss *)
      IMP_RES_TAC ic_cacheable_cl_oblg >>
      FULL_SIMP_TAC std_ss [icoh_def, iw_def]
     ]
);

val icoh_flush_other_lem = store_thm("icoh_flush_other_lem", ``
!ms ms' pa pa'. icoh ms pa' /\ (ms' = msca_trans ms (ICFR pa)) /\ pa' <> pa
        ==>
    icoh ms' pa'
``,
  REPEAT STRIP_TAC >>
  `(iw ms' pa' = iw ms pa') \/ ~ihit ms' pa'` by ( 
      METIS_TAC [ic_cacheable_cl_other_oblg] )
  >| [(* unchanged *)
      IMP_RES_TAC msca_ICFR_lem >>
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def, 
			    dirty_def, iw_def] >>
      STRIP_TAC >>
      IMP_RES_TAC chit_lem >>
      RES_TAC >>
      IMP_RES_TAC ccnt_lem >>
      `dw ms' pa' = dw ms pa'` by (
          FULL_SIMP_TAC std_ss [dw_def] 
      ) >>
      `M ms' pa' = M ms pa'` by (
          FULL_SIMP_TAC std_ss [M_def] 
      ) >>
      IMP_RES_TAC clean_oblg >>
      RW_TAC std_ss [] >>
      METIS_TAC [ccntw_ccnt_lem]
      ,
      (* flushed *)
      RW_TAC std_ss [icoh_def]
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
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def] >>
      STRIP_TAC >>
      RES_TAC >>
      IMP_RES_TAC ca_cacheable_mem >>
      PAT_X_ASSUM ``!pa. X`` ( fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) ) >>
      STRIP_TAC 
      >| [(* mem = ccnt *)
	  FULL_SIMP_TAC std_ss [] >> (
              FULL_SIMP_TAC std_ss []
	  ) >>
          FULL_SIMP_TAC std_ss [clean_def, dirty_def, dcnt_def, M_def]
	  ,
	  (* clean *)
          Cases_on `ca' (tag pa) = ms.dc (tag pa)`
          >| [(* unchanged *)
	      FULL_SIMP_TAC std_ss [] >> ( FULL_SIMP_TAC std_ss [] )
	      >| [(* mem unchanged *)
      	          `dw ms' pa = dw ms pa` by (
      	              FULL_SIMP_TAC std_ss [dw_def] 
      	          ) >>
      	          `M ms' pa = M ms pa` by (
      	              FULL_SIMP_TAC std_ss [M_def] 
      	          ) >>
      	          IMP_RES_TAC clean_oblg >>
      	          RW_TAC std_ss []
		  ,
		  (* flush *)
		  IMP_RES_TAC cdirty_chit_lem >>
		  IMP_RES_TAC chit_lem >>
		  `dcnt ms' pa = M ms' pa` by (
		      METIS_TAC [ccnt_lem, dcnt_def, M_def, ccntw_ccnt_lem]
		  ) >>
		  IMP_RES_TAC clean_equal_oblg >>
		  RW_TAC std_ss []
		 ]
              ,
              (* changed *)
              Cases_on `pa = PA dop`
              >| [(* PA dop, clean *)
		  FULL_SIMP_TAC std_ss [] >> ( FULL_SIMP_TAC std_ss [] )
		  >| [(* mem unchanged, cache changed *)
		      FULL_SIMP_TAC std_ss [not_wt_lem]
		      >| [(* read *)
			  IMP_RES_TAC ca_cacheable_read_lem >>
			  RW_TAC std_ss [clean_def, dcnt_def, M_def]
			  ,
			  (* clean *)
          		  IMP_RES_TAC ca_cacheable_cl_lem >>
			  PAT_X_ASSUM ``!pa. X`` ( 
			      fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) 
			  ) >>
			  RW_TAC std_ss [clean_def, dcnt_def, M_def] >>
			  FULL_SIMP_TAC std_ss [dirty_def] >>
			  IMP_RES_TAC not_chit_not_cdirty_lem
			 ]
		      ,
		      (* clean, cache changed *)
          	      IMP_RES_TAC ca_cacheable_cl_lem >>
		      PAT_X_ASSUM ``!pa. X`` ( 
		          fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) 
		      ) >>
		      RW_TAC std_ss [clean_def, dcnt_def, M_def] >>
		      FULL_SIMP_TAC std_ss [dirty_def] >>
		      IMP_RES_TAC not_chit_not_cdirty_lem
		     ]
		  ,
		  (* other pa *)
          	  IMP_RES_TAC ca_cacheable_other_lem >>
          	  IMP_RES_TAC not_chit_not_cdirty_lem >>
		  RW_TAC std_ss [clean_def, dcnt_def, M_def, dirty_def]
          	 ]
             ]
	 ]
      ,
      (* uncacheable *)
      IMP_RES_TAC uncacheable_unchanged_lem >>
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def, 
			    dirty_def, clean_def, dcnt_def]
     ]
);

val icoh_write_other_lem = store_thm("icoh_write_other_lem", ``
!ms dop ms' pa. icoh ms pa /\ dcoh ms pa /\ wt dop /\ (pa <> PA dop)
	     /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    icoh ms' pa
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  Cases_on `CA dop`
  >| [(* cacheable *)
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def, clean_def] >>
      STRIP_TAC >>
      RES_TAC >>
      IMP_RES_TAC ca_cacheable_mem >>
      PAT_X_ASSUM ``!pa. X`` ( fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) ) >>
      Cases_on `ca' (tag pa) = ms.dc (tag pa)`
      >| [(* unchanged *)
	  REV_FULL_SIMP_TAC std_ss [dirty_def]
	  >| [(* mem unchanged *)
	      STRIP_TAC >> 
	      IMP_RES_TAC ccnt_lem >>
	      IMP_RES_TAC cdirty_lem >>
	      RES_TAC >>
	      FULL_SIMP_TAC std_ss [dcnt_def] >>
	      IMP_RES_TAC cdirty_chit_lem >>
	      METIS_TAC [ccntw_ccnt_lem]
	      ,
	      (* eviction *)
	      RES_TAC >>
	      IMP_RES_TAC ccnt_lem >>
	      FULL_SIMP_TAC std_ss [dcnt_def] >>
	      STRIP_TAC >>
	      IMP_RES_TAC cdirty_chit_lem >>
	      METIS_TAC [ccntw_ccnt_lem]
	     ] 
	  ,
	  (* changed *)
	  IMP_RES_TAC not_cl_lem >>
	  IMP_RES_TAC not_rd_lem >>
	  REV_FULL_SIMP_TAC std_ss []
	  >| [(* mem unchanged *)
	      STRIP_TAC >>
	      FULL_SIMP_TAC std_ss [dirty_def, dcnt_def] >>
	      IMP_RES_TAC cdirty_chit_lem >>
	      IMP_RES_TAC ca_cacheable_other_lem
	      >| [(* miss -> contradiction *)
		  RW_TAC std_ss [] >>
	          FULL_SIMP_TAC std_ss []
		  ,
		  (* write hit *)
		  Cases_on `cdirty_ ms.dc pa`
		  >| [(* dirty but clean *)
		      RES_TAC >>
		      RW_TAC std_ss []
		      ,
		      (* not dirty -> need coherency *)
		      FULL_SIMP_TAC std_ss [dcoh_def] >>
		      IMP_RES_TAC coh_clean_lem
		     ]
		 ]
	      ,
	      (* dirty eviction *)
	      FULL_SIMP_TAC std_ss [dirty_def, dcnt_def] >>
	      STRIP_TAC >>
	      IMP_RES_TAC ca_cacheable_other_lem >>
	      IMP_RES_TAC not_chit_not_cdirty_lem
	     ]
	 ]
      ,
      (* uncacheable *)
      IMP_RES_TAC ca_uncacheable >>
      IMP_RES_TAC cl_other_unchanged_lem >>
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def, 
			    clean_def, dirty_def, dcnt_def] >>
      RW_TAC std_ss []
     ]
);


val icoh_preserve_oblg = store_thm("icoh_preserve_oblg", ``
!ms req ms' pa. icoh ms pa /\ dcoh ms pa /\ (ms' = msca_trans ms req)
	     /\ (Wreq req ==> (pa <> Adr req))
	     /\ clean ms pa
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
      FULL_SIMP_TAC std_ss [Freq_def] >>
      Cases_on `pa = p`
      >| [(* fetched pa *)
	  FULL_SIMP_TAC std_ss [Adr_def] >>
	  IMP_RES_TAC icoh_fetch_lem >>
	  RW_TAC std_ss []
	  ,
	  (* other address *)
	  IMP_RES_TAC icoh_fetch_other_lem >>
	  RW_TAC std_ss []
	 ]
      ,
      (* ICFR *)
      Cases_on `pa = p`
      >| [(* fetched pa *)
	  FULL_SIMP_TAC std_ss [Adr_def] >>
	  IMP_RES_TAC icoh_flush_oblg >>
	  RW_TAC std_ss []
	  ,
	  (* other address *)
	  IMP_RES_TAC icoh_flush_other_lem
	 ]
      ,
      (* NOREQ *)
      IMP_RES_TAC msca_NOREQ_lem >>
      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def,
			    clean_def, dirty_def, dcnt_def] 
     ]
);

val imv_dmv_oblg = store_thm("imv_dmv_oblg", ``
!ms pa. icoh ms pa /\ dcoh ms pa /\ clean ms pa ==> 
    (imv ms T pa = dmvca ms T pa)
``,
  REPEAT GEN_TAC >>
  Cases_on `dirty ms pa` >> (
      RW_TAC std_ss [icoh_def, ihit_def, icnt_def, imv_def, M_def, dcnt_def,
		     dcoh_def, clean_def, dirty_def, dmvca_def, MVca_def] 
  ) >> 
  FULL_SIMP_TAC std_ss [dirty_def] >>
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
  IMP_RES_TAC Freq_lem >> 
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC msca_FREQ_lem >>
  Cases_on `pa = PA dop`
  >| [(* PA dop *)
      Cases_on `ms'.ic (tag (PA dop)) = ms.ic (tag (PA dop))`
      >| [(* unchanged ic *)
	  RW_TAC std_ss [imv_def] >>
	  MATCH_MP_TAC MVca_lem >>
	  ASM_REWRITE_TAC []
	  ,
	  (* changed ic *)
	  RW_TAC std_ss [] >>
          IMP_RES_TAC ca_cacheable_read_lem >>
	  RW_TAC std_ss [imv_def, MVca_def]
	 ]
      ,
      (* other address *)
      Cases_on `ms'.ic (tag pa) = ms.ic (tag pa)`
      >| [(* unchanged ic *)
	  RW_TAC std_ss [imv_def] >>
	  MATCH_MP_TAC MVca_lem >>
	  ASM_REWRITE_TAC []
	  ,
	  (* changed ic *)
	  RW_TAC std_ss [] >>
	  IMP_RES_TAC not_wt_lem >>
          IMP_RES_TAC ca_cacheable_other_lem
	  >| [(* eviction *)
	      `chit_ ms.ic pa` by (
	          CCONTR_TAC >>
	          IMP_RES_TAC double_not_chit_lem
	      ) >>
	      FULL_SIMP_TAC std_ss [icoh_def, ihit_def, icnt_def, M_def] >>
	      RW_TAC std_ss [imv_def, MVca_def]
	      ,
	      (* read fill *)
	      RW_TAC std_ss [imv_def, MVca_def]
	     ]
	 ]
     ]
);

val imv_flush_oblg = store_thm("imv_flush_oblg", ``
!ms pa ms' req. icoh ms pa /\ Ireq req /\ (ms' = msca_trans ms req)
        ==>
    (imv ms' T pa = imv ms T pa)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Ireq_lem >> 
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC msca_ICFR_lem >>
  Cases_on `pa = PA dop`
  >| [(* PA dop *)
      Cases_on `ms'.ic (tag (PA dop)) = ms.ic (tag (PA dop))`
      >| [(* unchanged ic *)
	  RW_TAC std_ss [imv_def] >>
	  MATCH_MP_TAC MVca_lem >>
	  ASM_REWRITE_TAC []
	  ,
	  (* changed ic -> flushed *)
          IMP_RES_TAC ic_cacheable_cl_oblg >>
	  REV_FULL_SIMP_TAC std_ss [iw_def, icoh_def, ihit_def, 
				    icnt_def, M_def, dirty_def] >>
	  RW_TAC std_ss [imv_def, MVca_def]
	 ]
      ,
      (* other address *)
      FULL_SIMP_TAC std_ss [] >>
      `(iw ms' pa = iw ms pa) \/ ~ihit ms' pa` by (
          METIS_TAC [ic_cacheable_cl_other_oblg] )
      >| [(* unchanged ic *)
	  FULL_SIMP_TAC std_ss [imv_def, iw_def] >>
	  MATCH_MP_TAC MVca_lem >>
	  RW_TAC std_ss []
	  ,
	  (* changed ic -> flushed *)
	  REV_FULL_SIMP_TAC std_ss [iw_def, icoh_def, ihit_def, 
				    icnt_def, M_def, dirty_def] >>
	  RW_TAC std_ss [imv_def, MVca_def]
	 ]
     ]
);

val msca_clean_preserve_oblg = store_thm("msca_clean_preserve_oblg", ``
!ms pa ms' req. Dreq req /\ (ms' = msca_trans ms req)
	     /\ (Wreq req ==> (pa <> Adr req))
	     /\ clean ms pa
	     /\ dcoh ms pa
        ==>
    clean ms' pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC Dreq_lem >> 
  Cases_on `CA dop`
  >| [(* cacheable *)
      Cases_on `pa = PA dop`
      >| [(* PA dop *)
	  Cases_on `dw ms' (PA dop) = dw ms (PA dop)`
	  >| [(* dc unchanged *)
	      Cases_on `M ms' (PA dop) = M ms (PA dop)` 
	      >| [(* mem unchanged *)
		  METIS_TAC [clean_oblg]
		  ,
		  (* mem changed *)
		  Cases_on `cl dop`
		  >| [(* data flush *)
		      FULL_SIMP_TAC std_ss [] >>
		      IMP_RES_TAC M_cacheable_cl_oblg >>
		      IMP_RES_TAC dirty_hit_oblg >>
		      IMP_RES_TAC dcnt_oblg >>
		      MATCH_MP_TAC clean_equal_oblg >>
		      RW_TAC std_ss []
		      ,
		      (* not flush *)
		      FULL_SIMP_TAC std_ss [] >>
		      IMP_RES_TAC M_cacheable_not_cl_oblg >>
		      IMP_RES_TAC clean_equal_oblg >>
		      RW_TAC std_ss []
		     ]
		 ]
	      ,
	      (* dc changed *)
	      ASSUME_TAC ( SPEC ``dop:dop`` dop_cases_lem2 ) >>
	      FULL_SIMP_TAC std_ss []
	      >| [(* read *)
		  IMP_RES_TAC dc_cacheable_read_oblg >>
		  MATCH_MP_TAC clean_not_dirty_oblg >>
		  RW_TAC std_ss []
		  ,
		  (* write *)
		  `Wreq (DREQ dop)` by ( FULL_SIMP_TAC std_ss [Wreq_def] ) >>
		  RES_TAC >>
		  FULL_SIMP_TAC std_ss [Adr_def]
		  ,
		  (* clean *)
		  IMP_RES_TAC dc_cacheable_cl_oblg >>
		  MATCH_MP_TAC clean_not_dirty_oblg >>
	          IMP_RES_TAC not_dhit_not_dirty_oblg >>
		  RW_TAC std_ss []
		 ]
	     ]
	  ,
	  (* other *)
	  Cases_on `dw ms' pa = dw ms pa`
	  >| [(* dc unchanged *)
	      Cases_on `M ms' pa = M ms pa` 
	      >| [(* mem unchanged *)
		  METIS_TAC [clean_oblg]
		  ,
		  (* mem changed *)
		  FULL_SIMP_TAC std_ss [] >>
		  IMP_RES_TAC M_cacheable_other_oblg >>
		  IMP_RES_TAC dirty_hit_oblg >>
		  IMP_RES_TAC dcnt_oblg >>
		  MATCH_MP_TAC clean_equal_oblg >>
		  RW_TAC std_ss []
		 ]
	      ,
	      (* dc changed *)
	      FULL_SIMP_TAC std_ss [] >>
	      Cases_on `dhit ms' pa`
	      >| [(* dirty but clean *)
		  Cases_on `M ms' pa = M ms pa`
		  >| [(* mem unchanged *)
		      FULL_SIMP_TAC std_ss [clean_def] >>
		      Cases_on `dirty ms pa`
		      >| [(* dirty before *)
			  RES_TAC >>
			  STRIP_TAC >>
			  IMP_RES_TAC dirty_hit_oblg >>
			  IMP_RES_TAC dc_cacheable_other_oblg >>
			  RW_TAC std_ss []			  
			  ,
			  (* not dirty before -> use coherency *)
			  STRIP_TAC >>
			  Cases_on `dhit ms pa` 
			  >| [(* write hit *)
			      IMP_RES_TAC dc_cacheable_other_oblg >>
			      IMP_RES_TAC dcoh_clean_oblg >>
			      RW_TAC std_ss []
			      ,
			      (* write fill *)
			      RW_TAC std_ss [] >>
			      METIS_TAC [dc_cacheable_other_oblg]
			     ]			      
			 ]
		      ,
		      (* mem changed *)
		      IMP_RES_TAC M_cacheable_other_oblg >>
		      IMP_RES_TAC dirty_hit_oblg >>
		      IMP_RES_TAC dc_cacheable_other_oblg >>
		      RW_TAC std_ss [clean_def]
		     ]
		  ,
		  (* evicted *)
		  IMP_RES_TAC not_dhit_not_dirty_oblg >>
		  MATCH_MP_TAC clean_not_dirty_oblg >>
		  RW_TAC std_ss []
		 ]
	     ]
	 ]
      ,
      (* not cacheable *)
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC dc_uncacheable_unchanged_oblg >>
      Cases_on `pa = PA dop`
      >| [(* PA dop *)
	  Cases_on `wt dop`
	  >| [(* write -> contradiction *)
	      `Wreq (DREQ dop)` by ( FULL_SIMP_TAC std_ss [Wreq_def] ) >>
	      RES_TAC >>
	      FULL_SIMP_TAC std_ss [Adr_def]
	      ,
	      (* not write *)
	      IMP_RES_TAC M_uncacheable_unchanged_oblg >>
	      METIS_TAC [clean_oblg]
	     ]
	  ,
	  (* other *)
	  IMP_RES_TAC M_uncacheable_others_oblg >>	      
	  METIS_TAC [clean_oblg]
	 ]
     ]
);

val imv_dreq_lem = store_thm("imv_dreq_lem", ``
!ms pa ms' req. icoh ms pa /\ dcoh ms pa /\ Dreq req 
	     /\ (ms' = msca_trans ms req)
	     /\ (Wreq req ==> CAreq req /\ (pa <> Adr req))
	     /\ clean ms pa
        ==>
    (imv ms' T pa = imv ms T pa)
``,
  REPEAT STRIP_TAC >>
  `icoh ms' pa` by ( METIS_TAC [icoh_preserve_oblg] ) >>
  IMP_RES_TAC Dreq_lem >>
  `clean ms' pa` by ( METIS_TAC [msca_clean_preserve_oblg] ) >>
  Cases_on `Wreq req`
  >| [(* write *)
      RES_TAC >>
      FULL_SIMP_TAC std_ss [] >>
      REV_FULL_SIMP_TAC std_ss [Adr_def, CAreq_def, Wreq_def] >>
      `dcoh ms' pa` by (
          Cases_on `tag pa = tag (PA dop)` 
	  >| [(* same line *)
	      IMP_RES_TAC dcoh_write_oblg >>
	      FULL_SIMP_TAC std_ss [dcoh_def] >>
	      IMP_RES_TAC coh_other_lem >>
	      RW_TAC std_ss []
	      ,
	      (* other line *)
	      IMP_RES_TAC dcoh_other_oblg
	     ]
      ) >>
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
      IMP_RES_TAC dcoh_not_write_oblg >>
      REV_FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC imv_dmv_oblg >>
      RW_TAC std_ss []
     ]      
);


val imv_preserve_oblg = store_thm("imv_preserve_oblg", ``
!ms req ms' pa. icoh ms pa /\ dcoh ms pa /\ (ms' = msca_trans ms req)
	     /\ (Wreq req ==> CAreq req /\ (pa <> Adr req))
	     /\ clean ms pa
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
      (* ICFR *)
      IMP_RES_TAC imv_flush_oblg >>
      REV_FULL_SIMP_TAC std_ss []
      ,
      (* DREQ *)
      IMP_RES_TAC imv_dreq_lem >>
      REV_FULL_SIMP_TAC std_ss []
      ,
      (* NOREQ *)
      REWRITE_TAC [msca_trans_def]
     ]
);

(*********** finish ************)

val _ = export_theory();
