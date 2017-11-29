(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;
open coreIfTheory;
open msIfTheory;

val _ = new_theory "hw";

(************ importing interface lemmas **********)

(* core *)

val CV_lem = store_thm("CV_lem", ``
!c c' mv mv' pa. (mv T pa = mv' T pa) ==> 
    (CV c mv (MEM pa) = CV c' mv' (MEM pa))
``,
  REWRITE_TAC [CV_oblg]
);

val vdeps_PC_lem = store_thm("vdeps_PC_lem", ``
!c. VApc c IN vdeps_ c
``,
  REWRITE_TAC [vdeps_PC_oblg]
);

val Mmu_lem = store_thm("Mmu_lem", ``
!c c' mv mv' VAs. (!r. r IN MD_(c,mv,VAs) ==> (CV c mv r = CV c' mv' r)) ==>
	          (!va m ac. va IN VAs ==>
		             (Mmu_(c,mv,va,m,ac) = Mmu_(c',mv',va,m,ac)))
``,
  REWRITE_TAC [Mmu_oblg]
);

val MD__lem = store_thm("MD__lem", ``
!c c' mv mv' VAs. (!r. r IN MD_(c,mv,VAs) ==> (CV c mv r = CV c' mv' r)) ==>
		  (MD_(c,mv,VAs) = MD_(c',mv',VAs))
``,
  REWRITE_TAC [MD_oblg]
);

val MD__reg_lem = store_thm("MD__reg_lem", ``
!c c' mv mv' VAs. (!r. reg_res r ==> 
		       (r IN MD_(c,mv,VAs) <=> r IN MD_(c',mv',VAs))) 
``,
  REWRITE_TAC [MD_reg_oblg]
);

val MD__coreg_lem = store_thm("MD__coreg_lem", ``
!c c' mv mv' r VAs. reg_res r /\ r IN MD_(c,mv,VAs) /\ (c.coreg = c'.coreg) ==> 
    (CV c mv r = CV c' mv' r) 
``,
  REWRITE_TAC [MD_coreg_oblg]
);

val MD__monotonic_lem = store_thm("MD__monotonic_lem", ``
!c mv VAs VAs'. VAs SUBSET VAs' ==> MD_(c,mv,VAs) SUBSET MD_(c,mv,VAs')
``,
  REWRITE_TAC [MD_monotonic_oblg]
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

val Mmu_read_fetch_lem = store_thm("Mmu_read_fetch_lem", ``
!c mv va m pa C. (Mmu_(c,mv,va,m,EX) = SOME (pa,C)) ==>
                 (Mmu_(c,mv,va,m,R) = SOME (pa,C))
``,
  REWRITE_TAC [Mmu_read_fetch_oblg]
);

val Mmu_write_read_lem = store_thm("Mmu_write_read_lem", ``
!c mv va m pa C. (Mmu_(c,mv,va,m,W) = SOME (pa,C)) ==>
                 (Mmu_(c,mv,va,m,R) = SOME (pa,C))
``,
  REWRITE_TAC [Mmu_write_read_oblg]
);

val exentry__lem = store_thm("exentry__lem", ``
!c. exentry_ c ==> (Mode c = PRIV)
``,
  REWRITE_TAC [exentry__oblg]
);

val core_req_curr_mode_lem = store_thm("core_req_curr_mode_lem", ``
!c M mv req c'. core_req (c,M,mv,req,c') ==> (Mode c = M)
``,
  REWRITE_TAC [core_req_curr_mode_oblg] 
);

val core_req_mode_change_lem = store_thm("core_req_mode_change_lem", ``
!c M mv req c'. core_req (c,M,mv,req,c') /\ req <> NOREQ ==> (Mode c' = Mode c)
``,
  REWRITE_TAC [core_req_mode_change_oblg]
);

val core_req_user_MD_reg_lem = store_thm("core_req_user_MD_reg_lem", ``
!c mv req r c' VAs. reg_res r /\ r IN MD_ (c,mv,VAs) 
	         /\ core_req (c,USER,mv,req,c') ==>
    (CV c mv r = CV c' mv r)
``,
  REWRITE_TAC [core_req_user_MD_reg_oblg]
);

val core_rcv_user_MD_reg_lem = store_thm("core_rcv_user_MD_reg_lem", ``
!c w mv r c' VAs. reg_res r /\ r IN MD_ (c,mv,VAs) 
	       /\ core_rcv (c,USER,w,c') ==>
    (CV c mv r = CV c' mv r)
``,
  REWRITE_TAC [core_rcv_user_MD_reg_oblg]
);

val core_req_mmu_Freq_lem = store_thm("core_req_mmu_Freq_lem", ``
!c M mv req c'. core_req (c,M,mv,req,c') /\ Freq req ==> 
    (Mmu_(c,mv,VApc c,M,EX) = SOME (Adr req, T))
``,
  REWRITE_TAC [core_req_mmu_Freq_oblg]
);

val core_req_mmu_Ireq_lem = store_thm("core_req_mmu_Ireq_lem", ``
!c M mv req c'. core_req (c,M,mv,req,c') /\ Ireq req ==> 
    ?va. va IN vdeps_ c 
      /\ (Mmu_(c,mv,va,M,R) = SOME (Adr req, T))
``,
  REWRITE_TAC [core_req_mmu_Ireq_oblg]
);

val core_req_mmu_Dreq_lem = store_thm("core_req_mmu_Dreq_lem", ``
!c M mv req c'. core_req (c,M,mv,req,c') /\ Dreq req ==> 
    ?va. va IN vdeps_ c 
      /\ (Mmu_(c,mv,va,M,Acc req) = SOME (Adr req, CAreq req))
``,
  REWRITE_TAC [core_req_mmu_Dreq_oblg]
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
!c mv mv' req c'. 
    (!pa. MEM pa IN MD_(c,mv,vdeps_ c) ==> 
	  (CV c mv (MEM pa) = CV c mv' (MEM pa)))
        ==> 
    (core_req(c,Mode c,mv,req,c') <=> core_req(c,Mode c,mv',req,c'))
``,
  REWRITE_TAC [core_req_MD_mv_oblg]
);

val core_req_user_coreg_lem = store_thm("core_req_user_coreg_lem", ``
!c mv req c'. core_req (c,USER,mv,req,c') ==> (c'.coreg = c.coreg)
``,
  REWRITE_TAC [core_req_user_coreg_oblg]
);

val core_req_det_lem = store_thm("core_req_det_lem", ``
!c m mv req req' c' c''. 
    core_req(c,m,mv,req,c') /\ core_req(c,m,mv,req',c'')
        ==>
    (c' = c'') /\ (req = req')
``,
  REWRITE_TAC [core_req_det_oblg]
);

val core_req_progress_lem = store_thm("core_req_progress_lem", ``
!c mv. ?req c'. core_req(c,Mode c,mv,req,c')
``,
  REWRITE_TAC [core_req_progress_oblg]
);

val core_rcv_user_coreg_lem = store_thm("core_rcv_user_coreg_lem", ``
!c w c'. core_rcv (c,USER,w,c') ==> (c'.coreg = c.coreg)
``,
  REWRITE_TAC [core_rcv_user_coreg_oblg]
);

val core_rcv_det_lem = store_thm("core_rcv_det_lem", ``
!c M w c' c''. core_rcv (c,M,w,c') /\ core_rcv (c,M,w,c'')  ==> (c' = c'')
``,
  REWRITE_TAC [core_rcv_det_oblg]
);

val core_rcv_progress_lem = store_thm("core_rcv_progress_lem", ``
!c w. ?c'. core_rcv (c,Mode c,w,c')
``,
  REWRITE_TAC [core_rcv_progress_oblg]
);

(* memory system *)

val msca_DREQ_unchanged_lem = store_thm("msca_DREQ_unchanged_lem", ``
!ms dop ms'. (ms' = msca_trans ms (DREQ dop)) 
    ==>
(!pa. iw ms' pa = iw ms pa)
``,
  REWRITE_TAC [msca_DREQ_unchanged_oblg]
);

val msca_FREQ_unchanged_lem = store_thm("msca_FREQ_unchanged_lem", ``
!ms pa ms'. (ms' = msca_trans ms (FREQ pa)) 
    ==>
!pa. (dw ms' pa = dw ms pa) /\ (M ms' pa = M ms pa)
``,
  REWRITE_TAC [msca_FREQ_unchanged_oblg]
);

val msca_ICFR_unchanged_lem = store_thm("msca_ICFR_unchanged_lem", ``
!ms pa ms'. (ms' = msca_trans ms (ICFR pa)) 
    ==>
!pa. (dw ms' pa = dw ms pa) /\ (M ms' pa = M ms pa)
``,
  REWRITE_TAC [msca_ICFR_unchanged_oblg]
);

val msca_write_val_lem = store_thm("msca_write_val_lem", ``
!ms dop ms'. (ms' = msca_trans ms (DREQ dop)) /\ wt dop /\ CA dop 
    ==>
    (dmvca ms' T (PA dop) = VAL dop)
``,
  REWRITE_TAC [msca_write_val_oblg]
);

val msca_clean_preserve_lem = store_thm("msca_clean_preserve_lem", ``
!ms pa ms' req. Dreq req /\ (ms' = msca_trans ms req)
	     /\ (Wreq req ==> (pa <> Adr req))
	     /\ clean ms pa
	     /\ dcoh ms pa
        ==>
    clean ms' pa
``,
  REWRITE_TAC [msca_clean_preserve_oblg]
);

val M_dmvcl_lem = store_thm("M_dmvcl_lem", ``
!ms pa c. M ms pa = dmvcl ms c pa
``,
  REWRITE_TAC [M_dmvcl_oblg]
);

val dmvca_hit_lem = store_thm("dmvca_hit_lem", ``
!ms pa. dhit ms pa ==> (dmvca ms T pa = dcnt ms pa)
``,
  REWRITE_TAC [dmvca_hit_oblg] 
);

val dmvca_miss_lem = store_thm("dmvca_miss_lem", ``
!ms pa. ~dhit ms pa ==> (dmvca ms T pa = M ms pa)
``,
  REWRITE_TAC [dmvca_miss_oblg] 
);

val dhit_lem = store_thm("dhit_lem", ``
!ms ms' pa. (dw ms' pa = dw ms pa) ==> (dhit ms' pa <=> dhit ms pa)
``,
  REWRITE_TAC [dhit_oblg]
);

val double_not_dhit_lem = store_thm("double_not_dhit_lem", ``
!ms ms' pa. (~dhit ms' pa /\ ~dhit ms pa) ==> (dw ms' pa = dw ms pa)
``,
  REWRITE_TAC [double_not_dhit_oblg]
);

val dirty_lem = store_thm("dirty_lem", ``
!ms ms' pa. (dw ms' pa = dw ms pa) ==> (dirty ms' pa <=> dirty ms pa)
``,
  REWRITE_TAC [dirty_oblg]
);

val not_dhit_not_dirty_lem = store_thm("not_dhit_not_dirty_lem", ``
!ms pa. ~dhit ms pa ==> ~dirty ms pa 
``,
  REWRITE_TAC [not_dhit_not_dirty_oblg]
);

val dcnt_lem = store_thm("dcnt_lem", ``
!ms ms' pa. (dw ms' pa = dw ms pa) ==> (dcnt ms' pa = dcnt ms pa)
``,
  REWRITE_TAC [dcnt_oblg]
);

val dirty_hit_lem = store_thm("dirty_hit_lem", ``
!ms pa. dirty ms pa ==> dhit ms pa
``,
  REWRITE_TAC [dirty_hit_oblg]
);


val imv_hit_lem = store_thm("imv_hit_lem", ``
!ms pa. ihit ms pa ==> (imv ms T pa = icnt ms pa)
``,
  REWRITE_TAC [imv_hit_oblg]
);

val imv_miss_lem = store_thm("imv_miss_lem", ``
!ms pa. ~ihit ms pa ==> (imv ms T pa = M ms pa)
``,
  REWRITE_TAC [imv_miss_oblg]
);

val ihit_lem = store_thm("ihit_lem", ``
!ms ms' pa. (iw ms' pa = iw ms pa) ==> (ihit ms' pa <=> ihit ms pa)
``,
  REWRITE_TAC [ihit_oblg]
);

val double_not_ihit_lem = store_thm("double_not_ihit_lem", ``
!ms ms' pa. (~ihit ms' pa /\ ~ihit ms pa) ==> (iw ms' pa = iw ms pa)
``,
  REWRITE_TAC [double_not_ihit_oblg]
);

val icnt_lem = store_thm("icnt_lem", ``
!ms ms' pa. (iw ms' pa = iw ms pa) ==> (icnt ms' pa = icnt ms pa)
``,
  REWRITE_TAC [icnt_oblg]
);

val clean_lem = store_thm("clean_lem", ``
!ms ms' pa. (dw ms' pa = dw ms pa) /\ (M ms' pa = M ms pa) ==> 
	(clean ms' pa <=> clean ms pa)
``,
  REWRITE_TAC [clean_oblg] 
);

val clean_dirty_lem = store_thm("clean_dirty_lem", ``
!ms pa. clean ms pa /\ dirty ms pa ==> (dcnt ms pa = M ms pa)
``,
  REWRITE_TAC [clean_dirty_oblg]
);

val clean_not_dirty_lem = store_thm("clean_not_dirty_lem", ``
!ms pa. ~dirty ms pa ==> clean ms pa
``,
  REWRITE_TAC [clean_not_dirty_oblg]
);

val clean_equal_lem = store_thm("clean_equal_lem", ``
!ms pa. (dcnt ms pa = M ms pa) ==> clean ms pa
``,
  REWRITE_TAC [clean_equal_oblg]
);

(* deriveability lemmas *)

val dc_cacheable_other_lem = store_thm("dc_cacheable_other_lem", ``
!ms dop ms' pa. CA dop /\ (ms' = msca_trans ms (DREQ dop)) /\ (pa <> PA dop)
             /\ (dw ms' pa <> dw ms pa) ==> 
    (~dhit ms' pa  /\ (dirty ms pa ==> (M ms' pa = dcnt ms pa))) \/
    (wt dop /\ dhit ms pa /\ ~dirty ms pa /\ dirty ms' pa 
            /\ (dcnt ms' pa = dcnt ms pa)) \/
    (rd dop /\ ~dhit ms pa /\ dhit ms' pa /\ ~dirty ms' pa 
            /\ (dcnt ms' pa = M ms pa))
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

val dc_cacheable_cl_lem = store_thm("dc_cacheable_cl_lem", ``
!ms dop ms'. CA dop /\ cl dop /\ (ms' = msca_trans ms (DREQ dop))
	  /\ (dw ms' (PA dop) <> dw ms (PA dop)) 
        ==>
    ~dhit ms' (PA dop) 
 /\ (dirty ms (PA dop) ==> (M ms' (PA dop) = dcnt ms (PA dop)))
``,
  REWRITE_TAC [dc_cacheable_cl_oblg]
);

val dc_cacheable_cl_miss_lem = store_thm("dc_cacheable_cl_miss_lem", ``
!ms dop ms'. cl dop /\ (ms' = msca_trans ms (DREQ dop)) ==> ~dhit ms' (PA dop) 
``,
  REWRITE_TAC [dc_cacheable_cl_miss_oblg]
);

val M_cacheable_cl_lem = store_thm("M_cacheable_cl_lem", ``
!ms dop ms'. CA dop /\ cl dop /\ (ms' = msca_trans ms (DREQ dop))
	  /\ (M ms' (PA dop) <> M ms (PA dop)) 
        ==>
    dirty ms (PA dop) /\ (M ms' (PA dop) = dcnt ms (PA dop))
``,
  REWRITE_TAC [M_cacheable_cl_oblg]
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

val dc_uncacheable_unchanged_lem = store_thm("dc_uncacheable_unchanged_lem", ``
!ms dop ms'. ~CA dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (dw ms' = dw ms)
``,
  REWRITE_TAC [dc_uncacheable_unchanged_oblg]
);

val M_uncacheable_others_lem = store_thm("M_uncacheable_others_lem", ``
!ms dop ms' pa. ~CA dop /\ (pa <> PA dop) /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (M ms' pa = M ms pa)
``,
  REWRITE_TAC [M_uncacheable_others_oblg]
);

val M_uncacheable_write_lem = store_thm("M_uncacheable_write_lem", ``
!ms dop ms'. wt dop /\ (ms' = msca_trans ms (DREQ dop))
	  /\ (M ms' (PA dop) <> M ms (PA dop))
        ==>
    (~CA dop \/ (dcnt ms' (PA dop) = M ms' (PA dop)))
``,
  REWRITE_TAC [M_uncacheable_write_oblg]
);

(* instruction cache *)

val ic_cacheable_other_lem = store_thm("ic_cacheable_other_lem", ``
!ms pa ms' pa'. (ms' = msca_trans ms (FREQ pa')) /\ (pa <> pa')
             /\ (iw ms' pa <> iw ms pa) ==> 
    (~ihit ms' pa \/
     ~ihit ms pa /\ ihit ms' pa /\ (icnt ms' pa = M ms pa))
``,
  REWRITE_TAC [ic_cacheable_other_oblg]
);

val ic_cacheable_read_lem = store_thm("ic_cacheable_read_lem", ``
!ms pa ms'. (ms' = msca_trans ms (FREQ pa)) /\ (iw ms' pa <> iw ms pa) 
        ==>
    ~ihit ms pa /\ ihit ms' pa /\ (icnt ms' pa = M ms pa)
``,
  REWRITE_TAC [ic_cacheable_read_oblg]
);

(* instruction cache flush *)

val ic_cacheable_cl_other_lem = store_thm("ic_cacheable_cl_other_lem", ``
!ms pa ms' pa'. (ms' = msca_trans ms (ICFR pa')) /\ (pa <> pa') ==>
    (iw ms' pa = iw ms pa) \/ ~ihit ms' pa
``,
  REWRITE_TAC [ic_cacheable_cl_other_oblg]
);

val ic_cacheable_cl_lem = store_thm("ic_cacheable_cl_lem", ``
!ms pa ms'. (ms' = msca_trans ms (ICFR pa)) /\ (iw ms' pa <> iw ms pa) 
        ==>
    ~ihit ms' pa
``,
  REWRITE_TAC [ic_cacheable_cl_oblg]
);

(* Coherency *)

val dcoh_lem = store_thm("dcoh_lem", ``
!ms ms' pa. dcoh ms pa /\ (dw ms' pa = dw ms pa) /\ (M ms' pa = M ms pa)
        ==>
    dcoh ms' pa
``,
  REWRITE_TAC [dcoh_oblg]
);

val dCoh_lem = store_thm("dCoh_lem", ``
!ms As pa. dCoh ms As /\ pa IN As ==> dcoh ms pa
``,
  REWRITE_TAC [dCoh_oblg]
);

val dCoh_lem2 = store_thm("dCoh_lem2", ``
!ms As. dCoh ms As <=> !pa. pa IN As ==> dcoh ms pa
``,
  REWRITE_TAC [dCoh_oblg2]
);

val dCoh_subset_lem = store_thm("dCoh_subset_lem", ``
!ms As Bs. dCoh ms As /\ Bs SUBSET As ==> dCoh ms Bs
``,
  RW_TAC std_ss [pred_setTheory.SUBSET_DEF, dCoh_lem2]
);

val dCoh_alt_lem = store_thm("dCoh_alt_lem", ``
!ms Rs. dCoh ms Rs 
            <=> 
        !pa. pa IN Rs ==> ((dmvca ms) T pa = (dmvalt ms) T pa)
``,
  REWRITE_TAC [dCoh_alt_oblg]
);

val dcoh_alt_lem = store_thm("dcoh_alt_lem", ``
!ms Rs pa. dcoh ms pa <=> ((dmvca ms) T pa = (dmvalt ms) T pa)
``,
  REWRITE_TAC [dcoh_alt_oblg]
);

val dcoh_diff_lem = store_thm("dcoh_diff_lem", ``
!ms pa. dcoh ms pa <=> dhit ms pa /\ dcnt ms pa <> M ms pa ==> dirty ms pa
``,
  REWRITE_TAC [dcoh_diff_oblg]
);

val dcoh_unchanged_lem = store_thm("dcoh_unchanged_lem", ``
!ms ms' pa. dcoh ms pa /\ (dw ms' pa = dw ms pa) /\ (M ms' pa = M ms pa)
        ==>
    dcoh ms' pa
``,
  REWRITE_TAC [dcoh_unchanged_oblg]
);

val dcoh_clean_lem = store_thm("dcoh_clean_lem", ``
!ms pa. dcoh ms pa /\ dhit ms pa /\ ~dirty ms pa ==> (M ms pa = dcnt ms pa)
``,
  REWRITE_TAC [dcoh_clean_oblg]
);

val dcoh_dirty_lem = store_thm("dcoh_dirty_lem", ``
!ms pa. dirty ms pa ==> dcoh ms pa
``,
  REWRITE_TAC [dcoh_dirty_oblg]
);

val dcoh_equal_lem = store_thm("dcoh_equal_lem", ``
!ms pa. dhit ms pa /\ (dcnt ms pa = M ms pa) ==> dcoh ms pa
``,
  REWRITE_TAC [dcoh_equal_oblg]
);

val dcoh_miss_lem = store_thm("dcoh_miss_lem", ``
!ms pa. ~dhit ms pa ==> dcoh ms pa
``,
  REWRITE_TAC [dcoh_miss_oblg]
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

val dcoh_other_lem = store_thm("dcoh_other_lem", ``
!ms dop ms' pa. dcoh ms pa /\ (ms' = msca_trans ms (DREQ dop)) /\ pa <> PA dop
        ==>
    dcoh ms' pa
``,
  REWRITE_TAC [dcoh_other_oblg]
);

val dcoh_not_write_lem = store_thm("dcoh_not_write_lem", ``
!ms dop ms' pa. dcoh ms pa /\ ~wt dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    dcoh ms' pa
``,
  REWRITE_TAC [dcoh_not_write_oblg]
);

val dmv_unchanged_lem = store_thm("dmv_unchanged_lem", ``
!ms dop ms' pa. (~wt dop \/ pa <> PA dop) /\ dcoh ms pa
	     /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (dmvca ms' T pa = dmvca ms T pa)
``,
  REWRITE_TAC [dmv_unchanged_oblg]
);

val dmvca_lem = store_thm("dmvca_lem", ``
!ms ms' pa. (dw ms' pa = dw ms pa) /\ (M ms' pa = M ms pa) ==>
    (dmvca ms' T pa = dmvca ms T pa)
``,
  REWRITE_TAC [dmvca_oblg]
);

val imv_lem = store_thm("imv_lem", ``
!ms ms' pa. (iw ms' pa = iw ms pa) /\ (M ms' pa = M ms pa) ==>
    (imv ms' T pa = imv ms T pa)
``,
  REWRITE_TAC [imv_oblg]
);

val dmvalt_lem = store_thm("dmvalt_lem", ``
!ms ms' pa. (dw ms' pa = dw ms pa) /\ (M ms' pa = M ms pa) ==>
    (dmvalt ms' T pa = dmvalt ms T pa)
``,
  REWRITE_TAC [dmvalt_oblg]
);

val dmvalt_unchanged_lem = store_thm("dmvalt_unchanged_lem", ``
!ms dop ms' pa. pa <> PA dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (dmvalt ms' T pa = dmvalt ms T pa)
``,
  REWRITE_TAC [dmvalt_unchanged_oblg]
);

val dmvalt_not_write_lem = store_thm("dmvalt_not_write_lem", ``
!ms dop ms'. ~wt dop /\ (ms' = msca_trans ms (DREQ dop))
        ==>
    (dmvalt ms' T (PA dop) = dmvalt ms T (PA dop))
``,
  REWRITE_TAC [dmvalt_not_write_oblg]
);


val Invic_preserve_lem = store_thm("Invic_preserve_lem", ``
!ms req ms'. Invic ms /\ (ms' = msca_trans ms req) ==> Invic ms'
``,
  REWRITE_TAC [Invic_preserve_oblg]
);

val iCoh_lem = store_thm("iCoh_lem", ``
!ms As pa. iCoh ms As /\ pa IN As ==> icoh ms pa
``,
  REWRITE_TAC [iCoh_oblg]
);

val iCoh_lem2 = store_thm("iCoh_lem2", ``
!ms As. iCoh ms As <=> !pa. pa IN As ==> icoh ms pa
``,
  REWRITE_TAC [iCoh_oblg2]
);

val icoh_flush_lem = store_thm("icoh_flush_lem", ``
!ms ms' pa. (ms' = msca_trans ms (ICFR pa))
        ==>
    icoh ms' pa
``,
  REWRITE_TAC [icoh_flush_oblg]
);

val icoh_preserve_lem = store_thm("icoh_preserve_lem", ``
!ms req ms' pa. icoh ms pa /\ (ms' = msca_trans ms req)
	     /\ (Wreq req ==> (pa <> Adr req))
	     /\ clean ms pa
        ==>
    icoh ms' pa
``,
  REWRITE_TAC [icoh_preserve_oblg]
);

val imv_dmv_lem = store_thm("imv_dmv_lem", ``
!ms pa. icoh ms pa /\ dcoh ms pa /\ clean ms pa ==> 
    (imv ms T pa = dmvca ms T pa)
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

val imv_flush_lem = store_thm("imv_flush_lem", ``
!ms pa ms' req. icoh ms pa /\ Ireq req /\ (ms' = msca_trans ms req)
        ==>
    (imv ms' T pa = imv ms T pa)
``,
  REWRITE_TAC [imv_flush_oblg]
);

val imv_preserve_lem = store_thm("imv_preserve_lem", ``
!ms req ms' pa. icoh ms pa /\ dcoh ms pa /\ (ms' = msca_trans ms req)
	     /\ (Wreq req ==> (pa <> Adr req))
	     /\ clean ms pa
        ==>
    (imv ms' T pa = imv ms T pa)
``,
  REWRITE_TAC [imv_preserve_oblg]
);

(******* some derived lemmas *******)

val core_req_mmu_lem = store_thm("core_req_mmu_lem", ``
!c M mv req c'. core_req (c,M,mv,req,c') /\ req <> NOREQ ==> 
    ?va. Mmu_(c,mv,va,M,Acc req) = SOME (Adr req, CAreq req)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC not_NOREQ_lem
  >| [(* Dreq *)
      IMP_RES_TAC core_req_mmu_Dreq_lem >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC []
      ,
      (* Freq *)
      IMP_RES_TAC core_req_mmu_Freq_lem >>
      IMP_RES_TAC Freq_lem >>
      RW_TAC std_ss [Acc_def, CAreq_def] >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC []
      ,
      (* Ireq *)
      IMP_RES_TAC core_req_mmu_Ireq_lem >>
      IMP_RES_TAC Ireq_lem >>
      RW_TAC std_ss [Acc_def, CAreq_def] >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC []
     ]      
);

val Mon__lem = store_thm("Mon__lem", ``
!c c' mv mv'. (!r. r IN MD_(c,mv,UNIV:vadr set) ==> (CV c mv r = CV c' mv' r))
                  ==>
              (!r m ac. Mon_(c,mv,r,m,ac) <=> Mon_(c',mv',r,m,ac))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Mmu_lem >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNIV] >>
  Cases_on `reg_res r`
  >| [(* register resource *)
      METIS_TAC [Mon__reg_lem] 
      ,
      (* memory resource *)
      `?pa. r = MEM pa` by METIS_TAC [res_cases] >>
      RW_TAC std_ss [GSYM Mon__mem_lem]
     ]
);

val core_req_mem_req_lem = store_thm("core_req_mem_req_lem", ``
!c M mv req c'. core_req (c,M,mv,req,c') /\ req <> NOREQ ==> 
    Mon_(c,mv,MEM (Adr req),M,Acc req)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC core_req_mmu_lem >>
  IMP_RES_TAC Mon__mem_lem
);


(******* HW semantics ********)

val _ = Datatype `hw_state = <| 
    cs  : core_state;
    ms  : memsys_state
|>`;

val MD_def = Define `MD s = MD_ (s.cs, dmvca s.ms, UNIV:vadr set)`;
val MDVA_def = Define `MDVA s VAs = MD_ (s.cs, dmvca s.ms, VAs)`;
val Mon_def = Define `Mon s r m ac = Mon_ (s.cs, dmvca s.ms, r, m, ac)`;
val Mmu_def = Define `Mmu s va m ac = Mmu_ (s.cs, dmvca s.ms, va, m, ac)`;
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

val MD_lem = store_thm("MD_lem", ``
!s s'. (!r. r IN MD s ==> (Cv s r = Cv s' r)) ==> (MD s = MD s')
``,
  RW_TAC std_ss [MD_def, Cv_def, MD__lem]
);

val MDVA_lem = store_thm("MDVA_lem", ``
!s s' VAs. (!r. r IN MDVA s VAs ==> (Cv s r = Cv s' r)) ==> 
    (MDVA s VAs = MDVA s' VAs)
``,
  RW_TAC std_ss [MDVA_def, Cv_def, MD__lem]
);

val Cv_mem_lem = store_thm("Cv_mem_lem", ``
!s pa. Cv s (MEM pa) = dmvca s.ms T pa
``,
  RW_TAC std_ss [Cv_def, CV_def]
);

val exentry_lem = store_thm("exentry_lem", ``
!s. exentry s ==> (mode s = PRIV)
``,
  RW_TAC std_ss [exentry_def, mode_def, exentry__lem]
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
/\ (!s M pa s'. 
        (M = Mode s.cs)
     /\ core_req (s.cs, M, dmvca s.ms, ICFR pa, s'.cs) 
     /\ (s'.ms = msca_trans s.ms (ICFR pa))
    ==>
    hw_trans s M (ICFR pa) s')
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

val hw_trans_flush_lem = store_thm("hw_trans_flush_lem", ``
!s M req s'. Ireq req /\ hw_trans s M req s' ==>
    core_req (s.cs, M, dmvca s.ms, req, s'.cs) 
 /\ (s'.ms = msca_trans s.ms req)
``,
  NTAC 5 STRIP_TAC >>
  IMP_RES_TAC Ireq_lem >>
  IMP_RES_TAC hw_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct]
  ) >>
  FULL_SIMP_TAC std_ss [corereq_11] >>
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

val hw_trans_not_NOREQ_lem = store_thm("hw_trans_not_NOREQ_lem", ``
!s M req s'. req <> NOREQ /\ hw_trans s M req s' ==> 
    (s'.ms = msca_trans s.ms req)
``,
  RW_TAC std_ss [] >>
  IMP_RES_TAC hw_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct]
  )
);

val hw_trans_data_ic_lem = store_thm("hw_trans_data_ic_lem", ``
!s M req s'. Dreq req /\ hw_trans s M req s' 
        ==> 
    (!pa. iw s'.ms pa = iw s.ms pa)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC hw_trans_data_lem >>
  IMP_RES_TAC Dreq_lem >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC msca_DREQ_unchanged_lem >>
  METIS_TAC []
);

val hw_trans_core_req_lem = store_thm("hw_trans_core_req_lem", ``
!s M req s'. hw_trans s M req s' ==> 
    ?cs'. core_req (s.cs, M, dmvca s.ms, req, cs') 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC hw_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct] >>
      REV_FULL_SIMP_TAC std_ss [] >>
      HINT_EXISTS_TAC >>
      RW_TAC std_ss []
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
  RW_TAC std_ss [] >> (
      IMP_RES_TAC hw_trans_cases >> (
          FULL_SIMP_TAC std_ss [corereq_distinct, corereq_11] >>
          REV_FULL_SIMP_TAC std_ss []
      )
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
  RW_TAC std_ss [] >> (
      IMP_RES_TAC hw_trans_cases >> (
          FULL_SIMP_TAC std_ss [corereq_distinct, corereq_11] >>
          REV_FULL_SIMP_TAC std_ss []
      )
  )
);

val hw_trans_write_val_lem = store_thm("hw_trans_write_val_lem", ``
!s M req s'. Wreq req /\ hw_trans s M req s' /\ CAreq req ==>
    (Cv s' (MEM (Adr req)) = VAL (Dop req))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC Wreq_lem >>
  ASM_REWRITE_TAC [Dop_def, Adr_def] >>
  IMP_RES_TAC not_rd_lem >>
  RW_TAC std_ss [] >> 
  `s'.ms = msca_trans s.ms (DREQ dop)` by ( 
      IMP_RES_TAC hw_trans_cases >> (
          FULL_SIMP_TAC std_ss [corereq_distinct, corereq_11] >>
	  REV_FULL_SIMP_TAC std_ss []
      )
  ) >>
  FULL_SIMP_TAC std_ss [CAreq_def] >>
  IMP_RES_TAC msca_write_val_lem >>
  RW_TAC std_ss [Cv_def, CV_def] >>
  REV_FULL_SIMP_TAC std_ss []
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
  RW_TAC std_ss [] >> (
      IMP_RES_TAC hw_trans_cases >> (
          FULL_SIMP_TAC std_ss [corereq_distinct, corereq_11] >>
          REV_FULL_SIMP_TAC std_ss []
      )
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

val hw_trans_not_Dreq_lem = store_thm("hw_trans_not_Dreq_lem", ``
!s m req s'. ~Dreq req /\ hw_trans s m req s' ==>
    !pa. (dw s'.ms pa = dw s.ms pa) /\ (M s'.ms pa = M s.ms pa)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  `Freq req \/ Ireq req \/ (req = NOREQ)` by ( METIS_TAC [req_cases_lem] ) 
  >| [(* fetch *)
      IMP_RES_TAC hw_trans_fetch_lem >>
      IMP_RES_TAC Freq_lem >>
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC msca_FREQ_unchanged_lem >>
      REV_FULL_SIMP_TAC std_ss []
      ,
      (* fetch *)
      IMP_RES_TAC hw_trans_flush_lem >>
      IMP_RES_TAC Ireq_lem >>
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC msca_ICFR_unchanged_lem >>
      REV_FULL_SIMP_TAC std_ss []
      ,
      (* NOREQ *)
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC hw_trans_noreq_lem >>
      FULL_SIMP_TAC std_ss [] 
     ]
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
      ,
      (* Ireq *)
      IMP_RES_TAC hw_trans_flush_lem >> 
      IMP_RES_TAC core_req_mem_req_lem
     ]
);

val hw_trans_CA_lem = store_thm("hw_trans_CA_lem", ``
!s M req s'. Dreq req /\ ~CAreq req /\ hw_trans s M req s' ==>
    ?va. Mmu s va M (Acc req) = SOME (Adr req, F)
``,
  RW_TAC std_ss [Mmu_def] >>
  `req <> NOREQ` by ( METIS_TAC [req_cases_lem] ) >>
  IMP_RES_TAC hw_trans_core_req_lem >>
  IMP_RES_TAC core_req_mmu_lem >>
  REV_FULL_SIMP_TAC std_ss [] >>
  HINT_EXISTS_TAC >>
  RW_TAC std_ss []
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
      ,
      (* Ireq *)
      IMP_RES_TAC hw_trans_flush_lem >> 
      IMP_RES_TAC core_req_mode_lem
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

val hw_trans_coreg_lem = store_thm("hw_trans_coreg_lem", ``
!s req s'. hw_trans s USER req s' ==> (s'.cs.coreg = s.cs.coreg)
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC ( SPEC ``req:corereq`` req_cases_lem ) >> 
  FULL_SIMP_TAC std_ss []
  >| [(* fetch *)
      IMP_RES_TAC hw_trans_fetch_lem >>
      IMP_RES_TAC core_req_user_coreg_lem >>
      IMP_RES_TAC core_rcv_user_coreg_lem >>
      RW_TAC std_ss []
      ,
      (* Ireq *)
      IMP_RES_TAC hw_trans_flush_lem >>
      IMP_RES_TAC core_req_user_coreg_lem
      ,
      (* Dreq *)
      IMP_RES_TAC Dreq_cases_lem 
      >| [(* read *)
	  IMP_RES_TAC hw_trans_read_lem >>
	  IMP_RES_TAC core_req_user_coreg_lem >>
	  IMP_RES_TAC core_rcv_user_coreg_lem >>
	  RW_TAC std_ss []
	  ,
	  (* write *)
	  IMP_RES_TAC hw_trans_write_lem >>
	  IMP_RES_TAC core_req_user_coreg_lem
	  ,
	  (* clean *)
	  IMP_RES_TAC hw_trans_clean_lem >>
	  IMP_RES_TAC core_req_user_coreg_lem
	 ]
      ,
      (* NOREQ *)
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC hw_trans_noreq_lem >>
      IMP_RES_TAC core_req_user_coreg_lem
     ]
);

val hw_trans_progress_lem = store_thm("jw_trans_progress_lem", ``
!s. ?req s'. hw_trans s (mode s) req s'
``,
  RW_TAC std_ss [mode_def] >>
  ASSUME_TAC ( SPECL [``s.cs``,``dmvca s.ms``] core_req_progress_lem ) >>
  FULL_SIMP_TAC std_ss [] >>
  ASSUME_TAC ( SPEC ``req:corereq`` req_cases_lem ) >>
  FULL_SIMP_TAC std_ss [] 
  >| [(* Freq *)
      `?ms'. ms' = msca_trans s.ms req` by ( RW_TAC std_ss [] ) >>
      `?cs'. core_rcv(c',Mode c',imv s.ms T (Adr req),cs')` by (
          RW_TAC std_ss [core_rcv_progress_lem]
      ) >>
      IMP_RES_TAC core_req_mode_change_lem >>
      EXISTS_TAC ``req:corereq`` >>
      EXISTS_TAC ``<|cs := cs'; ms := ms'|>`` >>
      IMP_RES_TAC Freq_lem >>
      RW_TAC std_ss [hw_trans_cases] >> (
          FULL_SIMP_TAC std_ss [corereq_distinct, Adr_def]
      ) >>
      METIS_TAC []
      ,
      (* Ireq *)
      `?ms'. ms' = msca_trans s.ms req` by ( RW_TAC std_ss [] ) >>
      EXISTS_TAC ``req:corereq`` >>
      EXISTS_TAC ``<|cs := c'; ms := ms'|>`` >>
      IMP_RES_TAC Ireq_lem >>
      RW_TAC std_ss [hw_trans_cases] >> (
          FULL_SIMP_TAC std_ss [corereq_distinct, Adr_def, Dop_def]
      )
      ,
      (* Dreq *)
      IMP_RES_TAC Dreq_cases_lem
      >| [(* read *)
	  `?ms'. ms' = msca_trans s.ms req` by ( RW_TAC std_ss [] ) >>
	  `?cs'. core_rcv(c',Mode c',dmvca s.ms (CAreq req) (Adr req),cs')` by (
	      RW_TAC std_ss [core_rcv_progress_lem]
	  ) >>
	  IMP_RES_TAC core_req_mode_change_lem >>
	  EXISTS_TAC ``req:corereq`` >>
	  EXISTS_TAC ``<|cs := cs'; ms := ms'|>`` >>
	  IMP_RES_TAC Rreq_lem >>
	  RW_TAC std_ss [hw_trans_cases] >> (
	      FULL_SIMP_TAC std_ss [corereq_distinct, Adr_def, CAreq_def]
	  ) >>
	  IMP_RES_TAC rd_lem >>
	  METIS_TAC []
	  ,
	  (* write *)
	  `?ms'. ms' = msca_trans s.ms req` by ( RW_TAC std_ss [] ) >>
          EXISTS_TAC ``req:corereq`` >>
          EXISTS_TAC ``<|cs := c'; ms := ms'|>`` >>
          IMP_RES_TAC Wreq_lem >>
	  `~rd dop` by ( METIS_TAC [not_rd_lem] ) >>
          RW_TAC std_ss [hw_trans_cases] >> (
              FULL_SIMP_TAC std_ss [corereq_distinct, Adr_def, Dop_def]
          )
	  ,
	  (* clean *)
	  `?ms'. ms' = msca_trans s.ms req` by ( RW_TAC std_ss [] ) >>
          EXISTS_TAC ``req:corereq`` >>
          EXISTS_TAC ``<|cs := c'; ms := ms'|>`` >>
          IMP_RES_TAC Creq_lem >>
	  `~rd dop` by ( METIS_TAC [not_rd_lem] ) >>
          RW_TAC std_ss [hw_trans_cases] >> (
              FULL_SIMP_TAC std_ss [corereq_distinct, Adr_def, Dop_def]
          )
	 ]
      ,
      (* NOREQ *)
      EXISTS_TAC ``req:corereq`` >>
      EXISTS_TAC ``<|cs := c'; ms := s.ms|>`` >>
      RW_TAC std_ss [hw_trans_cases] >> (
          FULL_SIMP_TAC std_ss [corereq_distinct, Adr_def, Dop_def]
      )
     ]
);

(* memory system and coherency *)

val hw_trans_dmv_lem = store_thm("hw_trans_dmv_lem", ``
!s m req s' pa. (~Wreq req \/ pa <> Adr req) /\ dcoh s.ms pa 
	     /\ hw_trans s m req s'
         ==>
    (dmvca s'.ms T pa = dmvca s.ms T pa)
``,
  REPEAT GEN_TAC >>
  Cases_on `Dreq req`
  >| [(* Dreq *)
      STRIP_TAC >> (
	  IMP_RES_TAC Dreq_lem >>
	  FULL_SIMP_TAC std_ss [Wreq_def, Adr_def] >>
	  IMP_RES_TAC hw_trans_data_lem >>
	  IMP_RES_TAC dmv_unchanged_lem 
      )
      ,
      (* other *) 
      STRIP_TAC >> (
          IMP_RES_TAC hw_trans_not_Dreq_lem >>
	  MATCH_MP_TAC dmvca_lem >>
	  ASM_REWRITE_TAC []
      )
     ]
);

val hw_trans_dmv_set_lem = store_thm("hw_trans_dmv_set_lem", ``
!s m req s' As. (~Wreq req \/ Adr req NOTIN As) /\ dCoh s.ms As
	     /\ hw_trans s m req s'
         ==>
    (!pa. pa IN As ==> (dmvca s'.ms T pa = dmvca s.ms T pa))
``,
  RW_TAC std_ss [] >> ( IMP_RES_TAC dCoh_lem ) 
  >| [(* not write *)
      IMP_RES_TAC hw_trans_dmv_lem
      ,
      (* address not in Rs *)
      `pa <> Adr req` by (
          CCONTR_TAC >>
          FULL_SIMP_TAC std_ss []
      ) >>
      IMP_RES_TAC hw_trans_dmv_lem
     ]
);

val hw_trans_mon_write_lem = store_thm("hw_trans_mon_write_lem", ``
!s m req s' pa. hw_trans s m req s' /\ ~Mon s (MEM pa) m W 
        ==>
    (~Wreq req \/ pa <> Adr req)
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [GSYM IMP_DISJ_THM] >>
  STRIP_TAC >>
  IMP_RES_TAC Wreq_lem >>
  `req <> NOREQ` by ( FULL_SIMP_TAC std_ss [corereq_distinct] ) >>
  IMP_RES_TAC hw_trans_mon_lem >>
  CCONTR_TAC >>
  FULL_SIMP_TAC std_ss [Adr_def] >>
  REV_FULL_SIMP_TAC std_ss [Adr_def, Acc_def]
);

val hw_trans_mon_write_set_lem = store_thm("hw_trans_mon_write_set_lem", ``
!s m req s' As. hw_trans s m req s' /\ (!pa. pa IN As ==> ~Mon s (MEM pa) m W)
        ==>
    (~Wreq req \/ Adr req NOTIN As)
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [GSYM IMP_DISJ_THM] >>
  STRIP_TAC >>
  CCONTR_TAC >>
  FULL_SIMP_TAC std_ss [Adr_def] >>
  RES_TAC >>
  IMP_RES_TAC hw_trans_mon_write_lem >>
  FULL_SIMP_TAC std_ss []
);

val hw_trans_user_MD_lem = store_thm("hw_trans_user_MD_lem", ``
!s req s' r. hw_trans s USER req s' /\ reg_res r /\ r IN MD s
        ==>
    (Cv s' r = Cv s r)
``,
  RW_TAC std_ss [MD_def, Cv_def] >>
  ASSUME_TAC ( SPEC ``req:corereq`` req_cases_lem ) >> 
  FULL_SIMP_TAC std_ss []
  >| [(* fetch *)
      IMP_RES_TAC hw_trans_fetch_lem >>
      IMP_RES_TAC core_req_user_MD_reg_lem >>
      `CV cs' (dmvca s.ms) r = CV cs' (dmvca s'.ms) r` by (
          FULL_SIMP_TAC std_ss [CV_reg_lem]
      ) >>
      `r IN MD_ (cs',dmvca s'.ms, UNIV:vadr set)` by (
          IMP_RES_TAC MD__reg_lem >>
	  FULL_SIMP_TAC std_ss []
      ) >>
      IMP_RES_TAC core_rcv_user_MD_reg_lem >>
      RW_TAC std_ss []
      ,
      (* Ireq *)
      IMP_RES_TAC hw_trans_flush_lem >>
      IMP_RES_TAC core_req_user_MD_reg_lem >>
      FULL_SIMP_TAC std_ss [CV_reg_lem]
      ,
      (* Dreq *)
      IMP_RES_TAC Dreq_cases_lem 
      >| [(* read *)
	  IMP_RES_TAC hw_trans_read_lem >>
	  IMP_RES_TAC core_req_user_MD_reg_lem >>
          `CV cs' (dmvca s.ms) r = CV cs' (dmvca s'.ms) r` by (
              FULL_SIMP_TAC std_ss [CV_reg_lem]
	  ) >>
          `r IN MD_ (cs',dmvca s'.ms, UNIV:vadr set)` by (
              IMP_RES_TAC MD__reg_lem >>
	      FULL_SIMP_TAC std_ss []
	  ) >>
	  IMP_RES_TAC core_rcv_user_MD_reg_lem >>
	  RW_TAC std_ss []
	  ,
	  (* write *)
	  IMP_RES_TAC hw_trans_write_lem >>
	  IMP_RES_TAC core_req_user_MD_reg_lem >>
          FULL_SIMP_TAC std_ss [CV_reg_lem]
	  ,
	  (* clean *)
	  IMP_RES_TAC hw_trans_clean_lem >>
	  IMP_RES_TAC core_req_user_MD_reg_lem >>
          FULL_SIMP_TAC std_ss [CV_reg_lem]
	 ]
      ,
      (* NOREQ *)
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC hw_trans_noreq_lem >>
      IMP_RES_TAC core_req_user_MD_reg_lem >>
      FULL_SIMP_TAC std_ss [CV_reg_lem]
     ]
);

val hw_trans_dmvalt_lem = store_thm("hw_trans_dmvalt_lem", ``
!s m req s' pa. pa <> Adr req /\ hw_trans s m req s'
         ==>
    (dmvalt s'.ms T pa = dmvalt s.ms T pa)
``,
  REPEAT STRIP_TAC >>
  Cases_on `Dreq req`
  >| [(* Dreq *)
      IMP_RES_TAC Dreq_lem >>
      FULL_SIMP_TAC std_ss [Adr_def] >>
      IMP_RES_TAC hw_trans_data_lem >>
      IMP_RES_TAC dmvalt_unchanged_lem 
      ,
      (* other *) 
      IMP_RES_TAC hw_trans_not_Dreq_lem >>
      MATCH_MP_TAC dmvalt_lem >>
      ASM_REWRITE_TAC []
     ]
);

val hw_trans_dmvalt_not_write_lem = 
store_thm("hw_trans_dmvalt_not_write_lem", ``
!s m req s'. ~Wreq req /\ hw_trans s m req s'
         ==>
    (dmvalt s'.ms T (Adr req) = dmvalt s.ms T (Adr req))
``,
  REPEAT STRIP_TAC >>
  Cases_on `Dreq req`
  >| [(* Dreq *)
      IMP_RES_TAC Dreq_lem >>
      FULL_SIMP_TAC std_ss [Wreq_def, Adr_def] >>
      IMP_RES_TAC hw_trans_data_lem >>
      IMP_RES_TAC dmvalt_not_write_lem 
      ,
      (* other *) 
      IMP_RES_TAC hw_trans_not_Dreq_lem >>
      MATCH_MP_TAC dmvalt_lem >>
      ASM_REWRITE_TAC []
     ]
);

val hw_trans_dcoh_write_lem = store_thm("hw_trans_dcoh_write_lem", ``
!s m req s'. Wreq req /\ CAreq req /\ hw_trans s m req s' 
        ==> 
    dcoh s'.ms (Adr req)
``,
  REPEAT STRIP_TAC >>
  Cases_on `Dreq req`
  >| [(* Dreq *)
      IMP_RES_TAC Dreq_lem >>
      FULL_SIMP_TAC std_ss [Wreq_def, Adr_def, CAreq_def] >>
      IMP_RES_TAC hw_trans_data_lem >>
      IMP_RES_TAC dcoh_write_lem 
      ,
      (* other *) 
      ASSUME_TAC ( SPEC ``req:corereq`` req_cases_lem ) >>
      REV_FULL_SIMP_TAC std_ss [] >> (
          IMP_RES_TAC not_Wreq_lem
      )
     ]
);

val hw_trans_dcoh_not_write_lem = store_thm("hw_trans_dcoh_not_write_lem", ``
!s m req s' pa. dcoh s.ms pa /\ ~Wreq req /\ hw_trans s m req s' 
        ==> 
    dcoh s'.ms pa
``,
  REPEAT STRIP_TAC >>
  Cases_on `Dreq req`
  >| [(* Dreq *)
      IMP_RES_TAC Dreq_lem >>
      FULL_SIMP_TAC std_ss [Wreq_def] >>
      IMP_RES_TAC hw_trans_data_lem >>
      IMP_RES_TAC dcoh_not_write_lem 
      ,
      (* other *) 
      IMP_RES_TAC hw_trans_not_Dreq_lem >>
      MATCH_MP_TAC dcoh_lem >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC []
     ]
);

val hw_trans_clean_flush_lem = store_thm("hw_trans_clean_flush_lem", ``
!s m req s' pa. Creq req /\ hw_trans s m req s' 
        ==> 
    ~dirty s'.ms (Adr req)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC Creq_lem >> 
  IMP_RES_TAC hw_trans_clean_lem >>
  REV_FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC dc_cacheable_cl_miss_lem >> 
  IMP_RES_TAC not_dhit_not_dirty_lem >>
  REV_FULL_SIMP_TAC std_ss [Adr_def]
);

val hw_trans_dcoh_flush_lem = store_thm("hw_trans_dcoh_flush_lem", ``
!s m req s' pa. Creq req /\ hw_trans s m req s' 
        ==> 
    dcoh s'.ms (Adr req)
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC Creq_lem >> 
  IMP_RES_TAC hw_trans_clean_lem >>
  REV_FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC dc_cacheable_cl_miss_lem >> 
  IMP_RES_TAC dcoh_miss_lem >>
  REV_FULL_SIMP_TAC std_ss [Adr_def]
);

val hw_trans_clean_preserve_lem = store_thm("hw_trans_clean_preserve_lem", ``
!s m req s' pa. hw_trans s m req s' 
	     /\ (Wreq req ==> (pa <> Adr req))
	     /\ dcoh s.ms pa 
	     /\ clean s.ms pa
        ==>
    clean s'.ms pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  Cases_on `Dreq req`
  >| [(* Dreq *)
      IMP_RES_TAC hw_trans_data_lem >>
      IMP_RES_TAC msca_clean_preserve_lem
      ,
      (* not dreq *)
      IMP_RES_TAC hw_trans_not_Dreq_lem >>
      METIS_TAC [clean_lem]
     ]
);

val hw_trans_dCoh_preserve_lem = store_thm("hw_trans_dCoh_preserve_lem", ``
!s m req s' As. dCoh s.ms As /\ CAreq req /\ hw_trans s m req s' 
        ==> 
    dCoh s'.ms As
``,
  RW_TAC std_ss [dCoh_lem2] >>
  RES_TAC >>
  Cases_on `Wreq req`
  >| [(* Wreq *)
      Cases_on `pa = Adr req` 
      >| [(* Adr req *)
	  IMP_RES_TAC hw_trans_dcoh_write_lem >>
	  RW_TAC std_ss []
	  ,
	  (* other *)
	  `Dreq req` by ( 
	      IMP_RES_TAC Wreq_lem >>
	      FULL_SIMP_TAC std_ss [Wreq_lem, Dreq_def] 
	  ) >> 
	  IMP_RES_TAC hw_trans_data_lem >>
	  IMP_RES_TAC Dreq_lem >>
	  FULL_SIMP_TAC std_ss [Adr_def] >>
	  IMP_RES_TAC dcoh_other_lem >>
	  REV_FULL_SIMP_TAC std_ss []
	 ]
      ,
      (* not Wreq *)
      IMP_RES_TAC hw_trans_dcoh_not_write_lem
     ]
);

val hw_trans_icoh_flush_lem = store_thm("hw_trans_icoh_flush_lem", ``
!s m req s' pa. hw_trans s m req s' /\ Ireq req ==> icoh s'.ms (Adr req)
``,
  REPEAT STRIP_TAC >>
  `req <> NOREQ` by ( METIS_TAC [Ireq_lem, corereq_distinct] ) >>
  IMP_RES_TAC hw_trans_not_NOREQ_lem >>
  IMP_RES_TAC Ireq_lem >>
  FULL_SIMP_TAC std_ss [Adr_def] >>
  IMP_RES_TAC icoh_flush_lem >>
  REV_FULL_SIMP_TAC std_ss []
);

val hw_trans_icoh_clean_preserve_lem = 
store_thm("hw_trans_icoh_clean_preserve_lem", ``
!s m req s' pa. 
    hw_trans s m req s'
 /\ (Wreq req ==> pa <> Adr req)
 /\ icoh s.ms pa
 /\ dcoh s.ms pa
 /\ clean s.ms pa
        ==> 
    icoh s'.ms pa
 /\ clean s'.ms pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  Cases_on `req = NOREQ`
  >| [(* NOREQ *)
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC hw_trans_noreq_lem >>
      ASM_REWRITE_TAC []
      ,
      (* Dreq or Freq *)
      IMP_RES_TAC hw_trans_not_NOREQ_lem >>
      IMP_RES_TAC icoh_preserve_lem >>
      IMP_RES_TAC not_NOREQ_lem
      >| [(* Dreq *)
	  IMP_RES_TAC msca_clean_preserve_lem >>
	  ASM_REWRITE_TAC []
	  ,
	  (* Freq *)
	  IMP_RES_TAC Freq_lem >>
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC msca_FREQ_unchanged_lem >>
	  METIS_TAC [clean_lem]
	  ,
	  (* Ireq *)
	  IMP_RES_TAC Ireq_lem >>
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC msca_ICFR_unchanged_lem >>
	  METIS_TAC [clean_lem]
	 ]
     ]
);

(****** Deriveability *******) 

val drvbl_non_def = Define `drvbl_non s s' pa = 
   (M s'.ms pa <> M s.ms pa ==> dirty s.ms pa /\ (M s'.ms pa = dcnt s.ms pa))
/\ (dw s'.ms pa <> dw s.ms pa ==> 
       (~dhit s'.ms pa /\ (dirty s.ms pa ==> (M s'.ms pa = dcnt s.ms pa))
        \/ dhit s.ms pa /\ ~dirty s.ms pa /\ dirty s'.ms pa 
	                /\ (dcnt s'.ms pa = dcnt s.ms pa)
        \/ ~dhit s.ms pa /\ dhit s'.ms pa /\ ~dirty s'.ms pa 
	                /\ (dcnt s'.ms pa = M s.ms pa)))
`;

(* NOTE: need cleanness here to preserve isafe later *)
val drvbl_rd_def = Define `drvbl_rd s s' pa = 
   (Mon s (MEM pa) USER R \/ MEM pa IN MD s)
/\ (M s'.ms pa = M s.ms pa)
/\ (dw s'.ms pa <> dw s.ms pa ==> 
        ~dhit s.ms pa /\ dhit s'.ms pa /\ ~dirty s'.ms pa 
		      /\ (dcnt s'.ms pa = M s.ms pa))
`;

val drvbl_wt_def = Define `drvbl_wt s s' pa = 
   Mon s (MEM pa) USER W 
/\ (dw s'.ms pa <> dw s.ms pa ==> 
        (dirty s'.ms pa \/ 
	 ~dirty s'.ms pa /\ (M s'.ms pa = dcnt s'.ms pa))) (* WT case *)
/\ (M s'.ms pa <> M s.ms pa ==> 
        (~dirty s'.ms pa ==> ((?va. Mmu s va USER W = SOME (pa,F))
			     \/ (M s'.ms pa = dcnt s'.ms pa)))) (* WT case *)
`;

val drvbl_data_def = Define `drvbl_data s s' = 
!pa. drvbl_non s s' pa \/ drvbl_rd s s' pa \/ drvbl_wt s s' pa
`;

(* instruction cache deriveability *)

val drvbl_ic_non_def = Define `drvbl_ic_non s s' pa = 
iw s'.ms pa <> iw s.ms pa ==> 
     (~ihit s'.ms pa \/ 
      ~ihit s.ms pa /\ ihit s'.ms pa /\ (icnt s'.ms pa = M s.ms pa))
`;

val drvbl_ic_ex_def = Define `drvbl_ic_ex s s' pa = 
   Mon s (MEM pa) USER EX 
/\ (iw s'.ms pa <> iw s.ms pa ==> 
       ~ihit s.ms pa /\ ihit s'.ms pa /\ (icnt s'.ms pa = M s.ms pa))
`;

val drvbl_ic_def = Define `drvbl_ic s s' = 
!pa. drvbl_ic_non s s' pa \/ drvbl_ic_ex s s' pa
`;


val drvbl_def = Define `drvbl s s' = 
(s'.cs.coreg = s.cs.coreg) /\ drvbl_data s s' /\ drvbl_ic s s' 
`;

(* deriveability lemmas *)

val drvbl_data_unchanged_lem = store_thm("drvbl_data_unchanged_lem", ``
!s s'. (!pa. (dw s'.ms pa = dw s.ms pa) /\ (M s'.ms pa = M s.ms pa))
    ==>
drvbl_data s s'
``,
  RW_TAC std_ss [drvbl_data_def] >>
  DISJ1_TAC >>
  RW_TAC std_ss [drvbl_non_def]
);

val drvbl_ic_unchanged_lem = store_thm("drvbl_unchanged_lem", ``
!s s'. (!pa. (iw s'.ms pa = iw s.ms pa))
    ==>
drvbl_ic s s'
``,
  RW_TAC std_ss [drvbl_ic_def] >>
  DISJ1_TAC >>
  RW_TAC std_ss [drvbl_ic_non_def]
);

val drvbl_unchanged_lem = store_thm("drvbl_unchanged_lem", ``
!s s'. (!pa. (dw s'.ms pa = dw s.ms pa) 
	  /\ (M s'.ms pa = M s.ms pa)
          /\ (iw s'.ms pa = iw s.ms pa))
    /\ (s'.cs. coreg = s.cs.coreg)
    ==>
drvbl s s'
``,
  RW_TAC std_ss [drvbl_def]
  >| [METIS_TAC [drvbl_data_unchanged_lem]
      ,
      METIS_TAC [drvbl_ic_unchanged_lem]
     ]
);
   
val drvbl_lem = store_thm("drvbl_lem", ``
!s req s'. hw_trans s USER req s' ==> drvbl s s'
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC hw_trans_coreg_lem >>
  Cases_on `Dreq req`
  >| [(* Dreq *)
      IMP_RES_TAC Dreq_lem >>
      `req <> NOREQ` by ( METIS_TAC [req_cases_lem] ) >>
      IMP_RES_TAC hw_trans_mon_lem >>
      FULL_SIMP_TAC std_ss [] >>
      `drvbl_ic s s'` by (
          IMP_RES_TAC hw_trans_data_ic_lem >>
          IMP_RES_TAC drvbl_ic_unchanged_lem
      ) >>
      RW_TAC std_ss [drvbl_def] >>
      IMP_RES_TAC hw_trans_data_lem >>
      RW_TAC std_ss [drvbl_data_def] >>
      Cases_on `CA dop` 
      >| [(* CA dop *)
	  Cases_on `pa = PA dop`
	  >| [(* PA dop *)
	      ASSUME_TAC ( SPEC ``dop:dop`` dop_cases_lem2 ) >>
	      FULL_SIMP_TAC std_ss []
	      >| [(* read *)
		  DISJ2_TAC >>
		  DISJ1_TAC >>
		  FULL_SIMP_TAC std_ss [Adr_def, Acc_def] >>
		  REWRITE_TAC [drvbl_rd_def] >>
		  STRIP_TAC >- ( 
		      (* Monitor permission *)
		      ASM_REWRITE_TAC [] ) >>
		  STRIP_TAC >- ( 		  
		      (* mem unchanged *)
		      IMP_RES_TAC M_cacheable_read_lem ) >>
		  STRIP_TAC >> (
		      (* miss and cache fill *)
		      IMP_RES_TAC dc_cacheable_read_lem >>
		      ASM_REWRITE_TAC []
		  )
		  ,
		  (* write *)
		  DISJ2_TAC >>
		  DISJ2_TAC >>
		  FULL_SIMP_TAC std_ss [Adr_def, Acc_def] >>
		  REWRITE_TAC [drvbl_wt_def] >>
		  STRIP_TAC >- ( 
		      (* Monitor permission *)
		      ASM_REWRITE_TAC [] ) >>
		  STRIP_TAC >- ( 		  
		      (* dirty or WT *)
		      STRIP_TAC >>
		      IMP_RES_TAC dc_cacheable_write_lem >> (
		          ASM_REWRITE_TAC []
		      )
		  ) >>
		  STRIP_TAC >> (
		      (* clean write = WT *)
		      STRIP_TAC >>
		      DISJ2_TAC >>
		      IMP_RES_TAC M_cacheable_not_cl_lem >>
		      ASM_REWRITE_TAC []
		  )
		  ,
		  (* clean *)
		  DISJ1_TAC >>
		  REWRITE_TAC [drvbl_non_def] >>
		  STRIP_TAC >- ( 		  
		      (* dirty write back *)
		      STRIP_TAC >>
		      IMP_RES_TAC M_cacheable_cl_lem >>
 	              ASM_REWRITE_TAC []
		  ) >>
		  STRIP_TAC >> (
		      (* miss and dirty write back *)
		      IMP_RES_TAC dc_cacheable_cl_lem >>
		      ASM_REWRITE_TAC []
		  )
		 ]
	      ,
	      (* others *)
	      DISJ1_TAC >>
	      REWRITE_TAC [drvbl_non_def] >>
	      STRIP_TAC
	      >| [(* mem changed *)
		  STRIP_TAC >>
		  IMP_RES_TAC M_cacheable_other_lem >>
		  ASM_REWRITE_TAC []
		  ,
		  (* cache changed *)
		  STRIP_TAC >>
		  IMP_RES_TAC dc_cacheable_other_lem >> (
		      ASM_REWRITE_TAC []
		  )
		 ]
	     ]
	  ,
	  (* uncacheable *)
	  IMP_RES_TAC dc_uncacheable_unchanged_lem >>
	  Cases_on `wt dop`
	  >| [(* write *)
	      Cases_on `pa = PA dop`
	      >| [(* PA dop *)
		  Cases_on `M s'.ms pa = M s.ms pa`
		  >| [(* mem unchanged *)
		      DISJ1_TAC >>
		      RW_TAC std_ss [drvbl_non_def]
		      ,
		      (* mem changed *)
		      RW_TAC std_ss [] >>
		      DISJ2_TAC >>
		      DISJ2_TAC >>
		      RW_TAC std_ss [drvbl_wt_def]
		      >| [(* Monitor permission *)
			  FULL_SIMP_TAC std_ss [Acc_def, Adr_def]
			  ,
			  (* uncacheable alias *)
			  `~CAreq (DREQ dop)` by ( 
			      FULL_SIMP_TAC std_ss [CAreq_def]
			  ) >>
			  IMP_RES_TAC hw_trans_CA_lem >>
			  DISJ1_TAC >>
			  REV_FULL_SIMP_TAC std_ss [Acc_def, Adr_def] >>
			  HINT_EXISTS_TAC >>
			  RW_TAC std_ss []
			 ]
		     ]
		  ,
		  (* others *)
		  IMP_RES_TAC M_uncacheable_others_lem >>
		  DISJ1_TAC >>
		  RW_TAC std_ss [drvbl_non_def]
		 ]
	      ,
	      (* not write *)
	      IMP_RES_TAC ms_uncacheable_unchanged_lem >>
	      DISJ1_TAC >>
	      RW_TAC std_ss [drvbl_non_def]
	     ]
	 ]
      ,
      (* not Dreq *)
      `drvbl_data s s'` by (
          IMP_RES_TAC hw_trans_not_Dreq_lem >>
          METIS_TAC [drvbl_data_unchanged_lem]
      ) >>
      RW_TAC std_ss [drvbl_def] >>
      Cases_on `req = NOREQ`
      >| [(* NOREQ *)
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC hw_trans_noreq_lem >>
	  `!pa. iw s'.ms pa = iw s.ms pa` by ( FULL_SIMP_TAC std_ss [] ) >>
	  IMP_RES_TAC drvbl_ic_unchanged_lem
	  ,
	  (* fetch or flush *)
	  IMP_RES_TAC hw_trans_mon_lem >>
	  IMP_RES_TAC not_NOREQ_lem
	  >| [(* fetch *)
	      IMP_RES_TAC hw_trans_fetch_lem >>
	      IMP_RES_TAC Freq_lem >>
	      FULL_SIMP_TAC std_ss [Adr_def, Acc_def] >>
	      RW_TAC std_ss [drvbl_ic_def] >>
	      Cases_on `pa' = pa`
	      >| [(* fetched address *)
	          RW_TAC std_ss [] >>
	          DISJ2_TAC >>
	          REWRITE_TAC [drvbl_ic_ex_def] >>
	          STRIP_TAC >- ( ASM_REWRITE_TAC [] ) >>
	          STRIP_TAC >>
	          IMP_RES_TAC ic_cacheable_read_lem >>
	          ASM_REWRITE_TAC []
	          ,
	          (* other address *)
	          DISJ1_TAC >>
	          REWRITE_TAC [drvbl_ic_non_def] >>
	          STRIP_TAC >>
	          IMP_RES_TAC ic_cacheable_other_lem >> (
		      RW_TAC std_ss []
		  )
		 ]
	      ,
	      (* flush *)
	      IMP_RES_TAC hw_trans_flush_lem >>
	      IMP_RES_TAC Ireq_lem >>
	      FULL_SIMP_TAC std_ss [Adr_def, Acc_def] >>
	      RW_TAC std_ss [drvbl_ic_def] >>
	      DISJ1_TAC >>
	      Cases_on `pa' = pa`
	      >| [(* fetched address *)
		  FULL_SIMP_TAC std_ss [] >>
	          IMP_RES_TAC msca_ICFR_lem >>
	          REWRITE_TAC [drvbl_ic_non_def] >>
	          STRIP_TAC >>
	          IMP_RES_TAC ic_cacheable_cl_lem >>
		  RW_TAC std_ss []
	          ,
	          (* other address *)
	          REWRITE_TAC [drvbl_ic_non_def] >>
	          STRIP_TAC >>
	          IMP_RES_TAC ic_cacheable_cl_other_lem >>
		  RW_TAC std_ss []
	         ]
	     ]
	 ]
     ]
);


(********** MMU safety ************)

val safe_def = Define `safe s = 
!s'. drvbl s s' ==> !m r ac. Mon s m r ac <=> Mon s' m r ac
`;

(* some lemmas *)

val Cv_reg_eq = Define `Cv_reg_eq s s' Rs = 
!r. r IN Rs /\ reg_res r ==> (Cv s' r = Cv s r)
`;

val Cv_dmv_eq = Define `Cv_dmv_eq s s' Rs = 
!pa. MEM pa IN Rs ==> (dmvca s'.ms T pa = dmvca s.ms T pa)
`;

val Cv_imv_eq = Define `Cv_imv_eq s s' Rs = 
!pa. MEM pa IN Rs ==> (imv s'.ms T pa = imv s.ms T pa)
`;

val Cv_lem = store_thm("Cv_lem", ``
!Rs s s'. Cv_reg_eq s s' Rs /\ Cv_dmv_eq s s' Rs ==>
    (!r. r IN Rs ==> (Cv s r = Cv s' r))
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC ( SPEC ``r:resource`` res_cases ) >>
  FULL_SIMP_TAC std_ss [] 
  >| [(* memory resource *)
      IMP_RES_TAC Cv_dmv_eq >>
      RW_TAC std_ss [Cv_def, CV_def]
      ,
      (* reg resource *)
      IMP_RES_TAC Cv_reg_eq >>
      ASM_REWRITE_TAC []
     ]
);

val dCoh_protect_lem = store_thm("dCoh_protect_lem", ``
!s m req s' Rs. hw_trans s m req s' 
	     /\ (!pa. MEM pa IN Rs ==> ~Mon s (MEM pa) m W)
	     /\ dCoh s.ms {pa | MEM pa IN Rs}
        ==>
    Cv_dmv_eq s s' Rs
``,
  RW_TAC std_ss [Cv_dmv_eq] >>
  RES_TAC >>
  `pa IN {pa | MEM pa IN Rs}` by (
      RW_TAC std_ss [pred_setTheory.IN_GSPEC_IFF]
  ) >>
  IMP_RES_TAC dCoh_lem >>
  IMP_RES_TAC hw_trans_mon_write_lem >> (
      IMP_RES_TAC hw_trans_dmv_lem
  )
);

val Mon_protect_lem = store_thm("Mon_protect_lem", ``
!s req s'. hw_trans s USER req s' 
	/\ (!pa. MEM pa IN MD s ==> ~Mon s (MEM pa) USER W)
	/\ dCoh s.ms {pa | MEM pa IN MD s}
        ==>
    !m r ac. Mon s m r ac <=> Mon s' m r ac
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  MATCH_MP_TAC Mon_lem >>
  MATCH_MP_TAC Cv_lem >>
  STRIP_TAC
  >| [(* register resources of MD *)
      RW_TAC std_ss [Cv_reg_eq] >>
      IMP_RES_TAC hw_trans_user_MD_lem >>
      ASM_REWRITE_TAC []
      ,
      (* memory resources of MD *)
      MATCH_MP_TAC dCoh_protect_lem >>
      METIS_TAC []
     ]
);

val drvbl_MD_reg_lem = store_thm("drvbl_MD_reg_lem", ``
!s s'. drvbl s s' ==> Cv_reg_eq s s' (MD s)
``,
  RW_TAC std_ss [Cv_reg_eq, MD_def, Cv_def] >>
  `s.cs.coreg = s'.cs.coreg` by ( METIS_TAC [drvbl_def] ) >>
  IMP_RES_TAC MD__coreg_lem >>
  RW_TAC std_ss []
);

val drvbl_Coh_mem_lem = store_thm("drvbl_Coh_mem_lem", ``
!s s' Rs. drvbl s s' 	
       /\ (!pa. MEM pa IN Rs ==> ~Mon s (MEM pa) USER W)
       /\ dCoh s.ms {pa | MEM pa IN Rs}
           ==> 
       Cv_dmv_eq s s' Rs
``,
  RW_TAC std_ss [Cv_dmv_eq, Cv_def] >>
  RES_TAC >>
  FULL_SIMP_TAC std_ss [drvbl_def, drvbl_data_def] >>
  PAT_X_ASSUM ``!pa. X \/ Y \/ Z`` (
      fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) 
  ) >>
  FULL_SIMP_TAC std_ss [drvbl_non_def(* , drvbl_rd_def *), drvbl_wt_def]
  >| [(* eviction, dirtying, or line fill *)
      Cases_on `dw s'.ms pa = dw s.ms pa`
      >| [(* cache unchanged *)
	  Cases_on `M s'.ms pa = M s.ms pa`
	  >| [(* memory unchanged *)
	      IMP_RES_TAC dmvca_lem
	      ,
	      (* memory changed *)
	      RES_TAC >>
	      IMP_RES_TAC dirty_hit_lem >>
	      IMP_RES_TAC dhit_lem >>
	      IMP_RES_TAC dcnt_lem >>
	      RW_TAC std_ss [dmvca_hit_lem]
	     ]
	  ,
	  (* cache changed *)
	  RES_TAC
	  >| [(* write back *)
	      Cases_on `dirty s.ms pa`
	      >| [(* dirty write back *)
	          RES_TAC >>
	          IMP_RES_TAC dirty_hit_lem >>
	          RW_TAC std_ss [dmvca_hit_lem, dmvca_miss_lem]
	          ,
	          (* clean / no write back -> use coherency *)
	          `M s'.ms pa = M s.ms pa` by (
	              CCONTR_TAC >>
	      	      FULL_SIMP_TAC std_ss []
	          ) >>
	          `dhit s.ms pa` by ( 
	              CCONTR_TAC >>
	      	      FULL_SIMP_TAC std_ss [double_not_dhit_lem]
	          ) >>
	          RW_TAC std_ss [dmvca_hit_lem, dmvca_miss_lem] >>
	          `pa IN {pa | MEM pa IN Rs}` by (
	              RW_TAC std_ss [pred_setTheory.IN_GSPEC_IFF]
	          ) >>
	          IMP_RES_TAC dCoh_lem >>
	          IMP_RES_TAC dcoh_clean_lem
	         ]
	      ,
	      (* dirtied entry *)
	      IMP_RES_TAC dirty_hit_lem >>
	      RW_TAC std_ss [dmvca_hit_lem]
	      ,
	      (* line fill *)
	      IMP_RES_TAC not_dhit_not_dirty_lem >>
	      `M s'.ms pa = M s.ms pa` by (
	          CCONTR_TAC >>
	      	  FULL_SIMP_TAC std_ss []
	      ) >>
	      RW_TAC std_ss [dmvca_hit_lem, dmvca_miss_lem]
	     ]	      
	 ]
      ,
      (* read *)
      Cases_on `dw s'.ms pa = dw s.ms pa`
      >| [(* cache and memory unchanged *)
	  FULL_SIMP_TAC std_ss [drvbl_rd_def] >> (
	      IMP_RES_TAC dmvca_lem
	  )
	  ,
	  (* only cache changed *)
	  FULL_SIMP_TAC std_ss [drvbl_rd_def] >> (
	      `dhit s'.ms pa` by ( 
	          CCONTR_TAC >>
		  IMP_RES_TAC double_not_dhit_lem
	      ) >>
	      RW_TAC std_ss [dmvca_hit_lem, dmvca_miss_lem]
	  )
	 ]
      ,
      (* write -> not possible *)
      FULL_SIMP_TAC std_ss []
     ]
);

val drvbl_MD_unchanged_lem = store_thm("drvbl_MD_unchanged_lem", ``
!s s'. drvbl s s' 	
    /\ (!pa. MEM pa IN MD s ==> ~Mon s (MEM pa) USER W)
    /\ dCoh s.ms {pa | MEM pa IN MD s}
        ==> 
    (!r. r IN MD s ==> (Cv s r = Cv s' r))
``,
  REPEAT GEN_TAC >> STRIP_TAC >>
  MATCH_MP_TAC Cv_lem >>
  RW_TAC std_ss [drvbl_MD_reg_lem, drvbl_Coh_mem_lem]
);

val Mon_Coh_safe_lem = store_thm("Mon_Coh_safe_lem", ``
!s. (!pa. MEM pa IN MD s ==> ~Mon s (MEM pa) USER W)
 /\ dCoh s.ms {pa | MEM pa IN MD s}
        ==>
    safe s
``,
  RW_TAC std_ss [safe_def] >>
  MATCH_MP_TAC Mon_lem >>
  RW_TAC std_ss [drvbl_MD_unchanged_lem]
);

val drvbl_non_dcoh_lem = store_thm("drvbl_non_dcoh", ``
!s s' pa. drvbl_non s s' pa /\ dcoh s.ms pa ==> dcoh s'.ms pa
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [drvbl_non_def] >>
  Cases_on `dw s'.ms pa = dw s.ms pa`
  >| [(* cache unchanged *)
      Cases_on `M s'.ms pa = M s.ms pa`
      >| [(* memory unchanged *)
	  IMP_RES_TAC dcoh_unchanged_lem
	  ,
	  (* memory changed -> becomes equal*)
	  RES_TAC >>
          IMP_RES_TAC dirty_hit_lem >>
	  IMP_RES_TAC dhit_lem >>
	  IMP_RES_TAC dcnt_lem >>
	  `dcnt s'.ms pa = M s'.ms pa` by ( FULL_SIMP_TAC std_ss [] ) >>
	  IMP_RES_TAC dcoh_equal_lem
	 ]
      ,
      (* cache changed -> miss *)
      RES_TAC
      >| [(* eviction *)
	  IMP_RES_TAC dcoh_miss_lem
	  ,
	  (* dirtied line *)
	  IMP_RES_TAC dcoh_dirty_lem
	  ,
	  (* line fill *)
	  IMP_RES_TAC not_dhit_not_dirty_lem >>
	  `M s'.ms pa = M s.ms pa` by (
	      CCONTR_TAC >>
	      FULL_SIMP_TAC std_ss []
	  ) >>
	  MATCH_MP_TAC dcoh_equal_lem >>
	  ASM_REWRITE_TAC []
	 ]
     ]
);


val drvbl_rd_dcoh_lem = store_thm("drvbl_rd_dcoh", ``
!s s' pa. drvbl_rd s s' pa /\ dcoh s.ms pa ==> dcoh s'.ms pa
``,
  REPEAT STRIP_TAC >>
  Cases_on `dw s'.ms pa = dw s.ms pa`
  >| [(* cache and memory unchanged *)
      FULL_SIMP_TAC std_ss [drvbl_rd_def] >> (
          IMP_RES_TAC dcoh_unchanged_lem
      )
      ,
      (* only cache changed *)
      FULL_SIMP_TAC std_ss [drvbl_rd_def] >> (
	  `dcnt s'.ms pa = M s'.ms pa` by ( FULL_SIMP_TAC std_ss [] ) >>
	  `dhit s'.ms pa` by (
              CCONTR_TAC >>
	      IMP_RES_TAC double_not_dhit_lem
	  ) >>
	  IMP_RES_TAC dcoh_equal_lem
      )
     ]
);

val drvbl_dCoh_lem = store_thm("drvbl_dCoh_lem", ``
!s s' As. drvbl s s' 	
       /\ (!pa. pa IN As ==> ~Mon s (MEM pa) USER W)
       /\ dCoh s.ms As
           ==> 
       dCoh s'.ms As
``,
  RW_TAC std_ss [dCoh_lem2] >>
  RES_TAC >>
  FULL_SIMP_TAC std_ss [drvbl_def,drvbl_data_def] >>
  PAT_X_ASSUM ``!pa. X \/ Y \/ Z`` (
      fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) 
  ) >>
  FULL_SIMP_TAC std_ss [drvbl_wt_def]
  >| [(* eviction *)
      IMP_RES_TAC drvbl_non_dcoh_lem
      ,
      (* read *)
      IMP_RES_TAC drvbl_rd_dcoh_lem
      ,
      (* write -> not possible *)
      FULL_SIMP_TAC std_ss []
     ]
);

val only_CA__def = Define `only_CA_ (cs,mv) pa =
!va m ac c. (Mmu_(cs,mv,va,m,ac) = SOME (pa,c)) ==> (c = T)
`;

val only_CA_def = Define `only_CA s pa = only_CA_ (s.cs, dmvca s.ms) pa`;

val only_CA_lem = store_thm("only_CA_lem", ``
!s pa. only_CA s pa <=> (!va m ac c. (Mmu s va m ac = SOME (pa,c)) ==> (c = T))
``,
  RW_TAC std_ss [only_CA_def, only_CA__def, Mmu_def]
);

val drvbl_dCoh_cacheable_lem = store_thm("drvbl_dCoh_cacheable_lem", ``
!s s' As. drvbl s s' 	
       /\ (!pa. pa IN As ==> only_CA s pa)	       
       /\ dCoh s.ms As
           ==> 
       dCoh s'.ms As
``,
  REPEAT STRIP_TAC >>
  REWRITE_TAC [dCoh_lem2] >>
  REPEAT STRIP_TAC >>
  IMP_RES_TAC dCoh_lem2 >>
  PAT_X_ASSUM ``!pa. X`` (
      fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) 
  ) >>
  FULL_SIMP_TAC std_ss [drvbl_def,drvbl_data_def] >>
  PAT_X_ASSUM ``!pa. X \/ Y \/ Z`` (
      fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm ) 
  ) >>
  FULL_SIMP_TAC std_ss [drvbl_wt_def]
  >| [(* eviction *)
      IMP_RES_TAC drvbl_non_dcoh_lem
      ,
      (* read *)
      IMP_RES_TAC drvbl_rd_dcoh_lem
      ,
      (* write *)
      Cases_on `dw s'.ms pa = dw s.ms pa`
      >| [(* cache unchanged *)
	  Cases_on `M s'.ms pa = M s.ms pa`
	  >| [(* memory unchanged *)
	      IMP_RES_TAC dcoh_unchanged_lem
	      ,
	      (* memory changed -> becomes equal*)
	      Cases_on `dirty s'.ms pa`
	      >| [(* dirty' *)
		  IMP_RES_TAC dcoh_dirty_lem
		  ,
		  (* ~dirty' *)
		  RES_TAC
		  >| [(* uncacheable alias *)
		      IMP_RES_TAC only_CA_lem >>
		      FULL_SIMP_TAC std_ss []
		      ,
		      (* WT case *)
		      Cases_on `dhit s'.ms pa`
		      >| [(* hit *)
			  IMP_RES_TAC dcoh_equal_lem >>
			  FULL_SIMP_TAC std_ss []
			  ,
			  (* miss *)
			  IMP_RES_TAC dcoh_miss_lem
			 ]
		     ]
		 ]
	     ]
	  ,
	  (* cache changed *)
	  RES_TAC
	  >| [(* dirty case *)
	      IMP_RES_TAC dcoh_dirty_lem
	      ,
	      (* WT case *)
	      Cases_on `dhit s'.ms pa`
	      >| [(* hit *)
		  IMP_RES_TAC dcoh_equal_lem >>
		  FULL_SIMP_TAC std_ss []
		  ,
		  (* miss *)
		  IMP_RES_TAC dcoh_miss_lem
		 ]
	     ]
	 ]
     ]
);


(* instruction cache integrity *)

(* NOTE: former region only restricted executable addresses,
executability not strictly required as long as PC is always in isafe region *)
val isafe_def = Define `isafe s As =
!pa. pa IN As (* /\ Mon s (MEM pa) m EX *) ==> clean s.ms pa
`;

val drvbl_clean_lem = store_thm("drvbl_clean_lem", ``
!s s' pa. 
    drvbl s s'
 /\ ~Mon s (MEM pa) USER W
 /\ dcoh s.ms pa
 /\ clean s.ms pa
        ==>
    clean s'.ms pa
``,
  RW_TAC std_ss [drvbl_def, drvbl_data_def] >>
  PAT_X_ASSUM ``!pa. X`` (
      fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm )
  ) >>
  REV_FULL_SIMP_TAC std_ss [drvbl_wt_def]
  >| [(* eviction *)
      Cases_on `dw s'.ms pa = dw s.ms pa`
      >| [(* cache unchanged *)
	  Cases_on `M s'.ms pa = M s.ms pa`
	  >| [(* mem unchanged *)
	      IMP_RES_TAC clean_lem
	      ,
	      (* mem changed *)
	      IMP_RES_TAC dcnt_lem >>
	      FULL_SIMP_TAC std_ss [drvbl_non_def] >>
	      MATCH_MP_TAC clean_equal_lem >>
	      RW_TAC std_ss []
	     ]
	  ,
	  (* cache changed *)
	  FULL_SIMP_TAC std_ss [drvbl_non_def]
	  >| [(* eviction *)
	      IMP_RES_TAC not_dhit_not_dirty_lem >>
	      IMP_RES_TAC clean_not_dirty_lem
	      ,
	      (* dirtied line *)
	      Cases_on `M s'.ms pa = M s.ms pa` 
	      >| [(* mem unchanged *)
		  MATCH_MP_TAC clean_equal_lem >>
		  IMP_RES_TAC dcoh_clean_lem >>
		  RW_TAC std_ss []
		  ,
		  (* mem changed -> contradiction *)
		  RES_TAC
		 ]
	      ,
	      (* line fill *)
	      IMP_RES_TAC not_dhit_not_dirty_lem >>
	      `M s'.ms pa = M s.ms pa` by (
	          CCONTR_TAC >>
	          FULL_SIMP_TAC std_ss []
	      ) >>
	      MATCH_MP_TAC clean_equal_lem >>
	      ASM_REWRITE_TAC []
	     ]
	 ]
      ,
      (* read *)
      Cases_on `dw s'.ms pa = dw s.ms pa`
      >| [(* cache and memory unchanged *)
	  FULL_SIMP_TAC std_ss [drvbl_rd_def] >> (
 	      METIS_TAC [clean_lem]
	  )
	  ,
	  (* only cache changed *)
	  FULL_SIMP_TAC std_ss [drvbl_rd_def] >> (
	      MATCH_MP_TAC clean_equal_lem >>
	      RW_TAC std_ss []
	  )
	 ]
     ]
);

val drvbl_isafe_lem = store_thm("drvbl_isafe_lem", ``
!s s' As. (!pa. pa IN As ==> ~Mon s (MEM pa) USER W)
       /\ safe s 
       /\ isafe s As
       /\ dCoh s.ms As
       /\ drvbl s s'
    ==>
        isafe s' As
``,
  RW_TAC std_ss [isafe_def, safe_def, dCoh_lem2] >>
  RES_TAC >>
  IMP_RES_TAC drvbl_clean_lem
);

val drvbl_mem_unchanged_lem = store_thm("drvbl_mem_unchanged_lem", ``
!s s' pa. ~Mon s (MEM pa) USER W /\ drvbl s s' /\ clean s.ms pa
         ==> 
    (M s'.ms pa = M s.ms pa)
``,
  RW_TAC std_ss [drvbl_def, drvbl_data_def] >>
  PAT_X_ASSUM ``!pa. X`` (
      fn thm => ASSUME_TAC ( SPEC ``pa:padr`` thm )
  ) >>
  CCONTR_TAC >>
  REV_FULL_SIMP_TAC std_ss [drvbl_wt_def]
  >| [(* eviction *)
      FULL_SIMP_TAC std_ss [drvbl_non_def] >>
      IMP_RES_TAC clean_dirty_lem >>
      FULL_SIMP_TAC std_ss []
      ,
      (* read *)
      FULL_SIMP_TAC std_ss [drvbl_rd_def]
     ]		  
);


val drvbl_iCoh_lem = store_thm("drvbl_iCoh_lem", ``
!s s' As. (!pa. pa IN As ==> ~Mon s (MEM pa) USER W)
(* /\ ?m. Mon s (MEM pa) m EX *)
       /\ dCoh s.ms As 
       /\ iCoh s.ms As 
       /\ isafe s As
       /\ drvbl s s'
    ==>
        iCoh s'.ms As
``,
  RW_TAC std_ss [iCoh_def, isafe_def, dCoh_lem2] >>
  RES_TAC >>
  RES_TAC >>
  FULL_SIMP_TAC std_ss [icoh_def] >>
  NTAC 2 STRIP_TAC 
  >| [(* instruction memory coherence *)
      IMP_RES_TAC drvbl_mem_unchanged_lem >>
      Cases_on `iw s'.ms pa = iw s.ms pa`
      >| [(* ic unchanged *)
	  IMP_RES_TAC ihit_lem >>
	  IMP_RES_TAC icnt_lem >>
	  RES_TAC >>
	  ASM_REWRITE_TAC []
	  ,
	  (* ic changed *)
	  `drvbl_ic_non s s' pa \/ drvbl_ic_ex s s' pa` by (
	      FULL_SIMP_TAC std_ss [drvbl_def, drvbl_ic_def] )
	  >| [(* eviction -> contradiction with hit *)
	      FULL_SIMP_TAC std_ss [drvbl_ic_non_def] >>
	      RES_TAC
	      ,
	      (* cache fill on fetch *)
	      FULL_SIMP_TAC std_ss [drvbl_ic_ex_def]
	     ]
	 ]
      ,
      (* clean in dc *)
      IMP_RES_TAC drvbl_clean_lem
     ]
);

val drvbl_iCoh_mem_lem = store_thm("drvbl_iCoh_mem_lem", ``
!s s' Rs. drvbl s s' 	
       /\ (!pa. MEM pa IN Rs ==> ~Mon s (MEM pa) USER W) 
	                      (* /\ ?m. Mon s (MEM pa) m EX) *)
       /\ dCoh s.ms {pa | MEM pa IN Rs}
       /\ iCoh s.ms {pa | MEM pa IN Rs}
       /\ isafe s {pa | MEM pa IN Rs}
           ==> 
       Cv_imv_eq s s' Rs
``,
  RW_TAC std_ss [Cv_imv_eq, Cv_def] >>
  `pa IN {pa | MEM pa IN Rs}` by ( 
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] 
  ) >>
  FULL_SIMP_TAC std_ss [iCoh_def, dCoh_lem2, isafe_def] >>
  RES_TAC >> 
  IMP_RES_TAC drvbl_mem_unchanged_lem >>
  Cases_on `iw s'.ms pa = iw s.ms pa`
  >| [(* cache unchanged *)
      IMP_RES_TAC imv_lem
      ,
      (* cache changed *)
      `drvbl_ic_non s s' pa \/ drvbl_ic_ex s s' pa` by (
      FULL_SIMP_TAC std_ss [drvbl_def, drvbl_ic_def] )
      >| [(* eviction or fill *)
	  FULL_SIMP_TAC std_ss [drvbl_ic_non_def] >>
	  RES_TAC
	  >| [(* eviction *)
	      `ihit s.ms pa` by ( METIS_TAC [double_not_ihit_lem] ) >>
	      RW_TAC std_ss [imv_hit_lem, imv_miss_lem] >>
	      FULL_SIMP_TAC std_ss [icoh_def] 
	      ,
	      (* line fill *)
	      RW_TAC std_ss [imv_hit_lem, imv_miss_lem]
	     ]	      
	  ,
	  (* cache fill on fetch *)
	  FULL_SIMP_TAC std_ss [drvbl_ic_ex_def] >>
	  RES_TAC >>
	  `ihit s'.ms pa` by ( METIS_TAC [double_not_ihit_lem] ) >>
	  RW_TAC std_ss [imv_hit_lem, imv_miss_lem]
	 ]
     ]
);

(******** abstract cache-aware model ********)

val abs_ca_trans_def = Define `
   (abs_ca_trans s m [] s' = hw_trans s m NOREQ s' 
			  \/ ?pa. hw_trans s m (FREQ pa) s')
/\ (abs_ca_trans s m ((DOP d)::ds) s' = hw_trans s m (DREQ d) s' /\ (ds = []))
/\ (abs_ca_trans s m ((IFL pa)::ds) s' = hw_trans s m (ICFR pa) s' /\ (ds = []))
`;

val abs_ca_distinct_dl_lem = store_thm("abs_ca_distinct_dl_lem", ``
!s m dl s'. abs_ca_trans s m dl s' ==> ALL_DISTINCT dl
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl` 
  >| [(* empty *)
      FULL_SIMP_TAC std_ss [abs_ca_trans_def] >> (
          RW_TAC std_ss [listTheory.ALL_DISTINCT]
      )
      ,
      (* non-empty *)
      Cases_on `h` >> (
          FULL_SIMP_TAC std_ss [abs_ca_trans_def] >>
          RW_TAC std_ss [listTheory.ALL_DISTINCT_SING]
      )
     ]
);

val abs_ca_req_lem = store_thm("abs_ca_req_lem", ``
!s m dl s'. abs_ca_trans s m dl s' ==> 
    ?req. hw_trans s m req s' 
       /\ (dl <> [] ==> Adr req IN adrs dl /\ 
		        (   (?dop. (req = DREQ dop) /\ (dl = [DOP dop]))
	                 \/ (?pa. (req = ICFR pa) /\ (dl = [IFL pa]))))
       /\ ((dl = []) ==> (Freq req \/ (req = NOREQ)))
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl`
  >| [(* empty *)
      FULL_SIMP_TAC std_ss [abs_ca_trans_def] >> (
	  HINT_EXISTS_TAC >>
	  ASM_REWRITE_TAC [corereq_distinct, Freq_def]
      )
      ,
      (* non-empty *)
      Cases_on `h` >> (
         FULL_SIMP_TAC std_ss [abs_ca_trans_def] >> 
         HINT_EXISTS_TAC >>
	 RW_TAC list_ss [Adr_def, adrs_def, opd_def, PA_def]
      )
     ] 
);

val abs_ca_trans_no_dop_oblg = store_thm("abs_ca_trans_no_dop_oblg", ``
!s m s'. abs_ca_trans s m [] s' ==> 
    !pa. Cv s' (MEM pa) = Cv s (MEM pa)
``,
  RW_TAC std_ss [Cv_def, coreIfTheory.CV_def, cachememTheory.MVcl_def] >>
  MATCH_MP_TAC dmvca_lem >>
  MATCH_MP_TAC hw_trans_not_Dreq_lem >>
  FULL_SIMP_TAC std_ss [abs_ca_trans_def] >> (
      METIS_TAC [Dreq_def]
  )
);

val abs_ca_trans_mode_oblg = store_thm("abs_ca_trans_mode_oblg", ``
!s m dl s'. abs_ca_trans s m dl s' ==> (mode s = m) 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC abs_ca_req_lem >>
  IMP_RES_TAC hw_trans_core_req_lem >>
  IMP_RES_TAC core_req_curr_mode_lem >>
  ASM_REWRITE_TAC [mode_def]
);
 
val abs_ca_trans_not_write_oblg = store_thm("abs_ca_trans_not_write_oblg", ``
!s m dl s' pa. abs_ca_trans s m dl s' /\ dcoh s.ms pa /\ pa NOTIN writes dl ==> 
    (Cv s' (MEM pa) = Cv s (MEM pa))
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl`
  >| [(* empty *)
      IMP_RES_TAC abs_ca_trans_no_dop_oblg >>
      ASM_REWRITE_TAC []
      ,
      (* non-empty *)
      Cases_on `h` >> (
          FULL_SIMP_TAC std_ss [abs_ca_trans_def] >>
          REV_FULL_SIMP_TAC list_ss [] >>
          IMP_RES_TAC writes_lem >>
          RW_TAC std_ss [Cv_def, CV_def] >>
          MATCH_MP_TAC hw_trans_dmv_lem >>
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

val abs_ca_trans_dmvalt_oblg = store_thm("abs_ca_trans_dmvalt_oblg", ``
!s m dl s' pa. 
    abs_ca_trans s m dl s' 
 /\ pa NOTIN adrs dl 
 /\ dCoh s.ms (writes dl)
        ==> 
    (dmvalt s'.ms T pa = dmvalt s.ms T pa)
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl`
  >| [(* empty *)
      FULL_SIMP_TAC std_ss [abs_ca_trans_def]
      >| [(* NOREQ *)
	  FULL_SIMP_TAC std_ss [hw_trans_cases, corereq_distinct]
	  ,
	  (* FREQ *)
	  FULL_SIMP_TAC std_ss [hw_trans_cases, corereq_distinct] >>
	  IMP_RES_TAC msca_FREQ_lem >>
	  MATCH_MP_TAC dmvalt_lem >>
	  RW_TAC std_ss [dw_def, M_def] >> ( METIS_TAC [] )
	 ]
      ,
      (* non-empty *)
      IMP_RES_TAC abs_ca_req_lem >>
      FULL_SIMP_TAC list_ss [] >>
      MATCH_MP_TAC hw_trans_dmvalt_lem >>
      EXISTS_TAC ``m:mode`` >>
      HINT_EXISTS_TAC >>
      RW_TAC std_ss [] >>
      CCONTR_TAC >>
      FULL_SIMP_TAC std_ss []
     ]
);

val abs_ca_trans_dmvalt_not_write_oblg = 
store_thm("abs_ca_trans_dmvalt_not_write_oblg", ``
!s m dl s' pa. 
    abs_ca_trans s m dl s'
 /\ pa IN adrs dl
 /\ pa NOTIN writes dl 
 /\ dCoh s.ms (writes dl)
        ==> 
    (dmvalt s'.ms T pa = dmvalt s.ms T pa)
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl`
  >| [(* empty *)
      FULL_SIMP_TAC std_ss [abs_ca_trans_def]
      >| [(* NOREQ *)
	  FULL_SIMP_TAC std_ss [hw_trans_cases, corereq_distinct]
	  ,
	  (* FREQ *)
	  FULL_SIMP_TAC std_ss [hw_trans_cases, corereq_distinct] >>
	  IMP_RES_TAC msca_FREQ_lem >>
	  MATCH_MP_TAC dmvalt_lem >>
	  RW_TAC std_ss [dw_def, M_def] >> ( METIS_TAC [] )
	 ]
      ,
      (* non-empty *)
      IMP_RES_TAC abs_ca_req_lem >>
      FULL_SIMP_TAC list_ss [] >> (
          FULL_SIMP_TAC std_ss [] >>
          IMP_RES_TAC writes_lem >>
          IMP_RES_TAC adrs_lem2 >>
          FULL_SIMP_TAC std_ss [] >>
          IMP_RES_TAC hw_trans_dmvalt_not_write_lem >>
          FULL_SIMP_TAC std_ss [Adr_def, Wreq_def, opd_def, PA_def]
      )
     ]
);

val abs_ca_trans_dcoh_write_oblg = store_thm("abs_ca_trans_dcoh_write_oblg", ``
!s m dl s' pa. 
    abs_ca_trans s m dl s'
 /\ (!d. MEM d dl ==> CA (opd d))
 /\ pa IN writes dl 
        ==> 
    dcoh s'.ms pa
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl`
  >| [(* empty *)
      FULL_SIMP_TAC list_ss [writes_def]
      ,
      (* non-empty *)
      IMP_RES_TAC abs_ca_req_lem >>
      FULL_SIMP_TAC list_ss []
      >| [(* DREQ *)
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC writes_lem2 >>
	  RES_TAC >>
	  FULL_SIMP_TAC std_ss [opd_def] >>
	  `Wreq (DREQ dop)` by ( ASM_REWRITE_TAC [Wreq_def] ) >>
	  `CAreq (DREQ dop)` by ( METIS_TAC [CAreq_def, opd_def] ) >>
	  IMP_RES_TAC hw_trans_dcoh_write_lem >>
	  REV_FULL_SIMP_TAC std_ss [Adr_def]
	  ,
	  (* ICFR *)
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC writes_lem2 >>
	  FULL_SIMP_TAC std_ss [wt_def, opd_def]
	 ]
     ]
);

val abs_ca_trans_dcoh_flush_oblg = store_thm("abs_ca_trans_dcoh_flush_oblg", ``
!s m dl s' pa. abs_ca_trans s m dl s' /\ pa IN dcleans dl ==> 
    dcoh s'.ms pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC abs_ca_req_lem >>
  Cases_on `dl = []`
  >| [(* Fetch or NOREQ *)
      FULL_SIMP_TAC list_ss [dcleans_def]
      ,
      (* Dreq or Ireq *)
      FULL_SIMP_TAC std_ss []
      >| [(* Dreq *)
          FULL_SIMP_TAC std_ss [] >>
	  `Creq req /\ (Adr req = pa)` by (
	      FULL_SIMP_TAC std_ss [] >>
	      IMP_RES_TAC dcleans_lem >>
	      FULL_SIMP_TAC std_ss [Creq_def, PA_def, opd_def, Adr_def]
	  ) >>
          REV_FULL_SIMP_TAC std_ss [] >>
          IMP_RES_TAC hw_trans_dcoh_flush_lem >>
	  REV_FULL_SIMP_TAC std_ss []
	  ,
	  (* Ireq *)
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC dcleans_lem >>
	  FULL_SIMP_TAC std_ss [ifl_def]
	 ]
     ]
);

val abs_ca_trans_dCoh_preserve_oblg = 
store_thm("abs_ca_trans_dCoh_preserve_oblg", ``
!s m dl s' As. 
    dCoh s.ms As
 /\ (!d. MEM d dl ==> CA (opd d))
 /\ abs_ca_trans s m dl s' 
        ==> 
    dCoh s'.ms As
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC abs_ca_req_lem >>
  Cases_on `dl = []`
  >| [(* empty *)
      FULL_SIMP_TAC std_ss [dCoh_lem2] 
      >| [(* FREQ *)
	  REPEAT STRIP_TAC >>
	  IMP_RES_TAC Freq_lem >>
          RES_TAC >>
	  FULL_SIMP_TAC std_ss [] >>
	  `~Wreq (FREQ pa')` by ( REWRITE_TAC [Wreq_def] ) >>
	  IMP_RES_TAC hw_trans_dcoh_not_write_lem
	  ,
	  (* NOREQ *)
	  REPEAT STRIP_TAC >>
          RES_TAC >>
	  FULL_SIMP_TAC std_ss [] >>
	  `~Wreq NOREQ` by ( REWRITE_TAC [Wreq_def] ) >>
	  IMP_RES_TAC hw_trans_dcoh_not_write_lem
	 ]
      ,
      (* non-empty *)
      FULL_SIMP_TAC list_ss [] >> (
          `CAreq req` by ( FULL_SIMP_TAC list_ss [CAreq_def, opd_def] ) >>
	  IMP_RES_TAC hw_trans_dCoh_preserve_lem
      )
     ]
);

val abs_ca_trans_clean_oblg = store_thm("abs_ca_trans_clean_oblg", ``
!s m dl s' pa. abs_ca_trans s m dl s' /\ pa IN dcleans dl ==> 
    clean s'.ms pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  `~dirty s'.ms pa` suffices_by (
      RW_TAC std_ss [clean_not_dirty_lem]
  ) >>
  IMP_RES_TAC abs_ca_req_lem >>
  Cases_on `dl = []`
  >| [(* Fetch or NOREQ *)
      FULL_SIMP_TAC list_ss [dcleans_def]
      ,
      (* Dreq or Ireq *)
      FULL_SIMP_TAC std_ss []
      >| [(* Dreq *)
          FULL_SIMP_TAC std_ss [] >>
	  `Creq req /\ (Adr req = pa)` by (
	      FULL_SIMP_TAC std_ss [] >>
	      IMP_RES_TAC dcleans_lem >>
	      FULL_SIMP_TAC std_ss [Creq_def, PA_def, opd_def, Adr_def]
	  ) >>
          REV_FULL_SIMP_TAC std_ss [] >>
          IMP_RES_TAC hw_trans_clean_flush_lem >>
	  REV_FULL_SIMP_TAC std_ss []
	  ,
	  (* Ireq *)
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC dcleans_lem >>
	  FULL_SIMP_TAC std_ss [ifl_def]
	 ]
     ]
);

val abs_ca_trans_clean_preserve_oblg = 
store_thm("abs_ca_trans_clean_preserve_oblg", ``
!s m dl s' pa. abs_ca_trans s m dl s' 
            /\ pa NOTIN writes dl 
            /\ dcoh s.ms pa 
            /\ clean s.ms pa 
        ==> 
    clean s'.ms pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC abs_ca_req_lem >>
  Cases_on `dl = []`
  >| [(* Fetch or NOREQ *)
      FULL_SIMP_TAC list_ss [writes_def] >> (
	  `~Wreq req` by ( METIS_TAC [Freq_lem, Wreq_def] ) >>
	  METIS_TAC [hw_trans_clean_preserve_lem]
      )
      ,
      (* Dreq or Ireq *)
      FULL_SIMP_TAC std_ss []
      >| [(* Dreq *)
          FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC writes_lem >>
	  `Wreq (DREQ dop) ==> pa <> Adr (DREQ dop)` by (
	      FULL_SIMP_TAC std_ss [Wreq_def, opd_def, Adr_def]
	  ) >>
	  METIS_TAC [hw_trans_clean_preserve_lem]
	  ,
	  (* Ireq *)
	  `~Wreq req` by ( METIS_TAC [Wreq_def] ) >>
	  METIS_TAC [hw_trans_clean_preserve_lem]	  
	 ]
     ]
);

val abs_ca_trans_drvbl_oblg = store_thm("abs_ca_trans_drvbl_oblg", ``
!s dl s'. abs_ca_trans s USER dl s' ==> drvbl s s'
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC abs_ca_req_lem >>
  IMP_RES_TAC drvbl_lem
);

val abs_ca_trans_switch_oblg = store_thm("abs_ca_trans_switch_oblg", ``
!s dl s'. abs_ca_trans s USER dl s' ∧ (mode s' = PRIV) ⇒ exentry s'
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC abs_ca_req_lem >>
  IMP_RES_TAC hw_trans_switch_lem
);

val abs_ca_progress_oblg = store_thm("abs_ca_progress_oblg", ``
!s. ?dl s'. abs_ca_trans s (mode s) dl s'
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC ( SPEC ``s:hw_state`` hw_trans_progress_lem ) >>
  FULL_SIMP_TAC std_ss [] >>
  Cases_on `req`
  >| [(* DREQ *)
      EXISTS_TAC ``[DOP d:mop]`` >>
      EXISTS_TAC ``s':hw_state`` >>
      RW_TAC std_ss [abs_ca_trans_def]
      ,
      (* FREQ *)
      EXISTS_TAC ``[]:mop list`` >>
      EXISTS_TAC ``s':hw_state`` >>
      RW_TAC std_ss [abs_ca_trans_def] >>
      METIS_TAC []
      ,
      (* ICFR *)
      EXISTS_TAC ``[IFL p:mop]`` >>
      EXISTS_TAC ``s':hw_state`` >>
      RW_TAC std_ss [abs_ca_trans_def]
      ,
      (* NOREQ *)
      EXISTS_TAC ``[]:mop list`` >>
      EXISTS_TAC ``s':hw_state`` >>
      RW_TAC std_ss [abs_ca_trans_def] >>
      METIS_TAC []
     ]
);

val abs_ca_trans_icoh_clean_preserve_oblg = 
store_thm("abs_ca_trans_icoh_clean_preserve_oblg", ``
!s m dl s' pa. 
    abs_ca_trans s m dl s'
 /\ pa NOTIN writes dl
 /\ dcoh s.ms pa
 /\ icoh s.ms pa
 /\ clean s.ms pa
        ==> 
    icoh s'.ms pa
 /\ clean s'.ms pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC abs_ca_req_lem >>
  Cases_on `dl = []`
  >| [(* Freq or NOREQ *)
      `~Wreq req` by (
          FULL_SIMP_TAC std_ss []
	  >| [(* fetch *)
	      IMP_RES_TAC Freq_lem >>
	      ASM_REWRITE_TAC [Wreq_def]
	      ,
	      (* NOREQ *)
	      REWRITE_TAC [Wreq_def]
	     ]
      ) >>
      METIS_TAC [hw_trans_icoh_clean_preserve_lem]
      ,
      (* Dreq or Ireq *)
      FULL_SIMP_TAC std_ss [] >> (
          FULL_SIMP_TAC list_ss [] >>
          IMP_RES_TAC writes_lem >>
          `Wreq req ==> pa <> Adr req` by (
              FULL_SIMP_TAC std_ss [Wreq_def, Adr_def, opd_def]
          ) >>
          METIS_TAC [hw_trans_icoh_clean_preserve_lem]
      )
     ]
);

val abs_ca_trans_icoh_flush_oblg = store_thm("abs_ca_trans_icoh_flush_oblg", ``
!s m dl s' pa. 
    abs_ca_trans s m dl s'
 /\ pa IN icleans dl
        ==> 
    icoh s'.ms pa
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC abs_ca_req_lem >>
  Cases_on `dl = []`
  >| [(* Freq or NOREQ *)
      FULL_SIMP_TAC list_ss [icleans_def]
      ,
      (* Dreq or Ireq *)
      FULL_SIMP_TAC std_ss []
      >| [(* Dreq *)
	  FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC icleans_lem >>
	  FULL_SIMP_TAC std_ss [ifl_def]
	  ,
	  (* Ireq *)
          FULL_SIMP_TAC std_ss [] >>
	  `Ireq req` by ( FULL_SIMP_TAC std_ss [Ireq_def] ) >>
	  `Adr req = pa` by (
	      FULL_SIMP_TAC std_ss [] >>
	      IMP_RES_TAC icleans_lem >>
	      FULL_SIMP_TAC std_ss [PA_def, opd_def, Adr_def]
	  ) >>
          IMP_RES_TAC hw_trans_icoh_flush_lem >>
	  REV_FULL_SIMP_TAC std_ss []
	 ]
     ]
);

val abs_ca_trans_clean_disj_oblg = store_thm("abs_ca_trans_clean_disj_oblg", ``
!s m dl s'. 
    abs_ca_trans s m dl s'
        ==> 
    DISJOINT (dcleans dl) (icleans dl)
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl = []`
  >| [(* Freq or NOREQ *)
      RW_TAC list_ss [dcleans_def, icleans_def, pred_setTheory.DISJOINT_EMPTY]
      ,
      (* Dreq or Ireq *)
      IMP_RES_TAC abs_ca_req_lem >>
      REV_FULL_SIMP_TAC std_ss []
      >| [(* Dreq *)
	  RW_TAC list_ss [icleans_def]
	  >| [(* ifl dop -> contradiction *)
	      FULL_SIMP_TAC std_ss [ifl_def]
	      ,
	      (* empty *)
	      REWRITE_TAC [pred_setTheory.DISJOINT_EMPTY]
	     ]
	  ,
	  (* Ireq *)
	  RW_TAC list_ss [dcleans_def]
	  >| [(* ifl dop -> contradiction *)
	      FULL_SIMP_TAC std_ss [ifl_def]
	      ,
	      (* empty *)
	      REWRITE_TAC [pred_setTheory.DISJOINT_EMPTY]
	     ]
	 ]
     ]
);

val abs_ca_trans_i_w_disj_oblg = store_thm("abs_ca_trans_i_w_disj_oblg", ``
!s m dl s'. 
    abs_ca_trans s m dl s'
        ==> 
    DISJOINT (writes dl) (icleans dl)
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl = []`
  >| [(* Freq or NOREQ *)
      RW_TAC list_ss [dcleans_def, icleans_def, pred_setTheory.DISJOINT_EMPTY]
      ,
      (* Dreq or Ireq *)
      IMP_RES_TAC abs_ca_req_lem >>
      REV_FULL_SIMP_TAC std_ss []
      >| [(* Dreq *)
	  RW_TAC list_ss [icleans_def]
	  >| [(* ifl dop -> contradiction *)
	      FULL_SIMP_TAC std_ss [ifl_def]
	      ,
	      (* empty *)
	      REWRITE_TAC [pred_setTheory.DISJOINT_EMPTY]
	     ]
	  ,
	  (* Ireq *)
	  RW_TAC list_ss [writes_def]
	  >| [(* ifl dop -> contradiction *)
	      FULL_SIMP_TAC std_ss [ifl_def, opd_def, wt_def]
	      ,
	      (* empty *)
	      REWRITE_TAC [pred_setTheory.DISJOINT_EMPTY]
	     ]
	 ]
     ]
);

val hw_state_comp_eq = store_thm("hw_state_comp_eq", ``
!s s'. (s = s') <=> (s.cs = s'.cs) /\ (s.ms = s'.ms)
``,
  REPEAT GEN_TAC >>
  ASSUME_TAC (SPEC ``s:hw_state``(TypeBase.nchotomy_of ``:hw_state``)) >>
  ASSUME_TAC (SPEC ``s':hw_state``(TypeBase.nchotomy_of ``:hw_state``)) >>
  FULL_SIMP_TAC std_ss (TypeBase.accessors_of ``:hw_state``) >>
  RW_TAC std_ss [TypeBase.one_one_of ``:hw_state``]
);

val abs_ca_unique_oblg = store_thm("abs_ca_unique_oblg", ``
!s m dl dl' s' s''. abs_ca_trans s m dl s' /\ abs_ca_trans s m dl' s'' ==>
    (s'' = s') /\ (dl' = dl)
``,
  NTAC 7 STRIP_TAC >>
  IMP_RES_TAC abs_ca_req_lem >>
  `req' = req` by (
      IMP_RES_TAC hw_trans_core_req_lem >>
      IMP_RES_TAC core_req_det_lem
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  Cases_on `dl = []` 
  >| [(* Fetch or NOREQ *)
      Cases_on `dl' = []`
      >| [(* Fetch or NOREQ *)
	  Cases_on `Freq req'`
	  >| [(* Fetch *)
	      IMP_RES_TAC Freq_lem >>
	      REV_FULL_SIMP_TAC std_ss [corereq_distinct] >> 
	      FULL_SIMP_TAC std_ss [] >>
	      IMP_RES_TAC hw_trans_fetch_lem >>
	      IMP_RES_TAC core_req_det_lem >>
	      RW_TAC std_ss [] >>
	      IMP_RES_TAC core_rcv_det_lem >>
	      METIS_TAC [hw_state_comp_eq]
	      ,
	      (* NOREQ *)
	      REV_FULL_SIMP_TAC std_ss [corereq_distinct] >> 
	      FULL_SIMP_TAC std_ss [] >> 
	      IMP_RES_TAC hw_trans_noreq_lem >>
	      IMP_RES_TAC core_req_det_lem >>
	      METIS_TAC [hw_state_comp_eq]
	      ]
	  ,
	  (* no match -> contradiction *)
	  METIS_TAC [corereq_distinct, Freq_lem]
	 ]
      ,
      Cases_on `dl' = []`
      >| [(* no match -> contradiction *)
	  FULL_SIMP_TAC std_ss [Freq_lem, corereq_distinct] >> (
	      FULL_SIMP_TAC std_ss [corereq_distinct, Freq_def]
	  )
	  ,
	  (* DREQ or ICFR *)
	  Cases_on `?dop. req = DREQ dop`
	  >| [(* DREQ *)
	      FULL_SIMP_TAC std_ss [corereq_distinct] >> (
	          FULL_SIMP_TAC std_ss [corereq_distinct, mop_11, corereq_11]
	      ) >>
	      RW_TAC std_ss [] >>
	      Cases_on `dop`
	      >| [(* read *)
		  IMP_RES_TAC hw_trans_read_lem >>
		  FULL_SIMP_TAC std_ss [Rreq_def, rd_def] >>
		  IMP_RES_TAC core_req_det_lem >>
		  RW_TAC std_ss [] >>
		  IMP_RES_TAC core_rcv_det_lem >>
		  METIS_TAC [hw_state_comp_eq]
		  ,
		  (* write *)
		  IMP_RES_TAC hw_trans_write_lem >>
		  FULL_SIMP_TAC std_ss [Wreq_def, wt_def] >>
		  IMP_RES_TAC core_req_det_lem >>
		  METIS_TAC [hw_state_comp_eq]
		  ,
		  (* clean *)
		  IMP_RES_TAC hw_trans_clean_lem >>
		  FULL_SIMP_TAC std_ss [Creq_def, cl_def] >>
		  IMP_RES_TAC core_req_det_lem >>
		  METIS_TAC [hw_state_comp_eq]
		 ]
	      ,
	      (* ICFR *)
	      FULL_SIMP_TAC std_ss [corereq_distinct] >> (
	          FULL_SIMP_TAC std_ss [corereq_distinct, mop_11, corereq_11]
	      ) >>
	      RW_TAC std_ss [] >>
	      IMP_RES_TAC hw_trans_flush_lem >>
	      FULL_SIMP_TAC std_ss [Ireq_def] >>
	      IMP_RES_TAC core_req_det_lem >>
	      METIS_TAC [hw_state_comp_eq]
	     ]	      
	 ]
     ]
);

(* dependencies *)

val ca_Tr_def = Define `ca_Tr s va = Tr_ s.cs (dmvca s.ms) va`;

val ca_vdeps_def = Define `ca_vdeps s = vdeps_ s.cs`;

val ca_vdeps_PC_oblg = store_thm("ca_vdeps_PC_oblg", ``
!s. VApc s.cs IN ca_vdeps s
``,
  RW_TAC std_ss [ca_vdeps_def, vdeps_PC_lem]
);

val ca_deps_def = Define `ca_deps s = deps_ s.cs (dmvca s.ms)`;

val ca_deps_pc_oblg = store_thm("ca_deps_pc_oblg", ``
!s. ca_Tr s (VApc s.cs) IN ca_deps s
``,
  RW_TAC std_ss [ca_Tr_def, ca_deps_def, coreIfTheory.deps__def] >>
  REWRITE_TAC [pred_setTheory.IN_UNION] >>
  DISJ1_TAC >>
  RW_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
  EXISTS_TAC ``VApc s.cs`` >>
  REWRITE_TAC [coreIfTheory.vdeps_spec]
);

val ca_deps_vdeps_oblg = store_thm("ca_deps_vdeps_oblg", ``
!s. ca_deps s SUBSET ({pa | ?va. (pa = ca_Tr s va) /\ va IN ca_vdeps s} UNION
                      {pa | MEM pa IN MDVA s (ca_vdeps s)})
``,
  RW_TAC std_ss [ca_deps_def, coreIfTheory.deps__def] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF, pred_setTheory.IN_UNION] >>
  REPEAT STRIP_TAC
  >| [(* vdeps *)
      DISJ1_TAC >>
      RW_TAC std_ss [ca_vdeps_def, ca_Tr_def] >>
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC []
      ,
      (* MEM pa *)
      DISJ2_TAC >>
      RW_TAC std_ss [ca_vdeps_def, MDVA_def]
     ]
);

val ca_deps_MD_oblg = store_thm("ca_deps_MD_oblg", ``
!s pa. MEM pa IN MDVA s (ca_vdeps s) ==> pa IN ca_deps s
``,
  RW_TAC std_ss [ca_deps_def, ca_vdeps_def, MDVA_def,
		 coreIfTheory.deps__def] >>
  REWRITE_TAC [pred_setTheory.IN_UNION] >>
  DISJ2_TAC >>
  RW_TAC std_ss [pred_setTheory.IN_GSPEC_IFF]
);

val ca_deps_reads_oblg = store_thm("ca_deps_reads_oblg", ``
!s m dl s' pa. abs_ca_trans s m dl s' /\ pa IN reads dl ==> pa IN ca_deps s
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
	  FULL_SIMP_TAC std_ss [abs_ca_trans_def] >>
	  REV_FULL_SIMP_TAC list_ss [] >>
	  IMP_RES_TAC reads_lem >>
          IMP_RES_TAC hw_trans_core_req_lem >>
          IMP_RES_TAC core_req_curr_mode_lem >>
          `Dreq (DREQ d)` by ( FULL_SIMP_TAC std_ss [Dreq_def, opd_def] ) >>
          IMP_RES_TAC core_req_mmu_Dreq_lem >>
          RW_TAC std_ss [ca_deps_def, coreIfTheory.deps__def, 
           		 pred_setTheory.IN_UNION] >>
          DISJ1_TAC >>
          `~wt d` by ( FULL_SIMP_TAC std_ss [not_wt_lem, opd_def] ) >>
          FULL_SIMP_TAC std_ss [Acc_def, Adr_def, opd_def] >>
          RW_TAC std_ss [pred_setTheory.IN_GSPEC_IFF, coreIfTheory.Tr__def] >>
          HINT_EXISTS_TAC >>
          RW_TAC std_ss []
	  ,
	  (* Ireq *)
	  FULL_SIMP_TAC std_ss [abs_ca_trans_def] >>
	  REV_FULL_SIMP_TAC list_ss [] >>
	  IMP_RES_TAC reads_lem >>
	  FULL_SIMP_TAC std_ss [rd_def, opd_def]
	 ]
     ]
);

val ca_deps_writes_oblg = store_thm("ca_deps_writes_oblg", ``
!s m dl s' pa. abs_ca_trans s m dl s' /\ pa IN writes dl ==> pa IN ca_deps s
``,
  REPEAT STRIP_TAC >>
  Cases_on `dl` 
  >| [(* empty *)
      FULL_SIMP_TAC std_ss [writes_def, listTheory.FILTER, listTheory.MAP, 
			    listTheory.MEM]
      ,
      (* non-empty *)
      Cases_on `h`
      >| [(* Dreq *)
	  FULL_SIMP_TAC std_ss [abs_ca_trans_def] >>
	  REV_FULL_SIMP_TAC list_ss [] >>
	  IMP_RES_TAC writes_lem2 >>
          IMP_RES_TAC hw_trans_core_req_lem >>
          IMP_RES_TAC core_req_curr_mode_lem >>
          `Dreq (DREQ d)` by ( FULL_SIMP_TAC std_ss [Dreq_def, opd_def] ) >>
          IMP_RES_TAC core_req_mmu_Dreq_lem >>
          RW_TAC std_ss [ca_deps_def, coreIfTheory.deps__def, 
           		 pred_setTheory.IN_UNION] >>
          DISJ1_TAC >>
          FULL_SIMP_TAC std_ss [Acc_def, Adr_def, opd_def] >>
          RW_TAC std_ss [pred_setTheory.IN_GSPEC_IFF, coreIfTheory.Tr__def] >>
          HINT_EXISTS_TAC >>
	  REV_FULL_SIMP_TAC std_ss [] >>
	  IMP_RES_TAC Mmu_write_read_lem >> 
	  RW_TAC std_ss []
	  ,
	  (* Ireq *)
	  FULL_SIMP_TAC std_ss [abs_ca_trans_def] >>
	  REV_FULL_SIMP_TAC list_ss [] >>
	  IMP_RES_TAC writes_lem2 >>
	  FULL_SIMP_TAC std_ss [wt_def, opd_def]
	 ]
     ]
);

val hw_trans_fetch_deps_lem = store_thm("hw_trans_fetch_deps_lem", ``
!s M req s'. Freq req /\ hw_trans s M req s' ==> Adr req IN ca_deps s
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Freq_lem >>
  RW_TAC std_ss [Adr_def] >>
  IMP_RES_TAC hw_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct]
  ) >>
  FULL_SIMP_TAC std_ss [corereq_11] >>
  RW_TAC std_ss [] >>
  IMP_RES_TAC core_req_mmu_Freq_lem >>
  IMP_RES_TAC Mmu_read_fetch_lem >>
  `pa = ca_Tr s (VApc s.cs)` by (
      RW_TAC std_ss [ca_Tr_def, Tr__def, Adr_def]
  ) >>
  RW_TAC std_ss [ca_deps_pc_oblg]
);

val hw_trans_fetch_pc_lem = store_thm("hw_trans_fetch_pc_lem", ``
!s M req s'. Freq req /\ hw_trans s M req s' ==>
    (Adr req = ca_Tr s (VApc s.cs))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Freq_lem >>
  RW_TAC std_ss [Adr_def] >>
  IMP_RES_TAC hw_trans_cases >> (
      FULL_SIMP_TAC std_ss [corereq_distinct]
  ) >>
  FULL_SIMP_TAC std_ss [corereq_11] >>
  RW_TAC std_ss [] >>
  IMP_RES_TAC core_req_mmu_Freq_lem >>
  IMP_RES_TAC Mmu_read_fetch_lem >>
  RW_TAC std_ss [ca_Tr_def, coreIfTheory.Tr__def, Adr_def]
);

(* fix translation for privileged mode *)

val ca_fixmmu_def = Define `ca_fixmmu s VAs f = 
!va. va IN VAs ==> 
     (Mmu s va PRIV R = SOME (f va, T))
  /\ (!pa c. (Mmu s va PRIV W = SOME (pa,c)) ==> (pa = f va) /\ c)
  /\ (!pa c. (Mmu s va PRIV EX = SOME (pa,c)) ==> (pa = f va) /\ c)
`;

val ca_fixmmu_Tr_oblg = store_thm("ca_fixmmu_Tr_oblg", ``
!s VAs va f. ca_fixmmu s VAs f /\ va IN VAs /\ (mode s = PRIV) ==> 
    (ca_Tr s va = f va)
``,
  REWRITE_TAC [ca_fixmmu_def, ca_Tr_def, Mmu_def, mode_def, Tr__def] >>
  REPEAT STRIP_TAC >>
  RES_TAC >>
  ASM_REWRITE_TAC [optionTheory.THE_DEF, pairTheory.FST]
);

val ca_fixmmu_MD_lem = store_thm("ca_fixmmu_MD_lem", ``
!s s' VAs f. 
    ca_fixmmu s VAs f 
 /\ (!r. r IN MDVA s VAs ==> (Cv s r = Cv s' r))
	==>
    ca_fixmmu s' VAs f
``,
  REWRITE_TAC [ca_fixmmu_def, Mmu_def, Cv_def, MDVA_def] >>
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC Mmu_lem >>
  METIS_TAC []
);

(******** cacheaware computation ********)

val (ca_kcomp_rules, ca_kcomp_ind, ca_kcomp_cases) = Hol_reln `
   (!s. exentry s ==> ca_kcomp s s 0)
/\ (!s s' s'' n. ca_kcomp s s' n /\ (?dl. abs_ca_trans s' PRIV dl s'')
        ==>
    ca_kcomp s s'' (SUC n))
`;

val ca_kcomp_exentry_lem = store_thm("ca_kcomp_exentry_lem", ``
!s s' n. ca_kcomp s s' n ==> exentry s
``,
  Induct_on `n` 
  >| [(* n = 0 *)
      ONCE_REWRITE_TAC [ca_kcomp_cases] >>
      REPEAT STRIP_TAC >>
      FULL_SIMP_TAC std_ss [numTheory.NOT_SUC]
      ,
      (* n -> SUC n *)
      ONCE_REWRITE_TAC [ca_kcomp_cases] >>
      REPEAT STRIP_TAC >>
      FULL_SIMP_TAC std_ss [numTheory.INV_SUC] >>
      RW_TAC std_ss [] >>
      RES_TAC
     ]
);

val ca_kcomp_0_lem = store_thm("ca_kcomp_0_lem", ``
!s s'. ca_kcomp s s' 0 ==> exentry s /\ (s' = s)
``,
  ONCE_REWRITE_TAC [ca_kcomp_cases] >>
  FULL_SIMP_TAC std_ss [numTheory.NOT_SUC]
);

val ca_kcomp_SUC_lem = store_thm("ca_kcomp_SUC_lem", ``
!s s' n. 
ca_kcomp s s' (SUC n) 
    <=> 
?s'' dl. ca_kcomp s s'' n /\ abs_ca_trans s'' PRIV dl s'
``,
  REPEAT STRIP_TAC >>
  EQ_TAC 
  >| [(* ==> *)
      STRIP_TAC >>
      IMP_RES_TAC ca_kcomp_cases >> (
          FULL_SIMP_TAC std_ss [numTheory.NOT_SUC]
      ) >>
      METIS_TAC []
      ,
      (* <== *)
      STRIP_TAC >>
      ONCE_REWRITE_TAC [ca_kcomp_cases] >>
      FULL_SIMP_TAC std_ss [numTheory.NOT_SUC] >>
      METIS_TAC []
     ]      
);

val ca_kcomp_shorten_lem = store_thm("ca_kcomp_shorten_lem", ``
!s s' n m. ca_kcomp s s' n /\ m < n ==> 
    ?s''. ca_kcomp s s'' m /\ (mode s'' = PRIV)
``,
  Induct_on `n` 
  >| [(* n = 0 *)
      FULL_SIMP_TAC arith_ss []
      ,
      (* n -> SUC n *)
      RW_TAC std_ss [ca_kcomp_SUC_lem] >>
      IMP_RES_TAC abs_ca_trans_mode_oblg >>
      Cases_on `m = n`
      >| [(* m = n *)
	  METIS_TAC []
	  ,
	  (* m <> n *)
	  `m < n` by ( DECIDE_TAC ) >>
	  RES_TAC >>
	  METIS_TAC []
	 ]	  
     ]      
);


val ca_wrel_def = Define` ca_wrel s s' n = 
ca_kcomp s s' n /\ (mode s' = USER)`;

val ca_wrel_exentry_lem = store_thm("ca_wrel_exentry_lem", ``
!s s' n. ca_wrel s s' n ==> exentry s
``,
  RW_TAC std_ss [ca_wrel_def] >>
  IMP_RES_TAC ca_kcomp_exentry_lem
);

val ca_wrel_mode_lem = store_thm("ca_wrel_mode_lem", ``
!s s' n. ca_wrel s s' n ==> (mode s = PRIV) /\ (mode s' = USER)
``,
  RW_TAC std_ss [ca_wrel_def] >>
  IMP_RES_TAC ca_kcomp_exentry_lem >>
  FULL_SIMP_TAC std_ss [exentry_def, mode_def, exentry_spec]
);


(*********** finish ************)

val _ = export_theory();
