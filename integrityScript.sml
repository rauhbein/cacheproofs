(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open hwTheory;
open InvIfTheory;
open cachelessTheory;
open histTheory;

val _ = new_theory "integrity";

(******** import Inv interface ********)

val CR_lem = store_thm("CR_lem", ``
!s s'. Ifun s /\ (!r. r IN CR s ==> (Cv s r = Cv s' r)) ==> (CR s = CR s')
``,
  REWRITE_TAC [CR_oblg]
);

val CR_coreg_lem = store_thm("CR_coreg_lem", ``
!s s' r. Ifun s /\ reg_res r /\ r IN CR s /\ (s'.cs.coreg = s.cs.coreg) ==> 
    (Cv s r = Cv s' r) 
``,
  REWRITE_TAC [CR_coreg_oblg]
);

val CRex_eq_lem = store_thm("CRex_eq_lem", ``
!s s'. Ifun s /\ (!r. r IN CR s ==> (Cv s r = Cv s' r)) ==> (CRex s = CRex s')
``,
  REWRITE_TAC [CRex_eq_oblg]
);

val CRex_lem = store_thm("CRex_lem", ``
!s r. Ifun s /\ r IN CRex s ==> (?pa. (r = MEM pa)) /\ r IN CR s
``,
  REWRITE_TAC [CRex_oblg]
);

val ca_fixmmu_Tr_lem = store_thm("ca_fixmmu_Tr_lem", ``
!s VAs va f. ca_fixmmu s VAs f /\ va IN VAs /\ (mode s = PRIV) ==> 
    (ca_Tr s va = f va)
``,
  REWRITE_TAC [ca_fixmmu_Tr_oblg]
);

val Ifun_CR_lem = store_thm("Ifun_CR_lem", ``
!s s'. (!r. r IN CR s ==> (Cv s r = Cv s' r)) ==> (Ifun s <=> Ifun s')
``,
  REWRITE_TAC [Ifun_CR_oblg]
); 

val Ifun_MD_lem = store_thm("Ifun_MD_lem", ``
!s r. Ifun s /\ r IN MD s ==> r IN CR s
``,
  REWRITE_TAC [Ifun_MD_oblg]
); 

val Ifun_Mon_lem = store_thm("Ifun_Mon_lem", ``
!s r. Ifun s /\ r IN CR s ==> ~Mon s r USER W
``,
  REWRITE_TAC [Ifun_Mon_oblg]
); 

val Icoh_CR_lem = store_thm("Icoh_CR_lem", ``
!s s' Icoh Icode Icm.
       cm_user_po Icoh Icode Icm  
    /\ Ifun s
    /\ dCoh s.ms {pa | MEM pa IN CR s} 
    /\ dCoh s'.ms {pa | MEM pa IN CR s'}
    /\ (!r. r IN CR s ==> (Cv s r = Cv s' r))
        ==>
    (Icoh s <=> Icoh s')
``,
  REWRITE_TAC [Icoh_CR_oblg]
); 

val Icoh_dCoh_lem = store_thm("Icoh_dCoh_lem", ``
!s Icoh Icode Icm. cm_user_po Icoh Icode Icm /\ Ifun s /\ Icoh s ==> 
    dCoh s.ms {pa | MEM pa IN CR s}
``,
  REWRITE_TAC [Icoh_dCoh_oblg]
); 

val Icode_CR_lem = store_thm("Icode_CR_lem", ``
!s s' Icoh Icode Icm. 
       cm_user_po Icoh Icode Icm
    /\ Ifun s
    /\ iCoh s.ms {pa | MEM pa IN CRex s}
    /\ iCoh s'.ms {pa | MEM pa IN CRex s'}
    /\ isafe s {pa | MEM pa IN CRex s}
    /\ isafe s' {pa | MEM pa IN CRex s'}
    /\ (!r. r IN CR s ==> (Cv s r = Cv s' r))
        ==>
    (Icode s <=> Icode s')
``,
  REPEAT STRIP_TAC >>
  `!r. r IN CRex s ==> (Cv s r = Cv s' r)` by (
      REPEAT STRIP_TAC >>
      IMP_RES_TAC CRex_lem >>
      RES_TAC
  ) >>
  IMP_RES_TAC Icode_CR_oblg
);

val Icode_iCoh_lem = store_thm("Icode_iCoh_lem", ``
!s Icoh Icode Icm. cm_user_po Icoh Icode Icm /\ Ifun s /\ Icode s ==> 
    iCoh s.ms {pa | MEM pa IN CRex s}
``,
  REWRITE_TAC [Icode_iCoh_oblg]
);

val Icode_isafe_lem = store_thm("Icode_isafe_lem", ``
!s Icoh Icode Icm. cm_user_po Icoh Icode Icm /\ Ifun s /\ Icode s ==> 
    isafe s {pa | MEM pa IN CRex s}
``,
  REWRITE_TAC [Icode_isafe_oblg]
);

val Icm_lem = store_thm("Icm_lem", ``
!s s' Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm 
 /\ Inv Icoh Icode Icm s
 /\ drvbl s s' 
        ==> 
    Icm s'
``,
  REWRITE_TAC [Icm_oblg]
); 

val Inv_lem = store_thm("Inv_lem", ``
!s Icoh Icode Icm. Inv Icoh Icode Icm s <=> Ifun s /\ Icoh s /\ Icode s /\ Icm s
``,
  REWRITE_TAC [Inv_oblg]
); 

val abs_ca_trans_mode_lem = store_thm("abs_ca_trans_mode_lem", ``
!s m dl s'. abs_ca_trans s m dl s' ==> (mode s = m) 
``,
  REWRITE_TAC [abs_ca_trans_mode_oblg]
);

val abs_ca_trans_dmvalt_lem = store_thm("abs_ca_trans_dmvalt_lem", ``
!s m dl s' pa. abs_ca_trans s m dl s' /\ pa NOTIN adrs dl ==> 
    (dmvalt s'.ms T pa = dmvalt s.ms T pa)
``,
  REWRITE_TAC [abs_ca_trans_dmvalt_oblg]
);

val abs_ca_trans_dmvalt_not_write_lem = 
store_thm("abs_ca_trans_dmvalt_not_write_lem", ``
!s m dl s' pa. abs_ca_trans s m dl s' /\ pa IN adrs dl /\ pa NOTIN writes dl 
        ==> 
    (dmvalt s'.ms T pa = dmvalt s.ms T pa)
``,
  REWRITE_TAC [abs_ca_trans_dmvalt_not_write_oblg]
);

val abs_ca_trans_dcoh_write_lem = store_thm("abs_ca_trans_dcoh_write_lem", ``
!s m dl s' pa. 
    abs_ca_trans s m dl s'
 /\ (!d. MEM d dl ==> CA (opd d))
 /\ pa IN writes dl 
        ==> 
    dcoh s'.ms pa
``,
  REWRITE_TAC [abs_ca_trans_dcoh_write_oblg]
);

val abs_ca_trans_dCoh_preserve_lem = 
store_thm("abs_ca_trans_dCoh_preserve_lem", ``
!s m dl s' As. 
    dCoh s.ms As
 /\ (!d. MEM d dl ==> CA (opd d))
 /\ abs_ca_trans s m dl s' 
        ==> 
    dCoh s'.ms As
``,
  REWRITE_TAC [abs_ca_trans_dCoh_preserve_oblg]
);

val abs_ca_trans_drvbl_lem = store_thm("abs_ca_trans_drvbl_lem", ``
!s dl s'. 
    abs_ca_trans s USER dl s'
 /\ (!pa. MEM pa IN MD s ==> ~Mon s (MEM pa) USER W)
 /\ (dCoh s.ms {pa | MEM pa IN MD s})
        ==> 
    drvbl s s'
``,
  METIS_TAC [abs_ca_trans_drvbl_oblg]
);

val abs_ca_trans_switch_lem = store_thm("abs_ca_trans_switch_lem", ``
!s dl s'. abs_ca_trans s USER dl s' /\ (mode s' = PRIV) ==> exentry s'
``,
  REWRITE_TAC [abs_ca_trans_switch_oblg]
);

val abs_ca_progress_lem = store_thm("abs_ca_progress_lem", ``
!s. ?dl s'. abs_ca_trans s (mode s) dl s'
``,
  REWRITE_TAC [abs_ca_progress_oblg]  
);

val abs_ca_trans_icoh_clean_preserve_lem = 
store_thm("abs_ca_trans_icoh_clean_preserve_lem", ``
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
  REWRITE_TAC [abs_ca_trans_icoh_clean_preserve_oblg]
);

val abs_cl_trans_mode_lem = store_thm("abs_cl_trans_mode_lem", ``
!s m dl s'. abs_cl_trans s m dl s' ==> (cl_mode s = m) 
``,
  REWRITE_TAC [abs_cl_trans_mode_oblg]
);

val abs_cl_trans_not_write_lem = store_thm("abs_cl_trans_not_write_lem", ``
!s m dl s' pa. abs_cl_trans s m dl s' /\ pa NOTIN writes dl ==> 
    (cl_Cv s' (MEM pa) = cl_Cv s (MEM pa))
``,
  REWRITE_TAC [abs_cl_trans_not_write_oblg]
);

val abs_cl_trans_not_adrs_lem = store_thm("abs_cl_trans_not_adrs_lem", ``
!s m dl s' pa. abs_cl_trans s m dl s' /\ pa NOTIN adrs dl ==> 
    (cl_Cv s' (MEM pa) = cl_Cv s (MEM pa))
``,
  REWRITE_TAC [abs_cl_trans_not_adrs_oblg]
);

val abs_cl_trans_fixmmu_CA_lem = store_thm("abs_cl_trans_fixmmu_CA_lem", ``
!s dl s' VAs f. 
    cl_fixmmu s VAs f 
 /\ cl_vdeps s SUBSET VAs 
 /\ abs_cl_trans s PRIV dl s' 
	==>
    !d. MEM d dl ==> CA (opd d)
``,
  REWRITE_TAC [abs_cl_trans_fixmmu_CA_oblg]
);

val abs_cl_progress_lem = store_thm("abs_cl_progress_lem", ``
!s. ?dl s'. abs_cl_trans s (cl_mode s) dl s'
``,
  REWRITE_TAC [abs_cl_progress_oblg]
);

val core_bisim_dl_lem = store_thm("core_bisim_dl_lem", ``
!s s' sc sc' m dl dlc. 
    abs_cl_trans s m dl s'
 /\ abs_ca_trans sc m dlc sc'
 /\ (s.cs = sc.cs)
 /\ (!pa. pa IN ca_deps sc ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
 /\ (cl_Cv s (MEM (cl_Tr s (VApc s.cs))) = imv sc.ms T (ca_Tr sc (VApc sc.cs)))
        ==>
    (dl = dlc)
``,
  METIS_TAC [core_bisim_dl_oblg]
);

val core_bisim_lem = store_thm("core_bisim_lem", ``
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
  REWRITE_TAC [core_bisim_oblg]
);

val ca_deps_pc_lem = store_thm("ca_deps_pc_lem", ``
!s. ca_Tr s (VApc s.cs) IN ca_deps s
``,
  REWRITE_TAC [ca_deps_pc_oblg]
);

val deps_eq_lem = store_thm("deps_eq_lem", ``
!s sc. (s.cs = sc.cs)
    /\ (!pa. pa IN ca_deps sc ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (cl_deps s = ca_deps sc)
``,
  REWRITE_TAC [deps_eq_oblg]
);

val cl_deps_eq_lem = store_thm("cl_deps_eq_lem", ``
!s sc. (s.cs = sc.cs)
    /\ (!pa. pa IN cl_deps s ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (cl_deps s = ca_deps sc)
``,
  REWRITE_TAC [cl_deps_eq_oblg]
);

val ca_vdeps_PC_lem = store_thm("ca_vdeps_PC_lem", ``
!s. VApc s.cs IN ca_vdeps s
``,
  REWRITE_TAC [ca_vdeps_PC_oblg]
);

val deps_vdeps_eq_lem = store_thm("deps_vdeps_eq_lem", ``
!s sc. (s.cs = sc.cs)
    /\ (!pa. pa IN ca_deps sc ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
        ==>
    (cl_vdeps s = ca_vdeps sc)
``,
  REWRITE_TAC [deps_vdeps_eq_oblg]
);

(******** top level proof ********)

(* user integrity *)

val Inv_MD_Coh_lem = store_thm("Inv_MD_Coh_lem", ``
!s Icoh Icode Icm. cm_user_po Icoh Icode Icm /\ Inv Icoh Icode Icm s ==> 
    dCoh s.ms {pa | MEM pa IN MD s}
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Icoh_dCoh_lem >>
  FULL_SIMP_TAC std_ss [dCoh_lem2, pred_setTheory.IN_GSPEC_IFF] >>
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Ifun_MD_lem >>
  RES_TAC
);

val Inv_MD_not_writable_lem = store_thm("Inv_MD_not_writable_lem", ``
!s Icoh Icode Icm. cm_user_po Icoh Icode Icm /\ Inv Icoh Icode Icm s ==> 
    (!pa. MEM pa IN MD s ==> ~Mon s (MEM pa) USER W)
``,
  REPEAT GEN_TAC >>
  NTAC 3 STRIP_TAC >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Ifun_Mon_lem >>
  IMP_RES_TAC Ifun_MD_lem >>
  RES_TAC
);

val Inv_drvbl_lem = store_thm("Inv_drvbl_lem", ``
!s Icoh Icode Icm dl s'. 
    cm_user_po Icoh Icode Icm 
 /\ Inv Icoh Icode Icm s 
 /\ abs_ca_trans s USER dl s'
        ==> 
    drvbl s s'
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Inv_MD_not_writable_lem >>
  IMP_RES_TAC Inv_MD_Coh_lem >>
  IMP_RES_TAC abs_ca_trans_drvbl_lem
);


val Inv_CRex_dCoh_lem = store_thm("Inv_CRex_dCoh_lem", ``
!s Icoh Icode Icm. cm_user_po Icoh Icode Icm /\ Inv Icoh Icode Icm s ==> 
    dCoh s.ms {pa | MEM pa IN CRex s}
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Icoh_dCoh_lem >>
  `{pa | MEM pa IN CRex s} SUBSET {pa | MEM pa IN CR s}` by (
      RW_TAC std_ss [pred_setTheory.SUBSET_DEF] >>
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
      IMP_RES_TAC CRex_lem
  ) >>
  IMP_RES_TAC dCoh_subset_lem 
);

val Inv_safe_lem = store_thm("Inv_safe_lem", ``
!s Icoh Icode Icm. cm_user_po Icoh Icode Icm /\ Inv Icoh Icode Icm s ==> safe s
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC Mon_Coh_safe_lem >>
  IMP_RES_TAC Inv_MD_Coh_lem >>
  IMP_RES_TAC Inv_MD_not_writable_lem >>
  ASM_REWRITE_TAC []
);

val Inv_CR_unchanged_lem = store_thm("Inv_CR_unchanged_lem", ``
!s s' Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ drvbl s s'
        ==> 
    (!r. r IN CR s ==> (Cv s r = Cv s' r))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  MATCH_MP_TAC Cv_lem >>
  STRIP_TAC
  >| [(* regs equal *)
      RW_TAC std_ss [Cv_reg_eq_def] >>
      FULL_SIMP_TAC std_ss [drvbl_def, Inv_lem] >>
      IMP_RES_TAC CR_coreg_lem >>
      ASM_REWRITE_TAC []
      ,
      (* data core view of CR unchanged *)
      MATCH_MP_TAC drvbl_Coh_mem_lem >>
      FULL_SIMP_TAC std_ss [Inv_lem] >>
      IMP_RES_TAC Ifun_Mon_lem >>
      IMP_RES_TAC Icoh_dCoh_lem >>
      RW_TAC std_ss []
     ]
);

val Inv_CR_lem = store_thm("Inv_CR_lem", ``
!s s' Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ drvbl s s'
        ==> 
    (CR s' = CR s)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Inv_CR_unchanged_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC CR_lem >>
  ASM_REWRITE_TAC []
);

val Inv_Coh_CR_lem = store_thm("Inv_Coh_CR_lem", ``
!s s' Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ drvbl s s'
        ==> 
    dCoh s'.ms {pa | MEM pa IN CR s'}
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Inv_CR_lem >>
  ASM_REWRITE_TAC [] >>
  MATCH_MP_TAC drvbl_dCoh_lem >>
  HINT_EXISTS_TAC >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Ifun_Mon_lem >>
  IMP_RES_TAC Icoh_dCoh_lem >>
  RW_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF]
);

val Inv_Ifun_lem = store_thm("Inv_Ifun_lem", ``
!s s' req Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ abs_ca_trans s USER req s' 
        ==> 
    Ifun s' 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Inv_drvbl_lem >>
  IMP_RES_TAC Inv_CR_unchanged_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Ifun_CR_lem
);

val Inv_Icoh_lem = store_thm("Inv_Icoh_lem", ``
!s s' req Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ abs_ca_trans s USER req s' 
        ==> 
    Icoh s' 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Inv_drvbl_lem >>
  IMP_RES_TAC Inv_CR_unchanged_lem >>
  IMP_RES_TAC Inv_Coh_CR_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Icoh_dCoh_lem >>
  IMP_RES_TAC Icoh_CR_lem
);

val Inv_Mon_CR_lem = store_thm("Inv_Mon_CR_lem", ``
!s s' Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ (!r. r IN CR s ==> (Cv s r = Cv s' r)) 
        ==>
    !r m ac. Mon s r m ac <=> Mon s' r m ac
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC Mon_lem >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Ifun_MD_lem >>
  RES_TAC
);

val Inv_CRex_lem = store_thm("Inv_CRex_lem", ``
!s s' Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ drvbl s s' 
        ==> 
    (CRex s' = CRex s)
``,
  RW_TAC std_ss [] >>
  IMP_RES_TAC Inv_CR_unchanged_lem >>
  IMP_RES_TAC CRex_eq_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem]
);

val Inv_iCoh_lem = store_thm("Inv_iCoh_lem", ``
!s s' Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ drvbl s s' 
        ==> 
    iCoh s'.ms {pa | MEM pa IN CRex s'}
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Inv_CRex_lem >>
  ASM_REWRITE_TAC [] >>
  MATCH_MP_TAC drvbl_iCoh_lem >>
  HINT_EXISTS_TAC >>
  IMP_RES_TAC Inv_CRex_dCoh_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Ifun_Mon_lem >>
  IMP_RES_TAC Icode_iCoh_lem >>
  IMP_RES_TAC Icode_isafe_lem >>
  RW_TAC std_ss [] >>
  (* CRex not writable *)
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
  IMP_RES_TAC CRex_lem >>
  RES_TAC
);

val Inv_isafe_lem = store_thm("Inv_isafe_lem", ``
!s s' Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ drvbl s s' 
        ==> 
    isafe s' {pa | MEM pa IN CRex s'}
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Inv_CRex_lem >>
  ASM_REWRITE_TAC [] >>
  MATCH_MP_TAC drvbl_isafe_lem >>
  HINT_EXISTS_TAC >>
  IMP_RES_TAC Inv_safe_lem >>
  IMP_RES_TAC Inv_CRex_dCoh_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Ifun_Mon_lem >>
  IMP_RES_TAC Icode_isafe_lem >>
  RW_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
  IMP_RES_TAC CRex_lem >>
  RES_TAC
);

val Inv_Icode_lem = store_thm("Inv_Icode_lem", ``
!s s' req Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ abs_ca_trans s USER req s' 
        ==> 
    Icode s' 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Inv_drvbl_lem >>
  IMP_RES_TAC Inv_CR_unchanged_lem >>
  IMP_RES_TAC Inv_iCoh_lem >>
  IMP_RES_TAC Inv_isafe_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Icode_iCoh_lem >>
  IMP_RES_TAC Icode_isafe_lem >>
  IMP_RES_TAC Icode_CR_lem
);

val Inv_Icm_lem = store_thm("Inv_Icm_lem", ``
!s s' req Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ abs_ca_trans s USER req s' 
        ==> 
    Icm s' 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Inv_drvbl_lem >>
  IMP_RES_TAC Icm_lem
);

val Inv_user_preserved_lem = store_thm("Inv_user_preserved_lem", ``
!s s' req Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ abs_ca_trans s USER req s' 
        ==> 
    Inv Icoh Icode Icm s'
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Inv_Ifun_lem >>
  IMP_RES_TAC Inv_Icoh_lem >>
  IMP_RES_TAC Inv_Icode_lem >>
  IMP_RES_TAC Inv_Icm_lem >>
  RW_TAC std_ss [Inv_lem]
);

(* User Integrity Theorem *)

val Inv_user_preserved_thm = store_thm("Inv_user_preserved_thm", ``
!s s' req Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ abs_ca_trans s USER req s' 
        ==> 
    Inv Icoh Icode Icm s'
 /\ (!r. r IN CR s ==> (Cv s r = Cv s' r))
 /\ Cv_imv_eq s s' (CRex s)
 /\ ((mode s' = PRIV) ==> exentry s')
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC Inv_drvbl_lem >>
  IMP_RES_TAC Inv_CR_unchanged_lem >>
  IMP_RES_TAC abs_ca_trans_switch_lem >>
  RW_TAC std_ss [] >- ( IMP_RES_TAC Inv_user_preserved_lem ) >>
  MATCH_MP_TAC drvbl_iCoh_mem_lem >>
  IMP_RES_TAC Inv_CRex_dCoh_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Icode_iCoh_lem >>
  IMP_RES_TAC Icode_isafe_lem >>
  IMP_RES_TAC Ifun_Mon_lem >>
  RW_TAC std_ss [] >>
  IMP_RES_TAC CRex_lem >>
  RES_TAC
);

(*********** kernel integrity ************)

(* some more useful lemmas *)

val Rsim_deps_lem = store_thm("Rsim_deps_lem", ``
!sc s As. Rsim sc s /\ dCoh sc.ms As /\ ca_deps sc SUBSET As ==>
    (cl_deps s = ca_deps sc)
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC deps_eq_lem >>
  IMP_RES_TAC Rsim_cs_lem >>
  ASM_REWRITE_TAC [] >>
  IMP_RES_TAC Rsim_dCoh_Cv_lem >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF]
);

val Rsim_cl_deps_lem = store_thm("Rsim_cl_deps_lem", ``
!sc s As. Rsim sc s /\ dCoh sc.ms As /\ cl_deps s SUBSET As ==>
    (cl_deps s = ca_deps sc)
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC cl_deps_eq_lem >>
  IMP_RES_TAC Rsim_cs_lem >>
  ASM_REWRITE_TAC [] >>
  IMP_RES_TAC Rsim_dCoh_Cv_lem >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF]
);

val Rsim_deps_cnt_lem = store_thm("Rsim_deps_cnt_lem", ``
!sc s As. Rsim sc s /\ dCoh sc.ms As /\ ca_deps sc SUBSET As ==>
    (!pa. pa IN ca_deps sc ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_dCoh_Cv_lem >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF]
);

val Rsim_ca_step_lem = store_thm("Rsim_ca_step_lem", ``
!sc s m dl sc'.
    Rsim sc s
 /\ dCoh sc.ms (ca_deps sc) 
 /\ icoh sc.ms (ca_Tr sc (VApc sc.cs)) 
 /\ clean sc.ms (ca_Tr sc (VApc sc.cs)) 
 /\ abs_ca_trans sc m dl sc'
        ==>
    ?s'. abs_cl_trans s m dl s' 
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC ( SPEC ``s:cl_state`` abs_cl_progress_lem ) >> 
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Rsim_cs_lem >>
  `cl_mode s = m` by (
      IMP_RES_TAC abs_ca_trans_mode_lem >>
      FULL_SIMP_TAC std_ss [cl_mode_def, mode_def]
  ) >>
  IMP_RES_TAC Rsim_dCoh_Cv_lem >>
  FULL_SIMP_TAC std_ss [] >>
  `ca_Tr sc (VApc sc.cs) IN ca_deps sc` by (
      REWRITE_TAC [ca_deps_pc_lem]
  ) >>
  `VApc sc.cs IN ca_vdeps sc` by (
      REWRITE_TAC [ca_vdeps_PC_lem]
  ) >>
  `cl_Tr s (VApc s.cs) = ca_Tr sc (VApc sc.cs)` by (
      RW_TAC std_ss [] >>
      IMP_RES_TAC deps_Tr_eq_lem 
  ) >>
  `cl_Cv s (MEM (cl_Tr s (VApc s.cs))) = 
   imv sc.ms T (ca_Tr sc (VApc sc.cs))` by (
      RW_TAC std_ss [Cv_mem_lem] >>
      MATCH_MP_TAC EQ_SYM >>
      MATCH_MP_TAC imv_dmv_lem >>
      IMP_RES_TAC dCoh_lem >>
      ASM_REWRITE_TAC []
  ) >>
  IMP_RES_TAC core_bisim_dl_lem >>
  FULL_SIMP_TAC std_ss [] >>
  HINT_EXISTS_TAC >>
  ASM_REWRITE_TAC []
);

(* top level proof *)

(* simulating execution of kernel code preserve the invariant, if:
- Rsim holds initially and finally
- final access history variables are equivalent
- cache-less invariant holds initially and finally
- cache-aware invariant holds initially
- intermediate invariants hold finally on both models
 *)
val ca_Inv_rebuild_lem = store_thm("ca_Inv_rebuild_lem", ``
!s s' sc sc' Icoh Icode Icm cl_Icmf ca_Icmf cl_Icodef ca_Icodef n. 
    cm_user_po Icoh Icode Icm
 /\ cm_kernel_po cl_Icmf cl_Icodef ca_Icmf ca_Icodef Icoh Icode Icm
 /\ Inv Icoh Icode Icm sc
 /\ cl_Inv s
 /\ Rsim sc s
 /\ ca_wrel sc sc' n
 /\ cl_wrel s s' n
 /\ Rsim sc' s'
 /\ (!f. clh f s s' n = cah f sc sc' n)
 /\ cl_Inv s' 
 /\ ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc sc' n
 /\ cl_II cl_Icmf cl_Icodef s s' n
        ==>
    Inv Icoh Icode Icm sc'
``,
  RW_TAC std_ss [cm_kernel_po_def] >>
  IMP_RES_TAC cl_wrel_mode_lem >>
  IMP_RES_TAC cl_wrel_exentry_lem >>
  IMP_RES_TAC ca_wrel_mode_lem >>
  IMP_RES_TAC ca_wrel_exentry_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem, Inv_rebuild_po_def] >>
  METIS_TAC [Icm_f_po_def]
);

(* main bisimulation lemma (assuming proof obligations): 
GIVEN
- we start in simulating states
- initial invariants hold
- cache-less and cache-aware kernel computations of the same length
THEN
- the bisimulation relation is preserved
- intermediate invariants hold in the final states on both models
- all final state history variables are equivalent
*)
val kernel_bisim_lem = store_thm("kernel_bisim_lem", ``
!s s' sc sc' n Icoh Icode Icm cl_Icmf ca_Icmf cl_Icodef ca_Icodef. 
    cm_user_po Icoh Icode Icm
 /\ cm_kernel_po cl_Icmf cl_Icodef ca_Icmf ca_Icodef Icoh Icode Icm
 /\ cl_II_po cl_Icmf cl_Icodef
 /\ Rsim sc s
 /\ cl_Inv s 
 /\ Inv Icoh Icode Icm sc
 /\ cl_kcomp s s' n
 /\ ca_kcomp sc sc' n
        ==>
    Rsim sc' s'
 /\ cl_II cl_Icmf cl_Icodef s s' n
 /\ ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc sc' n
 /\ (!f. clh f s s' n = cah f sc sc' n)
``,
  Induct_on `n`
  >| [(* n = 0 *)
      REPEAT GEN_TAC >>
      STRIP_TAC >>
      IMP_RES_TAC cl_kcomp_0_lem >>
      IMP_RES_TAC ca_kcomp_0_lem >>
      IMP_RES_TAC cl_II_po_def >>
      FULL_SIMP_TAC std_ss [cm_kernel_po_def, cl_II_def] >>
      REV_FULL_SIMP_TAC std_ss [] >>
      `ca_Icmf sc sc 0` by ( IMP_RES_TAC Icmf_init_sim_lem ) >>
      RW_TAC std_ss [ca_II_def, clh_0_lem, cah_0_lem] >>
      IMP_RES_TAC Icodef_init_sim_lem
      ,
      (* n -> SUC n *)
      REPEAT GEN_TAC >>
      STRIP_TAC >>
      IMP_RES_TAC cl_II_po_def >>
      FULL_SIMP_TAC std_ss [cl_kcomp_SUC_lem, ca_kcomp_SUC_lem] >>
      `Rsim s''' s'' /\
       ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc s''' n /\
       (!f. clh f s s'' n = cah f sc s''' n)` by ( METIS_TAC [] ) >>
      MATCH_MP_TAC (
          prove(``(A /\ (dl':mop list = dl)) /\ (A /\ (dl' = dl) ==> C) /\ 
		  (A /\ (dl' = dl) /\ C ==> B ) ==> 
		  A /\ B /\ C``, PROVE_TAC [])
      ) >>
      STRIP_TAC >- (
          (* Rsim *)
	  FULL_SIMP_TAC std_ss [Rsim_cs_lem] >>
	  (* prepare for application of bisim lem *)
	  `dCoh s'''.ms (ca_deps s''')` by (
	      FULL_SIMP_TAC std_ss [cm_kernel_po_def, ca_II_def] >>
	      IMP_RES_TAC abs_ca_trans_mode_lem >>
	      FULL_SIMP_TAC std_ss [Inv_lem] >>
	      IMP_RES_TAC ca_Icmf_po_def
	  ) >>
	  `!pa. pa IN ca_deps s''' ==> 
           (cl_Cv s'' (MEM pa) = Cv s''' (MEM pa))` by (
	      RW_TAC std_ss [cl_Cv_mem_lem, Cv_mem_lem] >>
	      MATCH_MP_TAC EQ_SYM >>
	      FULL_SIMP_TAC std_ss [dCoh_alt_lem]
	  ) >>
	  `ca_Tr s''' (VApc s'''.cs) IN ca_deps s'''` by (
	      REWRITE_TAC [ca_deps_pc_lem]
	  ) >>
	  `VApc s'''.cs IN ca_vdeps s'''` by (
	      REWRITE_TAC [ca_vdeps_PC_lem]
	  ) >>
	  `cl_Tr s'' (VApc s''.cs) = ca_Tr s''' (VApc s'''.cs)` by (
	      RW_TAC std_ss [] >>
	      IMP_RES_TAC deps_Tr_eq_lem 
	  ) >>
	  `cl_Cv s'' (MEM (cl_Tr s'' (VApc s''.cs))) = 
           imv s'''.ms T (ca_Tr s''' (VApc s'''.cs))` by (
              RW_TAC std_ss [Cv_mem_lem] >>
	      MATCH_MP_TAC EQ_SYM >>
	      MATCH_MP_TAC imv_dmv_lem >>
	      IMP_RES_TAC dCoh_lem >>
	      IMP_RES_TAC abs_ca_trans_mode_lem >>
	      FULL_SIMP_TAC std_ss [cm_kernel_po_def, ca_II_def] >>
	      IMP_RES_TAC ca_Icodef_po_def >>
	      ASM_REWRITE_TAC []
	  ) >>
	  `cl_deps s'' = ca_deps s'''` by ( IMP_RES_TAC deps_eq_lem ) >>
	  `!d. MEM d dl ==> CA (opd d)` by (
	      IMP_RES_TAC cl_II_po_def >>
	      FULL_SIMP_TAC std_ss [cm_kernel_po_def, cl_II_def] >>
	      IMP_RES_TAC cl_Icmf_po_def
	  ) >>
	  (* apply core bisim lem *)
	  `(s'.cs = sc'.cs) /\ (dl = dl') /\  
	   !pa. pa IN writes dl ==> (cl_Cv s' (MEM pa) = Cv sc' (MEM pa))` by (
	      IMP_RES_TAC core_bisim_lem >>
	      ASM_REWRITE_TAC []
	  ) >>
	  RW_TAC std_ss [] >>
	  Cases_on `pa IN adrs dl`
	  >| [(* touched address *)
	      Cases_on `pa IN writes dl`
	      >| [(* written address -> use coherency*)
		  IMP_RES_TAC abs_ca_trans_dcoh_write_lem >>
		  IMP_RES_TAC dcoh_alt_lem >>
		  FULL_SIMP_TAC std_ss [cl_Cv_mem_lem, Cv_mem_lem]
		  ,
		  (* not write -> unchanged *)
		  IMP_RES_TAC abs_cl_trans_not_write_lem >>
		  IMP_RES_TAC abs_ca_trans_dmvalt_not_write_lem >>
		  FULL_SIMP_TAC std_ss [cl_Cv_mem_lem]
		 ]
	      ,
	      (* other addresses -> unchanged *)
	      IMP_RES_TAC abs_cl_trans_not_adrs_lem >>
	      IMP_RES_TAC abs_ca_trans_dmvalt_lem >>
	      FULL_SIMP_TAC std_ss [cl_Cv_mem_lem]
	     ] 
      ) >>
      NTAC 2 STRIP_TAC
      >| [(* history equivalent *)
	  METIS_TAC [hist_SUC_bisim_lem]
	  ,
	  (* ca_II *)
	  IMP_RES_TAC cl_II_po_def >>
	  `cl_Icmf s s' (SUC n)` by ( FULL_SIMP_TAC std_ss [cl_II_def] ) >>
	  IMP_RES_TAC cm_kernel_po_def >>
	  IMP_RES_TAC cl_kcomp_exentry_lem >>
	  IMP_RES_TAC ca_kcomp_exentry_lem >>
	  `ca_Icmf sc sc' (SUC n)` by ( 
	      MATCH_MP_TAC Icmf_sim_lem >>
	      EXISTS_TAC ``s''':hw_state``>>
	      EXISTS_TAC ``s:cl_state``>>
	      EXISTS_TAC ``s'':cl_state``>>
	      EXISTS_TAC ``s':cl_state``>>
	      EXISTS_TAC ``dl: mop list``>>
	      `!f. (clh f s s'' n = cah f sc s''' n)
		/\ (clh f s s' (SUC n) = cah f sc sc' (SUC n)) 
		/\ (cah f sc sc' (SUC n) = f (cah f sc s''' n) dl)` by (
	          METIS_TAC [cah_SUC_lem]
	      ) >>
	      METIS_TAC []
	  ) >>
	  RW_TAC std_ss [ca_II_def] >>
	  `cl_Icodef s s' (SUC n)` by ( FULL_SIMP_TAC std_ss [cl_II_def] ) >>
	  MATCH_MP_TAC Icodef_sim_lem >>
	  EXISTS_TAC ``s''':hw_state`` >>
	  EXISTS_TAC ``s:cl_state`` >>
	  EXISTS_TAC ``s'':cl_state`` >>
	  EXISTS_TAC ``s':cl_state`` >>
	  EXISTS_TAC ``dl: mop list``>>
	  `!f. (clh f s s'' n = cah f sc s''' n)
	    /\ (clh f s s' (SUC n) = cah f sc sc' (SUC n)) 
	    /\ (cah f sc sc' (SUC n) = f (cah f sc s''' n) dl)` by (
	      METIS_TAC [cah_SUC_lem]
	  ) >>
	  METIS_TAC []
	 ]      
     ]
);

(* existence of simulating cache-less kernel computation of the same length *)
val kernel_wrel_sim_lem = store_thm("kernel_wrel_sim_lem", ``
!sc sc' Icoh Icode Icm cl_Icmf ca_Icmf cl_Icodef ca_Icodef n. 
    cm_user_po Icoh Icode Icm
 /\ cm_kernel_po cl_Icmf cl_Icodef ca_Icmf ca_Icodef Icoh Icode Icm
 /\ cl_Inv_po
 /\ cl_II_po cl_Icmf cl_Icodef
 /\ Inv Icoh Icode Icm sc
 /\ ca_wrel sc sc' n
        ==>
?s s'. 
    Rsim sc s
 /\ cl_Inv s
 /\ cl_wrel s s' n
 /\ Rsim sc' s'
 /\ cl_Inv s' 
 /\ ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc sc' n
 /\ cl_II cl_Icmf cl_Icodef s s' n
 /\ (!f. clh f s s' n = cah f sc sc' n)
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC ( SPEC ``sc:hw_state`` Rsim_exists_lem ) >>
  FULL_SIMP_TAC std_ss [ca_wrel_def] >>
  IMP_RES_TAC Rsim_cl_Inv_lem >>
  IMP_RES_TAC ca_kcomp_exentry_lem >>
  IMP_RES_TAC Rsim_exentry_lem >>
  IMP_RES_TAC cl_kcomp_exists_lem >>
  PAT_X_ASSUM ``!n. x`` (
      fn thm => ASSUME_TAC ( SPEC ``n:num`` thm )
  ) >>
  FULL_SIMP_TAC std_ss [] >>
  Cases_on `m = n`
  >| [(* same length *)
      RW_TAC std_ss [] >>
      `Rsim sc' s' /\
       cl_II cl_Icmf cl_Icodef s s' m /\
       ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc sc' m /\
       !f. clh f s s' m = cah f sc sc' m` by (
          METIS_TAC [kernel_bisim_lem]
      ) >>
      IMP_RES_TAC Rsim_mode_lem >>
      `cl_wrel s s' m` by ( METIS_TAC [cl_wrel_def] ) >>
      IMP_RES_TAC cl_Inv_po_def >>
      METIS_TAC []
      ,
      (* shorter cl computation -> contradiction *)
      `m < n` by ( DECIDE_TAC ) >>
      RES_TAC >>
      `?sc''. ca_kcomp sc sc'' m /\ (mode sc'' = PRIV)` by (
          METIS_TAC [ca_kcomp_shorten_lem]
      ) >>
      `Rsim sc'' s'` by ( METIS_TAC [kernel_bisim_lem] ) >>
      IMP_RES_TAC Rsim_mode_lem >>
      REV_FULL_SIMP_TAC std_ss [basetypesTheory.mode_distinct]
     ]
);

(* Kernel integrity theorem *)

val Inv_kernel_preserved_thm = store_thm("Inv_kernel_preserved_thm", ``
!sc sc' Icoh Icode Icm cl_Icmf ca_Icmf cl_Icodef ca_Icodef n. 
    cm_user_po Icoh Icode Icm
 /\ cm_kernel_po cl_Icmf cl_Icodef ca_Icmf ca_Icodef Icoh Icode Icm
 /\ cl_Inv_po
 /\ cl_II_po cl_Icmf cl_Icodef
 /\ Inv Icoh Icode Icm sc
 /\ ca_wrel sc sc' n
        ==>
    Inv Icoh Icode Icm sc'
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC ca_Inv_rebuild_lem >>
  METIS_TAC [kernel_wrel_sim_lem]
);


val kernel_integrity_sim_thm = store_thm("kernel_integrity_sim_thm", ``
!s sc sc' Icoh Icode Icm cl_Icmf ca_Icmf cl_Icodef ca_Icodef n. 
    cm_user_po Icoh Icode Icm
 /\ cm_kernel_po cl_Icmf cl_Icodef ca_Icmf ca_Icodef Icoh Icode Icm
 /\ cl_Inv_po
 /\ cl_II_po cl_Icmf cl_Icodef
 /\ Inv Icoh Icode Icm sc
 /\ Rsim sc s
 /\ ca_wrel sc sc' n
        ==>
?s'. 
    cl_wrel s s' n
 /\ Rsim sc' s'
 /\ Inv Icoh Icode Icm sc'
``,
  REPEAT STRIP_TAC >>
  `Inv Icoh Icode Icm sc'` by (
      IMP_RES_TAC Inv_kernel_preserved_thm
  ) >>
  ASM_REWRITE_TAC [] >>
  `?s' s''. Rsim sc s' /\ cl_wrel s' s'' n /\ Rsim sc' s''` by ( 
      METIS_TAC [kernel_wrel_sim_lem] 
  ) >>
  IMP_RES_TAC Rsim_unique_lem >>
  RW_TAC std_ss [] >>
  HINT_EXISTS_TAC >>
  ASM_REWRITE_TAC []
);

(******** overall integrity *********)

(* Invariant preserved by weak transition relation, merging kernel steps *)

val (Wrel_rules, Wrel_ind, Wrel_cases) = Hol_reln `
   (!s s' req s''. Wrel s s' /\ abs_ca_trans s' USER req s'' ==> Wrel s s'')
/\ (!s s' s'' n. Wrel (s:hw_state) s' /\ ca_wrel s' s'' n ==> Wrel s s'')
`;

val overall_integrity_thm = store_thm("overall_integrity_thm", ``
!sc sc' Icoh Icode Icm cl_Icmf ca_Icmf cl_Icodef ca_Icodef. 
    cm_user_po Icoh Icode Icm
 /\ cm_kernel_po cl_Icmf cl_Icodef ca_Icmf ca_Icodef Icoh Icode Icm
 /\ cl_Inv_po
 /\ cl_II_po cl_Icmf cl_Icodef
 /\ Inv Icoh Icode Icm sc
 /\ Wrel sc sc'
        ==>
    Inv Icoh Icode Icm sc'
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  UNDISCH_TAC ``Wrel sc sc'`` >>
  SPEC_TAC (``sc':hw_state``,``sc':hw_state``) >>
  IndDefRules.RULE_INDUCT_THEN Wrel_ind ASSUME_TAC ASSUME_TAC
  >| [(* USER step *)
      IMP_RES_TAC Inv_user_preserved_thm
      ,
      (* weak kernel transition *)
      IMP_RES_TAC Inv_kernel_preserved_thm
     ]      
);


(*********** finish ************)

val _ = export_theory();
