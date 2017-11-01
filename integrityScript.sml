(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open hwTheory;
open InvIfTheory;
open cachelessTheory;

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

val CRex_lem = store_thm("CRex_lem", ``
!s r. r IN CRex s ==> (?pa. (r = MEM pa)) /\ r IN CR s /\ ?m. Mon s r m EX
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
  REWRITE_TAC [Icode_CR_oblg]
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
!s dl s'. abs_ca_trans s USER dl s' ==> drvbl s s'
``,
  REWRITE_TAC [abs_ca_trans_drvbl_oblg]
);

val abs_ca_trans_switch_lem = store_thm("abs_ca_trans_switch_lem", ``
!s dl s'. abs_ca_trans s USER dl s' ∧ (mode s' = PRIV) ⇒ exentry s'
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
 /\ icoh s.ms pa
 /\ ~dirty s.ms pa
        ==> 
    icoh s'.ms pa
 /\ ~dirty s'.ms pa
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
        ==>
    (dl = dlc)
``,
  REWRITE_TAC [core_bisim_dl_oblg]
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

val cl_CRex_lem = store_thm("cl_CRex_lem", ``
!s r. r IN cl_CRex s ==> 
(?pa. (r = MEM pa)) /\ r IN cl_CR s /\ ?m. cl_Mon s r m EX
``,
  REWRITE_TAC [cl_CRex_oblg]
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
  IMP_RES_TAC abs_ca_trans_drvbl_lem >>
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
  IMP_RES_TAC abs_ca_trans_drvbl_lem >>
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
  RW_TAC std_ss [CRex_def] >>
  IMP_RES_TAC Inv_CR_lem >>
  IMP_RES_TAC Inv_CR_unchanged_lem >>
  IMP_RES_TAC Inv_Mon_CR_lem >>
  ASM_REWRITE_TAC []
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
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Ifun_Mon_lem >>
  IMP_RES_TAC Icode_iCoh_lem >>
  IMP_RES_TAC Icode_isafe_lem >>
  RW_TAC std_ss []
  >| [(* CRex not writable *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
      IMP_RES_TAC CRex_lem >>
      RES_TAC
      ,
      (* CRex executable *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
      IMP_RES_TAC CRex_lem >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC []
     ]
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
  IMP_RES_TAC abs_ca_trans_drvbl_lem >>
  IMP_RES_TAC Inv_CR_unchanged_lem >>
  IMP_RES_TAC Inv_iCoh_lem >>
  IMP_RES_TAC Inv_isafe_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  (* IMP_RES_TAC Icoh_dCoh_lem >> *)
  IMP_RES_TAC Icode_iCoh_lem >>
  IMP_RES_TAC Icode_isafe_lem >>
  (* IMP_RES_TAC Inv_Coh_CR_lem >> *)
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
  IMP_RES_TAC abs_ca_trans_drvbl_lem >>
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
  IMP_RES_TAC abs_ca_trans_drvbl_lem >>
  IMP_RES_TAC Inv_CR_unchanged_lem >>
  IMP_RES_TAC abs_ca_trans_switch_lem >>
  RW_TAC std_ss [] >- ( IMP_RES_TAC Inv_user_preserved_lem ) >>
  MATCH_MP_TAC drvbl_iCoh_mem_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Icode_iCoh_lem >>
  IMP_RES_TAC Icode_isafe_lem >>
  IMP_RES_TAC Ifun_Mon_lem >>
  RW_TAC std_ss []
  >| [(* CRex not writable *)
      IMP_RES_TAC CRex_lem >>
      RES_TAC
      ,
      (* CRex executable *)
      IMP_RES_TAC CRex_lem >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC []
     ]
);

(********* Instantiation: Always Cacheability *********)

val _ = new_constant("Mac", ``:padr set``);
val _ = new_constant("Kvm", ``:vadr set``);
val _ = new_constant("Ktr", ``:vadr -> padr``);

val Kcode_exists = store_thm("Kcode_exists", ``
?Kcode. !va. va IN Kcode ==> va IN Kvm
``,
  EXISTS_TAC ``EMPTY:vadr set`` >>
  RW_TAC std_ss [pred_setTheory.NOT_IN_EMPTY]
);

val Kcode_spec = new_specification ("Kcode_spec",
  ["Kcode"], Kcode_exists);

val Ifun_AC_po = Define `Ifun_AC_po = 
!s. Ifun s ==> 
    (!pa. pa IN Mac ==> only_CA s pa)
 /\ (!pa. MEM pa IN CR s ==> pa IN Mac)
`;

val Icoh_AC_def = Define `Icoh_AC s = 
    dCoh s.ms (Mac INTER {pa | MEM pa IN CR s})
`; 

val Icode_AC_def = Define `Icode_AC s = 
    iCoh s.ms {pa | MEM pa IN CRex s}
 /\ isafe s {pa | MEM pa IN CRex s}
`; 

val Icm_AC_def = Define `Icm_AC s = 
   dCoh s.ms (Mac DIFF {pa | MEM pa IN CR s})
`; 

val Inv_AC_CR_unchanged_lem = store_thm("Inv_AC_CR_unchanged_lem", ``
!s s'. 
    Icoh_AC s
 /\ Ifun s
 /\ Ifun_AC_po
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
      FULL_SIMP_TAC std_ss [drvbl_def] >>
      IMP_RES_TAC CR_coreg_lem >>
      ASM_REWRITE_TAC []
      ,
      (* data core view of CR unchanged *)
      MATCH_MP_TAC drvbl_Coh_mem_lem >>
      IMP_RES_TAC Ifun_Mon_lem >>
      IMP_RES_TAC Icoh_AC_def >>
      FULL_SIMP_TAC std_ss [dCoh_lem2, pred_setTheory.IN_INTER] >>
      REPEAT STRIP_TAC >>
      `MEM pa IN CR s` by ( 
          FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF]
      ) >>
      IMP_RES_TAC Ifun_AC_po >>
      FULL_SIMP_TAC std_ss []
     ]
);

val Inv_AC_CR_lem = store_thm("Inv_AC_CR_lem", ``
!s s'.
    Icoh_AC s
 /\ Ifun s
 /\ Ifun_AC_po
 /\ drvbl s s'
        ==> 
    (CR s' = CR s)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Inv_AC_CR_unchanged_lem >>
  IMP_RES_TAC CR_lem >>
  ASM_REWRITE_TAC []
);


val discharge_user_AC_lem = store_thm("discharge_user_AC_lem", ``
Ifun_AC_po ==> cm_user_po Icoh_AC Icode_AC Icm_AC
``,
  RW_TAC std_ss [cm_user_po_def]
  >| [(* Icoh_CR_po *)
      RW_TAC std_ss [Icoh_CR_po_def, Icoh_AC_def] >>
      IMP_RES_TAC CR_lem >>
      FULL_SIMP_TAC std_ss [dCoh_lem2, pred_setTheory.IN_INTER]
      ,
      (* Icoh_dCoh_po *)
      RW_TAC std_ss [Icoh_dCoh_po_def, Icoh_AC_def] >>
      FULL_SIMP_TAC std_ss [dCoh_lem2, pred_setTheory.IN_INTER] >>
      RW_TAC std_ss [] >>
      `MEM pa IN CR s` by ( 
          FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF]
      ) >>
      IMP_RES_TAC Ifun_AC_po >>
      FULL_SIMP_TAC std_ss []
      ,
      (* Icode_CR_po *)
      RW_TAC std_ss [Icode_CR_po_def, Icode_AC_def]
      ,
      (* Icode_iCoh_po *)
      RW_TAC std_ss [Icode_iCoh_po_def, Icode_AC_def]
      ,
      (* Icode_isafe_po *)
      RW_TAC std_ss [Icode_isafe_po_def, Icode_AC_def]
      ,
      (* Icm_po *)
      RW_TAC std_ss [Icm_po_def, Icm_AC_def] >>
      FULL_SIMP_TAC std_ss [Inv_lem] >>
      IMP_RES_TAC Inv_AC_CR_lem >>
      FULL_SIMP_TAC std_ss [Ifun_AC_po, Icm_AC_def] >>
      RES_TAC >>
      `!pa. pa IN (Mac DIFF {pa | MEM pa IN CR s'}) ==> only_CA s pa` by (
          REPEAT STRIP_TAC >>
          FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF]
      ) >>
      MATCH_MP_TAC drvbl_dCoh_cacheable_lem >>
      HINT_EXISTS_TAC >>
      RW_TAC std_ss []
     ]
);

val Inv_AC_user_preserved_thm = store_thm("Inv_AC_user_preserved_thm", ``
!s s' req. 
    Inv Icoh_AC Icode_AC Icm_AC s
 /\ Ifun_AC_po
 /\ abs_ca_trans s USER req s' 
        ==> 
    Inv Icoh_AC Icode_AC Icm_AC s'
 /\ (!r. r IN CR s ==> (Cv s r = Cv s' r))
 /\ Cv_imv_eq s s' (CRex s)
 /\ ((mode s' = PRIV) ==> exentry s')
``,
  NTAC 4 STRIP_TAC >>
  MATCH_MP_TAC Inv_user_preserved_thm >>
  HINT_EXISTS_TAC >> 
  IMP_RES_TAC discharge_user_AC_lem >>
  ASM_REWRITE_TAC []
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
  IMP_RES_TAC core_bisim_dl_lem >>
  FULL_SIMP_TAC std_ss [] >>
  HINT_EXISTS_TAC >>
  ASM_REWRITE_TAC []
);

val Rsim_cl_step_lem = store_thm("Rsim_cl_step_lem", ``
!sc s m dl s'.
    Rsim sc s
 /\ dCoh sc.ms (ca_deps sc) 
 /\ abs_cl_trans s m dl s'
        ==>
    ?sc'. abs_ca_trans sc m dl sc' 
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC ( SPEC ``sc:hw_state`` abs_ca_progress_lem ) >> 
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Rsim_cs_lem >>
  `mode sc = m` by (
      IMP_RES_TAC abs_cl_trans_mode_lem >>
      REV_FULL_SIMP_TAC std_ss [cl_mode_def, mode_def]
  ) >>
  IMP_RES_TAC Rsim_dCoh_Cv_lem >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_bisim_dl_lem >>
  FULL_SIMP_TAC std_ss [] >>
  HINT_EXISTS_TAC >>
  ASM_REWRITE_TAC []
);


(* top level proof *)

val ca_Inv_rebuild_lem = store_thm("ca_Inv_rebuild_lem", ``
!s s' sc sc' Icoh Icode Icm cl_Icmf ca_Icmf cl_Icodef ca_Icodef. 
    cm_user_po Icoh Icode Icm
 /\ cm_kernel_po cl_Icmf cl_Icodef ca_Icmf ca_Icodef Icoh Icode Icm
 /\ ca_wrel sc sc' 
 /\ Rsim sc' s'
 /\ cl_Inv s' 
 /\ ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc sc'
 /\ cl_II cl_Icmf cl_Icodef s s'
        ==>
    Inv Icoh Icode Icm sc'
``,
  RW_TAC std_ss [cm_kernel_po_def] >>
  IMP_RES_TAC Icm_f_po_def >>
  FULL_SIMP_TAC std_ss [Inv_lem, Inv_rebuild_po_def] >>
  RES_TAC >>
  ASM_REWRITE_TAC []
);

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
 /\ cl_II cl_Icmf cl_Icodef s s' 
 /\ ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc sc'
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
      `ca_Icmf sc sc` by ( IMP_RES_TAC Icmf_init_sim_lem ) >>
      RW_TAC std_ss [ca_II_def] >>
      IMP_RES_TAC Icodef_init_sim_lem
      ,
      (* n -> SUC n *)
      REPEAT GEN_TAC >>
      STRIP_TAC >>
      IMP_RES_TAC cl_II_po_def >>
      FULL_SIMP_TAC std_ss [cl_kcomp_SUC_lem, ca_kcomp_SUC_lem] >>
      `Rsim s''' s'' /\
       ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc s'''` by ( METIS_TAC [] ) >>
      MATCH_MP_TAC (
          prove(``(A /\ (dl':mop list = dl)) /\ (A /\ (dl' = dl) ==> B) ==> 
		  A /\ B``, PROVE_TAC [])
      ) >>
      STRIP_TAC 
      >| [(* Rsim *)
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
	      FULL_SIMP_TAC std_ss [cm_kernel_po_def, ca_II_def, Inv_lem] >>
	      IMP_RES_TAC abs_ca_trans_mode_lem >>
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
	  ,
          (* ca_II *)
	  STRIP_TAC >>
	  FULL_SIMP_TAC std_ss [cm_kernel_po_def] >>
	  IMP_RES_TAC cl_II_po_def >>
	  `cl_Icmf s s'` by ( FULL_SIMP_TAC std_ss [cl_II_def] ) >>
	  `ca_Icmf sc sc'` by ( IMP_RES_TAC Icmf_sim_lem ) >>
	  RW_TAC std_ss [ca_II_def] >>
	  `cl_Icodef s s'` by ( FULL_SIMP_TAC std_ss [cl_II_def] ) >>
	  MATCH_MP_TAC Icodef_sim_lem >>
	  EXISTS_TAC ``s''':hw_state`` >>
	  EXISTS_TAC ``s:cl_state`` >>
	  EXISTS_TAC ``s'':cl_state`` >>
	  EXISTS_TAC ``s':cl_state`` >>
	  METIS_TAC []
	 ]
     ]
);

val kernel_wrel_sim_lem = store_thm("kernel_wrel_sim_lem", ``
!sc sc' Icoh Icode Icm cl_Icmf ca_Icmf cl_Icodef ca_Icodef. 
    cm_user_po Icoh Icode Icm
 /\ cm_kernel_po cl_Icmf cl_Icodef ca_Icmf ca_Icodef Icoh Icode Icm
 /\ cl_Inv_po
 /\ cl_II_po cl_Icmf cl_Icodef
 /\ Inv Icoh Icode Icm sc
 /\ ca_wrel sc sc'
        ==>
?s s'. 
    Rsim sc s
 /\ cl_Inv s
 /\ cl_wrel s s'
 /\ Rsim sc' s'
 /\ cl_Inv s' 
 /\ ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc sc'
 /\ cl_II cl_Icmf cl_Icodef s s'
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
       cl_II cl_Icmf cl_Icodef s s' /\
       ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc sc'` by (
          METIS_TAC [kernel_bisim_lem]
      ) >>
      IMP_RES_TAC Rsim_mode_lem >>
      `cl_wrel s s'` by ( METIS_TAC [cl_wrel_def] ) >>
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
!sc sc' Icoh Icode Icm cl_Icmf ca_Icmf cl_Icodef ca_Icodef. 
    cm_user_po Icoh Icode Icm
 /\ cm_kernel_po cl_Icmf cl_Icodef ca_Icmf ca_Icodef Icoh Icode Icm
 /\ cl_Inv_po
 /\ cl_II_po cl_Icmf cl_Icodef
 /\ Inv Icoh Icode Icm sc
 /\ ca_wrel sc sc'
        ==>
    Inv Icoh Icode Icm sc'
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC ca_Inv_rebuild_lem >>
  METIS_TAC [kernel_wrel_sim_lem]
);


val kernel_integrity_sim_thm = store_thm("kernel_integrity_sim_thm", ``
!s sc sc' Icoh Icode Icm cl_Icmf ca_Icmf cl_Icodef ca_Icodef. 
    cm_user_po Icoh Icode Icm
 /\ cm_kernel_po cl_Icmf cl_Icodef ca_Icmf ca_Icodef Icoh Icode Icm
 /\ cl_Inv_po
 /\ cl_II_po cl_Icmf cl_Icodef
 /\ Inv Icoh Icode Icm sc
 /\ Rsim sc s
 /\ ca_wrel sc sc'
        ==>
?s'. 
    cl_wrel s s'
 /\ Rsim sc' s'
 /\ Inv Icoh Icode Icm sc'
``,
  REPEAT STRIP_TAC >>
  `Inv Icoh Icode Icm sc'` by (
      IMP_RES_TAC Inv_kernel_preserved_thm
  ) >>
  ASM_REWRITE_TAC [] >>
  `?s' s''. Rsim sc s' /\ cl_wrel s' s'' /\ Rsim sc' s''` by ( 
      METIS_TAC [kernel_wrel_sim_lem] 
  ) >>
  IMP_RES_TAC Rsim_unique_lem >>
  RW_TAC std_ss [] >>
  HINT_EXISTS_TAC >>
  ASM_REWRITE_TAC []
);

(******** overall integrity *********)

val (Wrel_rules, Wrel_ind, Wrel_cases) = Hol_reln `
   (!s s' req s''. Wrel s s' /\ abs_ca_trans s' USER req s'' ==> Wrel s s'')
/\ (!s s' s''. Wrel (s:hw_state) s' /\ ca_wrel s' s'' ==> Wrel s s'')
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

(********* Instantiation: Always Cachability **********)

val cl_Inv_Mmu_fixed_def = Define `cl_Inv_Mmu_fixed s s' =
    cl_fixmmu s Kvm Ktr
 /\ (!r. r IN cl_MDVA s Kvm ==> (cl_Cv s r = cl_Cv s' r))
`;

val cl_Inv_Mmu_fixed_lem = store_thm("cl_Inv_Mmu_fixed_lem", ``
!s s'. cl_Inv_Mmu_fixed s s' ==> cl_fixmmu s' Kvm Ktr
``,
  RW_TAC std_ss [cl_Inv_Mmu_fixed_def] >>
  IMP_RES_TAC cl_fixmmu_MD_lem
);

val ca_Inv_Mmu_fixed_def = Define `ca_Inv_Mmu_fixed s s' =
    ca_fixmmu s Kvm Ktr
 /\ (!r. r IN MDVA s Kvm ==> (Cv s r = Cv s' r))
`;

val ca_Inv_Mmu_fixed_lem = store_thm("ca_Inv_Mmu_fixed_lem", ``
!s s'. ca_Inv_Mmu_fixed s s' ==> ca_fixmmu s' Kvm Ktr
``,
  RW_TAC std_ss [ca_Inv_Mmu_fixed_def] >>
  IMP_RES_TAC ca_fixmmu_MD_lem
);

(* additional constraint on functional invariant for changes of CR:
   - Kcode should always remain in cl_CRex *)
val cl_Inv_AC_po = Define `cl_Inv_AC_po = 
!s. cl_Inv s ==> 
    !va. va IN Kcode ==> MEM (Ktr va) IN cl_CRex s
`;

val cl_Inv_AC_xfer_lem = store_thm("cl_Inv_AC_xfer_lem", ``
!sc s.
    cm_user_po Icoh_AC Icode_AC Icm_AC
 /\ cl_Inv_AC_po
 /\ Inv Icoh_AC Icode_AC Icm_AC sc
 /\ Rsim sc s
       ==>
    !va. va IN Kcode ==> MEM (Ktr va) IN CRex sc
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_cl_Inv_lem >>
  IMP_RES_TAC cl_Inv_AC_po >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Rsim_CRex_lem >>
  FULL_SIMP_TAC std_ss []  
);

(* fix MMU so that all va in Kvm are cacheable 
   only accesses va from KVM
   corresponding pa are in always cacheable region 
   resulting CR is in always cacheable region
*)
val cl_Icmf_AC_def = Define `cl_Icmf_AC s s' = 
    cl_Inv_Mmu_fixed s s'
 /\ cl_vdeps s' SUBSET Kvm
 /\ cl_deps s' SUBSET Mac
 (* /\ (!pa. MEM pa IN cl_CR s' ==> pa IN Mac) *)
 (* /\ (!pa. MEM pa IN cl_MD s' ==> pa IN Mac) *)
`; 

(* fix MMU so that all va in Kvm are cacheable 
   only accesses va from KVM
   corresponding pa are in always cacheable region 
   always cacheable region is coherent
   resulting CR is in always cacheable region
*)
val ca_Icmf_AC_def = Define `ca_Icmf_AC s s' = 
    ca_Inv_Mmu_fixed s s'
 /\ ca_vdeps s' SUBSET Kvm
 /\ ca_deps s' SUBSET Mac
 /\ dCoh s'.ms Mac
 (* /\ ((mode s' = USER) ==> !pa. MEM pa IN CR s' ==> pa IN Mac) *)
 (* /\ ((mode s' = USER) ==> !pa. MEM pa IN MD s' ==> pa IN Mac) *)
`; 


(* fix MMU so that all va in Kvm are cacheable 
   all va in Kcode map to CRex
   PC always in Kcode
   never write CRex
   resulting CRex not expanding and contains Kcode
*)
val cl_Icodef_AC_def = Define `cl_Icodef_AC s s' = 
    VApc s'.cs IN Kcode
 /\ (!pa s'' dl. abs_cl_trans s' PRIV dl s'' 
              /\ MEM pa IN cl_CRex s ==> 
		 pa NOTIN writes dl)
(* TODO: no support for ic flush yet, cannot expand cl_CRex *) 
 /\ ((cl_mode s' = USER) ==> (cl_CRex s' SUBSET cl_CRex s))
`; 

(* fix MMU so that all va in Kvm are cacheable 
   all va in Kcode map to CRex
   PC always in Kcode
   never write CRex
   CRex i-coherent and not dirty
   resulting CRex not expanding and contains Kcode
*)
val ca_Icodef_AC_def = Define `ca_Icodef_AC s s' = 
    VApc s'.cs IN Kcode
 /\ (!pa s'' dl. abs_ca_trans s' PRIV dl s'' 
              /\ MEM pa IN CRex s ==> 
		 pa NOTIN writes dl)
 /\ (!pa. MEM pa IN CRex s ==> icoh s'.ms pa /\ ~dirty s'.ms pa)
(* TODO: no support for ic flush yet, cannot expand ca_CRex *) 
 /\ ((mode s' = USER) ==> (CRex s' SUBSET CRex s))
`; 

val Inv_Coh_AC_lem = store_thm("Inv_Coh_AC_lem", ``
!sc. cm_user_po Icoh_AC Icode_AC Icm_AC
  /\ Inv Icoh_AC Icode_AC Icm_AC sc
        ==>
     dCoh sc.ms Mac
``,
  RW_TAC std_ss [cm_user_po_def, Inv_lem] >>
  FULL_SIMP_TAC std_ss [Icoh_AC_def, Icm_AC_def, dCoh_lem2] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER, pred_setTheory.IN_DIFF] >>
  Cases_on `pa IN {pa | MEM pa IN CR sc}` >> (
      FULL_SIMP_TAC std_ss []
  )
);

(* discharge proof obligations *)

val dCoh_subset_lem = store_thm("dCoh_subset_lem", ``
!ms As Bs. dCoh ms As /\ Bs SUBSET As ==> dCoh ms Bs
``,
  RW_TAC std_ss [pred_setTheory.SUBSET_DEF, dCoh_lem2]
);

val Inv_MDVA_Mac_lem = store_thm("Inv_MDVA_Mac_lem", ``
!sc. 
    cm_user_po Icoh_AC Icode_AC Icm_AC 
 /\ Inv Icoh_AC Icode_AC Icm_AC sc 
 /\ Ifun_AC_po
        ==> 
    {pa | MEM pa IN MDVA sc Kvm} SUBSET Mac
``,
  RW_TAC std_ss [Inv_lem, Icoh_AC_def] >>
  `MDVA sc Kvm SUBSET MD sc` by ( 
      FULL_SIMP_TAC std_ss [MDVA_def, MD_def] >>
      `Kvm SUBSET UNIV:vadr set` by (
          FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_UNIV]
      ) >>
      RW_TAC std_ss [MD__monotonic_lem]
  ) >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF, 
		        pred_setTheory.IN_GSPEC_IFF] >>
  REPEAT STRIP_TAC >>
  RES_TAC >>
  IMP_RES_TAC Ifun_MD_lem >>
  IMP_RES_TAC Ifun_AC_po
);

val Inv_CRex_Mac_lem = store_thm("Inv_CRex_Mac_lem", ``
!sc. 
    cm_user_po Icoh_AC Icode_AC Icm_AC 
 /\ Inv Icoh_AC Icode_AC Icm_AC sc 
 /\ Ifun_AC_po
        ==> 
    {pa | MEM pa IN CRex sc} SUBSET Mac
``,
  RW_TAC std_ss [Inv_lem, Icoh_AC_def] >>
  `CRex sc SUBSET CR sc` by ( 
      FULL_SIMP_TAC std_ss [CRex_def, CR_def, pred_setTheory.SUBSET_DEF, 
			    pred_setTheory.IN_GSPEC_IFF] 
  ) >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF, 
		        pred_setTheory.IN_GSPEC_IFF] >>
  REPEAT STRIP_TAC >>
  RES_TAC >>
  IMP_RES_TAC Ifun_AC_po
);

val Icmf_AC_init_xfer_lem = store_thm("Icmf_AC_init_xfer_lem", ``
Icmf_init_xfer_po ca_Icmf_AC cl_Icmf_AC Icoh_AC Icode_AC Icm_AC
``,
  RW_TAC std_ss [Icmf_init_xfer_po_def, ca_Icmf_AC_def, cl_Icmf_AC_def] >>
  IMP_RES_TAC Inv_Coh_AC_lem >>
  ASM_REWRITE_TAC [] >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  (* `cl_CR s = CR sc` by ( IMP_RES_TAC Rsim_CR_eq_lem ) >> *)
  (* `cl_MD s = MD sc` by ( IMP_RES_TAC Rsim_MD_lem ) >> *)
  IMP_RES_TAC Rsim_cs_lem >>
  ASM_REWRITE_TAC [ca_Inv_Mmu_fixed_def, cl_Inv_Mmu_fixed_def] >>
  		   (* mode_def, cl_mode_def] >> *)
  `cl_fixmmu s Kvm Ktr <=> ca_fixmmu sc Kvm Ktr` by (
      METIS_TAC [Rsim_fixmmu_lem]
  ) >>
  EQ_TAC 
  >| [(* ==> *)
      STRIP_TAC >>
      IMP_RES_TAC Rsim_deps_lem >>
      IMP_RES_TAC Rsim_deps_cnt_lem >>
      IMP_RES_TAC deps_vdeps_eq_lem >>
      RW_TAC std_ss []
      ,
      (* ==> *)
      STRIP_TAC >>
      IMP_RES_TAC Rsim_cl_deps_lem >>
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC Rsim_deps_cnt_lem >>
      IMP_RES_TAC deps_vdeps_eq_lem >>
      FULL_SIMP_TAC std_ss []
     ]  
);

val Icodef_AC_init_xfer_lem = store_thm("Icodef_AC_init_xfer_lem", ``
Icodef_init_xfer_po ca_Icodef_AC cl_Icodef_AC 
                    Icoh_AC Icode_AC Icm_AC 
		    ca_Icmf_AC cl_Icmf_AC
``,
  RW_TAC std_ss [Icodef_init_xfer_po_def, 
		 ca_Icodef_AC_def, cl_Icodef_AC_def,
		 ca_Icmf_AC_def, cl_Icmf_AC_def] >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  `cl_CRex s = CRex sc` by ( IMP_RES_TAC Rsim_CRex_lem ) >>
  IMP_RES_TAC Rsim_cs_lem >>
  ASM_REWRITE_TAC [ca_Inv_Mmu_fixed_def, cl_Inv_Mmu_fixed_def, 
		   mode_def, cl_mode_def] >>
  `cl_fixmmu s Kvm Ktr <=> ca_fixmmu sc Kvm Ktr` by (
      METIS_TAC [Rsim_fixmmu_lem]
  ) >>
  IMP_RES_TAC Icode_AC_def >>
  ASM_REWRITE_TAC [pred_setTheory.SUBSET_REFL] >>
  EQ_TAC 
  >| [(* ==> *)
      STRIP_TAC >>
      IMP_RES_TAC Rsim_deps_lem >>
      RW_TAC std_ss [] >>
      IMP_RES_TAC dCoh_subset_lem >>
      IMP_RES_TAC Rsim_cl_step_lem >>
      RES_TAC 
      ,
      (* <== *)
      STRIP_TAC >>
      IMP_RES_TAC Rsim_cl_deps_lem >>
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC dCoh_subset_lem >>
      STRIP_TAC
      >| [(* CRex not written *)
	  RW_TAC std_ss [] >>
	  IMP_RES_TAC Rsim_ca_step_lem >>
	  RES_TAC 
	  ,
	  (* iCoh sc /\ isafe *)
	  NTAC 2 STRIP_TAC >>
	  `pa IN {pa | MEM pa IN CRex sc}` by (
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF]
	  ) >>
	  IMP_RES_TAC iCoh_lem >>
	  IMP_RES_TAC isafe_CRex_lem >>
	  ASM_REWRITE_TAC []
	 ]
     ]  
);

val Icmf_AC_xfer_lem = store_thm("Icmf_AC_xfer_lem", ``
Ifun_AC_po ==> Icmf_xfer_po ca_Icmf_AC cl_Icmf_AC Icoh_AC Icode_AC Icm_AC
``,
  RW_TAC std_ss [Icmf_xfer_po_def, ca_Icmf_AC_def, cl_Icmf_AC_def] >>
  FULL_SIMP_TAC std_ss [ca_II_def, cl_II_def] >>
  (* `cl_CR s = CR sc` by ( IMP_RES_TAC Rsim_CR_eq_lem ) >> *)
  (* `cl_MD s = MD sc` by ( IMP_RES_TAC Rsim_MD_lem ) >> *)
  IMP_RES_TAC Rsim_cs_lem >>
  ASM_REWRITE_TAC [ca_Inv_Mmu_fixed_def, cl_Inv_Mmu_fixed_def] >>
		   (* mode_def, cl_mode_def] >> *)
  IMP_RES_TAC Inv_MDVA_Mac_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  `cl_fixmmu s Kvm Ktr <=> ca_fixmmu sc Kvm Ktr` by (
      METIS_TAC [Rsim_fixmmu_lem]
  ) >>
  EQ_TAC 
  >| [(* ==> *)
      STRIP_TAC >>
      `cl_deps s'' = ca_deps sc''` by ( IMP_RES_TAC Rsim_deps_lem ) >>
      `cl_vdeps s'' = ca_vdeps sc''` by (
          IMP_RES_TAC Rsim_deps_cnt_lem >>
	  IMP_RES_TAC deps_vdeps_eq_lem
      ) >>
      RW_TAC std_ss [] >>
      `cl_Cv s r = Cv sc r` by ( METIS_TAC [Rsim_MDVA_eq_lem] ) >>
      `cl_MDVA s Kvm = MDVA sc Kvm` by ( METIS_TAC [Rsim_MDVA_lem] ) >>
      IMP_RES_TAC MDVA_lem >>
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC dCoh_subset_lem >>
      IMP_RES_TAC Rsim_MDVA_eq_dCoh_ca_lem >>
      ASM_REWRITE_TAC []
      (* , *)
      (* 	  (* cl_CR' in Mac *) *)
      (* 	  `dCoh sc''.ms {pa | MEM pa IN CR sc''}` by ( *)
      (* 	      RES_TAC >> *)
      (* 	      `{pa | MEM pa IN CR sc''} SUBSET Mac` by ( *)
      (* 	          FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF, *)
      (* 				        pred_setTheory.IN_GSPEC_IFF] *)
      (* 	      ) >> *)
      (* 	      IMP_RES_TAC dCoh_subset_lem *)
      (* 	  ) >> *)
      (* 	  IMP_RES_TAC Rsim_CR_eq_dCoh_ca_lem >> *)
      (* 	  FULL_SIMP_TAC std_ss [] *)
      (* 	  , *)
      (* 	  (* cl_MD' in Mac *) *)
      (* 	  `dCoh sc''.ms {pa | MEM pa IN MD sc''}` by ( *)
      (* 	      RES_TAC >> *)
      (* 	      `{pa | MEM pa IN MD sc''} SUBSET Mac` by ( *)
      (* 	          FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF, *)
      (* 				        pred_setTheory.IN_GSPEC_IFF] *)
      (* 	      ) >> *)
      (* 	      IMP_RES_TAC dCoh_subset_lem *)
      (* 	  ) >> *)
      (* 	  IMP_RES_TAC Rsim_MD_dCoh_ca_lem >> *)
      (* 	  FULL_SIMP_TAC std_ss [] *)
      (* 	 ] *)
      ,
      (* <== *)
      STRIP_TAC >>
      FULL_SIMP_TAC std_ss [ca_Icmf_AC_def, cl_Icmf_AC_def] >>
      IMP_RES_TAC cl_Inv_Mmu_fixed_lem >>
      `!d. MEM d dl ==> CA (opd d)` by (
          IMP_RES_TAC abs_cl_trans_fixmmu_CA_lem
      ) >>
      IMP_RES_TAC abs_ca_trans_dCoh_preserve_lem >>
      `cl_deps s'' = ca_deps sc''` by ( IMP_RES_TAC Rsim_cl_deps_lem ) >>
      `cl_vdeps s'' = ca_vdeps sc''` by (
          FULL_SIMP_TAC std_ss [] >>
          IMP_RES_TAC Rsim_deps_cnt_lem >>
	  IMP_RES_TAC deps_vdeps_eq_lem
      ) >>
      FULL_SIMP_TAC std_ss [] >>
      RW_TAC std_ss [] >>
      `Cv sc r = cl_Cv s r` by ( METIS_TAC [Rsim_MDVA_eq_cl_lem] ) >>
      `MDVA sc Kvm = cl_MDVA s Kvm` by ( METIS_TAC [Rsim_MDVA_lem] ) >>
      IMP_RES_TAC cl_MDVA_lem >>
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC dCoh_subset_lem >>
      IMP_RES_TAC Rsim_MDVA_eq_dCoh_cl_lem
	 (*  , *)
	 (*  (* cl_CR' in Mac *) *)
	 (*  `dCoh sc''.ms {pa | MEM pa IN cl_CR s''}` by ( *)
	 (*      RES_TAC >> *)
	 (*      `{pa | MEM pa IN cl_CR s''} SUBSET Mac` by ( *)
	 (*          FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF, *)
	 (* 			        pred_setTheory.IN_GSPEC_IFF] *)
	 (*      ) >> *)
	 (*      IMP_RES_TAC dCoh_subset_lem *)
	 (*  ) >> *)
	 (*  IMP_RES_TAC Rsim_CR_eq_dCoh_cl_lem >> *)
	 (*  FULL_SIMP_TAC std_ss [] *)
	 (*  , *)
	 (*  (* cl_MD' in Mac *) *)
	 (*  `dCoh sc''.ms {pa | MEM pa IN cl_MD s''}` by ( *)
	 (*      RES_TAC >> *)
	 (*      `{pa | MEM pa IN cl_MD s''} SUBSET Mac` by ( *)
	 (*          FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF, *)
	 (* 			        pred_setTheory.IN_GSPEC_IFF] *)
	 (*      ) >> *)
	 (*      IMP_RES_TAC dCoh_subset_lem *)
	 (*  ) >> *)
	 (*  IMP_RES_TAC Rsim_MD_dCoh_cl_lem >> *)
	 (*  FULL_SIMP_TAC std_ss [] *)
	 (* ] *)
     ]      
);

val Icodef_AC_xfer_lem = store_thm("Icodef_AC_xfer_lem", ``
Ifun_AC_po ==> Icodef_xfer_po ca_Icodef_AC cl_Icodef_AC 
               Icoh_AC Icode_AC Icm_AC 
	       ca_Icmf_AC cl_Icmf_AC
``,
  RW_TAC std_ss [Icodef_xfer_po_def, ca_Icodef_AC_def, cl_Icodef_AC_def] >>
  FULL_SIMP_TAC std_ss [ca_II_def, cl_II_def, ca_Icmf_AC_def, cl_Icmf_AC_def] >>
  `cl_CRex s = CRex sc` by ( 
      MATCH_MP_TAC Rsim_CRex_lem >>
      METIS_TAC [Inv_lem]
  ) >>
  IMP_RES_TAC Rsim_cs_lem >>
  FULL_SIMP_TAC std_ss[ca_Inv_Mmu_fixed_def, cl_Inv_Mmu_fixed_def, 
		       mode_def, cl_mode_def] >>
  IMP_RES_TAC Inv_CRex_Mac_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  EQ_TAC 
  >| [(* ==> *)
      RW_TAC std_ss [] >- (
          (* do not write CRex *)
	  IMP_RES_TAC Rsim_deps_lem >>
	  IMP_RES_TAC dCoh_subset_lem >>
	  IMP_RES_TAC Rsim_cl_step_lem >>
	  RES_TAC 
      ) >> (
	  (* CRex equal *)
	  `dCoh sc''.ms {pa | MEM pa IN CR sc''}` by ( ALL_TAC ) >>
	      RES_TAC >>
	      `{pa | MEM pa IN CR sc''} SUBSET Mac` by (
	          FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF,
				        pred_setTheory.IN_GSPEC_IFF] ) >>
	          REPEAT STRIP_TAC >>
	          IMP_RES_TAC Ifun_AC_po
	      ) >>
	      IMP_RES_TAC dCoh_subset_lem
	  ) >>
	  `dCoh sc''.ms {pa | MEM pa IN MD sc''}` by (
	      RES_TAC >>
	      `{pa | MEM pa IN MD sc''} SUBSET Mac` by (
	          FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF,
				        pred_setTheory.IN_GSPEC_IFF]
	      ) >>
	      IMP_RES_TAC dCoh_subset_lem
	  ) >>
	  IMP_RES_TAC Rsim_CRex_dCoh_ca_lem >>
	  FULL_SIMP_TAC std_ss []
      )
      ,
      (* <== *) 
      STRIP_TAC >>
      FULL_SIMP_TAC std_ss [] >>
      NTAC 2 STRIP_TAC
      >| [(* do not write CRex *)
          REPEAT GEN_TAC >> 
	  STRIP_TAC >>
	  IMP_RES_TAC Rsim_deps_lem >>
	  IMP_RES_TAC dCoh_subset_lem >>
	  IMP_RES_TAC Rsim_ca_step_lem >>
	  RES_TAC 
	  ,
	  (* icoh CRex and not dirty *)
	  NTAC 2 STRIP_TAC >>
	  FULL_SIMP_TAC std_ss [ca_Icodef_AC_def] >>
	  RES_TAC >>
	  METIS_TAC [abs_ca_trans_icoh_clean_preserve_lem]
	  ,
	  (* CRex equal *)
	  STRIP_TAC >>
	  `dCoh sc''.ms {pa | MEM pa IN cl_CR s''}` by (
	      RES_TAC >>
	      `{pa | MEM pa IN cl_CR s''} SUBSET Mac` by (
	          FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF,
				        pred_setTheory.IN_GSPEC_IFF]
	      ) >>
	      IMP_RES_TAC dCoh_subset_lem
	  ) >>
	  `dCoh sc''.ms {pa | MEM pa IN cl_MD s''}` by (
	      RES_TAC >>
	      `{pa | MEM pa IN cl_MD s''} SUBSET Mac` by (
	          FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF,
				        pred_setTheory.IN_GSPEC_IFF]
	      ) >>
	      IMP_RES_TAC dCoh_subset_lem
	  ) >>
	  IMP_RES_TAC Rsim_CRex_dCoh_cl_lem >>
	  FULL_SIMP_TAC std_ss []
	 ]
     ]
);

val Icm_f_AC_lem = store_thm("Icm_f_AC_lem", ``
Icm_f_po ca_Icmf_AC ca_Icodef_AC Icoh_AC Icode_AC Icm_AC
``,
  RW_TAC std_ss [Icm_f_po_def, ca_II_def, ca_Icmf_AC_def, ca_Icodef_AC_def,
		 Icm_AC_def] >>
  FULL_SIMP_TAC std_ss [dCoh_lem2, pred_setTheory.IN_DIFF]
);

val cl_Icmf_AC_lem = store_thm("cl_Icmf_AC_lem", ``
cl_Icmf_po cl_Icmf_AC
``,
  RW_TAC std_ss [cl_Icmf_po_def, cl_Icmf_AC_def] >>
  IMP_RES_TAC cl_Inv_Mmu_fixed_lem >>
  IMP_RES_TAC abs_cl_trans_fixmmu_CA_lem
);

val ca_Icmf_AC_lem = store_thm("ca_Icmf_AC_lem", ``
ca_Icmf_po ca_Icmf_AC Icoh_AC Icode_AC Icm_AC
``,
  RW_TAC std_ss [ca_Icmf_po_def, ca_Icmf_AC_def]
  >| [(* deps coherent *)
      IMP_RES_TAC dCoh_subset_lem
      ,
      (* Icoh in final state *)
      RES_TAC >>
      RW_TAC std_ss [Icoh_AC_def] >>
      FULL_SIMP_TAC std_ss [dCoh_lem2, pred_setTheory.IN_INTER]
     ]
);

val ca_Icodef_AC_lem = store_thm("ca_Icodef_AC_lem", ``
ca_Icodef_po ca_Icodef_AC Icoh_AC Icode_AC Icm_AC ca_Icmf_AC
``,
  REWRITE_TAC [ca_Icodef_po_def, ca_Icodef_AC_def, ca_Icmf_AC_def] >>
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC ca_Inv_Mmu_fixed_lem >>
  NTAC 2 STRIP_TAC
  >| [(* PC i-coherent and clean *)
      `VApc s'.cs IN Kvm` by ( FULL_SIMP_TAC std_ss [Kcode_spec] ) >>
      `ca_Tr s' (VApc s'.cs) = Ktr (VApc s'.cs)` by (
          IMP_RES_TAC ca_fixmmu_Tr_lem
      ) >>
      ASM_REWRITE_TAC [] >>
      RES_TAC >>
      RES_TAC >>
      ASM_REWRITE_TAC []
      ,
      (* Icode_AC in final state *)
      RES_TAC >>
      RW_TAC std_ss [Icode_AC_def]
      >| [(* iCoh CRex' *)
	  FULL_SIMP_TAC std_ss [iCoh_lem2, pred_setTheory.IN_GSPEC_IFF] >>
	  REPEAT STRIP_TAC >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF]
	  ,
	  (* isafe CRex' *)
	  FULL_SIMP_TAC std_ss [Icode_AC_def, isafe_def,
			        pred_setTheory.IN_GSPEC_IFF] >>
	  REPEAT GEN_TAC >> 
	  STRIP_TAC >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF]
	 ]
     ]
);

val discharge_kernel_AC_lem = store_thm("discharge_kernel_AC_lem", ``
cm_kernel_po cl_Icmf_AC cl_Icodef_AC ca_Icmf_AC ca_Icodef_AC 
             Icoh_AC Icode_AC Icm_AC
``,
  RW_TAC std_ss [cm_kernel_po_def, 
		 Icmf_AC_init_xfer_lem,
		 Icodef_AC_init_xfer_lem,
		 Icmf_AC_xfer_lem,
		 Icodef_AC_xfer_lem,
		 Icm_f_AC_lem,
		 cl_Icmf_AC_lem, 
		 ca_Icmf_AC_lem,
		 ca_Icodef_AC_lem]
);

val Inv_kernel_preserved_AC_thm = store_thm("Inv_kernel_preserved_AC_thm", ``
!sc sc'. 
    cl_Inv_po
 /\ Ifun_AC_po
 /\ cl_II_po cl_Icmf_AC cl_Icodef_AC
 /\ Inv Icoh_AC Icode_AC Icm_AC sc
 /\ ca_wrel sc sc'
        ==>
    Inv Icoh_AC Icode_AC Icm_AC sc'
``, 
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC Inv_kernel_preserved_thm >>
  HINT_EXISTS_TAC >> 
  IMP_RES_TAC discharge_user_AC_lem >>
  ASSUME_TAC discharge_kernel_AC_lem >>
  METIS_TAC []
);

val kernel_integrity_sim_AC_thm = store_thm("kernel_integrity_sim_AC_thm", ``
!s sc sc'. 
    cl_Inv_po
 /\ Ifun_AC_po
 /\ cl_II_po cl_Icmf_AC cl_Icodef_AC
 /\ Inv Icoh_AC Icode_AC Icm_AC sc
 /\ Rsim sc s
 /\ ca_wrel sc sc'
        ==>
?s'. 
    cl_wrel s s'
 /\ Rsim sc' s'
 /\ Inv Icoh_AC Icode_AC Icm_AC sc'
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC kernel_integrity_sim_thm >>
  HINT_EXISTS_TAC >> 
  IMP_RES_TAC discharge_user_AC_lem >>
  ASSUME_TAC discharge_kernel_AC_lem >>
  METIS_TAC []
);

val overall_integrity_AC_thm = store_thm("overall_integrity_AC_thm", ``
!sc sc'. 
    cl_Inv_po
 /\ Ifun_AC_po
 /\ cl_II_po cl_Icmf_AC cl_Icodef_AC
 /\ Inv Icoh_AC Icode_AC Icm_AC sc
 /\ Wrel sc sc'
        ==>
    Inv Icoh_AC Icode_AC Icm_AC sc'
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC overall_integrity_thm >>
  HINT_EXISTS_TAC >> 
  IMP_RES_TAC discharge_user_AC_lem >>
  ASSUME_TAC discharge_kernel_AC_lem >>
  METIS_TAC []
);



(*********** finish ************)

val _ = export_theory();
