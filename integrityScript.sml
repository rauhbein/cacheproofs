(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open hwTheory;
open InvIfTheory;
open cachelessTheory;

val _ = new_theory "integrity";

(******** import Inv interface ********)

val CR_lem = store_thm("CR_lem", ``
!s s'. (!r. r IN CR s ==> (Cv s r = Cv s' r)) ==> (CR s = CR s')
``,
  REWRITE_TAC [CR_oblg]
);

val CR_coreg_lem = store_thm("CR_coreg_lem", ``
!s s' r. reg_res r /\ r IN CR s /\ (s'.cs.coreg = s.cs.coreg) ==> 
    (Cv s r = Cv s' r) 
``,
  REWRITE_TAC [CR_coreg_oblg]
);

val CRex_lem = store_thm("CRex_lem", ``
!s r. r IN CRex s ==> (?pa. (r = MEM pa)) /\ r IN CR s /\ ?m. Mon s r m EX
``,
  REWRITE_TAC [CRex_oblg]
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
    /\ dCoh s.ms {pa | MEM pa IN CR s} 
    /\ dCoh s'.ms {pa | MEM pa IN CR s'}
    /\ (!r. r IN CR s ==> (Cv s r = Cv s' r))
        ==>
    (Icoh s <=> Icoh s')
``,
  REWRITE_TAC [Icoh_CR_oblg]
); 

val Icoh_dCoh_lem = store_thm("Icoh_dCoh_lem", ``
!s Icoh Icode Icm. cm_user_po Icoh Icode Icm /\ Icoh s ==> 
    dCoh s.ms {pa | MEM pa IN CR s}
``,
  REWRITE_TAC [Icoh_dCoh_oblg]
); 

val Icode_CR_lem = store_thm("Icode_CR_lem", ``
!s s' Icoh Icode Icm. 
       cm_user_po Icoh Icode Icm 
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
!s Icoh Icode Icm. cm_user_po Icoh Icode Icm /\ Icode s ==> 
    iCoh s.ms {pa | MEM pa IN CRex s}
``,
  REWRITE_TAC [Icode_iCoh_oblg]
);

val Icode_isafe_lem = store_thm("Icode_isafe_lem", ``
!s Icoh Icode Icm. cm_user_po Icoh Icode Icm /\ Icode s ==> 
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
 /\ (!d. MEM d dl ==> CA d)
 /\ pa IN writes dl 
        ==> 
    dcoh s'.ms pa
``,
  REWRITE_TAC [abs_ca_trans_dcoh_write_oblg]
);

val abs_ca_trans_drvbl_lem = store_thm("abs_ca_trans_drvbl_lem", ``
!s m dl s' pa. abs_ca_trans s USER dl s' ==> drvbl s s'
``,
  REWRITE_TAC [abs_ca_trans_drvbl_oblg]
);

val abs_ca_trans_switch_lem = store_thm("abs_ca_trans_switch_lem", ``
!s dl s'. abs_ca_trans s USER dl s' ∧ (mode s' = PRIV) ⇒ exentry s'
``,
  REWRITE_TAC [abs_ca_trans_switch_oblg]
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


val core_bisim_lem = store_thm("core_bisim_lem", ``
!s s' sc sc' m dl dlc. 
    abs_cl_trans s m dl s'
 /\ abs_ca_trans sc m dlc sc'
 /\ (s.cs = sc.cs)
 /\ (!pa. pa IN ca_deps sc ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa)))
 /\ (cl_Cv s (MEM (cl_Tr s (VApc s.cs))) = imv sc.ms T (ca_Tr sc (VApc sc.cs)))
 /\ (cl_deps s = ca_deps sc)
 /\ (!d. MEM d dl ==> CA d)
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

val ca_vdeps_PC_lem = store_thm("ca_vdeps_PC_lem", ``
!s. VApc s.cs IN ca_vdeps s
``,
  REWRITE_TAC [ca_vdeps_PC_oblg]
);

(******** top level proof ********)

(* user integrity *)

val Inv_MD_Coh_lem = store_thm("Inv_MD_Coh_lem", ``
!s s' Icoh Icode Icm. cm_user_po Icoh Icode Icm /\ Inv Icoh Icode Icm s ==> 
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
      FULL_SIMP_TAC std_ss [drvbl_def] >>
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

val Ifun_AC_po = Define `Ifun_AC_po = 
!s. Ifun s ==> 
    !pa. pa IN Mac ==> only_CA s pa
`;

val Icoh_AC_def = Define `Icoh_AC s = 
    (!pa. MEM pa IN CR s ==> pa IN Mac)
 /\ dCoh s.ms (Mac INTER {pa | MEM pa IN CR s})
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

val ca_Inv_rebuild_lem = store_thm("ca_Inv_rebuild_lem", ``
!s' sc sc' Icoh Icode Icm cl_Icmf ca_Icmf cl_Icodef ca_Icodef. 
    cm_user_po Icoh Icode Icm
 /\ cm_kernel_po cl_Icmf cl_Icodef ca_Icmf ca_Icodef Icm
 /\ ca_wrel sc sc' 
 /\ Rsim sc' s'
 /\ cl_Inv s' 
 /\ ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc sc'
        ==>
    Inv Icoh Icode Icm sc'
``,
  RW_TAC std_ss [cm_kernel_po_def] >>
  IMP_RES_TAC Icm_f_po_def >>
  FULL_SIMP_TAC std_ss [ca_II_def, Inv_lem] >>
  REPEAT STRIP_TAC
  >| [(* Ifun *)
      `Icoh sc'` by ( IMP_RES_TAC ca_Icmf_Icoh_lem ) >>
      IMP_RES_TAC Ifun_Icoh_lem 
      ,
      (* Icoh *)
      IMP_RES_TAC ca_Icmf_Icoh_lem
      ,
      (* Icode *)
      IMP_RES_TAC ca_Icmf_Icode_lem 
     ]
);

val kernel_bisim_lem = store_thm("kernel_bisim_lem", ``
!s s' sc sc' n Icoh Icode Icm cl_Icmf ca_Icmf cl_Icodef ca_Icodef. 
    cm_user_po Icoh Icode Icm
 /\ cm_kernel_po cl_Icmf cl_Icodef ca_Icmf ca_Icodef Icm
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
      RW_TAC std_ss [ca_II_def] >> (
	  IMP_RES_TAC init_cm_xfer_po_def
      )
      ,
      (* n -> SUC n *)
      REPEAT GEN_TAC >>
      STRIP_TAC >>
      IMP_RES_TAC cl_II_po_def >>
      FULL_SIMP_TAC std_ss [cl_kcomp_SUC_lem, ca_kcomp_SUC_lem] >>
      `Rsim s''' s'' /\
       ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc s'''` by ( METIS_TAC [] ) >>
      MATCH_MP_TAC (
          prove(``(A /\ (dl':dop list = dl)) /\ (A /\ (dl' = dl) ==> B) ==> 
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
	  `!d. MEM d dl ==> CA d` by (
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
	  RW_TAC std_ss [ca_II_def]
	  >| [(* Icmf *)
	      `ca_Icmf sc sc' <=> cl_Icmf s s'` suffices_by (
	          FULL_SIMP_TAC std_ss [cl_II_def]
	      ) >>
	      IMP_RES_TAC Icmf_xfer_po_def
	      ,
	      (* Icmf *)
	      `ca_Icodef sc sc' <=> cl_Icodef s s'` suffices_by (
	          FULL_SIMP_TAC std_ss [cl_II_def]
	      ) >>
	      IMP_RES_TAC Icodef_xfer_po_def
	     ]
	 ]
     ]
);




(*********** finish ************)

val _ = export_theory();
