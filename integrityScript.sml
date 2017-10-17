(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open hwTheory;
open InvIfTheory;

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
 /\ hw_trans s USER req s' 
        ==> 
    Ifun s' 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC drvbl_lem >>
  IMP_RES_TAC Inv_CR_unchanged_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Ifun_CR_lem
);

val Inv_Icoh_lem = store_thm("Inv_Icoh_lem", ``
!s s' req Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ hw_trans s USER req s' 
        ==> 
    Icoh s' 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC drvbl_lem >>
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
 /\ hw_trans s USER req s' ==> Icode s' 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC drvbl_lem >>
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
 /\ hw_trans s USER req s' 
        ==> 
    Icm s' 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC drvbl_lem >>
  IMP_RES_TAC Icm_lem
);

val Inv_user_preserved_lem = store_thm("Inv_user_preserved_lem", ``
!s s' req Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ hw_trans s USER req s' 
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
 /\ hw_trans s USER req s' 
        ==> 
    Inv Icoh Icode Icm s'
 /\ (!r. r IN CR s ==> (Cv s r = Cv s' r))
 /\ Cv_imv_eq s s' (CRex s)
 /\ ((mode s' = PRIV) ==> exentry s')
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC drvbl_lem >>
  IMP_RES_TAC Inv_CR_unchanged_lem >>
  IMP_RES_TAC hw_trans_switch_lem >>
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
    !pa. pa IN Mac ==> 
        !va m ac c. (Mmu_(s.cs, dmvca s.ms, va, m, ac) = SOME (pa,c))            
		        ==>
	            (c = T)
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

(*********** finish ************)

val _ = export_theory();
