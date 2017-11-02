(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open hwTheory;
open cachelessTheory;
open InvIfTheory;
open integrityTheory;

val _ = new_theory "AC_cm";

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

(* user integrity *)

val Ifun_AC_user_po = Define `Ifun_AC_user_po = 
!c mv. Ifun_(c,mv) ==> 
    (!pa. pa IN Mac ==> only_CA_(c,mv) pa)
 /\ (!pa. MEM pa IN CR_(c,mv) ==> pa IN Mac)
`;

val Ifun_AC_user_lem = store_thm("Ifun_AC_user_lem", ``
!s. Ifun_AC_user_po /\ Ifun s ==> 
    (!pa. pa IN Mac ==> only_CA s pa)
 /\ (!pa. MEM pa IN CR s ==> pa IN Mac)
``,
  RW_TAC std_ss [Ifun_AC_user_po, Ifun_def, only_CA_def, CR_def] >>
  RES_TAC
);

val cl_Inv_AC_user_lem = store_thm("cl_Inv_AC_user_lem", ``
!s. Ifun_AC_user_po /\ cl_Inv s ==> 
    (!pa. MEM pa IN cl_CR s ==> pa IN Mac)
``,
  RW_TAC std_ss [Ifun_AC_user_po, cl_Inv_def, cl_CR_def] >>
  RES_TAC
);

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
 /\ Ifun_AC_user_po
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
      IMP_RES_TAC Ifun_AC_user_lem >>
      FULL_SIMP_TAC std_ss []
     ]
);

val Inv_AC_CR_lem = store_thm("Inv_AC_CR_lem", ``
!s s'.
    Icoh_AC s
 /\ Ifun s
 /\ Ifun_AC_user_po
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
Ifun_AC_user_po ==> cm_user_po Icoh_AC Icode_AC Icm_AC
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
      IMP_RES_TAC Ifun_AC_user_lem >>
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
      FULL_SIMP_TAC std_ss [Icm_AC_def] >>
      IMP_RES_TAC Ifun_AC_user_lem >>
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
 /\ Ifun_AC_user_po
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

(* kernel integrity *)

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
val Ifun_AC_kernel_po = Define `Ifun_AC_kernel_po = 
!c mv. Ifun_(c,mv) ==> 
    !va. va IN Kcode ==> 
        MEM (Ktr va) IN {r | (?pa. r = MEM pa) /\ 
			     r IN CR_(c,mv) /\ 
			     ?m. Mon_(c,mv,r,m,EX)}
`;

val cl_Inv_AC_kernel_lem = store_thm("cl_Inv_AC_kernel_lem", ``
!s. Ifun_AC_kernel_po /\ cl_Inv s ==> 
    !va. va IN Kcode ==> MEM (Ktr va) IN cl_CRex s
``,
  RW_TAC std_ss [Ifun_AC_kernel_po, cl_Inv_def, 
		 cl_CRex_def, cl_CR_def, cl_Mon_def]
);

val Inv_AC_kernel_lem = store_thm("Inv_AC_kernel_lem", ``
!sc s.
    cm_user_po Icoh_AC Icode_AC Icm_AC
 /\ Ifun_AC_kernel_po
 /\ Inv Icoh_AC Icode_AC Icm_AC sc
       ==>
    !va. va IN Kcode ==> MEM (Ktr va) IN CRex sc
``,
  RW_TAC std_ss [Inv_lem, Ifun_AC_kernel_po, Ifun_def, 
		 CRex_def, CR_def, Mon_def]
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
`; 


(* fix MMU so that all va in Kvm are cacheable 
   all va in Kcode map to CRex
   PC always in Kcode
   never write CRex
   resulting CRex not expanding (or fixed) and contains Kcode
*)
val cl_Icodef_AC_def = Define `cl_Icodef_AC s s' = 
    VApc s'.cs IN Kcode
 /\ (!pa s'' dl. abs_cl_trans s' PRIV dl s'' 
              /\ MEM pa IN cl_CRex s ==> 
		 pa NOTIN writes dl)
 /\ ((cl_mode s' = USER) ==> (cl_CRex s' SUBSET cl_CRex s))
`; 

(* fix MMU so that all va in Kvm are cacheable 
   all va in Kcode map to CRex
   PC always in Kcode
   never write CRex
   CRex i-coherent and not dirty
   resulting CRex not expanding (or fixed) and contains Kcode
*)
val ca_Icodef_AC_def = Define `ca_Icodef_AC s s' = 
    VApc s'.cs IN Kcode
 /\ (!pa s'' dl. abs_ca_trans s' PRIV dl s'' 
              /\ MEM pa IN CRex s ==> 
		 pa NOTIN writes dl)
 /\ (!pa. MEM pa IN CRex s ==> icoh s'.ms pa /\ ~dirty s'.ms pa)
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

val Inv_MDVA_Mac_lem = store_thm("Inv_MDVA_Mac_lem", ``
!sc. 
    cm_user_po Icoh_AC Icode_AC Icm_AC 
 /\ Inv Icoh_AC Icode_AC Icm_AC sc 
 /\ Ifun_AC_user_po
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
  IMP_RES_TAC Ifun_AC_user_lem
);

val Inv_CRex_Mac_lem = store_thm("Inv_CRex_Mac_lem", ``
!sc. 
    cm_user_po Icoh_AC Icode_AC Icm_AC 
 /\ Inv Icoh_AC Icode_AC Icm_AC sc 
 /\ Ifun_AC_user_po
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
  IMP_RES_TAC Ifun_AC_user_lem
);

val Icmf_AC_init_xfer_lem = store_thm("Icmf_AC_init_xfer_lem", ``
Icmf_init_xfer_po ca_Icmf_AC cl_Icmf_AC Icoh_AC Icode_AC Icm_AC
``,
  REWRITE_TAC [Icmf_init_xfer_po_def, ca_Icmf_AC_def, cl_Icmf_AC_def] >>
  NTAC 3 STRIP_TAC >>
  IMP_RES_TAC Inv_Coh_AC_lem >>
  ASM_REWRITE_TAC [] >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Rsim_cs_lem >>
  ASM_REWRITE_TAC [ca_Inv_Mmu_fixed_def, cl_Inv_Mmu_fixed_def] >>
  `cl_fixmmu s Kvm Ktr <=> ca_fixmmu sc Kvm Ktr` by (
      METIS_TAC [Rsim_fixmmu_lem]
  ) >>
  IMP_RES_TAC Rsim_cl_deps_lem >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Rsim_deps_cnt_lem >>
  IMP_RES_TAC deps_vdeps_eq_lem >>
  FULL_SIMP_TAC std_ss [cl_Inv_Mmu_fixed_def]
);

val Icodef_AC_init_xfer_lem = store_thm("Icodef_AC_init_xfer_lem", ``
Icodef_init_xfer_po ca_Icodef_AC cl_Icodef_AC 
                    Icoh_AC Icode_AC Icm_AC 
		    ca_Icmf_AC cl_Icmf_AC
``,
  REWRITE_TAC [Icodef_init_xfer_po_def, ca_Icodef_AC_def, cl_Icodef_AC_def,
	       ca_Icmf_AC_def, cl_Icmf_AC_def] >>
  NTAC 3 STRIP_TAC >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  `cl_CRex s = CRex sc` by ( IMP_RES_TAC Rsim_CRex_lem ) >>
  IMP_RES_TAC Rsim_cs_lem >>
  ASM_REWRITE_TAC [ca_Inv_Mmu_fixed_def, cl_Inv_Mmu_fixed_def] >>
  `cl_fixmmu s Kvm Ktr <=> ca_fixmmu sc Kvm Ktr` by (
      METIS_TAC [Rsim_fixmmu_lem]
  ) >>
  IMP_RES_TAC Icode_AC_def >>
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
);

val Icmf_AC_xfer_lem = store_thm("Icmf_AC_xfer_lem", ``
Ifun_AC_user_po ==> Icmf_xfer_po ca_Icmf_AC cl_Icmf_AC Icoh_AC Icode_AC Icm_AC
``,
  REWRITE_TAC [Icmf_xfer_po_def, ca_Icmf_AC_def, cl_Icmf_AC_def] >>
  NTAC 12 STRIP_TAC >>
  FULL_SIMP_TAC std_ss [ca_II_def, cl_II_def] >>
  IMP_RES_TAC Rsim_cs_lem >>
  ASM_REWRITE_TAC [ca_Inv_Mmu_fixed_def, cl_Inv_Mmu_fixed_def] >>
  IMP_RES_TAC Inv_MDVA_Mac_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  `cl_fixmmu s Kvm Ktr <=> ca_fixmmu sc Kvm Ktr` by (
      METIS_TAC [Rsim_fixmmu_lem]
  ) >>
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
  FULL_SIMP_TAC std_ss [cl_Inv_Mmu_fixed_def] >>
  RW_TAC std_ss [] >>
  IMP_RES_TAC cl_MDVA_lem >>
  `MDVA sc Kvm = cl_MDVA s Kvm` by ( METIS_TAC [Rsim_MDVA_lem] ) >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC dCoh_subset_lem >>
  IMP_RES_TAC Rsim_MDVA_eq_dCoh_cl_lem >>
  `Cv sc r = cl_Cv s r` by ( METIS_TAC [Rsim_MDVA_eq_cl_lem] ) >>
  FULL_SIMP_TAC std_ss []
);

val Icodef_AC_xfer_lem = store_thm("Icodef_AC_xfer_lem", ``
Ifun_AC_user_po ==> Icodef_xfer_po ca_Icodef_AC cl_Icodef_AC 
               Icoh_AC Icode_AC Icm_AC 
	       ca_Icmf_AC cl_Icmf_AC
``,
  REWRITE_TAC [Icodef_xfer_po_def, ca_Icodef_AC_def, cl_Icodef_AC_def] >>
  NTAC 10 STRIP_TAC >>
  FULL_SIMP_TAC std_ss [ca_II_def, cl_II_def, ca_Icmf_AC_def, cl_Icmf_AC_def] >>
  `cl_CRex s = CRex sc` by ( 
      MATCH_MP_TAC Rsim_CRex_lem >>
      METIS_TAC [Inv_lem]
  ) >>
  IMP_RES_TAC Rsim_cs_lem >>
  FULL_SIMP_TAC std_ss[ca_Inv_Mmu_fixed_def, cl_Inv_Mmu_fixed_def] >>
  IMP_RES_TAC Inv_CRex_Mac_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  STRIP_TAC
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
  RW_TAC std_ss [ca_Icmf_po_def, ca_Icmf_AC_def] >>
  IMP_RES_TAC dCoh_subset_lem
);

val ca_Icodef_AC_lem = store_thm("ca_Icodef_AC_lem", ``
Ifun_AC_kernel_po ==> 
ca_Icodef_po ca_Icodef_AC Icoh_AC Icode_AC Icm_AC ca_Icmf_AC
``,
  REWRITE_TAC [ca_Icodef_po_def, ca_Icodef_AC_def, ca_Icmf_AC_def] >>
  NTAC 5 STRIP_TAC >>
  IMP_RES_TAC ca_Inv_Mmu_fixed_lem >>
  `VApc s'.cs IN Kvm` by ( FULL_SIMP_TAC std_ss [Kcode_spec] ) >>
  `ca_Tr s' (VApc s'.cs) = Ktr (VApc s'.cs)` by (
      IMP_RES_TAC ca_fixmmu_Tr_lem
  ) >>
  ASM_REWRITE_TAC [] >>
  IMP_RES_TAC Inv_AC_kernel_lem >>
  RES_TAC >>
  ASM_REWRITE_TAC []
);

val Inv_rebuild_AC_lem = store_thm("Inv_rebuild_AC_lem", ``
Ifun_AC_user_po /\ cm_user_po Icoh_AC Icode_AC Icm_AC ==> 
Inv_rebuild_po Icoh_AC Icode_AC Icm_AC 
               ca_Icmf_AC ca_Icodef_AC cl_Icmf_AC cl_Icodef_AC
``,
  REWRITE_TAC [Inv_rebuild_po_def] >>
  NTAC 6 STRIP_TAC >>
  MATCH_MP_TAC (
      prove(``A /\ (A ==> B) /\ (A /\ B ==> C) ==> A /\ B /\ C``, PROVE_TAC [])
  ) >>
  REPEAT STRIP_TAC
  >| [(* Ifun *)
      MATCH_MP_TAC Ifun_xfer_lem >>
      HINT_EXISTS_TAC >>
      RW_TAC std_ss [] >>
      ASSUME_TAC ( SPEC ``r:resource`` coreIfTheory.res_cases ) >>
      FULL_SIMP_TAC std_ss []
      >| [(* memory *)
	  FULL_SIMP_TAC std_ss [] >>
	  `pa IN Mac` by ( IMP_RES_TAC cl_Inv_AC_user_lem ) >>
	  FULL_SIMP_TAC std_ss [ca_II_def, ca_Icmf_AC_def] >>
	  IMP_RES_TAC Rsim_dCoh_Cv_lem
	  ,
          (* register *)
	  IMP_RES_TAC Rsim_lem
	 ]
      ,
      (* Icoh *)
      RW_TAC std_ss [Icoh_AC_def, dCoh_lem2, pred_setTheory.IN_INTER] >>
      FULL_SIMP_TAC std_ss [ca_II_def, ca_Icmf_AC_def] >>
      IMP_RES_TAC dCoh_lem2
      ,
      (* Icode *)
      REWRITE_TAC [Icode_AC_def, iCoh_CRex_lem, isafe_CRex_lem2] >>
      `CRex sc' SUBSET CRex sc` suffices_by (
          FULL_SIMP_TAC std_ss [ca_II_def, ca_Icodef_AC_def, 
				pred_setTheory.SUBSET_DEF]
      ) >>
      `CRex sc' = cl_CRex s'` by ( 
          IMP_RES_TAC Rsim_CRex_lem >>
          ASM_REWRITE_TAC []
      ) >>
      `Ifun sc /\ Icoh_AC sc` by ( FULL_SIMP_TAC std_ss [Inv_lem] ) >>
      `CRex sc = cl_CRex s` by ( 
          IMP_RES_TAC Rsim_CRex_lem >>
          ASM_REWRITE_TAC []
      ) >>
      FULL_SIMP_TAC std_ss [cl_II_def] >>
      IMP_RES_TAC cachelessTheory.cl_wrel_mode_lem >>
      IMP_RES_TAC cl_Icodef_AC_def
     ]
);

val discharge_kernel_AC_lem = store_thm("discharge_kernel_AC_lem", ``
    Ifun_AC_user_po  
 /\ Ifun_AC_kernel_po 
 /\ cm_user_po Icoh_AC Icode_AC Icm_AC 
        ==> 
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
		 ca_Icodef_AC_lem,
		 Inv_rebuild_AC_lem]
);

val Inv_kernel_preserved_AC_thm = store_thm("Inv_kernel_preserved_AC_thm", ``
!sc sc'. 
    cl_Inv_po
 /\ Ifun_AC_user_po
 /\ Ifun_AC_kernel_po
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
 /\ Ifun_AC_user_po
 /\ Ifun_AC_kernel_po
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
 /\ Ifun_AC_user_po
 /\ Ifun_AC_kernel_po
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
