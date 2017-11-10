(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open hwTheory;
open cachelessTheory;
open histTheory;
open InvIfTheory;
open integrityTheory;

val _ = new_theory "SE_cm";

(********* Instantiation: Selective Eviction *********)

(* importing obligations *)

val abs_ca_trans_clean_lem = store_thm("abs_ca_trans_clean_lem", ``
!s m dl s' pa. abs_ca_trans s m dl s' /\ pa IN dcleans dl ==> 
    ~dirty s'.ms pa
``,
  REWRITE_TAC [abs_ca_trans_clean_oblg]
);

val abs_ca_trans_clean_preserve_lem = 
store_thm("abs_ca_trans_clean_preserve_lem", ``
!s m dl s' pa. abs_ca_trans s m dl s' 
            /\ pa NOTIN writes dl 
            /\ ~dirty s.ms pa 
        ==> 
    ~dirty s'.ms pa
``,
  REWRITE_TAC [abs_ca_trans_clean_preserve_oblg]
);

val abs_ca_trans_dcoh_flush_lem = store_thm("abs_ca_trans_dcoh_flush_lem", ``
!s m dl s' pa. abs_ca_trans s m dl s' /\ pa IN dcleans dl ==> 
    dcoh s'.ms pa
``,
  REWRITE_TAC [abs_ca_trans_dcoh_flush_oblg]
);

val abs_ca_trans_icoh_flush_lem = store_thm("abs_ca_trans_icoh_flush_lem", ``
!s m dl s' pa. 
    abs_ca_trans s m dl s'
 /\ pa IN icleans dl
        ==> 
    icoh s'.ms pa
``,
  REWRITE_TAC [abs_ca_trans_icoh_flush_oblg]
);

val abs_ca_trans_icoh_preserve_lem = 
store_thm("abs_ca_trans_icoh__preserve_lem", ``
!s m dl s' pa.
    abs_ca_trans s m dl s'
 /\ pa NOTIN writes dl
 /\ pa NOTIN dcleans dl
 /\ icoh s.ms pa
 /\ ~dirty s.ms pa
        ==>
    icoh s'.ms pa
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC abs_ca_trans_icoh_clean_preserve_oblg
);

val abs_ca_trans_clean_disj_lem = store_thm("abs_ca_trans_clean_disj_lem", ``
!s m dl s'. 
    abs_ca_trans s m dl s'
        ==> 
    DISJOINT (dcleans dl) (icleans dl)
``,
  REWRITE_TAC [abs_ca_trans_clean_disj_oblg]
);

val abs_ca_trans_i_w_disj_lem = store_thm("abs_ca_trans_i_w_disj_lem", ``
!s m dl s'. 
    abs_ca_trans s m dl s'
        ==> 
    DISJOINT (writes dl) (icleans dl)
``,
  REWRITE_TAC [abs_ca_trans_i_w_disj_oblg]
);

val abs_cl_trans_clean_disj_lem = store_thm("abs_cl_trans_clean_disj_lem", ``
!s m dl s'. 
    abs_cl_trans s m dl s'
        ==> 
    DISJOINT (dcleans dl) (icleans dl)
``,
  REWRITE_TAC [abs_cl_trans_clean_disj_oblg]
);

val abs_cl_trans_i_w_disj_lem = store_thm("abs_cl_trans_i_w_disj_lem", ``
!s m dl s'. 
    abs_cl_trans s m dl s'
        ==> 
    DISJOINT (writes dl) (icleans dl)
``,
  REWRITE_TAC [abs_cl_trans_i_w_disj_oblg]
);

(* history functions *)

val hwr_def = Define `hwr h dl = h UNION writes dl`;

val hdcl_def = Define `hdcl h dl = h UNION dcleans dl`;

val hdclnw_def = Define `hdclnw h dl = (h DIFF writes dl) UNION dcleans dl`;

val hicl_def = Define `hicl h dl = 
(h DIFF (writes dl UNION dcleans dl)) UNION icleans dl`;

val hwr_lem = store_thm("hwr_lem", ``
!pa s dl s' h. 
    abs_ca_trans s PRIV dl s' 
 /\ ~dirty s.ms pa 
 /\ pa NOTIN hwr h dl
        ==>
    ~dirty s'.ms pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  FULL_SIMP_TAC std_ss [hwr_def, pred_setTheory.IN_UNION] >>
  IMP_RES_TAC abs_ca_trans_clean_preserve_lem
);

val hdcl_lem = store_thm("hdcl_lem", ``
!pa s dl s' h. 
    abs_ca_trans s PRIV dl s' 
 /\ dCoh s.ms h
 /\ pa IN hdcl h dl
 /\ (!d. MEM d dl ==> CA (opd d))
        ==>
    dcoh s'.ms pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  FULL_SIMP_TAC std_ss [hdcl_def, pred_setTheory.IN_UNION]
  >| [(* in h *)
      IMP_RES_TAC abs_ca_trans_dCoh_preserve_lem >>
      FULL_SIMP_TAC std_ss [dCoh_lem2]
      ,
      (* in dcleans *)
      IMP_RES_TAC abs_ca_trans_dcoh_flush_lem
     ]
);

val hdiffw_lem = store_thm("hdiffw_lem", ``
!pa s dl s' h. 
    abs_ca_trans s PRIV dl s' 
 /\ ~dirty s.ms pa 
 /\ pa IN h DIFF writes dl
        ==>
    ~dirty s'.ms pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  FULL_SIMP_TAC std_ss [hwr_def, pred_setTheory.IN_DIFF] >>
  IMP_RES_TAC abs_ca_trans_clean_preserve_lem
);

val hdclnw_lem = store_thm("hdclnw_lem", ``
!pa s dl s' h. 
    abs_ca_trans s PRIV dl s' 
 /\ (pa IN h ==> ~dirty s.ms pa)
 /\ pa IN hdclnw h dl
        ==>
    ~dirty s'.ms pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  FULL_SIMP_TAC std_ss [hdclnw_def, pred_setTheory.IN_UNION] 
  >| [(* h diff w *)
      `pa IN h` by ( FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] ) >>
      RES_TAC >>
      IMP_RES_TAC hdiffw_lem
      ,
      (* in dcleans *)
      IMP_RES_TAC abs_ca_trans_clean_lem
     ]
);

val hdiffwcl_lem = store_thm("hdiffwcl_lem", ``
!pa s dl s' h. 
    abs_ca_trans s PRIV dl s' 
 /\ icoh s.ms pa
 /\ ~dirty s.ms pa
 /\ pa IN h DIFF (writes dl UNION dcleans dl)
        ==>
    icoh s'.ms pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF, pred_setTheory.IN_UNION] >>
  IMP_RES_TAC abs_ca_trans_icoh_preserve_lem
);

val hicl_lem = store_thm("hicl_lem", ``
!pa s dl s' h. 
    abs_ca_trans s PRIV dl s' 
 /\ (pa IN h ==> icoh s.ms pa)
 /\ ~dirty s.ms pa
 /\ pa IN hicl h dl
        ==>
    icoh s'.ms pa
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [hicl_def, pred_setTheory.IN_UNION]
  >| [(* h diff w cl *)
      `pa IN h` by ( FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] ) >>
      RES_TAC >>
      IMP_RES_TAC hdiffwcl_lem 
      ,
      (* icleans *)
      IMP_RES_TAC abs_ca_trans_icoh_flush_lem
     ]
);

val icoh_clean_hwr_lem = store_thm("icoh_clean_hwr_lem", ``
!pa s dl s' h A. 
    abs_ca_trans s PRIV dl s' 
 /\ (!pa. pa IN A DIFF h ==> icoh s.ms pa /\ ~dirty s.ms pa)
        ==>
    !pa. pa IN A DIFF hwr h dl ==> icoh s'.ms pa /\ ~dirty s'.ms pa
``,
  NTAC 9 STRIP_TAC >>
  `pa IN A DIFF h` by (
      FULL_SIMP_TAC std_ss [hwr_def, pred_setTheory.IN_DIFF, 
			    pred_setTheory.IN_UNION]
  ) >>
  RES_TAC >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] >>
  STRIP_TAC
  >| [(* icoh *)
      FULL_SIMP_TAC std_ss [hwr_def, pred_setTheory.IN_UNION] >>
      IMP_RES_TAC abs_ca_trans_icoh_clean_preserve_lem
      ,
      (* clean *)
      IMP_RES_TAC hwr_lem
     ]
);

val hcl_inter_lem = store_thm("hcl_inter_lem", ``
!pa s dl s' hd hi. 
    abs_ca_trans s PRIV dl s' 
 /\ pa IN hicl hi dl INTER hdclnw hd dl 
        ==>
    pa IN hd
``,
  RW_TAC std_ss [pred_setTheory.IN_INTER, hdclnw_def, hicl_def] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]
  >| [(* in hd diff w / hi diff w cl *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF]
      ,
      (* in hd diff w / icl *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF, pred_setTheory.IN_UNION]
      ,
      (* in cl / hi diff w cl *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF]
      ,
      (* in i d -> not possible *)
      `DISJOINT (dcleans dl) (icleans dl)` by ( 
          IMP_RES_TAC abs_ca_trans_clean_disj_lem
      ) >>
      METIS_TAC [pred_setTheory.IN_DISJOINT]
     ]
);

val icoh_clean_hcl_lem = store_thm("icoh_clean_hcl_lem", ``
!pa s dl s' hd hi. 
    abs_ca_trans s PRIV dl s' 
 /\ (!pa. pa IN hd ==> ~dirty s.ms pa)
 /\ (!pa. pa IN hi /\ pa IN hd ==> icoh s.ms pa)
        ==>
    !pa. pa IN hicl hi dl INTER hdclnw hd dl ==> 
        icoh s'.ms pa /\ ~dirty s'.ms pa
``,
  NTAC 9 STRIP_TAC >>
  IMP_RES_TAC hcl_inter_lem >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER] >>
  RES_TAC >>
  IMP_RES_TAC hdclnw_lem >>
  ASM_REWRITE_TAC [] >>
  METIS_TAC [hicl_lem]
);

val icoh_clean_hist_lem = store_thm("icoh_clean_hist_lem", ``
!s hd hi hw A. 
    (!pa. pa IN hd ==> ~dirty s.ms pa)
 /\ (!pa. pa IN hi INTER hd ==> icoh s.ms pa)
 /\ (!pa. pa IN A DIFF hw ==> icoh s.ms pa /\ ~dirty s.ms pa)
        ==>
    !pa. pa IN (A DIFF hw) UNION (hi INTER hd) ==> 
        icoh s.ms pa /\ ~dirty s.ms pa
``,
  NTAC 8 STRIP_TAC >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION, pred_setTheory.IN_INTER]
);

val icoh_clean_hist_next_lem = store_thm("icoh_clean_hist_next_lem", ``
!pa s dl s' hd hi hw A. 
    abs_ca_trans s PRIV dl s' 
 /\ (!pa. pa IN hd ==> ~dirty s.ms pa)
 /\ (!pa. pa IN hi INTER hd ==> icoh s.ms pa)
 /\ (!pa. pa IN A DIFF hw ==> icoh s.ms pa /\ ~dirty s.ms pa)
        ==>
    !pa. pa IN (A DIFF hwr hw dl) UNION (hicl hi dl INTER hdclnw hd dl) ==> 
        icoh s'.ms pa /\ ~dirty s'.ms pa
``,
  NTAC 9 STRIP_TAC >>
  MATCH_MP_TAC icoh_clean_hist_lem >>
  NTAC 3 STRIP_TAC 
  >| [(* hdclnw *)
      METIS_TAC [hdclnw_lem]
      ,
      (* hicl cap hdclnw *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER] >>
      STRIP_TAC >>
      IMP_RES_TAC icoh_clean_hcl_lem >>
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER]
      ,
      (* A diff hwr *)
      STRIP_TAC >>
      IMP_RES_TAC icoh_clean_hwr_lem >> 
      ASM_REWRITE_TAC []
     ]
);

val cl_hw_def = Define `cl_hw s s' n = clh hwr s s' n`;
val ca_hw_def = Define `ca_hw s s' n = cah hwr s s' n`;

val cl_hdc_def = Define `cl_hdc s s' n = clh hdcl s s' n`;
val ca_hdc_def = Define `ca_hdc s s' n = cah hdcl s s' n`;

val cl_hdcn_def = Define `cl_hdcn s s' n = clh hdclnw s s' n`;
val ca_hdcn_def = Define `ca_hdcn s s' n = cah hdclnw s s' n`;

val cl_hic_def = Define `cl_hic s s' n = clh hicl s s' n`; 
val ca_hic_def = Define `ca_hic s s' n = cah hicl s s' n`; 

val cl_h0_lem = store_thm("cl_h0_lem", ``
!s. cl_exentry s ==> 
    (cl_hw s s 0 = EMPTY)
 /\ (cl_hdc s s 0 = EMPTY)
 /\ (cl_hdcn s s 0 = EMPTY)
 /\ (cl_hic s s 0 = EMPTY)
``,
  RW_TAC std_ss [cl_hw_def, cl_hdc_def, cl_hdcn_def, cl_hic_def, clh_0_lem]
); 

val ca_h0_lem = store_thm("ca_h0_lem", ``
!s. exentry s ==> 
    (ca_hw s s 0 = EMPTY)
 /\ (ca_hdc s s 0 = EMPTY)
 /\ (ca_hdcn s s 0 = EMPTY)
 /\ (ca_hic s s 0 = EMPTY)
``,
  RW_TAC std_ss [ca_hw_def, ca_hdc_def, ca_hdcn_def, ca_hic_def, cah_0_lem]
); 


(********* Instantiation *********)

val _ = new_constant("Kvm", ``:vadr set``);
val _ = new_constant("Ktr", ``:vadr -> padr``);

(* user integrity *)

val Icoh_SE_def = Define `Icoh_SE s = 
    dCoh s.ms ({pa | MEM pa IN CR s})
`; 

val Icode_SE_def = Define `Icode_SE s = 
    iCoh s.ms {pa | MEM pa IN CRex s}
 /\ isafe s {pa | MEM pa IN CRex s}
`; 

val Icm_SE_def = Define `Icm_SE s = T`; 

(* discharge POs *)

val Inv_SE_CR_unchanged_lem = store_thm("Inv_SE_CR_unchanged_lem", ``
!s s'. 
    Icoh_SE s
 /\ Ifun s
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
      IMP_RES_TAC Icoh_SE_def >>
      FULL_SIMP_TAC std_ss []
     ]
);

val Inv_SE_CR_lem = store_thm("Inv_SE_CR_lem", ``
!s s'.
    Icoh_SE s
 /\ Ifun s
 /\ drvbl s s'
        ==> 
    (CR s' = CR s)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Inv_SE_CR_unchanged_lem >>
  IMP_RES_TAC CR_lem >>
  ASM_REWRITE_TAC []
);


val discharge_user_SE_lem = store_thm("discharge_user_SE_lem", ``
cm_user_po Icoh_SE Icode_SE Icm_SE
``,
  RW_TAC std_ss [cm_user_po_def]
  >| [(* Icoh_CR_po *)
      RW_TAC std_ss [Icoh_CR_po_def, Icoh_SE_def]
      ,
      (* Icoh_dCoh_po *)
      RW_TAC std_ss [Icoh_dCoh_po_def, Icoh_SE_def]
      ,
      (* Icode_CR_po *)
      RW_TAC std_ss [Icode_CR_po_def, Icode_SE_def]
      ,
      (* Icode_iCoh_po *)
      RW_TAC std_ss [Icode_iCoh_po_def, Icode_SE_def]
      ,
      (* Icode_isafe_po *)
      RW_TAC std_ss [Icode_isafe_po_def, Icode_SE_def]
      ,
      (* Icm_po *)
      RW_TAC std_ss [Icm_po_def, Icm_SE_def]
     ]
);

val Inv_SE_user_preserved_thm = store_thm("Inv_SE_user_preserved_thm", ``
!s s' req. 
    Inv Icoh_SE Icode_SE Icm_SE s
 /\ abs_ca_trans s USER req s' 
        ==> 
    Inv Icoh_SE Icode_SE Icm_SE s'
 /\ (!r. r IN CR s ==> (Cv s r = Cv s' r))
 /\ Cv_imv_eq s s' (CRex s)
 /\ ((mode s' = PRIV) ==> exentry s')
``,
  NTAC 4 STRIP_TAC >>
  MATCH_MP_TAC Inv_user_preserved_thm >>
  HINT_EXISTS_TAC >> 
  ASM_REWRITE_TAC [discharge_user_SE_lem]
);

(* kernel integrity *)

(* data and instruction flushed region *)

val cl_Dfl_def = Define `
cl_Dfl s s' n = {pa | MEM pa IN cl_CR s} UNION cl_hdc s s' n
`;

val cl_EXfl_def = Define `
cl_EXfl s s' n = ({pa | MEM pa IN cl_CRex s} DIFF cl_hw s s' n) 
           UNION (cl_hic s s' n INTER cl_hdcn s s' n)
`;

val ca_Dfl_def = Define `
ca_Dfl s s' n = {pa | MEM pa IN CR s} UNION ca_hdc s s' n
`;

val ca_EXfl_def = Define `
ca_EXfl s s' n = ({pa | MEM pa IN CRex s} DIFF ca_hw s s' n) 
           UNION (ca_hic s s' n INTER ca_hdcn s s' n)
`;

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

(* fix MMU so that all va in Kvm are cacheable 
   only accessed va from Kvm 
   corresponding pa are in data flushed region 
   resulting CR is in data flushed region
*)
val cl_Icmf_SE_def = Define `cl_Icmf_SE s s' (n:num) = 
    cl_Inv_Mmu_fixed s s'
 /\ cl_vdeps s' SUBSET Kvm
 /\ cl_deps s' SUBSET cl_Dfl s s' n
 /\ ((cl_mode s' = USER) ==> ({pa | MEM pa IN cl_CR s'} SUBSET cl_Dfl s s' n))
`; 

(* fix MMU so that all va in Kvm are cacheable 
   only accesses va from KVM
   corresponding pa are in data flushed region 
   data flushed region is coherent
*)
val ca_Icmf_SE_def = Define `ca_Icmf_SE s s' (n:num) = 
    ca_Inv_Mmu_fixed s s'
 /\ ca_vdeps s' SUBSET Kvm
 /\ ca_deps s' SUBSET ca_Dfl s s' n
 /\ dCoh s'.ms (ca_Dfl s s' n)
`; 


(* fix MMU so that all va in Kvm are cacheable 
   PC always in Kvm
   Translation of PC is in instruction flushed region
   resulting CRex is in instruction flushed region
*)
val cl_Icodef_SE_def = Define `cl_Icodef_SE s s' (n:num) = 
    VApc s'.cs IN Kvm
 /\ Ktr (VApc s'.cs) IN cl_EXfl s s' n
 /\ ((cl_mode s' = USER) ==> ({pa | MEM pa IN cl_CRex s'} SUBSET cl_EXfl s s' n))
`; 

(* fix MMU so that all va in Kvm are cacheable 
   PC always in Kvm
   Translation of PC is in instruction flushed region
   CRex minus written addresses i-coherent and not dirty
   data flushed and not subsequently written addresses are clean
       (needed to make i-coherency and i-safety of EXfl inductive)
   intersection with recently i-cleaned addresses is i-coherent (and clean)
*)
val ca_Icodef_SE_def = Define `ca_Icodef_SE s s' (n:num) = 
    VApc s'.cs IN Kvm
 /\ Ktr (VApc s'.cs) IN ca_EXfl s s' n
 /\ (!pa. pa IN {pa | MEM pa IN CRex s} DIFF ca_hw s s' n ==> 
	  icoh s'.ms pa /\ ~dirty s'.ms pa)
 /\ (!pa. pa IN ca_hdcn s s' n ==> ~dirty s'.ms pa)
 /\ (!pa. pa IN ca_hic s s' n INTER ca_hdcn s s' n ==> icoh s'.ms pa)
`; 

(* some lemmas *)

val cl_Dfl_init_lem = store_thm("cl_Dfl_init_lem", ``
!s. cl_exentry s ==> (cl_Dfl s s 0 = {pa | MEM pa IN cl_CR s})
``,
  RW_TAC std_ss [cl_Dfl_def, pred_setTheory.EXTENSION, cl_h0_lem] >>
  REWRITE_TAC [pred_setTheory.UNION_EMPTY]
);

val ca_Dfl_init_lem = store_thm("ca_Dfl_init_lem", ``
!sc. exentry sc ==> (ca_Dfl sc sc 0 = {pa | MEM pa IN CR sc})
``,
  RW_TAC std_ss [ca_Dfl_def, pred_setTheory.EXTENSION, ca_h0_lem] >>
  REWRITE_TAC [pred_setTheory.UNION_EMPTY]
);

val cl_EXfl_init_lem = store_thm("cl_EXfl_init_lem", ``
!s. cl_exentry s ==> (cl_EXfl s s 0 = {pa | MEM pa IN cl_CRex s})
``,
  RW_TAC std_ss [cl_EXfl_def, pred_setTheory.EXTENSION, cl_h0_lem] >>
  REWRITE_TAC [pred_setTheory.UNION_EMPTY, 
	       pred_setTheory.INTER_EMPTY,
	       pred_setTheory.DIFF_EMPTY]
);

val ca_EXfl_init_lem = store_thm("ca_EXfl_init_lem", ``
!sc. exentry sc ==> (ca_EXfl sc sc 0 = {pa | MEM pa IN CRex sc})
``,
  RW_TAC std_ss [ca_EXfl_def, pred_setTheory.EXTENSION, ca_h0_lem] >>
  REWRITE_TAC [pred_setTheory.UNION_EMPTY, 
	       pred_setTheory.INTER_EMPTY,
	       pred_setTheory.DIFF_EMPTY]
);

val Inv_MDVA_Dfl_lem = store_thm("Inv_MDVA_Dfl_lem", ``
!sc. 
    cm_user_po Icoh_SE Icode_SE Icm_SE 
 /\ Inv Icoh_SE Icode_SE Icm_SE sc 
 /\ exentry sc
        ==> 
    {pa | MEM pa IN MDVA sc Kvm} SUBSET ca_Dfl sc sc 0
``,
  RW_TAC std_ss [Inv_lem] >>
  `MDVA sc Kvm SUBSET MD sc` by ( 
      FULL_SIMP_TAC std_ss [MDVA_def, MD_def] >>
      `Kvm SUBSET UNIV:vadr set` by (
          FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_UNIV]
      ) >>
      RW_TAC std_ss [MD__monotonic_lem]
  ) >>
  RW_TAC std_ss [ca_Dfl_init_lem] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF, 
		        pred_setTheory.IN_GSPEC_IFF] >>
  REPEAT STRIP_TAC >>
  RES_TAC >>
  IMP_RES_TAC Ifun_MD_lem
);

val Inv_CRex_EXfl_lem = store_thm("Inv_CRex_EXfl_lem", ``
!sc. exentry sc
        ==> 
    {pa | MEM pa IN CRex sc} SUBSET ca_EXfl sc sc 0
``,
  RW_TAC std_ss [ca_EXfl_init_lem] >>
  REWRITE_TAC [pred_setTheory.SUBSET_REFL]
);

val hist_bisim_SE_lem = store_thm("hist_bisim_SE_lem", ``
!s s' sc sc' m dl (n:num).
    cm_user_po Icoh_SE Icode_SE Icm_SE
 /\ ca_Icmf_po ca_Icmf_SE Icoh_SE Icode_SE Icm_SE
 /\ Rsim sc s
 /\ (!m s'' sc''. 
        m <= n
     /\ cl_kcomp s s'' m
     /\ ca_kcomp sc sc'' m
            ==>
        Rsim sc'' s''
     /\ ca_Icmf_SE sc sc'' m)
 /\ Icoh_SE sc
 /\ cl_kcomp s s' n
 /\ ca_kcomp sc sc' n
        ==>
    (cl_hw s s' n = ca_hw sc sc' n)
 /\ (cl_hdc s s' n = ca_hdc sc sc' n)
 /\ (cl_hdcn s s' n = ca_hdcn sc sc' n)
 /\ (cl_hic s s' n = ca_hic sc sc' n)
``,
  RW_TAC std_ss [cl_hw_def, ca_hw_def, cl_hdc_def, ca_hdc_def, 
		 cl_hdcn_def, ca_hdcn_def, cl_hic_def, ca_hic_def] >> (
      MATCH_MP_TAC hist_bisim_lem >>
      METIS_TAC []
  )
);

val Dfl_bisim_lem = store_thm("Dfl_bisim_lem", ``
!s s' sc sc' m dl (n:num).
    cm_user_po Icoh_SE Icode_SE Icm_SE
 /\ ca_Icmf_po ca_Icmf_SE Icoh_SE Icode_SE Icm_SE
 /\ Rsim sc s
 /\ (!m s'' sc''. 
        m <= n
     /\ cl_kcomp s s'' m
     /\ ca_kcomp sc sc'' m
            ==>
        Rsim sc'' s''
     /\ ca_Icmf_SE sc sc'' m)
 /\ Icoh_SE sc
 /\ Ifun sc
 /\ cl_kcomp s s' n
 /\ ca_kcomp sc sc' n
        ==>
    (cl_Dfl s s' n = ca_Dfl sc sc' n)
``,
  RW_TAC std_ss [cl_Dfl_def, ca_Dfl_def] >>
  IMP_RES_TAC Rsim_CR_eq_lem >>
  IMP_RES_TAC hist_bisim_SE_lem >>
  FULL_SIMP_TAC std_ss []
);

val EXfl_bisim_lem = store_thm("EXfl_bisim_lem", ``
!s s' sc sc' m dl (n:num).
    cm_user_po Icoh_SE Icode_SE Icm_SE
 /\ ca_Icmf_po ca_Icmf_SE Icoh_SE Icode_SE Icm_SE
 /\ Rsim sc s
 /\ (!m s'' sc''. 
        m <= n
     /\ cl_kcomp s s'' m
     /\ ca_kcomp sc sc'' m
            ==>
        Rsim sc'' s''
     /\ ca_Icmf_SE sc sc'' m)
 /\ Icoh_SE sc
 /\ Ifun sc
 /\ cl_kcomp s s' n
 /\ ca_kcomp sc sc' n
        ==>
    (cl_EXfl s s' n = ca_EXfl sc sc' n)
``,
  RW_TAC std_ss [cl_EXfl_def, ca_EXfl_def] >>
  IMP_RES_TAC Rsim_CRex_lem >>
  IMP_RES_TAC hist_bisim_SE_lem >>
  FULL_SIMP_TAC std_ss []
);

val ca_Dfl_dCoh_lem = store_thm("ca_Dfl_dCoh_lem", ``
!s s' s'' n dl. ca_kcomp s s' n /\ abs_ca_trans s' PRIV dl s'' 
	     /\ ca_Icmf_SE s s' n
	     /\ (!d. MEM d dl ==> CA (opd d))
		     ==> 
    dCoh s''.ms (ca_Dfl s s'' (SUC n))
``,
  RW_TAC std_ss [ca_Icmf_SE_def, ca_Dfl_def] >>
  IMP_RES_TAC abs_ca_trans_dCoh_preserve_lem >>
  FULL_SIMP_TAC std_ss [dCoh_lem2] >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION, ca_hdc_def] >>
  `cah hdcl s s'' (SUC n) = hdcl (cah hdcl s s' n) dl` by (
      METIS_TAC [cah_SUC_lem] 
  ) >>
  MATCH_MP_TAC hdcl_lem >>
  FULL_SIMP_TAC std_ss [] >>
  METIS_TAC [dCoh_lem2]
);

val ca_EXfl_icoh_clean_next_lem = store_thm("ca_EXfl_icoh_clean_next_lem", ``
!s s' s'' n dl. ca_kcomp s s' n /\ abs_ca_trans s' PRIV dl s'' 
	     /\ ca_Icodef_SE s s' n
		     ==> 
    !pa. pa IN ca_EXfl s s'' (SUC n) ==> icoh s''.ms pa /\ ~dirty s''.ms pa  
``,
  NTAC 6 STRIP_TAC >>
  FULL_SIMP_TAC std_ss [ca_Icodef_SE_def, ca_EXfl_def] >>
  FULL_SIMP_TAC std_ss [ca_hw_def, ca_hic_def, ca_hdcn_def] >>
  `cah hwr s s'' (SUC n) = hwr (cah hwr s s' n) dl` by (
      METIS_TAC [cah_SUC_lem] 
  ) >>
  `cah hicl s s'' (SUC n) = hicl (cah hicl s s' n) dl` by (
      METIS_TAC [cah_SUC_lem] 
  ) >>
  `cah hdclnw s s'' (SUC n) = hdclnw (cah hdclnw s s' n) dl` by (
      METIS_TAC [cah_SUC_lem] 
  ) >>
  ASM_REWRITE_TAC [] >>
  MATCH_MP_TAC icoh_clean_hist_next_lem >>
  METIS_TAC []
);

val ca_Icodef_icoh_clean_lem = store_thm("ca_Icodef_icoh_clean_lem", ``
!s s' s'' n dl. ca_kcomp s s' n /\ abs_ca_trans s' PRIV dl s'' 
	     /\ ca_Icodef_SE s s' n
		     ==> 
(!pa. pa IN {pa | MEM pa IN CRex s} DIFF ca_hw s s'' (SUC n) ==>
      icoh s''.ms pa /\ ~dirty s''.ms pa) /\
(!pa. pa IN ca_hdcn s s'' (SUC n) ==> ~dirty s''.ms pa) /\
(!pa. pa IN ca_hic s s'' (SUC n) INTER ca_hdcn s s'' (SUC n) ==>
  icoh s''.ms pa)
``,
  NTAC 6 STRIP_TAC >>
  FULL_SIMP_TAC std_ss [ca_Icodef_SE_def] >>
  FULL_SIMP_TAC std_ss [ca_hw_def, ca_hic_def, ca_hdcn_def] >>
  `cah hwr s s'' (SUC n) = hwr (cah hwr s s' n) dl` by (
      METIS_TAC [cah_SUC_lem] 
  ) >>
  `cah hicl s s'' (SUC n) = hicl (cah hicl s s' n) dl` by (
      METIS_TAC [cah_SUC_lem] 
  ) >>
  `cah hdclnw s s'' (SUC n) = hdclnw (cah hdclnw s s' n) dl` by (
      METIS_TAC [cah_SUC_lem] 
  ) >>
  ASM_REWRITE_TAC [] >>
  STRIP_TAC >- (
      (* CRex \ hw' *)
      MATCH_MP_TAC icoh_clean_hwr_lem >>
      METIS_TAC []
  ) >>
  STRIP_TAC
  >| [(* hdcn' *)
      METIS_TAC [hdclnw_lem]
      ,
      (* hi' cap hd' *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER] >>
      STRIP_TAC >>
      IMP_RES_TAC icoh_clean_hcl_lem >>
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER]
     ]
);

val cl_Dfl_SUC_lem = store_thm("cl_Dfl_SUC_lem", ``
!s s' s'' n dl. cl_kcomp s s' n /\ abs_cl_trans s' PRIV dl s'' ==> 
    (cl_Dfl s s'' (SUC n) = cl_Dfl s s' n UNION dcleans dl)
``,
  RW_TAC std_ss [cl_Dfl_def, pred_setTheory.EXTENSION, cl_hdc_def] >>
  `clh hdcl s s'' (SUC n) = hdcl (clh hdcl s s' n) dl` by (
      METIS_TAC [clh_SUC_lem] 
  ) >>
  RW_TAC std_ss [hdcl_def, pred_setTheory.UNION_ASSOC]
);

val ca_Dfl_SUC_lem = store_thm("ca_Dfl_SUC_lem", ``
!s s' s'' n dl. ca_kcomp s s' n /\ abs_ca_trans s' PRIV dl s'' ==> 
    (ca_Dfl s s'' (SUC n) = ca_Dfl s s' n UNION dcleans dl)
``,
  RW_TAC std_ss [ca_Dfl_def, pred_setTheory.EXTENSION, ca_hdc_def] >>
  `cah hdcl s s'' (SUC n) = hdcl (cah hdcl s s' n) dl` by (
      METIS_TAC [cah_SUC_lem] 
  ) >>
  RW_TAC std_ss [hdcl_def, pred_setTheory.UNION_ASSOC]
);


val cl_hw_SUC_lem = store_thm("cl_hw_SUC_lem", ``
!s s' s'' n dl. cl_kcomp s s' n /\ abs_cl_trans s' PRIV dl s'' ==> 
    (cl_hw s s'' (SUC n) = cl_hw s s' n UNION writes dl)
``,
  RW_TAC std_ss [pred_setTheory.EXTENSION, cl_hw_def] >>
  `clh hwr s s'' (SUC n) = hwr (clh hwr s s' n) dl` by (
      METIS_TAC [clh_SUC_lem] 
  ) >>
  RW_TAC std_ss [hwr_def]
);

val ca_hw_SUC_lem = store_thm("ca_hw_SUC_lem", ``
!s s' s'' n dl. ca_kcomp s s' n /\ abs_ca_trans s' PRIV dl s'' ==> 
    (ca_hw s s'' (SUC n) = ca_hw s s' n UNION writes dl)
``,
  RW_TAC std_ss [pred_setTheory.EXTENSION, ca_hw_def] >>
  `cah hwr s s'' (SUC n) = hwr (cah hwr s s' n) dl` by (
      METIS_TAC [cah_SUC_lem] 
  ) >>
  RW_TAC std_ss [hwr_def]
);

val cl_hdcn_SUC_lem = store_thm("cl_hdcn_SUC_lem", ``
!s s' s'' n dl. cl_kcomp s s' n /\ abs_cl_trans s' PRIV dl s'' ==> 
    (cl_hdcn s s'' (SUC n) = (cl_hdcn s s' n DIFF writes dl) UNION dcleans dl)
``,
  RW_TAC std_ss [pred_setTheory.EXTENSION, cl_hdcn_def] >>
  `clh hdclnw s s'' (SUC n) = hdclnw (clh hdclnw s s' n) dl` by (
      METIS_TAC [clh_SUC_lem] 
  ) >>
  RW_TAC std_ss [hdclnw_def]
);

val ca_hdcn_SUC_lem = store_thm("ca_hdcn_SUC_lem", ``
!s s' s'' n dl. ca_kcomp s s' n /\ abs_ca_trans s' PRIV dl s'' ==> 
    (ca_hdcn s s'' (SUC n) = (ca_hdcn s s' n DIFF writes dl) UNION dcleans dl)
``,
  RW_TAC std_ss [pred_setTheory.EXTENSION, ca_hdcn_def] >>
  `cah hdclnw s s'' (SUC n) = hdclnw (cah hdclnw s s' n) dl` by (
      METIS_TAC [cah_SUC_lem] 
  ) >>
  RW_TAC std_ss [hdclnw_def]
);

val cl_hic_SUC_lem = store_thm("cl_hic_SUC_lem", ``
!s s' s'' n dl. cl_kcomp s s' n /\ abs_cl_trans s' PRIV dl s'' ==> 
    (cl_hic s s'' (SUC n) = (cl_hic s s' n DIFF (writes dl UNION dcleans dl))
		      UNION icleans dl)
``,
  RW_TAC std_ss [pred_setTheory.EXTENSION, cl_hic_def] >>
  `clh hicl s s'' (SUC n) = hicl (clh hicl s s' n) dl` by (
      METIS_TAC [clh_SUC_lem] 
  ) >>
  RW_TAC std_ss [hicl_def]
);

val ca_hic_SUC_lem = store_thm("ca_hic_SUC_lem", ``
!s s' s'' n dl. ca_kcomp s s' n /\ abs_ca_trans s' PRIV dl s'' ==> 
    (ca_hic s s'' (SUC n) = (ca_hic s s' n DIFF (writes dl UNION dcleans dl))
		      UNION icleans dl)
``,
  RW_TAC std_ss [pred_setTheory.EXTENSION, ca_hic_def] >>
  `cah hicl s s'' (SUC n) = hicl (cah hicl s s' n) dl` by (
      METIS_TAC [cah_SUC_lem] 
  ) >>
  RW_TAC std_ss [hicl_def]
);

val cl_EXfl_SUC_lem = store_thm("cl_EXfl_SUC_lem", ``
!s s' s'' n dl. cl_kcomp s s' n /\ abs_cl_trans s' PRIV dl s'' ==> 
    (cl_EXfl s s'' (SUC n) = 
         (cl_EXfl s s' n DIFF (writes dl UNION dcleans dl)) UNION
	 (({pa | MEM pa IN cl_CRex s} DIFF (cl_hw s s' n UNION writes dl))
	      INTER dcleans dl) UNION
	 (cl_hdcn s s' n INTER icleans dl))
``,
  RW_TAC std_ss [cl_EXfl_def, pred_setTheory.EXTENSION] >>
  IMP_RES_TAC cl_hw_SUC_lem >>
  IMP_RES_TAC cl_hdcn_SUC_lem >>
  IMP_RES_TAC cl_hic_SUC_lem >>
  ASM_REWRITE_TAC [] >>
  EQ_TAC
  >| [(* ==> *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] >>
      STRIP_TAC
      >| [(* EX diff hw' *)
	  DISJ1_TAC >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] >>
	  REWRITE_TAC [pred_setTheory.IN_INTER] >>
	  REWRITE_TAC [pred_setTheory.IN_DIFF] >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]
	  ,
	  (* hi' cap hd' *)
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER] >>
	  Cases_on `x IN icleans dl`
	  >| [(* i *)
	      DISJ2_TAC >>
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]
	      >| [(* hd diff w *)
		  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF]
		  ,
		  (* i and d disjoint *)
		  IMP_RES_TAC abs_cl_trans_clean_disj_lem >>
	          METIS_TAC [pred_setTheory.IN_DISJOINT]
		 ]
	      ,
	      (* untouched *)
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]
	      >| [(* not d *)
		  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] >>
		  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] >>
		  FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER]
		  ,
		  (* d -> contradiction *)
		  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] >>
		  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]
		 ]
	     ]
	 ]
      ,
      (* <== *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] >>
      STRIP_TAC
      >| [(* x diff w d *)
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]
	  >| [(* EX diff hw diff w d *)
	      DISJ1_TAC >>
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF]
	      ,
	      (* hi cap hd diff w d *) 
	      DISJ2_TAC >>
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER] >>
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] >>
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] >>
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]
	     ]
	  ,
	  (* EX diff hw' cap d *)
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER]
	  ,
	  (* hd cap i *)
	  DISJ2_TAC >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER] >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] >>
	  IMP_RES_TAC abs_cl_trans_clean_disj_lem >>
	  IMP_RES_TAC abs_cl_trans_i_w_disj_lem >>
	  METIS_TAC [pred_setTheory.IN_DISJOINT]
	 ]
     ]
);

val ca_EXfl_SUC_lem = store_thm("ca_EXfl_SUC_lem", ``
!s s' s'' n dl. ca_kcomp s s' n /\ abs_ca_trans s' PRIV dl s'' ==> 
    (ca_EXfl s s'' (SUC n) = 
         (ca_EXfl s s' n DIFF (writes dl UNION dcleans dl)) UNION
	 (({pa | MEM pa IN CRex s} DIFF (ca_hw s s' n UNION writes dl))
	      INTER dcleans dl) UNION
	 (ca_hdcn s s' n INTER icleans dl))
``,
  RW_TAC std_ss [ca_EXfl_def, pred_setTheory.EXTENSION] >>
  IMP_RES_TAC ca_hw_SUC_lem >>
  IMP_RES_TAC ca_hdcn_SUC_lem >>
  IMP_RES_TAC ca_hic_SUC_lem >>
  ASM_REWRITE_TAC [] >>
  EQ_TAC
  >| [(* ==> *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] >>
      STRIP_TAC
      >| [(* EX diff hw' *)
	  DISJ1_TAC >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] >>
	  REWRITE_TAC [pred_setTheory.IN_INTER] >>
	  REWRITE_TAC [pred_setTheory.IN_DIFF] >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]
	  ,
	  (* hi' cap hd' *)
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER] >>
	  Cases_on `x IN icleans dl`
	  >| [(* i *)
	      DISJ2_TAC >>
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]
	      >| [(* hd diff w *)
		  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF]
		  ,
		  (* i and d disjoint *)
		  IMP_RES_TAC abs_ca_trans_clean_disj_lem >>
	          METIS_TAC [pred_setTheory.IN_DISJOINT]
		 ]
	      ,
	      (* untouched *)
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]
	      >| [(* not d *)
		  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] >>
		  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] >>
		  FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER]
		  ,
		  (* d -> contradiction *)
		  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] >>
		  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]
		 ]
	     ]
	 ]
      ,
      (* <== *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] >>
      STRIP_TAC
      >| [(* x diff w d *)
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]
	  >| [(* EX diff hw diff w d *)
	      DISJ1_TAC >>
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF]
	      ,
	      (* hi cap hd diff w d *) 
	      DISJ2_TAC >>
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER] >>
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] >>
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] >>
	      FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]
	     ]
	  ,
	  (* EX diff hw' cap d *)
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER]
	  ,
	  (* hd cap i *)
	  DISJ2_TAC >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_INTER] >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION] >>
	  FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF] >>
	  IMP_RES_TAC abs_ca_trans_clean_disj_lem >>
	  IMP_RES_TAC abs_ca_trans_i_w_disj_lem >>
	  METIS_TAC [pred_setTheory.IN_DISJOINT]
	 ]
     ]
);


(* discharge proof obligations *)

val Icmf_SE_init_xfer_lem = store_thm("Icmf_SE_init_xfer_lem", ``
Icmf_init_xfer_po ca_Icmf_SE cl_Icmf_SE Icoh_SE Icode_SE Icm_SE
``,
  REWRITE_TAC [Icmf_init_xfer_po_def, ca_Icmf_SE_def, cl_Icmf_SE_def] >>
  NTAC 3 STRIP_TAC >>
  REV_FULL_SIMP_TAC std_ss [cl_Dfl_init_lem] >>
  IMP_RES_TAC Rsim_exentry_lem >>
  FULL_SIMP_TAC std_ss [ca_Dfl_init_lem] >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  IMP_RES_TAC Rsim_cs_lem >>
  FULL_SIMP_TAC std_ss [ca_Inv_Mmu_fixed_def, cl_Inv_Mmu_fixed_def] >>
  `cl_fixmmu s Kvm Ktr <=> ca_fixmmu sc Kvm Ktr` by (
      METIS_TAC [Rsim_fixmmu_lem]
  ) >> 
  IMP_RES_TAC Rsim_CR_eq_lem >>
  FULL_SIMP_TAC std_ss [Icoh_SE_def] >>
  IMP_RES_TAC Rsim_cl_deps_lem >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Rsim_deps_cnt_lem >>
  IMP_RES_TAC deps_vdeps_eq_lem >>
  FULL_SIMP_TAC std_ss []
);

val Icodef_SE_init_xfer_lem = store_thm("Icodef_SE_init_xfer_lem", ``
Icodef_init_xfer_po ca_Icodef_SE cl_Icodef_SE 
                    Icoh_SE Icode_SE Icm_SE 
		    ca_Icmf_SE cl_Icmf_SE
``,
  REWRITE_TAC [Icodef_init_xfer_po_def, ca_Icodef_SE_def, cl_Icodef_SE_def,
	       ca_Icmf_SE_def, cl_Icmf_SE_def] >>
  NTAC 3 STRIP_TAC >>
  IMP_RES_TAC Rsim_exentry_lem >>
  FULL_SIMP_TAC std_ss [cl_h0_lem, ca_h0_lem] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.DIFF_EMPTY,
			pred_setTheory.INTER_EMPTY,
			pred_setTheory.NOT_IN_EMPTY] >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  `cl_CRex s = CRex sc` by ( IMP_RES_TAC Rsim_CRex_lem ) >>
  IMP_RES_TAC Rsim_cs_lem >>
  REV_FULL_SIMP_TAC std_ss [cl_EXfl_init_lem] >>
  FULL_SIMP_TAC std_ss [cl_EXfl_init_lem] >>
  FULL_SIMP_TAC std_ss [ca_EXfl_init_lem] >>
  IMP_RES_TAC Icode_SE_def >>
  NTAC 2 STRIP_TAC >>
  IMP_RES_TAC iCoh_lem >>
  IMP_RES_TAC isafe_CRex_lem >>
  ASM_REWRITE_TAC []
);

val Icmf_SE_xfer_lem = store_thm("Icmf_SE_xfer_lem", ``
ca_Icmf_po ca_Icmf_SE Icoh_SE Icode_SE Icm_SE  ==> 
    Icmf_xfer_po ca_Icmf_SE cl_Icmf_SE Icoh_SE Icode_SE Icm_SE
``,
  REWRITE_TAC [Icmf_xfer_po_def, ca_Icmf_SE_def, cl_Icmf_SE_def] >>
  NTAC 12 STRIP_TAC >> 
  `cl_exentry s` by ( cheat ) >>
  `exentry sc` by ( cheat ) >>
  (* IMP_RES_TAC ca_kcomp_exentry_lem >> *)
  (* IMP_RES_TAC cl_kcomp_exentry_lem >> *)

  IMP_RES_TAC ca_Dfl_init_lem >>
  FULL_SIMP_TAC std_ss [ca_II_def, cl_II_def] >>
  IMP_RES_TAC Rsim_cs_lem >>
  ASM_REWRITE_TAC [ca_Inv_Mmu_fixed_def, cl_Inv_Mmu_fixed_def] >>
  IMP_RES_TAC Inv_MDVA_Dfl_lem >>
  FULL_SIMP_TAC std_ss [Inv_lem] >>
  `cl_fixmmu s Kvm Ktr <=> ca_fixmmu sc Kvm Ktr` by (
      METIS_TAC [Rsim_fixmmu_lem]
  ) >>
  IMP_RES_TAC cl_Inv_Mmu_fixed_lem >>
  `!d. MEM d dl ==> CA (opd d)` by (
      FULL_SIMP_TAC std_ss [cl_Icmf_SE_def] >>
      IMP_RES_TAC cl_Inv_Mmu_fixed_lem >>
      IMP_RES_TAC abs_cl_trans_fixmmu_CA_lem
  ) >>
  IMP_RES_TAC ca_Dfl_dCoh_lem >>
  `{pa | MEM pa IN CR sc} SUBSET ca_Dfl sc sc'' (SUC n)` by (
      RW_TAC std_ss [ca_Dfl_def, pred_setTheory.SUBSET_DEF, 
		     pred_setTheory.IN_UNION]
  ) >>
  IMP_RES_TAC cl_Dfl_SUC_lem >>
  IMP_RES_TAC ca_Dfl_SUC_lem >>
  `cl_Dfl s s' n = ca_Dfl sc sc' n` by ( METIS_TAC [Dfl_bisim_lem] ) >>
  FULL_SIMP_TAC std_ss [ca_Icmf_SE_def, cl_Icmf_SE_def] >>
  `cl_deps s'' = ca_deps sc''` by ( IMP_RES_TAC Rsim_cl_deps_lem ) >>
  `cl_vdeps s'' = ca_vdeps sc''` by (
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC Rsim_deps_cnt_lem >>
      IMP_RES_TAC deps_vdeps_eq_lem
  ) >>
  REV_FULL_SIMP_TAC std_ss [cl_Inv_Mmu_fixed_def] >>
  FULL_SIMP_TAC std_ss [cl_Inv_Mmu_fixed_def] >>
  RW_TAC std_ss [] >>
  `cl_MDVA s Kvm = cl_MDVA s'' Kvm` by ( METIS_TAC [cl_MDVA_lem] ) >>
  `MDVA sc Kvm = cl_MDVA s Kvm` by ( METIS_TAC [Rsim_MDVA_lem] ) >>
  FULL_SIMP_TAC std_ss [Icoh_SE_def] >>
  IMP_RES_TAC dCoh_subset_lem >>
  IMP_RES_TAC Rsim_MDVA_eq_dCoh_cl_lem >>
  `Cv sc r = cl_Cv s r` by ( METIS_TAC [Rsim_MDVA_eq_cl_lem] ) >>
  METIS_TAC []
);

val Icodef_SE_xfer_lem = store_thm("Icodef_SE_xfer_lem", ``
ca_Icmf_po ca_Icmf_SE Icoh_SE Icode_SE Icm_SE ==> 
Icodef_xfer_po ca_Icodef_SE cl_Icodef_SE 
               Icoh_SE Icode_SE Icm_SE 
	       ca_Icmf_SE cl_Icmf_SE
``,
  REWRITE_TAC [Icodef_xfer_po_def, ca_Icodef_SE_def, cl_Icodef_SE_def] >>
  NTAC 10 STRIP_TAC >>
  IMP_RES_TAC ca_kcomp_exentry_lem >>
  IMP_RES_TAC cl_kcomp_exentry_lem >>
  IMP_RES_TAC ca_EXfl_init_lem >>
  `!m s1 sc1.
       m <= n /\ cl_kcomp s s1 m /\ ca_kcomp sc sc1 m ==>
           Rsim sc1 s1 /\ ca_Icmf_SE sc sc1 m` by ( 
      NTAC 4 STRIP_TAC >>
      RES_TAC >>
      FULL_SIMP_TAC std_ss [ca_II_def]
  ) >>
  `n <= n` by ( FULL_SIMP_TAC arith_ss [] ) >>
  RES_TAC >>
  FULL_SIMP_TAC std_ss [ca_II_def, cl_II_def, Inv_lem] >>
  IMP_RES_TAC Rsim_cs_lem >>
  `(cl_hw s s' n = ca_hw sc sc' n) /\
   (cl_hdc s s' n = ca_hdc sc sc' n) /\
   (cl_hdcn s s' n = ca_hdcn sc sc' n) /\
   (cl_hic s s' n = ca_hic sc sc' n)` by ( METIS_TAC [hist_bisim_SE_lem] ) >>
  `cl_CRex s = CRex sc` by ( METIS_TAC [Rsim_CRex_lem] ) >>
  IMP_RES_TAC cl_EXfl_SUC_lem >>
  IMP_RES_TAC ca_EXfl_SUC_lem >>
  `cl_EXfl s s' n = ca_EXfl sc sc' n` by ( METIS_TAC [EXfl_bisim_lem] ) >>
  METIS_TAC [ca_Icodef_icoh_clean_lem]
);

val Icm_f_SE_lem = store_thm("Icm_f_SE_lem", ``
Icm_f_po ca_Icmf_SE ca_Icodef_SE Icoh_SE Icode_SE Icm_SE
``,
  RW_TAC std_ss [Icm_f_po_def, Icm_SE_def]
);

val cl_Icmf_SE_lem = store_thm("cl_Icmf_SE_lem", ``
cl_Icmf_po cl_Icmf_SE
``,
  RW_TAC std_ss [cl_Icmf_po_def, cl_Icmf_SE_def] >>
  IMP_RES_TAC cl_Inv_Mmu_fixed_lem >>
  IMP_RES_TAC abs_cl_trans_fixmmu_CA_lem
);

val ca_Icmf_SE_lem = store_thm("ca_Icmf_SE_lem", ``
ca_Icmf_po ca_Icmf_SE Icoh_SE Icode_SE Icm_SE
``,
  RW_TAC std_ss [ca_Icmf_po_def, ca_Icmf_SE_def] >>
  IMP_RES_TAC dCoh_subset_lem
);

val ca_Icodef_SE_lem = store_thm("ca_Icodef_SE_lem", ``
ca_Icodef_po ca_Icodef_SE Icoh_SE Icode_SE Icm_SE ca_Icmf_SE
``,
  REWRITE_TAC [ca_Icodef_po_def, ca_Icodef_SE_def, ca_Icmf_SE_def] >>
  NTAC 4 STRIP_TAC >>
  IMP_RES_TAC ca_Inv_Mmu_fixed_lem >>
  `ca_Tr s' (VApc s'.cs) = Ktr (VApc s'.cs)` by (
      IMP_RES_TAC ca_fixmmu_Tr_lem
  ) >>
  IMP_RES_TAC icoh_clean_hist_lem >>
  FULL_SIMP_TAC std_ss [ca_EXfl_def]
);

val Inv_rebuild_SE_lem = store_thm("Inv_rebuild_SE_lem", ``
cm_user_po Icoh_SE Icode_SE Icm_SE ==> 
Inv_rebuild_po Icoh_SE Icode_SE Icm_SE 
               ca_Icmf_SE ca_Icodef_SE cl_Icmf_SE cl_Icodef_SE
``,
  REWRITE_TAC [Inv_rebuild_po_def] >>
  NTAC 7 STRIP_TAC >>
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
	  `pa IN cl_Dfl s s' n` by ( 
	      FULL_SIMP_TAC std_ss [Inv_lem, cl_II_def, 
				    cl_Icmf_SE_def, 
				    pred_setTheory.SUBSET_DEF,
				    pred_setTheory.IN_GSPEC_IFF] >>
	      RES_TAC
	  ) >> (* Dfl_bisim_lem *)
	  `cl_Dfl s s' n = ca_Dfl sc sc' n` by ( cheat ) >>
	  FULL_SIMP_TAC std_ss [ca_II_def, ca_Icmf_SE_def] >>
	  IMP_RES_TAC Rsim_dCoh_Cv_lem
	  ,
          (* register *)
	  IMP_RES_TAC Rsim_lem
	 ]
      ,
      (* Icoh *)
      RW_TAC std_ss [Icoh_SE_def, dCoh_lem2] >>
      `cl_Dfl s s' n = ca_Dfl sc sc' n` by ( cheat ) >>
      `{pa | MEM pa IN cl_CR s'} SUBSET ca_Dfl sc sc' n` by ( 
          FULL_SIMP_TAC std_ss [Inv_lem, cl_II_def, 
				cl_Icmf_SE_def, 
				pred_setTheory.SUBSET_DEF] >>
	  RES_TAC
      ) >> 
      FULL_SIMP_TAC std_ss [ca_II_def, ca_Icmf_SE_def] >>
      IMP_RES_TAC dCoh_subset_lem >> 
      `cl_CR s' = CR sc'` by ( METIS_TAC [Rsim_CR_eq_dCoh_cl_lem] ) >>
      FULL_SIMP_TAC std_ss [dCoh_lem2]
      ,
      (* Icode *)
      REWRITE_TAC [Icode_SE_def, iCoh_CRex_lem, isafe_CRex_lem2] >>
      `{pa | MEM pa IN CRex sc'} SUBSET ca_EXfl sc sc' n` suffices_by (
          FULL_SIMP_TAC std_ss [ca_II_def, ca_Icodef_SE_def, 
				pred_setTheory.SUBSET_DEF,
			        pred_setTheory.IN_GSPEC_IFF] >>
	  STRIP_TAC >>
	  FULL_SIMP_TAC std_ss [ca_EXfl_def] >>
	  METIS_TAC [pred_setTheory.IN_UNION, pred_setTheory.IN_INTER]
      ) >>
      `CRex sc' = cl_CRex s'` by ( 
          IMP_RES_TAC Rsim_CRex_lem >>
          ASM_REWRITE_TAC []
      ) >>  (* EXfl_bisim_lem *)
      `cl_EXfl s s' n = ca_EXfl sc sc' n` by ( cheat ) >>
      FULL_SIMP_TAC std_ss [cl_II_def, cl_Icodef_SE_def]
     ]
);

val discharge_kernel_SE_lem = store_thm("discharge_kernel_SE_lem", ``
    cm_user_po Icoh_SE Icode_SE Icm_SE 
        ==> 
    cm_kernel_po cl_Icmf_SE cl_Icodef_SE ca_Icmf_SE ca_Icodef_SE 
                 Icoh_SE Icode_SE Icm_SE
``,
  STRIP_TAC >> 
  REWRITE_TAC [cm_kernel_po_def] >>
  MATCH_MP_TAC (
      prove(``a /\ b /\ (f ==> c) /\ (f ==> d) /\ e /\ f /\ g /\ h /\ i ==>
	      a /\ b /\ c /\ d /\ e /\ f /\ g /\ h /\ i``, PROVE_TAC [])
  ) >>
  RW_TAC std_ss [Icmf_SE_init_xfer_lem,
		 Icodef_SE_init_xfer_lem,
		 Icmf_SE_xfer_lem,
		 Icodef_SE_xfer_lem,
		 Icm_f_SE_lem,
		 cl_Icmf_SE_lem, 
		 ca_Icmf_SE_lem,
		 ca_Icodef_SE_lem,
		 Inv_rebuild_SE_lem]
);

val Inv_kernel_preserved_SE_thm = store_thm("Inv_kernel_preserved_SE_thm", ``
!sc sc' n. 
    cl_Inv_po
 /\ cl_II_po cl_Icmf_SE cl_Icodef_SE
 /\ Inv Icoh_SE Icode_SE Icm_SE sc
 /\ ca_wrel sc sc' n
        ==>
    Inv Icoh_SE Icode_SE Icm_SE sc'
``, 
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC Inv_kernel_preserved_thm >>
  HINT_EXISTS_TAC >> 
  ASSUME_TAC discharge_user_SE_lem >>
  ASSUME_TAC discharge_kernel_SE_lem >>
  METIS_TAC []
);

val kernel_integrity_sim_SE_thm = store_thm("kernel_integrity_sim_SE_thm", ``
!s sc sc' n. 
    cl_Inv_po
 /\ cl_II_po cl_Icmf_SE cl_Icodef_SE
 /\ Inv Icoh_SE Icode_SE Icm_SE sc
 /\ Rsim sc s
 /\ ca_wrel sc sc' n
        ==>
?s'. 
    cl_wrel s s' n
 /\ Rsim sc' s'
 /\ Inv Icoh_SE Icode_SE Icm_SE sc'
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC kernel_integrity_sim_thm >>
  HINT_EXISTS_TAC >> 
  ASSUME_TAC discharge_user_SE_lem >>
  ASSUME_TAC discharge_kernel_SE_lem >>
  METIS_TAC []
);

val overall_integrity_SE_thm = store_thm("overall_integrity_SE_thm", ``
!sc sc'. 
    cl_Inv_po
 /\ cl_II_po cl_Icmf_SE cl_Icodef_SE
 /\ Inv Icoh_SE Icode_SE Icm_SE sc
 /\ Wrel sc sc'
        ==>
    Inv Icoh_SE Icode_SE Icm_SE sc'
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC overall_integrity_thm >>
  HINT_EXISTS_TAC >> 
  ASSUME_TAC discharge_user_SE_lem >>
  ASSUME_TAC discharge_kernel_SE_lem >>
  METIS_TAC []
);

(*********** finish ************)

val _ = export_theory();
