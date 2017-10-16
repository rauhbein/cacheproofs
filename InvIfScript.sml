(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;
open hwTheory;
open cachelessTheory;

val _ = new_theory "InvIf";

(*********** software proof obligations ***********)

(* critical resources *)

val CR_exists = prove (``
?CR:core_state # mem_view -> resource set.
!c c' mv mv'. ((!r. r IN CR(c,mv) ==> (CV c mv r = CV c' mv' r)) ==>
	       (CR(c,mv) = CR(c',mv')))
	   /\ (!r. reg_res r /\ r IN CR(c,mv) ==> ?r'. r = COREG r')
``,
  EXISTS_TAC ``\ (c,mv):core_state # mem_view. EMPTY:resource set`` >>
  RW_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.NOT_IN_EMPTY]
);  

val CR_spec = new_specification ("CR_spec",
  ["CR_"], CR_exists);

val CR_def = Define `CR s = CR_(s.cs, dmvca s.ms)`;

val CRex_def = Define `CRex s = 
{r | (?pa. r = MEM pa) /\ r IN CR s /\ ?m. Mon s r m EX}`;

(* exported theorems *)

val CR_oblg = store_thm("CR_oblg", ``
!s s'. (!r. r IN CR s ==> (Cv s r = Cv s' r)) ==> (CR s = CR s')
``,
  RW_TAC std_ss [Cv_def, CR_def] >>
  IMP_RES_TAC CR_spec
);

val CR_coreg_oblg = store_thm("CR_coreg_oblg", ``
!s s' r. reg_res r /\ r IN CR s /\ (s'.cs.coreg = s.cs.coreg) ==> 
    (Cv s r = Cv s' r) 
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [CR_def] >>
  IMP_RES_TAC CR_spec >>
  RW_TAC std_ss [Cv_def, coreIfTheory.CV_def]
);

val CRex_oblg = store_thm("CRex_oblg", ``
!s r. r IN CRex s ==> (?pa. (r = MEM pa)) /\ r IN CR s /\ ?m. Mon s r m EX
``,
  RW_TAC std_ss [CRex_def] >> (
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
      RW_TAC std_ss []
  ) >>
  HINT_EXISTS_TAC >>
  ASM_REWRITE_TAC []
);

(* Integrity obligations *)

val Ifun_CR_po = Define `Ifun_CR_po I =
!s s'. (!r. r IN CR s ==> (Cv s r = Cv s' r)) ==> (I s <=> I s')
`; 

val Ifun_MD_po = Define `Ifun_MD_po I =
!s. I s ==> MD s SUBSET CR s
`; 

val Ifun_Mon_po = Define `Ifun_Mon_po I =
!s r. I s /\ r IN CR s ==> ~Mon s r USER W
`; 

val Icoh_CR_po = Define `Icoh_CR_po I = 
!s s'. dCoh s.ms {pa | MEM pa IN CR s} 
    /\ dCoh s'.ms {pa | MEM pa IN CR s'}
    /\ (!r. r IN CR s ==> (Cv s r = Cv s' r))
        ==>
    (I s <=> I s')
`;

val Icoh_dCoh_po = Define `Icoh_dCoh_po I = 
!s. I s ==> dCoh s.ms {pa | MEM pa IN CR s}
`;

val Icode_CR_po = Define `Icode_CR_po I = 
!s s'. iCoh s.ms {pa | MEM pa IN CRex s}
    /\ iCoh s'.ms {pa | MEM pa IN CRex s'}
    /\ isafe s {pa | MEM pa IN CRex s}
    /\ isafe s' {pa | MEM pa IN CRex s'}
    /\ (!r. r IN CR s ==> (Cv s r = Cv s' r))
        ==>
    (I s <=> I s')
`;

val Icode_iCoh_po = Define `Icode_iCoh_po I = 
!s. I s ==> iCoh s.ms {pa | MEM pa IN CRex s}
`;

val Icode_isafe_po = Define `Icode_isafe_po I = 
!s. I s ==> isafe s {pa | MEM pa IN CRex s}
`;

val Icm_po = Define `Icm_po I Icm =
!s s'. I s /\ drvbl s s' ==> Icm s'
`;

val Ifun_exists = store_thm("Ifun_exists", ``
?Ifun. Ifun_CR_po Ifun /\ Ifun_MD_po Ifun /\ Ifun_Mon_po Ifun
``,
  EXISTS_TAC ``\s. MD s SUBSET CR s 
                /\ !r. r IN CR s ==> ~Mon s r USER W`` >>
  RW_TAC std_ss [Ifun_CR_po, Ifun_MD_po, Ifun_Mon_po] >>
  IMP_RES_TAC CR_oblg >>
  EQ_TAC 
  >| [(* ==> *)
      STRIP_TAC >>
      `!r. r IN MD s ==> (Cv s r = Cv s' r)` by (
          REPEAT STRIP_TAC >>
	  IMP_RES_TAC pred_setTheory.SUBSET_DEF >>
	  RES_TAC
      ) >>
      IMP_RES_TAC MD_lem >>
      METIS_TAC [Mon_lem]
      ,
      (* <== *)
      STRIP_TAC >>
      `!r. r IN MD s' ==> (Cv s' r = Cv s r)` by (
          REPEAT STRIP_TAC >>
	  IMP_RES_TAC pred_setTheory.SUBSET_DEF >>
	  FULL_SIMP_TAC std_ss []
      ) >>
      IMP_RES_TAC MD_lem >>
      METIS_TAC [Mon_lem]
     ]
);

val Icoh_exists = store_thm("Icoh_exists", ``
?Icoh. Icoh_CR_po Icoh /\ Icoh_dCoh_po Icoh 
``,
  EXISTS_TAC ``\s. dCoh s.ms {pa | MEM pa IN CR s}`` >>
  RW_TAC std_ss [Icoh_dCoh_po, Icoh_CR_po]
);

val Icode_exists = store_thm("Icode_exists", ``
?Icode. Icode_CR_po Icode /\ Icode_iCoh_po Icode /\ Icode_isafe_po Icode
``,
  EXISTS_TAC ``\s. iCoh s.ms {pa | MEM pa IN CRex s}
                /\ isafe s {pa | MEM pa IN CRex s}`` >>
  RW_TAC std_ss [Icode_CR_po, Icode_iCoh_po, Icode_isafe_po]
);

val Inv_exists = store_thm("Inv_exists", ``
?Inv Ifun Icoh Icode Icm.
    (!s. Inv s <=> Ifun s /\ Icoh s /\ Icode s /\ Icm s)
 /\ Ifun_CR_po Ifun /\ Ifun_MD_po Ifun /\ Ifun_Mon_po Ifun
 /\ Icoh_CR_po Icoh /\ Icoh_dCoh_po Icoh
 /\ Icode_CR_po Icode /\ Icode_iCoh_po Icode /\ Icode_isafe_po Icode
 /\ Icm_po Inv Icm
``,
  ASSUME_TAC Ifun_exists >>
  ASSUME_TAC Icoh_exists >>
  ASSUME_TAC Icode_exists >>
  FULL_SIMP_TAC std_ss [] >>
  EXISTS_TAC ``\s:hw_state. Ifun s /\ Icoh s /\ Icode s`` >>
  EXISTS_TAC ``Ifun:hw_state -> bool`` >>
  EXISTS_TAC ``Icoh:hw_state -> bool`` >>
  EXISTS_TAC ``Icode:hw_state -> bool`` >>
  EXISTS_TAC ``\s:hw_state. T`` >>
  RW_TAC std_ss [Icm_po]
);

val Inv_spec = new_specification ("Inv_spec",
  ["Inv", "Ifun", "Icoh", "Icode", "Icm"], Inv_exists);

(* exported theorems *)

val Ifun_CR_oblg = store_thm("Ifun_CR_oblg", ``
!s s'. (!r. r IN CR s ==> (Cv s r = Cv s' r)) ==> (Ifun s <=> Ifun s')
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC Inv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Ifun_CR_po  
); 

val Ifun_MD_oblg = store_thm("Ifun_MD_oblg", ``
!s r. Ifun s /\ r IN MD s ==> r IN CR s
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC Inv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Ifun_MD_po >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF]
); 

val Ifun_Mon_oblg = store_thm("Ifun_Mon_oblg", ``
!s r. Ifun s /\ r IN CR s ==> ~Mon s r USER W
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  ASSUME_TAC Inv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Ifun_Mon_po 
); 

val Icoh_CR_oblg = store_thm("Icoh_CR_oblg", ``
!s s'. dCoh s.ms {pa | MEM pa IN CR s} 
    /\ dCoh s'.ms {pa | MEM pa IN CR s'}
    /\ (!r. r IN CR s ==> (Cv s r = Cv s' r))
        ==>
    (Icoh s <=> Icoh s')
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC Inv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Icoh_CR_po 
); 

val Icoh_dCoh_oblg = store_thm("Icoh_dCoh_oblg", ``
!s. Icoh s ==> dCoh s.ms {pa | MEM pa IN CR s}
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC Inv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Icoh_dCoh_po 
); 

val Icode_CR_oblg = store_thm("Icode_CR_oblg", ``
!s s'. iCoh s.ms {pa | MEM pa IN CRex s}
    /\ iCoh s'.ms {pa | MEM pa IN CRex s'}
    /\ isafe s {pa | MEM pa IN CRex s}
    /\ isafe s' {pa | MEM pa IN CRex s'}
    /\ (!r. r IN CR s ==> (Cv s r = Cv s' r))
        ==>
    (Icode s <=> Icode s')
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC Inv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Icode_CR_po 
);

val Icode_iCoh_oblg = store_thm("Icode_iCoh_oblg", ``
!s. Icode s ==> iCoh s.ms {pa | MEM pa IN CRex s}
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC Inv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Icode_iCoh_po 
);

val Icode_isafe_oblg = store_thm("Icode_isafe_oblg", ``
!s. Icode s ==> isafe s {pa | MEM pa IN CRex s}
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC Inv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Icode_isafe_po 
);

val Icm_oblg = store_thm("Icm_oblg", ``
!s s'. Inv s /\ drvbl s s' ==> Icm s'
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC Inv_spec >>
  REV_FULL_SIMP_TAC std_ss [Icm_po] >>
  RES_TAC
); 

val Inv_oblg = store_thm("Inv_oblg", ``
!s. Inv s <=> Ifun s /\ Icoh s /\ Icode s /\ Icm s
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC Inv_spec >>
  FULL_SIMP_TAC std_ss []
); 

(******** Simulation relation ********)

val Mv_def = Define `
   (Mv sc (MEM pa) = dmvalt sc.ms T pa)
/\ (Mv sc r = Cv sc r)
`;

val Rsim_def = Define `Rsim sc s = 
!r. cl_Cv s r = Mv sc r
`;

val Rsim_lem = store_thm("Rsim_lem", ``
!sc s. Rsim sc s <=>    (!r. reg_res r ==> (cl_Cv s r = Cv sc r)) 
                     /\ (!pa. MVcl s.M T pa = dmvalt sc.ms T pa)
``,
  RW_TAC std_ss [Rsim_def] >>
  EQ_TAC 
  >| [(* ==> *)
      REPEAT STRIP_TAC
      >| [(* register *)
	  PAT_X_ASSUM ``!r. x`` (
	      fn thm => ASSUME_TAC ( SPEC ``r:resource`` thm )
	  ) >>
	  Cases_on `r` >> ( 
	      FULL_SIMP_TAC std_ss [Mv_def, coreIfTheory.reg_res_def] 
	  ) 
	  ,
	  (* memory *)
	  PAT_X_ASSUM ``!r. x`` (
	      fn thm => ASSUME_TAC ( SPEC ``MEM pa`` thm )
	  ) >>
	  FULL_SIMP_TAC std_ss [cl_Cv_def, Mv_def, coreIfTheory.CV_def]
	 ]
      ,
      (* <== *)
      REPEAT STRIP_TAC >>
      Cases_on `r` >> (
          FULL_SIMP_TAC std_ss [cl_Cv_def, Mv_def, 
				coreIfTheory.reg_res_def,
				coreIfTheory.CV_def]
      )
     ]	  
);

val Rsim_dCoh_lem = store_thm("Rsim_dCoh_lem", ``
!sc s As. Rsim sc s /\ dCoh sc.ms As ==>
    !pa. pa IN As ==> (MVcl s.M T pa = dmvca sc.ms T pa)
``,
  RW_TAC std_ss [Rsim_lem, dCoh_alt_lem]
);

val Rsim_iCoh_lem = store_thm("Rsim_iCoh_lem", ``
!sc s As. Rsim sc s /\ dCoh sc.ms As /\ iCoh sc.ms As ==>
    !pa. pa IN As /\ ~dirty sc.ms pa ==> (MVcl s.M T pa = imv sc.ms T pa)
``,
  RW_TAC std_ss [Rsim_lem] >>
  IMP_RES_TAC dCoh_alt_lem >>
  IMP_RES_TAC dCoh_lem >>
  IMP_RES_TAC msIfTheory.iCoh_def >>
  IMP_RES_TAC imv_dmv_lem >>
  RW_TAC std_ss []
);


(******** Cache-less Invariants and proof obligations **********)

(* critical resources *)

val cl_CR_def = Define `cl_CR s = CR_(s.cs, MVcl s.M)`;

val cl_CR_lem = store_thm("cl_CR_lem", ``
!s sca. (!r. r IN cl_CR s ==> (cl_Cv s r = Cv sca r)) ==>
    (cl_CR s = CR sca)
``,
  RW_TAC std_ss [cl_CR_def, CR_def, cl_Cv_def, Cv_def] >>
  IMP_RES_TAC CR_spec
);

val CR_cl_lem = store_thm("CR_cl_lem", ``
!s sca. (!r. r IN CR sca ==> (cl_Cv s r = Cv sca r)) ==>
    (cl_CR s = CR sca)
``,
  RW_TAC std_ss [cl_CR_def, CR_def, cl_Cv_def, Cv_def] >>
  METIS_TAC [CR_spec]
);

val cl_MD_lem = store_thm("cl_CR_lem", ``
!s sca. (!r. r IN cl_MD s ==> (cl_Cv s r = Cv sca r)) ==>
    (cl_MD s = MD sca)
``,
  RW_TAC std_ss [cl_MD_def, MD_def, cl_Cv_def, Cv_def] >>
  IMP_RES_TAC MD__lem
);

val MD_cl_lem = store_thm("CR_cl_lem", ``
!s sca. (!r. r IN MD sca ==> (cl_Cv s r = Cv sca r)) ==>
    (cl_MD s = MD sca)
``,
  RW_TAC std_ss [cl_MD_def, MD_def, cl_Cv_def, Cv_def] >>
  METIS_TAC [MD__lem]
);

(* software invariants *)

val cl_Inv_exists = store_thm("cl_Inv_exists", ``
?cl_Inv.
!s sca. (!r. r IN cl_CR s ==> (cl_Cv s r = Cv sca r)) ==>
    (cl_Inv s <=> Ifun sca)
``,
  EXISTS_TAC ``\s.
      !sca. (!r. r IN cl_CR s ==> (cl_Cv s r = Cv sca r)) ==> Ifun sca`` >>
  RW_TAC std_ss [] >>
  EQ_TAC
  >| [(* ==> *)
      REPEAT STRIP_TAC >>
      PAT_X_ASSUM ``!sca'. x ==> Ifun sca'`` (
          fn thm => ASSUME_TAC ( SPEC ``sca:hw_state`` thm )
      ) >>
      FULL_SIMP_TAC std_ss []
      ,
      (* <== *)
      REPEAT STRIP_TAC >>
      IMP_RES_TAC cl_CR_lem >>
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC Ifun_CR_oblg
     ]
);

val cl_Inv_spec = new_specification ("cl_Inv_spec",
  ["cl_Inv"], cl_Inv_exists);

val cl_Inv_preserve_po = Define `cl_Inv_preserve_po =
!s s'. cl_Inv s /\ cl_wrel s s' ==> cl_Inv s'
`;

(* NOTE: omitting Kvm and PC condition here, 
 * just need:
 ** executable addresses are in CR
 ** only cacheable addresses are used 
 ** PRIV configuration not changed by kernel (needed to couple Mon)
TODO?: pc always at executable address -> 
   avoids nexted exceptions, not modeled here, not important for proof
*)
val cl_Inv_Mmu_po = Define `cl_Inv_Mmu_po = 
!s s' n. cl_Inv s /\ cl_kcomp s s' n ==>
    (!va pa c acc. (Mmu_(s.cs, MVcl s.M, va, PRIV, acc) = SOME (pa,c)) ==>
                   ((acc = EX) ==> MEM pa IN cl_CR s) /\ (c = T))
 /\ (!va acc. Mmu_(s'.cs, MVcl s'.M, va, PRIV, acc) = 
              Mmu_(s.cs, MVcl s.M, va, PRIV, acc))
`;

(* some lemmas *)

val cl_Inv_Mmu_lem = store_thm("cl_Inv_Mmu_req_lem", ``
!s s' req s'' n. cl_Inv_Mmu_po /\ cl_Inv s /\ cl_kcomp s s' n 
        ==>
    (!va pa c acc. (Mmu_(s'.cs, MVcl s'.M, va, PRIV, acc) = SOME (pa,c)) ==>
                   ((acc = EX) ==> MEM pa IN cl_CR s) /\ (c = T))
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  REPEAT GEN_TAC >>
  IMP_RES_TAC cl_Inv_Mmu_po >>
  ASM_REWRITE_TAC [] >>
  STRIP_TAC >>
  RES_TAC >>
  ASM_REWRITE_TAC []
);

val cl_Inv_Mmu_req_lem = store_thm("cl_Inv_Mmu_req_lem", ``
!s s' req s'' n. cl_Inv_Mmu_po /\ cl_Inv s /\ req <> NOREQ 
	      /\ cl_kcomp s s' n /\ cl_trans s' PRIV req s''
        ==>
    (Freq req ==> MEM (Adr req) IN cl_CR s) /\ CAreq req
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC cl_trans_core_req_lem >>
  IMP_RES_TAC core_req_mmu_lem >>
  IMP_RES_TAC cl_Inv_Mmu_lem >>
  ASM_REWRITE_TAC [] >>
  IMP_RES_TAC not_NOREQ_lem
  >| [(* Dreq *)
      IMP_RES_TAC Dreq_lem >>
      RW_TAC std_ss [Freq_def]
      ,
      (* Freq *)
      IMP_RES_TAC Freq_lem >>
      FULL_SIMP_TAC std_ss [Acc_def]
     ]
);

val Rsim_CR_lem = store_thm("Rsim_CR_lem", ``
!sc s. Rsim sc s /\ Icoh sc ==>
    (!r. r IN CR sc ==> (cl_Cv s r = Cv sc r))
``,
  REPEAT STRIP_TAC >>
  Cases_on `reg_res r`
  >| [(* register *)
      FULL_SIMP_TAC std_ss [Rsim_lem]
      ,
      (* memory *)
      ASSUME_TAC ( SPEC ``r:resource`` coreIfTheory.res_cases ) >>
      FULL_SIMP_TAC std_ss [] >> (
          FULL_SIMP_TAC std_ss [] 
      ) >>
      IMP_RES_TAC Icoh_dCoh_oblg >>
      `pa IN {pa | MEM pa IN CR sc}` by (
          FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF]
      ) >>
      IMP_RES_TAC Rsim_dCoh_lem >>
      RW_TAC std_ss [cl_Cv_def, Cv_def, coreIfTheory.CV_def]
     ]
);

val Rsim_cl_CR_lem = store_thm("Rsim_CR_lem", ``
!sc s. Rsim sc s /\ Icoh sc ==>
    (!r. r IN cl_CR s ==> (cl_Cv s r = Cv sc r))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_CR_lem >>
  IMP_RES_TAC CR_cl_lem >>
  FULL_SIMP_TAC std_ss []
);

val Rsim_MD_lem = store_thm("Rsim_MD_lem", ``
!sc s. Rsim sc s /\ Icoh sc /\ Ifun sc ==>
    (!r. cl_MD s = MD sc)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_CR_lem >>
  MATCH_MP_TAC MD_cl_lem >>
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Ifun_MD_oblg >>
  RES_TAC 
);


val Rsim_Mon_lem = store_thm("Rsim_Mon_lem", ``
!sc s. Rsim sc s /\ Icoh sc /\ Ifun sc ==>
    (!r m ac. cl_Mon s r m ac = Mon sc r m ac)
``,
  RW_TAC std_ss [cl_Mon_def, Mon_def] >>
  MATCH_MP_TAC Mon__lem >>
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_MD_lem >>
  IMP_RES_TAC Ifun_MD_oblg >>
  FULL_SIMP_TAC std_ss [cl_MD_def, MD_def] >>
  RES_TAC >>
  IMP_RES_TAC Rsim_CR_lem >>
  FULL_SIMP_TAC std_ss [cl_Cv_def, Cv_def]
);

(* internal invariants *)

val cmfinv_xfer_def = Define `cmfinv_xfer Ic I =
!sc sc' s s'. Inv sc /\ cl_Inv s /\ Icoh sc' /\ Icode sc' 
           /\ Rsim sc s /\ Rsim sc' s'
        ==>
    (Ic sc sc' <=> I s s')
`;

val cmfinv_sinv_def = Define `cmfinv_sinv If Is =
!sc sc'. Inv sc /\ Icoh sc' /\ Icode sc' /\ If sc sc' ==> Is sc'
`;



(*********** finish ************)

val _ = export_theory();


