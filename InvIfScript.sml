(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;
open hwTheory;
open cachelessTheory;

val _ = new_theory "InvIf";

(*********** software proof obligations ***********)

(* critical resources and invariant obligations *)

val Ifun_CR_po = Define `Ifun_CR_po I CR =
!c c' mv mv'. I(c,mv) ==>
    ((!r. r IN CR(c,mv) ==> (CV c mv r = CV c' mv' r)) ==>
        (CR(c,mv) = CR(c',mv')) /\ I(c',mv'))
 /\ (!r. reg_res r /\ r IN CR(c,mv) ==> ?r'. r = COREG r')
`;

val Ifun_CR_po2 = Define `Ifun_CR_po2 I CR =
!c c' mv mv'. I(c,mv) ==>
    ((!r. r IN CR(c',mv') ==> (CV c' mv' r = CV c mv r)) ==>
        (CR(c',mv') = CR(c,mv)) /\ I(c',mv'))
 /\ (!r. reg_res r /\ r IN CR(c,mv) ==> ?r'. r = COREG r')
`;

(* val Ifun_CR_po = Define `Ifun_CR_po I CR = *)
(* !c c' mv mv'. (!r. r IN CR(c,mv) ==> (CV c mv r = CV c' mv' r)) ==>  *)
(*     (I(c,mv) <=> I(c',mv')) *)
(* `;  *)

val Ifun_MD_po = Define `Ifun_MD_po I CR =
!c mv. I(c,mv) ==> MD_(c,mv,UNIV:vadr set) SUBSET CR(c,mv)
`; 

val Ifun_Mon_po = Define `Ifun_Mon_po I CR =
!c mv r. I(c,mv) /\ r IN CR(c,mv) ==> ~Mon_(c,mv,r,USER,W)
`; 

val Ifun_CR_exists = prove (``
?CR:core_state # mem_view -> resource set
 Ifun:core_state # mem_view -> bool.
    Ifun_CR_po Ifun CR
 /\ Ifun_CR_po2 Ifun CR
 /\ Ifun_MD_po Ifun CR
 /\ Ifun_Mon_po Ifun CR
``,
  Q.ABBREV_TAC `Cr = \(c,mv):core_state # mem_view. MD_(c,mv,UNIV:vadr set)` >>
  EXISTS_TAC ``Cr:core_state # mem_view -> resource set`` >>
  EXISTS_TAC ``\(c,mv). MD_(c,mv,UNIV:vadr set) SUBSET Cr(c,mv) 
                /\ !r. r IN Cr(c,mv) ==> ~Mon_(c,mv,r,USER,W)`` >>
  Q.UNABBREV_TAC `Cr` >>
  RW_TAC std_ss [Ifun_Mon_po, Ifun_CR_po2, Ifun_MD_po, Ifun_CR_po]
  >| [(* CR = CR' *)
      IMP_RES_TAC MD__lem
      ,
      (* MD SUBSET CR *)
      FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_REFL]
      ,
      (* ~W CR *)
      RES_TAC >>
      IMP_RES_TAC MD__lem >>
      IMP_RES_TAC Mon__lem >>
      FULL_SIMP_TAC std_ss []
      ,
      (* CR coreg *)
      `(!r. reg_res r /\ r IN MD_ (c,mv,UNIV:vadr set) ==> 
            ?r'. r = COREG r')` by (
          METIS_TAC [coreIfTheory.Mmu_MD_spec]
      ) >>
      RES_TAC >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC []
      ,
      (* CR = CR' *)
      IMP_RES_TAC MD__lem
      ,
      (* MD SUBSET CR *)
      FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_REFL]
      ,
      (* ~W CR *)
      RES_TAC >>
      IMP_RES_TAC MD__lem >>
      IMP_RES_TAC Mon__lem >>
      FULL_SIMP_TAC std_ss []
      ,
      (* CR coreg *)
      `(!r. reg_res r /\ r IN MD_ (c,mv,UNIV:vadr set) ==> 
            ?r'. r = COREG r')` by (
          METIS_TAC [coreIfTheory.Mmu_MD_spec]
      ) >>
      RES_TAC >>
      HINT_EXISTS_TAC >>
      ASM_REWRITE_TAC []
     ]
);  

val Ifun_CR_spec = new_specification ("Ifun_CR_spec",
  ["CR_", "Ifun_"], Ifun_CR_exists);

val CR__lem = store_thm("CR__lem", ``
!c c' mv mv'. 
    Ifun_(c,mv)
 /\ (!r. r IN CR_(c,mv) ==> (CV c mv r = CV c' mv' r))
        ==>
    (CR_(c,mv) = CR_(c',mv'))
``,
  ASSUME_TAC Ifun_CR_spec >>
  FULL_SIMP_TAC std_ss [Ifun_CR_po]
);  

val CR__lem2 = store_thm("CR__lem2", ``
!c c' mv mv'. 
    Ifun_(c',mv')
 /\ (!r. r IN CR_(c,mv) ==> (CV c mv r = CV c' mv' r))
        ==>
    (CR_(c,mv) = CR_(c',mv'))
``,
  ASSUME_TAC Ifun_CR_spec >>
  FULL_SIMP_TAC std_ss [Ifun_CR_po2]
);  

val Ifun__lem = store_thm("Ifun__lem", ``
!c c' mv mv'. (!r. r IN CR_(c,mv) ==> (CV c mv r = CV c' mv' r))
        ==>
    (Ifun_(c,mv) <=> Ifun_(c',mv'))
``,
  ASSUME_TAC Ifun_CR_spec >>
  REPEAT STRIP_TAC >>
  EQ_TAC 
  >| [(* ==> *)
      FULL_SIMP_TAC std_ss [Ifun_CR_po] >>
      STRIP_TAC >>
      RES_TAC 
      ,
      (* <== *)
      FULL_SIMP_TAC std_ss [Ifun_CR_po2] >>
      STRIP_TAC >>
      RES_TAC 
     ]
);  

val CR_def = Define `CR s = CR_(s.cs, dmvca s.ms)`;

val CRex_def = Define `CRex s = 
{r | (?pa. r = MEM pa) /\ r IN CR s /\ ?m. Mon s r m EX}`;

val iCoh_CRex_lem = store_thm("iCoh_CRex_lem", ``
!sc. iCoh sc.ms {pa | MEM pa IN CRex sc} <=>
     !pa. MEM pa IN CRex sc ==> icoh sc.ms pa
``,
  RW_TAC std_ss [iCoh_lem2, pred_setTheory.IN_GSPEC_IFF]
);

val isafe_CRex_lem = store_thm("isafe_CRex_lem", ``
!s pa. pa IN {pa | MEM pa IN CRex s} /\ isafe s {pa | MEM pa IN CRex s} ==>
    ~dirty s.ms pa
``,
  RW_TAC std_ss [CRex_def, isafe_def] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
  RES_TAC
);

val isafe_CRex_lem2 = store_thm("isafe_CRex_lem2", ``
!sc. isafe sc {pa | MEM pa IN CRex sc} <=>
     !pa. MEM pa IN CRex sc ==> ~dirty sc.ms pa
``,
  GEN_TAC >>
  EQ_TAC 
  >| [(* ==> *)
      NTAC 3 STRIP_TAC >> 
      MATCH_MP_TAC isafe_CRex_lem >>
      RW_TAC std_ss [pred_setTheory.IN_GSPEC_IFF]
      ,
      (* <== *)
      RW_TAC std_ss [isafe_def] >>
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF]
     ]
);

val Ifun_def = Define `Ifun s = Ifun_(s.cs, dmvca s.ms)`;

(* exported theorems *)

val CR_oblg = store_thm("CR_oblg", ``
!s s'. Ifun s /\ (!r. r IN CR s ==> (Cv s r = Cv s' r)) ==> (CR s = CR s')
``,
  RW_TAC std_ss [Cv_def, CR_def, Ifun_def] >>
  IMP_RES_TAC CR__lem
);

val CR_coreg_oblg = store_thm("CR_coreg_oblg", ``
!s s' r. Ifun s /\ reg_res r /\ r IN CR s /\ (s'.cs.coreg = s.cs.coreg) ==> 
    (Cv s r = Cv s' r) 
``,
  ASSUME_TAC Ifun_CR_spec >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [CR_def, Ifun_def, Ifun_CR_po, Cv_def] >>
  RES_TAC >>
  RW_TAC std_ss [coreIfTheory.CV_def]
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

val Icoh_CR_po = Define `Icoh_CR_po I = 
!s s'. Ifun s 
    /\ dCoh s.ms {pa | MEM pa IN CR s} 
    /\ dCoh s'.ms {pa | MEM pa IN CR s'}
    /\ (!r. r IN CR s ==> (Cv s r = Cv s' r))
        ==>
    (I s <=> I s')
`;

val Icoh_dCoh_po = Define `Icoh_dCoh_po I = 
!s. Ifun s /\ I s ==> dCoh s.ms {pa | MEM pa IN CR s}
`;

val Icode_CR_po = Define `Icode_CR_po I = 
!s s'. Ifun s
    /\ iCoh s.ms {pa | MEM pa IN CRex s}
    /\ iCoh s'.ms {pa | MEM pa IN CRex s'}
    /\ isafe s {pa | MEM pa IN CRex s}
    /\ isafe s' {pa | MEM pa IN CRex s'}
    /\ (!r. r IN CR s ==> (Cv s r = Cv s' r))
        ==>
    (I s <=> I s')
`;

val Icode_iCoh_po = Define `Icode_iCoh_po I = 
!s. Ifun s /\ I s ==> iCoh s.ms {pa | MEM pa IN CRex s}
`;

val Icode_isafe_po = Define `Icode_isafe_po I = 
!s. Ifun s /\ I s ==> isafe s {pa | MEM pa IN CRex s}
`;

val Icm_po = Define `Icm_po I Icm =
!s s'. I s /\ drvbl s s' ==> Icm s'
`;

val Icoh_exists = store_thm("Icoh_exists", ``
?Icoh. Icoh_CR_po Icoh /\ Icoh_dCoh_po Icoh
``,
  EXISTS_TAC ``\s. dCoh s.ms {pa | MEM pa IN CR s}`` >>
  RW_TAC std_ss [Icoh_dCoh_po, Icoh_CR_po]
);

val Icode_exists = store_thm("Icode_exists", ``
?Icode. 
   Icode_CR_po Icode
/\ Icode_iCoh_po Icode
/\ Icode_isafe_po Icode
``,
  EXISTS_TAC ``\s. iCoh s.ms {pa | MEM pa IN CRex s}
                /\ isafe s {pa | MEM pa IN CRex s}`` >>
  RW_TAC std_ss [Icode_CR_po, Icode_iCoh_po, Icode_isafe_po]
);

val Inv_exists = store_thm("Inv_exists", ``
?Inv.
    (!s Icoh Icode Icm. Inv Icoh Icode Icm s <=> 
	Ifun s /\ Icoh s /\ Icode s /\ Icm s)
``,
  EXISTS_TAC ``\Icoh Icode Icm s:hw_state. 
	           Ifun s /\ Icoh s /\ Icode s /\ Icm s`` >>
  RW_TAC std_ss []
);

val Inv_spec = new_specification ("Inv_spec",
  ["Inv"(* , "Icoh", "Icode", "Icm" *)], Inv_exists);

val cm_user_po = Define `cm_user_po Icoh Icode Icm = 
   Icoh_CR_po Icoh
/\ Icoh_dCoh_po Icoh
/\ Icode_CR_po Icode
/\ Icode_iCoh_po Icode 
/\ Icode_isafe_po Icode
/\ Icm_po (Inv Icoh Icode Icm) Icm
`;

(* exported theorems *)

val Ifun_CR_oblg = store_thm("Ifun_CR_oblg", ``
!s s'. (!r. r IN CR s ==> (Cv s r = Cv s' r)) ==> (Ifun s <=> Ifun s')
``,
  RW_TAC std_ss [CR_def, Ifun_def, Cv_def] >>
  IMP_RES_TAC Ifun__lem  
); 

val Ifun_MD_oblg = store_thm("Ifun_MD_oblg", ``
!s r. Ifun s /\ r IN MD s ==> r IN CR s
``,
  RW_TAC std_ss [MD_def, CR_def, Ifun_def] >>
  ASSUME_TAC Ifun_CR_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Ifun_MD_po >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF]
); 

val Ifun_Mon_oblg = store_thm("Ifun_Mon_oblg", ``
!s r. Ifun s /\ r IN CR s ==> ~Mon s r USER W
``,
  RW_TAC std_ss [MD_def, CR_def, Ifun_def, Mon_def] >>
  ASSUME_TAC Ifun_CR_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC Ifun_Mon_po 
); 

val Icoh_CR_oblg = store_thm("Icoh_CR_oblg", ``
!s s' Icoh Icode Icm.
       cm_user_po Icoh Icode Icm  
    /\ Ifun s
    /\ dCoh s.ms {pa | MEM pa IN CR s} 
    /\ dCoh s'.ms {pa | MEM pa IN CR s'}
    /\ (!r. r IN CR s ==> (Cv s r = Cv s' r))
        ==>
    (Icoh s <=> Icoh s')
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [cm_user_po] >>
  IMP_RES_TAC Icoh_CR_po 
); 

val Icoh_dCoh_oblg = store_thm("Icoh_dCoh_oblg", ``
!s Icoh Icode Icm. cm_user_po Icoh Icode Icm /\ Ifun s /\ Icoh s ==> 
    dCoh s.ms {pa | MEM pa IN CR s}
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [cm_user_po] >>
  IMP_RES_TAC Icoh_dCoh_po 
); 

val Icode_CR_oblg = store_thm("Icode_CR_oblg", ``
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
  FULL_SIMP_TAC std_ss [cm_user_po] >>
  IMP_RES_TAC Icode_CR_po 
);

val Icode_iCoh_oblg = store_thm("Icode_iCoh_oblg", ``
!s Icoh Icode Icm. cm_user_po Icoh Icode Icm /\ Ifun s /\ Icode s ==> 
    iCoh s.ms {pa | MEM pa IN CRex s}
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [cm_user_po] >>
  IMP_RES_TAC Icode_iCoh_po 
);

val Icode_isafe_oblg = store_thm("Icode_isafe_oblg", ``
!s Icoh Icode Icm. cm_user_po Icoh Icode Icm /\ Ifun s /\ Icode s ==> 
    isafe s {pa | MEM pa IN CRex s}
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [cm_user_po] >>
  IMP_RES_TAC Icode_isafe_po 
);

val Icm_oblg = store_thm("Icm_oblg", ``
!s s' Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm 
 /\ Inv Icoh Icode Icm s
 /\ drvbl s s' 
        ==> 
    Icm s'
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [cm_user_po] >>
  REV_FULL_SIMP_TAC std_ss [Icm_po] >>
  RES_TAC
); 

val Inv_oblg = store_thm("Inv_oblg", ``
!s Icoh Icode Icm. Inv Icoh Icode Icm s <=> Ifun s /\ Icoh s /\ Icode s /\ Icm s
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

val Rsim_cs_lem = store_thm("Rsim_cs_lem", ``
!sc s. Rsim sc s <=> (s.cs = sc.cs) /\ (!pa. MVcl s.M T pa = dmvalt sc.ms T pa)
``,
  RW_TAC std_ss [Rsim_lem] >>
  EQ_TAC 
  >| [(* ==> *) 
      RW_TAC std_ss [coreIfTheory.core_state_component_equality, 
		     FUN_EQ_THM]
      >| [(* GPR *)
	  `reg_res (REG x)` by ( REWRITE_TAC [coreIfTheory.reg_res_def] ) >>
	  RES_TAC >>
	  FULL_SIMP_TAC std_ss [cl_Cv_def, Cv_def, coreIfTheory.CV_def]
	  ,
	  (* COREG *)
	  `reg_res (COREG x)` by ( REWRITE_TAC [coreIfTheory.reg_res_def] ) >>
	  RES_TAC >>
	  FULL_SIMP_TAC std_ss [cl_Cv_def, Cv_def, coreIfTheory.CV_def]
	  ,
	  (* PSRS *)
	  `reg_res (PSRS x)` by ( REWRITE_TAC [coreIfTheory.reg_res_def] ) >>
	  RES_TAC >>
	  FULL_SIMP_TAC std_ss [cl_Cv_def, Cv_def, coreIfTheory.CV_def]
	 ]
      ,
      (* <== *)
      RW_TAC std_ss [cl_Cv_def, Cv_def] >>
      Cases_on `r` >> ( 
          FULL_SIMP_TAC std_ss [coreIfTheory.CV_def, 
				coreIfTheory.reg_res_def]
      )
     ]
);

val Rsim_exentry_lem = store_thm("Rsim_exentry_lem", ``
!sc s. Rsim sc s ==> (cl_exentry s <=> exentry sc)
``,
  RW_TAC std_ss [Rsim_cs_lem, cl_exentry_def, exentry_def]
);

val Rsim_mode_lem = store_thm("Rsim_mode_lem", ``
!sc s. Rsim sc s ==> (cl_mode s = mode sc)
``,
  RW_TAC std_ss [Rsim_cs_lem, cl_mode_def, mode_def]
);

val Rsim_exists_lem = store_thm("Rsim_exists_lem", ``
!sc. ?s. Rsim sc s
``,
  RW_TAC std_ss [Rsim_cs_lem] >>
  EXISTS_TAC ``<| cs := sc.cs; M := dmvalt sc.ms T |>`` >>
  RW_TAC std_ss [cachememTheory.MVcl_def]
);

val Rsim_unique_lem = store_thm("Rsim_unique_lem", ``
!sc s s'. Rsim sc s /\ Rsim sc s' ==> (s = s')
``,
  RW_TAC std_ss [Rsim_cs_lem, cl_state_component_equality] >>
  FULL_SIMP_TAC std_ss [cachememTheory.MVcl_def] >>
  RW_TAC std_ss [FUN_EQ_THM]
);

val Rsim_dCoh_lem = store_thm("Rsim_dCoh_lem", ``
!sc s As. Rsim sc s /\ dCoh sc.ms As ==>
    !pa. pa IN As ==> (MVcl s.M T pa = dmvca sc.ms T pa)
``,
  RW_TAC std_ss [Rsim_lem, dCoh_alt_lem]
);

val Rsim_dCoh_Cv_lem = store_thm("Rsim_dCoh_Cv_lem", ``
!sc s As. Rsim sc s /\ dCoh sc.ms As ==>
    !pa. pa IN As ==> (cl_Cv s (MEM pa) = Cv sc (MEM pa))
``,
  RW_TAC std_ss [cl_Cv_mem_lem, Cv_mem_lem] >>
  IMP_RES_TAC Rsim_dCoh_lem
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

val Rsim_iCoh_Cv_lem = store_thm("Rsim_iCoh_lem", ``
!sc s As. Rsim sc s /\ dCoh sc.ms As /\ iCoh sc.ms As ==>
    !pa. pa IN As /\ ~dirty sc.ms pa ==> (cl_Cv s (MEM pa) = imv sc.ms T pa)
``,
  RW_TAC std_ss [cl_Cv_mem_lem] >>
  IMP_RES_TAC Rsim_iCoh_lem
);

val Rsim_icoh_Cv_lem = store_thm("Rsim_icoh_lem", ``
!sc s pa. Rsim sc s /\ dcoh sc.ms pa /\ icoh sc.ms pa /\ ~dirty sc.ms pa ==> 
    (cl_Cv s (MEM pa) = imv sc.ms T pa)
``,
  REPEAT STRIP_TAC >>
  `dCoh sc.ms {pa}` by ( RW_TAC std_ss [dCoh_lem2, pred_setTheory.IN_SING] ) >>
  `iCoh sc.ms {pa}` by ( RW_TAC std_ss [iCoh_lem2, pred_setTheory.IN_SING] ) >>
  IMP_RES_TAC Rsim_iCoh_Cv_lem >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_SING]
);


(******** Cache-less Invariants and proof obligations **********)

(* critical resources *)

val cl_CR_def = Define `cl_CR s = CR_(s.cs, MVcl s.M)`;

val cl_Inv_def = Define `cl_Inv s = Ifun_(s.cs, MVcl s.M)`;

val cl_CR_lem = store_thm("cl_CR_lem", ``
!s sca. cl_Inv s /\ (!r. r IN cl_CR s ==> (cl_Cv s r = Cv sca r)) ==>
    (cl_CR s = CR sca)
``,
  RW_TAC std_ss [cl_CR_def, CR_def, cl_Cv_def, Cv_def, cl_Inv_def] >>
  IMP_RES_TAC CR__lem
);

val CR_cl_lem = store_thm("CR_cl_lem", ``
!s sca. Ifun sca /\ (!r. r IN CR sca ==> (cl_Cv s r = Cv sca r)) ==>
    (cl_CR s = CR sca)
``,
  RW_TAC std_ss [cl_CR_def, CR_def, cl_Cv_def, Cv_def, Ifun_def] >>
  METIS_TAC [CR__lem]
);

val cl_CRex_def = Define `cl_CRex s = 
{r | (?pa. r = MEM pa) /\ r IN cl_CR s /\ ?m. cl_Mon s r m EX}`;

val cl_CRex_oblg = store_thm("cl_CRex_oblg", ``
!s r. r IN cl_CRex s ==> 
(?pa. (r = MEM pa)) /\ r IN cl_CR s /\ ?m. cl_Mon s r m EX
``,
  RW_TAC std_ss [cl_CRex_def] >> (
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
      RW_TAC std_ss []
  ) >>
  HINT_EXISTS_TAC >>
  ASM_REWRITE_TAC []
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

val cl_Inv_spec = store_thm("cl_Inv_spec", ``
!s sca. (!r. r IN cl_CR s ==> (cl_Cv s r = Cv sca r)) ==>
    (cl_Inv s <=> Ifun sca)
``,
  RW_TAC std_ss [cl_CR_def, cl_Inv_def, Ifun_def, cl_Cv_def, Cv_def] >>
  IMP_RES_TAC Ifun__lem
);

val Ifun_xfer_lem = store_thm("Ifun_xfer_lem", ``
!sc s. cl_Inv s /\ (!r. r IN cl_CR s ==> (cl_Cv s r = Cv sc r)) ==> Ifun sc
``,
  RW_TAC std_ss [cl_Inv_def, Ifun_def, cl_CR_def, cl_Cv_def, Cv_def] >>
  IMP_RES_TAC Ifun__lem
);

val cl_Inv_preserve_po = Define `cl_Inv_preserve_po =
!s s' n. cl_Inv s /\ cl_wrel s s' n ==> cl_Inv s'
`;

(* NOTE: Kvm and PC condition moved to countermeasure
 * need:
 ** Kvm always cacheable
 ** only accesses to Kvm
 ** PRIV configuration (MD Kvm) not changed by kernel 
    (needed to show Coh of CR and bisim through Icm)
 ** Kcode subset of Kvm, always in CRex
 ** PC always in Kcode
 ** PC not dirty
*)

(* some lemmas *)

val Rsim_CR_dCoh_ca_lem = store_thm("Rsim_CR_dCoh_ca_lem", ``
!sc s. Rsim sc s /\ dCoh sc.ms {pa | MEM pa IN CR sc}
         ==>
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
      `pa IN {pa | MEM pa IN CR sc}` by (
          FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF]
      ) >>
      IMP_RES_TAC Rsim_dCoh_lem >>
      RW_TAC std_ss [cl_Cv_def, Cv_def, coreIfTheory.CV_def]
     ]
);


val Rsim_CR_dCoh_cl_lem = store_thm("Rsim_CR_dCoh_cl_lem", ``
!sc s. Rsim sc s /\ dCoh sc.ms {pa | MEM pa IN cl_CR s}
         ==>
    (!r. r IN cl_CR s ==> (cl_Cv s r = Cv sc r))
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
      `pa IN {pa | MEM pa IN cl_CR s}` by (
          FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF]
      ) >>
      IMP_RES_TAC Rsim_dCoh_lem >>
      RW_TAC std_ss [cl_Cv_def, Cv_def, coreIfTheory.CV_def]
     ]
);

val Rsim_CR_lem = store_thm("Rsim_CR_lem", ``
!sc s Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Rsim sc s
 /\ Ifun sc
 /\ Icoh sc 
        ==>
    (!r. r IN CR sc ==> (cl_Cv s r = Cv sc r))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Icoh_dCoh_oblg >>
  IMP_RES_TAC Rsim_CR_dCoh_ca_lem
);

(* NOTE: cannot transfer Icoh and Ifun separately in new version *)
(* val Rsim_cl_CR_lem = store_thm("Rsim_cl_CR_lem", `` *)
(* !sc s Icoh Icode Icm.  *)
(*     cm_user_po Icoh Icode Icm *)
(*  /\ Rsim sc s *)
(*  /\ cl_Inv s *)
(*  /\ Icoh sc *)
(*         ==> *)
(*     (!r. r IN cl_CR s ==> (cl_Cv s r = Cv sc r)) *)
(* ``, *)
(*   REPEAT STRIP_TAC >> *)
(*   IMP_RES_TAC Rsim_CR_lem >> *)
(*   IMP_RES_TAC CR_cl_lem >> *)
(*   FULL_SIMP_TAC std_ss [] *)
(* ); *)

val Rsim_CR_eq_dCoh_ca_lem = store_thm("Rsim_CR_eq_dCoh_ca_lem", ``
!sc s. Rsim sc s /\ Ifun sc /\ dCoh sc.ms {pa | MEM pa IN CR sc} 
        ==>
    (cl_CR s = CR sc)
``,
  REPEAT STRIP_TAC >>
  MATCH_MP_TAC EQ_SYM >>
  FULL_SIMP_TAC std_ss [cl_CR_def, CR_def, Ifun_def] >>
  MATCH_MP_TAC CR__lem >>
  ASM_REWRITE_TAC [] >>
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_CR_dCoh_ca_lem >> 
  FULL_SIMP_TAC std_ss [CR_def, cl_Cv_def, Cv_def]
);

val Rsim_CR_eq_dCoh_cl_lem = store_thm("Rsim_CR_eq_dCoh_cl_lem", ``
!sc s. Rsim sc s /\ cl_Inv s /\ dCoh sc.ms {pa | MEM pa IN cl_CR s} 
        ==>
    (cl_CR s = CR sc)
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [cl_CR_def, CR_def, cl_Inv_def] >>
  MATCH_MP_TAC CR__lem >>
  ASM_REWRITE_TAC [] >>
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_CR_dCoh_cl_lem >> 
  FULL_SIMP_TAC std_ss [cl_CR_def, cl_Cv_def, Cv_def]
);

val Rsim_CR_eq_lem = store_thm("Rsim_CR_eq_lem", ``
!sc s Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Rsim sc s
 /\ Ifun sc
 /\ Icoh sc
        ==>
    (cl_CR s = CR sc)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Icoh_dCoh_oblg >>
  IMP_RES_TAC Rsim_CR_eq_dCoh_ca_lem
);

val Rsim_MD_dCoh_ca_lem = store_thm("Rsim_MD_dCoh_ca_lem", ``
!sc s. Rsim sc s /\ dCoh sc.ms {pa | MEM pa IN MD sc}
        ==>
    (cl_MD s = MD sc)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_dCoh_Cv_lem >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
  MATCH_MP_TAC MD_cl_lem >>
  REPEAT STRIP_TAC >>
  Cases_on `reg_res r`
  >| [(* register *)
      FULL_SIMP_TAC std_ss [Rsim_lem]
      ,
      (* MEM *)
      ASSUME_TAC ( SPEC ``r:resource`` coreIfTheory.res_cases ) >>
      FULL_SIMP_TAC std_ss [] >> (
          FULL_SIMP_TAC std_ss [] 
      )
     ]
);

val Rsim_MD_dCoh_cl_lem = store_thm("Rsim_MD_dCoh_cl_lem", ``
!sc s. Rsim sc s /\ dCoh sc.ms {pa | MEM pa IN cl_MD s}
        ==>
    (cl_MD s = MD sc)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_dCoh_Cv_lem >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
  MATCH_MP_TAC cl_MD_lem >>
  REPEAT STRIP_TAC >>
  Cases_on `reg_res r`
  >| [(* register *)
      FULL_SIMP_TAC std_ss [Rsim_lem]
      ,
      (* MEM *)
      ASSUME_TAC ( SPEC ``r:resource`` coreIfTheory.res_cases ) >>
      FULL_SIMP_TAC std_ss [] >> (
          FULL_SIMP_TAC std_ss [] 
      )
     ]
);

val Rsim_MD_lem = store_thm("Rsim_MD_lem", ``
!sc s Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm 
 /\ Rsim sc s /\ Icoh sc /\ Ifun sc 
        ==>
    (cl_MD s = MD sc)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_CR_lem >>
  MATCH_MP_TAC MD_cl_lem >>
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Ifun_MD_oblg >>
  RES_TAC 
);

val Rsim_MDVA_eq_dCoh_cl_lem = store_thm("Rsim_MDVA_eq_dCoh_cl_lem", ``
!sc s VAs. Rsim sc s /\ dCoh sc.ms {pa | MEM pa IN cl_MDVA s VAs}
        ==>
    (!r. r IN cl_MDVA s VAs ==> (cl_Cv s r = Cv sc r))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_dCoh_Cv_lem >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
  Cases_on `reg_res r`
  >| [(* register *)
      FULL_SIMP_TAC std_ss [Rsim_lem]
      ,
      (* MEM *)
      ASSUME_TAC ( SPEC ``r:resource`` coreIfTheory.res_cases ) >>
      FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF] >> (
          FULL_SIMP_TAC std_ss [] 
      )
     ]
);

val Rsim_MDVA_eq_dCoh_ca_lem = store_thm("Rsim_MDVA_eq_dCoh_ca_lem", ``
!sc s VAs. Rsim sc s /\ dCoh sc.ms {pa | MEM pa IN MDVA sc VAs}
        ==>
    (!r. r IN MDVA sc VAs ==> (cl_Cv s r = Cv sc r))
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_dCoh_Cv_lem >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_GSPEC_IFF] >>
  Cases_on `reg_res r`
  >| [(* register *)
      FULL_SIMP_TAC std_ss [Rsim_lem]
      ,
      (* MEM *)
      ASSUME_TAC ( SPEC ``r:resource`` coreIfTheory.res_cases ) >>
      FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF] >> (
          FULL_SIMP_TAC std_ss [] 
      )
     ]
);

val Rsim_MDVA_eq_lem = store_thm("Rsim_MDVA_eq_lem", ``
!sc s VAs Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm 
 /\ Rsim sc s /\ Icoh sc /\ Ifun sc 
        ==>
    (!r. r IN cl_MDVA s VAs ==> (cl_Cv s r = Cv sc r))
``,
  REPEAT STRIP_TAC >>
  `cl_MDVA s VAs SUBSET cl_MD s` by ( 
      FULL_SIMP_TAC std_ss [cl_MDVA_def, cl_MD_def] >>
      `VAs SUBSET UNIV:vadr set` by (
          FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_UNIV]
      ) >>
      RW_TAC std_ss [MD__monotonic_lem]
  ) >>
  `cl_MD s = MD sc` by ( IMP_RES_TAC Rsim_MD_lem ) >>
  IMP_RES_TAC Rsim_CR_lem >>
  IMP_RES_TAC Ifun_MD_oblg >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF]
);

val Rsim_MDVA_eq_cl_lem = store_thm("Rsim_MDVA_eq_cl_lem", ``
!sc s VAs Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm 
 /\ Rsim sc s /\ Icoh sc /\ Ifun sc 
        ==>
    (!r. r IN MDVA sc VAs ==> (cl_Cv s r = Cv sc r))
``,
  REPEAT STRIP_TAC >>
  `MDVA sc VAs SUBSET MD sc` by ( 
      FULL_SIMP_TAC std_ss [MDVA_def, MD_def] >>
      `VAs SUBSET UNIV:vadr set` by (
          FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_UNIV]
      ) >>
      RW_TAC std_ss [MD__monotonic_lem]
  ) >>
  `cl_MD s = MD sc` by ( IMP_RES_TAC Rsim_MD_lem ) >>
  IMP_RES_TAC Rsim_CR_lem >>
  IMP_RES_TAC Ifun_MD_oblg >>
  FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF]
);

val Rsim_MDVA_dCoh_cl_lem = store_thm("Rsim_MDVA_dCoh_cl_lem", ``
!sc s VAs Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm 
 /\ Rsim sc s /\ Icoh sc /\ Ifun sc 
        ==>
    (cl_MDVA s VAs = MDVA sc VAs)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_MDVA_eq_lem >>
  FULL_SIMP_TAC std_ss [cl_MDVA_def, MDVA_def] >>
  MATCH_MP_TAC MD__lem >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [cl_Cv_def, Cv_def] >>
  RES_TAC 
);

val Rsim_MDVA_lem = store_thm("Rsim_MDVA_lem", ``
!sc s VAs Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm 
 /\ Rsim sc s /\ Icoh sc /\ Ifun sc 
        ==>
    (cl_MDVA s VAs = MDVA sc VAs)
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_MDVA_eq_lem >>
  FULL_SIMP_TAC std_ss [cl_MDVA_def, MDVA_def] >>
  MATCH_MP_TAC MD__lem >>
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [cl_Cv_def, Cv_def] >>
  RES_TAC 
);

val Rsim_Mmu_lem = store_thm("Rsim_Mon_lem", ``
!sc s Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Rsim sc s
 /\ Icoh sc
 /\ Ifun sc
        ==>
    (!va m ac. cl_Mmu s va m ac = Mmu sc va m ac)
``,
  RW_TAC std_ss [cl_Mmu_def, Mmu_def] >>
  MATCH_MP_TAC (
      prove(``(x IN UNIV:vadr set ==> (P (a,b,x,c,d) = P (e,f,x,g,h)))
			          ==> (P (a,b,x,c,d) = P (e,f,x,g,h))``, 
	      METIS_TAC [pred_setTheory.IN_UNIV])
  ) >>
  MATCH_MP_TAC Mmu_lem >>
  IMP_RES_TAC Rsim_MD_lem >>
  IMP_RES_TAC Ifun_MD_oblg >>
  FULL_SIMP_TAC std_ss [cl_MD_def, MD_def] >>
  REPEAT STRIP_TAC >>
  RES_TAC >>
  IMP_RES_TAC Rsim_CR_lem >>
  FULL_SIMP_TAC std_ss [cl_Cv_def, Cv_def]
);

val Rsim_Mon_dCoh_ca_lem = store_thm("Rsim_Mon_dCoh_ca_lem", ``
!sc s. Rsim sc s /\ dCoh sc.ms {pa | MEM pa IN MD sc}
        ==>
    (!r m ac. cl_Mon s r m ac = Mon sc r m ac)
``,
  RW_TAC std_ss [cl_Mon_def, Mon_def] >>
  IMP_RES_TAC Rsim_MD_dCoh_ca_lem >>
  MATCH_MP_TAC Mon__lem >>
  REPEAT STRIP_TAC >>
  Cases_on `reg_res r`
  >| [(* register *)
      FULL_SIMP_TAC std_ss [Rsim_lem, cl_Cv_def, Cv_def]
      ,
      (* MEM *)
      ASSUME_TAC ( SPEC ``r:resource`` coreIfTheory.res_cases ) >>
      FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF] >> (
          FULL_SIMP_TAC std_ss [] 
      ) >>  
      `pa IN {pa | MEM pa IN MD sc}` by (
          FULL_SIMP_TAC std_ss [cl_MD_def, MD_def, pred_setTheory.IN_GSPEC_IFF] >>
          REV_FULL_SIMP_TAC std_ss []
      ) >>
      IMP_RES_TAC Rsim_dCoh_Cv_lem >>
      FULL_SIMP_TAC std_ss [cl_Cv_def, Cv_def]
     ]
);

val Rsim_Mon_dCoh_cl_lem = store_thm("Rsim_Mon_dCoh_cl_lem", ``
!sc s. Rsim sc s /\ dCoh sc.ms {pa | MEM pa IN cl_MD s}
        ==>
    (!r m ac. cl_Mon s r m ac = Mon sc r m ac)
``,
  RW_TAC std_ss [cl_Mon_def, Mon_def] >>
  IMP_RES_TAC Rsim_MD_dCoh_cl_lem >>
  MATCH_MP_TAC Mon__lem >>
  REPEAT STRIP_TAC >>
  Cases_on `reg_res r`
  >| [(* register *)
      FULL_SIMP_TAC std_ss [Rsim_lem, cl_Cv_def, Cv_def]
      ,
      (* MEM *)
      ASSUME_TAC ( SPEC ``r:resource`` coreIfTheory.res_cases ) >>
      FULL_SIMP_TAC std_ss [pred_setTheory.SUBSET_DEF] >> (
          FULL_SIMP_TAC std_ss [] 
      ) >>  
      `pa IN {pa | MEM pa IN cl_MD s}` by (
          FULL_SIMP_TAC std_ss [cl_MD_def, MD_def, pred_setTheory.IN_GSPEC_IFF] >>
          REV_FULL_SIMP_TAC std_ss []
      ) >>
      REV_FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC Rsim_dCoh_Cv_lem >>
      FULL_SIMP_TAC std_ss [cl_Cv_def, Cv_def]
     ]
);

val Rsim_Mon_lem = store_thm("Rsim_Mon_lem", ``
!sc s Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Rsim sc s
 /\ Icoh sc
 /\ Ifun sc
        ==>
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

val Rsim_CRex_dCoh_ca_lem = store_thm("Rsim_CRex_dCoh_ca_lem", ``
!sc s. Rsim sc s /\ Ifun sc
    /\ dCoh sc.ms {pa | MEM pa IN CR sc} 
    /\ dCoh sc.ms {pa | MEM pa IN MD sc}
        ==>
    (cl_CRex s = CRex sc)
``,
  RW_TAC std_ss [cl_CRex_def, CRex_def, pred_setTheory.EXTENSION,
		 pred_setTheory.IN_GSPEC_IFF] >>
  `(cl_CR s = CR sc) /\ (!m. cl_Mon s x m EX <=> Mon sc x m EX)` suffices_by (
      RW_TAC std_ss []
  ) >>
  REPEAT STRIP_TAC
  >| [(* CR *)
      IMP_RES_TAC Rsim_CR_eq_dCoh_ca_lem
      ,
      (* Mon *)
      IMP_RES_TAC Rsim_Mon_dCoh_ca_lem >>
      ASM_REWRITE_TAC []
     ]
);

val Rsim_CRex_dCoh_cl_lem = store_thm("Rsim_CRex_dCoh_cl_lem", ``
!sc s. Rsim sc s /\ cl_Inv s
    /\ dCoh sc.ms {pa | MEM pa IN cl_CR s} 
    /\ dCoh sc.ms {pa | MEM pa IN cl_MD s}
        ==>
    (cl_CRex s = CRex sc)
``,
  RW_TAC std_ss [cl_CRex_def, CRex_def, pred_setTheory.EXTENSION,
		 pred_setTheory.IN_GSPEC_IFF] >>
  `(cl_CR s = CR sc) /\ (!m. cl_Mon s x m EX <=> Mon sc x m EX)` suffices_by (
      RW_TAC std_ss []
  ) >>
  REPEAT STRIP_TAC
  >| [(* CR *)
      IMP_RES_TAC Rsim_CR_eq_dCoh_cl_lem
      ,
      (* Mon *)
      IMP_RES_TAC Rsim_Mon_dCoh_cl_lem >>
      ASM_REWRITE_TAC []
     ]
);

val Rsim_CRex_lem = store_thm("Rsim_CRex_lem", ``
!sc s Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Rsim sc s
 /\ Icoh sc
 /\ Ifun sc
        ==>
    (cl_CRex s = CRex sc)
``,
  RW_TAC std_ss [cl_CRex_def, CRex_def, pred_setTheory.EXTENSION,
		 pred_setTheory.IN_GSPEC_IFF] >>
  `(cl_CR s = CR sc) /\ (!m. cl_Mon s x m EX <=> Mon sc x m EX)` suffices_by (
      RW_TAC std_ss []
  ) >>
  REPEAT STRIP_TAC
  >| [(* CR *)
      IMP_RES_TAC Rsim_CR_eq_lem
      ,
      (* Mon *)
      IMP_RES_TAC Rsim_Mon_lem >>
      ASM_REWRITE_TAC []
     ]
);

val Rsim_fixmmu_lem = store_thm("Rsim_fixmmu_lem", ``
!sc s VAs f Icoh Icode Icm. 
    cm_user_po Icoh Icode Icm
 /\ Rsim sc s
 /\ Icoh sc
 /\ Ifun sc
        ==>
    (cl_fixmmu s VAs f <=> ca_fixmmu sc VAs f)
``,
  REWRITE_TAC [cl_fixmmu_def, ca_fixmmu_def] >>
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Rsim_Mmu_lem >>
  METIS_TAC []
);

(* NOTE: cannot transfer Ifun and Icoh separately in new version *)
(* val Ifun_Icoh_lem = store_thm("Ifun_Icoh_lem", `` *)
(* !s sc Icoh Icode Icm. Rsim sc s /\ cm_user_po Icoh Icode Icm /\ Icoh sc *)
(*         ==>  *)
(*     (Ifun sc <=> cl_Inv s) *)
(* ``, *)
(*   REPEAT STRIP_TAC >> *)
(*   MATCH_MP_TAC EQ_SYM >> *)
(*   MATCH_MP_TAC cl_Inv_spec >> *)
(*   IMP_RES_TAC Rsim_cl_CR_lem *)
(* ); *)

val Rsim_cl_Inv_lem = store_thm("Rsim_cl_Inv_lem", ``
!s sc Icoh Icode Icm. 
    Rsim sc s 
 /\ cm_user_po Icoh Icode Icm 
 /\ Inv Icoh Icode Icm sc 
        ==> 
    cl_Inv s 
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [Inv_oblg] >>
  IMP_RES_TAC Rsim_CR_lem >>
  FULL_SIMP_TAC std_ss [Ifun_def, cl_Inv_def, cl_Cv_def, Cv_def, CR_def] >>
  METIS_TAC [Ifun__lem]
);

(* internal invariants *)

val cl_II_def = Define `cl_II Icmf Icodef s (s': cl_state) (n:num) = 
cl_Inv s /\ Icmf s s' n /\ Icodef s s' n
`;

val ca_II_def = Define `
ca_II Icoh Icode Icm Icmf Icodef s (s': hw_state) (n:num) = 
   Inv Icoh Icode Icm s /\ Icmf s s' n /\ Icodef s s' n
`;

val cl_Inv_po = Define `cl_Inv_po =
!s s' n. cl_Inv s /\ cl_wrel s s' n ==> cl_Inv s'
`; 

val cl_II_po = Define `cl_II_po Icmf Icodef =
!s s' n. cl_Inv s /\ cl_kcomp s s' n ==> cl_II Icmf Icodef s s' n
`; 

val Icmf_init_xfer_po = Define `Icmf_init_xfer_po caI clI Icoh Icode Icm =
!sc s. 
    cm_user_po Icoh Icode Icm 
 /\ Rsim sc s
 /\ Inv Icoh Icode Icm sc
 /\ cl_Inv s
 /\ clI s s 0
        ==>
    caI sc sc 0
`;

val Icodef_init_xfer_po = 
Define `Icodef_init_xfer_po caI clI Icoh Icode Icm ca_Icmf cl_Icmf =
!sc s. 
    cm_user_po Icoh Icode Icm 
 /\ Rsim sc s
 /\ Inv Icoh Icode Icm sc
 /\ ca_Icmf sc sc 0
 /\ cl_Icmf s s 0
 /\ cl_Inv s
 /\ clI s s 0
        ==>
    caI sc sc 0
`;

val Icmf_xfer_po = Define `Icmf_xfer_po caI clI Icoh Icode Icm =
!sc sc' sc'' s s' s'' n dl ca_Icodef cl_Icodef. 
    cm_user_po Icoh Icode Icm 
 /\ Rsim sc s
 /\ (!m sm scm. 
        m <= n
     /\ cl_kcomp s sm m
     /\ ca_kcomp sc scm m
            ==>
        Rsim scm sm
     /\ ca_II Icoh Icode Icm caI ca_Icodef sc scm m
     /\ cl_II clI cl_Icodef s sm m)
 /\ cl_kcomp s s' n 
 /\ ca_kcomp sc sc' n
 /\ abs_cl_trans s' PRIV dl s''
 /\ abs_ca_trans sc' PRIV dl sc''
 /\ Rsim sc'' s''
 /\ clI s s'' (SUC n)
        ==>
    caI sc sc'' (SUC n)
`;


val Icodef_xfer_po = 
Define `Icodef_xfer_po caI clI Icoh Icode Icm ca_Icmf cl_Icmf =
!sc sc' sc'' s s' s'' n dl. 
    cm_user_po Icoh Icode Icm 
 /\ Rsim sc s
 /\ (!m sm scm. 
        m <= n
     /\ cl_kcomp s sm m
     /\ ca_kcomp sc scm m
            ==>
        Rsim scm sm
     /\ ca_II Icoh Icode Icm ca_Icmf caI sc scm m
     /\ cl_II cl_Icmf clI s sm m)
 /\ ca_kcomp sc sc' n
 /\ cl_kcomp s s' n 
 /\ ca_Icmf sc sc'' (SUC n)
 /\ cl_Icmf s s'' (SUC n)
 /\ abs_cl_trans s' PRIV dl s''
 /\ abs_ca_trans sc' PRIV dl sc''
 /\ Rsim sc'' s''
 /\ clI s s'' (SUC n)
        ==>
    caI sc sc'' (SUC n)
`;

(* functional cm condition on cacheless model,
   need to ensure that all memory accesses are cacheable *)
val cl_Icmf_po = Define `cl_Icmf_po Icmf = 
!s s' s'' n dl. cl_kcomp s s' n /\ abs_cl_trans s' PRIV dl s'' /\ Icmf s s' n
        ==>
    (!d. MEM d dl ==> CA (opd d))
`;

val ca_Icmf_po = Define `ca_Icmf_po Icmf Icoh Icode Icm = 
!s s' n. 
    cm_user_po Icoh Icode Icm
 /\ ca_kcomp s s' n 
 /\ Icoh s
 /\ Icmf s s' n
        ==>
    dCoh s'.ms (ca_deps s')
`;

val ca_Icodef_po = Define `ca_Icodef_po Icodef Icoh Icode Icm Icmf = 
!s s' n. 
    cm_user_po Icoh Icode Icm
 /\ Inv Icoh Icode Icm s
 /\ ca_kcomp s s' n 
 /\ Icmf s s' n
 /\ Icodef s s' n
 /\ (mode s' = PRIV)
        ==>
    icoh s'.ms (ca_Tr s' (VApc s'.cs))
 /\ ~dirty s'.ms (ca_Tr s' (VApc s'.cs))
`;

val Inv_rebuild_po = Define `
Inv_rebuild_po Icoh Icode Icm ca_Icmf ca_Icodef cl_Icmf cl_Icodef =
!sc sc' s s' n. 
    cm_user_po Icoh Icode Icm 
 /\ Inv Icoh Icode Icm sc
 /\ cl_Inv s
 /\ Rsim sc s
 /\ ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc sc' n
 /\ cl_II cl_Icmf cl_Icodef s s' n
 /\ ca_wrel sc sc' n
 /\ cl_wrel s s' n
 /\ Rsim sc' s'
 /\ cl_Inv s'
        ==> 
    Ifun sc' /\ Icoh sc' /\ Icode sc'
`;

val Icm_f_po = Define `Icm_f_po Icmf Icodef Icoh Icode Icm =
!sc sc' n. 
    cm_user_po Icoh Icode Icm 
 /\ ca_II Icoh Icode Icm Icmf Icodef sc sc' n
 /\ ca_wrel sc sc' n
        ==> 
    Icm sc'
`;

val cm_kernel_po_def = Define `
cm_kernel_po cl_Icmf cl_Icodef ca_Icmf ca_Icodef Icoh Icode Icm =
    Icmf_init_xfer_po ca_Icmf cl_Icmf Icoh Icode Icm
 /\ Icodef_init_xfer_po ca_Icodef cl_Icodef Icoh Icode Icm ca_Icmf cl_Icmf
 /\ Icmf_xfer_po ca_Icmf cl_Icmf Icoh Icode Icm
 /\ Icodef_xfer_po ca_Icodef cl_Icodef Icoh Icode Icm ca_Icmf cl_Icmf
 /\ cl_Icmf_po cl_Icmf
 /\ ca_Icmf_po ca_Icmf Icoh Icode Icm
 /\ ca_Icodef_po ca_Icodef Icoh Icode Icm ca_Icmf
 /\ Inv_rebuild_po Icoh Icode Icm ca_Icmf ca_Icodef cl_Icmf cl_Icodef
 /\ Icm_f_po ca_Icmf ca_Icodef Icoh Icode Icm
`;

val Icmf_init_sim_lem = store_thm("Icmf_init_sim_lem", ``
!s sc ca_Icmf cl_Icmf Icoh Icode Icm n:num. 
    cm_user_po Icoh Icode Icm 
 /\ Rsim sc s
 /\ Inv Icoh Icode Icm sc
 /\ cl_Inv s
 /\ Icmf_init_xfer_po ca_Icmf cl_Icmf Icoh Icode Icm
 /\ cl_Icmf s s 0
        ==>
    ca_Icmf sc sc 0
``,
  RW_TAC std_ss [Icmf_init_xfer_po] >>
  RES_TAC 
);

val Icodef_init_sim_lem = store_thm("Icodef_init_sim_lem", ``
!s sc ca_Icodef cl_Icodef Icoh Icode Icm ca_Icmf cl_Icmf.
    cm_user_po Icoh Icode Icm 
 /\ Rsim sc s
 /\ Inv Icoh Icode Icm sc
 /\ cl_Inv s
 /\ Icodef_init_xfer_po ca_Icodef cl_Icodef Icoh Icode Icm ca_Icmf cl_Icmf
 /\ ca_Icmf sc sc 0
 /\ cl_Icmf s s 0
 /\ cl_Icodef s s 0
        ==>
    ca_Icodef sc sc 0
``,
  RW_TAC std_ss [Icodef_init_xfer_po] >>
  RES_TAC 
);

val Icmf_sim_lem = store_thm("Icmf_sim_lem", ``
!sc sc' sc'' s s' s'' n dl Icoh Icode Icm ca_Icmf cl_Icmf ca_Icodef cl_Icodef.
    cm_user_po Icoh Icode Icm 
 /\ Rsim sc s
 /\ (!m sm scm. 
        m <= n
     /\ cl_kcomp s sm m
     /\ ca_kcomp sc scm m
            ==>
        Rsim scm sm
     /\ ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc scm m
     /\ cl_II cl_Icmf cl_Icodef s sm m)
 /\ cl_kcomp s s' n
 /\ ca_kcomp sc sc' n
 /\ abs_cl_trans s' PRIV dl s''
 /\ abs_ca_trans sc' PRIV dl sc''
 /\ Rsim sc'' s''
 /\ Icmf_xfer_po ca_Icmf cl_Icmf Icoh Icode Icm
 /\ cl_Icmf s s'' (SUC n)
        ==>
    ca_Icmf sc sc'' (SUC n)
``,
  RW_TAC std_ss [Icmf_xfer_po] >> 
  PAT_X_ASSUM ``!a b c d e f g h i j. y`` (
      fn thm => ASSUME_TAC (
		    SPECL [``sc:hw_state``, ``sc':hw_state``,
			   ``sc'':hw_state``, ``s:cl_state``, 
			   ``s':cl_state``, ``s'':cl_state``, 
			   ``n:num``, ``dl:mop list``,
			   ``ca_Icodef:hw_state -> hw_state -> num -> bool``,
			   ``cl_Icodef:cl_state -> cl_state -> num -> bool``] 
			  thm 
		)
  ) >>
  RES_TAC
);

val Icodef_sim_lem = store_thm("Icodef_sim_lem", ``
!sc sc' sc'' s s' s'' n dl Icoh Icode Icm ca_Icmf cl_Icmf ca_Icodef cl_Icodef.
    cm_user_po Icoh Icode Icm 
 /\ Rsim sc s
 /\ (!m sm scm. 
        m <= n
     /\ cl_kcomp s sm m
     /\ ca_kcomp sc scm m
            ==>
        Rsim scm sm
     /\ ca_II Icoh Icode Icm ca_Icmf ca_Icodef sc scm m
     /\ cl_II cl_Icmf cl_Icodef s sm m)
 /\ cl_kcomp s s' n
 /\ ca_kcomp sc sc' n
 /\ ca_Icmf sc sc'' (SUC n) 
 /\ cl_Icmf s s'' (SUC n) 
 /\ abs_cl_trans s' PRIV dl s''
 /\ abs_ca_trans sc' PRIV dl sc''
 /\ Rsim sc'' s''
 /\ Icodef_xfer_po ca_Icodef cl_Icodef Icoh Icode Icm ca_Icmf cl_Icmf
 /\ cl_Icodef s s'' (SUC n)
        ==>
    ca_Icodef sc sc'' (SUC n)
``,
  RW_TAC std_ss [Icodef_xfer_po] >> 
  PAT_X_ASSUM ``!a b c d e f g h. y`` (
      fn thm => ASSUME_TAC (
		    SPECL [``sc:hw_state``, ``sc':hw_state``,
			   ``sc'':hw_state``, ``s:cl_state``, 
			   ``s':cl_state``, ``s'':cl_state``, 
			   ``n:num``, ``dl:mop list``] thm 
		)
  ) >>
  RES_TAC
);

(*********** finish ************)

val _ = export_theory();


