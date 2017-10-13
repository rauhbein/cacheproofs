(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open hwTheory;

val _ = new_theory "InvIf";

(*********** software proof obligations ***********)

(* critical resources *)

val CR_exists = prove (``
?CR:core_state # mem_view -> resource set.
!c c' mv mv'. (!r. r IN CR(c,mv) ==> (CV c mv r = CV c' mv' r)) ==>
	      (CR(c,mv) = CR(c',mv'))
``,
  EXISTS_TAC ``\ (c,mv):core_state # mem_view. EMPTY:resource set`` >>
  RW_TAC std_ss []
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

val CRex_oblg = store_thm("CR_oblg", ``
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

val Inv_exists = store_thm("Inv_exists", ``
?Inv Ifun Icoh Icm.
    (!s. Inv s <=> Ifun s /\ Icoh s /\ Icm s)
 /\ Ifun_CR_po Ifun /\ Ifun_MD_po Ifun /\ Ifun_Mon_po Ifun
 /\ Icoh_CR_po Icoh /\ Icoh_dCoh_po Icoh
 /\ Icm_po Inv Icm
``,
  ASSUME_TAC Ifun_exists >>
  ASSUME_TAC Icoh_exists >>
  FULL_SIMP_TAC std_ss [] >>
  EXISTS_TAC ``\s:hw_state. Ifun s /\ Icoh s`` >>
  EXISTS_TAC ``Ifun:hw_state -> bool`` >>
  EXISTS_TAC ``Icoh:hw_state -> bool`` >>
  EXISTS_TAC ``\s:hw_state. T`` >>
  RW_TAC std_ss [Icm_po]
);

val Inv_spec = new_specification ("Inv_spec",
  ["Inv", "Ifun", "Icoh", "Icm"], Inv_exists);

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

val Icm_oblg = store_thm("Icm_oblg", ``
!s s'. Inv s /\ drvbl s s' ==> Icm s'
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC Inv_spec >>
  REV_FULL_SIMP_TAC std_ss [Icm_po] >>
  RES_TAC
); 

val Inv_oblg = store_thm("Inv_oblg", ``
!s. Inv s ==> Ifun s /\ Icoh s /\ Icm s
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC Inv_spec >>
  FULL_SIMP_TAC std_ss []
); 
