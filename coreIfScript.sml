(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;

val _ = new_theory "coreIf";

(* introduce uninterpreted types *)

val _ = new_type("reg_name", 0);
val _ = new_type("coreg_name", 0);
val _ = new_type("psrs_name", 0);

val _ = new_constant("PC", ``:reg_name``);

val _ = Datatype `core_state =
  <| reg: reg_name -> word;
     coreg: coreg_name -> word;
     psrs: psrs_name -> word     
  |>`;

val _ = Datatype `resource = REG reg_name | COREG coreg_name | 
		             PSRS psrs_name | MEM padr`;
val reg_res_def = Define `
   (reg_res (MEM pa) = F)
/\ (reg_res _ = T)
`;

val res_cases = store_thm("res_cases", ``
!r. (?pa. r = MEM pa) /\ ~reg_res r
 \/ (!pa. r <> MEM pa) /\ reg_res r
``,
  Cases >> (
      RW_TAC std_ss [reg_res_def]
  )
);

val CV_def = Define `
   (CV c (mv:mem_view) (REG r) = c.reg r)
/\ (CV c mv (COREG r) = c.coreg r)
/\ (CV c mv (PSRS r) = c.psrs r)
/\ (CV c mv (MEM pa) = mv T pa)
`;

val CV_reg_lem = store_thm("CV_reg_lem", ``
!c mv mv' r. reg_res r ==> (CV c mv r = CV c mv' r)
``,
  REPEAT STRIP_TAC >>
  Cases_on `r` >> (
      FULL_SIMP_TAC std_ss [reg_res_def, CV_def]
  )   
);


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


(* introduce uninterpreted functions *)

new_constant("MODE", ``:(psrs_name -> word) -> mode``);

val Mode_def = Define `Mode c = MODE c.psrs`; 
val Pc_def = Define `Pc c = c.reg PC`; 

(* Monitor spec *)

val Mmu_MD_exists = prove (``
?(Mmu:core_state # mem_view # vadr # mode # acc -> (padr # bool) option) 
 (MD:core_state # mem_view -> resource set).
!c c' mv mv'. (!r. r IN MD(c,mv) ==> (CV c mv r = CV c' mv' r)) ==>
	      (MD(c,mv) = MD(c',mv')) /\
	      (!va m ac. Mmu(c,mv,va,m,ac) = Mmu(c',mv',va,m,ac))
``,
  EXISTS_TAC ``\(c,mv,va,m,ac):core_state # mem_view # vadr # mode # acc.
		NONE:(padr # bool) option`` >>
  EXISTS_TAC ``\ (c,mv):core_state # mem_view. EMPTY:resource set`` >>
  RW_TAC std_ss []
);  

val Mmu_MD_spec = new_specification ("Mmu_MD_spec",
  ["Mmu_", "MD_"], Mmu_MD_exists);

val dummyMon_def = Define `
   (dummyMon (c,mv, MEM pa ,m,ac) = ?va ca. Mmu_(c,mv,va,m,ac) = SOME (pa,ca))
/\ (dummyMon (c,mv, _ ,m,ac) = F)
`;

val Mon_exists = prove (``
?(Mon:core_state # mem_view # resource # mode # acc -> bool).
!c mv ac. 
   (!pa m. (?va ca. Mmu_(c,mv,va,m,ac) = SOME(pa,ca)) <=> Mon(c,mv,MEM pa,m,ac))
/\ (!r. reg_res r /\ r IN MD_ (c,mv) ==> ~Mon(c,mv,r,USER,ac))
/\ (!r c' mv' m. reg_res r ==> (Mon(c,mv,r,m,ac) = Mon(c',mv',r,m,ac)))
``,
  EXISTS_TAC ``dummyMon`` >>
  RW_TAC std_ss [dummyMon_def] >> (
      Cases_on `r` >> (
          FULL_SIMP_TAC std_ss [reg_res_def] >>
          RW_TAC std_ss [dummyMon_def]
      )
  )  
);  

val Mon_spec = new_specification ("Mon_spec",
  ["Mon_"], Mon_exists);

(* exception entry point *)

val dummyexentry_def = Define `dummyexentry c = (Mode c = PRIV)`;

val exentry_exists = prove (``
?exentry:core_state -> bool. !c. exentry c ==> (Mode c = PRIV)
``,
  EXISTS_TAC ``dummyexentry`` >>
  RW_TAC std_ss [dummyexentry_def]
);  

val exentry_spec = new_specification ("exentry_spec",
  ["exentry_"], exentry_exists);

(***** transition relations *****)

(* requesting transition *)

val core_mode_po = Define `core_mode_po trans = 
!c M mv req c'. trans (c,M,mv,req,c') ==> (Mode c = M)
`;

(* change to PRIV -> exentry *)
val core_exentry_po = Define `core_exentry_po trans = 
!c mv req c'. trans (c,USER,mv,req,c') /\ (Mode c' = PRIV) ==> 
    exentry_ c' /\ (req = NOREQ)
`;

(* mem request -> Mon obeyed *)
val core_Mon_mem_po = Define `core_Mon_mem_po trans = 
!c M mv req c'. trans (c,M,mv,req,c') /\ (req <> NOREQ) ==> 
    (?va. Mmu_(c,mv,va,M,Acc req) = SOME (Adr req, CAreq req))
`;

(* reg unchanged if no Mon permission *)
val core_Mon_reg_po = Define `core_Mon_reg_po trans = 
!c M mv req r c'. reg_res r /\ trans (c,M,mv,req,c') /\ ~Mon_(c,mv,r,M,W) ==>
    (CV c mv r = CV c' mv r)
`;

(* corereq only depending on MD in memview *)
val core_MD_mv_po = Define `core_MD_mv_po trans = 
!c M mv mv' req c'. (!r. r IN MD_ (c,mv) ==> (CV c mv r = CV c mv' r)) ==>
    (trans (c,M,mv,req,c') <=> trans (c,M,mv',req,c'))
`;

(* user transitions do not modify coregs *)
val core_user_coreg_po = Define `core_user_coreg_po trans = 
!c mv req c'. trans (c,USER,mv,req,c') ==> (c'.coreg = c.coreg)
`;

val dummy_cr_def = Define `
dummy_cr (c:core_state,M:mode,mv:mem_view,req:corereq,c':core_state) = 
(c = c') /\ (req = NOREQ) /\ (Mode c = M)
`;

val core_req_exists = prove (``
?(trans:core_state # mode # mem_view # corereq # core_state -> bool).
    core_mode_po trans
 /\ core_exentry_po trans
 /\ core_Mon_mem_po trans
 /\ core_Mon_reg_po trans
 /\ core_MD_mv_po trans
 /\ core_user_coreg_po trans
``,
  EXISTS_TAC ``dummy_cr`` >>
  REPEAT STRIP_TAC 
  >| [(* mode *)
      RW_TAC std_ss [core_mode_po, dummy_cr_def]
      ,
      (* exentry *)
      RW_TAC std_ss [core_exentry_po, dummy_cr_def] >>
      FULL_SIMP_TAC std_ss [mode_distinct]
      ,
      (* memory monitor *)
      RW_TAC std_ss [core_Mon_mem_po, dummy_cr_def]
      ,
      (* reg monitor *)
      RW_TAC std_ss [core_Mon_reg_po, dummy_cr_def]
      ,
      (* MD dependency *)
      RW_TAC std_ss [core_MD_mv_po, dummy_cr_def]
      ,
      (* coreg unchanged *)
      RW_TAC std_ss [core_user_coreg_po, dummy_cr_def]
     ]
);  

val core_req_spec = new_specification ("core_req_spec",
  ["core_req"], core_req_exists);

(* receiving transition, for receiving read results *)

(* does not change mode *)
val rcv_mode_po = Define `rcv_mode_po trans = 
!c M w c'. trans (c,M,w,c') ==> (Mode c = M) /\ (Mode c = Mode c')
`;

val rcv_Mon_reg_po = Define `rcv_Mon_reg_po trans = 
!c M w mv r c'. reg_res r /\ trans (c,M,w,c') /\ ~Mon_(c,mv,r,M,W) ==>
    (CV c mv r = CV c' mv r)
`;

val rcv_user_coreg_po = Define `rcv_user_coreg_po trans = 
!c w c'. trans (c,USER,w,c') ==> (c'.coreg = c.coreg)
`;


val dummy_rcv_def = Define `
dummy_rcv (c:core_state,M:mode,w:word,c':core_state) = 
(c = c') /\ (Mode c = M)
`;

val core_rcv_exists = prove (``
?(trans:core_state # mode # word # core_state -> bool).
    rcv_mode_po trans
 /\ rcv_Mon_reg_po trans
 /\ rcv_user_coreg_po trans
``,
  EXISTS_TAC ``dummy_rcv`` >>
  REPEAT STRIP_TAC 
  >| [(* mode *)
      RW_TAC std_ss [rcv_mode_po, dummy_rcv_def]
      ,
      (* reg monitor *)
      RW_TAC std_ss [rcv_Mon_reg_po, dummy_rcv_def]
      ,
      (* coregs *)
      RW_TAC std_ss [rcv_user_coreg_po, dummy_rcv_def]
     ]
);  

val core_rcv_spec = new_specification ("core_rcv_spec",
  ["core_rcv"], core_rcv_exists);

(* Proof obligations on components, exported to main theory *)

val CR_oblg = store_thm("CR_oblg", ``
!c c' mv mv'. (!r. r IN CR_ (c,mv) ==> (CV c mv r = CV c' mv' r)) ==>
              (CR_ (c,mv) = CR_ (c',mv'))
``,
  METIS_TAC [CR_spec]
);

val Mmu_oblg = store_thm("Mmu_oblg", ``
!c c' mv mv'. (!r. r IN MD_(c,mv) ==> (CV c mv r = CV c' mv' r)) ==>
	      (!va m ac. Mmu_(c,mv,va,m,ac) = Mmu_(c',mv',va,m,ac))
``,
  METIS_TAC [Mmu_MD_spec]
);

val MD_oblg = store_thm("MD_oblg", ``
!c c' mv mv'. (!r. r IN MD_(c,mv) ==> (CV c mv r = CV c' mv' r)) ==>
	      (MD_(c,mv) = MD_(c',mv'))
``,
  METIS_TAC [Mmu_MD_spec]
);

val Mon_mem_oblg = store_thm("Mon_mem_oblg", ``
!c mv pa m ac.
  (?va ca. Mmu_ (c,mv,va,m,ac) = SOME (pa,ca)) <=> Mon_ (c,mv,MEM pa,m,ac)
``,
  METIS_TAC [Mon_spec]
);

val Mon_reg_oblg = store_thm("Mon_reg_oblg", ``
!c mv r c' mv' m ac. reg_res r ==> (Mon_ (c,mv,r,m,ac) <=> Mon_ (c',mv',r,m,ac))
``,
  METIS_TAC [Mon_spec]
);

val core_req_user_MD_reg_oblg = store_thm("core_req_user_MD_reg_oblg", ``
!c mv req r c'. reg_res r /\ r IN MD_ (c,mv) 
	     /\ core_req (c,USER,mv,req,c') ==>
    (CV c mv r = CV c' mv r)
``,
  REPEAT STRIP_TAC >>
  `~Mon_ (c,mv,r,USER,W)` by (   METIS_TAC [Mon_spec] ) >>
  ASSUME_TAC core_req_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_Mon_reg_po
);

val core_rcv_user_MD_reg_oblg = store_thm("core_rcv_user_MD_reg_oblg", ``
!c w mv r c'. reg_res r /\ r IN MD_ (c,mv) 
	   /\ core_rcv (c,USER,w,c') ==>
    (CV c mv r = CV c' mv r)
``,
  REPEAT STRIP_TAC >>
  `~Mon_ (c,mv,r,USER,W)` by (   METIS_TAC [Mon_spec] ) >>
  ASSUME_TAC core_rcv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC rcv_Mon_reg_po
);

val core_req_mmu_oblg = store_thm("core_req_mmu_oblg", ``
!c M mv req c'. core_req (c,M,mv,req,c') /\ req <> NOREQ ==> 
    ?va. Mmu_(c,mv,va,M,Acc req) = SOME (Adr req, CAreq req)
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_req_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_Mon_mem_po >>
  HINT_EXISTS_TAC >>
  ASM_REWRITE_TAC []
);

val core_req_exentry_oblg = store_thm("core_req_exentry_oblg", ``
!c mv req c'. core_req (c,USER,mv,req,c') /\ (Mode c' = PRIV) ==> 
    exentry_ c'
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_req_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_exentry_po
);

val core_req_mode_oblg = store_thm("core_req_mode_oblg", ``
!c mv req c'. core_req (c,USER,mv,req,c') /\ req <> NOREQ ==> 
    Mode c' <> PRIV
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_req_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_exentry_po  
);

val core_rcv_mode_oblg = store_thm("core_rcv_mode_oblg", ``
!c M w c'. core_rcv (c,M,w,c') ==> (Mode c' = Mode c)
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_rcv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC rcv_mode_po >>
  ASM_REWRITE_TAC []
);

val core_req_MD_mv_oblg = store_thm("core_req_MD_mv_oblg", ``
!c M mv mv' req c'. core_req (c,M,mv,req,c') 
		 /\ (!r. r IN MD_ (c,mv) ==> (CV c mv r = CV c mv' r))
        ==> 
    core_req(c,M,mv',req,c')
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_req_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_MD_mv_po  
);

val core_req_user_coreg_oblg = store_thm("core_req_user_coreg_oblg", ``
!c mv req c'. core_req (c,USER,mv,req,c') ==> (c'.coreg = c.coreg)
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_req_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_user_coreg_po  
);

val core_rcv_user_coreg_oblg = store_thm("core_rcv_user_coreg_oblg", ``
!c w c'. core_rcv (c,USER,w,c') ==> (c'.coreg = c.coreg)
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_rcv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC rcv_user_coreg_po 
);



(*********** finish ************)

val _ = export_theory();



