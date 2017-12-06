(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;
open cacheIfTheory;

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

val VApc = Define `VApc c = VADR ((31><2) (c.reg PC) :bool[30])`;

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

val CV_oblg = store_thm("CV_oblg", ``
!c c' mv mv' pa. (mv T pa = mv' T pa) ==> 
    (CV c mv (MEM pa) = CV c' mv' (MEM pa))
``,
  RW_TAC std_ss [CV_def]
);

(* introduce uninterpreted functions *)

new_constant("MODE", ``:(psrs_name -> word) -> mode``);

val Mode_def = Define `Mode c = MODE c.psrs`; 
val Pc_def = Define `Pc c = c.reg PC`; 

(* Monitor spec *)

val Mmu_MD_exists = prove (``
?(Mmu:core_state # mem_view # vadr # mode # acc -> (padr # bool) option) 
 (MD:core_state # mem_view # vadr set -> resource set).
(* MD contains all resources that MD and Mmu depend on *)
!c c' mv mv' VAs. ((!r. r IN MD(c,mv,VAs) ==> (CV c mv r = CV c' mv' r)) ==>
	       (MD(c,mv,VAs) = MD(c',mv',VAs)) /\	
	       (!va m ac. va IN VAs ==>
		          (Mmu(c,mv,va,m,ac) = Mmu(c',mv',va,m,ac))))
(* register Monitor resources only depend on core state *)
           /\ (!r. reg_res r ==> (r IN MD(c,mv,VAs) <=> r IN MD(c',mv',VAs))) 
(* all register Monitor resources are coprocessor registers *)
           /\ (!r. reg_res r /\ r IN MD(c,mv,VAs) ==> ?r'. r = COREG r')
(* MD is monotonically defined set wrt. VAs *)
           /\ (!VAs'. VAs' SUBSET VAs ==> MD(c,mv,VAs') SUBSET MD(c,mv,VAs))
(* reads and fetches have same translation for a given address, 
   must be readable in ARM to be executable,
   similarly, writable addresses are always readable
   NOTE: just used to simplifiy the model, i.e., def of Tr / deps for PC *)
           /\ (!va m pa C. (Mmu(c,mv,va,m,EX) = SOME (pa,C)) ==>
		           (Mmu(c,mv,va,m,R) = SOME (pa,C)))
           /\ (!va m pa C. (Mmu(c,mv,va,m,W) = SOME (pa,C)) ==>
		           (Mmu(c,mv,va,m,R) = SOME (pa,C)))
(* pages span at least one cache line, 
   i.e., addresses with same cache tag have same access permissions *)
           /\ (!va m pa acc C pa'. 
                  (Mmu(c,mv,va,m,acc) = SOME (pa,C)) /\ (tag pa' = tag pa) ==>
		      ?va'. Mmu(c,mv,va',m,acc) = SOME (pa',C))
``,
  EXISTS_TAC ``\(c,mv,va,m,ac):core_state # mem_view # vadr # mode # acc.
		NONE:(padr # bool) option`` >>
  EXISTS_TAC ``\(c,mv):core_state # mem_view # vadr set. EMPTY:resource set`` >>
  RW_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.NOT_IN_EMPTY, 
			pred_setTheory.EMPTY_SUBSET]
);  

val Mmu_MD_spec = new_specification ("Mmu_MD_spec",
  ["Mmu_", "MD_"], Mmu_MD_exists);

val Tr__def = Define `Tr_ c mv va = FST(THE(Mmu_(c,mv,va,Mode c,R)))`;

val Mmu_read_fetch_oblg = store_thm("Mmu_read_fetch_oblg", ``
!c mv va m pa C. (Mmu_(c,mv,va,m,EX) = SOME (pa,C)) ==>
                 (Mmu_(c,mv,va,m,R) = SOME (pa,C))
``,
  METIS_TAC [Mmu_MD_spec]
);

val Mmu_write_read_oblg = store_thm("Mmu_write_read_oblg", ``
!c mv va m pa C. (Mmu_(c,mv,va,m,W) = SOME (pa,C)) ==>
                 (Mmu_(c,mv,va,m,R) = SOME (pa,C))
``,
  METIS_TAC [Mmu_MD_spec]
);

val Mmu_tag_oblg = store_thm("Mmu_tag_oblg", ``
!c mv va m pa acc C pa'. 
    (Mmu_(c,mv,va,m,acc) = SOME (pa,C)) /\ (tag pa' = tag pa) ==>
	?va'. Mmu_(c,mv,va',m,acc) = SOME (pa',C)
``,
  METIS_TAC [Mmu_MD_spec]
);

val MD_monotonic_oblg = store_thm("MD_monotonic_oblg", ``
!c mv VAs VAs'. VAs SUBSET VAs' ==> MD_(c,mv,VAs) SUBSET MD_(c,mv,VAs')
``,
  METIS_TAC [Mmu_MD_spec]
);

val dummyMon_def = Define `
   (dummyMon (c,mv, MEM pa ,m,ac) = ?va ca. Mmu_(c,mv,va,m,ac) = SOME (pa,ca))
/\ (dummyMon (c,mv, _ ,m,ac) = F)
`;

val Mon_exists = prove (``
?(Mon:core_state # mem_view # resource # mode # acc -> bool).
!c mv ac. 
   (!pa m. (?va ca. Mmu_(c,mv,va,m,ac) = SOME(pa,ca)) <=> Mon(c,mv,MEM pa,m,ac))
/\ (!r VAs. reg_res r /\ r IN MD_ (c,mv,VAs) ==> ~Mon(c,mv,r,USER,ac))
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

val exentry__oblg = store_thm("exentry__oblg", ``
!c. exentry_ c ==> (Mode c = PRIV)
``,
  REWRITE_TAC [exentry_spec]
);

(***** transition relations *****)

(* touched va, depending on core registers here, as fetch separate 
   otherwise: need that it is self-contained wrt. translated mem
	    + depending on registers *)

val vdeps_exists = store_thm("vdeps_exists", ``
?vdeps. !c. VApc c IN vdeps c
``,
  EXISTS_TAC ``\c. {VApc c}`` >>
  RW_TAC std_ss [pred_setTheory.IN_SING]
);

val vdeps_spec = new_specification ("vdeps_spec",
  ["vdeps_"], vdeps_exists);

val vdeps_PC_oblg = store_thm("vdeps_PC_oblg", ``
!c. VApc c IN vdeps_ c
``,
  REWRITE_TAC [vdeps_spec]
);

(* physical address dependencies *)

val deps__def = Define `deps_ c mv = 
{pa | ?va. (Tr_ c mv va = pa) /\ va IN vdeps_ c} UNION 
{pa | MEM pa IN MD_(c,mv,vdeps_ c)}
`;

(* requesting transition *)

val core_mode_po = Define `core_mode_po trans = 
!c M mv req c'. trans (c,M,mv,req,c') ==> (Mode c = M)
`;

val core_mode_change_po = Define `core_mode_change_po trans = 
!c M mv req c'. trans (c,M,mv,req,c') /\ req <> NOREQ ==> (Mode c' = Mode c)
`;

(* change to PRIV -> exentry *)
val core_exentry_po = Define `core_exentry_po trans = 
!c mv req c'. trans (c,USER,mv,req,c') /\ (Mode c' = PRIV) ==> exentry_ c'
`;

(* mem request -> Mon obeyed *)
val core_Mon_mem_po = Define `core_Mon_mem_po trans = 
!c M mv req c'. trans (c,M,mv,req,c') ==>
    (Dreq req ==> (?va. va IN vdeps_ c /\ 
		  (Mmu_(c,mv,va,M,Acc req) = SOME (Adr req, CAreq req))))
 /\ (Freq req ==> (Mmu_(c,mv,VApc c,M,EX) = SOME (Adr req, T)))
 /\ (Ireq req ==> (?va. va IN vdeps_ c /\ 
		  (Mmu_(c,mv,va,M,R) = SOME (Adr req, T))))
`;

(* reg unchanged if no Mon permission *)
val core_Mon_reg_po = Define `core_Mon_reg_po trans = 
!c M mv req r c'. reg_res r /\ trans (c,M,mv,req,c') /\ ~Mon_(c,mv,r,M,W) ==>
    (CV c mv r = CV c' mv r)
`;

(* corereq only depending on vdeps *)
val core_MD_mv_po = Define `core_MD_mv_po trans = 
!c mv mv' req c'. 
    (!pa. MEM pa IN MD_(c,mv,vdeps_ c) ==> 
	  (CV c mv (MEM pa) = CV c mv' (MEM pa)))
            ==>
        (trans (c,Mode c,mv,req,c') <=> trans (c,Mode c,mv',req,c'))
`;

(* user transitions do not modify coregs *)
val core_user_coreg_po = Define `core_user_coreg_po trans = 
!c mv req c'. trans (c,USER,mv,req,c') ==> (c'.coreg = c.coreg)
`;

(* core transitions are deterministic *)
val core_det_po = Define `core_det_po trans = 
!c mv m req req' c' c''. trans (c,m,mv,req,c') /\ trans (c,m,mv,req',c'')
        ==> 
    (c' = c'') /\ (req = req')
`;

(* core may not get stuck *)
val core_progress_po = Define `core_progress_po trans = 
!c mv. ?req c'. trans (c,Mode c,mv,req,c')
`;

val dummy_cr_def = Define `
dummy_cr (c:core_state,M:mode,mv:mem_view,req:corereq,c':core_state) = 
(c = c') /\ (req = NOREQ) /\ (Mode c = M)
`;

val core_req_exists = prove (``
?(trans:core_state # mode # mem_view # corereq # core_state -> bool).
    core_mode_po trans
 /\ core_mode_change_po trans
 /\ core_exentry_po trans
 /\ core_Mon_mem_po trans
 /\ core_Mon_reg_po trans
 /\ core_MD_mv_po trans
 /\ core_user_coreg_po trans
 /\ core_det_po trans
 /\ core_progress_po trans
``,
  EXISTS_TAC ``dummy_cr`` >>
  REPEAT STRIP_TAC 
  >| [(* mode *)
      RW_TAC std_ss [core_mode_po, dummy_cr_def]
      ,
      (* mode change *)
      RW_TAC std_ss [core_mode_change_po, dummy_cr_def]
      ,
      (* exentry *)
      RW_TAC std_ss [core_exentry_po, dummy_cr_def] >>
      FULL_SIMP_TAC std_ss [mode_distinct]
      ,
      (* memory monitor *)
      RW_TAC std_ss [core_Mon_mem_po, dummy_cr_def, 
		     Dreq_def, Freq_def, Ireq_def]
      ,
      (* reg monitor *)
      RW_TAC std_ss [core_Mon_reg_po, dummy_cr_def]
      ,
      (* MD dependency *)
      RW_TAC std_ss [core_MD_mv_po, dummy_cr_def]
      ,
      (* coreg unchanged *)
      RW_TAC std_ss [core_user_coreg_po, dummy_cr_def]
      ,
      (* determinism *)
      RW_TAC std_ss [core_det_po, dummy_cr_def]
      ,
      (* progress *)
      RW_TAC std_ss [core_progress_po, dummy_cr_def]
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

(* deterministic *)
val rcv_det_po = Define `rcv_det_po trans = 
!c:core_state m:mode w:word c':core_state c''. 
    trans (c,m,w,c') /\ trans (c,m,w,c'') ==> (c' = c'')
`;

val rcv_progress_po = Define `rcv_progress_po trans = 
!c:core_state m:mode w:word. ?c':core_state. trans (c,Mode c,w,c')
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
 /\ rcv_det_po trans
 /\ rcv_progress_po trans
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
      ,
      (* determinism *)
      RW_TAC std_ss [rcv_det_po, dummy_rcv_def]
      ,
      (* progress *)
      RW_TAC std_ss [rcv_progress_po, dummy_rcv_def]
     ]
);  

val core_rcv_spec = new_specification ("core_rcv_spec",
  ["core_rcv"], core_rcv_exists);

(* Proof obligations on components, exported to main theory *)

val Mmu_oblg = store_thm("Mmu_oblg", ``
!c c' mv mv' VAs. (!r. r IN MD_(c,mv,VAs) ==> (CV c mv r = CV c' mv' r)) ==>
	          (!va m ac. va IN VAs ==>
		             (Mmu_(c,mv,va,m,ac) = Mmu_(c',mv',va,m,ac)))
``,
  METIS_TAC [Mmu_MD_spec]
);

val MD_oblg = store_thm("MD_oblg", ``
!c c' mv mv' VAs. (!r. r IN MD_(c,mv,VAs) ==> (CV c mv r = CV c' mv' r)) ==>
		  (MD_(c,mv,VAs) = MD_(c',mv',VAs))
``,
  METIS_TAC [Mmu_MD_spec]
);

val MD_reg_oblg = store_thm("MD_reg_oblg", ``
!c c' mv mv' VAs. (!r. reg_res r ==> 
		       (r IN MD_(c,mv,VAs) <=> r IN MD_(c',mv',VAs))) 
``,
  METIS_TAC [Mmu_MD_spec]
);

val MD_coreg_oblg = store_thm("MD_coreg_oblg", ``
!c c' mv mv' r VAs. reg_res r /\ r IN MD_(c,mv,VAs) /\ (c.coreg = c'.coreg) ==> 
    (CV c mv r = CV c' mv' r) 
``,
  REPEAT STRIP_TAC >>
  IMP_RES_TAC Mmu_MD_spec >>
  RW_TAC std_ss [CV_def]
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

val Mon_tag_oblg = store_thm("Mon_tag_oblg", ``
!c mv pa pa' m ac. (tag pa = tag pa') ==>
    (Mon_ (c,mv,MEM pa,m,ac) <=> Mon_ (c,mv,MEM pa',m,ac))
``,
  RW_TAC std_ss [GSYM Mon_mem_oblg] >>
  EQ_TAC >> (
      STRIP_TAC >>
      METIS_TAC [Mmu_tag_oblg]
  )
);

val core_req_curr_mode_oblg = store_thm("core_req_curr_mode_oblg", ``
!c M mv req c'. core_req (c,M,mv,req,c') ==> (Mode c = M)
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_req_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_mode_po
);

val core_req_mode_change_oblg = store_thm("core_req_mode_change_oblg", ``
!c M mv req c'. core_req (c,M,mv,req,c') /\ req <> NOREQ ==> (Mode c' = Mode c)
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_req_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_mode_change_po
);

val core_req_user_MD_reg_oblg = store_thm("core_req_user_MD_reg_oblg", ``
!c mv req r c' VAs. reg_res r /\ r IN MD_ (c,mv,VAs) 
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
!c w mv r c' VAs. reg_res r /\ r IN MD_ (c,mv,VAs) 
	       /\ core_rcv (c,USER,w,c') ==>
    (CV c mv r = CV c' mv r)
``,
  REPEAT STRIP_TAC >>
  `~Mon_ (c,mv,r,USER,W)` by (   METIS_TAC [Mon_spec] ) >>
  ASSUME_TAC core_rcv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC rcv_Mon_reg_po
);

val core_req_mmu_Freq_oblg = store_thm("core_req_mmu_Freq_oblg", ``
!c M mv req c'. core_req (c,M,mv,req,c') /\ Freq req ==> 
    (Mmu_(c,mv,VApc c,M,EX) = SOME (Adr req, T))
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_req_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_Mon_mem_po
);

val core_req_mmu_Ireq_oblg = store_thm("core_req_mmu_Ireq_oblg", ``
!c M mv req c'. core_req (c,M,mv,req,c') /\ Ireq req ==> 
    ?va. va IN vdeps_ c 
      /\ (Mmu_(c,mv,va,M,R) = SOME (Adr req, T))
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_req_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_Mon_mem_po >>
  HINT_EXISTS_TAC >>
  ASM_REWRITE_TAC []
);

val core_req_mmu_Dreq_oblg = store_thm("core_req_mmu_Dreq_oblg", ``
!c M mv req c'. core_req (c,M,mv,req,c') /\ Dreq req ==> 
    ?va. va IN vdeps_ c 
      /\ (Mmu_(c,mv,va,M,Acc req) = SOME (Adr req, CAreq req))
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
  IMP_RES_TAC core_exentry_po >> 
  IMP_RES_TAC core_mode_po >> 
  IMP_RES_TAC core_mode_change_po >>
  REV_FULL_SIMP_TAC std_ss [mode_distinct]
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
!c mv mv' req c'. 
    (!pa. MEM pa IN MD_(c,mv,vdeps_ c) ==> 
	  (CV c mv (MEM pa) = CV c mv' (MEM pa)))
        ==> 
    (core_req(c,Mode c,mv,req,c') <=> core_req(c,Mode c,mv',req,c'))
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_req_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_MD_mv_po >>
  RW_TAC std_ss []
);

val core_req_user_coreg_oblg = store_thm("core_req_user_coreg_oblg", ``
!c mv req c'. core_req (c,USER,mv,req,c') ==> (c'.coreg = c.coreg)
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_req_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_user_coreg_po  
);

val core_req_det_oblg = store_thm("core_req_det_oblg", ``
!c m mv req req' c' c''. 
    core_req(c,m,mv,req,c') /\ core_req(c,m,mv,req',c'')
        ==>
    (c' = c'') /\ (req = req')
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >> 
  ASSUME_TAC core_req_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_det_po >>
  RW_TAC std_ss []
);

val core_req_progress_oblg = store_thm("core_req_progress_oblg", ``
!c mv. ?req c'. core_req(c,Mode c,mv,req,c')
``,
  REPEAT GEN_TAC >>
  ASSUME_TAC core_req_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC core_progress_po >>
  RW_TAC std_ss []
);

val core_rcv_user_coreg_oblg = store_thm("core_rcv_user_coreg_oblg", ``
!c w c'. core_rcv (c,USER,w,c') ==> (c'.coreg = c.coreg)
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_rcv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC rcv_user_coreg_po 
);

val core_rcv_det_oblg = store_thm("core_rcv_det_oblg", ``
!c M w c' c''. core_rcv (c,M,w,c') /\ core_rcv (c,M,w,c'')  ==> (c' = c'')
``,
  REPEAT STRIP_TAC >>
  ASSUME_TAC core_rcv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC rcv_det_po
);

val core_rcv_progress_oblg = store_thm("core_rcv_progress_oblg", ``
!c w. ?c'. core_rcv (c,Mode c,w,c')
``,
  REPEAT GEN_TAC >>
  ASSUME_TAC core_rcv_spec >>
  FULL_SIMP_TAC std_ss [] >>
  IMP_RES_TAC rcv_progress_po >>
  RW_TAC std_ss []
);

(*********** finish ************)

val _ = export_theory();



