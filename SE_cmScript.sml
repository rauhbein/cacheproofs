(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open hwTheory;
open cachelessTheory;
open InvIfTheory;
open integrityTheory;

val _ = new_theory "SE_cm";

(********* Instantiation: Selective Eviction *********)

(* importing obligations *)

val abs_ca_unique_lem = store_thm("abs_ca_unique_lem", ``
!s m dl dl' s' s''. abs_ca_trans s m dl s' /\ abs_ca_trans s m dl' s'' ==>
    (s'' = s') /\ (dl' = dl)
``,
  REWRITE_TAC [abs_ca_unique_oblg]
);

val abs_cl_unique_lem = store_thm("abs_cl_unique_lem", ``
!s m dl dl' s' s''. abs_cl_trans s m dl s' /\ abs_cl_trans s m dl' s'' ==>
    (s'' = s') /\ (dl' = dl)
``,
  REWRITE_TAC [abs_cl_unique_oblg]
);

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

(* padr history variables, start with empty history *)
(* cacheless history *)

val (cl_hist_rules, cl_hist_ind, cl_hist_cases) = Hol_reln `
    (!s s' f h. 
         cl_exentry s
      /\ (s = s')
      /\ (h = EMPTY:padr set) 
     ==> cl_hist f s s' h 0)
 /\ (!s s' s'' f h dl h' n. 
	 cl_hist f s s' h n
      /\ abs_cl_trans s' PRIV dl s'' 
      /\ (h' = f h dl)
     ==> cl_hist f s s'' h' (SUC n))
`;

val cl_hist_init_lem = store_thm("cl_hist_init_lem", ``
!s f. cl_exentry s ==> cl_hist f s s EMPTY 0
``,
  ONCE_REWRITE_TAC [cl_hist_cases] >>
  RW_TAC std_ss []
);

val cl_hist_0_lem = store_thm("cl_hist_0_lem", ``
!s s' f h. cl_hist f s s' h 0 ==> (h = EMPTY) /\ (s = s') /\ cl_exentry s
``,
  ONCE_REWRITE_TAC [cl_hist_cases] >>
  RW_TAC arith_ss []
);

val cl_hist_SUC_lem = store_thm("cl_hist_SUC_lem", ``
!s s' f h n. cl_hist f s s' h (SUC n) <=> 
   ?h' s'' dl. cl_hist f s s'' h' n
            /\ (h = f h' dl)
            /\ abs_cl_trans s'' PRIV dl s' 
``,
  REPEAT STRIP_TAC >>
  EQ_TAC 
  >| [(* ==> *)
      STRIP_TAC >>
      IMP_RES_TAC cl_hist_cases >> (
          FULL_SIMP_TAC std_ss [numTheory.NOT_SUC]
      ) >>
      METIS_TAC []
      ,
      (* <== *)
      STRIP_TAC >>      
      ONCE_REWRITE_TAC [cl_hist_cases] >>
      FULL_SIMP_TAC std_ss [numTheory.NOT_SUC] >>
      METIS_TAC []
     ]
);

val cl_hist_kcomp_lem = store_thm("cl_hist_kcomp_lem", ``
!s s' f n. cl_kcomp s s' n <=> ?h. cl_hist f s s' h n
``,
  Induct_on `n`
  >| [(* n = 0 *)
      RW_TAC std_ss [] >>
      EQ_TAC
      >| [(* ==> *)
	  STRIP_TAC >>
          IMP_RES_TAC cl_kcomp_0_lem >>
	  EXISTS_TAC ``EMPTY:padr set`` >>
	  RW_TAC std_ss [cl_hist_init_lem]
	  ,
	  (* <== *)
	  STRIP_TAC >>
          IMP_RES_TAC cl_hist_0_lem >>
	  ASM_REWRITE_TAC [] >>
	  ONCE_REWRITE_TAC [cl_kcomp_cases] >>
	  RW_TAC std_ss []
	 ]
      ,
      (* n -> SUC n *)
      REPEAT STRIP_TAC >>
      EQ_TAC 
      >| [(* ==> *)
	  RW_TAC std_ss [cl_kcomp_SUC_lem] >>
          RES_TAC >>
	  PAT_X_ASSUM ``!f. ?h. x`` (
              fn thm => ASSUME_TAC ( SPEC ``f:(padr -> bool) -> 
					      mop list -> 
					      padr -> bool`` thm )
	  ) >>
	  FULL_SIMP_TAC std_ss [] >>
	  EXISTS_TAC ``(f (h:padr set) (dl:mop list)):padr set`` >>
	  ONCE_REWRITE_TAC [cl_hist_cases] >>
	  METIS_TAC []
	  ,
	  (* <== *)
	  STRIP_TAC >>
	  RES_TAC >>
	  IMP_RES_TAC cl_hist_SUC_lem >>
	  RES_TAC >>
	  RW_TAC std_ss [cl_kcomp_SUC_lem] >>
	  METIS_TAC []
	 ]
     ]
);

val cl_kcomp_unique_lem = store_thm("cl_kcomp_unique_lem", ``
!s s' s'' n. cl_kcomp s s' n /\ cl_kcomp s s'' n ==> (s' = s'')
``,
  Induct_on `n`
  >| [(* n = 0 *)
      RW_TAC std_ss [] >>
      IMP_RES_TAC cl_kcomp_0_lem >>
      ASM_REWRITE_TAC []
      ,
      (* n -> SUC n *)
      RW_TAC std_ss [cl_kcomp_SUC_lem] >>
      RES_TAC >>
      RW_TAC std_ss [] >>
      IMP_RES_TAC abs_cl_unique_lem
     ]
);

val cl_hist_unique_lem = store_thm("cl_hist_unique_lem", ``
!s s' f n h h'.
    cl_hist f s s' h n
 /\ cl_hist f s s' h' n
        ==>
    (h = h')
``,
  Induct_on `n`
  >| [(* n = 0 *)
      RW_TAC std_ss [] >>
      IMP_RES_TAC cl_hist_0_lem >>
      RW_TAC std_ss []
      ,
      (* n -> SUC n *)
      RW_TAC std_ss [cl_kcomp_SUC_lem, cl_hist_SUC_lem] >>
      `cl_kcomp s s'' n /\ cl_kcomp s s''' n` by (
          IMP_RES_TAC cl_hist_kcomp_lem >>
	  ASM_REWRITE_TAC []
      ) >>
      IMP_RES_TAC cl_kcomp_unique_lem >>
      RW_TAC std_ss [] >>
      RES_TAC >>
      IMP_RES_TAC abs_cl_unique_lem >>
      RW_TAC std_ss []
     ]
);

val clh_def = Define `clh f s s' n = CHOICE {h | cl_hist f s s' h n}`;

val clh_sing_lem = store_thm("clh_sing_lem", ``
!f s s' h n. cl_hist f s s' h n <=> ({h | cl_hist f s s' h n} = {h}) 
``,
  REPEAT STRIP_TAC >>
  EQ_TAC
  >| [(* ==> *)
      RW_TAC std_ss [pred_setTheory.EXTENSION] >>
      RW_TAC std_ss [pred_setTheory.IN_SING, pred_setTheory.IN_GSPEC_IFF] >>
      EQ_TAC
      >| [(* unique hist *)
	  STRIP_TAC >>
	  IMP_RES_TAC cl_hist_unique_lem
	  ,
	  (* trivial *)
	  RW_TAC std_ss []
	 ]
      ,
      (* <== *)
      RW_TAC std_ss [pred_setTheory.EXTENSION,
		     pred_setTheory.IN_SING, 
		     pred_setTheory.IN_GSPEC_IFF]
     ]
);

val clh_unique_lem = store_thm("clh_unique_lem", ``
!f s s' h n. cl_kcomp s s' n ==> 
(cl_hist f s s' h n <=> (clh f s s' n = h))
``,
  RW_TAC std_ss [clh_def] >>
  EQ_TAC
  >| [(* ==> *)
      STRIP_TAC >>
      IMP_RES_TAC clh_sing_lem >>
      ASM_REWRITE_TAC [pred_setTheory.CHOICE_SING]
      ,
      (* <== *)
      IMP_RES_TAC cl_hist_kcomp_lem >>
      PAT_X_ASSUM ``!f. ?h. x`` (
          fn thm => ASSUME_TAC ( SPEC ``f:(padr -> bool) -> 
					  mop list -> 
					  padr -> bool`` thm )
      ) >>
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC clh_sing_lem >>
      ASM_REWRITE_TAC [pred_setTheory.CHOICE_SING] >>
      STRIP_TAC >>
      FULL_SIMP_TAC std_ss []
     ]
);

val cl_hist_clh_lem = store_thm("cl_hist_clh_lem", ``
!f s s' h n. cl_kcomp s s' n ==> cl_hist f s s' (clh f s s' n) n 
``,
  REPEAT STRIP_TAC >>
  `?h. clh f s s' n = h` by ( RW_TAC std_ss [] ) >>
  ASM_REWRITE_TAC [] >>
  IMP_RES_TAC clh_unique_lem
); 

val clh_0_lem = store_thm("clh_0_lem", ``
!f s n. cl_exentry s ==> (clh f s s 0 = EMPTY)
``,
  REPEAT STRIP_TAC >>
  `cl_hist f s s EMPTY 0` by ( 
      IMP_RES_TAC cl_hist_init_lem >>
      ASM_REWRITE_TAC []
  ) >>
  `cl_kcomp s s 0` by ( IMP_RES_TAC cl_kcomp_rules ) >>
  IMP_RES_TAC clh_unique_lem
); 

val clh_SUC_lem = store_thm("clh_SUC_lem", ``
!f s s' s'' n dl. cl_kcomp s s' n /\ abs_cl_trans s' PRIV dl s'' ==> 
    (clh f s s'' (SUC n) = f (clh f s s' n) dl)
``,
  REPEAT STRIP_TAC >>
  `cl_kcomp s s'' (SUC n)` by ( IMP_RES_TAC cl_kcomp_SUC_lem ) >>
  `?h. cl_hist f s s'' h (SUC n)` by ( 
      IMP_RES_TAC cl_hist_kcomp_lem >>
      ASM_REWRITE_TAC []
  ) >>
  `?h' s''' dl'. cl_hist f s s''' h' n 
              /\ (h = f h' dl') 
              /\ abs_cl_trans s''' PRIV dl' s''` by (
      IMP_RES_TAC cl_hist_SUC_lem >>
      METIS_TAC []
  ) >>
  `(s''' = s') /\ (dl' = dl)` by (
      IMP_RES_TAC cl_hist_kcomp_lem >>
      IMP_RES_TAC cl_kcomp_unique_lem >>
      RW_TAC std_ss [] >>
      IMP_RES_TAC abs_cl_unique_lem 
  ) >>
  RW_TAC std_ss [] >>
  IMP_RES_TAC clh_unique_lem >>
  ASM_REWRITE_TAC []
); 

(* cache-aware history *)

val (ca_hist_rules, ca_hist_ind, ca_hist_cases) = Hol_reln `
    (!s s' f h. 
         exentry s
      /\ (s = s')
      /\ (h = EMPTY:padr set) 
     ==> ca_hist f s s' h 0)
 /\ (!s s' s'' f h dl h' n. 
	 ca_hist f s s' h n
      /\ abs_ca_trans s' PRIV dl s'' 
      /\ (h' = f h dl)
     ==> ca_hist f s s'' h' (SUC n))
`;

val ca_hist_init_lem = store_thm("ca_hist_init_lem", ``
!s f. exentry s ==> ca_hist f s s EMPTY 0
``,
  ONCE_REWRITE_TAC [ca_hist_cases] >>
  RW_TAC std_ss []
);

val ca_hist_0_lem = store_thm("ca_hist_0_lem", ``
!s s' f h. ca_hist f s s' h 0 ==> (h = EMPTY) /\ (s = s') /\ exentry s
``,
  ONCE_REWRITE_TAC [ca_hist_cases] >>
  RW_TAC arith_ss []
);

val ca_hist_SUC_lem = store_thm("ca_hist_SUC_lem", ``
!s s' f h n. ca_hist f s s' h (SUC n) <=> 
   ?h' s'' dl. ca_hist f s s'' h' n
            /\ (h = f h' dl)
            /\ abs_ca_trans s'' PRIV dl s' 
``,
  REPEAT STRIP_TAC >>
  EQ_TAC 
  >| [(* ==> *)
      STRIP_TAC >>
      IMP_RES_TAC ca_hist_cases >> (
          FULL_SIMP_TAC std_ss [numTheory.NOT_SUC]
      ) >>
      METIS_TAC []
      ,
      (* <== *)
      STRIP_TAC >>      
      ONCE_REWRITE_TAC [ca_hist_cases] >>
      FULL_SIMP_TAC std_ss [numTheory.NOT_SUC] >>
      METIS_TAC []
     ]
);

val ca_hist_kcomp_lem = store_thm("ca_hist_kcomp_lem", ``
!s s' f n. ca_kcomp s s' n <=> ?h. ca_hist f s s' h n
``,
  Induct_on `n`
  >| [(* n = 0 *)
      RW_TAC std_ss [] >>
      EQ_TAC
      >| [(* ==> *)
	  STRIP_TAC >>
          IMP_RES_TAC ca_kcomp_0_lem >>
	  EXISTS_TAC ``EMPTY:padr set`` >>
	  RW_TAC std_ss [ca_hist_init_lem]
	  ,
	  (* <== *)
	  STRIP_TAC >>
          IMP_RES_TAC ca_hist_0_lem >>
	  ASM_REWRITE_TAC [] >>
	  ONCE_REWRITE_TAC [ca_kcomp_cases] >>
	  RW_TAC std_ss []
	 ]
      ,
      (* n -> SUC n *)
      REPEAT STRIP_TAC >>
      EQ_TAC 
      >| [(* ==> *)
	  RW_TAC std_ss [ca_kcomp_SUC_lem] >>
          RES_TAC >>
	  PAT_X_ASSUM ``!f. ?h. x`` (
              fn thm => ASSUME_TAC ( SPEC ``f:(padr -> bool) -> 
					      mop list -> 
					      padr -> bool`` thm )
	  ) >>
	  FULL_SIMP_TAC std_ss [] >>
	  EXISTS_TAC ``(f (h:padr set) (dl:mop list)):padr set`` >>
	  ONCE_REWRITE_TAC [ca_hist_cases] >>
	  METIS_TAC []
	  ,
	  (* <== *)
	  STRIP_TAC >>
	  RES_TAC >>
	  IMP_RES_TAC ca_hist_SUC_lem >>
	  RES_TAC >>
	  RW_TAC std_ss [ca_kcomp_SUC_lem] >>
	  METIS_TAC []
	 ]
     ]
);

val ca_kcomp_unique_lem = store_thm("ca_kcomp_unique_lem", ``
!s s' s'' n. ca_kcomp s s' n /\ ca_kcomp s s'' n ==> (s' = s'')
``,
  Induct_on `n`
  >| [(* n = 0 *)
      RW_TAC std_ss [] >>
      IMP_RES_TAC ca_kcomp_0_lem >>
      ASM_REWRITE_TAC []
      ,
      (* n -> SUC n *)
      RW_TAC std_ss [ca_kcomp_SUC_lem] >>
      RES_TAC >>
      RW_TAC std_ss [] >>
      IMP_RES_TAC abs_ca_unique_lem
     ]
);

val ca_hist_unique_lem = store_thm("ca_hist_unique_lem", ``
!s s' f n h h'.
    ca_hist f s s' h n
 /\ ca_hist f s s' h' n
        ==>
    (h = h')
``,
  Induct_on `n`
  >| [(* n = 0 *)
      RW_TAC std_ss [] >>
      IMP_RES_TAC ca_hist_0_lem >>
      RW_TAC std_ss []
      ,
      (* n -> SUC n *)
      RW_TAC std_ss [ca_kcomp_SUC_lem, ca_hist_SUC_lem] >>
      `ca_kcomp s s'' n /\ ca_kcomp s s''' n` by (
          IMP_RES_TAC ca_hist_kcomp_lem >>
	  ASM_REWRITE_TAC []
      ) >>
      IMP_RES_TAC ca_kcomp_unique_lem >>
      RW_TAC std_ss [] >>
      RES_TAC >>
      IMP_RES_TAC abs_ca_unique_lem >>
      RW_TAC std_ss []
     ]
);

val cah_def = Define `cah f s s' n = CHOICE {h | ca_hist f s s' h n}`;

val cah_sing_lem = store_thm("cah_sing_lem", ``
!f s s' h n. ca_hist f s s' h n <=> ({h | ca_hist f s s' h n} = {h}) 
``,
  REPEAT STRIP_TAC >>
  EQ_TAC
  >| [(* ==> *)
      RW_TAC std_ss [pred_setTheory.EXTENSION] >>
      RW_TAC std_ss [pred_setTheory.IN_SING, pred_setTheory.IN_GSPEC_IFF] >>
      EQ_TAC
      >| [(* unique hist *)
	  STRIP_TAC >>
	  IMP_RES_TAC ca_hist_unique_lem
	  ,
	  (* trivial *)
	  RW_TAC std_ss []
	 ]
      ,
      (* <== *)
      RW_TAC std_ss [pred_setTheory.EXTENSION,
		     pred_setTheory.IN_SING, 
		     pred_setTheory.IN_GSPEC_IFF]
     ]
);

val cah_unique_lem = store_thm("cah_unique_lem", ``
!f s s' h n. ca_kcomp s s' n ==> 
(ca_hist f s s' h n <=> (cah f s s' n = h))
``,
  RW_TAC std_ss [cah_def] >>
  EQ_TAC
  >| [(* ==> *)
      STRIP_TAC >>
      IMP_RES_TAC cah_sing_lem >>
      ASM_REWRITE_TAC [pred_setTheory.CHOICE_SING]
      ,
      (* <== *)
      IMP_RES_TAC ca_hist_kcomp_lem >>
      PAT_X_ASSUM ``!f. ?h. x`` (
          fn thm => ASSUME_TAC ( SPEC ``f:(padr -> bool) -> 
					  mop list -> 
					  padr -> bool`` thm )
      ) >>
      FULL_SIMP_TAC std_ss [] >>
      IMP_RES_TAC cah_sing_lem >>
      ASM_REWRITE_TAC [pred_setTheory.CHOICE_SING] >>
      STRIP_TAC >>
      FULL_SIMP_TAC std_ss []
     ]
);

val ca_hist_cah_lem = store_thm("ca_hist_cah_lem", ``
!f s s' h n. ca_kcomp s s' n ==> ca_hist f s s' (cah f s s' n) n 
``,
  REPEAT STRIP_TAC >>
  `?h. cah f s s' n = h` by ( RW_TAC std_ss [] ) >>
  ASM_REWRITE_TAC [] >>
  IMP_RES_TAC cah_unique_lem
); 

val cah_0_lem = store_thm("cah_0_lem", ``
!f s n. exentry s ==> (cah f s s 0 = EMPTY)
``,
  REPEAT STRIP_TAC >>
  `ca_hist f s s EMPTY 0` by ( 
      IMP_RES_TAC ca_hist_init_lem >>
      ASM_REWRITE_TAC []
  ) >>
  `ca_kcomp s s 0` by ( IMP_RES_TAC ca_kcomp_rules ) >>
  IMP_RES_TAC cah_unique_lem
); 

val cah_SUC_lem = store_thm("cah_SUC_lem", ``
!f s s' s'' n dl. ca_kcomp s s' n /\ abs_ca_trans s' PRIV dl s'' ==> 
    (cah f s s'' (SUC n) = f (cah f s s' n) dl)
``,
  REPEAT STRIP_TAC >>
  `ca_kcomp s s'' (SUC n)` by ( IMP_RES_TAC ca_kcomp_SUC_lem ) >>
  `?h. ca_hist f s s'' h (SUC n)` by ( 
      IMP_RES_TAC ca_hist_kcomp_lem >>
      ASM_REWRITE_TAC []
  ) >>
  `?h' s''' dl'. ca_hist f s s''' h' n 
              /\ (h = f h' dl') 
              /\ abs_ca_trans s''' PRIV dl' s''` by (
      IMP_RES_TAC ca_hist_SUC_lem >>
      METIS_TAC []
  ) >>
  `(s''' = s') /\ (dl' = dl)` by (
      IMP_RES_TAC ca_hist_kcomp_lem >>
      IMP_RES_TAC ca_kcomp_unique_lem >>
      RW_TAC std_ss [] >>
      IMP_RES_TAC abs_ca_unique_lem 
  ) >>
  RW_TAC std_ss [] >>
  IMP_RES_TAC cah_unique_lem >>
  ASM_REWRITE_TAC []
); 


(* bisim property *)

val hist_bisim_lem = store_thm("hist_bisim_lem", ``
!s s' sc sc' m dl (n:num) f Icoh Icode Icm ca_Icmf.
    cm_user_po Icoh Icode Icm
 /\ ca_Icmf_po ca_Icmf Icoh Icode Icm
 /\ Rsim sc s
 /\ (!m s'' sc''. 
        m <= n
     /\ cl_kcomp s s'' m
     /\ ca_kcomp sc sc'' m
            ==>
        Rsim sc'' s''
     /\ ca_Icmf sc sc'' m)
 /\ Icoh sc
 /\ cl_kcomp s s' n
 /\ ca_kcomp sc sc' n
        ==>
    (clh f s s' n = cah f sc sc' n)
``,
  Induct_on `n`
  >| [(* n = 0 *)
      REPEAT STRIP_TAC >>
      IMP_RES_TAC cl_kcomp_0_lem >>
      IMP_RES_TAC ca_kcomp_0_lem >>
      IMP_RES_TAC clh_0_lem >>
      IMP_RES_TAC cah_0_lem >>
      ASM_REWRITE_TAC []
      ,
      (* n -> SUC n *)
      REPEAT STRIP_TAC >>
      FULL_SIMP_TAC std_ss [cl_kcomp_SUC_lem, ca_kcomp_SUC_lem] >>
      `n <= SUC n` by ( RW_TAC arith_ss [] ) >>
      `Rsim s''' s''` by ( RES_TAC ) >>
      `ca_Icmf sc s''' n` by ( RES_TAC ) >>
      `s''.cs = s'''.cs` by ( IMP_RES_TAC Rsim_cs_lem ) >>
      `dl = dl'` by (
          MATCH_MP_TAC core_bisim_dl_lem >>
	  IMP_RES_TAC ca_Icmf_po_def >>
	  IMP_RES_TAC Rsim_dCoh_Cv_lem >>
	  METIS_TAC []
      ) >>
      RW_TAC std_ss [] >>
      `!m s1 sc1. m <= n /\ cl_kcomp s s1 m /\ ca_kcomp sc sc1 m ==>
		  Rsim sc1 s1 /\ ca_Icmf sc sc1 m` by ( 
          REPEAT GEN_TAC >>
	  STRIP_TAC >>
	  `m <= SUC n` by ( DECIDE_TAC ) >>
	  METIS_TAC [] 
      ) >>
      `clh f s s'' n = cah f sc s''' n` by ( METIS_TAC [] ) >>
      IMP_RES_TAC clh_SUC_lem >>
      IMP_RES_TAC cah_SUC_lem >>
      RW_TAC std_ss []
     ]
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
 /\ pa IN hdclnw hd dl INTER hicl hi dl
        ==>
    pa IN hd
``,
  RW_TAC std_ss [pred_setTheory.IN_INTER, hdclnw_def, hicl_def] >>
  FULL_SIMP_TAC std_ss [pred_setTheory.IN_UNION]
  >| [(* in hd diff w / hi diff w cl *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF]
      ,
      (* in hd diff w / icl *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF]
      ,
      (* in cl / hi diff w cl *)
      FULL_SIMP_TAC std_ss [pred_setTheory.IN_DIFF, pred_setTheory.IN_UNION]
      ,
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
    !pa. pa IN hdclnw hd dl INTER hicl hi dl ==> 
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
    !pa. pa IN (A DIFF hw) UNION (hd INTER hi) ==> 
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
    !pa. pa IN (A DIFF hwr hw dl) UNION (hdclnw hd dl INTER hicl hi dl) ==> 
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
