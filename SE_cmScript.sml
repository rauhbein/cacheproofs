(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open hwTheory;
open cachelessTheory;
open InvIfTheory;
open integrityTheory;

val _ = new_theory "AC_cm";

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

(* padr history variables, start with empty history *)

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

