(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;
open cacheIfTheory;

val _ = new_theory "cachemem";

(* memory state and memory view *)

val _ = Parse.type_abbrev("mem_state", ``:padr -> word``);

(* cacheless memory view *)
val MVcl_def = Define `MVcl (m:mem_state) = 
\(c:bool) pa. m pa
`;

(* cache-aware memory view *)
val MVca_def = Define `MVca ca m = 
\c pa. if c /\ chit_ ca pa then ccnt_ ca pa else m pa
`;

(* alternative memory view *)
val MValt_def = Define `MValt ca m = 
\c pa. if c /\ cdirty_ ca pa then ccnt_ ca pa else m pa
`;

(* memory semantics *)

(* cacheless *)
val mtfcl_def = Define `
   (mtfcl m (WT pa w c) = (pa =+ w) m)
/\ (mtfcl m _ = m)
`;

val wb_def = Define `
   (wb (ca:cache_state,NONE) (m:mem_state) = (ca,m))
/\ (wb (ca,SOME(pa,w)) m = (ca,(pa =+ w) m))
`;

val wb_mem_def = Define `
   (wb_mem m NONE = m)
/\ (wb_mem m (SOME (pa,w)) = (pa =+ w) m)
`;

val wb_lem = store_thm("wb_lem", ``
!ca m w. wb (ca,w) m = (ca,wb_mem m w)
``,
  Cases_on `w`
  >| [(* NONE *)
      RW_TAC std_ss [wb_def, wb_mem_def]
      ,
      (* SOME x *)
      REPEAT STRIP_TAC >>
      `?c w. x = (c,w)` by (
          RW_TAC std_ss [pairTheory.pair_CASES]
      ) >>
      RW_TAC std_ss [wb_def, wb_mem_def]
     ]
);

(* cache-aware *)
val mtfca_def = Define `
   (mtfca ca m (RD pa T)   = wb (ctf ca (MVcl m) (RD pa T)) m)
/\ (mtfca ca m (WT pa w T) = wb (ctf ca (MVcl m) (WT pa w T)) m)
/\ (mtfca ca m (WT pa w F) = (ca,(pa =+ w) m))
/\ (mtfca ca m (CL pa)     = wb (ctf ca (MVcl m) (CL pa)) m)
/\ (mtfca ca m _           = (ca,m))
`;

(* TODO: add some useful lemmas *)

val mtfca_cacheable = store_thm("mtfca_cacheable", ``
!ca m dop. CA dop ==> (mtfca ca m dop = wb (ctf ca (MVcl m) dop) m)
``,
  RW_TAC std_ss [CA_lem] >> (
      FULL_SIMP_TAC std_ss [mtfca_def]
  )
);

val cl_mem_unchanged = store_thm("cl_mem_unchanged", ``
!m dop m'. ~wt dop /\ (mtfcl m dop = m') ==>
(MVcl m = MVcl m')
``,
  RW_TAC std_ss [not_wt_lem, rd_lem, cl_lem] >> (
      RW_TAC std_ss [mtfcl_def]
  )
);    

val cl_write_semantics = store_thm("cl_write_semantics", ``
!m m' pa w c. (mtfcl m (WT pa w c) = m') ==>
   (!c. (MVcl m') c pa = w) 
/\ (!pa' c. pa <> pa' ==> ((MVcl m) c pa' = (MVcl m') c pa'))
``,
  RW_TAC std_ss [MVcl_def, mtfcl_def] >> (
      RW_TAC std_ss [combinTheory.APPLY_UPDATE_THM]
  )
); 

val ca_uncacheable = store_thm("ca_uncacheable", ``
!ca m dop ca' m'. ~CA dop /\ (mtfca ca m dop = (ca',m')) ==>
   (ca' = ca) /\ (m' = mtfcl m dop)
``,
  RW_TAC std_ss [not_CA_lem] >> (
      FULL_SIMP_TAC std_ss [mtfca_def, mtfcl_def]
  )
);

val ca_cl_reduction = store_thm("ca_cl_reduction", ``
!ca m c. MVca ca m F = MVcl m c 
``,
  RW_TAC std_ss [MVcl_def, MVca_def]
);


val ca_cacheable_mem = store_thm("ca_cacheable_mem", ``
!ca m dop ca' m'. CA dop /\ ((ca',m') = mtfca ca m dop) ==>
    !pa. (m' pa = m pa) \/ (ca pa = SOME(m' pa, T))
``,
  RW_TAC (std_ss++boolSimps.CONJ_ss) [mtfca_cacheable] >>
  cheat
);


(*********** finish ************)

val _ = export_theory();
