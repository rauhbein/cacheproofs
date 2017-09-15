(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

open basetypesTheory;
open cachememTheory;

val _ = new_theory "msIf";

(* TODO: 
- ms record type
- accessor functions
- transition function / relation
- lift deriveability lemmas
- IC lemmas / invariant
*)

val _ = Datatype `memsys_state = <| 
    dc  : cache_state;
    ic  : cache_state;
    mem : mem_state 
|>`;

val dw_def = Define `dw ms pa = ms.dc pa`;
val dhit_def = Define `dhit ms pa = chit_ ms.dc pa`;
val dirty_def = Define `dirty ms pa = cdirty_ ms.dc pa`;
val dcnt_def = Define `dcnt ms pa = ccnt_ ms.dc pa`;
val M_def = Define `M ms pa = ms.mem pa`;

val iw_def = Define `iw ms pa = ms.ic pa`;
val ihit_def = Define `ihit ms pa = chit_ ms.ic pa`;
val icnt_def = Define `icnt ms pa = ccnt_ ms.ic pa`;

(* instruction cache invariant *)

val Invic_def = Define `Invic ms = !pa. ~cdirty_ ms.ic pa`;

(* lookup functions / memory views *)

val dmvcl_def = Define `dmvcl ms = MVcl ms.mem`;
val dmvca_def = Define `dmvca ms = MVca ms.dc ms.mem`;
val dmvalt_def = Define `dmvalt ms = MValt ms.dc ms.mem`;
val imv_def = Define `imv ms = MVca ms.ic ms.mem`;

(* transition system *)

val ms_dupd_def = Define `
ms_dupd ms (ca,m) = ms with <| dc := ca; mem := m |>
`;

val ms_dupd_rw = store_thm("ms_dupd_rw", ``
!ms ca m. ((ms_dupd ms (ca,m)).dc = ca)
       /\ ((ms_dupd ms (ca,m)).ic = ms.ic)
       /\ ((ms_dupd ms (ca,m)).mem = m)
``,
  RW_TAC std_ss [ms_dupd_def]
);

val ms_iupd_def = Define `
ms_iupd ms (ca,m) = ms with <| ic := ca |>
`;

val ms_iupd_rw = store_thm("ms_iupd_rw", ``
!ms ca m. ((ms_iupd ms (ca,m)).dc = ms.dc)
       /\ ((ms_iupd ms (ca,m)).ic = ca)
       /\ ((ms_iupd ms (ca,m)).mem = ms.mem)
``,
  RW_TAC std_ss [ms_iupd_def]
);

val ms_mupd_def = Define `
ms_mupd ms m = ms with <| mem := m |>
`;

val ms_mupd_rw = store_thm("ms_mupd_rw", ``
!ms ca m. ((ms_mupd ms m).dc = ms.dc)
       /\ ((ms_mupd ms m).ic = ms.ic)
       /\ ((ms_mupd ms m).mem = m)
``,
  RW_TAC std_ss [ms_mupd_def]
);

val msca_trans_def = Define `
   (msca_trans ms (DREQ dop) = ms_dupd ms (mtfca (ms.dc, ms.mem) dop))
/\ (msca_trans ms (FREQ pa) = ms_iupd ms (mtfca (ms.ic, ms.mem) (RD pa T)))
/\ (msca_trans ms NOREQ = ms)
`;

val mtf_pat = ``(x,y) = mtfca (a,b) c``; 

val mtf_pat2 = ``mtfca (a,b) c = (x,y)``; 

fun ASM_SYM_TAC pat = PAT_X_ASSUM pat (fn thm => ASSUME_TAC (SYM thm));


val msca_DREQ_lem = store_thm("msca_DREQ_lem", ``
!ms dop ms'. (ms' = msca_trans ms (DREQ dop)) 
    ==>
?ca' m'. ((ca',m') = mtfca (ms.dc, ms.mem) dop) 
      /\ (ms'.dc = ca')
      /\ (ms'.ic = ms.ic)
      /\ (ms'.mem = m')
``,
  REWRITE_TAC [msca_trans_def] >> 
  REPEAT STRIP_TAC >>
  `?ca' m'. (ca',m') = mtfca (ms.dc, ms.mem) dop` by (
      METIS_TAC [pairTheory.pair_CASES]
  ) >>
  EXISTS_TAC ``ca':cache_state`` >>
  EXISTS_TAC ``m':mem_state`` >>
  ASM_SYM_TAC mtf_pat >>
  ASM_REWRITE_TAC [ms_dupd_rw]
);

(* deriveability obligations *)

val ms_cacheable_other_oblg = store_thm("ms_cacheable_other_oblg", ``
!ms dop ms' pa. CA dop /\ (ms' = msca_trans ms (DREQ dop)) /\ (pa <> PA dop)
             /\ (dw ms' pa <> dw ms pa) ==> 
    ~dhit ms' pa
``,
  REPEAT GEN_TAC >>
  STRIP_TAC >>
  IMP_RES_TAC msca_DREQ_lem >>
  FULL_SIMP_TAC std_ss [dw_def, dhit_def] >>
  IMP_RES_TAC ca_cacheable_other_lem
);


(*********** finish ************)

val _ = export_theory();
