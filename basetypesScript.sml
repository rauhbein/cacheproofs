(********** Loading *************)

open HolKernel boolLib bossLib;
open wordsLib blastLib; 

val _ = new_theory "basetypes";

val _ = Parse.type_abbrev("byte", ``:bool[8]``);
val _ = Parse.type_abbrev("word", ``:bool[32]``);

val _ = Datatype `padr = PADR bool[30]`;
val _ = Datatype `vadr = VADR bool[30]`;

val _ = Datatype `mode = PRIV | USER`;

val _ = Datatype `acc = R | W`;

val _ = Parse.type_abbrev("mem_view", ``:bool -> padr -> word``);

val _ = Datatype `dop = RD padr bool | WT padr word bool | CL padr`;

val rd_def = Define `
   (rd (RD pa c) = T)
/\ (rd _ = F)
`;

val wt_def = Define `
   (wt (WT pa w c) = T)
/\ (wt _ = F)
`;

val cl_def = Define `
   (cl (CL pa) = T)
/\ (cl _ = F)
`;

val PA_def = Define `
   (PA (RD pa c) = pa)
/\ (PA (WT pa w c) = pa)
/\ (PA (CL pa) = pa)
`;

val VAL_def = Define `VAL (WT pa w c) = w`;

val CA_def = Define `
   (CA (RD pa c) = c)
/\ (CA (WT pa w c) = c)
/\ (CA (CL pa) = T)
`;

(* some useful lemmas *)

val dop_cases_lem = store_thm("dop_cases_lem", ``
!dop. rd dop \/ wt dop \/ cl dop
``,
  Cases >> ( RW_TAC std_ss [rd_def, wt_def, cl_def] )
);

val dop_cases_lem2 = store_thm("dop_cases_lem2", ``
!dop. rd dop /\ ~wt dop /\ ~cl dop
   \/ ~rd dop /\ wt dop /\ ~cl dop
   \/ ~rd dop /\ ~wt dop /\ cl dop
``,
  Cases >> ( RW_TAC std_ss [rd_def, wt_def, cl_def] )
);

val not_rd_lem = store_thm("not_rd_lem", ``
!dop. ~rd dop <=> (wt dop \/ cl dop)
``,
  Cases >> (
      RW_TAC std_ss [wt_def, rd_def, cl_def]
  )
);

val not_wt_lem = store_thm("not_wt_lem", ``
!dop. ~wt dop <=> (rd dop \/ cl dop)
``,
  Cases >> (
      RW_TAC std_ss [wt_def, rd_def, cl_def]
  )
);

val not_cl_lem = store_thm("not_cl_lem", ``
!dop. ~cl dop <=> (rd dop \/ wt dop)
``,
  Cases >> (
      RW_TAC std_ss [wt_def, rd_def, cl_def]
  )
);

val rd_lem = store_thm("rd_lem", ``
!dop. rd dop <=> ?pa c. dop = RD pa c
``,
  Cases >> (
      METIS_TAC [rd_def]
  )
);

val wt_lem = store_thm("wt_lem", ``
!dop. wt dop <=> ?pa w c. dop = WT pa w c
``,
  Cases >> (
      METIS_TAC [wt_def]
  )
);

val cl_lem = store_thm("cl_lem", ``
!dop. cl dop <=> ?pa. dop = CL pa
``,
  Cases >> (
      METIS_TAC [cl_def]
  )
);

val not_CA_lem = store_thm("not_CA_lem", ``
!dop. ~CA dop <=> (?pa. dop = RD pa F) \/ (?pa w. dop = WT pa w F)
``,
  Cases >> (
      RW_TAC std_ss [CA_def]
  )
);

val CA_lem = store_thm("CA_lem", ``
!dop. CA dop <=> (?pa. dop = RD pa T) \/ (?pa w. dop = WT pa w T) 
			              \/ (?pa. dop = CL pa)
``,
  Cases >> (
      RW_TAC std_ss [CA_def]
  )
);

val cl_CA_lem = store_thm("cl_CA_lem", ``
!dop. cl dop ==> CA dop
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [cl_lem, CA_def]
);

val rd_CA_lem = store_thm("rd_CA_lem", ``
!dop. rd dop /\ CA dop ==> ?pa. dop = RD pa T
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [rd_lem] >>
  EXISTS_TAC ``pa:padr`` >>
  RW_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [CA_def]
);

val wt_CA_lem = store_thm("wt_CA_lem", ``
!dop. wt dop /\ CA dop ==> ?pa v. dop = WT pa v T
``,
  REPEAT STRIP_TAC >>
  FULL_SIMP_TAC std_ss [wt_lem] >>
  EXISTS_TAC ``pa:padr`` >>
  RW_TAC std_ss [] >>
  FULL_SIMP_TAC std_ss [CA_def]
);

(* core requests to memory *)

val _ = Datatype `corereq = DREQ dop | FREQ padr | NOREQ`;

val Adr_def = Define `
   (Adr (DREQ dop) = PA dop)
/\ (Adr (FREQ pa) = pa)
`;

val Freq_def = Define `
   (Freq (FREQ pa) = T)
/\ (Freq _ = F)
`;

val Dreq_def = Define `
   (Dreq (DREQ dop) = T)
/\ (Dreq _ = F)
`;

val Rreq_def = Define `
   (Rreq (DREQ dop) = rd dop)
/\ (Rreq _ = F)
`;

val Wreq_def = Define `
   (Wreq (DREQ dop) = wt dop)
/\ (Wreq _ = F)
`;

val Creq_def = Define `
   (Creq (DREQ dop) = cl dop)
/\ (Creq _ = F)
`;

val Freq_lem = store_thm("Freq_lem", ``
!req. Freq req ==> ?pa. req = FREQ pa
``,
  Cases >> (
      RW_TAC std_ss [Freq_def]
  )
);

val Dreq_lem = store_thm("Dreq_lem", ``
!req. Dreq req ==> ?dop. req = DREQ dop
``,
  Cases >> (
      RW_TAC std_ss [Dreq_def]
  )
);

val not_Wreq_lem = store_thm("not_Wreq_lem", ``
!req. (Freq req \/ Rreq req \/ Creq req \/ (req = NOREQ)) ==> ~Wreq req
``,
  Cases >> (
      RW_TAC std_ss [Freq_def, Rreq_def, Wreq_def, Creq_def] >>
      METIS_TAC [dop_cases_lem2]
  )
);

val req_cases_lem = store_thm("req_cases_lem", ``
!req. Freq req /\ ~Dreq req /\ req <> NOREQ
   \/ ~Freq req /\ Dreq req /\ req <> NOREQ
   \/ ~Freq req /\ ~Dreq req /\ (req = NOREQ)
``,
  Cases >> (
      RW_TAC std_ss [Freq_def, Dreq_def]
  )
);

val Dreq_cases_lem = store_thm("Dreq_cases_lem", ``
!req. Dreq req ==> 
      Rreq req /\ ~Wreq req /\ ~Creq req
   \/ ~Rreq req /\ Wreq req /\ ~Creq req
   \/ ~Rreq req /\ ~Wreq req /\ Creq req
``,
  GEN_TAC >> STRIP_TAC >>
  IMP_RES_TAC Dreq_lem >>
  ASSUME_TAC ( SPEC ``dop:dop`` dop_cases_lem2 ) >>
  RW_TAC std_ss [Rreq_def, Wreq_def, Creq_def]
);


(*********** finish ************)

val _ = export_theory();
