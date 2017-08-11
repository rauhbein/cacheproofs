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

val not_wt_lem = store_thm("not_wt_lem", ``
!dop. ~wt dop <=> (rd dop \/ cl dop)
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

(*********** finish ************)

val _ = export_theory();
