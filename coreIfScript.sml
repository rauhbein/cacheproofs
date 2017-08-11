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
val CV_def = Define `
   (CV c (mv:mem_view) (REG r) = c.reg r)
/\ (CV c mv (COREG r) = c.coreg r)
/\ (CV c mv (PSRS r) = c.psrs r)
/\ (CV c mv (MEM pa) = mv T pa)
`;

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

new_constant("CR", ``:core_state -> mem_view -> resource set``);

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
!c mv pa m ac. (?va ca. Mmu_(c,mv,va,m,ac) = SOME(pa,ca)) <=>
               Mon(c,mv,MEM pa,m,ac)
``,
  EXISTS_TAC ``dummyMon`` >>
  RW_TAC std_ss [dummyMon_def]
);  

val Mon_spec = new_specification ("Mon_spec",
  ["Mon_"], Mon_exists);

(* transition relation *)

val _ = new_constant("core_trans", 
 		     ``:core_state # mem_view # mode # dop # core_state -> bool``
);

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

val Mon_oblg = store_thm("MD_oblg", ``
!c mv pa m ac.
  (?va ca. Mmu_ (c,mv,va,m,ac) = SOME (pa,ca)) <=> Mon_ (c,mv,MEM pa,m,ac)
``,
  METIS_TAC [Mon_spec]
);


(*********** finish ************)

val _ = export_theory();



