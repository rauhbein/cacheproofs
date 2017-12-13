val ca_def = 
  Define `ca i t dc =
    ((dc i).sl t)`
;

val ccnt_def =
  Define `ccnt va pa dc state =
  let (i, t, wi) = lineSpec(va, pa) state in
    (THE((dc i).sl t)).value`
;

val ccntw_def =
  Define `ccntw va pa dc state =
  let (i, t, wi) = lineSpec(va, pa) state in
    CellRead(i,t,wi, dc)`
;


val mllu_def =
  Define `mllu i t pm dc h n state = 
    LineFill(h, i, t, pm, dc, n) state`
;

val mlwb_def =
  Define `mlwb va pa pm dc state =
    let (i,t,wi) = lineSpec(va, pa) state in
     WriteBack(i, t, wi, pm, THE ((dc i).sl t)) state`
;

val mv_def = 
    Define `mv (cbl:bool) (pm:word48->word8) (dc:word48->CSET) f g  =
    case cbl of
    T => f(pm, dc):word48->word8
  | F => g(pm, dc)`
;

val _ = Datatype `dop = RD word64#word48#bool | WT word64#word48#wrTyp#bool | CL word64#word48`;

val rd_def = Define `
   (rd (RD (va,pa,c)) = T)
/\ (rd _ = F)
`;

val wt_def = Define `
   (wt (WT (va,pa,w,c)) = T)
/\ (wt _ = F)
`;
val VAL_def = Define `VAL (WT (va,pa,w, c)) = w`;


val cl_def = Define `
   (cl (CL (va,pa)) = T)
/\ (cl _ = F)
`;

val ADD_def = Define`
   ADD dop = case dop of
     (RD (va,pa,c))   => (va,pa)
   | (WT (va,pa,w,c)) => (va,pa)
   | (CL (va,pa))     => (va,pa)`;

val _ = new_constant("dummy", ``:bitstring``);

val fmem_def =
  Define `fmem ((pm:word48->word8), (dc:word48->CSET)) = 
    pm
`;
val _ = new_constant ("fcm", ``:(word48 -> word8) # (word48 -> CSET) -> word48 -> word8``);

val ctf'_def = 
  Define `ctf' pm dc state dop =
      let f = (mv T pm dc fmem fcm)  in 
      case dop of
     (RD (va,pa,c))      => CacheRead(va, pa, f,dc) state
   | (WT (va,pa,data,c)) => 
     let (cache, mem) = CacheWrite(va,pa,data,f,dc) state in (cache, mem, dummy)
   | (CL (va,pa))        =>
     let (cache, mem) = CacheInvalidateByAdr(va,pa,f,dc) state in (cache, mem, dummy)`;







