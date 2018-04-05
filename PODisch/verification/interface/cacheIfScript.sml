open HolKernel boolLib bossLib;
open cacheTheory cutilsLib;

val _ = new_theory "cacheIf";
     
val ca_def =  
 Define`ca i t dc = (((dc i).sl) t)`
;


val lcnt_def =
    Define `lcnt i t dc =
      (THE((dc i).sl t)).value`
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

val fmem_def =
  Define `fmem ((pm:word48->word8), (dc:word48->'a)) = 
    pm
`;
val _ = new_constant ("fcm", ``:(word48 -> word8) # (word48 -> 'a) -> word48 -> word8``);
val _ = new_constant ("dc2", ``:(word48 -> 'a)``);


val mv_def = 
    Define `mv (cbl:bool) (pm:word48->word8) dc f g  =
    case cbl of
    T => f(pm, dc):word48->word8
  | F => g(pm, dc)`
;

val read32_def = 
    Define `read32(pa, f, g) =
    g(pa, f)`
;

val lv_def =
    Define `lv i t pm dc h n state = 
      let f = (mv T pm dc2 (fmem:(word48->word8)#(word48->CSET)-> (word48 -> word8)) fcm) in 
      LineFill(h, i, t, f, dc, n) state`
;

val lw_def =
   Define `lw va pa l state =
     let (i,t,wi) = lineSpec(va, pa) state in
     l(n2w wi)`
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

val cl_def = Define `
   (cl (CL (va,pa)) = T)
/\ (cl _ = F)
`;

val ADD_def = Define`
   ADD dop = case dop of
     (RD (va,pa,c))   => (va,pa)
   | (WT (va,pa,w,c)) => (va,pa)
   | (CL (va,pa))     => (va,pa)`;

val VAL_def = Define `VAL (WT (va,pa,w, c)) = w`;

val ctf_def = 
  Define `ctf pm dc state dop =
   let f = (mv T pm dc2 (fmem:(word48->word8)#(word48->CSET)-> (word48 -> word8)) fcm)  in 
   case dop of

   (CL (va,pa)) =>
     let (i, t, _) = lineSpec(va, pa) state in
     let (cache, mem) = CacheInvalidateByAdr(va,pa,f,dc) state in 
     let (tg, il) = SND(HD (cache i).hist)  in    
     if LineDirty(il,n2w(tg):word48, dc) 
     then (cache, (il, SOME ((n2w tg):word48), (ca il (n2w(tg)) dc)))
     else (cache, (il, NONE, NONE))

  | (WT (va,pa,data,c)) =>
     let (i, t, _) = lineSpec(va, pa) state         in
     let (cache, mem) = CacheWrite(va,pa,data,f,dc) state in
     let (tg, il) = SND(HD(TL (TL (cache i).hist))) in
     if ((~Hit(va, pa, dc) state) /\ (EP ((dc i).hist,t,dc) <> NONE))
     then if LineDirty(il,n2w(tg):word48, dc)
          then (cache,  (il, SOME (n2w tg), (ca il (n2w(tg)) dc)))
  	  else (cache,  (il, NONE, NONE))
     else (cache, (il, NONE, NONE))

  | (RD (va,pa,c)) =>
     let (i, t, _) = lineSpec(va, pa) state         in
     let (cache, mem, c) = CacheRead(va,pa,f,dc) state in
     let (tg, il) = SND(HD(TL (TL (cache i).hist))) in
     if ((~Hit(va, pa, dc) state) /\ (EP ((dc i).hist,t,dc) <> NONE))
     then if LineDirty(il,n2w(tg):word48, dc)
          then (cache, (il, SOME (n2w tg), (ca il (n2w(tg)) dc)))
  	  else (cache,  (il, NONE, NONE))
     else (cache,  (il, NONE, NONE))`

;

val _ = export_theory();




