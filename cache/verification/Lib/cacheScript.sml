HOL_Interactive.toggle_quietdec();
open HolKernel boolLib bossLib Parse;
open wordsTheory wordsLib wordsSyntax;
open mmu_utilsLib;
HOL_Interactive.toggle_quietdec();

(* val _ = new_theory "Cache" *)


val writeMem_tm     = prim_mk_const {Name="write_mem",   Thy="dharma8"}
val dest_writeMem   = dest_monop writeMem_tm (ERR "dest_writeMem" "")
val is_writeMem     = can dest_writeMem

val readMem_tm      = prim_mk_const {Name="read_mem",   Thy="dharma8"}
val dest_readMem    = dest_monop readMem_tm (ERR "dest_readMem" "")
val is_readMem      = can dest_readMem


val readReq_tm     = prim_mk_const {Name="readReq",   Thy="dharma8"}
val dest_readReq    = dest_monop readReq_tm (ERR "dest_readReq" "")
val is_readReq      = can dest_readReq

val writeReq_tm     = prim_mk_const {Name="writeReq",   Thy="dharma8"}
val dest_writeReq   = dest_monop writeReq_tm (ERR "dest_writeReq" "")
val is_writeReq     = can dest_writeReq

val writeBackLine_tm       = prim_mk_const {Name="WriteBackLine",   Thy="dharma8"}
val dest_writeBackLine     = dest_monop writeBackLine_tm (ERR "dest_writeBackLine" "")
val is_writeBackLine       = can dest_writeBackLine

val evict_tm       = prim_mk_const {Name="Evict",   Thy="dharma8"}
val dest_evict     = dest_monop evict_tm (ERR "dest_evict" "")
val is_evict       = can dest_evict

val lineFill_tm       = prim_mk_const {Name="LineFill",   Thy="dharma8"}
val dest_lineFill     = dest_monop lineFill_tm (ERR "dest_lineFill" "")
val is_lineFill       = can dest_lineFill

val Fill_tm       = prim_mk_const {Name="Fill",   Thy="dharma8"}
val dest_Fill     = dest_monop Fill_tm (ERR "dest_Fill" "")
val is_Fill       = can dest_Fill


val cacheRead_tm       = prim_mk_const {Name="CacheRead",   Thy="dharma8"}
val dest_cacheRead     = dest_monop cacheRead_tm (ERR "dest_cacheRead" "")
val is_cacheRead       = can dest_cacheRead

val cacheWrite_tm       = prim_mk_const {Name="CacheWrite",   Thy="dharma8"}
val dest_cacheWrite     = dest_monop cacheWrite_tm (ERR "dest_cacheWrite" "")
val is_cacheWrite       = can dest_cacheWrite

val linespec_tm        = prim_mk_const {Name="lineSpec",   Thy="dharma8"}
val dest_linespec      = dest_monop linespec_tm (ERR "dest_linespec" "")
val is_linespec        = can dest_linespec

(* --------------------------------------------------------------------------------------------- *)
val abr_lineSpec_tac_dubl =
 (fn (asl, g) => let val a::b::_ = rm_dup (find_terms ifilter g)
		     val c::d::_ = rm_dup (find_terms tfilter g)
		in (Q.ABBREV_TAC `i'= ^a`  >> Q.ABBREV_TAC `t' = (FST ^c)` >> Q.ABBREV_TAC `wi' = (SND ^c)`
                 \\ Q.ABBREV_TAC `i = ^b`  >> Q.ABBREV_TAC `t = (FST ^d)`  >> Q.ABBREV_TAC `wi = (SND ^d)`)
 (asl ,g) end);


val abr_lineSpec_tac_sgl =
 (fn (asl, g) => let val a::_ = rm_dup (find_terms ifilter g)  val c::_ = rm_dup (find_terms tfilter g)
		in (Q.ABBREV_TAC `i' = ^a`  >> Q.ABBREV_TAC `t' = (FST ^c)` >> Q.ABBREV_TAC `wi' = (SND ^c)`)
 (asl ,g) end);


(* To prove that line  size is lee that 2 ** 15 *)
fun line_size_lt_dimword15 nl =
      `2 ** ^nl ≤ 32769` by (all_tac
    \\ assume_tac(Drule.ISPECL[``(state :dharma8_state).DC.ctr.DminLine``](w2n_lt) |> SIMP_RULE(srw_ss())[])
    \\ `w2n state.DC.ctr.DminLine <= 15`  by decide_tac
    \\ `!a b. a <= b ==> 2**a <= 2**b` by FULL_SIMP_TAC(arith_ss)[]
    \\ REABBREV_TAC
    \\ qpat_assum `!a b. P` (qspecl_then [`^nl`, `15n`] assume_tac)
    \\ res_tac
    \\ `(2 ** ^nl ≤ 2 ** 15) ==> (2 ** ^nl < (2 ** 15) + 1)` by FULL_SIMP_TAC (bool_ss)[]
    >|[(qspecl_then [`2 ** ^nl`, `2 ** 15`] assume_tac) arithmeticTheory.LE_LT1
    \\ res_tac
    \\ FULL_SIMP_TAC (arith_ss)[], all_tac]
    \\ fs[]);

val set_size_lt_48 = 
    SUBGOAL_THEN ``w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) < 48`` (fn thm => assume_tac thm)
    >- (xfs[word_log2_def]
       \\ (qspecl_then [`state.DC.ccsidr.NumSets `] assume_tac) (INST_TYPE [alpha |-> ``:15``]LOG2_w2n_lt)
       \\ `(state.DC.ccsidr.NumSets ≥ 1w) ==> (state.DC.ccsidr.NumSets + 1w ≠ 0w)` by blastLib.BBLAST_TAC
       \\ res_tac
       \\ rfs[invariant_cache_def]);

(* --------------------------------------------------------------------------------------------- *)

val write_mem32_def = Define `
write_mem32 (add:bool[48], (pm:(word48->word8)), value:bool[32]) =
  let pm = (add =+ ((7 >< 0) value):word8)      pm in
  let pm = (add+1w =+ ((15 >< 8) value):word8)  pm in
  let pm = (add+2w =+ ((23 >< 16) value):word8) pm in
  let pm = (add+3w =+ ((31 >< 24) value):word8)pm in
      pm
`;

val write_read_thm = Q.store_thm("write_read_thm", `
 !a v m. 
   (let m' = write_mem32(a,m,v) in
      (read_mem32(a,m') = w2v v))`,
       rpt GEN_TAC
    \\ EVAL_TAC
    \\ lfs[read_mem32_def, combinTheory.UPDATE_def]
    \\ rpt (CASE_TAC >- FIRST_ASSUM (fn thm => let val trm = concl thm in `~^trm` by blastLib.BBLAST_TAC end))
    \\ fs[w2v_def]
    \\ blastLib.BBLAST_PROVE_TAC
);


val write_read_unch_thm = Q.store_thm("write_read_unch_thm", `
  !a a' v m m'.
  (a' + 3w <+ a /\ a' + 3w >=+ 3w /\ a + 3w >=+ 3w) \/
  (a' >+ a + 3w /\ a' + 3w >=+ 3w /\ a + 3w >=+ 3w) ==>
  (m' = write_mem32(a,m,v)) ==>
  (read_mem32(a',m') = read_mem32(a',m))`,
       rpt GEN_TAC
    \\ EVAL_TAC
    \\ rw[read_mem32_def]
    \\ fs[combinTheory.UPDATE_def]
    \\ EVERY[rpt (schneiderUtils.UNDISCH_ALL_TAC >> CASE_TAC
       >- (schneiderUtils.UNDISCH_ALL_TAC >> blastLib.BBLAST_PROVE_TAC))
   ]);

(* --------------------------------------------------------------------------------------------- *)
local 
 fun termExt trm res n =  
    case n of 0 => res 
    | _  => let val (trm, trm') = dest_comb  trm 
	    in
		termExt (trm') [trm] (n -1)
	    end
 fun SYM_ASM_TAC pat =  PAT_ASSUM pat (fn thm => let val cnl = concl thm 
				   val (a1,a2) = dest_eq cnl
                                   val new_thm = SPECL [a1,a2] (Thm.INST_TYPE[alpha |-> (type_of a1)] EQ_SYM)
				   val (_, rh)= (dest_imp o concl) new_thm
				in
				   (ASSUME_TAC  thm)
                                   THEN (ASSUME_TAC new_thm)
				   THEN `^rh` by METIS_TAC []
				   THEN FULL_SIMP_TAC (srw_ss()) []
				end)
fun wt_mem_eq_tac a b n= 
   (fn (asl, w) =>
        let val (a1,a2) = dest_eq w
	val l = (snd o dest_comb o hd) (termExt a1 [] n)
	val r = (snd o dest_comb o hd) (termExt a2 [] n)
		in (SUBGOAL_THEN ``^r = ^l`` (fn thm => ASSUME_TAC thm)) (asl, w)  end)
  \\ ASSUME_SPECL_TAC [``^a``, ``^b``, `` (w2v (data:word32))``] (INST_TYPE [alpha |-> ``:32``, beta |-> ``:8``] 
     extract_v2w)
  \\ `LENGTH (w2v (data :word32)) ≤ dimindex ((:32) :32 itself)` by (blastLib.BBLAST_TAC
          \\ ASSUME_SPEC_TAC ``data:word32`` (INST_TYPE [alpha |-> ``:32`` ]w2v_def)
          \\ fs[])
  
  \\ fs[]
  \\ SYM_ASM_TAC ``a = b``
  \\ fs []
  \\ blastLib.BBLAST_TAC
in 
 val write_mem32_thm = Q.store_thm("write_mem32_thm",
  `! (pa:word48) (data:word32)  (mc:MEM_CONFIG) (pm:(word48->word8)).
   let (mc', pm1) = write_mem(0w:word32, pa, w2v(data), mc, pm) in 
   let pm2 = write_mem32(pa, pm, data) in 
       pm1 = pm2`,

   rw_tac (srw_ss())[]
  \\ fs [write_mem32_def , write_mem_def]
  \\ (NTAC 4 (fs[Once state_transformerTheory.FOR_def, state_transformerTheory.BIND_DEF]))
  \\ rw_tac (srw_ss())[]
  \\ unabbrev_all_tac
  \\ fs[]
  \\ wt_mem_eq_tac ``(31:num)`` ``(24:num)`` 1
  \\ wt_mem_eq_tac ``(23:num)`` ``(16:num)`` 2
  \\ wt_mem_eq_tac ``(15:num)`` ``(8:num)`` 3
  \\ wt_mem_eq_tac ``(7:num)`` ``(0:num)`` 4
)


val write_mem32_thm2 = Q.store_thm("write_mem32_thm2",
 `! (size:word32) (pa:word48) (data:bitstring)  (mc:MEM_CONFIG) (pm:(word48->word8)).
   let (mc', pm1) = write_mem(size, pa, data, mc, pm) in 
   let pm2 = write_mem32(pa, pm, v2w(data):(word32)) in
    (LENGTH data ≤ dimindex (:32)) ==> (pm1 = pm2)`,

       rw_tac (srw_ss())[]
    \\ fs [write_mem32_def , write_mem_def]
    \\ (NTAC 4 (fs [Once state_transformerTheory.FOR_def, state_transformerTheory.BIND_DEF]))
    \\ xrw[]
    \\ unabbrev_all_tac
    \\ fs[combinTheory.UPDATE_def]
    \\ MAP_EVERY (fn (a,b) => assume_tac(extract_v2w
	|> INST_TYPE [alpha |-> ``:32``, beta |-> ``:8``] 
	|> Q.ISPECL[`^a`,`^b`,`data:bitstring`]
     )) [(``31n``,``24n``), (``23n``, ``16n``), (``15n``, ``8n``), (``7n``, ``0n``)]
    \\ rfs[] 
)
end;
    
(* --------------------------------------------------------------------------------------------- *)
val read_mem32_thm = Q.store_thm("read_mem32_thm",
 `!pa:word48 (pm:(word48->word8)). read_mem(0w:word32, pa, pm) = read_mem32(pa, pm)`,

     fs [read_mem32_def, read_mem_def]
  \\ EVAL_TAC
  \\ blastLib.BBLAST_TAC);

(* --------------------------------------------------------------------------------------------- *)
val wrtBck_dirtybit_thm = Q.store_thm("wrtBck_dirty_thm",
    `!i:(48 word) t:(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) (n:num) (state:dharma8_state). 
    (let (dc', pm') =  WriteBackLine(i, t, pm, dc, n) state in 
     ((n <= dimword(:15)) ==>
       (!wi:num. (wi <= n) ==> (~LineDirty(i, t,  dc')) )))`,
      
        lrw[]
     \\ lfs [WriteBackLine_def, Once LET_DEF, FOR_FOLDL]
     \\ (EVAL_TAC \\ fs[LET_DEF, LineDirty_def, WriteBack_def, combinTheory.UPDATE_def])
);

(* --------------------------------------------------------------------------------------------- *)
val lt_mod_thm = Q.store_thm("lt_mod_thm",
 `!a b c d. ((a < b) /\ (b <= c) /\ (c < d)) ==> ((a MOD d) < (b MOD d))`,
     fs []);


val adr_thm = Q.prove(
 `!(a:word48) (b:word48) (c:word48) (d:word48) (n:num) (m:num). 
   let bmM = ((0xffffffffffffw:word48) >>> (n + m)) in
   let bmL = (((0xffffffffffffw:word48) << (48 - (n + m))) >>> (48 - n)) in
  ((n < 48) /\ (m < (48 - n))) ==>  
  ((a && bmM = a) /\ (b && bmL = b)) ==>
  ((c && bmM = c) /\ (d && bmL = d)) ==>   
  ((a <> c) ==> (((a << (n+m)) !! (b << m) ) <>  ((c << (n+m)) !! (d << m)))) /\
  ((d <> b) ==> (((a << (n+m)) !! (b << m) ) <>  ((c << (n+m)) !! (d << m)))) /\
  ((((a << (n+m)) !! (b << m) ) =  ((c << (n+m)) !! (d << m))) ==> ((a = c) /\ (b = d)))`, cheat);

 (* ntac 4 strip_tac *)
 (*  \\ ntac 48 (FIRST[Cases_on`n`, Cases_on`n'`] *)
 (*  >- (ntac 48(Induct_on `m` *)
 (*  THENL[fs[] \\ blastLib.BBLAST_PROVE_TAC, fs[] \\ PAT_ASSUM ``a``(fn thm => all_tac)])) *)
 (*  \\ fs[]) *)
(* ); *)


val adr_neq2_thm = Q.store_thm("adr_neq2_thm",
  `!(a:word48) (b:word48) (c:word48) (n:num). 
   let bmM = ((0xffffffffffffw:word48) >>> n) in
   let bmL = ~((0xffffffffffffw:word48) >>> n << n) in
  ((n < 48)) ==>  
  ((a && bmM = a) /\ (b && bmL = b) /\ (c && bmL = c)) ==>
  (b <> c) ==>   
  (((a << n) !! b) <> ((a << n) !! c))`, cheat);

(*   ntac 3 strip_tac *)
(*   \\ ntac 48 (Induct_on `n` *)
(*    THENL[fs[] \\ blastLib.BBLAST_PROVE_TAC,   *)
(* 	 fs[] \\ PAT_ASSUM ``a``(fn thm => all_tac)]) *)
(* ); *)


val numeral_tac = (
         ASSUME_TAC((SPECL[``(w2w((n2w wi :48 word) ) : word48)``, 
                         ``(w2w ((n2w ((n :num) + (1 :num)) :48 word)) :word48)``]
              (INST_TYPE [alpha |-> ``:48``](GSYM WORD_LO)) ) |> SIMP_RULE (srw_ss()) [w2n_w2w])

      \\ ASSUME_TAC(SPECL[``wi:num``, ``(n:num)+1``, ``dimword(:16)``, ``dimword(:48)``]lt_mod_thm)
      \\ rfs []
      \\ PAT_ASSUM``a <+ b``(fn thm => let val asm = concl thm  val ls = (snd o strip_comb) asm
			     val t1 = (snd o dest_comb) (hd ls )val t2 = (snd o dest_comb) (hd (tl ls) )
			     in
			      assume_tac(thm)  \\ `^asm ==> ^t2 <> ^t1` by fs[]
			     end
			    ) 

      \\ res_tac
      \\ `((n2w ((n :num) + (1 :num)) :48 word) ≠ (n2w (wi :num) :48 word)) /\ (wi < dimword(:15)) /\ (n+1 <= dimword(:15)) ==>
           ((n2w ((n :num) + (1 :num)) :48 word) << 2) <> ((n2w (wi :num) :48 word) << 2)` by 
         (fs [word_lsl_n2w] \\ xrw [] \\ fs[])
      \\ rfs[]
      \\ `wi < 32768` by decide_tac
      \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`i`, `t`, `wi`, `ln' + 2n`, `sn`, `state`] ASSUME_TAC)
      \\ rpt (WEAKEN_TAC is_forall)
      \\ xfs[invariant_cache_def]
      \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`i`, `t`, `n+1`, `ln' + 2n`, `sn`, `state`] ASSUME_TAC)
      \\ rpt (WEAKEN_TAC is_forall)
      \\ xfs[LET_DEF]
      \\ assume_tac(adr_neq2_thm |> spec_let_elim [`(i ‖ t ≪ sn)`, `n2w (n + 1) ≪ 2`, `n2w wi ≪ 2`, `(ln' + 2)`])
      \\ assume_tac(SPECL[``(state :dharma8_state).DC.ctr.DminLine``](INST_TYPE[alpha |-> ``:4``]w2n_lt) |> SIMP_RULE(srw_ss())[])
      \\ `ln' + 2 < 48` by decide_tac
      \\ rfs[]
);

val wrtBck_memory_thm = Q.store_thm("wrtBck_memory_thm",
 `!i:(48 word) t:(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state) (n:num).
    (let (dc', pm') =  WriteBackLine(i, t, pm, dc, n) state in
     let sn = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
     let ln = (w2n state.DC.ctr.DminLine) in
     (n <= dimword(:15) ==> (!wi:num. wi <= n ==>
          let pa = ((t << (sn + ln + 2)) !! (i << (ln + 2)) !! (n2w(wi):(48 word) << 2)) in
           (invariant_cache) ==>
	   (CellRead(i, t, wi, dc') = v2w(read_mem32(pa, pm')))
     )))`,

       xrw []
    \\ fs [WriteBackLine_def, CellRead_def ,FOR_FOLDL, combinTheory.UPDATE_def]
    \\ lrw[]

    >- (Induct_on `n`
     >-(EVAL_TAC
        \\ rfs[read_mem32_def, combinTheory.UPDATE_def]
	\\ strip_tac
  	\\ ntac 3 ((fn (asl, g) =>
                let val (t,_,_) = (dest_cond o repeat (snd  o wordsSyntax.dest_word_concat) o snd o dest_eq) g in
	        `~^t` by  (fs [] \\ blastLib.BBLAST_TAC) end (asl, g))
	        \\ fs [])
	\\ blastLib.BBLAST_TAC)
      (* Inductive step *)
      \\ rpt strip_tac
      \\ `n ≤ 32768` by decide_tac
      \\ fs[DECIDE``SUC n = n + 1``]
      \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])

      \\ lfs []
      \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]]
      \\ abr_tac listSyntax.is_foldl
      \\ THM_KEEP_TAC ``invariant_cache`` (xfs [invariant_cache_def])
      \\ simp[CellRead_def, read_mem32_def]
      \\ qpat_assum `∀s:dharma8_state s':dharma8_state. P` (qspecl_then[`(SND (SND (SND (SND abr))))`,`state`] assume_tac)
      \\ xfs[]
      \\ Cases_on `wi ≤ n`
      THENL[xfs[]
           \\ simp[combinTheory.UPDATE_def]
           \\ (fn (asl, g) => let val t = (find_term is_eq o snd o dest_eq)g in (Cases_on`^t`) (asl, g)end)
	   THENL[xfs [Abbr`pa`]
	     \\ ntac 3 ((fn (asl, g) => let val t = (find_terms is_eq o snd o dest_eq)g
			 in (MAP_FIRST (fn z =>  `~^z` by blastLib.BBLAST_TAC) t) (asl, g) end)
		        \\ xfs[])
	     \\ (ASSUME_TAC (DECIDE ``((wi:num) ≤ n + 1) ==> ((wi< n + 1)\/ (wi = n + 1))``)
             \\ res_tac THENL[numeral_tac, fs[]]) ,
	   xfs [Abbr`pa`]
	 \\ (fn (asl, g) => let val t = (find_terms is_eq o snd o dest_eq)g
		in (MAP_EVERY (fn z =>  `~^z` by blastLib.BBLAST_TAC) t) (asl, g) end)
	 \\ xfs [read_mem32_def]],
         `(wi = n + 1)` by decide_tac 
	 \\ simp[WriteBack_def, combinTheory.UPDATE_def]
	 \\ xfs[Abbr`pa`]
         \\ (fn (asl, g) => let val t = (find_terms is_eq o snd o dest_eq)g
	      	in (MAP_EVERY (fn z =>  `~^z` by blastLib.BBLAST_TAC) t) (asl, g) end)
	 \\ rfs[]
	 \\ blastLib.BBLAST_TAC])

       \\ assume_tac (coherency_axiom |> spec_let_elim[`i`, `t`, `wi`, `dc`, `pm`, `sn`, `ln'`])
       \\ rfs[LineDirty_def, CellRead_def]
);

val WriteBackLine_simp_def = Define`
    WriteBackLine_simp (li,t,pm,dc,n) =
     (let v = (dc li).sl
      in
        ((li =+
          dc li with sl := (t =+ SOME (THE (v t) with dirty := F)) v)
           dc,pm))
`;

val WriteBackLine_Dont_change_cache_value = Q.prove(
   `!i:(48 word) t:(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state) (n:num).
    (let (dc', _) =  WriteBackLine(i, t, pm, dc, n) state in
     let (dc'', _) =  WriteBackLine_simp(i, t, pm, dc, n) in
     let sn = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
     let ln = (w2n state.DC.ctr.DminLine) in
     (n <= dimword(:15) ==>  (((dc' i).sl t) = ((dc'' i).sl t))))`,

       xrw []
    \\ fs [WriteBackLine_simp_def, WriteBackLine_def, CellRead_def ,FOR_FOLDL, combinTheory.UPDATE_def]
    \\ lrw[]

    \\ Induct_on `n`

    >- (EVAL_TAC)
    \\ fs[DECIDE``SUC n = n + 1``, FOR_FOLDL]
    \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
    \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]] 
);

val WriteBackLine_CellRead_dcEQdc'_thm = Q.prove(
    `!i:(48 word) t:(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state) (n:num).
    (let (dc', _) =  WriteBackLine(i, t, pm, dc, n) state in
    ((n <= dimword(:15)) ==> (!wi:num. wi <= n ==>
     (CellRead(i,t,wi, dc) = CellRead(i,t,wi, dc'))				 
    )))`,
          xrw[CellRead_def]
       \\ assume_tac (WriteBackLine_Dont_change_cache_value |> spec_let_elim[`i`, `t`, `pm`, `dc`, `state`, `n`])
       \\ rfs[]
       \\ lrw[WriteBackLine_simp_def,  combinTheory.UPDATE_def, CellRead_def]
);

val wrtBckLine_dcEQpm'_thm = Q.store_thm("wrtBckLine_dcEQpm'_thm",
  `!i:(48 word) t:(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) n (state:dharma8_state).
    (let (dc', pm') =  WriteBackLine(i, t, pm, dc, n) state in
     let sn = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
     let ln = (w2n state.DC.ctr.DminLine) in
     (n <= dimword(:15) ==> (!wi:num. wi <= n ==>
          let pa = ((t << (sn + ln + 2)) !! (i << (ln + 2)) !! (n2w(wi):(48 word) << 2)) in
           (invariant_cache) ==>
	   (CellRead(i, t, wi, dc) = v2w(read_mem32(pa, pm')))
     )))`,

    xrw[]
    \\ imp_res_tac (wrtBck_memory_thm |> SIMP_RULE(srw_ss())[LET_DEF] |> PairedLambda.GEN_BETA_RULE)
    \\ qpat_assum`!x. P`(qspecl_then[`t`, `state`, `pm`, `i`, `dc`] assume_tac)
    \\ REABBREV_TAC

    \\ imp_res_tac (WriteBackLine_CellRead_dcEQdc'_thm |> SIMP_RULE(srw_ss())[LET_DEF] |> PairedLambda.GEN_BETA_RULE)
    \\ qpat_assum`!x. P`(qspecl_then[`t`, `state`, `pm`, `i`, `dc`] assume_tac)
    \\ rfs[]
);

val WriteBackLine_Dont_change_Mem_IfNotDirty_thm = Q.prove(
   `!(i:word48) (t:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state) n.
    (let (dc', pm')  =  WriteBackLine(i, t, pm, dc, n) state in
     let (dc'',pm'') =  WriteBackLine_simp(i, t, pm, dc, n) in
     let sn = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
     let ln = (w2n state.DC.ctr.DminLine) in
     (~LineDirty(i, t, dc)) ==>
     (!pa'. v2w(read_mem32(pa', pm')):word32 = v2w(read_mem32(pa', pm'')))
    )`,

       xrw []
    \\ fs_lambda_elim [WriteBackLine_simp_def, WriteBackLine_def, CellRead_def ,FOR_FOLDL, combinTheory.UPDATE_def, LineDirty_def]
);

val wrtBckLine_pmEQpm'IfNotDirty_thm = Q.store_thm("wrtBckLine_pmEQpm'IfNotDirty_thm",
   `!(i:word48) (t:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) n (state:dharma8_state).
    (let (_, pm') =  WriteBackLine(i, t, pm, dc, n) state in
     (~LineDirty(i, t, dc)) ==>
     (!pa'. (v2w(read_mem32(pa', pm)):word32 = v2w(read_mem32(pa', pm'))))
    )`,

       xrw[]
    \\ assume_tac(WriteBackLine_Dont_change_Mem_IfNotDirty_thm |> spec_let_elim [`i`, `t`, `pm`, `dc`, `state`, `n`])
    \\ rfs[]
    \\ qpat_assum`!a. P`(qspecl_then[`pa`] assume_tac)
    \\ fs[WriteBackLine_simp_def]
);

val writBckLine_NotchgTag'_thm = Q.prove(
   `!i:(48 word) t:(48 word)  (pm:(word48->word8)) (dc:(48 word -> CSET)) n t':(48 word) state.
    (let (dc', pm') =  WriteBackLine(i, t, pm, dc, n) state in
     (t <> t') ==>
     (n <= dimword(:15) ==>
     (((dc i).sl t') = ((dc' i).sl t')) ))`,

    lrw[]
    \\ PairedLambda.GEN_BETA_TAC
    \\ fs [WriteBackLine_def,FOR_FOLDL, combinTheory.UPDATE_def]
    \\ lrw[]

    \\ Induct_on `n`
    >- EVAL_TAC
    \\ strip_tac
    \\ `n ≤ 32768` by decide_tac
    \\ fs[DECIDE``SUC n = n + 1``]
    \\ ASSUME_TAC(rich_listTheory.COUNT_LIST_ADD
	 |> Q.SPECL[`n + 1n`, `1n`]
	 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
    \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]]);

val writBckLine_NotchgSidx'_thm = Q.prove(
    `!i:(48 word) i':(48 word) t:(48 word) t':(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) state n.
    (let (dc', pm') =  WriteBackLine(i, t, pm, dc, n) state in
     (n <= dimword(:15) ==>
     (i <> i') ==>
     (((dc i').sl t') = ((dc' i').sl t')) ))`,

    lrw[]
    \\ PairedLambda.GEN_BETA_TAC
    \\ fs [WriteBackLine_def,FOR_FOLDL, combinTheory.UPDATE_def]
    \\ lrw[]

    \\ Induct_on `n`
    >- EVAL_TAC
    \\ strip_tac
    \\ `n ≤ 32768` by decide_tac
    \\ fs[DECIDE``SUC n = n + 1``]
    \\ ASSUME_TAC(rich_listTheory.COUNT_LIST_ADD
	 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
	 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
    \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]]);

(* --------------------------------------------------------------------------------------------- *)
val cellFill_memeq_thm = Q.store_thm ("cellFill_memeq_thm",
  `!wi:num pa:(48 word) (pm:(word48->word8)).
    (let sval =  (CellFill(wi, pa, pm)) (n2w(wi):(48 word)) in
	 sval =  v2w(read_mem32(pa ||  (n2w(wi):48 word) << 2, pm))
    )`,
   fs[CellFill_def, combinTheory.UPDATE_def]
);

val mem_uchg_tac = 
(     xrw []
    \\ Induct_on `n`  
    THENL[xrw []
         \\ lfs[EVAL ``COUNT_LIST 1``,  combinTheory.UPDATE_def],
	  xfs []
         \\ `SUC n = n + 1 ` by FULL_SIMP_TAC (arith_ss) []
	 \\ FULL_SIMP_TAC (bool_ss) []
	 \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])

      \\ rfs []
      \\ xfs []
      \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]]]
);

val linefill_memeq_thm = Q.store_thm ("linefill_memeq_t",
 `!(h:(actions # num # 48 word) list) i:(48 word) t:(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) n state.
    (let (sl, _) =  LineFill(h, i, t, pm, dc, n) state in 
     let sn = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))  in
     let ln = (w2n state.DC.ctr.DminLine) in
     (n <= dimword(:15) ==>(!wi:num. wi <= n ==>
          let pa = (t << (sn + ln + 2)) !! (i << (ln + 2)) !! (n2w(wi):(48 word) << 2) in
	   (((THE (sl t)).value) (n2w(wi):48 word) = v2w(read_mem32(pa, pm)))
     )))`,

    xrw []
    \\ fs [LineFill_def,FOR_FOLDL, Abbr`pa`]
    \\ lrw[]
    \\ Induct_on `n`  
    THENL[xrw []
         \\ lfs[Abbr`sn`, Abbr`ln'`, EVAL ``COUNT_LIST 1``,  combinTheory.UPDATE_def, CellFill_def],

            ntac 2 strip_tac
	 \\ xrw[]
         \\ `n < 32768` by decide_tac
         \\ fs []
         \\ `SUC n = n + 1 ` by FULL_SIMP_TAC (arith_ss) []
         \\ FULL_SIMP_TAC (bool_ss) []
         \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
    			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
    			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
    
         \\ rfs[]
         \\ Cases_on `wi ≤ n`
         THENL[`wi < dimword(:15)` by (fs[] THEN REV_FULL_SIMP_TAC (arith_ss) [])
               \\ xfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]]
               \\ abr_tac listSyntax.is_foldl
               \\ xfs[combinTheory.UPDATE_def]
	       \\ (CASE_TAC  THEN REV_FULL_SIMP_TAC (arith_ss) []),
	       
	          xfs [combinTheory.UPDATE_def]
	       \\ `(wi = n + 1)` by decide_tac
	       \\ xfs [rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[],CellFill_def,combinTheory.UPDATE_def]
	       \\ (fn (asl,g) => let val a = (find_term is_fst g) in  
                            (SUBGOAL_THEN ``^a = pm`` (fn thm => ASSUME_TAC thm)) (asl, g) end)
	       \\ mem_uchg_tac
	       \\ fs[]
	      ]
	 ]
);

(* --------------------------------------------------------------------------------------------- *)
val w2vWordsEq_impl_wordsEq = Q.prove(
 `! w v:word32. (w2v(w) = w2v(v)) ==> (w = v)`,

    rw[]
    \\ CCONTR_TAC
    \\ undisch_all_tac
    \\ fs[w2v_def]
    \\ blastLib.BBLAST_PROVE_TAC
);

val neg_word_msb = Q.prove(
  `!w. (w >= 0w) ==> ~(word_msb w)`,
    lrw[]
 \\ assume_tac (SPEC``w: 'a word``(GSYM word_msb_neg))
 \\ undisch_all_tac
 \\ blastLib.BBLAST_PROVE_TAC
);

val si_ge_1_thm = Q.prove( 
 `!w:15 word. (w >= 1w) ==> (word_log2(w + 1w) >= 1w)`,

    SRW_TAC [ARITH_ss][word_log2_def, w2n_add, WORD_GE]
    \\ assume_tac(LOG2_w2n_lt |> Q.ISPEC `((w:15 word) + 1w)`)
    \\ rfs[word_msb_n2w_numeric, w2n_add]
    \\ EVERY[
      (`(LOG2(w2n w + 1))>=1` by(assume_tac
         (bitTheory.LOG2_LE_MONO 
         |> spec_let_elim[`2n`,`w2n(w:15 word)+1`]) >> fs[])
      \\ (Cases_on `w + 1w ≠ 0w` >> fs[])
      \\ (undisch_all_tac >> blastLib.BBLAST_PROVE_TAC))
   ]
);

val wIdx_extract_thm = Q.store_thm("wIdx_extract_thm",
 `! (pa:word48) (state:dharma8_state).
  let wi = wIdx(pa) state in 
  (wi) = (((w2n (state.DC.ctr.DminLine) + 1) >< (2 :num)) (pa:word48) :(48 word))`,
  
  lrw[wIdx_def]
  \\ ASSUME_TAC(word_extract_v2w
      |> Thm.INST_TYPE [Type.alpha |-> ``:48``, Type.beta  |-> ``:48``]
      |> Q.SPECL[`(w2n (state.DC.ctr.DminLine) + 1)`,`2n`,`w2v(pa:word48)`])
  \\ fs[v2w_w2v, word_bits_v2w]
  \\ blastLib.BBLAST_TAC);

val wi_lt_line_size_thm = Q.store_thm("wi_lt_line_size_thm",
`! va pa state.
   let (i, t, wi) = lineSpec(va, pa) state in
   let nl = w2n state.DC.ctr.DminLine      in
     (wi <= (2 ** nl - 1n))`,

    lrw[lineSpec_def] 
    \\ THM_SPECL_GOAL "wIdx" wIdx_extract_thm [``state:dharma8_state``]
    \\ assume_tac(WORD_EXTRACT_LT |> INST_TYPE[alpha |-> ``:48``, beta |-> ``:48``]
				  |> spec_let_elim [`w2n state.DC.ctr.DminLine + 1`, `2n`, `pa`])
    \\ fs[(DECIDE``!a. SUC a  = (a + 1)``)]
);

val wIdx_lt_dimword48_thm = Q.store_thm("wIdx_lt_dimword48_thm",
 `! va pa state.
    let (i, t, wi) = lineSpec(va, pa) state in 
    wi = (wi MOD 281474976710656)`,

   lrw[]
   \\ fs_lambda_elim[lineSpec_def, (wIdx_extract_thm |> SIMP_RULE(srw_ss())[LET_DEF])]
   \\ assume_tac(WORD_EXTRACT_LT |> INST_TYPE[alpha |-> ``:48``, beta |-> ``:48``]
				  |> spec_let_elim [`w2n state.DC.ctr.DminLine + 1`, `2n`, `pa`])
   \\ line_size_lt_dimword15 ``w2n state.DC.ctr.DminLine``
   \\ rfs[(DECIDE``!a. SUC a  = (a + 1)``)]);

val si_extract_thm = Q.store_thm("si_extract_thm",
 `!(va:word64) (pa:word48) (state:dharma8_state).
  let sid = si(va, pa) state in 
  let b = w2n (state.DC.ctr.DminLine) + 1 in
  let s = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
  (sid) = ((s + b) >< (b + 1)) (pa:word48) :(48 word)`,

  xrw []
  \\ FULL_SIMP_TAC(bool_ss)[si_def]
  \\ ASSUME_TAC(word_extract_v2w
      |> Thm.INST_TYPE [Type.alpha |-> ``:48``, Type.beta  |-> ``:48``]
      |> Q.SPECL[`(s:num) + (b:num)`,`(b:num) + 1`,`w2v(pa:word48)`])
  \\ fs[v2w_w2v, word_bits_v2w]
  \\ unabbrev_all_tac
  \\ blastLib.BBLAST_TAC);

val word_log2_lt_adrSize = Q.store_thm("word_log2_lt_adrSize",
 `!v:(15 word).(v <> 0w) ==>  w2n(word_log2(v))  < 48`,
  xrw []
  \\ imp_res_tac LOG2_w2n_lt
  \\ fs [word_lt_n2w, word_log2_def]);


val tag_extract_thm = Q.store_thm("tag_extract_thm",
  `!(va:word64) (pa:word48) (state:dharma8_state).
  let tg = tag(va, pa) state in 
  let ps = LENGTH (w2v pa) in
  let bi = w2n (state.DC.ctr.DminLine) + 1 in
  let st = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
  (* ((state.DC.ccsidr.NumSets + 1w) <> 0w) ==> *)
  ((tg) = ((ps - 1 >< (bi + st + 1)) (pa:word48) :(48 word)))`,

  xrw []
  \\ FULL_SIMP_TAC(bool_ss)[tag_def]
  \\ ASSUME_TAC(word_extract_v2w
      |> Thm.INST_TYPE [Type.alpha |-> ``:48``, Type.beta  |-> ``:48``]
      |> Q.SPECL[`ps - 1`,`((bi:num) + (st:num)) + 1`,`w2v(pa:word48)`])
  \\ fs [v2w_w2v, word_bits_v2w]
  \\ unabbrev_all_tac
  \\ blastLib.BBLAST_TAC);


val lineSpec_thm = Q.store_thm("lineSpec_thm",
  `!(va:word64) (pa:word48) (state:dharma8_state).
  let (i, t, wi) = lineSpec(va, pa) state in
  let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
  let nl = (w2n (state.DC.ctr.DminLine)) in
  invariant_cache ==>
  (pa = ((t ≪ (ns + nl + 2) ‖ i ≪ (nl + 2)) ‖ (n2w (wi):(48 word)) ≪ (2 :num)))`,

       lrw[]
    \\ PairedLambda.GEN_BETA_TAC
    \\ strip_tac
    \\ fs[lineSpec_def]
    \\ (qspecl_then [`pa`, `state`] assume_tac)wIdx_extract_thm
    \\ (qspecl_then [`va`, `pa`, `state`] assume_tac)si_extract_thm
    \\ (qspecl_then [`va`, `pa`, `state`] assume_tac)tag_extract_thm
    \\ rfs[LET_DEF]
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ abr_tac_goal wordsSyntax.is_w2n "ns" NONE
    \\ assume_tac(EXTRACT_JOIN_LSL
        |> INST_TYPE [beta |-> ``:48``]
	|> Q.ISPECL [`47n`, `nl + (ns + 1n)`, `nl+(ns + 2n)`, `nl + 2n`, `(nl+(ns + 2n))`, `nl + 2n`, `pa:word48`]
	|> SIMP_RULE (srw_ss()++ARITH_ss)[])
    \\ `nl + (ns + 2) ≤ 47` by (all_tac
        \\ fs[invariant_cache_def]
	\\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`_`, `_`, `_`, `nl + 2`, `ns + 1`, `state`] ASSUME_TAC)
	\\ fs[])
    \\ `MIN 47 (MIN (nl + 49) 47) = 47` by fs[arithmeticTheory.MIN_DEF]
    \\ assume_tac(si_ge_1_thm |> spec_let_elim [`state.DC.ccsidr.NumSets`])
    \\ fs[]
    \\ assume_tac(EXTRACT_JOIN_LSL
        |> INST_TYPE [beta |-> ``:48``]
	|> Q.ISPECL [`47n`, `nl + 1n`, `nl + 2n`, `2n`, `nl + 2n`, `2n`, `pa:word48`]
	|> SIMP_RULE (srw_ss()++ARITH_ss)[])

    \\ assume_tac(SPECL[``(state :dharma8_state).DC.ctr.DminLine``](INST_TYPE[alpha |->``:4``]w2n_lt) 
       |> SIMP_RULE(srw_ss())[])
    \\ `2 ≤ nl + 1` by (all_tac
        \\ xfs[invariant_cache_def, Abbr`nl`]
	\\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`_`, `_`, `_`, `nl + 2`, `ns`, `state`] ASSUME_TAC)
	\\ assume_tac(WORD_GE |> Q.ISPECL[`state.DC.ctr.DminLine:word4`, `1w:word4`])
	\\ rfs[])
    \\ fs[invariant_cache_def]
    \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`_`, `_`, `_`, `nl + 2`, `ns`, `state`] ASSUME_TAC)
    \\ qpat_assum`!pa'. 0xFFFFFFFFFFFCw && pa' = pa'` (qspecl_then[`pa`] assume_tac )
    \\ ntac 2 (WEAKEN_TAC is_forall)
    \\ `w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) ≥ 1` by fs[]
        >- (UNDISCH_MATCH_TAC``word_log2 (state.DC.ccsidr.NumSets + 1w) ≥ 1w`` >> fs[WORD_GE])
    \\ rfs[] >> `2 ≤ ns + 1` by decide_tac
    \\ undisch_all_tac
    \\ blastLib.BBLAST_PROVE_TAC
);

(* --------------------------------------------------------------------------------------------- *)
val fill_dcEQpm_thm = Q.store_thm("fill_dcEQpm_thm",
   `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state).
    (let (dc', pm') =  Fill(va, pa, pm, dc) state in
     let (i, t, wi) = lineSpec(va, pa) state in
     ((2 ** w2n state.DC.ctr.DminLine − 1) <= dimword(:15) ==>( invariant_cache ==>
      (wi <= (2 ** w2n state.DC.ctr.DminLine − 1)) ==> (CellRead(i, t, wi, dc') = v2w(read_mem32(pa, pm')))
     )))`,

   lrw []
   \\ ntac 3 (xfs[Fill_def, Once LET_DEF])
   \\ PairedLambda.GEN_BETA_TAC
   \\ REPEAT STRIP_TAC
   \\ xfs []
   \\ CASE_TAC
   THENL[
   xfs [LET_DEF]
   \\(fn (asl, g) => let val a::b::c::_ = (strip_pair o snd o dest_comb o fst o dest_eq) g 
		     in (Q.ABBREV_TAC`i = ^a`
			\\ Q.ABBREV_TAC`t = ^b`
			\\ Q.ABBREV_TAC`wi = ^c`)(asl, g)
		     end)
   \\ PairedLambda.GEN_BETA_TAC
   \\ fs [combinTheory.UPDATE_def]
   \\ simp[CellRead_def] 
   \\ ASSUME_TAC (linefill_memeq_thm
      |> Q.ISPECL[`((dc:(48 word -> CSET)) i).hist`,`i:(48 word)`,`t:(48 word)`,`(pm:(word48->word8))`,
                  `(dc:(48 word -> CSET))`, `2 ** w2n state.DC.ctr.DminLine − 1`, `state:dharma8_state`]
      |> SIMP_RULE(srw_ss())[LET_DEF] 
      |> PairedLambda.GEN_BETA_RULE)
   \\ rfs[]
   \\ PAT_ASSUM``!(wi:num). x`` (fn thm => ASSUME_TAC(SPECL[``wi:num``] thm))
   \\ THM_KEEP_TAC ``invariant_cache`` (fs[invariant_cache_def])
   \\ qpat_assum `!p:word48. P` (qspecl_then [`pa`] ASSUME_TAC)
   \\ ASSUME_TAC(lineSpec_thm
      |> Q.ISPECL[`va:word64`,`pa:word48`,`state:dharma8_state`]
      |> SIMP_RULE(srw_ss()) [LET_DEF]
      |> PairedLambda.GEN_BETA_RULE)
   \\ REABBREV_TAC
   \\ REV_FULL_SIMP_TAC (arith_ss) [],

   CONV_TAC (ONCE_DEPTH_CONV (REWRITE_CONV [LET_DEF]))
   \\ PairedLambda.GEN_BETA_TAC
   \\ fs [combinTheory.UPDATE_def] 
   \\ (fn (asl, g) => let val a::b::c::_ = (strip_pair o snd o dest_comb o fst o dest_eq) g 
		     in (Q.ABBREV_TAC`i = ^a`
			\\ Q.ABBREV_TAC`t = ^b`
			\\ Q.ABBREV_TAC`wi = ^c`)(asl, g)
		     end)
   \\ simp[CellRead_def]
   \\(fn (asl, g) => let val (cc, mm) = (dest_eq) g
			  val m = (snd o dest_pair o snd o dest_comb o fst o bitstringSyntax.dest_v2w ) mm
			  val c = (find_term is_abs) cc
  			  val h = (find_term is_snd) cc
		in (Q.ABBREV_TAC`pm' = ^m` 
		   \\ Q.ABBREV_TAC`dc' = ^c`
		   \\ Q.ABBREV_TAC`h' = ^h`) (asl, g) end)  
   \\ ASSUME_TAC (linefill_memeq_thm
      |> Q.ISPECL[`(h' :(actions # num # word48) list)`,`i:(48 word)`,`t:(48 word)`,`(pm':(word48->word8))`,
                  `(dc':(48 word -> CSET))`, `2 ** w2n state.DC.ctr.DminLine − 1`,`state:dharma8_state`]
      |> SIMP_RULE(srw_ss())[LET_DEF] 
      |> PairedLambda.GEN_BETA_RULE)
   \\ rfs []
   \\ PAT_ASSUM``!(wi:num). x`` (fn thm => ASSUME_TAC(SPECL[``wi:num``] thm))
   \\ THM_KEEP_TAC ``invariant_cache`` (fs[invariant_cache_def])
   \\ qpat_assum `!p:word48. P` (qspecl_then [`pa`] ASSUME_TAC)
   \\ ASSUME_TAC(lineSpec_thm
      |> Q.ISPECL[`va:word64`,`pa:word48`,`state:dharma8_state`]
      |> SIMP_RULE(srw_ss()) [LET_DEF]
      |> PairedLambda.GEN_BETA_RULE)
   \\ REABBREV_TAC
   \\ FULL_SIMP_TAC (arith_ss) []
]);

(* --------------------------------------------------------------------------------------------- *)
val shift_add_thm = Q.store_thm("shift_add_thm",
`!w1:(word48) w2 n m. ((w1 << (n + m)) !! (w2 << m)) = (((w1 << n) !! w2) << m)`,
fs[]);

val adr_neq_thm = Q.store_thm("adr_neq_thm",
 `!(a:word48) (b:word48) (c:word48) (d:word48) (n:num). 
   let bmM = ((0xffffffffffffw:word48) >>> n) in
   let bmL = ~((0xffffffffffffw:word48) >>> n << n) in
  ((n < 48)) ==>  
  ((a && bmM = a) /\ (b && bmM = b)) ==>
  ((c && bmL = c) /\ (d && bmL = d)) ==>
  ((a << n) <> (b << n)) ==>   
  (((a << n) !! c) <> ((b << n) !! d))`,

  ntac 4 strip_tac
  \\ ntac 48 (Induct_on `n`
   THENL[fs[] \\ blastLib.BBLAST_PROVE_TAC,  
	 fs[] \\ PAT_ASSUM ``a``(fn thm => all_tac)])
);

val writeback_mem_eq_thm = Q.store_thm ("writeback_mem_eq_thm",
  `!(pa:word48) (va:word64) (pm:(word48->word8)) (slval:SLVAL) (state:dharma8_state) i':(48 word) t':(48 word) wi'.
	    (let (i, t, wi) = lineSpec(va, pa) state in
             let pm' =  WriteBack(i', t', wi', pm, slval) state in 
	     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in 
	     let nl = (w2n state.DC.ctr.DminLine) in 
	     (((((t' << ns) !! i') << (nl + 2n)) <> ((t << ns) !! i) << (nl + 2n)) ==> 
	      (invariant_cache) ==> 
	      (v2w(read_mem32(pa, pm)):word32 = v2w(read_mem32(pa, pm')))	
	      )
	    )`,

        lrw[]
     \\ PairedLambda.GEN_BETA_TAC	      
     \\ (fn (asl, g) => let val  a::b::_ = find_terms wordsSyntax.is_w2n ((fst o dest_imp) g)
			    val  c::d::_ = find_terms is_fst ((fst o dest_imp) g)
		       in (Q.ABBREV_TAC`ns = (^a)` \\ Q.ABBREV_TAC`nl = ^b`
			\\ Q.ABBREV_TAC`t = ^c`  \\ Q.ABBREV_TAC`i = ^d`)(asl, g)        end)
     \\ xrw []
     \\ fs [WriteBack_def, combinTheory.UPDATE_def, read_mem32_def]

     \\ ASSUME_TAC(lineSpec_thm
 	     |> Q.ISPECL[`va:word64`,`pa:word48`,`state:dharma8_state`]
	     |> SIMP_RULE(srw_ss()) [LET_DEF]
	     |> PairedLambda.GEN_BETA_RULE)
	   \\ REABBREV_TAC
     \\ rfs[]
     \\ Q.ABBREV_TAC`wi = (SND (SND (lineSpec (va,pa) state)))`
     \\ THM_KEEP_TAC ``invariant_cache`` (fs[invariant_cache_def])
     \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`i`, `t`, `wi`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
     \\ qpat_assum `!p:word48. a=b` (qspecl_then [`w2w(i ≪ (nl+2) ‖ t ≪ (nl+(ns+2)) ‖ n2w wi ≪ 2)`] ASSUME_TAC)
     \\ ntac 2 (WEAKEN_TAC is_forall)
     \\ fs[invariant_cache_def]
     \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`i'`, `t'`, `wi'`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
     \\ qpat_assum`!p:word48. a=b`(qspecl_then [`w2w(i' ≪ (nl+2) ‖ t' ≪ (nl+(ns+2)) ‖ n2w wi' ≪ 2)`] ASSUME_TAC)
     \\ ntac 2 (WEAKEN_TAC is_forall)
   
     \\ (qspecl_then [`(t << ns !! i )`,`(t' << ns !! i' )`,`n2w wi << 2`,`n2w wi' << 2`,`(nl+2)`] ASSUME_TAC) 
        adr_neq_thm
     \\ fs[LET_DEF]
     \\ rfs[]
     \\ Q.ABBREV_TAC`pa' = (i' ≪ (nl + 2) ‖ t' ≪ (nl + (ns + 2)) ‖ n2w wi' ≪ 2)`
     \\ Q.ABBREV_TAC`pa = (i ≪ (nl + 2) ‖ t ≪ (nl + (ns + 2)) ‖ n2w wi ≪ 2)`
     \\ REPEAT ((fn (asl, g) => 
                let val (t,_,_) = (dest_cond o find_term is_cond o snd o dest_eq) g in
	        `~^t` by  (ntac 2 (UNDISCH_MATCH_TAC ``0xFFFFFFFFFFFCw && x = x``)
			   \\ (UNDISCH_MATCH_TAC ``x <> y``) 
			   \\ blastLib.BBLAST_PROVE_TAC ) end (asl, g))
	        \\ fs [])
);

(* --------------------------------------------------------------------------------------------- *)
val lineSpec_eq_thm = Q.store_thm("lineSpec_eq_thm",
 `!s s' pa va.
  invariant_cache ==>
  (lineSpec(va, pa) s = lineSpec(va, pa) s')`,

  lrw[]
  \\ fs[invariant_cache_def]
  \\ qpat_assum `!s:dharma8_state a'. P` (qspecl_then [`s`, `s'`] ASSUME_TAC)
  \\ REPEAT (WEAKEN_TAC is_forall)
  \\ fs[lineSpec_def, si_def, tag_def, wIdx_def]
);


val writebackline_mem_eq_thm = Q.store_thm("writebackline_mem_eq_thm",
 `!(i':word48) (t':word48)  (pm:(word48->word8)) (dc:(48 word -> CSET)) (n:num) (va:word64) (pa:word48) state.
	    (let (i, t, wi) = lineSpec(va, pa) state in
	     let (dc', pm') =  WriteBackLine(i', t', pm, dc, n) state in
	     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))  in
	     let nl = (w2n state.DC.ctr.DminLine) in 
	      (((((t' << ns) !! i') << (nl + 2n)) <> ((t << ns) !! i) << (nl + 2n)) ==>
	       (n <= dimword(:15)) ==> 
	       (invariant_cache) ==> 
	       (v2w(read_mem32(pa, pm)):word32 = v2w(read_mem32(pa, pm')))
	      )
	    )`,

     fs [WriteBackLine_def, combinTheory.UPDATE_def, FOR_FOLDL]
    \\ rpt strip_tac
    \\ (Induct_on`n` \\ PairedLambda.GEN_BETA_TAC \\ lrw [])
    THENL[lfs[EVAL ``COUNT_LIST 1``]
         \\ assume_tac(writeback_mem_eq_thm
             |> spec_let_elim[`pa`,`va`,`pm`, `THE (((dc:(48 word -> CSET)) i').sl t')`, `state`, `i':word48`, `t'`, `0`] 
             |> SIMP_RULE(srw_ss()) [WriteBack_def, LET_DEF, combinTheory.UPDATE_def])
         \\ rfs[],
        
          UNDISCH_MATCH_TAC``(\(a,b, c). (x)) d``
         \\ PairedLambda.GEN_BETA_TAC
         \\ strip_tac
         \\ `n < 32768` by decide_tac
         \\ fs[]
         \\`SUC n = n + 1 ` by FULL_SIMP_TAC (arith_ss) []
         \\ REV_FULL_SIMP_TAC (bool_ss) []
         \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
         			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
         			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
         
         \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]]
         \\ abr_tac listSyntax.is_foldl

	 \\ (fn (asl, g) => let val trm1 = (dest_fst o find_term is_fst) g val trm2 = repeat (dest_snd) trm1 
             in 
                  (assume_tac(writeback_mem_eq_thm 
                  |> spec_let_elim[`pa`, `va`, `FST ^trm1`, `FST ^trm2`, `SND ^trm1`, `i'`,`t'`,`n+1`]
		  |> SIMP_RULE(srw_ss()) [WriteBack_def, LET_DEF, combinTheory.UPDATE_def]))  (asl, g)
             end)
        \\ FIRST_ASSUM (fn thm => let val trm = (find_term is_snd (concl thm))
           in 
                  THM_KEEP_TAC ``invariant_cache`` (fs[invariant_cache_def])
		  \\ (qspecl_then [`state`, `^trm`, `pa`, `va`] assume_tac) lineSpec_eq_thm
                  \\ qpat_assum `!s:dharma8_state s'. P` (qspecl_then[`state`, `^trm`] assume_tac)
	   end)
         \\ fs[]
	 \\ metis_tac[] ]
);  


(* --------------------------------------------------------------------------------------------- *)
val word_shift_eq = Q.prove(
 `!w:word48 v m. (w = v) ==> ((w << m) = (v << m))`,
blastLib.BBLAST_PROVE_TAC);


local
  val th1 = `x <> t'` by (all_tac  
    \\ CCONTR_TAC
    \\ fs[invariant_cache_def, Hit_def]
    \\ qpat_assum `∀h i t dc x. P` (qspecl_then [`((dc:word48->CSET) (i:word48)).hist`, `i`, `t`, `dc`, `t'`] assume_tac)
    \\ UNDISCH_MATCH_TAC ``¬(λ(li,t,wi). IS_SOME (b)) (a)``
    \\ PairedLambda.GEN_BETA_TAC
    \\ rwsimp[])

  val subgoal_tac1 =
       (TAKE_DOWN_TAC ``a ==> b``

    \\ FIRST_ASSUM (fn thm => let val trm = (fst o dest_imp o concl) thm in `^trm`by all_tac end)
    >- (assume_tac(adr_thm |> spec_let_elim [`x`, `i`, `t'`, `i'`, `ns`, `(nl + 2)`])
       \\ THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
       \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`i'`, `t'`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
       \\ xfs[invariant_cache_def]
       \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`i`, `x`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
       \\ rfs[])
    \\ fs[])

in
 val fill_pm'EQpm_diffIn_thm = Q.store_thm("fill_pm'EQpm_diffIn_thm",
  `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (va':word64) (pa':word48) state.
    (let (dc', pm') =  Fill(va, pa, pm, dc) state in    
     ((invariant_cache ==> 
      ~Hit(va', pa', dc) state ==>
      (v2w(read_mem32(pa', pm')):word32 =v2w(read_mem32(pa', pm)))
     )))`,

    lrw []
    \\ fs_lambda_elim[Fill_def]
    \\ rpt strip_tac
    \\ CASE_TAC
    >-(fs_lambda_elim[LET_DEF] >> fs[])
   
    \\ CONV_TAC (ONCE_DEPTH_CONV (REWRITE_CONV [LET_DEF]))
    \\ fs_lambda_elim [combinTheory.UPDATE_def] 
    \\ Q.ABBREV_TAC`i = FST (lineSpec (va,pa) state)`
    \\ THM_SPECL_GOAL "WriteBackLine" writebackline_mem_eq_thm 
       [``va':word64``,``pa':word48``,``state:dharma8_state``]
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ undisch_all_tac
    \\ abr_lineSpec_tac_dubl
    \\ rpt strip_tac
    \\ line_size_lt_dimword15 ``nl:num``
    \\ Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`
    \\ Cases_on`i <> i'`
    >- subgoal_tac1
    \\ (th1 \\ subgoal_tac1)
 )
end;

(* --------------------------------------------------------------------------------------------- *)

val CacheClean_dcEQpm'_thm = Q.store_thm("CacheClean_dcEQpm'_thm",
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:dharma8_state).
    (let (dc', pm')    =  CacheCleanByAdr(va, pa, pm, dc) state in
     let (i', t', wi') = lineSpec(va', pa') state in
     let (i, t, wi)    = lineSpec(va, pa) state in
     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
     let nl = (w2n state.DC.ctr.DminLine) in
     (Hit (va,pa,dc) state) ==>
     ((invariant_cache) ==>
      ((((t' << ns) !! i') << (nl + 2n)) = ((t << ns) !! i) << (nl + 2n)) ==>
	   (CellRead(i', t', wi', dc) = v2w(read_mem32(pa', pm')))
     ))`,
     
    fs_lambda_elim[CacheCleanByAdr_def]
    \\ lrw[]
    \\ abr_lineSpec_tac_sgl
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`

    \\ THM_SPECL_GOAL "WriteBackLine" wrtBckLine_dcEQpm'_thm [``state:dharma8_state``]
    \\ line_size_lt_dimword15 ``nl:num``
    \\ THM_SPECL_ASSM "lineSpec" wi_lt_line_size_thm[`state`]
    \\ THM_SPECL_ASSM "lineSpec" lineSpec_thm [`state`]
    \\ abr_lineSpec_tac_sgl  
    \\ (res_tac >> qpat_assum`!a. b` (qspecl_then[`wi''`] assume_tac))
    \\ rfs[]
    \\ assume_tac(adr_thm |> spec_let_elim[`t'`, `i'`,`t''`, `i''`, `ns`, `(nl + 2)`]
		      |> SIMP_RULE(arith_ss)[])
    \\ THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
    \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`i'`, `t'`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
    \\ fs[invariant_cache_def]
    \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`i''`, `t''`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
    \\ rw[]
    \\ metis_tac[]
);


val CacheClean_dcEQdc'_thm = Q.store_thm("CacheClean_dcEQdc'_thm",
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:dharma8_state).
    (let (dc', pm') =  CacheCleanByAdr(va, pa, pm, dc) state in
     let (i', t', wi') = lineSpec(va', pa') state in
     let (i, t, wi) = lineSpec(va, pa) state in
     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
     let nl = (w2n state.DC.ctr.DminLine) in
     ((invariant_cache) ==>
      ((((t' << ns) !! i') << (nl + 2n)) = ((t << ns) !! i) << (nl + 2n)) ==>
	    (CellRead(i', t', wi', dc) = CellRead(i', t', wi', dc'))
     ))`,
     
    fs_lambda_elim[CacheCleanByAdr_def]
    \\ lrw[]
    \\ abr_lineSpec_tac_sgl
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`
    \\ abr_lineSpec_tac_sgl
    \\ assume_tac(WriteBackLine_CellRead_dcEQdc'_thm |> spec_let_elim[`i''`, `t''`, `pm`, `dc`,`state`, `2 ** nl:num − 1`])
    \\ line_size_lt_dimword15 ``nl:num``
    \\ fs[]
    \\ qpat_assum`!a. b` (qspecl_then[`wi''`] assume_tac)
    \\ THM_SPECL_ASSM "lineSpec" wi_lt_line_size_thm[`state`]
    \\ assume_tac(adr_thm |> spec_let_elim[`t'`, `i'`,`t''`, `i''`, `ns`, `(nl + 2)`]
	      |> SIMP_RULE(arith_ss)[])
    \\ THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
    \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`i'`, `t'`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
    \\ fs[invariant_cache_def]
    \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`i''`, `t''`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
    \\ rw[]
    \\ metis_tac[]
);

local

val tac =
       fs_lambda_elim[CacheCleanByAdr_def, combinTheory.UPDATE_def, Hit_def, Evict_def, CellRead_def]
    \\ lrw[]
    \\ abr_lineSpec_tac_sgl
    \\ Q.ABBREV_TAC`i = FST (lineSpec (va,pa) state)`
    \\ Q.ABBREV_TAC`t = FST (SND (lineSpec (va,pa) state))`
    \\ Cases_on`i <> i'`
    \\ (assume_tac(writBckLine_NotchgSidx'_thm 
         |> spec_let_elim[`i`, `i'`, `t`, `t'`, `pm`, `dc`, `state`, `2 ** w2n state.DC.ctr.DminLine − 1`])
       \\ line_size_lt_dimword15``w2n state.DC.ctr.DminLine``
       \\ fs[])
  
    \\ (`t <> t'` by (CCONTR_TAC >> fs[]))
    \\ THM_SPECL_GOAL "WriteBackLine" writBckLine_NotchgTag'_thm [``t':word48``, ``state:dharma8_state``]
    \\ line_size_lt_dimword15``w2n state.DC.ctr.DminLine``    
    \\ fs[]

in
val CacheClean_dcEQdc'_diffMsb_thm = Q.store_thm("CacheClean_dcEQdc'_diffMsb_thm",
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:dharma8_state).
    (let (dc', pm') =  CacheCleanByAdr(va, pa, pm, dc) state in
     let (i', t', wi') = lineSpec(va', pa') state in
     let (i, t, wi) = lineSpec(va, pa) state in
     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
     let nl = (w2n state.DC.ctr.DminLine) in
     ((invariant_cache) ==>
      ((((t' << ns) !! i') << (nl + 2n)) <> ((t << ns) !! i) << (nl + 2n)) ==>
	    (CellRead(i', t', wi', dc) = CellRead(i', t', wi', dc'))
     ))`, 
    tac
)

val CacheClean_hitDc'_diffAddr_thm = Q.store_thm("CacheClean_hitDc'_diffAddr_thm",
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:dharma8_state).
    (let (i, t, wi)    = lineSpec(va, pa) state               in
     let (i', t', wi') = lineSpec(va', pa') state             in
     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))  in
     let nl = (w2n state.DC.ctr.DminLine)                     in 
     let (dc', pm') =  CacheCleanByAdr(va, pa, pm, dc) state  in
     ((((t' << ns) !! i') << (nl + 2n)) <> ((t << ns) !! i) << (nl + 2n)) ==>
     (Hit (va ,pa ,dc) state) ==>
     (Hit (va',pa',dc) state) ==>
     (Hit (va',pa',dc') state)
    )`,
    tac
)

val CacheClean_keepMiss_diffMsb_thm = Q.store_thm("CacheClean_keepMiss_diffMsb_thm",
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:dharma8_state).
    (let (i, t, wi)    = lineSpec(va, pa) state               in
     let (i', t', wi') = lineSpec(va', pa') state             in
     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))  in
     let nl = (w2n state.DC.ctr.DminLine)                     in 
     let (dc', pm') =  CacheCleanByAdr(va, pa, pm, dc) state in
     ((((t' << ns) !! i') << (nl + 2n)) <> ((t << ns) !! i) << (nl + 2n)) ==>
     (Hit (va ,pa ,dc) state) ==>
     (~Hit (va',pa',dc) state) ==>
     (~Hit (va',pa',dc') state)
    )`,
    tac
)
end;

val CacheClean_pmEqpm'_diffMsb_thm = Q.prove(
`!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:dharma8_state).
    (let (i, t, wi)    = lineSpec(va, pa) state               in
     let (i', t', wi') = lineSpec(va', pa') state             in
     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))  in
     let nl = (w2n state.DC.ctr.DminLine)                     in 
     let (dc', pm') =  CacheCleanByAdr(va, pa, pm, dc) state in
     ((((t' << ns) !! i') << (nl + 2n)) <> ((t << ns) !! i) << (nl + 2n)) ==>
     (invariant_cache) ==>
     (v2w(read_mem32(pa', pm)):word32 =  v2w(read_mem32(pa', pm')))
    )`,

      fs_lambda_elim[CacheCleanByAdr_def, combinTheory.UPDATE_def, Hit_def, Evict_def]
    \\ lrw[]
    \\ THM_SPECL_GOAL "WriteBackLine" writebackline_mem_eq_thm [``va':word64``, ``pa':word48``, ``state:dharma8_state``]
    \\ line_size_lt_dimword15``w2n state.DC.ctr.DminLine``
    \\ rfs[]
);

val CacheInvalidate_dcEQpm'_thm = Q.store_thm("CacheInvalidate_dcEQpm'_thm",
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:dharma8_state).
    (let (dc', pm')    =  CacheInvalidateByAdr(va, pa, pm, dc) state in
     let (i, t, wi)    = lineSpec(va, pa) state in
     let (i', t', wi') = lineSpec(va', pa') state in
     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
     let nl = (w2n state.DC.ctr.DminLine) in
     (Hit (va,pa,dc) state) ==>
     ((invariant_cache) ==>
      ((((t' << ns) !! i') << (nl + 2n)) = ((t << ns) !! i) << (nl + 2n)) ==>
	   (CellRead(i', t', wi', dc) = v2w(read_mem32(pa', pm')))
     ))`,
     
    fs_lambda_elim[CacheInvalidateByAdr_def]
    \\ lrw[]
    \\ abr_lineSpec_tac_sgl
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ THM_SPECL_GOAL "WriteBackLine" wrtBckLine_dcEQpm'_thm [``state:dharma8_state``]
    \\ line_size_lt_dimword15 ``nl:num``
    \\ fs[]
    \\ abr_lineSpec_tac_sgl
    \\ qpat_assum`!a. b` (qspecl_then[`wi''`] assume_tac)
    \\ THM_SPECL_ASSM  "lineSpec" wi_lt_line_size_thm [`state`]
    \\ THM_SPECL_ASSM "lineSpec" lineSpec_thm [`state`]
    \\ mfs[]
    \\ Q.ABBREV_TAC`nl = (w2n state.DC.ctr.DminLine)`
    \\ Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`
    \\ assume_tac(adr_thm |> spec_let_elim[`t'`, `i'`,`t''`, `i''`, `ns`, `(nl + 2)`]
		      |> SIMP_RULE(arith_ss)[])
    \\ THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
    \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`i'`, `t'`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
    \\ fs[invariant_cache_def]
    \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`i''`, `t''`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
    \\ rw[]
    \\ metis_tac[]

);


val CacheInvalidate_missDc'_thm = Q.store_thm("CacheInvalidate_missDc'_thm",
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state).
    (let (dc', pm') =  CacheInvalidateByAdr(va, pa, pm, dc) state in
     (Hit (va,pa,dc) state) ==>
     (~Hit (va,pa,dc') state)
    )`,
    fs_lambda_elim[CacheInvalidateByAdr_def, combinTheory.UPDATE_def, Hit_def, Evict_def]
    \\ lrw[]
);


local
val tac = 
      fs_lambda_elim[WriteBackLine_def, combinTheory.UPDATE_def]
    \\ lrw[]
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ abr_tac_goal wordsSyntax.is_w2n "ns" NONE
    \\ mk_subgoal_then ``T`` ``2 ** nl − 1n``
    >- (Induct
       >- (EVAL_TAC >> fs[])
      \\ fs [WriteBackLine_def, CellRead_def ,FOR_FOLDL, combinTheory.UPDATE_def]
      \\ fs[DECIDE``SUC n = n + 1``]
      \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])

      \\ lfs []
      \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]])
    \\ qpat_assum`!a. b` (qspecl_then [`n`] assume_tac)
    \\ fs[]

in

val CacheInvalidate_hitDc'_diffAddr_thm = Q.store_thm("CacheInvalidate_hitDc'_diffAddr_thm",
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:dharma8_state).
    (let (i, t, wi)    = lineSpec(va, pa) state               in
     let (i', t', wi') = lineSpec(va', pa') state             in
     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))  in
     let nl = (w2n state.DC.ctr.DminLine)                     in 
     let (dc', pm') =  CacheInvalidateByAdr(va, pa, pm, dc) state in
     ((((t' << ns) !! i') << (nl + 2n)) <> ((t << ns) !! i) << (nl + 2n)) ==>
     (Hit (va ,pa ,dc) state) ==>
     (Hit (va',pa',dc) state) ==>
     (Hit (va',pa',dc') state)
    )`,

       fs_lambda_elim[CacheInvalidateByAdr_def, combinTheory.UPDATE_def, Hit_def, Evict_def]
    \\ lrw[]
    \\ abr_lineSpec_tac_sgl
    \\ Q.ABBREV_TAC`i = FST (lineSpec (va,pa) state)`
    \\ Q.ABBREV_TAC`t = FST (SND (lineSpec (va,pa) state))`

    >- ((`t <> t'` by (CCONTR_TAC >> fs[])) \\ ( rfs[] >>  tac ))
    \\ tac
)



val CacheInvalidate_dcEQdc'_diffAddr_thm = Q.store_thm("CacheInvalidate_dcEQdc'_diffAddr_thm",
`! (va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:dharma8_state).
    (let (i, t, wi)    = lineSpec(va, pa) state               in
     let (i', t', wi') = lineSpec(va', pa') state             in
     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))  in
     let nl = (w2n state.DC.ctr.DminLine)                     in 
     let (dc', pm') =  CacheInvalidateByAdr(va, pa, pm, dc) state in
     ((((t' << ns) !! i') << (nl + 2n)) <> ((t << ns) !! i) << (nl + 2n)) ==>
     (Hit (va ,pa ,dc) state) ==>
     (Hit (va',pa',dc) state) ==>
     (CellRead(i', t', wi', dc) = CellRead(i', t', wi', dc'))
    )`,

       fs_lambda_elim[CacheInvalidateByAdr_def, combinTheory.UPDATE_def, Hit_def, Evict_def, CellRead_def]
    \\ lrw[]
    \\ abr_lineSpec_tac_sgl
    \\ Q.ABBREV_TAC`i = FST (lineSpec (va,pa) state)`
    \\ Q.ABBREV_TAC`t = FST (SND (lineSpec (va,pa) state))`
    >- ((`t <> t'` by (CCONTR_TAC >> fs[])) \\ ( rfs[] >>  tac ))
    \\ tac
)

val CacheInvalidate_keepMiss_diffMsb_thm = Q.store_thm("CacheInvalidate_keepMiss_diffMsb_thm",
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:dharma8_state).
    (let (i, t, wi)    = lineSpec(va, pa) state               in
     let (i', t', wi') = lineSpec(va', pa') state             in
     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))  in
     let nl = (w2n state.DC.ctr.DminLine)                     in 
     let (dc', pm') =  CacheInvalidateByAdr(va, pa, pm, dc) state in
     ((((t' << ns) !! i') << (nl + 2n)) <> ((t << ns) !! i) << (nl + 2n)) ==>
     (Hit (va ,pa ,dc) state) ==>
     (~Hit (va',pa',dc) state) ==>
     (~Hit (va',pa',dc') state)
    )`,

       fs_lambda_elim[CacheInvalidateByAdr_def, combinTheory.UPDATE_def, Hit_def, Evict_def]
    \\ lrw[]
    >- (CCONTR_TAC >> UNDISCH_MATCH_TAC``IS_SOME x`` >> tac)
    \\ tac
)
end; 

val CacheInvalidate_pmEqpm'_diffMsb_thm = Q.prove(
`!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:dharma8_state).
    (let (i, t, wi)    = lineSpec(va, pa) state               in
     let (i', t', wi') = lineSpec(va', pa') state             in
     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))  in
     let nl = (w2n state.DC.ctr.DminLine)                     in 
     let (dc', pm') =  CacheInvalidateByAdr(va, pa, pm, dc) state in
     ((((t' << ns) !! i') << (nl + 2n)) <> ((t << ns) !! i) << (nl + 2n)) ==>
     (invariant_cache) ==>
     (v2w(read_mem32(pa', pm)):word32 =  v2w(read_mem32(pa', pm')))
    )`,

      fs_lambda_elim[CacheInvalidateByAdr_def, combinTheory.UPDATE_def, Hit_def, Evict_def]
    \\ lrw[]
    \\ THM_SPECL_GOAL "WriteBackLine" writebackline_mem_eq_thm [``va':word64``, ``pa':word48``, ``state:dharma8_state``]
    \\ line_size_lt_dimword15``w2n state.DC.ctr.DminLine``
    \\ rfs[]
);

(* --------------------------------------------------------------------------------------------- *)
val msb_extract_def = Define`msb_extract va pa state =
  let (i, t, wi) = lineSpec(va, pa) state                  in
  let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))  in
  let nl = (w2n state.DC.ctr.DminLine)                     in 
  ((t << ns) !! i) << (nl + 2n)
`;

val msbEqAdrs_Hit_dc_thm = Q.store_thm("msbEqAdrs_Hit_dc_thm",
`!va pa dc va' pa' state.
 (invariant_cache) ==>
 (Hit(va, pa, dc) state) ==>
 ((msb_extract va pa state) = (msb_extract va' pa' state)) ==> 
 (Hit(va', pa', dc) state)`,
 
    fs_lambda_elim [Hit_def, msb_extract_def]
    \\ ntac 6 strip_tac
    \\ abr_lineSpec_tac_dubl
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ abr_tac_goal wordsSyntax.is_w2n "ns" NONE
    \\ lrw[]
    \\ assume_tac(adr_thm |> spec_let_elim[`t`, `i`,`t'`, `i'`, `ns`, `(nl + 2)`]
		      |> SIMP_RULE(arith_ss)[])
    \\ THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
    \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`i`, `t`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
    \\ fs[invariant_cache_def]
    \\ qpat_assum `!i t wi ni nt s. P` (qspecl_then [`i'`, `t'`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
    \\ fs[]
);

val cacheRead_miss_thm = Q.store_thm("cacheRead_miss_thm",
  `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state).
  let (dc', pm', vlc) = CacheRead (va, pa, pm, dc) state in
  let (i, t, wi) = lineSpec(va, pa) state  in
  let vlm = v2w(read_mem32(pa, pm)):word32 in
      invariant_cache ==>
      (~(Hit(va, pa, dc) state) ==> (vlm = v2w(vlc):word32))`,
  
    lrw []
    \\ xfs[CacheRead_def]
    \\ (CASE_TAC \\ CONV_TAC (ONCE_DEPTH_CONV PairedLambda.GEN_BETA_CONV))
    \\ PairedLambda.GEN_BETA_TAC
    \\ REPEAT STRIP_TAC
    \\ fs_lambda_elim[Once LET_DEF]
    \\ abr_lineSpec_tac_sgl
    \\ ASSUME_TAC(fill_dcEQpm_thm
       |> Q.ISPECL[`va:word64`,`pa:word48`,`(pm:(word48->word8))`,`(dc:(48 word->CSET))`,`(state:dharma8_state)`] 
       |> SIMP_RULE (srw_ss()) [LET_DEF]
       |> PairedLambda.GEN_BETA_RULE)
    \\ rfs[combinTheory.UPDATE_def]
    \\ line_size_lt_dimword15 ``w2n state.DC.ctr.DminLine``
    \\ THM_SPECL_ASSM "lineSpec" wi_lt_line_size_thm [`state`]
    \\ THM_KEEP_TAC ``invariant_cache`` (fs[invariant_cache_def])
    \\ qpat_assum `!i t w n m state. P` (qspecl_then [`i`, `t`, `wi`, `nl + 2`, `ns`, `state`] assume_tac)
    \\ ntac 3 (WEAKEN_TAC is_forall)
    \\ FULL_SIMP_TAC (arith_ss)[CellRead_def]
    \\ assume_tac(fill_pm'EQpm_diffIn_thm
       |> Q.SPECL [`va`,`pa`,`pm`,`dc`,`va`, `pa`, `(state:dharma8_state)`]
       |> SIMP_RULE (srw_ss())[LET_DEF]
       |> PairedLambda.GEN_BETA_RULE)
   \\ rfs[]
);

val CacheRead_dcEQpm_NotDirty_thm = Q.store_thm("CacheRead_dcEQpm_NotDirty_thm",
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state).
  let (_,_, vlc) = CacheRead(va, pa, pm, dc) state in
  let vlm = read_mem32(pa, pm) in 
  (invariant_cache) ==>
  (~lDirty(va, pa, dc) state) ==>  
  (v2w(vlc):word32 = v2w(vlm):word32)`,

    fs_lambda_elim[CacheRead_def, Touch_def, lDirty_def]
    \\ lrw[]
    >- (abr_lineSpec_tac_sgl
	\\ PAIR_SPLIT_TAC
	\\ assume_tac(coherency_axiom |> spec_let_elim [`i'`, `t'`, `wi'`, `dc`, `pm`, 
            `w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`, `w2n state.DC.ctr.DminLine`])          

	\\ THM_SPECL_ASSM "lineSpec" lineSpec_thm [`state`]
	\\ fs[]
	\\ rfs[CellRead_def]
       )
    \\ THM_SPECL_GOAL "Fill" cacheRead_miss_thm [``state:dharma8_state``]
    \\ fs_lambda_elim[CacheRead_def]
    \\ rfs[]
);

(* --------------------------------------------------------------------------------------------- *)
val cacheRead_hit_thm = Q.store_thm("cacheRead_hit_thm",
  `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state).
  let (dc', pm', vlc) = CacheRead (va, pa, pm, dc) state in
  let (i, t, wi) = lineSpec(va, pa) state in
  let vlc' = CellRead(i, t, wi, dc) in
      ((Hit(va, pa, dc) state) ==> (vlc' = v2w(vlc):word32))`,
  
   lrw []
   \\ xfs[CacheRead_def, CellRead_def]
   \\ (CASE_TAC \\ CONV_TAC (ONCE_DEPTH_CONV PairedLambda.GEN_BETA_CONV))
   \\ ntac 2 (fs[Once LET_DEF])
   \\ PairedLambda.GEN_BETA_TAC
   \\ fs[combinTheory.UPDATE_def, Touch_def]
);

(* --------------------------------------------------------------------------------------------- *)
val cacheWrite_setCell_thm = Q.store_thm("cacheWrite_setCell_thm",
 `!(va:word64) (pa:word48) (data:wrTyp) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state).
  let (dc', pm')= CacheWrite (va, pa, data, pm, dc) state in 
  let (i, t, wi) = lineSpec(va, pa) state  in
      ((THE ((dc' i).sl t)).dirty = data.flag) /\ 
      ((THE ((dc' i).sl t)).value (n2w wi) = data.value)`,

      lrw[]
   \\ fs[CacheWrite_def]
   \\ PairedLambda.GEN_BETA_TAC
   \\ rw[Touch_def, combinTheory.UPDATE_def]  
);

(* --------------------------------------------------------------------------------------------- *)
val linefill_hit_thm = Q.store_thm ("linefill_hit_t",
   `!(h:(actions # num # 48 word) list) i:(48 word) t:(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state) (n:num).
    let (sl, _) =  LineFill(h, i, t, pm, dc, n) state in 
     let sn = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
     let ln = (w2n state.DC.ctr.DminLine) in
     (!wi:num.
       let pa = (t << (sn + ln + 2)) !! (i << (ln + 2)) !! (n2w(wi):(48 word) << 2) in 
	   (IS_SOME(sl t))
     )`,

    xrw []
    \\ fs [LineFill_def,FOR_FOLDL, Abbr`pa`]
    \\ lrw[]
    \\ Induct_on `n`  
    THENL[lfs[EVAL ``COUNT_LIST 1``,  combinTheory.UPDATE_def],
          xfs [combinTheory.UPDATE_def]]
				     
);

val fill_hit_thm = Q.store_thm("fill_hit_thm",
  `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state).
    (let (dc', pm') =  Fill(va, pa, pm, dc) state in
     let (i, t, wi) = lineSpec(va, pa) state in    
      (* (IS_SOME((dc' i).sl t)) *)
      Hit(va, pa, dc') state
    )`,

   lrw []
   \\ NTAC 3 (xfs[Fill_def, Hit_def, Once LET_DEF])
   \\ PairedLambda.GEN_BETA_TAC
   \\ CASE_TAC

   THENL[ (fn (asl, g) => let val a::b::_ = find_terms is_fst g in
       (Q.ABBREV_TAC`t = ^a` \\ Q.ABBREV_TAC`i = ^b`)(asl, g) end)
   \\ fs_lambda_elim [LET_DEF]
   \\ fs[combinTheory.UPDATE_def]
   \\ assume_tac(linefill_hit_thm |> spec_let_elim [`((dc:(48 word -> CSET)) i).hist`, `i`, `t`, `pm`, `dc`, `state`, `2 ** w2n state.DC.ctr.DminLine − 1`])
   \\ rfs[],

      (fn (asl, g) => let val a::b::_ = find_terms is_fst g in
       (Q.ABBREV_TAC`t = ^a` \\ Q.ABBREV_TAC`i = ^b`)(asl, g) end)
   \\  CONV_TAC (ONCE_DEPTH_CONV (REWRITE_CONV [LET_DEF]))
   \\ PairedLambda.GEN_BETA_TAC
   \\ fs [combinTheory.UPDATE_def]
   \\ (fn (asl, g) => let val b = find_term is_abs  g   val a = find_term is_snd g in
       (Q.ABBREV_TAC`dc' = ^b` \\ Q.ABBREV_TAC`hist' = ^a`) (asl,g) end)
   \\ (fn (asl, g) => let val c = find_term is_writeBackLine  g in (Q.ABBREV_TAC`pm' = SND (^c state)`) (asl,g) end)
   \\ assume_tac(linefill_hit_thm 
       |> spec_let_elim [`hist'`, `i`, `t`, `pm'`, `dc'`, `state`, `2 ** w2n state.DC.ctr.DminLine − 1`])
   \\ rfs[]]
);



val cacheRead_paHitdc'_thm = Q.store_thm("cacheRead_paHitdc'_thm",
  `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state).
  let (dc', pm', _)= CacheRead(va, pa, pm, dc) state in 
        (Hit(va, pa, dc') state)`,

       lrw[]
    \\ fs[CacheRead_def]
    \\ PairedLambda.GEN_BETA_TAC
    \\ rw[Touch_def, combinTheory.UPDATE_def]  
    >- (fs[Hit_def] \\ schneiderUtils.UNDISCH_ALL_TAC \\ PairedLambda.GEN_BETA_TAC \\ fs[])

    \\ (fs[Hit_def] \\ schneiderUtils.UNDISCH_ALL_TAC \\ PairedLambda.GEN_BETA_TAC \\ fs[])
    \\ lrw[]
    \\ (fn (asl, g) => let val a::b::_ = find_terms is_fst g in (Q.ABBREV_TAC`t = ^a` \\ Q.ABBREV_TAC`i = ^b`)(asl, g) end)
    \\ assume_tac (fill_hit_thm |> spec_let_elim[`va`, `pa`, `pm`, `dc`, `state`] 
          |> SIMP_RULE(srw_ss())[LET_DEF, Hit_def] |> PairedLambda.GEN_BETA_RULE)
    \\ rfs[] 
);

val cacheWrite_paHitdc'_thm = Q.store_thm("cacheWrite_paHitdc'_thm",
  `!(va:word64) (pa:word48) (data:wrTyp) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state).
  let (dc', pm')= CacheWrite(va, pa, data, pm, dc) state in 
        (Hit(va, pa, dc') state)`,
       lrw[]
    \\ fs[CacheWrite_def]
    \\ PairedLambda.GEN_BETA_TAC
    \\ rw[Touch_def, combinTheory.UPDATE_def]  
    \\ EVERY[fs[Hit_def] \\ PairedLambda.GEN_BETA_TAC \\ PAIR_SPLIT_TAC \\ fs[]]);

(* --------------------------------------------------------------------------------------------- *)
val cacheWrite_paNOTCHGpm_thm = Q.store_thm("cacheWrite_paNOTCHGpm_thm",
 `!(va:word64) (pa:word48) (data:wrTyp) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state).
  let (dc', pm')= CacheWrite (va, pa, data, pm, dc) state in 
       invariant_cache ==>
       (v2w(read_mem32(pa, pm)):word32 = v2w(read_mem32(pa, pm')))`,

      lrw[]
    \\ fs[CacheWrite_def]
    \\ PairedLambda.GEN_BETA_TAC
    \\ rw[Touch_def, combinTheory.UPDATE_def]  
    \\ imp_res_tac (fill_pm'EQpm_diffIn_thm |> SIMP_RULE(srw_ss())[LET_DEF] |> PairedLambda.GEN_BETA_RULE)
    \\ qpat_assum `!x .P` (qspecl_then [`va`,`pm`, `pa`] assume_tac)
    \\ fs[]);

val cacheWrite_read_thm = Q.store_thm("cacheWrite_read_thm", 
  `!(va:word64) (pa:word48) (data:wrTyp) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:dharma8_state).
  let (dc', pm')= CacheWrite(va, pa, data, pm, dc) state in 
  let (a, b, vl)= CacheRead (va, pa, pm', dc') state in
       ((v2w vl:word32) = data.value)`,

       lrw[]
    \\ PairedLambda.GEN_BETA_TAC
    \\ fs[CacheRead_def]
    \\ PairedLambda.GEN_BETA_TAC
    \\ rw[Touch_def, combinTheory.UPDATE_def]  
    >- rfs[ (cacheWrite_setCell_thm 
          |> Q.ISPECL[`va:word64`, `pa:word48`, `data:wrTyp`, `pm:(word48->word8)`, `dc:(word48->CSET)`, `state:dharma8_state`]
	  |> SIMP_RULE (srw_ss()) [LET_DEF] |> PairedLambda.GEN_BETA_RULE)]
    \\ fs[(cacheWrite_paHitdc'_thm 
    |> Q.ISPECL[`va:word64`, `pa:word48`, `data:wrTyp`, `pm:(word48->word8)`, `dc:(48 word -> CSET)`, `state:dharma8_state`]
    |> SIMP_RULE(srw_ss()) [LET_DEF] |> PairedLambda.GEN_BETA_RULE)]
);

val cache_write_read_WB_thm = Q.store_thm("cache_write_read_WB_thm", 
  `!(va:word64) (pa:word48) data:bitstring  (mc:MEM_CONFIG) (pm:(word48->word8)) (dc:(48 word -> CSET)) (dirty:bool) state. 
   let (_,pm',dc') = write_cache(0w:word32, va, pa, data, mc, pm ,dc, dirty) state in 
   let (_, _, vl)  = read_cache(0w:word32, va, pa, pm', dc') state in 
     (LENGTH data = 32) ==>
     (v2w(data):word32  = v2w(vl))`,


    lrw[]
    \\ PairedLambda.GEN_BETA_TAC
    \\ fs[read_cache_def, write_cache_def]
    \\ PairedLambda.GEN_BETA_TAC
    \\ rw[combinTheory.UPDATE_def]  
    \\ (NTAC 4 (xfs [Once state_transformerTheory.FOR_def, state_transformerTheory.BIND_DEF]))
    \\ (fn (asl, g) => let val rc = find_term TypeBase.is_record g in (
           assume_tac (cacheWrite_read_thm
              |> Q.ISPECL[`va:word64`, `pa:word48`, `^rc`, `pm:(word48->word8)`, `dc:(word48->CSET)`, `state:dharma8_state`]
	      |> SIMP_RULE(srw_ss())[LET_DEF]
	      |> PairedLambda.GEN_BETA_RULE)
       ) (asl, g) end)
   \\ rfs[(field_id_imp |> Q.ISPECL [`31n`, `data:bitstring`])]
   \\ CASE_TAC
   \\ PAIR_SPLIT_TAC
   \\ lfs[field_def]
   \\ fs[(v2w_fixwidth 
       |> INST_TYPE [alpha |-> ``:32``]
       |> Q.ISPECL[`(shiftr (SND (r:(word48 -> word8) # bitstring)) (0 :num))`]
       |> SIMP_RULE (srw_ss())[]) , shiftr_0]
);

val cache_write_read_WT_thm = Q.store_thm("cache_write_read_WT_thm", 
  `!(va:word64) (pa:word48) data:bitstring  (mc:MEM_CONFIG) (pm:(word48->word8)) (dc:(48 word -> CSET)) (dirty:bool) state. 
   let (mc',pm',dc') = write_cache(0w:word32, va, pa, data, mc, pm ,dc, dirty) state in 
   let (_, pm'') = write_mem(0w:word32, pa, data, mc', pm') in 
   let (_, _, vl)  = read_cache(0w:word32, va, pa, pm'', dc') state in 
     (LENGTH data = 32) ==>
     (v2w(data):word32  = v2w(vl))`,

    lrw[]
    \\ PairedLambda.GEN_BETA_TAC
    \\ fs_lambda_elim[read_cache_def, write_cache_def, write_mem_def]
    \\ rw[combinTheory.UPDATE_def] 
    \\ ntac 2 (ntac 4 (xfs [Once state_transformerTheory.FOR_def, state_transformerTheory.BIND_DEF]))
    \\ (fn (asl, g) => let val rc = find_term TypeBase.is_record g
        in assume_tac(cacheWrite_paHitdc'_thm |> Q.SPECL[`va`, `pa`, `^rc`, `pm`, `dc`, `state`] |> LET_ELIM_RULE) (asl, g) end)
    \\ fs_lambda_elim [CacheRead_def]
    \\ fs[combinTheory.UPDATE_def, Touch_def]  
    \\ (fn (asl, g) => let val rc = find_term TypeBase.is_record g
        in assume_tac (cacheWrite_read_thm  |> Q.SPECL[`va`, `pa`, `^rc`, `pm`, `dc`, `state`] |> LET_ELIM_RULE) (asl, g) end)
    \\ schneiderUtils.UNDISCH_HD_TAC
    \\ fs_lambda_elim[CacheRead_def]
    \\ fs[combinTheory.UPDATE_def, Touch_def, (field_id_imp |> Q.ISPECL [`31n`, `data:bitstring`])]
);


val cache_writeReq_readReq_thm = Q.store_thm("cache_writeReq_readReq_thm",
  `!size (cbl:word2) (va:word64) (pa:word48) (data:bitstring) (ms:MEM_SYSTEM) (state:dharma8_state).
   let ms'    = writeReq(size, cbl, va, pa, data, ms) state in
   let (_,vl) = readReq (size, cbl, va, pa, ms') state in
     (size = 4n) ==>
     (LENGTH data = 32) ==>
     (v2w(data):word32  = v2w(vl))`,

       lrw[]
    \\ PairedLambda.GEN_BETA_TAC
    \\ fs_lambda_elim[writeReq_def, readReq_def]
    \\ rw[combinTheory.UPDATE_def]
    >- (imp_res_tac (cache_write_read_WB_thm |> LET_ELIM_RULE)
     \\ qpat_assum`!x.P`(qspecl_then[`va`, `state`, `ms.PM`, `pa`, `ms.MC`, `T`, `ms.CACHE`]assume_tac)
     \\ fs[])
    >-(imp_res_tac (cache_write_read_WT_thm |> LET_ELIM_RULE)
     \\ qpat_assum`!x.P`(qspecl_then[`va`, `state`, `ms.PM`, `pa`, `ms.MC`, `F`, `ms.CACHE`]assume_tac)
     \\ fs[])
    \\ fs[read_mem32_thm, write_mem32_thm2 |> spec_let_elim [`0w:word32`,`pa`, `data`, `ms.MC`, `ms.PM`],
              write_read_thm |> spec_let_elim [`pa`, `v2w data:word32`, `ms.PM`]]
);
    
val writeReq_NOTCHGconfigS_thm = Q.store_thm("writeReq_NOTCHGconfigS_thm", 
  `!size (cbl:word2) (va:word64) (pa:word48) (data:bitstring) (ms:MEM_SYSTEM) (state:dharma8_state).
   let ms' = writeReq (size, cbl, va, pa, data, ms) state in 
      (size = 4n) ==>
      (ms.MC.S = ms'.MC.S)`,

       lrw[]
    \\ fs_lambda_elim[writeReq_def]
    \\ rw[combinTheory.UPDATE_def]  
    \\ EVERY[ntac 5 (fs_lambda_elim[write_cache_def, write_mem_def, Once state_transformerTheory.FOR_def, state_transformerTheory.BIND_DEF])]
);

(* --------------------------------------------------------------------------------------------- *)
(* val () = export_theory () *)
