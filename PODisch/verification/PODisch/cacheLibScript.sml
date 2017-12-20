open HolKernel boolLib bossLib Parse;
open wordsTheory wordsLib wordsSyntax;
open cutilsLib cacheTheory arm_stepTheory;

val _ = new_theory "CacheLib"


val invariant_cache_def = Define `
  invariant_cache  (* (C:CORE_CONFIG) *) =
    (* (C.SCTLR_EL2.C = T) /\ *)
    (* (C.HCR_EL2.DC  = T) /\ *)
    (!pa:word48. pa && 0xFFFFFFFFFFFCw = pa) /\
    (!(i: 48 word) (t: 48 word) (wi:num) ni nt state.
     let MSB  =  ((0xffffffffffffw:word48) >>> ni) in
     let LSB  = ~((0xffffffffffffw:word48) >>> ni << ni) in
     let MSB2 =  ((0xffffffffffffw:word48) >>> (ni + nt)) in
     let LSB2 =  ((0xffffffffffffw:word48) << (48 - (ni + nt)) >>> (48 - nt)) in
     (state.DC.ctr.DminLine >= 1w) /\
     (state.DC.ccsidr.NumSets >= 1w) /\ 
     (ni < 48 - nt) /\ (t && MSB2 = t) /\ (i && LSB2 = i) /\ 
     (((t << nt) !! i) && MSB = (t << nt) !! i) /\  (n2w(wi):word48 << 2 && LSB = n2w(wi):word48 << 2)) /\
      
    (!s s'. (s.DC.ctr.DminLine = s'.DC.ctr.DminLine) /\ (s.DC.ccsidr.NumSets = s'.DC.ccsidr.NumSets) ) /\
    (* If EP returns a tag, it should be present in the cache, Hit *)
    (!h i t dc x. (EP(h, t, dc) = SOME x) ==> (IS_SOME ((dc (i)).sl (x)))) 

`;

(* --------------------------------------------------------------------------------------------- *)

val lt_mod_thm = Q.store_thm("lt_mod_thm",
 `!a b c d. ((a < b) /\ (b <= c) /\ (c < d)) ==> ((a MOD d) < (b MOD d))`,
     fs []);

val adr_segNeq_thm = Q.prove(
 `!(a:word48) (b:word48) (c:word48) (n:num) (m:num). 
   (((b << (n+m)) !! (a << m) ) <>  ((c << (n+m)) !! (a << m))) ==>
    (b <> c)`, fs []);

val adr_neq3_thm = Q.store_thm("adr_neq3_thm",
  `!(a:word48) (b:word48) (c:word48) (n:num). 
   let bmM = ((0xffffffffffffw:word48) >>> n) in
   let bmL = ~((0xffffffffffffw:word48) >>> n << n) in
   ((n < 48)) ==>  
   ((a && bmL = a) /\ (b && bmM = b) /\ (c && bmM = c)) ==> 
   (((b << n) !! a) <> ((c << n) !! a)) ==>
    (b <> c) `,

     rpt strip_tac
  \\ ntac 48 (FIRST[Cases_on `n`, Cases_on `n'`]
  >- (EVAL_TAC \\ blastLib.BBLAST_PROVE_TAC))
  \\ fs[]
);


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

(* --------------------------------------------------------------------------------------------- *)

(* To prove that line  size is less that 2 ** 15 *)
fun line_size_lt_dimword15 nl =
      `2 ** ^nl ≤ 32769` by (all_tac
    \\ assume_tac(Drule.ISPECL[``(state :cache_state).DC.ctr.DminLine``](w2n_lt) |> SIMP_RULE(srw_ss())[])
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

val wrtBck_dirtybit_thm = Q.store_thm("wrtBck_dirty_thm",
    `!i:(48 word) t:(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) (n:num) (state:cache_state). 
    (let (dc', pm') =  WriteBackLine(i, t, pm, dc, n) state in 
     ((n <= dimword(:15)) ==>
       (!wi:num. (wi <= n) ==> (~LineDirty(i, t,  dc')) )))`,
      
        lrw[]
     \\ lfs [WriteBackLine_def, Once LET_DEF, FOR_FOLDL]
     \\ (EVAL_TAC \\ fs[LET_DEF, LineDirty_def, WriteBack_def, combinTheory.UPDATE_def])
);

(* --------------------------------------------------------------------------------------------- *)

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
      \\ assume_tac(SPECL[``(state :cache_state).DC.ctr.DminLine``](INST_TYPE[alpha |-> ``:4``]w2n_lt) |> SIMP_RULE(srw_ss())[])
      \\ `ln' + 2 < 48` by decide_tac
      \\ rfs[]
);

val wrtBck_memory_thm = Q.store_thm("wrtBck_memory_thm",
 `!i:(48 word) t:(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state) (n:num).
    (let (dc', pm') =  WriteBackLine(i, t, pm, dc, n) state in
     let sn = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
     let ln = (w2n state.DC.ctr.DminLine) in
     (n <= dimword(:15) ==> (!wi:num. wi <= n ==>
          let pa = ((t << (sn + ln + 2)) !! (i << (ln + 2)) !! (n2w(wi):(48 word) << 2)) in
           (invariant_cache) ==>
           (LineDirty(i,t, dc)) ==>
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
      \\ qpat_assum `∀s:cache_state s':cache_state. P` (qspecl_then[`(SND (SND (SND (SND abr))))`,`state`] assume_tac)
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


       (* \\ assume_tac (coherency_axiom |> spec_let_elim[`i`, `t`, `wi`, `dc`, `pm`, `sn`, `ln'`]) *)
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
   `!i:(48 word) t:(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state) (n:num).
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
    `!i:(48 word) t:(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state) (n:num).
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
  `!i:(48 word) t:(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) n (state:cache_state).
    (let (dc', pm') =  WriteBackLine(i, t, pm, dc, n) state in
     let sn = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
     let ln = (w2n state.DC.ctr.DminLine) in
     (n <= dimword(:15) ==> (!wi:num. wi <= n ==>
          let pa = ((t << (sn + ln + 2)) !! (i << (ln + 2)) !! (n2w(wi):(48 word) << 2)) in
           (invariant_cache) ==>
           (LineDirty(i,t,dc)) ==>
	   (CellRead(i, t, wi, dc) = v2w(read_mem32(pa, pm')))
     )))`,

    xrw[]
    \\ imp_res_tac (wrtBck_memory_thm |> SIMP_RULE(srw_ss())[LET_DEF] |> PairedLambda.GEN_BETA_RULE)
    \\ qpat_assum`!x. P`(qspecl_then[`state`, `pm`] assume_tac)
    \\ REABBREV_TAC

    \\ imp_res_tac (WriteBackLine_CellRead_dcEQdc'_thm |> SIMP_RULE(srw_ss())[LET_DEF] |> PairedLambda.GEN_BETA_RULE)
    \\ qpat_assum`!x. P`(qspecl_then[`t`, `state`, `pm`, `i`, `dc`] assume_tac)
    \\ rfs[]
);

val WriteBackLine_Dont_change_Mem_IfNotDirty_thm = Q.prove(
   `!(i:word48) (t:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state) n.
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
   `!(i:word48) (t:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) n (state:cache_state).
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
 `! (pa:word48) (state:cache_state).
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
    \\ THM_SPECL_GOAL "wIdx" wIdx_extract_thm [``state:cache_state``]
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
 `!(va:word64) (pa:word48) (state:cache_state).
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
  `!(va:word64) (pa:word48) (state:cache_state).
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
  `!(va:word64) (pa:word48) (state:cache_state).
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

    \\ assume_tac(SPECL[``(state :cache_state).DC.ctr.DminLine``](INST_TYPE[alpha |->``:4``]w2n_lt) 
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
    \\ SUBGOAL_THEN ``w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) ≥ 1`` (fn thm => assume_tac thm)
    >- (xfs[] >> UNDISCH_MATCH_TAC``word_log2 (state.DC.ccsidr.NumSets + 1w) ≥ 1w`` >> fs[WORD_GE])
    \\ `2 ≤ ns + 1` by rfs[]
    \\ lfs[]
    \\ UNDISCH_MATCH_TAC``a || b = c``
    \\ UNDISCH_MATCH_TAC``a || b = c << (d + 2)``
    \\ UNDISCH_MATCH_TAC``a && pa = pa``
    \\ blastLib.BBLAST_PROVE_TAC
);

val lineSpecEq_thm = Q.prove(
`!(va:word64) (pa:word48) (va':word64)  state.
   lineSpec(va, pa) state = lineSpec(va', pa) state`,

   fs_lambda_elim[lineSpec_def, si_def, tag_def, wIdx_def]
);

(* --------------------------------------------------------------------------------------------- *)
val fill_dcEQpm_thm = Q.store_thm("fill_dcEQpm_thm",
   `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state).
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
                  `(dc:(48 word -> CSET))`, `2 ** w2n state.DC.ctr.DminLine − 1`, `state:cache_state`]
      |> SIMP_RULE(srw_ss())[LET_DEF] 
      |> PairedLambda.GEN_BETA_RULE)
   \\ rfs[]
   \\ PAT_ASSUM``!(wi:num). x`` (fn thm => ASSUME_TAC(SPECL[``wi:num``] thm))
   \\ THM_KEEP_TAC ``invariant_cache`` (fs[invariant_cache_def])
   \\ qpat_assum `!p:word48. P` (qspecl_then [`pa`] ASSUME_TAC)
   \\ ASSUME_TAC(lineSpec_thm
      |> Q.ISPECL[`va:word64`,`pa:word48`,`state:cache_state`]
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
                  `(dc':(48 word -> CSET))`, `2 ** w2n state.DC.ctr.DminLine − 1`,`state:cache_state`]
      |> SIMP_RULE(srw_ss())[LET_DEF] 
      |> PairedLambda.GEN_BETA_RULE)
   \\ rfs []
   \\ PAT_ASSUM``!(wi:num). x`` (fn thm => ASSUME_TAC(SPECL[``wi:num``] thm))
   \\ THM_KEEP_TAC ``invariant_cache`` (fs[invariant_cache_def])
   \\ qpat_assum `!p:word48. P` (qspecl_then [`pa`] ASSUME_TAC)
   \\ ASSUME_TAC(lineSpec_thm
      |> Q.ISPECL[`va:word64`,`pa:word48`,`state:cache_state`]
      |> SIMP_RULE(srw_ss()) [LET_DEF]
      |> PairedLambda.GEN_BETA_RULE)
   \\ REABBREV_TAC
   \\ FULL_SIMP_TAC (arith_ss) []
]);

(* --------------------------------------------------------------------------------------------- *)
val shift_add_thm = Q.store_thm("shift_add_thm",
`!w1:(word48) w2 n m. ((w1 << (n + m)) !! (w2 << m)) = (((w1 << n) !! w2) << m)`,
fs[]);

val writeback_mem_eq_thm = Q.store_thm ("writeback_mem_eq_thm",
  `!(pa:word48) (va:word64) (pm:(word48->word8)) (slval:SLVAL) (state:cache_state) i':(48 word) t':(48 word) wi'.
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
 	     |> Q.ISPECL[`va:word64`,`pa:word48`,`state:cache_state`]
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
  \\ qpat_assum `!s:cache_state a'. P` (qspecl_then [`s`, `s'`] ASSUME_TAC)
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
                  \\ qpat_assum `!s:cache_state s'. P` (qspecl_then[`state`, `^trm`] assume_tac)
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
       [``va':word64``,``pa':word48``,``state:cache_state``]
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
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:cache_state).
    (let (dc', pm')    =  CacheCleanByAdr(va, pa, pm, dc) state in
     let (i', t', wi') = lineSpec(va', pa') state in
     let (i, t, wi)    = lineSpec(va, pa) state in
     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
     let nl = (w2n state.DC.ctr.DminLine) in
     (Hit (va,pa,dc) state) ==>
     ((invariant_cache) ==>
     (LineDirty(i',t', dc)) ==>
      ((((t' << ns) !! i') << (nl + 2n)) = ((t << ns) !! i) << (nl + 2n)) ==>
	   (CellRead(i', t', wi', dc) = v2w(read_mem32(pa', pm')))
     ))`,
     
    fs_lambda_elim[CacheCleanByAdr_def]
    \\ lrw[]
    \\ abr_lineSpec_tac_sgl
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`

    \\ THM_SPECL_GOAL "WriteBackLine" wrtBckLine_dcEQpm'_thm [``state:cache_state``]
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
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:cache_state).
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
    \\ THM_SPECL_GOAL "WriteBackLine" writBckLine_NotchgTag'_thm [``t':word48``, ``state:cache_state``]
    \\ line_size_lt_dimword15``w2n state.DC.ctr.DminLine``    
    \\ fs[]

in
val CacheClean_dcEQdc'_diffMsb_thm = Q.store_thm("CacheClean_dcEQdc'_diffMsb_thm",
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:cache_state).
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
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:cache_state).
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
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:cache_state).
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
`!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:cache_state).
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
    \\ THM_SPECL_GOAL "WriteBackLine" writebackline_mem_eq_thm [``va':word64``, ``pa':word48``, ``state:cache_state``]
    \\ line_size_lt_dimword15``w2n state.DC.ctr.DminLine``
    \\ rfs[]
);

val CacheInvalidate_dcEQpm'_thm = Q.store_thm("CacheInvalidate_dcEQpm'_thm",
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:cache_state).
    (let (dc', pm')    =  CacheInvalidateByAdr(va, pa, pm, dc) state in
     let (i, t, wi)    = lineSpec(va, pa) state in
     let (i', t', wi') = lineSpec(va', pa') state in
     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
     let nl = (w2n state.DC.ctr.DminLine) in
     (Hit (va,pa,dc) state) ==>
     ((invariant_cache) ==>
      (LineDirty(i', t', dc)) ==> 
      ((((t' << ns) !! i') << (nl + 2n)) = ((t << ns) !! i) << (nl + 2n)) ==>
	   (CellRead(i', t', wi', dc) = v2w(read_mem32(pa', pm')))
     ))`,
     
    fs_lambda_elim[CacheInvalidateByAdr_def]
    \\ lrw[]
    \\ abr_lineSpec_tac_sgl
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ THM_SPECL_GOAL "WriteBackLine" wrtBckLine_dcEQpm'_thm [``state:cache_state``]
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
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state).
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
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:cache_state).
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
`! (va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:cache_state).
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
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:cache_state).
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
`!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) va' pa' (state:cache_state).
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
    \\ THM_SPECL_GOAL "WriteBackLine" writebackline_mem_eq_thm [``va':word64``, ``pa':word48``, ``state:cache_state``]
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
  `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state).
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
       |> Q.ISPECL[`va:word64`,`pa:word48`,`(pm:(word48->word8))`,`(dc:(48 word->CSET))`,`(state:cache_state)`] 
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
       |> Q.SPECL [`va`,`pa`,`pm`,`dc`,`va`, `pa`, `(state:cache_state)`]
       |> SIMP_RULE (srw_ss())[LET_DEF]
       |> PairedLambda.GEN_BETA_RULE)
   \\ rfs[]
);

(* --------------------------------------------------------------------------------------------- *)
val cacheRead_hit_thm = Q.store_thm("cacheRead_hit_thm",
  `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state).
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
 `!(va:word64) (pa:word48) (data:wrTyp) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state).
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
   `!(h:(actions # num # 48 word) list) i:(48 word) t:(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state) (n:num).
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
  `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state).
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
  `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state).
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
  `!(va:word64) (pa:word48) (data:wrTyp) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state).
  let (dc', pm')= CacheWrite(va, pa, data, pm, dc) state in 
        (Hit(va, pa, dc') state)`,
       lrw[]
    \\ fs[CacheWrite_def]
    \\ PairedLambda.GEN_BETA_TAC
    \\ rw[Touch_def, combinTheory.UPDATE_def]  
    \\ EVERY[fs[Hit_def] \\ PairedLambda.GEN_BETA_TAC \\ PAIR_SPLIT_TAC \\ fs[]]);

(* --------------------------------------------------------------------------------------------- *)
val cacheWrite_paNOTCHGpm_thm = Q.store_thm("cacheWrite_paNOTCHGpm_thm",
 `!(va:word64) (pa:word48) (data:wrTyp) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state).
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
  `!(va:word64) (pa:word48) (data:wrTyp) (pm:(word48->word8)) (dc:(48 word -> CSET)) (state:cache_state).
  let (dc', pm')= CacheWrite(va, pa, data, pm, dc) state in 
  let (a, b, vl)= CacheRead (va, pa, pm', dc') state in
       ((v2w vl:word32) = data.value)`,

       lrw[]
    \\ PairedLambda.GEN_BETA_TAC
    \\ fs[CacheRead_def]
    \\ PairedLambda.GEN_BETA_TAC
    \\ rw[Touch_def, combinTheory.UPDATE_def]  
    >- rfs[ (cacheWrite_setCell_thm 
          |> Q.ISPECL[`va:word64`, `pa:word48`, `data:wrTyp`, `pm:(word48->word8)`, `dc:(word48->CSET)`, `state:cache_state`]
	  |> SIMP_RULE (srw_ss()) [LET_DEF] |> PairedLambda.GEN_BETA_RULE)]
    \\ fs[(cacheWrite_paHitdc'_thm 
    |> Q.ISPECL[`va:word64`, `pa:word48`, `data:wrTyp`, `pm:(word48->word8)`, `dc:(48 word -> CSET)`, `state:cache_state`]
    |> SIMP_RULE(srw_ss()) [LET_DEF] |> PairedLambda.GEN_BETA_RULE)]
);

(* --------------------------------------------------------------------------------------------- *)

val CacheRead_vaEQva'_thm = Q.prove(
`!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (va':word64) state. 
      CacheRead (va, pa, pm, dc) state = CacheRead (va', pa, pm, dc) state`,
   
        fs_lambda_elim[CacheRead_def, Touch_def, combinTheory.UPDATE_def, Hit_def, Fill_def]
     \\ lrw[]
     \\ THM_SPECL_ASSM "lineSpec" lineSpecEq_thm [`va'`, `state`]
     \\ fs[]
     \\ EVERY[rfs[]]
);

val CacheRead_lfoldEQval_SameAddress_thm = Q.store_thm("CacheRead_lfoldEQval_SameAddress_thm",
  `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) state.
  let (dc',pm', vlc) = CacheRead (va, pa, pm, dc) state in
  let (_, _, vlc') = CacheRead (va, pa, pm', dc') state in
     (vlc = vlc')`,

       lrw[]
    \\ PairedLambda.GEN_BETA_TAC
    \\ assume_tac(cacheRead_paHitdc'_thm |> spec_let_elim[`va`, `pa`, `pm`, `dc`, `state`])
    \\ fs_lambda_elim[CacheRead_def, Touch_def, combinTheory.UPDATE_def]
    \\ rw[]
);


val CacheRead_KeepHit_if_PaHitDc_thm = Q.prove(
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (va':word64) (pa':word48) state.
  let (dc',pm')   = CacheRead (va, pa, pm, dc) state in
  let (i,t,wi)    = lineSpec(va, pa) state      in
  let (i',t',wi') = lineSpec(va', pa') state    in
    (Hit(va, pa, dc) state)  ==>
    (Hit(va', pa', dc) state)  ==>
    (Hit(va', pa', dc') state)`,

   fs_lambda_elim[CacheRead_def, combinTheory.UPDATE_def, Touch_def, Hit_def]
   \\ lrw[]);

val Fill_KeepHit_if_iNOTEQi'_thm = Q.prove(
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (va':word64) (pa':word48) state.
  let (dc',pm')   = Fill (va, pa, pm, dc) state in
  let (i,t,wi)    = lineSpec(va, pa) state      in
  let (i',t',wi') = lineSpec(va', pa') state    in
    (i <> i') ==>
    (~Hit(va, pa, dc) state)  ==>
    (Hit(va', pa', dc) state)  ==>
    (Hit(va', pa', dc') state)`,

   fs_lambda_elim[Fill_def, Hit_def, combinTheory.UPDATE_def]
   \\ lrw[]
   \\ abr_lineSpec_tac_dubl
   \\ (fn (asl, g) => let val c = find_term wordsSyntax.is_w2n  g in (Q.ABBREV_TAC`nl = (^c)`) (asl,g) end)
   \\ (CASE_TAC >> fs[])
   \\ assume_tac(writBckLine_NotchgSidx'_thm |> spec_let_elim [`i`, `i'`, `x`, `t'`, `pm`, `dc`, `state`, `2 ** nl − 1`])
   \\ line_size_lt_dimword15 ``nl:num``
   \\ rfs[]
   \\ SYM_ASSUMPTION_TAC``a = b``
   \\ fs[]
);

val EPNotEqNONE_impEvict_thm = Q.prove(
  `!(va:word64) (pa:word48)  (pm:(word48->word8)) (dc:(48 word -> CSET))  (va':word64) (pa':word48) state.
  let (dc',pm')   = Fill (va, pa, pm, dc) state in
  let (i,t,wi)    = lineSpec(va, pa) state      in
  let (i',t',wi') = lineSpec(va', pa') state    in
    (i = i') ==>
    (~Hit(va, pa, dc) state)  ==>
    (Hit(va', pa', dc) state)  ==>
    (~Hit(va', pa', dc') state)  ==>
    (EP ((dc i).hist,t,dc) <> NONE)`,

      fs_lambda_elim[Fill_def,  Hit_def, combinTheory.UPDATE_def]
   \\ lrw[]
   \\ FIRST_ASSUM(fn thm => let val c = find_term wordsSyntax.is_w2n (concl thm) in Q.ABBREV_TAC`nl = ^c` end)
   \\ abr_lineSpec_tac_sgl
   \\ strip_tac
   \\ fs[]
   \\ UNDISCH_MATCH_TAC``FST(x) y = NONE``
   \\ mk_subgoal_then ``T`` ``2 ** nl − 1``
   >-(fs_lambda_elim[LineFill_def, CellFill_def, combinTheory.UPDATE_def, FOR_FOLDL]
     \\ CASE_TAC
     \\ Induct
     >-(EVAL_TAC >> CCONTR_TAC >> fs[])
     \\ fs[DECIDE``SUC n = n + 1``, FOR_FOLDL]
     \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
     \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]])
   \\ qpat_assum`!a. P` (qspecl_then[`n`] assume_tac)
   \\ fs[]
);

val Fill_NotchgTag'_thm = Q.prove(
  `!(va:word64) (pa:word48)  (pm:(word48->word8)) (dc:(48 word -> CSET)) n (va':word64) (pa':word48) state.
  let (i, t, wi)  = lineSpec(va, pa) state                       in
  let (i',t',wi') = lineSpec(va', pa') state                     in
  let (sl, _)   = LineFill ((dc i).hist, i, t, pm, dc, n) state  in
    (i = i') ==>
    (t <> t') ==>
    (invariant_cache) ==>
    (IS_SOME (sl t')) ==>
    (IS_SOME ((dc i').sl t')) ==>
      ((THE(sl t')).value (n2w wi') = (THE((dc i').sl t')).value (n2w wi'))`,


    lrw[]
    \\ PairedLambda.GEN_BETA_TAC
    \\ abr_lineSpec_tac_dubl
    \\ xrw []
    \\ simp[LineFill_def, CellFill_def, combinTheory.UPDATE_def, FOR_FOLDL]
    \\ PairedLambda.GEN_BETA_TAC
    \\ Induct_on `n`
    >-(EVAL_TAC >> fs[])
    \\ SUBGOAL_THEN``IS_SOME (FST (LineFill ((dc i).hist,i,t,pm,dc,n) state) t')`` (fn thm => assume_tac thm)
    >-  (WEAKEN_TAC is_imp
        \\ simp[LineFill_def, CellFill_def, combinTheory.UPDATE_def, FOR_FOLDL]
        \\ PairedLambda.GEN_BETA_TAC
        \\ Induct_on `n`
        >-(EVAL_TAC >> fs[])
        \\ fs[DECIDE``SUC n = n + 1``]
        \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
        			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
        			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
        
        \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]])
    \\ fs[DECIDE``SUC n = n + 1``]
    \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
    \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]]);

val Fill_NotchgHitDC'Tag_thm = Q.prove(
  `!(va:word64) (pa:word48) (va':word64) (pa':word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (x:word48) state.
  let (dc',pm')   = Fill (va, pa, pm, dc) state in
  let (i,t,wi)    = lineSpec(va, pa) state      in
  let (i',t',wi') = lineSpec(va', pa') state    in
    (i = i') ==>
    (~Hit(va, pa, dc) state)  ==>
    (IS_SOME ((dc i).sl t'))  ==>
    (IS_SOME ((dc' i).sl t')) ==>
    (EP ((dc i).hist,t,dc) = SOME x) ==>
         (t' <> x)`,

   rw[Fill_def, combinTheory.UPDATE_def]
   \\ PairedLambda.GEN_BETA_TAC
   \\ abr_lineSpec_tac_dubl
   \\ (CASE_TAC \\ (rw[] \\ fs[])) 
   \\ UNDISCH_MATCH_TAC``IS_SOME(x)``
   \\ (fn (asl, g) => let val c = find_term is_writeBackLine  g in (Q.ABBREV_TAC`wbs' = (^c state)`) (asl,g) end)
   \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
   \\ abr_tac_goal is_snd "h'" NONE
   \\ abr_tac_goal is_pabs "proc" NONE
   \\ mk_subgoal_then ``T`` ``2 ** nl − 1``
   >- (Induct
   >- (fs[LineFill_def, combinTheory.UPDATE_def, FOR_FOLDL, EVAL ``COUNT_LIST 1``, Hit_def]
       \\ UNDISCH_MATCH_TAC``~(λ(x,y,z). IS_SOME (f)) (g)``
       \\ fs_lambda_elim []
       \\ lrw[Abbr`proc`, Evict_def, combinTheory.UPDATE_def]
       \\ fs[])

   \\ schneiderUtils.UNDISCH_HD_TAC
   \\ simp[LineFill_def, combinTheory.UPDATE_def]
   \\ CASE_TAC 
      >- (fs[Hit_def]
      \\ UNDISCH_MATCH_TAC``~(λ(x,y,z). IS_SOME (f)) (g)``
      \\ PairedLambda.GEN_BETA_TAC
      \\ lrw[] \\ fs[]) 
   \\ strip_tac
   \\ fs[DECIDE``SUC n = n + 1``, FOR_FOLDL]
   \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
   \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]])
   \\ qpat_assum`!a. P` (qspecl_then[`2 ** nl − 1`] assume_tac)
   \\ PAIR_SPLIT_TAC
   \\ fs[]
);

val thm1 = Q.prove(
  `!(va:word64) (pa:word48) (va':word64) (pa':word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) state.
  let (dc',pm')   = Fill (va, pa, pm, dc) state           in
  let (i, t, wi)  = lineSpec(va, pa) state                in
  let (i',t',wi') = lineSpec(va', pa') state              in
  let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in 
  let nl = (w2n state.DC.ctr.DminLine)                    in     
    (invariant_cache) ==>
    (~Hit (va,pa,dc) state) ==>
    (Hit (va',pa',dc) state) ==>
    (Hit (va',pa',dc') state) ==>
    ((((t' << ns) !! i') << (nl + 2n)) <> ((t << ns) !! i) << (nl + 2n)) ==>
         (CellRead(i', t', wi', dc) = CellRead(i', t', wi', dc'))`,

        xrw [] 
    \\ (PAIR_SPLIT_TAC >> fs[])
    \\ SYM_ASSUMPTION_TAC``FST(x) = dc':(48 word -> CSET)``
    \\ simp[CellRead_def, Fill_def, Hit_def, LET_DEF, combinTheory.UPDATE_def]
    \\ PairedLambda.GEN_BETA_TAC
    \\ CASE_TAC
    >- ((PAIR_SPLIT_TAC >> fs[])
	\\ (CASE_TAC >> fs[])
	\\ SUBGOAL_THEN ``(t:word48) <> t'`` (fn thm => assume_tac thm)
        >- (assume_tac(adr_segNeq_thm |> spec_let_elim [`i'`, `t`, `t'`, `ns`, `(nl + 2)`]) >> rfs[])
        \\ THM_SPECL_ASSM "Fill" Fill_NotchgTag'_thm [`2 ** nl − 1`, `va'`, `pa'`, `state`]
	\\ rfs[Hit_def]
	\\ PAIR_SPLIT_TAC
	\\ rfs[]
        \\ PAT_ASSUM ``a==>b``(fn thm => let val t = (fst o dest_imp o concl) thm in 
            assume_tac thm >> `^t` by all_tac end)
	>- (UNDISCH_MATCH_TAC``IS_SOME(x)``
            \\ (fs_lambda_elim [Fill_def, Hit_def, LET_DEF, combinTheory.UPDATE_def] >> fs[]))
	\\ fs[])
    (* ______________________________________________ *)
    \\ (PAIR_SPLIT_TAC >> fs[])
    \\ CASE_TAC

    >- (assume_tac(Fill_NotchgHitDC'Tag_thm |>  spec_let_elim[`va`, `pa`, `va'`, `pa'`, `pm`, `dc`, `x`, `state`])
    \\ rfs[]
    \\ `t' ≠ x` by (fs[Hit_def] >> undisch_all_tac \\ PairedLambda.GEN_BETA_TAC \\ lrw[])

    \\ PAIR_SPLIT_TAC \\ fs[]
    \\ abr_tac_goal is_abs "dc''" NONE
    \\ abr_tac_goal is_snd "hist'" NONE
    \\ abr_tac_goal is_snd "pm''" NONE
    \\ mk_subgoal_then ``T`` ``2 ** nl − 1``
   >- (fs[LineFill_def, combinTheory.UPDATE_def]
      \\ CASE_TAC \\ fs[]

      \\ Induct

      >-(EVAL_TAC
         \\ fs[Abbr `dc''`, Evict_def, combinTheory.UPDATE_def]
	 \\ THM_SPECL_ASSM "WriteBackLine" writBckLine_NotchgTag'_thm [`t'`, `state`]
	 \\ line_size_lt_dimword15 ``nl:num``
	 \\ fs[])

      \\ fs[DECIDE``SUC n = n + 1``, FOR_FOLDL]
      \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
      \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]])
      \\ qpat_assum`!a. P` (qspecl_then[`2 ** nl − 1`] assume_tac)
      \\ fs[])

      \\ assume_tac(writBckLine_NotchgSidx'_thm 
         |> spec_let_elim [`i`, `i'`, `x`, `t'`, `pm`, `dc`, `state`, `2 ** nl − 1`])
      \\ line_size_lt_dimword15 ``nl:num``
      \\ fs[]
);

val Fill_someEPevict_dcEQpm'_thm = Q.store_thm("Fill_someEPevict_dcEQpm'_thm",
  `!(va:word64) (pa:word48) (va':word64) (pa':word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (x:word48) (state).
  let (dc',pm')   = Fill (va, pa, pm, dc) state           in
  let (i, t, wi)  = lineSpec(va, pa) state                in
  let (i',t',wi') = lineSpec(va', pa') state              in
  let nl = (w2n state.DC.ctr.DminLine)                    in 
     LineDirty (i',t',dc) ⇒                   
    (pa <> pa') /\ (i' = i) ==> 
    (invariant_cache) ==>
    (t'  = THE(SOME x)) ==>
    (EP ((dc i).hist,t,dc) = SOME x) ==>
         (CellRead(i', t', wi', dc) = v2w(read_mem32(pa', pm')))`,

       xrw []
    \\ fs_lambda_elim[Fill_def, read_mem32_def, CellRead_def, combinTheory.UPDATE_def]
    \\ THM_SPECL_ASSM "lineSpec" wi_lt_line_size_thm [`state`]
    \\ THM_KEEP_TAC ``invariant_cache`` (fs[invariant_cache_def])
    \\ qpat_assum `∀h i t dc x. P` (qspecl_then [`(dc i).hist`, `i`, `t`, `dc`, `t'`] assume_tac)
    \\ qpat_assum `∀i t wi ni nt state. P` (qspecl_then [`i`, `t'`, `wi'`, `nl + 2n`, `_`, `state`] assume_tac)
    \\ assume_tac( wrtBckLine_dcEQpm'_thm |> spec_let_elim[`i`,`t'`, `pm`, `dc`, `2 ** nl − 1`, `state`])
    \\ line_size_lt_dimword15 ``nl:num``
    \\ assume_tac (lineSpec_thm |> spec_let_elim [`va'`, `pa'`, `state`])
    \\ rfs[CellRead_def, read_mem32_def] 
    \\ PAIR_SPLIT_TAC
    \\ fs[]
);

  
val Fill_KeepHitDC'Tag_thm = Q.prove(
 `!(va:word64) (pa:word48) (va':word64) (pa':word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (x:word48) state.
  let (dc',pm')   = Fill (va, pa, pm, dc) state in
  let (i,t,wi)    = lineSpec(va, pa) state      in
  let (i',t',wi') = lineSpec(va', pa') state    in
    ((i = i') /\ (t' <> x)) ==>
    (~Hit(va, pa, dc) state)  ==>
    (Hit(va', pa', dc) state)  ==>
    (EP ((dc i).hist,t,dc) = SOME x) ==>
        (IS_SOME ((dc' i).sl t'))`,


   rw[Fill_def, combinTheory.UPDATE_def]
   \\ PairedLambda.GEN_BETA_TAC
   \\ abr_lineSpec_tac_dubl
   \\ (CASE_TAC \\ (rw[] \\ fs[]))
   \\ abr_tac_goal is_writeBackLine "wbs'" (SOME ``state:cache_state``)
   \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
   \\ abr_tac_goal is_snd "h'" NONE
   \\ abr_tac_goal is_pabs "proc" NONE
   \\ mk_subgoal_then ``T`` ``2 ** nl − 1``
   >-(Induct
   >-(fs[LineFill_def, combinTheory.UPDATE_def, FOR_FOLDL, EVAL ``COUNT_LIST 1``, Hit_def]
       \\ (CASE_TAC \\ fs[])
       \\ UNDISCH_MATCH_TAC ``(λ(li,t,wi). IS_SOME (a)) b``
       \\ PairedLambda.GEN_BETA_TAC
       \\ lrw[Abbr`proc`, Evict_def, combinTheory.UPDATE_def]
       \\ THM_SPECL_ASSM "WriteBackLine" writBckLine_NotchgTag'_thm [`t'`, `state`]
       \\ line_size_lt_dimword15 ``nl:num``
       \\ `x ≠ t'` by fs[]
       \\ fs[Abbr`wbs'`])
    \\ UNDISCH_MATCH_TAC``a``
    \\ simp[LineFill_def, combinTheory.UPDATE_def]
    \\ (CASE_TAC \\ fs[])     
    \\ fs[DECIDE``SUC n = n + 1``, FOR_FOLDL]
    \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
    \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]])

    \\ qpat_assum`!a. P` (qspecl_then[`n`] assume_tac)
    \\ fs[]
);

val Fill_EpEqtag_tagDc'Miss_thm = Q.prove(
  `!(va:word64) (pa:word48)  (pm:(word48->word8)) (dc:(48 word->CSET)) (va':word64) (pa':word48) (x:word48) state.
  let (dc',pm')   = Fill (va, pa, pm, dc) state in
  let (i,t,wi)    = lineSpec(va, pa) state      in
  let (i',t',wi') = lineSpec(va', pa') state    in
    (i = i') ==>
    (~Hit(va, pa, dc) state) ==>
    (Hit(va', pa', dc) state)  ==>
    (~Hit(va', pa', dc') state)  ==>
    (EP ((dc i).hist,t,dc) = SOME x) ==>
         (t' = x)`,
   xrw[]
   \\ (Cases_on`t'<>x` \\ fs[])
   \\ assume_tac(Fill_KeepHitDC'Tag_thm |> spec_let_elim[`va`, `pa`, `va'`, `pa'`, `pm`, `dc`, `x`, `state`])
   \\ rfs[Hit_def]
);

val Fill_ifInLineRange_HitDC'Pa_thm = Q.prove(
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (va':word64) (pa':word48) state.
  let (dc',pm')   = Fill (va, pa, pm, dc) state           in
  let (i, t, wi)  = lineSpec(va, pa) state                in
  let (i',t',wi') = lineSpec(va', pa') state              in
  let nl = (w2n state.DC.ctr.DminLine)                    in     
    (invariant_cache) ==>
    (~Hit (va,pa,dc) state) ==>
    (~Hit (va',pa',dc) state) ==>
    (Hit (va',pa',dc') state) ==>
    ((i = i') /\ (t = t'))`,

       rw[Fill_def, combinTheory.UPDATE_def]
    \\ PairedLambda.GEN_BETA_TAC
    \\ abr_lineSpec_tac_dubl
    \\ (CASE_TAC \\ rwsimp [])
    >| [(undisch_all_tac >> fs_lambda_elim[Hit_def] >> lrw[]),
        (undisch_all_tac
        \\ fs_lambda_elim[Hit_def]
	\\ ntac 10 strip_tac
	\\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
	\\ REABBREV_TAC
	\\ mk_subgoal_then ``T`` ``2 ** nl − 1``
        >- (fs_lambda_elim[LineFill_def, CellFill_def, combinTheory.UPDATE_def]
        \\ (CASE_TAC \\ rw[])
	\\ Induct_on`n`
        >- (EVAL_TAC \\ fs[])
        \\fs[DECIDE``SUC n = n + 1``, FOR_FOLDL]
	\\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
        \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]])
	\\ qpat_assum `!a .P` (qspecl_then[`n`] assume_tac)
	\\ fs[]),
        (undisch_all_tac
        \\ fs_lambda_elim[Hit_def]
	\\ lrw[]
	\\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
	\\ assume_tac(writBckLine_NotchgSidx'_thm 
                 |> spec_let_elim[`i`, `i'`, `x`, `t'`, `pm`, `dc`, `state`, `2 ** w2n state.DC.ctr.DminLine − 1`])
        \\ line_size_lt_dimword15 ``nl:num``
	\\ rfs[]), all_tac]

    \\ undisch_all_tac
    \\ fs_lambda_elim[Hit_def]
    \\ ntac 10 strip_tac
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ REABBREV_TAC
    \\ abr_tac_goal is_writeBackLine "wbs'" (SOME ``state:cache_state``)
    \\ (fn (asl, g) => let val c = find_term is_evict  g in (Q.ABBREV_TAC`h' = (SND ^c)`) (asl,g) end)
    \\ abr_tac_goal is_pabs "proc" NONE
    \\ mk_subgoal_then ``n <= 32768n`` ``2 ** nl − 1``
    >- (Induct
       >- (CASE_TAC
       >- (fs[LineFill_def, CellFill_def, combinTheory.UPDATE_def, FOR_FOLDL]
       \\ EVAL_TAC
       \\ CASE_TAC
       \\ fs[Abbr`proc`, Abbr`wbs'`, Evict_def, combinTheory.UPDATE_def]
       \\ THM_SPECL_ASSM "WriteBackLine" writBckLine_NotchgTag'_thm [`t'`, `state`]
       \\ line_size_lt_dimword15 ``nl:num``
       \\ (Cases_on`x ≠ t'` \\ fs[]))
       \\ assume_tac(writBckLine_NotchgSidx'_thm |> spec_let_elim[`i`, `i'`, `x`, `t'`, `pm`, `dc`, `state`, `0`])
       \\ fs[])
       (* Inductive case *)
      \\ CASE_TAC
      >- (fs[LineFill_def, CellFill_def, combinTheory.UPDATE_def, FOR_FOLDL]
      \\ CASE_TAC
      \\ fs[DECIDE``SUC n = n + 1``, FOR_FOLDL]
      \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
      \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]])
      \\ assume_tac(writBckLine_NotchgSidx'_thm |> spec_let_elim[`i`, `i'`, `x`, `t'`, `pm`, `dc`, `state`, `SUC n`])
      \\ strip_tac
      \\ fs[])
      \\ qpat_assum`!a .P` (qspecl_then[`2 ** nl − 1`] assume_tac)
      \\ line_size_lt_dimword15 ``nl:num``
      \\ rfs[]
);

val linefill_slEq_diffInputDc_thm = Q.prove(
 `! h i:(48 word) t:(48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) (n:num) (wi:num) (dc':(48 word -> CSET)) 
   (state).
  let sl = FST(LineFill(h, i, t, pm, dc', n) state)       in
  let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
  let nl = (w2n state.DC.ctr.DminLine)                    in  
  let pa =  t ≪ (ns + nl + (2 :num)) ‖ i ≪ (nl + (2 :num)) ‖ (n2w wi :word48) ≪ (2 :num) in 
   (wi <= n) ==>
   (n <= dimword (:15)) ==>
   (CellRead (i,t,wi,dc) = v2w (read_mem32 (pa,pm))) ==> 
   (CellRead (i,t,wi,dc) = ((THE(sl t)).value (n2w wi)))`,
 
   xrw[]
   \\ THM_SPECL_ASSM "LineFill"  linefill_memeq_thm []
   \\ (qpat_assum`!s.P`(qspecl_then[`state`] assume_tac))
   \\ rfs[]
);

val linefill_slEq_diffInputDcAndalsoPM_thm  = Q.prove(
 `!i:(48 word) t:(48 word) t':(48 word) wi:num h (pm:(word48->word8)) (dc:(48 word -> CSET)) (dc':(48 word -> CSET))pa state n m.
   let pm' = SND (WriteBackLine (i,t',pm,dc,m) state)      in
   let sl  = FST (LineFill (h,i,t,pm,dc',n) state)         in
   let sl' = FST (LineFill (h,i,t,pm',dc',n) state)        in 
   let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
   let nl = (w2n state.DC.ctr.DminLine)                    in 
   (t <> t') ==>
   (wi<= n) ==>
   (n <= dimword(:15)) ==>   
   (v2w (read_mem32 (pa,pm)):word32 = v2w (read_mem32 (pa, pm'))) ==>
   (pa =  (t ≪ (ns + nl + (2 :num)) ‖ i ≪ (nl + (2 :num)) ‖ (n2w wi :word48) ≪ (2 :num))) ==> 
       (((THE(sl t)).value (n2w wi)) = ((THE(sl' t)).value (n2w wi)))`,

    xrw[]
   \\ THM_SPECL_ASSM "LineFill" linefill_memeq_thm [`state`]
   \\ rfs[]
);

val CacheRead_KeepMiss_if_PaMissDc_thm = Q.prove(
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (va':word64) (pa':word48) state.
  let (dc',pm')   = CacheRead (va, pa, pm, dc) state in
  let (i,t,wi)    = lineSpec(va, pa) state      in
  let (i',t',wi') = lineSpec(va', pa') state    in
    (Hit(va, pa, dc) state)  ==>
    (~Hit(va', pa', dc) state)  ==>
    (~Hit(va', pa', dc') state)`,

   fs_lambda_elim[CacheRead_def, combinTheory.UPDATE_def, Touch_def, Hit_def]
   \\ lrw[]);

val Fill_NotChgCache_ifEQSiAndalsoTag = Q.prove(
 `!(va:word64) (pa:48 word) (pm:(word48->word8)) (dc:(48 word -> CSET)) (va':word64) (pa':48 word) state.
   let (i, t, wi)  = lineSpec(va, pa) state                in
   let (i',t',wi') = lineSpec(va', pa') state              in
   let dc' = FST (Fill (va,pa,pm,dc) state)                in
   let dc'' = FST (Fill (va',pa',pm,dc) state)             in
    (i = i') ==> (t = t') ==> (dc' = dc'')`,

   lrw[Fill_def, combinTheory.UPDATE_def]
   \\ PairedLambda.GEN_BETA_TAC
   \\ abr_lineSpec_tac_dubl
   \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
   \\ CASE_TAC
   >-(rfs[] 
   \\ rpt strip_tac
   \\ `EP ((dc i').hist,t',dc) = NONE` by fs[]
   \\ rfs[])
   \\ rfs[] 
   \\ rpt strip_tac
   \\ `EP ((dc i').hist,t',dc) = SOME x` by fs[]
   \\ rfs[]
);


val eviction_policy_axiom = new_axiom("eviction_policy_axiom",
  ``!h t dc i x. (EP(h, t, dc) = SOME x) ==> (IS_SOME ((dc (i)).sl (x)))``
);

val diffPa_imply_diffElement_thm = Q.prove(
 `!va pa va' pa' state.
  let (i, t, wi) = lineSpec(va, pa) state in 
  let (i', t', wi') = lineSpec(va', pa') state in 
   (invariant_cache) ==>
   (pa <> pa') ==>
   ((i <> i')  \/ (wi <> wi') \/ (t <> t'))`,

     lrw[]
    \\ PairedLambda.GEN_BETA_TAC
    \\ abr_lineSpec_tac_dubl
    \\ CCONTR_TAC

    \\ assume_tac(lineSpec_thm |> spec_let_elim [`va`, `pa`, `state`])
    \\ assume_tac(lineSpec_thm |> spec_let_elim [`va'`, `pa'`, `state`])
    \\ rfs[]
    \\ fs[]
);

val Fill_causing_evict_EP_IsSome_thm = Q.prove(
 `!(va:word64) (pa:word48) (va':word64) (pa':word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) state.
  let (dc',pm')   = Fill (va, pa, pm, dc) state in
  let (i,t,wi)    = lineSpec(va, pa) state      in
  let (i',t',wi') = lineSpec(va', pa') state    in
    ((i = i') /\ (t <> t')) ==>
    (~Hit(va, pa, dc) state)  ==>
    (Hit(va', pa', dc) state)   ==>
    (~Hit(va', pa', dc') state)   ==>
    (EP ((dc i).hist,t,dc) <> NONE )`,


   rw[Fill_def, combinTheory.UPDATE_def, Hit_def]
   \\ PairedLambda.GEN_BETA_TAC
   \\ abr_lineSpec_tac_dubl
   \\ (CASE_TAC >> rwsimp[])
   \\ (UNDISCH_MATCH_TAC ``a`` >> fs[])
   \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE

   \\ mk_subgoal_then ``T`` ``2 ** nl − 1``

   >-(Induct   >> fs[LineFill_def, combinTheory.UPDATE_def, FOR_FOLDL]
   >-(EVAL_TAC >> (CCONTR_TAC >> fs[]))
   \\ xrw[]
   \\ fs[DECIDE``SUC n = n + 1``, FOR_FOLDL]
   \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
   \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]])

   \\ qpat_assum`!a. P` (qspecl_then[`n`] assume_tac)
   \\ fs[]
);

val Fill_Keep_Miss_DiffTag_thm = Q.prove(
  `!(va:word64) (pa:word48)  (pm:(word48->word8)) (dc:(48 word -> CSET))  (va':word64) (pa':word48) state.
   let (dc',pm')   = Fill (va, pa, pm, dc) state in
   let (i,t,wi)    = lineSpec(va, pa) state      in
   let (i',t',wi') = lineSpec(va', pa') state    in
    (i = i') ==> (t <> t') ==>
    (~Hit(va', pa', dc) state)  ==>
    (~Hit(va', pa', dc') state)`,

      fs_lambda_elim[Fill_def,  Hit_def, combinTheory.UPDATE_def]
   \\ lrw[]
   \\ abr_lineSpec_tac_sgl
   \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
   \\ CASE_TAC
   \\ rfs[]
(* NONE case *)
   >-(mk_subgoal_then ``T`` ``2 ** nl − 1``
   >-(Induct   >> fs[LineFill_def, combinTheory.UPDATE_def, FOR_FOLDL]
   >-(EVAL_TAC >> (CCONTR_TAC >> fs[]))
   \\ xrw[]
   \\ fs[DECIDE``SUC n = n + 1``, FOR_FOLDL]
   \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
   \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]])
   \\ qpat_assum`!a. P` (qspecl_then[`n`] assume_tac)
   \\ fs[])
(* SOME case *)
   \\ rfs[]
   \\ abr_tac_goal is_writeBackLine "pm'" (SOME ``state:cache_state``)
   \\ abr_tac_goal is_evict "h'" NONE
   \\ abr_tac_goal is_pabs "proc" NONE
   \\ mk_subgoal_then ``T`` ``2 ** nl − 1``
   >-(Induct   >> fs[LineFill_def, combinTheory.UPDATE_def, FOR_FOLDL]
   >-(EVAL_TAC >> rfs[Abbr `proc`, Abbr `h'`, Evict_def, combinTheory.UPDATE_def]
      \\ rw[]
      \\ rfs[Abbr`pm'`]
      \\ Cases_on` t' = x`
      >- (THM_SPECL_ASSM "EP" eviction_policy_axiom [`FST (lineSpec (va,pa) state)`, `x`] >> rfs[])
      \\ rfs[]
      \\ THM_SPECL_ASSM "WriteBackLine" writBckLine_NotchgTag'_thm [`t'`, `state`]
      \\ line_size_lt_dimword15 ``nl:num``
      \\ fs[] >> rfs[])

   \\ xrw[]
   \\ fs[DECIDE``SUC n = n + 1``, FOR_FOLDL]
   \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
   \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]])

   \\ qpat_assum`!a. P` (qspecl_then[`n`] assume_tac)
   \\ fs[]
);

val CacheWrite_DiffPa_EqReadMemPa'_thm = Q.store_thm("CacheWrite_DiffPa_EqReadMemPa'_thm",
  `!(va:word64) (pa:word48) data  (pm:(word48->word8)) (dc:(48 word -> CSET))  (va':word64) (pa':word48) state.
   let (dc',pm')   = CacheWrite (va, pa, data, pm, dc) state in
   let (i,t,wi)    = lineSpec(va, pa) state      in
   let (i',t',wi') = lineSpec(va', pa') state    in
    (pa <> pa')                 ==>
    (invariant_cache)           ==>
    (~Hit(va', pa', dc) state)  ==>
    (~Hit(va', pa', dc') state) ==>
    (v2w(read_mem32(pa', pm)):word32 = v2w(read_mem32(pa', pm')))`,

       fs_lambda_elim[CacheWrite_def, Touch_def, combinTheory.UPDATE_def]
    \\ lrw[]       
    \\ THM_SPECL_GOAL "Fill" fill_pm'EQpm_diffIn_thm [``va':word64``,``pa':word48``,``state:cache_state``]
    \\ rfs[]
);


val CacheWrite_DiffPa_EqReadMemPa'_thm3 = Q.store_thm("CacheWrite_DiffPa_EqReadMemPa'_thm3",
  `!(va:word64) (pa:word48) data  (pm:(word48->word8)) (dc:(48 word -> CSET))  (va':word64) (pa':word48) state.
   let (dc',pm')   = CacheWrite (va, pa, data, pm, dc) state in
   let (i,t,wi)    = lineSpec(va, pa) state      in
   let (i',t',wi') = lineSpec(va', pa') state    in
    (pa <> pa')                 ==>
    (invariant_cache)           ==>
    (~Hit(va', pa', dc) state)  ==>
    (Hit(va', pa', dc') state) ==>
    (v2w(read_mem32(pa', pm)):word32 = v2w(read_mem32(pa', pm')))`,

       fs_lambda_elim[CacheWrite_def, Touch_def, combinTheory.UPDATE_def]
    \\ lrw[]       
    \\ THM_SPECL_GOAL "Fill" fill_pm'EQpm_diffIn_thm [``va':word64``,``pa':word48``,``state:cache_state``]
    \\ rfs[]
);

val Fill_dcEqPm_thm = Q.prove(
 `!va pa (pm:(word48->word8)) (dc:(48 word -> CSET)) state.
   let (dc', pm') = Fill(va, pa, pm, dc) state in 
   let (i, t, wi) = lineSpec(va, pa) state      in
   (invariant_cache) ==>
   (~Hit(va, pa, dc) state) ==>
   (CellRead(i, t, wi, dc')  = v2w(read_mem32(pa, pm)))`,

    fs_lambda_elim[Fill_def, combinTheory.UPDATE_def]
    \\ lrw[]
    \\ abr_lineSpec_tac_sgl
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ CASE_TAC

    >-(rfs[CellRead_def, Touch_def]
      \\ THM_SPECL_GOAL "LineFill" linefill_memeq_thm [``state:cache_state``]
      \\ line_size_lt_dimword15 ``nl:num``
      \\ fs[]
      \\ qpat_assum `!wi. P`(qspecl_then[`wi'`] assume_tac)
      \\ THM_SPECL_ASSM "lineSpec" wi_lt_line_size_thm [`state`]  
      \\ THM_SPECL_ASSM "lineSpec" lineSpec_thm [`state`]
      \\ rfs[])


   \\ rfs[CellRead_def, Touch_def]
   \\ abr_tac_goal is_writeBackLine "pm'" (SOME ``state:cache_state``)
   \\ abr_tac_goal is_evict "h'" NONE
   \\ abr_tac_goal is_pabs "proc" NONE
   \\ Cases_on` t' = x`
   >- (THM_SPECL_ASSM "EP" eviction_policy_axiom [`FST (lineSpec (va,pa) state)`, `x`] 
       \\  rfs[Hit_def]
       \\ ntac 3 PAIR_SPLIT_TAC 
       \\ fs[] >> rfs[])
  \\ THM_SPECL_ASSM "WriteBackLine" writebackline_mem_eq_thm [`va`, `pa`, `state`]
  \\ Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`
  \\ FIRST_ASSUM (fn thm => let val trm = (fst o dest_imp o concl) thm in `^trm`by all_tac end)
     >- (assume_tac(adr_thm 
              |> spec_let_elim [`x`, `i'`, `t'`, `i'`, `ns`, `(nl + 2)`]
	      |> SIMP_RULE(arith_ss)[])
     	   \\ THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
     	   \\ qpat_assum `!i t wi ni nt s. P` 
              (qspecl_then [`i'`, `x`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
     	   \\ rpt (WEAKEN_TAC is_forall)
	   \\ fs[])
  \\ line_size_lt_dimword15 ``nl:num``
  \\ THM_SPECL_GOAL "LineFill" linefill_memeq_thm [``state:cache_state``]
  \\ rfs[]
  \\ qpat_assum `!wi. P`(qspecl_then[`wi'`] assume_tac)
  \\ THM_SPECL_ASSM "lineSpec" wi_lt_line_size_thm [`state`]
  \\ THM_SPECL_ASSM "lineSpec" lineSpec_thm [`state`]
  \\ rfs[]
);

val Miss_After_Evict_thm = Q.store_thm("Miss_After_Evict_th",
 `!(va:word64) (pa:word48) (pm:(word48->word8)) (dc:(48 word -> CSET)) (t':word48) (state:cache_state).
  let (i, t, wi) = lineSpec(va, pa) state     in
  let (dc', pm') = Fill(va, pa, pm, dc) state in 
      (EP ((dc i).hist,t,dc) = SOME t') ==>  
      (~Hit(va, pa, dc) state) ==>
      (invariant_cache) ==>
      ((dc' i).sl t' = NONE)`,

     fs_lambda_elim[Fill_def, combinTheory.UPDATE_def, Hit_def]
    \\ lrw[] 
    \\ abr_lineSpec_tac_sgl
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE

    \\ abr_tac_goal is_snd "h'" NONE
    \\ abr_tac_goal is_writeBackLine "wbs'" (SOME ``state:cache_state``)
    \\ abr_tac_goal is_pabs "dc'"  NONE
    \\ mk_subgoal_then ``(n <= dimword(:15))`` ``2 ** nl − 1n``
    >- ( xrw[]
	 \\ fs_lambda_elim[LineFill_def, CellFill_def, combinTheory.UPDATE_def, FOR_FOLDL]
	 \\ CASE_TAC
	 >-(fs[invariant_cache_def]
           \\ qpat_assum`∀h i t dc x. P` (qspecl_then[`((dc:word48->CSET) (i':word48)).hist`, `i'`, `t'`, `dc`, `t'`] assume_tac)
	   \\ rfs[])
         \\ Induct_on `n`
	 >- fs_lambda_elim[EVAL``COUNT_LIST 1``, Abbr`dc'`, Evict_def, combinTheory.UPDATE_def]

         \\ strip_tac
	 \\ `n ≤ 32768` by decide_tac
	 \\ fs[DECIDE``SUC n = n + 1``]
	 \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
 	 \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]])
   \\ qpat_assum` !a. P` (qspecl_then[`n`] assume_tac)
   \\ Q.UNABBREV_TAC `n`
   \\ line_size_lt_dimword15 ``nl:num``
   \\ fs[]
);

val () = export_theory ()
