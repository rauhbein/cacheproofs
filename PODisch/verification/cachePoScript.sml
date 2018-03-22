open HolKernel boolLib bossLib pairSyntax;
open arm_stepTheory;
open cacheTheory cutilsLib CacheLibTheory cacheIfTheory;

val _ = new_theory "cachePo";

val writeback_mem_eq_dc_val_thm = Q.store_thm ("writeback_mem_eq_dc_val_thm",
  `!(pa:word48) (va:word64) (pm:(word48->word8)) dc   (state:cache_state).
	    (let (i, t, wi) = lineSpec(va, pa) state in
             let pm' =  WriteBack(i, t, wi, pm, THE ((dc i).sl t)) state in 
	     let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in 
	     let nl = (w2n state.DC.ctr.DminLine) in 
	      (invariant_cache) ==> 
	      (CellRead(i,t,wi,dc) = v2w(read_mem32(pa, pm')):word32)	
	      )
	    `,
        lrw[]
     \\ PairedLambda.GEN_BETA_TAC	      
     \\ abr_lineSpec_tac_sgl
     \\ fs_lambda_elim[WriteBack_def, combinTheory.UPDATE_def, read_mem32_def,CellRead_def]
     \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
     \\ Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))` 
     \\ ASSUME_TAC(lineSpec_thm
 	     |> Q.ISPECL[`va:word64`,`pa:word48`,`state:cache_state`]
	     |> SIMP_RULE(srw_ss()) [LET_DEF]
	     |> PairedLambda.GEN_BETA_RULE)
	   \\ REABBREV_TAC
     \\ rfs[]  
     \\ xrw []
     \\ fs[]
     \\ UNDISCH_ALL_TAC
     \\ blastLib.BBLAST_PROVE_TAC
);

val mlwb_oblg_disch = Q.prove(
 `!va pa pm dc state.
  let pm' =  mlwb va pa pm dc state in
  let (i,t,wi) = lineSpec(va, pa) state in
  invariant_cache ==>
  (CellRead(i,t,wi,dc) = v2w(read_mem32(pa, pm')):word32)`,
  fs_lambda_elim[mlwb_def]
  \\ lrw[]
  \\ abr_lineSpec_tac_sgl
  \\ assume_tac(writeback_mem_eq_dc_val_thm |> spec_let_elim[`pa`, `va`, `pm`, `dc`, `state`])
  \\ rfs[]
);

val mlwb_other_oblg_disch = Q.prove(
`!va pa va' pa' pm dc state.
  let pm' =  mlwb va' pa' pm dc state in
  let (i,t,wi) = lineSpec(va, pa) state in
  let (i',t',wi') = lineSpec(va', pa') state in

  ((i = i') /\ (t <> t')) ==>
  invariant_cache ==>
  (v2w(read_mem32(pa, pm)) = v2w(read_mem32(pa, pm')):word32)`,

  fs_lambda_elim[mlwb_def]
  \\ ntac 7 strip_tac
  \\ abr_lineSpec_tac_dubl
  \\ lrw[]
  \\ assume_tac( writeback_mem_eq_thm |> spec_let_elim[`pa`, `va`, `pm`, `THE(((dc :word48 -> CSET) i).sl t')`, `state`, `i`, `t'`, `wi'`])
  \\ rfs[]
  \\ Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`
  \\ Q.ABBREV_TAC`nl = w2n state.DC.ctr.DminLine`
  \\ `(i ≪ (nl + 2) ‖ t' ≪ (nl + (ns + 2))) ≠ (i ≪ (nl + 2) ‖ t ≪ (nl + (ns + 2)))` by
       (assume_tac(adr_thm 
              |> spec_let_elim [`t`, `i`, `t'`, `i`, `ns`, `(nl + 2)`]
	      |> SIMP_RULE(arith_ss)[])
     	   \\ THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
     	   \\ qpat_assum `!(i:word48) t wi ni nt s. P` 
              (qspecl_then [`i`, `t`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
     	   \\ rpt (WEAKEN_TAC is_forall)
	   \\ fs[])

   \\ rfs[]
);

val mllu_oblg_disch = Q.prove(
  `!(va:word64) (pa:word48)  (pm:(word48->word8)) (dc:(48 word->CSET)) (va':word64) (pa':word48) h n state.
  let (i,t,wi)    = lineSpec(va, pa) state      in
  let (i',t',wi') = lineSpec(va', pa') state    in
  let (sl, _) =  LineFill(h, i, t, pm, dc, n) state in
  (n ≤ 32768) ==>
  (wi' <= n)  ==>
  invariant_cache ==>
  (i = i') /\ (t = t') ==>
  (((THE (sl t')).value) (n2w(wi'):48 word) = v2w(read_mem32 (pa', pm)))`,

      xrw[]
   \\ ASSUME_TAC (linefill_memeq_thm
      |> Q.ISPECL[`h:(actions # num # word48) list`,`i:(48 word)`,`t:(48 word)`,`(pm:(word48->word8))`,
                  `(dc:(48 word -> CSET))`, `n:num`, `state:cache_state`]
      |> SIMP_RULE(srw_ss())[LET_DEF] 
      |> PairedLambda.GEN_BETA_RULE)
   \\ rfs[]
   \\ qpat_assum `!wi. P` (qspecl_then [`wi'`] ASSUME_TAC)
   \\ ASSUME_TAC(lineSpec_thm
      |> Q.ISPECL[`va':word64`,`pa':word48`,`state:cache_state`]
      |> SIMP_RULE(srw_ss()) [LET_DEF]
      |> PairedLambda.GEN_BETA_RULE)
   \\ rfs[]);

(* ``!t va state. ?pa. t  = SND(lineSpec(va, pa) state)``; *)
val chit_oblg_disch = Q.prove(
`!va pa  dc dc' state.
 let (i, t, _) = lineSpec(va, pa) state in
 (((dc i).sl t) = ((dc' i).sl t))  ==>
 ((Hit(va, pa, dc) state) = (Hit(va, pa, dc') state))`,
 
    xrw[]
  \\ rfs[Hit_def]
);

val chit_other_oblg_disch = Q.prove(
 `!(va:word64) (pa:word48) (dc:(48 word -> CSET)) (va':word64) (pa':word48) state.
  let (i,t,wi)    = lineSpec(va, pa) state      in
  let (i',t',wi') = lineSpec(va', pa') state    in
    (i = i') /\ (t = t') ==>
    ((Hit(va, pa, dc) state) =  (Hit(va', pa', dc) state))`,
 
    xrw[]
  \\ rfs[Hit_def]
);


val ccnt_oblg_disch = Q.prove(
`!va pa  dc dc' state.
 let (i, t, wi) = lineSpec(va, pa) state in
 ((ca i t dc) = (ca i t dc'))  ==>
 ((ccnt va pa dc state) = (ccnt va pa dc' state))`,
  
  xrw[ccnt_def, ca_def]
  \\ fs[]
);
    

val ccnt_other_oblg_disch = Q.prove(
`!(va:word64) (pa:word48) (dc:(48 word -> CSET)) (va':word64) (pa':word48) state.
  let (i,t,wi)    = lineSpec(va, pa) state      in
  let (i',t',wi') = lineSpec(va', pa') state    in
    (i = i') /\ (t = t') ==>
  ((THE((dc i).sl t)).value = (THE ((dc i').sl t')).value)`,

  
  xrw[]
  \\ fs[CellRead_def]
);

val ccntw_oblg_disch = Q.prove(
`!va pa  dc dc' state.
 let (i, t, wi) = lineSpec(va, pa) state in
 (((dc i).sl t) = ((dc' i).sl t))  ==>
  (CellRead(i,t,wi, dc) =  CellRead(i,t,wi, dc'))`,
  
  xrw[]
  \\ fs[CellRead_def]
);


val ccntw_ccnt_oblg = Q.prove(
`!va pa dc dc' state.
  Hit(va, pa, dc)  state ==>
  Hit(va, pa, dc') state ==>
  ((ccnt va pa dc state) = (ccnt va pa dc' state)) ==>
  ((ccntw va pa dc state) = (ccntw va pa dc' state))`,
 
  fs_lambda_elim[ccnt_def, ccntw_def, Hit_def, CellRead_def]
  \\ lrw[]
);  

val ccntw_other_oblg_disch = Q.prove(
`!(va:word64) (pa:word48) (dc:(48 word -> CSET)) (va':word64) (pa':word48) state.
  let (i,t,wi)    = lineSpec(va, pa) state      in
  let (i',t',wi') = lineSpec(va', pa') state    in
    (i = i') /\ (t = t') ==>
  (CellRead(i,t,wi, dc) =  CellRead(i,t,wi, dc))`,

  
  xrw[]
  \\ fs[CellRead_def]
);


val FUN_NEQ_THM = Q.prove (
 `!f g.  (f <> g) = (?x. f x <> g x)`,
  metis_tac[]
);

val ccntw_ccnt_diff_oblg_disch = Q.prove(
`!(va:word64) (pa:word48) pa' (dc:(48 word -> CSET)) dc' state.
  let (i,t,wi) = lineSpec(va, pa) state      in
  ((Hit(va, pa, dc) state) /\ (Hit(va, pa, dc') state) /\ ((THE((dc i).sl t)).value <> (THE ((dc' i).sl t)).value)) ==>
  (?x. (CellRead(i,t,x,dc) <> CellRead(i,t,x,dc')))`,

      xrw[] 
   \\ fs_lambda_elim[CellRead_def, ccntw_def]
   \\ Q.ABBREV_TAC `f = (THE ((dc i).sl t)).value`
   \\ Q.ABBREV_TAC `g = (THE ((dc' i).sl t)).value`
   \\ assume_tac(FUN_NEQ_THM |> Q.ISPECL[`f:word48->word32`, `g:word48->word32`])
   \\ rfs[]
   \\ EXISTS_TAC ``w2n (x:word48)``
   \\ lrw[]
);

local
val subgoal_tac1 =
       (xrw[]
     \\ ntac 2 (abr_tac_goal is_lineFill "lfill" (SOME ``state:cache_state``))
     \\ THM_SPECL_ASSM "LineFill" linefill_memeq_thm [`state`]
     \\ THM_SPECL_ASSM "lineSpec" lineSpec_thm [`state`]
     \\ UNDISCH_MATCH_TAC ``a``
     \\ rwsimp[]
     \\ rfs[])

val subgoal_tac2 =
       qpat_assum`!n. P` (qspecl_then[`2 ** nl − 1`] assume_tac)
     \\ line_size_lt_dimword15 ``nl:num``
     \\ `wi' ≤ 2 ** nl − 1` by fs[invariant_cache_def, Abbr`nl`]
     \\ rfs[]

fun fn1 x = 
    (assume_tac(adr_thm 
              |> spec_let_elim [`^x`, `i'`, `t'`, `i'`, `ns`, `(nl + 2)`]
	      |> SIMP_RULE(arith_ss)[])
    \\ rfs[]
    \\ THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
    \\ qpat_assum `!i t wi ni nt s. P` 
        (qspecl_then [`i'`, `^x`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
    \\ rpt (WEAKEN_TAC is_forall)
    \\ fs[])
in
val ccnt_oblg_disch = Q.prove (
`!dc:(48 word -> CSET) dc':(48 word -> CSET) pm pa va state.
 let (i, t, wi) = lineSpec(va, pa) state     in
 let (_,_,val1) = CacheRead (va, pa, pm, dc) state  in
 let (_,_,val2) = CacheRead (va, pa, pm, dc') state in
     invariant_cache ==>
     (((dc i).sl t) = ((dc' i).sl t)) ==>
      (val1 = val2)`,

     lrw[]
     \\ fs_lambda_elim[CacheRead_def, combinTheory.UPDATE_def,Touch_def, Hit_def]
     \\ abr_lineSpec_tac_sgl
     \\ CASE_TAC 
     \\ rwsimp []
     >- rfs[]

    \\ simp[Fill_def, combinTheory.UPDATE_def]
    \\ PairedLambda.GEN_BETA_TAC
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`
    \\ THM_SPECL_ASSM "lineSpec" wi_lt_line_size_thm [`state`]
    \\ xfs[]
    \\ CASE_TAC
    (* EP ((dc i').hist,t',dc) = NONE *)
    >-(CASE_TAC
     >- (mk_subgoal_then ``(n <= dimword(:15)) /\ (wi' <= n)`` ``2 ** nl − 1n``
        >- subgoal_tac1
     \\ subgoal_tac2)

     \\ Cases_on `x = t'`
     >- (THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
        \\ qpat_assum `∀h i t dc x. P` (qspecl_then [`(dc' i').hist`, `i'`, `t'`, `dc'`, `x`] assume_tac)
	\\ rfs[])
     \\ mk_subgoal_then ``(n <= dimword(:15)) /\ (wi' <= n)`` ``2 ** nl − 1n``
     >- (strip_tac >> subgoal_tac1
       \\ THM_SPECL_ASSM "WriteBackLine" writebackline_mem_eq_thm [`va`, `pa`, `state`]
       \\ FIRST_ASSUM (fn thm => let val trm = (fst o dest_imp o concl) thm in `^trm`by all_tac end)
       \\ rfs[]
       >- fn1 ``x:word48``)
     \\ subgoal_tac2)

    \\ CASE_TAC
    >- (Cases_on `x = t'`
     >- (THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
     \\ qpat_assum `∀h i t dc x. P` (qspecl_then [ `(dc i').hist`, `i'`, `t'`, `dc`, `x`] assume_tac)
     \\ rfs[])
    \\ mk_subgoal_then ``(n <= dimword(:15)) /\ (wi' <= n)`` ``2 ** nl − 1n``
    >- (subgoal_tac1
    \\ THM_SPECL_ASSM "WriteBackLine" writebackline_mem_eq_thm [`va`, `pa`, `state`]
    \\ FIRST_ASSUM (fn thm => let val trm = (fst o dest_imp o concl) thm in `^trm`by all_tac end)
    \\ rfs[]
    >- fn1 ``x:word48``)
    \\ subgoal_tac2)

    \\ Cases_on `x' = t'`
    >- (THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
    \\ qpat_assum `∀h i t dc x. P` (qspecl_then [`(dc' i').hist`, `i'`, `t'`, `dc'`, `x'`] assume_tac)
    \\ rfs[])
    \\ Cases_on `x = t'`
    >- (THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
    \\ qpat_assum `∀h i t dc x. P` (qspecl_then [`(dc i').hist`, `i'`, `t'`, `dc`, `x`] assume_tac)
    \\ rfs[])
    \\ mk_subgoal_then ``(n <= dimword(:15)) /\ (wi' <= n)`` ``2 ** nl − 1n``
    >- (subgoal_tac1
    \\ THM_SPECL_ASSM "WriteBackLine" writebackline_mem_eq_thm [`va`, `pa`, `state`]
    >- (  fn1 ``x:word48``  
       \\ fn1 ``x':word48``))
    \\ subgoal_tac2
)
end;

val ccnt_lcnt_oblg_disch = Q.prove(
`!va pa dc state.
  let (i, t, wi) = lineSpec(va, pa) state in
   ((ccnt va pa dc state) = (lcnt i t dc))`,

        lrw[]
     \\ fs_lambda_elim[ca_def, ccnt_def, lcnt_def]
     \\ rfs[]
);

val ccnt_not_eq_oblg_disch = Q.prove (
`!dc:(48 word -> CSET) dc':(48 word -> CSET) pm pa va state.
 let (i, t, wi) = lineSpec(va, pa) state     in
     Hit(va, pa, dc) state  ==>
     Hit(va, pa, dc') state ==>
     LineDirty (i,t,dc)     ==>
     LineDirty (i,t,dc')    ==>
     (THE(ca i t dc) <> THE(ca i t dc')) ==>
     ((ccnt va pa dc state) <> (ccnt va pa dc' state))`,

        lrw[]
     \\ fs_lambda_elim[Hit_def, combinTheory.UPDATE_def,LineDirty_def, ca_def, ccnt_def]
     \\ abr_lineSpec_tac_sgl
     \\ Q.ABBREV_TAC `f = (THE ((dc i').sl t'))`
     \\ Q.ABBREV_TAC `g = (THE ((dc' i').sl t'))`
     \\ rwsimp[]
     \\ Cases_on`f` >> Cases_on`g`
     \\ rfs[datatype_SLVAL]
);


val miss_oblg_disch = Q.prove (
`!dc:(48 word -> CSET) pa va state.
  let (i, t, wi) = lineSpec(va, pa) state     in
  ~(Hit (va, pa, dc)  state) ==> 
  ((ca i t dc) = NONE)`,

   fs_lambda_elim[Hit_def, ca_def]
   \\ rwsimp []
);


val cdirty_oblg_disch = Q.prove (
`!dc:(48 word -> CSET) dc':(48 word -> CSET) pa va state.
 let (i, t, wi) = lineSpec(va, pa) state     in
     (((dc i).sl t) = ((dc' i).sl t)) ==>
     (LineDirty (i,t,dc) = LineDirty (i,t,dc'))`,

   fs_lambda_elim[LineDirty_def]
   \\ rwsimp []
);


val lDirty_axiom = new_axiom("lDirty_axiom",
 ``!dc pa va state.
  let (i, t, wi) = lineSpec(va, pa) state     in
  (lDirty(va, pa, dc) state)==>
  ((dc i).sl t) <> NONE``
);

val cdirty_chit_oblg_disch = Q.prove(
`!dc pa va state.
  (lDirty(va, pa, dc) state) ==>
  (Hit(va,pa, dc) state)`,

     lrw[]
  \\ fs_lambda_elim[Hit_def, lDirty_def, LineDirty_def,lDirty_axiom ]
  \\ abr_lineSpec_tac_sgl
  \\ assume_tac(lDirty_axiom |> spec_let_elim[`dc`, `pa`, `va`, `state`])
  \\ rfs[lDirty_def, LineDirty_def]
  \\ CCONTR_TAC
  \\ assume_tac(optionTheory.NOT_IS_SOME_EQ_NONE |> Q.ISPECL[`(((dc :word48 -> CSET) (i' :word48)).sl (t' :word48))`])
  \\ rfs[]
);


val cdirty_other_oblg_disch = Q.prove(
`!va pa pa' dc state.
 let (i,t,wi)  = lineSpec(va, pa) state in
 let (i',t',wi')  = lineSpec(va, pa') state in
 ((i = i') /\ (t = t')) ==>
 (LineDirty(i,t,dc) =  LineDirty(i',t',dc))`,
  
  fs_lambda_elim[LineDirty_def] >> rw[]
);


val cdirty_ldirty_oblg_disch = Q.prove(
`!va pa dc state.
 let (i, t, wi) = lineSpec(va, pa) state in
 LineDirty(i,t,dc) = lDirty(va, pa, dc) state`,
 
  fs_lambda_elim[LineDirty_def, lDirty_def] 
  \\ lrw[]
  \\ ntac 2 CASE_TAC
);

val not_chit_not_cdirty_oblg_disch = Q.prove(
`!dc va pa state. (~Hit(va, pa, dc) state) ==> (~lDirty(va, pa, dc) state)`,

    fs_lambda_elim[Hit_def, lDirty_def, LineDirty_def]
    \\ lrw[]
    \\ ntac 2 CASE_TAC
    \\ assume_tac(dirty_axiom)
    \\ qpat_assum `!l. P`(qspecl_then[`(dc (FST (q,q',r'))).sl (FST (SND (q,q',r')))`] assume_tac)
    \\ rfs[]
);

val lw_ccntw_oblg_disch = Q.prove(
`!va pa va' pa' dc state.
    let (i, t, wi) = lineSpec(va, pa) state in
    let (i', t', wi') = lineSpec(va, pa) state in
    ((i= i') /\ (t = t')) ==> 
    ((lw va pa (ccnt va pa dc state) state) =
      (ccntw va pa dc state))`,

  RW_TAC std_ss [ ccntw_def, ccnt_def, CellRead_def, lw_def]
);



val lw_lv_oblg_disch = Q.prove(
`!va pa pm dc h n state.
  let (i,t,wi) = lineSpec(va, pa) state in
  let sl = THE(FST(lv i t pm dc h n state) t) in 
  let mvl = read32(pa, (mv T pm dc2 (fmem:(word48->word8)#(word48->CSET)-> (word48 -> word8)) fcm), read_mem32) in 
  (invariant_cache) ==>
  (n <= dimword(:15)) ==>
  (wi <= n) ==>
  ((sl.value (n2w wi)) = v2w (mvl):word32)`,

    fs_lambda_elim[lv_def, mv_def, fmem_def, read32_def]
  \\ lrw[]
  \\ abr_lineSpec_tac_sgl
  \\ THM_SPECL_GOAL "LineFill" linefill_memeq_thm [``state:cache_state``]
  \\ rfs[]
  \\ qpat_assum `!wi. P`(qspecl_then[`wi`] assume_tac)
  \\ THM_SPECL_ASSM "lineSpec" wi_lt_line_size_thm [`state`]  
  \\ THM_SPECL_ASSM "lineSpec" lineSpec_thm [`state`]
  \\ rfs[]
);
    

val lv_oblg_disch = Q.prove(
`!va pa va' pa' pm dc h n state. 
  let (i,t,wi) = lineSpec(va, pa) state in
  let (i',t',wi') = lineSpec(va', pa') state in
  ((i=i') /\ (t=t')) ==> 
  ((lv i' t' pm dc h n state) = (lv i' t' pm dc h n state))`,
  
  fs_lambda_elim[lv_def, mv_def, fmem_def]
  \\ lrw[]
);
      
val mllu_lv_oblg_disch = Q.prove(
` ∀ va pa va' pa' pm dc h n state.
  let (i,t,wi) = lineSpec(va, pa) state in
  let (i',t',wi') = lineSpec(va', pa') state in
  ((i=i') /\ (t=t')) ==> 
  (((lv i' t' pm dc h n state) = (mllu i t pm dc h n state)) <=> 
  (!va'' pa''.
   let (i'', t'', wi'') = lineSpec(va'', pa'') state in
   let sl = THE ((FST (lv i' t' pm dc h n state)) t') in
   let sl' = THE ((FST (mllu i t pm dc h n state)) t) in
    ((sl.value (n2w wi'')) = (sl'.value (n2w wi'')))))`,
  
  fs_lambda_elim[lv_def, mllu_def, mv_def, fmem_def]
  \\ lrw[]
);


(* Transition function obligations*)
    
val ctf_chit_oblg_disch = Q.prove(
`!dc pm dop state.
 let (dc', pm', _) = ctf pm dc state dop in
 let (va, pa) = ADD dop in 
  ~cl dop ==> (Hit(va, pa, dc') state)`,

      fs_lambda_elim[ctf_def, fmem_def, mv_def, ca_def, ADD_def]
    \\ lrw[]
    \\ Cases_on`dop`
    \\ rfs[]
    \\ rpt CASE_TAC
    \\ FIRST[metis_tac[cl_def], all_tac]
    \\ rpt (FIRST_PROVE[(assume_tac(cacheRead_paHitdc'_thm |> spec_let_elim[`q`,`q'`, `pm`, `dc`, `state`]) >> fs[]),
                   (assume_tac(cacheWrite_paHitdc'_thm |> spec_let_elim[`q`,`q'`, `q''`, `pm`, `dc`, `state`]) >> fs[])])
);

val ctf_cl_miss_oblg_disch =Q.prove(
`!dc pm dop state .
 let (dc', pm', _) = ctf pm dc state dop in
 let (va, pa) = ADD dop in 
 let (i,t,wi) = lineSpec(va, pa) state in
  cl dop ==>
  (!pa'.  let (i',t',wi') = lineSpec(va, pa') state in
          ((i = i') /\ (t = t')) ==> (~Hit(va, pa', dc') state))`,

      fs_lambda_elim[ctf_def,ADD_def]
    \\ Cases_on`dop`
    \\ rfs[cl_def]
    \\ rpt CASE_TAC
    \\ lrw[]      
    \\ fs_lambda_elim[CacheInvalidateByAdr_def, combinTheory.UPDATE_def, Hit_def, Evict_def]
    \\ rwsimp[]
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
val ctf_cl_other_oblg_disch = Q.prove(
`!dc pm dop state pa'.
 let (dc', pm', _) = ctf pm dc state dop in
 let (va, pa) = ADD dop in 
 let (i,t,wi) = lineSpec(va, pa) state in
 let (i',t',wi') = lineSpec(va, pa') state in
 let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))  in
 let nl = (w2n state.DC.ctr.DminLine)                     in 
  cl dop ==>
  ((((t' << ns) !! i') << (nl + 2n)) <> ((t << ns) !! i) << (nl + 2n)) ==>    
    ((ca i' t' dc) = (ca i' t' dc'))`,

      fs_lambda_elim[ctf_def,ADD_def, ca_def]
    \\ Cases_on`dop`
    \\ rfs[cl_def]
    \\ rpt CASE_TAC
    \\ lrw[]      
    \\ abr_lineSpec_tac_sgl
    \\ fs_lambda_elim[CacheInvalidateByAdr_def, combinTheory.UPDATE_def, Hit_def, Evict_def]
    \\ lrw[]

    \\ Q.ABBREV_TAC`i = FST (lineSpec (q,r) state)`
    \\ Q.ABBREV_TAC`t = FST (SND (lineSpec (q,r) state))`
    \\ rpt CASE_TAC
    >- ((`t <> t'` by (CCONTR_TAC >> fs[])) \\ ( rfs[] >>  tac ))
    \\ tac
)
end;

val ctf_cl_wb_oblg_disch = Q.prove(
`!dc pm dop state.
 let (dc', pm', _) = ctf pm dc state dop in
 let (va, pa) = ADD dop in 
 let (i,t,wi) = lineSpec(va, pa) state in
 let (tg, il) = SND(HD (dc' i).hist) in
  (Hit(va,pa,dc) state) ==>
  cl dop ==> (t = n2w(tg))`,

       fs_lambda_elim[ctf_def,ADD_def, ca_def]
    \\ Cases_on`dop`
    \\ rfs[cl_def]
    \\ rpt CASE_TAC
    \\ lrw[]      
    \\ abr_lineSpec_tac_sgl
    \\ fs_lambda_elim[CacheInvalidateByAdr_def, combinTheory.UPDATE_def, Hit_def, Evict_def]
    \\ rfs[Abbr`t'`]
);

val Fill_NotchgCacheLineForTag'_thm = Q.prove(
  `!(va:word64) (pa:word48)  (pm:(word48->word8)) (dc:(48 word -> CSET)) n (va':word64) (pa':word48) state.
  let (i, t, wi)  = lineSpec(va, pa) state                       in
  let (i',t',wi') = lineSpec(va', pa') state                     in
  let (sl, _)   = LineFill ((dc i).hist, i, t, pm, dc, n) state  in
    (i = i') ==>
    (t <> t') ==>
    (invariant_cache) ==>
    (IS_SOME (sl t')) ==>
    (IS_SOME ((dc i').sl t')) ==>
      (((sl t')) = (((dc i').sl t')))`,


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
    \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]]
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

local
val tac =
     mk_subgoal_then ``T`` ``2 ** nl − 1``
   >-(Induct
   >-(fs_lambda_elim[LineFill_def, combinTheory.UPDATE_def, FOR_FOLDL, EVAL ``COUNT_LIST 1``, Hit_def] >> rfs[])
    \\ UNDISCH_MATCH_TAC``a``
    \\ simp[LineFill_def, combinTheory.UPDATE_def]
    \\ fs[DECIDE``SUC n = n + 1``, FOR_FOLDL]
    \\ ASSUME_TAC( rich_listTheory.COUNT_LIST_ADD
			 |> Q.ISPECL[`(n:num) + 1`, `1:num`]
			 |> SIMP_RULE(srw_ss())[listTheory.MAP, EVAL ``COUNT_LIST  (1)``])
    \\ rfs[rich_listTheory.FOLDL_APPEND |> SIMP_RULE(srw_ss())[]])

    \\ qpat_assum`!a. P` (qspecl_then[`n`] assume_tac)
    \\ fs[]
in

val ctf_not_cl_other_oblg_disch = Q.prove(
`!(va:word64) (pa:word48) (va':word64) (pa':word48) (pm:(word48->word8)) (dc:(48 word -> CSET))state.
  let (dc',pm')   = Fill (va, pa, pm, dc) state in
  let (i,t,wi)    = lineSpec(va, pa) state      in
  let (i',t',wi') = lineSpec(va', pa') state    in
    invariant_cache ==> 
    ((i = i') /\ (t' <> t)) ==>
    (~Hit(va, pa, dc) state)  ==>
    (Hit(va', pa', dc) state)  ==> 
    if (EP ((dc i).hist,t,dc) = SOME t')
     then (ca i' t' dc' = NONE)
     else ((CellRead(i', t', wi', dc) = CellRead(i', t', wi', dc')))`,

   fs_lambda_elim[ca_def, combinTheory.UPDATE_def]
   \\ lrw[]
   \\ abr_lineSpec_tac_sgl
   >- metis_tac[Miss_After_Evict_thm |> spec_let_elim[`va`, `pa`, `pm`, `dc`, `t'`, `state`]]
   \\ Q.ABBREV_TAC`i = FST (lineSpec (va,pa) state)`
   \\ Q.ABBREV_TAC`t = FST (SND (lineSpec (va,pa) state))`
   \\ Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`
   \\ Q.ABBREV_TAC`nl = w2n state.DC.ctr.DminLine`
   \\ assume_tac(thm1 |> spec_let_elim[`va`, `pa`, `va'`, `pa'`, `pm`, `dc`, `state`])
   \\ mfs[]
   \\  FIRST_ASSUM (fn thm => let val trm = (fst o dest_imp o snd o dest_imp o concl) thm in `^trm`by all_tac end)
     >- (assume_tac(adr_thm 
              |> spec_let_elim [`t`, `i'`, `t'`, `i'`, `ns`, `(nl + 2)`]
	      |> SIMP_RULE(arith_ss)[])
     	   \\ THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
     	   \\ qpat_assum `!i t wi ni nt s. P` 
              (qspecl_then [`i'`, `t`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
     	   \\ rpt (WEAKEN_TAC is_forall)
	   \\ fs[])
   \\ fs[]
   \\ Cases_on`EP ((dc i').hist,t,dc)`
   \\ rfs[]
   >- (`Hit (va',pa',FST (Fill (va,pa,pm,dc) state)) state` by
	  (simp[Hit_def, Fill_def, combinTheory.UPDATE_def]
	  \\ PairedLambda.GEN_BETA_TAC
	  \\ rfs[]
	  \\ UNDISCH_MATCH_TAC``Hit (a, b, c) s``
	  \\ UNDISCH_MATCH_TAC``~Hit (a, b, c) s``
	  \\ tac)
      \\ rfs []
      )
   \\ assume_tac(Fill_KeepHitDC'Tag_thm |> spec_let_elim[`va`, `pa`, `va'`, `pa'`, `pm`, `dc`, `x`, `state`])
   \\ rfs[]
   \\ UNDISCH_ALL_TAC
   \\ fs_lambda_elim[Hit_def]
   \\ lrw[]
)
end;
 
val ctf_not_cl_wb_oblg_disch = Q.prove(
`!dc pm dop state.
  let (dc', pm', (_, y)) = ctf pm dc state dop in 
  let (va, pa) = ADD dop in
  let (i, t, wi) = lineSpec(va, pa) state  in  
  (~Hit(va, pa, dc) state) ==>
  (invariant_cache) ==>
  ~cl dop    ==> 
  (y = if (EP ((dc i).hist,t,dc) = NONE)
       then (NONE,NONE)
       else if (LineDirty(i, THE (EP ((dc i).hist,t,dc)), dc)) /\ (THE (EP ((dc i).hist,t,dc)) <> t)
       then ((EP ((dc i).hist,t,dc)), (ca i (THE (EP ((dc i).hist,t,dc))) dc))
       else (NONE,NONE))`,

       fs_lambda_elim[ctf_def, ADD_def, ca_def, Hit_def, LineDirty_def,CacheWrite_def,CacheRead_def, Fill_def, Touch_def, combinTheory.UPDATE_def, Evict_def, LineFill_def]
    \\ Cases_on`dop`
    \\ rfs[cl_def]
    \\ rpt CASE_TAC
    \\ lrw[]
    \\ FIRST [metis_tac[cl_def,optionTheory.IS_SOME_DEF],  all_tac] 
    \\ UNDISCH_ALL_TAC
    \\ abr_lineSpec_tac_sgl
    \\ rpt (CASE_TAC >> rfs [])  
    \\ (CCONTR_TAC
    \\ rfs[invariant_cache_def]
    \\ ntac 3 (WEAKEN_TAC is_forall)
    \\ qpat_assum `∀h i t dc x. P` (qspecl_then [`(dc i').hist`, `i'`, `t'`, `dc`, `t'`] assume_tac)
    \\ rfs[])
);

val ctf_wt_cdirty_oblg_disch = Q.prove(
`!dc pm dop state.
  let (dc', pm', h) = ctf pm dc state dop in
  let (va, pa) = ADD dop in
  let (i, t, wi) = lineSpec(va, pa) state  in  
  wt dop ==> 
  ((VAL dop).flag) ==>
  (LineDirty(i, t, dc'))`,

      Cases_on`dop`
    \\ rpt CASE_TAC
    \\ fs_lambda_elim[ctf_def, mv_def, fmem_def, ADD_def, wt_def, VAL_def, LineDirty_def]
    \\ lrw[]      
    \\ abr_lineSpec_tac_sgl
    \\ rfs[]
    \\ rpt (CASE_TAC >> rfs [])
    \\ assume_tac(cacheWrite_setCell_thm |> spec_let_elim[`q`, `q'`, `(VAL (WT (q,q',q'',r)))`, `pm`, `dc`, `state`])
    \\ rfs[VAL_def]
);

val ctf_rd_hit_oblg_disch = Q.prove(
`!dc pm dop state.
  let (dc', pm', h) = ctf pm dc state dop in
  let (va, pa) = ADD dop in
  let (i, t, wi) = lineSpec(va, pa) state  in  
  rd dop ==>
  (Hit(va, pa, dc) state) ==>
  (ca i t dc = ca i t dc')`,

       Cases_on`dop`
    \\ fs_lambda_elim[ctf_def, mv_def, fmem_def, ADD_def, ca_def, rd_def, Hit_def, CacheRead_def, combinTheory.UPDATE_def]
    \\ lrw[]      
    \\ abr_lineSpec_tac_sgl
    \\ rpt (CASE_TAC >> rfs [])
); 

val ctf_rd_miss_oblg_disch = Q.prove(
`!dc pm dop state.
  let (dc', pm', _) = ctf pm dc state dop in
  let (va, pa) = ADD dop in
  let (i, t, wi) = lineSpec(va, pa) state  in  
  invariant_cache ==>
  rd dop ==>
  (~Hit(va, pa, dc) state) ==>
  ((Hit(va, pa, dc') state) /\
   (CellRead(i,t,wi, dc') = v2w(read_mem32(pa, pm)):word32) /\
   (~LineDirty(i,t,dc')))`,

       Cases_on`dop`
    \\ rfs[rd_def]
    \\ rpt CASE_TAC
    \\ fs_lambda_elim[ctf_def, mv_def, fmem_def, ADD_def, CellRead_def, rd_def, Hit_def, CacheRead_def, Touch_def, combinTheory.UPDATE_def]
    \\ lrw[]      
    \\ abr_lineSpec_tac_sgl
    \\ rfs[]
    \\ rpt (CASE_TAC >> rfs [])
    \\ FIRST_PROVE[(assume_tac(fill_hit_thm |> spec_let_elim[`q`, `q'`, `pm`, `dc`, `state`])
            \\ fs[Hit_def]
	    \\ ntac 3 PAIR_SPLIT_TAC 
	    \\ rfs[]),
                   (assume_tac(cacheRead_miss_thm |> spec_let_elim [`q`, `q'`,`pm`, `dc`, `state`]
			      |> SIMP_RULE(srw_ss())[LET_DEF, Hit_def, CacheRead_def] 
			      |> PairedLambda.GEN_BETA_RULE )
            \\ rfs[]),
                   fs_lambda_elim[LineDirty_def,Fill_def, combinTheory.UPDATE_def, LineFill_def]
            \\ rpt (CASE_TAC >> rfs [])
      ]
);


local 
val tac_1 =
    (assume_tac(wIdx_lt_dimword48_thm |> spec_let_elim[`q`, `q'`, `state`])
      \\ assume_tac(wIdx_lt_dimword48_thm |> spec_let_elim[`va'`, `pa'`, `state`])
      \\ `wi'' MOD 281474976710656 = wi''` by rfs[]
      \\ `wi' MOD 281474976710656 = wi'` by rfs[]
      \\ fs[]
      \\ assume_tac (diffPa_imply_diffElement_thm |> spec_let_elim [`q`, `q'`, `va'`, `pa'`, `state`])
      \\ rfs[])

in

val ctf_wt_fill_oblg_disch = Q.prove(
`!dc pm dop state va' pa'.
  let (dc', pm', _) = ctf pm dc state dop in
  let (va, pa) = ADD dop in
  let (i, t, wi) = lineSpec(va, pa) state  in  
  let (i', t', wi') = lineSpec(va', pa') state  in   
  invariant_cache ==>
  ((pa <> pa') /\ (i= i') /\ (t = t')) ==>
  (~Hit(va, pa, dc) state) ==>
  wt dop ==> 
  ((Hit(va', pa',dc') state) /\
   (CellRead(i',t',wi',dc') = v2w(read_mem32(pa', pm)):word32)
  )`,

    fs_lambda_elim[ctf_def, mv_def, fmem_def, ADD_def, CellRead_def, Hit_def, CacheWrite_def, Touch_def, combinTheory.UPDATE_def]
    \\ Cases_on`dop`
    \\ rfs[wt_def, mv_def]
    \\ rpt CASE_TAC
    \\ ntac 5 strip_tac
    \\ abr_lineSpec_tac_sgl
    \\ lrw[]      
    \\ rpt (CASE_TAC >> rfs [])
    \\ rpt (FIRST_PROVE [tac_1,
        (fs_lambda_elim[Fill_def, combinTheory.UPDATE_def]
	\\ abr_lineSpec_tac_sgl
	\\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
	\\ CASE_TAC 
	\\ rfs[]
	\\ abr_tac_goal is_writeBackLine "pm'" (SOME ``state:cache_state``)
	\\ abr_tac_goal is_evict "h'" NONE
	\\ abr_tac_goal is_pabs "proc" NONE
	\\ line_size_lt_dimword15 ``nl:num``
	\\ THM_SPECL_GOAL "LineFill" linefill_memeq_thm [``state:cache_state``]
	\\ rfs[]
	\\ qpat_assum `!wi. P`(qspecl_then[`wi'`] assume_tac)
	\\ THM_SPECL_ASSM "lineSpec" wi_lt_line_size_thm [`state`]
	\\ THM_SPECL_ASSM "lineSpec" lineSpec_thm [`state`]
	\\ assume_tac(fill_pm'EQpm_diffIn_thm |> spec_let_elim [`q`, `q'`, `pm`, `dc`, `va'`, `pa'`, `state`])
	\\ UNDISCH_ALL_TAC
	\\ fs_lambda_elim[ Hit_def, combinTheory.UPDATE_def,Fill_def]
	\\ lrw[]      
	\\ rfs[])])

    \\ fs_lambda_elim[Fill_def, combinTheory.UPDATE_def]
    \\ abr_lineSpec_tac_sgl
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ THM_SPECL_GOAL "LineFill" linefill_memeq_thm [``state:cache_state``]
    \\ line_size_lt_dimword15 ``nl:num``
    \\ fs[]
    \\ qpat_assum `!wi. P`(qspecl_then[`wi'`] assume_tac)
    \\ THM_SPECL_ASSM "lineSpec" wi_lt_line_size_thm [`state`]  
    \\ THM_SPECL_ASSM "lineSpec" lineSpec_thm [`state`]
    \\ rfs[]

)
end;

val ctf_wt_ccnt_oblg_disch = Q.prove(
`!dc pm dop state va' pa'.
  let (dc', pm', _) = ctf pm dc state dop in
  let (va, pa) = ADD dop in
  let (i, t, wi) = lineSpec(va, pa) state  in  
  let (i', t', wi') = lineSpec(va', pa') state  in   
  invariant_cache ==>
  (Hit(va, pa, dc) state) ==>
  wt dop ==> 
  ((CellRead(i,t,wi,dc') = (VAL dop).value) /\
  ((pa <> pa') ==> (i=i') ==> (t=t') ==> (Hit(va', pa',dc) state) ==> 
    (CellRead(i',t',wi',dc) = CellRead(i',t',wi',dc')))
  )`,

     fs_lambda_elim[ctf_def, mv_def,fmem_def, ADD_def, CellRead_def]
    \\ Cases_on`dop`
    \\ rfs[wt_def]
    \\ rpt CASE_TAC
    \\ lrw[]      
    \\ abr_lineSpec_tac_sgl
    >- (assume_tac(cacheWrite_setCell_thm |> spec_let_elim[`q`, `q'`, `q''`,
          `mv T pm dc2 (fmem:(word48->word8)#(word48->CSET)-> (word48 -> word8)) fcm`, `dc`, `state`]) >> rfs[VAL_def, mv_def, fmem_def])
    \\ UNDISCH_ALL_TAC
    \\ fs_lambda_elim[CacheWrite_def, Touch_def, combinTheory.UPDATE_def, Hit_def]
    \\ xrw[]
    \\ assume_tac(wIdx_lt_dimword48_thm |> spec_let_elim[`q`, `q'`, `state`])
    \\ assume_tac(wIdx_lt_dimword48_thm |> spec_let_elim[`va'`, `pa'`, `state`])
    \\ `wi'' MOD 281474976710656 = wi''` by rfs[]
    \\ `wi' MOD 281474976710656 = wi'` by rfs[]
    \\ fs[]
    \\ assume_tac (diffPa_imply_diffElement_thm |> spec_let_elim [`q`, `q'`, `va'`, `pa'`, `state`])
    \\ rfs[]
);

val ctf_wb_not_cl_evpol_oblg = Q.prove(
`!dc pm dop state.
  let (dc', pm', (_, tg, v)) = ctf pm dc state dop in 
  let (va, pa) = ADD dop in
  let (i, t, wi) = lineSpec(va, pa) state  in  
  ~cl dop    ==> 
  IS_SOME tg ==>
  (~Hit(va, pa, dc) state) ==> 
  (EP ((dc i).hist,t,dc) = tg ) ==>
  ((ca i (THE tg) dc) = v) ==>
  (LineDirty(i, THE tg, dc))`,

       fs_lambda_elim[ctf_def, ADD_def, ca_def, Hit_def, LineDirty_def,CacheWrite_def,CacheRead_def, combinTheory.UPDATE_def]
    \\ Cases_on`dop`
    \\ rfs[cl_def]
    \\ rpt CASE_TAC
    \\ lrw[]
);

val ctf_wb_not_cl_evpol_some_oblg_disch = Q.prove(
`!dc pm dop state x.
  let (dc', pm', (_, tg, _)) = ctf pm dc state dop in
  let (va, pa) = ADD dop in
  let (i, t, wi) = lineSpec(va, pa) state  in  
  ~cl dop ==> 
  (EP ((dc i).hist,t,dc) = SOME x) ==>
  (~Hit(va, pa, dc) state)    ==>
  (LineDirty(i, x, dc)) ==>
  (THE tg = x)`,


       fs_lambda_elim[ctf_def, ADD_def, ca_def, Hit_def, LineDirty_def,CacheWrite_def,CacheRead_def, Fill_def, Touch_def, combinTheory.UPDATE_def, Evict_def, LineFill_def]
    \\ Cases_on`dop`
    \\ rfs[cl_def]
    \\ rpt CASE_TAC
    \\ lrw[]
    \\ FIRST [metis_tac[cl_def], all_tac]  
);

val _ = export_theory();
