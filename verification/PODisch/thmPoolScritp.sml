(* --------------------------------------------------------------------------------------------- *)
(* Read Part                                                                                     *)
(* --------------------------------------------------------------------------------------------- *)

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

val lineSpecEq_thm = Q.prove(
`!(va:word64) (pa:word48) (va':word64)  state.
   lineSpec(va, pa) state = lineSpec(va', pa) state`,

   fs_lambda_elim[lineSpec_def, si_def, tag_def, wIdx_def]
);

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

local
  fun th1 h dc x = `^x <> t'` by (all_tac  
    \\ CCONTR_TAC
    \\ fs[invariant_cache_def]
    \\ qpat_assum `∀h i t dc x. P` (qspecl_then [ `^h`, `i'`, `t'`, `^dc`, `^x`] assume_tac)
    \\ FIRST[rfs[Abbr`^dc`], rfs[]])

  fun th2 x t =
       Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`
    \\ line_size_lt_dimword15 ``nl:num``
    \\ ntac 2 (fn (asl, g) => let val c = find_term is_lineFill g in (Q.ABBREV_TAC`fill = (^c state)`) (asl,g) end)
    \\ THM_SPECL_ASSM "WriteBackLine" writebackline_mem_eq_thm [`va'`, `pa'`, `state`]
    \\ rfs[]
    \\ FIRST_ASSUM (fn thm => let val trm = (fst o dest_imp o concl) thm in `^trm`by all_tac end)
     >- (assume_tac(adr_thm 
              |> spec_let_elim [`^x`, `i'`, `^t`, `i'`, `ns`, `(nl + 2)`]
	      |> SIMP_RULE(arith_ss)[])
     	   \\ rfs[]
     	   \\ THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
     	   \\ qpat_assum `!i t wi ni nt s. P` 
              (qspecl_then [`i'`, `^x`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
     	   \\ rpt (WEAKEN_TAC is_forall)
	   \\ fs[])
  val subgoal_tac1 =
       (xrw[]
     \\ ntac 2 (fn (asl, g) => let val c = find_term is_lineFill  g in (Q.ABBREV_TAC`fill = (^c state)`) (asl,g) end)
     \\ THM_SPECL_ASSM "LineFill" linefill_memeq_thm [`state`]
     \\ rfs[]
     \\ THM_SPECL_ASSM "lineSpec" lineSpec_thm [`state`]
     \\ rfs[]
     \\ metis_tac [])
  val subgoal_tac2 =
       qpat_assum`!n. P` (qspecl_then[`2 ** nl − 1`] assume_tac)
     \\ line_size_lt_dimword15 ``nl:num``
     \\ `wi' ≤ 2 ** nl − 1` by fs[invariant_cache_def, Abbr`nl`]
     \\ rfs[]

in
 val Fill_HitCase = Q.prove(
  `!(va:word64) (pa:word48)  (pm:(word48->word8)) (dc:(48 word -> CSET)) (va':word64) (pa':word48) (state:cache_state).
  let (dc', pm',_)  = CacheRead (va, pa, pm, dc)  state in 
  let dc''        = FST (Fill (va',pa',pm,dc)   state)  in 
  let dc'''       = FST (Fill (va',pa',pm',dc') state)  in 
  let (i',t',wi') = lineSpec(va', pa') state            in
    (invariant_cache) ==>
    (Hit(va, pa, dc) state) ==> 
    (~Hit(va', pa', dc) state) ==> 
     ((THE((dc'' i').sl t')).value (n2w wi') = (THE((dc''' i').sl t')).value (n2w wi'))`,

    fs_lambda_elim[CacheRead_def, combinTheory.UPDATE_def, Touch_def, Hit_def]
    \\ lrw[]
    \\ fs_lambda_elim[Fill_def, combinTheory.UPDATE_def]
    \\ abr_lineSpec_tac_dubl
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ THM_SPECL_ASSM "lineSpec" wi_lt_line_size_thm [`state`]
    \\ CASE_TAC
    >-(CASE_TAC
       >-(CASE_TAC
            >-(fs[]
              \\ abr_tac_goal is_abs "dc'" NONE
	      \\ mk_subgoal_then ``(n <= dimword(:15)) /\ (wi' <= n)`` ``2 ** nl − 1n``
	      >- (strip_tac \\ subgoal_tac1)
 	     \\ subgoal_tac2)
      (* NOT a possible Case: I open the definition of EP to prove this subgoal *)
     (* EP ((dc i').hist,t',dc) = NONE *)
     (* i = i' *)
     (* EP *)
     (*      ((dc i' with hist := (a_read,w2n t,i')::(dc i').hist).hist,t', *)
     (*       (λc. *)
     (*          if i' = c then *)
     (*            dc c with hist := (a_read,w2n t,c)::(dc c).hist *)
     (*          else dc c)) = *)
     (*    SOME x *)
      \\ fs[EP_def]  
       )
    \\ CASE_TAC
    >- (fs[] 
        \\ abr_tac_goal is_abs "dc'" NONE
	\\ mk_subgoal_then ``(n <= dimword(:15)) /\ (wi' <= n)`` ``2 ** nl − 1n``
	>- (strip_tac \\ subgoal_tac1)
        \\ subgoal_tac2)

      (* NOT a possible Case: I open the definition of EP to prove this subgoal *)
     (* EP ((dc i').hist,t',dc) = NONE *)
     (* i ≠ i' *)
     (* EP *)
     (*       ((dc i').hist,t', *)
     (*        (λc. *)
     (*           if i = c then *)
     (*             dc c with hist := (a_read,w2n t,c)::(dc c).hist *)
     (*           else dc c)) = *)
     (*     SOME x *)
   \\ fs[EP_def])

   \\ CASE_TAC  
   >- (CASE_TAC
     (* NOT a possible Case: I open the definition of EP to prove this subgoal *)
     (* EP ((dc i').hist,t',dc) = SOME x *)
     (* i = i' *)
     (* EP *)
     (*         ((dc i' with hist := (a_read,w2n t,i')::(dc i').hist).hist,t', *)
     (*          (λc. *)
     (*             if i' = c then *)
     (*               dc c with hist := (a_read,w2n t,c)::(dc c).hist *)
     (*             else dc c)) = *)
     (*       NONE *)
     >- fs[EP_def]
    \\ fs[]

     \\ abr_tac_goal is_snd "h'" NONE
     \\ abr_tac_goal is_writeBackLine "wbs'" (SOME ``state:cache_state``)
     \\ abr_tac_goal is_pabs "dc'"  NONE
     \\ abr_tac_goal is_pabs "dc''" NONE
     \\ abr_tac_goal is_writeBackLine "wb''" (SOME ``state:cache_state``)
     \\ abr_tac_goal is_pabs "dc''" NONE
     \\ Cases_on`x = x'`
    >-(fs[]
    \\ th1 ``((dc:word48->CSET) i').hist`` ``dc`` ``x'``
    \\ th2 ``x':word48`` ``t':word48``
    \\ fs[Abbr`fill`, Abbr`fill'`]
    \\ mk_subgoal_then ``(n <= dimword(:15)) /\ (wi' <= n)`` ``2 ** nl − 1n``
    >- (strip_tac \\ subgoal_tac1)
    \\ subgoal_tac2)

(* `x<>x'` *)
    \\ th1 ``((dc:word48->CSET) i').hist`` ``dc`` ``x``
    \\ th1 ``(a_read,w2n(t:word48),(i':word48))::((dc:word48->CSET) i').hist``  ``dc''`` ``x'``
    \\ Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`
    \\ line_size_lt_dimword15 ``nl:num``
    \\ ntac 2 (fn (asl,g) => let val c = find_term is_lineFill g in (Q.ABBREV_TAC`fill = (^c state)`) (asl,g) end)
    \\ THM_SPECL_ASSM "WriteBackLine" writebackline_mem_eq_thm [`va'`, `pa'`, `state`]
    \\ rfs[]
    \\ FIRST_ASSUM (fn thm => let val trm = (fst o dest_imp o concl) thm in `^trm`by all_tac end)
     >- (assume_tac(adr_thm 
              |> spec_let_elim [`x`, `i'`, `t'`, `i'`, `ns`, `(nl + 2)`]
	      |> SIMP_RULE(arith_ss)[])
     	   \\ rfs[]
     	   \\ THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
     	   \\ qpat_assum `!i t wi ni nt s. P` 
              (qspecl_then [`i'`, `x`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
     	   \\ rpt (WEAKEN_TAC is_forall)
	   \\ fs[])
     \\ fs[]
     \\ WEAKEN_TAC is_neq
     \\ WEAKEN_TAC is_eq
     \\ WEAKEN_TAC is_imp
     \\ FIRST_ASSUM (fn thm => let val trm = (fst o dest_imp o concl) thm in `^trm`by all_tac end)
     >- (assume_tac(adr_thm 
              |> spec_let_elim [`x'`, `i'`, `t'`, `i'`, `ns`, `(nl + 2)`]
	      |> SIMP_RULE(arith_ss)[])
     	   \\ rfs[]
     	   \\ THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
     	   \\ qpat_assum `!i t wi ni nt s. P` 
              (qspecl_then [`i'`, `x'`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
     	   \\ rpt (WEAKEN_TAC is_forall)
	   \\ fs[])
    \\ fs[Abbr`fill`, Abbr`fill'`]
    \\ mk_subgoal_then  ``(n <= dimword(:15)) /\ (wi' <= n)`` ``2 ** nl − 1n``
    >- (strip_tac \\ subgoal_tac1)
    \\ subgoal_tac2)

(* i <> i' *)
    \\ (CASE_TAC >|[fs[EP_def], all_tac]) 
    (* Here I open the definition of EP to prove that for a cache set different from the one that the last action took palce 
       inside, history cannot affect Eviction Policy. And if something should be evicted it should be the same.*)
    \\ `x = x'` by fs[EP_def]
    \\ fs[]
    \\ th1 ``((dc:word48->CSET) i').hist`` ``dc`` ``x'``
    \\ abr_tac_goal is_snd "h'" NONE
    \\ abr_tac_goal is_writeBackLine "wbs'" (SOME ``state:cache_state``)
    \\ abr_tac_goal is_pabs "dc'"  NONE
    \\ abr_tac_goal is_pabs "dc''" NONE
    \\ abr_tac_goal is_writeBackLine "wb''" (SOME ``state:cache_state``)
    \\ abr_tac_goal is_pabs "dc'''" NONE
    \\ th2 ``x':word48`` ``t':word48``
    \\ fs[Abbr`fill`, Abbr`fill'`]
    \\ mk_subgoal_then  ``(n <= dimword(:15)) /\ (wi' <= n)`` ``2 ** nl − 1n``
    >- (strip_tac \\ subgoal_tac1)
    \\ subgoal_tac2
)
end;

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


local 
 fun th1 h dc x = `^x <> t'` by (all_tac  
    \\ CCONTR_TAC
    \\ fs[invariant_cache_def]
    \\ qpat_assum `∀h i t dc x. P` (qspecl_then [ `^h`, `i'`, `t'`, `^dc`, `^x`] assume_tac)
    \\ FIRST[rfs[Abbr`^dc`], rfs[]])

  fun th2 x t =
       Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`
    \\ line_size_lt_dimword15 ``nl:num``
    \\  ntac 2 (fn (asl,g) => let val c = find_term is_lineFill g in (Q.ABBREV_TAC`fill = (^c state)`) (asl,g) end)
    \\ THM_SPECL_ASSM "WriteBackLine" writebackline_mem_eq_thm [`va'`, `pa'`, `state`]
    \\ rfs[]
    \\ FIRST_ASSUM (fn thm => let val trm = (fst o dest_imp o concl) thm in `^trm`by all_tac end)
     >- (assume_tac(adr_thm 
              |> spec_let_elim [`^x`, `i'`, `^t`, `i'`, `ns`, `(nl + 2)`]
	      |> SIMP_RULE(arith_ss)[])
     	   \\ rfs[]
     	   \\ THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
     	   \\ qpat_assum `!i t wi ni nt s. P` 
              (qspecl_then [`i'`, `^x`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
     	   \\ rpt (WEAKEN_TAC is_forall)
	   \\ fs[])

  fun th3 i x t =
     Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`
     \\ FIRST_ASSUM (fn thm => let val trm = (fst o dest_imp o concl) thm in `^trm`by all_tac end)
     >- (assume_tac(adr_thm 
              |> spec_let_elim [`^x`, `^i`, `^t`, `^i`, `ns`, `(nl + 2)`]
	      |> SIMP_RULE(arith_ss)[])
     	   \\ rfs[]
     	   \\ THM_KEEP_TAC``invariant_cache`` (fs[invariant_cache_def])
     	   \\ qpat_assum `!i t wi ni nt s. P` 
              (qspecl_then [`^i`, `^x`, `_`, `nl + 2n`, `ns`, `state`] ASSUME_TAC)
     	   \\ rpt (WEAKEN_TAC is_forall)
	   \\ fs[])
     \\ fs[]

  val subgoal_tac1 =
       (xrw[]
     \\ ntac 2 (abr_tac_goal is_lineFill "lfill" (SOME ``state:cache_state``))
     \\ THM_SPECL_ASSM "LineFill" linefill_memeq_thm [`state`]
     \\ THM_SPECL_ASSM "lineSpec" lineSpec_thm [`state`]
     \\ THM_SPECL_ASSM "Fill" fill_pm'EQpm_diffIn_thm [`va'`, `pa'`, `state`]
     \\ UNDISCH_MATCH_TAC ``a``
     \\ fs_lambda_elim[Hit_def]
     \\ rwsimp[]
     \\ rfs[])

  val subgoal_tac2 =
       qpat_assum`!n. P` (qspecl_then[`2 ** nl − 1`] assume_tac)
     \\ line_size_lt_dimword15 ``nl:num``
     \\ `wi' ≤ 2 ** nl − 1` by fs[invariant_cache_def, Abbr`nl`]
     \\ rfs[]

  val subgoal_tac3 =
       (xrw[]
     \\ Q.ABBREV_TAC`ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))`
     \\ line_size_lt_dimword15 ``nl:num``
     \\ ntac 2 (abr_tac_goal is_lineFill "lfill" (SOME ``state:cache_state``))
     \\ THM_SPECL_ASSM "LineFill" linefill_memeq_thm [`state`]
     \\ THM_SPECL_ASSM "lineSpec" lineSpec_thm [`state`]
     \\ rfs[]
     \\ SYM_ASSUMPTION_TAC``a = b``
     \\ THM_SPECL_ASSM "Fill" fill_pm'EQpm_diffIn_thm [`va'`, `pa'`, `state`]
     \\ THM_SPECL_ASSM "WriteBackLine" writebackline_mem_eq_thm [`va'`, `pa'`, `state`]
     \\ rfs[])

in

 val Fill_MissCase = Q.prove(
  `!(va:word64) (pa:word48)  (pm:(word48->word8)) (dc:(48 word -> CSET)) (va':word64) (pa':word48) state.
   let (dc', pm',_)  = CacheRead (va, pa, pm, dc)  state in 
   let dc''        = FST (Fill (va',pa',pm,dc)   state)  in 
   let dc'''       = FST (Fill (va',pa',pm',dc') state)  in 
   let (i',t',wi') = lineSpec(va', pa') state            in
    (invariant_cache) ==>
    (~Hit(va, pa, dc) state) ==> 
    (~Hit(va', pa', dc) state) ==> 
    (~Hit(va', pa', dc') state)  ==> 
     ((THE((dc'' i').sl t')).value (n2w wi') = (THE((dc''' i').sl t')).value (n2w wi'))`, 


    fs_lambda_elim[CacheRead_def, combinTheory.UPDATE_def, Touch_def, Hit_def]
    \\ rpt strip_tac
    \\ abr_lineSpec_tac_dubl
    \\ lrw[]
    \\ rfs[]
    \\ Q.ABBREV_TAC `fill = (Fill (va,pa,pm,dc) state)`
    \\ abr_tac_goal is_snd "pm'" NONE
    \\ abr_tac_goal is_pabs "dc'" NONE

    \\ simp[Fill_def, combinTheory.UPDATE_def]
    \\ PairedLambda.GEN_BETA_TAC
    \\ abr_tac_goal wordsSyntax.is_w2n "nl" NONE
    \\ rfs[]
    \\ THM_SPECL_ASSM "lineSpec" wi_lt_line_size_thm [`state`]
    \\ CASE_TAC
(* EP ((dc i').hist,t',dc) = NONE *)
    >-(CASE_TAC
     >- (fs[]
     \\ mk_subgoal_then ``(n <= dimword(:15)) /\ (wi' <= n)`` ``2 ** nl − 1n``
        >- (strip_tac  \\ subgoal_tac1)
     \\ subgoal_tac2)

     (* NOT a possible Case: I open the definition of EP to prove this subgoal *)
    (* EP ((dc i').hist,t',dc) = NONE *)
    (* EP ((dc' i').hist,t',dc') = SOME x *)
    \\ fs[EP_def])

(* EP ((dc i').hist,t',dc) = SOME x *)
    \\ CASE_TAC
    (* Not a possible cases*)
    >- (Cases_on `(i <> i') \/ (t <> t')`
     >- (fs[EP_def])
     \\ THM_SPECL_ASSM "Fill" fill_hit_thm [`state`]
     \\ UNDISCH_MATCH_TAC ``a``
     \\ fs_lambda_elim[Hit_def]
     \\ strip_tac
     \\ rfs[])

    \\ fs[]
    \\ abr_tac_goal is_snd "h'" NONE
    \\ abr_tac_goal is_writeBackLine "wbs'" (SOME ``state:cache_state``)
    \\ abr_tac_goal is_pabs "dc''"  NONE
    \\ abr_tac_goal is_evict "h''" NONE
    \\ abr_tac_goal is_writeBackLine "wbs''" (SOME ``state:cache_state``)
    \\ abr_tac_goal is_pabs "dc'''"  NONE
    \\ Cases_on `i = i'`
    >- (fs[]
       \\ th1 ``((dc:word48->CSET) i').hist`` ``dc`` ``x``
       \\ th1 ``((dc':word48->CSET) i').hist`` ``dc'`` ``x'``
       \\ Cases_on`t = t'`
    >- (`(dc' i').sl x = NONE` by (all_tac
       \\ THM_SPECL_ASSM "Fill" Miss_After_Evict_thm [`x`, `state`]
       \\ rfs[Abbr`h'`, Abbr`dc'`]
       \\ UNDISCH_MATCH_TAC``a``
       \\ fs_lambda_elim[Hit_def]
       \\ lrw[])
       \\ `x' <> x` by (all_tac
       \\ fs[invariant_cache_def]
       \\ qpat_assum`∀h i t dc x. P` (qspecl_then[`((dc':word48->CSET) (i':word48)).hist`, `i'`, `t'`, `dc'`, `x'`] assume_tac)
       \\ CCONTR_TAC
       \\ lrw[]
       \\ rfs[])
       \\ mk_subgoal_then ``(n <= dimword(:15)) /\ (wi' <= n)`` ``2 ** nl − 1n``
       >- (   subgoal_tac3
           \\ th3 ``i:word48`` ``x:word48`` ``t:word48``
	   \\ TAKE_DOWN_TAC ``(a==>b)``
	   \\ WEAKEN_TAC is_imp
	   \\ TAKE_DOWN_TAC ``(a==>b)``
	   \\ th3 ``i:word48`` ``x':word48`` ``t:word48``
	   \\ `¬Hit (va',pa',dc) state` by (all_tac \\ fs_lambda_elim[Hit_def] \\ rfs[])
	   \\ rfs[]) \\  subgoal_tac2
       )
       \\ mk_subgoal_then ``(n <= dimword(:15)) /\ (wi' <= n)`` ``2 ** nl − 1n``
       >- (   subgoal_tac3
           \\ th3 ``i:word48`` ``x:word48`` ``t':word48``
	   \\ TAKE_DOWN_TAC ``(a==>b)``
	   \\ WEAKEN_TAC is_imp
	   \\ TAKE_DOWN_TAC ``(a==>b)``
	   \\ th3 ``i:word48`` ``x':word48`` ``t':word48``
	   \\ `¬Hit (va',pa',dc) state` by (all_tac \\ fs_lambda_elim[Hit_def] \\ rfs[])
	   \\ rfs[]) \\  subgoal_tac2
       )
    (* i ≠ i' *)
    \\ th1 ``((dc:word48->CSET) i').hist`` ``dc`` ``x``
    \\ `x = x'` by fs[Abbr`dc'`, EP_def]
    \\ mk_subgoal_then ``(n <= dimword(:15)) /\ (wi' <= n)`` ``2 ** nl − 1n``
    >-(   subgoal_tac3
       \\ th3 ``i':word48`` ``x:word48`` ``t':word48``
       \\`¬Hit (va',pa',dc) state` by (all_tac \\ fs_lambda_elim[Hit_def] \\ rfs[])
       \\ rfs[]) \\ subgoal_tac2
  )
end;

(* ---------------------- cache write-read different address fold ------------------------------ *)
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

