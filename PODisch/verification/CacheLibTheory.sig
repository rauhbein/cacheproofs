signature CacheLibTheory =
sig
  type thm = Thm.thm

  (*  Axioms  *)
    val dirty_axiom : thm
    val eviction_policy_axiom : thm

  (*  Definitions  *)
    val WriteBackLine_simp_def : thm
    val invariant_cache_def : thm
    val msb_extract_def : thm
    val write_mem32_def : thm

  (*  Theorems  *)
    val CacheClean_dcEQdc'_diffMsb_thm : thm
    val CacheClean_dcEQdc'_thm : thm
    val CacheClean_dcEQpm'_thm : thm
    val CacheClean_hitDc'_diffAddr_thm : thm
    val CacheClean_keepMiss_diffMsb_thm : thm
    val CacheInvalidate_dcEQdc'_diffAddr_thm : thm
    val CacheInvalidate_dcEQpm'_thm : thm
    val CacheInvalidate_hitDc'_diffAddr_thm : thm
    val CacheInvalidate_keepMiss_diffMsb_thm : thm
    val CacheInvalidate_missDc'_thm : thm
    val CacheRead_lfoldEQval_SameAddress_thm : thm
    val CacheWrite_DiffPa_EqReadMemPa'_thm : thm
    val CacheWrite_DiffPa_EqReadMemPa'_thm3 : thm
    val Fill_someEPevict_dcEQpm'_thm : thm
    val Miss_After_Evict_th : thm
    val adr_neq2_thm : thm
    val adr_neq3_thm : thm
    val adr_neq_thm : thm
    val cacheRead_hit_thm : thm
    val cacheRead_miss_thm : thm
    val cacheRead_paHitdc'_thm : thm
    val cacheWrite_paHitdc'_thm : thm
    val cacheWrite_paNOTCHGpm_thm : thm
    val cacheWrite_read_thm : thm
    val cacheWrite_setCell_thm : thm
    val cellFill_memeq_thm : thm
    val fill_dcEQpm_thm : thm
    val fill_hit_thm : thm
    val fill_pm'EQpm_diffIn_thm : thm
    val lineSpec_eq_thm : thm
    val lineSpec_thm : thm
    val linefill_hit_t : thm
    val linefill_memeq_t : thm
    val lt_mod_thm : thm
    val msbEqAdrs_Hit_dc_thm : thm
    val shift_add_thm : thm
    val si_extract_thm : thm
    val tag_extract_thm : thm
    val wIdx_extract_thm : thm
    val wIdx_lt_dimword48_thm : thm
    val wi_lt_line_size_thm : thm
    val word_log2_lt_adrSize : thm
    val write_read_thm : thm
    val write_read_unch_thm : thm
    val writeback_mem_eq_thm : thm
    val writebackline_mem_eq_thm : thm
    val wrtBckLine_dcEQpm'_thm : thm
    val wrtBckLine_pmEQpm'IfNotDirty_thm : thm
    val wrtBck_dirty_thm : thm
    val wrtBck_memory_thm : thm

  val CacheLib_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [arm_step] Parent theory of "CacheLib"

   [cache] Parent theory of "CacheLib"

   [dirty_axiom]  Axiom

      [oracles: ] [axioms: dirty_axiom] []
      |- ∀l. ¬IS_SOME l ⇒ ¬(THE l).dirty

   [eviction_policy_axiom]  Axiom

      [oracles: ] [axioms: eviction_policy_axiom] []
      |- ∀h t dc i x. (EP (h,t,dc) = SOME x) ⇒ IS_SOME ((dc i).sl x)

   [WriteBackLine_simp_def]  Definition

      |- ∀li t pm dc n.
           WriteBackLine_simp (li,t,pm,dc,n) =
           (let v = (dc li).sl
            in
              ((li =+
                dc li with sl := (t =+ SOME (THE (v t) with dirty := F)) v)
                 dc,pm))

   [invariant_cache_def]  Definition

      |- invariant_cache ⇔
         (∀pa. pa && 0xFFFFFFFFFFFCw = pa) ∧
         (∀i t wi ni nt state.
            (let MSB = 0xFFFFFFFFFFFFw ⋙ ni in
             let LSB = ¬(0xFFFFFFFFFFFFw ⋙ ni ≪ ni) in
             let MSB2 = 0xFFFFFFFFFFFFw ⋙ (ni + nt) in
             let LSB2 = 0xFFFFFFFFFFFFw ≪ (48 − (ni + nt)) ⋙ (48 − nt)
             in
               state.DC.ctr.DminLine ≥ 1w ∧ state.DC.ccsidr.NumSets ≥ 1w ∧
               ni < 48 − nt ∧ (t && MSB2 = t) ∧ (i && LSB2 = i) ∧
               ((t ≪ nt ‖ i) && MSB = t ≪ nt ‖ i) ∧
               (n2w wi ≪ 2 && LSB = n2w wi ≪ 2))) ∧
         (∀s s'.
            (s.DC.ctr.DminLine = s'.DC.ctr.DminLine) ∧
            (s.DC.ccsidr.NumSets = s'.DC.ccsidr.NumSets)) ∧
         ∀h i t dc x. (EP (h,t,dc) = SOME x) ⇒ IS_SOME ((dc i).sl x)

   [msb_extract_def]  Definition

      |- ∀va pa state.
           msb_extract va pa state =
           (let (i,t,wi) = lineSpec (va,pa) state in
            let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let nl = w2n state.DC.ctr.DminLine
            in
              (t ≪ ns ‖ i) ≪ (nl + 2))

   [write_mem32_def]  Definition

      |- ∀add pm value.
           write_mem32 (add,pm,value) =
           (let pm = (add =+ (7 >< 0) value) pm in
            let pm = (add + 1w =+ (15 >< 8) value) pm in
            let pm = (add + 2w =+ (23 >< 16) value) pm in
            let pm = (add + 3w =+ (31 >< 24) value) pm
            in
              pm)

   [CacheClean_dcEQdc'_diffMsb_thm]  Theorem

      |- ∀va pa pm dc va' pa' state.
           (let (dc',pm') = CacheCleanByAdr (va,pa,pm,dc) state in
            let (i',t',wi') = lineSpec (va',pa') state in
            let (i,t,wi) = lineSpec (va,pa) state in
            let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let nl = w2n state.DC.ctr.DminLine
            in
              invariant_cache ⇒
              (t' ≪ ns ‖ i') ≪ (nl + 2) ≠ (t ≪ ns ‖ i) ≪ (nl + 2) ⇒
              (CellRead (i',t',wi',dc) = CellRead (i',t',wi',dc')))

   [CacheClean_dcEQdc'_thm]  Theorem

      [oracles: DISK_THM, cheat] [axioms: ] []
      |- ∀va pa pm dc va' pa' state.
           (let (dc',pm') = CacheCleanByAdr (va,pa,pm,dc) state in
            let (i',t',wi') = lineSpec (va',pa') state in
            let (i,t,wi) = lineSpec (va,pa) state in
            let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let nl = w2n state.DC.ctr.DminLine
            in
              invariant_cache ⇒
              ((t' ≪ ns ‖ i') ≪ (nl + 2) = (t ≪ ns ‖ i) ≪ (nl + 2)) ⇒
              (CellRead (i',t',wi',dc) = CellRead (i',t',wi',dc')))

   [CacheClean_dcEQpm'_thm]  Theorem

      [oracles: DISK_THM, cheat] [axioms: ] []
      |- ∀va pa pm dc va' pa' state.
           (let (dc',pm') = CacheCleanByAdr (va,pa,pm,dc) state in
            let (i',t',wi') = lineSpec (va',pa') state in
            let (i,t,wi) = lineSpec (va,pa) state in
            let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let nl = w2n state.DC.ctr.DminLine
            in
              Hit (va,pa,dc) state ⇒
              invariant_cache ⇒
              LineDirty (i',t',dc) ⇒
              ((t' ≪ ns ‖ i') ≪ (nl + 2) = (t ≪ ns ‖ i) ≪ (nl + 2)) ⇒
              (CellRead (i',t',wi',dc) = v2w (read_mem32 (pa',pm'))))

   [CacheClean_hitDc'_diffAddr_thm]  Theorem

      |- ∀va pa pm dc va' pa' state.
           (let (i,t,wi) = lineSpec (va,pa) state in
            let (i',t',wi') = lineSpec (va',pa') state in
            let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let nl = w2n state.DC.ctr.DminLine in
            let (dc',pm') = CacheCleanByAdr (va,pa,pm,dc) state
            in
              (t' ≪ ns ‖ i') ≪ (nl + 2) ≠ (t ≪ ns ‖ i) ≪ (nl + 2) ⇒
              Hit (va,pa,dc) state ⇒
              Hit (va',pa',dc) state ⇒
              Hit (va',pa',dc') state)

   [CacheClean_keepMiss_diffMsb_thm]  Theorem

      |- ∀va pa pm dc va' pa' state.
           (let (i,t,wi) = lineSpec (va,pa) state in
            let (i',t',wi') = lineSpec (va',pa') state in
            let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let nl = w2n state.DC.ctr.DminLine in
            let (dc',pm') = CacheCleanByAdr (va,pa,pm,dc) state
            in
              (t' ≪ ns ‖ i') ≪ (nl + 2) ≠ (t ≪ ns ‖ i) ≪ (nl + 2) ⇒
              Hit (va,pa,dc) state ⇒
              ¬Hit (va',pa',dc) state ⇒
              ¬Hit (va',pa',dc') state)

   [CacheInvalidate_dcEQdc'_diffAddr_thm]  Theorem

      |- ∀va pa pm dc va' pa' state.
           (let (i,t,wi) = lineSpec (va,pa) state in
            let (i',t',wi') = lineSpec (va',pa') state in
            let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let nl = w2n state.DC.ctr.DminLine in
            let (dc',pm') = CacheInvalidateByAdr (va,pa,pm,dc) state
            in
              (t' ≪ ns ‖ i') ≪ (nl + 2) ≠ (t ≪ ns ‖ i) ≪ (nl + 2) ⇒
              Hit (va,pa,dc) state ⇒
              Hit (va',pa',dc) state ⇒
              (CellRead (i',t',wi',dc) = CellRead (i',t',wi',dc')))

   [CacheInvalidate_dcEQpm'_thm]  Theorem

      [oracles: DISK_THM, cheat] [axioms: ] []
      |- ∀va pa pm dc va' pa' state.
           (let (dc',pm') = CacheInvalidateByAdr (va,pa,pm,dc) state in
            let (i,t,wi) = lineSpec (va,pa) state in
            let (i',t',wi') = lineSpec (va',pa') state in
            let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let nl = w2n state.DC.ctr.DminLine
            in
              Hit (va,pa,dc) state ⇒
              invariant_cache ⇒
              LineDirty (i',t',dc) ⇒
              ((t' ≪ ns ‖ i') ≪ (nl + 2) = (t ≪ ns ‖ i) ≪ (nl + 2)) ⇒
              (CellRead (i',t',wi',dc) = v2w (read_mem32 (pa',pm'))))

   [CacheInvalidate_hitDc'_diffAddr_thm]  Theorem

      |- ∀va pa pm dc va' pa' state.
           (let (i,t,wi) = lineSpec (va,pa) state in
            let (i',t',wi') = lineSpec (va',pa') state in
            let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let nl = w2n state.DC.ctr.DminLine in
            let (dc',pm') = CacheInvalidateByAdr (va,pa,pm,dc) state
            in
              (t' ≪ ns ‖ i') ≪ (nl + 2) ≠ (t ≪ ns ‖ i) ≪ (nl + 2) ⇒
              Hit (va,pa,dc) state ⇒
              Hit (va',pa',dc) state ⇒
              Hit (va',pa',dc') state)

   [CacheInvalidate_keepMiss_diffMsb_thm]  Theorem

      |- ∀va pa pm dc va' pa' state.
           (let (i,t,wi) = lineSpec (va,pa) state in
            let (i',t',wi') = lineSpec (va',pa') state in
            let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let nl = w2n state.DC.ctr.DminLine in
            let (dc',pm') = CacheInvalidateByAdr (va,pa,pm,dc) state
            in
              (t' ≪ ns ‖ i') ≪ (nl + 2) ≠ (t ≪ ns ‖ i) ≪ (nl + 2) ⇒
              Hit (va,pa,dc) state ⇒
              ¬Hit (va',pa',dc) state ⇒
              ¬Hit (va',pa',dc') state)

   [CacheInvalidate_missDc'_thm]  Theorem

      |- ∀va pa pm dc state.
           (let (dc',pm') = CacheInvalidateByAdr (va,pa,pm,dc) state
            in
              Hit (va,pa,dc) state ⇒ ¬Hit (va,pa,dc') state)

   [CacheRead_lfoldEQval_SameAddress_thm]  Theorem

      |- ∀va pa pm dc state.
           (let (dc',pm',vlc) = CacheRead (va,pa,pm,dc) state in
            let (_,_,vlc') = CacheRead (va,pa,pm',dc') state
            in
              vlc = vlc')

   [CacheWrite_DiffPa_EqReadMemPa'_thm]  Theorem

      [oracles: DISK_THM, cheat] [axioms: ] []
      |- ∀va pa data pm dc va' pa' state.
           (let (dc',pm') = CacheWrite (va,pa,data,pm,dc) state in
            let (i,t,wi) = lineSpec (va,pa) state in
            let (i',t',wi') = lineSpec (va',pa') state
            in
              pa ≠ pa' ⇒
              invariant_cache ⇒
              ¬Hit (va',pa',dc) state ⇒
              ¬Hit (va',pa',dc') state ⇒
              (v2w (read_mem32 (pa',pm)) = v2w (read_mem32 (pa',pm'))))

   [CacheWrite_DiffPa_EqReadMemPa'_thm3]  Theorem

      [oracles: DISK_THM, cheat] [axioms: ] []
      |- ∀va pa data pm dc va' pa' state.
           (let (dc',pm') = CacheWrite (va,pa,data,pm,dc) state in
            let (i,t,wi) = lineSpec (va,pa) state in
            let (i',t',wi') = lineSpec (va',pa') state
            in
              pa ≠ pa' ⇒
              invariant_cache ⇒
              ¬Hit (va',pa',dc) state ⇒
              Hit (va',pa',dc') state ⇒
              (v2w (read_mem32 (pa',pm)) = v2w (read_mem32 (pa',pm'))))

   [Fill_someEPevict_dcEQpm'_thm]  Theorem

      [oracles: DISK_THM, cheat] [axioms: ] []
      |- ∀va pa va' pa' pm dc x state.
           (let (dc',pm') = Fill (va,pa,pm,dc) state in
            let (i,t,wi) = lineSpec (va,pa) state in
            let (i',t',wi') = lineSpec (va',pa') state in
            let nl = w2n state.DC.ctr.DminLine
            in
              LineDirty (i',t',dc) ⇒
              pa ≠ pa' ∧ (i' = i) ⇒
              invariant_cache ⇒
              (t' = THE (SOME x)) ⇒
              (EP ((dc i).hist,t,dc) = SOME x) ⇒
              (CellRead (i',t',wi',dc) = v2w (read_mem32 (pa',pm'))))

   [Miss_After_Evict_th]  Theorem

      |- ∀va pa pm dc t' state.
           (let (i,t,wi) = lineSpec (va,pa) state in
            let (dc',pm') = Fill (va,pa,pm,dc) state
            in
              (EP ((dc i).hist,t,dc) = SOME t') ⇒
              ¬Hit (va,pa,dc) state ⇒
              invariant_cache ⇒
              ((dc' i).sl t' = NONE))

   [adr_neq2_thm]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀a b c n.
           (let bmM = 0xFFFFFFFFFFFFw ⋙ n in
            let bmL = ¬(0xFFFFFFFFFFFFw ⋙ n ≪ n)
            in
              n < 48 ⇒
              (a && bmM = a) ∧ (b && bmL = b) ∧ (c && bmL = c) ⇒
              b ≠ c ⇒
              (a ≪ n ‖ b) ≠ (a ≪ n ‖ c))

   [adr_neq3_thm]  Theorem

      |- ∀a b c n.
           (let bmM = 0xFFFFFFFFFFFFw ⋙ n in
            let bmL = ¬(0xFFFFFFFFFFFFw ⋙ n ≪ n)
            in
              n < 48 ⇒
              (a && bmL = a) ∧ (b && bmM = b) ∧ (c && bmM = c) ⇒
              (b ≪ n ‖ a) ≠ (c ≪ n ‖ a) ⇒
              b ≠ c)

   [adr_neq_thm]  Theorem

      |- ∀a b c d n.
           (let bmM = 0xFFFFFFFFFFFFw ⋙ n in
            let bmL = ¬(0xFFFFFFFFFFFFw ⋙ n ≪ n)
            in
              n < 48 ⇒
              (a && bmM = a) ∧ (b && bmM = b) ⇒
              (c && bmL = c) ∧ (d && bmL = d) ⇒
              a ≪ n ≠ b ≪ n ⇒
              (a ≪ n ‖ c) ≠ (b ≪ n ‖ d))

   [cacheRead_hit_thm]  Theorem

      |- ∀va pa pm dc state.
           (let (dc',pm',vlc) = CacheRead (va,pa,pm,dc) state in
            let (i,t,wi) = lineSpec (va,pa) state in
            let vlc' = CellRead (i,t,wi,dc)
            in
              Hit (va,pa,dc) state ⇒ (vlc' = v2w vlc))

   [cacheRead_miss_thm]  Theorem

      [oracles: DISK_THM, cheat] [axioms: ] []
      |- ∀va pa pm dc state.
           (let (dc',pm',vlc) = CacheRead (va,pa,pm,dc) state in
            let (i,t,wi) = lineSpec (va,pa) state in
            let vlm = v2w (read_mem32 (pa,pm))
            in
              invariant_cache ⇒ ¬Hit (va,pa,dc) state ⇒ (vlm = v2w vlc))

   [cacheRead_paHitdc'_thm]  Theorem

      |- ∀va pa pm dc state.
           (let (dc',pm',_) = CacheRead (va,pa,pm,dc) state
            in
              Hit (va,pa,dc') state)

   [cacheWrite_paHitdc'_thm]  Theorem

      |- ∀va pa data pm dc state.
           (let (dc',pm') = CacheWrite (va,pa,data,pm,dc) state
            in
              Hit (va,pa,dc') state)

   [cacheWrite_paNOTCHGpm_thm]  Theorem

      [oracles: DISK_THM, cheat] [axioms: ] []
      |- ∀va pa data pm dc state.
           (let (dc',pm') = CacheWrite (va,pa,data,pm,dc) state
            in
              invariant_cache ⇒
              (v2w (read_mem32 (pa,pm)) = v2w (read_mem32 (pa,pm'))))

   [cacheWrite_read_thm]  Theorem

      |- ∀va pa data pm dc state.
           (let (dc',pm') = CacheWrite (va,pa,data,pm,dc) state in
            let (a,b,vl) = CacheRead (va,pa,pm',dc') state
            in
              v2w vl = data.value)

   [cacheWrite_setCell_thm]  Theorem

      |- ∀va pa data pm dc state.
           (let (dc',pm') = CacheWrite (va,pa,data,pm,dc) state in
            let (i,t,wi) = lineSpec (va,pa) state
            in
              ((THE ((dc' i).sl t)).dirty ⇔ data.flag) ∧
              ((THE ((dc' i).sl t)).value (n2w wi) = data.value))

   [cellFill_memeq_thm]  Theorem

      |- ∀wi pa pm.
           (let sval = CellFill (wi,pa,pm) (n2w wi)
            in
              sval = v2w (read_mem32 (pa ‖ n2w wi ≪ 2,pm)))

   [fill_dcEQpm_thm]  Theorem

      |- ∀va pa pm dc state.
           (let (dc',pm') = Fill (va,pa,pm,dc) state in
            let (i,t,wi) = lineSpec (va,pa) state
            in
              2 ** w2n state.DC.ctr.DminLine − 1 ≤ dimword (:15) ⇒
              invariant_cache ⇒
              wi ≤ 2 ** w2n state.DC.ctr.DminLine − 1 ⇒
              (CellRead (i,t,wi,dc') = v2w (read_mem32 (pa,pm'))))

   [fill_hit_thm]  Theorem

      |- ∀va pa pm dc state.
           (let (dc',pm') = Fill (va,pa,pm,dc) state in
            let (i,t,wi) = lineSpec (va,pa) state
            in
              Hit (va,pa,dc') state)

   [fill_pm'EQpm_diffIn_thm]  Theorem

      [oracles: DISK_THM, cheat] [axioms: ] []
      |- ∀va pa pm dc va' pa' state.
           (let (dc',pm') = Fill (va,pa,pm,dc) state
            in
              invariant_cache ⇒
              ¬Hit (va',pa',dc) state ⇒
              (v2w (read_mem32 (pa',pm')) = v2w (read_mem32 (pa',pm))))

   [lineSpec_eq_thm]  Theorem

      |- ∀s s' pa va.
           invariant_cache ⇒ (lineSpec (va,pa) s = lineSpec (va,pa) s')

   [lineSpec_thm]  Theorem

      |- ∀va pa state.
           (let (i,t,wi) = lineSpec (va,pa) state in
            let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let nl = w2n state.DC.ctr.DminLine
            in
              invariant_cache ⇒
              (pa = (t ≪ (ns + nl + 2) ‖ i ≪ (nl + 2)) ‖ n2w wi ≪ 2))

   [linefill_hit_t]  Theorem

      |- ∀h i t pm dc state n.
           (let (sl,_) = LineFill (h,i,t,pm,dc,n) state in
            let sn = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let ln = w2n state.DC.ctr.DminLine
            in
              ∀wi.
                (let pa = t ≪ (sn + ln + 2) ‖ i ≪ (ln + 2) ‖ n2w wi ≪ 2
                 in
                   IS_SOME (sl t)))

   [linefill_memeq_t]  Theorem

      |- ∀h i t pm dc n state.
           (let (sl,_) = LineFill (h,i,t,pm,dc,n) state in
            let sn = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let ln = w2n state.DC.ctr.DminLine
            in
              n ≤ dimword (:15) ⇒
              ∀wi.
                wi ≤ n ⇒
                (let pa = t ≪ (sn + ln + 2) ‖ i ≪ (ln + 2) ‖ n2w wi ≪ 2
                 in
                   (THE (sl t)).value (n2w wi) = v2w (read_mem32 (pa,pm))))

   [lt_mod_thm]  Theorem

      |- ∀a b c d. a < b ∧ b ≤ c ∧ c < d ⇒ a MOD d < b MOD d

   [msbEqAdrs_Hit_dc_thm]  Theorem

      [oracles: DISK_THM, cheat] [axioms: ] []
      |- ∀va pa dc va' pa' state.
           invariant_cache ⇒
           Hit (va,pa,dc) state ⇒
           (msb_extract va pa state = msb_extract va' pa' state) ⇒
           Hit (va',pa',dc) state

   [shift_add_thm]  Theorem

      |- ∀w1 w2 n m. w1 ≪ (n + m) ‖ w2 ≪ m = (w1 ≪ n ‖ w2) ≪ m

   [si_extract_thm]  Theorem

      |- ∀va pa state.
           (let sid = si (va,pa) state in
            let b = w2n state.DC.ctr.DminLine + 1 in
            let s = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))
            in
              sid = (s + b >< b + 1) pa)

   [tag_extract_thm]  Theorem

      |- ∀va pa state.
           (let tg = tag (va,pa) state in
            let ps = LENGTH (w2v pa) in
            let bi = w2n state.DC.ctr.DminLine + 1 in
            let st = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w))
            in
              tg = (ps − 1 >< bi + st + 1) pa)

   [wIdx_extract_thm]  Theorem

      |- ∀pa state.
           (let wi = wIdx pa state
            in
              wi = (w2n state.DC.ctr.DminLine + 1 >< 2) pa)

   [wIdx_lt_dimword48_thm]  Theorem

      |- ∀va pa state.
           (let (i,t,wi) = lineSpec (va,pa) state
            in
              wi = wi MOD 281474976710656)

   [wi_lt_line_size_thm]  Theorem

      |- ∀va pa state.
           (let (i,t,wi) = lineSpec (va,pa) state in
            let nl = w2n state.DC.ctr.DminLine
            in
              wi ≤ 2 ** nl − 1)

   [word_log2_lt_adrSize]  Theorem

      |- ∀v. v ≠ 0w ⇒ w2n (word_log2 v) < 48

   [write_read_thm]  Theorem

      |- ∀a v m.
           (let m' = write_mem32 (a,m,v) in read_mem32 (a,m') = w2v v)

   [write_read_unch_thm]  Theorem

      |- ∀a a' v m m'.
           a' + 3w <₊ a ∧ a' + 3w ≥₊ 3w ∧ a + 3w ≥₊ 3w ∨
           a' >₊ a + 3w ∧ a' + 3w ≥₊ 3w ∧ a + 3w ≥₊ 3w ⇒
           (m' = write_mem32 (a,m,v)) ⇒
           (read_mem32 (a',m') = read_mem32 (a',m))

   [writeback_mem_eq_thm]  Theorem

      |- ∀pa va pm slval state i' t' wi'.
           (let (i,t,wi) = lineSpec (va,pa) state in
            let pm' = WriteBack (i',t',wi',pm,slval) state in
            let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let nl = w2n state.DC.ctr.DminLine
            in
              (t' ≪ ns ‖ i') ≪ (nl + 2) ≠ (t ≪ ns ‖ i) ≪ (nl + 2) ⇒
              invariant_cache ⇒
              (v2w (read_mem32 (pa,pm)) = v2w (read_mem32 (pa,pm'))))

   [writebackline_mem_eq_thm]  Theorem

      |- ∀i' t' pm dc n va pa state.
           (let (i,t,wi) = lineSpec (va,pa) state in
            let (dc',pm') = WriteBackLine (i',t',pm,dc,n) state in
            let ns = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let nl = w2n state.DC.ctr.DminLine
            in
              (t' ≪ ns ‖ i') ≪ (nl + 2) ≠ (t ≪ ns ‖ i) ≪ (nl + 2) ⇒
              n ≤ dimword (:15) ⇒
              invariant_cache ⇒
              (v2w (read_mem32 (pa,pm)) = v2w (read_mem32 (pa,pm'))))

   [wrtBckLine_dcEQpm'_thm]  Theorem

      [oracles: DISK_THM, cheat] [axioms: ] []
      |- ∀i t pm dc n state.
           (let (dc',pm') = WriteBackLine (i,t,pm,dc,n) state in
            let sn = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let ln = w2n state.DC.ctr.DminLine
            in
              n ≤ dimword (:15) ⇒
              ∀wi.
                wi ≤ n ⇒
                (let pa = t ≪ (sn + ln + 2) ‖ i ≪ (ln + 2) ‖ n2w wi ≪ 2
                 in
                   invariant_cache ⇒
                   LineDirty (i,t,dc) ⇒
                   (CellRead (i,t,wi,dc) = v2w (read_mem32 (pa,pm')))))

   [wrtBckLine_pmEQpm'IfNotDirty_thm]  Theorem

      |- ∀i t pm dc n state.
           (let (_,pm') = WriteBackLine (i,t,pm,dc,n) state
            in
              ¬LineDirty (i,t,dc) ⇒
              ∀pa'. v2w (read_mem32 (pa',pm)) = v2w (read_mem32 (pa',pm')))

   [wrtBck_dirty_thm]  Theorem

      |- ∀i t pm dc n state.
           (let (dc',pm') = WriteBackLine (i,t,pm,dc,n) state
            in
              n ≤ dimword (:15) ⇒ ∀wi. wi ≤ n ⇒ ¬LineDirty (i,t,dc'))

   [wrtBck_memory_thm]  Theorem

      [oracles: DISK_THM, cheat] [axioms: ] []
      |- ∀i t pm dc state n.
           (let (dc',pm') = WriteBackLine (i,t,pm,dc,n) state in
            let sn = w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) in
            let ln = w2n state.DC.ctr.DminLine
            in
              n ≤ dimword (:15) ⇒
              ∀wi.
                wi ≤ n ⇒
                (let pa = t ≪ (sn + ln + 2) ‖ i ≪ (ln + 2) ‖ n2w wi ≪ 2
                 in
                   invariant_cache ⇒
                   LineDirty (i,t,dc) ⇒
                   (CellRead (i,t,wi,dc') = v2w (read_mem32 (pa,pm')))))


*)
end