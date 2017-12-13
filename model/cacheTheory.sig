signature cacheTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val Alias_def : thm
    val CACHE_CONFIG_TY_DEF : thm
    val CACHE_CONFIG_case_def : thm
    val CACHE_CONFIG_ccsidr : thm
    val CACHE_CONFIG_ccsidr_fupd : thm
    val CACHE_CONFIG_csselr_el1 : thm
    val CACHE_CONFIG_csselr_el1_fupd : thm
    val CACHE_CONFIG_ctr : thm
    val CACHE_CONFIG_ctr_fupd : thm
    val CACHE_CONFIG_size_def : thm
    val CCSIDR_Associativity : thm
    val CCSIDR_Associativity_fupd : thm
    val CCSIDR_LineSize : thm
    val CCSIDR_LineSize_fupd : thm
    val CCSIDR_NumSets : thm
    val CCSIDR_NumSets_fupd : thm
    val CCSIDR_RA : thm
    val CCSIDR_RA_fupd : thm
    val CCSIDR_TY_DEF : thm
    val CCSIDR_WA : thm
    val CCSIDR_WA_fupd : thm
    val CCSIDR_WB : thm
    val CCSIDR_WB_fupd : thm
    val CCSIDR_WT : thm
    val CCSIDR_WT_fupd : thm
    val CCSIDR_case_def : thm
    val CCSIDR_size_def : thm
    val CSET_TY_DEF : thm
    val CSET_case_def : thm
    val CSET_hist : thm
    val CSET_hist_fupd : thm
    val CSET_size_def : thm
    val CSET_sl : thm
    val CSET_sl_fupd : thm
    val CSSELR_EL1_InD : thm
    val CSSELR_EL1_InD_fupd : thm
    val CSSELR_EL1_Level : thm
    val CSSELR_EL1_Level_fupd : thm
    val CSSELR_EL1_RES0 : thm
    val CSSELR_EL1_RES0_fupd : thm
    val CSSELR_EL1_TY_DEF : thm
    val CSSELR_EL1_case_def : thm
    val CSSELR_EL1_size_def : thm
    val CTR_CWG : thm
    val CTR_CWG_fupd : thm
    val CTR_DminLine : thm
    val CTR_DminLine_fupd : thm
    val CTR_ERG : thm
    val CTR_ERG_fupd : thm
    val CTR_IminLine : thm
    val CTR_IminLine_fupd : thm
    val CTR_L1Ip : thm
    val CTR_L1Ip_fupd : thm
    val CTR_RES00 : thm
    val CTR_RES00_fupd : thm
    val CTR_RES01 : thm
    val CTR_RES01_fupd : thm
    val CTR_RES1 : thm
    val CTR_RES1_fupd : thm
    val CTR_TY_DEF : thm
    val CTR_case_def : thm
    val CTR_size_def : thm
    val CacheCleanByAdr_def : thm
    val CacheInvalidateByAdr_def : thm
    val CacheRead_def : thm
    val CacheWrite_def : thm
    val CellFill_def : thm
    val CellRead_def : thm
    val EP_def : thm
    val EvictAlias_def : thm
    val Evict_def : thm
    val Fill_def : thm
    val Hit_def : thm
    val LineDirty_def : thm
    val LineFill_def : thm
    val SLVAL_TY_DEF : thm
    val SLVAL_case_def : thm
    val SLVAL_dirty : thm
    val SLVAL_dirty_fupd : thm
    val SLVAL_size_def : thm
    val SLVAL_value : thm
    val SLVAL_value_fupd : thm
    val Touch_def : thm
    val WriteBackLine_def : thm
    val WriteBack_def : thm
    val actions_BIJ : thm
    val actions_CASE : thm
    val actions_TY_DEF : thm
    val actions_size_def : thm
    val cache_state_DC : thm
    val cache_state_DC_fupd : thm
    val cache_state_TY_DEF : thm
    val cache_state_case_def : thm
    val cache_state_exception : thm
    val cache_state_exception_fupd : thm
    val cache_state_size_def : thm
    val exception_BIJ : thm
    val exception_CASE : thm
    val exception_TY_DEF : thm
    val exception_size_def : thm
    val lDirty_def : thm
    val lineSpec_def : thm
    val mv_def : thm
    val raise'exception_def : thm
    val read_mem32_def : thm
    val read_mem_inner_def : thm
    val rec'CCSIDR_def : thm
    val rec'CSSELR_EL1_def : thm
    val rec'CTR_def : thm
    val reg'CCSIDR_def : thm
    val reg'CSSELR_EL1_def : thm
    val reg'CTR_def : thm
    val si_def : thm
    val tag_def : thm
    val wIdx_def : thm
    val wrTyp_TY_DEF : thm
    val wrTyp_case_def : thm
    val wrTyp_flag : thm
    val wrTyp_flag_fupd : thm
    val wrTyp_size_def : thm
    val wrTyp_value : thm
    val wrTyp_value_fupd : thm
    val write'rec'CCSIDR_def : thm
    val write'rec'CSSELR_EL1_def : thm
    val write'rec'CTR_def : thm
    val write'reg'CCSIDR_def : thm
    val write'reg'CSSELR_EL1_def : thm
    val write'reg'CTR_def : thm

  (*  Theorems  *)
    val CACHE_CONFIG_11 : thm
    val CACHE_CONFIG_Axiom : thm
    val CACHE_CONFIG_accessors : thm
    val CACHE_CONFIG_accfupds : thm
    val CACHE_CONFIG_case_cong : thm
    val CACHE_CONFIG_component_equality : thm
    val CACHE_CONFIG_fn_updates : thm
    val CACHE_CONFIG_fupdcanon : thm
    val CACHE_CONFIG_fupdcanon_comp : thm
    val CACHE_CONFIG_fupdfupds : thm
    val CACHE_CONFIG_fupdfupds_comp : thm
    val CACHE_CONFIG_induction : thm
    val CACHE_CONFIG_literal_11 : thm
    val CACHE_CONFIG_literal_nchotomy : thm
    val CACHE_CONFIG_nchotomy : thm
    val CACHE_CONFIG_updates_eq_literal : thm
    val CCSIDR_11 : thm
    val CCSIDR_Axiom : thm
    val CCSIDR_accessors : thm
    val CCSIDR_accfupds : thm
    val CCSIDR_case_cong : thm
    val CCSIDR_component_equality : thm
    val CCSIDR_fn_updates : thm
    val CCSIDR_fupdcanon : thm
    val CCSIDR_fupdcanon_comp : thm
    val CCSIDR_fupdfupds : thm
    val CCSIDR_fupdfupds_comp : thm
    val CCSIDR_induction : thm
    val CCSIDR_literal_11 : thm
    val CCSIDR_literal_nchotomy : thm
    val CCSIDR_nchotomy : thm
    val CCSIDR_updates_eq_literal : thm
    val CSET_11 : thm
    val CSET_Axiom : thm
    val CSET_accessors : thm
    val CSET_accfupds : thm
    val CSET_case_cong : thm
    val CSET_component_equality : thm
    val CSET_fn_updates : thm
    val CSET_fupdcanon : thm
    val CSET_fupdcanon_comp : thm
    val CSET_fupdfupds : thm
    val CSET_fupdfupds_comp : thm
    val CSET_induction : thm
    val CSET_literal_11 : thm
    val CSET_literal_nchotomy : thm
    val CSET_nchotomy : thm
    val CSET_updates_eq_literal : thm
    val CSSELR_EL1_11 : thm
    val CSSELR_EL1_Axiom : thm
    val CSSELR_EL1_accessors : thm
    val CSSELR_EL1_accfupds : thm
    val CSSELR_EL1_case_cong : thm
    val CSSELR_EL1_component_equality : thm
    val CSSELR_EL1_fn_updates : thm
    val CSSELR_EL1_fupdcanon : thm
    val CSSELR_EL1_fupdcanon_comp : thm
    val CSSELR_EL1_fupdfupds : thm
    val CSSELR_EL1_fupdfupds_comp : thm
    val CSSELR_EL1_induction : thm
    val CSSELR_EL1_literal_11 : thm
    val CSSELR_EL1_literal_nchotomy : thm
    val CSSELR_EL1_nchotomy : thm
    val CSSELR_EL1_updates_eq_literal : thm
    val CTR_11 : thm
    val CTR_Axiom : thm
    val CTR_accessors : thm
    val CTR_accfupds : thm
    val CTR_case_cong : thm
    val CTR_component_equality : thm
    val CTR_fn_updates : thm
    val CTR_fupdcanon : thm
    val CTR_fupdcanon_comp : thm
    val CTR_fupdfupds : thm
    val CTR_fupdfupds_comp : thm
    val CTR_induction : thm
    val CTR_literal_11 : thm
    val CTR_literal_nchotomy : thm
    val CTR_nchotomy : thm
    val CTR_updates_eq_literal : thm
    val EXISTS_CACHE_CONFIG : thm
    val EXISTS_CCSIDR : thm
    val EXISTS_CSET : thm
    val EXISTS_CSSELR_EL1 : thm
    val EXISTS_CTR : thm
    val EXISTS_SLVAL : thm
    val EXISTS_cache_state : thm
    val EXISTS_wrTyp : thm
    val FORALL_CACHE_CONFIG : thm
    val FORALL_CCSIDR : thm
    val FORALL_CSET : thm
    val FORALL_CSSELR_EL1 : thm
    val FORALL_CTR : thm
    val FORALL_SLVAL : thm
    val FORALL_cache_state : thm
    val FORALL_wrTyp : thm
    val SLVAL_11 : thm
    val SLVAL_Axiom : thm
    val SLVAL_accessors : thm
    val SLVAL_accfupds : thm
    val SLVAL_case_cong : thm
    val SLVAL_component_equality : thm
    val SLVAL_fn_updates : thm
    val SLVAL_fupdcanon : thm
    val SLVAL_fupdcanon_comp : thm
    val SLVAL_fupdfupds : thm
    val SLVAL_fupdfupds_comp : thm
    val SLVAL_induction : thm
    val SLVAL_literal_11 : thm
    val SLVAL_literal_nchotomy : thm
    val SLVAL_nchotomy : thm
    val SLVAL_updates_eq_literal : thm
    val actions2num_11 : thm
    val actions2num_ONTO : thm
    val actions2num_num2actions : thm
    val actions2num_thm : thm
    val actions_Axiom : thm
    val actions_EQ_actions : thm
    val actions_case_cong : thm
    val actions_case_def : thm
    val actions_distinct : thm
    val actions_induction : thm
    val actions_nchotomy : thm
    val cache_state_11 : thm
    val cache_state_Axiom : thm
    val cache_state_accessors : thm
    val cache_state_accfupds : thm
    val cache_state_case_cong : thm
    val cache_state_component_equality : thm
    val cache_state_fn_updates : thm
    val cache_state_fupdcanon : thm
    val cache_state_fupdcanon_comp : thm
    val cache_state_fupdfupds : thm
    val cache_state_fupdfupds_comp : thm
    val cache_state_induction : thm
    val cache_state_literal_11 : thm
    val cache_state_literal_nchotomy : thm
    val cache_state_nchotomy : thm
    val cache_state_updates_eq_literal : thm
    val datatype_CACHE_CONFIG : thm
    val datatype_CCSIDR : thm
    val datatype_CSET : thm
    val datatype_CSSELR_EL1 : thm
    val datatype_CTR : thm
    val datatype_SLVAL : thm
    val datatype_actions : thm
    val datatype_cache_state : thm
    val datatype_exception : thm
    val datatype_wrTyp : thm
    val exception2num_11 : thm
    val exception2num_ONTO : thm
    val exception2num_num2exception : thm
    val exception2num_thm : thm
    val exception_Axiom : thm
    val exception_EQ_exception : thm
    val exception_case_cong : thm
    val exception_case_def : thm
    val exception_distinct : thm
    val exception_induction : thm
    val exception_nchotomy : thm
    val num2actions_11 : thm
    val num2actions_ONTO : thm
    val num2actions_actions2num : thm
    val num2actions_thm : thm
    val num2exception_11 : thm
    val num2exception_ONTO : thm
    val num2exception_exception2num : thm
    val num2exception_thm : thm
    val wrTyp_11 : thm
    val wrTyp_Axiom : thm
    val wrTyp_accessors : thm
    val wrTyp_accfupds : thm
    val wrTyp_case_cong : thm
    val wrTyp_component_equality : thm
    val wrTyp_fn_updates : thm
    val wrTyp_fupdcanon : thm
    val wrTyp_fupdcanon_comp : thm
    val wrTyp_fupdfupds : thm
    val wrTyp_fupdfupds_comp : thm
    val wrTyp_induction : thm
    val wrTyp_literal_11 : thm
    val wrTyp_literal_nchotomy : thm
    val wrTyp_nchotomy : thm
    val wrTyp_updates_eq_literal : thm

  val cache_grammars : type_grammar.grammar * term_grammar.grammar

  val inventory: {Thy: string, T: string list, C: string list, N: int list}
(*
   [bitstring] Parent theory of "cache"

   [integer_word] Parent theory of "cache"

   [machine_ieee] Parent theory of "cache"

   [state_transformer] Parent theory of "cache"

   [Alias_def]  Definition

      |- ∀va pa dc.
           Alias (va,pa,dc) =
           (λstate.
              (let (_,t,_1) = lineSpec (va,pa) state
               in
                 FST
                   (SND
                      (FOR
                         (0,
                          (w2n state.DC.ccsidr.NumSets + 1) *
                          (w2n state.DC.ccsidr.Associativity + 1) − 1,
                          (λi state.
                             ((),
                              if
                                IS_SOME ((FST (SND state) (n2w i)).sl t)
                              then
                                (SOME (n2w i),SND state)
                              else state))) (ARB,dc,state)))))

   [CACHE_CONFIG_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'CACHE_CONFIG' .
                  (∀a0'.
                     (∃a0 a1 a2.
                        a0' =
                        (λa0 a1 a2.
                           ind_type$CONSTR 0 (a0,a1,a2)
                             (λn. ind_type$BOTTOM)) a0 a1 a2) ⇒
                     'CACHE_CONFIG' a0') ⇒
                  'CACHE_CONFIG' a0') rep

   [CACHE_CONFIG_case_def]  Definition

      |- ∀a0 a1 a2 f.
           CACHE_CONFIG_CASE (CACHE_CONFIG a0 a1 a2) f = f a0 a1 a2

   [CACHE_CONFIG_ccsidr]  Definition

      |- ∀C C0 C1. (CACHE_CONFIG C C0 C1).ccsidr = C

   [CACHE_CONFIG_ccsidr_fupd]  Definition

      |- ∀f C C0 C1.
           CACHE_CONFIG C C0 C1 with ccsidr updated_by f =
           CACHE_CONFIG (f C) C0 C1

   [CACHE_CONFIG_csselr_el1]  Definition

      |- ∀C C0 C1. (CACHE_CONFIG C C0 C1).csselr_el1 = C0

   [CACHE_CONFIG_csselr_el1_fupd]  Definition

      |- ∀f C C0 C1.
           CACHE_CONFIG C C0 C1 with csselr_el1 updated_by f =
           CACHE_CONFIG C (f C0) C1

   [CACHE_CONFIG_ctr]  Definition

      |- ∀C C0 C1. (CACHE_CONFIG C C0 C1).ctr = C1

   [CACHE_CONFIG_ctr_fupd]  Definition

      |- ∀f C C0 C1.
           CACHE_CONFIG C C0 C1 with ctr updated_by f =
           CACHE_CONFIG C C0 (f C1)

   [CACHE_CONFIG_size_def]  Definition

      |- ∀a0 a1 a2.
           CACHE_CONFIG_size (CACHE_CONFIG a0 a1 a2) =
           1 + (CCSIDR_size a0 + (CSSELR_EL1_size a1 + CTR_size a2))

   [CCSIDR_Associativity]  Definition

      |- ∀c c0 c1 b b0 b1 b2. (CCSIDR c c0 c1 b b0 b1 b2).Associativity = c

   [CCSIDR_Associativity_fupd]  Definition

      |- ∀f c c0 c1 b b0 b1 b2.
           CCSIDR c c0 c1 b b0 b1 b2 with Associativity updated_by f =
           CCSIDR (f c) c0 c1 b b0 b1 b2

   [CCSIDR_LineSize]  Definition

      |- ∀c c0 c1 b b0 b1 b2. (CCSIDR c c0 c1 b b0 b1 b2).LineSize = c0

   [CCSIDR_LineSize_fupd]  Definition

      |- ∀f c c0 c1 b b0 b1 b2.
           CCSIDR c c0 c1 b b0 b1 b2 with LineSize updated_by f =
           CCSIDR c (f c0) c1 b b0 b1 b2

   [CCSIDR_NumSets]  Definition

      |- ∀c c0 c1 b b0 b1 b2. (CCSIDR c c0 c1 b b0 b1 b2).NumSets = c1

   [CCSIDR_NumSets_fupd]  Definition

      |- ∀f c c0 c1 b b0 b1 b2.
           CCSIDR c c0 c1 b b0 b1 b2 with NumSets updated_by f =
           CCSIDR c c0 (f c1) b b0 b1 b2

   [CCSIDR_RA]  Definition

      |- ∀c c0 c1 b b0 b1 b2. (CCSIDR c c0 c1 b b0 b1 b2).RA ⇔ b

   [CCSIDR_RA_fupd]  Definition

      |- ∀f c c0 c1 b b0 b1 b2.
           CCSIDR c c0 c1 b b0 b1 b2 with RA updated_by f =
           CCSIDR c c0 c1 (f b) b0 b1 b2

   [CCSIDR_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'CCSIDR' .
                  (∀a0'.
                     (∃a0 a1 a2 a3 a4 a5 a6.
                        a0' =
                        (λa0 a1 a2 a3 a4 a5 a6.
                           ind_type$CONSTR 0 (a0,a1,a2,a3,a4,a5,a6)
                             (λn. ind_type$BOTTOM)) a0 a1 a2 a3 a4 a5 a6) ⇒
                     'CCSIDR' a0') ⇒
                  'CCSIDR' a0') rep

   [CCSIDR_WA]  Definition

      |- ∀c c0 c1 b b0 b1 b2. (CCSIDR c c0 c1 b b0 b1 b2).WA ⇔ b0

   [CCSIDR_WA_fupd]  Definition

      |- ∀f c c0 c1 b b0 b1 b2.
           CCSIDR c c0 c1 b b0 b1 b2 with WA updated_by f =
           CCSIDR c c0 c1 b (f b0) b1 b2

   [CCSIDR_WB]  Definition

      |- ∀c c0 c1 b b0 b1 b2. (CCSIDR c c0 c1 b b0 b1 b2).WB ⇔ b1

   [CCSIDR_WB_fupd]  Definition

      |- ∀f c c0 c1 b b0 b1 b2.
           CCSIDR c c0 c1 b b0 b1 b2 with WB updated_by f =
           CCSIDR c c0 c1 b b0 (f b1) b2

   [CCSIDR_WT]  Definition

      |- ∀c c0 c1 b b0 b1 b2. (CCSIDR c c0 c1 b b0 b1 b2).WT ⇔ b2

   [CCSIDR_WT_fupd]  Definition

      |- ∀f c c0 c1 b b0 b1 b2.
           CCSIDR c c0 c1 b b0 b1 b2 with WT updated_by f =
           CCSIDR c c0 c1 b b0 b1 (f b2)

   [CCSIDR_case_def]  Definition

      |- ∀a0 a1 a2 a3 a4 a5 a6 f.
           CCSIDR_CASE (CCSIDR a0 a1 a2 a3 a4 a5 a6) f =
           f a0 a1 a2 a3 a4 a5 a6

   [CCSIDR_size_def]  Definition

      |- ∀a0 a1 a2 a3 a4 a5 a6.
           CCSIDR_size (CCSIDR a0 a1 a2 a3 a4 a5 a6) =
           1 +
           (bool_size a3 + (bool_size a4 + (bool_size a5 + bool_size a6)))

   [CSET_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'CSET' .
                  (∀a0'.
                     (∃a0 a1.
                        a0' =
                        (λa0 a1.
                           ind_type$CONSTR 0 (a0,a1) (λn. ind_type$BOTTOM))
                          a0 a1) ⇒
                     'CSET' a0') ⇒
                  'CSET' a0') rep

   [CSET_case_def]  Definition

      |- ∀a0 a1 f. CSET_CASE (CSET a0 a1) f = f a0 a1

   [CSET_hist]  Definition

      |- ∀l f. (CSET l f).hist = l

   [CSET_hist_fupd]  Definition

      |- ∀f0 l f. CSET l f with hist updated_by f0 = CSET (f0 l) f

   [CSET_size_def]  Definition

      |- ∀a0 a1.
           CSET_size (CSET a0 a1) =
           1 +
           list_size (pair_size actions_size (pair_size (λx. x) (λv. 0)))
             a0

   [CSET_sl]  Definition

      |- ∀l f. (CSET l f).sl = f

   [CSET_sl_fupd]  Definition

      |- ∀f0 l f. CSET l f with sl updated_by f0 = CSET l (f0 f)

   [CSSELR_EL1_InD]  Definition

      |- ∀b c c0. (CSSELR_EL1 b c c0).InD ⇔ b

   [CSSELR_EL1_InD_fupd]  Definition

      |- ∀f b c c0.
           CSSELR_EL1 b c c0 with InD updated_by f = CSSELR_EL1 (f b) c c0

   [CSSELR_EL1_Level]  Definition

      |- ∀b c c0. (CSSELR_EL1 b c c0).Level = c

   [CSSELR_EL1_Level_fupd]  Definition

      |- ∀f b c c0.
           CSSELR_EL1 b c c0 with Level updated_by f =
           CSSELR_EL1 b (f c) c0

   [CSSELR_EL1_RES0]  Definition

      |- ∀b c c0. (CSSELR_EL1 b c c0).RES0 = c0

   [CSSELR_EL1_RES0_fupd]  Definition

      |- ∀f b c c0.
           CSSELR_EL1 b c c0 with RES0 updated_by f = CSSELR_EL1 b c (f c0)

   [CSSELR_EL1_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'CSSELR_EL1' .
                  (∀a0'.
                     (∃a0 a1 a2.
                        a0' =
                        (λa0 a1 a2.
                           ind_type$CONSTR 0 (a0,a1,a2)
                             (λn. ind_type$BOTTOM)) a0 a1 a2) ⇒
                     'CSSELR_EL1' a0') ⇒
                  'CSSELR_EL1' a0') rep

   [CSSELR_EL1_case_def]  Definition

      |- ∀a0 a1 a2 f. CSSELR_EL1_CASE (CSSELR_EL1 a0 a1 a2) f = f a0 a1 a2

   [CSSELR_EL1_size_def]  Definition

      |- ∀a0 a1 a2.
           CSSELR_EL1_size (CSSELR_EL1 a0 a1 a2) = 1 + bool_size a0

   [CTR_CWG]  Definition

      |- ∀c c0 c1 c2 c3 c4 c5 b. (CTR c c0 c1 c2 c3 c4 c5 b).CWG = c

   [CTR_CWG_fupd]  Definition

      |- ∀f c c0 c1 c2 c3 c4 c5 b.
           CTR c c0 c1 c2 c3 c4 c5 b with CWG updated_by f =
           CTR (f c) c0 c1 c2 c3 c4 c5 b

   [CTR_DminLine]  Definition

      |- ∀c c0 c1 c2 c3 c4 c5 b. (CTR c c0 c1 c2 c3 c4 c5 b).DminLine = c0

   [CTR_DminLine_fupd]  Definition

      |- ∀f c c0 c1 c2 c3 c4 c5 b.
           CTR c c0 c1 c2 c3 c4 c5 b with DminLine updated_by f =
           CTR c (f c0) c1 c2 c3 c4 c5 b

   [CTR_ERG]  Definition

      |- ∀c c0 c1 c2 c3 c4 c5 b. (CTR c c0 c1 c2 c3 c4 c5 b).ERG = c1

   [CTR_ERG_fupd]  Definition

      |- ∀f c c0 c1 c2 c3 c4 c5 b.
           CTR c c0 c1 c2 c3 c4 c5 b with ERG updated_by f =
           CTR c c0 (f c1) c2 c3 c4 c5 b

   [CTR_IminLine]  Definition

      |- ∀c c0 c1 c2 c3 c4 c5 b. (CTR c c0 c1 c2 c3 c4 c5 b).IminLine = c2

   [CTR_IminLine_fupd]  Definition

      |- ∀f c c0 c1 c2 c3 c4 c5 b.
           CTR c c0 c1 c2 c3 c4 c5 b with IminLine updated_by f =
           CTR c c0 c1 (f c2) c3 c4 c5 b

   [CTR_L1Ip]  Definition

      |- ∀c c0 c1 c2 c3 c4 c5 b. (CTR c c0 c1 c2 c3 c4 c5 b).L1Ip = c3

   [CTR_L1Ip_fupd]  Definition

      |- ∀f c c0 c1 c2 c3 c4 c5 b.
           CTR c c0 c1 c2 c3 c4 c5 b with L1Ip updated_by f =
           CTR c c0 c1 c2 (f c3) c4 c5 b

   [CTR_RES00]  Definition

      |- ∀c c0 c1 c2 c3 c4 c5 b. (CTR c c0 c1 c2 c3 c4 c5 b).RES00 = c4

   [CTR_RES00_fupd]  Definition

      |- ∀f c c0 c1 c2 c3 c4 c5 b.
           CTR c c0 c1 c2 c3 c4 c5 b with RES00 updated_by f =
           CTR c c0 c1 c2 c3 (f c4) c5 b

   [CTR_RES01]  Definition

      |- ∀c c0 c1 c2 c3 c4 c5 b. (CTR c c0 c1 c2 c3 c4 c5 b).RES01 = c5

   [CTR_RES01_fupd]  Definition

      |- ∀f c c0 c1 c2 c3 c4 c5 b.
           CTR c c0 c1 c2 c3 c4 c5 b with RES01 updated_by f =
           CTR c c0 c1 c2 c3 c4 (f c5) b

   [CTR_RES1]  Definition

      |- ∀c c0 c1 c2 c3 c4 c5 b. (CTR c c0 c1 c2 c3 c4 c5 b).RES1 ⇔ b

   [CTR_RES1_fupd]  Definition

      |- ∀f c c0 c1 c2 c3 c4 c5 b.
           CTR c c0 c1 c2 c3 c4 c5 b with RES1 updated_by f =
           CTR c c0 c1 c2 c3 c4 c5 (f b)

   [CTR_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'CTR' .
                  (∀a0'.
                     (∃a0 a1 a2 a3 a4 a5 a6 a7.
                        a0' =
                        (λa0 a1 a2 a3 a4 a5 a6 a7.
                           ind_type$CONSTR 0 (a0,a1,a2,a3,a4,a5,a6,a7)
                             (λn. ind_type$BOTTOM)) a0 a1 a2 a3 a4 a5 a6
                          a7) ⇒
                     'CTR' a0') ⇒
                  'CTR' a0') rep

   [CTR_case_def]  Definition

      |- ∀a0 a1 a2 a3 a4 a5 a6 a7 f.
           CTR_CASE (CTR a0 a1 a2 a3 a4 a5 a6 a7) f =
           f a0 a1 a2 a3 a4 a5 a6 a7

   [CTR_size_def]  Definition

      |- ∀a0 a1 a2 a3 a4 a5 a6 a7.
           CTR_size (CTR a0 a1 a2 a3 a4 a5 a6 a7) = 1 + bool_size a7

   [CacheCleanByAdr_def]  Definition

      |- ∀va pa pm dc.
           CacheCleanByAdr (va,pa,pm,dc) =
           (λstate.
              (let (li,t,_) = lineSpec (va,pa) state in
               let s =
                     if Hit (va,pa,dc) state then
                       (let (ca,mm) =
                              WriteBackLine
                                (li,t,pm,dc,
                                 2 ** w2n state.DC.ctr.DminLine − 1) state
                        in
                          (ca,mm,state))
                     else (dc,pm,state)
               in
                 (FST s,FST (SND s))))

   [CacheInvalidateByAdr_def]  Definition

      |- ∀va pa pm dc.
           CacheInvalidateByAdr (va,pa,pm,dc) =
           (λstate.
              (let (li,t,_) = lineSpec (va,pa) state in
               let s =
                     if Hit (va,pa,dc) state then
                       (let (ca,mm) =
                              WriteBackLine
                                (li,t,pm,dc,
                                 2 ** w2n state.DC.ctr.DminLine − 1) state
                        in
                        let (cacheSl,cacheH) = Evict ((ca li).hist,li,t,ca)
                        in
                        let s3 = (li =+ ca li with sl := cacheSl) ca
                        in
                          ((li =+ s3 li with hist := cacheH) s3,mm,state))
                     else (dc,pm,state)
               in
                 (FST s,FST (SND s))))

   [CacheRead_def]  Definition

      |- ∀va pa pm dc.
           CacheRead (va,pa,pm,dc) =
           (λstate.
              (let (li,t,wi) = lineSpec (va,pa) state
               in
                 if Hit (va,pa,dc) state then
                   (let (cset,cacheH) =
                          Touch ((dc li).hist,li,t,n2w wi,NONE,dc)
                    in
                      ((li =+ dc li with hist := cacheH) dc,pm,
                       w2v ((THE (cset t)).value (n2w wi))))
                 else
                   (let (ca,mm) = Fill (va,pa,pm,dc) state
                    in
                      ((li =+
                        ca li with hist := (a_read,w2n t,li)::(ca li).hist)
                         ca,mm,
                       w2v ((THE ((ca li).sl t)).value (n2w wi))))))

   [CacheWrite_def]  Definition

      |- ∀va pa data pm dc.
           CacheWrite (va,pa,data,pm,dc) =
           (λstate.
              (let (li,t,wi) = lineSpec (va,pa) state
               in
                 if Hit (va,pa,dc) state then
                   (let (cacheSl,cacheH) =
                          Touch ((dc li).hist,li,t,n2w wi,SOME data,dc)
                    in
                    let s0 = (li =+ dc li with sl := cacheSl) dc
                    in
                      ((li =+ s0 li with hist := cacheH) s0,pm))
                 else
                   (let (ca,mm) = Fill (va,pa,pm,dc) state in
                    let (cacheSl,cacheH) =
                          Touch ((ca li).hist,li,t,n2w wi,SOME data,ca)
                    in
                    let s0 = (li =+ dc li with sl := cacheSl) dc
                    in
                      ((li =+ s0 li with hist := cacheH) s0,mm))))

   [CellFill_def]  Definition

      |- ∀wi adr pm.
           CellFill (wi,adr,pm) =
           (n2w wi =+ v2w (read_mem32 (adr ‖ n2w wi ≪ 2,pm))) ARB

   [CellRead_def]  Definition

      |- ∀i t wi dc.
           CellRead (i,t,wi,dc) = (THE ((dc i).sl t)).value (n2w wi)

   [EP_def]  Definition

      |- ∀h t dc. EP (h,t,dc) = ARB

   [EvictAlias_def]  Definition

      |- ∀va pa pm dc.
           EvictAlias (va,pa,pm,dc) =
           (λstate.
              (let (v,s) = (Alias (va,pa,dc) state,dc,pm,state) in
               let (v0,s) =
                     (let (v,s3) =
                            (let (v,s3) =
                                   (let s0 = SND (SND s)
                                    in
                                      (lineSpec (va,pa) s0,s0))
                             in
                               (v,FST (SND s),s3))
                      in
                        (v,FST s,s3))
               in
               let (_,t,_1) = v0
               in
                 if IS_SOME v then
                   (let li = THE v in
                    let (v,s) =
                          (let (v,s3) =
                                 (let (v,s3) =
                                        (let s0 = SND (SND s)
                                         in
                                           (WriteBackLine
                                              (li,t,FST (SND s),FST s,
                                               2 **
                                               w2n
                                                 (SND (SND s)).DC.ctr.
                                                 DminLine − 1) s0,s0))
                                  in
                                    (v,FST (SND s),s3))
                           in
                             (v,FST s,s3))
                    in
                    let (ca,mm) = v in
                    let (cacheSl,cacheH) = Evict ((ca li).hist,li,t,ca) in
                    let s0 = (li =+ ca li with sl := cacheSl) ca
                    in
                      ((li =+ s0 li with hist := cacheH) s0,mm))
                 else (FST s,FST (SND s))))

   [Evict_def]  Definition

      |- ∀h li t dc.
           Evict (h,li,t,dc) =
           ((t =+ NONE) (dc li).sl,(a_evict,w2n t,li)::h)

   [Fill_def]  Definition

      |- ∀va pa pm dc.
           Fill (va,pa,pm,dc) =
           (λstate.
              (let v = 2 ** w2n state.DC.ctr.DminLine − 1 in
               let (li,t,_) = lineSpec (va,pa) state in
               let s =
                     case EP ((dc li).hist,t,dc) of
                       NONE =>
                         (let (sl,h) =
                                LineFill ((dc li).hist,li,t,pm,dc,v) state
                          in
                          let s0 = (li =+ dc li with sl := sl) dc
                          in
                            ((li =+ s0 li with hist := h) s0,pm,state))
                     | SOME et =>
                         (let (ca,mm) = WriteBackLine (li,et,pm,dc,v) state
                          in
                          let (sl,h) = Evict ((ca li).hist,li,et,ca) in
                          let s3 = (li =+ ca li with sl := sl) ca in
                          let s0 = (li =+ s3 li with hist := h) s3 in
                          let (sl,h) =
                                LineFill ((s0 li).hist,li,t,mm,s0,v) state
                          in
                          let s0 = (li =+ s0 li with sl := sl) s0
                          in
                            ((li =+ s0 li with hist := h) s0,mm,state))
               in
                 (FST s,FST (SND s))))

   [Hit_def]  Definition

      |- ∀va pa dc.
           Hit (va,pa,dc) =
           (λstate.
              (let (li,t,_) = lineSpec (va,pa) state
               in
                 IS_SOME ((dc li).sl t)))

   [LineDirty_def]  Definition

      |- ∀li t dc. LineDirty (li,t,dc) ⇔ (THE ((dc li).sl t)).dirty

   [LineFill_def]  Definition

      |- ∀h li t pm dc n.
           LineFill (h,li,t,pm,dc,n) =
           (λstate.
              (let v = w2n state.DC.ctr.DminLine in
               let s =
                     SND
                       (FOR
                          (0,n,
                           (λi state0.
                              ((),
                               (n2w i =+
                                CellFill
                                  (i,
                                   t ≪
                                   (w2n
                                      (word_log2
                                         (state.DC.ccsidr.NumSets + 1w)) +
                                    v + 2) ‖ li ≪ (v + 2),
                                   FST (SND (SND (SND (SND state0)))))
                                  (n2w i)) (FST state0),SND state0)))
                          (ARB,ARB,(dc li).sl,dc,pm,state))
               in
               let s = (FST s,FST (SND s) with dirty := F,SND (SND s)) in
               let s = (FST s,FST (SND s) with value := FST s,SND (SND s))
               in
                 ((t =+ SOME (FST (SND s))) (FST (SND (SND s))),
                  (a_lfill,w2n t,li)::h)))

   [SLVAL_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'SLVAL' .
                  (∀a0'.
                     (∃a0 a1.
                        a0' =
                        (λa0 a1.
                           ind_type$CONSTR 0 (a0,a1) (λn. ind_type$BOTTOM))
                          a0 a1) ⇒
                     'SLVAL' a0') ⇒
                  'SLVAL' a0') rep

   [SLVAL_case_def]  Definition

      |- ∀a0 a1 f. SLVAL_CASE (SLVAL a0 a1) f = f a0 a1

   [SLVAL_dirty]  Definition

      |- ∀b f. (SLVAL b f).dirty ⇔ b

   [SLVAL_dirty_fupd]  Definition

      |- ∀f0 b f. SLVAL b f with dirty updated_by f0 = SLVAL (f0 b) f

   [SLVAL_size_def]  Definition

      |- ∀a0 a1. SLVAL_size (SLVAL a0 a1) = 1 + bool_size a0

   [SLVAL_value]  Definition

      |- ∀b f. (SLVAL b f).value = f

   [SLVAL_value_fupd]  Definition

      |- ∀f0 b f. SLVAL b f with value updated_by f0 = SLVAL b (f0 f)

   [Touch_def]  Definition

      |- ∀h li t wi data dc.
           Touch (h,li,t,wi,data,dc) =
           (let v = (dc li).sl in
            let v0 = THE (v t)
            in
              if IS_SOME data then
                (let data = THE data
                 in
                   ((t =+
                     SOME
                       (v0 with
                        <|value := (wi =+ data.value) v0.value;
                          dirty := data.flag|>)) v,(a_write,w2n t,li)::h))
              else ((dc li).sl,(a_read,w2n t,li)::h))

   [WriteBackLine_def]  Definition

      |- ∀li t pm dc n.
           WriteBackLine (li,t,pm,dc,n) =
           (λstate.
              (let v = (dc li).sl in
               let s5 = THE (v t) in
               let v0 = w2n state.DC.ctr.DminLine in
               let s =
                     if s5.dirty then
                       SND
                         (FOR
                            (0,n,
                             (λi state0.
                                (let v1 = (FST state0).value (n2w i) in
                                 let pa =
                                       (t ≪
                                        (w2n
                                           (word_log2
                                              (state.DC.ccsidr.NumSets +
                                               1w)) + v0 + 2) ‖
                                        li ≪ (v0 + 2)) ‖ n2w i ≪ 2
                                 in
                                 let s =
                                       (FST state0,
                                        (let s0 = SND state0
                                         in
                                           (FST s0,
                                            (let s0 = SND s0
                                             in
                                               (FST s0,
                                                (pa =+ (7 >< 0) v1)
                                                  (FST
                                                     (SND
                                                        (SND
                                                           (SND state0)))),
                                                SND (SND s0))))))
                                 in
                                 let s =
                                       (FST s,
                                        (let s0 = SND s
                                         in
                                           (FST s0,
                                            (let s0 = SND s0
                                             in
                                               (FST s0,
                                                (pa + 1w =+ (15 >< 8) v1)
                                                  (FST
                                                     (SND (SND (SND s)))),
                                                SND (SND s0))))))
                                 in
                                 let s =
                                       (FST s,
                                        (let s0 = SND s
                                         in
                                           (FST s0,
                                            (let s0 = SND s0
                                             in
                                               (FST s0,
                                                (pa + 2w =+ (23 >< 16) v1)
                                                  (FST
                                                     (SND (SND (SND s)))),
                                                SND (SND s0))))))
                                 in
                                   ((),FST s,
                                    (let s0 = SND s
                                     in
                                       (FST s0,
                                        (let s0 = SND s0
                                         in
                                           (FST s0,
                                            (pa + 3w =+ (31 >< 24) v1)
                                              (FST (SND (SND (SND s)))),
                                            SND (SND s0)))))))))
                            (s5,v,dc,pm,state))
                     else (s5,v,dc,pm,state)
               in
               let s = (FST s with dirty := F,SND s) in
               let s =
                     (FST s,(t =+ SOME (FST s)) (FST (SND s)),SND (SND s))
               in
               let s =
                     (FST s,
                      (let s0 = SND s
                       in
                         (FST s0,
                          (li =+
                           FST (SND (SND s)) li with sl := FST (SND s))
                            (FST (SND (SND s))),SND (SND s0))))
               in
                 (FST (SND (SND s)),FST (SND (SND (SND s))))))

   [WriteBack_def]  Definition

      |- ∀i t wi pm cslCnt.
           WriteBack (i,t,wi,pm,cslCnt) =
           (λstate.
              (let s0 = cslCnt.value (n2w wi) in
               let v = w2n state.DC.ctr.DminLine in
               let pa =
                     (t ≪
                      (w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) + v +
                       2) ‖ i ≪ (v + 2)) ‖ n2w wi ≪ 2
               in
                 (pa + 3w =+ (31 >< 24) s0)
                   ((pa + 2w =+ (23 >< 16) s0)
                      ((pa + 1w =+ (15 >< 8) s0)
                         ((pa =+ (7 >< 0) s0) pm)))))

   [actions_BIJ]  Definition

      |- (∀a. num2actions (actions2num a) = a) ∧
         ∀r. (λn. n < 4) r ⇔ (actions2num (num2actions r) = r)

   [actions_CASE]  Definition

      |- ∀x v0 v1 v2 v3.
           (case x of
              a_read => v0
            | a_write => v1
            | a_evict => v2
            | a_lfill => v3) =
           (λm.
              if m < 1 then v0
              else if m < 2 then v1
              else if m = 2 then v2
              else v3) (actions2num x)

   [actions_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 4) rep

   [actions_size_def]  Definition

      |- ∀x. actions_size x = 0

   [cache_state_DC]  Definition

      |- ∀C e. (cache_state C e).DC = C

   [cache_state_DC_fupd]  Definition

      |- ∀f C e. cache_state C e with DC updated_by f = cache_state (f C) e

   [cache_state_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'cache_state' .
                  (∀a0'.
                     (∃a0 a1.
                        a0' =
                        (λa0 a1.
                           ind_type$CONSTR 0 (a0,a1) (λn. ind_type$BOTTOM))
                          a0 a1) ⇒
                     'cache_state' a0') ⇒
                  'cache_state' a0') rep

   [cache_state_case_def]  Definition

      |- ∀a0 a1 f. cache_state_CASE (cache_state a0 a1) f = f a0 a1

   [cache_state_exception]  Definition

      |- ∀C e. (cache_state C e).exception = e

   [cache_state_exception_fupd]  Definition

      |- ∀f C e.
           cache_state C e with exception updated_by f =
           cache_state C (f e)

   [cache_state_size_def]  Definition

      |- ∀a0 a1.
           cache_state_size (cache_state a0 a1) =
           1 + (CACHE_CONFIG_size a0 + exception_size a1)

   [exception_BIJ]  Definition

      |- (∀a. num2exception (exception2num a) = a) ∧
         ∀r. (λn. n < 2) r ⇔ (exception2num (num2exception r) = r)

   [exception_CASE]  Definition

      |- ∀x v0 v1.
           (case x of NoException => v0 | CACHE_WRITE_FAULT => v1) =
           (λm. if m = 0 then v0 else v1) (exception2num x)

   [exception_TY_DEF]  Definition

      |- ∃rep. TYPE_DEFINITION (λn. n < 2) rep

   [exception_size_def]  Definition

      |- ∀x. exception_size x = 0

   [lDirty_def]  Definition

      |- ∀va pa dc.
           lDirty (va,pa,dc) =
           (λstate.
              case lineSpec (va,pa) state of
                (li,t,v3) => LineDirty (li,t,dc))

   [lineSpec_def]  Definition

      |- ∀va pa.
           lineSpec (va,pa) =
           (λstate.
              (si (va,pa) state,tag (va,pa) state,w2n (wIdx pa state)))

   [mv_def]  Definition

      |- ∀cbl va pa pm dc.
           mv (cbl,va,pa,pm,dc) =
           (λstate.
              if cbl then read_mem32 (pa,pm)
              else case CacheRead (va,pa,pm,dc) state of (c,m,vl) => vl)

   [raise'exception_def]  Definition

      |- ∀e.
           raise'exception e =
           (λstate.
              (ARB,
               if state.exception = NoException then
                 state with exception := e
               else state))

   [read_mem32_def]  Definition

      |- ∀ad pm.
           read_mem32 (ad,pm) =
           w2v
             (pm (ad + 3w) @@ pm (ad + 2w) @@ pm (ad + 1w) @@ pm (ad + 0w))

   [read_mem_inner_def]  Definition

      |- ∀size ad pm.
           read_mem_inner (size,ad,pm) =
           FST
             (SND
                (SND
                   (FOR
                      (0,word_len 0w DIV 8 − 1,
                       (λi state.
                          ((),FST state,
                           w2v (FST state (ad + n2w i)) ++ FST (SND state),
                           ()))) (pm,[],()))))

   [rec'CCSIDR_def]  Definition

      |- ∀x.
           rec'CCSIDR x =
           CCSIDR ((12 >< 3) x) ((2 >< 0) x) ((27 >< 13) x) (word_bit 29 x)
             (word_bit 28 x) (word_bit 30 x) (word_bit 31 x)

   [rec'CSSELR_EL1_def]  Definition

      |- ∀x.
           rec'CSSELR_EL1 x =
           CSSELR_EL1 (word_bit 0 x) ((3 >< 1) x) ((31 >< 4) x)

   [rec'CTR_def]  Definition

      |- ∀x.
           rec'CTR x =
           CTR ((27 >< 24) x) ((19 >< 16) x) ((23 >< 20) x) ((3 >< 0) x)
             ((15 >< 14) x) ((30 >< 28) x) ((13 >< 4) x) (word_bit 31 x)

   [reg'CCSIDR_def]  Definition

      |- ∀x.
           reg'CCSIDR x =
           case x of
             CCSIDR Associativity LineSize NumSets RA WA WB WT =>
               v2w [WT] @@ v2w [WB] @@ v2w [RA] @@ v2w [WA] @@ NumSets @@
               Associativity @@ LineSize

   [reg'CSSELR_EL1_def]  Definition

      |- ∀x.
           reg'CSSELR_EL1 x =
           case x of
             CSSELR_EL1 InD Level RES0 => RES0 @@ Level @@ v2w [InD]

   [reg'CTR_def]  Definition

      |- ∀x.
           reg'CTR x =
           case x of
             CTR CWG DminLine ERG IminLine L1Ip RES00 RES01 RES1 =>
               v2w [RES1] @@ RES00 @@ CWG @@ ERG @@ DminLine @@ L1Ip @@
               RES01 @@ IminLine

   [si_def]  Definition

      |- ∀va pa.
           si (va,pa) =
           (λstate.
              (let v0 = w2n state.DC.ctr.DminLine + 1
               in
                 v2w
                   (field
                      (v0 + w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)))
                      (v0 + 1) (w2v pa))))

   [tag_def]  Definition

      |- ∀va pa.
           tag (va,pa) =
           (λstate.
              v2w
                (field (LENGTH (w2v pa) − 1)
                   (w2n state.DC.ctr.DminLine + 1 +
                    w2n (word_log2 (state.DC.ccsidr.NumSets + 1w)) + 1)
                   (w2v pa)))

   [wIdx_def]  Definition

      |- ∀pa.
           wIdx pa =
           (λstate. v2w (field (w2n state.DC.ctr.DminLine + 1) 2 (w2v pa)))

   [wrTyp_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0'.
                ∀'wrTyp' .
                  (∀a0'.
                     (∃a0 a1.
                        a0' =
                        (λa0 a1.
                           ind_type$CONSTR 0 (a0,a1) (λn. ind_type$BOTTOM))
                          a0 a1) ⇒
                     'wrTyp' a0') ⇒
                  'wrTyp' a0') rep

   [wrTyp_case_def]  Definition

      |- ∀a0 a1 f. wrTyp_CASE (wrTyp a0 a1) f = f a0 a1

   [wrTyp_flag]  Definition

      |- ∀b c. (wrTyp b c).flag ⇔ b

   [wrTyp_flag_fupd]  Definition

      |- ∀f b c. wrTyp b c with flag updated_by f = wrTyp (f b) c

   [wrTyp_size_def]  Definition

      |- ∀a0 a1. wrTyp_size (wrTyp a0 a1) = 1 + bool_size a0

   [wrTyp_value]  Definition

      |- ∀b c. (wrTyp b c).value = c

   [wrTyp_value_fupd]  Definition

      |- ∀f b c. wrTyp b c with value updated_by f = wrTyp b (f c)

   [write'rec'CCSIDR_def]  Definition

      |- ∀_ x. write'rec'CCSIDR (_,x) = reg'CCSIDR x

   [write'rec'CSSELR_EL1_def]  Definition

      |- ∀_ x. write'rec'CSSELR_EL1 (_,x) = reg'CSSELR_EL1 x

   [write'rec'CTR_def]  Definition

      |- ∀_ x. write'rec'CTR (_,x) = reg'CTR x

   [write'reg'CCSIDR_def]  Definition

      |- ∀_ x. write'reg'CCSIDR (_,x) = rec'CCSIDR x

   [write'reg'CSSELR_EL1_def]  Definition

      |- ∀_ x. write'reg'CSSELR_EL1 (_,x) = rec'CSSELR_EL1 x

   [write'reg'CTR_def]  Definition

      |- ∀_ x. write'reg'CTR (_,x) = rec'CTR x

   [CACHE_CONFIG_11]  Theorem

      |- ∀a0 a1 a2 a0' a1' a2'.
           (CACHE_CONFIG a0 a1 a2 = CACHE_CONFIG a0' a1' a2') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2')

   [CACHE_CONFIG_Axiom]  Theorem

      |- ∀f. ∃fn. ∀a0 a1 a2. fn (CACHE_CONFIG a0 a1 a2) = f a0 a1 a2

   [CACHE_CONFIG_accessors]  Theorem

      |- (∀C C0 C1. (CACHE_CONFIG C C0 C1).ccsidr = C) ∧
         (∀C C0 C1. (CACHE_CONFIG C C0 C1).csselr_el1 = C0) ∧
         ∀C C0 C1. (CACHE_CONFIG C C0 C1).ctr = C1

   [CACHE_CONFIG_accfupds]  Theorem

      |- (∀f C. (C with csselr_el1 updated_by f).ccsidr = C.ccsidr) ∧
         (∀f C. (C with ctr updated_by f).ccsidr = C.ccsidr) ∧
         (∀f C. (C with ccsidr updated_by f).csselr_el1 = C.csselr_el1) ∧
         (∀f C. (C with ctr updated_by f).csselr_el1 = C.csselr_el1) ∧
         (∀f C. (C with ccsidr updated_by f).ctr = C.ctr) ∧
         (∀f C. (C with csselr_el1 updated_by f).ctr = C.ctr) ∧
         (∀f C. (C with ccsidr updated_by f).ccsidr = f C.ccsidr) ∧
         (∀f C.
            (C with csselr_el1 updated_by f).csselr_el1 = f C.csselr_el1) ∧
         ∀f C. (C with ctr updated_by f).ctr = f C.ctr

   [CACHE_CONFIG_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧
           (∀a0 a1 a2.
              (M' = CACHE_CONFIG a0 a1 a2) ⇒ (f a0 a1 a2 = f' a0 a1 a2)) ⇒
           (CACHE_CONFIG_CASE M f = CACHE_CONFIG_CASE M' f')

   [CACHE_CONFIG_component_equality]  Theorem

      |- ∀C1 C2.
           (C1 = C2) ⇔
           (C1.ccsidr = C2.ccsidr) ∧ (C1.csselr_el1 = C2.csselr_el1) ∧
           (C1.ctr = C2.ctr)

   [CACHE_CONFIG_fn_updates]  Theorem

      |- (∀f C C0 C1.
            CACHE_CONFIG C C0 C1 with ccsidr updated_by f =
            CACHE_CONFIG (f C) C0 C1) ∧
         (∀f C C0 C1.
            CACHE_CONFIG C C0 C1 with csselr_el1 updated_by f =
            CACHE_CONFIG C (f C0) C1) ∧
         ∀f C C0 C1.
           CACHE_CONFIG C C0 C1 with ctr updated_by f =
           CACHE_CONFIG C C0 (f C1)

   [CACHE_CONFIG_fupdcanon]  Theorem

      |- (∀g f C.
            C with <|csselr_el1 updated_by f; ccsidr updated_by g|> =
            C with <|ccsidr updated_by g; csselr_el1 updated_by f|>) ∧
         (∀g f C.
            C with <|ctr updated_by f; ccsidr updated_by g|> =
            C with <|ccsidr updated_by g; ctr updated_by f|>) ∧
         ∀g f C.
           C with <|ctr updated_by f; csselr_el1 updated_by g|> =
           C with <|csselr_el1 updated_by g; ctr updated_by f|>

   [CACHE_CONFIG_fupdcanon_comp]  Theorem

      |- ((∀g f.
             csselr_el1_fupd f ∘ ccsidr_fupd g =
             ccsidr_fupd g ∘ csselr_el1_fupd f) ∧
          ∀h g f.
            csselr_el1_fupd f ∘ ccsidr_fupd g ∘ h =
            ccsidr_fupd g ∘ csselr_el1_fupd f ∘ h) ∧
         ((∀g f. ctr_fupd f ∘ ccsidr_fupd g = ccsidr_fupd g ∘ ctr_fupd f) ∧
          ∀h g f.
            ctr_fupd f ∘ ccsidr_fupd g ∘ h =
            ccsidr_fupd g ∘ ctr_fupd f ∘ h) ∧
         (∀g f.
            ctr_fupd f ∘ csselr_el1_fupd g =
            csselr_el1_fupd g ∘ ctr_fupd f) ∧
         ∀h g f.
           ctr_fupd f ∘ csselr_el1_fupd g ∘ h =
           csselr_el1_fupd g ∘ ctr_fupd f ∘ h

   [CACHE_CONFIG_fupdfupds]  Theorem

      |- (∀g f C.
            C with <|ccsidr updated_by f; ccsidr updated_by g|> =
            C with ccsidr updated_by f ∘ g) ∧
         (∀g f C.
            C with <|csselr_el1 updated_by f; csselr_el1 updated_by g|> =
            C with csselr_el1 updated_by f ∘ g) ∧
         ∀g f C.
           C with <|ctr updated_by f; ctr updated_by g|> =
           C with ctr updated_by f ∘ g

   [CACHE_CONFIG_fupdfupds_comp]  Theorem

      |- ((∀g f. ccsidr_fupd f ∘ ccsidr_fupd g = ccsidr_fupd (f ∘ g)) ∧
          ∀h g f.
            ccsidr_fupd f ∘ ccsidr_fupd g ∘ h = ccsidr_fupd (f ∘ g) ∘ h) ∧
         ((∀g f.
             csselr_el1_fupd f ∘ csselr_el1_fupd g =
             csselr_el1_fupd (f ∘ g)) ∧
          ∀h g f.
            csselr_el1_fupd f ∘ csselr_el1_fupd g ∘ h =
            csselr_el1_fupd (f ∘ g) ∘ h) ∧
         (∀g f. ctr_fupd f ∘ ctr_fupd g = ctr_fupd (f ∘ g)) ∧
         ∀h g f. ctr_fupd f ∘ ctr_fupd g ∘ h = ctr_fupd (f ∘ g) ∘ h

   [CACHE_CONFIG_induction]  Theorem

      |- ∀P. (∀C C0 C1. P (CACHE_CONFIG C C0 C1)) ⇒ ∀C. P C

   [CACHE_CONFIG_literal_11]  Theorem

      |- ∀C21 C11 C01 C22 C12 C02.
           (<|ccsidr := C21; csselr_el1 := C11; ctr := C01|> =
            <|ccsidr := C22; csselr_el1 := C12; ctr := C02|>) ⇔
           (C21 = C22) ∧ (C11 = C12) ∧ (C01 = C02)

   [CACHE_CONFIG_literal_nchotomy]  Theorem

      |- ∀C. ∃C2 C1 C0. C = <|ccsidr := C2; csselr_el1 := C1; ctr := C0|>

   [CACHE_CONFIG_nchotomy]  Theorem

      |- ∀CC. ∃C C0 C1. CC = CACHE_CONFIG C C0 C1

   [CACHE_CONFIG_updates_eq_literal]  Theorem

      |- ∀C C2 C1 C0.
           C with <|ccsidr := C2; csselr_el1 := C1; ctr := C0|> =
           <|ccsidr := C2; csselr_el1 := C1; ctr := C0|>

   [CCSIDR_11]  Theorem

      |- ∀a0 a1 a2 a3 a4 a5 a6 a0' a1' a2' a3' a4' a5' a6'.
           (CCSIDR a0 a1 a2 a3 a4 a5 a6 =
            CCSIDR a0' a1' a2' a3' a4' a5' a6') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2') ∧ (a3 ⇔ a3') ∧ (a4 ⇔ a4') ∧
           (a5 ⇔ a5') ∧ (a6 ⇔ a6')

   [CCSIDR_Axiom]  Theorem

      |- ∀f.
           ∃fn.
             ∀a0 a1 a2 a3 a4 a5 a6.
               fn (CCSIDR a0 a1 a2 a3 a4 a5 a6) = f a0 a1 a2 a3 a4 a5 a6

   [CCSIDR_accessors]  Theorem

      |- (∀c c0 c1 b b0 b1 b2.
            (CCSIDR c c0 c1 b b0 b1 b2).Associativity = c) ∧
         (∀c c0 c1 b b0 b1 b2. (CCSIDR c c0 c1 b b0 b1 b2).LineSize = c0) ∧
         (∀c c0 c1 b b0 b1 b2. (CCSIDR c c0 c1 b b0 b1 b2).NumSets = c1) ∧
         (∀c c0 c1 b b0 b1 b2. (CCSIDR c c0 c1 b b0 b1 b2).RA ⇔ b) ∧
         (∀c c0 c1 b b0 b1 b2. (CCSIDR c c0 c1 b b0 b1 b2).WA ⇔ b0) ∧
         (∀c c0 c1 b b0 b1 b2. (CCSIDR c c0 c1 b b0 b1 b2).WB ⇔ b1) ∧
         ∀c c0 c1 b b0 b1 b2. (CCSIDR c c0 c1 b b0 b1 b2).WT ⇔ b2

   [CCSIDR_accfupds]  Theorem

      |- (∀f C.
            (C with LineSize updated_by f).Associativity =
            C.Associativity) ∧
         (∀f C.
            (C with NumSets updated_by f).Associativity =
            C.Associativity) ∧
         (∀f C. (C with RA updated_by f).Associativity = C.Associativity) ∧
         (∀f C. (C with WA updated_by f).Associativity = C.Associativity) ∧
         (∀f C. (C with WB updated_by f).Associativity = C.Associativity) ∧
         (∀f C. (C with WT updated_by f).Associativity = C.Associativity) ∧
         (∀f C.
            (C with Associativity updated_by f).LineSize = C.LineSize) ∧
         (∀f C. (C with NumSets updated_by f).LineSize = C.LineSize) ∧
         (∀f C. (C with RA updated_by f).LineSize = C.LineSize) ∧
         (∀f C. (C with WA updated_by f).LineSize = C.LineSize) ∧
         (∀f C. (C with WB updated_by f).LineSize = C.LineSize) ∧
         (∀f C. (C with WT updated_by f).LineSize = C.LineSize) ∧
         (∀f C. (C with Associativity updated_by f).NumSets = C.NumSets) ∧
         (∀f C. (C with LineSize updated_by f).NumSets = C.NumSets) ∧
         (∀f C. (C with RA updated_by f).NumSets = C.NumSets) ∧
         (∀f C. (C with WA updated_by f).NumSets = C.NumSets) ∧
         (∀f C. (C with WB updated_by f).NumSets = C.NumSets) ∧
         (∀f C. (C with WT updated_by f).NumSets = C.NumSets) ∧
         (∀f C. (C with Associativity updated_by f).RA ⇔ C.RA) ∧
         (∀f C. (C with LineSize updated_by f).RA ⇔ C.RA) ∧
         (∀f C. (C with NumSets updated_by f).RA ⇔ C.RA) ∧
         (∀f C. (C with WA updated_by f).RA ⇔ C.RA) ∧
         (∀f C. (C with WB updated_by f).RA ⇔ C.RA) ∧
         (∀f C. (C with WT updated_by f).RA ⇔ C.RA) ∧
         (∀f C. (C with Associativity updated_by f).WA ⇔ C.WA) ∧
         (∀f C. (C with LineSize updated_by f).WA ⇔ C.WA) ∧
         (∀f C. (C with NumSets updated_by f).WA ⇔ C.WA) ∧
         (∀f C. (C with RA updated_by f).WA ⇔ C.WA) ∧
         (∀f C. (C with WB updated_by f).WA ⇔ C.WA) ∧
         (∀f C. (C with WT updated_by f).WA ⇔ C.WA) ∧
         (∀f C. (C with Associativity updated_by f).WB ⇔ C.WB) ∧
         (∀f C. (C with LineSize updated_by f).WB ⇔ C.WB) ∧
         (∀f C. (C with NumSets updated_by f).WB ⇔ C.WB) ∧
         (∀f C. (C with RA updated_by f).WB ⇔ C.WB) ∧
         (∀f C. (C with WA updated_by f).WB ⇔ C.WB) ∧
         (∀f C. (C with WT updated_by f).WB ⇔ C.WB) ∧
         (∀f C. (C with Associativity updated_by f).WT ⇔ C.WT) ∧
         (∀f C. (C with LineSize updated_by f).WT ⇔ C.WT) ∧
         (∀f C. (C with NumSets updated_by f).WT ⇔ C.WT) ∧
         (∀f C. (C with RA updated_by f).WT ⇔ C.WT) ∧
         (∀f C. (C with WA updated_by f).WT ⇔ C.WT) ∧
         (∀f C. (C with WB updated_by f).WT ⇔ C.WT) ∧
         (∀f C.
            (C with Associativity updated_by f).Associativity =
            f C.Associativity) ∧
         (∀f C. (C with LineSize updated_by f).LineSize = f C.LineSize) ∧
         (∀f C. (C with NumSets updated_by f).NumSets = f C.NumSets) ∧
         (∀f C. (C with RA updated_by f).RA ⇔ f C.RA) ∧
         (∀f C. (C with WA updated_by f).WA ⇔ f C.WA) ∧
         (∀f C. (C with WB updated_by f).WB ⇔ f C.WB) ∧
         ∀f C. (C with WT updated_by f).WT ⇔ f C.WT

   [CCSIDR_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧
           (∀a0 a1 a2 a3 a4 a5 a6.
              (M' = CCSIDR a0 a1 a2 a3 a4 a5 a6) ⇒
              (f a0 a1 a2 a3 a4 a5 a6 = f' a0 a1 a2 a3 a4 a5 a6)) ⇒
           (CCSIDR_CASE M f = CCSIDR_CASE M' f')

   [CCSIDR_component_equality]  Theorem

      |- ∀C1 C2.
           (C1 = C2) ⇔
           (C1.Associativity = C2.Associativity) ∧
           (C1.LineSize = C2.LineSize) ∧ (C1.NumSets = C2.NumSets) ∧
           (C1.RA ⇔ C2.RA) ∧ (C1.WA ⇔ C2.WA) ∧ (C1.WB ⇔ C2.WB) ∧
           (C1.WT ⇔ C2.WT)

   [CCSIDR_fn_updates]  Theorem

      |- (∀f c c0 c1 b b0 b1 b2.
            CCSIDR c c0 c1 b b0 b1 b2 with Associativity updated_by f =
            CCSIDR (f c) c0 c1 b b0 b1 b2) ∧
         (∀f c c0 c1 b b0 b1 b2.
            CCSIDR c c0 c1 b b0 b1 b2 with LineSize updated_by f =
            CCSIDR c (f c0) c1 b b0 b1 b2) ∧
         (∀f c c0 c1 b b0 b1 b2.
            CCSIDR c c0 c1 b b0 b1 b2 with NumSets updated_by f =
            CCSIDR c c0 (f c1) b b0 b1 b2) ∧
         (∀f c c0 c1 b b0 b1 b2.
            CCSIDR c c0 c1 b b0 b1 b2 with RA updated_by f =
            CCSIDR c c0 c1 (f b) b0 b1 b2) ∧
         (∀f c c0 c1 b b0 b1 b2.
            CCSIDR c c0 c1 b b0 b1 b2 with WA updated_by f =
            CCSIDR c c0 c1 b (f b0) b1 b2) ∧
         (∀f c c0 c1 b b0 b1 b2.
            CCSIDR c c0 c1 b b0 b1 b2 with WB updated_by f =
            CCSIDR c c0 c1 b b0 (f b1) b2) ∧
         ∀f c c0 c1 b b0 b1 b2.
           CCSIDR c c0 c1 b b0 b1 b2 with WT updated_by f =
           CCSIDR c c0 c1 b b0 b1 (f b2)

   [CCSIDR_fupdcanon]  Theorem

      |- (∀g f C.
            C with <|LineSize updated_by f; Associativity updated_by g|> =
            C with <|Associativity updated_by g; LineSize updated_by f|>) ∧
         (∀g f C.
            C with <|NumSets updated_by f; Associativity updated_by g|> =
            C with <|Associativity updated_by g; NumSets updated_by f|>) ∧
         (∀g f C.
            C with <|NumSets updated_by f; LineSize updated_by g|> =
            C with <|LineSize updated_by g; NumSets updated_by f|>) ∧
         (∀g f C.
            C with <|RA updated_by f; Associativity updated_by g|> =
            C with <|Associativity updated_by g; RA updated_by f|>) ∧
         (∀g f C.
            C with <|RA updated_by f; LineSize updated_by g|> =
            C with <|LineSize updated_by g; RA updated_by f|>) ∧
         (∀g f C.
            C with <|RA updated_by f; NumSets updated_by g|> =
            C with <|NumSets updated_by g; RA updated_by f|>) ∧
         (∀g f C.
            C with <|WA updated_by f; Associativity updated_by g|> =
            C with <|Associativity updated_by g; WA updated_by f|>) ∧
         (∀g f C.
            C with <|WA updated_by f; LineSize updated_by g|> =
            C with <|LineSize updated_by g; WA updated_by f|>) ∧
         (∀g f C.
            C with <|WA updated_by f; NumSets updated_by g|> =
            C with <|NumSets updated_by g; WA updated_by f|>) ∧
         (∀g f C.
            C with <|WA updated_by f; RA updated_by g|> =
            C with <|RA updated_by g; WA updated_by f|>) ∧
         (∀g f C.
            C with <|WB updated_by f; Associativity updated_by g|> =
            C with <|Associativity updated_by g; WB updated_by f|>) ∧
         (∀g f C.
            C with <|WB updated_by f; LineSize updated_by g|> =
            C with <|LineSize updated_by g; WB updated_by f|>) ∧
         (∀g f C.
            C with <|WB updated_by f; NumSets updated_by g|> =
            C with <|NumSets updated_by g; WB updated_by f|>) ∧
         (∀g f C.
            C with <|WB updated_by f; RA updated_by g|> =
            C with <|RA updated_by g; WB updated_by f|>) ∧
         (∀g f C.
            C with <|WB updated_by f; WA updated_by g|> =
            C with <|WA updated_by g; WB updated_by f|>) ∧
         (∀g f C.
            C with <|WT updated_by f; Associativity updated_by g|> =
            C with <|Associativity updated_by g; WT updated_by f|>) ∧
         (∀g f C.
            C with <|WT updated_by f; LineSize updated_by g|> =
            C with <|LineSize updated_by g; WT updated_by f|>) ∧
         (∀g f C.
            C with <|WT updated_by f; NumSets updated_by g|> =
            C with <|NumSets updated_by g; WT updated_by f|>) ∧
         (∀g f C.
            C with <|WT updated_by f; RA updated_by g|> =
            C with <|RA updated_by g; WT updated_by f|>) ∧
         (∀g f C.
            C with <|WT updated_by f; WA updated_by g|> =
            C with <|WA updated_by g; WT updated_by f|>) ∧
         ∀g f C.
           C with <|WT updated_by f; WB updated_by g|> =
           C with <|WB updated_by g; WT updated_by f|>

   [CCSIDR_fupdcanon_comp]  Theorem

      |- ((∀g f.
             LineSize_fupd f ∘ Associativity_fupd g =
             Associativity_fupd g ∘ LineSize_fupd f) ∧
          ∀h g f.
            LineSize_fupd f ∘ Associativity_fupd g ∘ h =
            Associativity_fupd g ∘ LineSize_fupd f ∘ h) ∧
         ((∀g f.
             NumSets_fupd f ∘ Associativity_fupd g =
             Associativity_fupd g ∘ NumSets_fupd f) ∧
          ∀h g f.
            NumSets_fupd f ∘ Associativity_fupd g ∘ h =
            Associativity_fupd g ∘ NumSets_fupd f ∘ h) ∧
         ((∀g f.
             NumSets_fupd f ∘ LineSize_fupd g =
             LineSize_fupd g ∘ NumSets_fupd f) ∧
          ∀h g f.
            NumSets_fupd f ∘ LineSize_fupd g ∘ h =
            LineSize_fupd g ∘ NumSets_fupd f ∘ h) ∧
         ((∀g f.
             RA_fupd f ∘ Associativity_fupd g =
             Associativity_fupd g ∘ RA_fupd f) ∧
          ∀h g f.
            RA_fupd f ∘ Associativity_fupd g ∘ h =
            Associativity_fupd g ∘ RA_fupd f ∘ h) ∧
         ((∀g f.
             RA_fupd f ∘ LineSize_fupd g = LineSize_fupd g ∘ RA_fupd f) ∧
          ∀h g f.
            RA_fupd f ∘ LineSize_fupd g ∘ h =
            LineSize_fupd g ∘ RA_fupd f ∘ h) ∧
         ((∀g f. RA_fupd f ∘ NumSets_fupd g = NumSets_fupd g ∘ RA_fupd f) ∧
          ∀h g f.
            RA_fupd f ∘ NumSets_fupd g ∘ h =
            NumSets_fupd g ∘ RA_fupd f ∘ h) ∧
         ((∀g f.
             WA_fupd f ∘ Associativity_fupd g =
             Associativity_fupd g ∘ WA_fupd f) ∧
          ∀h g f.
            WA_fupd f ∘ Associativity_fupd g ∘ h =
            Associativity_fupd g ∘ WA_fupd f ∘ h) ∧
         ((∀g f.
             WA_fupd f ∘ LineSize_fupd g = LineSize_fupd g ∘ WA_fupd f) ∧
          ∀h g f.
            WA_fupd f ∘ LineSize_fupd g ∘ h =
            LineSize_fupd g ∘ WA_fupd f ∘ h) ∧
         ((∀g f. WA_fupd f ∘ NumSets_fupd g = NumSets_fupd g ∘ WA_fupd f) ∧
          ∀h g f.
            WA_fupd f ∘ NumSets_fupd g ∘ h =
            NumSets_fupd g ∘ WA_fupd f ∘ h) ∧
         ((∀g f. WA_fupd f ∘ RA_fupd g = RA_fupd g ∘ WA_fupd f) ∧
          ∀h g f. WA_fupd f ∘ RA_fupd g ∘ h = RA_fupd g ∘ WA_fupd f ∘ h) ∧
         ((∀g f.
             WB_fupd f ∘ Associativity_fupd g =
             Associativity_fupd g ∘ WB_fupd f) ∧
          ∀h g f.
            WB_fupd f ∘ Associativity_fupd g ∘ h =
            Associativity_fupd g ∘ WB_fupd f ∘ h) ∧
         ((∀g f.
             WB_fupd f ∘ LineSize_fupd g = LineSize_fupd g ∘ WB_fupd f) ∧
          ∀h g f.
            WB_fupd f ∘ LineSize_fupd g ∘ h =
            LineSize_fupd g ∘ WB_fupd f ∘ h) ∧
         ((∀g f. WB_fupd f ∘ NumSets_fupd g = NumSets_fupd g ∘ WB_fupd f) ∧
          ∀h g f.
            WB_fupd f ∘ NumSets_fupd g ∘ h =
            NumSets_fupd g ∘ WB_fupd f ∘ h) ∧
         ((∀g f. WB_fupd f ∘ RA_fupd g = RA_fupd g ∘ WB_fupd f) ∧
          ∀h g f. WB_fupd f ∘ RA_fupd g ∘ h = RA_fupd g ∘ WB_fupd f ∘ h) ∧
         ((∀g f. WB_fupd f ∘ WA_fupd g = WA_fupd g ∘ WB_fupd f) ∧
          ∀h g f. WB_fupd f ∘ WA_fupd g ∘ h = WA_fupd g ∘ WB_fupd f ∘ h) ∧
         ((∀g f.
             WT_fupd f ∘ Associativity_fupd g =
             Associativity_fupd g ∘ WT_fupd f) ∧
          ∀h g f.
            WT_fupd f ∘ Associativity_fupd g ∘ h =
            Associativity_fupd g ∘ WT_fupd f ∘ h) ∧
         ((∀g f.
             WT_fupd f ∘ LineSize_fupd g = LineSize_fupd g ∘ WT_fupd f) ∧
          ∀h g f.
            WT_fupd f ∘ LineSize_fupd g ∘ h =
            LineSize_fupd g ∘ WT_fupd f ∘ h) ∧
         ((∀g f. WT_fupd f ∘ NumSets_fupd g = NumSets_fupd g ∘ WT_fupd f) ∧
          ∀h g f.
            WT_fupd f ∘ NumSets_fupd g ∘ h =
            NumSets_fupd g ∘ WT_fupd f ∘ h) ∧
         ((∀g f. WT_fupd f ∘ RA_fupd g = RA_fupd g ∘ WT_fupd f) ∧
          ∀h g f. WT_fupd f ∘ RA_fupd g ∘ h = RA_fupd g ∘ WT_fupd f ∘ h) ∧
         ((∀g f. WT_fupd f ∘ WA_fupd g = WA_fupd g ∘ WT_fupd f) ∧
          ∀h g f. WT_fupd f ∘ WA_fupd g ∘ h = WA_fupd g ∘ WT_fupd f ∘ h) ∧
         (∀g f. WT_fupd f ∘ WB_fupd g = WB_fupd g ∘ WT_fupd f) ∧
         ∀h g f. WT_fupd f ∘ WB_fupd g ∘ h = WB_fupd g ∘ WT_fupd f ∘ h

   [CCSIDR_fupdfupds]  Theorem

      |- (∀g f C.
            C with
            <|Associativity updated_by f; Associativity updated_by g|> =
            C with Associativity updated_by f ∘ g) ∧
         (∀g f C.
            C with <|LineSize updated_by f; LineSize updated_by g|> =
            C with LineSize updated_by f ∘ g) ∧
         (∀g f C.
            C with <|NumSets updated_by f; NumSets updated_by g|> =
            C with NumSets updated_by f ∘ g) ∧
         (∀g f C.
            C with <|RA updated_by f; RA updated_by g|> =
            C with RA updated_by f ∘ g) ∧
         (∀g f C.
            C with <|WA updated_by f; WA updated_by g|> =
            C with WA updated_by f ∘ g) ∧
         (∀g f C.
            C with <|WB updated_by f; WB updated_by g|> =
            C with WB updated_by f ∘ g) ∧
         ∀g f C.
           C with <|WT updated_by f; WT updated_by g|> =
           C with WT updated_by f ∘ g

   [CCSIDR_fupdfupds_comp]  Theorem

      |- ((∀g f.
             Associativity_fupd f ∘ Associativity_fupd g =
             Associativity_fupd (f ∘ g)) ∧
          ∀h g f.
            Associativity_fupd f ∘ Associativity_fupd g ∘ h =
            Associativity_fupd (f ∘ g) ∘ h) ∧
         ((∀g f.
             LineSize_fupd f ∘ LineSize_fupd g = LineSize_fupd (f ∘ g)) ∧
          ∀h g f.
            LineSize_fupd f ∘ LineSize_fupd g ∘ h =
            LineSize_fupd (f ∘ g) ∘ h) ∧
         ((∀g f. NumSets_fupd f ∘ NumSets_fupd g = NumSets_fupd (f ∘ g)) ∧
          ∀h g f.
            NumSets_fupd f ∘ NumSets_fupd g ∘ h =
            NumSets_fupd (f ∘ g) ∘ h) ∧
         ((∀g f. RA_fupd f ∘ RA_fupd g = RA_fupd (f ∘ g)) ∧
          ∀h g f. RA_fupd f ∘ RA_fupd g ∘ h = RA_fupd (f ∘ g) ∘ h) ∧
         ((∀g f. WA_fupd f ∘ WA_fupd g = WA_fupd (f ∘ g)) ∧
          ∀h g f. WA_fupd f ∘ WA_fupd g ∘ h = WA_fupd (f ∘ g) ∘ h) ∧
         ((∀g f. WB_fupd f ∘ WB_fupd g = WB_fupd (f ∘ g)) ∧
          ∀h g f. WB_fupd f ∘ WB_fupd g ∘ h = WB_fupd (f ∘ g) ∘ h) ∧
         (∀g f. WT_fupd f ∘ WT_fupd g = WT_fupd (f ∘ g)) ∧
         ∀h g f. WT_fupd f ∘ WT_fupd g ∘ h = WT_fupd (f ∘ g) ∘ h

   [CCSIDR_induction]  Theorem

      |- ∀P. (∀c c0 c1 b b0 b1 b2. P (CCSIDR c c0 c1 b b0 b1 b2)) ⇒ ∀C. P C

   [CCSIDR_literal_11]  Theorem

      |- ∀c11 c01 c1 b21 b11 b01 b1 c12 c02 c2 b22 b12 b02 b2.
           (<|Associativity := c11; LineSize := c01; NumSets := c1;
              RA := b21; WA := b11; WB := b01; WT := b1|> =
            <|Associativity := c12; LineSize := c02; NumSets := c2;
              RA := b22; WA := b12; WB := b02; WT := b2|>) ⇔
           (c11 = c12) ∧ (c01 = c02) ∧ (c1 = c2) ∧ (b21 ⇔ b22) ∧
           (b11 ⇔ b12) ∧ (b01 ⇔ b02) ∧ (b1 ⇔ b2)

   [CCSIDR_literal_nchotomy]  Theorem

      |- ∀C.
           ∃c1 c0 c b2 b1 b0 b.
             C =
             <|Associativity := c1; LineSize := c0; NumSets := c; RA := b2;
               WA := b1; WB := b0; WT := b|>

   [CCSIDR_nchotomy]  Theorem

      |- ∀CC. ∃c c0 c1 b b0 b1 b2. CC = CCSIDR c c0 c1 b b0 b1 b2

   [CCSIDR_updates_eq_literal]  Theorem

      |- ∀C c1 c0 c b2 b1 b0 b.
           C with
           <|Associativity := c1; LineSize := c0; NumSets := c; RA := b2;
             WA := b1; WB := b0; WT := b|> =
           <|Associativity := c1; LineSize := c0; NumSets := c; RA := b2;
             WA := b1; WB := b0; WT := b|>

   [CSET_11]  Theorem

      |- ∀a0 a1 a0' a1'.
           (CSET a0 a1 = CSET a0' a1') ⇔ (a0 = a0') ∧ (a1 = a1')

   [CSET_Axiom]  Theorem

      |- ∀f. ∃fn. ∀a0 a1. fn (CSET a0 a1) = f a0 a1

   [CSET_accessors]  Theorem

      |- (∀l f. (CSET l f).hist = l) ∧ ∀l f. (CSET l f).sl = f

   [CSET_accfupds]  Theorem

      |- (∀f C. (C with sl updated_by f).hist = C.hist) ∧
         (∀f C. (C with hist updated_by f).sl = C.sl) ∧
         (∀f C. (C with hist updated_by f).hist = f C.hist) ∧
         ∀f C. (C with sl updated_by f).sl = f C.sl

   [CSET_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧ (∀a0 a1. (M' = CSET a0 a1) ⇒ (f a0 a1 = f' a0 a1)) ⇒
           (CSET_CASE M f = CSET_CASE M' f')

   [CSET_component_equality]  Theorem

      |- ∀C1 C2. (C1 = C2) ⇔ (C1.hist = C2.hist) ∧ (C1.sl = C2.sl)

   [CSET_fn_updates]  Theorem

      |- (∀f0 l f. CSET l f with hist updated_by f0 = CSET (f0 l) f) ∧
         ∀f0 l f. CSET l f with sl updated_by f0 = CSET l (f0 f)

   [CSET_fupdcanon]  Theorem

      |- ∀g f C.
           C with <|sl updated_by f; hist updated_by g|> =
           C with <|hist updated_by g; sl updated_by f|>

   [CSET_fupdcanon_comp]  Theorem

      |- (∀g f. sl_fupd f ∘ hist_fupd g = hist_fupd g ∘ sl_fupd f) ∧
         ∀h g f. sl_fupd f ∘ hist_fupd g ∘ h = hist_fupd g ∘ sl_fupd f ∘ h

   [CSET_fupdfupds]  Theorem

      |- (∀g f C.
            C with <|hist updated_by f; hist updated_by g|> =
            C with hist updated_by f ∘ g) ∧
         ∀g f C.
           C with <|sl updated_by f; sl updated_by g|> =
           C with sl updated_by f ∘ g

   [CSET_fupdfupds_comp]  Theorem

      |- ((∀g f. hist_fupd f ∘ hist_fupd g = hist_fupd (f ∘ g)) ∧
          ∀h g f. hist_fupd f ∘ hist_fupd g ∘ h = hist_fupd (f ∘ g) ∘ h) ∧
         (∀g f. sl_fupd f ∘ sl_fupd g = sl_fupd (f ∘ g)) ∧
         ∀h g f. sl_fupd f ∘ sl_fupd g ∘ h = sl_fupd (f ∘ g) ∘ h

   [CSET_induction]  Theorem

      |- ∀P. (∀l f. P (CSET l f)) ⇒ ∀C. P C

   [CSET_literal_11]  Theorem

      |- ∀l1 f1 l2 f2.
           (<|hist := l1; sl := f1|> = <|hist := l2; sl := f2|>) ⇔
           (l1 = l2) ∧ (f1 = f2)

   [CSET_literal_nchotomy]  Theorem

      |- ∀C. ∃l f. C = <|hist := l; sl := f|>

   [CSET_nchotomy]  Theorem

      |- ∀CC. ∃l f. CC = CSET l f

   [CSET_updates_eq_literal]  Theorem

      |- ∀C l f. C with <|hist := l; sl := f|> = <|hist := l; sl := f|>

   [CSSELR_EL1_11]  Theorem

      |- ∀a0 a1 a2 a0' a1' a2'.
           (CSSELR_EL1 a0 a1 a2 = CSSELR_EL1 a0' a1' a2') ⇔
           (a0 ⇔ a0') ∧ (a1 = a1') ∧ (a2 = a2')

   [CSSELR_EL1_Axiom]  Theorem

      |- ∀f. ∃fn. ∀a0 a1 a2. fn (CSSELR_EL1 a0 a1 a2) = f a0 a1 a2

   [CSSELR_EL1_accessors]  Theorem

      |- (∀b c c0. (CSSELR_EL1 b c c0).InD ⇔ b) ∧
         (∀b c c0. (CSSELR_EL1 b c c0).Level = c) ∧
         ∀b c c0. (CSSELR_EL1 b c c0).RES0 = c0

   [CSSELR_EL1_accfupds]  Theorem

      |- (∀f C. (C with Level updated_by f).InD ⇔ C.InD) ∧
         (∀f C. (C with RES0 updated_by f).InD ⇔ C.InD) ∧
         (∀f C. (C with InD updated_by f).Level = C.Level) ∧
         (∀f C. (C with RES0 updated_by f).Level = C.Level) ∧
         (∀f C. (C with InD updated_by f).RES0 = C.RES0) ∧
         (∀f C. (C with Level updated_by f).RES0 = C.RES0) ∧
         (∀f C. (C with InD updated_by f).InD ⇔ f C.InD) ∧
         (∀f C. (C with Level updated_by f).Level = f C.Level) ∧
         ∀f C. (C with RES0 updated_by f).RES0 = f C.RES0

   [CSSELR_EL1_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧
           (∀a0 a1 a2.
              (M' = CSSELR_EL1 a0 a1 a2) ⇒ (f a0 a1 a2 = f' a0 a1 a2)) ⇒
           (CSSELR_EL1_CASE M f = CSSELR_EL1_CASE M' f')

   [CSSELR_EL1_component_equality]  Theorem

      |- ∀C1 C2.
           (C1 = C2) ⇔
           (C1.InD ⇔ C2.InD) ∧ (C1.Level = C2.Level) ∧ (C1.RES0 = C2.RES0)

   [CSSELR_EL1_fn_updates]  Theorem

      |- (∀f b c c0.
            CSSELR_EL1 b c c0 with InD updated_by f =
            CSSELR_EL1 (f b) c c0) ∧
         (∀f b c c0.
            CSSELR_EL1 b c c0 with Level updated_by f =
            CSSELR_EL1 b (f c) c0) ∧
         ∀f b c c0.
           CSSELR_EL1 b c c0 with RES0 updated_by f = CSSELR_EL1 b c (f c0)

   [CSSELR_EL1_fupdcanon]  Theorem

      |- (∀g f C.
            C with <|Level updated_by f; InD updated_by g|> =
            C with <|InD updated_by g; Level updated_by f|>) ∧
         (∀g f C.
            C with <|RES0 updated_by f; InD updated_by g|> =
            C with <|InD updated_by g; RES0 updated_by f|>) ∧
         ∀g f C.
           C with <|RES0 updated_by f; Level updated_by g|> =
           C with <|Level updated_by g; RES0 updated_by f|>

   [CSSELR_EL1_fupdcanon_comp]  Theorem

      |- ((∀g f. Level_fupd f ∘ InD_fupd g = InD_fupd g ∘ Level_fupd f) ∧
          ∀h g f.
            Level_fupd f ∘ InD_fupd g ∘ h =
            InD_fupd g ∘ Level_fupd f ∘ h) ∧
         ((∀g f. RES0_fupd f ∘ InD_fupd g = InD_fupd g ∘ RES0_fupd f) ∧
          ∀h g f.
            RES0_fupd f ∘ InD_fupd g ∘ h = InD_fupd g ∘ RES0_fupd f ∘ h) ∧
         (∀g f. RES0_fupd f ∘ Level_fupd g = Level_fupd g ∘ RES0_fupd f) ∧
         ∀h g f.
           RES0_fupd f ∘ Level_fupd g ∘ h = Level_fupd g ∘ RES0_fupd f ∘ h

   [CSSELR_EL1_fupdfupds]  Theorem

      |- (∀g f C.
            C with <|InD updated_by f; InD updated_by g|> =
            C with InD updated_by f ∘ g) ∧
         (∀g f C.
            C with <|Level updated_by f; Level updated_by g|> =
            C with Level updated_by f ∘ g) ∧
         ∀g f C.
           C with <|RES0 updated_by f; RES0 updated_by g|> =
           C with RES0 updated_by f ∘ g

   [CSSELR_EL1_fupdfupds_comp]  Theorem

      |- ((∀g f. InD_fupd f ∘ InD_fupd g = InD_fupd (f ∘ g)) ∧
          ∀h g f. InD_fupd f ∘ InD_fupd g ∘ h = InD_fupd (f ∘ g) ∘ h) ∧
         ((∀g f. Level_fupd f ∘ Level_fupd g = Level_fupd (f ∘ g)) ∧
          ∀h g f.
            Level_fupd f ∘ Level_fupd g ∘ h = Level_fupd (f ∘ g) ∘ h) ∧
         (∀g f. RES0_fupd f ∘ RES0_fupd g = RES0_fupd (f ∘ g)) ∧
         ∀h g f. RES0_fupd f ∘ RES0_fupd g ∘ h = RES0_fupd (f ∘ g) ∘ h

   [CSSELR_EL1_induction]  Theorem

      |- ∀P. (∀b c c0. P (CSSELR_EL1 b c c0)) ⇒ ∀C. P C

   [CSSELR_EL1_literal_11]  Theorem

      |- ∀b1 c01 c1 b2 c02 c2.
           (<|InD := b1; Level := c01; RES0 := c1|> =
            <|InD := b2; Level := c02; RES0 := c2|>) ⇔
           (b1 ⇔ b2) ∧ (c01 = c02) ∧ (c1 = c2)

   [CSSELR_EL1_literal_nchotomy]  Theorem

      |- ∀C. ∃b c0 c. C = <|InD := b; Level := c0; RES0 := c|>

   [CSSELR_EL1_nchotomy]  Theorem

      |- ∀CC. ∃b c c0. CC = CSSELR_EL1 b c c0

   [CSSELR_EL1_updates_eq_literal]  Theorem

      |- ∀C b c0 c.
           C with <|InD := b; Level := c0; RES0 := c|> =
           <|InD := b; Level := c0; RES0 := c|>

   [CTR_11]  Theorem

      |- ∀a0 a1 a2 a3 a4 a5 a6 a7 a0' a1' a2' a3' a4' a5' a6' a7'.
           (CTR a0 a1 a2 a3 a4 a5 a6 a7 =
            CTR a0' a1' a2' a3' a4' a5' a6' a7') ⇔
           (a0 = a0') ∧ (a1 = a1') ∧ (a2 = a2') ∧ (a3 = a3') ∧ (a4 = a4') ∧
           (a5 = a5') ∧ (a6 = a6') ∧ (a7 ⇔ a7')

   [CTR_Axiom]  Theorem

      |- ∀f.
           ∃fn.
             ∀a0 a1 a2 a3 a4 a5 a6 a7.
               fn (CTR a0 a1 a2 a3 a4 a5 a6 a7) = f a0 a1 a2 a3 a4 a5 a6 a7

   [CTR_accessors]  Theorem

      |- (∀c c0 c1 c2 c3 c4 c5 b. (CTR c c0 c1 c2 c3 c4 c5 b).CWG = c) ∧
         (∀c c0 c1 c2 c3 c4 c5 b.
            (CTR c c0 c1 c2 c3 c4 c5 b).DminLine = c0) ∧
         (∀c c0 c1 c2 c3 c4 c5 b. (CTR c c0 c1 c2 c3 c4 c5 b).ERG = c1) ∧
         (∀c c0 c1 c2 c3 c4 c5 b.
            (CTR c c0 c1 c2 c3 c4 c5 b).IminLine = c2) ∧
         (∀c c0 c1 c2 c3 c4 c5 b. (CTR c c0 c1 c2 c3 c4 c5 b).L1Ip = c3) ∧
         (∀c c0 c1 c2 c3 c4 c5 b. (CTR c c0 c1 c2 c3 c4 c5 b).RES00 = c4) ∧
         (∀c c0 c1 c2 c3 c4 c5 b. (CTR c c0 c1 c2 c3 c4 c5 b).RES01 = c5) ∧
         ∀c c0 c1 c2 c3 c4 c5 b. (CTR c c0 c1 c2 c3 c4 c5 b).RES1 ⇔ b

   [CTR_accfupds]  Theorem

      |- (∀f C. (C with DminLine updated_by f).CWG = C.CWG) ∧
         (∀f C. (C with ERG updated_by f).CWG = C.CWG) ∧
         (∀f C. (C with IminLine updated_by f).CWG = C.CWG) ∧
         (∀f C. (C with L1Ip updated_by f).CWG = C.CWG) ∧
         (∀f C. (C with RES00 updated_by f).CWG = C.CWG) ∧
         (∀f C. (C with RES01 updated_by f).CWG = C.CWG) ∧
         (∀f C. (C with RES1 updated_by f).CWG = C.CWG) ∧
         (∀f C. (C with CWG updated_by f).DminLine = C.DminLine) ∧
         (∀f C. (C with ERG updated_by f).DminLine = C.DminLine) ∧
         (∀f C. (C with IminLine updated_by f).DminLine = C.DminLine) ∧
         (∀f C. (C with L1Ip updated_by f).DminLine = C.DminLine) ∧
         (∀f C. (C with RES00 updated_by f).DminLine = C.DminLine) ∧
         (∀f C. (C with RES01 updated_by f).DminLine = C.DminLine) ∧
         (∀f C. (C with RES1 updated_by f).DminLine = C.DminLine) ∧
         (∀f C. (C with CWG updated_by f).ERG = C.ERG) ∧
         (∀f C. (C with DminLine updated_by f).ERG = C.ERG) ∧
         (∀f C. (C with IminLine updated_by f).ERG = C.ERG) ∧
         (∀f C. (C with L1Ip updated_by f).ERG = C.ERG) ∧
         (∀f C. (C with RES00 updated_by f).ERG = C.ERG) ∧
         (∀f C. (C with RES01 updated_by f).ERG = C.ERG) ∧
         (∀f C. (C with RES1 updated_by f).ERG = C.ERG) ∧
         (∀f C. (C with CWG updated_by f).IminLine = C.IminLine) ∧
         (∀f C. (C with DminLine updated_by f).IminLine = C.IminLine) ∧
         (∀f C. (C with ERG updated_by f).IminLine = C.IminLine) ∧
         (∀f C. (C with L1Ip updated_by f).IminLine = C.IminLine) ∧
         (∀f C. (C with RES00 updated_by f).IminLine = C.IminLine) ∧
         (∀f C. (C with RES01 updated_by f).IminLine = C.IminLine) ∧
         (∀f C. (C with RES1 updated_by f).IminLine = C.IminLine) ∧
         (∀f C. (C with CWG updated_by f).L1Ip = C.L1Ip) ∧
         (∀f C. (C with DminLine updated_by f).L1Ip = C.L1Ip) ∧
         (∀f C. (C with ERG updated_by f).L1Ip = C.L1Ip) ∧
         (∀f C. (C with IminLine updated_by f).L1Ip = C.L1Ip) ∧
         (∀f C. (C with RES00 updated_by f).L1Ip = C.L1Ip) ∧
         (∀f C. (C with RES01 updated_by f).L1Ip = C.L1Ip) ∧
         (∀f C. (C with RES1 updated_by f).L1Ip = C.L1Ip) ∧
         (∀f C. (C with CWG updated_by f).RES00 = C.RES00) ∧
         (∀f C. (C with DminLine updated_by f).RES00 = C.RES00) ∧
         (∀f C. (C with ERG updated_by f).RES00 = C.RES00) ∧
         (∀f C. (C with IminLine updated_by f).RES00 = C.RES00) ∧
         (∀f C. (C with L1Ip updated_by f).RES00 = C.RES00) ∧
         (∀f C. (C with RES01 updated_by f).RES00 = C.RES00) ∧
         (∀f C. (C with RES1 updated_by f).RES00 = C.RES00) ∧
         (∀f C. (C with CWG updated_by f).RES01 = C.RES01) ∧
         (∀f C. (C with DminLine updated_by f).RES01 = C.RES01) ∧
         (∀f C. (C with ERG updated_by f).RES01 = C.RES01) ∧
         (∀f C. (C with IminLine updated_by f).RES01 = C.RES01) ∧
         (∀f C. (C with L1Ip updated_by f).RES01 = C.RES01) ∧
         (∀f C. (C with RES00 updated_by f).RES01 = C.RES01) ∧
         (∀f C. (C with RES1 updated_by f).RES01 = C.RES01) ∧
         (∀f C. (C with CWG updated_by f).RES1 ⇔ C.RES1) ∧
         (∀f C. (C with DminLine updated_by f).RES1 ⇔ C.RES1) ∧
         (∀f C. (C with ERG updated_by f).RES1 ⇔ C.RES1) ∧
         (∀f C. (C with IminLine updated_by f).RES1 ⇔ C.RES1) ∧
         (∀f C. (C with L1Ip updated_by f).RES1 ⇔ C.RES1) ∧
         (∀f C. (C with RES00 updated_by f).RES1 ⇔ C.RES1) ∧
         (∀f C. (C with RES01 updated_by f).RES1 ⇔ C.RES1) ∧
         (∀f C. (C with CWG updated_by f).CWG = f C.CWG) ∧
         (∀f C. (C with DminLine updated_by f).DminLine = f C.DminLine) ∧
         (∀f C. (C with ERG updated_by f).ERG = f C.ERG) ∧
         (∀f C. (C with IminLine updated_by f).IminLine = f C.IminLine) ∧
         (∀f C. (C with L1Ip updated_by f).L1Ip = f C.L1Ip) ∧
         (∀f C. (C with RES00 updated_by f).RES00 = f C.RES00) ∧
         (∀f C. (C with RES01 updated_by f).RES01 = f C.RES01) ∧
         ∀f C. (C with RES1 updated_by f).RES1 ⇔ f C.RES1

   [CTR_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧
           (∀a0 a1 a2 a3 a4 a5 a6 a7.
              (M' = CTR a0 a1 a2 a3 a4 a5 a6 a7) ⇒
              (f a0 a1 a2 a3 a4 a5 a6 a7 = f' a0 a1 a2 a3 a4 a5 a6 a7)) ⇒
           (CTR_CASE M f = CTR_CASE M' f')

   [CTR_component_equality]  Theorem

      |- ∀C1 C2.
           (C1 = C2) ⇔
           (C1.CWG = C2.CWG) ∧ (C1.DminLine = C2.DminLine) ∧
           (C1.ERG = C2.ERG) ∧ (C1.IminLine = C2.IminLine) ∧
           (C1.L1Ip = C2.L1Ip) ∧ (C1.RES00 = C2.RES00) ∧
           (C1.RES01 = C2.RES01) ∧ (C1.RES1 ⇔ C2.RES1)

   [CTR_fn_updates]  Theorem

      |- (∀f c c0 c1 c2 c3 c4 c5 b.
            CTR c c0 c1 c2 c3 c4 c5 b with CWG updated_by f =
            CTR (f c) c0 c1 c2 c3 c4 c5 b) ∧
         (∀f c c0 c1 c2 c3 c4 c5 b.
            CTR c c0 c1 c2 c3 c4 c5 b with DminLine updated_by f =
            CTR c (f c0) c1 c2 c3 c4 c5 b) ∧
         (∀f c c0 c1 c2 c3 c4 c5 b.
            CTR c c0 c1 c2 c3 c4 c5 b with ERG updated_by f =
            CTR c c0 (f c1) c2 c3 c4 c5 b) ∧
         (∀f c c0 c1 c2 c3 c4 c5 b.
            CTR c c0 c1 c2 c3 c4 c5 b with IminLine updated_by f =
            CTR c c0 c1 (f c2) c3 c4 c5 b) ∧
         (∀f c c0 c1 c2 c3 c4 c5 b.
            CTR c c0 c1 c2 c3 c4 c5 b with L1Ip updated_by f =
            CTR c c0 c1 c2 (f c3) c4 c5 b) ∧
         (∀f c c0 c1 c2 c3 c4 c5 b.
            CTR c c0 c1 c2 c3 c4 c5 b with RES00 updated_by f =
            CTR c c0 c1 c2 c3 (f c4) c5 b) ∧
         (∀f c c0 c1 c2 c3 c4 c5 b.
            CTR c c0 c1 c2 c3 c4 c5 b with RES01 updated_by f =
            CTR c c0 c1 c2 c3 c4 (f c5) b) ∧
         ∀f c c0 c1 c2 c3 c4 c5 b.
           CTR c c0 c1 c2 c3 c4 c5 b with RES1 updated_by f =
           CTR c c0 c1 c2 c3 c4 c5 (f b)

   [CTR_fupdcanon]  Theorem

      |- (∀g f C.
            C with <|DminLine updated_by f; CWG updated_by g|> =
            C with <|CWG updated_by g; DminLine updated_by f|>) ∧
         (∀g f C.
            C with <|ERG updated_by f; CWG updated_by g|> =
            C with <|CWG updated_by g; ERG updated_by f|>) ∧
         (∀g f C.
            C with <|ERG updated_by f; DminLine updated_by g|> =
            C with <|DminLine updated_by g; ERG updated_by f|>) ∧
         (∀g f C.
            C with <|IminLine updated_by f; CWG updated_by g|> =
            C with <|CWG updated_by g; IminLine updated_by f|>) ∧
         (∀g f C.
            C with <|IminLine updated_by f; DminLine updated_by g|> =
            C with <|DminLine updated_by g; IminLine updated_by f|>) ∧
         (∀g f C.
            C with <|IminLine updated_by f; ERG updated_by g|> =
            C with <|ERG updated_by g; IminLine updated_by f|>) ∧
         (∀g f C.
            C with <|L1Ip updated_by f; CWG updated_by g|> =
            C with <|CWG updated_by g; L1Ip updated_by f|>) ∧
         (∀g f C.
            C with <|L1Ip updated_by f; DminLine updated_by g|> =
            C with <|DminLine updated_by g; L1Ip updated_by f|>) ∧
         (∀g f C.
            C with <|L1Ip updated_by f; ERG updated_by g|> =
            C with <|ERG updated_by g; L1Ip updated_by f|>) ∧
         (∀g f C.
            C with <|L1Ip updated_by f; IminLine updated_by g|> =
            C with <|IminLine updated_by g; L1Ip updated_by f|>) ∧
         (∀g f C.
            C with <|RES00 updated_by f; CWG updated_by g|> =
            C with <|CWG updated_by g; RES00 updated_by f|>) ∧
         (∀g f C.
            C with <|RES00 updated_by f; DminLine updated_by g|> =
            C with <|DminLine updated_by g; RES00 updated_by f|>) ∧
         (∀g f C.
            C with <|RES00 updated_by f; ERG updated_by g|> =
            C with <|ERG updated_by g; RES00 updated_by f|>) ∧
         (∀g f C.
            C with <|RES00 updated_by f; IminLine updated_by g|> =
            C with <|IminLine updated_by g; RES00 updated_by f|>) ∧
         (∀g f C.
            C with <|RES00 updated_by f; L1Ip updated_by g|> =
            C with <|L1Ip updated_by g; RES00 updated_by f|>) ∧
         (∀g f C.
            C with <|RES01 updated_by f; CWG updated_by g|> =
            C with <|CWG updated_by g; RES01 updated_by f|>) ∧
         (∀g f C.
            C with <|RES01 updated_by f; DminLine updated_by g|> =
            C with <|DminLine updated_by g; RES01 updated_by f|>) ∧
         (∀g f C.
            C with <|RES01 updated_by f; ERG updated_by g|> =
            C with <|ERG updated_by g; RES01 updated_by f|>) ∧
         (∀g f C.
            C with <|RES01 updated_by f; IminLine updated_by g|> =
            C with <|IminLine updated_by g; RES01 updated_by f|>) ∧
         (∀g f C.
            C with <|RES01 updated_by f; L1Ip updated_by g|> =
            C with <|L1Ip updated_by g; RES01 updated_by f|>) ∧
         (∀g f C.
            C with <|RES01 updated_by f; RES00 updated_by g|> =
            C with <|RES00 updated_by g; RES01 updated_by f|>) ∧
         (∀g f C.
            C with <|RES1 updated_by f; CWG updated_by g|> =
            C with <|CWG updated_by g; RES1 updated_by f|>) ∧
         (∀g f C.
            C with <|RES1 updated_by f; DminLine updated_by g|> =
            C with <|DminLine updated_by g; RES1 updated_by f|>) ∧
         (∀g f C.
            C with <|RES1 updated_by f; ERG updated_by g|> =
            C with <|ERG updated_by g; RES1 updated_by f|>) ∧
         (∀g f C.
            C with <|RES1 updated_by f; IminLine updated_by g|> =
            C with <|IminLine updated_by g; RES1 updated_by f|>) ∧
         (∀g f C.
            C with <|RES1 updated_by f; L1Ip updated_by g|> =
            C with <|L1Ip updated_by g; RES1 updated_by f|>) ∧
         (∀g f C.
            C with <|RES1 updated_by f; RES00 updated_by g|> =
            C with <|RES00 updated_by g; RES1 updated_by f|>) ∧
         ∀g f C.
           C with <|RES1 updated_by f; RES01 updated_by g|> =
           C with <|RES01 updated_by g; RES1 updated_by f|>

   [CTR_fupdcanon_comp]  Theorem

      |- ((∀g f.
             DminLine_fupd f ∘ CWG_fupd g = CWG_fupd g ∘ DminLine_fupd f) ∧
          ∀h g f.
            DminLine_fupd f ∘ CWG_fupd g ∘ h =
            CWG_fupd g ∘ DminLine_fupd f ∘ h) ∧
         ((∀g f. ERG_fupd f ∘ CWG_fupd g = CWG_fupd g ∘ ERG_fupd f) ∧
          ∀h g f.
            ERG_fupd f ∘ CWG_fupd g ∘ h = CWG_fupd g ∘ ERG_fupd f ∘ h) ∧
         ((∀g f.
             ERG_fupd f ∘ DminLine_fupd g = DminLine_fupd g ∘ ERG_fupd f) ∧
          ∀h g f.
            ERG_fupd f ∘ DminLine_fupd g ∘ h =
            DminLine_fupd g ∘ ERG_fupd f ∘ h) ∧
         ((∀g f.
             IminLine_fupd f ∘ CWG_fupd g = CWG_fupd g ∘ IminLine_fupd f) ∧
          ∀h g f.
            IminLine_fupd f ∘ CWG_fupd g ∘ h =
            CWG_fupd g ∘ IminLine_fupd f ∘ h) ∧
         ((∀g f.
             IminLine_fupd f ∘ DminLine_fupd g =
             DminLine_fupd g ∘ IminLine_fupd f) ∧
          ∀h g f.
            IminLine_fupd f ∘ DminLine_fupd g ∘ h =
            DminLine_fupd g ∘ IminLine_fupd f ∘ h) ∧
         ((∀g f.
             IminLine_fupd f ∘ ERG_fupd g = ERG_fupd g ∘ IminLine_fupd f) ∧
          ∀h g f.
            IminLine_fupd f ∘ ERG_fupd g ∘ h =
            ERG_fupd g ∘ IminLine_fupd f ∘ h) ∧
         ((∀g f. L1Ip_fupd f ∘ CWG_fupd g = CWG_fupd g ∘ L1Ip_fupd f) ∧
          ∀h g f.
            L1Ip_fupd f ∘ CWG_fupd g ∘ h = CWG_fupd g ∘ L1Ip_fupd f ∘ h) ∧
         ((∀g f.
             L1Ip_fupd f ∘ DminLine_fupd g =
             DminLine_fupd g ∘ L1Ip_fupd f) ∧
          ∀h g f.
            L1Ip_fupd f ∘ DminLine_fupd g ∘ h =
            DminLine_fupd g ∘ L1Ip_fupd f ∘ h) ∧
         ((∀g f. L1Ip_fupd f ∘ ERG_fupd g = ERG_fupd g ∘ L1Ip_fupd f) ∧
          ∀h g f.
            L1Ip_fupd f ∘ ERG_fupd g ∘ h = ERG_fupd g ∘ L1Ip_fupd f ∘ h) ∧
         ((∀g f.
             L1Ip_fupd f ∘ IminLine_fupd g =
             IminLine_fupd g ∘ L1Ip_fupd f) ∧
          ∀h g f.
            L1Ip_fupd f ∘ IminLine_fupd g ∘ h =
            IminLine_fupd g ∘ L1Ip_fupd f ∘ h) ∧
         ((∀g f. RES00_fupd f ∘ CWG_fupd g = CWG_fupd g ∘ RES00_fupd f) ∧
          ∀h g f.
            RES00_fupd f ∘ CWG_fupd g ∘ h =
            CWG_fupd g ∘ RES00_fupd f ∘ h) ∧
         ((∀g f.
             RES00_fupd f ∘ DminLine_fupd g =
             DminLine_fupd g ∘ RES00_fupd f) ∧
          ∀h g f.
            RES00_fupd f ∘ DminLine_fupd g ∘ h =
            DminLine_fupd g ∘ RES00_fupd f ∘ h) ∧
         ((∀g f. RES00_fupd f ∘ ERG_fupd g = ERG_fupd g ∘ RES00_fupd f) ∧
          ∀h g f.
            RES00_fupd f ∘ ERG_fupd g ∘ h =
            ERG_fupd g ∘ RES00_fupd f ∘ h) ∧
         ((∀g f.
             RES00_fupd f ∘ IminLine_fupd g =
             IminLine_fupd g ∘ RES00_fupd f) ∧
          ∀h g f.
            RES00_fupd f ∘ IminLine_fupd g ∘ h =
            IminLine_fupd g ∘ RES00_fupd f ∘ h) ∧
         ((∀g f. RES00_fupd f ∘ L1Ip_fupd g = L1Ip_fupd g ∘ RES00_fupd f) ∧
          ∀h g f.
            RES00_fupd f ∘ L1Ip_fupd g ∘ h =
            L1Ip_fupd g ∘ RES00_fupd f ∘ h) ∧
         ((∀g f. RES01_fupd f ∘ CWG_fupd g = CWG_fupd g ∘ RES01_fupd f) ∧
          ∀h g f.
            RES01_fupd f ∘ CWG_fupd g ∘ h =
            CWG_fupd g ∘ RES01_fupd f ∘ h) ∧
         ((∀g f.
             RES01_fupd f ∘ DminLine_fupd g =
             DminLine_fupd g ∘ RES01_fupd f) ∧
          ∀h g f.
            RES01_fupd f ∘ DminLine_fupd g ∘ h =
            DminLine_fupd g ∘ RES01_fupd f ∘ h) ∧
         ((∀g f. RES01_fupd f ∘ ERG_fupd g = ERG_fupd g ∘ RES01_fupd f) ∧
          ∀h g f.
            RES01_fupd f ∘ ERG_fupd g ∘ h =
            ERG_fupd g ∘ RES01_fupd f ∘ h) ∧
         ((∀g f.
             RES01_fupd f ∘ IminLine_fupd g =
             IminLine_fupd g ∘ RES01_fupd f) ∧
          ∀h g f.
            RES01_fupd f ∘ IminLine_fupd g ∘ h =
            IminLine_fupd g ∘ RES01_fupd f ∘ h) ∧
         ((∀g f. RES01_fupd f ∘ L1Ip_fupd g = L1Ip_fupd g ∘ RES01_fupd f) ∧
          ∀h g f.
            RES01_fupd f ∘ L1Ip_fupd g ∘ h =
            L1Ip_fupd g ∘ RES01_fupd f ∘ h) ∧
         ((∀g f.
             RES01_fupd f ∘ RES00_fupd g = RES00_fupd g ∘ RES01_fupd f) ∧
          ∀h g f.
            RES01_fupd f ∘ RES00_fupd g ∘ h =
            RES00_fupd g ∘ RES01_fupd f ∘ h) ∧
         ((∀g f. RES1_fupd f ∘ CWG_fupd g = CWG_fupd g ∘ RES1_fupd f) ∧
          ∀h g f.
            RES1_fupd f ∘ CWG_fupd g ∘ h = CWG_fupd g ∘ RES1_fupd f ∘ h) ∧
         ((∀g f.
             RES1_fupd f ∘ DminLine_fupd g =
             DminLine_fupd g ∘ RES1_fupd f) ∧
          ∀h g f.
            RES1_fupd f ∘ DminLine_fupd g ∘ h =
            DminLine_fupd g ∘ RES1_fupd f ∘ h) ∧
         ((∀g f. RES1_fupd f ∘ ERG_fupd g = ERG_fupd g ∘ RES1_fupd f) ∧
          ∀h g f.
            RES1_fupd f ∘ ERG_fupd g ∘ h = ERG_fupd g ∘ RES1_fupd f ∘ h) ∧
         ((∀g f.
             RES1_fupd f ∘ IminLine_fupd g =
             IminLine_fupd g ∘ RES1_fupd f) ∧
          ∀h g f.
            RES1_fupd f ∘ IminLine_fupd g ∘ h =
            IminLine_fupd g ∘ RES1_fupd f ∘ h) ∧
         ((∀g f. RES1_fupd f ∘ L1Ip_fupd g = L1Ip_fupd g ∘ RES1_fupd f) ∧
          ∀h g f.
            RES1_fupd f ∘ L1Ip_fupd g ∘ h =
            L1Ip_fupd g ∘ RES1_fupd f ∘ h) ∧
         ((∀g f. RES1_fupd f ∘ RES00_fupd g = RES00_fupd g ∘ RES1_fupd f) ∧
          ∀h g f.
            RES1_fupd f ∘ RES00_fupd g ∘ h =
            RES00_fupd g ∘ RES1_fupd f ∘ h) ∧
         (∀g f. RES1_fupd f ∘ RES01_fupd g = RES01_fupd g ∘ RES1_fupd f) ∧
         ∀h g f.
           RES1_fupd f ∘ RES01_fupd g ∘ h = RES01_fupd g ∘ RES1_fupd f ∘ h

   [CTR_fupdfupds]  Theorem

      |- (∀g f C.
            C with <|CWG updated_by f; CWG updated_by g|> =
            C with CWG updated_by f ∘ g) ∧
         (∀g f C.
            C with <|DminLine updated_by f; DminLine updated_by g|> =
            C with DminLine updated_by f ∘ g) ∧
         (∀g f C.
            C with <|ERG updated_by f; ERG updated_by g|> =
            C with ERG updated_by f ∘ g) ∧
         (∀g f C.
            C with <|IminLine updated_by f; IminLine updated_by g|> =
            C with IminLine updated_by f ∘ g) ∧
         (∀g f C.
            C with <|L1Ip updated_by f; L1Ip updated_by g|> =
            C with L1Ip updated_by f ∘ g) ∧
         (∀g f C.
            C with <|RES00 updated_by f; RES00 updated_by g|> =
            C with RES00 updated_by f ∘ g) ∧
         (∀g f C.
            C with <|RES01 updated_by f; RES01 updated_by g|> =
            C with RES01 updated_by f ∘ g) ∧
         ∀g f C.
           C with <|RES1 updated_by f; RES1 updated_by g|> =
           C with RES1 updated_by f ∘ g

   [CTR_fupdfupds_comp]  Theorem

      |- ((∀g f. CWG_fupd f ∘ CWG_fupd g = CWG_fupd (f ∘ g)) ∧
          ∀h g f. CWG_fupd f ∘ CWG_fupd g ∘ h = CWG_fupd (f ∘ g) ∘ h) ∧
         ((∀g f.
             DminLine_fupd f ∘ DminLine_fupd g = DminLine_fupd (f ∘ g)) ∧
          ∀h g f.
            DminLine_fupd f ∘ DminLine_fupd g ∘ h =
            DminLine_fupd (f ∘ g) ∘ h) ∧
         ((∀g f. ERG_fupd f ∘ ERG_fupd g = ERG_fupd (f ∘ g)) ∧
          ∀h g f. ERG_fupd f ∘ ERG_fupd g ∘ h = ERG_fupd (f ∘ g) ∘ h) ∧
         ((∀g f.
             IminLine_fupd f ∘ IminLine_fupd g = IminLine_fupd (f ∘ g)) ∧
          ∀h g f.
            IminLine_fupd f ∘ IminLine_fupd g ∘ h =
            IminLine_fupd (f ∘ g) ∘ h) ∧
         ((∀g f. L1Ip_fupd f ∘ L1Ip_fupd g = L1Ip_fupd (f ∘ g)) ∧
          ∀h g f. L1Ip_fupd f ∘ L1Ip_fupd g ∘ h = L1Ip_fupd (f ∘ g) ∘ h) ∧
         ((∀g f. RES00_fupd f ∘ RES00_fupd g = RES00_fupd (f ∘ g)) ∧
          ∀h g f.
            RES00_fupd f ∘ RES00_fupd g ∘ h = RES00_fupd (f ∘ g) ∘ h) ∧
         ((∀g f. RES01_fupd f ∘ RES01_fupd g = RES01_fupd (f ∘ g)) ∧
          ∀h g f.
            RES01_fupd f ∘ RES01_fupd g ∘ h = RES01_fupd (f ∘ g) ∘ h) ∧
         (∀g f. RES1_fupd f ∘ RES1_fupd g = RES1_fupd (f ∘ g)) ∧
         ∀h g f. RES1_fupd f ∘ RES1_fupd g ∘ h = RES1_fupd (f ∘ g) ∘ h

   [CTR_induction]  Theorem

      |- ∀P.
           (∀c c0 c1 c2 c3 c4 c5 b. P (CTR c c0 c1 c2 c3 c4 c5 b)) ⇒
           ∀C. P C

   [CTR_literal_11]  Theorem

      |- ∀c51 c41 c31 c21 c11 c01 c1 b1 c52 c42 c32 c22 c12 c02 c2 b2.
           (<|CWG := c51; DminLine := c41; ERG := c31; IminLine := c21;
              L1Ip := c11; RES00 := c01; RES01 := c1; RES1 := b1|> =
            <|CWG := c52; DminLine := c42; ERG := c32; IminLine := c22;
              L1Ip := c12; RES00 := c02; RES01 := c2; RES1 := b2|>) ⇔
           (c51 = c52) ∧ (c41 = c42) ∧ (c31 = c32) ∧ (c21 = c22) ∧
           (c11 = c12) ∧ (c01 = c02) ∧ (c1 = c2) ∧ (b1 ⇔ b2)

   [CTR_literal_nchotomy]  Theorem

      |- ∀C.
           ∃c5 c4 c3 c2 c1 c0 c b.
             C =
             <|CWG := c5; DminLine := c4; ERG := c3; IminLine := c2;
               L1Ip := c1; RES00 := c0; RES01 := c; RES1 := b|>

   [CTR_nchotomy]  Theorem

      |- ∀CC. ∃c c0 c1 c2 c3 c4 c5 b. CC = CTR c c0 c1 c2 c3 c4 c5 b

   [CTR_updates_eq_literal]  Theorem

      |- ∀C c5 c4 c3 c2 c1 c0 c b.
           C with
           <|CWG := c5; DminLine := c4; ERG := c3; IminLine := c2;
             L1Ip := c1; RES00 := c0; RES01 := c; RES1 := b|> =
           <|CWG := c5; DminLine := c4; ERG := c3; IminLine := c2;
             L1Ip := c1; RES00 := c0; RES01 := c; RES1 := b|>

   [EXISTS_CACHE_CONFIG]  Theorem

      |- ∀P.
           (∃C. P C) ⇔
           ∃C2 C1 C0. P <|ccsidr := C2; csselr_el1 := C1; ctr := C0|>

   [EXISTS_CCSIDR]  Theorem

      |- ∀P.
           (∃C. P C) ⇔
           ∃c1 c0 c b2 b1 b0 b.
             P
               <|Associativity := c1; LineSize := c0; NumSets := c;
                 RA := b2; WA := b1; WB := b0; WT := b|>

   [EXISTS_CSET]  Theorem

      |- ∀P. (∃C. P C) ⇔ ∃l f. P <|hist := l; sl := f|>

   [EXISTS_CSSELR_EL1]  Theorem

      |- ∀P. (∃C. P C) ⇔ ∃b c0 c. P <|InD := b; Level := c0; RES0 := c|>

   [EXISTS_CTR]  Theorem

      |- ∀P.
           (∃C. P C) ⇔
           ∃c5 c4 c3 c2 c1 c0 c b.
             P
               <|CWG := c5; DminLine := c4; ERG := c3; IminLine := c2;
                 L1Ip := c1; RES00 := c0; RES01 := c; RES1 := b|>

   [EXISTS_SLVAL]  Theorem

      |- ∀P. (∃S. P S) ⇔ ∃b f. P <|dirty := b; value := f|>

   [EXISTS_cache_state]  Theorem

      |- ∀P. (∃c. P c) ⇔ ∃C e. P <|DC := C; exception := e|>

   [EXISTS_wrTyp]  Theorem

      |- ∀P. (∃w. P w) ⇔ ∃b c. P <|flag := b; value := c|>

   [FORALL_CACHE_CONFIG]  Theorem

      |- ∀P.
           (∀C. P C) ⇔
           ∀C2 C1 C0. P <|ccsidr := C2; csselr_el1 := C1; ctr := C0|>

   [FORALL_CCSIDR]  Theorem

      |- ∀P.
           (∀C. P C) ⇔
           ∀c1 c0 c b2 b1 b0 b.
             P
               <|Associativity := c1; LineSize := c0; NumSets := c;
                 RA := b2; WA := b1; WB := b0; WT := b|>

   [FORALL_CSET]  Theorem

      |- ∀P. (∀C. P C) ⇔ ∀l f. P <|hist := l; sl := f|>

   [FORALL_CSSELR_EL1]  Theorem

      |- ∀P. (∀C. P C) ⇔ ∀b c0 c. P <|InD := b; Level := c0; RES0 := c|>

   [FORALL_CTR]  Theorem

      |- ∀P.
           (∀C. P C) ⇔
           ∀c5 c4 c3 c2 c1 c0 c b.
             P
               <|CWG := c5; DminLine := c4; ERG := c3; IminLine := c2;
                 L1Ip := c1; RES00 := c0; RES01 := c; RES1 := b|>

   [FORALL_SLVAL]  Theorem

      |- ∀P. (∀S. P S) ⇔ ∀b f. P <|dirty := b; value := f|>

   [FORALL_cache_state]  Theorem

      |- ∀P. (∀c. P c) ⇔ ∀C e. P <|DC := C; exception := e|>

   [FORALL_wrTyp]  Theorem

      |- ∀P. (∀w. P w) ⇔ ∀b c. P <|flag := b; value := c|>

   [SLVAL_11]  Theorem

      |- ∀a0 a1 a0' a1'.
           (SLVAL a0 a1 = SLVAL a0' a1') ⇔ (a0 ⇔ a0') ∧ (a1 = a1')

   [SLVAL_Axiom]  Theorem

      |- ∀f. ∃fn. ∀a0 a1. fn (SLVAL a0 a1) = f a0 a1

   [SLVAL_accessors]  Theorem

      |- (∀b f. (SLVAL b f).dirty ⇔ b) ∧ ∀b f. (SLVAL b f).value = f

   [SLVAL_accfupds]  Theorem

      |- (∀f S. (S with value updated_by f).dirty ⇔ S.dirty) ∧
         (∀f S. (S with dirty updated_by f).value = S.value) ∧
         (∀f S. (S with dirty updated_by f).dirty ⇔ f S.dirty) ∧
         ∀f S. (S with value updated_by f).value = f S.value

   [SLVAL_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧ (∀a0 a1. (M' = SLVAL a0 a1) ⇒ (f a0 a1 = f' a0 a1)) ⇒
           (SLVAL_CASE M f = SLVAL_CASE M' f')

   [SLVAL_component_equality]  Theorem

      |- ∀S1 S2. (S1 = S2) ⇔ (S1.dirty ⇔ S2.dirty) ∧ (S1.value = S2.value)

   [SLVAL_fn_updates]  Theorem

      |- (∀f0 b f. SLVAL b f with dirty updated_by f0 = SLVAL (f0 b) f) ∧
         ∀f0 b f. SLVAL b f with value updated_by f0 = SLVAL b (f0 f)

   [SLVAL_fupdcanon]  Theorem

      |- ∀g f S.
           S with <|value updated_by f; dirty updated_by g|> =
           S with <|dirty updated_by g; value updated_by f|>

   [SLVAL_fupdcanon_comp]  Theorem

      |- (∀g f.
            value_fupd f ∘ dirty_fupd g = dirty_fupd g ∘ value_fupd f) ∧
         ∀h g f.
           value_fupd f ∘ dirty_fupd g ∘ h =
           dirty_fupd g ∘ value_fupd f ∘ h

   [SLVAL_fupdfupds]  Theorem

      |- (∀g f S.
            S with <|dirty updated_by f; dirty updated_by g|> =
            S with dirty updated_by f ∘ g) ∧
         ∀g f S.
           S with <|value updated_by f; value updated_by g|> =
           S with value updated_by f ∘ g

   [SLVAL_fupdfupds_comp]  Theorem

      |- ((∀g f. dirty_fupd f ∘ dirty_fupd g = dirty_fupd (f ∘ g)) ∧
          ∀h g f.
            dirty_fupd f ∘ dirty_fupd g ∘ h = dirty_fupd (f ∘ g) ∘ h) ∧
         (∀g f. value_fupd f ∘ value_fupd g = value_fupd (f ∘ g)) ∧
         ∀h g f. value_fupd f ∘ value_fupd g ∘ h = value_fupd (f ∘ g) ∘ h

   [SLVAL_induction]  Theorem

      |- ∀P. (∀b f. P (SLVAL b f)) ⇒ ∀S. P S

   [SLVAL_literal_11]  Theorem

      |- ∀b1 f1 b2 f2.
           (<|dirty := b1; value := f1|> = <|dirty := b2; value := f2|>) ⇔
           (b1 ⇔ b2) ∧ (f1 = f2)

   [SLVAL_literal_nchotomy]  Theorem

      |- ∀S. ∃b f. S = <|dirty := b; value := f|>

   [SLVAL_nchotomy]  Theorem

      |- ∀SS. ∃b f. SS = SLVAL b f

   [SLVAL_updates_eq_literal]  Theorem

      |- ∀S b f.
           S with <|dirty := b; value := f|> = <|dirty := b; value := f|>

   [actions2num_11]  Theorem

      |- ∀a a'. (actions2num a = actions2num a') ⇔ (a = a')

   [actions2num_ONTO]  Theorem

      |- ∀r. r < 4 ⇔ ∃a. r = actions2num a

   [actions2num_num2actions]  Theorem

      |- ∀r. r < 4 ⇔ (actions2num (num2actions r) = r)

   [actions2num_thm]  Theorem

      |- (actions2num a_read = 0) ∧ (actions2num a_write = 1) ∧
         (actions2num a_evict = 2) ∧ (actions2num a_lfill = 3)

   [actions_Axiom]  Theorem

      |- ∀x0 x1 x2 x3.
           ∃f.
             (f a_read = x0) ∧ (f a_write = x1) ∧ (f a_evict = x2) ∧
             (f a_lfill = x3)

   [actions_EQ_actions]  Theorem

      |- ∀a a'. (a = a') ⇔ (actions2num a = actions2num a')

   [actions_case_cong]  Theorem

      |- ∀M M' v0 v1 v2 v3.
           (M = M') ∧ ((M' = a_read) ⇒ (v0 = v0')) ∧
           ((M' = a_write) ⇒ (v1 = v1')) ∧ ((M' = a_evict) ⇒ (v2 = v2')) ∧
           ((M' = a_lfill) ⇒ (v3 = v3')) ⇒
           ((case M of
               a_read => v0
             | a_write => v1
             | a_evict => v2
             | a_lfill => v3) =
            case M' of
              a_read => v0'
            | a_write => v1'
            | a_evict => v2'
            | a_lfill => v3')

   [actions_case_def]  Theorem

      |- (∀v0 v1 v2 v3.
            (case a_read of
               a_read => v0
             | a_write => v1
             | a_evict => v2
             | a_lfill => v3) =
            v0) ∧
         (∀v0 v1 v2 v3.
            (case a_write of
               a_read => v0
             | a_write => v1
             | a_evict => v2
             | a_lfill => v3) =
            v1) ∧
         (∀v0 v1 v2 v3.
            (case a_evict of
               a_read => v0
             | a_write => v1
             | a_evict => v2
             | a_lfill => v3) =
            v2) ∧
         ∀v0 v1 v2 v3.
           (case a_lfill of
              a_read => v0
            | a_write => v1
            | a_evict => v2
            | a_lfill => v3) =
           v3

   [actions_distinct]  Theorem

      |- a_read ≠ a_write ∧ a_read ≠ a_evict ∧ a_read ≠ a_lfill ∧
         a_write ≠ a_evict ∧ a_write ≠ a_lfill ∧ a_evict ≠ a_lfill

   [actions_induction]  Theorem

      |- ∀P. P a_evict ∧ P a_lfill ∧ P a_read ∧ P a_write ⇒ ∀a. P a

   [actions_nchotomy]  Theorem

      |- ∀a. (a = a_read) ∨ (a = a_write) ∨ (a = a_evict) ∨ (a = a_lfill)

   [cache_state_11]  Theorem

      |- ∀a0 a1 a0' a1'.
           (cache_state a0 a1 = cache_state a0' a1') ⇔
           (a0 = a0') ∧ (a1 = a1')

   [cache_state_Axiom]  Theorem

      |- ∀f. ∃fn. ∀a0 a1. fn (cache_state a0 a1) = f a0 a1

   [cache_state_accessors]  Theorem

      |- (∀C e. (cache_state C e).DC = C) ∧
         ∀C e. (cache_state C e).exception = e

   [cache_state_accfupds]  Theorem

      |- (∀f c. (c with exception updated_by f).DC = c.DC) ∧
         (∀f c. (c with DC updated_by f).exception = c.exception) ∧
         (∀f c. (c with DC updated_by f).DC = f c.DC) ∧
         ∀f c. (c with exception updated_by f).exception = f c.exception

   [cache_state_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧
           (∀a0 a1. (M' = cache_state a0 a1) ⇒ (f a0 a1 = f' a0 a1)) ⇒
           (cache_state_CASE M f = cache_state_CASE M' f')

   [cache_state_component_equality]  Theorem

      |- ∀c1 c2.
           (c1 = c2) ⇔ (c1.DC = c2.DC) ∧ (c1.exception = c2.exception)

   [cache_state_fn_updates]  Theorem

      |- (∀f C e.
            cache_state C e with DC updated_by f = cache_state (f C) e) ∧
         ∀f C e.
           cache_state C e with exception updated_by f =
           cache_state C (f e)

   [cache_state_fupdcanon]  Theorem

      |- ∀g f c.
           c with <|exception updated_by f; DC updated_by g|> =
           c with <|DC updated_by g; exception updated_by f|>

   [cache_state_fupdcanon_comp]  Theorem

      |- (∀g f.
            exception_fupd f ∘ DC_fupd g = DC_fupd g ∘ exception_fupd f) ∧
         ∀h g f.
           exception_fupd f ∘ DC_fupd g ∘ h =
           DC_fupd g ∘ exception_fupd f ∘ h

   [cache_state_fupdfupds]  Theorem

      |- (∀g f c.
            c with <|DC updated_by f; DC updated_by g|> =
            c with DC updated_by f ∘ g) ∧
         ∀g f c.
           c with <|exception updated_by f; exception updated_by g|> =
           c with exception updated_by f ∘ g

   [cache_state_fupdfupds_comp]  Theorem

      |- ((∀g f. DC_fupd f ∘ DC_fupd g = DC_fupd (f ∘ g)) ∧
          ∀h g f. DC_fupd f ∘ DC_fupd g ∘ h = DC_fupd (f ∘ g) ∘ h) ∧
         (∀g f.
            exception_fupd f ∘ exception_fupd g = exception_fupd (f ∘ g)) ∧
         ∀h g f.
           exception_fupd f ∘ exception_fupd g ∘ h =
           exception_fupd (f ∘ g) ∘ h

   [cache_state_induction]  Theorem

      |- ∀P. (∀C e. P (cache_state C e)) ⇒ ∀c. P c

   [cache_state_literal_11]  Theorem

      |- ∀C1 e1 C2 e2.
           (<|DC := C1; exception := e1|> =
            <|DC := C2; exception := e2|>) ⇔ (C1 = C2) ∧ (e1 = e2)

   [cache_state_literal_nchotomy]  Theorem

      |- ∀c. ∃C e. c = <|DC := C; exception := e|>

   [cache_state_nchotomy]  Theorem

      |- ∀cc. ∃C e. cc = cache_state C e

   [cache_state_updates_eq_literal]  Theorem

      |- ∀c C e.
           c with <|DC := C; exception := e|> = <|DC := C; exception := e|>

   [datatype_CACHE_CONFIG]  Theorem

      |- DATATYPE (record CACHE_CONFIG ccsidr csselr_el1 ctr)

   [datatype_CCSIDR]  Theorem

      |- DATATYPE
           (record CCSIDR Associativity LineSize NumSets RA WA WB WT)

   [datatype_CSET]  Theorem

      |- DATATYPE (record CSET hist sl)

   [datatype_CSSELR_EL1]  Theorem

      |- DATATYPE (record CSSELR_EL1 InD Level RES0)

   [datatype_CTR]  Theorem

      |- DATATYPE
           (record CTR CWG DminLine ERG IminLine L1Ip RES00 RES01 RES1)

   [datatype_SLVAL]  Theorem

      |- DATATYPE (record SLVAL dirty value)

   [datatype_actions]  Theorem

      |- DATATYPE (actions a_read a_write a_evict a_lfill)

   [datatype_cache_state]  Theorem

      |- DATATYPE (record cache_state DC exception)

   [datatype_exception]  Theorem

      |- DATATYPE (exception NoException CACHE_WRITE_FAULT)

   [datatype_wrTyp]  Theorem

      |- DATATYPE (record wrTyp flag value)

   [exception2num_11]  Theorem

      |- ∀a a'. (exception2num a = exception2num a') ⇔ (a = a')

   [exception2num_ONTO]  Theorem

      |- ∀r. r < 2 ⇔ ∃a. r = exception2num a

   [exception2num_num2exception]  Theorem

      |- ∀r. r < 2 ⇔ (exception2num (num2exception r) = r)

   [exception2num_thm]  Theorem

      |- (exception2num NoException = 0) ∧
         (exception2num CACHE_WRITE_FAULT = 1)

   [exception_Axiom]  Theorem

      |- ∀x0 x1. ∃f. (f NoException = x0) ∧ (f CACHE_WRITE_FAULT = x1)

   [exception_EQ_exception]  Theorem

      |- ∀a a'. (a = a') ⇔ (exception2num a = exception2num a')

   [exception_case_cong]  Theorem

      |- ∀M M' v0 v1.
           (M = M') ∧ ((M' = NoException) ⇒ (v0 = v0')) ∧
           ((M' = CACHE_WRITE_FAULT) ⇒ (v1 = v1')) ⇒
           ((case M of NoException => v0 | CACHE_WRITE_FAULT => v1) =
            case M' of NoException => v0' | CACHE_WRITE_FAULT => v1')

   [exception_case_def]  Theorem

      |- (∀v0 v1.
            (case NoException of
               NoException => v0
             | CACHE_WRITE_FAULT => v1) =
            v0) ∧
         ∀v0 v1.
           (case CACHE_WRITE_FAULT of
              NoException => v0
            | CACHE_WRITE_FAULT => v1) =
           v1

   [exception_distinct]  Theorem

      |- NoException ≠ CACHE_WRITE_FAULT

   [exception_induction]  Theorem

      |- ∀P. P CACHE_WRITE_FAULT ∧ P NoException ⇒ ∀a. P a

   [exception_nchotomy]  Theorem

      |- ∀a. (a = NoException) ∨ (a = CACHE_WRITE_FAULT)

   [num2actions_11]  Theorem

      |- ∀r r'.
           r < 4 ⇒ r' < 4 ⇒ ((num2actions r = num2actions r') ⇔ (r = r'))

   [num2actions_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2actions r) ∧ r < 4

   [num2actions_actions2num]  Theorem

      |- ∀a. num2actions (actions2num a) = a

   [num2actions_thm]  Theorem

      |- (num2actions 0 = a_read) ∧ (num2actions 1 = a_write) ∧
         (num2actions 2 = a_evict) ∧ (num2actions 3 = a_lfill)

   [num2exception_11]  Theorem

      |- ∀r r'.
           r < 2 ⇒
           r' < 2 ⇒
           ((num2exception r = num2exception r') ⇔ (r = r'))

   [num2exception_ONTO]  Theorem

      |- ∀a. ∃r. (a = num2exception r) ∧ r < 2

   [num2exception_exception2num]  Theorem

      |- ∀a. num2exception (exception2num a) = a

   [num2exception_thm]  Theorem

      |- (num2exception 0 = NoException) ∧
         (num2exception 1 = CACHE_WRITE_FAULT)

   [wrTyp_11]  Theorem

      |- ∀a0 a1 a0' a1'.
           (wrTyp a0 a1 = wrTyp a0' a1') ⇔ (a0 ⇔ a0') ∧ (a1 = a1')

   [wrTyp_Axiom]  Theorem

      |- ∀f. ∃fn. ∀a0 a1. fn (wrTyp a0 a1) = f a0 a1

   [wrTyp_accessors]  Theorem

      |- (∀b c. (wrTyp b c).flag ⇔ b) ∧ ∀b c. (wrTyp b c).value = c

   [wrTyp_accfupds]  Theorem

      |- (∀w f. (w with value updated_by f).flag ⇔ w.flag) ∧
         (∀w f. (w with flag updated_by f).value = w.value) ∧
         (∀w f. (w with flag updated_by f).flag ⇔ f w.flag) ∧
         ∀w f. (w with value updated_by f).value = f w.value

   [wrTyp_case_cong]  Theorem

      |- ∀M M' f.
           (M = M') ∧ (∀a0 a1. (M' = wrTyp a0 a1) ⇒ (f a0 a1 = f' a0 a1)) ⇒
           (wrTyp_CASE M f = wrTyp_CASE M' f')

   [wrTyp_component_equality]  Theorem

      |- ∀w1 w2. (w1 = w2) ⇔ (w1.flag ⇔ w2.flag) ∧ (w1.value = w2.value)

   [wrTyp_fn_updates]  Theorem

      |- (∀f b c. wrTyp b c with flag updated_by f = wrTyp (f b) c) ∧
         ∀f b c. wrTyp b c with value updated_by f = wrTyp b (f c)

   [wrTyp_fupdcanon]  Theorem

      |- ∀w g f.
           w with <|value updated_by f; flag updated_by g|> =
           w with <|flag updated_by g; value updated_by f|>

   [wrTyp_fupdcanon_comp]  Theorem

      |- (∀g f. value_fupd f ∘ flag_fupd g = flag_fupd g ∘ value_fupd f) ∧
         ∀h g f.
           value_fupd f ∘ flag_fupd g ∘ h = flag_fupd g ∘ value_fupd f ∘ h

   [wrTyp_fupdfupds]  Theorem

      |- (∀w g f.
            w with <|flag updated_by f; flag updated_by g|> =
            w with flag updated_by f ∘ g) ∧
         ∀w g f.
           w with <|value updated_by f; value updated_by g|> =
           w with value updated_by f ∘ g

   [wrTyp_fupdfupds_comp]  Theorem

      |- ((∀g f. flag_fupd f ∘ flag_fupd g = flag_fupd (f ∘ g)) ∧
          ∀h g f. flag_fupd f ∘ flag_fupd g ∘ h = flag_fupd (f ∘ g) ∘ h) ∧
         (∀g f. value_fupd f ∘ value_fupd g = value_fupd (f ∘ g)) ∧
         ∀h g f. value_fupd f ∘ value_fupd g ∘ h = value_fupd (f ∘ g) ∘ h

   [wrTyp_induction]  Theorem

      |- ∀P. (∀b c. P (wrTyp b c)) ⇒ ∀w. P w

   [wrTyp_literal_11]  Theorem

      |- ∀b1 c1 b2 c2.
           (<|flag := b1; value := c1|> = <|flag := b2; value := c2|>) ⇔
           (b1 ⇔ b2) ∧ (c1 = c2)

   [wrTyp_literal_nchotomy]  Theorem

      |- ∀w. ∃b c. w = <|flag := b; value := c|>

   [wrTyp_nchotomy]  Theorem

      |- ∀ww. ∃b c. ww = wrTyp b c

   [wrTyp_updates_eq_literal]  Theorem

      |- ∀w b c.
           w with <|flag := b; value := c|> = <|flag := b; value := c|>


*)
end
