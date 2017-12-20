signature cutilsLib =
sig
val dest_Fill : term -> term
val dest_cacheRead : term -> term
val dest_cacheWrite: term -> term
val dest_evict : term -> term
val dest_lineFill : term -> term
val dest_lineSpec : term -> term
val dest_writeBackLine: term -> term
val is_Fill : term -> bool
val is_cacheRead : term -> bool
val is_cacheWrite : term -> bool
val is_evict : term -> bool
val is_lineFill : term -> bool
val is_lineSpec : term -> bool
val is_writeBackLine : term -> bool
val xrw : thm list -> tactic
val do_nothing : tactic
val undisch_hd_tac : schneiderUtils.tactic
val undisch_all_tac : schneiderUtils.tactic
val LET_ELIM_RULE : thm -> thm
val fs_lambda_elim : thm list -> goal -> goal list * (thm list -> thm)
val rwsimp : thm list -> goal -> goal list * (thm list -> thm)
val rfs_lambda_elim : thm list -> goal -> goal list * (thm list -> thm)
val xfs : thm list -> tactic
val mfs : thm list -> goal -> goal list * (thm list -> thm)
val CASE_ON_LEFT_IMPL_TAC : tactic
val CASE_ON_RIGHT_IMPL_TAC : tactic
val spec_let_elim : Q.tmquote list -> thm -> thm
val tspec_let_elim : term list -> thm -> thm
val ifilter : term -> bool
val tfilter : term -> bool
val rm_dup : ''a list -> ''a list
val abr_tac : (term -> bool) -> tactic
val abr_tac_goal : (term -> bool) -> string -> term option -> term list * term -> goal list * validation
val THM_SPECL_GOAL : string -> thm -> term list -> term list * term -> goal list * validation
val THM_SPECL_ASSM : string -> thm -> Q.tmquote list -> term list * term -> goal list * validation
val UNDISCH_MATCH_TAC : term -> tactic
val UNDISCH_ALL_TAC : tactic
val SPEC_ASSUM_TAC : term * term list -> tactic
val SPEC_AND_KEEP_ASSUM_TAC : term * term list -> tactic
val THROW_AWAY_TAC : term -> tactic
val THROW_ONE_AWAY_TAC : term -> tactic
val THROW_AWAY_IMPLICATIONS_TAC : tactic
val ASSERT_ASSUM_TAC : term -> tactic
val PROTECTED_RW_TAC : term -> tactic
val PROTECTED_OR_RW_TAC : thm list -> tactic
val PROTECTED_OR_SIMP_TAC : thm list -> tactic
val CONJ_ASSUM_TAC : tactic
val FORCE_REWRITE_TAC : thm -> tactic
val FORCE_REV_REWRITE_TAC : thm -> tactic
val ASSUME_SPECL_TAC : term list -> thm -> tactic
val ASSUME_SPECL_PAT_TAC : term -> term list -> tactic
val ASSUME_SIMP_TAC : thm list -> thm -> tactic
val IMP_RES_SIMP_TAC : thm list -> thm -> tactic
val ASSUME_SPEC_TAC : term -> thm -> tactic
val ASSUME_SPECL_SIMP_TAC : term list -> thm list -> thm -> tactic
val IMP_RES_SPEC_TAC : term -> thm -> tactic
val PAT_UNABBREV_TAC : term -> tactic
val TAKE_DOWN_TAC : term -> tactic
val THM_KEEP_TAC : term -> tactic -> tactic
val NO_THM_KEEP_TAC : term -> tactic -> tactic
val LET_HYP_PAT_ELIM_TAC : term -> thm list -> tactic
val LET_HYP_ELIM_TAC : thm list -> tactic
val FULL_SIMP_BY_ASSUMPTION_TAC : term -> tactic
val SIMP_BY_ASSUMPTION_TAC : term -> tactic
val SIMP_AND_KEEP_BY_ASSUMPTION_TAC : term -> tactic
val SPEC_ASSUMPTION_TAC : term -> term -> tactic
val FULL_SIMP_BY_BLAST_TAC : term -> tactic
val DISJX_TAC : int -> tactic
val ASSUME_ALL_TAC : thm list -> tactic
val SYM_ASSUMPTION_TAC : term -> tactic
val member : ''a -> ''a list -> bool
val list_comp : ''a list -> ''a list -> ''a list
val remFirst : ''a -> ''a list -> ''a list -> bool * ''a list
val ADD_CANC_TAC : term list * term -> goal list * validation
val Cncl_FUN_TAC : term list * term -> goal list * validation
val is_neq : term -> bool
val PAIR_SPLIT_TAC : term list * term -> goal list * validation
val mk_subgoal_then : term -> term -> goal -> goal list * (thm list -> thm)
val FIX_TUPLE_EQ_TAC : tactic
val SPLIT_ABBREVS : tactic
val proof_free_vars :
   (term list -> tactic) -> term list * term -> goal list * validation
val LET_ASS_TAC : tactic
val LET_EQ_ASS_TAC : tactic
val LET_EQ2_ASS_TAC : tactic
val FIX_ABBREV_TAC : tactic
val FIX_ABBREV_TAC2 : tactic
val FIX_ABBREV_TAC3 : tactic
val DEABBREV_AND_FIX_TAC : tactic
val DEABBREV_AND_FIX_TUPLE_TAC : tactic
val LET_X_TO_ONE_TAC : term -> thm -> tactic
val LET_TUPLE_TO_TUPLE_TAC : term -> thm -> tactic
val LET_ONE_TO_TUPLE_TAC : term -> thm -> tactic
val SIMPLE_LET_TAC : tactic
val SIMPLE_LET_EQ_ASS_TAC : tactic
val PAT_UNDISCH : term -> tactic
val PROVE_BY_BLAST : (term list * term, thm) gentactic
val ABBREV_GOAL : term list * term -> goal list * validation
val INVERT_ABBR_LET : tactic
val INVERT_LET_EQ : tactic
val SIMP_BY_PAT : term -> thm list -> tactic
val NO_SPLIT_TAC : tactic
val TERM_PAT_ASSUM : term -> (term list -> (goal, thm) gentactic) -> tactic
val TERM_PAT_ASSUM_W_THM : term -> (term list -> tactic) -> tactic
val SPECL_ASSUM : term -> term list -> tactic
val SYM_ASSUM : term -> tactic
val FST : tactic
val FIX_CONST_EQ : tactic
val split_pair_tac : term list * term -> goal list * validation
val ABBREV_TUPLE   : term -> term -> term list * term -> goal list * validation
val ABBREV_VAR     : term -> term list * term -> goal list * validation
val abr_lineSpec_tac_dubl : term list * term -> goal list * (thm list -> thm)
val abr_lineSpec_tac_sgl : term list * term -> goal list * (thm list -> thm)
end
