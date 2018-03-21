structure cutilsLib :> cutilsLib =
struct

open HolKernel boolLib bossLib Parse wordsLib lcsymtacs;
open wordsLib wordsTheory bitstringTheory schneiderUtils;     
open numSyntax pairLib pairTools Abbrev cacheTheory cutilsSyntax;

(* -------------------------------------------------------- *)
(* Tactics to simplify the proofs                           *)
(* -------------------------------------------------------- *) 
val is_neq = can (dest_eq o dest_neg);
val xrw = fn tac => RW_TAC(srw_ss()) tac;
val do_nothing = ALL_TAC;
val undisch_all_tac = schneiderUtils.UNDISCH_ALL_TAC;
val undisch_hd_tac  = schneiderUtils.UNDISCH_HD_TAC;

fun LET_ELIM_RULE thm = (thm |> SIMP_RULE(srw_ss()) [LET_DEF] |> PairedLambda.GEN_BETA_RULE);
fun fs_lambda_elim ls = fs ls \\ PairedLambda.GEN_BETA_TAC;
fun rfs_lambda_elim ls =  PairedLambda.GEN_BETA_TAC \\ fs ls;
fun xfs ls = FULL_SIMP_TAC(srw_ss()) ls;
fun spec_let_elim ls thm = thm |> Q.SPECL ls |> LET_ELIM_RULE ;
fun tspec_let_elim ls thm = thm |> SPECL ls |> LET_ELIM_RULE ;
fun rwsimp ls = ((rw ls) \\ (fs ls));
fun mfs ls = (rfs ls \\ fs ls);

val ifilter = (fn trm => (is_fst trm) andalso is_lineSpec ((fst o dest_comb o dest_fst) trm));
val tfilter = (fn trm => (is_snd trm) andalso is_lineSpec ((fst o dest_comb o dest_snd) trm));

val CASE_ON_LEFT_IMPL_TAC = 
   PAT_ASSUM ``A==>B`` 
    (fn thm => 
      let val c = (fst o dest_imp o concl) thm 
      in assume_tac thm >> Cases_on`^c` end
    )
;

val CASE_ON_RIGHT_IMPL_TAC = 
   PAT_ASSUM ``A==>B`` 
    (fn thm => 
      let val c = (snd o dest_imp o concl) thm 
      in assume_tac thm >> Cases_on`^c` end
    )
;

val UNDISCH_MATCH_TAC = fn MATCH => (PAT_ASSUM MATCH (fn th => (MP_TAC th)));
val UNDISCH_ALL_TAC = (REPEAT (UNDISCH_MATCH_TAC ``X``));

val SPEC_ASSUM_TAC = fn (MATCH, SLIST) => (REPEAT (PAT_ASSUM MATCH (fn th => ASSUME_TAC (SPECL SLIST th))));
val SPEC_AND_KEEP_ASSUM_TAC = fn (MATCH, SLIST) => (PAT_ASSUM MATCH (fn th => ASSUME_TAC th THEN ASSUME_TAC (SPECL SLIST th)));


val THROW_AWAY_TAC = fn MATCH => (REPEAT (PAT_ASSUM MATCH (fn th => IMP_RES_TAC th)));
val THROW_ONE_AWAY_TAC = fn MATCH => (PAT_ASSUM MATCH (fn th => IMP_RES_TAC th));
val THROW_AWAY_IMPLICATIONS_TAC = (REPEAT (WEAKEN_TAC is_imp));


val ASSERT_ASSUM_TAC = fn MATCH => (PAT_ASSUM MATCH (fn th => ASSUME_TAC th));


val PROTECTED_RW_TAC = fn MATCH => (PAT_ASSUM MATCH (fn th => (RW_TAC (srw_ss()) [] THEN ASSUME_TAC th)));

val PROTECTED_OR_RW_TAC = 
     fn RWLIST => (PAT_ASSUM ``X \/ Y`` 
        (fn th => (RW_TAC (srw_ss()) RWLIST THEN ASSUME_TAC th))) ORELSE (RW_TAC (srw_ss()) RWLIST);

val PROTECTED_OR_SIMP_TAC = 
     fn RWLIST => (PAT_ASSUM ``X \/ Y`` 
        (fn th => (FULL_SIMP_TAC (srw_ss()) RWLIST THEN ASSUME_TAC th))) ORELSE (FULL_SIMP_TAC (srw_ss()) RWLIST);

val CONJ_ASSUM_TAC = (REPEAT (PAT_ASSUM ``A /\ B`` (fn th => ASSUME_TAC (CONJUNCT1 th) THEN ASSUME_TAC (CONJUNCT2 th))));


val FORCE_REWRITE_TAC = 
    (fn thm =>
     let val (_, trm) = dest_thm (SPEC_ALL thm)
         val COMB (ab, c) = dest_term trm
         val COMB (a, b) = dest_term ab
     in SUBGOAL_THEN c (fn sgl => ASSUME_TAC thm  THEN ASSUME_TAC sgl THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [])
     end);


val FORCE_REV_REWRITE_TAC = 
    (fn thm =>
     let val (_, trm) = dest_thm (SPEC_ALL thm)
         val COMB (ab, c) = dest_term trm
         val COMB (a, b) = dest_term ab
     in SUBGOAL_THEN b (fn sgl => ASSUME_TAC thm  THEN ASSUME_TAC sgl THEN UNDISCH_ALL_TAC THEN RW_TAC (srw_ss()) [])
     end);

val ASSUME_SPECL_TAC = 
fn l => fn thm => ASSUME_TAC (SPECL l thm);

val ASSUME_SPECL_PAT_TAC = 
fn pat => fn l => PAT_ASSUM pat (fn thm => ASSUME_SPECL_TAC l thm);

val ASSUME_SIMP_TAC = 
fn l => fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) l thm);

val IMP_RES_SIMP_TAC = 
fn l => fn thm => IMP_RES_TAC (SIMP_RULE (srw_ss()) l thm);


val ASSUME_SPEC_TAC = 
fn l => fn thm => ASSUME_TAC (SPEC l thm);


val ASSUME_SPECL_SIMP_TAC = 
fn l => fn sthms => fn thm => ASSUME_TAC (SPECL l (SIMP_RULE (srw_ss()) sthms thm));

val IMP_RES_SPEC_TAC = 
fn l => fn thm => IMP_RES_TAC (SPEC l thm);

val PAT_UNABBREV_TAC  = fn pat => PAT_ASSUM  pat (fn thm => let val c = concl thm 
						 val g = (snd o dest_comb) c in
						 ASSUME_TAC thm					 
						 \\ `^g` by xfs[]
						 \\ xfs[]
					     end);
val TAKE_DOWN_TAC = fn pat => PAT_ASSUM  pat (fn thm => let val c = concl thm  in  ASSUME_TAC thm  end);


val let_ss = simpLib.mk_simpset [boolSimps.LET_ss] ;

fun THM_KEEP_TAC pattern tac = 
    PAT_ASSUM pattern (fn thm =>
       (ASSUME_TAC thm) THEN
        tac THEN
	(ASSUME_TAC thm)
    );
fun NO_THM_KEEP_TAC pattern tac = 
    PAT_ASSUM pattern (fn thm =>
        tac THEN
	(ASSUME_TAC thm)
    );
fun LET_HYP_PAT_ELIM_TAC pat thms = 
    PAT_ASSUM pat
	      (fn thm => 
		  ASSUME_TAC (
		  SIMP_RULE (srw_ss()) 
			    ([Once combinTheory.LET_FORALL_ELIM,
			     combinTheory.S_DEF,
			     markerTheory.Abbrev_def
			     ]@thms) thm))
;
fun LET_HYP_ELIM_TAC thms = 
    LET_HYP_PAT_ELIM_TAC ``let x = a in P`` thms;

fun FULL_SIMP_BY_ASSUMPTION_TAC pattern = 
    PAT_ASSUM pattern (fn thm => FULL_SIMP_TAC
    (srw_ss()) [thm]);
fun SIMP_BY_ASSUMPTION_TAC pattern = 
    PAT_ASSUM pattern (fn thm => 
    RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [thm]));

fun SIMP_AND_KEEP_BY_ASSUMPTION_TAC pattern = 
    THM_KEEP_TAC pattern (
    SIMP_BY_ASSUMPTION_TAC pattern);

fun SPEC_ASSUMPTION_TAC pattern term = 
  PAT_ASSUM pattern (fn thm => ASSUME_TAC (SPEC term thm));

fun FULL_SIMP_BY_BLAST_TAC term =
    (FULL_SIMP_TAC (srw_ss()) [
     blastLib.BBLAST_PROVE(term)]);

fun DISJX_TAC nth =
MAP_EVERY (fn x =>
	      if x = 0 then DISJ1_TAC
	      else DISJ2_TAC)
(List.tabulate (nth, fn x => nth-x-1));

fun ASSUME_ALL_TAC thms =
MAP_EVERY (fn x => ASSUME_TAC x) thms;

fun SYM_ASSUMPTION_TAC pattern = 
  PAT_ASSUM pattern (fn thm => ASSUME_TAC (GSYM thm));

fun member y []      = false
 |  member y (x::xs) = x=y orelse member y xs;


fun list_comp l1 l2 =
   let fun comp rls ls =
       case (null rls) of true => ls
	    | _ => 
	      (if (member (hd rls) l2 )
	       then (comp (tl rls) (ls@[(hd rls)]))
	       else (comp (tl rls) ls))
   in
       comp l1 []
   end;
fun remFirst _ [] rest = (false, rev rest)
  | remFirst x (y::ys) rest =
    if x = y then
        (true, rev rest @ ys)
    else
        remFirst x ys (y :: rest);

fun ADD_CANC_TAC (asl, w) =
    let val (eq_1, eq_2) = dest_eq w
	val l1 = numSyntax.strip_plus eq_1
	val l2 = numSyntax.strip_plus eq_2
	val com = hd (list_comp l1 l2)
	val eq_11 = snd (remFirst com l1 [])
	val eq_22 = snd (remFirst com l2 [])
	val eq = mk_eq((foldl mk_plus (hd eq_11) (tl eq_11)),(foldl mk_plus (hd eq_22) (tl eq_22)))
    in
    (* FULL_SIMP_TAC(arith_ss)[ *)
  (`^w = ^eq` by FULL_SIMP_TAC(arith_ss)[])
    end (asl,w);


fun Cncl_FUN_TAC (asl, w) =
    let val (eq_1, eq_2) = dest_eq w
	val l1 = numSyntax.strip_plus eq_1
	val l2 = numSyntax.strip_plus eq_2
	val com = hd (list_comp l1 l2)
	val eq_11 = snd (remFirst com l1 [])
	val eq_22 = snd (remFirst com l2 [])
	val eq = mk_eq((foldl mk_plus (hd eq_11) (tl eq_11)),(foldl mk_plus (hd eq_22) (tl eq_22)))
    in
	
	(`^w = ^eq` by FULL_SIMP_TAC(arith_ss)[]) 
        THEN FULL_SIMP_TAC(srw_ss())[]
	THEN FULL_SIMP_TAC(arith_ss)[]
    end (asl,w);




fun abr_tac f =
(FIRST_ASSUM (fn thm =>
    let
      val t = find_term f (concl thm)
    in Q.ABBREV_TAC`abr = ^t` 
    end));

fun abr_tac_goal f var s =
 case s of NONE =>
    (fn (asl ,g) => let val trm = find_term f g
    		     val vr  = mk_var (var, (type_of trm))
      in 
        (Q.ABBREV_TAC `^vr = ^trm` )(asl ,g)
      end
    )
   | SOME s =>
    (fn (asl ,g) => let val trm = find_term f g
    			val vr  = mk_var (var, (type_of (``^trm ^s``)))
      in 
        (Q.ABBREV_TAC `^vr = (^trm ^s)` )(asl ,g)
      end
    );

fun rm_dup [] = []
  | rm_dup (l as x::xs) =
      let fun remove (x,[]) = []
            | remove (x,l as y::ys) = if x = y
                                      then remove(x,ys)
                                      else y::remove(x,ys)
  in
        x::rm_dup(remove(x,xs))
  end;



fun THM_SPECL_GOAL fn_str th arg = 
  let val thy         = (fst o fst o hd)(DB.find (String.concat[fn_str, "_def"]))
      val fn_tm       = prim_mk_const {Name=fn_str,   Thy=thy}
      val dest_fn     = dest_monop fn_tm (ERR (String.concat["dest_", fn_str]) "")
      val is_fn       = can dest_fn
 in 
  (fn (asl,g) => 
   let val ls = ((fn ls => append ls arg) o strip_pair o dest_fn) (find_term is_fn g)  
   in 
     (assume_tac (th |> tspec_let_elim ls)) (asl ,g) 
   end)
 end
;

fun THM_SPECL_ASSM fn_str th arg  = 
  let val thy         = (fst o fst o hd)(DB.find (String.concat[fn_str, "_def"]))
      val fn_tm       = prim_mk_const {Name=fn_str,   Thy=thy}
      val dest_fn     = dest_monop fn_tm (ERR (String.concat["dest_", fn_str]) "")
      val is_fn       = can dest_fn
 in 
   (fn (asl,g) => 
   let val tls =
      filter (fn trm => trm <>``_``) (map (fn trm => find_term is_fn trm handle _ => ``_``) asl)  
    val ls = (map (strip_pair o dest_fn) tls)
   in 
     (map_every (fn l => assume_tac (Q.SPECL arg (th |> tspec_let_elim l ))) (ls)) (asl ,g) 
   end)
end;



fun PAIR_SPLIT_TAC (asm,gol) =
   let
      val to_split = flatten (map (fn a => find_terms (fn trm => (not (pairSyntax.is_pair trm)) andalso (fst (dest_type ( type_of trm)) = "prod") andalso ((not (is_const (strip_comb trm |> fst))) orelse ((dest_const (strip_comb trm |> fst) |> fst) <> "UNCURRY"))) a) asm)
      val thms = map (fn element => prove (``^element = (FST ^element, SND ^element)``,Cases_on `^element` THEN FULL_SIMP_TAC (srw_ss()) [])) to_split
      val lhsc = lhs o concl
      val PAIR_SPLIT_CONV = (fn trm =>
                            case  List.find (fn t => (lhsc t) = trm) thms
                              of SOME t => t
                               | NONE => raise UNCHANGED)
in
   (RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV PAIR_SPLIT_CONV)) 
    THEN CONV_TAC (DEPTH_CONV PAIR_SPLIT_CONV)) (asm,gol)
end;

fun mk_subgoal_then ant trm =
    Q.ABBREV_TAC`n = ^trm`
    \\ (fn (asl, g) => (SUBGOAL_THEN ``!n. ^ant ==> ^g`` (fn thm => assume_tac thm)) (asl ,g)) 
    >| [Q.UNABBREV_TAC`n`, all_tac];


fun my_match pat term =
  let val (l,_) = match_term pat term in
      map (fn m => (#residue m)) l
  end;

val FIX_TUPLE_EQ_TAC = PAT_ASSUM ``(a,b) = c`` (fn thm =>
  ASSUME_TAC (SYM thm)
  THEN (FULL_SIMP_TAC (srw_ss()) [])
);



val SPLIT_ABBREVS = (PAT_ASSUM ``Abbrev(a /\ b)`` (fn thm=>
      let val thm1 = (SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def] thm)
	  val thm11 = CONJUNCT1 thm1
	  val thm12 = CONJUNCT2 thm1
          val thm21 = REWRITE_RULE [Once (ISPEC (concl thm11) (GSYM markerTheory.Abbrev_def))] thm11
	  val thm22 = REWRITE_RULE [Once (ISPEC (concl thm12) (GSYM markerTheory.Abbrev_def))] thm12
      in
      (ASSUME_TAC thm21)
      THEN (ASSUME_TAC thm22)
      end
       ));

val proof_free_vars = fn tac_fv => fn (asl,w)   =>
    let val fvs = free_vars w
        val fvs1 = List.concat (List.map free_vars asl)
        val tac:tactic = tac_fv (fvs@fvs1)
    in
	 tac(asl,w)
    end
;

val LET_ASS_TAC = PAT_ASSUM ``LET a b`` (fn thm =>
  let val (body,value) = dest_let (concl thm)  in
  proof_free_vars (fn vars =>
  let val var_name = variant vars (mk_var ("v", type_of value)) in
      if (List.length(pairLib.strip_prod (type_of value)) = 1) then
         ((Q.ABBREV_TAC `^var_name = ^value`)
	 THEN (ASSUME_TAC thm))
      else if (is_pair value) then
         (ASSUME_TAC (SIMP_RULE (srw_ss()) [Once LET_DEF] thm))
      else 
	  ((ASSUME_TAC thm)
          THEN (Q.ABBREV_TAC `^var_name = ^value`)
          THEN (pairLib.PairCases_on `^var_name`))
  end
  )
  end
);


val LET_EQ_ASS_TAC = PAT_ASSUM ``LET a b = v`` (fn thm =>
  let val (a,b) = dest_eq (concl thm)
      val (body,value) = dest_let a
  in
  proof_free_vars (fn vars =>
  let val var_name = variant vars (mk_var ("v", type_of value)) in
      if (List.length(pairLib.strip_prod (type_of value)) = 1) then
         ((Q.ABBREV_TAC `^var_name = ^value`)
	 THEN (ASSUME_TAC thm))
      else if (is_pair value) then
         (ASSUME_TAC (SIMP_RULE (srw_ss()) [Once LET_DEF] thm))
      else 
	  ((ASSUME_TAC thm)
          THEN (Q.ABBREV_TAC `^var_name = ^value`)
          THEN (pairLib.PairCases_on `^var_name`))
  end
  )
  end
);

val LET_EQ2_ASS_TAC = 

PAT_ASSUM ``Abbrev(x = (LET a b))`` (fn thm =>
  let val (a,b) = dest_eq (concl 
         (SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def] thm))
      val (body,value) = dest_let b
  in
  proof_free_vars (fn vars =>
  let val var_name = variant vars (mk_var ("v", type_of value)) in
      if (List.length(pairLib.strip_prod (type_of value)) = 1) then
	  ((ASSUME_TAC (SIMP_RULE (srw_ss()) [Once LET_DEF] thm))
	  THEN (Q.ABBREV_TAC `^var_name = ^value`))
      else if (is_pair value) then
         (ASSUME_TAC (SIMP_RULE (srw_ss()) [Once LET_DEF] thm))
      else 
	  (ASSUME_TAC thm)
          THEN (Q.ABBREV_TAC `^var_name = ^value`)
          THEN (pairLib.PairCases_on `^var_name`)
  end
  )
  end
);

val FIX_ABBREV_TAC =
  (PAT_ASSUM ``Abbrev(~a)`` (fn thm=>
      ASSUME_TAC (SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def] thm)))
  ORELSE SPLIT_ABBREVS
;

val FIX_ABBREV_TAC2 =
  EVERY_ASSUM (fn thm =>
     (let val l = my_match ``Abbrev(a)`` (concl thm)
	  val thm1 = (SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def] thm)
	  val t = concl thm1 in
	  if (is_neg t) then ASSUME_TAC thm1
	  else if (is_var t) then ASSUME_TAC thm1
	  else if (is_conj t) then
	      let val thm11 = CONJUNCT1 thm1
		  val thm12 = CONJUNCT2 thm1
		  val thm21 = REWRITE_RULE [Once (ISPEC (concl thm11) (GSYM markerTheory.Abbrev_def))] thm11
		  val thm22 = REWRITE_RULE [Once (ISPEC (concl thm12) (GSYM markerTheory.Abbrev_def))] thm12
	      in
		  (ASSUME_TAC thm21)
		      THEN (ASSUME_TAC thm22)
	      end
	  else ASSUME_TAC thm
      end) THEN (WEAKEN_TAC (equal (concl thm)))
      handle _ => ASSUME_TAC thm
);

val FIX_ABBREV_TAC3 =
  EVERY_ASSUM (fn thm =>
  let val v::[] = my_match ``Abbrev(a)`` (concl thm)
  in
      if is_var v then (ASSUME_TAC (SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def] thm))
      else ALL_TAC
  end
  handle _ => ALL_TAC)
;


val DEABBREV_AND_FIX_TAC = 
    (REPEAT (PAT_ASSUM ``Abbrev(a)`` (fn thm=>
      ASSUME_TAC (SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def] thm))))
;

val DEABBREV_AND_FIX_TUPLE_TAC = 
    (PAT_ASSUM ``Abbrev((a,b)=c)`` (fn thm=>
      ASSUME_TAC (SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def] thm)))
;




val LET_X_TO_ONE_TAC = fn let_term => fn thm =>
  let val (body,value) = dest_let let_term
      val _ = print "************************"
  in
  if (not (is_abs body)) then (FAIL_TAC "is not a single term")
    else
    let val (var, f) = dest_abs body in
         if (is_pair  var) then
    	  FAIL_TAC "not a single variable"
         else
    	  proof_free_vars (fn vars =>
               let val var = variant (vars@(free_vars value)) var
                   val _ = print_term var
        in
    		ASSUME_TAC (SIMP_RULE (srw_ss()) [Once LET_DEF] thm)
    		THEN (Q.ABBREV_TAC `^var = ^value`)
    	    end)
     end
  end
;


val LET_TUPLE_TO_TUPLE_TAC = fn let_term => fn thm =>
  let val (body,value) = dest_let let_term
      val ([vars], body) = strip_pabs body;
      val var_list = strip_pair vars
      val val_list = strip_pair value
  in
      if ((List.length var_list) <> (List.length val_list)) then
	  FAIL_TAC "lists with different variables"
      else
	  ASSUME_TAC (SIMP_RULE (srw_ss()) [Once LET_DEF] thm)
  end
;

val LET_ONE_TO_TUPLE_TAC = fn let_term => fn thm =>
  let val (body,value) = dest_let let_term
      val ([vars], body) = strip_pabs body;
      val var_list = strip_pair vars
      val val_list = strip_pair value
  in
      if ((List.length val_list) <> 1) then
	  FAIL_TAC "right value is not a single value"
      else
	  proof_free_vars (fn all_vars =>
            let val var = variant all_vars (mk_var ("my_temp_var", type_of value)) 
	    in
	  ASSUME_TAC thm
          THEN (Q.ABBREV_TAC `^var=^value`)
	  THEN (pairLib.PairCases_on `^var`)
	  THEN (PAT_ASSUM ``Abbrev (a = ^var)`` (fn thm =>
             let val thm_no_abbrev = SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def] thm
	  	 val (a,b) = dest_eq (concl thm_no_abbrev)
		 val (s,_) = match_term vars a
		 val val_list = strip_pair a
	     in
               ASSUME_TAC thm_no_abbrev
	       THEN (MAP_EVERY (fn v =>
                  Q.ABBREV_TAC `^(variant all_vars (#redex v))=^(#residue v)`
	       ) s)
	       THEN (MAP_EVERY (fn v =>
                       PAT_ASSUM ``Abbrev (x=y)`` (fn thm => ALL_TAC)
	       	     ) s)
	     end
          ))
	    end)
  end
;



val SIMPLE_LET_TAC = 
  PAT_ASSUM ``LET a b`` (fn thm =>
  let val a = concl thm in
  (LET_X_TO_ONE_TAC a thm)
  ORELSE (LET_TUPLE_TO_TUPLE_TAC a thm)
  ORELSE (LET_ONE_TO_TUPLE_TAC a thm)
  end
);


val SIMPLE_LET_EQ_ASS_TAC = PAT_ASSUM ``LET a b = v`` (fn thm =>
  let val (a,b) = dest_eq (concl thm) in
  (LET_X_TO_ONE_TAC a thm)
  ORELSE (LET_TUPLE_TO_TUPLE_TAC a thm)
  ORELSE (LET_ONE_TO_TUPLE_TAC a thm)
  end
);



val PAT_UNDISCH = fn pat => 
    (PAT_ASSUM pat
      (fn thm => (ASSUME_TAC thm) THEN (UNDISCH_TAC (concl thm))));

  
val PROVE_BY_BLAST =    ((fn (asl,w) =>
     let val t = blastLib.BBLAST_PROVE w
     in
	 ASSUME_TAC t (asl,w)
     end 
	)
   THEN (FULL_SIMP_TAC (srw_ss()) []));

val ABBREV_GOAL = (fn (asl,w) => (Q.ABBREV_TAC `goal=^w`)(asl,w));


val INVERT_ABBR_LET = (PAT_ASSUM ``Abbrev(a = LET b c)`` (fn thm => 
  let val thm1 = (SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def] thm) in
    ASSUME_TAC (SYM thm1)
  end));

val INVERT_LET_EQ = (PAT_ASSUM ``a = LET b c`` (fn thm => 
    ASSUME_TAC (SYM thm)
  ));

val SIMP_BY_PAT = (fn pat => (fn thms =>
    (PAT_ASSUM pat (fn thm =>
      (ASSUME_TAC (SIMP_RULE (srw_ss()) thms thm))
    ))));

val NO_SPLIT_TAC = PAT_ASSUM ``a \/ b`` (fn thm => 
  (ASSUME_TAC thm) THEN (Q.ABBREV_TAC `no_split=^(concl thm)`));



fun TERM_PAT_ASSUM pat term_tac  =
  (PAT_ASSUM pat (fn thm =>
      (term_tac (my_match pat (concl thm)))
      THEN (ASSUME_TAC thm)));

fun TERM_PAT_ASSUM_W_THM pat term_tac  =
  (PAT_ASSUM pat (fn thm =>
      (ASSUME_TAC thm)
      THEN (term_tac (my_match pat (concl thm)))
  ));

fun SPECL_ASSUM pat lst =
  (PAT_ASSUM pat (fn thm => 
    (ASSUME_TAC (SPECL lst thm))
  ));

fun SYM_ASSUM pat = 
  (PAT_ASSUM pat (fn thm => ASSUME_TAC (SYM thm)));

val FST = (FULL_SIMP_TAC (srw_ss()) []);

val FIX_CONST_EQ = RULE_ASSUM_TAC (fn thm =>
  if not( is_eq (concl thm)) then thm
  else if not( is_const (fst (dest_eq (concl thm)))) then thm
  else (SYM thm)
);


val split_pair_tac =
LAST_ASSUM (fn thm =>
  let val t = find_term (fn t=> (is_var t) andalso
                                (((List.length o strip_prod o type_of) t) > 1))
                        (concl thm)
      val _ = print_term t
  in
    PairCases_on `^t`
  end
  );

val split_pair_tac =
proof_free_vars (fn vars =>
     let val vars = List.filter (fn t=> ((List.length o strip_prod o type_of) t) > 1) vars
     in
        if (List.length vars) > 0 then
          PairCases_on `^(List.hd vars)`
        else FAIL_TAC "no more split"
     end);


fun ABBREV_TUPLE vars value =
 proof_free_vars (fn all_vars =>
    let val var = variant all_vars (mk_var ("my_temp_var", type_of value))
    in
        (Q.ABBREV_TAC `^var=^value`)
        \\ (pairLib.PairCases_on `^var`)
        \\ (PAT_ASSUM ``Abbrev (a = ^var)`` (fn thm =>
           let val new_vars = (fst o dest_eq o snd o dest_comb o concl) thm
           		 val (s,_) = match_term vars new_vars
           in
             (ASSUME_TAC thm)
             \\ (MAP_EVERY (fn v =>
                  Q.ABBREV_TAC `^(variant all_vars (#redex v))=^(#residue v)`
                  ) s)
             \\ (MAP_EVERY (fn v =>
                       PAT_ASSUM ``Abbrev (x=y)`` (fn thm => ALL_TAC)
	       	     ) s)
           end
        ))
    end
 );

fun ABBREV_VAR trm =
    proof_free_vars (fn vars =>
    let val (var, value) = dest_eq trm
        val var = variant (vars@(free_vars value)) var
    in
      (Q.ABBREV_TAC `^var = ^value`)
    end);

(* -------------------------------------------------------- *) 
(* END: Tactics to simplify the proofs                      *)
(* -------------------------------------------------------- *) 

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

end
