signature cacheIfTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val ADD_def : thm
    val VAL_primitive_def : thm
    val ca_def : thm
    val ccnt_def : thm
    val ccntw_def : thm
    val cl_primitive_def : thm
    val ctf_def : thm
    val dop_TY_DEF : thm
    val dop_case_def : thm
    val dop_size_def : thm
    val fmem_def : thm
    val lcnt_def : thm
    val lv_def : thm
    val lw_def : thm
    val mllu_def : thm
    val mlwb_def : thm
    val mv_def : thm
    val rd_primitive_def : thm
    val read32_def : thm
    val wt_primitive_def : thm

  (*  Theorems  *)
    val VAL_def : thm
    val VAL_ind : thm
    val cl_def : thm
    val cl_ind : thm
    val datatype_dop : thm
    val dop_11 : thm
    val dop_Axiom : thm
    val dop_case_cong : thm
    val dop_distinct : thm
    val dop_induction : thm
    val dop_nchotomy : thm
    val rd_def : thm
    val rd_ind : thm
    val wt_def : thm
    val wt_ind : thm

  val cacheIf_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [blast] Parent theory of "cacheIf"

   [cache] Parent theory of "cacheIf"

   [ADD_def]  Definition

      |- ∀dop.
           ADD dop =
           case dop of
             RD (va,pa,c) => (va,pa)
           | WT (va',pa',v10) => (va',pa')
           | CL (va'',pa'') => (va'',pa'')

   [VAL_primitive_def]  Definition

      |- VAL =
         WFREC (@R. WF R)
           (λVAL a.
              case a of RD v => ARB | WT (va,pa,w,c) => I w | CL v3 => ARB)

   [ca_def]  Definition

      |- ∀i t dc. ca i t dc = (dc i).sl t

   [ccnt_def]  Definition

      |- ∀va pa dc state.
           ccnt va pa dc state =
           (let (i,t,wi) = lineSpec (va,pa) state
            in
              (THE ((dc i).sl t)).value)

   [ccntw_def]  Definition

      |- ∀va pa dc state.
           ccntw va pa dc state =
           (let (i,t,wi) = lineSpec (va,pa) state in CellRead (i,t,wi,dc))

   [cl_primitive_def]  Definition

      |- cl =
         WFREC (@R. WF R)
           (λcl a. case a of RD v3 => I F | WT v4 => I F | CL v5 => I T)

   [ctf_def]  Definition

      |- ∀pm dc state dop.
           ctf pm dc state dop =
           (let f = mv T pm dc2 fmem fcm
            in
              case dop of
                RD (va'',pa'',c') =>
                  (let (i,t,_) = lineSpec (va'',pa'') state in
                   let (cache,mem,c) = CacheRead (va'',pa'',f,dc) state in
                   let (tg,il) = SND (HD (TL (TL (cache i).hist)))
                   in
                     if
                       ¬Hit (va'',pa'',dc) state ∧
                       EP ((dc i).hist,t,dc) ≠ NONE
                     then
                       if LineDirty (il,n2w tg,dc) then
                         (cache,mem,SOME c,SOME (n2w tg),ca il (n2w tg) dc)
                       else (cache,mem,SOME c,NONE,NONE)
                     else (cache,mem,SOME c,NONE,NONE))
              | WT (va',pa',data,c) =>
                  (let (i,t,_) = lineSpec (va',pa') state in
                   let (cache,mem) = CacheWrite (va',pa',data,f,dc) state
                   in
                   let (tg,il) = SND (HD (TL (TL (cache i).hist)))
                   in
                     if
                       ¬Hit (va',pa',dc) state ∧
                       EP ((dc i).hist,t,dc) ≠ NONE
                     then
                       if LineDirty (il,n2w tg,dc) then
                         (cache,mem,NONE,SOME (n2w tg),ca il (n2w tg) dc)
                       else (cache,mem,NONE,NONE,NONE)
                     else (cache,mem,NONE,NONE,NONE))
              | CL (va,pa) =>
                  (let (i,t,_) = lineSpec (va,pa) state in
                   let (cache,mem) =
                         CacheInvalidateByAdr (va,pa,f,dc) state
                   in
                   let (tg,il) = SND (HD (cache i).hist)
                   in
                     if LineDirty (il,n2w tg,dc) then
                       (cache,mem,NONE,SOME (n2w tg),ca il (n2w tg) dc)
                     else (cache,mem,NONE,NONE,NONE)))

   [dop_TY_DEF]  Definition

      |- ∃rep.
           TYPE_DEFINITION
             (λa0.
                ∀'dop' .
                  (∀a0.
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR 0 (a,ARB,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC 0) (ARB,a,ARB)
                             (λn. ind_type$BOTTOM)) a) ∨
                     (∃a.
                        a0 =
                        (λa.
                           ind_type$CONSTR (SUC (SUC 0)) (ARB,ARB,a)
                             (λn. ind_type$BOTTOM)) a) ⇒
                     'dop' a0) ⇒
                  'dop' a0) rep

   [dop_case_def]  Definition

      |- (∀a f f1 f2. dop_CASE (RD a) f f1 f2 = f a) ∧
         (∀a f f1 f2. dop_CASE (WT a) f f1 f2 = f1 a) ∧
         ∀a f f1 f2. dop_CASE (CL a) f f1 f2 = f2 a

   [dop_size_def]  Definition

      |- (∀a.
            dop_size (RD a) =
            1 + pair_size (λv. 0) (pair_size (λv. 0) bool_size) a) ∧
         (∀a.
            dop_size (WT a) =
            1 +
            pair_size (λv. 0)
              (pair_size (λv. 0) (pair_size wrTyp_size bool_size)) a) ∧
         ∀a. dop_size (CL a) = 1 + pair_size (λv. 0) (λv. 0) a

   [fmem_def]  Definition

      |- ∀pm dc. fmem (pm,dc) = pm

   [lcnt_def]  Definition

      |- ∀i t dc. lcnt i t dc = (THE ((dc i).sl t)).value

   [lv_def]  Definition

      |- ∀i t pm dc h n state.
           lv i t pm dc h n state =
           (let f = mv T pm dc2 fmem fcm in LineFill (h,i,t,f,dc,n) state)

   [lw_def]  Definition

      |- ∀va pa l state.
           lw va pa l state =
           (let (i,t,wi) = lineSpec (va,pa) state in l (n2w wi))

   [mllu_def]  Definition

      |- ∀i t pm dc h n state.
           mllu i t pm dc h n state = LineFill (h,i,t,pm,dc,n) state

   [mlwb_def]  Definition

      |- ∀va pa pm dc state.
           mlwb va pa pm dc state =
           (let (i,t,wi) = lineSpec (va,pa) state
            in
              WriteBack (i,t,wi,pm,THE ((dc i).sl t)) state)

   [mv_def]  Definition

      |- ∀cbl pm dc f g.
           mv cbl pm dc f g = if cbl then f (pm,dc) else g (pm,dc)

   [rd_primitive_def]  Definition

      |- rd =
         WFREC (@R. WF R)
           (λrd a. case a of RD v3 => I T | WT v4 => I F | CL v5 => I F)

   [read32_def]  Definition

      |- ∀pa f g. read32 (pa,f,g) = g (pa,f)

   [wt_primitive_def]  Definition

      |- wt =
         WFREC (@R. WF R)
           (λwt a. case a of RD v3 => I F | WT v4 => I T | CL v5 => I F)

   [VAL_def]  Theorem

      |- VAL (WT (va,pa,w,c)) = w

   [VAL_ind]  Theorem

      |- ∀P.
           (∀va pa w c. P (WT (va,pa,w,c))) ∧ (∀v1. P (RD v1)) ∧
           (∀v4. P (CL v4)) ⇒
           ∀v. P v

   [cl_def]  Theorem

      |- (cl (CL (va,pa)) ⇔ T) ∧ (cl (RD v) ⇔ F) ∧ (cl (WT v1) ⇔ F)

   [cl_ind]  Theorem

      |- ∀P.
           (∀va pa. P (CL (va,pa))) ∧ (∀v. P (RD v)) ∧ (∀v1. P (WT v1)) ⇒
           ∀v. P v

   [datatype_dop]  Theorem

      |- DATATYPE (dop RD WT CL)

   [dop_11]  Theorem

      |- (∀a a'. (RD a = RD a') ⇔ (a = a')) ∧
         (∀a a'. (WT a = WT a') ⇔ (a = a')) ∧
         ∀a a'. (CL a = CL a') ⇔ (a = a')

   [dop_Axiom]  Theorem

      |- ∀f0 f1 f2.
           ∃fn.
             (∀a. fn (RD a) = f0 a) ∧ (∀a. fn (WT a) = f1 a) ∧
             ∀a. fn (CL a) = f2 a

   [dop_case_cong]  Theorem

      |- ∀M M' f f1 f2.
           (M = M') ∧ (∀a. (M' = RD a) ⇒ (f a = f' a)) ∧
           (∀a. (M' = WT a) ⇒ (f1 a = f1' a)) ∧
           (∀a. (M' = CL a) ⇒ (f2 a = f2' a)) ⇒
           (dop_CASE M f f1 f2 = dop_CASE M' f' f1' f2')

   [dop_distinct]  Theorem

      |- (∀a' a. RD a ≠ WT a') ∧ (∀a' a. RD a ≠ CL a') ∧
         ∀a' a. WT a ≠ CL a'

   [dop_induction]  Theorem

      |- ∀P. (∀p. P (RD p)) ∧ (∀p. P (WT p)) ∧ (∀p. P (CL p)) ⇒ ∀d. P d

   [dop_nchotomy]  Theorem

      |- ∀dd. (∃p. dd = RD p) ∨ (∃p. dd = WT p) ∨ ∃p. dd = CL p

   [rd_def]  Theorem

      |- (rd (RD (va,pa,c)) ⇔ T) ∧ (rd (WT v1) ⇔ F) ∧ (rd (CL v2) ⇔ F)

   [rd_ind]  Theorem

      |- ∀P.
           (∀va pa c. P (RD (va,pa,c))) ∧ (∀v1. P (WT v1)) ∧
           (∀v2. P (CL v2)) ⇒
           ∀v. P v

   [wt_def]  Theorem

      |- (wt (WT (va,pa,w,c)) ⇔ T) ∧ (wt (RD v) ⇔ F) ∧ (wt (CL v2) ⇔ F)

   [wt_ind]  Theorem

      |- ∀P.
           (∀va pa w c. P (WT (va,pa,w,c))) ∧ (∀v. P (RD v)) ∧
           (∀v2. P (CL v2)) ⇒
           ∀v. P v


*)
end
