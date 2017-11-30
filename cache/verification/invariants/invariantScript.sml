
val _ = new_constant ("CrResource", ``:word48->bool``);
val _ = new_constant ("access_policy", ``:word48#bool->bool``);

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

val invariant_mem_def = Define `
  invariant_mem =
   (!pa:word48. CrResource(pa) ==> ~access_policy(pa, F)) /\
   (!pa pm. LENGTH (read_mem32 (pa, pm)) = 32)
`; 

