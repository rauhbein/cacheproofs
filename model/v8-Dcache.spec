-----------------------------------------------------------------------
-- This an extension of:					     --	
-- 								     --
-- Formal Specification of the ARMv8-A instruction set architecture  --
-- (c) Anthony Fox, University of Cambridge                          --
-- 								     --
-- for introducing system level functionality 			     --
-- and a cache system interface				             --
-- Author: Hamed Nemati, KTH CSC Stockholm			     --
-----------------------------------------------------------------------
-- comp echo 'val () = Runtime.LoadF "v8-cache-type.spec v8-Dcache.spec"' | l3 
-- SML echo 'val () = Runtime.LoadF"v8-cache-type.spec v8-cache.spec";val () = SMLExport.export "dharma8";' | l3


---------------------------------------------
-- instantiating some of the functions
---------------------------------------------
SI si(va::VA, pa::PA) =
{   sti  = [Log2(DC.ccsidr.NumSets + 1)]::nat;
    bi   = [DC.ctr.DminLine]::nat  + 1;
    [([pa]::bool list)<(bi + sti):(bi + 1)>]
} 

TAG tag(va::VA, pa::PA) =
{   as = Length([pa]::bool list);
    bi  = [DC.ctr.DminLine]::nat  + 1;
    sti = [Log2(DC.ccsidr.NumSets + 1)]::nat;		
    [([pa]::bool list)<(as - 1):(bi + sti) + 1>]
}

WI wIdx(pa::PA) =
{   
    bi = [DC.ctr.DminLine]::nat  + 1;
    [([pa]::bool list)<bi:2>]
} 


-- We do not need to return bi as it can be computed from li by ([li] div  (DC.ccsidr.Associativity + 1))
-- I return it here to simplify implementation of other methods
SI * TAG * nat lineSpec(va::VA, pa::PA) =
{
    i    = si(va, pa);
    t     = tag(va, pa);
    wi    = [wIdx(pa)]::nat;
    return (i, t, wi)
}

-- Main point here is that this function works only when there is no allias in the 
-- cahce. I do not use such a function here just to make easier  verification. And
-- there is no need to change pen and paper cahce model.

MEM_ABS WriteBack(i::SI, t::TAG, wi::nat, pm::MEM_ABS, cslCnt::SLVAL) =
{
    var PM = pm;

    var cnt    = cslCnt.value ([wi]::WI);
    ln = [DC.ctr.DminLine]::nat;
    sn = [Log2(DC.ccsidr.NumSets + 1)]::nat; 
     
    pa = (t << (sn + ln + 2)) || (i << (ln + 2)) || ([wi]::bits(48)) << 2;

    PM(pa)       <- cnt<7:0>;     PM(pa+1)    <- cnt<15:8>;
    PM(pa+2)     <- cnt<23:16>;   PM(pa+3)    <- cnt<31:24>;
    return PM
}


CACHE_ABS * MEM_ABS WriteBackLine(li::SI, t::TAG,  pm::MEM_ABS, dc::CACHE_ABS, n::nat) =
{
    var PM = pm;
    var cache = dc;  
    var csl    = cache(li).sl ;
    var cslCnt = ValOf(csl(t));

    ln = [DC.ctr.DminLine]::nat;
    sn = [Log2(DC.ccsidr.NumSets + 1)]::nat; 

  
    when (cslCnt.dirty) do {
        for i in 0 .. n do {   
	    cnt    = cslCnt.value ([i]::WI);
	    pa = (t << (sn + ln + 2)) || (li << (ln + 2)) || ([i]::bits(48)) << 2;
	    PM(pa)       <- cnt<7:0>;     PM(pa+1)    <- cnt<15:8>;
    	    PM(pa+2)     <- cnt<23:16>;   PM(pa+3)    <- cnt<31:24>
        }
    };
    cslCnt.dirty <- false;
    csl(t)       <- Some(cslCnt);
    cache(li).sl <- csl;
   return (cache, PM)
}


SI option Alias(va::VA, pa::PA, dc::CACHE_ABS) =
{
    var cache = dc;
    (_, t, _) = lineSpec(va, pa);
    var res :: SI option;
    itr = ([DC.ccsidr.NumSets]::nat + 1) * ([DC.ccsidr.Associativity]::nat + 1);
    for i in 0 .. itr - 1  do
    {
	cacheSl = cache([i]).sl;
	when (IsSome(cacheSl(t))) do{
	     res <- Some([i]::SI)}
    };
    return res
}


