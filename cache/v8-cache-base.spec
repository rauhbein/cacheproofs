-----------------------------------------------------------------------
-- This an extension of:					     --	
-- 								     --
-- Formal Specification of the ARMv8-A instruction set architecture  --
-- (c) Anthony Fox, University of Cambridge                          --
-- 								     --
-- for introducing system level functionality 			     --
-- and a generic cache system interface				             --
-- Author: Hamed Nemati, KTH CSC Stockholm			     --
-----------------------------------------------------------------------

---------------------------------------------
-- cache uninterpreted functions 
---------------------------------------------
--declare si    	  :: VA * PA -> SI
--declare tag   	  :: VA * PA -> TAG
--declare wIdx  	  :: PA -> WI
--declare WriteBack       :: SI *  TAG * WI * PA -> unit
--declare Alias	          :: VA * PA -> SI  option -- finding any existing alias


SLICE * HIST_ABS Touch(h::HIST_ABS, li::SI, t::TAG, wi::WI, data :: wrTyp option, dc::CACHE_ABS) =
{
    var cache = dc;
    var cacheSl = cache(li).sl;     
    var slice   = ValOf(cacheSl(t));
    var sliceCnt=slice.value;

    if(IsSome(data))
    then{data = ValOf(data); vl = data.value; flg = data.flag;
         sliceCnt(wi) <- vl; 
         slice.dirty  <- flg;
	 slice.value  <- sliceCnt;         
         cacheSl(t)   <- Some(slice);
	 return  (cacheSl, (a_write, [t], li) @ h)
    }
    else{cacheSl = cache(li).sl; return (cacheSl, (a_read, [t], li) @ h)
    }
}

SLICE * HIST_ABS Evict(h::HIST_ABS, li::SI, t::TAG, dc::CACHE_ABS) =
{
    var cache    = dc; 
    var csl      = cache(li).sl;
    csl(t)       <- None;

    H = (a_evict, [t], li) @ h;
    return (csl, H)
}


(WI -> word) CellFill(wi::nat, adr::bits(48), pm::MEM_ABS) =
{ 
    var PM       = pm;
    var sliceCnt :: WI -> word;

    value     = read_mem32(adr || ([wi]::bits(48) << 2), PM);         
    sliceCnt([wi]::WI) <- [value]; 

    return sliceCnt
} 

SLICE * HIST_ABS LineFill(h::HIST_ABS, li::SI, t::TAG, pm::MEM_ABS, dc::CACHE_ABS, n::nat) =
{ 
    var PM      = pm;
    var cache   = dc;
    var cacheSl = cache(li).sl;
    var cnt      :: SLVAL;    
    var sliceCnt :: WI -> word;
    -- var cnt:: SLVAL; 
    ln = [DC.ctr.DminLine]::nat;
    sn = [Log2(DC.ccsidr.NumSets + 1)]::nat; 
    
    for i in 0 .. n  do
        {adr = (t << (sn + ln + 2)) || (li << (ln + 2));
         sc  = CellFill(i, adr, PM);
	 sliceCnt([i]::WI) <- sc([i]::WI)
	};
    H          = (a_lfill, [t], li) @ h;
    cnt.dirty <- false; cnt.value <- sliceCnt;
    cacheSl(t) <- Some(cnt);
    return (cacheSl, H)
} 

-- Here start defining the very initial verion of the cache interface functions.
-- These are functins that are available for core.
bool Hit(va::VA, pa::PA, dc::CACHE_ABS) =
{
    var cache  = dc;

    (li, t, wi) = lineSpec(va, pa);
    cset   = cache(li).sl;
    if(IsSome(cset(t)))
    then true
    else false
}

bool LineDirty(li::SI, t::TAG, dc::CACHE_ABS) = 
{
    var cache = dc;

    csl    = cache(li).sl;
    cslCnt = ValOf(csl(t));
    return cslCnt.dirty     
}

bool lDirty(va::VA, pa::PA, dc::CACHE_ABS) =
{
    var cache  = dc;
    (li, t, wi) = lineSpec(va, pa);
    return LineDirty(li, t, dc)     
}

CACHE_ABS * MEM_ABS EvictAlias(va::VA, pa::PA, pm::MEM_ABS, dc::CACHE_ABS) =
{
    var PM     = pm;
    var cache  = dc;

    eli        = Alias(va, pa, cache);
    (_, t, wi) = lineSpec(va, pa);

    if(IsSome(eli))
    then{li               = ValOf(eli);
         (ca, mm)         = WriteBackLine(li, t, PM, cache, (2 ** [DC.ctr.DminLine]::nat - 1));
         cache <- ca;  PM <- mm;
    	 (cacheSl, cacheH)= Evict(cache(li).hist, li, t, cache);
         cache(li).sl <- cacheSl;  cache(li).hist <- cacheH; 	 
    	 return (cache, PM)
    	}
    else  return (cache, PM)
}


-- The function invalidates a memory block starting at address adr(va, pa).
-- The address is aligned to a line size boundry.
CACHE_ABS * MEM_ABS CacheInvalidateByAdr(va::VA, pa::PA, pm::MEM_ABS, dc::CACHE_ABS) =
{
    var PM     = pm;
    var cache  = dc;
    lineSize   = (2 ** [DC.ctr.DminLine]::nat - 1);
    (li, t, wi)= lineSpec(va, pa);

    when(Hit(va, pa, cache)) do
       {(ca, mm)         =  WriteBackLine(li, t, PM, cache, lineSize); 
        cache <- ca;  PM <- mm;
        (cacheSl, cacheH)= Evict(cache(li).hist, li, t, cache);
        cache(li).sl <- cacheSl;  cache(li).hist <- cacheH
       };    
    return (cache, PM) 
}

-- The function cleans a memory block starting at address adr(va, pa).
-- The address is aligned to a line size boundry.
CACHE_ABS * MEM_ABS CacheCleanByAdr(va::VA, pa::PA, pm::MEM_ABS, dc::CACHE_ABS) =
{
    var PM     = pm;
    var cache  = dc;
    lineSize   = (2 ** [DC.ctr.DminLine]::nat - 1);
    (li, t, wi)= lineSpec(va, pa);

    when(Hit(va, pa, cache)) do
       {(ca, mm) = WriteBackLine(li, t, PM, cache, lineSize);
        cache <- ca;  PM <- mm
       };
    return (cache, PM) 
}

CACHE_ABS * MEM_ABS Fill(va::VA, pa::PA, pm::MEM_ABS, dc::CACHE_ABS) =
{
    lineMask     = 0xFFFFFFFFFFC0::PA;
    lineSize     = (2 ** [DC.ctr.DminLine]::nat - 1);
    var PM       = pm;
    var cache    = dc;
    var csl :: SLICE;
    
    (li, t, wi)   = lineSpec(va, pa);
    var cacheSet = cache(li).sl;
    var cacheSl  = cacheSet(t);

    
    et     = EP(cache(li).hist, t, cache);
    match et
        {case Some(et)   => 
            {(ca, mm)     =  WriteBackLine(li, [et], PM, cache, lineSize);
             cache <- ca; PM <- mm;
             (sl, h)      =  Evict(cache(li).hist, li, et, cache);
             cache(li).sl <- sl; cache(li).hist <- h;
             (sl, h)      =  LineFill(cache(li).hist,li, t, PM, cache, lineSize); 
             cache(li).sl <- sl; cache(li).hist <- h
             --return EvictAlias(va, pa, PM, cache)
            }	       
         case _ => 
            {(sl, h) = LineFill(cache(li).hist, li, t, PM, cache, lineSize);
             cache(li).sl <- sl; cache(li).hist <- h
            }
    };
    return (cache, PM)
}

word CellRead(i::SI, t::TAG, wi::nat, dc::CACHE_ABS) =
{
    cset = dc(i).sl;
    csl  = ValOf(cset(t));
    cnt  = csl.value([wi]::WI);
    return [cnt]
}
-- !i . dirty(i) ==> CacheRead = cache(i).value
CACHE_ABS * MEM_ABS * (bool list) CacheRead(va::VA, pa::PA, pm::MEM_ABS, dc::CACHE_ABS) =
{
    var PM     = pm;
    var cache  = dc;
    var cacheH :: HIST_ABS;

    (li, t, wi) = lineSpec(va, pa);
    if(Hit(va, pa, cache))
    then{(cset,cacheH)  = Touch(cache(li).hist, li, t, [wi]::WI, None, cache);
	 csl            = ValOf(cset(t));
         cnt            = csl.value([wi]::WI);
	 cache(li).hist <- cacheH;
 	 return (cache, PM, [cnt]) 
    }
    else{(ca, mm)       = Fill(va, pa, PM, cache);
         cache <- ca;  PM <- mm;
         cset           = cache(li).sl;
    	 csl            = ValOf(cset(t));
         cnt            = csl.value([wi]::WI);
	 cache(li).hist <-(a_read, [t], li) @ cache(li).hist;
	 return (cache, PM, [cnt])
    }
}

CACHE_ABS * MEM_ABS CacheWrite(va::VA, pa::PA, data::wrTyp, pm::MEM_ABS, dc::CACHE_ABS) =
{
    var PM     = pm;
    var cache  = dc;

    (li, t, wi) = lineSpec(va, pa);
    if(Hit(va, pa, cache))
    then{(cacheSl, cacheH) = Touch(cache(li).hist, li, t, [wi]::WI, Some(data), cache);  
	 cache(li).sl      <- cacheSl; cache(li).hist <- cacheH; 
	 return (cache, PM) 
    }
    else{(ca, mm)          = Fill(va, pa, PM, cache);
   	 (cacheSl, cacheH) = Touch(ca(li).hist, li, t, [wi]::WI, Some(data), ca); 
	 cache(li).sl      <- cacheSl; cache(li).hist <- cacheH;
	 return (cache, mm)
    }
}





