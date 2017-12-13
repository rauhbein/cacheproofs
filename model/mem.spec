-----------------------------------------------------------------------
-- Memory System              					     --	
-----------------------------------------------------------------------
(bool list) mv (cbl::bool, va::VA, pa::PA, pm::MEM_ABS, dc::CACHE_ABS) =
{
    if(cbl)
    then {vl = read_mem32(pa, pm);
    	  return vl}
    else {(c,m,vl) = CacheRead(va, pa, pm, dc);
    	  return vl}

}

