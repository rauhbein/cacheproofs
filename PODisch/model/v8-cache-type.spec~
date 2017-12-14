-----------------------------------------------------------------------
-- This an extension of:					     --	
-- 								     --
-- Formal Specification of the ARMv8-A instruction set architecture  --
-- (c) Anthony Fox, University of Cambridge                          --
-- 								     --
-- for introducing cache configuration register 		     --
-- Author: Hamed Nemati, KTH CSC Stockholm			     --
-----------------------------------------------------------------------


---------------------------------------------
-- Basic types
---------------------------------------------
type word = bits(32)
-- maximal physical address size
type ADR  = bits(48)
-- effective virtual and physical address
type VA   = bits(64)     -- virtual address
type PA   = bits(48)     -- physical address

record wrTyp 
{
   value :: word	
   flag  :: bool  
}

-- Some Notes on Cortex-A53: 
-- The data cache is 4-way set associative and uses a Physically Indexed Physically Tagged (PIPT) scheme for lookup that enables unambiguous address management in the system.
-- The data cache has the following features:
--  • Pseudo-random cache replacement policy.
--  • Critical word first linefill on a cache miss.


---------------------------------------------
-- Core Registers
---------------------------------------------

---------------------------------------------
-- Cache Size ID Register
-- Purpose: Provides information about the architecture of the caches.
-- Usage constraints This register is accessible as follows:
-- |EL0(NS/S)|EL1(NS/S)|EL2|EL3(NS=1/0)         
   ------------------------------------------
-- |-        |RO       |RO |RO 

-- Configurations: CCSIDR is architecturally mapped to AArch64 register CCSIDR_EL1.
-- Attributes: CCSIDR is a 32-bit register.
---------------------------------------------
register CCSIDR :: word
{
   31 : WT       -- Indicates support for Write-Through 0: Cache level does not support Write-Through.
   30 : WB       -- Indicates support for Write-Back 0/1
   29 : RA       -- Indicates support for Read-Allocation 0/1
   28 : WA       -- Indicates support for Write-Allocation 0/1
27-13 : NumSets  -- Indicates the number of sets in cache - 1. Therefore, a value of 0 indicates 1 set in the cache. The number of sets does not have to be a power of 2.   
12-3  : Associativity  -- Indicates the associativity of cache - 1. Therefore, a value of 0 indicates an associativity of 1. The associativity does not have to be a power of 2.
 2-0  : LineSize -- Indicates the (log2 (number of words in cache line)) - 2, 0b010:16 words per line
}


---------------------------------------------
-- Cache Size Selection Register
-- Purpose: Selects the current Cache Size ID Register, by specifying:
--  • The required cache level.
--  • The cache type, either instruction or data cache.
-- Usage constraints This register is accessible as follows:
-- |EL0|EL1(NS/S)|EL2|EL3(NS=1/0)         
   ------------------------------------------
-- |-  |RW       |Rw |RW 

-- Configurations: CSSELR_EL1 is architecturally mapped to AArch32 register CSSELR(NS).
-- Attributes: CSSELR_EL1 is a 32-bit register.
---------------------------------------------
register CSSELR_EL1 :: word
{
31-4  : RES0     -- Reserved, RES 0
 3-1  : Level    -- Cache level of required cache: i) 0b000--> L1 ii) 0b001--> L2 iii) 0b010-0b111 Reserved.
   0  : InD      -- Instruction not Data bit: i) 0--> Data or unified cache  ii) 1-->Instruction cache
}

---------------------------------------------
-- Cache Type Register
-- Purpose: Provides information about the architecture of the caches.
-- Usage constraints
-- This register is accessible as follows:
-- |EL0|EL1(NS)|EL1(S)|EL2|EL3(NS=1)|EL3(NS=0)         
   ------------------------------------------
-- |-  |RO     |RO    |RO |RO       |RO

-- Configurations: CTR_EL0 is architecturally mapped to AArch32 register CTR
-- Attributes: CTR_EL0 is a 32-bit register.
---------------------------------------------
register CTR :: word
{
   31 : RES1     -- Reserved, res1.
30-28 : RES00    -- Reserved, res0.
27-24 : CWG      -- Cache Write-Back granule
23-20 : ERG	 -- Exclusives Reservation Granule.
19-16 : DminLine -- Log2 of the number of words in the smallest cache line of all the data and unified caches that the processor controls,  0x4: Smallest data cache line size is 16 words.
15-14 : L1Ip     -- L1 Instruction cache policy. Indicates the indexing and tagging policy for the L1 Instruction cache, 0b10: Virtually Indexed Physically Tagged (VIPT).
13-4  : RES01     -- Reserved, res0. 	
 3-0  : IminLine  -- Log2 of the number of words in the smallest cache line of all the instruction caches that the processor controls, 0x4: Smallest instruction cache line size is 16 words.
}




---------------------------------------------
-- Types
---------------------------------------------
record CACHE_CONFIG -- Cache configuration data structure
{
    ccsidr     :: CCSIDR
    csselr_el1 :: CSSELR_EL1
    ctr        :: CTR 
}

type words  = word list

---------------------------------------------
-- cache specifice types
---------------------------------------------
type TAG      = bits(48)    -- line tag
type SI       = bits(48)    -- cache set index
type WI       = bits(48)    -- word index
type LINE     = words * bool -- cache line
record SLVAL
{
    value :: WI -> word
    dirty :: bool
} 
type SLICE    = TAG ->  (SLVAL option)
construct actions
{
    a_read
    a_write
    a_evict
    a_lfill
}   
type HIST_ABS = (actions * nat * SI) list

record CSET
{   sl   :: SLICE
    hist :: HIST_ABS
}
type CACHE_ABS   = SI -> CSET

-- Cache exception
exception CACHE_WRITE_FAULT
---------------------------------------------
-- cache uninterpreted functions 
---------------------------------------------
declare DC        :: CACHE_CONFIG
--declare EP        :: HIST_ABS * TAG  -> (TAG * SI) option -- eviction policy
(TAG) option EP(h::HIST_ABS, t::TAG, dc::CACHE_ABS)=
{
  UNKNOWN
}
-- declare lineMask  :: PA

-- declare cache 	  :: CACHE_ABS
type MEM_ABS = ADR -> bits(8)
-- declare PM :: MEM_ABS

bool list read_mem_inner(size :: bits(N), ad :: ADR, pm :: MEM_ABS) with N in 8, 16, 32, 64, 128 = 
{
    n = N div 8;
    var d = Nil :: bool list;
    var PM = pm;

    -- convert to little endian bool list
    for i in 0 .. n-1 do d <- [PM(ad+[i])] : d;

    return d
}

bool list read_mem32 (ad :: ADR, pm :: MEM_ABS) = {
  [(pm(ad+3):pm(ad+2):pm(ad+1):pm(ad+0))]
}

--declare dbgVct:: nat

