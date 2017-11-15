# cacheproofs
HOL4 implementation of the proof strategy for the verification of cache storage
channels countermeasures to ensure system integrity

## Files 

The following files are provided:

* *integrityScript.sml*: user and kernel integrity proof based on proof
   obligations on hw, sw, and invariants
* *AC_cmScript.sml*: discharging all proof obligations for always cacheability,
   resulting theorems with additional SW proof obligations
* *SE_cmScript.sml*: discharging all proof obligations for always cacheability,
   resulting theorems with additional SW proof obligations
* *InvIfScript.sml*: introduces CR, EX, simulation relation, and invariants on
   cacheless and cache-aware model, as well as proof obligations on invariants
* *hwScript.sml*: hardware abstraction layer for cache aware model, introduces
   deriveability and hw proof obligations, all discharged on
   single-memory-request model based on core and memory system interface, proofs
   about (data/instruction) coherency and derivability
* *cachelessScript.sml*: hardware abstraction layer for the cacheless model, all
   proof obligation discharged on a single-request model based on core interface
   and a flat memory without caches or coherency issues.
* *coreIfScript.sml*: abstract core interface including hw proof obligations,
   axiomatic style using specification functions
* *msIfScript.sml*: memory system interface including hw proof obligations on
   cache behaviour, all discharged on model with separate L1 instruction and
   data cache
* *cachememScript.sml*: cacheless and cache-aware memory semantics, based on
   abstract cache interface, supports both write through or write back
* *cacheIfScript.sml*: abstract cache interface, all obligations discharged on
   simple cache model: one word per cache line, direct-mapped, write back,
   eviction policy underspecified
* *histScript.sml*: introduces history variables based on the performed memory
   operations on top of both models
* *basetypesScript.sml*: basic datatypes and helper functions
* *userint.dot*: dependency graph for the user integrity proof (dot format)
* *kernelint.dot*: dependency graph for the kernel integrity proof (dot format)
* *README.md*: this file

## Theorems

We prove the two main theorems of integrity assuming the proof obligations lined
out in the paper. Additionally we dicharge proof obligations for the
countermeasures yielding theorems that depend only on proof obligations on the
code of the kernel running in the cacheless model.

### Theorem 1 (Inv_user_preserved_lem)

A user mode step on the cache-aware model preserves the invariant.

### Theorem 2 (kernel_integrity_sim_thm)

Every run of the kernel on the cache-aware model preserves the invariant and
there exists a simulating computation in the cacheless model.

### Corollary (overall_integrity_thm)

The invariant is preserved by the weak transition relation which is the union of
user steps and complete kernel executions.

### Countermeasure verification

All three theorems are instantiated for the countermeasures of
*always-cacheability* and *selective eviction*. The resulting theorems are

* Inv_AC_user_preserved_thm
* kernel_integrity_sim_AC_thm
* overall_integrity_AC_thm

for the former and

* Inv_SE_user_preserved_thm
* kernel_integrity_sim_SE_thm
* overall_integrity_SE_thm

for the latter countermeasure.

## Lemmas and Proof Obligations

TODO

## Hardware Abstraction Layers

We introduce several abstraction layers in the overall theory with interfaces
between them to ease the hardware instantiation. On one layer of abstraction the
assumptions on the hardware are imported as lemmas verified using proof
obligations shown on the lower level. These hardware proof obligations are
tagged by the suffice "_oblg".

### Abstract Hardware Layer

On this top level layer hardware steps of the cacheless and cache-aware model
are represented by transition relations (abs_cl_trans and abs_ca_trans) that
relate pre and post state of a hardware step together with labels for the
associated execution mode and list of memory operations.

The latter may be read, writes, data cache flushes (DOP d) or instruction cache
flushes (IFL pa). By flushes here we refer to instructions that both clean and
invalidate the cache. Instruction fetch operations and MMU memory accesses are
implicit here, i.e., they are not mentioned explicitly in the labels, but may
occur in every step in addition to the explicitly named memory operations.

Fundamental assumptions (proof obligations) here are that the hardware is
deterministic and can always progress. Moreover, we assume that a single step
does not mix instruction cleaning, data cleaning, and write operations, which is
consistent with common instruction set architectures. Other assumptions concern
the effect of memory operations and the preservation or establishment of
coherency.

In addition we demand that user steps on the cache-aware model are in the
deriveability relation (abs_ca_trans_drvbl_oblg), and that cacheless and
cache-aware model perform the same step if they agree on the core-view of
dependencies of the current instruction (core_bisim_oblg).

### Single Memory Request Model

In order to sanity-check the hardware proof obligations, we discharge them on a
simple (cacheless and cache-aware) hardware model where only one memory
operation is performed per hardware step. In this model instruction fetches are
explicit, however operations on memory by the MMU are not modeled. The abstract
layer is instantiated in a trivial way by mapping steps one to one and all proof
obligations are discharged.

On the simple hardware model the execution of one instruction may take more than
one step. If instruction granularity is desired, several steps of the simple
model could be mapped to one step of the abstract model, collecting all memory
accesses in the list of operations associated with the abstract step.

The simple model itself is built on top of an abstract core interface and the
memory system interface, basically plugging these separate parts together by
forwarding memory requests of the core to the memory system and feeding back
replies to instruction fetch and read requests.

The same core interface is used by both cacheless and cache-aware model. On the
contrary, the cacheless hardware model uses a flat memory, while the cache-aware
model's memory system may contain data and instruction caches. The exact cache
structure is hidden by the memory interface at this level.

This abstraction layer introduces proof obligations on the core and memory
system, essentially pushing down assumption of the abstract hardware layer down
to the more concrete layers. However on this level we proof that derivability is
a sound abstraction of the simple hardware model as well as several properties
about coherency, using properties guaranteed by the cache-aware memory system
through proof obligations.

### Abstract Core Interface

This layer describes transitions on the core registers based on inputs from the
memory system. It completely abstracts from a specific instruction set
architecture and instead uses an axiomatic style, exposing only the necessary
properties of such core transitions.

In particular, it introduces transition relations *core_req* and *core_rcv*
where the former is the main transition function of the core. The main idea here
is that all atomic core transitions that can be performed without memory input,
are contained in core_req. In this step, also a request to the memory system may
be sent. Exceptions are handled by this step internally, e.g., by switching into
an exception entry state.

In case of read of instruction fetch requests, the corresponding reply is
then processed by core_rcv, without doing anything more. Note that writes, cache
flushes, and internal steps generated by a core_req step, do not require a
subsequent core_rcv step (however the composition with the memory system is
defined on the above abstraction layer).

Additionally, the dependency functions (deps and vdeps) of the hardware model
are introduced here together with the MMU domain as well as the definitions of
core-view (CV), mode (Mode), and exception entry state (exentry_).

The main properties assumed here are:

* *Mmu_oblg*: the translation of some virtual addresses by the MMU only depends
  on the corresponding MMU domain resources
* *MD_oblg*: the MMU domain is self-contained for a given set of virtual
   addresses  
* *MD_coreg_oblg*: only coprocessor registers are contained in the MMU domain
* *core_req_exentry_oblg*: only through exceptions it may be switched to
   privileged mode
* *exentry__oblg*: in an exception entry state the mode is privileged
* *core_req_mode_change_oblg*: the mode is not changed while there is an
   outstanding memory request
* *core_rcv_mode_oblg*: receiving a reply from the memory does not change the
   mode
* *core_req_user_MD_reg_oblg* and *core_rcv_user_MD_reg_oblg*: user steps cannot
   modify the registers controlling the MMU (coreg)
* *vdeps_PC_oblg*: the PC is contained in the virtual dependencies of an
   instruction
* *core_req_mmu_Freq_oblg*: instruction fetches always target the translated PC
* *core_req_mmu_Dreq_oblg* and *core_req_mmu_Ireq_oblg*: other operations always
   target some translated virtual dependency
* *deps__def*: the depencies always contain the translated virtual dependencies
  and the MMU domain for all virtual dependencies
* *core_req_det_oblg* and *core_rcv_det_oblg*: the core transition relations are
   deterministic if one fixes core and memory view, resp. the value of the
   received reply from the memory system in case of core_rcv
* *core_req_MD_mv_oblg*: the core_req transition (i.e., the sent request and the
  next state) is only depending on the core state and the core-view of the MMU
  domain of its virtual dependencies (1)
* *core_req_progress_oblg* and *core_rcv_progress_oblg*: the core transitions
   are always able to progress

(1) Intuitively this holds for a suitable instantiation, because instruction
fetches and memory operations are performed separately. A fetch request usually
only depends on the translation of the PC, thus on the resources needed to
translate it. After the reply to the fetch is received, the corresponding
instruction and all virtual dependencies of the next step can be
determined. Then the physical address of a subsequent memory access only depends
on the translation of these dependencies.

### Memory System Interface

The memory system interface abstracts from any concrete underlying cache and
memory architecture. However it is currently tailored to describe a single level
of caches. Note that on the abstract hw model, no such assumptions are made, this
restriction only concerns the intermediate memory system interface in its
current state.

#### Interface Functions

The memoty system interface provides the following definitions to describe the
memory functionality:

* *dw*: the data cache entry for a given physical address (pa)
* *dhit*: predicate stating whether a given pa hits the data cache
* *dirty*: predicate stating whether a given pa is dirty in the data cache
* *dcnt*: content for a given pa in the data cache
* *M*: Memory content for a given pa
* *iw*: the instruction cache entry for a given pa
* *ihit*: predicate stating whether a given pa hits the instruction cache
* *icnt*: content for a given pa in the instruction cache
* *dmvcl*: cacheless view of the memory system
* *dmvca*: cacheaware view of the memory system
* *dmvalt*: memory view of the memory system (if *dirty* then *dcnt* else *M*)
* *imv*: instruction view of the memory system
* *dcoh*: the notion of data coherency for a given pa
* *icoh*: the notion of instruction coherency for a given pa
* *isafe*: the notion of non-dirtyness for a potentially i-coherent pa
* *msca_trans*: transition function for the memory system

Note that in the paper instruction coherency is the conjunction of *dcoh*, *icoh*, and *isafe*. 

#### Interface Proof Obligations

For each instantiation of the memory system these functions need to be defined
in such a way that the following proof obligations hold:

* *M_dmvcl_oblg*: *dmvcl* returns the memory content
* *dmvca_hit_oblg*: if a pa hits the data cache(s), then *dmvca* returns *dcnt*
* *dmvca_miss_oblg*: in case of a miss, **dmvca* returns the memory content
* *imv_hit_oblg*: if a pa hits the instruction cache, *imv* returns *icnt*
* *imv_miss_oblg*: if a pa hits the instruction cache, *imv* returns the memory
   content (2)
* *dhit_oblg*: whether a pa hits in the data cache(s), depends only on its
   corresponding cache entry
* *double_not_dhit_oblg*: no information is contained in the data cache(s) for
   addresses that miss the cache, i.e., data cache entries in two different
   memory system states are equal for a pa that misses
* *dirty_oblg*: whether a pa is dirty in the data cache(s), depends only on its
   corresponding cache entry
* *not_dhit_not_dirty_oblg*: a pa that misses the data cache(s) is not dirty
* *dcnt_oblg*: the content stored for a given pa in the data cache depends only
   on its corresponding cache entry
* *ihit_oblg*: whether a pa hits in the instruction cache, depends only on its
   corresponding cache entry
* *double_not_ihit_oblg*: no information is contained in the instruction cache
   for addresses that miss the cache, i.e., instruction cache entries in two
   different memory system states are equal for a pa that misses
* *icnt_oblg*: the content stored for a given pa in the instruction cache
   depends only on its corresponding cache entry
* *msca_DREQ_unchanged_oblg*: data operations do not change entries of the
   instruction cache
* *msca_FREQ_unchanged_oblg*: instruction fetches do not change data cache
   entries or the memory (2)
* *msca_ICFR_unchanged_oblg*: instruction cache flushes do not change data cache
   entries or the memory
* *msca_write_val_oblg*: a cacheable write operation updates *dmvca* at the
   written pa to the written value
* *dc_cacheable_other_oblg*: if a cacheable data operation affects the cache
   entry of a different address than the one accessed, then this line is evicted
   and written back to memory if it was dirty (3)
* *M_cacheable_other_oblg*: if a cacheable data operation affects the memory of
   different address than the one accessed, then this was due to the write back
   of a dirty data cache line
* *M_cacheable_read_oblg*: cacheable read operations do not affect the memory
   content of the read address
* *dc_cacheable_read_oblg*: cacheable read operations only change the cache
   entry for the read address in case of a line fill, where a previously missing
   address now hits the cache, is not dirty, and the data cache is loaded with
   the corresponding value from memory.
* *dc_cacheable_write_oblg*: a cacheable write operation make the accessed
   address dirty in the cache, or in the write-through case makes it clean and
   writes the data to memory
* *M_cacheable_not_cl_oblg*: reads or writes leave the corresponding memory
   content unchanged or data cache and memory have the same contents for the
   accessed address
* *dc_cacheable_cl_oblg*: if a data cache flush affects a cache entry, it
   removes the flushed address from the data cache(s) and writes its cache
   content back to memory if it was dirty
* *dc_cacheable_cl_miss_oblg*: a data cache flush always results in a miss for
   the flushed address (5)
* *M_cacheable_cl_oblg*: if a data cache flush affects the memory for the
   flushed address, then it was dirty before and the new memory content is the
   former data cache content
* *ms_uncacheable_unchanged_oblg*: uncacheable read accesses do not affect the
   data cache(s) nor the memory
* *dc_uncacheable_unchanged_oblg*: uncacheable accesses bypass the data cache
* *M_uncacheable_others_oblg*: uncacheable accesses do not affect the memory
   contents for other addresses than the one accessed (written)
* *M_uncacheable_write_oblg*: if a write changes the memory of the written
   address it was either an uncacheable access or a write-through
* *ic_cacheable_other_oblg*: if an instruction fetch affects an entry of the
   instruction cache belonging to a different address than the one accessed, it
   is due to an eviction
* *ic_cacheable_read_oblg*: an instruction fetch only affects the corresponding
   cache entry if it was missing before and results in a cache fill of the
   address from memory (2)
* *ic_cacheable_cl_other_oblg*: an instruction cache flush does not affect
   instruction cache entries for addresses other than the flushed one (3)
* *ic_cacheable_cl_oblg*: if an instruction cache flush affects the target
   address' instruction cache entry, it results in a miss for that address
* *dcoh_oblg*: if memory and cache entries are unchanged for a given pa, then
   data coherency is preserved
* *dcoh_alt_oblg*: for data coherent addresses, *dmvca* and *dmvalt* are equal
* *dcoh_diff_oblg*: data coherency holds for pa iff a hit a difference between
   its data cache and memory contents imply that it is dirty
* *dcoh_clean_oblg*: for data coherent addresses that hit the data cache,
   non-dirtyness implies that its data cache and memory contents agree
* *dcoh_dirty_oblg*: dirty addresses are always data coherent
* *dcoh_equal_oblg*: address that have the same contents in the data cache(s)
   and memory are data coherent
* *dcoh_miss_oblg*: addresses that miss the data cache(s) are data coherent
* *dcoh_write_oblg*: cacheable writes make addresses data coherent
* *dcoh_ca_trans_oblg*: cacheable data operations preserve data coherency
* *dcoh_other_oblg*: all data operations (cacheable or not) preserve the data
   coherency of addresses not accessed by the operation
* *dcoh_not_write_oblg*: non-writing data operations preserve data coherency
* *dmv_unchanged_oblg*: for data coherent addresses that are not written,
   the cacheable data view *dmvca* is unchanged
* *dmvca_oblg*: the data view of an address only depends on its data cache entry
   and memory content
* *imv_oblg*: the instruction view of an address only depends on its instruction
   cache entry and memory content (2)
* *dmvalt_oblg*: the memory view of an address only depends on its data cache
   entry and memory content
* *dmvalt_unchanged_oblg*: the memory view is unchanged for addresses that are
   not touched by a data operation
* *dmvalt_not_write_oblg*: the memory view of an address is unchanged unless it
   is target of a write operation
* *iCoh_oblg*: instruction coherency holds for pa iff a hit implies that its
   instruction cache and memory contents agree and it is not dirty in the data
   cache (2)
* *icoh_flush_oblg*: an instruction flush makes the flushed address instruction
   coherent
* *icoh_preserve_oblg*: instruction coherency is preserved for addresses that
   are not dirty and not written in a memory system operation
* *imv_dmv_oblg*: for non-dirty, data and instruction coherent address, the data
   and instruction view agree
* *imv_dmvcl_oblg*: for instruction coherent addresses the cacheless and
   instruction view agree
* *imv_fetch_oblg*: instruction fetches preserve the instruction view of
   instruction coherent addresses
* *imv_flush_oblg*: instruction cache flushes preserve the instruction view of
   instruction coherent addresses
* *msca_clean_preserve_oblg*: non-dirty addresses are kept non-dirty by data
   operations unless they are written
* *imv_preserve_oblg*: for non-dirty, data and instruction coherent addresses,
   the instruction view is unchanged, unless they are written

(2) These proof obligations are broken by memory systems with a unified L2 cache
from which the instruction cache can be filled and in which instruction fetches
may be allocated, causing eviction of dirty data entries. To support such a case
they need to generalized along with the proofs of the lemmas that depend on them
in the simple hardware model above. Instruction coherency needs to be extended
as well, e.g., by demanding data coherency for the unified L2 cache. This work
is ongoing.

(3) Here our instantiation of the cache model with a word-length line size
shines through. To support wider caches, the proof obligations need to cover the
cases that addresses may be evicted or marked dirty by accesses to an address on
the same cache line. This work is ongoing.

#### Interface Instantiation

We instantiated the memory system interface with system consisting of a single
level of separate data and instruction caches being connected to mein
memory. The specific structure of the caches is uninterpreted here and based on
our abstract cache interface. 

The memory system itself is defined in the obvious way. Data operations, i.e.,
reads, writes, and data cache flushes, are directed to the data cache, while
instruction fetches and instruction cache flushes target the instruction
cache. By construction only Data operations may affect the memory, i.e., evicted
instruction are not written back to memory as they cannot become dirty.

All of the above memory system proof obligations have been discharged on this
model.

### Abstract Cache Model

The caches in the memory system are instances of our abstract cache model. For
an uninterpreted cache state, it provides the interface functions to access
cache entries and contents for a given address, and check whether such is
hitting the cache and being dirty. It also defines a cache transition function
*ctf* and proof obligations an uninterpreted eviction policy that define the
expected cache semantics. We omit a more detailed description here. Naturally,
many of these properties are used to discharge the proof obligations on the
memory system.

As an example instantiation we provide a very rudimentary direct-mapped and
write-back cache definition, where lines are exactly one word long. All proof
obligations of the cache interface are discharged on this model. Work on an
instantiation with a more realistic cache design is ongoing.

## Instantiation of the Theory

TODO