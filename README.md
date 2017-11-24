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

Below we list all proof obligations on the abstract cache-aware hardware model.

* *abs_ca_trans_mode_oblg*: the mode parameter in the transition relation
   correctly reflects the mode of the starting state
* *abs_ca_trans_dmvalt_oblg*: steps of the cache-aware model that do not touch
   an address leave its memory view unchanged
* *abs_ca_trans_dmvalt_not_write_oblg*: steps of the cache-aware model that
   touch an address but do not write it leave its memory view unchanged
* *abs_ca_trans_dcoh_write_oblg*: cacheable writes make the written addresses
   data-coherent
* *abs_ca_trans_dCoh_preserve_oblg*: cacheable accesses preserve data-coherence
* *abs_ca_trans_drvbl_oblg*: the transition relation for USER steps of the
   cache-aware model is a subset of the deriveability relation, if the MMU
   domain is data-coherent and not writable in user mode
* *abs_ca_trans_switch_lem*: any user step of the cache-aware model that
   switches mode to privileged leads into an exception entry state, i.e., only
   exceptions may escalate the execution mode privileges
* *abs_ca_progress_oblg*: the cache-less model never gets stuck
* *abs_ca_trans_icoh_clean_preserve_oblg*: addresses that are data and
   instruction coherent and clean preserve their instruction coherency and
   cleanness by a step of the cache-aware model if they are not written
* *ca_deps_pc_oblg*: the translated PC is always contained in the dependencies
   of the current instruction
* *ca_vdeps_PC_oblg*: the PC is always contained in the virtual dependencies of
   the current instruction
* *ca_fixmmu_Tr_oblg*: if the MMU is fixed to a given translation function f for
   a domain of virtual addresses VA, then all addresses va in VA will be
   translated by the hardware to f(va)

On the cacheless model we have the following proof obligations:

* *abs_cl_trans_mode_oblg*: the mode parameter of the transition relation
   correctly reflects the mode of the current state
* *abs_cl_trans_not_write_oblg*: the cache-less core-view of an address does not
   change when it is not written
* *abs_cl_trans_not_adrs_oblg*: the cache-less core-view of an address does not
   change when it is not touched at all
* *abs_cl_trans_fixmmu_CA_lem*: if the MMU is fixed to only provide cacheable
   aliases in privileged mode, every privileged transition of the cacheless
   model will only perform cacheable memory operations
* *abs_cl_progress_lem*: the cacheless model never gets stuck

More obligations are needed in order to couple the cache-aware and cacheless
model in the bisimulation proof for kernel execution:

* *core_bisim_dl_oblg*: if a cache-aware and cacheless state have the same core
   configuration, the states agree on the data view of the dependencies of the
   next instruction of the cache-aware model, and the cacheless view and the
   instruction view agree on the translated PC, then the next steps in both
   models will exhibit the same memory operations
* *core_bisim_oblg*: in the scenario above, if additionally both states have the
   same dependencies for the next instruction and the memory operations
   performed are only cacheable operations, then the resulting core states are
   equal again, and the data views agree on all written addresses
* *deps_eq_oblg*: if a cache-aware and cacheless state have the same core
   configuration, the states agree on the data view of the dependencies of the
   next instruction of the cache-aware model, then the dependencies of the next
   instruction in both states are equal
* *cl_deps_eq_oblg*: if a cache-aware and cacheless state have the same core
   configuration, the states agree on the data view of the dependencies of the
   next instruction of the cacheless model, then the dependencies of the next
   instruction in both states are equal
* *deps_vdeps_eq_oblg*: if a cache-aware and cacheless state have the same core
   configuration, the states agree on the data view of the dependencies of the
   next instruction of the cache-aware model, then the virtual dependencies of
   the next instruction in both states are equal

In addition to these properties, the proof of the *selective eviction*
countermeasure introduces the following proof obligations on the hardware:

* *abs_ca_trans_clean_oblg*: addresses that are targeted by data flush
   operations on the cache-aware model become clean
* *abs_ca_trans_clean_preserve_oblg*: data-coherent and clean addresses stay
   clean if they are not written in the cache-aware model
* *abs_ca_trans_dcoh_flush_oblg*: addresses that are targeted by data flush
   operations on the cache-aware model become data-coherent
* *abs_ca_trans_icoh_flush_oblg*: addresses that are targeted by instruction flush
   operations on the cache-aware model become instruction-coherent
* *abs_ca_trans_icoh_clean_preserve_oblg*: data-coherent, instruction-coherent
   and clean addresses stay instruction coherent if they are not written or
   data-flushed in the cache-aware model
* *abs_ca_trans_clean_disj_oblg*: a cache-aware model step never performs both
   data and instruction flush operations
* *abs_ca_trans_i_w_disj_lem*: a cache-aware model step never performs both
   instruction flush and write operations
* *abs_cl_trans_clean_disj_oblg*: a cacheless model step never performs both
   data and instruction flush operations
* *abs_cl_trans_i_w_disj_lem*: a cacheless model step never performs both
   instruction flush and write operations


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
are introduced here together with the MMU domain (MD) as well as the definitions
of core-view (CV), mode (Mode), and exception entry state (exentry).

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
* *clean*: predicate stating that a cache line is either not dirty or its data
   cache content is consistent with its memory content
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
* *clean_oblg*: the cleanness of an address only depends on the corresponding
   data cache entry and its memory content
* *clean_dirty_oblg*: if an address is dirty but clean, its data cache and
   memory contents agree
* *clean_not_dirty_oblg*: non-dirty lines are always clean
* *clean_equal_oblg*: if data cache content and memory content agree for a given
   pa, it is considered clean
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
   and written back to memory if it was dirty, or it was made dirty by a write
   to an address hitting the same cache line
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
* *ic_cacheable_cl_other_oblg*: an instruction cache flush only affects
   instruction cache entries for addresses other than the flushed one by
   evicting them as well
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
   instruction cache and memory contents agree and it is clean in the data
   cache, i.e., not dirty or consistent with the memory content (2)
* *icoh_flush_oblg*: an instruction flush makes the flushed address instruction
   coherent
* *icoh_preserve_oblg*: instruction coherency is preserved for addresses that
   are clean and not written in a memory system operation
* *imv_dmv_oblg*: for clean, data and instruction coherent address, the data
   and instruction view agree
* *imv_dmvcl_oblg*: for instruction coherent addresses the cacheless and
   instruction view agree
* *imv_fetch_oblg*: instruction fetches preserve the instruction view of
   instruction coherent addresses
* *imv_flush_oblg*: instruction cache flushes preserve the instruction view of
   instruction coherent addresses
* *msca_clean_preserve_oblg*: clean and data coherent addresses are kept clean
   by data operations unless they are written
* *imv_preserve_oblg*: for clean, data and instruction coherent addresses,
   the instruction view is unchanged, unless they are written

(2) These proof obligations are broken by memory systems with a unified L2 cache
from which the instruction cache can be filled and in which instruction fetches
may be allocated, causing eviction of dirty data entries. To support such cases
the obligations need to be generalized along with the proofs of the lemmas that
depend on them in the simple hardware model above. Instruction coherency needs
to be extended as well, e.g., by demanding data coherency for the unified L2
cache. This work is ongoing.

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
*ctf*, an uninterpreted eviction policy, and proof obligations that define the
expected cache semantics. We omit a more detailed description here. Naturally,
many of these properties are used to discharge the proof obligations on the
memory system.

As an example instantiation we provide a very rudimentary direct-mapped and
write-back cache definition, where lines are exactly one word long. All proof
obligations of the cache interface are discharged on this model. Work on an
instantiation with a more realistic cache design is ongoing.

## Instantiation of the Theory

The provided theorems can be instantiated for different softwares and
hardwares. Below we describe how the proof obligations on hardware, invariants,
and the code can be discharged separately.

### Hardware Instantiation

Our abstract hardware model assumes that the underlying hardware can be split
into a core component and a memory system component, containing all caches and
main memory. In order to connect such a hardware model to this theory, one must
instantiate the core and memory system interface functions on top of it and
prove the hardware proof obligations on the abstract hardware layer outlined
above.

Parts of our example instantiation can be reused, if the concrete model of the
hardware is split into a core and memory system component and the core issues at
most one memory operation per system transition. In this case, one can
instantiate the core and memory system interface separately and discharge the
corresponding lower level proof obligations. Our proofs yielding the abstract
hardware layer obligations can then be reused.

In principle one can also re-use our instantiation of the memory system, if only
one layer of separate data and instruction cache is present. Then it suffices to
instantiate the core and cache interfaces separately. However, in its current
shape the cache interface is not general enough to support realistic
instantiations, as some of its proof obligations rely on simplifications in our
underlying rudimentary instantiation. Work to generalize the cache interface is
ongoing.

### Software Instantiation (Invariants)

Software-specific properties are introduced in the theory by means of
specification functions. For a given software these specification functions need
to replaced by their corresponding definitions in the formal specification of
that software. In particular, one must instantiate:

* *cl_Inv* / *Ifun*: the functional invariant on the cacheless model /
   cache-aware model
* *Inv*: the invariant on the cache-aware model
* *cl_CR* / *CR*: the critical resources in the cacheless / cache-aware model
* *cl_CRex* / *CRex*: the executable critical resources in the cacheless /
   cache-aware model

In general definitions on the cache-aware model should be obtained by expressing
their cacheless counterparts wrt. the cache-aware data view of memory. Then the
following statements need to be proven about these functions.

* *CR_oblg*: if the functional invariant holds on the cache-aware model, then CR
   is self-contained, i.e., CR only depends on the data-view of resources
   contained in CR
* *CR_coreg_oblg*: only coprocessor registers can be part of the critical
   resources
* *CRex_eq_oblg*: if the functional invariant holds on the cache-aware model,
   then CRex is self-contained, i.e., CRex only depends on the data-view of
   resources contained in CRex
* *CRex_oblg*: CRex only contains memory resources and is a subset of CR
* *Ifun_CR_oblg*: Ifun only depends on the data view of resources in CR
* *Ifun_MD_oblg*: all resources in the Mmu domain are contained in CR
* *Ifun_Mon_oblg*: Ifun constrains the Mmu in such a way that resources in CR
   are not writable in user mode
* *Inv_oblg*: the invariant on the cache-aware model is exactly the conjunction
   of Ifun with the counter-measure specific invariants Icoh, Icode, and Icm

Note that all obligations on the counter-measure specific invariants have
already been discharged for always cacheability and selective eviction.

The always cacheability countermeasure introduces further proof obigations on
the functional invariant:

* *Ifun_AC_user_po*: the functional invariant guarantees that all aliases to the
   always cacheable region are cacheable and that the critical memory resources
   always lie in the always cacheable region
* *Ifun_AC_kernel_po*: the Kcode region is mapped into the critical executable
   resources and it is executable in privileged mode

### Software Instantiation (Code Verification)

The antecedents of the resulting theorems contain code verification
conditions. In particular all theorems rely on:

* *cl_Inv_po*: the functional invariant is preserved by the execution of kernel
   handlers in the cacheless model
* *cl_II_po*: the countermeasure specific parts of the intermediate invariant
   hold throughout the kernel execution on the cacheless model

Once these verification conditions are discharged, the theorems can be
strengthened by removing these assumptions. 

### Countermeasure Verification

The presented framework can be used to verify new countermeasures that preserve
integrity. In order to do so the following predicates need to be instantiated:

* *Icoh*: the invariant on the cache-aware model guaranteeing data-coherency of
   the critical resources
* *Icode*: the invariant on the cache-aware model guaranteeing
   instruction-coherency and cleanness of the executable critical resources
* *Icm*: a countermeasure-specific invariant to guarantee instruction / data
   coherency of other resources
* *cl_Icmf*: functional properties of the kernel code on the cacheless model
   that give the correctness of the countermeasure wrt. data coherency
* *ca_Icmf*: data coherency-related properties established by the countermeasure
   during the execution of kernel code
* *cl_Icodef*: functional properties of the kernel code on the cacheless model
   that give the correctness of the countermeasure wrt. instruction coherency
* *ca_Icodef*: instruction coherency-related properties established by the
   countermeasure during the execution of kernel code

The corresponding proof obligations are collected in predicates *cm_user_po* and
*cm_kernel_po* demanding the following properties:

* *Icoh_CR_po*: Icoh only depends on the coherency of critical resources, their
   data-view, and the functional invariant on them
* *Icoh_dCoh_po*: Icoh and Ifun guarantee the data coherency of critical
   resources
* *Icode_CR_po*: Icoh only depends on the instruction coherency and cleanness of
   executable critical resources, their data-view, and the functional invariant
   on them
* *Icode_iCoh_po*: Icode and Ifun guarantee the instruction coherency of
   executable critical resources
* *Icode_isafe_po*: Icode and Ifun guarantee the cleanness of executable
   critical resources
* *Icm_po*: Icm is preserved by derivable transitions from a state where Inv
   holds
* *Icmf_init_xfer_po*: if cl_Icmf holds in an exception entry point together
   with cl_Inv on the cacheless model, then ca_Icmf holds in any simulating
   cache-aware state where Inv holds
* *Icodef_init_xfer_po*: if cl_Icodef holds in an exception entry point together
   with cl_Inv and cl_Icmf on the cacheless model, then ca_Icodef holds in any
   simulating cache-aware state where Inv and ca_Icmf hold
* *Icmf_xfer_po*: given simulating pairs of states (s,sc), (s',sc'), and
   (s'',sc'') such that 
  1. (s,sc) are exception entry points where cl_Inv and
   Inv hold, respectively, 
  2. the intermediate invariants hold between s and s' as well as sc and sc', 
  3. both cacheless and cache-aware models perform
   a step from s' to s'', resp. sc' to sc'', 
  4. the histories in (s',s'') agree with (sc',sc'') and are computed correctly
  for the cache-aware step, and 
  5. cl_Icmf holds between s and s'', 
  
  then ca_Icmf holds between sc and sc''
* *Icodef_xfer_po*: in the same scenario as above if additionally cl_Icodef
   holds between s and s'', and ca_Icmf holds between sc and sc'', then
   ca_Icodef holds between sc and sc''
* *cl_Icmf_po*: on any kernel computation from a cacheless state s to s', if
   cl_Icmf holds between them, then the hardware only performs cacheable
   operations
* *ca_Icmf_po*: if Icoh holds in s and ca_Icmf holds between s and s', then the
   dependencies of the next instruction in s' are data-coherent
* *ca_Icodef_po*: if Inv holds in s and ca_Icmf and ca_Icodef holds between s
   and s', then the translation of the PC in s' is instruction-coherent and
   clean
* *Inv_rebuild_po*: given simulating pairs of states (s,sc) and (s',sc') such that 
  1. (s,sc) are exception entry points where cl_Inv and Inv hold, respectively,
  2. the intermediate invariants hold between s and s', resp. sc and sc',
  3. the history variables in s' and sc' agree, 
  4. cl_Inv holds in s', and 
  5. in both s' and sc' are the excecution mode is unprivileged,

  then Ifun, Icoh, and Icode hold in sc'
* *Icm_f_po*: if the intermediate invariant holds between s and s' and the
   execution mode in s' is unprivileged, Icm holds in s'

Once these obligations are discharged for a given countermeasure, *cm_user_po*
and *cm_kernel_po* can be removed from the antecedents of the generic kernel
integrity theorems, yielding the integrity result for this countermeasure. Here,
this procedure has been demonstrated for always cacheability and selective
eviction.