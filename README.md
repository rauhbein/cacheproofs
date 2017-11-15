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
* *Mmu_oblg*:the translation of some virtual addresses by the MMU only depends
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

