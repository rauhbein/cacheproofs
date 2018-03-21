signature cutilsSyntax =
sig
     include Abbrev
val dest_Fill : term -> term
val dest_cacheRead : term -> term
val dest_cacheWrite: term -> term
val dest_evict : term -> term
val dest_lineFill : term -> term
val dest_lineSpec : term -> term
val dest_writeBackLine: term -> term
val is_Fill : term -> bool
val is_cacheRead : term -> bool
val is_cacheWrite : term -> bool
val is_evict : term -> bool
val is_lineFill : term -> bool
val is_lineSpec : term -> bool
val is_writeBackLine : term -> bool

end