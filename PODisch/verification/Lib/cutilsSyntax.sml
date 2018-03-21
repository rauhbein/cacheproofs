structure cutilsSyntax :> cutilsSyntax =
struct

open numSyntax pairLib pairTools Abbrev HolKernel;

val writeBackLine_tm       = prim_mk_const {Name="WriteBackLine",   Thy="cache"};
val dest_writeBackLine     = HolKernel.dest_monop writeBackLine_tm (ERR "dest_writeBackLine" "");
val is_writeBackLine       = can dest_writeBackLine;

val evict_tm       = prim_mk_const {Name="Evict",   Thy="cache"}
val dest_evict     = dest_monop evict_tm (ERR "dest_evict" "")
val is_evict       = can dest_evict

val lineFill_tm       = prim_mk_const {Name="LineFill",   Thy="cache"}
val dest_lineFill     = dest_monop lineFill_tm (ERR "dest_lineFill" "")
val is_lineFill       = can dest_lineFill

val Fill_tm       = prim_mk_const {Name="Fill",   Thy="cache"}
val dest_Fill     = dest_monop Fill_tm (ERR "dest_Fill" "")
val is_Fill       = can dest_Fill


val cacheRead_tm       = prim_mk_const {Name="CacheRead",   Thy="cache"}
val dest_cacheRead     = dest_monop cacheRead_tm (ERR "dest_cacheRead" "")
val is_cacheRead       = can dest_cacheRead

val cacheWrite_tm       = prim_mk_const {Name="CacheWrite",   Thy="cache"}
val dest_cacheWrite     = dest_monop cacheWrite_tm (ERR "dest_cacheWrite" "")
val is_cacheWrite       = can dest_cacheWrite

val lineSpec_tm       = prim_mk_const {Name="lineSpec",   Thy="cache"}
val dest_lineSpec     = dest_monop lineSpec_tm (ERR "dest_lineSpec" "")
val is_lineSpec       = can dest_lineSpec;

end
