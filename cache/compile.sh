#echo 'val () = Runtime.LoadF"../v8-base_types.spec, ../v8-mem_types.spec, ../v8-seqmem.spec v8-cache-type.spec v8-Dcache.spec v8-cache-base.spec v8-Dcache-base.spec test.spec";val () = SMLExport.export "cache";' | l3

echo 'val () = Runtime.LoadF"v8-cache-type.spec v8-Dcache.spec v8-cache-base.spec test.spec";val () = SMLExport.export "cache";' | l3
#echo 'val () = Runtime.LoadF"v8-cache-type.spec v8-Dcache.spec v8-cache-base.spec";val () = SMLExport.export "cache";' | l3


