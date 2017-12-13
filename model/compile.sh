#echo 'val () = Runtime.LoadF"v8-cache-type.spec v8-Dcache.spec v8-cache-base.spec";val () = SMLExport.export "cache";' | l3
echo 'val () = Runtime.LoadF"v8-cache-type.spec v8-Dcache.spec v8-cache-base.spec mem.spec ";val () = HolExport.export "cache";' | l3


