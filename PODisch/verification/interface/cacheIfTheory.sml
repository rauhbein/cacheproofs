structure cacheIfTheory :> cacheIfTheory =
struct
  val _ = if !Globals.print_thy_loads then print "Loading cacheIfTheory ... " else ()
  open Type Term Thm
  infixr -->

  fun C s t ty = mk_thy_const{Name=s,Thy=t,Ty=ty}
  fun T s t A = mk_thy_type{Tyop=s, Thy=t,Args=A}
  fun V s q = mk_var(s,q)
  val U     = mk_vartype
  (*  Parents *)
  local open blastTheory cacheTheory
  in end;
  val _ = Theory.link_parents
          ("cacheIf",
          Arbnum.fromString "1521712448",
          Arbnum.fromString "37751")
          [("blast",
           Arbnum.fromString "1510750330",
           Arbnum.fromString "969185"),
           ("cache",
           Arbnum.fromString "1521643636",
           Arbnum.fromString "731319")];
  val _ = Theory.incorporate_types "cacheIf" [("dop", 0)];

  val idvector = 
    let fun ID(thy,oth) = {Thy = thy, Other = oth}
    in Vector.fromList
  [ID("min", "fun"), ID("min", "bool"), ID("cacheIf", "dop"),
   ID("pair", "prod"), ID("fcp", "cart"), ID("fcp", "bit0"),
   ID("one", "one"), ID("fcp", "bit1"), ID("cache", "cache_state"),
   ID("cache", "CSET"), ID("list", "list"), ID("num", "num"),
   ID("cache", "actions"), ID("option", "option"), ID("cache", "SLVAL"),
   ID("cache", "wrTyp"), ID("ind_type", "recspace"), ID("bool", "!"),
   ID("arithmetic", "+"), ID("pair", ","), ID("bool", "/\\"),
   ID("num", "0"), ID("min", "="), ID("min", "==>"), ID("bool", "?"),
   ID("min", "@"), ID("cacheIf", "ADD"), ID("bool", "ARB"),
   ID("arithmetic", "BIT1"), ID("ind_type", "BOTTOM"), ID("cacheIf", "CL"),
   ID("bool", "COND"), ID("ind_type", "CONSTR"), ID("cache", "CSET_hist"),
   ID("cache", "CSET_sl"), ID("cache", "CacheInvalidateByAdr"),
   ID("cache", "CacheRead"), ID("cache", "CacheWrite"),
   ID("cache", "CellRead"), ID("bool", "DATATYPE"), ID("cache", "EP"),
   ID("bool", "F"), ID("list", "HD"), ID("cache", "Hit"),
   ID("combin", "I"), ID("bool", "LET"), ID("cache", "LineDirty"),
   ID("cache", "LineFill"), ID("option", "NONE"),
   ID("arithmetic", "NUMERAL"), ID("cacheIf", "RD"),
   ID("cache", "SLVAL_value"), ID("pair", "SND"), ID("option", "SOME"),
   ID("num", "SUC"), ID("bool", "T"), ID("option", "THE"),
   ID("list", "TL"), ID("bool", "TYPE_DEFINITION"), ID("pair", "UNCURRY"),
   ID("cacheIf", "VAL"), ID("relation", "WF"), ID("relation", "WFREC"),
   ID("cacheIf", "WT"), ID("cache", "WriteBack"), ID("arithmetic", "ZERO"),
   ID("bool", "\\/"), ID("basicSize", "bool_size"), ID("cacheIf", "ca"),
   ID("cacheIf", "ccnt"), ID("cacheIf", "ccntw"), ID("cacheIf", "cl"),
   ID("cacheIf", "ctf"), ID("cacheIf", "dc2"), ID("cacheIf", "dop_CASE"),
   ID("cacheIf", "dop_size"), ID("cacheIf", "fcm"), ID("cacheIf", "fmem"),
   ID("cacheIf", "lcnt"), ID("cache", "lineSpec"), ID("cacheIf", "lv"),
   ID("cacheIf", "lw"), ID("cacheIf", "mllu"), ID("cacheIf", "mlwb"),
   ID("cacheIf", "mv"), ID("words", "n2w"), ID("pair", "pair_CASE"),
   ID("basicSize", "pair_size"), ID("cacheIf", "rd"),
   ID("cacheIf", "read32"), ID("cache", "wrTyp_size"), ID("cacheIf", "wt"),
   ID("bool", "~")]
  end;
  local open SharingTables
  in
  val tyvector = build_type_vector idvector
  [TYOP [1], TYOP [2], TYOP [0, 1, 0], TYV "'a", TYV "'c", TYV "'b",
   TYOP [3, 5, 4], TYOP [0, 6, 3], TYOP [3, 4, 7], TYOP [3, 5, 8],
   TYOP [0, 9, 3], TYOP [6], TYOP [5, 11], TYOP [5, 12], TYOP [5, 13],
   TYOP [4, 0, 14], TYOP [7, 11], TYOP [5, 16], TYOP [5, 17], TYOP [5, 18],
   TYOP [5, 19], TYOP [4, 0, 20], TYOP [0, 21, 15], TYOP [3, 22, 3],
   TYOP [0, 23, 22], TYOP [0, 24, 22], TYOP [0, 24, 25], TYOP [0, 3, 26],
   TYOP [0, 22, 27], TYOP [0, 0, 28], TYOP [8], TYOP [0, 30, 22], TYOP [9],
   TYOP [0, 21, 32], TYOP [0, 33, 31], TYOP [0, 22, 34], TYOP [0, 21, 35],
   TYOP [5, 14], TYOP [5, 37], TYOP [5, 38], TYOP [4, 0, 39],
   TYOP [0, 40, 36], TYOP [11], TYOP [3, 42, 21], TYOP [12],
   TYOP [3, 44, 43], TYOP [10, 45], TYOP [14], TYOP [13, 47],
   TYOP [0, 21, 48], TYOP [3, 49, 46], TYOP [0, 30, 50], TYOP [0, 42, 51],
   TYOP [0, 46, 52], TYOP [0, 33, 53], TYOP [0, 22, 54], TYOP [0, 21, 55],
   TYOP [0, 21, 56], TYOP [0, 30, 3], TYOP [4, 0, 5], TYOP [0, 59, 3],
   TYOP [0, 60, 58], TYOP [0, 21, 61], TYOP [0, 40, 62], TYOP [4, 0, 38],
   TYOP [0, 21, 64], TYOP [0, 3, 32], TYOP [0, 66, 65], TYOP [0, 21, 67],
   TYOP [0, 3, 68], TYOP [0, 21, 3], TYOP [3, 22, 70], TYOP [0, 71, 22],
   TYOP [10, 0], TYOP [0, 1, 42], TYOP [3, 40, 21], TYOP [0, 75, 3],
   TYOP [0, 76, 3], TYOP [15], TYOP [3, 78, 0], TYOP [3, 21, 79],
   TYOP [3, 40, 80], TYOP [0, 81, 3], TYOP [0, 82, 77], TYOP [3, 21, 0],
   TYOP [3, 40, 84], TYOP [0, 85, 3], TYOP [0, 86, 83], TYOP [0, 1, 87],
   TYOP [13, 21], TYOP [3, 89, 48], TYOP [13, 73], TYOP [3, 91, 90],
   TYOP [3, 22, 92], TYOP [3, 33, 93], TYOP [0, 1, 94], TYOP [0, 30, 95],
   TYOP [0, 33, 96], TYOP [0, 22, 97], TYOP [0, 30, 64], TYOP [0, 33, 99],
   TYOP [0, 21, 100], TYOP [0, 40, 101], TYOP [0, 30, 65],
   TYOP [0, 33, 103], TYOP [0, 21, 104], TYOP [0, 40, 105],
   TYOP [0, 66, 48], TYOP [0, 21, 107], TYOP [0, 3, 108], TYOP [0, 81, 1],
   TYOP [0, 1, 78], TYOP [0, 85, 1], TYOP [0, 75, 1], TYOP [0, 1, 75],
   TYOP [3, 81, 75], TYOP [3, 85, 115], TYOP [16, 116], TYOP [0, 117, 0],
   TYOP [0, 1, 2], TYOP [0, 113, 0], TYOP [0, 110, 120],
   TYOP [0, 112, 121], TYOP [0, 1, 3], TYOP [0, 1, 117], TYOP [0, 3, 0],
   TYOP [0, 125, 0], TYOP [0, 5, 0], TYOP [0, 127, 0], TYOP [0, 4, 0],
   TYOP [0, 129, 0], TYOP [0, 0, 0], TYOP [0, 131, 0], TYOP [0, 30, 0],
   TYOP [0, 133, 0], TYOP [0, 40, 0], TYOP [0, 135, 0], TYOP [0, 21, 0],
   TYOP [0, 137, 0], TYOP [0, 2, 0], TYOP [0, 66, 0], TYOP [0, 140, 0],
   TYOP [0, 60, 0], TYOP [0, 142, 0], TYOP [0, 70, 0], TYOP [0, 144, 0],
   TYOP [0, 33, 0], TYOP [0, 146, 0], TYOP [0, 22, 0], TYOP [0, 148, 0],
   TYOP [0, 139, 0], TYOP [0, 7, 0], TYOP [0, 151, 0], TYOP [0, 76, 0],
   TYOP [0, 153, 0], TYOP [0, 86, 0], TYOP [0, 155, 0], TYOP [0, 82, 0],
   TYOP [0, 157, 0], TYOP [0, 24, 0], TYOP [0, 159, 0], TYOP [0, 118, 0],
   TYOP [0, 161, 0], TYOP [0, 46, 0], TYOP [0, 163, 0], TYOP [0, 42, 0],
   TYOP [0, 165, 0], TYOP [0, 75, 0], TYOP [0, 167, 0], TYOP [0, 85, 0],
   TYOP [0, 169, 0], TYOP [0, 81, 0], TYOP [0, 171, 0], TYOP [0, 78, 0],
   TYOP [0, 173, 0], TYOP [0, 42, 42], TYOP [0, 42, 175], TYOP [0, 4, 6],
   TYOP [0, 5, 177], TYOP [0, 8, 9], TYOP [0, 5, 179], TYOP [0, 7, 8],
   TYOP [0, 4, 181], TYOP [0, 21, 75], TYOP [0, 40, 183], TYOP [0, 84, 85],
   TYOP [0, 40, 185], TYOP [3, 21, 33], TYOP [3, 40, 187],
   TYOP [0, 187, 188], TYOP [0, 40, 189], TYOP [3, 22, 33],
   TYOP [3, 21, 191], TYOP [3, 40, 192], TYOP [0, 192, 193],
   TYOP [0, 40, 194], TYOP [0, 80, 81], TYOP [0, 40, 196],
   TYOP [3, 78, 191], TYOP [3, 21, 198], TYOP [3, 40, 199],
   TYOP [0, 199, 200], TYOP [0, 40, 201], TYOP [0, 0, 84],
   TYOP [0, 21, 203], TYOP [0, 33, 187], TYOP [0, 21, 205],
   TYOP [3, 21, 187], TYOP [0, 187, 207], TYOP [0, 21, 208],
   TYOP [3, 33, 42], TYOP [3, 22, 210], TYOP [3, 21, 211],
   TYOP [3, 21, 212], TYOP [0, 212, 213], TYOP [0, 21, 214],
   TYOP [3, 42, 33], TYOP [3, 21, 216], TYOP [3, 21, 217],
   TYOP [0, 217, 218], TYOP [0, 21, 219], TYOP [3, 22, 47],
   TYOP [3, 42, 221], TYOP [3, 21, 222], TYOP [3, 21, 223],
   TYOP [0, 223, 224], TYOP [0, 21, 225], TYOP [0, 191, 192],
   TYOP [0, 21, 227], TYOP [0, 211, 212], TYOP [0, 21, 229],
   TYOP [0, 216, 217], TYOP [0, 21, 231], TYOP [0, 222, 223],
   TYOP [0, 21, 233], TYOP [0, 79, 80], TYOP [0, 21, 235],
   TYOP [0, 198, 199], TYOP [0, 21, 237], TYOP [0, 42, 210],
   TYOP [0, 33, 239], TYOP [0, 93, 94], TYOP [0, 33, 241], TYOP [0, 3, 23],
   TYOP [0, 22, 243], TYOP [0, 47, 221], TYOP [0, 22, 245],
   TYOP [0, 70, 71], TYOP [0, 22, 247], TYOP [0, 33, 191],
   TYOP [0, 22, 249], TYOP [0, 210, 211], TYOP [0, 22, 251],
   TYOP [0, 92, 93], TYOP [0, 22, 253], TYOP [3, 46, 187],
   TYOP [0, 187, 255], TYOP [0, 46, 256], TYOP [3, 46, 213],
   TYOP [0, 213, 258], TYOP [0, 46, 259], TYOP [0, 33, 216],
   TYOP [0, 42, 261], TYOP [0, 221, 222], TYOP [0, 42, 263],
   TYOP [0, 48, 90], TYOP [0, 89, 265], TYOP [0, 90, 92],
   TYOP [0, 91, 267], TYOP [0, 115, 116], TYOP [0, 85, 269],
   TYOP [0, 75, 115], TYOP [0, 81, 271], TYOP [0, 0, 79],
   TYOP [0, 78, 273], TYOP [0, 191, 198], TYOP [0, 78, 275],
   TYOP [0, 0, 131], TYOP [0, 3, 125], TYOP [0, 64, 0], TYOP [0, 64, 279],
   TYOP [0, 65, 0], TYOP [0, 65, 281], TYOP [0, 22, 148], TYOP [0, 2, 139],
   TYOP [0, 111, 0], TYOP [0, 111, 285], TYOP [0, 42, 165],
   TYOP [0, 48, 0], TYOP [0, 48, 288], TYOP [0, 89, 0], TYOP [0, 89, 290],
   TYOP [0, 75, 167], TYOP [0, 85, 169], TYOP [0, 81, 171],
   TYOP [0, 94, 0], TYOP [0, 94, 295], TYOP [0, 50, 0], TYOP [0, 50, 297],
   TYOP [0, 117, 118], TYOP [0, 78, 173], TYOP [0, 123, 0],
   TYOP [0, 301, 0], TYOP [0, 124, 0], TYOP [0, 303, 0], TYOP [0, 119, 0],
   TYOP [0, 305, 119], TYOP [0, 22, 22], TYOP [0, 22, 307],
   TYOP [0, 0, 308], TYOP [0, 94, 94], TYOP [0, 94, 310], TYOP [0, 0, 311],
   TYOP [0, 42, 117], TYOP [0, 313, 117], TYOP [0, 116, 314],
   TYOP [0, 42, 315], TYOP [0, 32, 46], TYOP [0, 32, 49], TYOP [3, 33, 22],
   TYOP [0, 30, 319], TYOP [0, 193, 320], TYOP [3, 22, 73],
   TYOP [3, 33, 322], TYOP [0, 30, 323], TYOP [0, 193, 324],
   TYOP [0, 200, 320], TYOP [0, 218, 64], TYOP [0, 255, 89],
   TYOP [0, 46, 45], TYOP [0, 188, 133], TYOP [0, 78, 78],
   TYOP [0, 22, 94], TYOP [0, 332, 332], TYOP [0, 22, 50],
   TYOP [0, 334, 334], TYOP [3, 21, 42], TYOP [3, 21, 336],
   TYOP [0, 337, 3], TYOP [0, 338, 338], TYOP [0, 337, 64],
   TYOP [0, 340, 340], TYOP [0, 337, 65], TYOP [0, 342, 342],
   TYOP [0, 337, 22], TYOP [0, 344, 344], TYOP [0, 337, 94],
   TYOP [0, 346, 346], TYOP [0, 319, 94], TYOP [0, 348, 348],
   TYOP [0, 323, 94], TYOP [0, 350, 350], TYOP [0, 43, 94],
   TYOP [0, 352, 352], TYOP [0, 207, 0], TYOP [0, 258, 51],
   TYOP [0, 47, 65], TYOP [0, 45, 43], TYOP [0, 21, 89], TYOP [0, 73, 91],
   TYOP [0, 48, 47], TYOP [0, 46, 46], TYOP [0, 118, 303],
   TYOP [0, 336, 3], TYOP [0, 42, 3], TYOP [0, 21, 364],
   TYOP [0, 365, 363], TYOP [0, 336, 64], TYOP [0, 42, 64],
   TYOP [0, 21, 368], TYOP [0, 369, 367], TYOP [0, 336, 65],
   TYOP [0, 42, 65], TYOP [0, 21, 372], TYOP [0, 373, 371],
   TYOP [0, 336, 22], TYOP [0, 42, 22], TYOP [0, 21, 376],
   TYOP [0, 377, 375], TYOP [0, 336, 94], TYOP [0, 42, 94],
   TYOP [0, 21, 380], TYOP [0, 381, 379], TYOP [0, 21, 363],
   TYOP [0, 383, 338], TYOP [0, 21, 367], TYOP [0, 385, 340],
   TYOP [0, 21, 371], TYOP [0, 387, 342], TYOP [0, 21, 375],
   TYOP [0, 389, 344], TYOP [0, 21, 379], TYOP [0, 391, 346],
   TYOP [0, 33, 332], TYOP [0, 393, 348], TYOP [0, 322, 94],
   TYOP [0, 33, 395], TYOP [0, 396, 350], TYOP [0, 73, 94],
   TYOP [0, 22, 398], TYOP [0, 399, 395], TYOP [0, 21, 94],
   TYOP [0, 42, 401], TYOP [0, 402, 352], TYOP [0, 2, 2], TYOP [0, 404, 2],
   TYOP [0, 119, 405], TYOP [0, 111, 111], TYOP [0, 407, 111],
   TYOP [0, 119, 408], TYOP [0, 224, 31], TYOP [0, 0, 42],
   TYOP [0, 33, 48], TYOP [0, 21, 412], TYOP [0, 21, 413],
   TYOP [0, 171, 168], TYOP [0, 169, 415], TYOP [0, 1, 416],
   TYOP [0, 75, 75], TYOP [0, 418, 75], TYOP [0, 81, 75],
   TYOP [0, 420, 419], TYOP [0, 85, 75], TYOP [0, 422, 421],
   TYOP [0, 1, 423], TYOP [0, 75, 94], TYOP [0, 425, 94], TYOP [0, 81, 94],
   TYOP [0, 427, 426], TYOP [0, 85, 94], TYOP [0, 429, 428],
   TYOP [0, 1, 430], TYOP [0, 75, 78], TYOP [0, 432, 78], TYOP [0, 81, 78],
   TYOP [0, 434, 433], TYOP [0, 85, 78], TYOP [0, 436, 435],
   TYOP [0, 1, 437], TYOP [0, 191, 22], TYOP [0, 30, 337],
   TYOP [0, 75, 440], TYOP [0, 439, 22], TYOP [0, 439, 442],
   TYOP [0, 33, 443], TYOP [0, 22, 444], TYOP [0, 0, 445],
   TYOP [0, 42, 59], TYOP [0, 42, 21], TYOP [0, 184, 75],
   TYOP [0, 75, 449], TYOP [0, 40, 401], TYOP [0, 451, 94],
   TYOP [0, 75, 452], TYOP [0, 84, 75], TYOP [0, 40, 454],
   TYOP [0, 455, 75], TYOP [0, 85, 456], TYOP [0, 84, 94],
   TYOP [0, 40, 458], TYOP [0, 459, 94], TYOP [0, 85, 460],
   TYOP [0, 80, 75], TYOP [0, 40, 462], TYOP [0, 463, 75],
   TYOP [0, 81, 464], TYOP [0, 80, 94], TYOP [0, 40, 466],
   TYOP [0, 467, 94], TYOP [0, 81, 468], TYOP [0, 80, 78],
   TYOP [0, 40, 470], TYOP [0, 471, 78], TYOP [0, 81, 472],
   TYOP [0, 0, 75], TYOP [0, 21, 474], TYOP [0, 475, 75],
   TYOP [0, 84, 476], TYOP [0, 0, 94], TYOP [0, 21, 478],
   TYOP [0, 479, 94], TYOP [0, 84, 480], TYOP [0, 79, 75],
   TYOP [0, 21, 482], TYOP [0, 483, 75], TYOP [0, 80, 484],
   TYOP [0, 79, 94], TYOP [0, 21, 486], TYOP [0, 487, 94],
   TYOP [0, 80, 488], TYOP [0, 79, 78], TYOP [0, 21, 490],
   TYOP [0, 491, 78], TYOP [0, 80, 492], TYOP [0, 78, 478],
   TYOP [0, 494, 94], TYOP [0, 79, 495], TYOP [0, 0, 78],
   TYOP [0, 78, 497], TYOP [0, 498, 78], TYOP [0, 79, 499],
   TYOP [0, 75, 42], TYOP [0, 21, 42], TYOP [0, 502, 501],
   TYOP [0, 40, 42], TYOP [0, 504, 503], TYOP [0, 85, 42],
   TYOP [0, 84, 42], TYOP [0, 507, 506], TYOP [0, 504, 508],
   TYOP [0, 81, 42], TYOP [0, 80, 42], TYOP [0, 511, 510],
   TYOP [0, 504, 512], TYOP [0, 411, 507], TYOP [0, 502, 514],
   TYOP [0, 79, 42], TYOP [0, 516, 511], TYOP [0, 502, 517],
   TYOP [0, 411, 516], TYOP [0, 78, 42], TYOP [0, 520, 519]]
  end
  val _ = Theory.incorporate_consts "cacheIf" tyvector
     [("wt", 2), ("read32", 10), ("rd", 2), ("mv", 29), ("mlwb", 41),
      ("mllu", 57), ("lw", 63), ("lv", 57), ("lcnt", 69), ("fmem", 72),
      ("fcm", 72), ("dummy3", 48), ("dummy2", 21), ("dummy1", 73),
      ("dop_size", 74), ("dop_CASE", 88), ("dc2", 70), ("ctf", 98),
      ("cl", 2), ("ccntw", 102), ("ccnt", 106), ("ca", 109), ("WT", 110),
      ("VAL", 111), ("RD", 112), ("CL", 113), ("ADD", 114)];

  local open SharingTables
  in
  val tmvector = build_term_vector idvector tyvector
  [TMV("'dop'", 118), TMV("M", 1), TMV("M'", 1), TMV("P", 2),
   TMV("R", 119), TMV("VAL", 111), TMV("_", 42), TMV("a", 1), TMV("a", 75),
   TMV("a", 85), TMV("a", 81), TMV("a'", 75), TMV("a'", 85), TMV("a'", 81),
   TMV("a0", 117), TMV("c", 0), TMV("c", 73), TMV("c'", 0),
   TMV("cache", 33), TMV("cbl", 0), TMV("cl", 2), TMV("d", 1),
   TMV("data", 78), TMV("dc", 3), TMV("dc", 66), TMV("dc", 70),
   TMV("dc", 33), TMV("dd", 1), TMV("dop", 1), TMV("dop", 122),
   TMV("f", 4), TMV("f", 22), TMV("f", 86), TMV("f", 24), TMV("f'", 86),
   TMV("f0", 86), TMV("f1", 82), TMV("f1'", 82), TMV("f2", 76),
   TMV("f2'", 76), TMV("fn", 123), TMV("g", 7), TMV("g", 24), TMV("h", 46),
   TMV("i", 3), TMV("i", 21), TMV("il", 21), TMV("l", 60), TMV("mem", 22),
   TMV("n", 42), TMV("p", 75), TMV("p", 85), TMV("p", 81), TMV("pa", 5),
   TMV("pa", 21), TMV("pa'", 21), TMV("pa''", 21), TMV("pm", 22),
   TMV("rd", 2), TMV("rep", 124), TMV("state", 30), TMV("t", 21),
   TMV("tg", 42), TMV("v", 40), TMV("v", 21), TMV("v", 1), TMV("v", 85),
   TMV("v1", 85), TMV("v1", 81), TMV("v10", 79), TMV("v2", 75),
   TMV("v2", 81), TMV("v3", 75), TMV("v3", 85), TMV("v4", 75),
   TMV("v4", 81), TMV("v4", 84), TMV("v5", 75), TMV("v6", 80),
   TMV("v8", 80), TMV("v8", 79), TMV("va", 40), TMV("va'", 40),
   TMV("va''", 40), TMV("w", 78), TMV("wi", 42), TMV("wt", 2),
   TMC(17, 126), TMC(17, 128), TMC(17, 130), TMC(17, 132), TMC(17, 134),
   TMC(17, 136), TMC(17, 138), TMC(17, 139), TMC(17, 141), TMC(17, 143),
   TMC(17, 145), TMC(17, 147), TMC(17, 149), TMC(17, 150), TMC(17, 152),
   TMC(17, 154), TMC(17, 156), TMC(17, 158), TMC(17, 160), TMC(17, 162),
   TMC(17, 164), TMC(17, 166), TMC(17, 168), TMC(17, 170), TMC(17, 172),
   TMC(17, 161), TMC(17, 174), TMC(18, 176), TMC(19, 178), TMC(19, 180),
   TMC(19, 182), TMC(19, 184), TMC(19, 186), TMC(19, 190), TMC(19, 195),
   TMC(19, 197), TMC(19, 202), TMC(19, 204), TMC(19, 206), TMC(19, 209),
   TMC(19, 215), TMC(19, 220), TMC(19, 226), TMC(19, 228), TMC(19, 230),
   TMC(19, 232), TMC(19, 234), TMC(19, 236), TMC(19, 238), TMC(19, 240),
   TMC(19, 242), TMC(19, 244), TMC(19, 246), TMC(19, 248), TMC(19, 250),
   TMC(19, 252), TMC(19, 254), TMC(19, 257), TMC(19, 260), TMC(19, 262),
   TMC(19, 264), TMC(19, 266), TMC(19, 268), TMC(19, 270), TMC(19, 272),
   TMC(19, 274), TMC(19, 276), TMC(20, 277), TMC(21, 42), TMC(22, 278),
   TMC(22, 277), TMC(22, 280), TMC(22, 119), TMC(22, 282), TMC(22, 283),
   TMC(22, 284), TMC(22, 286), TMC(22, 287), TMC(22, 289), TMC(22, 291),
   TMC(22, 292), TMC(22, 293), TMC(22, 294), TMC(22, 296), TMC(22, 298),
   TMC(22, 299), TMC(22, 300), TMC(23, 277), TMC(24, 302), TMC(24, 304),
   TMC(24, 168), TMC(24, 170), TMC(24, 172), TMC(25, 306), TMC(26, 114),
   TMC(27, 75), TMC(27, 85), TMC(27, 81), TMC(27, 78), TMC(28, 175),
   TMC(29, 117), TMC(30, 113), TMC(31, 309), TMC(31, 312), TMC(32, 316),
   TMC(33, 317), TMC(34, 318), TMC(35, 321), TMC(36, 325), TMC(37, 326),
   TMC(38, 327), TMC(39, 131), TMC(40, 328), TMC(41, 0), TMC(42, 329),
   TMC(43, 330), TMC(44, 131), TMC(44, 331), TMC(45, 333), TMC(45, 335),
   TMC(45, 339), TMC(45, 341), TMC(45, 343), TMC(45, 345), TMC(45, 347),
   TMC(45, 349), TMC(45, 351), TMC(45, 353), TMC(46, 354), TMC(47, 355),
   TMC(48, 48), TMC(48, 89), TMC(48, 91), TMC(49, 175), TMC(50, 112),
   TMC(51, 356), TMC(52, 357), TMC(53, 358), TMC(53, 359), TMC(54, 175),
   TMC(55, 0), TMC(56, 360), TMC(57, 361), TMC(58, 362), TMC(59, 366),
   TMC(59, 370), TMC(59, 374), TMC(59, 378), TMC(59, 382), TMC(59, 384),
   TMC(59, 386), TMC(59, 388), TMC(59, 390), TMC(59, 392), TMC(59, 394),
   TMC(59, 397), TMC(59, 400), TMC(59, 403), TMC(60, 111), TMC(61, 305),
   TMC(62, 406), TMC(62, 409), TMC(63, 110), TMC(64, 410), TMC(65, 42),
   TMC(66, 277), TMC(67, 411), TMC(68, 109), TMC(68, 414), TMC(69, 106),
   TMC(70, 102), TMC(71, 2), TMC(72, 98), TMC(73, 33), TMC(74, 88),
   TMC(74, 417), TMC(74, 424), TMC(74, 431), TMC(74, 438), TMC(75, 74),
   TMC(76, 439), TMC(77, 72), TMC(77, 439), TMC(78, 69), TMC(79, 441),
   TMC(80, 57), TMC(81, 63), TMC(82, 57), TMC(83, 41), TMC(84, 29),
   TMC(84, 446), TMC(85, 447), TMC(85, 448), TMC(86, 450), TMC(86, 453),
   TMC(86, 457), TMC(86, 461), TMC(86, 465), TMC(86, 469), TMC(86, 473),
   TMC(86, 477), TMC(86, 481), TMC(86, 485), TMC(86, 489), TMC(86, 493),
   TMC(86, 496), TMC(86, 500), TMC(87, 505), TMC(87, 509), TMC(87, 513),
   TMC(87, 515), TMC(87, 518), TMC(87, 521), TMC(88, 2), TMC(89, 10),
   TMC(90, 520), TMC(91, 2), TMC(92, 131)]
  end
  local
  val DT = Thm.disk_thm val read = Term.read_raw tmvector
  in
  fun op ca_def x = x
    val op ca_def =
    DT(((("cacheIf",0),[]),[]),
       [read"%87%44%93%61%95%24%165%254$2@$1@$0@@%193$0$2@@$1@@|@|@|@"])
  fun op ccnt_def x = x
    val op ccnt_def =
    DT(((("cacheIf",1),[]),[]),
       [read"%92%81%93%54%98%26%91%60%160%256$3@$2@$1@$0@@%209%238%45%233%61%85%222%228%193$4$2@@$1@@@||@|@@%271%118$3@$2@@$0@@@|@|@|@|@"])
  fun op lcnt_def x = x
    val op lcnt_def =
    DT(((("cacheIf",2),[]),[]),
       [read"%87%44%93%61%95%24%160%270$2@$1@$0@@%222%228%193$0$2@@$1@@@@|@|@|@"])
  fun op ccntw_def x = x
    val op ccntw_def =
    DT(((("cacheIf",3),[]),[]),
       [read"%92%81%93%54%98%26%91%60%158%257$3@$2@$1@$0@@%208%237%45%232%61%85%197%128$2@%132$1@%146$0@$4@@@@||@|@@%271%118$3@$2@@$0@@@|@|@|@|@"])
  fun op mllu_def x = x
    val op mllu_def =
    DT(((("cacheIf",4),[]),[]),
       [read"%93%45%93%61%99%57%98%26%107%43%108%49%91%60%171%274$6@$5@$4@$3@$2@$1@$0@@%216%145$2@%127$6@%131$5@%142$4@%136$3@$1@@@@@@$0@@|@|@|@|@|@|@|@"])
  fun op mlwb_def x = x
    val op mlwb_def =
    DT(((("cacheIf",5),[]),[]),
       [read"%92%81%93%54%99%57%98%26%91%60%161%275$4@$3@$2@$1@$0@@%210%239%45%234%61%85%250%129$2@%133$1@%147$0@%139$5@%228%193$4$2@@$1@@@@@@@$3@||@|@@%271%118$4@$3@@$0@@@|@|@|@|@|@"])
  fun op fmem_def x = x
    val op fmem_def =
    DT(((("cacheIf",6),[("pair",[16])]),["DISK_THM"]),
       [read"%99%57%97%25%161%268%140$1@$0@@@$1@|@|@"])
  fun op mv_def x = x
    val op mv_def =
    DT(((("cacheIf",7),[]),[]),
       [read"%90%19%99%57%87%23%105%33%105%42%161%276$4@$3@$2@$1@$0@@%189$4@$1%138$3@$2@@@$0%138$3@$2@@@@|@|@|@|@|@"])
  fun op read32_def x = x
    val op read32_def =
    DT(((("cacheIf",8),[("pair",[16])]),["DISK_THM"]),
       [read"%88%53%89%30%101%41%156%301%116$2@%117$1@$0@@@@$0%115$2@$1@@@|@|@|@"])
  fun op lv_def x = x
    val op lv_def =
    DT(((("cacheIf",9),[]),[]),
       [read"%93%45%93%61%99%57%98%26%107%43%108%49%91%60%171%272$6@$5@$4@$3@$2@$1@$0@@%206%31%216%145$3@%127$7@%131$6@%142$0@%136$4@$2@@@@@@$1@|@%277%227@$4@%260@%269@%267@@@|@|@|@|@|@|@|@"])
  fun op lw_def x = x
    val op lw_def =
    DT(((("cacheIf",10),[]),[]),
       [read"%92%81%93%54%96%47%91%60%156%273$3@$2@$1@$0@@%207%236%45%231%61%85$4%278$0@@||@|@@%271%118$3@$2@@$0@@@|@|@|@|@"])
  fun op dop_TY_DEF x = x
    val op dop_TY_DEF =
    DT(((("cacheIf",11),[("bool",[26])]),["DISK_THM"]),
       [read"%176%59%230%14%106%0%174%112%14%174%252%178%9%172$1@%9%191%155@%150$0@%151%184@%182@@@%49%187|@|$0@@|@@%252%179%10%172$1@%10%191%226%155@@%150%183@%151$0@%182@@@%49%187|@|$0@@|@@%177%8%172$1@%8%191%226%226%155@@@%150%183@%151%184@$0@@@%49%187|@|$0@@|@@@@$1$0@@|@@$0$1@@|@|@$0@|@"])
  fun op dop_case_def x = x
    val op dop_case_def =
    DT(((("cacheIf",19),
        [("bool",[26,180]),("cacheIf",[12,13,14,15,16,17,18]),
         ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
       [read"%154%110%9%103%32%104%36%102%38%156%261%221$3@@$2@$1@$0@@$2$3@@|@|@|@|@@%154%111%10%103%32%104%36%102%38%156%261%249$3@@$2@$1@$0@@$1$3@@|@|@|@|@@%109%8%103%32%104%36%102%38%156%261%188$3@@$2@$1@$0@@$0$3@@|@|@|@|@@@"])
  fun op dop_size_def x = x
    val op dop_size_def =
    DT(((("cacheIf",20),
        [("bool",[26,180]),("cacheIf",[12,13,14,15,16,17,18]),
         ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
       [read"%154%110%9%164%266%221$0@@@%114%220%186%251@@@%295%63%155|@%297%64%155|@%253@@$0@@@|@@%154%111%10%164%266%249$0@@@%114%220%186%251@@@%296%63%155|@%298%64%155|@%299%302@%253@@@$0@@@|@@%109%8%164%266%188$0@@@%114%220%186%251@@@%294%63%155|@%64%155|@$0@@@|@@@"])
  fun op rd_primitive_def x = x
    val op rd_primitive_def =
    DT(((("cacheIf",28),[]),[]),
       [read"%162%300@%247%180%4%246$0@|@@%58%7%262$0@%73%203%227@|@%75%203%200@|@%77%203%200@|@||@@"])
  fun op wt_primitive_def x = x
    val op wt_primitive_def =
    DT(((("cacheIf",31),[]),[]),
       [read"%162%303@%247%180%4%246$0@|@@%86%7%262$0@%73%203%200@|@%75%203%227@|@%77%203%200@|@||@@"])
  fun op cl_primitive_def x = x
    val op cl_primitive_def =
    DT(((("cacheIf",34),[]),[]),
       [read"%162%258@%247%180%4%246$0@|@@%20%7%262$0@%73%203%200@|@%75%203%200@|@%77%203%227@|@||@@"])
  fun op ADD_def x = x
    val op ADD_def =
    DT(((("cacheIf",37),[]),[]),
       [read"%94%28%167%181$0@@%263$0@%66%282$0@%81%76%287$0@%54%15%118$3@$1@||@||@|@%68%284$0@%82%79%289$0@%55%69%118$3@$1@||@||@|@%70%280$0@%83%56%118$1@$0@||@|@@|@"])
  fun op VAL_primitive_def x = x
    val op VAL_primitive_def =
    DT(((("cacheIf",38),[]),[]),
       [read"%163%245@%248%180%4%246$0@|@@%5%7%265$0@%66%185|@%71%286$0@%81%78%291$0@%54%80%293$0@%84%15%204$1@||@||@||@|@%72%185|@||@@"])
  fun op ctf_def x = x
    val op ctf_def =
    DT(((("cacheIf",41),[]),[]),
       [read"%99%57%98%26%91%60%94%28%170%259$3@$2@$1@$0@@%205%31%264$1@%66%283$0@%83%76%288$0@%56%17%211%240%45%235%61%6%213%242%18%243%48%16%214%244%62%46%190%154%304%202%120$11@%125$9@$16@@@$15@@@%304%166%199%144%192$16$7@@@%125$6@$16@@@@%218@@@@%190%215%126$0@%125%279$1@@$16@@@@%137$4@%143$3@%149%225$2@@%148%224%279$1@@@%255$0@%279$1@@$16@@@@@@%137$4@%143$3@%149%225$2@@%148%218@%217@@@@@@%137$4@%143$3@%149%225$2@@%148%218@%217@@@@@||@@%223%201%229%229%192$2$5@@@@@@@||@|@@%195%121$6@%130$4@%141$8@$11@@@@$10@@||@|@@%271%118$3@$1@@$7@@||@||@|@%68%285$0@%82%79%290$0@%55%69%292$0@%22%15%211%240%45%235%61%6%212%241%18%48%214%244%62%46%190%154%304%202%120$12@%125$10@$17@@@$16@@@%304%166%199%144%192$17$6@@@%125$5@$17@@@@%218@@@@%190%215%126$0@%125%279$1@@$17@@@@%137$3@%143$2@%149%219@%148%224%279$1@@@%255$0@%279$1@@$17@@@@@@%137$3@%143$2@%149%219@%148%218@%217@@@@@@%137$3@%143$2@%149%219@%148%218@%217@@@@@||@@%223%201%229%229%192$1$4@@@@@@@||@@%196%123$8@%135$6@%153$4@%141$10@$13@@@@@$12@@||@|@@%271%118$5@$3@@$9@@||@||@||@|@%70%281$0@%81%54%211%240%45%235%61%6%212%241%18%48%214%244%62%46%190%215%126$0@%125%279$1@@$13@@@@%137$3@%143$2@%149%219@%148%224%279$1@@@%255$0@%279$1@@$13@@@@@@%137$3@%143$2@%149%219@%148%218@%217@@@@@||@@%223%201%192$1$4@@@@@||@@%194%121$4@%130$3@%141$6@$9@@@@$8@@||@|@@%271%118$1@$0@@$5@@||@|@|@%277%227@$3@%260@%269@%267@@@|@|@|@|@"])
  fun op datatype_dop x = x
    val op datatype_dop =
    DT(((("cacheIf",21),[("bool",[25,170])]),["DISK_THM"]),
       [read"%198%29%221@%249@%188@@"])
  fun op dop_11 x = x
    val op dop_11 =
    DT(((("cacheIf",22),
        [("bool",[26,55,62,180]),("cacheIf",[12,13,14,15,16,17,18]),
         ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
       [read"%154%110%9%110%12%157%159%221$1@@%221$0@@@%168$1@$0@@|@|@@%154%111%10%111%13%157%159%249$1@@%249$0@@@%169$1@$0@@|@|@@%109%8%109%11%157%159%188$1@@%188$0@@@%167$1@$0@@|@|@@@"])
  fun op dop_distinct x = x
    val op dop_distinct =
    DT(((("cacheIf",23),
        [("bool",[25,26,35,46,50,53,55,62,180]),
         ("cacheIf",[12,13,14,15,16,17,18]),("ind_type",[33,34]),
         ("pair",[8,9])]),["DISK_THM"]),
       [read"%154%111%13%110%9%304%159%221$0@@%249$1@@@|@|@@%154%109%11%110%9%304%159%221$0@@%188$1@@@|@|@@%109%11%111%10%304%159%249$0@@%188$1@@@|@|@@@"])
  fun op dop_case_cong x = x
    val op dop_case_cong =
    DT(((("cacheIf",24),
        [("bool",[26,180]),
         ("cacheIf",[12,13,14,15,16,17,18,19])]),["DISK_THM"]),
       [read"%94%1%94%2%103%32%104%36%102%38%174%154%159$4@$3@@%154%110%9%174%159$4@%221$0@@@%156$3$0@@%34$0@@@|@@%154%111%10%174%159$4@%249$0@@@%156$2$0@@%37$0@@@|@@%109%8%174%159$4@%188$0@@@%156$1$0@@%39$0@@@|@@@@@%156%261$4@$2@$1@$0@@%261$3@%34@%37@%39@@@|@|@|@|@|@"])
  fun op dop_nchotomy x = x
    val op dop_nchotomy =
    DT(((("cacheIf",25),
        [("bool",[26,180]),
         ("cacheIf",[12,13,14,15,16,17,18])]),["DISK_THM"]),
       [read"%94%27%252%178%51%159$1@%221$0@@|@@%252%179%52%159$1@%249$0@@|@@%177%50%159$1@%188$0@@|@@@|@"])
  fun op dop_Axiom x = x
    val op dop_Axiom =
    DT(((("cacheIf",26),
        [("bool",[26,180]),("cacheIf",[12,13,14,15,16,17,18]),
         ("ind_type",[33,34]),("pair",[8,9])]),["DISK_THM"]),
       [read"%103%35%104%36%102%38%175%40%154%110%9%156$1%221$0@@@$4$0@@|@@%154%111%10%156$1%249$0@@@$3$0@@|@@%109%8%156$1%188$0@@@$2$0@@|@@@|@|@|@|@"])
  fun op dop_induction x = x
    val op dop_induction =
    DT(((("cacheIf",27),
        [("bool",[26]),("cacheIf",[12,13,14,15,16,17,18])]),["DISK_THM"]),
       [read"%100%3%174%154%110%51$1%221$0@@|@@%154%111%52$1%249$0@@|@@%109%50$1%188$0@@|@@@@%94%21$1$0@|@@|@"])
  fun op rd_ind x = x
    val op rd_ind =
    DT(((("cacheIf",29),
        [("bool",[25,26,27,52,53,62,180]),
         ("cacheIf",[12,13,14,15,16,17,18]),("pair",[5]),
         ("relation",[101,107]),("sat",[1,3,5,6,7,11,15])]),["DISK_THM"]),
       [read"%100%3%174%154%92%81%93%54%90%15$3%221%119$2@%124$1@$0@@@@|@|@|@@%154%111%68$1%249$0@@|@@%109%70$1%188$0@@|@@@@%94%65$1$0@|@@|@"])
  fun op rd_def x = x
    val op rd_def =
    DT(((("cacheIf",30),
        [("bool",[15]),("cacheIf",[19,28]),("combin",[19]),
         ("relation",[107,126])]),["DISK_THM"]),
       [read"%154%157%300%221%119%81@%124%54@%15@@@@@%227@@%154%157%300%249%68@@@%200@@%157%300%188%70@@@%200@@@"])
  fun op wt_ind x = x
    val op wt_ind =
    DT(((("cacheIf",32),
        [("bool",[25,26,46,47,52,53,57,62,71,76,77,79,180]),
         ("cacheIf",[12,13,14,15,16,17,18]),("pair",[5]),
         ("relation",[101,107]),
         ("sat",[1,3,5,6,7,11,12,13,14,15])]),["DISK_THM"]),
       [read"%100%3%174%154%92%81%93%54%113%84%90%15$4%249%122$3@%134$2@%152$1@$0@@@@@|@|@|@|@@%154%110%66$1%221$0@@|@@%109%70$1%188$0@@|@@@@%94%65$1$0@|@@|@"])
  fun op wt_def x = x
    val op wt_def =
    DT(((("cacheIf",33),
        [("bool",[15]),("cacheIf",[19,31]),("combin",[19]),
         ("relation",[107,126])]),["DISK_THM"]),
       [read"%154%157%303%249%122%81@%134%54@%152%84@%15@@@@@@%227@@%154%157%303%221%66@@@%200@@%157%303%188%70@@@%200@@@"])
  fun op cl_ind x = x
    val op cl_ind =
    DT(((("cacheIf",35),
        [("bool",[25,26,46,47,52,53,57,62,71,76,77,79,180]),
         ("cacheIf",[12,13,14,15,16,17,18]),("pair",[5]),
         ("relation",[101,107]),
         ("sat",[1,3,5,6,7,11,12,13,14,15])]),["DISK_THM"]),
       [read"%100%3%174%154%92%81%93%54$2%188%118$1@$0@@@|@|@@%154%110%66$1%221$0@@|@@%111%68$1%249$0@@|@@@@%94%65$1$0@|@@|@"])
  fun op cl_def x = x
    val op cl_def =
    DT(((("cacheIf",36),
        [("bool",[15]),("cacheIf",[19,34]),("combin",[19]),
         ("relation",[107,126])]),["DISK_THM"]),
       [read"%154%157%258%188%118%81@%54@@@@%227@@%154%157%258%221%66@@@%200@@%157%258%249%68@@@%200@@@"])
  fun op VAL_ind x = x
    val op VAL_ind =
    DT(((("cacheIf",39),
        [("bool",[25,26,46,47,52,53,57,62,71,76,77,79,180]),
         ("cacheIf",[12,13,14,15,16,17,18]),("pair",[5]),
         ("relation",[101,107]),
         ("sat",[1,3,5,6,7,11,12,13,14,15])]),["DISK_THM"]),
       [read"%100%3%174%154%92%81%93%54%113%84%90%15$4%249%122$3@%134$2@%152$1@$0@@@@@|@|@|@|@@%154%110%67$1%221$0@@|@@%109%74$1%188$0@@|@@@@%94%65$1$0@|@@|@"])
  fun op VAL_def x = x
    val op VAL_def =
    DT(((("cacheIf",40),
        [("bool",[15]),("cacheIf",[19,38]),("combin",[19]),("pair",[49]),
         ("relation",[107,126])]),["DISK_THM"]),
       [read"%173%245%249%122%81@%134%54@%152%84@%15@@@@@@%84@"])
  end
  val _ = DB.bindl "cacheIf"
  [("ca_def",ca_def,DB.Def), ("ccnt_def",ccnt_def,DB.Def),
   ("lcnt_def",lcnt_def,DB.Def), ("ccntw_def",ccntw_def,DB.Def),
   ("mllu_def",mllu_def,DB.Def), ("mlwb_def",mlwb_def,DB.Def),
   ("fmem_def",fmem_def,DB.Def), ("mv_def",mv_def,DB.Def),
   ("read32_def",read32_def,DB.Def), ("lv_def",lv_def,DB.Def),
   ("lw_def",lw_def,DB.Def), ("dop_TY_DEF",dop_TY_DEF,DB.Def),
   ("dop_case_def",dop_case_def,DB.Def),
   ("dop_size_def",dop_size_def,DB.Def),
   ("rd_primitive_def",rd_primitive_def,DB.Def),
   ("wt_primitive_def",wt_primitive_def,DB.Def),
   ("cl_primitive_def",cl_primitive_def,DB.Def),
   ("ADD_def",ADD_def,DB.Def),
   ("VAL_primitive_def",VAL_primitive_def,DB.Def),
   ("ctf_def",ctf_def,DB.Def), ("datatype_dop",datatype_dop,DB.Thm),
   ("dop_11",dop_11,DB.Thm), ("dop_distinct",dop_distinct,DB.Thm),
   ("dop_case_cong",dop_case_cong,DB.Thm),
   ("dop_nchotomy",dop_nchotomy,DB.Thm), ("dop_Axiom",dop_Axiom,DB.Thm),
   ("dop_induction",dop_induction,DB.Thm), ("rd_ind",rd_ind,DB.Thm),
   ("rd_def",rd_def,DB.Thm), ("wt_ind",wt_ind,DB.Thm),
   ("wt_def",wt_def,DB.Thm), ("cl_ind",cl_ind,DB.Thm),
   ("cl_def",cl_def,DB.Thm), ("VAL_ind",VAL_ind,DB.Thm),
   ("VAL_def",VAL_def,DB.Thm)]

  local open GrammarSpecials Parse
    fun UTOFF f = Feedback.trace("Parse.unicode_trace_off_complaints",0)f
  in
  val _ = mk_local_grms [("blastTheory.blast_grammars",
                          blastTheory.blast_grammars),
                         ("cacheTheory.cache_grammars",
                          cacheTheory.cache_grammars)]
  val _ = List.app (update_grms reveal) []
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("ca", (Term.prim_mk_const { Name = "ca", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("ca", (Term.prim_mk_const { Name = "ca", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("ccnt", (Term.prim_mk_const { Name = "ccnt", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("ccnt", (Term.prim_mk_const { Name = "ccnt", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("lcnt", (Term.prim_mk_const { Name = "lcnt", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("lcnt", (Term.prim_mk_const { Name = "lcnt", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("ccntw", (Term.prim_mk_const { Name = "ccntw", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("ccntw", (Term.prim_mk_const { Name = "ccntw", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("mllu", (Term.prim_mk_const { Name = "mllu", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("mllu", (Term.prim_mk_const { Name = "mllu", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("mlwb", (Term.prim_mk_const { Name = "mlwb", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("mlwb", (Term.prim_mk_const { Name = "mlwb", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("fmem", (Term.prim_mk_const { Name = "fmem", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("fmem", (Term.prim_mk_const { Name = "fmem", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("fcm", (Term.prim_mk_const { Name = "fcm", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("dc2", (Term.prim_mk_const { Name = "dc2", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("mv", (Term.prim_mk_const { Name = "mv", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("mv", (Term.prim_mk_const { Name = "mv", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("read32", (Term.prim_mk_const { Name = "read32", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("read32", (Term.prim_mk_const { Name = "read32", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("lv", (Term.prim_mk_const { Name = "lv", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("lv", (Term.prim_mk_const { Name = "lv", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("lw", (Term.prim_mk_const { Name = "lw", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("lw", (Term.prim_mk_const { Name = "lw", Thy = "cacheIf"}))
  val _ = update_grms temp_add_type "dop"
  val _ = update_grms temp_add_type "dop"








  val _ = update_grms
       (UTOFF temp_overload_on)
       ("RD", (Term.prim_mk_const { Name = "RD", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("RD", (Term.prim_mk_const { Name = "RD", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("WT", (Term.prim_mk_const { Name = "WT", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("WT", (Term.prim_mk_const { Name = "WT", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("CL", (Term.prim_mk_const { Name = "CL", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("CL", (Term.prim_mk_const { Name = "CL", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("dop_CASE", (Term.prim_mk_const { Name = "dop_CASE", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("dop_size", (Term.prim_mk_const { Name = "dop_size", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("rd", (Term.prim_mk_const { Name = "rd", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("rd", (Term.prim_mk_const { Name = "rd", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("wt", (Term.prim_mk_const { Name = "wt", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("wt", (Term.prim_mk_const { Name = "wt", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("cl", (Term.prim_mk_const { Name = "cl", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("cl", (Term.prim_mk_const { Name = "cl", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("ADD", (Term.prim_mk_const { Name = "ADD", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("ADD", (Term.prim_mk_const { Name = "ADD", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("VAL", (Term.prim_mk_const { Name = "VAL", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("VAL", (Term.prim_mk_const { Name = "VAL", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("dummy1", (Term.prim_mk_const { Name = "dummy1", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("dummy2", (Term.prim_mk_const { Name = "dummy2", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("dummy3", (Term.prim_mk_const { Name = "dummy3", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("ctf", (Term.prim_mk_const { Name = "ctf", Thy = "cacheIf"}))
  val _ = update_grms
       (UTOFF temp_overload_on)
       ("ctf", (Term.prim_mk_const { Name = "ctf", Thy = "cacheIf"}))
  val cacheIf_grammars = Parse.current_lgrms()
  end


  val _ =
    TypeBase.write [
      let
        open TypeBasePure
        val tyinfo0 = mk_datatype_info
          {ax=ORIG dop_Axiom,
           case_def=dop_case_def,
           case_cong=dop_case_cong,
           induction=ORIG dop_induction,
           nchotomy=dop_nchotomy,
           size=SOME(Parse.Term`(cacheIf$dop_size) :(cacheIf$dop) -> (num$num)`,
                     ORIG dop_size_def),
           encode = NONE,
           lift=NONE,
           one_one=SOME dop_11,
           distinct=SOME dop_distinct,
           fields=let fun T t s A = mk_thy_type{Thy=t,Tyop=s,Args=A}
    val U = mk_vartype
in
[] end,
           accessors=[],
           updates=[],
           recognizers=[],
           destructors=[]}
        val tyinfo0 = tyinfo0
        val () = computeLib.write_datatype_info tyinfo0
      in
        tyinfo0
      end
    ];
  val _ = Theory.LoadableThyData.temp_encoded_update {
    thy = "cacheIf",
    thydataty = "compute",
    data =
        "cacheIf.ca_def cacheIf.wt_def cacheIf.ctf_def cacheIf.VAL_def cacheIf.ADD_def cacheIf.cl_def cacheIf.mv_def cacheIf.rd_def cacheIf.lw_def cacheIf.lv_def cacheIf.read32_def cacheIf.mllu_def cacheIf.fmem_def cacheIf.mlwb_def cacheIf.ccnt_def cacheIf.ccntw_def cacheIf.lcnt_def"
  }

val _ = if !Globals.print_thy_loads then print "done\n" else ()
val _ = Theory.load_complete "cacheIf"
end
