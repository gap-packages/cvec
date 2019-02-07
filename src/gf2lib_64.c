/* This file includes gf2lib.def more than once with different parameters. */
/* This is for 64bit machines. */

/* Here come the global definitions: */
typedef uint64_t WORD;
#define PTRINT uint64_t
#define ALIGN 0x100000L

/* Now for 512x512 matrices: */
#define NAME 512
#define WPR 8
#define MATROWS 512
#define GREASE 8
#define GREASE2 256
#include "gf2libh.def"
#include "gf2lib.def"
#undef NAME
#undef WPR
#undef MATROWS
#undef GREASE
#undef GREASE2

/* Now for 256x256 matrices: */
#define NAME 256
#define WPR 4
#define MATROWS 256
#define GREASE 8
#define GREASE2 256
#include "gf2libh.def"
#include "gf2lib.def"
#undef NAME
#undef WPR
#undef MATROWS
#undef GREASE
#undef GREASE2

/* Now for 128x128 matrices: */
#define NAME 128
#define WPR 2
#define MATROWS 128
#define GREASE 4
#define GREASE2 16
#include "gf2libh.def"
#include "gf2lib.def"
#undef NAME
#undef WPR
#undef MATROWS
#undef GREASE
#undef GREASE2

/* Now for 64x64 matrices: */
#define NAME 64
#define WPR 1
#define MATROWS 64
#define GREASE 4
#define GREASE2 16
#include "gf2libh.def"
#include "gf2lib.def"
#undef NAME
#undef WPR
#undef MATROWS
#undef GREASE
#undef GREASE2
