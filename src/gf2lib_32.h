/* This file includes gf2libh.def more than once with different parameters. */
/* This is for 32bit machines. */

/* Global definitions: */
#define WORD unsigned long
#define PTRINT unsigned long
#define ALIGN 0x100000L

/* Now for 512x512 matrices: */
#define NAME 512
#define WPR 16
#define MATROWS 512
#define GREASE 8
#define GREASE2 256
#include "gf2libh.def"
#undef NAME
#undef WPR
#undef MATROWS
#undef GREASE
#undef GREASE2

/* Now for 256x256 matrices: */
#define NAME 256
#define WPR 8
#define MATROWS 256
#define GREASE 8
#define GREASE2 256
#include "gf2libh.def"
#undef NAME
#undef WPR
#undef MATROWS
#undef GREASE
#undef GREASE2

/* Now for 128x128 matrices: */
#define NAME 128
#define WPR 4
#define MATROWS 128
#define GREASE 4
#define GREASE2 16
#include "gf2libh.def"
#undef NAME
#undef WPR
#undef MATROWS
#undef GREASE
#undef GREASE2

/* Now for 64x64 matrices: */
#define NAME 64
#define WPR 2
#define MATROWS 64
#define GREASE 4
#define GREASE2 16
#include "gf2libh.def"
#undef NAME
#undef WPR
#undef MATROWS
#undef GREASE
#undef GREASE2

/* Now for 32x32 matrices: */
#define NAME 32
#define WPR 1
#define MATROWS 32
#define GREASE 4
#define GREASE2 16
#include "gf2libh.def"
#undef NAME
#undef WPR
#undef MATROWS
#undef GREASE
#undef GREASE2

#undef WORD
typedef unsigned long WORD;
#define WORDSIZE 32

