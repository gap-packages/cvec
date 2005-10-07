/***************************************************************************
**
*A  cvec.c               cvec-package                        Max Neunhoeffer
**
**  
*Y  Copyright (C) 2005  Lehrstuhl D f\"ur Mathematik, RWTH Aachen
**  
*/

const char * Revision_pl_c =
   "$Id: cvec.c,v$";

#include <stdlib.h>

#include "src/compiled.h"          /* GAP headers                */

#if SYS_IS_CYGWIN32
#include <cygwin/in.h>
#endif

/* Our basic unit is a C unsigned long: */
typedef unsigned long Word;  /* Our basic unit for operations, 32 or 64 bits */
#define Word32 UInt4

#define WORDALLONE (~(0UL))
#define BYTESPERWORD sizeof(Word)
#define CACHESIZE (512L*1024L)
#define CACHELINE 64
/* If you want to change the following limit, please also change the
 * corresponding value in cvec.gi in CVEC.NewCVecClass! */
#define MAXDEGREE 1024

/* Define this to empty if you want global access to functions: */
#define STATIC static

/* Define this to empty if your compiler does not support inlined functions: */
#define INLINE inline


  /************************************/
 /* Macros to access the data types: */
/************************************/

/* The following positions are exported into the record CVEC for use
 * within the GAP part: If you add a position, please document it
 * in gap/cvec.gd and export it in InitLibrary! */

#define IDX_p 1
#define IDX_d 2
#define IDX_q 3
#define IDX_conway 4
#define IDX_bitsperel 5
#define IDX_elsperword 6
#define IDX_wordinfo 7
#define IDX_bestgrease 8
#define IDX_greasetabl 9
#define IDX_filts 10
#define IDX_tab1 11
#define IDX_tab2 12
#define IDX_size 13
#define IDX_scafam 14

#define IDX_fieldinfo 1
#define IDX_len 2
#define IDX_wordlen 3
#define IDX_type 4
#define IDX_GF 5
#define IDX_lens 6
#define IDX_classes 7

#define OFF_mask 0
#define OFF_offset 1
#define OFF_maskp 2
#define OFF_cutmask 3
#define POS_DATA_TYPE 3

/* currently unused, see below:
#define PREPARE(f) \
    Word *wi = (Word *) (CHARS_STRING(ELM_PLIST(f,IDX_wordinfo))); \
    register Word offset = wi[OFF_offset]; \
    register Word mask = wi[OFF_mask]; \
    register Int shift = INT_INTOBJ(ELM_PLIST(f,IDX_bitsperel))-1; \
    register Int p = INT_INTOBJ(ELM_PLIST(f,IDX_p))
#define REDUCE(x) (x - (((x + offset) & mask) >> shift) * p)
*/

/* The following is used for arithmetic: */
#define PREPARE(f) \
    Word *wi = (Word *) (CHARS_STRING(ELM_PLIST(f,IDX_wordinfo))); \
    register Word offset = wi[OFF_offset]; \
    register Word mask = wi[OFF_mask]; \
    register Int shift = INT_INTOBJ(ELM_PLIST(f,IDX_bitsperel))-1; \
    register Int ps = INT_INTOBJ(ELM_PLIST(f,IDX_p))*(mask>>shift)
#define REDUCE(x) x - ((((x+offset)&mask) - (((x+offset)&mask)>>shift))&ps)

#define PREPARE_cl(v,cl) \
    Obj cl = ELM_PLIST(TYPE_DATOBJ(v),POS_DATA_TYPE);
#define PREPARE_clfi(v,cl,fi) \
    Obj cl = ELM_PLIST(TYPE_DATOBJ(v),POS_DATA_TYPE); \
    Obj fi = ELM_PLIST(cl,IDX_fieldinfo)
#define PREPARE_p(fi) Int p = INT_INTOBJ(ELM_PLIST(fi,IDX_p))
#define PREPARE_d(fi) Int d = INT_INTOBJ(ELM_PLIST(fi,IDX_d))
#define PREPARE_q(fi) Int q = INT_INTOBJ(ELM_PLIST(fi,IDX_q))
#define PREPARE_cp(fi) Int *cp = \
            (Int *)CHARS_STRING(ELM_PLIST(fi,IDX_conway))
#define PREPARE_bpe(fi) Int bitsperel = \
            INT_INTOBJ(ELM_PLIST(fi,IDX_bitsperel))
#define PREPARE_epw(fi) Int elsperword = \
            INT_INTOBJ(ELM_PLIST(fi,IDX_elsperword))
#define PREPARE_type(fi) Obj type = ELM_PLIST(fi,IDX_type)
#define PREPARE_tab1(fi) Obj tab1 = ELM_PLIST(fi,IDX_tab1)
#define PREPARE_tab2(fi) Obj tab2 = ELM_PLIST(fi,IDX_tab2)
#define PREPARE_mask(fi) Word mask = \
            ((Word *)CHARS_STRING(ELM_PLIST(fi,IDX_wordinfo)))[OFF_mask]
#define PREPARE_offset(fi) Word offset = \
            ((Word *)CHARS_STRING(ELM_PLIST(fi,IDX_wordinfo)))[OFF_offset]
#define PREPARE_maskp(fi) Word maskp = \
            ((Word *)CHARS_STRING(ELM_PLIST(fi,IDX_wordinfo)))[OFF_maskp]
#define PREPARE_cutmask(fi) Word cutmask = \
            ((Word *)CHARS_STRING(ELM_PLIST(fi,IDX_wordinfo)))[OFF_cutmask]


#define DATA_CVEC(cvec) ((Word *)((ADDR_OBJ(cvec))+1))

/* The following macros is called IS_CVEC, but actually does not test
 * the complete type. It only does some cheap plausibility check. In
 * addition, it also covers the case of big FF scalars (CSca). */

#define IS_CVEC(obj) \
   (TNUM_OBJ(obj)==T_DATOBJ && \
    TNUM_OBJ(ELM_PLIST(TYPE_DATOBJ(obj),POS_DATA_TYPE))==T_POSOBJ)


  /*******************************/
 /* Internal or test functions: */
/*******************************/

STATIC Obj OurErrorBreakQuit(char *msg)
{
    ErrorReturnVoid(msg,0L,0L,
                    "    try 'return;' (which will not work here!)");
    ErrorQuit("You were told, 'return;' did not work!",0L,0L);
    return 0L;
}

STATIC Obj TEST_ASSUMPTIONS(Obj self)
/* Result 0 is OK, otherwise something is wrong... */
{
    /* Note in addition, that d * length of a vector must fit into a
     * C Int! */
    if (0UL - 1UL != WORDALLONE) return INTOBJ_INT(1);
    if ( WORDALLONE >> 0 != WORDALLONE ) return INTOBJ_INT(2);
    if ( sizeof(Word) != 8 && sizeof(Word) != 4) return INTOBJ_INT(3);
#if !(__BYTE_ORDER == __LITTLE_ENDIAN) && !(__BYTE_ORDER == __BIG_ENDIAN)
    return INTOBJ_INT(4);
#else
    return INTOBJ_INT(0);
#endif
#ifdef SYS_IS_64_BIT
    if (sizeof(Word) != 8) return INTOBJ_INT(5);
#else
    if (sizeof(Word) != 4) return INTOBJ_INT(6);
#endif
    if (sizeof(Word32) != 4) return INTOBJ_INT(7);
}

STATIC Obj COEFF_LIST_TO_C(Obj self, Obj po, Obj s)
{
    /* po is a list of (small) GAP integers, s a GAP string. */
    Int l,i;
    Int *p;

    l = LEN_PLIST(po);
    GrowString(s,sizeof(Int)*l);
    SET_LEN_STRING(s,sizeof(Int)*l);
    p = (Int *) CHARS_STRING(s);
    for (i = 1;i <= l;i++) *p++ = INT_INTOBJ(ELM_PLIST(po,i));
    return s;
}

STATIC Obj FINALIZE_FIELDINFO(Obj self, Obj f)
{
    Obj s;
    Word *po;
    Word w;
    Int j;
    
    PREPARE_p(f);
    PREPARE_bpe(f);
    PREPARE_epw(f);

    /* GARBAGE COLLECTION POSSIBLE */
    s = NEW_STRING(sizeof(Word) * 4);
    po = (Word *) CHARS_STRING(s);
    if (p & 1) {   /* Odd characteristic */
        for (w = 1UL,j = 1;j < elsperword;j++)
            w = (w << bitsperel)+1UL;
        po[OFF_mask] = w << (bitsperel-1);
        po[OFF_offset] = po[OFF_mask] - w * p;
        po[OFF_maskp] = (1UL << bitsperel)-1;
        po[OFF_cutmask] = w * po[OFF_maskp];
    } else {     /* Characteristic 2 */
        po[OFF_mask] = 0;
        po[OFF_offset] = 0;
        po[OFF_maskp] = 1;
        po[OFF_cutmask] = WORDALLONE;
    }
    SET_ELM_PLIST(f,IDX_wordinfo,s);
    CHANGED_BAG(f);
    return f;
}

Obj INIT_SMALL_GFQ_TABS(Obj self, Obj pp, Obj dd, Obj qq, Obj tab1, Obj tab2,
                        Obj primroot)
{
    extern unsigned long PolsFF[];
    UInt p = INT_INTOBJ(pp);
    UInt d = INT_INTOBJ(dd);
    UInt q = INT_INTOBJ(qq);
    UInt poly;           /* Conway polynomial of extension  */
    UInt i, l, f, n, e;  /* loop variables                  */
    /* We already know that tab1 and tab2 are lists of length q. */
    
    /* The following code is from finfield.c in the GAP kernel: */

    /* if q is a prime find the smallest primitive root $e$, use $x - e$   */
    if ( d == 1 ) {
        for ( e = 1, i = 1; i != p-1; ++e ) {
            for ( f = e, i = 1; f != 1; ++i )
                f = (f * e) % p;
        }
        poly = p-(e-1);
    }
    /* otherwise look up the polynomial used to construct this field       */
    else {
        for ( i = 0; PolsFF[i] != q; i += 2 ) ;
        poly = PolsFF[i+1];
    }

    /* We want ELM_PLIST(tab1,VAL_FFE(fe)+1) to be the small integer
     * whose p-adic expansion corresponds to fe in F_p[x]/cp where
     * cp is the Conway polynomial. tab2 works the opposite way, that is,
     * ELM_PLIST(tab2,e+1) = fe for the corresponding FFE. */
    SET_ELM_PLIST(tab1,1,INTOBJ_INT(0));
    SET_ELM_PLIST(tab2,1,NEW_FFE(FLD_FFE(primroot),0));
    for ( e = 1, n = 0; n < q-1; ++n ) {
        SET_ELM_PLIST(tab1,n+2,INTOBJ_INT(e));
        SET_ELM_PLIST(tab2,e+1,NEW_FFE(FLD_FFE(primroot),n+1));
        if ( p != 2 ) {
            f = p * (e % (q/p));  l = (p - (e/(q/p))) % p;  e = 0;
            for ( i = 1; i < q; i *= p )
                e = e + i * ((f/i + l * (poly/i)) % p);
        }
        else {
            if ( 2*e & q )  e = 2*e ^ poly ^ q;
            else            e = 2*e;
        }
    }
    return 0L;
}

  /**********************/
 /* Sequential access: */
/**********************/

typedef struct SeqAcc {
    Int d;
    Int bitsperel;
    Int elsperword;
    Int pos;     /* one based */
    Word mask;   /* to extract */
    Int bitpos;
    Int offset;  /* in words */
} seqaccess;

/* For the following macros sa is *seqaccess, v is *Word, off is Int, s is Int,
 * which is a prime field scalar. */

/* Gets a prime field component: */
#define GET_VEC_ELM(sa,w,off) \
  (((w)[(sa)->offset+off] & (sa)->mask) >> (sa)->bitpos)

/* Sets a prime field component: */
#define SET_VEC_ELM(sa,w,off,s) \
  (((w)[((sa)->offset)+(off)])) = \
  ((((w)[((sa)->offset)+(off)]) & (~((sa)->mask))) | (s << ((sa)->bitpos)))

/* Moves the sequential access struct left (down): */
#define STEP_LEFT(sa) \
  (sa)->pos--; \
  if ((sa)->bitpos > 0) { \
      (sa)->bitpos -= (sa)->bitsperel; \
      (sa)->mask >>= (sa)->bitsperel; \
  } else { \
      (sa)->bitpos += (sa)->bitsperel*((sa)->elsperword-1); \
      (sa)->mask <<= (sa)->bitsperel*((sa)->elsperword-1); \
      (sa)->offset -= (sa)->d; \
  }

/* Moves the sequential access struct right (up): */
#define STEP_RIGHT(sa) \
  (sa)->pos++; \
  if ((sa)->bitpos < (sa)->bitsperel*((sa)->elsperword-1)) { \
      (sa)->bitpos += (sa)->bitsperel; \
      (sa)->mask <<= (sa)->bitsperel; \
  } else { \
      (sa)->bitpos -= (sa)->bitsperel*((sa)->elsperword-1); \
      (sa)->mask >>= (sa)->bitsperel*((sa)->elsperword-1); \
      (sa)->offset += (sa)->d; \
  }

/* Initializes the sequential access struct, v is a cvec: */
INLINE void INIT_SEQ_ACCESS(seqaccess *sa, Obj v, Int pos)
{
    PREPARE_clfi(v,cl,fi);
    PREPARE_d(fi);
    PREPARE_bpe(fi);
    PREPARE_epw(fi);
    
    sa->d = d;
    sa->bitsperel = bitsperel;
    sa->elsperword = elsperword;
    sa->pos = pos;
    sa->offset = d*((pos-1) / elsperword);
    sa->bitpos = ((pos-1)%elsperword) * bitsperel;
    sa->mask = ((1UL << bitsperel)-1) << sa->bitpos;
}


  /*******************************************************/
 /* Interfacing stuff for the objects to the GAP level: */
/*******************************************************/

STATIC Obj NEW(Obj self, Obj cl, Obj type)
{
    Obj v;
    Int si;

    si = sizeof(Word) * INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen));
    /* GARBAGE COLLECTION POSSIBLE */
    v = NewBag( T_DATOBJ, sizeof( Obj ) + si );
    if (v == 0L) {
        return OurErrorBreakQuit("CVEC.NEW: Cannot allocate memory");
    }
    SET_TYPE_DATOBJ(v, type);
    return v;
}

STATIC Obj MAKEZERO(Obj self, Obj v)
{
    if (!IS_CVEC(v)) {
        return OurErrorBreakQuit("CVEC.MAKEZERO: no cvec");
    }
    {
        Int si;
        PREPARE_cl(v,cl);
        si = INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen));
        memset(DATA_CVEC(v),0,sizeof(Word)*si);
    }
    return 0L;
}
    
STATIC Obj COPY(Obj self, Obj v, Obj w)
{
    if (!IS_CVEC(v) || !IS_CVEC(w)) {
        return OurErrorBreakQuit("CVEC.COPY: no cvec");
    }
    {
        Int si,si2;
        PREPARE_cl(v,cl);
        PREPARE_cl(w,cl2);
        si = INT_INTOBJ(ELM_PLIST(cl,IDX_len));
        si2 = INT_INTOBJ(ELM_PLIST(cl2,IDX_len));
        if (si != si2) {
            return OurErrorBreakQuit("CVEC.COPY: unequal length");
        }
        si = INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen));
        memcpy(DATA_CVEC(w),DATA_CVEC(v),sizeof(Word)*si);
        return 0L;
    }
}

STATIC Obj CVEC_TO_INTREP(Obj self,Obj v,Obj l)
/* This function returns the vector in its integer representation. This
 * means, that for the case that q <= 65536 or d = 1 each integer
 * corresponds to one field entry (p-adic expansion for d>1). For bigger
 * q (and d), we fill a list of lists of length d containing d little
 * integers for each vector entry, giving the coefficients of the
 * polynomial over the prime field representing the residue class. */
{
    register Word *pw;
    Int len;
    Int size;

    if (!IS_CVEC(v)) {
        return OurErrorBreakQuit("CVEC.CVEC_TO_INTREP: no cvec");
    }
    if (!IS_PLIST(l)) {
        return OurErrorBreakQuit("CVEC.CVEC_TO_INTREP: no plist");
    }

    {
        PREPARE_clfi(v,cl,fi);
        PREPARE_d(fi);
        len = INT_INTOBJ(ELM_PLIST(cl,IDX_len));
        size = INT_INTOBJ(ELM_PLIST(fi,IDX_size));

        if (LEN_PLIST(l) != len) {
            return OurErrorBreakQuit("CVEC.CVEC_TO_INTREP: different lengths");
        }

        pw = DATA_CVEC(v);
        {
            PREPARE_p(fi);
            PREPARE_epw(fi);
            PREPARE_bpe(fi);
            PREPARE_maskp(fi);

            if (d == 1) {
                register Word y;
                register Word w = 0;
                Int i,ii;
                for (i = 1,ii = elsperword;i <= len;i++,ii++) {
                    if (ii == elsperword) { w = *pw++; ii = 0; }
                    y = w & maskp;
                    w >>= bitsperel;
                    SET_ELM_PLIST(l,i,INTOBJ_INT((Int) y));
                }
            } else {
                pw -= d;   /* This is corrected at i==0! */
                Int i;
                register Int j;
                register Int shift;
                register Word y;
                if (size <= 0) {
                    for (i = 0;i < len;i++) {
                        shift = (i % elsperword) * bitsperel;
                        if (shift == 0) pw += d;
                        y = 0;
                        for (j = d - 1;j >= 0;j--)
                            y = y * p + ((pw[j] >> shift) & maskp);
                        SET_ELM_PLIST(l,i+1,INTOBJ_INT((Int) y));
                    }
                } else {   /* size >= 1, we write coefficient lists */
                    for (i = 0;i < len;i++) {
                        Obj oo = ELM_PLIST(l,i+1);
                        shift = (i % elsperword) * bitsperel;
                        if (shift == 0) pw += d;
                        for (j = 0;j < d;j++)
                            SET_ELM_PLIST(oo,j+1,
                                 INTOBJ_INT((Int)((pw[j] >> shift) & maskp)));
                    }
                }
            }
        }
    }
    return 0L;
}

STATIC Obj INTREP_TO_CVEC(Obj self,Obj l,Obj v)
/* This function transfers data in integer representation to the vector. This
 * means, that for the case that q <= 65536 or d = 1, each integer
 * corresponds to one field entry (p-adic expansion for d > 1). For
 * bigger q (and d), we have a list of lists of length d of little
 * integers such that every d numbers give the coefficients of the
 * polynomial over the prime field representing the residue class.
 * The length of the list l must correspond to the length of v. As an
 * exception, the elements in integer representation may also be GAP
 * FFEs, if those are in the same field or a subfield. */
{
    register Word *pw;

    if (!IS_CVEC(v)) {
        return OurErrorBreakQuit("CVEC.INTREP_TO_CVEC: no cvec");
    }

    {
      PREPARE_clfi(v,cl,fi);
      PREPARE_d(fi);
      Int len = INT_INTOBJ(ELM_PLIST(cl,IDX_len));
      pw = DATA_CVEC(v);

      /* Check lengths: */
      if (!IS_PLIST(l) || LEN_PLIST(l) != len) {
          return OurErrorBreakQuit(
         "CVEC.INTREP_TO_CVEC: l must be a list of corresponding length to v");
      }

      {
          PREPARE_p(fi);
          PREPARE_q(fi);
          PREPARE_epw(fi);
          PREPARE_bpe(fi);
          PREPARE_tab1(fi);

          if (d == 1) {
              register Word y;
              register Word w;
              register Int j;
              register Obj o;
              Int i;
              for (i = 1;i <= len;i += elsperword) {
                  j = i+elsperword-1;
                  if (j > len) j=len;
                  w = 0;
                  while (j >= i) {
                      o = ELM_PLIST(l,j);
                      if (IS_INTOBJ(o))
                          y = (Word) INT_INTOBJ(o);
                      else if (IS_FFE(o) && CHAR_FF(FLD_FFE(o)) == p && 
                               DEGR_FF(FLD_FFE(o)) == 1)
                          if (VAL_FFE(o) == 0)
                            y = (Word) 0;
                          else
                            y = (Word) INT_INTOBJ(ELM_PLIST(tab1,
                             (VAL_FFE(o)-1)*((q-1)/(SIZE_FF(FLD_FFE(o))-1))+2));
                      else {
                          return OurErrorBreakQuit(
                                "CVEC.INTREP_TO_CVEC: invalid object in list");
                      }
                      w = (w << bitsperel) | y;
                      j--;
                  }
                  *pw++ = w;
              }
          } else {
              /* First clear the space: */
              memset(pw,0,sizeof(Word)*INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen)));
              pw -= d;   /* This is corrected at i==0! */
              Int i;
              register Int j;
              register Int shift;
              register Word y;
              register Obj o;
              for (i = 0;i < len;i++) {
                  shift = (i % elsperword) * bitsperel;
                  if (shift == 0) pw += d;
                  o = ELM_PLIST(l,i+1);
                  if (IS_INTOBJ(o)) {
                      y = (Word) INT_INTOBJ(o);
                      for (j = 0;j < d;j++) {
                          pw[j] |= ((y % p) << shift);
                          y /= p;
                      }
                  } else if (IS_FFE(o) && CHAR_FF(FLD_FFE(o)) == p && 
                           (d % DEGR_FF(FLD_FFE(o)) == 0)) {
                      if (VAL_FFE(o) == 0)
                          y = (Word) 0;
                      else 
                          y = (Word) INT_INTOBJ(ELM_PLIST(tab1,
                           (VAL_FFE(o)-1)*((q-1)/(SIZE_FF(FLD_FFE(o))-1))+2));
                      for (j = 0;j < d;j++) {
                          pw[j] |= ((y % p) << shift);
                          y /= p;
                      }
                  } else if (IS_PLIST(o) && LEN_PLIST(o) == d) {
                      register Obj oo;
                      for (j = 0;j < d;j++) {
                          oo = ELM_PLIST(o,j+1);
                          if (IS_INTOBJ(oo))
                              pw[j] |= INT_INTOBJ(oo) << shift;
                              /* This should better be between 0 and p-1! */
                          else if (IS_FFE(oo) && CHAR_FF(FLD_FFE(oo)) == p &&
                                   d == 1) {
                              if (VAL_FFE(oo) != 0)
                                  pw[j] |= INT_INTOBJ(ELM_PLIST(tab1,
                                               (VAL_FFE(oo)+1))) << shift;
                              /* We assume that tab1 is for GF(p) here! */
                          } else {
                              return OurErrorBreakQuit(
                             "CVEC.INTREP_TO_CVEC: invalid object in list");
                          }
                      }
                  } else {
                      return OurErrorBreakQuit(
                             "CVEC.INTREP_TO_CVEC: invalid object in list");
                  }
              }
          }
      }
    }
    return 0L;
}

Obj INTLI_TO_FFELI(Obj self,Obj fi, Obj l)
/* Transforms a list of integers between 0 and q-1 into FFEs. */
{
    if (!IS_PLIST(l)) {
        return OurErrorBreakQuit(
      "CVEC.INTLI_TO_FFELI: Must be called with a field info and a plain list");
    }
    {
        Int len;
        Int i;
        Obj e;
        PREPARE_q(fi);
        PREPARE_tab2(fi);

        len = LEN_PLIST(l);
        for (i = 1;i <= len;i++) {
            e = ELM_PLIST(l,i);
            if (!IS_INTOBJ(e) || INT_INTOBJ(e) < 0 || INT_INTOBJ(e) >= q) {
                return OurErrorBreakQuit("CVEC.INTLI_TO_FFELI: Elements of l "
                                         "must be integers between 0 and q‐1");
            }
            e = ELM_PLIST(tab2,INT_INTOBJ(e)+1);
            SET_ELM_PLIST(l,i,e);
        }
    }
    return 0L;
}

Obj FFELI_TO_INTLI(Obj self,Obj fi, Obj l)
/* Transforms a list of FFEs into integers between 0 and q-1. */
{
    if (!IS_PLIST(l)) {
        return OurErrorBreakQuit(
      "CVEC.FFELI_TO_INTLI: Must be called with a field info and a plain list");
    }
    {
        Int len;
        Int i;
        Obj e;
        PREPARE_p(fi);
        PREPARE_d(fi);
        PREPARE_q(fi);
        PREPARE_tab1(fi);

        len = LEN_PLIST(l);
        for (i = 1;i <= len;i++) {
            e = ELM_PLIST(l,i);
            if (!IS_FFE(e) || CHAR_FF(FLD_FFE(e)) != p || 
                (d % DEGR_FF(FLD_FFE(e))) != 0) {
                return OurErrorBreakQuit("CVEC.FFELI_TO_INTLI: Elements of l "
                                         "must be finite field elements over "
                                         "the right field");
            }
            if (VAL_FFE(e) == 0) {
                e = INTOBJ_INT(0);
            } else {
                e = ELM_PLIST(tab1,
                         (VAL_FFE(e)-1)*((q-1)/(SIZE_FF(FLD_FFE(e))-1))+2);
            }
            SET_ELM_PLIST(l,i,e);
        }
    }
    return 0L;
}

STATIC Obj CVEC_TO_NUMBERFFLIST(Obj self, Obj v, Obj l, Obj split)
{
    PREPARE_clfi(v,cl,fi);
    PREPARE_epw(fi);
    PREPARE_bpe(fi);
    PREPARE_maskp(fi);
    PREPARE_p(fi);
    Int wordlen = INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen));
    Word *vv = DATA_CVEC(v);
    Word wo;
    Word res;
    Int i,j;
    Int shift;

    for (i = 1;i <= wordlen;i++) {
        wo = *vv++;
        res = 0;
        shift = bitsperel * (elsperword-1);
        for (j = elsperword;j > 0;j--,shift -= bitsperel)
            res = res * p + ((wo >> shift) & maskp);
        if (split == True) {
            SET_ELM_PLIST(l,2*i-1,
                 INTOBJ_INT(res & ((1 << (4*BYTESPERWORD)) - 1L)));
            SET_ELM_PLIST(l,2*i,
                 INTOBJ_INT(res >> (4*BYTESPERWORD)));
        } else {
            SET_ELM_PLIST(l,i,INTOBJ_INT((Int) res));
        }
    } 
    return 0L;
}

STATIC Obj NUMBERFFLIST_TO_CVEC(Obj self, Obj l, Obj v, Obj split)
{
    PREPARE_clfi(v,cl,fi);
    PREPARE_epw(fi);
    PREPARE_bpe(fi);
    PREPARE_p(fi);
    Int wordlen = INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen));
    Word *vv = DATA_CVEC(v);
    Word wo;
    Word res;
    Int i,j;
    Int shift;

    for (i = 1;i <= wordlen;i++) {
        if (split == True) {
            res = (Word) INT_INTOBJ(ELM_PLIST(l,2*i-1)) +
                  (((Word) INT_INTOBJ(ELM_PLIST(l,2*i))) << (4*BYTESPERWORD));
        } else {
            res = INT_INTOBJ(ELM_PLIST(l,i));
        }
        shift = 0;
        wo = 0;
        for (j = elsperword;j > 0;j--,shift += bitsperel) {
            wo |= (res % p) << shift;
            res /= p;
        }
        *vv++ = wo;;
    } 
    return 0L;
}

  /*******************/
 /* The arithmetic: */
/*******************/

 /* Now we have the real worker routines, they are meant to be called from   */
/* the C level.                                                             */

/* For multiplication with scalars with non-prime fields we need some
 * infrastructure: */
/* p-adic expansion of the scalar (mod Conway polynomial): */
/* (index 0 contains prime field entry) */
static Int scbuf[MAXDEGREE+1];
/* Number of entries actually used in sc (beginning with 0): */
/* Is always at least 1. */
static Int sclen; 
/* A buffer for elsperword consecutive field entries: */
static Int buf[MAXDEGREE+1]; 

   /*                                                          */
  /* First some internal inlined functions to do addition and */
 /* scalar multiplication:                                   */
/*                                                          */

static INLINE void ADD2_INL(Word *vv,Word *ww,Obj f,long i)
/* This internal inlined function adds i Words at *ww to the corresponding
 * Words at *vv. Characteristic 2 and odd characteristic are handled
 * separately. */
{
    PREPARE_p(f);
    if (p == 2) {
        /* Characteristic 2: */
        register Word *vv_r = vv;
        register Word *ww_r = ww;
        register long j = i;
        while (--j >= 0) *vv_r++ ^= *ww_r++;
    } else {
        /* Odd characteristic: */
        register Word wo;
        register Word *vv_r = vv;
        register Word *ww_r = ww;
        register long i_r = i;
        PREPARE(f);
        while (--i_r >= 0) {
            wo = *vv_r + *ww_r++;
            *vv_r++ = REDUCE(wo);
        }
    }
}

static INLINE void ADD3_INL(Word *uu,Word *vv,Word *ww,Obj f,long i)
/* This internal inlined function adds i Words at *ww to the corresponding
 * Words at *vv and stores them to *uu. Characteristic 2 and odd 
 * characteristic are handled separately. */
{
    PREPARE_p(f);
    if (p == 2) {
        /* Characteristic 2: */
        register Word *uu_r = uu;
        register Word *vv_r = vv;
        register Word *ww_r = ww;
        register long i_r = i;
        while (--i_r >= 0) *uu_r++ = (*vv_r++) ^ (*ww_r++);
    } else {
        /* Odd characteristic: */
        register Word wo;
        register long i_r = i;
        register Word *uu_r = uu;
        register Word *vv_r = vv;
        register Word *ww_r = ww;
        PREPARE(f);
        while (--i_r >= 0) {
            wo = *vv_r++ + *ww_r++;
            *uu_r++ = REDUCE(wo);
        }
    }
}

static INLINE void MUL_INL(Word *vv,Obj f,Word s,long i)
/* This interal inlined function multiplies i Words at *vv by the scalar
 * s from the prime field (0 <= s < p). Special cases 0, 1, p-1, and 2
 * are handled especially fast. 
 * This code is extremely similar to the code of MUL1_INL, MUL2_INL, ADDMUL_INL,
 * and ADDMUL1_INL, so changes should be made accordingly. */
{
    PREPARE_p(f);
    /* Note that the characteristic 2 case is handled properly, because
     * s is either 0 or 1. */
    /* Handle scalar 1: */
    if (s == 1) return;
    /* Handle scalar 0: */
    if (s == 0)
        memset(vv,0,sizeof(Word) * i);
    else if (s == p - 1) { 
        /* Here we can calculate p-x for all entries x. */
        PREPARE(f);
        PREPARE_bpe(f);
        register Word pm1 = (mask >> (bitsperel - 1)) * p;
        register long i_r = i;
        register Word *vv_r = vv;
        register Word wo;
        while (--i_r >= 0) {
            wo = pm1 - *vv_r;
            *vv_r++ = REDUCE(wo);
        }
    } else {
        /* From here on we need some extra variables: */
        PREPARE(f);
        register Word wo,res;
        register Word *vv_r = vv;
        register long i_r = i;

        if (s == 2) { /* Here we can add v to v */
            while (--i_r >= 0) {
                wo = *vv_r << 1;
                *vv_r++ = REDUCE(wo);
            }
        } else {
            /* Now to the ugly case: */
            while (--i_r >= 0) {
                /* Handle one word: */
                register Word ss = s;
                wo = *vv_r;
                res = 0;
                while (1) {
                    if (ss & 1) {
                        res += wo; 
                        res = REDUCE(res);
                    }
                    ss >>= 1;
                    if (!ss) break;
                    wo <<= 1; 
                    wo = REDUCE(wo);
                }
                *vv_r++ = res;
            }
        }
    }
}

static INLINE Word MUL1_INL(Word wo,Obj f,Word s)
/* This interal inlined function multiplies 1 Word wo by the scalar
 * s from the prime field (0 <= s < p). Special cases 0, 1, p-1, and 2
 * are handled especially fast. 
 * This code is extremely similar to the code of MUL_INL, MUL2_INL, ADDMUL_INL,
 * and ADDMUL1_INL, so changes should be made accordingly. */
{
    PREPARE_p(f);
    /* Note that the characteristic 2 case is handled properly, because
     * s is either 0 or 1. */
    /* Handle scalar 1: */
    if (s == 1) return wo;
    /* Handle scalar 0: */
    else if (s == 0) return (Word) 0UL;
    else if (s == p - 1) { 
        /* Here we can calculate p-x for all entries x. */
        PREPARE(f);
        PREPARE_bpe(f);
        register Word pm1 = (mask >> (bitsperel - 1)) * p;
        wo = pm1 - wo;
        return REDUCE(wo);
    } else {
        /* From here on we need some extra variables: */
        PREPARE(f);

        if (s == 2) { /* Here we can add v to v */
            wo <<= 1;
            return REDUCE(wo);
        } else {
            /* Now to the ugly case: */
            register Word res = 0;
            while (1) {
                if (s & 1) {
                    res += wo; 
                    res = REDUCE(res);
                }
                s >>= 1;
                if (!s) break;
                wo <<= 1; 
                wo = REDUCE(wo);
            }
            return res;
        }
    }
}

static INLINE void MUL2_INL(Word *vv,Word *ww,Obj f,Word s,long i)
/* This interal inlined function multiplies i Words at *ww by the scalar
 * s from the prime field (0 <= s < p) and stores the result to *vv. 
 * Special cases 0, 1, p-1, and 2 are handled especially fast. 
 * This code is extremely similar to the code of MUL_INL, MUL1_INL, ADDMUL_INL,
 * and ADDMUL1_INL, so changes should be made accordingly. */
{
    PREPARE_p(f);
    /* Note that the characteristic 2 case is handled properly, because
     * s is either 0 or 1. */
    /* Handle scalar 1: */
    if (s == 1) memcpy(vv,ww,sizeof(Word) * i);
    /* Handle scalar 0: */
    else if (s == 0) memset(vv,0,sizeof(Word) * i);
    else if (s == p - 1) { 
        PREPARE(f);
        PREPARE_bpe(f);
        /* Here we can calculate p-x for all entries x. */
        register Word pm1 = (mask >> (bitsperel - 1)) * p;
        register long i_r = i;
        register Word *ww_r = ww;
        register Word *vv_r = vv;
        register Word wo;
        while (--i_r >= 0) {
            wo = pm1 - *ww_r++;
            *vv_r++ = REDUCE(wo);
        }
    } else {
        /* From here on we need some extra variables: */
        PREPARE(f);
        register Word wo,res;
        register long i_r = i;
        register Word *ww_r = ww;
        register Word *vv_r = vv;

        if (s == 2) { /* Here we can add v to v */
            while (--i_r >= 0) {
                wo = *ww_r++ << 1;
                *vv_r++ = REDUCE(wo);
            }
        } else {
            /* Now to the ugly case: */
            while (--i_r >= 0) {
                /* Handle one word: */
                register Word ss = s;
                wo = *ww_r++;
                res = 0;
                while (1) {
                    if (ss & 1) {
                        res += wo; 
                        res = REDUCE(res);
                    }
                    ss >>= 1;
                    if (!ss) break;
                    wo <<= 1; 
                    wo = REDUCE(wo);
                }
                *vv_r++ = res;
            }
        }
    }
}

static INLINE void ADDMUL_INL(Word *vv,Word *ww,Obj f,Word s,long i)
/* This interal inlined function multiplies i Words at *ww by the scalar
 * s from the prime field (0 <= s < p) and adds the result to *vv. 
 * Special cases 0, 1, p-1, and 2 are handled especially fast. 
 * This code is extremely similar to the code of MUL_INL, MUL1_INL, MUL2_INL, 
 * and ADDMUL1_INL, so changes should be made accordingly. */
{
    PREPARE_p(f);
    /* Note that the characteristic 2 case is handled properly, because s
     * is either 0 or 1. */
    /* Handle scalar 1: */
    if (s == 1) ADD2_INL(vv,ww,f,i);
    /* Handle scalar 0: */
    else if (s == 0) return;
    else if (s == p - 1) { 
        /* Here we can calculate p-x for all entries x. */
        PREPARE(f);
        PREPARE_bpe(f);
        register Word pm1 = (mask >> (bitsperel - 1)) * p;
        register Word wo;
        register long i_r = i;
        register Word *ww_r = ww;
        register Word *vv_r = vv;
        while (--i_r >= 0) {
            wo = (pm1 - *ww_r++) + *vv_r;
            *vv_r++ = REDUCE(wo);
        }
    } else {
        /* From here on we need some extra variables: */
        PREPARE(f);
        register Word wo,res;
        register long i_r = i;
        register Word *ww_r = ww;
        register Word *vv_r = vv;

        if (s == 2) { /* Here we can add v to v */
            while (--i_r >= 0) {
                wo = (*ww_r++ << 1);
                wo = REDUCE(wo) + *vv_r;
                *vv_r++ = REDUCE(wo);
            }
        } else {
            /* Now to the ugly case: */
            while (--i_r >= 0) {
                /* Handle one word: */
                register Word ss = s;
                wo = *ww_r++;
                res = 0;
                while (1) {
                    if (ss & 1) {
                        res += wo; 
                        res = REDUCE(res);
                    }
                    ss >>= 1;
                    if (!ss) break;
                    wo <<= 1; 
                    wo = REDUCE(wo);
                }
                wo = *vv_r + res;
                *vv_r++ = REDUCE(wo);
            }
        }
    }
}

static INLINE Word ADDMUL1_INL(Word vv,Word ww,Obj f,Word s)
/* This interal inlined function multiplies one Word ww by the scalar
 * s from the prime field (0 <= s < p) and adds the result to the Word vv. 
 * Special cases 0, 1, p-1, and 2 are handled especially fast. 
 * This code is extremely similar to the code of MUL_INL, MUL1_INL, MUL2_INL, 
 * and ADDMUL_INL, so changes should be made accordingly. */
{
    PREPARE_p(f);
    if (p == 2) {  /* Even characteristic: */
        return s == 1 ? (vv ^ ww) : vv;
    } else {  /* Odd characteristic: */
        PREPARE(f);
        /* Handle scalar 1: */
        if (s == 1) { 
            vv += ww;
            return REDUCE(vv);
        }
        /* Handle scalar 0: */
        else if (s == 0) return vv;
        else if (s == p - 1) { 
            /* Here we can calculate p-x for all entries x. */
            PREPARE_bpe(f);
            register Word pm1 = (mask >> (bitsperel - 1)) * p;
            vv = (pm1 - ww) + vv;
            return REDUCE(vv);
        } else {
            /* From here on we need some extra variables: */
            register Word res;

            if (s == 2) { /* Here we can add v to v */
                ww = ww << 1;
                vv = REDUCE(ww) + vv;
                return REDUCE(vv);
            } else {
                /* Now to the ugly case: */
                res = 0;
                while (1) {
                    if (s & 1) {
                        res += ww; 
                        res = REDUCE(res);
                    }
                    s >>= 1;
                    if (!s) break;
                    ww <<= 1; 
                    ww = REDUCE(ww);
                }
                vv += res;
                return REDUCE(vv);
            }
        }
    }
}

/*
 * Element access, internally, we distinguish between prime field and
 * extension field. Also the cases for different representations of
 * scalars are distinguished. This is later used in the functions for the
 * GAP level: 
 */

static INLINE Int CVEC_Itemp(Obj fi, Word *v, Int i)
{
    PREPARE_epw(fi);
    PREPARE_bpe(fi);
    PREPARE_maskp(fi);
    i--;   /* we are now 1 based */
    return (Int) ((v[i/elsperword] >> (bitsperel * (i % elsperword))) & maskp);
}

static INLINE void CVEC_Itemq(Obj fi, Word *v, Int i)
/* Writes scalar into scbuf. */
{
    Int *sc = scbuf;
    Int j;
    i--;    /* we are now 1 based */

    PREPARE_epw(fi);
    PREPARE_bpe(fi);
    PREPARE_d(fi);
    PREPARE_maskp(fi);
    Int shift = (i % elsperword) * bitsperel;

    v += d * (i / elsperword);
    sclen = 1;  /* at least that */
    for (j = d;j > 0;j--) {
        *sc = ((*v++) >> shift) & maskp;
        if (*sc) sclen = (sc-scbuf)+1;
        sc++;
    }
}

static INLINE void CVEC_AssItemp(Obj fi, Word *v, Int i, Word sc)
{
    PREPARE_epw(fi);
    PREPARE_bpe(fi);
    PREPARE_maskp(fi);
    i--;   /* we are now 1 based */
    v += i / elsperword;
    register Int shift = bitsperel * (i % elsperword);
    *v = (*v & (WORDALLONE ^ (maskp << shift))) | (sc << shift);
}

static INLINE void CVEC_AssItemq(Obj fi, Word *v, Int i, Int *sc)
{
    PREPARE_epw(fi);
    PREPARE_bpe(fi);
    PREPARE_maskp(fi);
    PREPARE_d(fi);
    Int j;
    i--;   /* we are now 1 based */
    Int shift = (i % elsperword) * bitsperel;
    Word mask = WORDALLONE ^ (maskp << shift);

    v += d * (i / elsperword);
    for (j = d;j > 0;j--,v++) {
        *v = (*v & mask) | (((Word) (*sc++)) << shift);
    }
}

static INLINE Int CVEC_Firstnzp(Obj fi, Word *v, Int len)
/* Returns the index of the first non-zero element in the vector or len+1
 * if the vector is equal to zero. This is only for prime fields. */
{
    register PREPARE_epw(fi);
    register PREPARE_bpe(fi);
    register PREPARE_maskp(fi);
    register Word *p = v;
    register Int i = 1;
    register Int im = 0;  /* i mod elsperword */
    register Word w = 0;

    while (i <= len) {
        if (im == 0) {
            w = *p++;
            if (w == 0) {
                i += elsperword;
                continue;
            }
        }
        if (w & maskp) return i;
        w >>= bitsperel;
        i++;
        if (++im == elsperword) im = 0;
    }
    return len+1;
}

static INLINE Int CVEC_Firstnzq(Obj fi, Word *v, Int len, Int wordlen)
/* Returns the index of the first non-zero element in the vector or 0,
 * if the vector is equal to zero. This is for extension fields. */
{
    PREPARE_epw(fi);
    PREPARE_bpe(fi);
    PREPARE_d(fi);
    register Word *p = v;
    register Int i = 0;
    register Int im = 0;

    /* First look for the first non-vanishing word: */
    im = wordlen;
    while (*p == 0 && i < im) { p++; i++; }
    if (i >= im) return len+1;   /* Vector is zero */

    /* Go back to beginning of the d Words: */
    im = i % d;
    p -= im;
    i = ((i-im) / d) * elsperword + 1;
    {
        register PREPARE_maskp(fi);
        while (1) {
            for (im = d-1;im >= 0;im--) if (p[im] & maskp) return i;
            maskp <<= bitsperel;
            i++;
        }
    }
    /* Never reached: */
    return 0;
}

static INLINE Int CVEC_Lastnzp(Obj fi, Word *v, Int len)
/* Returns the index of the last non-zero element in the vector or 0
 * if the vector is equal to zero. This is only for prime fields. */
{
    PREPARE_epw(fi);
    PREPARE_bpe(fi);
    PREPARE_maskp(fi);
    Int i = len-1;   /* code used to be zero based */
    Word *p = v + i / elsperword;
    register Word w = *p--;
    register Word y = maskp << (bitsperel * (i % elsperword));
    if (w == 0) {
        i = i - i % elsperword - 1;
        y = maskp << (bitsperel * (elsperword-1));
        w = *p--;
    }
    /* Quickly step over zeros: */
    while (i >= 0 && w == 0) {
        i -= elsperword;
        w = *p--;
    }
    while (i >= 0) {
        if ((y & w) != 0) return i+1;   /* we use one based convention */
        y >>= bitsperel;
        if (i % elsperword == 0) {
            w = *p--;
            y = maskp << (bitsperel * (elsperword-1));
        }
        i--;
    }
    return 0;
}
    
static INLINE Int CVEC_Lastnzq(Obj fi, Word *v, Int len, Int wordlen)
/* Returns the index of the last non-zero element in the vector or 0,
 * if the vector is equal to zero. This is for extension fields. */
{
    register PREPARE_maskp(fi);
    PREPARE_epw(fi);
    PREPARE_bpe(fi);
    PREPARE_d(fi);
    register Word *p;
    register Int i;
    register Int im;
    register Word mask;

    /* First look for the first non-vanishing word: */
    i = wordlen-1;
    p = v + i;  /* The last word */
    while (*p == 0 && i >= 0) { p--; i--; }
    if (i < 0) return 0;   /* Vector is zero */

    /* Go back to beginning of the d Words: */
    im = i % d;
    p -= im;
    i = ((i-im) / d) * elsperword + elsperword - 1;
    mask = maskp << ((elsperword-1) * bitsperel);
    while (1) {
        for (im = d-1;im >= 0;im--) if (p[im] & mask) return i+1;
        mask >>= bitsperel;
        i--;
    }
    /* Never reached: */
    return 0;
} 


  /****************************************/
 /* Arithmetic for finite field scalars: */
/****************************************/

static INLINE Int invert_modp(Int s,Int p)
{
    /* This is a standard extended Euclidean algorithm for p and s.
     * We start with x:=p and y:=s and assume p>s>0. We always keep
     * a,a',b,b' such that x = a'*p+a*s and y = b'*p+b*s.
     * As we are only interested in b at the time when y divides x,
     * we do not bother to calculate a' and b'. 
     * The function returns the result between 1 and p-1. */
    ldiv_t qr;
    register Int a = 0;
    register Int b = 1;
    register Int c;
    register Int x = p;
    register Int y = s;
    while (1) {
        qr = ldiv(x,y);
        if (!qr.rem) {
            if (b < 0) return b+p;
            else       return b;
        }
        x = y;
        y = qr.rem;
        c = a-qr.quot*b;
        a = b;
        b = c;
    }
    return 0;   /* Never reached */
}

static INLINE Int mulmodp(Int a, Int b, Int p)
{
    return (Int)( (((long long)a) * b) % p);
}

/* Now some functions to put vector arithmetic up to the GAP level, here 
 * is an overview. Note that scalar multiplication with non-
 * prime-field values is implemented only here!             
 * For all of the following functions u,v, and w must be vectors over the
 * same field of equal length, already allocated:
 *   CVEC.ADD2(u,v,fr,to)       does u += v
 *   CVEC.ADD3(u,v,w)           does u = v+w
 *   CVEC.MUL1(v,s,fr,to)       does v *= s
 *   CVEC.MUL2(u,v,s)           does u = v*s
 *   CVEC.ADDMUL(u,v,s,fr,to)   does u += v*s
 * They all return nothing. Scalars s can be immediate integers or finite
 * field elements where appropriate. fr and to are hints, that all elements
 * outside the range [fr..to] in v are known to be zero, such that operations
 * can be left undone to save CPU time. The functions round fr and to to
 * word boundaries and apply the low level functions only within the bounds. 
 * The copying functions do not have this feature, because they have to
 * copy anyway. Both fr and to can be 0, which indicates 1 and length of
 * the vector respectively. */

static INLINE Int handle_hints(Obj cl, Obj fi, Obj fr, Obj to, 
                               Int *start, Int *end)
{
    Int st,en;
    PREPARE_epw(fi);
    PREPARE_d(fi);
    /* A return value of zero indicates failure. */
    if (!IS_INTOBJ(fr) || !IS_INTOBJ(to)) {
        return (Int) OurErrorBreakQuit(
                    "CVEC.handle_hints: fr and to must be immediate integers");
    }
    st = INT_INTOBJ(fr); 
    if (st == 0) st = 1;
    en = INT_INTOBJ(to); 
    if (en == 0) en = INT_INTOBJ(ELM_PLIST(cl,IDX_len));
    if (en == -1) en = 1;    /* a scalar! */
    *start = ((st-1) / elsperword) * d;
    *end = ((en+elsperword-1)/elsperword) * d;
    return 1;
}

STATIC Obj ADD2(Obj self, Obj u, Obj v,Obj fr, Obj to)
{
    if (!IS_CVEC(u) || !IS_CVEC(v)) {
        return OurErrorBreakQuit("CVEC.ADD2: no cvec");
    }
    {  /* The PREPAREs define new variables, so we want an extra block! */
        PREPARE_clfi(u,ucl,ufi);
        PREPARE_clfi(v,vcl,vfi);
        Int start,end;

        if (ufi != vfi || ELM_PLIST(ucl,IDX_len) != ELM_PLIST(vcl,IDX_len)) {
            return OurErrorBreakQuit(
                        "CVEC.ADD2: incompatible fields or lengths");
        }

        /* Handle hints: */
        if (!handle_hints(ucl,ufi,fr,to,&start,&end)) return 0L;

        ADD2_INL(DATA_CVEC(u)+start,DATA_CVEC(v)+start,ufi,end-start);
    }
    return 0L;
}

STATIC Obj ADD3(Obj self, Obj u, Obj v,Obj w)
{
    if (!IS_CVEC(u) || !IS_CVEC(v) || !IS_CVEC(w)) {
        return OurErrorBreakQuit("CVEC.ADD3: no cvec");
    }
    {  /* The PREPAREs define new variables, so we want an extra block! */
        PREPARE_clfi(u,ucl,ufi);
        PREPARE_clfi(v,vcl,vfi);
        PREPARE_clfi(w,wcl,wfi);

        if (ufi != vfi || vfi != wfi ||
            ELM_PLIST(ucl,IDX_len) != ELM_PLIST(vcl,IDX_len) ||
            ELM_PLIST(vcl,IDX_len) != ELM_PLIST(wcl,IDX_len)) {
            return OurErrorBreakQuit(
                        "CVEC.ADD3: incompatible fields or lengths");
        }
        ADD3_INL(DATA_CVEC(u),DATA_CVEC(v),DATA_CVEC(w),ufi,
             INT_INTOBJ(ELM_PLIST(ucl,IDX_wordlen)));
    }
    return 0L;
}

static INLINE Int *prepare_scalar(Obj fi, Obj s)
/* A NULL pointer indicates failure. */
{
    Int sc;
    PREPARE_p(fi);

    if (IS_FFE(s)) {
        PREPARE_tab1(fi);
        PREPARE_d(fi);
        PREPARE_q(fi);
        if (CHAR_FF(FLD_FFE(s)) == p && (d % DEGR_FF(FLD_FFE(s))) == 0) {
            if (VAL_FFE(s) == 0) {
                sc = 0;
            } else {
                sc = INT_INTOBJ(ELM_PLIST(tab1,
                         (VAL_FFE(s)-1)*((q-1)/(SIZE_FF(FLD_FFE(s))-1))+2));
            }
        } else {
            return (Int *) OurErrorBreakQuit(
                    "prepare_scalar: scalar from wrong field");
        }
    } else if (IS_INTOBJ(s)) {
        sc = INT_INTOBJ(s);
        /* goes on below, case distinction! */
    } else if (IS_PLIST(s)) {   /* Coefficients are either FFEs from the 
                                   prime field or integers < p */
        /* Note that we assume that we only see FFEs in such a list, if
         * p < 65536 < q, such that tab1 and tab2 are created, but for the
         * prime field for exactly this purpose here! */
        PREPARE_tab1(fi);
        PREPARE_d(fi);
        Int len = LEN_PLIST(s);
        Obj ss;
        sclen = 0;
        /* Note that the length can be 0 <= len <= d, which is <= MAXDEGREE */
        if (len > d) {
            return (Int *) OurErrorBreakQuit(
                    "prepare_scalar: coefficient list longer than d");
        }
        if (len == 0) {
            scbuf[0] = 0;
            sclen = 1;
            return scbuf;
        }
        while (sclen < len) {
            ss = ELM_PLIST(s,sclen+1);
            if (IS_INTOBJ(ss)) scbuf[sclen++] = INT_INTOBJ(ss);
            else if (IS_FFE(ss) && CHAR_FF(FLD_FFE(ss)) == p &&
                     DEGR_FF(FLD_FFE(ss)) == 1) {
                if (VAL_FFE(ss) == 0)
                    scbuf[sclen++] = 0L;
                else
                    scbuf[sclen++] = INT_INTOBJ(ELM_PLIST(tab1,VAL_FFE(ss)+1));
            } else {
                return (Int *) OurErrorBreakQuit(
                       "prepare_scalar: strange object in coefficient list");
            }
        }
        /* Find length of scalar: */
        for (/* nothing here */;sclen > 1 && scbuf[sclen-1] == 0;sclen--);
        return scbuf;
    } else {
        return (Int *) OurErrorBreakQuit(
                "CVEC.MUL*: strange object as scalar");
    }
    /* Now the scalar is in sc as integer between 0..q-1 */
    /* We write out the p-adic expansion into our buffer: */
    sclen = 0;  /* Length should be at least one. */
    do {
        scbuf[sclen++] = sc % p;
        sc /= p;
    } while(sc); 
    return scbuf;
}

STATIC INLINE void MUL1_INT(Obj u, Obj ucl, Obj ufi, Int d, Int *sc,
                            Int start, Int end)
/* This does the multiplication in place in the non-prime field case.
 * This is an internal function, called by MUL1 and possibly during
 * other primitive operations that are implemented in the kernel.
 * Note that this function is not exported to the GAP level and that
 * the global variable sclen must contain the length of the scalar. */
{
  register Word *vv;
  Int c = end-start;
  Int i;
  Int j;
  Int ss;
  register Word wo;
  Word *bb;
  PREPARE_cp(ufi);

  /* Now the ugly case involving conway polynomials: */
  for (i = 0,vv = DATA_CVEC(u)+start;i < c;i += d,vv += d) {
      /* Do one chunk of elsperword elements from F_q: */

      ss = 0;  /* This counts the nonzero entries in the scalar */

      /* Make one copy for further processing: */
      for (j = d,bb = buf;j > 0;j--) *bb++ = *vv++; 
      vv -= d;  /* Go back to beginning. */
      /* Now handle prime field component: */
      MUL2_INL(vv,buf,ufi,*sc,d);
      while (++ss < sclen) {
          /* Now we have to multiply the content of the buffer by the 
           * polynomial x modulo the conway polynomial. This means
           * shifting the Words in the buffer one up and multiplying
           * the Word falling out by the conway polynomial. We do that
           * now. */
          wo = buf[d - 1];   /* Keep this one */
          for (j = d - 1; j > 0; j--) buf[j] = buf[j-1];
          buf[0] = 0UL;
          for (j = 0,bb = buf;j < d;j++,bb++) {
              *bb = ADDMUL1_INL(*bb,wo,ufi,cp[j]);
          }
          /* Now add a multiple of that to the result: */
          ADDMUL_INL(vv,buf,ufi,sc[ss],d);
      }
  } 
}

STATIC Obj MUL1(Obj self, Obj u, Obj s, Obj fr, Obj to)
{
    if (!IS_CVEC(u)) {
        return OurErrorBreakQuit("CVEC.MUL1: no cvec");
    }
    {  /* The PREPAREs define new variables, so we want an extra block! */
        PREPARE_clfi(u,ucl,ufi);
        PREPARE_d(ufi);
        Int *sc;
        Int start,end;

        /* Now handle the scalar: */
        sc = prepare_scalar(ufi,s); if (!sc) return 0L;
        
        /* Handle hints: */
        if (!handle_hints(ucl,ufi,fr,to,&start,&end)) return 0L;
            
        if (sclen == 1) {  /* Good luck, scalar is in prime field! */
            MUL_INL(DATA_CVEC(u)+start,ufi,*sc,end-start);
            return 0L;
        }
        MUL1_INT(u,ucl,ufi,d,sc,start,end);
    }
    return 0L;
}

STATIC INLINE void MUL2_INT(Obj u, Obj ucl, Obj ufi, Obj v, 
                            Int d, Int wordlen, Int *sc)
/* This does the multiplication with result somewhere else in the non-prime 
 * field case.
 * This is an internal function, called by MUL2 and possibly during
 * other primitive operations that are implemented in the kernel.
 * Note that this function is not exported to the GAP level and that
 * the global variable sclen must contain the length of the scalar. */
{
  register Word *vv;
  register Word *uu;
  Int i;
  Int j;
  Int ss;
  register Word wo;
  Word *bb;
  PREPARE_cp(ufi);

  /* Now the ugly case involving conway polynomials: */
  for (i = 0,uu = DATA_CVEC(u),vv = DATA_CVEC(v);i < wordlen;
       i += d,uu += d) {
      /* Do one chunk of elsperword elements from F_q: */

      ss = 0;  /* This counts the nonzero entries in the scalar */

      /* Make one copy for further processing: */
      for (j = d,bb = buf;j > 0;j--) *bb++ = *vv++; 
      /* Now handle prime field component: */
      MUL2_INL(uu,buf,ufi,*sc,d);
      while (++ss < sclen) {
          /* Now we have to multiply the content of the buffer by the 
           * polynomial x modulo the conway polynomial. This means
           * shifting the Words in the buffer one up and multiplying
           * the Word falling out by the conway polynomial. We do that
           * now. */
          wo = buf[d - 1];   /* Keep this one */
          for (j = d - 1; j > 0; j--) buf[j] = buf[j-1];
          buf[0] = 0UL;
          for (j = 0,bb = buf;j < d;j++,bb++) {
              *bb = ADDMUL1_INL(*bb,wo,ufi,cp[j]);
          }
          /* Now add a multiple of that to the result: */
          ADDMUL_INL(uu,buf,ufi,sc[ss],d);
      }
  } 
}

STATIC Obj MUL2(Obj self, Obj u, Obj v, Obj s, Obj fr, Obj to)
{
    if (!IS_CVEC(u) || !IS_CVEC(v)) {
        return OurErrorBreakQuit("CVEC.MUL1: no cvec");
    }
    {  /* The PREPAREs define new variables, so we want an extra block! */
        PREPARE_clfi(u,ucl,ufi);
        PREPARE_d(ufi);
        PREPARE_clfi(v,vcl,vfi);
        Int wordlen = INT_INTOBJ(ELM_PLIST(ucl,IDX_wordlen));
        
        Int *sc;

        /* Check fields and lengths: */
        if (ufi != vfi || 
            ELM_PLIST(ucl,IDX_len) != ELM_PLIST(vcl,IDX_len)) {
            return OurErrorBreakQuit(
                        "CVEC.MUL2: incompatible fields or lengths");
        }
        
        /* Now handle the scalar: */
        sc = prepare_scalar(ufi,s); if (!sc) return 0L;
        
        if (sclen == 1) {  /* Good luck, scalar is in prime field! */
            MUL2_INL(DATA_CVEC(u),DATA_CVEC(v),ufi,*sc,wordlen);
            return 0L;
        }
        MUL2_INT(u,ucl,ufi,v,d,wordlen,sc);
    }
    return 0L;
}

STATIC INLINE void ADDMUL_INT(Obj u, Obj ucl, Obj ufi, Obj v,
                              Int d, Int *sc, Int start, Int end)
/* This does the multiplication plus addition to something else in the 
 * non-prime field case.
 * This is an internal function, called by ADDMUL and possibly during
 * other primitive operations that are implemented in the kernel.
 * Note that this function is not exported to the GAP level and that
 * the global variable sclen must contain the length of the scalar. */
{
  register Word *uu;
  register Word *vv;
  Int c = end-start;
  Int i;
  Int j;
  Int ss;
  register Word wo;
  Word *bb;
  PREPARE_cp(ufi);

  /* Now the ugly case involving conway polynomials: */
  for (i = 0,uu = DATA_CVEC(u)+start,vv = DATA_CVEC(v)+start;
       i < c;i += d,uu += d) {
      /* Do one chunk of elsperword elements from F_q: */

      ss = 0;  /* This counts the nonzero entries in the scalar */

      /* Make one copy for further processing: */
      for (j = d,bb = buf;j > 0;j--) *bb++ = *vv++; 
      /* Now handle prime field component: */
      ADDMUL_INL(uu,buf,ufi,*sc,d);
      while (++ss < sclen) {
          /* Now we have to multiply the content of the buffer by the 
           * polynomial x modulo the conway polynomial. This means
           * shifting the Words in the buffer one up and multiplying
           * the Word falling out by the conway polynomial. We do that
           * now. */
          wo = buf[d - 1];   /* Keep this one */
          for (j = d - 1; j > 0; j--) buf[j] = buf[j-1];
          buf[0] = 0UL;
          for (j = 0,bb = buf;j < d;j++,bb++) {
              *bb = ADDMUL1_INL(*bb,wo,ufi,cp[j]);
          }
          /* Now add a multiple of that to the result: */
          ADDMUL_INL(uu,buf,ufi,sc[ss],d);
      }
  } 
}

STATIC Obj ADDMUL(Obj self, Obj u, Obj v, Obj s, Obj fr, Obj to)
{
    if (!IS_CVEC(u) || !IS_CVEC(v)) {
        return OurErrorBreakQuit("CVEC.ADDMUL: no cvec");
    }
    {  /* The PREPAREs define new variables, so we want an extra block! */
        PREPARE_clfi(u,ucl,ufi);
        PREPARE_d(ufi);
        PREPARE_clfi(v,vcl,vfi);
        Int *sc;
        Int start,end;

        /* Check fields and lengths: */
        if (ufi != vfi || 
            ELM_PLIST(ucl,IDX_len) != ELM_PLIST(vcl,IDX_len)) {
            return OurErrorBreakQuit(
                        "CVEC.ADDMUL: incompatible fields or lengths");
        }
        
        /* Now handle the scalar: */
        sc = prepare_scalar(ufi,s); if (!sc) return 0L;
        
        /* Handle hints: */
        if (!handle_hints(ucl,ufi,fr,to,&start,&end)) return 0L;
            
        if (sclen == 1) {  /* Good luck, scalar is in prime field! */
            ADDMUL_INL(DATA_CVEC(u)+start,DATA_CVEC(v)+start,ufi,*sc,end-start);
            return 0L;
        }
        ADDMUL_INT(u,ucl,ufi,v,d,sc,start,end);
    }
    return 0L;
}

STATIC Obj ASS_CVEC(Obj self, Obj v, Obj pos, Obj s)
{
    Int i;
    Int *sc;
    if (!IS_CVEC(v)) {
        return OurErrorBreakQuit("CVEC.ASS_CVEC: no cvec");
    }
    if (!IS_INTOBJ(pos)) {
        return OurErrorBreakQuit("CVEC.ASS_CVEC: no integer");
    }
    i = INT_INTOBJ(pos);
    {
        PREPARE_clfi(v,cl,fi);
        PREPARE_d(fi);
        Int j;

        /* Check bounds: */
        if (i < 1 || i > INT_INTOBJ(ELM_PLIST(cl,IDX_len))) {
            return OurErrorBreakQuit("CVEC.ASS_CVEC: out of bounds");
        }

        /* Now handle the scalar: */
        sc = prepare_scalar(fi,s); if (!sc) return 0L;
        
        /* Fill unused space: */
        for (j = sclen;j < d;scbuf[j++] = 0) ;
         
        if (d == 1)
            CVEC_AssItemp(fi, DATA_CVEC(v), i, (Word) (*sc));
        else
            CVEC_AssItemq(fi, DATA_CVEC(v), i, sc);
    }
    return 0L;
}

STATIC Obj ELM_CVEC(Obj self, Obj v, Obj pos)
{
    Int i;
    if (!IS_CVEC(v)) {
        return OurErrorBreakQuit("CVEC.ELM_CVEC: no cvec");
    }
    if (!IS_INTOBJ(pos)) {
        return OurErrorBreakQuit("CVEC.ELM_CVEC: no integer");
    }
    i = INT_INTOBJ(pos);
    {
        /* The following are all pointers to masterpointers and thus
         * survive a garbage collection: */
        PREPARE_clfi(v,cl,fi);
        PREPARE_p(fi);
        PREPARE_d(fi);
        PREPARE_tab2(fi);
        Int size = INT_INTOBJ(ELM_PLIST(fi,IDX_size));
        Int s;
        Obj sca;

        /* Check bounds: */
        if (i < 1 || i > INT_INTOBJ(ELM_PLIST(cl,IDX_len))) {
            return OurErrorBreakQuit("CVEC.ELM_CVEC: out of bounds");
        }

        if (size >= 1 && d > 1) {  /* The field has more than 65536 elements */
            /* Let's allocate a new scalar first: */
            /* GARBAGE COLLECTION POSSIBLE */
            sca = NEW_PLIST( T_PLIST, d );
            SET_LEN_PLIST( sca, d );
            /* Here, a garbage collection might occur, however, all our
             * variables survive this, as they are pointers to master
             * pointers! */
        } else sca = 0L;  /* just to please the compiler */

        if (d == 1) {
            s = CVEC_Itemp(fi, DATA_CVEC(v), i);
            if (p < 65536)    /* we do GAP FFEs */
                return ELM_PLIST(tab2,s+1);
            else
                return INTOBJ_INT(s);
        } else {
            CVEC_Itemq(fi, DATA_CVEC(v), i);
            if (size == 0) {
                register Int i;
                for (s = 0,i = d-1;i >= 0;i--) s = s * p + scbuf[i];
                return ELM_PLIST(tab2,s+1);
            } else {
                if (p < 65536) {
                    for (i = 0;i < d;i++)
                        SET_ELM_PLIST(sca, i+1, ELM_PLIST(tab2,scbuf[i]+1));
                } else {
                    for (i = 0;i < d;i++)
                        SET_ELM_PLIST(sca, i+1, INTOBJ_INT(scbuf[i]));
                }
                return sca;
            }
        }
    }
    return 0L;
}

STATIC Obj POSITION_NONZERO_CVEC(Obj self, Obj v)
{
    if (!IS_CVEC(v)) {
        return OurErrorBreakQuit("CVEC.POSITION_NONZERO_CVEC: no cvec");
    }
    {
        PREPARE_clfi(v,cl,fi);
        PREPARE_d(fi);
        if (d == 1) {
            return INTOBJ_INT(CVEC_Firstnzp(fi,DATA_CVEC(v),
                                      INT_INTOBJ(ELM_PLIST(cl,IDX_len))));
        } else {
            return INTOBJ_INT(CVEC_Firstnzq(fi,DATA_CVEC(v),
                                      INT_INTOBJ(ELM_PLIST(cl,IDX_len)),
                                      INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen))));
        }
    }
}

STATIC Obj POSITION_LAST_NONZERO_CVEC(Obj self, Obj v)
{
    if (!IS_CVEC(v)) {
        return OurErrorBreakQuit("CVEC.POSITION_LAST_NONZERO_CVEC: no cvec");
    }
    {
        PREPARE_clfi(v,cl,fi);
        PREPARE_d(fi);
        if (d == 1) {
            return INTOBJ_INT(CVEC_Lastnzp(fi,DATA_CVEC(v),
                                      INT_INTOBJ(ELM_PLIST(cl,IDX_len))));
        } else {
            return INTOBJ_INT(CVEC_Lastnzq(fi,DATA_CVEC(v),
                                      INT_INTOBJ(ELM_PLIST(cl,IDX_len)),
                                      INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen))));
        }
    }
}
    
STATIC Obj CVEC_LT(Obj self, Obj u, Obj v)
{
    if (!IS_CVEC(u) || !IS_CVEC(v)) {
        return OurErrorBreakQuit("CVEC.CVEC_LT: no cvecs");
    }
    {  /* The PREPAREs define new variables, so we want an extra block! */
        register Int wordlen;
        register Word *p1;
        register Word *p2;
        PREPARE_clfi(u,ucl,ufi);
        PREPARE_clfi(v,vcl,vfi);

        /* Check fields and lengths: */
        if (ufi != vfi || 
            ELM_PLIST(ucl,IDX_len) != ELM_PLIST(vcl,IDX_len)) {
            return OurErrorBreakQuit(
                        "CVEC.CVEC_LT: incompatible fields or lengths");
        }
        wordlen = INT_INTOBJ(ELM_PLIST(ucl,IDX_wordlen));
        p1 = DATA_CVEC(u);
        p2 = DATA_CVEC(v);
        while (wordlen > 0) {
            if (*p1 < *p2) return True;
            else if (*p1 > *p2) return False;
            p1++; p2++; wordlen--;
        }
        return False;
    }
    /* Never reached: */
    return 0L;
}

STATIC Obj CVEC_EQ(Obj self, Obj u, Obj v)
{
    if (!IS_CVEC(u) || !IS_CVEC(v)) {
        return OurErrorBreakQuit("CVEC.CVEC_EQ: no cvecs");
    }
    {  /* The PREPAREs define new variables, so we want an extra block! */
        register Int wordlen;
        register Word *p1;
        register Word *p2;
        PREPARE_clfi(u,ucl,ufi);
        PREPARE_clfi(v,vcl,vfi);

        /* Check fields and lengths: */
        if (ufi != vfi || 
            ELM_PLIST(ucl,IDX_len) != ELM_PLIST(vcl,IDX_len)) {
            return OurErrorBreakQuit(
                        "CVEC.CVEC_EQ: incompatible fields or lengths");
        }
        wordlen = INT_INTOBJ(ELM_PLIST(ucl,IDX_wordlen));
        p1 = DATA_CVEC(u);
        p2 = DATA_CVEC(v);
        while (wordlen > 0) {
            if (*p1 != *p2) return False;
            p1++; p2++; wordlen--;
        }
        return True;
    }
    /* Never reached: */
    return 0L;
}

STATIC Obj CVEC_ISZERO(Obj self, Obj u)
{
    if (!IS_CVEC(u)) {
        return OurErrorBreakQuit("CVEC.CVEC_EQ: no cvec");
    }
    {  /* The PREPAREs define new variables, so we want an extra block! */
        register Int wordlen;
        register Word *p;
        PREPARE_cl(u,ucl);

        wordlen = INT_INTOBJ(ELM_PLIST(ucl,IDX_wordlen));
        p = DATA_CVEC(u);
        while (wordlen > 0) {
            if (*p != 0) return False;
            p++; wordlen--;
        }
        return True;
    }
    /* Never reached: */
    return 0L;
}

STATIC Obj EXTRACT(Obj self, Obj v, Obj ii, Obj ll)
/* Extracts ll field elements from the vector self at position ii into
 * one Word in a convenient way, fitting to FILL_GREASE_TAB.
 * Here is an example with l = 3, d = 2:
 * (on a potential machine with 25 bits wide Words   :-) )
 * |-|---|---|---|333|222|111|---|---| lower memory addresses   ^
 * |-|---|---|---|666|555|444|---|---| higher memory addresses  V
 * ==>
 * |-|---|---|666|555|444|333|222|111|
 * Here is an example where i is such that not all field elements are in
 * the same word:
 * |-|222|111|---|---|---|---|---|---| lower memory addresses   ^
 * |-|555|444|---|---|---|---|---|---|
 * |-|---|---|---|---|---|---|---|333|
 * |-|---|---|---|---|---|---|---|666| higher memory addresses  V
 * ==> 
 * |-|---|---|666|555|444|333|222|111| 
 * Note that 111 and 444 encode the coefficients of the leftmost extension
 * field element in the vector, 222 and 555 the next one and 333 and 666
 * the third. 
 */ 
{
    /* No checks here, because performance is mission critical! */ 
    PREPARE_clfi(v,cl,fi);
    PREPARE_bpe(fi);
    PREPARE_epw(fi);
    PREPARE_d(fi);
    Int overflow = 0;      /* Set to 1 if we read over the end of the vector */
    Int i = INT_INTOBJ(ii)-1; /* we are 1-based in GAP, here we want 0-based */
    Int l = INT_INTOBJ(ll);
    Word res = 0UL;
    Word *p = DATA_CVEC(v) + (i / elsperword) * d;
    Int rest = i % elsperword;
    Int wordlen = INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen));

    if (((i+l-1)/elsperword)*d >= wordlen) overflow = 1;
    /* In that case we do not look over the last word, fortunately, this
     * can only happen in the ugly cases and we only have to skip the
     * second step. */

    /* First the prime field case: */
    if (d == 1) {
        /* First decide, whether we are in the simple or the ugly case: */
        if (rest + l <= elsperword) {
            /* Good luck, everything is in the same word! */
            Int s1 = rest * bitsperel;
            Word mask1 = (1UL << (l * bitsperel)) - 1UL;
            res = (*p >> s1) & mask1;
        } else {
            /* Urgh! Field elements are distributed among two Words! */
            Int nrinfirstword = elsperword - i % elsperword;
            Int s1 = rest * bitsperel;
            Word mask1 = (1UL << (bitsperel * nrinfirstword)) - 1UL;
            Int s2 = nrinfirstword * bitsperel;
            Word mask2 = (1UL << (bitsperel * (l-nrinfirstword))) - 1UL;
            if (overflow)
                res = (p[0] >> s1) & mask1;
            else
                res = ((p[0] >> s1) & mask1) | ((p[1] & mask2) << s2);
        }
    } else {   /* Extension field case: */
        int k;
        /* First decide, whether we are in the simple or the ugly case: */
        if (rest + l <= elsperword) {
            /* Good luck, everything is in the same word! */
            Int pos = 0;
            Int inc = l * bitsperel;
            Int s1 = rest * bitsperel;
            Word mask1 = (1UL << inc) - 1UL;
            for (k = d;k > 0;k--) {
                res |= ((*p++ >> s1) & mask1) << pos;
                pos += inc;
            }
        } else {
            /* Urgh! Field elements are distributed among two Words! */
            Int inc = l * bitsperel;
            Int pos = 0;
            Int nrinfirstword = elsperword - i % elsperword;
            Int s1 = rest * bitsperel;
            Word mask1 = (1UL << (bitsperel * nrinfirstword)) - 1UL;
            Int s2 = nrinfirstword * bitsperel;
            Word mask2 = (1UL << (bitsperel * (l-nrinfirstword))) - 1UL;
            if (overflow) {
                for (k = d;k > 0;k--) {
                    res |= ((*p++ >> s1) & mask1) << pos;
                    pos += inc;
                }
            } else {
                Word *q = p + d;
                for (k = d;k > 0;k--) {
                    res |= (((*p++ >> s1) & mask1) | ((*q++ & mask2) << s2)) 
                           << pos;
                    pos += inc;
                }
            }
        }
    }
    return INTOBJ_INT( (Int) res );
}

/* The following routines do the same as EXTRACT, but more efficient,
 * if one needs many similar lookups. We separate initialization and lookup. */

static Int VecEx_d;
static Int VecEx_inc;
static Int VecEx_offset;
static Int VecEx_rest;
static Int VecEx_s1, VecEx_s2;
static Word VecEx_mask1, VecEx_mask2;
static Int VecEx_overflow;  /* see EXTRACT */

static Word (*Vector_Extract_Worker)(Word *data);
/* Call this for repeated lookup. */

static Word VecEx_Worker_prime_simple(Word *data)
/* Extraction worker for prime fields in the simple case. */
{
    register Word *p = data + VecEx_offset;
    return (*p >> VecEx_s1) & VecEx_mask1;
}

static Word VecEx_Worker_ext_simple(Word *data)
/* Extraction worker for extension fields in the simple case. */
{
    register Word res = 0;
    register Word *p = data + VecEx_offset;
    register Int pos = 0;
    register Int k;
    for (k = VecEx_d;k > 0;k--) {
        res |= ((*p++ >> VecEx_s1) & VecEx_mask1) << pos;
        pos += VecEx_inc;
    }
    return res;
}

static Word VecEx_Worker_prime_bad(Word *data)
/* Extraction worker for prime fields in the bad case. */
{
    register Word *p = data + VecEx_offset;
    if (VecEx_overflow)
        return (p[0] >> VecEx_s1) & VecEx_mask1;
    else
        return ((p[0] >> VecEx_s1) & VecEx_mask1) | 
               ((p[1] & VecEx_mask2) << VecEx_s2);
}

static Word VecEx_Worker_ext_bad(Word *data)
/* Extraction worker for extension fields in the bad case. */
{
    register Word res = 0;
    register Word *p = data + VecEx_offset;
    register Int pos = 0;
    register Int k;
    if (VecEx_overflow) {
        for (k = VecEx_d;k > 0;k--) {
            res |= ((*p++ >> VecEx_s1) & VecEx_mask1) << pos;
            pos += VecEx_inc;
        }
    } else {
        register Word *q = p + VecEx_d;
        for (k = VecEx_d;k > 0;k--) {
            res |= (((*p++ >> VecEx_s1) & VecEx_mask1) |
                    ((*q++ & VecEx_mask2) << VecEx_s2)) << pos;
            pos += VecEx_inc;
        }
    }
    return res;
}

STATIC Obj EXTRACT_INIT(Obj self, Obj v, Obj ii, Obj ll)
/* See comment of EXTRACT. This initializes the extraction routines.
 * Use Vector_Extract_Worker(Word *data) afterwards. */
{
    PREPARE_clfi(v,cl,fi);
    PREPARE_bpe(fi);
    PREPARE_epw(fi);
    PREPARE_d(fi);
    Int i = INT_INTOBJ(ii)-1;  /* 0 based from here */
    Int l = INT_INTOBJ(ll);
    Int rest = i % elsperword;
    Int wordlen = INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen));

    if (((i+l-1)/elsperword)*d >= wordlen) 
        VecEx_overflow = 1;
        /* In that case we do not look over the last word, fortunately, this
         * can only happen in the ugly cases and we only have to skip the
         * second step. */
    else
        VecEx_overflow = 0; 

    /* Some global static things to remember: */
    VecEx_d = d;
    VecEx_rest = rest;

    /* First the prime field case: */
    if (d == 1) {
        /* First decide, whether we are in the simple or the ugly case: */
        if (rest + l <= elsperword) {
            /* Good luck, everything is in the same word! */
            VecEx_s1 = rest * bitsperel;
            VecEx_mask1 = (1UL << (l * bitsperel)) - 1UL;
            VecEx_offset = i / elsperword;
            Vector_Extract_Worker = VecEx_Worker_prime_simple;
        } else {
            /* Urgh! Field elements are distributed among two Words! */
            int nrinfirstword = elsperword - i % elsperword;
            VecEx_s1 = rest * bitsperel;
            VecEx_mask1 = (1UL << (bitsperel * nrinfirstword)) - 1UL;
            VecEx_s2 = nrinfirstword * bitsperel;
            VecEx_mask2 = (1UL << (bitsperel * (l-nrinfirstword))) - 1UL;
            VecEx_offset = i / elsperword;
            Vector_Extract_Worker = VecEx_Worker_prime_bad;
        }
    } else {   /* Extension field case: */
        /* First decide, whether we are in the simple or the ugly case: */
        if (rest + l <= elsperword) {
            /* Good luck, everything is in the same word! */
            VecEx_inc = bitsperel * l;
            VecEx_s1 = rest * bitsperel;
            VecEx_mask1 = (1UL << (l * bitsperel)) - 1UL;
            VecEx_offset = (i / elsperword) * d;
            Vector_Extract_Worker = VecEx_Worker_ext_simple;
        } else {
            /* Urgh! Field elements are distributed among two Words! */
            int nrinfirstword = elsperword - rest;
            VecEx_inc = l * bitsperel;
            VecEx_s1 = rest * bitsperel;
            VecEx_mask1 = (1UL << (bitsperel * nrinfirstword)) - 1UL;
            VecEx_s2 = nrinfirstword * bitsperel;
            VecEx_mask2 = (1UL << (bitsperel * (l-nrinfirstword))) - 1UL;
            VecEx_offset = (i / elsperword) * d;
            Vector_Extract_Worker = VecEx_Worker_ext_bad;
        }
    }
    return 0L;  /* return nothing */
}

STATIC Obj EXTRACT_DOIT(Obj self, Obj v)
{
    /* Dereference the function pointer and call the worker routine: */
    return INTOBJ_INT( (Int) ( (*Vector_Extract_Worker)(DATA_CVEC(v)) ) );
}

STATIC Obj FILL_GREASE_TAB(Obj self, Obj li, Obj i, Obj l, Obj tab, Obj tablen,
                          Obj offset)
/* This function does the precalculation for greasing. This is the internal
 * version to be called from GAP. tab must already be long enough, no
 * checks are done. "Long enough" means that there must be room for
 * all pre-computed linear combinations and for two more vectors, used
 * during the calculation. 
 * 
 * li     is a plist of vectors
 * i      is the start index in li
 * l      is the grease level 
 * tablen is the length of the tab to fill here
 * offset is the first index in tab used 
 * tab    is a plist to cache the linear combinations, length must already
 *        be long enough, such that from offset on there is room for
 *        tablen+2 vectors, all those places must be filled with vectors
 * 
 * of course, all vectors must be prepared and be compatible. */
{
    Int j;          /* A counter */
    Int jj;         /* Another one */
    Int k,kk,kkk;   /* Further small counters */
    Obj v = ELM_PLIST(li,INT_INTOBJ(i));  /* one of the vectors */
    PREPARE_clfi(v,cl,fi);
    PREPARE_p(fi);
    PREPARE_d(fi);
    Obj w,u,x,y;
    Int len;
    Int po;
    Int wordlen = INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen));
    Int offs = INT_INTOBJ(offset);

    /* First put the zero vector into the tab at the beginning: */
    w = ELM_PLIST(tab,offs);
    memset(DATA_CVEC(ELM_PLIST(tab,offs)),0,sizeof(Word)*wordlen);

    /* We have two more vectors for intermediate results: */
    w = ELM_PLIST(tab,offs+INT_INTOBJ(tablen));
    u = ELM_PLIST(tab,offs+INT_INTOBJ(tablen)+1);

    len = 1;  /* Current length of vector list */
    for (k = 0,po = 1;k < d;k++,po *= p) {
        for (kk = 0;kk < INT_INTOBJ(l);kk++) {
            if (INT_INTOBJ(i)+kk > LEN_PLIST(li))
                /* Take the zero vector: */
                v = ELM_PLIST(tab,offs);
            else
                v = ELM_PLIST(li,INT_INTOBJ(i)+kk);
            memcpy(DATA_CVEC(w),DATA_CVEC(v),sizeof(Word)*wordlen);
            MUL1(self,w,INTOBJ_INT(po),INTOBJ_INT(0),INTOBJ_INT(0));
            memcpy(DATA_CVEC(u),DATA_CVEC(w),sizeof(Word)*wordlen);
            jj = len;
            for (kkk = p-1;kkk > 0;kkk--) {
                for (j = 0;j < len;j++) {
                    x = ELM_PLIST(tab,offs + jj++);
                    y = ELM_PLIST(tab,offs + j);
                    ADD3_INL(DATA_CVEC(x),DATA_CVEC(u),DATA_CVEC(y),fi,wordlen);
                }
                if (kkk > 0) ADD2_INL(DATA_CVEC(u),DATA_CVEC(w),fi,wordlen);
            }
            len = jj;
        }
    }
    return 0L;
}

STATIC Obj PROD_CVEC_CMAT_NOGREASE(Obj self, Obj u, Obj v, Obj m)
/* Note that m is the list of vectors with first component unbound. */
{
    PREPARE_clfi(u,ucl,ufi);
    PREPARE_cl(v,vcl);
    PREPARE_d(ufi);
    Int k = INT_INTOBJ(ELM_PLIST(vcl,IDX_len));
    Int wordlen = INT_INTOBJ(ELM_PLIST(ucl,IDX_wordlen));
    Word *uu = DATA_CVEC(u);
    Word *vv = DATA_CVEC(v);
    register Int i;

    if (d == 1) {
        Int s;
        for (i = 1;i <= k;i++) {
            s = CVEC_Itemp(ufi,vv,i);
            if (s) ADDMUL_INL(uu,DATA_CVEC(ELM_PLIST(m,i+1)),ufi,s,wordlen);
        }
    } else {   /* d > 1 */
        for (i = 1;i <= k;i++) {
            CVEC_Itemq(ufi,vv,i);
            if (sclen != 1 || scbuf[0] != 0) 
                ADDMUL_INT(u, ucl, ufi, ELM_PLIST(m,i+1), d, scbuf, 0, wordlen);
        }
    }
    return 0L;
}

STATIC Obj PROD_CVEC_CMAT_GREASED(Obj self, Obj u, Obj v, Obj mgreasetab,
                                  Obj spreadtab, Obj glev)
{
    PREPARE_clfi(u,ucl,ufi);
    PREPARE_cl(v,vcl);
    Int k = INT_INTOBJ(ELM_PLIST(vcl,IDX_len));
    Int lev = INT_INTOBJ(glev);
    Int wordlen = INT_INTOBJ(ELM_PLIST(ucl,IDX_wordlen));
    Word *uu = DATA_CVEC(u);
    register Int i;
    register Int pos;
    register Obj w;
    register Word val;

    for (i = 1,pos = 1;pos <= k;pos += lev,i++) {
        val = INT_INTOBJ(EXTRACT(self, v, INTOBJ_INT(pos), glev));
        if (val != 0) {
            val = INT_INTOBJ(ELM_PLIST(spreadtab,val+1));
            w = ELM_PLIST(ELM_PLIST(mgreasetab,i),val);
            ADD2_INL(uu,DATA_CVEC(w),ufi,wordlen);
        }
    }
    return 0;
}

STATIC Obj PROD_CMAT_CMAT_GREASED(Obj self, Obj l, Obj m, Obj ngreasetab, 
                                  Obj spreadtab, Obj len, Obj glev)
{  /* See mult. routine "for two cmats, second one greased" in cvec.gi */
    Int k = INT_INTOBJ(len);
    Int t = LEN_PLIST(l)-1;
    Int lev = INT_INTOBJ(glev);
    Int pos;
    Int i;
    Int j;
    Int val;
    Obj v,w;

    v = ELM_PLIST(l,2);  /* we know that the result is not empty */
    {
        PREPARE_clfi(v,cl,fi);
        Int wordlen = INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen));
        for (i = 1,pos = 1;pos <= k;pos += lev,i++) {
            EXTRACT_INIT(self,ELM_PLIST(m,2),INTOBJ_INT(pos),glev);
            for (j = 2;j <= t+1;j++) {
                val = (*Vector_Extract_Worker)(DATA_CVEC(ELM_PLIST(m,j)));
                if (val != 0) {
                    val = INT_INTOBJ(ELM_PLIST(spreadtab,val+1));
                    v = ELM_PLIST(l,j);
                    w = ELM_PLIST(ELM_PLIST(ngreasetab,i),val);
                    ADD2_INL(DATA_CVEC(v),DATA_CVEC(w),fi,wordlen);
                }
            }
        }
    }
    return 0L;
}

STATIC Obj PROD_CMAT_CMAT_WITHGREASE(Obj self, Obj l, Obj m, Obj n,
                                     Obj greasetab, Obj spreadtab, Obj glev)
{
    Int k = LEN_PLIST(n)-1;    /* the empty element in front! */
    Int t = LEN_PLIST(m)-1;    /* again */
    Int lev = INT_INTOBJ(glev);
    Int pos;
    Int j;
    Int val;
    Obj v,w;

    v = ELM_PLIST(l,2);  /* we know that the result is not empty */
    {
        PREPARE_clfi(v,cl,fi);
        Int wordlen = INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen));
        for (pos = 1;pos <= k;pos += lev) {
            /* First fill the greasetab: */
            FILL_GREASE_TAB(self,n,INTOBJ_INT(pos+1),glev,greasetab,
                            INTOBJ_INT(LEN_PLIST(greasetab)-2),INTOBJ_INT(1));
            EXTRACT_INIT(self,ELM_PLIST(m,2),INTOBJ_INT(pos),glev);
            for (j = 2;j <= t+1;j++) {
                val = (*Vector_Extract_Worker)(DATA_CVEC(ELM_PLIST(m,j)));
                if (val != 0) {
                    val = INT_INTOBJ(ELM_PLIST(spreadtab,val+1));
                    v = ELM_PLIST(l,j);
                    w = ELM_PLIST(greasetab,val);
                    ADD2_INL(DATA_CVEC(v),DATA_CVEC(w),fi,wordlen);
                }
            }
        }
    }
    return 0L;
}

STATIC Obj PROD_CMAT_CMAT_NOGREASE(Obj self, Obj l, Obj m, Obj n)
{
    Int k = LEN_PLIST(n)-1;    /* the empty element in front! */
    Int t = LEN_PLIST(l)-1;    /* dito */
    Int pos;
    Int j;
    Int val;
    Obj u,v;

    v = ELM_PLIST(l,2);  /* we know that the result is not empty */
    {
        PREPARE_clfi(v,cl,fi);
        PREPARE_d(fi);
        Int wordlen = INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen));
        if (d == 1) {
            for (j = 2;j <= t+1;j++) {
                u = ELM_PLIST(l,j);
                v = ELM_PLIST(m,j);
                for (pos = 1;pos <= k;pos++) {
                    val = CVEC_Itemp(fi,DATA_CVEC(v),pos);
                    if (val != 0) {
                        ADDMUL_INL(DATA_CVEC(u),DATA_CVEC(ELM_PLIST(n,pos+1)),
                                   fi,val,wordlen);
                    }
                }
            }
        } else {
            for (j = 2;j <= t+1;j++) {
                u = ELM_PLIST(l,j);
                v = ELM_PLIST(m,j);
                for (pos = 1;pos <= k;pos++) {
                    CVEC_Itemq(fi,DATA_CVEC(v),pos);
                    if (sclen != 1 || scbuf[0] != 0) {
                       ADDMUL_INT(u,cl,fi,ELM_PLIST(n,pos+1),d,scbuf,0,wordlen);
                    }
                }
            }
        }
    }
    return 0L;
}

STATIC Obj PROD_CMAT_CMAT_NOGREASE2(Obj self, Obj l, Obj m, Obj n)
{
    Int k = LEN_PLIST(n)-1;    /* the empty element in front! */
    Int t = LEN_PLIST(l)-1;    /* dito */
    Int pos;
    Int j;
    Int val;
    Obj u,v;
    Obj buf;

    v = ELM_PLIST(l,2);  /* we know that the result is not empty */
    {
        PREPARE_clfi(v,cl,fi);
        PREPARE_d(fi);
        Int size = INT_INTOBJ(ELM_PLIST(fi,IDX_size));
        Int wordlen = INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen));
        if (d == 1) {
            /* A temporary buffer */
            /* GARBAGE COLLECTION POSSIBLE */
            buf = NEW_PLIST( T_PLIST, k );
            SET_LEN_PLIST( buf, k );
            for (j = 2;j <= t+1;j++) {
                u = ELM_PLIST(l,j);
                v = ELM_PLIST(m,j);
                CVEC_TO_INTREP(self,v,buf);
                for (pos = 1;pos <= k;pos++) {
                    val = INT_INTOBJ(ELM_PLIST(buf,pos));
                    if (val != 0) {
                        ADDMUL_INL(DATA_CVEC(u),DATA_CVEC(ELM_PLIST(n,pos+1)),
                                   fi,val,wordlen);
                    }
                }
            }
        } else {
            /* A temporary buffer */
            if (size < 2) {
                /* GARBAGE COLLECTION POSSIBLE */
                buf = NEW_PLIST( T_PLIST, k );
                SET_LEN_PLIST( buf, k );
                for (j = 2;j <= t+1;j++) {
                    u = ELM_PLIST(l,j);
                    v = ELM_PLIST(m,j);
                    CVEC_TO_INTREP(self,v,buf);
                    for (pos = 1;pos <= k;pos++) {
                        prepare_scalar(fi,ELM_PLIST(buf,pos));
                        if (sclen != 1 || scbuf[0] != 0) {
                            ADDMUL_INT(u,cl,fi,ELM_PLIST(n,pos+1),d,scbuf,
                                       0,wordlen);
                        }
                    }
                }
            } else {
                /* GARBAGE COLLECTION POSSIBLE */
                buf = NEW_PLIST( T_PLIST, k*d );
                SET_LEN_PLIST( buf, k*d );
                for (j = 2;j <= t+1;j++) {
                    register Int pos2;
                    u = ELM_PLIST(l,j);
                    v = ELM_PLIST(m,j);
                    CVEC_TO_INTREP(self,v,buf);
                    for (pos = 1,pos2 = 1;pos <= k;pos++) {
                        register Int i;
                        for (i = 0,sclen = 1;i < d;i++) {
                            val = (Word) INT_INTOBJ(ELM_PLIST(buf,pos2++));
                            scbuf[i] = val;
                            if (val) sclen = i+1;
                        }
                        if (sclen != 1 || scbuf[0] != 0) {
                            ADDMUL_INT(u,cl,fi,ELM_PLIST(n,pos+1),d,scbuf,
                                       0,wordlen);
                        }
                    }
                }
            }
        }
    }
    return 0L;
}

/* Our contribution to slicing: */

STATIC void SLICE_INT(Word *src, Word *dst, Int fr, Int le, Int to,
                      Int d, Int elsperword, Int bitsperel)
{
    Word stamask,endmask,upmask,domask,kupmask,kdomask;
    Int stanr,endnr,shiftl,shiftr;

    fr--;   /* from here on zero based! */
    to--;

    /* A hint: 
     * If you want to understand this, first read the case "shiftl=0", which
     * basically means, that source and target are word-aligned. Then look
     * at the general case. */

    /* Some precalculations: */
    shiftl = (to-fr) % elsperword;
    if (shiftl < 0) shiftl += elsperword;
    if (shiftl == 0) {  /* this is the easy case */
        stanr = elsperword - (fr % elsperword);
        if (stanr > le) stanr = le;
        if (stanr*bitsperel == 8*BYTESPERWORD)
            stamask = WORDALLONE;
        else
            stamask = ((1UL << (stanr*bitsperel))-1) 
                                  << ((fr % elsperword) * bitsperel);
        endnr = (fr+le) % elsperword;
        endmask = (1UL << (endnr*bitsperel))-1;
        {
            register Word *v = src + (fr/elsperword)*d;
            register Word *w = dst + (to/elsperword)*d;
            register Int i;

            /* We do the start bit in any case, even if stanr = elsperword! */
            for (i = d;i > 0;i--,v++,w++) 
                *w = (*w & (~stamask)) | (*v & stamask);
            le -= stanr;

            /* The following is the code to move one word at the position
             * pointed to by v to its destination: */
            while (le >= elsperword) {
                for (i = d;i > 0;i--,v++,w++) *w = *v;
                le -= elsperword;
            }
            
            /* Finally maybe we have to do the rest: */
            if (le > 0) 
                for (i = d;i > 0;i--,v++,w++) 
                    *w = (*w & (~endmask)) | (*v & endmask);
        }
    } else {   /* shiftl != 0 : the hard case */
        shiftr = elsperword-shiftl;
        shiftl *= bitsperel;
        shiftr *= bitsperel;
        kdomask = ((1UL << shiftl)-1);
        upmask = kdomask << shiftr;
        kdomask = ~kdomask;
        domask = (1UL << shiftr)-1;
        kupmask = ~(domask << shiftl);
        stanr = elsperword - (fr % elsperword);
        if (stanr > le) stanr = le;
        if (stanr*bitsperel == 8*BYTESPERWORD)
            stamask = WORDALLONE;
        else
            stamask = ((1UL << (stanr*bitsperel))-1) 
                                  << ((fr % elsperword) * bitsperel);
        endnr = (fr+le) % elsperword;
        endmask = (1UL << (endnr*bitsperel))-1;

        {
            register Word *v = src + (fr/elsperword)*d;
            register Word *w = dst + (to/elsperword)*d;
            register Int i;
            register Word wo;
            Word mask;

            /* Handle the case that position to is only hit by the upper
             * part of the Word containing fr. In that case we have to
             * decrement w by d Words. In that case the first few commands
             * do not write because of the "if (wo)" clause. */
            if ((fr % elsperword) * bitsperel >= shiftr) w -= d; 
            
            /* We do the start bit in any case, even if stanr = elsperword! */
            for (i = d;i > 0;i--,v++,w++) {
                mask = domask & stamask;
                wo = (*v & mask) << shiftl;
                *w = (*w & (~(mask << shiftl))) | wo;
                mask = upmask & stamask;
                wo = (*v & mask) >> shiftr;
                w[d] = (w[d] & (~(mask >> shiftr))) | wo;
            }
            le -= stanr;

            /* The following is the code to move one word at the position
             * pointed to by v to its destination: */
            while (le >= elsperword) {
                for (i = d;i > 0;i--,v++,w++) {
                    wo = (*v & domask) << shiftl;
                    *w = (*w & kupmask) | wo;
                    wo = (*v & upmask) >> shiftr;
                    w[d] = (w[d] & kdomask) | wo;
                }
                le -= elsperword;
            }
            
            /* Finally maybe we have to do the rest: */
            if (le > 0) {
                for (i = d;i > 0;i--,v++,w++) {
                    mask = domask & endmask;
                    wo = (*v & mask) << shiftl;
                    *w = (*w & (~(mask << shiftl))) | wo;
                    mask = upmask & endmask;
                    wo = (*v & mask) >> shiftr;
                    w[d] = (w[d] & (~(mask >> shiftr))) | wo;
                }
            }
        }
    }
}

STATIC Obj SLICE(Obj self, Obj src, Obj dst, Obj srcpos, Obj len, Obj dstpos)
/* No checks are done at all. src and dst must be cvecs over the same field and
 * 1 <= srcpos <= srcpos+len-1 <= Length(src) and
 * 1 <= dstpos <= dstpos+len-1 <= Length(dst) must hold. */
{
    PREPARE_clfi(src,cl,fi);
    PREPARE_d(fi);
    PREPARE_epw(fi);
    PREPARE_bpe(fi);

    SLICE_INT(DATA_CVEC(src),DATA_CVEC(dst),INT_INTOBJ(srcpos),INT_INTOBJ(len),
              INT_INTOBJ(dstpos),d,elsperword,bitsperel);
    return 0L;
}
    
STATIC Obj CVEC_TO_EXTREP(Obj self, Obj v, Obj s)
{
    PREPARE_clfi(v,cl,fi);
    PREPARE_d(fi);
    Int wordlen = INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen));

    /* Unfortunately there are four cases: LITTLE/BIG ENDIAN, 32bit/64bit: */
#ifndef SYS_IS_64_BIT
    /* Here we assume 32bit, see TEST_ASSUMPTIONS. */

    /* To get rid of a warning: */
    d=d;

    /* GARBAGE COLLECTION POSSIBLE */
    GrowString(s,wordlen*BYTESPERWORD);
    SET_LEN_STRING(s,wordlen*BYTESPERWORD);

# if __BYTE_ORDER == __LITTLE_ENDIAN
    /* We are on a little endian machine, we just copy: */
    memcpy(CHARS_STRING(s),DATA_CVEC(v),wordlen*BYTESPERWORD);
# else
    /* Big endian machine, swap bytes: */
    register unsigned char *p;
    register unsigned char *q;
    /* Do a byte copy: */
    p = (unsigned char *) DATA_CVEC(v);
    q = (unsigned char *) CHARS_STRING(s);
    while (--wordlen >= 0) {
        q[3] = p[0];
        q[2] = p[1];
        q[1] = p[2];
        q[0] = p[3];
        p += 4;
        q += 4;
    }
# endif
    
#else
    /* From here on 64bit machine, we need some more variables: */
    PREPARE_epw(fi);
    PREPARE_bpe(fi);
    Int len = INT_INTOBJ(ELM_PLIST(cl,IDX_len));
    /* How would things be in a 32bit world? */
    Int elsperword32 = elsperword/2;
    /* note that elsperword is always even on 64bit machines! */
    Word wordlen32 = (len + elsperword32 - 1)/elsperword32;
    Word mask = (1UL << (elsperword32 * bitsperel))-1;
    register Word *p;
    register Word wo;
    register int shift = elsperword32 * bitsperel;
    register int k;

# if __BYTE_ORDER == __LITTLE_ENDIAN
    /* We are on a little endian machine, we copy, but have to
     * work for upper halves and lower halves separatedly. */

    register Word32 *q;

    wordlen /= d;   /* We remember the factor d ourselves! */

    /* GARBAGE COLLECTION POSSIBLE */
    GrowString(s,wordlen32*4*d);
    SET_LEN_STRING(s,wordlen32*4*d);

    if (wordlen32 & 1 != 0) wordlen--;  /* Do not copy last word */
    p = DATA_CVEC(v);
    q = (Word32 *) CHARS_STRING(s);
    while (--wordlen >= 0) {
        for (k = d-1;k >= 0;k--) {
            wo = *p++;
            *q = (Word32) (wo & mask);
            q[d] = (Word32) (wo >> shift);
            q++;
        }
        q += d;   /* Skip upper halves in result */
    }
    if (wordlen32 & 1 != 0) {  /* Handle last half of word: */
        for (k = d-1;k >= 0;k--)
            *q++ = (Word32) (*p++ & mask);
    }
# else
    /* Big endian machine with 64 bit, now it becomes ugly! */
    /* We have to work for upper halves and lower halves separatedly and
     * to swap bytes around! */

    register Word32 wo32;
    register unsigned char *q;
    
    wordlen /= d;   /* We remember the factor d ourselves! */
    
    /* GARBAGE COLLECTION POSSIBLE */
    GrowString(s,wordlen32*4*d);
    SET_LEN_STRING(s,wordlen32*4*d);

    if (wordlen32 & 1 != 0) wordlen--;  /* Do not copy last word */
    p = DATA_CVEC(v);
    q = (unsigned char *) CHARS_STRING(s);
    while (--wordlen >= 0) {
        for (k = d-1;k >= 0;k--) {
            wo = *p++;
            wo32 = (Word32) (wo & mask);
            *q = (unsigned char) (wo32 & 0xff); wo32 >>= 8;
            q[1] = (unsigned char) (wo32 & 0xff); wo32 >>= 8;
            q[2] = (unsigned char) (wo32 & 0xff); wo32 >>= 8;
            q[3] = (unsigned char) (wo32 & 0xff);
            q += d * 4;
            wo32 = (Word32) (wo >> shift);
            *q = (unsigned char) (wo32 & 0xff); wo32 >>= 8;
            q[1] = (unsigned char) (wo32 & 0xff); wo32 >>= 8;
            q[2] = (unsigned char) (wo32 & 0xff); wo32 >>= 8;
            q[3] = (unsigned char) (wo32 & 0xff);
            q -= d * 4 - 4;
        }
        q += d*4;   /* Skip upper halves in result */
    }
    if (wordlen32 & 1 != 0) {  /* Handle last half of word: */
        for (k = d-1;k >= 0;k--) {
            wo32 = (Word32) (*p++ & mask);
            *q = (unsigned char) (wo32 & 0xff); wo32 >>= 8;
            q[1] = (unsigned char) (wo32 & 0xff); wo32 >>= 8;
            q[2] = (unsigned char) (wo32 & 0xff); wo32 >>= 8;
            q[3] = (unsigned char) (wo32 & 0xff);
            q += 4;
        }
    }
# endif
#endif
    return 0L;
}

STATIC Obj EXTREP_TO_CVEC(Obj self, Obj s, Obj v)
{
    PREPARE_clfi(v,cl,fi);
    PREPARE_d(fi);
    Int wordlen = INT_INTOBJ(ELM_PLIST(cl,IDX_wordlen));

    /* Unfortunately there are four cases: LITTLE/BIG ENDIAN, 32bit/64bit: */
#ifndef SYS_IS_64_BIT
    /* Here we assume 32bit, see TEST_ASSUMPTIONS. */

    /* To get rid of a warning: */
    d=d;

# if __BYTE_ORDER == __LITTLE_ENDIAN
    /* We are on a little endian machine, we just copy: */
    memcpy(DATA_CVEC(v),CHARS_STRING(s),wordlen*BYTESPERWORD);
# else
    /* Big endian machine, swap bytes: */
    register unsigned char *p;
    register unsigned char *q;
    /* Do a byte copy: */
    p = (unsigned char *) CHARS_STRING(s);
    q = (unsigned char *) DATA_CVEC(v);
    while (--wordlen >= 0) {
        q[3] = p[0];
        q[2] = p[1];
        q[1] = p[2];
        q[0] = p[3];
        p += 4;
        q += 4;
    }
# endif
    
#else
    /* From here on 64bit machine, we need some more variables: */
    PREPARE_epw(fi);
    PREPARE_bpe(fi);
    Int len = INT_INTOBJ(ELM_PLIST(cl,IDX_len));
    /* How would things be in a 32bit world? */
    Int elsperword32 = elsperword/2;
    /* note that elsperword is always even on 64bit machines! */
    Word wordlen32 = (len + elsperword32 - 1)/elsperword32;
    register Word *q;
    register int shift = elsperword32 * bitsperel;
    register int k;

# if __BYTE_ORDER == __LITTLE_ENDIAN
    /* We are on a little endian machine, we copy, but have to
     * work for upper halves and lower halves separatedly. */

    register Word32 *p;

    wordlen /= d;   /* We remember the factor d ourselves! */

    if (wordlen32 & 1 != 0) wordlen--;  /* Do not copy last word */
    p = (Word32 *) CHARS_STRING(s);
    q = DATA_CVEC(v);
    while (--wordlen >= 0) {
        for (k = d-1;k >= 0;k--) {
            *q++ = (((Word)(p[d])) << shift) | (Word) (*p);
            p++;
        }
        p += d;   /* Skip upper halves in result */
    }
    if (wordlen32 & 1 != 0) {  /* Handle last half of word: */
        for (k = d-1;k >= 0;k--)
            *q++ = (Word) (*p++);
    }
# else
    /* Big endian machine with 64 bit, now it becomes ugly! */
    /* We have to work for upper halves and lower halves separatedly and
     * to swap bytes around! */

    register Word32 wo32;
    register unsigned char *p;
    register Word wo;
    
    wordlen /= d;   /* We remember the factor d ourselves! */
    
    if (wordlen32 & 1 != 0) wordlen--;  /* Do not copy last word */
    p = (unsigned char *) CHARS_STRING(s);
    q = DATA_CVEC(v);
    while (--wordlen >= 0) {
        for (k = d-1;k >= 0;k--) {
            wo = ( ( ( ( ( (Word)(p[3]) << 8)
                         | (Word)(p[2]) ) << 8)
                     | (Word)(p[1]) ) << 8)
                 | (Word)(p[0]);
            p += d * 4;
            wo |= ( ( ( ( ( ( (Word)(p[3]) << 8)
                            | (Word)(p[2]) ) << 8)
                        | (Word)(p[1]) ) << 8)
                    | (Word)(p[0]) ) << shift;
            p -= d * 4 - 4;
            *q++ = wo;
        }
        p += d*4;   /* Skip upper halves in result */
    }
    if (wordlen32 & 1 != 0) {  /* Handle last half of word: */
        for (k = d-1;k >= 0;k--) {
            *q++ = ( ( ( ( ( (Word)(p[3]) << 8)
                           | (Word)(p[2]) ) << 8)
                       | (Word)(p[1]) ) << 8)
                   | (Word)(p[0]);
            p += 4;
        }
    }
# endif
#endif
    return 0L;
}

Obj PROD_COEFFS_CVEC_PRIMEFIELD(Obj self, Obj u, Obj v, Obj w)
/* All four must be cvecs over the same (prime) field.
 * u is overwritten but has to be zero beforehand! 
 * u must have length len(v)+len(w)-1 */
{
    if (!IS_CVEC(u) || !IS_CVEC(v) || !IS_CVEC(w)) {
        return OurErrorBreakQuit("CVEC.COEFFS_CVEC_PRIMEFIELD: "
                   "no cvecs");
    }
    {
        PREPARE_clfi(u,ucl,fi);
        PREPARE_cl(v,vcl);
        PREPARE_cl(w,wcl);
        PREPARE_epw(fi);
        PREPARE_bpe(fi);
        Int lenv = INT_INTOBJ(ELM_PLIST(vcl,IDX_len));
        Int lenw = INT_INTOBJ(ELM_PLIST(wcl,IDX_len));
        /* First create a table for the first elsperword-1 shifted w: */
        Int wordlenw = INT_INTOBJ(ELM_PLIST(wcl,IDX_wordlen));
        Int wordlenu = INT_INTOBJ(ELM_PLIST(ucl,IDX_wordlen));
        Int tablen = elsperword < lenv ? elsperword-1 : lenv-1; 
                     /* Minimum */
        Obj tmp;
        Word *buf;
        register Int i, imodepw, j;
        
        /* GARBAGE COLLECTION POSSIBLE */
        tmp = NEW_STRING(sizeof(Word)*(wordlenw+1)*tablen);
        if (tmp == 0L) {
            return OurErrorBreakQuit("CVEC.COEFFS_CVEC_PRIMEFIELD: "
                                     "out of memory");
        }
        /* done with possible garbage collections, no references stored! */
        buf = (Word *) CHARS_STRING(tmp);

        /* Now do the slicing: */
        Word *ww = DATA_CVEC(w);
        for (i = 0;i < tablen;i++) {
            SLICE_INT(ww,buf + (i*(wordlenw+1)),1,lenw,i+2,
                      1 /* ==d */, elsperword, bitsperel);
        }
        
        {
            /* Now we are ready to prepare the result: */
            seqaccess sa;
            Word *vv = DATA_CVEC(v);
            Word *uu = DATA_CVEC(u);
            register Word s;

            i = 1; j = 0;  /* j is the word shift */
            INIT_SEQ_ACCESS(&sa,v,1);

            while (i <= lenv) {
                /* Do the (unshifted) thing: */
                s = GET_VEC_ELM(&sa,vv,0);
                if (s) ADDMUL_INL(uu+j,ww,fi,s,wordlenw);

                i++; imodepw = 1;
                STEP_RIGHT(&sa);
                while (i <= lenv && imodepw < elsperword) {
                    s = GET_VEC_ELM(&sa,vv,0);
                    if (s)
                        ADDMUL_INL(uu+j,buf + (wordlenw+1)*(imodepw-1),fi,s,
                            j+wordlenw+1 <= wordlenu ? wordlenw+1 : wordlenw);
                    /* Note that we know u is long enough. If 
                     * j+wordlenw+1 > wordlenu, then it can only be 1 more
                     * and things in the last word of the shifted vector
                     * cannot be significant. */
                    i++; imodepw++;
                    STEP_RIGHT(&sa);
                }
                j++;
            }
        }
    }
    return 0L;
}

STATIC Obj TRANSPOSED_MAT(Obj self, Obj m, Obj n)
{
    /* n is empty, correct size, >0 rows, >0 cols, right size, same field. */
    PREPARE_clfi(ELM_PLIST(m,2),cl,fi);
    PREPARE_d(fi);
    Int lenm = LEN_PLIST(m)-1;   /* Remember the shift by one */
    Int lenn = LEN_PLIST(n)-1;
    Word *v;
    register Int i,j,k;

    seqaccess sasrc;   /* For access in source */
    seqaccess sadst;   /* For access in destination */


    if (d == 1) {
        /* We read row-wise and write column-wise. */
        INIT_SEQ_ACCESS(&sadst,ELM_PLIST(n,2),1);
        for (i = 1;i <= lenm;i++) {
            INIT_SEQ_ACCESS(&sasrc,ELM_PLIST(m,2),1);
            v = DATA_CVEC(ELM_PLIST(m,i+1));
            for (j = 1;j <= lenn;j++) {
                SET_VEC_ELM(&sadst,DATA_CVEC(ELM_PLIST(n,j+1)),0,
                            GET_VEC_ELM(&sasrc,v,0));
                STEP_RIGHT(&sasrc);
            }
            STEP_RIGHT(&sadst);
        }
    } else {  /* d > 1 */
        /* We read row-wise and write column-wise. */
        INIT_SEQ_ACCESS(&sadst,ELM_PLIST(n,2),1);
        for (i = 1;i <= lenm;i++) {
            INIT_SEQ_ACCESS(&sasrc,ELM_PLIST(m,2),1);
            v = DATA_CVEC(ELM_PLIST(m,i+1));
            for (j = 1;j <= lenn;j++) {
                for (k = 0;k < d;k++) {
                    SET_VEC_ELM(&sadst,DATA_CVEC(ELM_PLIST(n,j+1)),k,
                                GET_VEC_ELM(&sasrc,v,k));
                }
                STEP_RIGHT(&sasrc);
            }
            STEP_RIGHT(&sadst);
        }
    }
    return 0L;
}


/*F * * * * * * * * * * * * * initialize package * * * * * * * * * * * * * * */

/******************************************************************************
*V  GVarFuncs . . . . . . . . . . . . . . . . . . list of functions to export
*/
static StructGVarFunc GVarFuncs [] = {

  { "TEST_ASSUMPTIONS", 0, "",
    TEST_ASSUMPTIONS,
    "cvec.c:TEST_ASSUMPTIONS" },

  { "COEFF_LIST_TO_C", 2, "coefflist, st",
    COEFF_LIST_TO_C,
    "cvec.c:COEFF_LIST_TO_C" },

  { "FINALIZE_FIELDINFO", 1, "fieldinfo",
    FINALIZE_FIELDINFO,
    "cvec.c:FINALIZE_FIELDINFO" },

  { "INIT_SMALL_GFQ_TABS", 6, "p, d, q, tab1, tab2, primroot",
    INIT_SMALL_GFQ_TABS,
    "cvec.c:INIT_SMALL_GFQ_TABS" },

  { "NEW", 2, "class, type",
    NEW,
    "cvec.c:NEW" },

  { "MAKEZERO", 1, "v",
    MAKEZERO,
    "cvec.c:MAKEZERO" },

  { "COPY", 2, "v, w",
    COPY,
    "cvec.c:COPY" },

  { "CVEC_TO_INTREP", 2, "v, l",
    CVEC_TO_INTREP,
    "cvec.c:CVEC_TO_INTREP" },

  { "INTREP_TO_CVEC", 2, "l, v",
    INTREP_TO_CVEC,
    "cvec.c:INTREP_TO_CVEC" },

  { "INTLI_TO_FFELI", 2, "c, l",
    INTLI_TO_FFELI,
    "cvec.c:INTLI_TO_FFELI" },

  { "FFELI_TO_INTLI", 2, "c, l",
    FFELI_TO_INTLI,
    "cvec.c:FFELI_TO_INTLI" },

  { "CVEC_TO_NUMBERFFLIST", 3, "v, l, split",
    CVEC_TO_NUMBERFFLIST,
    "cvec.c:CVEC_TO_NUMBERFFLIST" },

  { "NUMBERFFLIST_TO_CVEC", 3, "l, v, split",
    NUMBERFFLIST_TO_CVEC,
    "cvec.c:NUMBERFFLIST_TO_CVEC" },

  { "ADD2", 4, "u, v, fr, to",
    ADD2,
    "cvec.c:ADD2" },

  { "ADD3", 3, "u, v, w",
    ADD3,
    "cvec.c:ADD3" },

  { "MUL1", 4, "u, s, fr, to",
    MUL1,
    "cvec.c:MUL1" },

  { "MUL2", 3, "u, v, s",
    MUL2,
    "cvec.c:MUL2" },

  { "ADDMUL", 5, "u, v, s, fr, to",
    ADDMUL,
    "cvec.c:ADDMUL" },

  { "ASS_CVEC", 3, "v, pos, s",
    ASS_CVEC,
    "cvec.c:ASS_CVEC" },

  { "ELM_CVEC", 2, "v, pos",
    ELM_CVEC,
    "cvec.c:ELM_CVEC" },

  { "POSITION_NONZERO_CVEC", 1, "v",
    POSITION_NONZERO_CVEC,
    "cvec.c:POSITION_NONZERO_CVEC" },

  { "POSITION_LAST_NONZERO_CVEC", 1, "v",
    POSITION_LAST_NONZERO_CVEC,
    "cvec.c:POSITION_LAST_NONZERO_CVEC" },

  { "CVEC_LT", 2, "u, v",
    CVEC_LT,
    "cvec.c:CVEC_LT" },

  { "CVEC_EQ", 2, "u, v",
    CVEC_EQ,
    "cvec.c:CVEC_EQ" },

  { "CVEC_ISZERO", 1, "u",
    CVEC_ISZERO,
    "cvec.c:CVEC_ISZERO" },

  { "EXTRACT", 3, "v, i, l",
    EXTRACT,
    "cvec.c:EXTRACT" },

  { "EXTRACT_INIT", 3, "v, i, l",
    EXTRACT_INIT,
    "cvec.c:EXTRACT_INIT" },

  { "EXTRACT_DOIT", 1, "v",
    EXTRACT_DOIT,
    "cvec.c:EXTRACT_DOIT" },

  { "FILL_GREASE_TAB", 6, "li, i, l, tab, tablen, offset",
     FILL_GREASE_TAB,
     "cvec.c:FILL_GREASE_TAB" },

  { "PROD_CVEC_CMAT_NOGREASE", 3, "u, v, m",
    PROD_CVEC_CMAT_NOGREASE,
    "cvec.c:PROD_CVEC_CMAT_NOGREASE" },

  { "PROD_CVEC_CMAT_GREASED", 5, "u, v, mgreasetab, spreadtab, glev",
    PROD_CVEC_CMAT_GREASED,
    "cvec.c:PROD_CVEC_CMAT_GREASED" },

  { "PROD_CMAT_CMAT_GREASED", 6, "l, m, ngreasetab, spreadtab, len, glev",
    PROD_CMAT_CMAT_GREASED,
    "cvec.c:PROD_CMAT_CMAT_GREASED" },

  { "PROD_CMAT_CMAT_NOGREASE", 3, "l, m, n",
    PROD_CMAT_CMAT_NOGREASE,
    "cvec.c:PROD_CMAT_CMAT_NOGREASE" },

  { "PROD_CMAT_CMAT_NOGREASE2", 3, "l, m, n",
    PROD_CMAT_CMAT_NOGREASE2,
    "cvec.c:PROD_CMAT_CMAT_NOGREASE2" },

  { "PROD_CMAT_CMAT_WITHGREASE", 6, "l, m, n, greasetab, spreadtab, glev",
    PROD_CMAT_CMAT_WITHGREASE,
    "cvec.c:PROD_CMAT_CMAT_WITHGREASE" },

  { "SLICE", 5, "src, dst, srcpos, len, dstpos",
    SLICE,
    "cvec.c:SLICE" },

  { "CVEC_TO_EXTREP", 2, "v, s",
    CVEC_TO_EXTREP,
    "cvec.c:CVEC_TO_EXTREP" },

  { "EXTREP_TO_CVEC", 2, "s, v",
    EXTREP_TO_CVEC,
    "cvec.c:EXTREP_TO_CVEC" },

  { "PROD_COEFFS_CVEC_PRIMEFIELD", 3, "u, v, w",
    PROD_COEFFS_CVEC_PRIMEFIELD,
    "cvec.c:PROD_COEFFS_CVEC_PRIMEFIELD" },

  { "TRANSPOSED_MAT", 2, "m, n",
    TRANSPOSED_MAT,
    "cvec.c:TRANSPOSED_MAT" },

  { 0 }

};

/******************************************************************************
*F  InitKernel( <module> )  . . . . . . . . initialise kernel data structures
*/
static Int InitKernel ( StructInitInfo *module )
{
    /* init filters and functions                                          */
    InitHdlrFuncsFromTable( GVarFuncs );

    /* return success                                                      */
    return 0;
}

#define CVEC_PUBLISH(nam) gvar=GVarName("CVEC_"#nam); MakeReadWriteGVar(gvar);\
    AssGVar( gvar, INTOBJ_INT(nam)); MakeReadOnlyGVar(gvar)

/******************************************************************************
*F  InitLibrary( <module> ) . . . . . . .  initialise library data structures
*/
static Int InitLibrary ( StructInitInfo *module )
{
    Int             i, gvar;
    Obj             tmp;

    /* init filters and functions
       we assign the functions to components of a record "CVEC"         */
    tmp = NEW_PREC(0);
    for ( i = 0;  GVarFuncs[i].name != 0;  i++ ) {
      AssPRec(tmp, RNamName((Char*)GVarFuncs[i].name),
              NewFunctionC( GVarFuncs[i].name, GVarFuncs[i].nargs,
                 GVarFuncs[i].args, GVarFuncs[i].handler ) );
    }
    AssPRec(tmp, RNamName("BYTESPERWORD"), INTOBJ_INT(BYTESPERWORD));
    AssPRec(tmp, RNamName("MAXDEGREE"), INTOBJ_INT(MAXDEGREE));

    /* Export position numbers: */
    CVEC_PUBLISH(IDX_p);
    CVEC_PUBLISH(IDX_d);
    CVEC_PUBLISH(IDX_q);
    CVEC_PUBLISH(IDX_conway);
    CVEC_PUBLISH(IDX_bitsperel);
    CVEC_PUBLISH(IDX_elsperword);
    CVEC_PUBLISH(IDX_wordinfo);
    CVEC_PUBLISH(IDX_bestgrease);
    CVEC_PUBLISH(IDX_greasetabl);
    CVEC_PUBLISH(IDX_filts);
    CVEC_PUBLISH(IDX_tab1);
    CVEC_PUBLISH(IDX_tab2);
    CVEC_PUBLISH(IDX_size);
    CVEC_PUBLISH(IDX_scafam);

    CVEC_PUBLISH(IDX_fieldinfo);
    CVEC_PUBLISH(IDX_len);
    CVEC_PUBLISH(IDX_wordlen);
    CVEC_PUBLISH(IDX_type);
    CVEC_PUBLISH(IDX_GF);
    CVEC_PUBLISH(IDX_lens);
    CVEC_PUBLISH(IDX_classes);

    /*ImportFuncFromLibrary( "IsCVecRep", &IsCVecRep );*/

    gvar = GVarName("CVEC");
    MakeReadWriteGVar( gvar);
    AssGVar( gvar, tmp );
    MakeReadOnlyGVar(gvar);
    /* return success                                                      */
    return 0;
}

/******************************************************************************
*F  InitInfopl()  . . . . . . . . . . . . . . . . . table of init functions
*/
static StructInitInfo module = {
#ifdef CVECSTATIC
 /* type        = */ MODULE_STATIC,
#else
 /* type        = */ MODULE_DYNAMIC,
#endif
 /* name        = */ "cvec",
 /* revision_c  = */ 0,
 /* revision_h  = */ 0,
 /* version     = */ 0,
 /* crc         = */ 0,
 /* initKernel  = */ InitKernel,
 /* initLibrary = */ InitLibrary,
 /* checkInit   = */ 0,
 /* preSave     = */ 0,
 /* postSave    = */ 0,
 /* postRestore = */ 0
};

StructInitInfo * Init__Dynamic ( void )
{
 return &module;
}

StructInitInfo * Init__cvec ( void )
{
  return &module;
}


