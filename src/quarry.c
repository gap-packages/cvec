/* Cleaning vectors (using lazy grease): */

STATIC Int GREASEPOS_INT(Obj v, Int p, Int d, Int *pivs, Int pivslen)
{
    Int i,j;
    seqaccess sa;
    Int res;
    Word *ww = DATA_CVEC(v);

    i = pivslen-1;
    INIT_SEQ_ACCESS(&sa,v,pivs[i]);
    res = 0;
    while (1) {   /* we use break */
        /* sa already points to position i! */
        for (j = d-1;j >= 0;j--) res = res * p + GET_VEC_ELM(&sa,ww,j);
        if (--i < 0) break;
        MOVE_SEQ_ACCESS(&sa,pivs[i]);
    }
    return res+1;
}

STATIC Int GREASEPOS_INT_WITH_DEC(Obj v, Int p, Int d, Int *pivs, Int pivslen,
                                  Obj dec, Int startpos)
{
    Int i,j;
    seqaccess sa;
    seqaccess sadec;
    Int res;
    Word *ww = DATA_CVEC(v);
    Word *dd = DATA_CVEC(dec);
    Int c;

    i = pivslen-1;
    INIT_SEQ_ACCESS(&sa,v,pivs[i]);
    INIT_SEQ_ACCESS(&sadec,dec,startpos+pivslen-1);
    res = 0;
    while (1) {   /* we use break */
        /* sa already points to position i! */
        for (j = d-1;j >= 0;j--) {
            c = GET_VEC_ELM(&sa,ww,j);
            res = res * p + c;
            SET_VEC_ELM(&sadec,dd,j,c);
        }
        if (--i < 0) break;
        MOVE_SEQ_ACCESS(&sa,pivs[i]);
        STEP_LEFT(&sadec);
    }
    return res+1;
}


STATIC Obj GetLinearCombination(Obj self, Obj lg_vecs, Obj lg_tab, Obj lg_ind, 
            Int lg_lev, Obj vec, Obj cl, Obj fi, Int p, Int d, Int offset, 
            Int *pivs, Int pivslen, Int len, Obj dec, Int wordlen) 
{
    /* This function may trigger GARBAGE COLLECTIONS! */
    Int pos;
    Int group;
    Int i;
    Obj w;
    Obj ourtab;
    Obj rows = ElmPRec( lg_tab, RNamName("rows") );
    Int tlen;

    /* offset must be congruent 1 mod lev */
    if (dec != False && dec != True && pivslen == lg_lev)
        pos = GREASEPOS_INT_WITH_DEC(vec,p,d,pivs,pivslen,dec,offset);
    else 
        pos = GREASEPOS_INT(vec,p,d,pivs,pivslen);
    if (pos == 1) return INTOBJ_INT(0L);
    group = (offset-1) / lg_lev + 1;
    /* if (LEN_PLIST(lg_ind) < group || ELM_PLIST(lg_ind,group) == 0L) {*/
    if (!ISB_LIST(lg_ind,group)) {
        ASS_LIST(lg_ind,group,NEW_PLIST(T_PLIST,pos));
    }
    /* GARBAGE COLLECTION POSSIBLE! */
    ourtab = ELM_PLIST(lg_ind,group);
    if (!ISB_LIST(ourtab,pos)) {
        /* First we need a new vector: */
        w = NEW(self,cl,ELM_PLIST(cl,IDX_type));
        /* GARBAGE COLLECTION POSSIBLE! */
        if (d == 1) {  /* We distinguish prime field and extension field: */
            /* Cut away all trailing zeroes: */
            Int c;
            /* Note that at least one position is nonzero, otherwise pos==1 */
            i = pivslen-1;
            while (1) {
                c = CVEC_Itemp(fi, DATA_CVEC(vec), pivs[i]);
                if (c) break;
                i--;
            }
            /* Again: i < 0 does not happen! */
            MUL2_INL(DATA_CVEC(w),DATA_CVEC(ELM_PLIST(lg_vecs,offset+i+1)),fi,
                     c,wordlen);
            if (i > 0) {
                Obj ww;
                ww = GetLinearCombination(self,lg_vecs,lg_tab,lg_ind,lg_lev,
                        vec,cl,fi,p,d,offset,pivs,i,len,dec,wordlen);
                if (ww != INTOBJ_INT(0))
                  ADD2_INL(DATA_CVEC(w),DATA_CVEC(ww),fi,wordlen);
            }
            tlen = LEN_LIST(rows);
            ASS_LIST(rows,tlen+1,w);
            AssPRec(lg_tab,RNamName("len"),INTOBJ_INT(tlen));
            /* Note the fail in position 1! */
            ASS_LIST(ourtab,pos,INTOBJ_INT(tlen));   
            /* shift intentional because of the fail in position 1 of rows! */
            return w;
        } else {
            /* extension field case: */
            /* Cut away all trailing zeroes: */
            /* Note that at least one position is nonzero, otherwise pos==1 */
            i = pivslen-1;
            while (1) {
                CVEC_Itemq(fi, DATA_CVEC(vec), pivs[i]);
                if (sclen > 1 || scbuf[0] != 0) break;
                i--;
            }
            /* Again: i < 0 does not happen! */
            MUL2_INT(w,cl,fi,ELM_PLIST(lg_vecs,offset+i+1),d,wordlen,scbuf);
            if (i > 0) {
                Obj ww;
                ww = GetLinearCombination(self,lg_vecs,lg_tab,lg_ind,lg_lev,
                        vec,cl,fi,p,d,offset,pivs,i,len,dec,wordlen);
                if (ww != INTOBJ_INT(0))
                    ADD2_INL(DATA_CVEC(w),DATA_CVEC(ww),fi,wordlen);
            }
            tlen = LEN_LIST(rows);
            ASS_LIST(rows,tlen+1,w);
            AssPRec(lg_tab,RNamName("len"),INTOBJ_INT(tlen));
            /* Note the fail in position 1! */
            ASS_LIST(ourtab,pos,INTOBJ_INT(tlen));   
            /* shift intentional because of the fail in position 1 of rows! */
            return w;
        }
    } else {
        return ELM_PLIST(rows,INT_INTOBJ(ELM_PLIST(ourtab,pos))+1);
           /* Note the fail in position 1 of lg_tab */
    }
}

/* Aus CleanRowKernel: */

  Obj lazygreaser = ElmPRec( basis, RNamName( "lazygreaser" ) );
  Int pivs[16];   /* we will never see more than level 10 grease or so */
  Obj lc;
  Int shortcut;

  if (lazygreaser != Fail) {
      /* The grease case: */
      Obj lg_tab = ElmPRec( lazygreaser, RNamName( "tab" ) );
      Obj lg_ind = ElmPRec( lazygreaser, RNamName( "ind" ) );
      Int lg_lev = INT_INTOBJ(ElmPRec( lazygreaser, RNamName( "lev" ) ) );
      /* Note that lazygrease!.vecs must be the same object as 
       * basis.vectors! */

      for (i = 1;i+lg_lev-1 <= len;i += lg_lev) {
          /* Fetch the columns to work on: */
          shortcut = 1;
          for (j = 0;j < lg_lev;j++) {
              pivs[j] = INT_INTOBJ(ELM_PLIST(pivots,i+j));
              if (pivs[j] >= firstnz) shortcut = 0;
          }
          if (!shortcut) {
              /* Otherwise, there is nothing to do at all */
              Int lll = INT_INTOBJ(ElmPRec(lazygreaser,RNamName("count")));
              for (; lll > 0;lll--)
              lc = GetLinearCombination(self,rows,lg_tab,lg_ind,lg_lev,vec,
                      cl,fi,p,d,i,pivs,lg_lev,len,dec,wordlen);
              /* This changes dec in positions i..i+lg_lev-1 if it is a cvec! */
              if (lc != INTOBJ_INT(0L))   
                  /* 0 indicates the zero linear combination */
                  ADDMUL_INL( DATA_CVEC(vec), DATA_CVEC(lc),fi,p-1,wordlen );
          }
      }
      /* Now go to the standard case for the rest, starting at i */
  } else i = 1;
      /* The non-grease case starts from the beginning */

  /* we have to work without the lazy greaser: */

...


          if (lazygreaser != Fail) {
              /* In the grease case, we do full-echelon form within the 
                 grease block: */
              for (j = i;j <= len;j++) {
                  Word *w = DATA_CVEC(ELM_PLIST(rows,j+1));
                  c = CVEC_Itemp(fi,w,newpiv);
                  if (c) ADDMUL_INL(w,vecvec,fi,p-c,wordlen);
              }
          }

...


          if (lazygreaser != Fail) {
              /* In the grease case, we do full-echelon form within the 
                 grease block: */
              for (j = i;j <= len;j++) {
                  Obj w = ELM_PLIST(rows,j+1);
                  CVEC_Itemq(fi,DATA_CVEC(w),newpiv);
                  if (sclen > 1 || scbuf[0] != 0) {
                      Int k;
                      for (k = sclen-1;k >= 0;k--)
                          scbuf[k] = scbuf[k] ? p-scbuf[k] : 0;
                      ADDMUL_INT(w,cl,fi,vec,d,scbuf,0,wordlen);
                  }
              }
          }
