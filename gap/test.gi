#############################################################################
##
#W  test.gi               GAP 4 package `cvec'                Max Neunhoeffer
##
#Y  Copyright (C)  2005,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
##
##  This file contains some tests for the cvecs.
##

CVEC.TEST := rec();   # for regression tests
CVEC.BENCH := rec();  # for benchmarks

CVEC.TEST.ALLCHEAP := function(name,func)
  local p,d;
  for p in Primes do
    if p < CVEC.TEST.LIMIT_ALLFFE then
      Print("Testing ",name," p=",p,", d=1 ... \r");
      func(p,1);
    fi;
  od;
  for p in Primes{[1..20]} do
    if p^2 < CVEC.TEST.LIMIT_ALLFFE then
      Print("Testing ",name," p=",p,", d=2 ... \r");
      func(p,2);
    fi;
  od;
  for p in Primes{[1..9]} do
    if p^3 < CVEC.TEST.LIMIT_ALLFFE then
      Print("Testing ",name," p=",p,", d=3 ... \r");
      func(p,3);
    fi;
  od;
  for p in Primes{[1..4]} do
    if p^4 < CVEC.TEST.LIMIT_ALLFFE then
      Print("Testing ",name," p=",p,", d=4 ... \r");
      func(p,4);
    fi;
  od;
  for p in Primes{[1..3]} do
    if p^5 < CVEC.TEST.LIMIT_ALLFFE then
      Print("Testing ",name," p=",p,", d=5 ... \r");
      func(p,5);
    fi;
  od;
  for p in Primes{[1..2]} do
    if p^6 < CVEC.TEST.LIMIT_ALLFFE then
      Print("Testing ",name," p=",p,", d=6 ... \r");
      func(p,6);
    fi;
  od;
  for p in Primes{[1..2]} do
    if p^7 < CVEC.TEST.LIMIT_ALLFFE then
      Print("Testing ",name," p=",p,", d=7 ... \r");
      func(p,7);
    fi;
  od;
  for d in [8..13] do
    if p^8 < CVEC.TEST.LIMIT_ALLFFE then
      Print("Testing ",name," p=2, d=",d," ... \r");
      func(2,d);
    fi;
  od;
end;

CVEC.TEST.COMPRESSED_ALL := function(name,func)
  local p,d;
  for p in Primes do
      if p < 256 then
          d := 1;
          while p^d <= 256 do
              Print("Testing ",name," COMPRESSED p=",p,", d=",d," ...\r");
              func(p,d);
              d := d + 1;
          od;
      fi;
  od;
end;

CVEC.TEST.LIMIT_ALLFFE := 32768;

CVEC.TEST.ALLFFE := function(name,func)
  local d,p;
  p := 2;
  while p < CVEC.TEST.LIMIT_ALLFFE do   
      # this leaves out 32768 < p < 65536, but this needs
      # too much memory for the GF's in GAP
      d := 1;
      repeat
          Print("Testing ",name," p=",p,", d=",d," ...\r");
          func(p,d);
          d := d + 1;
      until p^d > MAXSIZE_GF_INTERNAL;
      p := NextPrimeInt(p);
      CVEC.ClearCache();
  od;
end;
         
CVEC.TEST.INTFFE_CONVERSION := function(p,d)
  local c,l,q;
  q := p^d;
  if not(IsPrimePowerInt(q)) or q > MAXSIZE_GF_INTERNAL then
      Error("Test is only for those p^d that are implemented in GAP!");
  fi;
  c := CVEC.NewCVecClass(p,d,q);
  c := c![1];
  l := 1*[0..q-1];
  CVEC.INTLI_TO_FFELI(c,l);
  if l <> c![12] then
      Print("Alarm: INTLI_TO_FFELI, p=",p," d=",d,"      \n");
  fi;
  l := ShallowCopy(c![12]);
  CVEC.FFELI_TO_INTLI(c,l);
  if l <> [0..q-1] then
      Print("Alarm: FFELI_TO_INTLI, p=",p," d=",d,"      \n");
  fi;
end;

CVEC.TEST.ADD2 := function(p,d)
  local c,q,l,v,w,ll,vv,ww,i;
  q := p^d;
  if not(IsPrimePowerInt(q)) or q > MAXSIZE_GF_INTERNAL then
      Error("Test is only for those p^d that are implemented in GAP!");
  fi;
      
  c := CVEC.NewCVecClass(p,d,q);   # Length is q
  v := CVEC.New(c);
  w := CVEC.New(c);
  l := 1*[0..q-1];
  CVEC.INTREP_TO_CVEC(l,v);
  vv := ShallowCopy(l);
  CVEC.INTLI_TO_FFELI(c![1],vv);   # Change numbers into FFEs
  l := 0*[1..q];
  ll := 0*[1..q];
  for i in [0..q-1] do
      CVEC.INTREP_TO_CVEC(l,w);
      ww := ShallowCopy(l);
      CVEC.INTLI_TO_FFELI(c![1],ww);
      CVEC.ADD2(w,v,1,q);
      CVEC.CVEC_TO_INTREP(w,ll);
      CVEC.INTLI_TO_FFELI(c![1],ll);
      if ll <> vv+ww then
          Print("Alarm: i=",i,"\n");
          Print("ll=",ll,"\nvv+ww=",vv+ww,"\n");
      fi;
      l := l + 1;
  od;
end;

CVEC.TEST.ADD2_COMPRESSED := function(p,d)
  local c,q,l,v,w,ll,vv,ww,i;
  q := p^d;
  if not(IsPrimePowerInt(q)) or q > 256 then
      Error("Only for those p^d for which compressed vectors are in GAP!");
  fi;
      
  c := CVEC.NewCVecClass(p,d,q);   # Length is q
  v := CVEC.New(c);
  w := CVEC.New(c);
  l := 1*[0..q-1];
  CVEC.INTREP_TO_CVEC(l,v);
  vv := ShallowCopy(l);
  CVEC.INTLI_TO_FFELI(c![1],vv);   # Change numbers into FFEs
  ConvertToVectorRep(vv);
  l := 0*[1..q];
  for i in [0..q-1] do
      CVEC.INTREP_TO_CVEC(l,w);
      ww := ShallowCopy(l);
      CVEC.INTLI_TO_FFELI(c![1],ww);
      ConvertToVectorRep(ww);
      CVEC.ADD2(w,v,1,q);
      ll := 0*[1..q];
      CVEC.CVEC_TO_INTREP(w,ll);
      CVEC.INTLI_TO_FFELI(c![1],ll);
      ConvertToVectorRep(ll);
      if ll <> vv+ww then
          Print("Alarm: i=",i,"\n");
          Print("ll=",ll,"\nvv+ww=",vv+ww,"\n");
      fi;
      l := l + 1;
  od;
end;

CVEC.TEST.ADD3 := function(p,d)
  local c,q,l,v,w,ll,vv,ww,i,u;
  q := p^d;
  if not(IsPrimePowerInt(q)) or q > MAXSIZE_GF_INTERNAL then
      Error("Test is only for those p^d that are implemented in GAP!");
  fi;
      
  c := CVEC.NewCVecClass(p,d,q);   # Length is q
  u := CVEC.New(c);
  v := CVEC.New(c);
  w := CVEC.New(c);
  l := 1*[0..q-1];
  CVEC.INTREP_TO_CVEC(l,v);
  vv := ShallowCopy(l);
  CVEC.INTLI_TO_FFELI(c![1],vv);   # Change numbers into FFEs
  l := 0*[1..q];
  ll := 0*[1..q];
  for i in [0..q-1] do
      CVEC.INTREP_TO_CVEC(l,w);
      ww := ShallowCopy(l);
      CVEC.INTLI_TO_FFELI(c![1],ww);
      CVEC.ADD3(u,w,v);
      CVEC.CVEC_TO_INTREP(u,ll);
      CVEC.INTLI_TO_FFELI(c![1],ll);
      if ll <> vv+ww then
          Print("Alarm: i=",i,"\n");
          Print("ll=",ll,"\nvv+ww=",vv+ww,"\n");
      fi;
      l := l + 1;
  od;
end;

CVEC.TEST.ADD3_COMPRESSED := function(p,d)
  local c,q,l,v,w,ll,vv,ww,i,u;
  q := p^d;
  if not(IsPrimePowerInt(q)) or q > 256 then
      Error("Only for those p^d for which compressed vectors are in GAP!");
  fi;
      
  c := CVEC.NewCVecClass(p,d,q);   # Length is q
  u := CVEC.New(c);
  v := CVEC.New(c);
  w := CVEC.New(c);
  l := 1*[0..q-1];
  CVEC.INTREP_TO_CVEC(l,v);
  vv := ShallowCopy(l);
  CVEC.INTLI_TO_FFELI(c![1],vv);   # Change numbers into FFEs
  ConvertToVectorRep(vv);
  l := 0*[1..q];
  for i in [0..q-1] do
      CVEC.INTREP_TO_CVEC(l,w);
      ww := ShallowCopy(l);
      CVEC.INTLI_TO_FFELI(c![1],ww);
      ConvertToVectorRep(ww);
      CVEC.ADD3(u,w,v);
      ll := 0*[1..q];
      CVEC.CVEC_TO_INTREP(u,ll);
      CVEC.INTLI_TO_FFELI(c![1],ll);
      ConvertToVectorRep(ll);
      if ll <> vv+ww then
          Print("Alarm: i=",i,"\n");
          Print("ll=",ll,"\nvv+ww=",vv+ww,"\n");
      fi;
      l := l + 1;
  od;
end;

CVEC.TEST.MUL1 := function(p,d)
  local c,i,l,ll,q,sc,v,vv,w;
  q := p^d;
  if not(IsPrimePowerInt(q)) or q > MAXSIZE_GF_INTERNAL then
      Error("Test is only for those p^d that are implemented in GAP!");
  fi;
      
  c := CVEC.NewCVecClass(p,d,q);   # Length is q
  v := CVEC.New(c);
  w := CVEC.New(c);
  l := 1*[0..q-1];
  CVEC.INTREP_TO_CVEC(l,v);
  vv := ShallowCopy(l);
  CVEC.INTLI_TO_FFELI(c![1],vv);   # Change numbers into FFEs
  ll := 0*[1..q];
  for i in [0..q-1] do
      sc := c![1]![12][i+1];
      CVEC.COPY(v,w);
      CVEC.MUL1(w,i,1,q);
      CVEC.CVEC_TO_INTREP(w,ll);
      CVEC.INTLI_TO_FFELI(c![1],ll);
      if ll <> sc * vv then
          Print("Alarm: i=",i,"\n");
          Print("ll=",ll,"\ni * vv=",vv,"\n");
      fi;
      l := l + 1;
  od;
end;

CVEC.TEST.MUL1_COMPRESSED := function(p,d)
  local c,i,l,ll,q,sc,v,vv,w;
  q := p^d;
  if not(IsPrimePowerInt(q)) or q > MAXSIZE_GF_INTERNAL then
      Error("Test is only for those p^d that are implemented in GAP!");
  fi;
      
  c := CVEC.NewCVecClass(p,d,q);   # Length is q
  v := CVEC.New(c);
  w := CVEC.New(c);
  l := 1*[0..q-1];
  CVEC.INTREP_TO_CVEC(l,v);
  vv := ShallowCopy(l);
  CVEC.INTLI_TO_FFELI(c![1],vv);   # Change numbers into FFEs
  ConvertToVectorRep(vv);
  for i in [0..q-1] do
      sc := c![1]![12][i+1];
      CVEC.COPY(v,w);
      CVEC.MUL1(w,i,1,q);
      ll := 0*[1..q];
      CVEC.CVEC_TO_INTREP(w,ll);
      CVEC.INTLI_TO_FFELI(c![1],ll);
      ConvertToVectorRep(ll);
      if ll <> sc * vv then
          Print("Alarm: i=",i,"\n");
          Print("ll=",ll,"\ni * vv=",vv,"\n");
      fi;
      l := l + 1;
  od;
end;

CVEC.TEST.MUL2 := function(p,d)
  local c,i,l,ll,q,sc,v,vv,w;
  q := p^d;
  if not(IsPrimePowerInt(q)) or q > MAXSIZE_GF_INTERNAL then
      Error("Test is only for those p^d that are implemented in GAP!");
  fi;
      
  c := CVEC.NewCVecClass(p,d,q);   # Length is q
  v := CVEC.New(c);
  w := CVEC.New(c);
  l := 1*[0..q-1];
  CVEC.INTREP_TO_CVEC(l,v);
  vv := ShallowCopy(l);
  CVEC.INTLI_TO_FFELI(c![1],vv);   # Change numbers into FFEs
  ll := 0*[1..q];
  for i in [0..q-1] do
      sc := c![1]![12][i+1];
      CVEC.MUL2(w,v,i);
      CVEC.CVEC_TO_INTREP(w,ll);
      CVEC.INTLI_TO_FFELI(c![1],ll);
      if ll <> sc * vv then
          Print("Alarm: i=",i,"\n");
          Print("ll=",ll,"\ni * vv=",vv,"\n");
      fi;
      l := l + 1;
  od;
end;

CVEC.TEST.MUL2_COMPRESSED := function(p,d)
  local c,i,l,ll,q,sc,v,vv,w;
  q := p^d;
  if not(IsPrimePowerInt(q)) or q > MAXSIZE_GF_INTERNAL then
      Error("Test is only for those p^d that are implemented in GAP!");
  fi;
      
  c := CVEC.NewCVecClass(p,d,q);   # Length is q
  v := CVEC.New(c);
  w := CVEC.New(c);
  l := 1*[0..q-1];
  CVEC.INTREP_TO_CVEC(l,v);
  vv := ShallowCopy(l);
  CVEC.INTLI_TO_FFELI(c![1],vv);   # Change numbers into FFEs
  ConvertToVectorRep(vv);
  for i in [0..q-1] do
      sc := c![1]![12][i+1];
      CVEC.MUL2(w,v,i);
      ll := 0*[1..q];
      CVEC.CVEC_TO_INTREP(w,ll);
      CVEC.INTLI_TO_FFELI(c![1],ll);
      ConvertToVectorRep(ll);
      if ll <> sc * vv then
          Print("Alarm: i=",i,"\n");
          Print("ll=",ll,"\ni * vv=",vv,"\n");
      fi;
      l := l + 1;
  od;
end;

CVEC.TEST.ADDMUL := function(p,d)
  local c,i,l,ll,lll,llll,q,u,v,w,z;
  q := p^d;
  if not(IsPrimePowerInt(q)) or q > MAXSIZE_GF_INTERNAL then
      Error("Test is only for those p^d that are implemented in GAP!");
  fi;
      
  c := CVEC.NewCVecClass(p,d,q);   # Length is q
  v := CVEC.New(c);
  w := CVEC.New(c);
  u := CVEC.New(c);
  z := CVEC.New(c);
  l := 1*[0..q-1];
  CVEC.INTREP_TO_CVEC(l,v);
  ll := [];
  for i in [0..q-1] do
      Add(ll,Random([0..q-1]));
  od;
  CVEC.INTREP_TO_CVEC(ll,w);
  lll := 0*[0..q-1];
  llll := ShallowCopy(lll);
  for i in [0..q-1] do
      CVEC.COPY(v,u);
      CVEC.ADDMUL(u,w,i,1,q);
      CVEC.MUL2(z,w,i);
      CVEC.ADD2(z,v,1,q);
      CVEC.CVEC_TO_INTREP(u,lll);
      CVEC.CVEC_TO_INTREP(z,llll);
      if lll <> llll then
          Print("Alarm: ADDMUL i=",i," ",lll,llll,"\n");
      fi;
  od;
end;

CVEC.TEST.ELM_CVEC := function(p,d)
  local c,el,i,l,q,v;
  q := p^d;
  if not(IsSmallIntRep(q)) then
      Error("Test is only for those p^d that are GAP small integers!");
  fi;

  c := CVEC.NewCVecClass(p,d,q);   # Length is q
  v := CVEC.New(c);
  l := 1*[0..q-1];
  CVEC.INTREP_TO_CVEC(l,v);
  for i in [1..q] do
      el := CVEC.ELM_CVEC(v,i);
      if q <= MAXSIZE_GF_INTERNAL then
          if el <> c![1]![12][i] then
              Print("Alarm: ELM_CVEC i=",i," ",el," ",c![1]![12][i],"      \n");
          fi;
      else
          if el <> i-1 then
              Print("Alarm: ELM_CVEC i=",i," ",el," ",i-1,"               \n");
          fi;
      fi;
  od;
end;
 
CVEC.TEST.ASS_CVEC := function(p,d)
  local c,i,l,q,v;
  q := p^d;
  if not(IsSmallIntRep(q)) then
      Error("Test is only for those p^d that are GAP small integers!");
  fi;

  c := CVEC.NewCVecClass(p,d,q);   # Length is q
  v := CVEC.New(c);
  l := 0*[0..q-1];
  for i in [1..q] do
      CVEC.ASS_CVEC(v,i,i-1);
  od;
  CVEC.CVEC_TO_INTREP(v,l);
  if l <> [0..q-1] then
      Print("Alarm ASS_CVEC p=",p," d=",d,"                  \n");
  fi;
  if q <= MAXSIZE_GF_INTERNAL then
      CVEC.MAKEZERO(v);
      # Try to assign finite field elements:
      for i in [1..q] do
          CVEC.ASS_CVEC(v,i,c![1]![12][i]);
      od;
      CVEC.CVEC_TO_INTREP(v,l);
      if l <> [0..q-1] then
          Print("Alarm ASS_CVEC FFE p=",p," d=",d,"                  \n");
      fi;
  fi;
end;
 
CVEC.TEST.POSITION_NONZERO_CVEC := function(p,d)
  local c,i,q,v,l;
  q := p^d;
  if not(IsSmallIntRep(q)) then
      Error("Test is only for those p^d that are GAP small integers!");
  fi;

  q := Minimum(q,256);   # just to reduce the length of the vectors
  c := CVEC.NewCVecClass(p,d,q);
  v := CVEC.New(c);
  if CVEC.POSITION_NONZERO_CVEC(v) <> q+1 then
      Print("Alarm POSITION_NONZERO_CVEC p=",p," d=",d," i=0        \n");
  fi;
  l := 1 * [0..q-1];
  l[1] := 1;
  for i in [1..q] do
      CVEC.ASS_CVEC(v,i,l[i]);
      if CVEC.POSITION_NONZERO_CVEC(v) <> i then
          Print("Alarm POSITION_NONZERO_CVEC p=",p," d=",d," i=",i,"       \n");
      fi;
      CVEC.ASS_CVEC(v,i,0);
  od;
end;

CVEC.TEST.POSITION_LAST_NONZERO_CVEC := function(p,d)
  local c,i,q,v,l;
  q := p^d;
  if not(IsSmallIntRep(q)) then
      Error("Test is only for those p^d that are GAP small integers!");
  fi;

  q := Minimum(q,256);   # just to reduce the length of the vectors
  c := CVEC.NewCVecClass(p,d,q);
  v := CVEC.New(c);
  if CVEC.POSITION_LAST_NONZERO_CVEC(v) <> 0 then
      Print("Alarm POSITION_LAST_NONZERO_CVEC p=",p," d=",d," i=0        \n");
  fi;
  l := 1 * [0..q-1];
  l[1] := 1;
  for i in [1..q] do
      CVEC.ASS_CVEC(v,i,l[i]);
      if CVEC.POSITION_LAST_NONZERO_CVEC(v) <> i then
          Print("Alarm POSITION_LAST_NONZERO_CVEC p=",p," d=",d," i=",
                i,"       \n");
      fi;
      CVEC.ASS_CVEC(v,i,0);
  od;
end;

CVEC.TEST.SCALARS := function(p,d)
  local c,i,j,l,l1,l2,l3,li,q,tab2,zero;
  q := p^d;
  if q > MAXSIZE_GF_INTERNAL then
      Error("Test is only for this p^d such that GF(p^d) is in GAP as FFE!");
  fi;

  # Make scalars class:
  c := CVEC.NewCVecClass(p,d,-1);

  # We now have a table:
  tab2 := ShallowCopy(c![1]![12]);

  # Now make scalars:
  l1 := [0..p-1];
  l2 := [];
  for i in [1..d] do
      Add(l2,l1);
  od;
  l3 := Cartesian(l2);
  l := List(l3,x->CSca(Reversed(x),c));

  SortParallel(tab2,l);
  
  Print("+\c");
  if q > 256 then
      li := List([1..256],i->Random([1..q]));
      Add(li,1); Add(li,2);  # check 0 and 1
  else
      li := [1..q];
  fi;
  for i in li do
      for j in [i..q] do
          if l[i]+l[j] <> l[Position(tab2,tab2[i]+tab2[j])] then
              Print("\nAlarm CSCA + p=",p," d=",d," a=",l[i]," b=",l[j],"\n");
          fi;
      od;
  od;
  Print("\r");

  Print("*\c");
  for i in li do
      for j in [i..q] do
          if l[i]*l[j] <> l[Position(tab2,tab2[i]*tab2[j])] then
              Print("\nAlarm CSCA * p=",p," d=",d," a=",l[i]," b=",l[j],"\n");
          fi;
      od;
  od;
  Print("\r");

  Print("-\c");
  for i in [1..q] do
      if -l[i] <> l[Position(tab2,-tab2[i])] then
          Print("\nAlarm CSCA ^-1 p=",p," d=",d," a=",l[i],"\n");
      fi;
  od;
  Print("\r");

  zero := CSca(0*[1..d],c);
  Print("/\c");
  for i in [1..q] do
      if l[i] <> zero and l[i]^-1 <> l[Position(tab2,tab2[i]^-1)] then
          Print("\nAlarm CSCA ^-1 p=",p," d=",d," a=",l[i],"\n");
      fi;
  od;
  Print("\r");
end;

CVEC.TEST.MATMUL := function(p,d)
  local a,aold,b,bold,c1,c2,c3,c4,ca,cb,f,fc,i,l,lev,q,r,s,t;
  if p^d > MAXSIZE_GF_INTERNAL then
      Error("Test is only for finite fields implemented in GAP");
      return;
  fi;
  f := GF(p,d);
  q := p^d;
  r := Random([100..150]);
  s := Random([100..150]);
  t := Random([100..150]);
  Print("\n     (doing ",r,"x",s," * ",s,"x",t,"...)\n");
  ca := CVEC.NewCVecClass(p,d,s);
  cb := CVEC.NewCVecClass(p,d,t);
  a := CMat([],ca);
  aold := [];
  for i in [1..r] do
      l := List([1..s],i->Random(f));
      Add(a,CVec(l,ca));
      Add(aold,l);
      if q <= 256 then ConvertToVectorRep(l,q); fi;
  od;
  ConvertToMatrixRep(aold);
  b := CMat([],cb);
  bold := [];
  for i in [1..s] do
      l := List([1..t],i->Random(f));
      Add(b,CVec(l,cb));
      Add(bold,l);
      if q <= 256 then ConvertToVectorRep(l,q); fi;
  od;
  ConvertToMatrixRep(bold);

  c1 := a * b;
  c2 := aold * bold;
  GreaseMat(b);
  c3 := a * b;
  UnGreaseMat(b);
  fc := ca![1];
  lev := fc![8];
  fc![8] := 0;
  c4 := a * b;
  fc![8] := lev;

  if List(c1,FFEList) <> List(c2,x->List(x,y->y)) then
      Print("Alarm p=",p," d=",d," std matmul            \n");
      Error("You can inspect c1, c2, c3, c4");
  fi;
  if c1 <> c3 then
      Print("Alarm p=",p," d=",d," greased matmul            \n");
      Error("You can inspect c1, c2, c3, c4");
  fi;
  if c1 <> c4 then
      Print("Alarm p=",p," d=",d," ungreased matmul            \n");
      Error("You can inspect c1, c2, c3, c4");
  fi;
end;


CVEC.TEST.DOALL := function()
  local inf;
  inf := InfoLevel(InfoWarning);
  SetInfoLevel(InfoWarning,0);  # Get rid of messages for Conway polynomials
  CVEC.TEST.ALLFFE("INTFFE_CONV",CVEC.TEST.INTFFE_CONVERSION);
  CVEC.TEST.ALLCHEAP("ADD2",CVEC.TEST.ADD2);
  CVEC.TEST.COMPRESSED_ALL("ADD2", CVEC.TEST.ADD2_COMPRESSED);
  CVEC.TEST.ALLCHEAP("ADD3",CVEC.TEST.ADD3);
  CVEC.TEST.COMPRESSED_ALL("ADD3", CVEC.TEST.ADD3_COMPRESSED);
  CVEC.TEST.ALLCHEAP("MUL1",CVEC.TEST.MUL1);
  CVEC.TEST.COMPRESSED_ALL("MUL1", CVEC.TEST.MUL1_COMPRESSED);
  CVEC.TEST.ALLCHEAP("MUL2",CVEC.TEST.MUL2);
  CVEC.TEST.COMPRESSED_ALL("MUL2", CVEC.TEST.MUL2_COMPRESSED);
  CVEC.TEST.ALLCHEAP("ADDMUL",CVEC.TEST.ADDMUL);
  CVEC.TEST.ALLCHEAP("ELM_CVEC",CVEC.TEST.ELM_CVEC);
  CVEC.TEST.ALLCHEAP("ASS_CVEC",CVEC.TEST.ASS_CVEC);
  CVEC.TEST.ALLFFE("POSITION_NONZERO_CVEC",CVEC.TEST.POSITION_NONZERO_CVEC);
  CVEC.TEST.ALLFFE("POSITION_LAST_NONZERO_CVEC",
                   CVEC.TEST.POSITION_LAST_NONZERO_CVEC);
  CVEC.TEST.ALLCHEAP("SCALARS",CVEC.TEST.SCALARS);
  CVEC.TEST.COMPRESSED_ALL("MATMUL",CVEC.TEST.MATMUL);
  Print("Testing MATMUL 2^9...\r");
  CVEC.TEST.MATMUL(2,9);
  Print("Testing MATMUL 3^10...\r");
  CVEC.TEST.MATMUL(3,10);
  Print("Testing MATMUL 31^3...\r");
  CVEC.TEST.MATMUL(31,3);
  Print("Testing MATMUL 257^1...\r");
  CVEC.TEST.MATMUL(257,1);
  SetInfoLevel(InfoWarning,inf);
end;

#############################################################################
# Benchmarks:
#############################################################################

CVEC.BENCH.ADD2 := function(p,d)
  local c,i,j,l,nr,q,r,r2,v,w,wordlen,table,vecsize,throughput;
  q := p^d;
  Print("CVEC.BENCH.ADD2:\n\n");
  Print("Working with vectors over GF(",p,",",d,").\n\n");
  l := 512;
  nr := 2^20;
  if q < 16 then nr := nr * 4; fi;   # some more for small fields
  table := [];
  repeat
    c := CVEC.NewCVecClass(p,d,l);
    wordlen := c![3];
    vecsize := CVEC.BYTESPERWORD*wordlen;
    Print("Doing vectors of length ",l," using ", vecsize," bytes each...\n");
    Print("Initialising...\c");
    v := CVEC.New(c);
    w := CVEC.New(c);
    j := 0;
    for i in [1..l] do
        v[i] := j;
        j := j + 1;
        if j >= q then j := 0; fi;
    od;
    Print("done.\n");
    Print("Doing ",nr," times ADD2 of such vectors...\c");
    r := Runtime();
    for i in [1..nr] do
        CVEC.ADD2(w,v,0,0);
    od;
    r2 := Runtime();
    Print("done.\n");
    throughput := QuoInt(nr*vecsize*1000,(r2-r)*1024*1024);  # in MB/s
    Print("Time: ",r2-r," ms which means: ",throughput," MB/s throughput.\n\n");
    Add(table,[vecsize,throughput]);
    l := l * 2;
    nr := nr / 2;
    Unbind(v);
    Unbind(w);
  until vecsize >= 2^26 or not(IsSmallIntRep(l)); 
  # do until vectors >= 64MB or the length is no longer an immediate int
  return table;
end;

CVEC.BENCH.ADDOLD := function(p,d)
  local i,j,l,li,me,nr,q,r,r2,table,throughput,v,vecsize,w;
  q := p^d;
  Print("CVEC.BENCH.ADDOLD:\n\n");
  Print("Working with vectors over GF(",p,",",d,").\n\n");
  l := 512;
  nr := 2^20;
  if q < 16 then nr := nr * 4; fi;   # some more for small fields
  table := [];
  repeat
    v := 0*[1..l]; ConvertToVectorRep(v,q);
    w := ShallowCopy(v);
    if p = 2 and d = 1 then
        vecsize := SHALLOW_SIZE(v)-4;
    else
        vecsize := SHALLOW_SIZE(v)-8;
    fi;
    Print("Doing vectors of length ",l," using ", vecsize," bytes each...\n");
    Print("Initialising...\c");
    li := Elements(GF(q));
    j := 0;
    for i in [1..l] do
        v[i] := li[j+1];
        j := j + 1;
        if j >= q then j := 0; fi;
    od;
    Print("done.\n");
    me := ApplicableMethod(AddRowVector,[w,v]);
    Print("Doing ",nr," times AddRowVector of such vectors...\c");
    r := Runtime();
    for i in [1..nr] do
        me(w,v);
    od;
    r2 := Runtime();
    Print("done.\n");
    throughput := QuoInt(nr*vecsize*1000,(r2-r)*1024*1024);  # in MB/s
    Print("Time: ",r2-r," ms which means: ",throughput," MB/s throughput.\n\n");
    Add(table,[vecsize,throughput]);
    l := l * 2;
    nr := nr / 2;
    Unbind(v);
    Unbind(w);
  until vecsize >= 2^23 or not(IsSmallIntRep(l)); 
  # do until vectors >= 64MB or the length is no longer an immediate int
  return table;
end;

CVEC.BENCH.MEASUREACCURACY := function()
  local c,d,i,j,l,nr,p,q,r,r2,sqsum,sum,times,throughput,v,vecsize,w,wordlen,x;
  p := 7;
  d := 4;
  q := p^d;
  l := 524288; # 16384;
  nr := 1024;  # 32768;
  times := 20;
  c := CVEC.NewCVecClass(p,d,l);
  wordlen := c![3];
  vecsize := CVEC.BYTESPERWORD*wordlen;
  Print("Doing vectors of length ",l," using ", vecsize," bytes each...\n");
  Print("Initialising...\c");
  v := CVEC.New(c);
  x := [1,2,3];
  w := CVEC.New(c);
  j := 0;
  for i in [1..l] do
      v[i] := j;
      j := j + 1;
      if j >= q then j := 0; fi;
  od;
  Print("done.\n");
  Print("Doing ",nr," times ADD2 of such vectors...\n");
  sum := 0;
  sqsum := 0;
  for j in [1..times] do
      r := Runtime();
      for i in [1..nr] do
          CVEC.ADD2(w,v,0,0);
      od;
      r2 := Runtime();
      throughput := QuoInt(nr*vecsize*1000,(r2-r)*1024);  # in kB/s
      Print("Time: ",r2-r," ms which means: ",throughput," kB/s throughput.\n");
      sum := sum + throughput;
      sqsum := sqsum + throughput^2;
      w := CVEC.New(c);   # see to it, that w changes its place in memory
  od;
  Print("Average: ",QuoInt(sum,times * 1000)," MB/s ",
        " Variance: ",
        QuoInt(QuoInt(sqsum,times)-QuoInt(sum,times)^2,1000000),
               " (MB/s)^2\n\n");
  p := 2;
  d := 16;
  q := p^d;
  l := 524288; # 16384;
  nr := 1024;  # 32768;
  times := 20;
  c := CVEC.NewCVecClass(p,d,l);
  wordlen := c![3];
  vecsize := CVEC.BYTESPERWORD*wordlen;
  Print("Doing vectors of length ",l," using ", vecsize," bytes each...\n");
  Print("Initialising...\c");
  v := CVEC.New(c);
  x := [1,2,3];
  w := CVEC.New(c);
  j := 0;
  for i in [1..l] do
      v[i] := j;
      j := j + 1;
      if j >= q then j := 0; fi;
  od;
  Print("done.\n");
  Print("Doing ",nr," times ADD2 of such vectors...\n");
  sum := 0;
  sqsum := 0;
  for j in [1..times] do
      r := Runtime();
      for i in [1..nr] do
          CVEC.ADD2(w,v,0,0);
      od;
      r2 := Runtime();
      throughput := QuoInt(nr*vecsize*1000,(r2-r)*1024);  # in kB/s
      Print("Time: ",r2-r," ms which means: ",throughput," kB/s throughput.\n");
      sum := sum + throughput;
      sqsum := sqsum + throughput^2;
      w := CVEC.New(c);   # see to it, that w changes its place in memory
  od;
  Print("Average: ",QuoInt(sum,times * 1000)," MB/s ",
        " Variance: ",
        QuoInt(QuoInt(sqsum,times)-QuoInt(sum,times)^2,1000000),
               " (MB/s)^2\n\n");
end;

