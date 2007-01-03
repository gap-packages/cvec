QuickRandomize := function(m)
  local f,i,j,n,posx,posy,urposx,urposy;
  f := BaseDomain(m);
  if Length(m) < 97 then
      Randomize(m);
      return;
  fi;
  n := ExtractSubMatrix(m,[1..97],[1..97]);
  Randomize(n);
  for i in [1..QuoInt(RowLength(m)+96,97)] do
      for j in [1..QuoInt(Length(m)+96,97)] do
          posx := [(i-1)*97+1..Minimum(RowLength(m),i*97)];
          posy := [(j-1)*97+1..Minimum(Length(m),j*97)];
          urposx := [1..Length(posx)];
          urposy := [1..Length(posy)];
          CopySubMatrix(Random(f)*n,m,urposy,posy,urposx,posx);
      od;
  od;
end;
  
QuickRandomMat := function(n,m,p,d)
  local cl,i,j,l,le,nrblocks,q,qadic,r,rs,tab;

  qadic := function(n,p,le) 
    local l,x; 
    l := []; 
    while le > 0 do
        x := QuotientRemainder(n,p);
        Add(l,x[2]); 
        n := x[1];
        le := le - 1;
    od; 
    return l; 
  end;

  q := p^d;
  if q > 1024 then Error("only q <= 1024 supported"); fi;

  le := LogInt(1024,q);
  tab := List([0..q^le-1],x->qadic(x,q,le));

  cl := CVecClass(p,d,m);
  l := 0*[1..n];
  nrblocks := QuoInt(m+le-1,le);
  r := ListWithIdenticalEntries(le*nrblocks,0);
  rs := RandomSource(IsMersenneTwister);
  for i in [1..n] do
      for j in [1..nrblocks] do
          r{[1+(j-1)*le..j*le]} := 
               tab[RandomIntegerMT(rs!.state,10) mod q^le + 1];
      od;
      while Length(r) > n do Unbind(r[Length(r)]); od;
      l[i] := CVec(r,cl);
  od;
  return CMat(l,cl);
end;

MatMulSpeedTest := function(p,d,what)
  local a,b,f,i,l,m,mm,n,reps,t,ti,x;
  f := GF(p,d);
  l := [];
  Print("Randomizing 2 matrices n=",Maximum(what),"...\c");
  m := QuickRandomMat(Maximum(what),Maximum(what),p,d);
  mm := QuickRandomMat(Maximum(what),Maximum(what),p,d);
  Print("done.\n");
  for n in what do
      a := ExtractSubMatrix(m,[1..n],[1..n]);
      b := ExtractSubMatrix(mm,[1..n],[1..n]);
      t := Runtime();
      x := a*b;
      #x := MultiplyWinograd2(a,b,false,n/2);
      t := Runtime()-t;
      if t < 5000 then
          if t = 0 then 
              reps := 2000;
          else
              reps := QuoInt(5000,t);
          fi;
          t := Runtime();
          for i in [1..reps] do
              x := a*b;
              #x := MultiplyWinograd2(a,b,false,n/2);
          od;
          t := Runtime()-t;
      else
          reps := 1;
      fi;
      ti := FLOAT_INT(t)/FLOAT_INT(reps);
      Add(l,[n,ti]);
      Print("Field: GF(",p,",",d,"), size: ",n,", time: ",
            STRING_FLOAT(ti)," [ms]\n");
  od;
  return l;
end;

