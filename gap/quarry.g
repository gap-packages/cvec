#############################################################################
# Lazy grease:
#############################################################################

InstallMethod( LazyGreaser, "for a vector and a positive grease level",
  [IsObject, IsPosInt],
  function( vecs, lev )
    local lg;
    lg := rec( vecs := vecs, tab := vecs{[]}, ind := [], lev := lev, 
               fs := Size(BaseDomain(vecs)) );
    if lg.fs > 65536 then
        Error("Lazy grease only supported for fields with <= 65536 elements");
        return;
    fi;
    return Objectify( NewType(LazyGreaserFamily, IsLazyGreaser), lg );
  end );

InstallMethod( ViewObj, "for a lazy greaser",
  [IsLazyGreaser],
  function( lg )
    Print("<lazy greaser level ",lg!.lev," with ",Length(lg!.tab)," vectors>");
  end );

InstallMethod( GetLinearCombination, 
  "for a lazy greaser, a vector, an offset, and a list of integers",
  [IsLazyGreaser, IsVector, IsPosInt, IsList],
  function( lg, v, offset, pivs )
    # offset must be congruent 1 mod lev
    local group,i,pos,w;
    pos := NumberFFVector(v{Reversed(pivs)},lg!.fs)+1;
    if pos = 1 then return 0; fi;
    group := (offset-1) / lg!.lev + 1;
    #if not IsBound(lg!.ind[group]) then
    #    lg!.ind[group] := [];
    #fi;
    if not IsBound(lg!.ind[group][pos]) then
        # Cut away all trailing zeroes:
        i := Length(pivs);
        while i > 0 and IsZero(v[pivs[i]]) do i := i - 1; od;
        # i = 0 does not happen!
        if i = 1 then
            w := v[pivs[1]] * lg!.vecs[offset];
        else
            w := GetLinearCombination(lg,v,offset,pivs{[1..i-1]});
            if w = 0 then
                w := v[pivs[i]] * lg!.vecs[offset+i-1];
            else
                w := w + v[pivs[i]] * lg!.vecs[offset+i-1];
            fi;
        fi;
        Add(lg!.tab,w);
        lg!.ind[group][pos] := Length(lg!.tab);
    else
        w := lg!.tab[lg!.ind[group][pos]];
    fi;
    return w;
  end );

InstallMethod( GetLinearCombination, 
  "for a lazy greaser, a cvec, an offset, and a list of integers",
  [IsLazyGreaser, IsCVecRep, IsPosInt, IsList],
  function( lg, v, offset, pivs )
    # the vecs entry of the lazy greaser must be a cmat!
    # offset must be congruent 1 mod lev
    local group,i,pos,w;
    pos := CVEC_GREASEPOS(v,pivs);
    if pos = 1 then return 0; fi;
    group := (offset-1) / lg!.lev + 1;
    if not IsBound(lg!.ind[group]) then
        lg!.ind[group] := [];
    fi;
    if not IsBound(lg!.ind[group][pos]) then
        # Cut away all trailing zeroes:
        i := Length(pivs);
        while i > 0 and IsZero(v[pivs[i]]) do i := i - 1; od;
        # i = 0 does not happen!
        if i = 1 then
            w := v[pivs[1]] * lg!.vecs[offset];
        else
            w := GetLinearCombination(lg,v,offset,pivs{[1..i-1]});
            if w = 0 then
                w := v[pivs[i]] * lg!.vecs[offset+i-1];
            else
                w := w + v[pivs[i]] * lg!.vecs[offset+i-1];
            fi;
        fi;
        Add(lg!.tab,w);
        lg!.ind[group][pos] := Length(lg!.tab);
        return w;
    else
        return lg!.tab[lg!.ind[group][pos]];
    fi;
  end );

CVEC_TESTLAZY := function(m,lev)
  local erg,f,i,j,l,offset,newpos,poss,v,w;
  v := ShallowCopy(m[1]);
  l := LazyGreaser(m,lev);
  f := BaseDomain(m);
  offset := Random(1,Length(m)-lev+1);
  offset := QuoInt(offset-1,lev)*lev + 1;  # make it congruent 1 mod lev
  for i in [1..10000] do
      w := Zero(v);
      poss := [];
      for j in [1..lev] do
          repeat
              newpos := Random([1..Length(v)]);
          until not newpos in poss;
          Add(poss,newpos);
          v[poss[j]] := Random(f);
          w := w + v[poss[j]] * m[offset+j-1];
      od;
      erg := GetLinearCombination(l,v,offset,poss);
      if not((erg = 0 and IsZero(w)) or w = erg) then
          Error();
      fi;
      Print(i,"\r");
  od;
  Print("\n");
  return l;
end;

  if IsBound(basis.lazygreaser) and basis.lazygreaser <> fail then
    # The grease case:
    lev := basis.lazygreaser!.lev;
    i := 1;
    mo := -One(vec[1]);
    while i+lev-1 <= len do
      pivs := basis.pivots{[i..i+lev-1]};
      j := lev;
      while j > 0 and pivs[j] < firstnz do j := j - 1; od;
      if j > 0 then    # Otherwise, there is nothing to do at all
        lc := GetLinearCombination(basis.lazygreaser,vec,i,pivs);
        #lc := glc(basis.lazygreaser,vec,i,pivs);
        if lc <> 0 then   # 0 indicates the zero linear combination
          if dec <> false and dec <> true then
            for j in [i..i+lev-1] do
              dec[j] := vec[basis.pivots[j]];
            od;
          fi;
          AddRowVector( vec, lc, mo );
        fi;
      fi;
      i := i + lev;
    od;
    # Now go to the standard case for the rest, starting at i
  else
    i := 1;
    # The non-grease case starts from the beginning
  fi;

  # we have to work without the lazy greaser:
  ...

InstallMethod( EmptySemiEchelonBasis, "GAP method", [IsObject],
  function( vec )
    return rec( vectors := MatrixNC([],vec), pivots := [], 
                lazygreaser := fail, helper := vec{[1]} );
    # The lazygreaser component must always be bound!
    # The helper is needed for the kernel cleaner for CVecs
  end );

InstallMethod( EmptySemiEchelonBasis, "GAP method", [IsObject, IsPosInt],
  function( vec, greaselev )
    local r;
    r := rec( vectors := MatrixNC([],vec), pivots := [], helper := vec{[1]} );
    # helper is needed for kernel cleaner
    r.lazygreaser := LazyGreaser( r.vectors, greaselev );
    return r;
  end );

      if IsBound(basis.lazygreaser) then
        # In the grease case, we do full-echelon form within the grease block:
        for j in [i..len] do
          c := basis.vectors[j][newpiv];
          if not IsZero(c) then
            AddRowVector( basis.vectors[j], basis.vectors[len+1], -c );
          fi;
        od;
      fi;

#############################################################################
# Lazy grease:
#############################################################################

BindGlobal( "LazyGreaserFamily", NewFamily("LazyGreaserFamily") );
DeclareCategory( "IsLazyGreaser", IsComponentObjectRep );
DeclareOperation( "LazyGreaser", [IsObject, IsPosInt] );
DeclareOperation( "GetLinearCombination", 
  [IsLazyGreaser, IsObject, IsPosInt, IsList] );


# From linalg.gi, early tries for minimal polynomial:
# The rest can probably go at some stage:

InstallGlobalFunction( CVEC_RelativeOrderPoly, function( m, v, subb, indetnr )
  # v must not lie in subb, a semi echelonised basis of a subspace W, m a matrix
  # v must already be cleaned with subb!
  # Returns a record:
  # Gives back a new semi echelonised basis of V/W (component b), together 
  # with the relative order polynomial of v+W in V/W (component ordpol),
  # v'=v*ordpol(m) in subb, and an invertible square matrix A with
  # A*[v,vm,vm^2,...,vm^{d-1}] = b (to write vectors in V/W in terms of
  # [v+W,vm+W,...]. Also a list vl containing [v,v*m,v*m^2,...,v*m^{d-1}]
  # is bound.
  # The original v is untouched!
  local A,B,b,closed,d,dec,f,fam,i,l,lambda,o,ordpol,vcopy,vl,vv;
  f := BaseDomain(m);
  o := One(f);
  fam := FamilyObj(o);
  b := EmptySemiEchelonBasis(v);
  dec := ZeroMutable(v);
  CleanRow(b,ShallowCopy(v),true,dec);  # this puts v into b as first vector
  lambda := [dec{[1]}];
  vl := [v];
  while true do
      v := v * m;
      Add(vl,v);
      vcopy := ShallowCopy(v);
      CleanRow(subb,vcopy,false,fail);
      closed := CleanRow(b,vcopy,true,dec);
      if closed then break; fi;
      # now dec{[1..Length(b.vectors)]} * b.vectors = v
      # however, we need to express vectors in terms of the v's, so we 
      # have to invert the matrix of the dec's, this we do later on:
      Add(lambda,dec{[1..Length(b.pivots)]});
  od;
  d := Length(b.pivots);
  Unbind(vl[d+1]);  # this is linear dependent from the first d vectors!
  # we have the lambdas, expressing v*m^(i-1) in terms of the semiechelon
  # basis, now we have to express v*m^d in terms of the v*m^(i-1), that
  # means inverting a matrix: 
  B := CVEC_ZeroMat(d,CVecClass(lambda[d]));
  for i in [1..d] do
      CopySubVector(lambda[i],B[i],[1..i],[1..i]);
  od;
  A := B^-1;
  l := - dec{[1..d]} * A;
  l := Unpack(l);
  Add(l,o);
  ConvertToVectorRep(l,Size(f));
  ordpol := UnivariatePolynomialByCoefficients(fam,l,indetnr);
  vv := l[1] * vl[1];
  for i in [2..Length(vl)] do
      AddRowVector(vv,vl[i],l[i]);
  od;
  return rec( b := b, A := A, ordpol := ordpol, v := vv, vl := vl );
end );

InstallGlobalFunction( CVEC_CalcOrderPoly, 
function( opi, v, i, indetnr )
  local coeffs,g,h,j,ordpol,w;
  ordpol := [];  # comes factorised
  while i >= 1 do
      coeffs := v{opi.ranges[i]};
      if IsZero(coeffs) then
          i := i - 1;
          continue;
      fi;
      coeffs := Unpack(coeffs);
      h := UnivariatePolynomialByCoefficients(opi.fam,coeffs,indetnr);
      g := opi.rordpols[i]/Gcd(opi.rordpols[i],h);
      Add(ordpol,g);
      # This is the part coming from the ith cyclic space, now go down:
      coeffs := CoefficientsOfUnivariatePolynomial(g);
      w := coeffs[1]*v;
      for j in [2..Length(coeffs)] do
          v := v * opi.mm;
          AddRowVector(w,v,coeffs[j]);
      od;
      # Now w is one subspace lower
      v := w;
      i := i - 1;
      if IsZero(v) then break; fi;
      #Print("i=",i," new vector: ");
      #Display(v);
  od;
  return Product(ordpol);
end );
    
BindGlobal( "CVEC_CalcOrderPolyEstimate", 
function( est, opi, v, i, indetnr )
  local c,coeffs,g,h,j,k,op,ordpol,w;
  ordpol := [];  # comes factorised
  op := UnivariatePolynomialByCoefficients(opi.fam,[opi.o],indetnr);
  k := i;
  while true do   # break is used near the end
      coeffs := Unpack(v{opi.ranges[k]});
      h := UnivariatePolynomialByCoefficients(opi.fam,coeffs,indetnr);
      c := Gcd(opi.rordpols[k],h);
      g := opi.rordpols[k]/c;
      Add(ordpol,g);
      op := op * g;
      #Print("Relative order pol: ",g,"\n");
      # This is the part coming from the ith cyclic space, now go down:
      coeffs := CoefficientsOfUnivariatePolynomial(g);
      w := coeffs[1]*v;
      for j in [2..Length(coeffs)] do
          v := v * opi.mm;
          AddRowVector(w,v,coeffs[j]);
      od;
      # Now w is one subspace lower
      v := w;
      k := k - 1;
      if IsZero(v) then break; fi;
      if k = 0 then break; fi;
      #Print("Check:",Degree(est[i-1])," ", Degree(est[k]*op),"\n");
      if IsZero(est[i-1] mod (est[k] * op)) then
          Print("|\c");
          return est[i-1];
      fi;
      #Print("i=",i," new vector: ");
      #Display(v);
  od;
  return op;
end );
    
InstallGlobalFunction( CVEC_NewMinimalPolynomialMC, 
function( m, eps, verify, indetnr )
  # a new try using Cheryl's ideas for cyclic matrices generalised to 
  # an arbitrary matrix m
  # eps is a cyclotomic which is an upper bound for the error probability
  # verify is a boolean indicating, whether the result should be verified,
  # thereby proving correctness
  # indetnr is the number of an indeterminate
  local A,b,col,d,g,i,irreds,j,l,lowbounds,mm,mult,multmin,nrunclear,ns,opi,
        ordpol,p,pivs,prob,proof,re,v,vl,vli,w,zero;
  zero := ZeroMutable(m[1]);
  pivs := [1..Length(m)];
  b := EmptySemiEchelonBasis(zero);
  v := Matrix([],m[1]);   # start vectors for the spinning
  vl := Matrix([],m[1]);  # start vectors together with their images under m
  A := [];   # base changes within each subquotient
  l := [];   # a list of semi echelon bases for the subquotients
  # order polynomial infrastructure (grows over time):
  opi := rec( f := BaseDomain(m),
              d := [],
              ranges := [],
              rordpols := [],   # list of relative order polynomials
              ordpols := [],    # list of real order polynomials
              mm := fail,       # will be base-changed m later on
            );  
  opi.o := One(opi.f);
  opi.fam := FamilyObj(opi.o);
  Print(Length(m),":\c");
  while Length(pivs) > 0 do
      p := pivs[1];
      w := ShallowCopy(zero);
      w[p] := opi.o;
      Add(v,w);   # FIXME: needed?
      re := CVEC_RelativeOrderPoly(m,w,b,indetnr);
      d := Degree(re.ordpol);
      Print(d," \c");
      Add(opi.rordpols,re.ordpol);
      Add(opi.d,d);
      Add(opi.ranges,[Length(b.vectors)+1..Length(b.vectors)+d]);
      Add(l,re.b);  # FIXME: needed?
      Add(A,re.A);  # FIXME: needed?
      Append(vl,re.vl);
      pivs := Difference(pivs,re.b.pivots);
      # Add re.b to b:
      Append(b.vectors,re.b.vectors);
      Append(b.pivots,re.b.pivots);
      # Note that the latter does not cost too much memory as the vectors
      # are not copied.
  od;
  Print("\n");
  if Degree(opi.rordpols[1]) = Length(m) then
      return rec( minpoly := opi.rordpols[1],
                  charpoly := opi.rordpols[1],
                  opi := opi );
      # FIXME: Return a consistent result!
  fi;
  Info(InfoCVec,2,"Doing basechange...");
  # Now we have spun up the whole space, that is, vl is a basis of the full
  # row space
  # Now we do the base change:
  vli := vl^-1;
  opi.mm := vl*m*vli;
  Unbind(vl);  # no longer needed
  Unbind(vli); # dito

  Info(InfoCVec,2,"Factoring relative order polynomials...");
  # Factor all parts:
  col := List(opi.rordpols,f->Collected(Factors(f)));
  # Collect all irreducible factors:
  irreds := [];
  mult := [];
  lowbounds := [];
  multmin := [];
  for l in col do
      for i in l do
          p := Position(irreds,i[1]);
          if p = fail then
              Add(irreds,i[1]);
              Add(mult,i[2]);
              Add(lowbounds,i[2]);
              Add(multmin,0);
              p := Sortex(irreds);
              mult := Permuted(mult,p);
              lowbounds := Permuted(lowbounds,p);
          else
              mult[p] := mult[p] + i[2];
              if i[2] > lowbounds[p] then
                  lowbounds[p] := i[2];
              fi;
          fi;
      od;
  od;
  nrunclear := 0;   # number of irreducible factors the multiplicity of which
                    # are not yet known
  for i in [1..Length(irreds)] do
      if mult[i] > lowbounds[i] then
          nrunclear := nrunclear + 1;
      fi;
  od;
  Info(InfoCVec,2,"Number of irreducible factors in charpoly: ",Length(irreds),
                  " mult. in minpoly unknown: ",nrunclear);

  ordpol := Lcm(opi.rordpols); # this is a lower bound for the minpoly
                               # in particular, it is a multiple of rordpols[1]
  i := 2;
  p := 1/Size(opi.f);
  proof := false;
  repeat   # until verification said "OK"
      # This is an upper estimate of the probability not to find a generator
      # of a cyclic space:
      prob := p;   # we already have for one vector the order polynomial
      Info(InfoCVec,2,"Calculating order polynomials...");
      while i <= Length(opi.rordpols) do
          v := ShallowCopy(zero);
          v[opi.ranges[i][1]] := opi.o;
          g := CVEC_CalcOrderPoly(opi,v,i,indetnr);
          if not(IsZero(ordpol mod g)) then
              ordpol := Lcm(ordpol,g);
          fi;
          if Degree(ordpol) = Length(m) then   # a cyclic matrix!
              break;
          fi;
          prob := prob * p;  # probability to have missed one Jordan block
          Print( "Probability to have them all (%%): ",
                 Int((1-prob)^nrunclear*1000),"\n");
          if 1-(1-prob)^nrunclear < eps then
              break;   # this is the probability to have missed one
          fi;
          i := i + 1;
      od;

      Info(InfoCVec,2,"Checking multiplicities...");
      nrunclear := 0;
      for j in [1..Length(irreds)] do
          multmin[j] := CVEC_FactorMultiplicity(ordpol,irreds[j]);
          if multmin[j] < mult[j] then
              nrunclear := nrunclear + 1;
          fi;
      od;
      if nrunclear = 0 then proof := true; break; fi;   # result is correct!

      if verify then
          Info(InfoCVec,2,"Verifying result (",nrunclear,
               " unclear multiplicities) ...");
          proof := true;  # will be set to false once we discover something
          for j in [1..Length(irreds)] do
              if multmin[j] < mult[j] then
                  Info(InfoCVec,2,"Working on factor: ",irreds[j],
                                  " multiplicity: ",multmin[j]);
                  mm := Value(irreds[j],opi.mm)^multmin[j];
                  ns := NullspaceMatMutableX(mm);
                  if Length(ns) < mult[j] then
                      proof := false;
                      break;
                  fi;
              fi;
          od;
      fi;
  until not(verify) or proof;

  return rec(minpoly := ordpol,
             charpoly := Product( opi.rordpols ),
             opi := opi,
             irreds := irreds,
             mult := mult,
             multmin := multmin);
end );

InstallGlobalFunction( CVEC_NewMinimalPolynomial, function( m, indetnr )
  # a new try using Cheryl's ideas for cyclic matrices generalised to 
  # an arbitrary matrix m
  local A,b,d,est,g,i,l,opi,ordpol,p,pivs,re,v,vl,vli,w,zero;
  zero := ZeroMutable(m[1]);
  pivs := [1..Length(m)];
  b := EmptySemiEchelonBasis(zero);
  v := Matrix([],m[1]);   # start vectors for the spinning
  vl := Matrix([],m[1]);  # start vectors together with their images under m
  A := [];   # base changes within each subquotient
  l := [];   # a list of semi echelon bases for the subquotients
  # order polynomial infrastructure (grows over time):
  opi := rec( f := BaseDomain(m),
              d := [],
              ranges := [],
              rordpols := [],   # list of relative order polynomials
              ordpols := [],    # list of real order polynomials
              mm := fail,       # will be base-changed m later on
            );  
  opi.o := One(opi.f);
  opi.fam := FamilyObj(opi.o);
  Print(Length(m),":\c");
  while Length(pivs) > 0 do
      p := pivs[1];
      w := ShallowCopy(zero);
      w[p] := opi.o;
      Add(v,w);   # FIXME: needed?
      re := CVEC_RelativeOrderPoly(m,w,b,indetnr);
      d := Degree(re.ordpol);
      Print(d," \c");
      Add(opi.rordpols,re.ordpol);
      Add(opi.d,d);
      Add(opi.ranges,[Length(b.vectors)+1..Length(b.vectors)+d]);
      Add(l,re.b);  # FIXME: needed?
      Add(A,re.A);  # FIXME: needed?
      Append(vl,re.vl);
      pivs := Difference(pivs,re.b.pivots);
      # Add re.b to b:
      Append(b.vectors,re.b.vectors);
      Append(b.pivots,re.b.pivots);
      # Note that the latter does not cost too much memory as the vectors
      # are not copied.
  od;
  Print("\nDoing basechange...\c");
  # Now we have spun up the whole space, that is, vl is a basis of the full
  # row space
  # Now we do the base change:
  vli := vl^-1;
  opi.mm := vl*m*vli;
  Unbind(vl);  # no longer needed
  Unbind(vli); # dito
  ordpol := opi.rordpols[1];
  Print("done\nCalculating order polynomials...\c");
  est := [opi.rordpols[1]];
  for i in [2..Length(opi.rordpols)] do
      v := ShallowCopy(zero);
      v[opi.ranges[i][1]] := opi.o;
      g := CVEC_CalcOrderPolyEstimate(est,opi,v,i,indetnr);
      if g <> ordpol then
          ordpol := Lcm(ordpol,g);
      fi;
      est[i] := ordpol;
      Print(i,"(",Length(opi.rordpols),"):",Degree(ordpol)," \c");
      if Degree(ordpol) = Length(m) then   # a cyclic matrix!
          break;
      fi;
  od;
  return rec(minpoly := ordpol,charpoly := Product( opi.rordpols ),opi := opi);
end );

# From linalg.gd, early tries for the minimal polynomial:
# The rest can probably be deleted later on:
DeclareGlobalFunction( "CVEC_RelativeOrderPoly" );
DeclareGlobalFunction( "CVEC_CalcOrderPoly" );
DeclareGlobalFunction( "CVEC_NewMinimalPolynomial" );
DeclareGlobalFunction( "CVEC_NewMinimalPolynomialMC" );

