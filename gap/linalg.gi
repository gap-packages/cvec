#############################################################################
##
#W  linalg.gi               GAP 4 package `cvec'                
##                                                            Max Neunhoeffer
##
#Y  Copyright (C)  2005,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
##
##  This file contains the higher levels for efficient implementation of
##  some linear algebra routines for compact vectors over finite fields. 
##

#############################################################################
# Cleaning and semi-echelonised bases:
#############################################################################

BindGlobal( "CVEC_CleanRow", function( basis, vec, extend, dec)
  local c,firstnz,i,j,lc,len,lev,mo,newpiv,pivs;
  # INPUT
  # basis: record with fields
  #        pivots   : integer list of pivot columns of basis matrix
  #        vectors : matrix of basis vectors in semi echelon form
  # and optionally:
  #        lazygreaser : a lazygreaser object for the vectors
  # vec  : vector of same length as basis vectors
  # extend : boolean value indicating whether the basis will we extended
  #          note that for the greased case also the basis vectors before
  #          the new one may be changed
  # OUTPUT
  # returns decomposition of vec in the basis, if possible.
  # otherwise returns 'fail' and adds cleaned vec to basis and updates
  # pivots
  # NOTES
  # destructive in both arguments

  # Clear dec vector if given:
  if dec <> fail then
    MultRowVector(dec,Zero(dec[1]));
  fi;
  
  # First a little shortcut:
  firstnz := PositionNonZero(vec);
  if firstnz > Length(vec) then
      return true;
  fi;

  len := Length(basis.vectors);
  i := 1;

  for j in [i..len] do
    if basis.pivots[j] >= firstnz then
      c := vec[ basis.pivots[ j ] ];
      if not IsZero( c ) then
        if dec <> fail then
          dec[ j ] := c;
        fi;
        AddRowVector( vec, basis.vectors[ j ], -c );
      fi;
    fi;
  od;

  newpiv := PositionNonZero( vec );
  if newpiv = Length( vec ) + 1 then
    return true;
  else
    if extend then
      c := vec[newpiv]^-1;
      MultRowVector( vec, vec[ newpiv ]^-1 );
      if dec <> fail then
        dec[len+1] := c;
      fi;
      Add( basis.vectors, vec );
      Add( basis.pivots, newpiv );
    fi;
    return false;
  fi;
end );
    
InstallMethod( CleanRow, 
  "GAP method for a record, a vector, and a boolean or vector", 
  [IsRecord, IsObject, IsBool, IsObject], CVEC_CleanRow );

InstallMethod( CleanRow, 
  "kernel method for a record, a cvec, and a boolean or cvec", 
  [IsRecord, IsCVecRep, IsBool, IsObject], CVEC_CLEANROWKERNEL );

InstallMethod( EmptySemiEchelonBasis, "for a sample vector", [IsObject],
  function( vec )
    return rec( vectors := MatrixNC([],vec),pivots := [],
                helper := ZeroVector(vec,1) );
    # The helper is needed for the kernel cleaner for CVecs
  end );

InstallMethod( EmptySemiEchelonBasis, "for a sample vector", [IsCVecRep],
  function( vec )
    return rec( vectors := MatrixNC([],vec),pivots := [],
                helper := ZeroVector(vec,1) );
    # The helper is needed for the kernel cleaner for CVecs
  end );

InstallMethod( EmptySemiEchelonBasis, "for a cvecclass", [IsCVecClass],
  function( cl )
    local cl1;
    cl1 := CVEC_NewCVecClassSameField( cl, 1 );
    return rec( vectors := CMat([],cl), pivots := [],
                helper :=  CVEC_New( cl1 ) );
    # The helper is needed for the kernel cleaner for CVecs
  end );

InstallMethod( MakeSemiEchelonBasis, "for a semi echelonised matrix",
  [IsRecord],
  function(b)
    local i;
    if IsBound(b.pivots) then return b; fi;
    b.pivots := [];
    for i in [1..Length(b.vectors[1])] do
        if IsBound(b.heads[i]) and b.heads[i] > 0 then
            b.pivots[b.heads[i]] := i;
        fi;
    od;
    b.helper := b.vectors[1]{[1]};
    return b;
  end);

#############################################################################
# High speed cleaning of vectors, semi-echelonised matrices:
#############################################################################

InstallMethod( SemiEchelonRowsX, "for a cmat", [IsCMatRep and IsMutable],
  function( m )
    local b,v;
    b := EmptySemiEchelonBasis( m!.vecclass );
    for v in m do CleanRow(b,v,true,fail); od;
    return b;
  end );
InstallMethod( SemiEchelonRows, "for a cmat", [IsCMatRep],
  function( m )
    return SemiEchelonRowsX( MutableCopyMat( m ) );
  end );
InstallMethod( SemiEchelonRowsX, "for a cmat", [IsCMatRep],
  function( m )
    return SemiEchelonRowsX( MutableCopyMat( m ) );
  end );

InstallMethod( SemiEchelonRowsTX, "for a cmat", [IsCMatRep and IsMutable],
  function( m )
    local b,coeffs,dec,i,j,mo,newcoeffs,newrelation,relations,v,zerov;
    b := EmptySemiEchelonBasis( m!.vecclass );
    zerov := CVEC_New(m!.vecclass);
    dec := ZeroVector(zerov,m!.len);  # Maximal length of the basis
    if m!.len = 0 then
        b.coeffs := MatrixNC([],dec);
        b.relations := rec( vectors := MatrixNC([],dec), pivots := [] );
    fi;
    coeffs := MatrixNC([],dec);
    relations := MatrixNC([], dec );
    i := 0;  # is length of coeffs
    mo := -One(dec[1]);
    for j in [1..Length(m)] do
        v := m[j];
        if not CleanRow(b,v,true,dec) then
            # a new vector in the basis, we have to produce a coeff line:
            # now dec * b.vectors = v (original one)
            # need: coeffs * mat = b.vectors[Length(b.vectors)]
            # ==> need to use
            if i > 0 then
                newcoeffs := ((-dec[i+1]^-1) * dec{[1..i]}) * coeffs;
                newcoeffs[j] := dec[i+1]^-1;
                Add(coeffs,newcoeffs);
            else
                newcoeffs := ShallowCopy(dec);
                newcoeffs[1] := dec[1]^-1;
                Add(coeffs,newcoeffs);
            fi;
            i := i + 1;
        else
            if i > 0 then
                newrelation := dec{[1..i]} * coeffs;
                newrelation[j] := mo;
                #CleanRow(relations,newrelation,true,fail);
            else
                newrelation := ShallowCopy(dec);
                newrelation[j] := -mo;
                #Add(relations.vectors,newrelation);
                #Add(relations.pivots,j);
            fi;
            Add(relations,newrelation);
        fi;
    od;
    b.coeffs := coeffs;
    b.relations := relations;
    return b;
  end);
InstallMethod( SemiEchelonRowsT, "for a cmat", [IsCMatRep],
  function( m )
    return SemiEchelonRowsTX( MutableCopyMat( m ) );
  end );
InstallMethod( SemiEchelonRowsTX, "for an immutable cmat", [IsCMatRep],
  function( m )
    return SemiEchelonRowsTX( MutableCopyMat( m ) );
  end );

InstallMethod( SemiEchelonRowsPX, "for a cmat", 
  [IsCMatRep and IsMutable],
  function( m )
    local b,p,dec,j,v,zerov, decl;
    b := EmptySemiEchelonBasis( m!.vecclass );
    zerov := CVEC_New(m!.vecclass);
    decl := Minimum( 100, m!.len );
    dec := ZeroVector(zerov,decl);
    if m!.len = 0 then
        b.p := MatrixNC( [], dec );
        return b;
    fi;
    p := [];
    for j in [1..m!.len] do
        v := m[j];
        if Length( b.vectors ) >= decl then
            decl := Maximum( decl + 100, m!.len );
            dec := ZeroVector( dec, decl );
        fi;
        CleanRow(b,v,true,dec);
        Add( p, ShallowCopy( dec ) );
    od;
    decl := Length( b.vectors );
    j := 1;
    while j <= Length( p ) and Length( p[ j ] ) < decl do
        dec := ZeroVector( p[ j ], decl );
        CopySubVector( p[ j ], dec, [1..Length(p[j])],[1..Length(p[j])] );
        p[j] := dec;
        j := j + 1;
    od;
    while j <= Length( p ) do
        p[ j ] := p[ j ]{[1..decl]};
        j := j + 1;
    od;
    b.p := CMat( p );
    return b;
  end);
InstallMethod( SemiEchelonRowsP, "for a cmat", [IsCMatRep],
  function( m )
    return SemiEchelonRowsPX( MutableCopyMat( m ) );
  end );
InstallMethod( SemiEchelonRowsPX, "for an immutable cmat", [IsCMatRep],
  function( m )
    return SemiEchelonRowsPX( MutableCopyMat( m ) );
  end );

InstallMethod( MutableNullspaceMatX, "for an immutable cmat", [IsCMatRep],
  function( m )
    local b;
    b := SemiEchelonRowsTX( MutableCopyMat( m ) );
    return b.relations;
  end );
InstallMethod( MutableNullspaceMatX, "for a cmat", [IsCMatRep and IsMutable],
  function( m )
    local b;
    b := SemiEchelonRowsTX(m);
    return b.relations;
  end );
InstallMethod( MutableNullspaceMat, "for a cmat", [IsCMatRep],
  function( m )
    return MutableNullspaceMatX( MutableCopyMat( m ) );
  end );

InstallOtherMethod( NullspaceMatDestructive, "for a cmat", 
  [IsCMatRep and IsOrdinaryMatrix],
  function( m )
    local res;
    res := MutableNullspaceMatX( m );
    MakeImmutable(res);
    return res;
  end );

InstallOtherMethod( NullspaceMat, "for a cmat", 
  [IsCMatRep and IsOrdinaryMatrix],
  function( m )
    local res;
    res := MutableNullspaceMatX( MutableCopyMat( m ) );
    MakeImmutable(res);
    return res;
  end );

InstallMethod( SemiEchelonNullspaceX, "for a cmat",
  [IsCMatRep],
  function( m )
    local n;
    n := MutableNullspaceMatX( m );
    return SemiEchelonRowsX( n );
  end );
InstallMethod( SemiEchelonNullspace, "for a cmat",
  [IsCMatRep],
  function( m )
    local n;
    n := MutableNullspaceMat( m );
    return SemiEchelonRowsX( n );
  end );

#############################################################################
# Characteristic polynomials:
#############################################################################

InstallGlobalFunction( CVEC_CharacteristicPolynomialFactors,
function(m,indetnr)
  # m must be square
  local L,b,b2,closed,d,dec,f,facs,fam,i,l,lambda,newlambda,o,p,
        newpiv,pivs,subdim,v,vcopy,zero;
  zero := ZeroMutable(m[1]);
  d := Length(m);
  b := EmptySemiEchelonBasis(zero);
  pivs := [1..d];
  facs := [];
  f := BaseField(m);
  o := One(f);
  fam := FamilyObj(o);
  dec := ShallowCopy(zero);
  while Length(pivs) > 0 do
      subdim := Length(b.pivots);
      p := pivs[1];
      v := ShallowCopy(zero);
      v[p] := o;
      b2 := EmptySemiEchelonBasis(v);
      Add(b2.vectors,v);
      Add(b2.pivots,p);
      lambda := [dec{[1]}];
      lambda[1][1] := o;
      RemoveSet(pivs,p);
      while true do   # break is used to jump out
          v := v * m;
          vcopy := ShallowCopy(v);
          CleanRow(b,vcopy,false,fail);
          closed := CleanRow(b2,vcopy,true,dec);
          if closed then break; fi;
          Add(lambda,dec{[1..Length(b2.pivots)]});
          RemoveSet(pivs,b2.pivots[Length(b2.pivots)]);
      od;
      d := Length(b2.pivots);
      # we have the lambdas, expressing v*m^(i-1) in terms of the semiechelon
      # basis, now we have to express v*m^d in terms of the v*m^(i-1), that
      # means inverting a matrix: 
      L := CVEC_ZeroMat(d,CVecClass(lambda[d]));
      for i in [1..d] do
          CopySubVector(lambda[i],L[i],[1..i],[1..i]);
      od;
      l := - dec{[1..d]} * L^-1;
      l := Unpack(l);
      Add(l,o);
      ConvertToVectorRep(l,Size(f));
      Add(facs,UnivariatePolynomialByCoefficients(fam,l,indetnr));
      # Add b2 to b:
      Append(b.vectors,b2.vectors);
      Append(b.pivots,b2.pivots);
  od;
  return facs;
end );

InstallMethod( CharacteristicPolynomialOfMatrix, "for a cmat and an indet nr", 
  [IsCMatRep, IsPosInt],
  function( m, indetnr )
    local facs;
    facs := CVEC_CharacteristicPolynomialFactors(m, indetnr);
    return rec( poly := Product(facs), factors := facs );
  end );

InstallMethod( CharacteristicPolynomialOfMatrix, "for a cmat", 
  [IsCMatRep],
  function( m )
    local facs;
    facs := CVEC_CharacteristicPolynomialFactors(m, 1);
    return rec( poly := Product(facs), factors := facs );
  end );

InstallMethod( FactorsOfCharacteristicPolynomial, "for a cmat", [IsCMatRep],
  function( m )
    return FactorsOfCharacteristicPolynomial(m,1);
  end );

InstallMethod( FactorsOfCharacteristicPolynomial, "for a cmat and an indet nr", 
  [IsCMatRep, IsPosInt],
  function( m, indetnr )
    local f,facs,irrfacs;
    facs := CVEC_CharacteristicPolynomialFactors(m,indetnr);
    irrfacs := [];
    for f in facs do
        Append(irrfacs,Factors(f));
    od;
    Sort(irrfacs);
    return irrfacs;
  end );

BindGlobal( "CVEC_ActionOnQuotient", function( gens, basis )
  local dimsubspc, dimfullspc, dimquotspc, diff, zerov, imgens, x, i, k;
  # INPUT
  # gens : List of matrices
  # basis : basis of submodule ie record with fields
  #         pivots   : integer list of pivot columns
  #         vectors : matrix of basis in semi-echelon form
  # OUTPUT
  # List of matrices representing the action of the module given by 'gens'
  # on the quotient space induced by 'basis'
  # NOTES
  # 
  dimsubspc := Length( basis.vectors );
  dimfullspc := Length( basis.vectors[ 1 ] );
  dimquotspc := dimfullspc - dimsubspc;
  diff := Difference( [1..dimfullspc], basis.pivots );
  zerov := ZeroVector( basis.vectors[1], 
	               dimquotspc ); #prepare vector type
  imgens := []; # stores result
  for i in [ 1 .. Length( gens ) ] do
    imgens[ i ] := CVEC_ZeroMat( dimquotspc, CVecClass(zerov) );
    # grab rows corresponding to added basis vectors:
    x := MutableCopyMat(gens[ i ]{ diff }); 
    for k in [1..Length(x)] do # clean rows with subspace basis
      CleanRow( basis, x[ k ], false, fail );
    od;
    # now remove zero columns
    CopySubMatrix( x, imgens[ i ], [1..dimquotspc], [1..dimquotspc], 
                                   diff , [1..dimquotspc] );
  od;
  return imgens;
end );

InstallGlobalFunction( CVEC_MinimalPolynomial, function(m)
  # m must be square
  local L,b,b2,closed,d,dec,f,fam,i,l,lambda,o,p,pivs,poly,subdim,v,vcopy,zero;

  zero := ZeroMutable(m[1]);
  d := Length(m);
  b := EmptySemiEchelonBasis(zero);
  pivs := [1..d];
  f := BaseField(m);
  poly := One(PolynomialRing(f,[1]));
  o := One(f);
  fam := FamilyObj(o);
  dec := ShallowCopy(zero);
  while Length(pivs) > 0 do
      subdim := Length(b.pivots);
      p := pivs[1];
      v := ShallowCopy(zero);
      v[p] := o;
      b2 := EmptySemiEchelonBasis(v);
      Add(b2.vectors,v);
      Add(b2.pivots,p);
      lambda := [dec{[1]}];
      lambda[1][1] := o;
      RemoveSet(pivs,p);
      while true do   # break is used to jump out
          v := v * m;
          vcopy := ShallowCopy(v);
          closed := CleanRow(b2,vcopy,true,dec);
          if closed then break; fi;
          Add(lambda,dec{[1..Length(b2.pivots)]});
          RemoveSet(pivs,b2.pivots[Length(b2.pivots)]);
      od;
      d := Length(b2.pivots);
      # we have the lambdas, expressing v*m^(i-1) in terms of the semiechelon
      # basis, now we have to express v*m^d in terms of the v*m^(i-1), that
      # means inverting a matrix: 
      L := CVEC_ZeroMat(d,CVecClass(lambda[d]));
      for i in [1..d] do
          CopySubVector(lambda[i],L[i],[1..i],[1..i]);
      od;
      l := - dec{[1..d]} * L^-1;
      l := Unpack(l);
      Add(l,o);
      ConvertToVectorRep(l,Size(f));
      poly := Lcm(poly,UnivariatePolynomialByCoefficients(fam,l,1));
      # Add b2 to b:
      for v in b2.vectors do
          if not(CleanRow(b,v,true,fail)) then
              RemoveSet(pivs,b.pivots[Length(b.pivots)]);
          fi;
      od;
  od;
  return poly;
end );

InstallGlobalFunction( CVEC_CharAndMinimalPolynomial, function( m, indetnr )
  local col,deg,facs,havedim,i,irreds,l,lowbound,lowbounds,mp,mult,
        multfactoredout,multmin,nrblocks,ns,p,targetmult,upbound,x;
  # First the characteristic polynomial:
  facs := CVEC_CharacteristicPolynomialFactors(m,indetnr);
  if Length(facs) = 1 then
      return rec( charpoly := facs[1], irreds := facs, mult := [1],
                  minpoly := facs[1], multmin := [1] );
  fi;
  Info(InfoCVec,2,
       "More than 1 factor, factorising characteristic polynomial...");
  # Factor all parts:
  col := List(facs,f->Collected(Factors(f)));
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
  mp := irreds[1]^0;
  Info(InfoCVec,2,"Degrees of irreducible factors of charpoly:",
       List(irreds,DegreeOfLaurentPolynomial));
  for i in [1..Length(irreds)] do
      deg := DegreeOfLaurentPolynomial(irreds[i]);
      Info(InfoCVec,2,"Working on irreducible factor of degree ",deg,"...");
      if mult[i] = lowbounds[i] then
          Info(InfoCVec,2,"Found factor of degree ",deg," with multiplicity ",
                mult[i]);
          mp := mp * irreds[i]^mult[i];
          multmin[i] := mult[i];
      else
          x := Value(irreds[i],m);
          targetmult := mult[i];      # the multiplicity to reach
          lowbound := lowbounds[i];   # from the calc. of the charpoly
          upbound := targetmult;      # an upper bound
          Info(InfoCVec,2,"First lower bound: ",lowbound,
               " upper bound: ",upbound);
          multfactoredout := 0;       # no quotient yet
          # Note that when we divide something out, we adjust targetmult
          # and record this in multfactoredout.
          # This stores the number of dimensions each Jordan block is
          # made smaller by our current quotient.
          # We also adjust lowbound and upbound when we go to a quotient!
          while true do   # break is used to leave 
              # This loop tries to determine the size of the largest Jordan
              # block of the matrix x and either exits with 
              #    lowbound=upbound=that size
              # or reduces the problem to a smaller one in some quotient,
              # thereby adjusting multfactoredout by the number of rows/cols
              # that are divided away by the quotient and going to the
              # next iteration.
              # I.e. in the end the right multiplicity is always equal to
              #    lowbound+multfactoredout

              # First calculate a nullspace and get some estimates:
              Info(InfoCVec,2,"Target multiplicity: ",targetmult,
                   ", already factored out: ",multfactoredout);
              ns := SemiEchelonNullspace(x);
              havedim := Length(ns.vectors);
              Info(InfoCVec,2,"Found nullspace of dimension ",havedim);
              # We have a lower bound for the multiplicity in the minpoly
              # from earlier and one from the number of generalized Jordan 
              # blocks we see:
              nrblocks := havedim/deg;   # this is in quotient!
              # note that lowbound is absolute i.e. in the original space:
              lowbound := Maximum(lowbound,
                                  QuoInt(targetmult+nrblocks-1,nrblocks));
              upbound := Minimum(upbound,targetmult-nrblocks+1);
              Info(InfoCVec,2,"Lower bound: ",lowbound," upper bound: ",
                   upbound);
              if lowbound = upbound then break; fi;

              # Now we divide out the nullspace and go to lowbound:
              lowbound := lowbound-1;   # Adjustment because of quotient!
              Info(InfoCVec,2,"Factoring out nullspace of dimension ",havedim,
                   " and going to power ",lowbound);
              x := CVEC_ActionOnQuotient([x],ns)[1];
              multfactoredout := multfactoredout + 1;
              targetmult := targetmult - nrblocks;
              x := x^lowbound;
              Info(InfoCVec,2,"Target multiplicity: ",targetmult);
              ns := SemiEchelonNullspace(x);
              havedim := Length(ns.vectors);
              Info(InfoCVec,2,"Found nullspace of dimension ",havedim);

              # Check, whether we have the complete generalized eigenspace:
              if havedim/deg = targetmult then
                  # lowbound is correct!
                  upbound := lowbound;
                  break;
              fi;
              
              # Now we want to go to the quotient and redo everything:
              Info(InfoCVec,2,"Factoring out nullspace of dimension ",havedim,
                   " and going to power ",lowbound);
              x := CVEC_ActionOnQuotient([x],ns)[1];
              multfactoredout := multfactoredout + 1 + lowbound;
              targetmult := targetmult - Length(ns.vectors)/deg;
              lowbound := 0;   # we do not know anything about this quotient
              upbound := targetmult;
          od;
          Info(InfoCVec,2,"Done! Multiplicity is ",lowbound+multfactoredout);
          mp := mp * irreds[i]^(lowbound+multfactoredout);
          multmin[i] := (lowbound+multfactoredout);
      fi;
  od;
  return rec(charpoly := Product(facs), irreds := irreds, mult := mult,
             minpoly := mp, multmin := multmin);
end );

InstallMethod( CharAndMinimalPolynomialOfMatrix, "for a matrix and an indet nr",
  [IsCMatRep, IsPosInt],
  function( m, indetnr )
    return CVEC_CharAndMinimalPolynomial(m,indetnr);
  end );

InstallMethod( CharAndMinimalPolynomialOfMatrix, "for a matrix", [IsCMatRep],
  function( m )
    return CVEC_CharAndMinimalPolynomial(m,1);
  end );

InstallMethod( MinimalPolynomialOfMatrix, "for a matrix and an indet nr",
  [IsCMatRep, IsPosInt],
  function( m, indetnr )
    local res;
    res := CVEC_CharAndMinimalPolynomial(m,indetnr);
    return res.minpoly;
  end );

InstallMethod( MinimalPolynomialOfMatrix, "for a matrix", [IsCMatRep],
  function( m )
    local res;
    res := CVEC_CharAndMinimalPolynomial(m,1);
    return res.minpoly;
  end );

InstallGlobalFunction( CVEC_GlueMatrices, function(l)
  # all elements of the list l must be CMats over the same field
  local d,g,i,m,n,p,pos,x;
  n := Sum(l,Length);
  p := Characteristic(l[1]);
  d := DegreeFFE(l[1]);
  m := CVEC_ZeroMat(n,n,p,d);
  pos := 1;
  for i in [1..Length(l)] do
      CopySubMatrix(l[i],m,[1..Length(l[i])],[pos..pos+Length(l[i])-1],
                           [1..Length(l[i])],[pos..pos+Length(l[i])-1]);
      pos := pos + Length(l[i]);
  od;
  Display(m);
  g := GL(n,p^d);
  g := Group(List(GeneratorsOfGroup(g),CMat));
  x := PseudoRandom(g);
  return x * m * x^-1;
  #return m;
end );
  
InstallGlobalFunction( CVEC_MakeJordanBlock, function(f,pol,s)
  local c,cl,d,deg,i,m,n,o,p,pos;
  p := Characteristic(f);
  d := DegreeOverPrimeField(f);
  deg := DegreeOfLaurentPolynomial(pol);
  n := s * deg;
  m := CVEC_ZeroMat(n,n,p,d);
  c := CompanionMat(pol);
  c := CMat(List(c,CVec));
  o := OneMutable(c);
  pos := 1;
  for i in [1..s] do
      CopySubMatrix(c,m,[1..deg],[pos..pos+deg-1],[1..deg],[pos..pos+deg-1]);
      pos := pos + deg;
  od;
  pos := 1;
  for i in [1..s-1] do
      CopySubMatrix(o,m,[1..deg],[pos..pos+deg-1],[1..deg],
                        [pos+deg..pos+2*deg-1]);
      pos := pos + deg;
  od;
  return m;
end );

InstallGlobalFunction( CVEC_MakeExample, function(f,p,l)
  # p a list of irredcible polynomials
  # l a list of lists of the same length than p, each a list of sizes of
  # generalized Jordan blocks
  local i,ll,s;
  ll := [];
  for i in [1..Length(p)] do
      for s in l[i] do
          Add(ll,CVEC_MakeJordanBlock(f,p[i],s));
      od;
  od;
  return CVEC_GlueMatrices(ll);
end );

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
  f := BaseField(m);
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
    
InstallGlobalFunction( CVEC_CalcOrderPolyTuned, 
function( opi, v, i, indetnr )
  local coeffs,g,h,j,k,ordpol,vv,w;
  ordpol := [];  # comes factorised
  while i >= 1 do
      coeffs := v{opi.ranges[i]};
      if IsZero(coeffs) then
          i := i - 1;
          continue;
      fi;
      coeffs := Unpack(coeffs);
      ConvertToVectorRep(coeffs,Size(opi.f));
      h := UnivariatePolynomialByCoefficients(opi.fam,coeffs,indetnr);
      g := opi.rordpols[i]/Gcd(opi.rordpols[i],h);
      Add(ordpol,g);
      # This is the part coming from the ith cyclic space, now go down:
      coeffs := CoefficientsOfUnivariatePolynomial(g);
      w := coeffs[1]*v;
      for j in [2..Length(coeffs)] do
          # Now apply base changed matrix to v:
          #   v := v * opi.mm;
          # but remember, that we only store the interesting rows of mm:
          vv := ZeroMutable(v);
          CopySubVector(v,vv,[1..opi.ranges[i][2]-1],[2..opi.ranges[i][2]]);
          for k in [2..i] do
              vv[opi.ranges[k][1]] := opi.z;
          od;
          for k in [1..i] do
              AddRowVector(vv,opi.mm[k],v[opi.ranges[k][2]],1,opi.ranges[k][2]);
          od;
          v := vv;
          # Done.
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
    
InstallGlobalFunction( CVEC_FactorMultiplicity,
function( p, f )
  local m,r;
  m := 0;
  while true do   # we use break
    r := QuotientRemainder( p, f );
    if not(IsZero(r[2])) then break; fi;
    m := m + 1;
    p := r[1];
  od;
  return m;
end );

InstallGlobalFunction( CVEC_NewMinimalPolynomialMCTuned, 
function( m, eps, verify, indetnr )
  # The new algorithm of Cheryl and Max. Can be used as Las Vegas algorithm
  # or as deterministic algorithm with verification.
  # eps is a cyclotomic which is an upper bound for the error probability
  # verify is a boolean indicating, whether the result should be verified,
  # thereby proving correctness, indetnr is the number of an indeterminate
  local A,B,S,coeffs,col,d,dec,g,i,irreds,j,l,lowbounds,mm,mult,multmin,newBrow,
        nrunclear,ns,opi,ordpol,ordpolsinv,p,pivs,prob,proof,r,w,wcopy,ww,zero;
  r := Runtime();
  zero := ZeroMutable(m[1]);
  pivs := [1..Length(m)];   # those are the columns we still want pivots for
  S := EmptySemiEchelonBasis(zero);
  # order polynomial infrastructure (grows over time):
  opi := rec( f := BaseField(m),
              d := [],          # Degrees of the relative cyclic spaces
              ranges := [],     # numbers of basis vectors
              rordpols := [],   # list of relative order polynomials
              mm := MatrixNC([],zero), # will be crucial rows of base-changed m
            );  
  opi.o := One(opi.f);
  opi.z := Zero(opi.f);
  opi.fam := FamilyObj(opi.o);
  # We keep the base change between the basis
  #  Y = [x_1,x_1*m,x_1*m^2,...,x_1*(m^(d_1-1)),x_2,...,x_2*m^(d_2-1),...]
  # and the semi echelonised basis S by keeping Y=A*S and S=B*Y at the same 
  # time. Be are only interested in B, but we get A as a byproduct.
  A := MatrixNC([],zero);
  B := MatrixNC([],zero);
  ordpolsinv := []; # here we collect information to be used for the order pols

  Info(InfoCVec,2,"Spinning up vectors...");
  while Length(S.vectors) < Length(m) do
      p := pivs[1];
      w := ShallowCopy(zero);
      w[p] := opi.o;
      # The following randomisation seems to cost a lot because of 
      # non-sparseness, so we stick to the standard basis vectors.
      #w := ShallowCopy(zero);
      #repeat
      #    Print(".\c");
      #    Randomize(w);
      #    CleanRow(S,w,false,fail);
      #until not(IsZero(w));
      #Print("!\c");

      #re := CVEC_RelativeOrderPoly(m,w,b,indetnr);
      # We inline a relative order calculation mod the current b:
      d := Length(S.vectors);  # dimension of subspace:
      Add(S.vectors,w);
      Add(S.pivots,p);
      l := d+1;  # is always equal to Length(S.vectors)
      ww := ShallowCopy(zero);
      ww[l] := opi.o;
      Add(A,ww);
      Add(B,ww);
      while true do
          dec := ShallowCopy(zero);
          w := w * m;
          wcopy := ShallowCopy(w);
          if CleanRow(S,wcopy,true,dec) then break; fi;
          l := l + 1;
          Add(A,dec);
          # Now update B:
          # We know: with l=Length(S) we have dec{[1..l]}*S = Y[l]
          # Thus: dec[l]*S[l] = Y[l] - dec{[1..l-1]}*S{[1..l-1]}
          #                   = Y[l] - dec{[1..l-1]}*B*Y{[1..l-1]}
          # by a slight abuse of "*" because dec{[1..l-1]}*B has full length.
          newBrow := dec{[1..l-1]}*B;
          MultRowVector(newBrow,-opi.o);
          newBrow[l] := opi.o;
          MultRowVector(newBrow,dec[l]^-1);
          Add(B,newBrow);
      od;
      # Now we have extended the basis S together with A and B, such that
      # we still have Y = A*S and S = B*Y. The latest dec expresses 
      # x*m^something in terms of S, first express it in terms of Y, then
      # we can read off the relative order polynomial from components
      # components d+1 .. Length(S.vectors).
      dec := dec{[1..l]} * B;
      Add(opi.mm,dec);
      coeffs := -dec{[d+1..l]};
      coeffs := Unpack(coeffs);
      Add(coeffs,opi.o);
      ConvertToVectorRep(coeffs,Size(opi.f));
      Add(opi.rordpols,
          UnivariatePolynomialByCoefficients(opi.fam,coeffs,indetnr));
      Add(opi.d,l-d);  # the degree of the order polynomial
      Add(opi.ranges,[d+1..l]);
      SubtractSet(pivs,S.pivots{[d+1..l]});
  od;

  Error(0);
  # Release some memory:
  Unbind(A);
  Unbind(B);
  Unbind(S);

  Print("Runtime so far: ",Runtime()-r,"\n");
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
  Print("Runtime so far: ",Runtime()-r,"\n");
  Info(InfoCVec,2,"Number of irreducible factors in charpoly: ",Length(irreds),
                  " mult. in minpoly unknown: ",nrunclear);

  ordpol := Lcm(Set(opi.rordpols)); # this is a lower bound for the minpoly
                               # in particular, it is a multiple of rordpols[1]
  Print("Runtime so far: ",Runtime()-r,"\n");

  if nrunclear > 0 then
      i := 2;
      p := 1/Size(opi.f);   # probability to miss a big Jordan block with the
                            # order polynomial of one vector (upper bound)
      proof := false;
      repeat   # until verification said "OK"
          Print("Runtime so far: ",Runtime()-r,"\n");
          Error(1);
          # This is an upper estimate of the probability not to find a generator
          # of a cyclic space:
          prob := p;   # we already have the order polynomial for one vector 
          Info(InfoCVec,2,"Calculating order polynomials...");
          while i <= Length(opi.rordpols) do
              w := ShallowCopy(zero);
              w[opi.ranges[i][1]] := opi.o;
              g := CVEC_CalcOrderPolyTuned(opi,w,i,indetnr);
              if not(IsZero(ordpol mod g)) then
                  ordpol := Lcm(ordpol,g);
              fi;
              if Degree(ordpol) = Length(m) then   # a cyclic matrix!
                  proof := true;
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

          Error(2);
          Print("Runtime so far: ",Runtime()-r,"\n");
          Info(InfoCVec,2,"Checking multiplicities...");
          nrunclear := 0;
          for j in [1..Length(irreds)] do
              multmin[j] := CVEC_FactorMultiplicity(ordpol,irreds[j]);
              if multmin[j] < mult[j] then
                  nrunclear := nrunclear + 1;
              fi;
          od;
          if nrunclear = 0 then proof := true; break; fi;   # result is correct!

          Error(3);
          Print("Runtime so far: ",Runtime()-r,"\n");
          if verify then
              Info(InfoCVec,2,"Verifying result (",nrunclear,
                   " unclear multiplicities) ...");
              proof := true;  # will be set to false once we discover something
              for j in [1..Length(irreds)] do
                  if multmin[j] < mult[j] then
                      Info(InfoCVec,2,"Working on factor: ",irreds[j],
                                      " multiplicity: ",multmin[j]);
                      mm := Value(irreds[j],m)^multmin[j];
                      ns := MutableNullspaceMatX(mm);
                      Print("Runtime so far: ",Runtime()-r,"\n");
                      if Length(ns) < mult[j] then
                          proof := false;
                          break;
                      fi;
                  fi;
              od;
          fi;
      until not(verify) or proof;
  else
      proof := true;
  fi;

  return rec(minpoly := ordpol,
             charpoly := Product( opi.rordpols ),
             opi := opi,
             irreds := irreds,
             mult := mult,
             multmin := multmin,
             proof := proof);
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
  v := MatrixNC([],m[1]);   # start vectors for the spinning
  vl := MatrixNC([],m[1]);  # start vectors together with their images under m
  A := [];   # base changes within each subquotient
  l := [];   # a list of semi echelon bases for the subquotients
  # order polynomial infrastructure (grows over time):
  opi := rec( f := BaseField(m),
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
                  ns := MutableNullspaceMatX(mm);
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
  v := MatrixNC([],m[1]);   # start vectors for the spinning
  vl := MatrixNC([],m[1]);  # start vectors together with their images under m
  A := [];   # base changes within each subquotient
  l := [];   # a list of semi echelon bases for the subquotients
  # order polynomial infrastructure (grows over time):
  opi := rec( f := BaseField(m),
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
