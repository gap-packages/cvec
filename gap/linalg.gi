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
    b.pivots := [];
    for i in [1..Length(b.vectors)] do
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

InstallMethod( SemiEchelonRowsX, "for a cmat", [IsCMatRep],
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
InstallMethod( SemiEchelonRowsTX, "for a cmat", [IsCMatRep],
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
    relations := EmptySemiEchelonBasis( dec );
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
                CleanRow(relations,newrelation,true,fail);
            else
                newrelation := ShallowCopy(dec);
                newrelation[j] := -mo;
                Add(relations.vectors,newrelation);
                Add(relations.pivots,j);
            fi;
        fi;
    od;
    b.coeffs := coeffs;
    b.relations := relations;
    return b;
  end);
InstallMethod( SemiEchelonRowsXp, "for a cmat", [IsCMatRep],
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
InstallMethod( SemiEchelonRowsT, "for a cmat", [IsCMatRep],
  function( m )
    return SemiEchelonRowsTX( MutableCopyMat( m ) );
  end );

InstallMethod( SemiEchelonNullspaceX, "for a cmat", [IsCMatRep],
  function( m )
    local b;
    b := SemiEchelonRowsTX(m);
    return b.relations;
  end );
InstallMethod( SemiEchelonNullspace, "for a cmat", [IsCMatRep],
  function( m )
    return SemiEchelonNullspaceX( MutableCopyMat( m ) );
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

InstallMethod( MinimalPolynomialOfMatrix, "for a matrix and an indet nr",
  [IsCMatRep, IsPosInt],
  function( m, indetnr )
    return CVEC_CharAndMinimalPolynomial(m,indetnr);
  end );

InstallMethod( MinimalPolynomialOfMatrix, "for a matrix", [IsCMatRep],
  function( m )
    return CVEC_CharAndMinimalPolynomial(m,1);
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


