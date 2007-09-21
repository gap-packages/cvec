#############################################################################
##
#W  linalg.gi               GAP 4 package `cvec'                
##                                                            Max Neunhoeffer
##
##  Copyright (C) 2007  Max Neunhoeffer, Lehrstuhl D f. Math., RWTH Aachen
##  This file is free software, see license information at the end.
##
##  This file contains the higher levels for efficient implementation of
##  some linear algebra routines for compact vectors over finite fields. 
##


#############################################################################
# Creation of semi-echelonised basis:
#############################################################################

InstallMethod( SEBMaker, "generic method",
  [ IsRowListMatrix, IsList],
  function( vectors, pivots )
    local b;
    b := rec( vectors := vectors, pivots := pivots );
    return Objectify(NewType(FamilyObj(b.vectors),SEBType and IsMutable),b);
  end );

InstallMethod( SEBMaker, "for a cmat, and an integer list",
  [ IsCMatRep, IsList ],
  function( vectors, pivots )
    local b,cl;
    b := rec( vectors := vectors, pivots := pivots );
    cl := CVEC_NewCVecClassSameField(b.vectors!.vecclass,1);
    b.helper := CVEC_New(cl);
    return Objectify(NewType(FamilyObj(b.vectors),
                             SEBType and IsMutable and IsCMatSEB),b);
  end );

InstallMethod( SemiEchelonBasisMutable, "for a semi echelonised basis record",
  [IsRecord],
  function(b)
    local i;
    b.pivots := [];
    for i in [1..RowLength(b.vectors)] do
        if IsBound(b.heads[i]) and b.heads[i] > 0 then
            b.pivots[b.heads[i]] := i;
        fi;
    od;
    return SEBMaker(b.vectors,b.pivots);
  end);

InstallMethod( EmptySemiEchelonBasis, "for a row list matrix",
  [ IsRowListMatrix ],
  function( m )
    return SEBMaker( Matrix([],RowLength(m),m), [] );
  end );

InstallMethod( Vectors, "for a semi echelonsised basis", [ SEBType ],
  function(b)
    return b!.vectors;
  end );

InstallMethod( BasisVectors, "for a semi echelonised basis", [ SEBType ],
  function(b)
    return b!.vectors;
  end );

InstallMethod( Pivots, "for a semi echelonised basis", [ SEBType ],
  function(b)
    return b!.pivots;
  end );

InstallMethod( ViewObj, "for a semi echelonised basis",
  [ SEBType ],
  function(b)
    Print("<");
    if not(IsMutable(b)) or not(IsMutable(b!.vectors)) then
        Print("immutable ");
    fi;
    Print("semi echelonized basis over ",BaseDomain(b!.vectors)," of length ",
          Length(b!.vectors),">");
  end);

InstallMethod( Display, "for a semi echelonised basis",
  [ SEBType ],
  function(b)
    Print("<");
    if not(IsMutable(b)) or not(IsMutable(b!.vectors)) then
        Print("immutable ");
    fi;
    Print("semi echelonized basis over ",BaseDomain(b!.vectors)," of length ",
          Length(b!.vectors),"\n");
    Display(b!.vectors);
    Print(">");
  end );

#############################################################################
# High speed cleaning of vectors, semi-echelonised matrices:
#############################################################################

BindGlobal( "CVEC_CleanRow", function( basis, vec, extend, dec)
  local c,firstnz,i,j,lc,len,lev,mo,newpiv,pivs;
  # INPUT
  # basis: component object with fields
  #        pivots   : integer list of pivot columns of basis matrix
  #        vectors : matrix of basis vectors in semi echelon form
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

  len := Length(basis!.vectors);
  i := 1;

  for j in [i..len] do
    if basis!.pivots[j] >= firstnz then
      c := vec[ basis!.pivots[ j ] ];
      if not IsZero( c ) then
        if dec <> fail then
          dec[ j ] := c;
        fi;
        AddRowVector( vec, basis!.vectors[ j ], -c );
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
      Add( basis!.vectors, vec );
      Add( basis!.pivots, newpiv );
    fi;
    return false;
  fi;
end );
    
InstallMethod( CleanRow, 
  "GAP method for a semi echelon basis, a vector, and a boolean or vector", 
  [SEBType and IsMutable, IsRowVectorObj, IsBool, IsObject], CVEC_CleanRow );

InstallMethod( CleanRow, 
  "kernel method for a record, a cvec, and a boolean or cvec", 
  [SEBType and IsMutable and IsCMatSEB, IsCVecRep, IsBool, IsObject], 
   CVEC_CLEANROWKERNEL );

InstallMethod( IO_Pickle, "for a file and a cmat semi echelonized basis",
  [ IsFile, IsCMatSEB and IsList and IsSemiEchelonized ],
  function( f, seb )
    return IO_GenericObjectPickler(f,"CSEB",[seb!.vectors,seb!.pivots],
                                   seb,[],[],[]);
  end );

IO_Unpicklers.CSEB :=
  function( f )
    local vectors, pivots;
    vectors := IO_Unpickle(f); 
    if vectors = IO_Error then return IO_Error; fi;
    pivots := IO_Unpickle(f);
    if vectors = IO_Error then return IO_Error; fi;
    return SEBMaker(vectors,pivots);
  end;

InstallMethod( Coefficients, "for a semi echelonized basis, and a vector",
  [SEBType, IsRowVectorObj],
  function(b,v)
    local dec;
    dec := ZeroVector(Length(b),v);
    if CleanRow(b,ShallowCopy(v),false,dec) then
        return dec;
    else
        return fail;
    fi;
  end );

InstallMethod( LinearCombination, "for a semi echelonized basis, and a vector",
  [SEBType, IsRowVectorObj],
  function(b,v)
    return v * b!.vectors;
  end );


#############################################################################
# Computing semi-echelonised bases from matrices:
#############################################################################

InstallMethod( SemiEchelonBasisMutableX, "for a row list matrix", 
  [IsRowListMatrix and IsMutable],
  function( m )
    local b,v;
    b := EmptySemiEchelonBasis(m);
    for v in m do CleanRow(b,v,true,fail); od;
    return b;
  end );
InstallMethod( SemiEchelonBasisMutable, "for a row list matrix", 
  [IsRowListMatrix],
  function( m )
    return SemiEchelonBasisMutableX( MutableCopyMat( m ) );
  end );
InstallMethod( SemiEchelonBasisMutableX, "for a row list matrix", 
  [IsRowListMatrix],
  function( m )
    return SemiEchelonBasisMutableX( MutableCopyMat( m ) );
  end );

InstallMethod( SemiEchelonBasisMutableTX, "for a row list matrix", 
  [IsRowListMatrix and IsMutable],
  function( m )
    local b,coeffs,dec,i,j,mo,newcoeffs,newrelation,relations,rl,s,v,zerov;
    rl := RowLength(m);
    b := EmptySemiEchelonBasis( m );
    zerov := ZeroVector(rl,m);
    dec := ZeroVector(Length(m),zerov);  # Maximal length of the basis
    if Length(m) = 0 then
        b!.coeffs := Matrix([],0,m);
        b!.relations := rec( vectors := Matrix([],0,m), pivots := [] );
        return b;
    fi;
    # In the end, we want: coeffs * m = b!.vectors:
    coeffs := Matrix([],Length(m),m);
    # In the end, we want relations to be a basis for the nullspace of m:
    relations := Matrix([],Length(m),m);
    i := 0;  # this is the length of coeffs
    mo := -One(BaseDomain(m));
    for j in [1..Length(m)] do
        v := m[j];
        if not CleanRow(b,v,true,dec) then
            # a new vector in the basis, we have to produce a coeff line:
            # now dec * b!.vectors = v (original one)
            # need: coeffs * mat = b!.vectors[Length(b!.vectors)]
            # ==> we use b!.vectors[Length(b!.vectors)]
            #               = (v-dec{[1..i]}*b!.vectors)/dec[i+1]
            if i > 0 then
                s := dec[i+1]^-1;
                newcoeffs := ((-s) * dec{[1..i]}) * coeffs;
                newcoeffs[j] := s;
                Add(coeffs,newcoeffs);
            else
                newcoeffs := ZeroMutable(dec);
                newcoeffs[j] := dec[1]^-1;
                Add(coeffs,newcoeffs);
            fi;
            i := i + 1;
        else
            if i > 0 then
                newrelation := dec{[1..i]} * coeffs;
                newrelation[j] := mo;
            else
                newrelation := ZeroMutable(dec);
                newrelation[j] := mo;
            fi;
            Add(relations,newrelation);
        fi;
    od;
    b!.coeffs := coeffs;
    b!.relations := relations;
    return b;
  end);
InstallMethod( SemiEchelonBasisMutableT, "for a row list matrix", 
  [IsRowListMatrix],
  function( m )
    return SemiEchelonBasisMutableTX( MutableCopyMat( m ) );
  end );
InstallMethod( SemiEchelonBasisMutableTX, "for an immutable row list matrix", 
  [IsRowListMatrix],
  function( m )
    return SemiEchelonBasisMutableTX( MutableCopyMat( m ) );
  end );

InstallMethod( SemiEchelonBasisMutablePX, "for a row list matrix", 
  [IsRowListMatrix and IsMutable],
  function( m )
    # In the end we want b!.p * b!.vectors = m
    local b,p,dec,j,v,zerov, decl;
    b := EmptySemiEchelonBasis( m );
    zerov := ZeroVector(RowLength(m),m);
    decl := Minimum( 100, Length(m) );
    dec := ZeroVector(decl,zerov);
    if Length(m) = 0 then
        b!.p := Matrix( [], 0, m );
        return b;
    fi;
    p := [];   # we collect the vectors in a list because we do not know
               # their final length
    for j in [1..Length(m)] do
        v := m[j];
        if Length( b!.vectors ) >= decl then
            decl := Maximum( decl + 100, Length(m) );
            dec := ZeroVector( decl, dec );
        fi;
        CleanRow(b,v,true,dec);
        Add( p, ShallowCopy( dec ) );
    od;
    decl := Length( b!.vectors );
    b!.p := Matrix([],decl,m);
    j := 1;
    while j <= Length( p ) and Length( p[ j ] ) < decl do
        dec := ZeroVector( decl, dec );
        CopySubVector( p[ j ], dec, [1..Length(p[j])],[1..Length(p[j])] );
        Add(b!.p,dec);
        j := j + 1;
    od;
    while j <= Length( p ) do
        Add(b!.p,p[ j ]{[1..decl]});
        j := j + 1;
    od;
    return b;
  end);
InstallMethod( SemiEchelonBasisMutableP, "for a row list matrix", 
  [IsRowListMatrix],
  function( m )
    return SemiEchelonBasisMutablePX( MutableCopyMat( m ) );
  end );
InstallMethod( SemiEchelonBasisMutablePX, "for an immutable row list matrix", 
  [IsRowListMatrix],
  function( m )
    return SemiEchelonBasisMutablePX( MutableCopyMat( m ) );
  end );

InstallMethod( NullspaceMatMutableX, "for an immutable row list matrix", 
  [IsRowListMatrix],
  function( m )
    local b;
    b := SemiEchelonBasisMutableTX( MutableCopyMat( m ) );
    return b!.relations;
  end );
InstallMethod( NullspaceMatMutableX, "for a row list matrix", 
  [IsRowListMatrix and IsMutable],
  function( m )
    local b;
    b := SemiEchelonBasisMutableTX(m);
    return b!.relations;
  end );
InstallMethod( NullspaceMatMutable, "for a row list matrix", 
  [IsRowListMatrix],
  function( m )
    return NullspaceMatMutableX( MutableCopyMat( m ) );
  end );

InstallOtherMethod( NullspaceMatDestructive, "for a cmat", 
  [IsCMatRep and IsOrdinaryMatrix],
  function( m )
    local res;
    res := NullspaceMatMutableX( m );
    MakeImmutable(res);
    return res;
  end );

InstallOtherMethod( NullspaceMat, "for a cmat", 
  [IsCMatRep and IsOrdinaryMatrix],
  function( m )
    local res;
    res := NullspaceMatMutableX( MutableCopyMat( m ) );
    MakeImmutable(res);
    return res;
  end );

InstallMethod( SemiEchelonBasisNullspaceX, "for a row list matrix",
  [IsRowListMatrix],
  function( m )
    local n;
    n := NullspaceMatMutableX( m );
    return SemiEchelonBasisMutableX( n );
  end );
InstallMethod( SemiEchelonBasisNullspace, "for a row list matrix",
  [IsRowListMatrix],
  function( m )
    local n;
    n := NullspaceMatMutable( m );
    return SemiEchelonBasisMutableX( n );
  end );


#############################################################################
# Intersections and sums of spaces given by bases:
#############################################################################

InstallMethod( IntersectionAndSumRowSpaces, "for two semi echelonised bases",
  [ SEBType and IsMutable, SEBType and IsMutable ],
  function( b1, b2 )
    # Here is a proof why the following works. It is obviously better
    # than Zassenhaus' algorithm as it only works with vectors of the
    # original size rather than vectors of double length. It also
    # can profit from b1 and b2 already being semi-echelonised.
    #
    # Let V be the full row space and W be the row space generated by b1.
    # The semi-echenolised basis b1 defines a direct sum decomposition
    # V = W + W_0 where W_0 is the subspace of V of vectors having zeros
    # in the pivot columns of b1. Cleaning with b1 is an algorithm that
    # computes the projection p_0 onto W_0. The resulting dec contains 
    # coefficients such that the corresponding linear combination of b1
    # produces the result of the projection p onto W. Thus we can effectively
    # compute both projections.
    #
    # Let U be the span of b2.
    #
    # If d1 is the dimension of b1 and d2 that of b2 and s the dimension
    # of the sum, then the intersection has dimension d1+d2-s.
    #
    # By cleaning every vector of b2 with b1 we essentially compute
    # the image of U under the projection p_0. Computing a semi-echelonised
    # basis of the image in the variable "extension" computes this
    # image p_0(U) and at the same time produces generators for the
    # kernel, since every relation found in p_0(U) gives rise to an
    # element of the kernel, which is exactly the intersection U \cap W.
    # On the other hand these generators for the kernel are automatically
    # linearly independent, since the last non-zero entry is in different
    # columns. Thus they span the kernel by a dimension argument.
    #
    local d,dec,extension,images,res,v,w;
    images := Matrix([],RowLength(b1!.vectors),b1!.vectors);
    dec := ZeroVector( Length(b2), b1!.vectors );
    d := Length(b1!.vectors);
    # Calculate image:
    for v in b2!.vectors do
        w := ShallowCopy(v);
        CleanRow(b1,w,false,fail);
        Add(images,w);
    od;
    extension := SemiEchelonBasisMutableTX(images);
    res := rec( intersection := extension!.relations * b2!.vectors,
                sum := SEBMaker(ShallowCopy(b1!.vectors),
                                ShallowCopy(b1!.pivots)) );
    Append(res.sum!.vectors,extension!.vectors);
    Append(res.sum!.pivots,extension!.pivots);
    return res;
  end );

InstallMethod( IntersectionAndSumRowSpaces, "for two row list matrices",
  [ IsRowListMatrix, IsRowListMatrix ],
  function( m1, m2 )
    local b1, b2;
    b1 := SemiEchelonBasisMutable(m1);
    b2 := SemiEchelonBasisMutable(m2);
    return IntersectionAndSumRowSpaces(b1,b2);
  end );

# Just an experiment:
BindGlobal( "SumIntersectionMatCMat", 
  function(m1,m2)
    local i,int,mat,n,sum,v,w,zero;
    n := RowLength(m1);
    mat := Matrix([],2*n,m1);
    zero := ZeroVector(2*n,m1);
    for v in m1 do
        w := ShallowCopy(zero);
        CopySubVector(v,w,[1..n],[1..n]);
        CopySubVector(v,w,[1..n],[n+1..2*n]);
        Add(mat,w);
    od;
    for v in m2 do
        w := ShallowCopy(zero);
        CopySubVector(v,w,[1..n],[1..n]);
        Add(mat,w);
    od;
    mat := SemiEchelonBasisMutableX(mat);
    sum := Matrix([],n,m1);
    int := Matrix([],n,m1);
    for i in [1..Length(mat!.vectors)] do
        if mat!.pivots[i] > n then
            Add(int,mat!.vectors[i]{[n+1..2*n]});
        else
            Add(sum,mat!.vectors[i]{[1..n]});
        fi;
    od;
    return [sum,int];
  end );

# Make it public:
InstallMethod( SumIntersectionMat, "for two cmats",
  [ IsCMatRep, IsCMatRep ],
  SumIntersectionMatCMat );


#############################################################################
# Characteristic polynomials:
#############################################################################

InstallGlobalFunction( CVEC_CharacteristicPolynomialFactors,
function(m,indetnr)
  # m must be square
  local L,b,b2,closed,d,dec,f,facs,fam,i,l,lambda,newlambda,o,p,
        newpiv,pivs,subdim,v,vcopy,zero;
  zero := ZeroVector(RowLength(m),m);
  d := Length(m);
  b := EmptySemiEchelonBasis(m);
  pivs := [1..d];
  facs := [];
  f := BaseDomain(m);
  o := One(f);
  fam := FamilyObj(o);
  dec := ShallowCopy(zero);
  while Length(pivs) > 0 do
      subdim := Length(b!.pivots);
      p := pivs[1];
      v := ShallowCopy(zero);
      v[p] := o;
      b2 := EmptySemiEchelonBasis(m);
      Add(b2!.vectors,v);
      Add(b2!.pivots,p);
      lambda := [dec{[1]}];
      lambda[1][1] := o;
      RemoveSet(pivs,p);
      while true do   # break is used to jump out
          v := v * m;
          vcopy := ShallowCopy(v);
          CleanRow(b,vcopy,false,fail);
          closed := CleanRow(b2,vcopy,true,dec);
          if closed then break; fi;
          Add(lambda,dec{[1..Length(b2!.pivots)]});
          RemoveSet(pivs,b2!.pivots[Length(b2!.pivots)]);
      od;
      d := Length(b2!.pivots);
      # we have the lambdas, expressing v*m^(i-1) in terms of the semiechelon
      # basis, now we have to express v*m^d in terms of the v*m^(i-1), that
      # means inverting a matrix: 
      L := ZeroMatrix(d,Length(lambda[d]),m);
      for i in [1..d] do
          CopySubVector(lambda[i],L[i],[1..i],[1..i]);
      od;
      l := - dec{[1..d]} * L^-1;
      l := Unpack(l);
      Add(l,o);
      ConvertToVectorRep(l,Size(f));
      Add(facs,UnivariatePolynomialByCoefficients(fam,l,indetnr));
      # Add b2 to b:
      Append(b!.vectors,b2!.vectors);
      Append(b!.pivots,b2!.pivots);
  od;
  return facs;
end );

InstallMethod( CharacteristicPolynomialOfMatrix, 
  "for a row list matrix and an indet nr", 
  [IsRowListMatrix, IsPosInt],
  function( m, indetnr )
    local facs;
    facs := CVEC_CharacteristicPolynomialFactors(m, indetnr);
    return rec( poly := Product(facs), factors := facs );
  end );

InstallMethod( CharacteristicPolynomialOfMatrix, "for a row list matrix", 
  [IsRowListMatrix],
  function( m )
    local facs;
    facs := CVEC_CharacteristicPolynomialFactors(m, 1);
    return rec( poly := Product(facs), factors := facs );
  end );

InstallMethod( FactorsOfCharacteristicPolynomial, "for a row list matrix", 
  [IsRowListMatrix],
  function( m )
    return FactorsOfCharacteristicPolynomial(m,1);
  end );

InstallMethod( FactorsOfCharacteristicPolynomial, 
  "for a row list matrix and an indet nr", 
  [IsRowListMatrix, IsPosInt],
  function( m, indetnr )
    local f,facs,irrfacs,pr;
    facs := CVEC_CharacteristicPolynomialFactors(m,indetnr);
    pr := PolynomialRing(BaseDomain(m),[indetnr]);
    irrfacs := [];
    for f in facs do
        Append(irrfacs,Factors(pr,f));
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
  dimsubspc := Length( basis!.vectors );
  dimfullspc := RowLength( basis!.vectors );
  dimquotspc := dimfullspc - dimsubspc;
  diff := Difference( [1..dimfullspc], basis!.pivots );
  zerov := ZeroVector( dimquotspc, basis!.vectors ); #prepare vector type
  imgens := []; # stores result
  for i in [ 1 .. Length( gens ) ] do
    imgens[ i ] := ZeroMatrix( dimquotspc, dimquotspc, basis!.vectors );
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
  # This is the old algorithm, implemented for RowListMatrices
  local L,b,b2,closed,d,dec,f,fam,i,l,lambda,o,p,pivs,poly,subdim,v,vcopy,zero;

  zero := ZeroVector(RowLength(m),m);
  d := Length(m);
  b := EmptySemiEchelonBasis(m);
  pivs := [1..d];
  f := BaseField(m);
  poly := One(PolynomialRing(f,[1]));
  o := One(f);
  fam := FamilyObj(o);
  dec := ShallowCopy(zero);
  while Length(pivs) > 0 do
      subdim := Length(b!.pivots);
      p := pivs[1];
      v := ShallowCopy(zero);
      v[p] := o;
      b2 := EmptySemiEchelonBasis(m);
      Add(b2!.vectors,v);
      Add(b2!.pivots,p);
      lambda := [dec{[1]}];
      lambda[1][1] := o;
      RemoveSet(pivs,p);
      while true do   # break is used to jump out
          v := v * m;
          vcopy := ShallowCopy(v);
          closed := CleanRow(b2,vcopy,true,dec);
          if closed then break; fi;
          Add(lambda,dec{[1..Length(b2!.pivots)]});
          RemoveSet(pivs,b2!.pivots[Length(b2!.pivots)]);
      od;
      d := Length(b2!.pivots);
      # we have the lambdas, expressing v*m^(i-1) in terms of the semiechelon
      # basis, now we have to express v*m^d in terms of the v*m^(i-1), that
      # means inverting a matrix: 
      L := ZeroMatrix(d,d,m);
      for i in [1..d] do
          CopySubVector(lambda[i],L[i],[1..i],[1..i]);
      od;
      l := - dec{[1..d]} * L^-1;
      l := Unpack(l);
      Add(l,o);
      ConvertToVectorRep(l,Size(f));
      poly := Lcm(poly,UnivariatePolynomialByCoefficients(fam,l,1));
      # Add b2 to b:
      for v in b2!.vectors do
          if not(CleanRow(b,v,true,fail)) then
              RemoveSet(pivs,b!.pivots[Length(b!.pivots)]);
          fi;
      od;
  od;
  return poly;
end );

InstallGlobalFunction( CVEC_CharAndMinimalPolynomial, function( m, indetnr )
  # This is an early try to implement a deterministic, faster minimal
  # polynomial algorithm. It now uses the RowListMatrix interface.
  # Currently, this does not work properly, the method works in principle,
  # but there is something wrong with the factoring out of subspaces and
  # the corresponding lower and upper bounds. DO NOT USE!
  local col,deg,facs,havedim,i,irreds,l,lowbound,lowbounds,mp,mult,
        multfactoredout,multmin,nrblocks,ns,p,pr,targetmult,upbound,x;
  # First the characteristic polynomial:
  facs := CVEC_CharacteristicPolynomialFactors(m,indetnr);
  if Length(facs) = 1 then
      return rec( charpoly := facs[1], irreds := facs, mult := [1],
                  minpoly := facs[1], multmin := [1] );
  fi;
  Info(InfoCVec,2,
       "More than 1 factor, factorising characteristic polynomial...");
  # Factor all parts:
  pr := PolynomialRing(BaseDomain(m),[indetnr]);
  col := List(facs,f->Collected(Factors(pr,f)));
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
              ns := SemiEchelonBasisNullspace(x);
              havedim := Length(ns!.vectors);
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
              ns := SemiEchelonBasisNullspace(x);
              havedim := Length(ns!.vectors);
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
              targetmult := targetmult - Length(ns!.vectors)/deg;
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
    return CVEC_MinimalPolynomialMC(m,1/100,true,true,indetnr);
  end );

InstallMethod( CharAndMinimalPolynomialOfMatrix, "for a matrix", [IsCMatRep],
  function( m )
    return CVEC_MinimalPolynomialMC(m,1/100,true,true,1);
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
  # l must not be empty
  local d,g,i,m,n,p,pr,pos,x;
  n := Sum(l,Length);
  p := Characteristic(l[1]);
  d := DegreeFFE(l[1]);
  m := ZeroMatrix(n,n,l[1]);
  pos := 1;
  for i in [1..Length(l)] do
      CopySubMatrix(l[i],m,[1..Length(l[i])],[pos..pos+Length(l[i])-1],
                           [1..Length(l[i])],[pos..pos+Length(l[i])-1]);
      pos := pos + Length(l[i]);
  od;
  if InfoLevel(InfoCVec) >= 2 then 
      OverviewMat(m);
      Print("\n");
  fi;
  return m;
end );
  
InstallGlobalFunction( CVEC_ScrambleMatrices,
  function( l )
  local n,p,d,g,pr,x,xi;
  n := Length(l[1]);
  p := Characteristic(l[1]);
  d := DegreeFFE(l[1]);
  g := GL(n,p^d);
  g := List(GeneratorsOfGroup(g),CMat);
  pr := ProductReplacer(g,rec(scramble := Maximum(QuoInt(n,5),200)));
  x := Next(pr);
  xi := x^-1;
  l := List(l,y->x * y * xi);
  if InfoLevel(InfoCVec) >= 2 and Length(l) = 1 then
      OverviewMat(l[1]);
      Print("\n");
  fi;
  return l;
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
  local i,ll,s,x;
  ll := [];
  for i in [1..Length(p)] do
      for s in l[i] do
          Add(ll,CVEC_MakeJordanBlock(f,p[i],s));
      od;
  od;
  x := CVEC_ScrambleMatrices([CVEC_GlueMatrices(ll)]);
  return x[1];
end );

# The following function is used in the Monte Carlo minimal polynomial
# algorithm:
InstallGlobalFunction( CVEC_CalcOrderPolyTuned, 
function( opi, v, i, indetnr )
  local coeffs,g,h,j,k,ordpol,vv,w,Top,top;
  
  Top := range -> range[Length(range)];

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
      top := Top(opi.ranges[i]);
      for j in [2..Length(coeffs)] do
          # Now apply base changed matrix to v:
          #   v := v * opi.mm;
          # but remember, that we only store the interesting rows of mm:
          vv := ZeroMutable(v);
          CopySubVector(v,vv,[1..top-1],[2..top]);
          for k in [2..i] do
              vv[opi.ranges[k][1]] := opi.z;
          od;
          for k in [1..i] do
              AddRowVector(vv,opi.mm[k],v[Top(opi.ranges[k])],
                           1,Top(opi.ranges[k]));
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
    
# The following function is used in the Monte Carlo minimal polynomial
# algorithm:
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

InstallGlobalFunction( CVEC_MinimalPolynomialMC, 
function( m, eps, factorise, verify, indetnr )
  # The new algorithm of Cheryl and Max. Can be used as Monte Carlo algorithm
  # or as deterministic algorithm with verification.
  # eps is a cyclotomic which is an upper bound for the error probability
  # factorise is a boolean indicating, whether the resulting
  # polynomials should be factorised even if this would not be
  # necessary for verification purpose.
  # verify is a boolean indicating, whether the result should be verified,
  # thereby proving correctness, indetnr is the number of an indeterminate
  local A,B,S,coeffs,col,d,dec,g,i,irreds,j,l,lowbounds,mm,mult,multmin,newBrow,
        nrunclear,opi,ordpol,ordpolsinv,p,pivs,pr,prob,proof,rl,se,w,wcopy,ww,
        zero,ti,lcm,ti2;
  ti := Runtime();
  rl := RowLength(m);
  zero := ZeroVector(rl,m);
  pivs := [1..rl];   # those are the columns we still want pivots for
  S := EmptySemiEchelonBasis(m);
  # order polynomial infrastructure (grows over time):
  opi := rec( f := BaseDomain(m),
              d := [],          # Degrees of the relative cyclic spaces
              ranges := [],     # numbers of basis vectors
              rordpols := [],   # list of relative order polynomials
              mm := Matrix([],rl,m), # will be crucial rows of base-changed m
            );  
  opi.o := One(opi.f);
  opi.z := Zero(opi.f);
  opi.fam := FamilyObj(opi.o);
  pr := PolynomialRing(opi.f,[indetnr]);
  # We keep the base change between the basis
  #  Y = [x_1,x_1*m,x_1*m^2,...,x_1*(m^(d_1-1)),x_2,...,x_2*m^(d_2-1),...]
  # and the semi echelonised basis S by keeping Y=A*S and S=B*Y at the same 
  # time. Be are only interested in B, but we get A as a byproduct.
  A := Matrix([],rl,m);
  B := Matrix([],rl,m);
  ordpolsinv := []; # here we collect information to be used for the order pols

  Info(InfoCVec,2,"Spinning up vectors...");
  while Length(S!.vectors) < Length(m) do
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
      d := Length(S!.vectors);  # dimension of subspace:
      Add(S!.vectors,w);
      Add(S!.pivots,p);
      l := d+1;  # is always equal to Length(S!.vectors)
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
      # components d+1 .. Length(S!.vectors).
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
      SubtractSet(pivs,S!.pivots{[d+1..l]});
  od;

  # Release some memory:
  Unbind(A);
  Unbind(B);
  Unbind(S);

  ti2 := Runtime();
  Info(InfoCVec,2,"Time until now: ",ti2-ti," lap: ",ti2-ti);
  if not(factorise) and
     Length(opi.rordpols)^2 < Length(m) then   # a quick check for cyclicity:
      lcm := Lcm(opi.rordpols);
      if Degree(lcm) = rl then
          Info(InfoCVec,2,"Time until now: ",Runtime()-ti," lap: ",
               Runtime()-ti2);
          ti2 := Runtime();
          Info(InfoCVec,2,"Cyclic matrix!");
          return rec( minpoly := lcm, charpoly := lcm,
                      opi := opi,
                      irreds := false, mult := false, multmin := false,
                      proof := true );
      fi;
  fi;
  Info(InfoCVec,2,"Factoring relative order polynomials...");
  # Factor all parts:
  col := List(opi.rordpols,f->Collected(Factors(pr,f)));
  Info(InfoCVec,2,"Time until now: ",Runtime()-ti," lap: ",Runtime()-ti2);
  ti2 := Runtime();
  Info(InfoCVec,2,"Sorting and collecting factors...");
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
  Info(InfoCVec,2,"Time until now: ",Runtime()-ti," lap: ",Runtime()-ti2);
  ti2 := Runtime();
  Info(InfoCVec,2,"Number of irreducible factors in charpoly: ",Length(irreds),
                  " mult. in minpoly unknown: ",nrunclear);

  ordpol := Lcm(Set(opi.rordpols)); # this is a lower bound for the minpoly
                               # in particular, it is a multiple of rordpols[1]

  if nrunclear > 0 then
      i := 2;
      p := 1/Size(opi.f);   # probability to miss a big Jordan block with the
                            # order polynomial of one vector (upper bound)
      proof := false;
      repeat   # until verification said "OK"
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
              Info( InfoCVec, 2, "Probability to have them all (%%): ",
                     Int((1-prob)^nrunclear*1000));
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
          Info(InfoCVec,2,"Time until now: ",Runtime()-ti,
               " lap: ",Runtime()-ti2);
          ti2 := Runtime();
          if nrunclear = 0 then proof := true; break; fi;   # result is correct!

          if verify then
              Info(InfoCVec,2,"Verifying result (",nrunclear,
                   " unclear multiplicities) ...");
              proof := true;  # will be set to false once we discover something
              for j in [1..Length(irreds)] do
                  if multmin[j] < mult[j] then
                      Info(InfoCVec,2,"Working on factor: ",irreds[j],
                                      " multiplicity: ",multmin[j]);
                      mm := Value(irreds[j],m)^multmin[j];
                      se := SemiEchelonBasisMutableX(mm);
                      if Length(mm)-Length(se!.vectors) < mult[j] then
                          proof := false;
                          Info(InfoCVec,2,"Found too small multiplicity!");
                          break;
                      fi;
                  fi;
              od;
          fi;
      until not(verify) or proof;
  else
      proof := true;
  fi;

  Info(InfoCVec,2,"Time until now: ",Runtime()-ti," lap: ",Runtime()-ti2);
  return rec(minpoly := ordpol,
             charpoly := Product( opi.rordpols ),
             opi := opi,
             irreds := irreds,
             mult := mult,
             multmin := multmin,
             proof := proof);
end );

##
##  This program is free software; you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation; version 2 of the License.
##
##  This program is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##  GNU General Public License for more details.
##
##  You should have received a copy of the GNU General Public License
##  along with this program; if not, write to the Free Software
##  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
##
