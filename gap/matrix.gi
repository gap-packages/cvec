#############################################################################
##
#W  matrix.gi             GAP 4 package `cvec'                Max Neunhoeffer
##
#Y  Copyright (C)  2005,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
##
##  This file contains methods for matrices, mostly for cmats.
##  This implements some of the functionality in matrix.g{d,i} in the
##  main GAP library for cmats.
##

InstallMethod( IsDiagonalMat, "for a cmat", [IsCMatRep and IsMatrix],
  function(m)
    local i,mi;
    mi := Minimum(m!.len,m!.vecclass![CVEC_IDX_len]);
    i := 1;
    while i <= mi do
        if PositionNonZero(m!.rows[i+1]) < i or
           PositionLastNonZero(m!.rows[i+1]) > i then
            return false;
        fi;
        i := i + 1;
    od;
    while i <= m!.len do
        if not(IsZero(m!.rows[i+1])) then
            return false;
        fi;
        i := i + 1;
    od;
    return true;
  end);

InstallMethod( IsUpperTriangularMat, "for a cmat", [IsCMatRep and IsMatrix],
  function(m)
    local i,mi;
    mi := Minimum(m!.len,m!.vecclass![CVEC_IDX_len]);
    i := 1;
    while i <= mi do
        if PositionNonZero(m!.rows[i+1]) < i then
            return false;
        fi;
        i := i + 1;
    od;
    while i <= m!.len do
        if not(IsZero(m!.rows[i+1])) then
            return false;
        fi;
        i := i + 1;
    od;
    return true;
  end);

InstallMethod( IsLowerTriangularMat, "for a cmat", [IsCMatRep and IsMatrix],
  function(m)
    local i,mi;
    mi := Minimum(m!.len,m!.vecclass![CVEC_IDX_len]);
    i := 1;
    while i <= mi do
        if PositionLastNonZero(m!.rows[i+1]) > i then
            return false;
        fi;
        i := i + 1;
    od;
    while i <= m!.len do
        if not(IsZero(m!.rows[i+1])) then
            return false;
        fi;
        i := i + 1;
    od;
    return true;
  end);

# Copying of matrices:

InstallMethod( MutableCopyMat, "for a cmat", [IsCMatRep and IsMatrix],
  function(m)
    local l,i;
    l := 0*[1..m!.len+1];
    for i in [2..m!.len+1] do
        l[i] := ShallowCopy(m!.rows[i]);
    od;
    Unbind(l[1]);
    return CVEC_CMatMaker(l,m!.vecclass);
  end);

# SemiEchelonMat and friends:
# (note that we basically copy the library method, but use advanced
#  functionality of AddRowVector and MultRowVectors here):

InstallMethod( SemiEchelonMatDestructive, "for a cmat",
    [ IsMatrix and IsMutable and IsCMatRep ],
    function( mat )
    local zero,      # zero of the field of <mat>
          nrows,     # number of rows in <mat>
          ncols,     # number of columns in <mat>
          vectors,   # list of basis vectors
          heads,     # list of pivot positions in `vectors'
          i,         # loop over rows
          j,         # loop over columns
          x,         # a current element
          nzheads,   # list of non-zero heads
          row,       # the row of current interest
          inv;       # inverse of a matrix entry

    nrows:= Length( mat );
    ncols:= Length( mat[1] );

    zero:= Zero( mat[1][1] );

    heads:= ListWithIdenticalEntries( ncols, 0 );
    nzheads := [];
    vectors := [];
    for i in [ 1 .. nrows ] do
        row := mat[i];
        # Reduce the row with the known basis vectors.
        for j in [ 1 .. Length(nzheads) ] do
            x := row[nzheads[j]];
            if x <> zero then
              AddRowVector( row, vectors[ j ], - x , nzheads[j],ncols);
            fi;
        od;
        j := PositionNonZero( row );
        if j <= ncols then

            # We found a new basis vector.
            inv:= Inverse( row[j] );
            if inv = fail then
              return fail;
            fi;
            MultRowVector( row, inv, j, ncols );
            Add( vectors, row );
            Add( nzheads, j );
            heads[j]:= Length( vectors );

        fi;
    od;
    return rec( heads   := heads,
                vectors := vectors );
    end );
InstallMethod( SemiEchelonMat, "for a cmat", [ IsMatrix and IsCMatRep ],
    function( mat )
      return SemiEchelonMatDestructive( MutableCopyMat( mat ) );
    end );

InstallMethod( SemiEchelonMatTransformationDestructive,
    "for a cmat", [ IsMatrix and IsMutable and IsCMatRep ],
    function( mat )
    local zero,      # zero of the field of <mat>
          nrows,     # number of rows in <mat>
          ncols,     # number of columns in <mat>
          vectors,   # list of basis vectors
          heads,     # list of pivot positions in 'vectors'
          i,         # loop over rows
          j,         # loop over columns
          T,         # transformation matrix
          coeffs,    # list of coefficient vectors for 'vectors'
          relations, # basis vectors of the null space of 'mat'
          row, head, x, row2, one, cl, zv;
            
    nrows := Length( mat );
    ncols := Length( mat[1] );

    zero  := Zero( mat[1][1] );
    one   := One( mat[1][1] );

    heads   := ListWithIdenticalEntries( ncols, 0 );
    vectors := CMat([],mat!.vecclass);
    
    cl := CVEC_NewCVecClass( mat!.vecclass![CVEC_IDX_fieldinfo]![CVEC_IDX_p], 
                             mat!.vecclass![CVEC_IDX_fieldinfo]![CVEC_IDX_d],
                             nrows );
    zv := CVEC_NEW(cl,cl![CVEC_IDX_type]);
    T := CMat([],cl);
    for i in [1..nrows] do
        Add(T,ShallowCopy(zv));
        T[i][i] := one;
    od;
    coeffs    := CMat([],cl);
    relations := CMat([],cl);
    
    for i in [ 1 .. nrows ] do
        row := mat[i];
        row2 := T[i];

        # Reduce the row with the known basis vectors.
        for j in [ 1 .. ncols ] do
            head := heads[j];
            if head <> 0 then
                x := - row[j];
                if x <> zero then
                    AddRowVector( row2, coeffs[ head ],  x );
                    AddRowVector( row,  vectors[ head ], x, j, ncols );
                fi;
            fi;
        od;

        j:= PositionNonZero( row );
        if j <= ncols then
            # We found a new basis vector.
            x:= Inverse( row[j] );
            Add( coeffs,  row2 * x );
            Add( vectors, row  * x );
            heads[j]:= Length( vectors );
        else
            Add( relations, row2 );
        fi;
    od;

    return rec( heads     := heads,
                vectors   := vectors,
                coeffs    := coeffs,
                relations := relations );
end );
InstallMethod( SemiEchelonMatTransformation, 
    "for a cmat", [ IsMatrix and IsCMatRep ],
    function( mat )
      return SemiEchelonMatTransformationDestructive( MutableCopyMat( mat ) );
    end );


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

InstallGlobalFunction( OverviewMat, function(M)
  local i,j,s,ts,tz,z;
  z := Length(M);
  s := Length(M[1]);
  tz := QuoInt(z+39,40);
  ts := QuoInt(s+39,40);
  for i in [1..QuoInt(z+tz-1,tz)] do
      for j in [1..QuoInt(s+ts-1,ts)] do
          if IsZero(ExtractSubMatrix(M,[1+(i-1)*tz..Minimum(i*tz,z)],
                                       [1+(j-1)*ts..Minimum(j*ts,s)])) then
              Print(".");
          else
              Print("*");
          fi;
      od;
      Print("\n");
  od;
end );
InstallMethod( KroneckerProduct, "for cmats", 
               [ IsMatrix and IsCMatRep, IsMatrix and IsCMatRep],
  function( A, B )
    local rowsA, rowsB, colsA, colsB, newclass, AxB, i, j;
      rowsA := Length(A);
      colsA := Length(A[1]);
      rowsB := Length(B);
      colsB := Length(B[1]);

      newclass := CVecClass( A[1], colsA * colsB );
      AxB := CVEC_ZeroMat( rowsA * rowsB, newclass );

      # Cache matrices
      # not implemented yet

      for i in [1..rowsA] do
	for j in [1..colsA] do
	  CopySubMatrix( A[i][j] * B, AxB, 
			 [ 1 .. rowsB ], [ rowsB * (i-1) + 1 .. rowsB * i ],                             [ 1 .. colsB ], [ (j-1) * colsB + 1 .. j * colsB ] );
	od;
      od;
      return AxB;
    end );

# Some code to allow code reusage from the GAP library:

# todo:
# CharacteristicPolynomial
# MinimalPolynomial
# Order
# BaseMat --> Delegiert auf SemiEchelonMatDestructive
# SemiEchelonMat and friends [-Transformation]
# DefaultFieldOfMatrix?
# SumIntersectionMat
# DeterminantMat
# DiagonalizeMat?
# NullspaceMat
# TriangulizedNullspaceMat
# VectorSpace (list of vectors)
# RankMat
# SemiEchelonMats?
# 

# Low level:
# [Mutable]TransposedMat
