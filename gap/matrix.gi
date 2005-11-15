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
    return CVEC.CMatMaker(l,m!.vecclass);
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
    
    cl := CVEC.NewCVecClass( mat!.vecclass![CVEC_IDX_fieldinfo]![CVEC_IDX_p], 
                             mat!.vecclass![CVEC_IDX_fieldinfo]![CVEC_IDX_d],
                             nrows );
    zv := CVEC.NEW(cl,cl![CVEC_IDX_type]);
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
