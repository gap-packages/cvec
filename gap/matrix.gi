#############################################################################
##
#W  matrix.gi             GAP 4 package `cvec'
##                                                            Max Neunhoeffer
##
##  Copyright (C) 2007  Max Neunhoeffer, Lehrstuhl D f. Math., RWTH Aachen
##  This file is free software, see license information at the end.
##
##  This file contains methods for matrices, mostly for cmats.
##  This implements some of the functionality in matrix.g{d,i} in the
##  main GAP library for cmats.
##
##  For CMats these are basically obsolete because of the functions
##  around SemiEchelonRows* in linalg.gi, which however have a slightly
##  different interface.
##

# SemiEchelonMat and friends:
# (note that we basically copy the library method, but use advanced
#  functionality of AddRowVector and MultRowVectors here):

InstallMethod( SemiEchelonMatDestructive, "for a cmat",
    [ IsMutable and IsCMatRep ],
    function( mat )
    local nrows,     # number of rows in <mat>
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
    ncols:= RowLength( mat );

    heads:= ListWithIdenticalEntries( ncols, 0 );
    nzheads := [];
    vectors := [];
    for i in [ 1 .. nrows ] do
        row := mat[i];
        # Reduce the row with the known basis vectors.
        for j in [ 1 .. Length(nzheads) ] do
            x := row[nzheads[j]];
            if not(IsZero(x)) then
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
InstallMethod( SemiEchelonMat, "for a cmat", [ IsCMatRep ],
    function( mat )
      return SemiEchelonMatDestructive( MutableCopyMat( mat ) );
    end );

InstallMethod( SemiEchelonMatTransformationDestructive,
    "for a cmat", [ IsMutable and IsCMatRep ],
    function( mat )
    local nrows,     # number of rows in <mat>
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
    ncols := RowLength( mat );

    one   := One( BaseDomain( mat ) );

    heads   := ListWithIdenticalEntries( ncols, 0 );
    vectors := Matrix([],ncols,mat);
    
    zv := ZeroVector(nrows,mat);
    T := Matrix([],nrows,mat);
    for i in [1..nrows] do
        Add(T,ShallowCopy(zv));
        T[i][i] := one;
    od;
    coeffs    := Matrix([],nrows,mat);
    relations := Matrix([],nrows,mat);
    
    for i in [ 1 .. nrows ] do
        row := mat[i];
        row2 := T[i];

        # Reduce the row with the known basis vectors.
        for j in [ 1 .. ncols ] do
            head := heads[j];
            if head <> 0 then
                x := - row[j];
                if not(IsZero(x)) then
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
    "for a cmat", [ IsCMatRep ],
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
