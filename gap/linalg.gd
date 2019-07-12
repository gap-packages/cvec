#############################################################################
##
#W  linalg.gd               GAP 4 package `cvec'                
##                                                            Max Neunhoeffer
##
##  Copyright (C) 2007  Max Neunhoeffer, Lehrstuhl D f. Math., RWTH Aachen
##  This file is free software, see license information at the end.
##
##  This file contains the higher levels for efficient implementation of
##  some linear algebra routines for compact vectors over finite fields. 
##

#############################################################################
# High speed cleaning of vectors, semi-echelonised matrices:
#############################################################################


DeclareOperation( "SEBMaker", [IsRowListMatrix,IsList] );
DeclareOperation( "EmptySemiEchelonBasis", [ IsRowListMatrix ] );
DeclareOperation( "EmptySemiEchelonBasis", [ IsRowVector ] );
DeclareOperation( "SemiEchelonBasisMutable", [ IsRowListMatrix ] );
DeclareOperation( "SemiEchelonBasisMutable", [ IsRecord ] );
DeclareOperation( "SemiEchelonBasisMutableX", [IsRowListMatrix] );
DeclareOperation( "SemiEchelonBasisMutableTX", [IsRowListMatrix] );
DeclareOperation( "SemiEchelonBasisMutableT", [IsRowListMatrix] );
DeclareOperation( "SemiEchelonBasisMutablePX", [IsRowListMatrix] );
DeclareOperation( "SemiEchelonBasisMutableP", [IsRowListMatrix] );

DeclareFilter( "IsCMatSEB" );
DeclareFilter( "HasPivots" );

# A shortcut:
BindGlobal( "SEBType", 
  IsBasis and IsSemiEchelonized and HasPivots and IsComponentObjectRep );

# Operations for semi echolon basis:
DeclareOperation( "Vectors", [SEBType] );
DeclareOperation( "Pivots", [SEBType] );

DeclareOperation( "CleanRow", 
 [SEBType,IsVectorObj,IsBool,IsObject]);
# CleanRow ( basis, vec, extend, dec )
#   basis is record with the following components:
#       .vectors  : matrix whose rows are the vectors
#       .pivots   : pivot columns
#   vec is a vector
#   extend is true or false
#     true:   clean, extend if necessary
#     false:  clean, do not extend
#   dec, if not equal to fail, must be a vectors over the same field of
#     length at least the length of the basis
#     (+1, if extend=true, because the coefficient of the new basis vector
#     in a decomposition of vec is also written in to dec)
# Cleans vec with basis. If vec lies in the span, true is returned, 
# otherwise false. In case of false, if extend is true, the basis is
# extended. If dec is not equal to fail, then the coefficients of the
# linear combination of the vectors in the basis that represents vec
# is put into dec.

DeclareOperation( "LinearCombination", [SEBType, IsVectorObj] );

DeclareOperation( "NullspaceMatMutableX", [IsRowListMatrix] );
DeclareOperation( "NullspaceMatMutable", [IsRowListMatrix] );
DeclareOperation( "SemiEchelonBasisNullspaceX", [IsRowListMatrix] );
DeclareOperation( "SemiEchelonBasisNullspace", [IsRowListMatrix] );


#############################################################################
# Intersections and sums of spaces given by bases:
#############################################################################

DeclareOperation( "IntersectionAndSumRowSpaces", 
                  [SEBType,SEBType] );
DeclareOperation( "IntersectionAndSumRowSpaces", 
                  [IsRowListMatrix,IsRowListMatrix] );


#############################################################################
# Characteristic and Minimal polynomial:
#############################################################################

DeclareGlobalFunction( "CVEC_CharacteristicPolynomialFactors" );
DeclareGlobalFunction( "CVEC_CharAndMinimalPolynomial" );
DeclareGlobalFunction( "CVEC_MinimalPolynomial" );

DeclareOperation( "CharacteristicPolynomialOfMatrix", [IsObject] );
DeclareOperation( "CharacteristicPolynomialOfMatrix", [IsObject, IsInt] );
# Returns the characteristic polynomial of a matrix. Returns a record
# with components "poly" (the polynomial) and "factors" (a list of
# factors which happened to come out of the calculation, the product of 
# which is the charpoly)
# Second argument is indeterminate number.

DeclareOperation( "FactorsOfCharacteristicPolynomial", [IsObject] );
DeclareOperation( "FactorsOfCharacteristicPolynomial", [IsObject, IsInt] );
# Returns a list with the irreducible factors of the characteristic
# polynomial of a matrix, sorted in ascending order by degree.
# Second argument is indeterminate number.

DeclareOperation( "MinimalPolynomialOfMatrix", [IsObject] );
DeclareOperation( "MinimalPolynomialOfMatrix", [IsObject, IsInt] );

DeclareOperation( "CharAndMinimalPolynomialOfMatrix", [IsObject] );
DeclareOperation( "CharAndMinimalPolynomialOfMatrix", [IsObject, IsInt] );
# Returns a record with the following components:
#  charpoly: characteristic polynomial
#  irreds:   set of the irreducible factors of the char. poly
#  mult:     multiplicities of the irreducible factors in the char. poly
#  minpoly:  minimal polynomial
#  multmin:  multiplicities of the irreducible factors in the minimal poly
 
#############################################################################
# Some functions to put together bigger matrices from smaller ones:
#############################################################################

DeclareGlobalFunction( "CVEC_GlueMatrices" );
DeclareGlobalFunction( "CVEC_ScrambleMatrices" );
DeclareGlobalFunction( "CVEC_MakeJordanBlock" );
DeclareGlobalFunction( "CVEC_MakeExample" );


#############################################################################
# A Monte-Carlo algorithm for the minimal polynomial:
#############################################################################

DeclareGlobalFunction( "CVEC_CalcOrderPolyTuned" );
DeclareGlobalFunction( "CVEC_FactorMultiplicity" );
DeclareGlobalFunction( "MinimalPolynomialOfMatrixMC" );

##
##  This program is free software; you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation; either version 2 of the License,
##  or (at your option) any later version.
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
