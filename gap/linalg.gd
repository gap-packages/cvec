#############################################################################
##
#W  linalg.gd               GAP 4 package `cvec'                
##                                                            Max Neunhoeffer
##
#Y  Copyright (C)  2005,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
##
##  This file contains the higher levels for efficient implementation of
##  some linear algebra routines for compact vectors over finite fields. 
##

#############################################################################
# High speed cleaning of vectors, semi-echelonised matrices:
#############################################################################


DeclareOperation( "CleanRow", [IsRecord, IsObject, IsBool, IsObject] );
# CleanRow ( basis, vec, extend, dec )
#   basis is record with the following components:
#       .vectors  : matrix bzw. liste von Vektoren
#       .pivots   : spalten der pivots
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

DeclareOperation( "EmptySemiEchelonBasis", [IsObject] );
# EmptySemiEchelonBasis is an operation:
# EmptySemiEchelonBasis( vector )
#   vector is a sample vector

DeclareOperation( "MakeSemiEchelonBasis", [IsObject] );

DeclareOperation( "SemiEchelonRowsX", [IsObject] );
DeclareOperation( "SemiEchelonRows", [IsObject] );
DeclareOperation( "SemiEchelonRowsTX", [IsObject] );
DeclareOperation( "SemiEchelonRowsT", [IsObject] );
DeclareOperation( "SemiEchelonRowsPX", [IsObject] );
DeclareOperation( "SemiEchelonRowsP", [IsObject] );
# For compatibility:
DeclareOperation( "SemiEchelonRowsXp", [IsObject] );

DeclareOperation( "MutableNullspaceMatX", [IsObject] );
DeclareOperation( "MutableNullspaceMat", [IsObject] );
DeclareOperation( "SemiEchelonNullspaceX", [IsObject] );
DeclareOperation( "SemiEchelonNullspace", [IsObject] );


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
DeclareGlobalFunction( "CVEC_MakeJordanBlock" );
DeclareGlobalFunction( "CVEC_MakeExample" );

DeclareGlobalFunction( "CVEC_RelativeOrderPoly" );
DeclareGlobalFunction( "CVEC_CalcOrderPoly" );
DeclareGlobalFunction( "CVEC_NewMinimalPolynomial" );
DeclareGlobalFunction( "CVEC_FactorMultiplicity" );
DeclareGlobalFunction( "CVEC_NewMinimalPolynomialMCTuned" );
DeclareGlobalFunction( "CVEC_NewMinimalPolynomialMC" );

