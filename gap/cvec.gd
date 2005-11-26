#############################################################################
##
#W  cvec.gd               GAP 4 package `cvec'                Max Neunhoeffer
##
#Y  Copyright (C)  2005,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
##
##  This file contains the higher levels for compact vectors over finite 
##  fields. 
##

#############################################################################
## Info Class:
#############################################################################

DeclareInfoClass( "InfoCVec" );

#############################################################################
## The technical stuff for typing:
#############################################################################

BindGlobal("CVecFieldInfoFamily",NewFamily("CVecFieldInfoFamily"));
BindGlobal("CVecClassFamily",NewFamily("CVecClassFamily"));

DeclareRepresentation( "IsCVecRep", IsDataObjectRep, [] );
DeclareRepresentation( "IsCMatRep", IsComponentObjectRep, [] );
DeclareFilter( "IsCVecRepOverSmallField" );

#############################################################################
## Information about the base fields:
#############################################################################

## Do not change the following numbers without adjusting cvec.c!!!

DeclareRepresentation( "IsCVecFieldInfo", IsPositionalObjectRep, [] );
## Such an object holds the following information:
## We use the same symbolic names for these indices as exported from cvec.c
## in the CVEC record: CVEC_IDX_p and so on:
##  ![1] : p: cardinality of prime field
##  ![2] : d: degree of extension over prime field
##  ![3] : q=p^d as GAP integer
##  ![4] : a GAP string object containing the coefficients of the 
##         Conway polynomial as unsigned int []
##  ![5] : bits per element of the prime field
##  ![6] : prime field elements per Word
##         Note that for 64 bit machines we always put only twice as much
##         prime field elements into a Word than for 32 bit machines (even if
##         one more would fit!) such that conversion between binary formats
##         is easier later on.
##  ![7] : a GAP string object containing C data for internal use, see C part
##  ![8] : best grease level
##  ![9] : length of a grease table
##  ![10]: filter list for the creation of new vectors over this field
##  ![11]: table for GF(q) -> [0..q-1] conversion for q <= MAXSIZE_GF_INTERNAL
##  ![12]: table for [0..q-1] -> GF(q) conversion for q <= MAXSIZE_GF_INTERNAL
##  ![13]: 0 for q <= MAXSIZE_GF_INTERNAL, otherwise 1 if q is an 
##         immediate integer, 2 else
##  ![14]: the scalars family, vectors get the CollectionsFamily
##         this is FFEFamily(p) from the GAP library

DeclareRepresentation( "IsCVecClass", IsPositionalObjectRep, [] );
## We use the same symbolic names for these indices as exported from cvec.c
## in the CVEC record: CVEC_IDX_fieldinfo and so on:
##  ![1]: field info (see above) for base field
##  ![2]: length of vectors
##  ![3]: wordlen of vectors
##  ![4]: starting type (mutable version) for new vectors in this class
##  ![5]: GF(p,d)
##  ![6]: CVEC_lens[pos] where pos = Position(CVEC_q,q)
##  ![7]: CVEC_classes[pos] where pos = Position(CVEC_q.q)
##         the latter are used for fast access to other cvec classes over
##         the same field.


#############################################################################
# Looking for nonzero entries from behind:
#############################################################################

DeclareOperation( "PositionLastNonZero", [IsList] );

#############################################################################
# Making of vectors and matrices, conversions:
#############################################################################

DeclareOperation( "CVec", [IsObject, IsPosInt, IsPosInt] );
DeclareOperation( "CVec", [IsObject, IsObject] );
DeclareOperation( "CVec", [IsObject] );
DeclareOperation( "CMat", [IsList] );
DeclareOperation( "CMat", [IsList, IsObject] );
DeclareOperation( "CMat", [IsList, IsObject, IsBool] );
DeclareOperation( "Unpack", [IsObject] );
DeclareOperation( "IntegerRep", [IsObject] );

DeclareOperation( "CVecNumber", [IsInt, IsCVecClass] );
DeclareOperation( "CVecNumber", [IsInt, IsPosInt, IsPosInt, IsPosInt] );

DeclareFilter( "HasGreaseTab" );
DeclareOperation( "GreaseMat", [IsCMatRep, IsInt]);
DeclareOperation( "UnGreaseMat", [IsCMatRep]);


#############################################################################
# Access to the base field:
#############################################################################

DeclareOperation( "BaseField", [IsObject] );
DeclareOperation( "CVecClass", [IsObject] );
DeclareOperation( "CVecClass", [IsObject, IsInt] );
DeclareOperation( "CVecClass", [IsPosInt, IsPosInt, IsInt] );


DeclareOperation( "CleanRow", [IsRecord, IsObject, IsBool, IsObject] );
# CleanRow ( basis, vec, extend, dec )
#   basis ist record mit Eintraegen:
#       .vectors  : matrix bzw. liste von Vektoren
#       .pivots   : spalten der pivots
#   vec ist ein Vektor
#   extend ist true oder false
#     true:   clean, extend if necessary
#     false:  clean, do not extend
#   dec, falls ungleich fail, muss mindestens Laenge der Basis haben
#     (+1, falls extend=true)
#     ein vektor mind. der Laenge der Basis  (+1)

DeclareOperation( "EmptySemiEchelonBasis", [IsObject, IsInt] );
DeclareOperation( "EmptySemiEchelonBasis", [IsObject] );
# EmptySemiEchelonBasis ist Operation:
# EmptySemiEchelonBasis( vector [,greaselev] )
#   vector ist ein Beispielvektor
#   greaselev ist die Grease-Level

DeclareOperation( "MakeSemiEchelonBasis", [IsObject] );

DeclareOperation( "CharacteristicPolynomialOfMatrix", [IsObject] );
DeclareOperation( "CharacteristicPolynomialOfMatrix", [IsObject, IsInt] );
# Returns the characteristic polynomial of a matrix.
# Second argument is indeterminate number.

DeclareOperation( "FactorsOfCharacteristicPolynomial", [IsObject] );
DeclareOperation( "FactorsOfCharacteristicPolynomial", [IsObject, IsInt] );
# Returns a list with the irreducible factors of the characteristic
# polynomial of a matrix, sorted in ascending order by degree.
# Second argument is indeterminate number.

