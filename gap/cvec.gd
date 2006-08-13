#############################################################################
##
#W  cvec.gd               GAP 4 package `cvec'                
##                                                            Max Neunhoeffer
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

DeclareRepresentation( "IsCVecRep", 
  IsDataObjectRep and HasLength and IsCopyable and CanEasilyCompareElements and
  CanEasilySortElements and IsListDefault and IsSmallList and 
  IsConstantTimeAccessList and IsFinite and IsRowVectorObj, [] );
  # How about IsNoImmediateMethodsObject???
DeclareFilter( "IsCVecRepOverSmallField" );

#############################################################################
## Information about the base fields:
#############################################################################

DeclareGlobalVariable( "CVEC_q" );
DeclareGlobalVariable( "CVEC_F" );
DeclareGlobalVariable( "CVEC_lens" );
DeclareGlobalVariable( "CVEC_classes" );
DeclareGlobalVariable( "CVEC_BestGreaseTab" );

DeclareGlobalFunction( "CVEC_NewCVecClass" );
DeclareGlobalFunction( "CVEC_NewCVecClassSameField" );

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
# Access to the base field:
#############################################################################

DeclareOperation( "CVecClass", [IsObject] );
DeclareOperation( "CVecClass", [IsObject, IsInt] );
DeclareOperation( "CVecClass", [IsPosInt, IsPosInt, IsInt] );


#############################################################################
# Making of vectors and conversions:
#############################################################################

DeclareOperation( "CVec", [IsObject, IsPosInt, IsPosInt] );
DeclareOperation( "CVec", [IsObject, IsObject] );
DeclareOperation( "CVec", [IsObject] );
DeclareOperation( "Unpack", [IsCVecRep] );
DeclareOperation( "IntegerRep", [IsObject] );
DeclareOperation( "CVecNumber", [IsInt, IsCVecClass] );
DeclareOperation( "CVecNumber", [IsInt, IsPosInt, IsPosInt, IsPosInt] );

DeclareGlobalFunction( "CVEC_New" );

DeclareGlobalVariable( "CVEC_CharactersForDisplay" );

DeclareGlobalFunction( "CVEC_HandleScalar" );


#############################################################################
# Looking for nonzero entries from behind:
#############################################################################

DeclareOperation( "PositionLastNonZero", [IsList] );


#############################################################################
# Slicing and friends: 
#############################################################################

DeclareGlobalFunction( "CVEC_Slice" );
DeclareGlobalFunction( "CVEC_SliceList" );
DeclareGlobalFunction( "CVEC_Concatenation" );

#############################################################################
# The making of good hash functions:
#############################################################################

DeclareGlobalFunction( "CVEC_HashFunctionForCVecs" );

