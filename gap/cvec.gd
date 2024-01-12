#############################################################################
##
#W  cvec.gd               GAP 4 package `cvec'                
##                                                            Max Neunhoeffer
##
##  Copyright (C) 2007  Max Neunhoeffer, Lehrstuhl D f. Math., RWTH Aachen
##  This file is free software, see license information at the end.
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
  IsConstantTimeAccessList and IsFinite and IsVectorObj, [] );
  # How about IsNoImmediateMethodsObject???
DeclareFilter( "IsCVecRepOverSmallField" );
DeclareFilter( "IsCVecRepOverPrimeField" );

#############################################################################
## Information about the base fields:
#############################################################################

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
##  ![15]: filter list for the creation of new cmats over this field

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
##  ![8]: starting type (mutable vesion) for new cmats using vectors in
##        this class

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
DeclareOperation( "IntegerRep", [IsObject] );
DeclareOperation( "CVecNumber", [IsInt, IsCVecClass] );
DeclareOperation( "CVecNumber", [IsInt, IsPosInt, IsPosInt, IsPosInt] );

DeclareGlobalFunction( "CVEC_New" );

DeclareGlobalFunction( "CVEC_HandleScalar" );

DeclareOperation( "Memory", [IsCVecRep] );

#############################################################################
# Frobenius automorphisms for vectors:
#############################################################################

DeclareOperation("^", [IsCVecRep, IsMapping and IsOne]);
DeclareOperation("^", [IsCVecRep, IsFrobeniusAutomorphism]);

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
