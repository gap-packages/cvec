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

DeclareRepresentation( "IsCScaRep", IsDataObjectRep, [] );
DeclareRepresentation( "IsCVecRep", IsDataObjectRep, [] );
DeclareRepresentation( "IsCMatRep", IsComponentObjectRep, [] );

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
##         for q <= MAXSIZE_GF_INTERNAL this is FFEFamily(p) from the 
##         GAP library

DeclareRepresentation( "IsCVecClass", IsPositionalObjectRep, [] );
## We use the same symbolic names for these indices as exported from cvec.c
## in the CVEC record: CVEC_IDX_fieldinfo and so on:
##  ![1]: field info (see above) for base field
##  ![2]: length of vectors
##  ![3]: wordlen of vectors
##  ![4]: starting type (mutable version) for new vectors in this class
##  ![5]: GF(p,d)
##  ![6]: the class of the corresponding scalars, that is for (p,1,d)
##  From here on we only have values for d=1 and otherwise fail:
##  ![7]:  the starting type (immutable version) for new vectors
##         that are used for scalars of GF(p,l) in this class
##  ![8]:  the zero scalar of GF(p,l)
##  ![9]:  the one scalar of GF(p,l)
##  ![10]: the primitive root of GF(p,l)  (represented by x)
##  ![11]: rootinfo for taking roots, a list, see Sqrt and friends
##  ![12]: a dummy scalar used for overwriting during multiplication
##  again for d=1:
##  ![13]: for d=1 if GF(p,d) is used: conway-Polynomial as compressed 
##         vector over GF(p) or fail otherwise
##  ![14]: CVEC.lens[pos] where pos = Position(CVEC.q,q)
##  ![15]: CVEC.classes[pos] where pos = Position(CVEC.q.q)
##         the latter are used for fast access to other cvec classes over
##         the same field.
##  



#############################################################################
# Looking for nonzero entries from behind:
#############################################################################

DeclareOperation( "PositionLastNonZero", [IsList] );

#############################################################################
# Making of vectors and matrices, conversions:
#############################################################################

DeclareOperation( "CSca", [IsList, IsObject] );
DeclareOperation( "CSca", [IsList, IsPosInt, IsPosInt] );
DeclareOperation( "CVec", [IsObject, IsPosInt, IsPosInt] );
DeclareOperation( "CVec", [IsObject, IsObject] );
DeclareOperation( "CVec", [IsObject] );
DeclareOperation( "CMat", [IsList] );
DeclareOperation( "CMat", [IsList, IsObject] );
DeclareOperation( "CMat", [IsList, IsObject, IsBool] );
DeclareOperation( "Unpack", [IsObject] );
DeclareOperation( "FFEList", [IsObject] );

DeclareFilter( "HasGreaseTab" );
DeclareOperation( "GreaseMat", [IsCMatRep, IsInt]);
DeclareOperation( "UnGreaseMat", [IsCMatRep]);


#############################################################################
# Access to the base field:
#############################################################################

DeclareOperation( "BaseField", [IsObject] );
DeclareOperation( "CVecClass", [IsObject] );

