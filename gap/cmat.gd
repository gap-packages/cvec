#############################################################################
##
#W  cmat.gd               GAP 4 package `cvec'                
##                                                            Max Neunhoeffer
##
#Y  Copyright (C)  2005,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
##
##  This file contains the higher levels for compact matrices over finite 
##  fields. 
##

#############################################################################
## The technical stuff for typing:
#############################################################################

DeclareRepresentation( "IsCMatRep", 
  IsComponentObjectRep and IsMatrix and IsOrdinaryMatrix and HasLength and
  IsRowListMatrix, [] );


#############################################################################
# Making of matrices:
#############################################################################

DeclareOperation( "CMat", [IsList] );
DeclareOperation( "CMat", [IsList, IsObject] );
DeclareOperation( "CMat", [IsList, IsObject, IsBool] );

DeclareGlobalFunction( "CVEC_CMatMaker" );

DeclareGlobalFunction( "CVEC_ZeroMat" );
DeclareGlobalFunction( "CVEC_IdentityMat" );
DeclareGlobalFunction( "CVEC_RandomMat" );

#############################################################################
# Greasing of matrices:
#############################################################################

DeclareFilter( "HasGreaseTab" );
DeclareOperation( "GreaseMat", [IsCMatRep, IsInt]);
DeclareOperation( "UnGreaseMat", [IsCMatRep]);


#############################################################################
# Helper function for the display of matrices:
#############################################################################

DeclareGlobalFunction( "OverviewMat" );

#############################################################################
# CopySubMatrix and ExtractSubMatrix:
#############################################################################

DeclareGlobalFunction( "CVEC_CopySubMatrix" );
DeclareGlobalFunction( "CVEC_CopySubMatrixUgly" );

#############################################################################
# The making of good hash functions:
#############################################################################

DeclareGlobalFunction( "CVEC_HashFunctionForCMats" );

#############################################################################
# Greasing:
#############################################################################

DeclareGlobalVariable( "CVEC_SpreadTabCache" );
DeclareGlobalFunction( "CVEC_MakeSpreadTab" );
DeclareGlobalFunction( "CVEC_OptimizeGreaseHint" );

#############################################################################
# Inversion of matrices:
#############################################################################

DeclareGlobalFunction( "CVEC_InverseWithoutGrease" );
DeclareGlobalFunction( "CVEC_InverseWithGrease" );

#############################################################################
# I/O for Matrices:
#############################################################################

DeclareGlobalFunction( "CVEC_WriteMat" );
DeclareGlobalFunction( "CVEC_WriteMatToFile" );
DeclareGlobalFunction( "CVEC_WriteMatsToFile" );

DeclareGlobalFunction( "CVEC_ReadMat" );
DeclareGlobalFunction( "CVEC_ReadMatFromFile" );
DeclareGlobalFunction( "CVEC_ReadMatsFromFile" );

#############################################################################
# Folding of matrices and vectors:
#############################################################################

DeclareOperation( "Unfold", [ IsCMatRep ] );
DeclareOperation( "Fold", [ IsCVecRep, IsInt ] );

#############################################################################
# Grease calibration:
#############################################################################

DeclareGlobalFunction( "GreaseCalibration" );

