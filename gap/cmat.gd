#############################################################################
##
#W  cmat.gd               GAP 4 package `cvec'                
##                                                            Max Neunhoeffer
##
##  Copyright (C) 2007  Max Neunhoeffer, Lehrstuhl D f. Math., RWTH Aachen
##  This file is free software, see license information at the end.
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

DeclareOperation( "Memory", [IsCMatRep] );

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

DeclareGlobalFunction( "CVEC_ComputeVectorLengthsForCalibration" );
DeclareGlobalFunction( "CVEC_FastFill" );
DeclareGlobalFunction( "GreaseCalibration" );
DeclareGlobalFunction( "CVEC_StoreGreaseCalibration" );
DeclareGlobalFunction( "CVEC_AddMat" );
DeclareGlobalFunction( "CVEC_MulMat" );
DeclareGlobalFunction( "CVEC_MultiplyWinograd" );
DeclareGlobalFunction( "CVEC_MultiplyWinogradMemory" );
DeclareGlobalFunction( "CVEC_ValueLaurentPoly" );

#############################################################################
# Stuff for other packages:
#############################################################################

DeclareOperation( "ScalarProductsRows",
  [ IsMatrixObj, IsMatrixObj, IsPosInt ] );

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
