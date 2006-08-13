#############################################################################
##
#A  init.g               cvec-package                         Max Neunhoeffer
##
##
#Y  Copyright (C) 2005  Lehrstuhl D f\"ur Mathematik, RWTH Aachen
##  
##  Initialization of the cvec package
##  

if not(IsBound(IsMatrixObj)) then
    ReadPackage("cvec", "gap/matobj.gd");
fi;

ReadPackage("cvec", "gap/cvec.gd");
ReadPackage("cvec", "gap/cmat.gd");
ReadPackage("cvec", "gap/linalg.gd");
ReadPackage("cvec", "gap/matrix.gd");
