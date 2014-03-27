##  this creates the documentation, needs: GAPDoc package, latex, pdflatex,
##  mkindex, dvips
##  
##  Call this with GAP.
##  

SetPackagePath("cvec", ".");
PrintTo("VERSION", PackageInfo("cvec")[1].Version);

LoadPackage("GAPDoc");
LoadPackage("IO");
LoadPackage("orb");

MakeGAPDocDoc("doc", "cvec", [], "cvec");
CopyHTMLStyleFiles("doc");
GAPDocManualLab("cvec");

QUIT;
