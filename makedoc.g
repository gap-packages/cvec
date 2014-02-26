##  this creates the documentation, needs: GAPDoc package, latex, pdflatex,
##  mkindex, dvips
##  
##  Call this with GAP.
##  

LoadPackage("GAPDoc");
LoadPackage("IO");
LoadPackage("orb");

MakeGAPDocDoc("doc", "cvec", [], "cvec");

CopyHTMLStyleFiles("doc");

GAPDocManualLab("cvec");

QUIT;
