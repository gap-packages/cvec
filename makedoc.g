##  this creates the documentation, needs: GAPDoc package, latex, pdflatex,
##  mkindex, dvips
##  
##  Call this with GAP.
##  

PACKAGE := "cvec";
SetPackagePath(PACKAGE, ".");
PrintTo("VERSION", PackageInfo(PACKAGE)[1].Version);

LoadPackage("GAPDoc");
LoadPackage("IO");
LoadPackage("orb");

if fail <> LoadPackage("AutoDoc", ">= 2014.03.27") then
    AutoDoc(PACKAGE : scaffold := rec( MainPage := false ));
else
    MakeGAPDocDoc("doc", PACKAGE, [], PACKAGE, "MathJax");
    CopyHTMLStyleFiles("doc");
    GAPDocManualLab(PACKAGE);
fi;

QUIT;
