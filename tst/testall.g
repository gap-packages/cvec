LoadPackage("cvec");
# skip babymonster.tst by default because it requires downloading ~40 MB
# of matrix data; and this is broken in GAP 4.10's version of AtlasRep
TestDirectory(DirectoriesPackageLibrary("cvec", "tst"),
    rec(exclude := ["babymonster.tst"], exitGAP := true));
FORCE_QUIT_GAP(1);
