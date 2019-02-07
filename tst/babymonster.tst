#
gap> START_TEST("babymonster.tst");

# big matrix from Neunhöffer/Praeger article
gap> LoadPackage("AtlasRep", false);
true
gap> g := AtlasGroup("B",1);;
gap> m := (g.1+g.2+g.1*g.2);
<an immutable 4370x4370 matrix over GF2>
gap> cm := CMat(m);
<cmat 4370x4370 over GF(2,1)>
gap> mp := MinimalPolynomialOfMatrixMC(m, 1/100).minpoly;;
gap> Degree(mp);
2097
gap> mp := MinimalPolynomialOfMatrixMC(m, 0).minpoly;;
gap> Degree(mp);
2097
gap> cmp := MinimalPolynomialOfMatrixMC(cm, 0).minpoly;;
gap> Degree(cmp);
2097
gap> mp = cmp;
true

#
gap> STOP_TEST("babymonster.tst", 0);
