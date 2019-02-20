# Test functions defined in cmat.gi
gap> START_TEST("cmat.tst");

#
gap> NewIdentityMatrix(IsCMatRep, GF(3), 0);
<cmat 0x0 over GF(3,1)>
gap> NewIdentityMatrix(IsCMatRep, GF(3), 3);
<cmat 3x3 over GF(3,1)>

#
gap> NewZeroMatrix(IsCMatRep, GF(3), 0, 0);
<cmat 0x0 over GF(3,1)>
gap> NewZeroMatrix(IsCMatRep, GF(3), 0, 3);
<cmat 0x3 over GF(3,1)>
gap> NewZeroMatrix(IsCMatRep, GF(3), 3, 0);
<cmat 3x0 over GF(3,1)>
gap> NewZeroMatrix(IsCMatRep, GF(3), 3, 2);
<cmat 3x2 over GF(3,1)>

#
gap> m:=CMat(ImmutableMatrix(GF(3),[[1,0],[0,1]]*Z(3)));
<cmat 2x2 over GF(3,1)>
gap> ScalarProductsRows(m,m,1);
Z(3)^0
gap> ScalarProductsRows(m,m,2);
Z(3)

#
gap> STOP_TEST("cmat.tst", 0);
