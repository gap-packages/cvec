#
# EmptySemiEchelonBasis
#
gap> id:=IdentityMat(3,Z(3)^0);;
gap> ConvertToMatrixRep(id);
3
gap> c:=CMat(id);
<cmat 3x3 over GF(3,1)>
gap> EmptySemiEchelonBasis(c);
<semi echelonized basis over GF(3) of length 0>
gap> EmptySemiEchelonBasis(c[1]);
<semi echelonized basis over GF(3) of length 0>

