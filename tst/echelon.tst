#
# EmptySemiEchelonBasis
#
gap> id:=IdentityMat(3,Z(3)^0);;
gap> ConvertToMatrixRep(id);
3
gap> c:=CMat(id);
<cmat 3x3 over GF(3,1)>
gap> EmptySemiEchelonBasis(c);
<empty semi echelonized basis>
gap> EmptySemiEchelonBasis(c[1]);
<empty semi echelonized basis>
gap> EmptySemiEchelonBasis(id);
<empty semi echelonized basis>
