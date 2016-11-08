gap> m2 := [ 0 * Z(2), Z(2)^0 ];
[ 0*Z(2), Z(2)^0 ]
gap> m4 := [ 0 * Z(4), Z(4)^0 ];
[ 0*Z(2), Z(2)^0 ]
gap> m8 := [ 0 * Z(8), Z(8)^0 ];
[ 0*Z(2), Z(2)^0 ]
gap> m16 := [ 0 * Z(16), Z(16)^0 ];
[ 0*Z(2), Z(2)^0 ]
gap> m2 = m4;
true
gap> m2 = m8;
true
gap> m2 = m16;
true

#
gap> c := CVEC_NewCVecClass(2, 1, 2);
<cvec-class field=GF(2,1) len=2 wordlen=1>
gap> CVec(m2, c);
<cvec over GF(2,1) of length 2>
gap> CVec(m4, c);
<cvec over GF(2,1) of length 2>
gap> CVec(m8, c);
<cvec over GF(2,1) of length 2>
gap> CVec(m16, c);
<cvec over GF(2,1) of length 2>

#
gap> c := CVEC_NewCVecClass(2, 2, 2);
<cvec-class field=GF(2,2) len=2 wordlen=2>
gap> CVec(m2, c);
<cvec over GF(2,2) of length 2>
gap> CVec(m4, c);
<cvec over GF(2,2) of length 2>
gap> CVec(m8, c);
<cvec over GF(2,2) of length 2>
gap> CVec(m16, c);
<cvec over GF(2,2) of length 2>

#
gap> c := CVEC_NewCVecClass(2, 3, 2);
<cvec-class field=GF(2,3) len=2 wordlen=3>
gap> CVec(m2, c);
<cvec over GF(2,3) of length 2>
gap> CVec(m4, c);
<cvec over GF(2,3) of length 2>
gap> CVec(m8, c);
<cvec over GF(2,3) of length 2>
gap> CVec(m16, c);
<cvec over GF(2,3) of length 2>

#
gap> c := CVEC_NewCVecClass(2, 4, 2);
<cvec-class field=GF(2,4) len=2 wordlen=4>
gap> CVec(m2, c);
<cvec over GF(2,4) of length 2>
gap> CVec(m4, c);
<cvec over GF(2,4) of length 2>
gap> CVec(m8, c);
<cvec over GF(2,4) of length 2>
gap> CVec(m16, c);
<cvec over GF(2,4) of length 2>

#
# The following test is motivated by issue #5
#
gap> mat := [[0,1],[3,1]]*Z(5)^0;;
gap> basis := Basis(AsVectorSpace(GF(5),GF(5^2)));;
gap> omega := Z(5^2);;
gap> mat2 := List(BasisVectors(basis), t -> Coefficients(basis, t*omega));;
gap> mat = mat2;
true
gap> cmat := NewMatrix(IsCMatRep,GF(5),Length(mat[1]),mat);
<cmat 2x2 over GF(5,1)>
gap> cmat2 := NewMatrix(IsCMatRep,GF(5),Length(mat2[1]),mat2);
<cmat 2x2 over GF(5,1)>
gap> cmat = cmat2;
true
