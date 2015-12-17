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
