gap> f := GF(5);;
gap> z := Zero(f);;
gap> o := One(f);;
gap> two := o+o;;
gap> three := o+o+o;;
gap> x := X(f);;


gap> m := CVEC_MakeExample(f,[x-o],[[10]]);
<cmat 10x10 over GF(5,1)>
gap> mm := Unpack(m);;
gap> ConvertToMatrixRep(mm);
5
gap> c := CharacteristicPolynomial(mm);;
gap> cp := CharacteristicPolynomialOfMatrix(m);;
gap> c = cp.poly;
true
gap> mi := MinimalPolynomial(BaseDomain(m),mm);;
gap> mp := CVEC_MinimalPolynomial(m);;
gap> mi = mp;
true
gap> cm := CharAndMinimalPolynomialOfMatrix(m);;
gap> c = cm.charpoly;
true
gap> mi = cm.minpoly;
true


gap> m := CVEC_MakeExample(f,[x-o],[[1,5,10]]);
<cmat 16x16 over GF(5,1)>
gap> mm := Unpack(m);;
gap> ConvertToMatrixRep(mm);
5
gap> c := CharacteristicPolynomial(mm);;
gap> cp := CharacteristicPolynomialOfMatrix(m);;
gap> c = cp.poly;
true
gap> mi := MinimalPolynomial(BaseDomain(m),mm);;
gap> mp := CVEC_MinimalPolynomial(m);;
gap> mi = mp;
true
gap> cm := CharAndMinimalPolynomialOfMatrix(m);;
gap> c = cm.charpoly;
true
gap> mi = cm.minpoly;
true


gap> m := CVEC_MakeExample(f,[x-o,x-two],[[1,2,3,4,5],[5,4,3,2,1]]);
<cmat 30x30 over GF(5,1)>
gap> mm := Unpack(m);;
gap> ConvertToMatrixRep(mm);
5
gap> c := CharacteristicPolynomial(mm);;
gap> cp := CharacteristicPolynomialOfMatrix(m);;
gap> c = cp.poly;
true
gap> mi := MinimalPolynomial(BaseDomain(m),mm);;
gap> mp := CVEC_MinimalPolynomial(m);;
gap> mi = mp;
true
gap> cm := CharAndMinimalPolynomialOfMatrix(m);;
gap> c = cm.charpoly;
true
gap> mi = cm.minpoly;
true


gap> m := CVEC_MakeExample(f,[x^2+two*x+three],[[1,10,20]]);
<cmat 62x62 over GF(5,1)>
gap> mm := Unpack(m);;
gap> ConvertToMatrixRep(mm);
5
gap> c := CharacteristicPolynomial(mm);;
gap> cp := CharacteristicPolynomialOfMatrix(m);;
gap> c = cp.poly;
true
gap> mi := MinimalPolynomial(BaseDomain(m),mm);;
gap> mp := CVEC_MinimalPolynomial(m);;
gap> mi = mp;
true
gap> cm := CharAndMinimalPolynomialOfMatrix(m);;
gap> c = cm.charpoly;
true
gap> mi = cm.minpoly;
true


gap> m := CVEC_MakeExample(f,[CyclotomicPolynomial(f,97),x-o],[[1,3],[1,100]]);
<cmat 485x485 over GF(5,1)>
gap> mm := Unpack(m);;
gap> ConvertToMatrixRep(mm);
5
gap> c := CharacteristicPolynomial(mm);;
gap> cp := CharacteristicPolynomialOfMatrix(m);;
gap> c = cp.poly;
true
gap> mi := MinimalPolynomial(BaseDomain(m),mm);;
gap> mp := CVEC_MinimalPolynomial(m);;
gap> mi = mp;
true
gap> cm := CharAndMinimalPolynomialOfMatrix(m);;
gap> c = cm.charpoly;
true
gap> mi = cm.minpoly;
true
