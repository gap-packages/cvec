# This file tests the characteristic and minimal polynomial functions:

LoadPackage("cvec");

f := GF(5);
z := Zero(f);
o := One(f);
two := o+o;
three := o+o+o;
x := X(f);

SetInfoLevel(InfoCVec,2);

tester := function(m)
  local c,cm,cp,mc,mi,mm,mp;
  mm := Unpack(m);
  ConvertToMatrixRep(mm);
  c := CharacteristicPolynomial(mm);
  mi := MinimalPolynomial(BaseDomain(m),mm);
  cp := CharacteristicPolynomialOfMatrix(m);
  mp := CVEC_MinimalPolynomial(m);
  cm := CharAndMinimalPolynomialOfMatrix(m);
  if c <> cp.poly then
      Error("CharacteristicPolynomialOfMatrix is wrong");
  fi;
  if c <> cm.charpoly then
      Error("CharAndMinimalPolynomialOfMatrix is wrong in charpoly");
  fi;
  if mi <> cm.minpoly then
      Error("CharAndMinimalPolynomialOfMatrix is wrong in minpoly");
  fi;
  Print("\n\nAll OK.\n\n");
end;

Print("Testing one Block of size 10 with polynomial x-1...\n");
m := CVEC_MakeExample(f,[x-o],[[10]]);
tester(m);

Print("Testing blocks of sizes [1,5,10] with polynomial x-1...\n");
m := CVEC_MakeExample(f,[x-o],[[1,5,10]]);
tester(m);

Print("Testing two different blocks of sizes [1,2,3,4,5] with polynomials ",
      "x-1 and x-2...\n");
m := CVEC_MakeExample(f,[x-o,x-two],[[1,2,3,4,5],[5,4,3,2,1]]);
tester(m);

Print("Testing with a polynomial of larger degree:\n");
Print("Testing blocks of sizes [1,10,20] with polynomial x^2+2x+3:\n");
m := CVEC_MakeExample(f,[x^2+two*x+three],[[1,10,20]]);
tester(m);

Print("Testing a larger example:\n");
Print("Testing blocks of sizes [1,3] for cyclotomic(97) and sizes [1,100] ",
      "for x-1:\n");
SetInfoLevel(InfoCVec,1);
m := CVEC_MakeExample(f,[CyclotomicPolynomial(f,97),x-o],[[1,3],[1,100]]);
tester(m);

