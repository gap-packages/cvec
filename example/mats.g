# Some example matrices for testing:
m := CMat([CVec([1,2,3,4],5,3),CVec([4,3,2,1],5,3),CVec([1,1,1,1],5,3)]);
n := CMat([CVec([1,1,1,2,2,2,3,3,3,4,4,4],1031,3),
           CVec([4,4,4,3,3,3,2,2,2,1,1,1],1031,3),
           CVec([1,1,1,1,1,1,1,1,1,1,1,1],1031,3)]);
mm := m+m;
nn := n+n;
gens := AtlasGenerators("Fi22",6);
m1 := CVEC.MatToCMat(gens.generators[1],2,1);
m2 := CVEC.MatToCMat(gens.generators[2],2,1);

l := [];
for i in [1..100] do
    ll := List([1..100],x->Random(GF(2)));
    Add(l,ll);
od;

m2old := List(l,ShallowCopy);
ConvertToMatrixRep(m2old,2);
m2 := CMat(List(l,v->CVec(v,2,1)));

l := [];
for i in [1..150] do
    ll := List([1..150],x->Random(GF(3)));
    Add(l,ll);
od;

m3old := List(l,ShallowCopy);
ConvertToMatrixRep(m3old,3);
m3 := CMat(List(l,v->CVec(v,3,1)));

