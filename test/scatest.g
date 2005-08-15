TestScalars := function(p,d,z1,z2)
  # z1 and z2 should be primitive roots of GF(p,d) to be compared
  # We want to ask them for their Zero and One.
  local a,a1,a2,ae,b,b1,b2,be,f,i,qmo,ra,reps,ti,ti2;
  qmo := p^d-1;
  
  # First make two random elements:
  ae := Random(1,qmo);
  a1 := z1^ae;
  a2 := z2^ae;
  be := Random(1,qmo);
  b1 := z1^be;
  b2 := z2^be;

  reps := 1000000;
  
  Print("Benchmarking scalars, p=",p," d=",d,"...\n\n");

  Print("Benchmarking addition (",reps," repetitions) ...\n");
  SetGasmanMessageStatus("none");
  GASMAN("collect");
  SetGasmanMessageStatus("all");
  ti := Runtime();
  for i in [1..reps] do
      a := a1+b1;
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#1: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  GASMAN("collect");
  SetGasmanMessageStatus("all");
  ti := Runtime();
  for i in [1..reps] do
      b := a2+b2;
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#2: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  Print("Benchmarking addition without method selection (",
        reps," repetitions) ...\n");
  GASMAN("collect");
  SetGasmanMessageStatus("all");
  f := ApplicableMethod(\+,[a1,b1]);
  ti := Runtime();
  for i in [1..reps] do
      a := f(a1,b1);
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#1: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  GASMAN("collect");
  SetGasmanMessageStatus("all");
  f := ApplicableMethod(\+,[a2,b2]);
  ti := Runtime();
  for i in [1..reps] do
      b := f(a2,b2);
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#2: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  Print("Benchmarking subtraction (",reps," repetitions) ...\n");
  GASMAN("collect");
  SetGasmanMessageStatus("all");
  ti := Runtime();
  for i in [1..reps] do
      a := a1-b1;
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#1: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  GASMAN("collect");
  SetGasmanMessageStatus("all");
  ti := Runtime();
  for i in [1..reps] do
      b := a2-b2;
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#2: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  Print("Benchmarking multiplication (",reps," repetitions) ...\n");
  GASMAN("collect");
  SetGasmanMessageStatus("all");
  ti := Runtime();
  for i in [1..reps] do
      a := a1*b1;
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#1: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  GASMAN("collect");
  SetGasmanMessageStatus("all");
  ti := Runtime();
  for i in [1..reps] do
      b := a2*b2;
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#2: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  GASMAN("collect");
  SetGasmanMessageStatus("all");
  reps := 100000;
  Print("Benchmarking division (",reps," repetitions) ...\n");
  ti := Runtime();
  for i in [1..reps] do
      a := a1/b1;
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#1: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  GASMAN("collect");
  SetGasmanMessageStatus("all");
  ti := Runtime();
  for i in [1..reps] do
      b := a2/b2;
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#2: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  GASMAN("collect");
  SetGasmanMessageStatus("all");
  reps := 1000000;
  Print("Benchmarking negation (",reps," repetitions) ...\n");
  ti := Runtime();
  for i in [1..reps] do
      a := -a1;
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#1: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  GASMAN("collect");
  SetGasmanMessageStatus("all");
  ti := Runtime();
  for i in [1..reps] do
      b := -a2;
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#2: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  GASMAN("collect");
  SetGasmanMessageStatus("all");
  reps := 100000;
  Print("Benchmarking inversion (",reps," repetitions) ...\n");
  ti := Runtime();
  for i in [1..reps] do
      a := a1^-1;
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#1: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  GASMAN("collect");
  SetGasmanMessageStatus("all");
  ti := Runtime();
  for i in [1..reps] do
      b := a2^-1;
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#2: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  GASMAN("collect");
  SetGasmanMessageStatus("all");
  Print("Benchmarking comparison (=) (",reps," repetitions) ...\n");
  ti := Runtime();
  for i in [1..reps] do
      a := a1=b1;
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#1: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");

  GASMAN("collect");
  SetGasmanMessageStatus("all");
  ti := Runtime();
  for i in [1..reps] do
      b := a2=b2;
  od;
  ti2 := Runtime();
  SetGasmanMessageStatus("none");
  Print("#2: ",ti2-ti," ms ==> ",FLOAT_INT((ti2-ti)*1000)/FLOAT_INT(reps),
        " us/op.\n");
end;
