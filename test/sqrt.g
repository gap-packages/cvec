SqrtFinField := function(x,z,q)
  local T,c,e,i,k,me,mu,s,sigma,t,tau,xl,xs,xsm1d2,xsp1d2,y;
  e := One(x);
  me := -e;
  s := q-1;
  T := -1;
  while IsEvenInt(s) do
      s := s / 2;
      T := T + 1;
  od;
  Print("T=",T,"\n");
  Print("s=",s,"\n");
  c := [z^s];
  for i in [1..T] do Add(c,c[i]^2); od;
  Print(c,"\n");
  xsm1d2 := x^((s-1)/2);
  Print("x^((s-1)/2)",xsm1d2,"\n");
  xsp1d2 := xsm1d2*x;
  Print("x^((s+1)/2)",xsp1d2,"\n");
  xs := xsm1d2*xsp1d2;
  Print("x^s=",xs,"\n");
  if xs = e then return xsp1d2; fi;
  xl := [xs];
  y := xs;
  t := 0;
  while y <> me do
      y := y^2;
      Add(xl,y);
      t := t + 1;
  od;
  if t = T then return fail; fi;
  tau := [T-1];
  mu := 1;
  for k in [1..t] do
      sigma := xl[t-k+1];
      for i in [0..mu-1] do
          sigma := sigma * c[tau[i+1]+1];
      od;
      Print("sigma=",sigma,"\n");
      tau := tau - 1;   # increase all tau values
      if sigma = me then
          Add(tau,T-1);
          mu := mu + 1;
      fi;
  od;
  sigma := xsp1d2;
  for i in [0..mu-1] do
      sigma := sigma * c[tau[i+1]+1];
  od;
  return sigma;
end;

