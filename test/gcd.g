gcd := function(x,y)
  local a,b,c,q,r;
  a := 0;   # was: [1,0];
  b := 1;   # was: [0,1];
  repeat
    Print("x=",x," y=",y," a=",a," b=",b,"\n");
    r := x mod y;
    Print("r=",r,"\n");
    if r = 0 then
        return [y,a,b];
    fi;
    q := (x-r)/y;
    Print("q=",q,"\n");
    x := y;
    y := r;
    c := a-q*b;
    a := b;
    b := c;
  until false;
end;
