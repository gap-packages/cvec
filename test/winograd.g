AddMat := function(a,b,mult)
  local i;
  for i in [1..Length(a)] do
      AddRowVector(a[i],b[i],mult);
  od;
end;

MultiplyWinograd := function(M,N,R,limit)
  # Call with square matrices M and N of equal dimensions. R must
  # be either a matrix of the same dimensions or false. limit is an
  # integer. Does M*N. If R=false, a new matrix with the result is
  # returned. Otherwise the result is written to R. For matrices smaller
  # or equal to limit the standard matrix multiplication is used,
  # otherwise the Winograd trick is done. It is allowed, that R is
  # equal to M or N!
  local bz,brz,hi,hilo,l,l2,lo,mo,ne,nw,o,odd,rz,se,sw,x,y,ze;
  if Length(M) <= limit then
      if R = false then 
          return M*N; 
      else
          l := [1..Length(M)];
          CopySubMatrix(M*N,R,l,l,l,l);
          return R;
      fi;
  fi;
  # From now on we have a result matrix:
  l := Length(M);
  l2 := QuoInt(l+1,2);
  lo := [1..l2];
  hi := [l2+1..l];
  odd := IsOddInt(Length(M));
  if odd then
      hilo := [1..l2-1];
  else
      hilo := [1..l2];
  fi;
  o := One(BaseDomain(M));
  mo := -o;
  ze := Zero(BaseDomain(M));

  # We want to compute:
  # [[a,b],  *  [[A,C],  by doing: w := aA-(a-c-d)(A-C+D)
  #  [c,d]]      [B,D]]
  # and then:
  # [[aA+bB,                    w+(c+d)(C-A)+(a+b-c-d)D ],
  #  [w+(a-c)(D-C)-d(A-B-C+D),  w+(a-c)(D-C)+(c+d)(C-A)]],

  # Start by computing aA:
  x := ExtractSubMatrix(M,lo,lo);        # fetch a
  y := ExtractSubMatrix(N,lo,lo);        # fetch A
  nw := MultiplyWinograd(x,y,false,limit);
  # x is a and y is A, they can be used again, nw is aA

  # Compute w = aA - (a-c-d)(A-C+D) in sw:
  sw := MutableCopyMat(nw);
  rz := ZeroMutable(x);   # the rightmost column of this matrix will stay = 0
  bz := ZeroMutable(x);   # the downmost row of this matrix will stay = 0
  brz := ZeroMutable(x);  # the rightmost column and downmost will stay = 0
  CopySubMatrix(N,rz,lo,lo,hi,hilo);     # fetch C
  AddMat(y,rz,mo);                       # now y is A-C
  CopySubMatrix(M,bz,hi,hilo,lo,lo);     # fetch c
  AddMat(x,bz,mo);                       # now x is a-c
  CopySubMatrix(N,brz,hi,hilo,hi,hilo);  # fetch D
  AddMat(y,brz,o);                       # now y is A-C+D
  CopySubMatrix(M,brz,hi,hilo,hi,hilo);  # fetch d
  AddMat(x,brz,mo);                      # now x is a-c-d
  # Now x = a-c-d and y = A-C+D, bz is still c and brz is still d
  MultiplyWinograd(x,y,x,limit);         # now x is (a-c-d)(A-C+D)
  AddMat(sw,x,mo);                       # now sw = w
  # Now sw is w, x, y, bz, and brz can be used again
  
  # Compute (c+d)(C-A):
  # use: bz is still c and brz is still d
  CopySubMatrix(bz,x,lo,lo,lo,lo);   # move c to x
  AddMat(x,brz,o);                   # now x is c+d, bz again usable
  CopySubMatrix(N,y,lo,lo,lo,lo);    # fetch A
  CopySubMatrix(N,rz,lo,lo,hi,hilo); # fetch C
  AddMat(y,rz,mo);                   # now y is A-C
  MultiplyWinograd(x,y,x,limit);     # now x is (c+d)(A-C)
  ne := sw-x;                        # now ne contains w+(c+d)(C-A)
  se := MutableCopyMat(ne);          # now se contains w+(c+d)(C-A)
  # x, y again usable
  
  # Compute (a-c)(D-C):
  CopySubMatrix(M,x,lo,lo,lo,lo);    # fetch a
  CopySubMatrix(M,bz,hi,hilo,lo,lo); # fetch c
  AddMat(x,bz,mo);                   # now x is a-c
  CopySubMatrix(N,rz,lo,lo,hi,hilo);  # fetch C
  CopySubMatrix(N,brz,hi,hilo,hi,hilo);  # fetch D
  AddMat(rz,brz,mo);                 # now rz is C-D
  MultiplyWinograd(x,rz,x,limit);    # now x is (a-c)(C-D)
  AddMat(sw,x,mo);                   # now sw is w+(a-c)(D-C)
  AddMat(se,x,mo);                   # now se is w+(c+d)(C-A)+(a-c)(D-C) ready

  # Compute d(A-B-C+D):
  CopySubMatrix(N,y,lo,lo,lo,lo);    # Fetch A
  CopySubMatrix(N,bz,hi,hilo,lo,lo); # Fetch B
  AddMat(y,bz,mo);                   # now y is A-B
  CopySubMatrix(N,rz,lo,lo,hi,hilo); # Fetch C
  AddMat(y,rz,mo);                   # now y is A-B-C
  CopySubMatrix(N,brz,hi,hilo,hi,hilo);  # Fetch D
  AddMat(y,brz,o);                       # now y is A-B-C+D
  CopySubMatrix(M,brz,hi,hilo,hi,hilo);  # Fetch d
  MultiplyWinograd(brz,y,x,limit);   # now x is d(A-B-C+D)
  AddMat(sw,x,mo);                   # now sw is w+(a-c)(D-C)-d(A-B-C+D) ready

  # Compute (a+b-c-d)D:
  # use: brz is still d
  CopySubMatrix(M,x,lo,lo,lo,lo);    # fetch a
  AddMat(x,brz,mo);                  # now x is a-d
  CopySubMatrix(M,rz,lo,lo,hi,hilo); # fetch b
  AddMat(x,rz,o);                    # now x is a+b-d
  CopySubMatrix(M,bz,hi,hilo,lo,lo); # fetch c
  AddMat(x,bz,mo);                   # now x is a+b-c-d
  CopySubMatrix(N,brz,hi,hilo,hi,hilo);  # fetch D
  MultiplyWinograd(x,brz,x,limit);   # now x is (a+b-c-d)D
  AddMat(ne,x,o);                    # now ne is w+(c+d)(C-A)+(a+b-c-d)D ready

  # Compute bB:
  # use: rz is still b
  CopySubMatrix(N,bz,hi,hilo,lo,lo); # fetch B
  MultiplyWinograd(rz,bz,x,limit);   # now x is bB
  AddMat(nw,x,o);                    # now nw is aA+bB ready

  # Now put everything together:
  Unbind(x);
  Unbind(y);
  Unbind(rz);
  Unbind(bz);
  Unbind(brz);

  # Create a new result matrix if necessary:
  if R = false then
      R := ZeroMutable(M);
  fi;
  
  CopySubMatrix(nw,R,lo,lo,lo,lo);
  CopySubMatrix(ne,R,lo,lo,hilo,hi);
  CopySubMatrix(sw,R,hilo,hi,lo,lo);
  CopySubMatrix(se,R,hilo,hi,hilo,hi);

  return R;
end;

# fetches:
# a xxx
# b x
# c xxx
# d xx
# A xxx
# B xx
# C xxxx
# D xxxx

# Additions: xxxxxxxxxxxxxxxxxxx
# Copies: xx

MultiplyWinograd2 := function(M,N,R,limit)
  # Call with square matrices M and N of equal dimensions. R must
  # be either a matrix of the same dimensions or false. limit is an
  # integer. Does M*N. If R=false, a new matrix with the result is
  # returned. Otherwise the result is written to R. For matrices smaller
  # or equal to limit the standard matrix multiplication is used,
  # otherwise the Winograd trick is done. It is allowed, that R is
  # equal to M or N!
  local a11,a12,a21,a22,b11,b12,b21,b22,hi,hilo,l,l2,lo,m1,m2,m3,m4,m5,m6,m7,
        mo,o,s1,s2,s3,s4,s5,s6,s7,s8,t1,t2,ze,t;
  if Length(M) <= limit then
      if R = false then 
          return M*N; 
      else
          l := [1..Length(M)];
          CopySubMatrix(M*N,R,l,l,l,l);
          return R;
      fi;
  fi;
  t := Runtime();
  # From now on we have a result matrix:
  l := Length(M);
  l2 := QuoInt(l+1,2);
  lo := [1..l2];
  hi := [l2+1..l];
  if IsOddInt(Length(M)) then
      hilo := [1..l2-1];
  else
      hilo := [1..l2];
  fi;
  o := One(BaseDomain(M));
  mo := -o;
  ze := Zero(BaseDomain(M));

  a11 := ExtractSubMatrix(M,lo,lo);
  a21 := ZeroMutable(a11);
  CopySubMatrix(M,a21,hi,hilo,lo,lo);
  a22 := ZeroMutable(a11);
  CopySubMatrix(M,a22,hi,hilo,hi,hilo);
  s1 := a21+a22;
  s2 := s1-a11;
  s3 := a11-a21;
  a12 := ZeroMutable(a11);
  CopySubMatrix(M,a12,lo,lo,hi,hilo);
  s4 := a12-s2;
  b11 := ExtractSubMatrix(N,lo,lo);
  b12 := ZeroMutable(a11);
  CopySubMatrix(N,b12,lo,lo,hi,hilo);
  s5 := b12-b11;
  b22 := ZeroMutable(a11);
  CopySubMatrix(N,b22,hi,hilo,hi,hilo);
  s6 := b22-s5;
  s7 := b22-b12;
  b21 := ZeroMutable(a11);
  CopySubMatrix(N,b21,hi,hilo,lo,lo);
  s8 := s6-b21;
  #Print(Runtime()-t,"\n"); t := Runtime();

  # To save allocations:
  Unbind(a21);
  Unbind(b12);

  # Now the multiplications:
  m1 := MultiplyWinograd2(s2,s6,false,limit);
  #Print(Runtime()-t,"\n"); t := Runtime();
  m2 := MultiplyWinograd2(a11,b11,false,limit);
  #Print(Runtime()-t,"\n"); t := Runtime();
  m3 := MultiplyWinograd2(a12,b21,false,limit);
  #Print(Runtime()-t,"\n"); t := Runtime();
  m4 := MultiplyWinograd2(s3,s7,false,limit);
  #Print(Runtime()-t,"\n"); t := Runtime();
  m5 := MultiplyWinograd2(s1,s5,false,limit);
  #Print(Runtime()-t,"\n"); t := Runtime();
  m6 := MultiplyWinograd2(s4,b22,false,limit);
  #Print(Runtime()-t,"\n"); t := Runtime();
  m7 := MultiplyWinograd2(a22,s8,false,limit);
  #Print(Runtime()-t,"\n"); t := Runtime();

  Unbind(s1); Unbind(s2); Unbind(s3); Unbind(s4);
  Unbind(s5); Unbind(s6); Unbind(s7); Unbind(s8);

  t1 := m1;
  AddMat(t1,m2,o);
  t2 := m4;
  AddMat(t2,t1,o);
  #Print(Runtime()-t,"\n"); t := Runtime();
  
  Unbind(m1);

  # Create a new result matrix if necessary:
  if R = false then
      R := ZeroMutable(M);
  fi;

  # Put together the result:
  AddMat(m2,m3,o);
  CopySubMatrix(m2,R,lo,lo,lo,lo);
  AddMat(t1,m5,o);
  AddMat(t1,m6,o);
  CopySubMatrix(t1,R,lo,lo,hilo,hi);
  CopySubMatrix(t2-m7,R,hilo,hi,lo,lo);
  AddMat(t2,m5,o);
  CopySubMatrix(t2,R,hilo,hi,hilo,hi);
  #Print(Runtime()-t,"\n"); t := Runtime();

  return R;
end;

