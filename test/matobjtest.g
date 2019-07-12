RowListMatrixObjTester := function( m, level )
  local MyError,a,bd,dims,errors,i,j,k,l,n,nn,one,s,three,two,u,v,vv,w,wi,wit,
        wt,z,zero,vi,filter,pol,vvv,vvv2;
  
  MyError := function(nr)
    Print("ERROR: Number ",nr," see code of RowListMatrixObjTester!\n\n");
    Add(errors,nr);
  end;

  errors := [];

  Print("Testing matrix/vector interface...\n\n");

  if not(IsMatrixObj(m)) then
      Print("Warning, matrix is not in IsMatrixObj, ");
      Print("let's see what it can do...\n");
  fi;
  
  # Prepare things:
  bd := BaseDomain(m);
  zero := Zero(bd);
  one := One(bd);
  two := one+one;
  three := two+one;

  # Let's first look at its attributes:
  dims := DimensionsMat(m);
  if dims[1] <> NumberRows(m) then MyError(1); fi;
  if dims[2] <> NumberColumns(m) then MyError(2); fi;

  # We do not like too small matrices here:
  if dims[1] < 2 or dims[2] < 2 then
      Print("Please give me a matrix of dimensions at least 2x2!\n");
      return;
  fi;

  # Now first consider the vectors:
  v := m[1];
  if not(IsVectorObj(v)) then
      Print("Warning, corresp. vectors are not in IsVectorObj,\n");
      Print("let's see what they can do...\n");
  fi;

  # Test attributes:
  l := Length(v);
  if not(IsIdenticalObj(BaseDomain(v),bd)) then MyError(3); fi;
  if Characteristic(v) <> Characteristic(BaseDomain(v)) then MyError(7/2); fi;

  # Element access:
  s := 0;
  for i in [1..l] do
      s := s + v[i];
  od;

  # Make a shallow copy:
  w := ShallowCopy(v);
  if not(IsVectorObj(w)) then
      Print("Warning, ShallowCopy of vectors are not in IsVectorObj.\n");
  fi;

  # Is it a copy?
  w[1] := w[1] + one;
  if w[1] = v[1] then MyError(4); fi;

  # Write access:
  for i in [1..l] do
      w[i] := one;
  od;

  # Slicing:
  u := w{[1]};
  if not(IsVectorObj(u)) then
      Print("Warning, slices of vectors are not in IsVectorObj\n");
  fi;

  # PositionNonZero:
  w[1] := zero;
  w[2] := one;
  if PositionNonZero(w) <> 2 then MyError(5); fi;

  # PositionLastNonZero:
  w[l] := zero;
  w[l-1] := one;
  #if PositionLastNonZero(w) <> l-1 then MyError(6); fi;

  # The List command:
  w := List(v);
  if not(IsList(w)) then MyError(7); fi;
  for i in [1..l] do
      if w[i] <> v[i] then MyError(8); fi;
  od;

  # The List command with function:
  w := List(v,x->x*two);
  if not(IsList(w)) then MyError(9); fi;
  for i in [1..l] do
      if w[i] <> v[i] * two then MyError(10); fi;
  od;

  # StructuralCopy:
  w := StructuralCopy(v);

  # Viewing and printing of vectors:
  w := v{[1..2]};
  Print("A vector is printed as follows:\n",w,"\n\n");
  Print("ViewObj does the following to it:\n");
  ViewObj(w);
  Print("\n\n");
  Print("String gives the following:\n",String(w),"\n\n");
  Print("Display does this:\n");
  Display(w);
  Print("\n");

  # Make an immutable copy:
  w := ShallowCopy(v);
  wi := ShallowCopy(w);
  MakeImmutable(wi);
  if not(IsMutable(w)) then MyError(10); fi;
  if IsMutable(wi) then MyError(11); fi;
  
  # Now we try to do some arithmetic:
  u := w + w;
  for i in [1..l] do if u[i] <> w[i]+w[i] then MyError(12); fi; od;
  if not(IsMutable(u)) then MyError(13); fi;
  u := w + wi;
  if not(IsMutable(u)) then MyError(14); fi;
  u := wi + w;
  if not(IsMutable(u)) then MyError(15); fi;
  u := wi + wi;
  if IsMutable(u) then MyError(16); fi;
  u := w - w;
  if not(IsZero(u)) then MyError(17); fi;
  for i in [1..l] do if u[i] <> w[i]-w[i] then MyError(18); fi; od;
  if not(IsMutable(u)) then MyError(19); fi;
  u := w - wi;
  if not(IsMutable(u)) then MyError(20); fi;
  u := wi - w;
  if not(IsMutable(u)) then MyError(21); fi;
  u := wi - wi;
  if IsMutable(u) then MyError(22); fi;

  # Comparison and scalar multiplication:
  u := w * one;
  if not(u = w) then MyError(23); fi;
  if not(IsMutable(u)) then MyError(24); fi;
  u := wi * one;
  if IsMutable(u) then MyError(25); fi;
  u := one * w;
  if not(u = w) then MyError(26); fi;
  if not(IsMutable(u)) then MyError(27); fi;
  u := one * wi;
  if IsMutable(u) then MyError(28); fi;
  if u < w then MyError(29); fi;

  # Now in place:
  u := ZeroVector(l,w);
  AddRowVector(u,w);
  for i in [1..l] do if u[i] <> w[i] then MyError(30); fi; od;
  AddRowVector(u,w,two);
  for i in [1..l] do if u[i] <> w[i]*three then MyError(31); fi; od;
  AddRowVector(u,w,-two,1,l);
  if u <> w then MyError(32); fi;
  MultVector(u,two);
  for i in [1..l] do if u[i] <> w[i]*two then MyError(33); fi; od;
  MultVector(u,[1,2],w,[2,1],two);
  if u[1] <> w[2]*two or u[2] <> w[1]*two then MyError(34); fi;
  if w/one <> w then MyError(35); fi;

  # AdditiveInverse*:
  a := -w;
  for i in [1..l] do if a[i] <> -w[i] then MyError(36); fi; od;
  u := AdditiveInverseSameMutability(w);
  if a <> u then MyError(37); fi;
  if not(IsMutable(u)) then MyError(38); fi;
  u := AdditiveInverseImmutable(w);
  if a <> u then MyError(38); fi;
  if IsMutable(u) then MyError(39); fi;
  u := AdditiveInverseMutable(w);
  if a <> u then MyError(40); fi;
  if not(IsMutable(u)) then MyError(41); fi;
  u := AdditiveInverseSameMutability(wi);
  if a <> u then MyError(42); fi;
  if IsMutable(u) then MyError(43); fi;
  u := AdditiveInverseImmutable(wi);
  if a <> u then MyError(44); fi;
  if IsMutable(u) then MyError(45); fi;
  u := AdditiveInverseMutable(wi);
  if a <> u then MyError(46); fi;
  if not(IsMutable(u)) then MyError(47); fi;

  # Zero*
  u := ZeroSameMutability(w);
  if not(IsZero(u)) then MyError(48); fi;
  if not(IsMutable(u)) then MyError(49); fi;
  u := ZeroImmutable(w);
  if not(IsZero(u)) then MyError(50); fi;
  if IsMutable(u) then MyError(51); fi;
  u := ZeroMutable(w);
  if not(IsZero(u)) then MyError(52); fi;
  if not(IsMutable(u)) then MyError(53); fi;
  u := ZeroSameMutability(wi);
  if not(IsZero(u)) then MyError(54); fi;
  if IsMutable(u) then MyError(55); fi;
  u := ZeroImmutable(wi);
  if not(IsZero(u)) then MyError(56); fi;
  if IsMutable(u) then MyError(57); fi;
  u := ZeroMutable(wi);
  if not(IsZero(u)) then MyError(58); fi;
  if not(IsMutable(u)) then MyError(59); fi;

  # Constructors:
  z := ZeroVector(10,v);
  if not(IsZero(z)) then MyError(60); fi;
  if not(IsMutable(z)) then MyError(61); fi;
  if not(Length(z) = 10) then MyError(62); fi;
  z := ZeroVector(10,ZeroImmutable(v));
  if not(IsZero(z)) then MyError([60,1]); fi;
  if not(IsMutable(z)) then MyError([61,1]); fi;
  if not(Length(z) = 10) then MyError([62,1]); fi;
  z := Vector([zero,one,zero,one,zero,one,zero,one],z);
  if not(IsMutable(z)) then MyError(63); fi;
  if not(Length(z) = 8) then MyError(64); fi;
  z := Vector([zero,one,zero,one,zero,one,zero,one],ZeroImmutable(z));
  if not(IsMutable(z)) then MyError([63,1]); fi;
  if not(Length(z) = 8) then MyError([64,2]); fi;

  # Randomize:
  Randomize(z);

  # CopySubVector:
  CopySubVector(v,z,[2,1],[1,2]);
  if not(z[1] = v[2] and z[2] = v[1]) then MyError(65); fi;

  Print("Vector test completed.\n\n");

  # Now matrices:

  n := MutableCopyMat(m);
  if not(IsMatrixObj(n)) then
      Print("Warning: MutableCopyMat produces object not in IsMatrixObj!\n");
  fi;

  # Test RowList behaviour:
  v := n[1];
  v[1] := one;
  if n[1,1] <> one then MyError(66); fi;
  v[1] := two;
  if n[1,1] <> two then MyError(67); fi;
  n[1,1] := one;
  if v[1] <> one then MyError(68); fi;

  # Test sharing of rows:
  n[2] := v;
  n[1,2] := one;
  if n[2,2] <> one then MyError(69); fi;
  n[2,1] := two;
  if n[1,1] <> two then MyError(70); fi;
  # Test for identical row objects:
  if not(IsIdenticalObj(n[1],n[1])) then
      Print("Warning: Row objects of same row are not identical!\n");
  fi;
  if not(IsIdenticalObj(n[1],n[2])) then
      Print("Warning: Row objects are not identical!\n");
  fi;

  # PositionNonZero and friends:
  n := Matrix([[zero,zero],[one,two],[zero,zero]],2,m);
  if PositionNonZero(n) <> 2 then MyError(71); fi;
  if PositionNonZero(n,2) <> 4 then MyError(72); fi;
  if PositionLastNonZero(n) <> 2 then MyError(73); fi;
  if PositionLastNonZero(n,2) <> 0 then MyError(74); fi;
  v := Vector([one,two],m[1]);
  if Position(n,v) <> 2 then MyError(75); fi;
  v[2] := one;
  if Position(n,v) <> fail then MyError(76); fi;
  v[2] := two;
  n := Matrix([[one,two],[zero,zero]],2,m);
  if n[1] > n[2] then n := n{[2,1]}; fi;
  if not(n[1] <= n[2]) then MyError(78); fi;
  if PositionSorted(n,v) <> Position(n,v) then MyError(79); fi;
  v[2] := one;
  PositionSorted(n,v); # we cannot know what this will be, it only has to work

  # List operations:
  nn := MutableCopyMat(n);
  Add(n,v);
  if not(NrRows(n) = 3) then MyError(80); fi;
  Add(n,v,1);
  if not(NrRows(n) = 4) then MyError(81); fi;
  if not(IsIdenticalObj(n[1],n[4])) then MyError(82); fi;
  Remove(n,1);
  if not(NrRows(n) = 3) then MyError(83); fi;
  Remove(n);
  if not(NrRows(n) = 2) then MyError(84); fi;
  if not(n = nn) then MyError(85); fi;
  Unbind(n[2]);
  if not(NrRows(n) = 1) then MyError(85); fi;
  if not(n = nn{[1]}) then MyError(86); fi;
  Append(nn,n);
  if not(NrRows(nn) = 3 and nn[1] = nn[3]) then MyError(87); fi;
  u := Concatenation(n,nn);
  if not(NrRows(u) = 4 and IsIdenticalObj(u[1],u[4])) then MyError(88); fi;

  # We already have tested MutableCopyMat, how about ExtractSubMatrix?
  n := ExtractSubMatrix(m,[1,2],[1,2]);
  if not(IsMatrixObj(n)) then
      Print("Warning: ExtractSubMatrix does not return an object in ",
            "IsMatrixObj!\n");
  fi;
  if not(m[1,1] = n[1,1] and m[1,2] = n[1,2] and m[2,1] = n[2,1] and
         m[2,2] = n[2,2] and NumberRows(n) = 2 and NumberColumns(n) = 2) then
      MyError(89);
  fi;
  n := MutableCopyMat(n);
  CopySubMatrix(m,n,[2,1],[1,2],[2,1],[1,2]);
  if not(m[1,1] = n[2,2] and m[1,2] = n[2,1] and m[2,1] = n[1,2] and
         m[2,2] = n[1,1] and NumberRows(n) = 2 and NumberColumns(n) = 2) then
      MyError(90);
  fi;
  n := StructuralCopy(m);
  if not(m=n) then MyError(91); fi;
  n := ShallowCopy(m);
  if not(m=n and IsIdenticalObj(m[1],n[1])) then MyError(92); fi;

  # Printing and viewing:
  n := Matrix([[zero,one],[two,three]],2,m);
  Print("A matrix is printed as follows:\n",n,"\n\n");
  Print("ViewObj does the following to it:\n");
  ViewObj(n);
  Print("\n\n");
  Print("String gives the following:\n",String(n),"\n\n");
  Print("Display does this:\n");
  Display(n);
  Print("\n");

  # MakeImmutable:
  w := MutableCopyMat(m);
  wi := MutableCopyMat(w);
  MakeImmutable(wi);
  if IsMutable(wi) or IsMutable(wi[1]) then MyError(93); fi;
  
  # Now we try to do some arithmetic:
  l := NrRows(w);
  u := w + w;
  for i in [1..l] do if u[i] <> w[i]+w[i] then MyError(94); fi; od;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(95); fi;
  u := w + wi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(96); fi;
  u := wi + w;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(97); fi;
  u := wi + wi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(98); fi;
  u := w - w;
  if not(IsZero(u)) then MyError(99); fi;
  for i in [1..l] do if u[i] <> w[i]-w[i] then MyError(100); fi; od;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(101); fi;
  u := w - wi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(102); fi;
  u := wi - w;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(103); fi;
  u := wi - wi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(104); fi;

  # Comparison and scalar multiplication:
  u := w * one;
  if not(u = w) then MyError(105); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(105); fi;
  u := wi * one;
  if IsMutable(u) or IsMutable(u[1]) then MyError(106); fi;
  u := one * w;
  if not(u = w) then MyError(107); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(108); fi;
  u := one * wi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(109); fi;
  if u < w then MyError(110); fi;

  # AdditiveInverse*:
  a := -w;
  for i in [1..l] do if a[i] <> -w[i] then MyError(111); fi; od;
  u := AdditiveInverseSameMutability(w);
  if a <> u then MyError(112); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(113); fi;
  u := AdditiveInverseImmutable(w);
  if a <> u then MyError(114); fi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(115); fi;
  u := AdditiveInverseMutable(w);
  if a <> u then MyError(116); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(117); fi;
  u := AdditiveInverseSameMutability(wi);
  if a <> u then MyError(118); fi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(119); fi;
  u := AdditiveInverseImmutable(wi);
  if a <> u then MyError(120); fi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(121); fi;
  u := AdditiveInverseMutable(wi);
  if a <> u then MyError(122); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(123); fi;

  # Zero*
  u := ZeroSameMutability(w);
  if not(IsZero(u)) then MyError(124); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(125); fi;
  u := ZeroImmutable(w);
  if not(IsZero(u)) then MyError(126); fi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(127); fi;
  u := ZeroMutable(w);
  if not(IsZero(u)) then MyError(128); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(129); fi;
  u := ZeroSameMutability(wi);
  if not(IsZero(u)) then MyError(130); fi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(131); fi;
  u := ZeroImmutable(wi);
  if not(IsZero(u)) then MyError(132); fi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(133); fi;
  u := ZeroMutable(wi);
  if not(IsZero(u)) then MyError(134); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(135); fi;

  # Characteristic:
  if Characteristic(m) <> Characteristic(BaseDomain(m)) then MyError(136); fi;

  # TransposedMat*:
  wt := TransposedMatMutable(w);
  if not(IsMutable(wt)) or not(IsMutable(wt[1])) then MyError(137); fi;
  wit := TransposedMatImmutable(w);
  if IsMutable(wit) or IsMutable(wit[1]) then MyError(138); fi;
  
  # Matrix product:
  a := w * wt;
  u := a;
  for i in [1..l] do 
      for j in [1..NumberColumns(wt)] do
          s := Zero(BaseDomain(w));
          for k in [1..NumberColumns(w)] do
              s := s + w[i,k] * wt[k,j];
          od;
          if s <> u[i,j] then MyError(139); fi;
      od;
  od;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(140); fi;
  u := w * wit;
  if u <> a then MyError(141); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(142); fi;
  u := wi * wt;
  if u <> a then MyError(143); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(144); fi;
  u := wi * wit;
  if u <> a then MyError(145); fi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(146); fi;

  # One*
  w := Matrix([[zero,one],[two,three]],2,m);
  wi := MutableCopyMat(w);
  MakeImmutable(wi);
  u := OneSameMutability(w);
  if not(IsOne(u)) then MyError(147); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(148); fi;
  u := OneImmutable(w);
  if not(IsOne(u)) then MyError(149); fi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(150); fi;
  u := OneMutable(w);
  if not(IsOne(u)) then MyError(151); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(152); fi;
  u := OneSameMutability(wi);
  if not(IsOne(u)) then MyError(153); fi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(154); fi;
  u := OneImmutable(wi);
  if not(IsOne(u)) then MyError(155); fi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(156); fi;
  u := OneMutable(wi);
  if not(IsOne(u)) then MyError(157); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(158); fi;

  # ZeroMatrix, IsDiagonalMat, Is{Upper,Lower}TriangularMat:
  u := ZeroMatrix(3,3,m);
  if not(IsMutable(u)) then MyError(159); fi;
  if not(IsZero(u)) then MyError(160); fi;
  u[1,1] := one;
  u[2,1] := one;
  u[1,2] := one;
  if IsDiagonalMat(u) then MyError(161); fi;
  if IsLowerTriangularMat(u) then MyError(162); fi;
  if IsUpperTriangularMat(u) then MyError(163); fi;
  u[1,2] := zero;
  if not(IsLowerTriangularMat(u)) then MyError(164); fi;
  u[2,1] := zero;
  if not(IsUpperTriangularMat(u)) then MyError(165); fi;
  if not(IsDiagonalMat(u)) then MyError(166); fi;

  # IdentityMatrix, Matrix:
  u := IdentityMatrix(7,m);
  if not(NumberRows(u) = 7) or not(NumberColumns(u) = 7) or not(IsOne(u)) or
     not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(167); fi;
  v := Matrix(List(u),7,m);
  if u <> v or not(IsMutable(v)) or not(IsMutable(v[1])) then MyError(168); fi;

  # Randomize:
  Randomize(u);

  # List:
  v := Matrix(List(u,x->-x),7,u);
  if v <> -u then MyError(169); fi;

  # Vector times matrix:
  w := MutableCopyMat(m);
  wi := MutableCopyMat(w);
  MakeImmutable(wi);
  u := Matrix(List(w,v->v*wt),NrRows(w),w);
  if u <> w*wt then MyError(170); fi;
  v := w[1];
  vi := ShallowCopy(v);
  MakeImmutable(vi);
  u := v * wt;
  if not(IsMutable(u)) then MyError(171); fi;
  u := vi * wt;
  if not(IsMutable(u)) then MyError(172); fi;
  u := v * wit;
  if not(IsMutable(u)) then MyError(173); fi;
  u := vi * wit;
  if IsMutable(u) then MyError(174); fi;

  # Unpack:
  u := Unpack(m);
  if not(IsList(u)) and not(ForAll(u,IsList)) then MyError(175); fi;
  if u <> List(m,List) then MyError(176); fi;
  
  # KroneckerProduct:
  w := Matrix([[one,zero],[two,one]],2,m);
  wi := MutableCopyMat(w);
  MakeImmutable(wi);
  u := Matrix([[zero,one],[one,one]],2,m);
  a := KroneckerProduct(u,w);
  if not(IsZero(ExtractSubMatrix(a,[1,2],[1,2]))) then MyError(177); fi;
  if ExtractSubMatrix(a,[1,2],[3,4]) <> w then MyError(178); fi;
  if ExtractSubMatrix(a,[3,4],[1,2]) <> w then MyError(179); fi;
  if ExtractSubMatrix(a,[3,4],[3,4]) <> w then MyError(180); fi;

  # Inverse:
  u := InverseMutable(w);
  if not(IsOne(u*w)) then MyError(181); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(182); fi;
  a := u;
  u := InverseImmutable(w);
  if a <> u then MyError(183); fi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(184); fi;
  u := InverseSameMutability(w);
  if a <> u then MyError(185); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(186); fi;
  u := InverseMutable(wi);
  if a <> u then MyError(187); fi;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(188); fi;
  u := InverseImmutable(wi);
  if a <> u then MyError(189); fi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(190); fi;
  u := InverseSameMutability(wi);
  if a <> u then MyError(191); fi;
  if IsMutable(u) or IsMutable(u[1]) then MyError(192); fi;
  
  # Powering:
  u := w^2;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(193); fi;
  u := w^1;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(194); fi;
  if IsIdenticalObj(u,w) then MyError(195); fi;
  u := w^0;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(196); fi;
  if not(IsOne(u)) then MyError(197); fi;
  u := w^-1;
  if not(IsMutable(u)) or not(IsMutable(u[1])) then MyError(197); fi;
  if not(IsOne(u*w)) then MyError(198); fi;
  u := wi^2;
  if IsMutable(u) or IsMutable(u[1]) then MyError(199); fi;
  u := wi^1;
  if IsMutable(u) or IsMutable(u[1]) then MyError(200); fi;
  if not(IsIdenticalObj(u,wi)) then MyError(201); fi;
  u := wi^0;
  if IsMutable(u) or IsMutable(u[1]) then MyError(202); fi;
  if not(IsOne(u)) then MyError(203); fi;
  u := wi^-1;
  if IsMutable(u) or IsMutable(u[1]) then MyError(204); fi;
  if not(IsOne(u*wi)) then MyError(205); fi;

  # Now the constructors:
  filter := ConstructingFilter(v);
  vv := NewRowVector(filter,bd,Unpack(v));
  if v <> vv or not(IsIdenticalObj(TypeObj(v),TypeObj(vv))) then 
      MyError(208); 
  fi;
  vv := NewZeroVector(filter,bd,Length(v));
  if ZeroMutable(v) <> vv or 
     not(IsIdenticalObj(TypeObj(ZeroMutable(v)),TypeObj(vv))) then 
      MyError(209); 
  fi;
  filter := ConstructingFilter(m);
  vv := NewMatrix(filter,bd,NumberColumns(m),Unpack(m));
  if not(IsMutable(m)) then MakeImmutable(vv); fi;
  if vv <> m or not(IsIdenticalObj(TypeObj(vv),TypeObj(m))) then
      MyError(210);
  fi;
  vv := NewZeroMatrix(filter,bd,NumberRows(m),NumberColumns(m));
  if vv <> ZeroMutable(m) or
     not(IsIdenticalObj(TypeObj(vv),TypeObj(ZeroMutable(m)))) then
      MyError(211);
  fi;
  vv := NewIdentityMatrix(filter,bd,NumberRows(m));
  if not(IsOne(vv)) or
     not(IsIdenticalObj(TypeObj(vv),TypeObj(MutableCopyMat(m)))) then
      MyError(212);
  fi;

  # Now CompanionMatrix:
  pol := PolynomialRing(bd);
  vv := Unpack(m[1]);
  vvv := CompanionMatrix(UnivariatePolynomialByCoefficients(FamilyObj(one),
                         Concatenation(vv,[one]),1),m);
  if vvv[Length(vv)] <> -Vector(vv,CompatibleVector(m)) then MyError(216); fi;
  # Now NewCompanionMatrix:
  vvv2 := NewCompanionMatrix(ConstructingFilter(m),
                             UnivariatePolynomialByCoefficients(FamilyObj(one),
                             Concatenation(vv,[one]),1),BaseDomain(m));
  if vvv2 <> vvv then MyError(217); fi;

  # Now ConcatenationOfVectors:
  vvv2 := ConcatenationOfVectors(vvv[1],vvv[2]);
  if vvv2{[1..Length(vvv[1])]} <> vvv[1] or
     vvv2{[Length(vvv[1])+1..Length(vvv[1])+Length(vvv[2])]} <> vvv[2] then
      MyError(219);
  fi;

  # Now ExtractSubVector:
  vvv2 := ExtractSubVector(vvv[1],[1..Length(vvv[1])-1]);
  if vvv2 <> vvv[1]{[1..Length(vvv[1])-1]} then MyError(220); fi;

  # Now ScalarProduct:
  vvv2 := ScalarProduct(vvv[1],vvv[1]);
  if vvv2 <> Sum([1..Length(vvv[1])],i->vvv[1,i] * vvv[1,i]) then
      MyError(222);
  fi;

  # Now TraceMat:
  vvv2 := TraceMat(vvv);
  if vvv2 <> Sum([1..Length(vvv)],i->vvv[i,i]) then MyError(223); fi;

  # Now WeightOfVector:
  vvv2 := WeightOfVector(vvv[1]);
  if vvv2 <> Number([1..Length(vvv[1])],i->not(IsZero(vvv[1,i]))) then
      MyError(224);
  fi;

  # Now DistanceOfVectors:
  vvv2 := DistanceOfVectors(vvv[1],vvv[2]);
  if vvv2 <> Number([1..Length(vvv[1])],i->vvv[1,i] <> vvv[2,i]) then
      MyError(225);
  fi;

  if level = 0 then
      Print("Standard matrix tests completed.\n\n");
      Print("Errors: ",errors,"\n");
      return;
  fi;

  Print("Standard matrix tests completed, the rest is a bit strange!\n\n");

  # A few more absurd tests:

  # Try empty matrices and vectors:
  v := w[1];
  u := v{[]};
  if not(IsVectorObj(u)) then
      Print("Warning: Empty vector is not in IsVectorObj!\n");
  fi;
  if Length(u) <> 0 then MyError(413); fi;
  u := w{[]};
  if not(IsMatrixObj(u)) then
      Print("Warning: Matrix with no rows is not in IsMatrixObj!\n");
  fi;
  if NumberRows(u) <> 0 then MyError(414); fi;
  u := ExtractSubMatrix(w,[1..2],[]);
  if not(IsMatrixObj(u)) then
      Print("Warning: Matrix with empty rows is not in IsMatrixObj!\n");
  fi;
  if NumberColumns(u) <> 0 then MyError(415); fi;
  if NumberRows(u) <> 2 then MyError(416); fi;

  w := Matrix( [[one,two]],2,m );
  if IsOne(w) <> false then MyError(408); fi;
  # IsOne is a property and hence must only return false or true
  if OneMutable(w) <> fail then MyError(409); fi;
  if Inverse(w) <> fail then MyError(410); fi;
  # Error 211 taken out.
  w := Matrix( [[one,zero],[one,zero]],2,m );
  if Inverse(w) <> fail then MyError(412); fi;

  # Now Memory:
  vv := MemoryUsage(m[1]);
  vv := MemoryUsage(m);
  # This is only tried, not tested.

  Print("Strange tests completed.\n\n");

  Print("Errors: ",errors,"\n");
  return;
end;

