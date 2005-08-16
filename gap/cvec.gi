#############################################################################
##
#W  cvec.gi               GAP 4 package `cvec'                Max Neunhoeffer
##
#Y  Copyright (C)  2005,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
##
##  This file contains the higher levels for compact vectors over finite 
##  fields. 
##

################################
# First look after our C part: #
################################

# load kernel function if it is installed:
if (not IsBound(CVEC)) and ("cvec" in SHOW_STAT()) then
  # try static module
  LoadStaticModule("cvec");
fi;
if (not IsBound(CVEC)) and
   (Filename(DirectoriesPackagePrograms("cvec"), "cvec.so") <> fail) then
  LoadDynamicModule(Filename(DirectoriesPackagePrograms("cvec"), "cvec.so"));
fi;

#############################################################################
## Info Class:
#############################################################################

SetInfoLevel(InfoCVec,1);


#############################################################################
## The technical stuff for typing:
#############################################################################

# A set holding all q's for which we have cvec classes:
CVEC.q := [];
# A list holding field infos:
CVEC.F := [];
# A list holding lengths of vectors existing for each q:
CVEC.lens := [];
# A list holding cvec classes (which are pairs [fieldinfo,len])
CVEC.classes := [];

CVEC.ClearCache := function()
  local i;
  CVEC.q := [];
  CVEC.F := [];
  CVEC.lens := [];
  CVEC.classes := [];
  MakeReadWriteGVar("GALOIS_FIELDS");
  GALOIS_FIELDS := [];
  MakeReadOnlyGVar("GALOIS_FIELDS");
  #CVecFamily!.TYPES := [];   # we have outsourced the families
  #CVecFamily!.nTYPES := 0;   # now we suffer under the collateral damage
end;

#############################################################################
## Administration of field info and cvec class data:
#############################################################################

# If you want to change the 1024 limit below, please also change
# the macro MAXDEGREE in cvec.c!
CVEC.MAXDEGREE := 1024;

CVEC.BestGreaseTab :=
  [ ,            # q=1
    8,           # q=2
    5,           # q=3
    4,           # q=4
    3,           # q=5  
                 # No longer valid:
                 #      Note that we reduce here the grease level to 2 such
                 #      that elsperword (= 8) is divisible by the grease level,
                 #      this is used to make the multiplication function much
                 #      simpler (no bad case at right edge of A!)
    ,            # q=6
    3,           # q=7
    3,           # q=8
    3,           # q=9
    ,            # q=10
    2,           # q=11
    ,            # q=12
    2,           # q=13
    ,            # q=14
    ,            # q=15
    2,           # q=16
  ];

CVEC.NewCVecClass := function(p,d,len)
  # Creates a new class of cvecs or returns a cached one:
  local T,bestgrease,bitsperel,cl,elsperword,filts,greasetabl,i,j,l,li,o,po,
        pos,pos2,q,s,scaclass,scafam,size,tab1,tab2,ty,wordlen,z;

  # First check the arguments:
  if d <= 0 then 
      Error("CVEC.NewCVecClass: Degree must be positive."); 
      return fail;
  fi;
  if d >= CVEC.MAXDEGREE then 
      Error("CVEC.NewCVecClass: Degree must be < ",CVEC.MAXDEGREE,"."); 
      return fail;
  fi;
  if not(IsPrime(p)) then 
      Error("CVEC.MakeField: p must be a prime."); 
      return fail;
  fi; 
  if not(IsSmallIntRep(p)) then 
      Error("CVEC.NewCVecClass: p must be a prime that is an immediate int .");
      return fail;
  fi;
  if not(IsSmallIntRep(len)) then
      Error("CVEC.NewCVecClass: len must be an immediate integer.");
      return fail;
  fi;
  q := p^d;
  if q <= MAXSIZE_GF_INTERNAL then size := 0;
  elif IsSmallIntRep(q) then size := 1;
  else size := 2; fi;

  # First try to find q:
  pos := Position(CVEC.q,q);
  if pos = fail then
      # We have to make the new field info structure:
      po := -CoefficientsOfLaurentPolynomial(ConwayPolynomial(p,d));
      if po[2] <> 0 then Error("Unexpected case #1"); fi;
      po := List(po[1],IntFFE);
      s := CVEC.COEFF_LIST_TO_C(po,"");

      # Bits per element, will be increased in the following loop:
      if IsOddInt(p) then
          bitsperel := 1;
      else
          bitsperel := 0;
      fi;
      j := p-1;
      while j > 0 do
          bitsperel := bitsperel + 1;
          j := QuoInt(j,2);
      od;

      # Prime field elements per Word:
      # Note that for 64 bit machines we always put only twice as much
      # prime field elements into a Word than for 32 bit machines (even if
      # one more would fit!) such that conversion between binary formats
      # is easier later on.
      elsperword := QuoInt(32,bitsperel);
      if CVEC.BYTESPERWORD = 8 then
          elsperword := elsperword * 2;
      fi;

      # Set up best greasing level:
      if q <= 16 and IsBound(CVEC.BestGreaseTab[q]) then
          bestgrease := CVEC.BestGreaseTab[q];
          greasetabl := q^bestgrease;
      elif q <= 256 then
          bestgrease := 1;
          greasetabl := q;
      else
          bestgrease := 0;  # no grease
          greasetabl := 0;
      fi;

      # Now the starting filter list:
      #filts := IsHomogeneousList and IsListDefault and IsCopyable and
      #         IsCVecRep and IsSmallList and
      #         IsNoImmediateMethodsObject and
      #         IsRingElementList and HasLength and IsMutable;
      filts := IsCVecRep and IsNoImmediateMethodsObject and HasLength and
               IsMutable and IsCopyable and CanEasilyCompareElements;
      if q <= MAXSIZE_GF_INTERNAL then
          scafam := FFEFamily(p);
      else
          # for bigger q we generate a family for each field:
          scafam := NewFamily("CScaFamily",IsFFE);
          SetCharacteristic(scafam,p);
          SetIsUFDFamily(scafam,true);
          # Zero and One are set later, where they are created!
      fi;

      # Now for small finite fields two tables for conversion:
      if q <= MAXSIZE_GF_INTERNAL then
          tab1 := 0*[1..q];
          tab2 := 0*[1..q];
          CVEC.INIT_SMALL_GFQ_TABS(p,d,q,tab1,tab2,Z(q));
      else
          tab1 := [];
          tab2 := [];
      fi;

      l := [p,d,q,s,bitsperel,elsperword,0,bestgrease,greasetabl,filts,
            tab1,tab2,size,scafam];
      Objectify(NewType(CVecFieldInfoFamily,IsCVecFieldInfo),l);

      # Do the internal part:
      CVEC.FINALIZE_FIELDINFO(l);

      pos := PositionSorted(CVEC.q,q);
      Add(CVEC.q,q,pos);
      Add(CVEC.F,l,pos);
      Add(CVEC.lens,[],pos);
      Add(CVEC.classes,[],pos);
  else   # pos <> fail
      elsperword := CVEC.classes[pos][1]![1]![6];   # for later use
      filts := CVEC.classes[pos][1]![1]![10];       # for later use
      scafam := CVEC.classes[pos][1]![1]![14];      # for later use
  fi;

  # If q > MAXSIZE_GF_INTERNAL make sure, that the corresponding scalar 
  # class is there:
  if q > MAXSIZE_GF_INTERNAL or len = -1 then
      if IsBound(CVEC.lens[pos][1]) and CVEC.lens[pos][1] = -1 then
          scaclass := CVEC.classes[pos][1];
      else
          # First for taking square roots, we do some preparations:
          s := q-1;
          T := -1;
          while IsEvenInt(s) do
              s := s / 2;
              T := T + 1;
          od; 

          ty := NewType(scafam,
                        IsCScaRep and CanEasilyCompareElements and
                        IsNoImmediateMethodsObject and IsScalar);
          # the fails will be replaced with zero, one and x resp., see below
          # the last fail will be replaced with a list of (x^s)^(2^i) for
          # i between 0 and T. All this is needed for taking square roots.
          scaclass := [CVEC.F[pos],-1,d,ty,fail,fail,s,T,fail,fail];
          SetDataType(ty,scaclass);
          Objectify(NewType(CVecClassFamily,IsCVecClass),scaclass);
          # and put it into the cache:
          Add(CVEC.lens[pos],-1,1);
          Add(CVEC.classes[pos],scaclass,1);
          # Now make zero and one object:
          z := CVEC.NEW(scaclass);
          # CVEC.MAKEZERO(z);
          # this is unnecessary, since GASMAN returns empty bags
          MakeImmutable(z);
          scaclass![5] := z;
          o := CVEC.NEW(scaclass);
          li := 0*[1..d];
          li[1] := 1;
          CVEC.INTREP_TO_CSCA(li,o);
          MakeImmutable(o);
          scaclass![6] := o;
          
          # Put zero and one into the scalars family:
          SetZero(scafam,z);
          SetOne(scafam,o);

          # Now one more preparation for taking square roots:
          if d > 1 then
              z := CVEC.NEW(scaclass);
              li[1] := 0;
              li[2] := 1;
              CVEC.INTREP_TO_CSCA(li,z);
              scaclass![9] := z;
              scaclass![10] := [z^s];
              for i in [1..T] do Add(scaclass![10],scaclass![10][i]^2); od;
          # for degree 1 we do not search for a primitive root here
          # this we do, when the first square root has to be taken!
          fi;
      fi;
  fi; 

  # Now we know that the field info is at position pos:
  pos2 := Position(CVEC.lens[pos],len);
  if pos2 <> fail then
      return CVEC.classes[pos][pos2];
  fi;

  # The case len = -1 is done with here, because we already made it
          
  # Build the class object, note that we need elsperword and filts from above:
  # Note that the case l=-1 is special and stands for our scalars: */
  wordlen := d * (QuoInt( len + elsperword - 1, elsperword ));
  ty := NewType(CollectionsFamily(scafam),filts);
  if q > MAXSIZE_GF_INTERNAL then
      cl := [CVEC.F[pos],len,wordlen,ty,scaclass];
  else
      cl := [CVEC.F[pos],len,wordlen,ty,GF(CVEC.F[pos]![1],CVEC.F[pos]![2])];
  fi;
  SetDataType(ty,cl);
  Objectify(NewType(CVecClassFamily,IsCVecClass),cl);

  # Put it into the cache:
  pos2 := PositionSorted(CVEC.lens[pos],len);
  Add(CVEC.lens[pos],len,pos2);
  Add(CVEC.classes[pos],cl,pos2);
  
  return CVEC.classes[pos][pos2];
end;
 
InstallMethod( CVecClass, "for a csca", [IsCScaRep],
  function(v)
    return DataType(TypeObj(v));
  end);

InstallMethod( CVecClass, "for a cvec", [IsCVecRep],
  function(v)
    return DataType(TypeObj(v));
  end);

CVEC.CVecClass := function(v)
  # Returns the class of the vector or scalar
  return DataType(TypeObj(v));
end;

CVEC.New := function(arg)
  local c,p,d,l,v;
  if Length(arg) = 1 then
      c := arg[1];
      if IsCVecRep(c) or IsCScaRep(c) then
          c := CVEC.CVecClass(c);
      fi;
      if IsCVecClass(c) then
          v := CVEC.NEW(c);
          #CVEC.MAKEZERO(v);
          # not necessary, since GASMAN only gives empty bags
          return v;
      fi;
  elif Length(arg) = 3 then
      p := arg[1];
      d := arg[2];
      l := arg[3];
      if IsInt(p) and IsPrime(p) and p > 0 and IsInt(d) and d >= 1 and
         IsInt(l) and l >= 1 then
          c := CVEC.NewCVecClass(p,d,l);
          v := CVEC.NEW(c);
          #CVEC.MAKEZERO(v);
          # not necessary, since GASMAN only gives empty bags
          return v;
      fi;
  fi;
  Error("Usage: CVEC.New( [ cvec | cvecclass | p,d,l ] )");
end;

##############################
# Some nice viewing methods: #
##############################

InstallMethod( ViewObj, "for a cvec field info", [IsCVecFieldInfo], 
function(f)
  Print("<cvec-fieldinfo p=",f![1]," d=",f![2]," q=",f![3],
        " bpl=",f![5]," epw=",f![6],
        " grease=",f![8]," gtablen=",f![9],">");
end);

InstallMethod( ViewObj, "for a cvec class", [IsCVecClass], 
function(c)
  if c![2] = -1 then    
      # This is in fact a class of scalars:
      Print("<csca-class field=GF(",c![1]![1],",",c![1]![2],")>");
  else
      Print("<cvec-class field=GF(",c![1]![1],",",c![1]![2],") len=",c![2],
            " wordlen=",c![3],">");
  fi;
end);

InstallMethod( ViewObj, "for a csca", [IsCScaRep],
function(v)
  local c,d,i,l,written;
  c := CVEC.CVecClass(v);
  d := c![1]![2];    # the degree
  l := 0*[1..d];
  CVEC.CSCA_TO_INTREP(v,l);
  Print("<csca ");
  if l[1] <> 0 then 
      Print(l[1]);
      written := true;
  else
      written := false;
  fi;
  for i in [2..d] do
      if l[i] <> 0 then
          if written then Print("+"); fi;
          written := true;
          if l[i] <> 1 then Print(l[i],"*"); fi;
          Print("x");
          if i > 2 then Print("^",i-1); fi;
      fi;
  od;
  if not(written) then Print("0"); fi;
  Print("+(pol) in GF(",c![1]![1],",",c![1]![2],")>");
end);

InstallMethod( String, "for a csca", [IsCScaRep],
function(v)
  local c,d,i,l,written,res;
  c := CVEC.CVecClass(v);
  d := c![1]![2];    # the degree
  l := 0*[1..d];
  CVEC.CSCA_TO_INTREP(v,l);
  res := "<csca ";
  if l[1] <> 0 then 
      Append(res,String(l[1]));
      written := true;
  else
      written := false;
  fi;
  for i in [2..d] do
      if l[i] <> 0 then
          if written then Append(res,"+"); fi;
          written := true;
          if l[i] <> 1 then 
              Append(res,String(l[i]));
              Append(res,"*");
          fi;
          Append(res,"x");
          if i > 2 then Append(res,"^"); Append(res,String(i-1)); fi;
      fi;
  od;
  if not(written) then Append(res,"0"); fi;
  Append(res,"+(pol) in GF(");
  Append(res,String(c![1]![1]));
  Append(res,",");
  Append(res,String(c![1]![2]));
  Append(res,")>");
  return res;
end);

InstallMethod( ViewObj, "for a cvec", [IsCVecRep], 
function(v)
  local c;
  c := CVEC.CVecClass(v);
  Print("<");
  if not(IsMutable(v)) then Print("immutable "); fi;
  Print("cvec over GF(",c![1]![1],",",c![1]![2],") of length ",c![2],">");
end);

InstallMethod( ViewObj, "for a cmat", [IsCMatRep and IsMatrix],
function(m)
  local c;
  c := m!.vecclass;
  Print("<");
  if not(IsMutable(m)) then Print("immutable "); fi;
  if HasGreaseTab(m) then Print("greased "); fi;
  Print("cmat ",m!.len,"x",c![2]," over GF(",
        c![1]![1],",",c![1]![2],")>");
end);

InstallMethod( PrintObj, "for a cvec class", [IsCVecClass], 
function(c)
  Print("CVEC.NewCVecClass(",c![1]![1],",",c![1]![2],",",c![2],")");
end);

InstallMethod( PrintObj, "for a csca", [IsCScaRep],
function(v)
  local c,d,l,p;
  c := CVEC.CVecClass(v);
  p := c![1]![1];    # the characteristic
  d := c![1]![2];    # the degree
  l := 0*[1..d];
  CVEC.CSCA_TO_INTREP(v,l);
  Print("CSca(",l,",",p,",",d,")");
end);

InstallMethod( PrintObj, "for a cvec", [IsCVecRep], 
function(v)
  local l,c,i;
  c := CVEC.CVecClass(v);
  Print("CVec([");
  if c![1]![13] = 0 then   # GAP FFEs
      l := FFEList(v);
      for i in l do Print(i,","); od;
  else
      l := Unpack(v);
      for i in l do Print(i,","); od;
  fi;
  Print("],",c![1]![1],",",c![1]![2],")");
end);

InstallMethod( String, "for a cvec", [IsCVecRep], 
function(v)
  local l,c,i,res;
  c := CVEC.CVecClass(v);
  res := "CVec([";
  if c![1]![13] = 0 then   # GAP FFEs
      l := FFEList(v);
      for i in l do Append(res,String(i)); Append(res,","); od;
  else
      l := Unpack(v);
      for i in l do Append(res,String(i)); Append(res,","); od;
  fi;
  Append(res,"],");
  Append(res,String(c![1]![1]));
  Append(res,",");
  Append(res,String(c![1]![2]));
  Append(res,")");
  return res;
end);

InstallMethod( PrintObj, "for a cmat", [IsCMatRep and IsMatrix],
function(m)
  local c,i;
  Print("CMat([");
  for i in [1..m!.len] do
      Print(m!.rows[i+1],",");
  od;
  Print("],",m!.vecclass,")");
end);
  
CVEC.CharactersForDisplay := ".123456789abcdefghijklmnopqrstuvwxyz";

InstallMethod( Display, "for a cvec", [IsCVecRep], 
function(v)
  local i,l,c,q,lo;
  c := CVEC.CVecClass(v);
  Print("[");
  q := c![1]![3];
  if q <= 36 then
      l := Unpack(v);
      Print(CVEC.CharactersForDisplay{l+1},"]\n");
  elif c![1]![13] = 1 then
      l := Unpack(v);
      lo := LogInt(q,10)+2;   # This is the number of digits needed plus 1
      for i in l do Print(String(i,lo)); od;
      Print("]\n");
  else
      l := FFEList(v);
      for i in l do Print(i,","); od;
      Print("]\n");
  fi;
end);

InstallMethod( Display, "for a cmat", 
  [IsCMatRep and IsMatrix and IsFFECollColl],
function(m)
  local i;
  Print("[");
  for i in [1..m!.len] do
      if i <> 1 then Print(" "); fi;
      Display(m!.rows[i+1]);
  od;
  Print("]\n");
end);


#################################################
# Now to the installation of methods for cvecs: #
#################################################

# Length:

InstallOtherMethod( Length, "for cvecs", [IsCVecRep], 
function(v)
  return CVEC.CVecClass(v)![2];
end);

# AddRowVector(v,w [,s][,fr,to]) where s is integer or FFE:

InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep],
  function(v,w) CVEC.ADD2(v,w,0,0); end);

InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep, IsPosInt, IsPosInt],
  function(v,w,fr,to) CVEC.ADD2(v,w,fr,to); end);

InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep, IsFFE],
  function(v,w,s) CVEC.ADDMUL(v,w,s,0,0); end);
InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep, IsInt],
  function(v,w,s) CVEC.ADDMUL(v,w,s,0,0); end);
InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep, IsScalar and IsCScaRep],
  function(v,w,s) CVEC.ADDMUL(v,w,s,0,0); end);

InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep, IsFFE, IsPosInt, IsPosInt],
  CVEC.ADDMUL );
InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep, IsInt, IsPosInt, IsPosInt],
  CVEC.ADDMUL );
InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep, IsScalar and IsCScaRep, 
   IsPosInt, IsPosInt],
  CVEC.ADDMUL );

# MultRowVector(v,s [,fr,to]) where s is integer or FFE:
# Note that we do not give a method for MultRowVector with 5 arguments!

InstallOtherMethod( MultRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsInt],
  function(v,s) CVEC.MUL1(v,s,0,0); end);
InstallOtherMethod( MultRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsInt, IsPosInt, IsPosInt],
  CVEC.MUL1 );

InstallOtherMethod( MultRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsFFE],
  function(v,s) CVEC.MUL1(v,s,0,0); end);
InstallOtherMethod( MultRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsFFE, IsPosInt, IsPosInt],
  CVEC.MUL1 );

InstallOtherMethod( MultRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsScalar and IsCScaRep],
  function(v,s) CVEC.MUL1(v,s,0,0); end);
InstallOtherMethod( MultRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsScalar and IsCScaRep, IsPosInt, IsPosInt],
  CVEC.MUL1 );

# Addition of vectors:

InstallOtherMethod( \+, "for cvecs", [IsCVecRep, IsCVecRep],
  function(v,w)
    local u,vcl;
    vcl := CVEC.CVecClass(v);
    u := CVEC.NEW(vcl);
    CVEC.ADD3(u,v,w);
    if not(IsMutable(v)) or not(IsMutable(w)) then MakeImmutable(u); fi;
    return u;
  end);

# Subtraction of vectors:

InstallOtherMethod( \-, "for cvecs", [IsCVecRep, IsCVecRep],
  function(v,w)
    local u,vcl,p;
    vcl := CVEC.CVecClass(v);
    p := vcl![1]![1];
    u := CVEC.NEW(vcl);
    CVEC.COPY(v,u);
    CVEC.ADDMUL(u,w,p-1,0,0);
    if not(IsMutable(v)) or not(IsMutable(w)) then MakeImmutable(u); fi;
    return u;
  end);

# Additive inverse of vectors:

InstallOtherMethod( AdditiveInverseMutable, "for cvecs", [IsCVecRep],
  function(v)
    local u,vcl,p;
    vcl := CVEC.CVecClass(v);
    p := vcl![1]![1];
    u := CVEC.NEW(vcl);
    CVEC.MUL2(u,v,p-1);
    return u;
  end);
InstallOtherMethod( AdditiveInverseSameMutability, "for cvecs", [IsCVecRep],
  function(v)
    local u,vcl,p;
    vcl := CVEC.CVecClass(v);
    p := vcl![1]![1];
    u := CVEC.NEW(vcl);
    CVEC.MUL2(u,v,p-1);
    if not(IsMutable(v)) then MakeImmutable(u); fi;
    return u;
  end);

# Multiplication of vectors by scalars:

CVEC.VECTOR_TIMES_SCALAR := function(v,s)
    local u,vcl;
    vcl := CVEC.CVecClass(v);
    u := CVEC.NEW(vcl);
    CVEC.MUL2(u,v,s);
    if not(IsMutable(v)) then MakeImmutable(u); fi;
    return u;
  end;
InstallOtherMethod( \*, "for cvecs", [IsCVecRep, IsInt], 
  CVEC.VECTOR_TIMES_SCALAR);
InstallOtherMethod( \*, "for cvecs", [IsCVecRep, IsFFE], 
  CVEC.VECTOR_TIMES_SCALAR);
InstallOtherMethod( \*, "for cvecs", [IsCVecRep, IsScalar and IsCScaRep], 
  CVEC.VECTOR_TIMES_SCALAR);
InstallOtherMethod( \*, "for cvecs", [IsInt,IsCVecRep], 
  function(s,v) return CVEC.VECTOR_TIMES_SCALAR(v,s); end);
InstallOtherMethod( \*, "for cvecs", [IsFFE,IsCVecRep], 
  function(s,v) return CVEC.VECTOR_TIMES_SCALAR(v,s); end);
InstallOtherMethod( \*, "for cvecs", [IsScalar and IsCScaRep,IsCVecRep], 
  function(s,v) return CVEC.VECTOR_TIMES_SCALAR(v,s); end);

# Comparison of vectors:

InstallOtherMethod( \=, "for cvecs", [IsCVecRep, IsCVecRep], CVEC.CVEC_EQ );
InstallOtherMethod( \<, "for cvecs", [IsCVecRep, IsCVecRep], CVEC.CVEC_LT );
InstallOtherMethod( IsZero, "for cvecs", [IsCVecRep], CVEC.CVEC_ISZERO);

# Element access for vectors:

InstallOtherMethod( \[\]\:\=, "for a cvec, a pos, and an int",
  [IsCVecRep and IsMutable, IsPosInt, IsInt], CVEC.ASS_CVEC );
InstallOtherMethod( \[\]\:\=, "for a cvec, a pos, and a ffe",
  [IsCVecRep and IsMutable, IsPosInt, IsFFE], CVEC.ASS_CVEC );
InstallOtherMethod( \[\]\:\=, "for a cvec, a pos, and a csca",
  [IsCVecRep and IsMutable, IsPosInt, IsScalar and IsCScaRep], CVEC.ASS_CVEC );
InstallOtherMethod( \[\]\:\=, "for cvecs", [IsCVecRep, IsPosInt, IsInt],
  function(v,p,o) Error("cvec is immutable"); end);
InstallOtherMethod( \[\]\:\=, "for cvecs", [IsCVecRep, IsPosInt, IsFFE],
  function(v,p,o) Error("cvec is immutable"); end);
InstallOtherMethod( \[\]\:\=, "for a cvec, a pos, and a csca",
  [IsCVecRep, IsPosInt, IsScalar and IsCScaRep],
  function(v,p,o) Error("cvec is immutable"); end);

InstallOtherMethod( \[\], "for cvecs", [IsCVecRep, IsPosInt], CVEC.ELM_CVEC );

# PositionNonZero and friends:

InstallOtherMethod( PositionNonZero, "for cvecs",
  [IsCVecRep], CVEC.POSITION_NONZERO_CVEC);
InstallOtherMethod( PositionLastNonZero, "for cvecs",
  [IsCVecRep], CVEC.POSITION_LAST_NONZERO_CVEC);
InstallOtherMethod( PositionNot, "for cvecs",
  [IsCVecRep, IsFFE], 
  function(v,z)
    if z <> Zero(z) then
        Error("PositionNot for cvecs and other values than zero not yet impl.");
    fi;
    return PositionNonZero(v);
  end);
InstallOtherMethod( PositionNot, "for cvecs",
  [IsCVecRep, IsFFE, IsInt], 
  function(v,z,i)
    if z <> Zero(z) or i <> 0 then
        Error("PositionNot for cvecs and other values than zero not yet impl.");
    fi;
    return PositionNonZero(v);
  end);

# Copying:

InstallOtherMethod( ShallowCopy, "for cvecs", [IsCVecRep],
  function(v)
    local u,vcl;
    vcl := CVEC.CVecClass(v);
    u := CVEC.NEW(vcl);
    CVEC.COPY(v,u);
    return u;
  end);

# Zeroing:

InstallOtherMethod( ZeroMutable, "for cvecs", [IsCVecRep],
  function(v)
    local u,vcl;
    vcl := CVEC.CVecClass(v);
    u := CVEC.NEW(vcl);
    #CVEC.MAKEZERO(u);
    # Not necessary, since GASMAN only returns empty bags
    return u;
  end);
InstallOtherMethod( ZeroSameMutability, "for cvecs", [IsCVecRep],
  function(v)
    local u,vcl;
    vcl := CVEC.CVecClass(v);
    u := CVEC.NEW(vcl);
    #CVEC.MAKEZERO(u);
    # not necessary, since GASMAN only returns empty bags
    if not(IsMutable(v)) then
        MakeImmutable(u);
    fi;
    return u;
  end);

# The making of:

InstallMethod( CVec, "for a homogeneous list and two posints", 
  [IsHomogeneousList, IsPosInt, IsPosInt],
  function(l,p,d)
    local c,v;
    if IsSmallIntRep(p^d) then
        c := CVEC.NewCVecClass(p,d,Length(l));
    else
        c := CVEC.NewCVecClass(p,d,Length(l)/d);
    fi;
    v := CVEC.NEW(c);
    CVEC.INTREP_TO_CVEC(l,v);
    return v;
  end);
InstallMethod( CVec, "for a cvec class",
  [IsCVecClass],
  function(c)
    return CVEC.NEW(c);
  end);
InstallMethod( CVec, "for a homogeneous list and a cvec class",
  [IsHomogeneousList, IsCVecClass],
  function(l,c)
    local v;
    v := CVEC.NEW(c);
    CVEC.INTREP_TO_CVEC(l,v);
    return v;
  end);
InstallOtherMethod( CVec, "for a compressed gf2 vector",
  [IsHomogeneousList and IsGF2VectorRep],
  function(v)
    local c,w;
    v := ShallowCopy(v);
    Add(v,fail);   # this unpacks
    Unbind(v[Length(v)]);  
    c := CVEC.NewCVecClass(2,1,Length(v));
    w := CVEC.NEW(c);
    CVEC.INTREP_TO_CVEC(v,w);
    return w;
  end);
InstallOtherMethod( CVec, "for a compressed 8bit vector",
  [IsHomogeneousList and Is8BitVectorRep],
  function(v)
    local c,pd,w;
    pd := Factors(Size(Field(v)));
    v := ShallowCopy(v);
    Add(v,fail);   # this unpacks
    Unbind(v[Length(v)]);  
    c := CVEC.NewCVecClass(pd[1],Length(pd),Length(v));
    w := CVEC.NEW(c);
    CVEC.INTREP_TO_CVEC(v,w);
    return w;
  end);

# And the way back:

InstallMethod( Unpack, "for cvecs", [IsCVecRep],
  function(v)
    local l,vcl;
    vcl := CVEC.CVecClass(v);
    if vcl![1]![13] = 2 then
        l := 0 * [1..vcl![2]*vcl![1]![2]];   # length * d
    else
        l := 0*[1..Length(v)];
    fi;
    CVEC.CVEC_TO_INTREP(v,l);
    return l;
  end);

InstallMethod( FFEList, "for cvecs", [IsCVecRep],
  function(v)
    local vcl,l,i;
    vcl := CVEC.CVecClass(v);
    l := 0*[1..Length(v)];
    CVEC.CVEC_TO_FFELI(v,l);
    return l;
  end);

# Access to the base field:

InstallOtherMethod( DegreeFFE, "for cvecs", [IsCVecRep],
  function(v)
    local c;
    c := CVEC.CVecClass(v);
    return c![1]![2];
  end);
    
InstallOtherMethod( Characteristic, "for cvecs", [IsCVecRep],
  function(v)
    local c;
    c := CVEC.CVecClass(v);
    return c![1]![1];
  end);
    
InstallMethod( BaseField, "for cvecs", [IsCVecRep],
  function(v)
    local c,p,d;
    c := CVEC.CVecClass(v);
    p := c![1]![1];
    d := c![1]![2];
    if p^d <= MAXSIZE_GF_INTERNAL then
        return GF(p,d);
    else
        return c![5];
    fi;
  end);
    
# Slicing:

CVEC.Slice := function(src,dst,srcpos,len,dstpos)
  local cdst,csrc;
  csrc := CVEC.CVecClass(src);
  cdst := CVEC.CVecClass(dst);
  if not(IsIdenticalObj(csrc![1],cdst![1])) then
      Error("CVEC.Slice: vectors not over common field");
      return;
  fi;
  if srcpos < 1 or srcpos+len-1 > csrc![2] or len <= 0 then
      Error("CVEC.Slice: source area not valid");
      return;
  fi;
  if dstpos < 1 or dstpos+len-1 > cdst![2] then
      Error("CVEC.Slice: destination area not valid");
      return;
  fi;
  CVEC.SLICE(src,dst,srcpos,len,dstpos);
end;

InstallOtherMethod( \{\}, "for a cvec and a range", [IsCVecRep, IsRangeRep],
  function(v,r)
    # note that ranges in IsRangeRep always have length at least 2!
    local c,cl,first,inc,last,len,w;
    first := r[1];
    last := r[Length(r)];
    inc := (last-first)/(Length(r)-1);
    if inc <> 1 then
        Error("CVEC.{} : slicing only for ranges with increment 1 available");
        return;
    fi;
    cl := CVEC.CVecClass(v);
    len := last+1-first;
    c := CVEC.NewCVecClass(cl![1]![1],cl![1]![2],len);
    w := CVEC.NEW(c);
    CVEC.SLICE(v,w,first,len,1);
    if not(IsMutable(v)) then
        MakeImmutable(w);
    fi;
    return w;
  end);

InstallOtherMethod( \{\}, "for a cvec and a list", 
  [IsCVecRep, IsHomogeneousList],
  function(v,l)
    local c,cl,first,inc,last,len,w;
    if Length(l) = 0 then
        first := 1;
        last := 0;
    elif Length(l) = 1 then
        first := l[1];
        last := l[1];
    else
        first := l[1];
        last := l[Length(l)];
        inc := (last-first)/(Length(l)-1);
        if not(IsRange(l)) or inc <> 1 then
          Error("CVEC.{} : slicing only for ranges with increment 1 available");
          return;
        fi;
    fi;
    cl := CVEC.CVecClass(v);
    len := last+1-first;
    c := CVEC.NewCVecClass(cl![1]![1],cl![1]![2],len);
    w := CVEC.NEW(c);
    if len > 0 then CVEC.SLICE(v,w,first,len,1); fi;
    if not(IsMutable(v)) then
        MakeImmutable(w);
    fi;
    return w;
  end);

# Note that slicing assignment is intentionally not supported, because
# this will usually be used only by inefficient code. Use CVEC.Slice
# or even CVEC.SLICE instead.

#############################################################################
# Scalars:
#############################################################################

# Creation:

InstallMethod( CSca, "for a list of coefficients and a cvecclass",
  [IsList, IsCVecClass],
  function(l,c)
    local v;
    if c![2] <> -1 then 
        Error("CSca: not a class of finite field scalars"); 
        return fail;
    fi;
    v := CVEC.NEW(c);
    CVEC.INTREP_TO_CSCA(l,v);
    MakeImmutable(v);
    return v;
  end);

InstallMethod( CSca, "for a list of coefficients and a csca",
  [IsList, IsCScaRep],
  function(l,s)
    local v;
    v := CVEC.NEW(CVEC.CVecClass(s));
    CVEC.INTREP_TO_CSCA(l,v);
    MakeImmutable(v);
    return v;
  end);

InstallMethod( CSca, "for a list of coefficients and two integers",
  [IsList, IsPosInt, IsPosInt],
  function(l,p,d)
    local v;
    v := CVEC.NEW(CVEC.NewCVecClass(p,d,-1));
    CVEC.INTREP_TO_CSCA(l,v);
    MakeImmutable(v);
    return v;
  end);

# Addition of scalars:

InstallOtherMethod( \+, "for cscas", 
  [IsScalar and IsCScaRep, IsScalar and IsCScaRep],
  function(v,w)
  local u,vcl;
  vcl := CVEC.CVecClass(v);
  u := CVEC.NEW(vcl);
  CVEC.ADD3(u,v,w);
  MakeImmutable(u);
  return u;
end);

# Subtraction of scalars:

InstallOtherMethod( \-, "for cscas", 
  [IsScalar and IsCScaRep, IsScalar and IsCScaRep],
  function(v,w)
  local u,vcl,p;
  vcl := CVEC.CVecClass(v);
  p := vcl![1]![1];
  u := CVEC.NEW(vcl);
  CVEC.COPY(v,u);
  CVEC.ADDMUL(u,w,p-1,0,0);
  MakeImmutable(u);
  return u;
end);
  
# Additive inverse of scalars:

InstallOtherMethod( AdditiveInverseSameMutability, "for a csca", 
  [IsScalar and IsCScaRep],
  function(v)
  local u,vcl,p;
  vcl := CVEC.CVecClass(v);
  u := CVEC.NEW(vcl);
  p := vcl![1]![1];
  CVEC.MUL2(u,v,p-1);
  MakeImmutable(u);   # all CScas are immutable
  return u;
end);
InstallOtherMethod( AdditiveInverseImmutable, "for a csca", 
  [IsScalar and IsCScaRep],
  function(v)
  local u,vcl,p;
  vcl := CVEC.CVecClass(v);
  u := CVEC.NEW(vcl);
  p := vcl![1]![1];
  CVEC.MUL2(u,v,p-1);
  MakeImmutable(u);   # all CScas are immutable
  return u;
end);

# Comparison of scalars:

InstallOtherMethod( \=, "for cscas", 
  [IsScalar and IsCScaRep, IsScalar and IsCScaRep], CVEC.CVEC_EQ );
InstallOtherMethod( \<, "for cscas", 
  [IsScalar and IsCScaRep, IsScalar and IsCScaRep], CVEC.CVEC_LT );
InstallOtherMethod( IsZero, "for cscas", 
  [IsScalar and IsCScaRep], CVEC.CVEC_ISZERO);

# Multiplication of scalars:

InstallOtherMethod( \*, "for cscas",
  [IsScalar and IsCScaRep, IsScalar and IsCScaRep], 
  function(v,w)
  local u,vcl;
  vcl := CVEC.CVecClass(v);
  u := CVEC.NEW(vcl);
  CVEC.CSCA_MUL3(u,v,w);
  MakeImmutable(u);   # all CScas are immutable
  return u;
end);

InstallOtherMethod( InverseSameMutability, "for a csca", 
  [IsScalar and IsCScaRep],
  function(v)
  local u,vcl;
  vcl := CVEC.CVecClass(v);
  u := CVEC.NEW(vcl);
  MakeImmutable(u);   # all CScas are immutable
  return CVEC.CSCA_INV2(u,v);   # this might be fail
end);
InstallOtherMethod( InverseImmutable, "for a csca", 
  [IsScalar and IsCScaRep],
  function(v)
  local u,vcl;
  vcl := CVEC.CVecClass(v);
  u := CVEC.NEW(vcl);
  MakeImmutable(u);   # all CScas are immutable
  return CVEC.CSCA_INV2(u,v);   # this might be fail
end);

InstallOtherMethod( \/, "for cscas", 
  [IsScalar and IsCScaRep, IsScalar and IsCScaRep],
  function(v,w)
  local ww;
  ww := InverseImmutable(w);
  if ww = fail then
      Error("CSCA.\\/: cannot invert w");
      return fail;
  fi;
  return v*ww;
end);
  
# Zero:

InstallOtherMethod( ZeroSameMutability, "for a csca", [IsScalar and IsCScaRep],
  function(v)
  local u,vcl;
  vcl := CVEC.CVecClass(v);
  return vcl![5];
end);
InstallOtherMethod( ZeroImmutable, "for a csca", [IsScalar and IsCScaRep],
  function(v)
  local u,vcl;
  vcl := CVEC.CVecClass(v);
  return vcl![5];
end);
InstallOtherMethod( ZeroSameMutability, "for a cscaclass", 
  [IsCVecClass],
  function(vcl)
    if vcl![2] <> -1 then
        Error("ZeroSameMutability: not defined for a cvec class");
    fi;
  return vcl![5];
end);
InstallOtherMethod( ZeroImmutable, "for a cscaclass", 
  [IsCVecClass],
  function(vcl)
    if vcl![2] <> -1 then
        Error("ZeroImmutable: not defined for a cvec class");
    fi;
  return vcl![5];
end);

# One:

InstallOtherMethod( OneSameMutability, "for a csca", [IsScalar and IsCScaRep],
  function(v)
  local u,vcl;
  vcl := CVEC.CVecClass(v);
  return vcl![6];
end);
InstallOtherMethod( OneImmutable, "for a csca", [IsScalar and IsCScaRep],
  function(v)
  local u,vcl;
  vcl := CVEC.CVecClass(v);
  return vcl![6];
end);
InstallOtherMethod( OneSameMutability, "for a csca class", [IsCVecClass],
  function(c)
    if c![2] <> -1 then
        Error("OneSameMutability: not defined for a cvec class");
    fi;
    return c![6];
  end);
InstallOtherMethod( OneImmutable, "for a csca class", [IsCVecClass],
  function(c)
    if c![2] <> -1 then
        Error("OneImmutable: not defined for a cvec class");
    fi;
    return c![6];
  end);

# IsOne:

InstallOtherMethod( IsOne, "for a csca", [IsScalar and IsCScaRep],
  function(v)
  local vcl;
  vcl := CVEC.CVecClass(v);
  return v = vcl![6];
end);


# Characteristic:

InstallOtherMethod( Characteristic, "for a csca", [IsScalar and IsCScaRep],
  function(v)
  local vcl;
  vcl := CVEC.CVecClass(v);
  return vcl![1]![1];
end);

# DegreeFFE:

InstallOtherMethod( DegreeFFE, "for a csca", [IsScalar and IsCScaRep],
  function(v)
  local vcl;
  vcl := CVEC.CVecClass(v);
  return vcl![1]![2];
end);

# Square roots:

# We implement an algorithm described by F. Wang, Y. Nogami and Y. Morikawa
# in "A High-Speed Square Root Computation in Finite Fields with Application
# to Elliptic Curve Cryptosystem", Memoirs of the Faculty of Engeneering,
# Okayama University, Vol. 39, pp. 82--92, January, 2005.
# This is based on ideas from the "SMART" algorithm.
InstallOtherMethod( Sqrt, "for a csca", [IsScalar and IsCScaRep],
  function(x)
  local T,au,c,e,i,k,me,mu,s,sigma,t,tau,xcl,xl,xs,xsm1d2,xsp1d2,y,z;
  # We have some precomputed values:
  xcl := CVEC.CVecClass(x);
  e := xcl![6];
  me := -e;
  s := xcl![7];
  T := xcl![8];
  z := xcl![9];
  c := xcl![10];
  
  # Now we can start:
  xsm1d2 := x^((s-1)/2);
  xsp1d2 := xsm1d2*x;
  xs := xsm1d2*xsp1d2;
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
end);

# PrimitiveRoot:

InstallOtherMethod( PrimitiveRoot, "for a csca class", [IsCVecClass],
  function(c)
  if c![2] <> -1 then
      Error("PrimitiveRoot: not defined for cvec class");
  fi;
  return c![9];
end);
InstallOtherMethod( PrimitiveRoot, "for a csca", [IsScalar and IsCScaRep],
  function(x)
  local xcl;
  xcl := CVEC.CVecClass(x);
  return xcl![9];
end);

#############################################################################
# Matrices:
#############################################################################

InstallMethod( CMat, "for a list of cvecs and a cvec", [IsList, IsCVecRep],
  function(l,v)
    return CMat(l,CVEC.CVecClass(v),true);
  end);

InstallMethod( CMat, "for a list of cvecs, a cvec, and a boolean value",
  [IsList, IsCVecRep, IsBool],
  function(l,v,checks)
    return CMat(l,CVEC.CVecClass(v),checks);
  end);

InstallMethod( CMat, "for a list of cvecs", [IsList],
  function(l)
    local c;
    if Length(l) = 0 or not(IsBound(l[1])) then
        Error("CMat: Cannot use one-argument version with empty list");
        return fail;
    fi;
    c := CVEC.CVecClass(l[1]);
    return CMat(l,c,true);
  end);

InstallMethod( CMat, "for a list of cvecs, and a boolean value", 
  [IsList, IsBool],
  function(l,checks)
    local c;
    if Length(l) = 0 or not(IsBound(l[1])) then
        Error("CMat: Cannot use two-argument version with empty list and bool");
        return fail;
    fi;
    c := CVEC.CVecClass(l[1]);
    return CMat(l,c,checks);
  end);

InstallMethod( CMat, "for a list of cvecs and a cvecclass", 
  [IsList, IsCVecClass],
  function(l,c)
    return CMat(l,c,true);
  end);

InstallMethod( CMat, "for a list of cvecs, a cvecclass, and a boolean value", 
  [IsList, IsCVecClass, IsBool],
  function(l,c,checks)
    return CMat(l,c,checks);
  end);

InstallMethod( CMat, "for a compressed GF2 matrix",
  [IsList and IsGF2MatrixRep],
  function(m)
  local c,i,l,v;
  l := 0*[1..Length(m)+1];
  Unbind(l[1]);
  c := CVEC.NewCVecClass(2,1,Length(m[1]));
  for i in [1..Length(m)] do
      v := ShallowCopy(m[i]);
      Add(v,fail);   # this unpacks
      Unbind(v[Length(v)]);
      l[i+1] := CVec(v,c);
  od;
  return CVEC.CMatMaker(l,c);
end);

InstallMethod( CMat, "for a compressed 8bit matrix",
  [IsList and Is8BitMatrixRep],
  function(m)
  local c,i,l,pd,v;
  l := 0*[1..Length(m)+1];
  Unbind(l[1]);
  pd := Factors(Size(DefaultFieldOfMatrix(m)));
  c := CVEC.NewCVecClass(pd[1],Length(pd),Length(m[1]));
  for i in [1..Length(m)] do
      v := ShallowCopy(m[i]);
      Add(v,fail);   # this unpacks
      Unbind(v[Length(v)]);
      l[i+1] := CVec(v,c);
  od;
  return CVEC.CMatMaker(l,c);
end);

CVEC.CMatMaker := function(l,cl)
    # Makes a new CMat, given a list l with a hole in the first place
    local m,ty;
    if Length(l) > 0 then
        m := rec(rows := l, len := Length(l)-1, vecclass := cl);
    else
        m := rec(rows := l, len := 0, vecclass := cl);
    fi;
    m.scaclass := cl![5];
    m.greasehint := cl![1]![8];   # this is the current bestgrease
    ty := NewType(CollectionsFamily(CollectionsFamily(cl![1]![14])),
                  IsMatrix and IsOrdinaryMatrix and HasLength and
                  IsComponentObjectRep and IsCMatRep and IsMutable);
    return Objectify(ty,m);
end;

InstallMethod( CMat, "for a list of cvecs, a cvec class, and a boolean value", 
  [IsList,IsCVecClass,IsBool],
  function(l,cl,dochecks)
    local v;
    if dochecks then
        for v in [1..Length(l)] do
            if not(IsBound(l[v])) or not(IsCVecRep(l[v])) or 
               not(IsIdenticalObj(CVEC.CVecClass(l[v]),cl)) then
                Error("CVEC.CMat: Not all list entries are correct vectors");
                return fail;
            fi;
        od;
    fi;
    Add(l,fail,1);
    Unbind(l[1]);
    return CVEC.CMatMaker(l,cl);
  end);

# Some methods to make special matrices:

CVEC.ZeroMat := function(arg)
  local c,d,i,l,p,x,y;
  if Length(arg) = 2 then
      y := arg[1];
      c := arg[2];   # this must be a cvec class
      if not(IsInt(y)) and not(IsCVecClass(c)) then
          Error("Usage: CVEC.ZeroMat( rows, cvecclass)");
          return;
      fi;
  elif Length(arg) = 4 then
      y := arg[1];
      x := arg[2];
      p := arg[3];
      d := arg[4];
      if not(IsInt(y) and y >= 0) or
         not(IsInt(x) and x >= 0) or
         not(IsPosInt(p) and IsPrime(p)) or
         not(IsPosInt(d) and d < CVEC.MAXDEGREE) then
          Error("Usage: CVEC.ZeroMat( rows, cols, p, d )");
          return;
      fi;
      c := CVEC.NewCVecClass(p,d,x);
  else
      Error("Usage: CVEC.ZeroMat( rows, [ cvecclass | cols, p, d ] )");
      return;
  fi;
  l := 0*[1..y+1];
  Unbind(l[1]);
  for i in [1..y] do
      l[i+1] := CVEC.NEW(c);
  od;
  return CVEC.CMatMaker(l,c);
end;

CVEC.IdentityMat := function(arg)
  local c,d,i,l,p,y;
  if Length(arg) = 1 then
      c := arg[1];   # this must be a cvec class
      if not(IsCVecClass(c)) then
          Error("Usage: CVEC.IdentityMat(cvecclass)");
          return;
      fi;
  elif Length(arg) = 3 then
      y := arg[1];
      p := arg[2];
      d := arg[3];
      if not(IsInt(y) and y >= 0) or
         not(IsPosInt(p) and IsPrime(p)) or
         not(IsPosInt(d) and d < CVEC.MAXDEGREE) then
          Error("Usage: CVEC.IdentityMat( rows, p, d )");
          return;
      fi;
      c := CVEC.NewCVecClass(p,d,y);
  else
      Error("Usage: CVEC.IdentityMat( [ cvecclass | rows, p, d ] )");
      return;
  fi;
  l := 0*[1..y+1];
  Unbind(l[1]);
  for i in [1..y] do
      l[i+1] := CVEC.NEW(c);
      l[i+1][i] := 1;   # note that this works for all fields!
  od;
  return CVEC.CMatMaker(l,c);
end;

CVEC.RandomMat := function(arg)
  local c,d,i,j,l,li,p,q,x,y;
  if Length(arg) = 2 then
      y := arg[1];
      c := arg[2];   # this must be a cvec class
      if not(IsInt(y)) and not(IsCVecClass(c)) then
          Error("Usage: CVEC.RandomMat( rows, cvecclass)");
          return;
      fi;
      x := c![2];
      d := c![1]![2];   # used later on
      q := c![1]![3];  
  elif Length(arg) = 4 then
      y := arg[1];
      x := arg[2];
      p := arg[3];
      d := arg[4];
      q := p^d;
      if not(IsInt(y) and y >= 0) or
         not(IsInt(x) and x >= 0) or
         not(IsPosInt(p) and IsPrime(p)) or
         not(IsPosInt(d) and d < CVEC.MAXDEGREE) then
          Error("Usage: CVEC.RandomMat( rows, cols, p, d )");
          return;
      fi;
      c := CVEC.NewCVecClass(p,d,x);
  else
      Error("Usage: CVEC.RandomMat( rows, [ cvecclass | cols, p, d ] )");
      return;
  fi;
  l := 0*[1..y+1];
  Unbind(l[1]);
  if c![1]![13] <= 1 then    # q is an immediate integer
      li := 0*[1..x];
      for i in [1..y] do
          l[i+1] := CVEC.NEW(c);
          for j in [1..x] do
              li[j] := Random([0..q-1]);
          od;
          CVEC.INTREP_TO_CVEC(li,l[i+1]);
      od;
  else    # big scalars!
      li := 0*[1..x*d];
      for i in [1..y] do
          l[i+1] := CVEC.NEW(c);
          for j in [1..x*d] do
              li[j] := Random([0..p-1]);
          od;
          CVEC.INTREP_TO_CVEC(li,l[i+1]);
      od;
  fi;
  return CVEC.CMatMaker(l,c);
end;

# PostMakeImmutable to make subobjects immutable:

InstallMethod( PostMakeImmutable, "for a cmat", [IsCMatRep and IsMatrix],
  function(m)
    MakeImmutable(m!.rows);
  end);

# Elementary list operations for our matrices:

InstallOtherMethod( Add, "for a cmat, and a cvec",
  [IsCMatRep and IsMatrix and IsMutable, IsCVecRep],
  function(m,v)
    if not(IsIdenticalObj(CVEC.CVecClass(v),m!.vecclass)) then
        Error("Add: only correct cvecs allowed in this matrix");
        return fail;
    fi;
    m!.len := m!.len+1;
    m!.rows[m!.len+1] := v;
  end);
InstallOtherMethod( Add, "for a cmat, a cvec, and a position",
  [IsCMatRep and IsMatrix and IsMutable, IsCVecRep, IsPosInt],
  function(m,v,pos)
    if not(IsIdenticalObj(CVEC.CVecClass(v),m!.vecclass)) then
        Error("Add: only correct cvecs allowed in this matrix");
        return fail;
    fi;
    if pos < 1 or pos > m!.len+1 then
        Error("Add: position not possible because denseness");
    fi;
    m!.len := m!.len+1;
    Add(m!.rows,v,pos+1);
  end);

InstallOtherMethod( Remove, "for a cmat, and a position",
  [IsCMatRep and IsMatrix and IsMutable, IsPosInt],
  function(m,pos)
    if pos < 1 or pos > m!.len then
        Error("Remove: position not possible");
        return fail;
    fi;
    m!.len := m!.len-1;
    return Remove(m!.rows,pos+1);
  end);

InstallOtherMethod( \[\], "for a cmat, and a position", 
  [IsCMatRep and IsMatrix, IsPosInt],
  function(m,pos)
    if pos < 1 or pos > m!.len then
        Error("\\[\\]: illegal position");
        return fail;
    fi;
    return m!.rows[pos+1];
  end);

InstallOtherMethod( \[\]\:\=, "for a cmat, a position, and a cvec",
  [IsCMatRep and IsMatrix and IsMutable, IsPosInt, IsCVecRep],
  function(m,pos,v)
    if pos < 1 or pos > m!.len+1 then
        Error("\\[\\]\\:\\=: illegal position");
    fi;
    if not(IsIdenticalObj(CVEC.CVecClass(v),m!.vecclass)) then
        Error("\\[\\]\\:\\=: can only assign cvecs to cmat");
    fi;
    if pos = m!.len+1 then
        m!.len := m!.len + 1;
    fi;
    m!.rows[pos+1] := v;
  end);

InstallOtherMethod( \{\}, "for a cmat, and a list",
  [IsCMatRep and IsMatrix, IsHomogeneousList],
  function(m,li)
    local l;
    l := m!.rows{li+1};
    return CMat(l,m!.vecclass,false);
  end);

InstallOtherMethod( \{\}\:\=, "for a cmat, a homogeneous list, and a cmat",
  [IsCMatRep and IsMatrix, IsHomogeneousList, IsCMatRep and IsMatrix],
  function(m,l,n)
    local i;
    if not(IsIdenticalObj(m!.vecclass,n!.vecclass)) then
        Error("{}:= : cmats not compatible");
        return;
    fi;
    for i in [1..Length(l)] do
        m!.rows[l[i]+1] := n!.rows[i+1];
    od;
  end);

InstallOtherMethod( Length, "for a cmat",
  [IsCMatRep and IsMatrix],
  function(m) return m!.len; end);

InstallOtherMethod( ShallowCopy, "for a cmat",
  [IsCMatRep and IsMatrix],
  function(m) return CVEC.CMatMaker(ShallowCopy(m!.rows),m!.vecclass); end);

InstallOtherMethod( Collected, "for a cmat",
  [IsCMatRep and IsMatrix],
  function(m)
    return Collected(m!.rows{[2..m!.len+1]});
  end);

InstallOtherMethod( DuplicateFreeList, "for a cmat",
  [IsCMatRep and IsMatrix],
  function(m)
    local l;
    l := DuplicateFreeList(m!.rows);
    return CMat(l,m!.vecclass,false);
  end);

InstallOtherMethod( Append, "for two cmats",
  [IsCMatRep and IsMatrix and IsMutable, IsCMatRep and IsMatrix],
  function(m1,m2)
      local i;
      if not(IsIdenticalObj(m1!.vecclass,m2!.vecclass)) then
          Error("Append: Incompatible matrices");
          return fail;
      fi;
      for i in [2..m2!.len+1] do
          Add(m1!.rows,m2!.rows[i]);
      od;
      m1!.len := m1!.len + m2!.len;
  end);

InstallOtherMethod( FilteredOp, "for a cmat and a function",
  [IsCMatRep and IsMatrix, IsFunction],
  function(m,f)
    local l;
    l := Filtered(m!.rows,f);
    return CMat(l,m!.vecclass,false);
  end);

InstallOtherMethod( UNB_LIST, "for a cmat and a position",
  [IsCMatRep and IsMatrix and IsMutable, IsPosInt],
  function(m,pos)
    if pos = m!.len then
        Unbind(m!.rows[m!.len+1]);
        m!.len := m!.len-1;
    else
        Error("Unbind: not possible for cmats except last entry");
    fi;
  end);

CVEC.CopySubmatrix := function(src,dst,srcli,dstli,srcpos,len,dstpos)
  local i;
  if not(IsIdenticalObj(src!.scaclass,dst!.scaclass)) then
      Error("CVEC.CopySubmatrix: cmats not over common field");
      return;
  fi;
  if Length(srcli) <> Length(dstli) then
      Error("CVEC.CopySubmatrix: line lists do not have equal lengths");
      return;
  fi;
  if srcpos < 1 or srcpos+len-1 > src!.vecclass![2] or len <= 0 then
      Error("CVEC.CopySubmatrix: source area not valid");
      return;
  fi;
  if dstpos < 1 or dstpos+len-1 > dst!.vecclass![2] then
      Error("CVEC.CopySubmatrix: destination area not valid");
      return;
  fi;
  for i in [1..Length(srcli)] do
      CVEC.SLICE(src!.rows[srcli[i]+1],dst!.rows[dstli[i]+1],
                 srcpos,len,dstpos);
  od;
end;

# Arithmetic for matrices:

InstallOtherMethod( \+, "for cmats", 
  [IsCMatRep and IsMatrix, IsCMatRep and IsMatrix],
  function(m,n)
    local l,res;
    if not(IsIdenticalObj(m!.vecclass,n!.vecclass)) then
        Error("\\+: cmats not compatible");
    fi;
    if m!.len <> n!.len then
        Error("\\+: cmats do not have equal length");
    fi;
    l := m!.rows + n!.rows;
    res := CVEC.CMatMaker(l,m!.vecclass);
    if not(IsMutable(m)) and not(IsMutable(n)) then
        MakeImmutable(res);
    fi;
    return res;
  end);

InstallOtherMethod( \-, "for cmats", 
  [IsCMatRep and IsMatrix, IsCMatRep and IsMatrix],
  function(m,n)
    local l,res;
    if not(IsIdenticalObj(m!.vecclass,n!.vecclass)) then
        Error("\\-: cmats not compatible");
    fi;
    if m!.len <> n!.len then
        Error("\\-: cmats do not have equal length");
    fi;
    l := m!.rows - n!.rows;
    res := CVEC.CMatMaker(l,m!.vecclass);
    if not(IsMutable(m)) and not(IsMutable(n)) then
        MakeImmutable(res);
    fi;
  end);

InstallOtherMethod( AdditiveInverseSameMutability, "for a cmat",
  [IsCMatRep and IsMatrix],
  function(m)
    local l,res;
    l := -m!.rows;
    res := CVEC.CMatMaker(l,m!.vecclass);
    if not(IsMutable(m)) then
        MakeImmutable(res);
    fi;
    return res;
  end);
InstallOtherMethod( AdditiveInverseMutable, "for a cmat",
  [IsCMatRep and IsMatrix],
  function(m)
    local l;
    l := -m!.rows;
    return CVEC.CMatMaker(l,m!.vecclass);
  end);

InstallOtherMethod( ZeroImmutable, "for a cmat",
  [IsCMatRep and IsMatrix],
  function(m)
    local i,l,res,v;
    l := [];
    v := CVEC.NEW(m!.vecclass);
    MakeImmutable(v);
    for i in [2..m!.len+1] do
        l[i] := v;
    od;
    res := CVEC.CMatMaker(l,m!.vecclass);
    MakeImmutable(res);
    return res;
  end);
InstallOtherMethod( ZeroMutable, "for a cmat",
  [IsCMatRep and IsMatrix],
  function(m)
    local i,l;
    l := [];
    for i in [2..m!.len+1] do
        l[i] := CVEC.NEW(m!.vecclass);
    od;
    return CVEC.CMatMaker(l,m!.vecclass);
  end);
InstallOtherMethod( ZeroSameMutability, "for a cmat",
  [IsCMatRep and IsMatrix],
  function(m)
    if IsMutable(m) then
        return ZeroMutable(m);
    else
        return ZeroImmutable(m);
    fi;
  end);
    
InstallOtherMethod( OneMutable, "for a cmat",
  [IsCMatRep and IsMatrix],
  function(m)
    local i,l,one,v,w;
    if m!.vecclass![2] <> m!.len then
        Error("OneMutable: cmat is not square");
        return fail;
    fi;
    v := CVEC.NEW(m!.vecclass);
    l := 0*[1..m!.len+1];
    one := One(m!.scaclass);
    for i in [1..m!.len] do
        w := ShallowCopy(v);
        w[i] := one;
        l[i+1] := w;
    od;
    Unbind(l[1]);
    return CVEC.CMatMaker(l,m!.vecclass);
  end);
InstallOtherMethod( OneSameMutability, "for a cmat",
  [IsCMatRep and IsMatrix],
  function(m)
    local n;
    n := OneMutable(m);
    if not(IsMutable(m)) then
        MakeImmutable(n);
    fi;
    return n;
  end);

# Multiplication with scalars:

CVEC.MATRIX_TIMES_SCALAR := function(m,s)
    local i,l,res;
    l := 0*[1..m!.len+1];
    for i in [2..m!.len+1] do l[i] := s * m!.rows[i]; od;
    Unbind(l[1]);
    res := CVEC.CMatMaker(l,m!.vecclass);
    if not(IsMutable(m)) then
        MakeImmutable(res);
    fi;
    return res;
end;
InstallOtherMethod( \*, "for a cmat", [IsCMatRep and IsMatrix, IsInt], 
  CVEC.MATRIX_TIMES_SCALAR);
InstallOtherMethod( \*, "for a cmat", [IsCMatRep and IsMatrix, IsFFE], 
  CVEC.MATRIX_TIMES_SCALAR);
InstallOtherMethod( \*, "for a cmat", 
  [IsCMatRep and IsMatrix, IsScalar and IsCScaRep], 
  CVEC.MATRIX_TIMES_SCALAR);
InstallOtherMethod( \*, "for a cmat", [IsInt,IsCMatRep and IsMatrix], 
  function(s,m) return CVEC.MATRIX_TIMES_SCALAR(m,s); end);
InstallOtherMethod( \*, "for a cmat", [IsFFE,IsCMatRep and IsMatrix], 
  function(s,m) return CVEC.MATRIX_TIMES_SCALAR(m,s); end);
InstallOtherMethod( \*, "for a cmat", 
  [IsScalar and IsCScaRep,IsCMatRep and IsMatrix], 
  function(s,m) return CVEC.MATRIX_TIMES_SCALAR(m,s); end);


# Comparison:

InstallOtherMethod( \=, "for two cmats",
  [IsCMatRep and IsMatrix, IsCMatRep and IsMatrix],
  function(m,n)
    if not(IsIdenticalObj(m!.vecclass,n!.vecclass)) or m!.len <> n!.len then
        return false;
    fi;
    return m!.rows = n!.rows;
  end);

InstallOtherMethod( \<, "for two cmats",
  [IsCMatRep and IsMatrix, IsCMatRep and IsMatrix],
  function(m,n)
    if not(IsIdenticalObj(m!.vecclass,n!.vecclass)) or m!.len <> n!.len then
        return fail;
    fi;
    return m!.rows < n!.rows;
  end);

InstallOtherMethod( IsZero, "for a cmat", [IsCMatRep and IsMatrix],
  function(m)
    return ForAll(m!.rows,IsZero);
  end);


# Access to the base field:

InstallOtherMethod( DegreeFFE, "for a cmat", [IsCMatRep and IsMatrix],
  function(m)
    return m!.vecclass![1]![2];
  end);
    
InstallOtherMethod( Characteristic, "for a cmat", [IsCMatRep and IsMatrix],
  function(m)
    return m!.vecclass![1]![1];
  end);
    
InstallMethod( BaseField, "for a cmat", [IsCMatRep and IsMatrix],
  function(m)
    local c,p,d;
    c := m!.vecclass;
    p := c![1]![1];
    d := c![1]![2];
    if p^d <= MAXSIZE_GF_INTERNAL then
        return GF(p,d);
    else
        return c![5];
    fi;
  end);
    
#############################################################################
# Arithmetic between vectors and matrices, especially multiplication:
#############################################################################
    
InstallOtherMethod(\*, "for a cvec and a cmat, without greasing",
  [IsCVecRep, IsCMatRep and IsMatrix],
  function(v,m)
    local i,res,vcl,s,z;
    vcl := CVEC.CVecClass(v);
    if not(IsIdenticalObj(vcl![5],m!.scaclass)) then
        Error("\\*: incompatible base fields");
    fi;
    if Length(v) <> m!.len then
        Error("\\*: lengths not equal");
    fi;
    res := CVEC.NEW(m!.vecclass);  # the result
    CVEC.PROD_CVEC_CMAT_NOGREASE(res,v,m!.rows);
    if not(IsMutable(v)) then
        MakeImmutable(res);
    fi;
    return res;
  end);
 
InstallOtherMethod(\*, "for a cvec and a greased cmat",
  [IsCVecRep, IsCMatRep and IsMatrix and HasGreaseTab],
  function(v,m)
    local i,res,vcl,l,pos,val;
    vcl := CVEC.CVecClass(v);
    if not(IsIdenticalObj(vcl![5],m!.scaclass)) then
        Error("\\*: incompatible base fields");
    fi;
    if Length(v) <> m!.len then
        Error("\\*: lengths not equal");
    fi;
    res := CVEC.NEW(m!.vecclass);  # the result
    CVEC.PROD_CVEC_CMAT_GREASED(res,v,m!.greasetab,m!.spreadtab,m!.greaselev);
    if not(IsMutable(v)) then
        MakeImmutable(res);
    fi;
    return res;
  end);
 
InstallOtherMethod(\*, "for two cmats, second one not greased",
  [IsCMatRep and IsMatrix, IsCMatRep and IsMatrix],
  function(m,n)
    local greasetab,i,j,l,lev,res,spreadtab,tablen,vcl,q;
    if not(IsIdenticalObj(m!.scaclass,n!.scaclass)) then
        Error("\\*: incompatible base fields");
    fi;
    if m!.vecclass![2] <> n!.len then
        Error("\\*: lengths not fitting");
    fi;
    # First make a new matrix:
    l := 0*[1..m!.len+1];
    vcl := n!.vecclass;
    for i in [2..m!.len+1] do
        l[i] := CVEC.NEW(vcl);
    od;
    Unbind(l[1]);
    res := CVEC.CMatMaker(l,n!.vecclass);
    if m!.len > 0 then
        q := vcl![1]![3];
        lev := n!.greasehint;
        if lev = 0 or n!.len * (q-1) * lev <= (n!.len + vcl![1]![9]) * q then   
            # no greasing at all!
            CVEC.PROD_CMAT_CMAT_NOGREASE2(l,m!.rows,n!.rows);
            # we use version 2, which unpacks full rows of m instead of
            # extracting single field entries.
        else
            spreadtab := CVEC.MakeSpreadTab(vcl![1]![1],    # p
                                            vcl![1]![2],    # d,
                                            lev,            # bestgrease
                                            vcl![1]![5]);   # bitsperel
            tablen := vcl![1]![3]^lev;
            greasetab := 0*[1..tablen+2];
            for j in [1..tablen+2] do
                greasetab[j] := CVEC.NEW(n!.vecclass);
            od;
            CVEC.PROD_CMAT_CMAT_WITHGREASE(l,m!.rows,n!.rows,greasetab,
                                           spreadtab,lev);
        fi;
    fi;
    return res;
  end);

InstallOtherMethod(\*, "for two cmats, second one greased",
  [IsCMatRep and IsMatrix, IsCMatRep and IsMatrix and HasGreaseTab],
  function(m,n)
    local i,l,res,vcl;
    if not(IsIdenticalObj(m!.scaclass,n!.scaclass)) then
        Error("\\*: incompatible base fields");
    fi;
    if m!.vecclass![2] <> n!.len then
        Error("\\*: lengths not fitting");
    fi;
    # First make a new matrix:
    l := 0*[1..m!.len+1];
    vcl := n!.vecclass;
    for i in [2..m!.len+1] do
        l[i] := CVEC.NEW(vcl);
        #CVEC.MAKEZERO(l[i]);
        # not necessary, since GASMAN only gives empty bags
    od;
    Unbind(l[1]);
    res := CVEC.CMatMaker(l,n!.vecclass);
    if m!.len > 0 then
        CVEC.PROD_CMAT_CMAT_GREASED(l,m!.rows,n!.greasetab,n!.spreadtab,
                                    n!.len,n!.greaselev);
    fi;
    if not(IsMutable(m)) and not(IsMutable(n)) then
        MakeImmutable(res);
    fi;
    return res;
  end);


#############################################################################
# Greasing:
#############################################################################

InstallOtherMethod( GreaseMat, "for a cmat",
  [IsMatrix and IsCMatRep],
  function(m)
    if m!.vecclass![1]![8] = 0 then
        Info(InfoWarning,1,"GreaseMat: bestgrease is 0, we do not grease");
        return;
    fi;
    GreaseMat(m,m!.vecclass![1]![8]);
  end);

InstallMethod( GreaseMat, "for a cmat, and a level", 
  [IsMatrix and IsCMatRep, IsInt],
  function(m,l)
    local bitsperel,d,dim,e,f,i,j,k,mm,nrblocks,p,pot,q,tablen;
    f := m!.vecclass![1];   # the field info
    bitsperel := f![5];
    p := f![1];
    d := f![2];
    q := f![3];
    nrblocks := QuoInt(m!.len+l-1,l);  # we do grease the last <l rows!
    tablen := q^l;  # = p^(d*l)
    m!.greaselev := l;
    m!.greaseblo := nrblocks;
    m!.greasetab := 0*[1..nrblocks];
    for i in [1..nrblocks] do
        m!.greasetab[i] := 0*[1..tablen+2];
        for j in [1..tablen+2] do
            m!.greasetab[i][j] := CVEC.NEW(m!.vecclass);
        od;
        CVEC.FILL_GREASE_TAB(m!.rows,2+(i-1)*l,l,m!.greasetab[i],tablen,1);
    od;

    m!.spreadtab := CVEC.MakeSpreadTab(p,d,l,bitsperel);

    # Finally change the type:
    SetFilterObj(m,HasGreaseTab);
  end); 

CVEC.SpreadTabCache := [];

CVEC.MakeSpreadTab := function(p,d,l,bitsperel)
    # Make up the spreadtab (EXTRACT values are 2^bitsperel-adic
    # expansions with digits only between 0 and p-1):
    local dim,e,i,j,k,mm,pot,spreadtab;
    if IsBound(CVEC.SpreadTabCache[p]) and
       IsBound(CVEC.SpreadTabCache[p][d]) and
       IsBound(CVEC.SpreadTabCache[p][d][l]) then
        return CVEC.SpreadTabCache[p][d][l];
    fi;
    spreadtab := [];
    dim := d*l;
    e := 0*[1..dim+1];
    j := 0;
    mm := 2^bitsperel;
    for i in [0..p^dim-1] do
        spreadtab[j+1] := i+1;
        # Now increment expansion as a p-adic expansion and modify
        # j accordingly as the value of the corresponding m-adic
        # expansion:
        k := 1;
        pot := 1;
        while true do 
            e[k] := e[k] + 1;
            j := j + pot;
            if e[k] < p then break; fi;
            e[k] := 0;
            j := j - p*pot;
            k := k + 1;
            pot := pot * mm;
        od;
    od;
    if not(IsBound(CVEC.SpreadTabCache[p])) then
        CVEC.SpreadTabCache[p] := [];
    fi;
    if not(IsBound(CVEC.SpreadTabCache[p][d])) then
        CVEC.SpreadTabCache[p][d] := [];
    fi;
    CVEC.SpreadTabCache[p][d][l] := spreadtab;
    return spreadtab;
end;

InstallMethod( UnGreaseMat, "for a cmat",
  [IsMatrix and IsCMatRep],
  function(m)
    ResetFilterObj(m,HasGreaseTab);
    Unbind(m!.greasetab);
    Unbind(m!.greaselev);
    Unbind(m!.greaseblo);
    Unbind(m!.spreadtab);
  end);

CVEC.OptimizeGreaseHint := function(m,nr)
  local l,li,q;
  q := m!.vecclass![1]![3];
  li := [QuoInt(nr*(q-1)*m!.len + (q-1),q)];
  l := 1;
  while l < 12 do
      li[l+1] := QuoInt(m!.len + (l-1),l)*(nr+q^l);
      if l > 1 and li[l+1] > li[l] then break; fi;
      l := l + 1;
  od;
  if li[l] < li[1] then
      m!.greasehint := l-1;
  else
      m!.greasehint := 0;
  fi;
  #Print("OptimizeGreaseHint: ",li," ==> ",m!.greasehint,"\n");
end;

#############################################################################
# I/O for Matrices:
#############################################################################

CVEC.64BIT_NUMBER_TO_STRING_LITTLE_ENDIAN := function(n)
  local i,s;
  s := "        ";
  for i in [1..8] do
      s[i] := CHAR_INT(RemInt(n,256));
      n := QuoInt(n,256);
  od;
  return s;
end;

CVEC.WriteMat := function(f,m)
  local buf,c,chead,dhead,header,i,magic,phead,rhead;
  if not(IsFile(f)) then
      Error("CVEC.WriteMat: first argument must be a file");
      return fail;
  fi;
  if not(IsCMatRep(m)) then
      Error("CVEC.WriteMat: second argument must be a cmat");
      return fail;
  fi;
  c := m!.vecclass;
  Info(InfoCVec,2,"CVEC.WriteMat: Writing ",m!.len,"x",c![2]," matrix over GF(",
       c![1]![1],",",c![1]![2],")");
  # Make the header:
  magic := "GAPCMat1";
  phead := CVEC.64BIT_NUMBER_TO_STRING_LITTLE_ENDIAN(c![1]![1]);
  dhead := CVEC.64BIT_NUMBER_TO_STRING_LITTLE_ENDIAN(c![1]![2]);
  rhead := CVEC.64BIT_NUMBER_TO_STRING_LITTLE_ENDIAN(m!.len);
  chead := CVEC.64BIT_NUMBER_TO_STRING_LITTLE_ENDIAN(c![2]);
  header := Concatenation(magic,phead,dhead,rhead,chead);
  if IO.Write(f,header) <> 40 then
      Info(InfoCVec,1,"CVEC.WriteMat: Write error during writing of header");
      return fail;
  fi;
  buf := "";  # will be made longer automatically
  for i in [1..m!.len] do
      CVEC.CVEC_TO_EXTREP(m!.rows[i+1],buf);
      if IO.Write(f,buf) <> Length(buf) then
          Info(InfoCVec,1,"CVEC.WriteMat: Write error");
          return fail;
      fi;
  od;
  return true;
end;

CVEC.WriteMatToFile := function(fn,m)
  local f;
  f := IO.File(fn,"w");
  if f = fail then
      Info(InfoCVec,1,"CVEC.WriteMatToFile: Cannot create file");
      return fail;
  fi;
  if CVEC.WriteMat(f,m) = fail then return fail; fi;
  if IO.Close(f) = fail then
      Info(InfoCVec,1,"CVEC.WriteMatToFile: Cannot close file");
      return fail;
  fi;
  return true;
end;

CVEC.WriteMatsToFile := function(fnpref,l)
  local i;
  if not(IsString(fnpref)) then
      Error("CVEC.WriteMatsToFile: fnpref must be a string");
      return fail;
  fi;
  if not(IsList(l)) then
      Error("CVEC.WriteMatsToFile: l must be list");
      return fail;
  fi;
  for i in [1..Length(l)] do
      if CVEC.WriteMatToFile(Concatenation(fnpref,String(i)),l[i]) = fail then
          return fail;
      fi;
  od;
  return true;
end;

CVEC.STRING_LITTLE_ENDIAN_TO_64BIT_NUMBER := function(s)
  local i,n;
  n := 0;
  for i in [8,7..1] do
      n := n * 256 + INT_CHAR(s[i]);
  od;
  return n;
end;

CVEC.ReadMat := function(f)
  local buf,c,cols,d,header,i,len,m,p,rows;
  if not(IsFile(f)) then
      Error("CVEC.ReadMat: first argument must be a file");
      return fail;
  fi;
  header := IO.Read(f,40);
  if Length(header) < 40 then
      Info(InfoCVec,1,"CVEC.ReadMat: Cannot read header");
      return fail;
  fi;

  # Check and process the header:
  if header{[1..8]} <> "GAPCMat1" then
      Info(InfoCVec,1,"CVEC.ReadMat: Magic of header incorrect");
      return fail;
  fi;
  p := CVEC.STRING_LITTLE_ENDIAN_TO_64BIT_NUMBER(header{[9..16]});
  d := CVEC.STRING_LITTLE_ENDIAN_TO_64BIT_NUMBER(header{[17..24]});
  rows := CVEC.STRING_LITTLE_ENDIAN_TO_64BIT_NUMBER(header{[25..32]});
  cols := CVEC.STRING_LITTLE_ENDIAN_TO_64BIT_NUMBER(header{[33..40]});
  Info(InfoCVec,2,"CVEC.ReadMat: Reading ",rows,"x",cols," matrix over GF(",
       p,",",d,")");
   
  c := CVEC.NewCVecClass(p,d,cols);
  m := CVEC.ZeroMat(rows,c);
  buf := "";  # will be made longer automatically
  if rows > 0 then
      CVEC.CVEC_TO_EXTREP(m!.rows[2],buf);   # to get the length right
      len := Length(buf);
  else
      len := 0;
  fi;

  for i in [1..rows] do
      buf := IO.Read(f,len);
      if len <> Length(buf) then
          Info(InfoCVec,1,"CVEC.ReadMat: Read error");
          Error();
          return fail;
      fi;
      CVEC.EXTREP_TO_CVEC(buf,m!.rows[i+1]);
  od;
  return m;
end;

CVEC.ReadMatFromFile := function(fn)
  local f,m;
  f := IO.File(fn,"r");
  if f = fail then
      Info(InfoCVec,1,"CVEC.ReadMatFromFile: Cannot open file");
      return fail;
  fi;
  m := CVEC.ReadMat(f);
  if m = fail then return fail; fi;
  IO.Close(f);
  return m;
end;

CVEC.ReadMatsFromFile := function(fnpref)
  local f,i,l,m;
  if not(IsString(fnpref)) then
      Error("CVEC.ReadMatsFromFile: fnpref must be a string");
      return fail;
  fi;
  f := IO.File(Concatenation(fnpref,"1"),"r");
  if f = fail then
      Error("CVEC.ReadMatsFromFile: no matrices there");
      return fail;
  else
      IO.Close(f);
  fi;
  l := [];
  i := 1;
  while true do
      f := IO.File(Concatenation(fnpref,String(i)),"r");
      if f = fail then break; fi;
      IO.Close(f);
      m := CVEC.ReadMatFromFile(Concatenation(fnpref,String(i)));
      if m = fail then
          return fail;
      else
          Add(l,m);
          i := i + 1;
      fi;
  od;
  return l;
end;

      
# Utilities:

CVEC.MatToCMat := function(m,p,d)
  local c,i,l,ll,v;
  l := [];
  c := CVEC.NewCVecClass(p,d,Length(m[1]));
  for i in [1..Length(m)] do
      ll := List(m[i],x->x);   # this unpacks
      v := CVec(ll,c);
      l[i+1] := v;
  od;
  return CVEC.CMatMaker(l,c);
end;
# Hacks:

InstallMethod(Characteristic,[IsField and HasGeneratorsOfField],
  function(f) 
    local l;
    l := GeneratorsOfField(f);
    if Length(l) = 0 then
        TryNextMethod();
    else
        return Characteristic(l[1]); 
    fi;
  end);

InstallMethod(DefaultFieldOfMatrix,
  [IsMatrix and IsCMatRep and IsFFECollColl],
  function(m)
    local f;
    if m!.vecclass![1]![13] = 0 then
        return m!.scaclass;
    else
        f := FieldByGenerators([m!.scaclass![6]]);
        SetSize(f,m!.scaclass![1]![3]);
        return f;
    fi;
  end);

# From the GAP library ffe.gi:

InstallMethod( FieldByGenerators,
    "for two coll. of FFEs, the first a field",
    IsIdenticalObj,
    [ IsFFECollection and IsField, IsFFECollection ], 0,
    function( subfield, gens )
    
    local F, d, subd, q, z;
        
    F := Objectify( NewType( FamilyObj( gens ),
                             IsField and IsAttributeStoringRep ),
                    rec() );
        
    d:= DegreeFFE( gens );
    subd:= DegreeOverPrimeField( subfield );
    if d mod subd <> 0 then
      d:= LcmInt( d, subd );
      gens:= Concatenation( gens, GeneratorsOfDivisionRing( subfield ) );
    fi;

    q:= Characteristic( subfield )^d;

    SetLeftActingDomain( F, subfield );
    SetIsPrimeField( F, d = 1 );
    SetIsFinite( F, true );
    SetSize( F, q );
    SetDegreeOverPrimeField( F, d );
    SetDimension( F, d / DegreeOverPrimeField( subfield ) );

    if q <= MAXSIZE_GF_INTERNAL then
      z:= Z(q);
      SetPrimitiveRoot( F, z );
      gens:= [ z ];
    # Here we left out an Error for the case d > 1.
    fi;

    SetGeneratorsOfDivisionRing( F, gens );
    SetGeneratorsOfRing( F, gens );

    return F;
    end );

