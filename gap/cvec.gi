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
InstallValue( CVEC_q, [] );
# A list holding field infos:
InstallValue( CVEC_F, [] );
# A list holding lengths of vectors existing for each q:
InstallValue( CVEC_lens, [] );
# A list holding cvec classes (which are pairs [fieldinfo,len])
InstallValue( CVEC_classes, [] );


#############################################################################
## Administration of field info and cvec class data:
#############################################################################

InstallValue( CVEC_BestGreaseTab,
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
  ] );

InstallGlobalFunction( CVEC_NewCVecClass, function(p,d,len)
  # Creates a new class of cvecs or returns a cached one:
  local bestgrease,bitsperel,cl,elsperword,filts,greasetabl,j,l,po,pos,pos2,
        q,s,scafam,size,tab1,tab2,ty,wordlen;

  # First check the arguments:
  if d <= 0 then 
      Error("CVEC_NewCVecClass: Degree must be positive."); 
      return fail;
  fi;
  if d >= CVEC_MAXDEGREE then 
      Error("CVEC_NewCVecClass: Degree must be < ",CVEC_MAXDEGREE,"."); 
      return fail;
  fi;
  if not(IsPrime(p)) then 
      Error("CVEC_MakeField: p must be a prime."); 
      return fail;
  fi; 
  if not(IsSmallIntRep(p)) then 
      Error("CVEC_NewCVecClass: p must be a prime that is an immediate int .");
      return fail;
  fi;
  if not(IsSmallIntRep(len)) then
      Error("CVEC_NewCVecClass: len must be an immediate integer.");
      return fail;
  fi;
  q := p^d;
  if q <= MAXSIZE_GF_INTERNAL then size := 0;
  elif IsSmallIntRep(q) then size := 1;
  else size := 2; fi;

  # First try to find q:
  pos := Position(CVEC_q,q);
  if pos = fail then
      l := [];    # Here we collect the information
      l[CVEC_IDX_p] := p;
      l[CVEC_IDX_d] := d;
      l[CVEC_IDX_q] := q;
      l[CVEC_IDX_size] := size;

      # We have to make the new field info structure:
      po := -CoefficientsOfLaurentPolynomial(ConwayPolynomial(p,d));
      if po[2] <> 0 then Error("Unexpected case #1"); fi;
      po := List(po[1],IntFFE);
      s := CVEC_COEFF_LIST_TO_C(po,"");
      l[CVEC_IDX_conway] := s;
      
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
      l[CVEC_IDX_bitsperel] := bitsperel;

      # Prime field elements per Word:
      # Note that for 64 bit machines we always put only twice as much
      # prime field elements into a Word than for 32 bit machines (even if
      # one more would fit!) such that conversion between binary formats
      # is easier later on.
      elsperword := QuoInt(32,bitsperel);
      if CVEC_BYTESPERWORD = 8 then
          elsperword := elsperword * 2;
      fi;
      l[CVEC_IDX_elsperword] := elsperword;

      # Set up best greasing level:
      if q <= 16 and IsBound(CVEC_BestGreaseTab[q]) then
          bestgrease := CVEC_BestGreaseTab[q];
          greasetabl := q^bestgrease;
      elif q <= 256 then
          bestgrease := 1;
          greasetabl := q;
      else
          bestgrease := 0;  # no grease
          greasetabl := 0;
      fi;
      l[CVEC_IDX_bestgrease] := bestgrease;
      l[CVEC_IDX_greasetabl] := greasetabl; 

      # Now the starting filter list:
      if size = 0 then
          filts := IsCVecRep and IsNoImmediateMethodsObject and HasLength and
                   IsCopyable and CanEasilyCompareElements and
                   CanEasilySortElements and IsCVecRepOverSmallField;
      else
          filts := IsCVecRep and IsNoImmediateMethodsObject and HasLength and
                   IsCopyable and CanEasilyCompareElements and
                   CanEasilySortElements;
      fi;

      # Note that IsMutable is added below, when we create the vector type
      l[CVEC_IDX_filts] := filts;

      # We use the "official" families:
      scafam := FFEFamily(p);
      l[CVEC_IDX_scafam] := scafam;

      # Now for small finite fields two tables for conversion:
      if q <= MAXSIZE_GF_INTERNAL then
          tab1 := 0*[1..q];
          tab2 := 0*[1..q];
          CVEC_INIT_SMALL_GFQ_TABS(p,d,q,tab1,tab2,Z(q));
      else
          # If p is < 65536, we need access to the prime field:
          if p < MAXSIZE_GF_INTERNAL then
              tab1 := 0*[1..p];
              tab2 := 0*[1..p];
              CVEC_INIT_SMALL_GFQ_TABS(p,1,p,tab1,tab2,Z(p));
          else
              tab1 := [];
              tab2 := [];
          fi;
      fi;
      l[CVEC_IDX_tab1] := tab1;
      l[CVEC_IDX_tab2] := tab2;

      # Now l is nearly ready!
      #l := [p,d,q,s,bitsperel,elsperword,0,bestgrease,greasetabl,filts,
      #      tab1,tab2,size,scafam];
      Objectify(NewType(CVecFieldInfoFamily,IsCVecFieldInfo),l);

      # Do the internal part: This does index CVEC_IDX_wordinfo:
      CVEC_FINALIZE_FIELDINFO(l);

      pos := PositionSorted(CVEC_q,q);
      Add(CVEC_q,q,pos);
      Add(CVEC_F,l,pos);
      Add(CVEC_lens,[],pos);
      Add(CVEC_classes,[],pos);
  else   # pos <> fail
      elsperword := CVEC_F[pos]![CVEC_IDX_elsperword];  # for later use
      filts := CVEC_F[pos]![CVEC_IDX_filts];            # for later use
      scafam := CVEC_F[pos]![CVEC_IDX_scafam];          # for later use
  fi;

  # Now we know that the field info is at position pos:
  pos2 := Position(CVEC_lens[pos],len);
  if pos2 <> fail then
      return CVEC_classes[pos][pos2];
  fi;

  # Build the class object, note that we need elsperword and filts from above:
  cl := [];
  cl[CVEC_IDX_fieldinfo] := CVEC_F[pos];
  cl[CVEC_IDX_len] := len;
  wordlen := d * (QuoInt( len + elsperword - 1, elsperword ));
  cl[CVEC_IDX_wordlen] := wordlen;
  ty := NewType(CollectionsFamily(scafam),filts and IsMutable,cl);
  cl[CVEC_IDX_type] := ty;
  cl[CVEC_IDX_GF] := GF(p,d);
  cl[CVEC_IDX_lens] := CVEC_lens[pos];
  cl[CVEC_IDX_classes] := CVEC_classes[pos];

  Objectify(NewType(CVecClassFamily,IsCVecClass),cl);

  # Put it into the cache:
  pos2 := PositionSorted(CVEC_lens[pos],len);
  Add(CVEC_lens[pos],len,pos2);
  Add(CVEC_classes[pos],cl,pos2);
  
  # Now add zero, one, and primitive root for the case d=1:
  return CVEC_classes[pos][pos2];
end );
 
InstallGlobalFunction( CVEC_NewCVecClassSameField, function(c,len)
  # Creates a new class in the case that another length is already known:
  local pos;
  pos := Position(c![CVEC_IDX_lens],len);
  if pos = fail then 
      return CVEC_NewCVecClass(c![CVEC_IDX_fieldinfo]![CVEC_IDX_p],
                               c![CVEC_IDX_fieldinfo]![CVEC_IDX_d],len);
  else
      return c![CVEC_IDX_classes][pos];
  fi;
end );

InstallMethod( CVecClass, "for a cvec", [IsCVecRep],
  function(v)
    return DataType(TypeObj(v));
  end);

InstallMethod( CVecClass, "for a cvec and a length", [IsCVecRep, IsInt],
  function(v,l)
    return CVEC_NewCVecClassSameField(DataType(TypeObj(v)),l);
  end );

InstallMethod( CVecClass, "for a cvecclass and a length", [IsCVecClass, IsInt],
  function(c,l)
    return CVEC_NewCVecClassSameField(c,l);
  end );

InstallMethod( CVecClass, "for three integers", [IsPosInt, IsPosInt, IsInt],
  function(p,d,l)
    return CVEC_NewCVecClass(p,d,l);
  end );

InstallGlobalFunction( CVEC_New, function(arg)
  local c,d,l,p;
  if Length(arg) = 1 then
      c := arg[1];
      if IsCVecRep(c) then
          c := DataType(TypeObj(c));
      fi;
      if IsCVecClass(c) then
          return CVEC_NEW(c,c![CVEC_IDX_type]);
      fi;
  elif Length(arg) = 3 then
      p := arg[1];
      d := arg[2];
      l := arg[3];
      if IsInt(p) and IsPrime(p) and p > 0 and IsInt(d) and d >= 1 and
         IsInt(l) and l >= 1 then
          c := CVEC_NewCVecClass(p,d,l);
          return CVEC_NEW(c,c![CVEC_IDX_type]);
      fi;
  fi;
  Error("Usage: CVEC_New( [ cvec | cvecclass | p,d,l ] )");
end );

##############################
# Some nice viewing methods: #
##############################

InstallMethod( ViewObj, "for a cvec field info", [IsCVecFieldInfo], 
function(f)
  Print("<cvec-fieldinfo p=",f![CVEC_IDX_p],
        " d=",f![CVEC_IDX_d]," q=",f![CVEC_IDX_q],
        " bpl=",f![CVEC_IDX_bitsperel]," epw=",f![CVEC_IDX_elsperword],
        " grease=",f![CVEC_IDX_bestgrease],
        " gtablen=",f![CVEC_IDX_greasetabl],">");
end);

InstallMethod( ViewObj, "for a cvec class", [IsCVecClass], 
function(c)
  local f;
  f := c![CVEC_IDX_fieldinfo];
  Print("<cvec-class field=GF(",f![CVEC_IDX_p],",",f![CVEC_IDX_d],
        ") len=",c![CVEC_IDX_len]," wordlen=",c![CVEC_IDX_wordlen],">");
end);

InstallMethod( ViewObj, "for a cvec", [IsCVecRep], 
function(v)
  local c;
  c := DataType(TypeObj(v));
  Print("<");
  if not(IsMutable(v)) then Print("immutable "); fi;
  Print("cvec over GF(",c![CVEC_IDX_fieldinfo]![CVEC_IDX_p],",",
        c![CVEC_IDX_fieldinfo]![CVEC_IDX_d],") of length ",
        c![CVEC_IDX_len],">");
end);

InstallMethod( PrintObj, "for a cvec class", [IsCVecClass], 
function(c)
  Print("CVEC_NewCVecClass(",c![CVEC_IDX_fieldinfo]![CVEC_IDX_p],",",
        c![CVEC_IDX_fieldinfo]![CVEC_IDX_d],",",c![CVEC_IDX_len],")");
end);

InstallMethod( PrintObj, "for a cvec", [IsCVecRep], 
function(v)
  local l,c,i;
  c := DataType(TypeObj(v));
  Print("CVec([");
  if c![CVEC_IDX_fieldinfo]![CVEC_IDX_size] = 0 then   # GAP FFEs
      l := Unpack(v);
      for i in l do Print(i,","); od;
  else
      l := Unpack(v);
      for i in l do Print(i,","); od;
  fi;
  Print("],",c![CVEC_IDX_fieldinfo]![CVEC_IDX_p],",",
        c![CVEC_IDX_fieldinfo]![CVEC_IDX_d],")");
end);

InstallMethod( String, "for a cvec", [IsCVecRep], 
function(v)
  local l,c,i,res;
  c := DataType(TypeObj(v));
  res := "CVec([";
  if c![CVEC_IDX_fieldinfo]![CVEC_IDX_size] = 0 then   # GAP FFEs
      l := Unpack(v);
      for i in l do Append(res,String(i)); Append(res,","); od;
  else
      l := Unpack(v);
      for i in l do Append(res,String(i)); Append(res,","); od;
  fi;
  Append(res,"],");
  Append(res,String(c![CVEC_IDX_fieldinfo]![CVEC_IDX_p]));
  Append(res,",");
  Append(res,String(c![CVEC_IDX_fieldinfo]![CVEC_IDX_d]));
  Append(res,")");
  return res;
end);

InstallValue( CVEC_CharactersForDisplay,
              ".123456789abcdefghijklmnopqrstuvwxyz" );

InstallMethod( Display, "for a cvec", [IsCVecRep], 
function(v)
  local i,l,c,q,lo;
  c := DataType(TypeObj(v));
  Print("[");
  q := c![CVEC_IDX_fieldinfo]![CVEC_IDX_q];
  if q <= 36 then
      l := IntegerRep(v);
      Print(CVEC_CharactersForDisplay{l+1},"]\n");
  elif c![CVEC_IDX_fieldinfo]![CVEC_IDX_size] = 1 then
      l := Unpack(v);
      lo := LogInt(q,10)+7;   # This is the number of digits needed plus 6
      for i in l do Print(String(i,lo)); od;
      Print("]\n");
  else
      l := Unpack(v);
      for i in l do Print(i,","); od;
      Print("]\n");
  fi;
end);


#########################################
# Handling of scalars on the GAP level: # 
#########################################

InstallGlobalFunction( CVEC_HandleScalar, function(cl,s)
  # cl is a cvecclass and s a scalar
  local v,d;
  if   IsInternalRep(s) then return s;
    # Note that this case also covers integers!
  elif IsZmodnZObj(s) then return s![1];
  fi;
  # Now we have to check, whether the field element is over the right field:
  d := cl![CVEC_IDX_fieldinfo]![CVEC_IDX_d];
  if s![2] <> d then
      s := FFECONWAY.WriteOverLargerField(s,d);
  fi;
  if IsGF2VectorRep(s![1]) then
    v := ShallowCopy(s![1]);
    PLAIN_GF2VEC(v);
    return v;
  elif Is8BitVectorRep(s![1]) then
    v := ShallowCopy(s![1]);
    PLAIN_VEC8BIT(v);
    return v;
  elif cl![CVEC_IDX_fieldinfo]![CVEC_IDX_p] < MAXSIZE_GF_INTERNAL then
    return s![1];
  else
    return List(s![1],x->x![1]);   # this unpacks ZmodnZObjs
  fi;
end );

#################################################
# Now to the installation of methods for cvecs: #
#################################################

# Length:

InstallOtherMethod( Length, "for cvecs", [IsCVecRep], 
function(v)
  return DataType(TypeObj(v))![CVEC_IDX_len];
end);

# AddRowVector(v,w [,s][,fr,to]) where s is integer or FFE:

InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep],
  function(v,w) CVEC_ADD2(v,w,0,0); end);

InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep, IsInt, IsInt],
  function(v,w,fr,to) CVEC_ADD2(v,w,fr,to); end);

InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep, IsFFE and IsInternalRep],
  function(v,w,s)
    CVEC_ADDMUL(v,w,s,0,0);
  end );
InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep, IsFFE],
  function(v,w,s) 
    CVEC_ADDMUL(v,w,CVEC_HandleScalar(DataType(TypeObj(v)),s),0,0); 
  end);
InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep, IsInt and IsSmallIntRep],
  function(v,w,s) CVEC_ADDMUL(v,w,s,0,0); end);

InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep, IsFFE and IsInternalRep, IsInt, IsInt],
  function(v,w,s,fr,to) 
    CVEC_ADDMUL(v,w,s,fr,to); 
  end);
InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsCVecRep, IsFFE, IsInt, IsInt],
  function(v,w,s,fr,to) 
    CVEC_ADDMUL(v,w,CVEC_HandleScalar(DataType(TypeObj(v)),s),fr,to); 
  end);
InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep,IsCVecRep,IsInt and IsSmallIntRep,IsInt,IsInt],
  CVEC_ADDMUL );
InstallOtherMethod( AddRowVector, "for cvecs",
  [IsMutable and IsCVecRep,IsCVecRep,IsFFE and IsInternalRep,IsInt,IsInt],
  CVEC_ADDMUL );

# MultRowVector(v,s [,fr,to]) where s is integer or FFE:
# Note that we do not give a method for MultRowVector with 5 arguments!

InstallOtherMethod( MultRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsInt and IsSmallIntRep],
  function(v,s) CVEC_MUL1(v,s,0,0); end);
InstallOtherMethod( MultRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsInt and IsSmallIntRep, IsInt, IsInt],
  CVEC_MUL1 );

InstallOtherMethod( MultRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsFFE and IsInternalRep],
  function(v,s) CVEC_MUL1(v,s,0,0); end);
InstallOtherMethod( MultRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsFFE and IsInternalRep, IsInt, IsInt],
  CVEC_MUL1 );

InstallOtherMethod( MultRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsFFE],
  function(v,s) 
    CVEC_MUL1(v,CVEC_HandleScalar(DataType(TypeObj(v)),s),0,0); 
  end);
InstallOtherMethod( MultRowVector, "for cvecs",
  [IsMutable and IsCVecRep, IsFFE, IsInt, IsInt],
  function(v,s,fr,to) 
    CVEC_MUL1(v,CVEC_HandleScalar(DataType(TypeObj(v)),s),fr,to); 
  end);

# Addition of vectors:

InstallOtherMethod( \+, "for cvecs", [IsCVecRep, IsCVecRep],
  function(v,w)
    local u,vcl;
    vcl := DataType(TypeObj(v));
    u := CVEC_NEW(vcl,vcl![CVEC_IDX_type]);
    CVEC_ADD3(u,v,w);
    if not(IsMutable(v)) or not(IsMutable(w)) then MakeImmutable(u); fi;
    return u;
  end);

# Subtraction of vectors:

InstallOtherMethod( \-, "for cvecs", [IsCVecRep, IsCVecRep],
  function(v,w)
    local u,vcl,p;
    vcl := DataType(TypeObj(v));
    p := vcl![CVEC_IDX_fieldinfo]![CVEC_IDX_p];
    u := CVEC_NEW(vcl,vcl![CVEC_IDX_type]);
    CVEC_COPY(v,u);
    CVEC_ADDMUL(u,w,p-1,0,0);
    if not(IsMutable(v)) or not(IsMutable(w)) then MakeImmutable(u); fi;
    return u;
  end);

# Additive inverse of vectors:

InstallOtherMethod( AdditiveInverseMutable, "for cvecs", [IsCVecRep],
  function(v)
    local u,vcl,p;
    vcl := DataType(TypeObj(v));
    p := vcl![CVEC_IDX_fieldinfo]![CVEC_IDX_p];
    u := CVEC_NEW(vcl,vcl![CVEC_IDX_type]);
    CVEC_MUL2(u,v,p-1);
    return u;
  end);
InstallOtherMethod( AdditiveInverseSameMutability, "for cvecs", [IsCVecRep],
  function(v)
    local u,vcl,p;
    vcl := DataType(TypeObj(v));
    p := vcl![CVEC_IDX_fieldinfo]![CVEC_IDX_p];
    u := CVEC_NEW(vcl,vcl![CVEC_IDX_type]);
    CVEC_MUL2(u,v,p-1);
    if not(IsMutable(v)) then MakeImmutable(u); fi;
    return u;
  end);

# Multiplication of vectors by scalars:

BindGlobal( "CVEC_VECTOR_TIMES_SCALAR", function(v,s)
    # The scalar here must already be run through CVEC_HandleScalar 
    # if necessary! Of course, integers and FFEs in internal representation
    # of course is allowed.
    local u,vcl;
    vcl := DataType(TypeObj(v));
    u := CVEC_NEW(vcl,vcl![CVEC_IDX_type]);
    CVEC_MUL2(u,v,s);
    if not(IsMutable(v)) then MakeImmutable(u); fi;
    return u;
  end );
InstallOtherMethod( \*, "for cvecs", [IsCVecRep, IsInt], 
  CVEC_VECTOR_TIMES_SCALAR);
InstallOtherMethod( \*, "for cvecs", [IsCVecRep, IsFFE and IsInternalRep], 
  CVEC_VECTOR_TIMES_SCALAR);
InstallOtherMethod( \*, "for cvecs", [IsCVecRep, IsFFE], 
  function (v,s) 
    return CVEC_VECTOR_TIMES_SCALAR(v,
                CVEC_HandleScalar(DataType(TypeObj(v)),s));
  end);
InstallOtherMethod( \*, "for cvecs", [IsInt,IsCVecRep], 
  function(s,v) return CVEC_VECTOR_TIMES_SCALAR(v,s); end);
InstallOtherMethod( \*, "for cvecs", [IsFFE and IsInternalRep,IsCVecRep], 
  function(s,v) return CVEC_VECTOR_TIMES_SCALAR(v,s); end);
InstallOtherMethod( \*, "for cvecs", [IsFFE, IsCVecRep], 
  function (s,v) 
    return CVEC_VECTOR_TIMES_SCALAR(v,
                CVEC_HandleScalar(DataType(TypeObj(v)),s));
  end);

# Comparison of vectors:

InstallOtherMethod( \=, "for cvecs", [IsCVecRep, IsCVecRep], CVEC_CVEC_EQ );
InstallOtherMethod( \<, "for cvecs", [IsCVecRep, IsCVecRep], CVEC_CVEC_LT );
InstallOtherMethod( IsZero, "for cvecs", [IsCVecRep], CVEC_CVEC_ISZERO);

# Element access for vectors:

InstallOtherMethod( \[\]\:\=, "for a cvec, a pos, and an int",
  [IsCVecRep and IsMutable, IsPosInt, IsInt and IsSmallIntRep], CVEC_ASS_CVEC );
InstallOtherMethod( \[\]\:\=, "for a cvec, a pos, and an int",
  [IsCVecRep and IsMutable, IsPosInt, IsFFE and IsInternalRep], CVEC_ASS_CVEC );
InstallOtherMethod( \[\]\:\=, "for a cvec, a pos, and a ffe",
  [IsCVecRep and IsMutable, IsPosInt, IsFFE], 
  function(v,pos,s)
    CVEC_ASS_CVEC(v,pos,CVEC_HandleScalar(DataType(TypeObj(v)),s));
  end);
InstallOtherMethod( \[\]\:\=, "for cvecs", [IsCVecRep, IsPosInt, IsInt],
  function(v,p,o) Error("cvec is immutable"); end);
InstallOtherMethod( \[\]\:\=, "for cvecs", [IsCVecRep, IsPosInt, IsFFE],
  function(v,p,o) Error("cvec is immutable"); end);

InstallOtherMethod( \[\], "for cvecs", 
  [IsCVecRep and IsCVecRepOverSmallField, IsPosInt],CVEC_ELM_CVEC );
InstallOtherMethod( \[\], "for cvecs", [IsCVecRep, IsPosInt], 
  function(v,pos)
    local d,fam,i,p,s,size,vcl;
    vcl := DataType(TypeObj(v));
    size := vcl![CVEC_IDX_fieldinfo]![CVEC_IDX_size];
    s := CVEC_ELM_CVEC(v,pos);
    if size = 0 then return s; fi;
    d := vcl![CVEC_IDX_fieldinfo]![CVEC_IDX_d];
    if d = 1 then
        if IsFFE(s) then
            return s;
        else
            p := vcl![CVEC_IDX_fieldinfo]![CVEC_IDX_p];
            return ZmodnZObj(s,p);
        fi;
    else
        p := vcl![CVEC_IDX_fieldinfo]![CVEC_IDX_p];
        if p > 65536 then
            for i in [1..d] do
                s[i] := ZmodnZObj(s[i],p);
            od;
        fi;
        ConvertToVectorRep(s,p);
        s := [s,d,fail];
        fam := FFEFamily(p);
        Objectify(fam!.ConwayFldEltDefaultType,s);
        return s;
    fi;
  end);

# PositionNonZero and friends:

InstallOtherMethod( PositionNonZero, "for cvecs",
  [IsCVecRep], CVEC_POSITION_NONZERO_CVEC);
InstallOtherMethod( PositionLastNonZero, "for cvecs",
  [IsCVecRep], CVEC_POSITION_LAST_NONZERO_CVEC);
InstallOtherMethod( PositionNot, "for cvecs",
  [IsCVecRep, IsFFE], 
  function(v,z)
    local j;
    if z <> Zero(z) then
        for j in [1..Length(v)] do
            if v[j] <> z then
                return j;
            fi;
        od;
        return Length(v)+1;
    fi;
    return PositionNonZero(v);
  end);
InstallOtherMethod( PositionNot, "for cvecs",
  [IsCVecRep, IsFFE, IsInt], 
  function(v,z,i)
    local j;
    if z <> Zero(z) or i <> 0 then
        for j in [i+1..Length(v)] do
            if v[j] <> z then
                return j;
            fi;
        od;
        return Length(v)+1;
    fi;
    return PositionNonZero(v);
  end);

# Copying:

InstallOtherMethod( ShallowCopy, "for cvecs", [IsCVecRep],
  function(v)
    local u,vcl;
    vcl := DataType(TypeObj(v));
    u := CVEC_NEW(vcl,vcl![CVEC_IDX_type]);
    CVEC_COPY(v,u);
    return u;
  end);

# Zeroing:

InstallOtherMethod( ZeroMutable, "for cvecs", [IsCVecRep],
  function(v)
    local u,vcl;
    vcl := DataType(TypeObj(v));
    u := CVEC_NEW(vcl,vcl![CVEC_IDX_type]);
    return u;
  end);
InstallOtherMethod( ZeroSameMutability, "for cvecs", [IsCVecRep],
  function(v)
    local u,vcl;
    vcl := DataType(TypeObj(v));
    u := CVEC_NEW(vcl,vcl![CVEC_IDX_type]);
    if not(IsMutable(v)) then
        MakeImmutable(u);
    fi;
    return u;
  end);

InstallMethod( ZeroVector, "for a cvec and an integer",
  [IsCVecRep, IsInt],
  function(v,len)
    local cl;
    cl := CVEC_NewCVecClassSameField(DataType(TypeObj(v)),len);
    return CVEC_NEW(cl,cl![CVEC_IDX_type]);
  end);

# The making of:

InstallMethod( CVec, "for a cvec class",
  [IsCVecClass],
  function(c)
    return CVEC_NEW(c,c![CVEC_IDX_type]);
  end);
InstallMethod( CVec, "for a homogeneous list and two posints", 
  [IsHomogeneousList, IsPosInt, IsPosInt],
  function(l,p,d)
    local c,v;
    if IsSmallIntRep(p^d) then
        c := CVEC_NewCVecClass(p,d,Length(l));
    else
        c := CVEC_NewCVecClass(p,d,Length(l)/d);
    fi;
    return CVec(l,c);  # Delegate to the following routine
  end);
InstallMethod( CVec, "for a homogeneous list and a cvec class",
  [IsHomogeneousList, IsCVecClass],
  function(l,c)
    local v;
    v := CVEC_NEW(c,c![CVEC_IDX_type]);
    # We recognise the type of entries by looking at the first one:
    if Length(l) > 0 then
        if IsZmodnZObj(l[1]) then
            CVEC_INTREP_TO_CVEC(List(l,x->x![1]),v);
            return v;
        elif IsFFE(l[1]) and not(IsInternalRep(l[1])) then  # large scalars:
            CVEC_INTREP_TO_CVEC(List(l,x->CVEC_HandleScalar(c,x)),v);
            return v;
        fi;
    fi;
    # This can only handle integers and internal FFEs:
    CVEC_INTREP_TO_CVEC(l,v);
    return v;
  end);
InstallOtherMethod( CVec, "for a compressed gf2 vector",
  [IsHomogeneousList and IsGF2VectorRep],
  function(v)
    local c,w;
    v := ShallowCopy(v);
    PLAIN_GF2VEC(v);
    c := CVEC_NewCVecClass(2,1,Length(v));
    w := CVEC_NEW(c,c![CVEC_IDX_type]);
    CVEC_INTREP_TO_CVEC(v,w);
    return w;
  end);
InstallOtherMethod( CVec, "for a compressed 8bit vector",
  [IsHomogeneousList and Is8BitVectorRep],
  function(v)
    local c,pd,w;
    pd := Factors(Size(Field(v)));
    v := ShallowCopy(v);
    PLAIN_VEC8BIT(v);
    c := CVEC_NewCVecClass(pd[1],Length(pd),Length(v));
    w := CVEC_NEW(c,c![CVEC_IDX_type]);
    CVEC_INTREP_TO_CVEC(v,w);
    return w;
  end);

# And the way back:

InstallMethod( Unpack, "for cvecs", [IsCVecRep],
  function(v)
    local d,f,fam,i,l,p,q,vcl;
    vcl := DataType(TypeObj(v));
    f := vcl![CVEC_IDX_fieldinfo];
    p := f![CVEC_IDX_p];
    d := f![CVEC_IDX_d];
    q := f![CVEC_IDX_q];
    if q <= MAXSIZE_GF_INTERNAL or d = 1 then
        l := 0*[1..Length(v)];
    else
        l := List([1..Length(v)],i->0*[1..d]);
    fi;
    CVEC_CVEC_TO_INTREP(v,l);
    # Now convert things to FFEs:
    if q <= MAXSIZE_GF_INTERNAL then
        # We return internal FFEs:
        CVEC_INTLI_TO_FFELI(f,l);
    elif d = 1 then
        # We return ZmodnZObjs:
        for i in [1..Length(l)] do
            l[i] := ZmodnZObj(l[i],p);
        od;
    elif p < MAXSIZE_GF_INTERNAL then
        # We build a large FFE with GF2 or 8bit coeffs
        fam := FFEFamily(p);
        for i in [1..Length(l)] do
            CVEC_INTLI_TO_FFELI(f,l[i]);
            ConvertToVectorRep(l[i],p);
            l[i] := [l[i],d,fail];
            Objectify(fam!.ConwayFldEltDefaultType,l[i]);
        od;
    else
        # We build a large FFE with ZmodnZObj coeffs
        fam := FFEFamily(p);
        for i in [1..Length(l)] do
            l[i] := [List(l[i],x->ZmodnZObj(x,p)),d,fail];
            Objectify(fam!.ConwayFldEltDefaultType,l[i]);
        od;
    fi;
    return l;
  end);

InstallMethod( IntegerRep, "for cvecs", [IsCVecRep],
  function(v)
    local d,l,p,q,vcl;
    vcl := DataType(TypeObj(v));
    p := vcl![CVEC_IDX_fieldinfo]![CVEC_IDX_p];
    d := vcl![CVEC_IDX_fieldinfo]![CVEC_IDX_d];
    q := vcl![CVEC_IDX_fieldinfo]![CVEC_IDX_q];
    if q <= MAXSIZE_GF_INTERNAL or d = 1 then
        l := 0*[1..Length(v)];
    else
        l := List([1..Length(v)],i->0*[1..d]);
    fi;
    CVEC_CVEC_TO_INTREP(v,l);
    return l;
  end);

InstallOtherMethod( NumberFFVector, "for a cvec, and a field size",
  [IsCVecRep, IsPosInt],
  function(v,sz)
    local bas,c,f,halfword,i,l,res,wordlen;
    c := DataType(TypeObj(v));
    f := c![CVEC_IDX_fieldinfo];
    if sz <> f![CVEC_IDX_q] then
        Error("CVEC_NumberFFVector: vector over wrong field");
        return;
    fi;
    wordlen := c![CVEC_IDX_wordlen];
    bas := f![CVEC_IDX_p] ^ f![CVEC_IDX_elsperword];
    if IsSmallIntRep(bas) then
        l := 0*[1..wordlen];
        CVEC_CVEC_TO_NUMBERFFLIST(v,l,false);
        res := l[1];
        for i in [2..wordlen] do
            res := res * bas + l[i];
        od;
    else
        l := 0*[1..2*wordlen];
        CVEC_CVEC_TO_NUMBERFFLIST(v,l,true);
        halfword := 2^(CVEC_BYTESPERWORD*4);
        res := l[1] + l[2]*halfword;
        for i in [3,5..2*wordlen-1] do
            res := res * bas + l[i] + halfword * l[i+1];
        od;
    fi;
    return res;
  end);

InstallOtherMethod( NumberFFVector, "for a cvec", [IsCVecRep],
  function(v)
    local c;
    c := DataType(TypeObj(v));
    return NumberFFVector(v,c![CVEC_IDX_fieldinfo]![CVEC_IDX_q]);
  end);

InstallMethod( CVecNumber, "for four integers", 
  [IsInt,IsPosInt,IsPosInt,IsPosInt],
  function(nr,p,d,l)
    local c;
    c := CVEC_NewCVecClass(p,d,l);
    return CVecNumber(nr,c);
  end );

InstallMethod( CVecNumber, "for an integer, and a cvecclass",
  [IsInt, IsCVecClass],
  function(nr,c)
    local bas,f,halfword,i,l,q,qq,v,wordlen;
    v := CVEC_NEW(c,c![CVEC_IDX_type]);
    wordlen := c![CVEC_IDX_wordlen];
    f := c![CVEC_IDX_fieldinfo];
    bas := f![CVEC_IDX_p] ^ f![CVEC_IDX_elsperword];
    if IsSmallIntRep(bas) then
        l := 0*[1..wordlen];
        for i in [wordlen,wordlen-1..1] do
            q := QuotientRemainder(nr,bas);
            l[i] := q[2];
            nr := q[1];
        od;
        CVEC_NUMBERFFLIST_TO_CVEC(l,v,false);
    else
        l := 0*[1..2*wordlen];
        halfword := 2^(CVEC_BYTESPERWORD*4);
        for i in [2*wordlen-1,2*wordlen-3..1] do
            q := QuotientRemainder(nr,bas);
            qq := QuotientRemainder(q[2],halfword);
            l[i] := qq[2];
            l[i+1] := qq[1];
            nr := q[1];
        od;
        CVEC_NUMBERFFLIST_TO_CVEC(l,v,true);
    fi;
    return v;
  end );
    

#############################################################################
# Access to the base field:
#############################################################################

InstallOtherMethod( Characteristic, "for cvecs", [IsCVecRep],
  function(v)
    local c;
    c := DataType(TypeObj(v));
    return c![CVEC_IDX_fieldinfo]![CVEC_IDX_p];
  end);
    
InstallOtherMethod( DegreeFFE, "for cvecs", [IsCVecRep],
  function(v)
    local c;
    c := DataType(TypeObj(v));
    return c![CVEC_IDX_fieldinfo]![CVEC_IDX_d];
  end);
    
InstallMethod( BaseField, "for cvecs", [IsCVecRep],
  function(v)
    local c;
    c := DataType(TypeObj(v));
    return c![CVEC_IDX_GF];
  end);
    
#############################################################################
# Slicing:
#############################################################################

InstallGlobalFunction( CVEC_Slice, function(src,dst,srcpos,len,dstpos)
  local cdst,csrc;
  csrc := DataType(TypeObj(src));
  cdst := DataType(TypeObj(dst));
  if not(IsIdenticalObj(csrc![CVEC_IDX_fieldinfo],
                        cdst![CVEC_IDX_fieldinfo])) then
      Error("CVEC_Slice: vectors not over common field");
      return;
  fi;
  if srcpos < 1 or srcpos+len-1 > csrc![CVEC_IDX_len] or len <= 0 then
      Error("CVEC_Slice: source area not valid");
      return;
  fi;
  if dstpos < 1 or dstpos+len-1 > cdst![CVEC_IDX_len] then
      Error("CVEC_Slice: destination area not valid");
      return;
  fi;
  if not(IsMutable(dst)) then
      Error("CVEC_Slice: destination vector immutable");
      return;
  fi;
  CVEC_SLICE(src,dst,srcpos,len,dstpos);
end );

InstallGlobalFunction( CVEC_SliceList, function(src,dst,srcposs,dstposs)
  if not(IsMutable(dst)) then
      Error("CVEC_SliceList: destination vector immutable");
      return;
  fi;
  CVEC_SLICE_LIST(src,dst,srcposs,dstposs);
end );

InstallOtherMethod( \{\}, "for a cvec and a range", 
  [IsCVecRep, IsHomogeneousList and IsRangeRep],
  function(v,r)
    # note that ranges in IsRangeRep always have length at least 2!
    local c,cl,w;
    cl := DataType(TypeObj(v));
    c := CVEC_NewCVecClassSameField(cl,Length(r));
    w := CVEC_NEW(c,c![CVEC_IDX_type]);
    CVEC_SLICE_LIST(v,w,r,[1..Length(r)]);
    if not(IsMutable(v)) then
        MakeImmutable(w);
    fi;
    return w;
  end);

InstallOtherMethod( \{\}, "for a cvec and a list", 
  [IsCVecRep, IsHomogeneousList],
  function(v,l)
    local c,cl,w;
    cl := DataType(TypeObj(v));
    c := CVEC_NewCVecClassSameField(cl,Length(l));
    w := CVEC_NEW(c,c![CVEC_IDX_type]);
    CVEC_SLICE_LIST(v,w,l,[1..Length(l)]);
    if not(IsMutable(v)) then
        MakeImmutable(w);
    fi;

    return w;
  end);

InstallOtherMethod( CopySubVector, "for two cvecs and stuff",
  [IsCVecRep, IsCVecRep and IsMutable, IsHomogeneousList, IsHomogeneousList],
  function(src,dst,scols,dcols)
    if Length(scols) = 0 then return; fi;  # a little speedup
    CVEC_SLICE_LIST(src,dst,scols,dcols);
  end );

# Note that slicing assignment is intentionally not supported, because
# this will usually be used only by inefficient code. Use CVEC_Slice
# or even CVEC_SLICE instead.

# Concatenation of vectors:

InstallGlobalFunction( CVEC_Concatenation, function(arg)
  local c,cc,i,len,pos,v;
  if Length(arg) = 0 or not(IsCVecRep(arg[1])) then
      Error("CVEC_Concatenation: Need at least one cvec");
      return;
  fi;
  c := DataType(TypeObj(arg[1]));
  len := Length(arg[1]);
  for i in [2..Length(arg)] do
      if not(IsCVecRep(arg[i])) or 
         not(IsIdenticalObj(c,DataType(TypeObj(arg[i])))) then
          Error("CVEC_Concatenation: Arguments must all be cvecs over the ",
                "same field ");
          return;
      fi;
      len := len + Length(arg[i]);
  od;
  cc := CVEC_NewCVecClassSameField(c,len);
  v := CVEC_New(cc);
  pos := 1;
  for i in [1..Length(arg)] do
      CVEC_SLICE(arg[i],v,1,Length(arg[i]),pos);
      pos := pos + Length(arg[i]);
  od;
  return v;
end );


############################################################################
# For polynomial arithmetic: 
############################################################################

InstallOtherMethod( ProductCoeffs, "for cvecs",
  [IsCVecRep, IsCVecRep],
  function(v,w)
  local cl,u,vcl,wcl;
  vcl := DataType(TypeObj(v));
  if vcl![CVEC_IDX_fieldinfo]![CVEC_IDX_d] > 1 then
      Error("Non-prime fields not yet implemented (doable)!");
      return;
  fi;
  wcl := DataType(TypeObj(w));
  if not(IsIdenticalObj(vcl![CVEC_IDX_fieldinfo],wcl![CVEC_IDX_fieldinfo])) then
      Error("ProductCoeffs: Not over same field!");
  fi;
  cl := CVEC_NewCVecClassSameField(vcl,vcl![CVEC_IDX_len]+wcl![CVEC_IDX_len]-1);
  u := CVEC_NEW(cl,cl![CVEC_IDX_type]);
  CVEC_PROD_COEFFS_CVEC_PRIMEFIELD(u,v,w);
  return u;
end);


############################################################################
# For (pseudo) random vectors: 
############################################################################

InstallMethod( Randomize, "for cvecs", [IsCVecRep and IsMutable],
  function( v )
    local cl,d,j,len,li,p,q,size;
    cl := DataType(TypeObj(v));
    len := Length(v);
    size := cl![CVEC_IDX_fieldinfo]![CVEC_IDX_size];
    d := cl![CVEC_IDX_fieldinfo]![CVEC_IDX_d];
    if size <= 1 then
        q := cl![CVEC_IDX_fieldinfo]![CVEC_IDX_q];
        li := 0*[1..len];
        for j in [1..len] do
            li[j] := Random(0,q-1);
        od;
        CVEC_INTREP_TO_CVEC(li,v);
    else    # big scalars!
        li := 0*[1..len*d];
        p := cl![CVEC_IDX_fieldinfo]![CVEC_IDX_p];
        for j in [1..len*d] do
            li[j] := Random(0,p-1);
        od;
        CVEC_INTREP_TO_CVEC(li,v);
    fi;
    return v;
  end );

InstallMethod( Randomize, "for a cvec and a random source", 
  [IsCVecRep and IsMutable, IsRandomSource],
  function( v, rs )
    local cl,d,j,len,li,p,q,size;
    cl := DataType(TypeObj(v));
    len := Length(v);
    size := cl![CVEC_IDX_fieldinfo]![CVEC_IDX_size];
    d := cl![CVEC_IDX_fieldinfo]![CVEC_IDX_d];
    if size <= 1 then
        q := cl![CVEC_IDX_fieldinfo]![CVEC_IDX_q];
        li := 0*[1..len];
        for j in [1..len] do
            li[j] := Random(rs,0,q-1);
        od;
        CVEC_INTREP_TO_CVEC(li,v);
    else    # big scalars!
        li := 0*[1..len*d];
        p := cl![CVEC_IDX_fieldinfo]![CVEC_IDX_p];
        for j in [1..len*d] do
            li[j] := Random(rs,0,p-1);
        od;
        CVEC_INTREP_TO_CVEC(li,v);
    fi;
    return v;
  end );


#############################################################################
# The making of good hash functions:
#############################################################################

InstallGlobalFunction( CVEC_HashFunctionForCVecs, function(v,data)
  return HASHKEY_BAG(v,101,4,data[2]) mod data[1] + 1;
end );

InstallMethod( ChooseHashFunction, "for cvecs",
  [IsCVecRep,IsInt],
  function(p,hashlen)
    local bytelen,c;
    c := CVecClass(p);
    bytelen := c![CVEC_IDX_wordlen] * CVEC_BYTESPERWORD;
    return rec( func := CVEC_HashFunctionForCVecs,
                data := [hashlen,bytelen] );
  end );

