#############################################################################
# Lazy grease:
#############################################################################

InstallMethod( LazyGreaser, "for a vector and a positive grease level",
  [IsObject, IsPosInt],
  function( vecs, lev )
    local lg;
    lg := rec( vecs := vecs, tab := vecs{[]}, ind := [], lev := lev, 
               fs := Size(BaseField(vecs)) );
    if lg.fs > 65536 then
        Error("Lazy grease only supported for fields with <= 65536 elements");
        return;
    fi;
    return Objectify( NewType(LazyGreaserFamily, IsLazyGreaser), lg );
  end );

InstallMethod( ViewObj, "for a lazy greaser",
  [IsLazyGreaser],
  function( lg )
    Print("<lazy greaser level ",lg!.lev," with ",Length(lg!.tab)," vectors>");
  end );

InstallMethod( GetLinearCombination, 
  "for a lazy greaser, a vector, an offset, and a list of integers",
  [IsLazyGreaser, IsVector, IsPosInt, IsList],
  function( lg, v, offset, pivs )
    # offset must be congruent 1 mod lev
    local group,i,pos,w;
    pos := NumberFFVector(v{Reversed(pivs)},lg!.fs)+1;
    if pos = 1 then return 0; fi;
    group := (offset-1) / lg!.lev + 1;
    #if not IsBound(lg!.ind[group]) then
    #    lg!.ind[group] := [];
    #fi;
    if not IsBound(lg!.ind[group][pos]) then
        # Cut away all trailing zeroes:
        i := Length(pivs);
        while i > 0 and IsZero(v[pivs[i]]) do i := i - 1; od;
        # i = 0 does not happen!
        if i = 1 then
            w := v[pivs[1]] * lg!.vecs[offset];
        else
            w := GetLinearCombination(lg,v,offset,pivs{[1..i-1]});
            if w = 0 then
                w := v[pivs[i]] * lg!.vecs[offset+i-1];
            else
                w := w + v[pivs[i]] * lg!.vecs[offset+i-1];
            fi;
        fi;
        Add(lg!.tab,w);
        lg!.ind[group][pos] := Length(lg!.tab);
    else
        w := lg!.tab[lg!.ind[group][pos]];
    fi;
    return w;
  end );

InstallMethod( GetLinearCombination, 
  "for a lazy greaser, a cvec, an offset, and a list of integers",
  [IsLazyGreaser, IsCVecRep, IsPosInt, IsList],
  function( lg, v, offset, pivs )
    # the vecs entry of the lazy greaser must be a cmat!
    # offset must be congruent 1 mod lev
    local group,i,pos,w;
    pos := CVEC_GREASEPOS(v,pivs);
    if pos = 1 then return 0; fi;
    group := (offset-1) / lg!.lev + 1;
    if not IsBound(lg!.ind[group]) then
        lg!.ind[group] := [];
    fi;
    if not IsBound(lg!.ind[group][pos]) then
        # Cut away all trailing zeroes:
        i := Length(pivs);
        while i > 0 and IsZero(v[pivs[i]]) do i := i - 1; od;
        # i = 0 does not happen!
        if i = 1 then
            w := v[pivs[1]] * lg!.vecs[offset];
        else
            w := GetLinearCombination(lg,v,offset,pivs{[1..i-1]});
            if w = 0 then
                w := v[pivs[i]] * lg!.vecs[offset+i-1];
            else
                w := w + v[pivs[i]] * lg!.vecs[offset+i-1];
            fi;
        fi;
        Add(lg!.tab,w);
        lg!.ind[group][pos] := Length(lg!.tab);
        return w;
    else
        return lg!.tab[lg!.ind[group][pos]];
    fi;
  end );

CVEC_TESTLAZY := function(m,lev)
  local erg,f,i,j,l,offset,newpos,poss,v,w;
  v := ShallowCopy(m[1]);
  l := LazyGreaser(m,lev);
  f := BaseField(m);
  offset := Random(1,Length(m)-lev+1);
  offset := QuoInt(offset-1,lev)*lev + 1;  # make it congruent 1 mod lev
  for i in [1..10000] do
      w := Zero(v);
      poss := [];
      for j in [1..lev] do
          repeat
              newpos := Random([1..Length(v)]);
          until not newpos in poss;
          Add(poss,newpos);
          v[poss[j]] := Random(f);
          w := w + v[poss[j]] * m[offset+j-1];
      od;
      erg := GetLinearCombination(l,v,offset,poss);
      if not((erg = 0 and IsZero(w)) or w = erg) then
          Error();
      fi;
      Print(i,"\r");
  od;
  Print("\n");
  return l;
end;

  if IsBound(basis.lazygreaser) and basis.lazygreaser <> fail then
    # The grease case:
    lev := basis.lazygreaser!.lev;
    i := 1;
    mo := -One(vec[1]);
    while i+lev-1 <= len do
      pivs := basis.pivots{[i..i+lev-1]};
      j := lev;
      while j > 0 and pivs[j] < firstnz do j := j - 1; od;
      if j > 0 then    # Otherwise, there is nothing to do at all
        lc := GetLinearCombination(basis.lazygreaser,vec,i,pivs);
        #lc := glc(basis.lazygreaser,vec,i,pivs);
        if lc <> 0 then   # 0 indicates the zero linear combination
          if dec <> false and dec <> true then
            for j in [i..i+lev-1] do
              dec[j] := vec[basis.pivots[j]];
            od;
          fi;
          AddRowVector( vec, lc, mo );
        fi;
      fi;
      i := i + lev;
    od;
    # Now go to the standard case for the rest, starting at i
  else
    i := 1;
    # The non-grease case starts from the beginning
  fi;

  # we have to work without the lazy greaser:
  ...

InstallMethod( EmptySemiEchelonBasis, "GAP method", [IsObject],
  function( vec )
    return rec( vectors := MatrixNC([],vec), pivots := [], 
                lazygreaser := fail, helper := vec{[1]} );
    # The lazygreaser component must always be bound!
    # The helper is needed for the kernel cleaner for CVecs
  end );

InstallMethod( EmptySemiEchelonBasis, "GAP method", [IsObject, IsPosInt],
  function( vec, greaselev )
    local r;
    r := rec( vectors := MatrixNC([],vec), pivots := [], helper := vec{[1]} );
    # helper is needed for kernel cleaner
    r.lazygreaser := LazyGreaser( r.vectors, greaselev );
    return r;
  end );

      if IsBound(basis.lazygreaser) then
        # In the grease case, we do full-echelon form within the grease block:
        for j in [i..len] do
          c := basis.vectors[j][newpiv];
          if not IsZero(c) then
            AddRowVector( basis.vectors[j], basis.vectors[len+1], -c );
          fi;
        od;
      fi;

#############################################################################
# Lazy grease:
#############################################################################

BindGlobal( "LazyGreaserFamily", NewFamily("LazyGreaserFamily") );
DeclareCategory( "IsLazyGreaser", IsComponentObjectRep );
DeclareOperation( "LazyGreaser", [IsObject, IsPosInt] );
DeclareOperation( "GetLinearCombination", 
  [IsLazyGreaser, IsObject, IsPosInt, IsList] );


