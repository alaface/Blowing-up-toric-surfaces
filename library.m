// Some functions user to order the
// rays of a two dimensional fan

Ang := function(a,b)
 a := Eltseq(a);
 b := Eltseq(b);
 na := Sqrt(&+[a[i]^2 : i in [1..#a]]);
 nb := Sqrt(&+[b[i]^2 : i in [1..#b]]);
 return &+[a[i]*b[i] : i in [1..#a]]/(na*nb);
end function;

NextOne := function(a,L)
 m := -1;
 for b in L do
  if Ang(a,b) gt m and Determinant(Matrix([a,b])) gt 0 then
   v := b;
   m := Ang(a,v);
  end if;
 end for;
 return v;
end function;

Reorder := function(L)
 ll := [q : q in L | Min([Determinant(Matrix([q,p])) : p in L]) ge 0];
 if #ll eq 0 
  then S := [L[1]];
  else
  S := ll;
 end if;
 repeat
  v := NextOne(S[#S],L);
  i := Position(L,v);
  Append(~S,v);
 until #S eq #L;
 return S;
end function;


// ToricFromRays
// INPUT: a field, the rays of a two dimensional fan
// OUTPUT: the toric surface defined by the fan

ToricFromRays := function(Q,ra)
 rr := Reorder(ra);
 F := Fan([Cone(r) : r in [[rr[i],rr[i+1]] : i in [1..#rr-1]] cat [[rr[#rr],rr[1]]]]);
 X<[x]> := ToricVariety(Q,F);
 return X;
end function;

// LatticeIdeal
// INPUT: the rays of a fan
// OUTPUT: the lattice ideal of the corresponding toric variety

LatticeIdeal := function(ra)
  Q := Rationals();
  n := #ra;
  R<[x]> := PolynomialRing(Q,n);
  rw := Rows(Transpose(Matrix(ra)));
  bino1 := [Monomial(R,[Max(p[i],0) : i in [1..n]]) - Monomial(R,[-Min(p[i],0) : i in [1..n]]) : p in rw];
  I := Saturation(ideal<R|bino1>,&*x);
  return I;
end function;


// MultOneIdeal
// INPUT: the rays of a two dimensional fan
// OUTPUT: the saturation of <ts_i - f_i> 
// with respect to t, where <f_1,...,f_k>
// is the lattice ideal

MultOneIdeal := function(ra)
 I := LatticeIdeal(ra);
 r := Rank(Parent(I.1));
 B := MinimalBasis(I);
 k := #B;
 Q := BaseRing(I);
 R<[x]> := PolynomialRing(Q,r+k+1);
 B := [Evaluate(f,x[1..r]) : f in B];
 s := x[r+1..r+k];
 t := x[r+k+1];
 I1 := Ideal([t*s[i]-B[i] : i in [1..k]]);
 S := Saturation(I1,t);
 return <S,r,k>;
end function;

// TestMultOne
// INPUT: the rays of a two dimensional fan
// OUTPUT: true if the Cox ring of Bl_e(P) is generated in multiplicity one

TestMultOne := function(ra)
 Q := Rationals();
 ll := MultOneIdeal(ra);
 J := ll[1];
 r := ll[2];
 k := ll[3];
 t := J.(r+k+1);
 J1 := J + Ideal(t);
 return Dimension(J1) - Dimension(J1+Ideal(&*[J.i : i in [1..r]])) eq 1;
end function;

// TestComp
// INPUT: the rays of a two dimensional fan
// OUTPUT: false if the lattice ideal of the toric surface is contained in some <x_i,x_j,x_k>^2

TestComp := function(ra);
 Q := Rationals();
 I := LatticeIdeal(ra);
 r := #ra;
 A := Spec(Parent(I.1));
 comp := Set(&cat[PrimeComponents(Scheme(A,I+Ideal(A.i))) : i in [1..r]]);
 comp := [C : C in comp | IsSubscheme(Scheme(A,Ideal(C)^2),Scheme(A,I))];
 if #comp gt 0 then return false,comp;
 else return true;
 end if;
end function;


// IsIsom
// INPUT: two sequences of two dimensional rays 
// OUTPUT: true if the corresponding toric surfaces are isomorphic

IsIsom := function(a,b)
 a := Reorder(a);
 b := Reorder(b);
 G := DihedralGroup(#a);
 mm := [Transpose(Matrix([a[i^u] : i in [1..#a]])) : u in G];
 return &or[IsConsistent(Transpose(Matrix(b)),M) : M in mm];
end function;

