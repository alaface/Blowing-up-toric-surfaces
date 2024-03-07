// Some functions used to order the
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
 F := Fan(ra,[[i,i+1] : i in [1..#ra-1]] cat [[1,#ra]]);
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
 else return true,0;
 end if;
end function;

// CompIndices
// INPUT: the rays of a two dimensional fan
// OUTPUT: the sets {i,j,k} such that the lattice ideal of the toric surface is contained in  <x_i,x_j,x_k>^2

CompIndices := function(ra)
 bol,comp := TestComp(ra);
 if not bol then
  lis := {};
  for C in comp do
   v := {Position(Exponents(Monomials(B)[1]),1) : B in MinimalBasis(C)};
   Include(~lis,v);
  end for;
  return lis;
 else return [];
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
 B := Transpose(Matrix(b));
 return #a eq #b and &or[IsConsistent(B,M) and IsConsistent(M,B) : M in mm];
end function;

// qua 
// INPUT: two vectors a,b and a matrix M
// OUTPUT: Transpose(a)*M*b

qua := function(a,b,M);
 u := Eltseq(a);
 v := Eltseq(b);
 return (Matrix(Rationals(),1,#u,u)*Matrix(Rationals(),M)*Matrix(Rationals(),#v,1,v))[1,1];
end function;

// GensUpTo
// INPUT: the rays of a fan, a positive integer m
// OUTPUT: the classes of generators of the Cox ring 
// of Bl_eP up to multiplicity m

GensUpTo := function(ra,m);
 Q := Rationals();
 F := Fan(ra,[[i,i+1] : i in [1..#ra-1]] cat [[1,#ra]]);
 X<[x]> := ToricVariety(Q,F);
 J := IrrelevantIdeal(X);
 R := Parent(J.1);
 I := [Ideal([R!f : f in Basis(LatticeIdeal(ra))])];
 lis := MinimalBasis(I[1]);
 mul := [1 : i in [1..#lis]];
 for n in [2..m] do
  Append(~I,Saturation(I[1]^n,J));
  new := [p : p in NormalForm(Basis(I[n]),&+[I[i]*I[n-i] : i in [1..Floor(n/2)]]) | p ne 0];
  lis := lis cat new;
  mul := mul cat [n : i in [1..#new]];
 end for;
 Mat := Transpose(Matrix(Gradings(X)));
 E := ToricLattice(Nrows(Mat));
 Cl := ToricLattice(Ncols(Mat));
 cl := hom<E->Cl|Mat>;
 classes := [Eltseq(Zero(Cl)) cat [1]] cat [Eltseq(cl(e)) cat [0] : e in Basis(E)];
 for i in [1..#lis] do
  f := lis[i];
  mu := mul[i];
  w := cl(E!Exponents(Monomials(f)[1]));
  Append(~classes,Eltseq(w) cat [-mu]);
 end for;
 return classes,lis;
end function;


// IntMatWeil
// INPUT: a list of two-dimensional rays
// OUTPUT: the intersection matrix of the toric invariant 
// divisors of the surface whose fan is defined by the rays

IntMatWeil := function(ra)
  F := Fan(ra,[[i,i+1] : i in [1..#ra-1]] cat [[1,#ra]]);
 M := ZeroMatrix(Rationals(),#ra,#ra);
 for i in [1..#ra] do
  ind := [j : j in [1..#ra] | j ne i and Cone([ra[i],ra[j]]) in F];
  v := Eltseq(Kernel(Matrix([ra[i]] cat [ra[j] : j in ind])).1);
  for j in [1..#ra] do
   if j in ind then 
    M[i,j] := 1/Abs(Determinant(Matrix([ra[i],ra[j]])));
   end if;
  end for;
  M[i,i] := v[1]/v[2]*M[i,ind[1]];
 end for;
 return M;
end function;


// IntMatCl
// INPUT: a list of rays
// OUTPUT: the intersection matrix of the toric
// surface whose fan is defined by the rays

IntMatCl := function(ra)
 K := Rationals();
 FF := Fan(ra,[[i,i+1] : i in [1..#ra-1]] cat [[1,#ra]]); 
 X := ToricVariety(K,FF);
 M := IntMatWeil(ra);
 Mat := Transpose(Matrix(Gradings(X)));
 E := ToricLattice(Nrows(Mat));
 Cl := ToricLattice(Ncols(Mat));
 f := hom<E->Cl|Mat>;
 bas := [Preimage(f,b) : b in Basis(Cl)];
 return Matrix(#bas,#bas,[qua(a,b,M) : a,b in bas]);
end function;


// IntMatBl
// INPUT: a list of rays
// OUTPUT: the intersection matrix of Bl_eP, where P is the toric
// surface whose fan is defined by the rays

IntMatBl := function(ra)
 K := Rationals();
 return DiagonalJoin(IntMatCl(ra),Matrix(K,1,1,[-1]));
end function;


// PseudoEff
// INPUT: a list of rays, a positive integer m
// OUTPUT: the cone generated by classes of 
// generators of the Cox ring of Bl_eP up to 
// multiplicity m

PseudoEff := function(ra,m)
 return Cone(GensUpTo(ra,m));
end function;


// PseudoNef
// INPUT: a list of rays, a positive integer m
// OUTPUT: the dual of the cone generated by classes of 
// generators of the Cox ring of Bl_eP up to 
// multiplicity m

PseudoNef := function(ra,m)
 Eff := Cone(GensUpTo(ra,m));
 M := IntMatBl(ra);
 return Dual(Eff*M);
end function;


// IsMDS
// INPUT: a list of rays, a positive integer m
// OUTPUT: true if there is a pseudo generating
// set in multiplicity up to m

IsMDS := function(ra,m)
 S := GensUpTo(ra,m);
 Eff := Cone(S);
 M := IntMatBl(ra);
 for F in Facets(Eff) do
  R := Rays(F);
  MM := Matrix(#R,#R,[qua(a,b,M) : a,b in R]);
  if not IsNegativeSemiDefinite(MM) 
   then return false;
  end if;
 end for;
 Nef := Dual(Eff*M);
 rr := Rays(Nef);
 Cl := Ambient(Eff);
 Test := true;
 for D in rr do
  perp := [i : i in [1..#S] | qua(D,S[i],M) eq 0];
  Test := Test and Cl!Eltseq(D) in &meet[Cone(Remove(S,i)) : i in perp];
 end for;
 return Test;
end function;
