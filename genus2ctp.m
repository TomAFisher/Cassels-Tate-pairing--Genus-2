
//////////////////////////////////////////////////////////////
//                                                          //
//    MAGMA code for computing the Cassels-Tate pairing     //
//       on the 2-Selmer group of a genus 2 Jacobian        //
//                                                          //
//            T Fisher           February 2024              //
//                                                          //
//////////////////////////////////////////////////////////////

ZZ := Integers();
QQ := Rationals();
MC := MonomialCoefficient;
MD := MonomialsOfDegree;
Coeff := Coefficient;
Deriv := Derivative;
PRIM := func<xx|[x/d : x in Eltseq(xx)] where d is RationalGCD(Eltseq(xx))>;

declare verbose CasselsTatePairing,2; 

AddAttribute(CrvHyp,"etale_algebra_data");
AddAttribute(CrvHyp,"has_rational_trope");

twistedkummer := recformat<
        surface : Sch,
        pushout : AlgMatElt,
         selmer : Tup,
         points : SeqEnum,
  	  nodes : SeqEnum,
    searchbound : RngIntElt,
    coveringmap : MapSch,
 quadraticforms : Tup,
      badprimes : SetEnum >;
    
wedge := func<M|Matrix(BaseRing(M),6,6,
    [M[r[1],s[1]]*M[r[2],s[2]] - M[r[1],s[2]]*M[r[2],s[1]] : r,s in ii])
    where ii is [[1,2],[1,3],[2,3],[1,4],[4,2],[3,4]]>;

ASM := func<x|Matrix(Universe(Eltseq(x)),4,4,[
  [    0,   x[1],  x[2],  x[4] ],
  [ -x[1],     0,  x[3], -x[5] ],
  [ -x[2], -x[3],     0,  x[6] ],
  [ -x[4],  x[5], -x[6],    0] ])>;  

star := func<A|Matrix(BaseRing(A),4,4,[
  [   0,    A[4,3], A[2,4], A[3,2] ],
  [ A[3,4],    0,   A[4,1], A[1,3] ],
  [ A[4,2], A[1,4],    0,   A[2,1] ],
  [ A[2,3], A[3,1], A[1,2],    0   ]])>;

// Defining polynomial for the etale algebra corresponding to the
// set of partitions of the 6 Weierstrass points into 2 sets of 3.
// If the roots of f are t1, ..., t6 then this polynomial has
// root t1*t2*t3 + t4*t5*t6.

function Degree10Poly(f)
  f0,f1,f2,f3,f4,f5 := Explode(Coefficients(f));
  assert Coeff(f,6) eq 1;
  v := Parent(f).1;
  poly := v^10 - f3*v^9 + (-9*f0 - f1*f5 + f2*f4)*v^8 + (6*f0*f3 +
    f0*f4*f5 + f1*f2 + 2*f1*f3*f5 - f1*f4^2 - f2^2*f5)*v^7 + (27*f0^2
    + 9*f0*f1*f5 - 9*f0*f2*f4 + f0*f2*f5^2 + 3*f0*f3^2 - 3*f0*f3*f4*f5
    + f0*f4^3 + f1^2*f4 - f1^2*f5^2 - 3*f1*f2*f3 + f1*f2*f4*f5 +
    f2^3)*v^6 + (-9*f0^2*f3 - 3*f0^2*f4*f5 - 2*f0^2*f5^3 - 3*f0*f1*f2
    - 16*f0*f1*f3*f5 + 4*f0*f1*f4^2 + 2*f0*f1*f4*f5^2 + 4*f0*f2^2*f5 +
    f0*f2*f3*f4 + 2*f0*f2*f3*f5^2 - f0*f2*f4^2*f5 - 2*f1^3 +
    2*f1^2*f2*f5 + 2*f1^2*f3*f4 - f1^2*f3*f5^2 - f1*f2^2*f4)*v^5 +
    (-27*f0^3 - 30*f0^2*f1*f5 + 18*f0^2*f2*f4 - 2*f0^2*f2*f5^2 -
    15*f0^2*f3^2 + 16*f0^2*f3*f4*f5 + f0^2*f3*f5^3 - 4*f0^2*f4^3 -
    f0^2*f4^2*f5^2 - 2*f0*f1^2*f4 + 6*f0*f1^2*f5^2 + 16*f0*f1*f2*f3 -
    3*f0*f1*f2*f5^3 - f0*f1*f3^2*f5 - 2*f0*f1*f3*f4^2 +
    f0*f1*f3*f4*f5^2 - 4*f0*f2^3 - 2*f0*f2^2*f3*f5 + f0*f2^2*f4^2 +
    f1^3*f3 - 3*f1^3*f4*f5 + f1^3*f5^3 - f1^2*f2^2 +
    f1^2*f2*f3*f5)*v^4 + (9*f0^3*f5^3 + 39*f0^2*f1*f3*f5 -
    14*f0^2*f1*f4*f5^2 + f0^2*f1*f5^4 - 11*f0^2*f2*f3*f5^2 +
    2*f0^2*f2*f4*f5^3 - 3*f0^2*f3^3 + 3*f0^2*f3^2*f4*f5 -
    f0^2*f3^2*f5^3 + 9*f0*f1^3 - 14*f0*f1^2*f2*f5 - 11*f0*f1^2*f3*f4 +
    6*f0*f1^2*f3*f5^2 + 3*f0*f1^2*f4^2*f5 - f0*f1^2*f4*f5^3 +
    3*f0*f1*f2^2*f5^2 + 3*f0*f1*f2*f3^2 - f0*f1*f2*f3*f4*f5 + f1^4*f5
    + 2*f1^3*f2*f4 - f1^3*f2*f5^2 - f1^3*f3^2)*v^3 + (36*f0^3*f1*f5 -
    6*f0^3*f2*f5^2 + 18*f0^3*f3^2 - 24*f0^3*f3*f4*f5 - 4*f0^3*f3*f5^3
    + 8*f0^3*f4^2*f5^2 - f0^3*f4*f5^4 - 6*f0^2*f1^2*f4 -
    7*f0^2*f1^2*f5^2 - 24*f0^2*f1*f2*f3 - 4*f0^2*f1*f2*f4*f5 +
    10*f0^2*f1*f2*f5^3 + 8*f0^2*f1*f3^2*f5 + 8*f0^2*f1*f3*f4^2 -
    8*f0^2*f1*f3*f4*f5^2 + f0^2*f1*f3*f5^4 + 8*f0^2*f2^2*f3*f5 -
    2*f0^2*f2^2*f4*f5^2 - 2*f0^2*f2*f3^2*f4 + f0^2*f2*f3^2*f5^2 -
    4*f0*f1^3*f3 + 10*f0*f1^3*f4*f5 - 4*f0*f1^3*f5^3 + 8*f0*f1^2*f2^2
    - 8*f0*f1^2*f2*f3*f5 - 2*f0*f1^2*f2*f4^2 + f0*f1^2*f2*f4*f5^2 +
    f0*f1^2*f3^2*f4 - f1^4*f2 + f1^4*f3*f5)*v^2 + (-8*f0^4*f5^3 -
    24*f0^3*f1*f3*f5 + 16*f0^3*f1*f4*f5^2 - 2*f0^3*f1*f5^4 +
    8*f0^3*f2*f3*f5^2 - f0^3*f2*f5^5 + 8*f0^3*f3^3 - 8*f0^3*f3^2*f4*f5
    + 3*f0^3*f3^2*f5^3 - 8*f0^2*f1^3 + 16*f0^2*f1^2*f2*f5 +
    8*f0^2*f1^2*f3*f4 - 6*f0^2*f1^2*f3*f5^2 - 8*f0^2*f1^2*f4^2*f5 +
    3*f0^2*f1^2*f4*f5^3 - 8*f0^2*f1*f2^2*f5^2 - 8*f0^2*f1*f2*f3^2 +
    8*f0^2*f1*f2*f3*f4*f5 - f0^2*f1*f2*f3*f5^3 - f0^2*f1*f3^3*f5 -
    2*f0*f1^4*f5 + 3*f0*f1^3*f2*f5^2 + 3*f0*f1^3*f3^2 -
    f0*f1^3*f3*f4*f5 - f1^5*f4)*v + 8*f0^4*f3*f5^3 - 4*f0^4*f4*f5^4 +
    f0^4*f5^6 - 4*f0^3*f1*f2*f5^3 - 12*f0^3*f1*f3^2*f5 +
    8*f0^3*f1*f3*f4*f5^2 - 2*f0^3*f1*f3*f5^4 + f0^3*f2^2*f5^4 -
    2*f0^3*f2*f3^2*f5^2 + f0^3*f3^4 + 8*f0^2*f1^3*f3 -
    4*f0^2*f1^3*f4*f5 + 2*f0^2*f1^3*f5^3 + 8*f0^2*f1^2*f2*f3*f5 -
    2*f0^2*f1^2*f2*f4*f5^2 - 2*f0^2*f1^2*f3^2*f4 + f0^2*f1^2*f3^2*f5^2
    - 4*f0*f1^4*f2 - 2*f0*f1^4*f3*f5 + f0*f1^4*f4^2 + f1^6;
  return poly;
end function;

// Given a genus 2 curve C over a field k, returns true if one of the
// 16 ways of partitioning the 6 Weierstrass points of C into two sets
// of odd size is defined over k.

function HasRationalTrope(C)
  if assigned C`has_rational_trope then
    return C`has_rational_trope;
  end if;
  P := PolynomialRing(BaseRing(C));
  f := Evaluate(-Equation(C),[P.1,0,1]);
  assert C eq HyperellipticCurve(f);
  ans := true;
  if #Roots(f) eq 0 then
    f1 := f/Coeff(f,6);
    while true do
      poly10 := Degree10Poly(f1);
      if #Roots(poly10) eq 0 then ans := false; break; end if;
      if Discriminant(poly10) ne 0 then break; end if;
      f1 := Evaluate(f1,P.1+1);
    end while;
  end if;
  C`has_rational_trope := ans;
  return ans;
end function;

// Creates the etale algebra for the set of Weierstrass points

function Degree6Algebra(C)
  if assigned C`etale_algebra_data then
    L,LL,iso := Explode(C`etale_algebra_data);
    return L,LL,iso;
  end if;
  P := PolynomialRing(BaseRing(C));
  f := Evaluate(-Equation(C),[P.1,0,1]);
  assert C eq HyperellipticCurve(f);
  assert Degree(f) eq 6; 
  L := quo<P|f/Coeff(f,6)>;
  LL,iso := AbsoluteAlgebra(L);
  C`etale_algebra_data := <L,LL,iso>;  
  return L,LL,iso;
end function;

// Creates the etale algebra for the set of (3,3)-partitions of the
// Weierstrass points

function Degree10Algebra(C)
  assert assigned C`etale_algebra_data;
  if #C`etale_algebra_data eq 5 then
    return d[4],d[5] where d is C`etale_algebra_data;
  end if;
  function DecomposeEtaleAlgebra(A)
    k := BaseRing(A);
    AA1,iota1 := AbsoluteAlgebra(A);
    if k cmpeq QQ then return AA1,iota1; end if;
    nn := NumberOfComponents(AA1);
    AA := CartesianProduct([RelativeField(k,AA1[i]) : i in [1..nn]]);
    iota := map<A->AA|x:->AA!iota1(x),y:->(AA1!y) @@ iota1>;
    assert iota(k.1) eq AA!<AA[i]!k.1 : i in [1..nn]>;
    return AA,iota;
  end function;
  // Finds the cubic factors of f whose constant terms sum to sigma
  function CubicFactors(f,sigma)
    assert Degree(f) eq 6 and Coeff(f,6) eq 1;
    F := Parent(sigma);
    qq := PolynomialRing(F)![Evaluate(f,0),sigma,1];  
    if Discriminant(qq) eq 0 then return []; end if;
    Fplus := IsIrreducible(qq) select ext<F|qq> else F;
    ff := Factorization(PolynomialRing(Fplus)!f);
    degs := [Degree(ff[i,1]): i in [1..#ff]];
    SS := [S : S in Subsets({1..#ff}) | &+[ZZ|degs[i] : i in S] eq 3];
    SS := {{S,{i : i in [1..#ff] | i notin S}} : S in SS};
    ccc := [[&*[ff[i,1] : i in ii] : ii in S] : S in SS];
    ccc := [cc : cc in ccc | &+[Coeff(c,0): c in cc] eq sigma];
    assert #ccc eq 1;
    return ccc[1];
  end function;
  P := PolynomialRing(BaseRing(C));
  f := Evaluate(-Equation(C),[P.1,0,1]);
  assert C eq HyperellipticCurve(f);
  f /:= Coeff(f,6);
  f1 := f;
  shift := 0;
  while true do
    poly10 := Degree10Poly(f1);
    cubiclist := <>;
    if Discriminant(poly10) ne 0 then 
      L := quo<P|poly10>;
      LL,iso := DecomposeEtaleAlgebra(L);
      rho := iso(L.1);
      nLL := NumberOfComponents(LL);
      for ctr in [1..nLL] do
        cc := CubicFactors(f1,rho[ctr]);
        if #cc eq 0 then break; end if;
        cc := [Evaluate(c,Universe(cc).1-shift): c in cc];
        assert cc[1]*cc[2] eq f;
        Append(~cubiclist,cc);
      end for;
      if #cubiclist eq nLL then break; end if;
    end if;
    vprint CasselsTatePairing,2 : "Making a shift";
    f1 := Evaluate(f1,P.1+1);
    shift +:= 1;
  end while;
  C`etale_algebra_data cat:= <LL,cubiclist>;
  return LL,cubiclist; 
end function;

// Computes the true (i.e. unfaked) 2-Selmer group of J.
// J should either be the Jacobian of a genus 2 curve defined over Q,
// or the base change of such to a (quadratic) number field k.
// The genus 2 curve must be of the form y^2 = f(x) where f has degree 6.

intrinsic TwoSelmerGroupTrue(J::JacHyp:checking := false) -> GrpAb,Map,GrpAbElt
{Computes the true (i.e. unfaked) 2-Selmer group of the genus 2 Jacobian J. The genus 2 curve must be defined over Q (or the base change of such to a number field) and of the form y^2 = f(x) where f has degree 6.}
  k := BaseRing(J);
  C := Curve(J);
  canontriv := HasRationalTrope(C);
  require forall{ a : a in Coefficients(Equation(C)) |
    IsCoercible(QQ,a) } : "The genus 2 curve must be defined over Q";
  P := PolynomialRing(QQ);
  f := Evaluate(-Equation(C),[P.1,0,1]);
  require Degree(f) eq 6 :
    "The genus 2 curve must be given by a degree 6 model";
  C0 := HyperellipticCurve(f);
  assert C eq BaseChange(C0,k);  
  C1 := SimplifiedModel(ReducedMinimalWeierstrassModel(C0));
  f1 := Evaluate(-Equation(C1),[P.1,0,1]);
  assert C1 eq HyperellipticCurve(f1);
  assert Degree(f1) in [5,6];
  if k cmpeq QQ then
    J1 := Jacobian(C1);
    vprint TwoDescent,1 : "Computing the 2-Selmer group (using Stoll's code)";
    vtime TwoDescent,1 : bound,dimS2,Sdata,_,S2 := TwoSelmerGroupData(J1);
    selbasis := Sdata[1];
    assert dimS2 eq #Generators(S2);
  else
    J1 := Jacobian(BaseChange(C1,k));
    vprint TwoDescent,1 : "Computing the 2-Selmer group (using Bruin's code)";
    vtime TwoDescent,1 : S2,S2map := TwoSelmerGroupOld(J1);
    dimS2 := #Generators(S2);
    selbasis := [S2.i @@ S2map : i in [1..dimS2]];
    assert canontriv or (selbasis[dimS2] eq 1);
  end if;
  dimfake := dimS2 - (canontriv select 0 else 1);
  if k cmpeq QQ and checking then
    assert dimfake eq #Sdata[1] - #Sdata[2] + #Sdata[3];
    fact := [ a[1] : a in Factorization(f) ];
    oddfactor := exists{ a : a in fact | IsOdd(Degree(a)) };    
    HaveQuadraticSubextension := canontriv and (not oddfactor);
    assert #Sdata[3] eq (HaveQuadraticSubextension select 1 else 0);
    rank2tors := #fact - 1 - (oddfactor select 1 else 0);
    T,Tmap := TorsionSubgroup(J);
    assert rank2tors eq #[x : x in InvariantFactors(T) | IsEven(x)];
    assert bound + rank2tors + (IsOdd(J) select 1 else 0) eq dimS2;
  end if;
  flag,iso := IsIsomorphic(C0,C1);
  assert flag;
  de := DefiningEquations(iso);
  RR := Universe(de);
  mat := Matrix(QQ,2,2,[MC(de[i],RR.j): i,j in [1,3]])^(-1);
  a,b,c,d := Explode(Eltseq(mat));
  la := QQ!(f1/f^mat);
  assert la*(a*d - b*c) ne 0;
  assert f1 eq la*(c*x + d)^6*Evaluate(f,(a*x + b)/(c*x + d))
    where x is P.1;
  L := Degree6Algebra(C);
  theta := L.1;
  Pk := PolynomialRing(k);
  if Degree(f1) eq 5 then
    LL := quo<Pk|ExactQuotient(f,P.1 - a/c)>;
    theta := LL.1;
  end if;
  theta1 := (d*theta - b)/(-c*theta + a);
  assert Evaluate(f1,theta1) eq 0;
  selbasis := [Evaluate(Pk!xi,theta1) : xi in selbasis];
  if Degree(f1) eq 5 then 
    e := Evaluate(h,L.1)/Evaluate(h,a/c) where h is Modulus(LL);
    assert e^2 eq e;
    selbasis := [(1-e)*Evaluate(Pk!xi,L.1) + e*Norm(xi): xi in selbasis];
  end if;
  Lk := CartesianProduct(L,k);
  function MakeTrue(xi);
    flag,m := IsSquare(Norm(xi));
    assert flag;
    return Lk!<xi,m>;
  end function;
  sel_gens := [MakeTrue(selbasis[i]): i in [1..dimfake]];
  if (not canontriv) then
    sel_gens := [Lk!<1,-1>] cat sel_gens;
  end if;
  c := canontriv select S2!0 else S2.1;
  assert #sel_gens eq dimS2;
  S2map := map< S2 -> Lk |
    s :-> <&*[L| sel_gens[i,1]^ss[i] : i in [1..dimS2]],
           &*[k| sel_gens[i,2]^ss[i] : i in [1..dimS2]]>
    where ss is Eltseq(s)>;
  return S2,S2map,c;
end intrinsic;

// Checks whether (la,H) is a model for a 2-covering of the
// the Jacobian of y^2 = f(x).

function IsModel(f,model)
  la,H := Explode(model);
  R := Parent(H);
  u0,u1,u2,u3,u4,u5 := Explode([R.i : i in [1..6]]);
  G := u0*u5 + u1*u4 + u2*u3;
  P := Parent(f);
  M := la*P.1*(2*SymmetricMatrix(G)) - (2*SymmetricMatrix(H));
  f6 := Coeff(f,6);
  return Determinant(M) eq la^6*(-1/f6)*f;
end function;

// Finds a 6 by 6 matrix T with the given determinant such
// that G^T = u0*u5 + u1*u4 + u2*u3

function StandardiseQuadraticForm(G,det)
  R := Parent(G);
  assert BaseRing(R) cmpeq QQ;
  u0,u1,u2,u3,u4,u5 := Explode([R.i : i in [1..6]]);
  Id := IdentityMatrix(QQ,3);
  IS := IsotropicSubspace(G);
  assert Dimension(IS) eq 3;
  M := Matrix(Basis(IS));
  M := LLL(Matrix(Basis(PureLattice(Lattice(M)))));
  _,_,T := SmithForm(ChangeRing(M,ZZ));
  T := ChangeRing(Transpose(T^(-1)),QQ);
  mat := SymmetricMatrix(G^T);
  N1 := Matrix(QQ,3,3,[mat[i,j+3]: i,j in [1..3]]);
  T *:= DiagonalJoin(Id,N1^(-1));
  mat := SymmetricMatrix(G^T);
  N2 := Matrix(QQ,3,3,[mat[i+3,j+3]: i,j in [1..3]]);
  T *:= BlockMatrix(2,2,[Id,-N2/2,0,Id]);
  assert G^T eq 2*(u0*u3 + u1*u4 + u2*u5);
  T *:= Matrix(QQ,6,6,[<i,[1,2,3,6,5,4][i],1>: i in [1..6]]);
  T *:= DiagonalMatrix(QQ,[1,1,1,1/2,1/2,1/2]);
  assert G^T eq u0*u5 + u1*u4 + u2*u3;
  if Determinant(T) ne det then
    T *:= Matrix(QQ,6,6,[<i,[1,2,4,3,5,6][i],1>: i in [1..6]]);
  end if;
  assert Determinant(T) eq det;
  return T;
end function;

// Computes a minimised and reduced model (pair of quadratic forms
// in 6 variables) representing the given 2-Selmer element.

function MinRedQuadricIntersection(C,eps:checking:=false)
  P := PolynomialRing(BaseRing(C));
  f := Evaluate(-Equation(C),[P.1,0,1]);
  assert Degree(f) eq 6;
  assert C eq HyperellipticCurve(f);
  R := PolynomialRing(QQ,6);
  mons := MD(R,2);
  P := PolynomialRing(R);
  f5 := Coeff(f,5);
  f6 := Coeff(f,6);
  LL := quo<P|P!(f/f6)>;
  xi,m := Explode(eps);
  LHS := (LL!P!xi)*(&+[LL.1^(i-1)*R.i: i in [1..6]])^2;
  Q4 := R!Coeff(LHS,4);
  Q5 := R!Coeff(LHS,5);  
  G := Q5/2;
  H := (f6*Q4 - f5*Q5)/(2*f6);
  T := StandardiseQuadraticForm(G,1/m);
  G := G^T;
  H := H^T;
  if checking then 
    GG := 2*SymmetricMatrix(G);
    HH := 2*SymmetricMatrix(H);
    assert Determinant(Parent(f).1*GG - HH) eq -(1/f6)*f;
    theta := Parent(xi).1;
    assert Evaluate(f,theta) eq 0;
    df := Evaluate(Deriv(f),theta);
    aa := [&+[T[i,j]*theta^(i-1): i in [1..6]]: j in [1..6]];
    A := ASM(aa);
    assert Evaluate(G,Reverse(aa)) eq Pfaffian(A);
    assert Evaluate(H,Reverse(aa)) eq theta*Pfaffian(A);
    assert xi eq df/(2*f6*Pfaffian(A));
    assert m eq 1/Determinant(T);
    assert Norm(xi) eq m^2;
  end if;
  model := <1/d,H/d> where d is RationalGCD(Coefficients(H));
  assert IsModel(f,model);
  model := ReduceG2Model(f,model);
  model := MinimiseG2Model(f,model);  
  model := ReduceG2Model(f,model);
  if model[1] lt 0 then model := <-m : m in model>; end if;
  assert IsModel(f,model);
  return <model[1],[MC(model[2],mon): mon in mons]>;
end function;

intrinsic TwoDescentGenus2(J::JacHyp) -> GrpAb,Map
{Computes models (pairs of quadratic forms in 6 variables) representing the non-trivial elements of the 2-Selmer group of the genus 2 Jacobian J. The genus 2 curve must be defined over Q and of the form y^2 = f(x) where f has degree 6.}
  C := Curve(J);
  require BaseRing(C) cmpeq QQ : 
    "The genus 2 curve must be defined over the rationals";
  L := Degree6Algebra(C);
  S2,S2map,c := TwoSelmerGroupTrue(J);
  vprint TwoDescent,1 : "Computing models for the 2-Selmer elements";
  models := [];
  S2elts := [x : x in S2 | x ne S2!0];
  vtime TwoDescent,1 : for g in S2elts do
    vprintf TwoDescent,1 : "%o",Eltseq(g);
    model := MinRedQuadricIntersection(C,S2map(g));
    vprint TwoDescent,1 : " ->",model;
    Append(~models,model);
  end for;
  S2map := map<S2 -> models | x :-> models[Position(S2elts,x)]>;
  return S2,S2map,c;
end intrinsic;

// Simplifies a matrix defined over L = k[x]/(f) by multiplying
// it by a unit in L.

function SimplifySkewMatrix(C,A)
  L,LL,iso := Degree6Algebra(C);
  assert L eq BaseRing(A);
  nLL := NumberOfComponents(LL);
  mats := <>;
  for ctr in [1..nLL] do
    F := LL[ctr];
    OF := RingOfIntegers(F);
    mat := Matrix(F,4,4,[iso(A[i,j])[ctr]: i,j in [1..4]]);
    mat *:= Basis(LLL(ideal<OF|Eltseq(mat)>^(-1)))[1];
    Append(~mats,mat);
  end for;
  ans := [(LL!<mats[r,i,j]:r in [1..nLL]>) @@ iso:i,j in [1..4]];
  return Matrix(L,4,4,ans);
end function;

// Converts a model (pair of quadratic forms in 6 variables) to an (unfaked)
// 2-Selmer group element. (See Section 2.5 of the paper.)

function TwoSelmerElement(C,model:simplify:=true)
  la,coeffs := Explode(model);
  R := PolynomialRing(BaseRing(C),6);
  u0,u1,u2,u3,u4,u5 := Explode([R.i : i in [1..6]]);
  mons := MD(R,2);
  G := u0*u5 + u1*u4 + u2*u3;
  H := &+[coeffs[i]*mons[i] : i in [1..#mons]];
  L := Degree6Algebra(C);
  GG := 2*SymmetricMatrix(G);
  HH := 2*SymmetricMatrix(H);
  km := KernelMatrix(la*L.1*GG - HH);
  assert Nrows(km) eq 1;
  A := ASM(Eltseq(km));
  if simplify then A := SimplifySkewMatrix(C,A); end if;
  df := Evaluate(Deriv(Modulus(L)),L.1); // f'(theta)/f6
  xi := Pfaffian(A)/df;
  N := Matrix(6,6,[EltseqPad(A[i,j]): i,j in [1..4] | i lt j]);
  m := -1/8*Determinant(N);
  assert Norm(xi) eq m^2;
  return <xi,m>,A;
end function;

intrinsic TwoSelmerElementsGenus2(J::JacHyp,S2map::Map) -> Map
{Converts each model (pair of quadratic forms in 6 variables) representing a 2-covering of the genus 2 Jacobian J to an (unfaked) 2-Selmer group element. The given map should be from the abstract 2-Selmer group to the space of models. Such a map is returned by TwoDescentGenus2.}
  S2 := Domain(S2map);
  S2elts := [x : x in S2];
  C := Curve(J);
  id := <L!1,1> where L is Degree6Algebra(C);
  aa := [x eq S2!0 select id else TwoSelmerElement(C,S2map(x)) : x in S2elts];
  return map<S2 -> aa | x :-> aa[Position(S2elts,x)]>;
end intrinsic;

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////

// The following functions are used to construct the "inverse map" from
// Selmer group elements represented by pairs (xi,m) to the abstract
// abelian group.

function Adjustment(k,xi,iso,OLL)
  LL := Codomain(iso);
  ff := Factorization(iso(xi)[1]*OLL[1]);
  pp := {f[1] meet BaseRing(OLL[1]) : f in ff | IsOdd(f[2])};
  if k cmpeq QQ then
    ans := &*{ZZ|Generator(p): p in pp};
  else
    ans := 1;
    for p in pp do
      flag,elt := IsPrincipal(p);
      assert flag;
      ans *:= elt;
    end for;
  end if;
  return ans;  
end function;

function ApplyTest(test,e)
  i,pr,resmap,pi := Explode(test);
  u := Valuation(e[i],pr);
  assert IsEven(u);
  a := resmap(e[i]/pi^u);
  assert a ne 0;
  return IsSquare(a) select 0 else 1;
end function;

function GetTests(k,sel_basis,A,S,iso,OLL)
  LL := Codomain(iso);
  nLL := NumberOfComponents(LL);
  dd := [Adjustment(k,s[1],iso,OLL) : s in sel_basis];
  elts := A cat [dd[i]*sel_basis[i,1] : i in [1..#sel_basis]];
  V := VectorSpace(GF(2),#elts);
  U := sub<V|>;
  ee := [iso(e): e in elts];
  tests := <>;
  if k cmpeq QQ then
    S0 := S;
  else
    Ok := RingOfIntegers(k);
    S0 := {Generator(p meet ZZ) : p in S};
  end if;
  p0 := 2;
  ctr := 0;
  vecs := [];
  while true do
    repeat p0 := NextPrime(p0); until p0 notin S0;
    ctr +:= 1;
    if k cmpeq QQ then
      pp := [p0];
    else
      pp := [q[1] : q in Decomposition(Ok,p0)];
    end if;
    for p in pp do
      if k cmpeq QQ then
	pi := p;
      else
	flag,pi := IsPrincipal(p);
	assert flag;
      end if;
      for i in [1..nLL] do
        for pr in Decomposition(OLL[i],p) do	
          _,resmap := ResidueClassField(pr[1]);
          test := <i,pr[1],resmap,pi>;
          vec := V![ApplyTest(test,e): e in ee];
          if vec notin U then
            ctr := 0;
            U +:= sub<V|vec>;
  	    Append(~vecs,vec);
            Append(~tests,test);
          end if;
        end for;
      end for;
    end for;
    if ctr gt 20 then
      M := Matrix(GF(2),#tests,#elts,vecs);
      km := KernelMatrix(Transpose(M));
      slist := [&*[elts[j] : j in [1..#elts] | km[i,j] eq 1]
                           : i in [1..Nrows(km)]];
      if forall{ a : a in iso(s), s in slist | IsSquare(a) } then
        break;
      end if;
      print "problem extracting square roots";
      ctr := 0;
    end if;
  end while;
  return tests,M,km,dd;
end function;

function MyInverse(k,sel_basis,elt,iso,OLL,A,tests,M,km,dd)
  L := Domain(iso);
  LL := Codomain(iso);
  nLL := NumberOfComponents(LL);
  r0 := Adjustment(k,elt[1],iso,OLL);
  e := iso(r0*elt[1]);
  vec := Vector(GF(2),#tests,[ApplyTest(t,e): t in tests]);
  soln := Solution(Transpose(M),vec);
  degs := [ZZ|Degree(LL[i])/Degree(k): i in [1..nLL]];
  for loopvar in [1..2] do
    ans := [ZZ|soln[#A+i] : i in [1..#sel_basis]];
    prod := <&*[sel_basis[i,j]^ans[i] : i in [1..#sel_basis]]: j in [1,2]>;
    r := r0*&*[k| A[j] : j in [1..#A] | soln[j] eq 1];
    r *:= &*[dd[i]^ans[i] : i in [1..#sel_basis]];
    nu := < Sqrt(a): a in iso(elt[1]/(r*prod[1])) > @@ iso;
    RHS := <r*nu^2*prod[1],r^3*Norm(nu)*prod[2]>;
    assert elt in [RHS,<RHS[1],-RHS[2]>];
    if elt[2] eq -RHS[2] and
        exists(j){j : j in [1..nLL] | IsOdd(degs[j])} then
      nu *:= (<i eq j select -1 else 1: i in [1..nLL]> @@ iso);
      RHS := <r*nu^2*prod[1],r^3*Norm(nu)*prod[2]>;
    end if;
    if elt eq RHS then return ans; end if;
    assert Nrows(km) eq 1;
    soln +:= km[1];
  end for;
  assert false;
  return 0;
end function;

function MyRingOfIntegers(F,k)
  if k cmpne QQ then
    if F eq k then
      F := ext<k|Polynomial(k,[-1,1]):DoLinearExtension>;
    else
      F := RelativeField(k,F);
    end if;
  end if;
  return RingOfIntegers(F);
end function;  

function GetInverse(J,sel)
  S2 := Domain(sel);
  sel_basis := [sel(S2.i): i in [1..#Generators(S2)]];
  S := BadPrimes(Curve(J));
  k := BaseRing(J);
  if k cmpeq QQ then
    A := [-1] cat S;
  else
    assert #ClassGroup(k) eq 1; // for now
    G,Gmap := pSelmerGroup(2,Set(S));
    A := [G.i @@ Gmap: i in [1..#Generators(G)]];
  end if;
  L,LL,iso := Degree6Algebra(Curve(J));
  nLL := NumberOfComponents(LL);
  assert forall{ i : i in [1..nLL] | LL[i]!k.1 eq iso(L!k.1)[i] };
  OLL := <MyRingOfIntegers(LL[i],k) : i in [1..nLL]>;
  Lk := CartesianProduct(L,k);
  tests,M,km,dd := GetTests(k,sel_basis,A,S,iso,OLL);
  assert Nrows(km) in [0,1];
  return map<Lk->S2|x:->MyInverse(k,sel_basis,x,iso,OLL,A,tests,M,km,dd)>;
end function;

intrinsic IsEqualInSelmer(J::JacHyp,sel1::Tup,sel2::Tup) -> BoolElt, RngElt, RngElt
{Determines whether sel1 = (xi1,m1) and sel2 = (xi2,m2) in the 2-Selmer group of the genus 2 Jacobian J are equal. If they are equal then the function also returns r and nu such that (xi1/xi2,m1/m2) = (r nu^2,r^3 Norm(nu)).}
  sel := <sel1[i]/sel2[i] : i in [1..2]>;
  S := BadPrimes(Curve(J));
  k := BaseRing(J);
  if k cmpeq QQ then
    A := [-1] cat S;
  else
    assert #ClassGroup(k) eq 1;
    G,Gmap := pSelmerGroup(2,Set(S));
    A := [G.i @@ Gmap: i in [1..#Generators(G)]];
  end if;
  L,LL,iso := Degree6Algebra(Curve(J));
  nLL := NumberOfComponents(LL);
  assert forall{ i : i in [1..nLL] | LL[i]!k.1 eq iso(L!k.1)[i] };
  OLL := <MyRingOfIntegers(LL[i],k) : i in [1..nLL]>;
  degs := [ZZ|Degree(LL[i])/Degree(k): i in [1..nLL]];
  _,_,km,dd := GetTests(k,[sel],A,S,iso,OLL);
  assert Nrows(km) le 2;
  V := VectorSpace(GF(2),Nrows(km));
  solns := [Eltseq(v*km): v in VectorSpace(GF(2),Nrows(km))];
  solns := [ s : s in solns | s[#A + 1] eq 1];
  for soln in solns do
    r := dd[1]*&*[k| A[j] : j in [1..#A] | soln[j] eq 1];
    nu := < Sqrt(a): a in iso(1/r*sel[1]) > @@ iso;
    if sel eq <r*nu^2,r^3*Norm(nu)> then
      return true,r,nu;
    end if;
    assert sel eq <r*nu^2,-r^3*Norm(nu)>;
    if exists(j){j : j in [1..nLL] | IsOdd(degs[j])} then
      nu *:= (<i eq j select -1 else 1: i in [1..nLL]> @@ iso);
      assert sel eq <r*nu^2,r^3*Norm(nu)>;
      return true,r,nu;
    end if;
  end for;
  return false,_,_;
end intrinsic;

function PreimageUnderWedge(BB)
  mats := [KernelMatrix(HorizontalJoin([ASM(BB[i]): i in ii])) :
    ii in [[3,5,6],[2,4,6],[1,4,5],[1,2,3]]];
  B := Transpose(VerticalJoin(mats))^(-1);
  DD := BB*wedge(B)^(-1);
  assert IsDiagonal(DD);
  d := [DD[i,i] : i in [1..6]];
  B := DiagonalMatrix([d[1]*d[2],d[1]*d[3],d[2]*d[3],d[1]*d[6]])*B;
  assert IsScalar(BB*wedge(B)^(-1));
  return B;
end function;

intrinsic IsEquivalent(J::JacHyp,model1::Tup,model2::Tup:checking:=true) -> BoolElt,AlgMatElt
{Determines whether models (pairs of quadratic forms in 6 variables) representing 2-coverings of a genus 2 Jacobian J are equivalent, and if so returns a 4 by 4 invertible matrix relating the models}
  k := BaseRing(J);
  sel1,A1 := TwoSelmerElement(Curve(J),model1);
  sel2,A2 := TwoSelmerElement(Curve(J),model2);
  flag,r,nu := IsEqualInSelmer(J,sel1,sel2);
  if not flag then return false,_; end if;
  D := DiagonalMatrix(k,[r,1,1,1]); // just need det = r
  A3 := nu*D*A2*D;
  assert Pfaffian(A1) eq Pfaffian(A3);
  // method 1
  EE := [Matrix(k,4,4,[<i,j,1>]): i,j in [1..4]];
  mat := Matrix(k,2*16,6*16,[&cat[EltseqPad(c): c in Eltseq(M)]
    : M in [E*A3 : E in EE] cat [A1*E : E in EE]]);
  km := KernelMatrix(mat);
  assert Nrows(km) eq 1;
  U := &+[km[1,i]*EE[i] : i in [1..16]];
  V := &+[km[1,16+i]*EE[i] : i in [1..16]];
  assert IsScalar(U*Transpose(V));
  U1 := U*D;
  // method 2 
  ii := [[1,2],[1,3],[2,3],[1,4],[4,2],[3,4]];
  N1 := Matrix(k,6,6,[EltseqPad(A1[i[1],i[2]]): i in ii]); 
  N2 := Matrix(k,6,6,[EltseqPad(A3[i[1],i[2]]): i in ii]); 
  U2 := PreimageUnderWedge(N1*N2^(-1))*D;
  // checking methods agree
  assert IsScalar(U1*U2^(-1));
  if checking then
    R := PolynomialRing(k,6);
    u0,u1,u2,u3,u4,u5 := Explode([R.i : i in [1..6]]);
    mons := MD(R,2);
    la1,coeffs1 := Explode(model1);
    H1 := (1/la1)*&+[coeffs1[i]*mons[i] : i in [1..#mons]];  
    la2,coeffs2 := Explode(model2);
    H2 := (1/la2)*&+[coeffs2[i]*mons[i] : i in [1..#mons]];
    assert H2 eq (1/Determinant(U1))*H1^wedge(U1);
    assert H2 eq (1/Determinant(U2))*H1^wedge(U2);
  end if;  
  return true,U1;
end intrinsic;

intrinsic IsSameSubgroup(J::JacHyp,sel1::Map,sel2::Map) -> BoolElt,Map
{Determines whether the two descriptions (sel1 and sel2) of the 2-Selmer group of the genus 2 Jacobian J are compatible, and if so returns the corresponding isomorphism of abstract groups.}
  G1 := Domain(sel1);
  G2 := Domain(sel2);
  dimG := #Generators(G1);
  assert #Generators(G2) eq dimG;
  inv := GetInverse(J,sel1);
  bb := [inv(sel2(G2.i)): i in [1..dimG]];
  M := Matrix(GF(2),dimG,dimG,[Eltseq(b): b in bb]);
  assert Determinant(M) ne 0;
  M := M^(-1);
  alpha := hom<G1->G2|[G2!Eltseq(M[i]) : i in [1..Nrows(M)]]>;
  return true,alpha;
end intrinsic;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

// Functions for computing the Cassels-Tate pairing

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

// The lambda's as defined in Section 3.5

function GetLambdas(F,f6,cubics)
  r0,r1,r2,r3 := Explode(Coefficients(cubics[1]));
  s0,s1,s2,s3 := Explode(Coefficients(cubics[2]));
  assert r3 eq 1;
  assert s3 eq 1;
  la1 := f6*(r0*s2 + r2*s0);
  la2 := f6*(r0 + s0);
  la3 := f6*(r1 + s1);
  return [F| la2^2 - la1*la3, la1, la2, la3, 1];
end function; 

// Extracting a square root as required by Proposition 3.19

function MySquareRoot(quartic)
  R4 := Parent(quartic);
  assert exists(j){j : j in [1..4] | MC(quartic,R4.1^2*R4.j^2) ne 0};
  a := MC(quartic,R4.1^2*R4.j^2);
  if j eq 1 then
    l := &+[MC(quartic,R4.1^3*R4.i)*R4.i : i in [2..4]];
    q := &+[MC(quartic,R4.1^2*R4.i*R4.j)*R4.i*R4.j : i,j in [2..4] | i le j];
    // Using the binomial expansion of (1 + t)^(1/2) :
    sqrt := R4.1^2 + (1/(2*a))*R4.1*l - (1/8)*(1/a^2)*(l^2 - 4*a*q);
  else
    success,sqrt := IsSquare(quartic/a);
    assert success;
  end if;
  assert quartic eq a*sqrt^2;
  return a,sqrt;
end function;

// Computing numerical approximations for the nodes

function KummerSurfaceNodes(f,quadrics,v,prec)
  L := Universe(v);
  R := Universe(quadrics);
  Z := ASM([R.j : j in [1..6]]);
  M := Z*ASM([Deriv(quadrics[2],R.j): j in [1..6]]);
  xi := Pfaffian(ASM(v))/Evaluate(Deriv(f),L.1);
  N := Matrix(6,6,[EltseqPad(v0): v0 in v]);
  f6 := Coeff(f,6);
  m := Determinant(N)/(8*f6^3);
  assert Norm(xi) eq m^2;
  N := N^(-1);
  CC := ComplexField(prec);
  rts := [r[1] : r in Roots(f,CC)];
  P := PreimageRing(L);
  xx := [Evaluate(P!xi,r): r in rts];
  yy := [Sqrt(x) : x in xx];
  check := &*yy/m;
  if Abs(check + 1) lt 10^(-prec/2) then
    yy[1] *:= -1;
  end if;
  check := &*yy/m;
  assert Abs(check - 1) lt 10^(-prec/2);
  PCC<x> := PolynomialRing(CC);
  LCC,quomap := quo<PCC|f>;
  vdm := Matrix(CC,6,6,[r^j : r in rts,j in [0..5]]);
  vdminv := vdm^(-1);
  check := Eltseq(vdm*vdminv - 1);
  assert Maximum([Abs(b): b in check]) lt 10^(-prec/2);
  nodes := [];
  for e1,e2,e3,e4 in [-1,1] do
    e5 := e1*e2*e3*e4;
    yy1 := Vector([e1*yy[1],e2*yy[2],e3*yy[3],e4*yy[4],e5*yy[5],yy[6]]);
    mysqrt := LCC!Eltseq(yy1*vdminv);
    check := Eltseq(mysqrt^2 - LCC!Eltseq(xi));
    assert Maximum([Abs(b): b in check] cat [0]) lt 10^(-prec/2);
    zz := EltseqPad(mysqrt);
    zz1 := Eltseq(Vector(zz)*ChangeRing(N,CC));
    check := [Evaluate(q,zz1) : q in quadrics];
    assert Maximum([Abs(b): b in check] cat [0]) lt 10^(-prec/2);
    MM := Evaluate(M,zz1);
    scores := [Maximum([Abs(MM[i,j]): j in [1..4]]): i in [1..4]];
    _,i := Maximum(scores);
    node := MM[i];
    _,j0 := Maximum([Abs(node[j]): j in [1..4]]);
    Append(~nodes,[node[j]/Abs(node[j0]) : j in [1..4]]);
  end for;
  return nodes;
end function;  

intrinsic TwistedKummerSurface(J::JacHyp,model::Tup:
    R4 := PolynomialRing(QQ,4),prec := 100) -> Rec
{Computes a record of the twisted Kummer surface corresponding to the given model of a 2-covering of the genus 2 Jacobian J}

  C := Curve(J);
  k := BaseRing(C);
  P := PolynomialRing(k);
  f := Evaluate(-Equation(C),[P.1,0,1]);
  f0,f1,f2,f3,f4,f5,f6 := Explode(Eltseq(f));
  la,coeffs := Explode(model);
  R := PolynomialRing(k,6);
  u0,u1,u2,u3,u4,u5 := Explode([R.i : i in [1..6]]);
  mons := MD(R,2);
  H := &+[coeffs[i]*mons[i] : i in [1..#mons]];
  assert IsModel(f,<la,H>);
  G := u0*u5 + u1*u4 + u2*u3;
  H /:= la;
  GG := 2*SymmetricMatrix(G);
  HH := 2*SymmetricMatrix(H);
  assert Determinant(P.1*GG - HH) eq (-1/f6)*f;
  SS := HH*GG^(-1)*HH;
  S := (1/2)*&+[SS[i,j]*R.i*R.j: i,j in [1..6]];
  L := Degree6Algebra(C);
  
  if k cmpeq QQ then
    badprimes := [2] cat BadPrimes(C);
    badprimes cat:= PrimeDivisors(ZZ!f6);
    badprimes cat:= PrimeDivisors(ZZ!la);  
    badprimes := Set(badprimes);
  end if;

// Computing the twisted Kummer surface
    
  Lambda := Matrix(R4,4,6,[
      [ 0, 0, x4, 0, x3, x2 ],
      [ 0, -x4, 0, x3, 0, -x1 ],
      [ x4, 0, 0, -x2, -x1, 0 ],
      [ -x3, x2, -x1, 0, 0, 0 ] ])
    where x1,x2,x3,x4 is Explode([R4.i : i in [1..4]]);
  B := Lambda*ChangeRing(HH,R4)*Transpose(Lambda);
  B := Matrix(R4,4,4,Eltseq(B));
  adjB := Adjoint(B);
  KumEqn := ExactQuotient(adjB[4,4],R4.4^2);
  assert adjB eq KumEqn*Matrix(R4,4,4,[R4.i*R4.j : i,j in [1..4]]);

// Computing the associated quadratic forms

  toqf := func<q|&+[q[i,j]*R.i*R.j : i,j in [1..6]]>;
  mats := [GG*TT^r : r in [0..5]] where TT is GG^(-1)*HH;
  Qlist := [(1/f6)*&+[Coeff(f,i)*mats[i-j]: i in [j+1..6]] : j in [0..5]];
  Qlist1 := [toqf(q): q in Qlist];
  Jmat := Matrix(6,6,[Deriv(Q,R.j): j in [1..6],Q in Qlist1]);
  JJ := Determinant(Jmat);

// Computing the covering map

  wedgeB := wedge(B);
  Q0H,Q1H,Q2H,Q3H,Q4H,Q5H :=
    Explode([&+[Qlist[m,i,j]*wedgeB[i,j] : i,j in [1..6]] : m in [1..6]]);
  MM := [Lambda*ChangeRing(mats[i],R4)*Transpose(Lambda) : i in [2..4]];
  E1,E2,E3 := Explode([ExactQuotient(Adjoint(M)[4,4],R4.4^2): M in MM]);
  assert KumEqn eq E1;
  F0 := (1/(2*f6))*E1;
  F1 := Q2H - 2*f4*F0;
  F2 := -Q1H + f3*F0;  
  F3 := Q0H;
  F4 := f6*E3 - (f2*Q2H - f3*Q1H + f4*Q0H) - (f1*f5 - 4*f2*f4 + 2*f3^2)*F0;
  assert F2 eq -E2 - f3*F0;
  assert Q3H eq 4*f5*F0;
  assert Q4H eq 6*f6*F0;
  assert Q5H eq 0;

// Checking the covering map

  P3 := Proj(R4);
  KumEqn0 := R4!DefiningPolynomial(KummerSurface(J));
  K0 := Scheme(P3,KumEqn0);
  K1 := Scheme(P3,KumEqn);
  assert Evaluate(KumEqn0,[F1,F2,F3,F4]) in Ideal(K1);
  covmap := map<K1->K0|[F1,F2,F3,F4]>;
  covariants := [F0,F1,F2,F3,F4];
 
// Computing the corresponding Selmer element

  function GetSelmerElement(pt)
    xi := &+[Evaluate(Qlist1[i],pt)*L.1^(i-1): i in [1..6]];
    m := (1/2)^6*Evaluate(JJ,pt);
    assert Norm(xi) eq m^2;
    assert m ne 0;
    return <xi,m>;
  end function;

// Polynomials for computing the fudge factors
  
  Z := ASM([R.j : j in [1..6]]);
  W := star(ASM([Deriv(H,R.j): j in [1..6]]));
  Y := star(ASM([Deriv(S,R.j): j in [1..6]]));
  A := A0 + Transpose(A0) where A0 is star(W)*Z*star(Y);

// Some random points in P^5

  pts := [ [ 1, 0, 0, 0, 0, 0 ], [ 1, 1, 0, -1, 0, 0 ], [ 0, 0, 0, 0,
    0, 1 ], [ 1, 0, 0, -1, -1, 1 ], [ -1, -2, 2, 0, 2, -2 ], [ -1, 1,
    -1, 1, 1, 1 ], [ 1, -1, -1, -1, 2, 0 ], [ -2, -2, 0, 0, 1, -2 ], [
    -1, -1, 0, 1, 0, 0 ], [ 0, 1, 1, 0, 1, 1 ], [ 0, 0, 0, 0, -1, 0 ],
    [ 0, 2, -2, 0, 0, 1 ], [ -1, -1, 0, 2, -1, 1 ] ];

// The rank 1 quadratic forms over L10

  L10,cubiclist := Degree10Algebra(C);
  nL := NumberOfComponents(L10);
  la := <GetLambdas(L10[i],f6,cubiclist[i]) : i in [1..nL]>; 
  for pt0 in pts do
    pt := pt0;
    if Evaluate(JJ,pt) eq 0 then continue; end if;
    quadforms := <>;
    ff := [Evaluate(A[i,j],pt) : i,j in [1..4] | i le j];    
    for ctr in [1..nL] do
      F := L10[ctr];
      R4F := PolynomialRing(F,4);
      Peps := &+[la[ctr,j]*R4F!covariants[j] : j in [1..5]];
      alpha,Qeps := MySquareRoot(Peps);
      assert Peps eq alpha*Qeps^2;
      ee := [MC(Qeps,R4F.i*R4F.j): i,j in [1..4] | i le j];
      chi := &+[ee[i]*ff[i] : i in [1..10]];  
      if chi eq 0 then continue pt0; end if;
      Append(~quadforms,<F!chi,F!alpha,R4F!Qeps>);
    end for;
    break;
  end for;
  assert Position(pts,pt) lt #pts;

  if k cmpeq QQ then
    scalar := RationalGCD(Coefficients(KumEqn));
  else
    Ok := RingOfIntegers(k);
    I := &+[x*Ok : x in Coefficients(KumEqn)];
    flag,scalar := IsPrincipal(I);
    assert flag;
  end if;
  KumEqn /:= scalar;

// Creating a record of the twisted Kummer surface

  kum := rec<twistedkummer|
    surface := Scheme(P3,KumEqn),
    pushout := B,
    selmer := GetSelmerElement(pt),
    nodes := [],
    coveringmap := covmap,
    quadraticforms := quadforms>;

  if k cmpeq QQ then
    kum`badprimes := badprimes;
    kum`searchbound := 0;
    kum`points := []; 
// Computing numerical approximations to the nodes
    km := KernelMatrix(L.1*GG - HH);
    assert Nrows(km) eq 1;
    v := Reverse(Eltseq(km));
    kum`nodes := KummerSurfaceNodes(f,[G,H,S],v,prec);
    FF := [Deriv(KumEqn,i): i in [1..4]];
    for nn in kum`nodes do
      assert forall{F : F in FF | Abs(Evaluate(F,nn)) lt 10^(-prec/2)};
    end for;
  end if;

  return kum;
end intrinsic;

// Computes the quadratic form in Theorem 3.9 using Theorem 3.20

function CTP_QuadraticForm(J,sel,pt_eta,qfs,f6,R4)

// We compute nu and r "witnessing" the fact that the 3 given
// elements of the 2-Selmer group sum to zero.

  assert #sel eq 3;
  xi := [s[1] : s in sel];
  m := [s[2] : s in sel];
  flag,r,nu := IsEqualInSelmer(J,<&*xi,&*m>,<1,1>);
  assert flag;
  assert <&*xi,&*m> eq <r*nu^2,r^3*Norm(nu)>;

  k := BaseRing(J);
  FF,cubiclist := Degree10Algebra(Curve(J));
  mons := MD(R4,2);
  g := 0;
  P := PreimageRing(Parent(xi[1]));
  
  for ctr in [1..#cubiclist] do
    F := FF[ctr];
    R4F := PolynomialRing(F,4);
    chi   := [  F  | qfs[i,ctr,1] : i in [1..3]];
    alpha := [  F  | qfs[i,ctr,2] : i in [1..3]];
    QQQ   := [ R4F | qfs[i,ctr,3] : i in [1..3]];
    QQQ[3] := &+[mat[i,j]*R4F.i*R4F.j : i,j in [1..4]]
      where mat is (1/alpha[3])*SymmetricMatrix(QQQ[3])^(-1);
    cubic := Random(cubiclist[ctr]); // either should work
    tau := [Resultant(cubic,P!xi[i]) + m[i] : i in [1..3]];
    mu := F!(&*tau/Resultant(cubic,P!nu))/&*chi;
    assert -f6^3*mu^2 eq r^3*(&*alpha);
    psi := mu*Evaluate(QQQ[2],pt_eta)*Evaluate(QQQ[3],[1,0,0,0]);
    g +:= &+[Trace(psi*MC(QQQ[1],R4F!m),k)*m: m in mons];
  end for;
  
  if k cmpeq QQ then
    g /:= RationalGCD(Coefficients(g));
  else
    Ok := RingOfIntegers(k);
    I := ideal<Ok|Coefficients(g)>;
    flag,scalar := IsPrincipal(I);
    assert flag;
    g /:= scalar;
  end if;
  
  return g;
  
end function;

/////////////////////////////////////////////////////
//    Local calculations - non-archimedean case    //
/////////////////////////////////////////////////////

function RandomSmoothModpPoints(F,p)
  k,resmap := ResidueClassField(p);
  Rp := PolynomialRing(k,4);
  Fp := &+[resmap(Coefficients(F)[i])*Rp!(Monomials(F)[i])
        : i in [1..#Terms(F)]];
  Xp := Scheme(Proj(Rp),Fp);
  pts := {@ @};
  if #k gt 20 then
    for loopvar in [1..200] do
      Y := Xp;
      while Dimension(Y) gt 0 do
        f := &+[Random(k)*Rp.i : i in [1..4]];
        Y := Scheme(Y,f);
      end while;
      pts0 := { Xp!Eltseq(P): P in Points(Y) };
      pts join:= {@ P : P in pts0 | not IsSingular(P) @}; 
      if #pts ge 20 then break; end if;
    end for;
  end if;
  if #pts lt 20 then
    pts := {@ P : P in Points(Xp) | not IsSingular(P) @};
  end if;  
  return pts;
end function;

function IsDefinitelySquare(a,p:prec := Infinity())
  if a eq 0 then return false; end if;
  v := Valuation(a,p);
  if IsOdd(v) then return false; end if;
  k := Parent(a);
  e := 2*Valuation(k!2,p) + 1;
  if prec lt v + e then return false; end if;
  if k cmpeq QQ then
    a1 := ZZ!Integers(p^e)!(a/p^v);
    if p eq 2 then return a1 eq 1; end if;
    return LegendreSymbol(a1,p) eq 1;
  else
    pi := UniformizingElement(p);
    if e eq 1 then
      _,resmap := ResidueClassField(p);
      return IsSquare(resmap(a/pi^v));
    else   
      Ok := RingOfIntegers(k);
      RR := quo<Ok|p^e>;
      UU,map := UnitGroup(RR);
      return ((RR!(a/pi^v)) @@ map) in 2*UU;
    end if;
  end if;
end function;

function pAdicContribution(F,G,H,a,p,prec:limit := 10^6)

  if IsDefinitelySquare(a,p) then return 0; end if;

  k := BaseRing(Parent(F));
  _,resmap := ResidueClassField(p);
  if Valuation(k!2,p) eq 0 then
    for pt in RandomSmoothModpPoints(F,p) do
      xx := [x @@ resmap : x in Eltseq(pt)];
      assert Valuation(Evaluate(F,xx),p) gt 0;
      g0 := Evaluate(G,xx);
      h0 := Evaluate(H,xx);
      if Valuation(g0,p) eq 0 and IsSquare(resmap(g0))
          and Valuation(h0,p) eq 0
	  and (Valuation(a,p) eq 0 or IsSquare(resmap(h0))) then
	return 0;
      end if;	
    end for;
  end if;
  
  if k cmpeq QQ then
    vprintf CasselsTatePairing,2 : "p = %o ",p;
  else
    vprintf CasselsTatePairing,2 : "N(p) = %o ",Norm(p);
  end if;
  
  pi := (k cmpeq QQ) select p else UniformizingElement(p);
  vF := Minimum([Valuation(c,p): c in Coefficients(F)]);
  vG := Minimum([Valuation(c,p): c in Coefficients(G)]);
  vH := Minimum([Valuation(c,p): c in Coefficients(H)]);
  F /:= pi^vF;
  G /:= pi^(2*Floor(vG/2));
  H /:= pi^(2*Floor(vH/2));
  
  _<x> := PolynomialRing(k);
  e := 2*Valuation(k!2,p) + 1;
  if k cmpeq QQ then 
    kp := pAdicField(p,prec);
  else
    kp,iota := Completion(k,p:Precision := prec);
    PP := PolynomialRing(kp);
  end if;
  Ok := RingOfIntegers(k);
  RR,resmap := quo<Ok|p^e>;

  function MyRepresentativeModuloSquares(a)
    if a eq 0 then return 0; end if;
    v := Valuation(a,p);
    a1 := (RR!(a/pi^v)) @@ resmap;
    return k!(pi^(v mod 2)*a1);
  end function;

// Returns true if we can be sure there exists a in Qp
// with f(a) = 0, and g(a), h(a) in (Qp^*)^2

  function CheckExactly(f,g,h,x0)
    v := Valuation(x0,p);
    if v lt 0 then
      x0 /:= pi^v;
      f := Evaluate(f,pi^v*x);
      g := Evaluate(g,pi^v*x);
      h := Evaluate(h,pi^v*x);
    end if;
    vf := Minimum([Valuation(c,p): c in Coefficients(f)]);
    vg := Minimum([Valuation(c,p): c in Coefficients(g)]);
    vh := Minimum([Valuation(c,p): c in Coefficients(h)]);
    f /:= pi^vf;
    g /:= pi^(2*Floor(vg/2));
    h /:= pi^(2*Floor(vh/2));    
    assert Valuation(x0,p) ge 0;
    m := Valuation(Evaluate(f,x0),p);
    r := Valuation(Evaluate(Deriv(f),x0),p);
    return m gt 2*r
      and IsDefinitelySquare(Evaluate(g,x0),p:prec := m - r)
      and IsDefinitelySquare(Evaluate(h,x0),p:prec := m - r);
    return true;
  end function;
  
  RandomElement := func<B|k![Random([-B..B]): i in [1..Degree(k)]]>;
  
  for loopvar in [1..limit] do
    B := 10 + loopvar^2;
    repeat
      M := Matrix(2,4,[RandomElement(B): i in [1..8]]);
    until Rank(M) eq 2;
    subst := [M[1,j] + M[2,j]*x : j in [1..4]];
    F1 := Evaluate(F,subst);
    G1 := Evaluate(G,subst);
    H1 := Evaluate(H,subst);
    rts := 0;
    F1p := k cmpeq QQ select F1 else PP![iota(c): c in Eltseq(F1)];
    try
      rts := Roots(F1p,kp);
    catch e;
    end try;
    if rts cmpeq 0 then continue; end if;
    for rt in rts do
      if rt[2] ne 1 then continue; end if;
      if k cmpeq QQ then
        x0 := k!rt[1];
      else
        x0 := rt[1] @@ iota;
      end if;	
      g0 := Evaluate(G1,x0);	
      if IsDefinitelySquare(g0,p) then
        h0 := Evaluate(H1,x0);
        b := MyRepresentativeModuloSquares(h0);
	if b ne 0 and CheckExactly(F1,G1,b*H1,x0) then
	  return (HilbertSymbol(a,b,p) eq 1) select 0 else 1;
        end if;
      end if;
    end for;
  end for;

  printf "F := %o;\n",F;
  printf "pushout := %o;\n",G;
  printf "quadform := %o;\n",H;
  error "Failed to find a p-adic point ( p =",p," limit =",limit,")";
  
  return 0;
end function;

/////////////////////////////////////////////////////
//      Local calculations - archimedean case      //
/////////////////////////////////////////////////////

function RealContribution(F,G,H,a,j,nodes,prec:limit := 10^4)

  if Re(Conjugate(a,j)) gt 0 then return 0; end if;
  
  R := RealField(prec);
  k := BaseRing(Parent(F));  
  if k cmpeq QQ then 
    P<x> := PolynomialRing(QQ);
  else
    R4 := PolynomialRing(R,4);
    emb := func<f|&+[R4|(R!Conjugate(Coefficients(f)[i],j))
      *R4!(Monomials(f)[i]): i in [1..#Terms(f)]]>;
    F := emb(F);
    H := emb(H);
    G := emb(G);
    P<x> := PolynomialRing(R);
  end if;

  function MyIsolateRoots(f,e)
    ff := Factorization(f);
    ans := [];
    for p in ff do
      if Degree(p[1]) eq 1 then
        a := Roots(p[1])[1,1];
	assert Evaluate(f,a) eq 0;
        rts := [<a,a>];
      else	
        rts := IsolateRoots(p[1],e);
        for rr in rts do
          a,b := Explode(rr);
          assert a lt b;
          assert Evaluate(p[1],a)*Evaluate(p[1],b) lt 0;
        end for;
      end if;
      ans cat:= rts;
    end for;
    return ans;
  end function;

  function GoodInterval(a,b,f,ii)
  // Returns true if f(a) > 0, f(b) > 0 and none of the intervals
  // in ii intersect [a,b].
    return Evaluate(f,a) gt 0 and Evaluate(f,b) gt 0 and 
      forall{c : c in ii | c[2] lt a or b lt c[1]};
  end function;  

  function CheckExactly(f,g,h,e)
  // Returns true if we can be sure there is a real
  // number x with f(x) = 0, g(x) > 0 and h(x) > 0.
    rtsf := MyIsolateRoots(f,e);
    rtsg := MyIsolateRoots(g,e);
    rtsh := MyIsolateRoots(h,e);
    for rr in rtsf do
      a,b := Explode(rr);
      if GoodInterval(a,b,g,rtsg) and GoodInterval(a,b,h,rtsh) then
        return true;
      end if;
    end for;
    return false;
  end function;

  function RandomPoint(B,usenodes)
    if usenodes then
      P := Random(nodes);
      Q := Random(nodes);
      return [Round(B*Re(P[i] + Q[i])): i in [1..4]];
    end if;
    return [Random([-B..B]): i in [1..4]];
  end function;
  
  for loopvar in [1..limit] do
    B := 10 + loopvar^2;
    usenodes := (k cmpeq QQ) and IsEven(loopvar);
    repeat
      M := Matrix(2,4,[RandomPoint(B,usenodes): i in [1..2]]);
    until Rank(M) eq 2;
    subst := [M[1,j] + M[2,j]*x : j in [1..4]];
    F1 := Evaluate(F,subst);
    G1 := Evaluate(G,subst);
    H1 := Evaluate(H,subst);
    sgn := 0;
    for r in Roots(F1,R) do
      if Evaluate(G1,r[1]) gt 10^(-prec/2) then
        ans := Evaluate(H1,r[1]);
        if Abs(ans) gt 10^(-prec/2) then
	  sgn := Sign(ans);
          break r;
        end if;
      end if;
    end for;
    if sgn ne 0 and k cmpeq QQ then 
      for d in [1,10,prec] do
        flag := CheckExactly(F1,G1,sgn*H1,10^(-d));
        if flag then break; end if;
      end for;
      if not flag then sgn := 0; end if;
    end if;  
    if sgn ne 0 then
      return sgn eq 1 select 0 else 1;
    end if;
  end for;

  printf "F := %o;\n",F;
  printf "pushout := %o;\n",G;
  printf "quadform := %o;\n",H;
  error "Failed to find a real point";

  return 0;
end function;

////////////////////////////////////////////////
//       Computing the global pairing         //
////////////////////////////////////////////////

function CTP_EvaluatePairing(K,pushoutform,nodes,a,quadform,badprimes:
   real_prec := 100,padic_prec := 100)
   
  F := Equation(K);
  G := pushoutform;
  H := quadform;
  
  assert forall{c : c in Coefficients(F) | IsIntegral(c)};
  assert forall{c : c in Coefficients(G) | IsIntegral(c)};
  assert forall{c : c in Coefficients(H) | IsIntegral(c)};
  
  vprint CasselsTatePairing,2 :
    "Computing the contributions at the finite places";
  ctp := &+[GF(2)| pAdicContribution(F,G,H,a,p,padic_prec)
    : p in badprimes];
  vprint CasselsTatePairing,2 : "";
    
  vprint CasselsTatePairing,2 :
    "Computing the contributions at the infinite places";
  k := BaseRing(Parent(F));
  if k cmpeq QQ then
    ctp +:= GF(2)!RealContribution(F,G,H,a,1,nodes,real_prec);
  else
    SetKantPrecision(k,real_prec);  
    infplaces := InfinitePlaces(k);
    ctp +:= &+[GF(2)| RealContribution(F,G,H,a,v,[],real_prec)
      : v in [1..#infplaces] | IsReal(infplaces[v]) ];      
  end if;

  return ctp;
end function;

// Computes <eps,eta>_CT provided we know a rational point on K_eta.

function CTP_Internal(J,K_eps,K_eta,K_sum,real_prec,padic_prec)

  C := Curve(J);
  assert BaseRing(C) cmpeq QQ;
  P := PolynomialRing(BaseRing(C));
  f := Evaluate(-Equation(C),[P.1,0,1]);
  f6 := Coeff(f,6);

  R4<x1,x2,x3,x4> := CoordinateRing(Ambient(K_eps`surface));
  vprint CasselsTatePairing,2 : "";
  vprint CasselsTatePairing,2 : "K_eps has equation";
  vprint CasselsTatePairing,2 : Equation(K_eps`surface);
  vprint CasselsTatePairing,2 : "K_eta has equation";
  vprint CasselsTatePairing,2 : Equation(K_eta`surface);
  
  pts := K_eta`points;
  assert pts eq [P : P in pts | Evaluate(K_eta`pushout,Eltseq(P)) ne 0];
  error if #pts eq 0, "Kummer surface has no known rational points";

  alist := [];
  for pt0 in pts do
    pt := PRIM(Eltseq(pt0));
    M := wedge(Evaluate(K_eta`pushout,pt));
    assert exists(j){j : j in [1..6] | M[j,j] ne 0};
    a := PowerFreePart(-f6*M[j,j],2);
    Append(~alist,a);
    if a eq 1 then
      vprint CasselsTatePairing,2 : "Have global point: ",pt;
    end if;
  end for;
  vprint CasselsTatePairing,2 : "Known points in K_eta(Q) lift to J_eta(Q(sqrt(a))) for a =",{* a : a in alist *};

  pt_eta := PRIM(Eltseq(Random(pts)));
  vprint CasselsTatePairing,1 : "pt_eta =",pt_eta;
  assert not IsSingular(K_eta`surface!pt_eta);

  M := wedge(Evaluate(K_eta`pushout,pt_eta));
  assert exists(j){j : j in [1..6] | M[j,j] ne 0};
  a := PowerFreePart(-f6*M[j,j],2);
  vprint CasselsTatePairing,1 : "a =",a;

  sel := [K_eps`selmer,K_eta`selmer,K_sum`selmer];
  qfs := <K_eps`quadraticforms,K_eta`quadraticforms,K_sum`quadraticforms>;
  g := CTP_QuadraticForm(J,sel,pt_eta,qfs,f6,R4);
  vprint CasselsTatePairing,1 : "g =",g;

  badprimes := &join[K`badprimes : K in [K_eps,K_eta,K_sum]];
  badprimes join:= Set(PrimeDivisors(ZZ!a));
  badprimes := Sort(Setseq(Set(badprimes)));  
  vprint CasselsTatePairing,2 : "badprimes =",badprimes;

  N := -f6*wedge(K_eps`pushout);
  dd := RationalGCD(&cat[Coefficients(N[i,j]): i,j in [1..6]]);
  dd1 := PowerFreePart(dd,2);
  assert IsSquare(dd1/dd);
  N *:= (dd1/dd);
  return CTP_EvaluatePairing(K_eps`surface,N[1,1],K_eps`nodes,a,g,badprimes:
         real_prec := real_prec,padic_prec := padic_prec);
	 
end function;

intrinsic CasselsTatePairingGenus2(J::JacHyp,S2map::Map:hint:=0,real_prec:=100,padic_prec:=100) -> AlgMatElt
{Computes the Cassels-Tate pairing on the 2-Selmer group of the Jacobian J = Jac(C) of a genus 2 curve C/Q. The 2-Selmer group is specified by a map (as returned by TwoDescentGenus2) that sends each non-zero element of an abstract abelian group (Z/2Z)^d to a model for a 2-covering of J. It is required that C has equation y^2 = f(x) where deg(f) = 6. A model ( la : a_11, a_12, ..., a_66 ) corresponds to a pair of quadratic forms G = x1*x6 + x2*x5 + x3*x4 and H = sum a_ij xi*xj such that the associated 6 by 6 symmetric matrices satisfy det(la*x*G - H) = const*f(x). Up to quadratic twist, the 2-covering may be identified with the set of lines contained in the 3-fold \{G = H = 0\} in P^5. The output is a d by d matrix with entries in GF(2) representing the Cassels-Tate pairing with respect to the standard basis of (Z/2Z)^d. The method used for computing the pairing relies on being able to find rational points on sufficiently many of the twisted Kummer surfaces associated to the 2-coverings. In general there is no guarantee that such points exist. A variant of the function computes just one value of the pairing when a suitable "hint" is supplied.}

  if hint cmpeq 0 then
  
  C := Curve(J);
  assert IsSimplifiedModel(C);
  S2 := Domain(S2map);
  d := #Generators(S2);
  if d eq 0 then
    return ZeroMatrix(GF(2),0,0),S2!0;
  end if;

  sel := TwoSelmerElementsGenus2(J,S2map);
  inv := GetInverse(J,sel);
  c := inv(<1,-1>);
  assert HasRationalTrope(C) eq (c eq S2!0);
  badp := BadPrimes(C);
  defp := [p : p in [0] cat badp |  IsDeficient(C,p)];
   
  vprint CasselsTatePairing,1 : "Computing the twisted Kummer surfaces ...";
  R := PolynomialRing(QQ,4);
  K := AssociativeArray(S2);
  S2elts := [x : x in S2 | x ne S2!0];  
  vtime CasselsTatePairing,1 : for x in S2elts do
    K[x] := TwistedKummerSurface(J,S2map(x): R4 := R,prec := real_prec);
  end for;
  
  vprint CasselsTatePairing,1 :  " ... done";
    
  bas := [Matrix(GF(2),d,d,[<i,i,1>]): i in [1..d]];
  bas cat:= [Matrix(GF(2),d,d,[<i,j,1>,<j,i,1>]): i,j in [1..d] | i lt j];
  V := VectorSpace(GF(2),#bas);
  U := V;
  F2 := VectorSpace(GF(2),1);
  ctp := ZeroMatrix(GF(2),d,d);
  todolist := {[eps,eta] : eps,eta in S2elts | eps + eta notin [S2!0,c]};
  todolater := {};
  searchbound := 2;
  i := 0;  
  for loopvar in [1..8] do
    searchbound *:= 2;
    repeat
      success := false;
      if i eq 0 then
        eps := c;
        eta := c;
	ans := GF(2)!(#defp);
	success := true;
      elif i le d then
        eps := S2.i;
        eta := S2.i + c;
	ans := 0;
	success := true;
      else
        if #todolist eq 0 then
          todolist := todolater;
          todolater := {};
          continue loopvar;  
        end if;
        eps,eta := Explode(Random(todolist));
      end if;
      i +:= 1;
      if eps eq S2!0 or eta eq S2!0 then continue; end if;
      Exclude(~todolist,[eps,eta]);    
      v := Eltseq(eps);
      w := Eltseq(eta);
      MM := [&+[u[i]*bas[i] : i in [1..#bas]]: u in Basis(U)];
      vec := [&+[M[i,j]*v[i]*w[j]: i,j in [1..d]]: M in MM];
      if not success then      
        if forall{x : x in vec | x eq 0} then
          continue;
        end if; 
        if #K[eta]`points eq 0 and K[eta]`searchbound lt searchbound then 
          K[eta]`points :=
	    PointSearch(K[eta]`surface,searchbound:SkipSingularityCheck);
	  K[eta]`searchbound := searchbound;
	end if;
	if #K[eta]`points eq 0 then 
	  Include(~todolater,[eps,eta]);
	  continue;
	end if;
        ans := CTP_Internal(J,K[eps],K[eta],K[eps+eta],real_prec,padic_prec);
      end if;
      vprintf CasselsTatePairing,1 : "CTP( %o, %o ) = %o\n",v,w,ans;
      if ans ne &+[ctp[i,j]*v[i]*w[j]: i,j in [1..d]] then
        assert exists(j){j : j in [1..#MM] | vec[j] ne 0};
        ctp +:= MM[j];
      end if;
      assert ans eq &+[ctp[i,j]*v[i]*w[j]: i,j in [1..d]];
      U := Kernel(hom<U->F2|Matrix(GF(2),#Basis(U),1,vec)>);
    until Dimension(U) eq 0;
    break;
  end for;

  if Dimension(U) ne 0 then
    error "failed to compute the pairing";
  end if;
  vprint CasselsTatePairing,2 :  "";
  
  return ctp,c;

/////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////

  else

// Variant for computing the pairing over (small) quadratic fields.
// The genus 2 curve C should still be defined over Q.
// We compute <eps,eta>_CT, where eps, eta, and a point on K_eta
// are given as a "hint".

    k := BaseRing(J);
    Ok := RingOfIntegers(k);
    C := Curve(J);
    P := PolynomialRing(QQ); 
    f := Evaluate(-Equation(C),[P.1,0,1]);
    f6 := Coeff(f,6);
    
    eps,eta,pt_eta := Explode(hint);
    mm := [S2map(g): g in [eps,eta,eps+eta]];
    vprint CasselsTatePairing,1 : "Computing the twisted Kummer surfaces ...";
    R4<x1,x2,x3,x4> := PolynomialRing(k,4);
    K_eps := TwistedKummerSurface(J,mm[1]:R4 := R4);
    K_eta := TwistedKummerSurface(J,mm[2]:R4 := R4);
    K_sum := TwistedKummerSurface(J,mm[3]:R4 := R4);
    vprint CasselsTatePairing,1 :  " ... done";

    vprint CasselsTatePairing,2 : "K_eps has equation";
    vprint CasselsTatePairing,2 : Equation(K_eps`surface);
    vprint CasselsTatePairing,2 : "K_eta has equation";
    vprint CasselsTatePairing,2 : Equation(K_eta`surface);
 
    vprint CasselsTatePairing, 1 : "pt_eta =",pt_eta;
    assert Evaluate(Equation(K_eta`surface),pt_eta) eq 0;

    M := wedge(Evaluate(K_eta`pushout,pt_eta));
    assert exists(j){j : j in [1..6] | M[j,j] ne 0};
    a := NiceRepresentativeModuloPowers(-f6*M[j,j],2);
    vprint CasselsTatePairing, 1 : "a =",a;
  
    sel := [K_eps`selmer,K_eta`selmer,K_sum`selmer];
    data := <K_eps`quadraticforms,K_eta`quadraticforms,K_sum`quadraticforms>;
    g := CTP_QuadraticForm(J,sel,pt_eta,data,f6,R4);
    vprint CasselsTatePairing, 1 : "g =",g;

    S0 := PrimesInInterval(2,20);
    S0 cat:= BadPrimes(ChangeRing(C,QQ));
    S0 cat:= PrimeDivisors(ZZ!f6);
    S0 cat:= PrimeDivisors(ZZ!Norm(a));
    S0 := Sort(SetToSequence(Set(S0)));
    S := &cat[[pp[1] : pp in Decomposition(Ok,p)]: p in S0];
    vprint CasselsTatePairing, 2 : "norms of bad primes =",[Norm(p): p in S];

    N := -f6*wedge(K_eps`pushout);
    pushout := N[1,1];
    I := ideal<Ok|&cat[Coefficients(pushout): i,j in [1..6]]>;
    u1,v1 := SquareFree(Denominator(I));
    N *:= (u1*v1)^2;  
    pushout := N[1,1];
    I := ideal<Ok|&cat[Coefficients(pushout): i,j in [1..6]]>;
    assert I subset 1*Ok;
    ctp := CTP_EvaluatePairing(K_eps`surface,N[1,1],K_eps`nodes,a,g,S);
    v := Eltseq(eps);
    w := Eltseq(eta);
    vprintf CasselsTatePairing,1 : "CTP( %o, %o ) = %o\n",v,w,ctp;

    return ctp;
  end if;
  
end intrinsic;
