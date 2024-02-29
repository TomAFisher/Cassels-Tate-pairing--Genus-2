
//////////////////////////////////////////////////////////////////
//                                                              //
// A MAGMA file accompanying the article                        //
//                                                              //
//            COMPUTING THE CASSELS-TATE PAIRING                //
//        ON THE 2-SELMER GROUP OF A GENUS 2 JACOBIAN           //
//                                                              //
//               by TOM FISHER AND JIALI YAN                    //
//                                                              //
// This program checks some of the formulae and examples        //
// in the paper, in roughly the same order as the paper.        //
//                                                              //
// Version : June 2023                                          //
//                                                              //
//////////////////////////////////////////////////////////////////

have_biquadratic_forms := false;
f := 0; BiquadraticForms := 0; BF := 0;

// To check some of the formulae, it is necessary to load the
// biquadratic forms, as computed by Victor Flynn.

// To do this save a local copy of the file at
// https://people.maths.ox.ac.uk/flynn/genus2/kummer/biquadratic.forms
// and uncomment the next two lines
// f := Open("biquadratic.forms","r");
// have_biquadratic_forms := true;

if have_biquadratic_forms then 

R<f0,f1,f2,f3,f4,f5,f6,k1,k2,k3,k4,l1,l2,l3,l4>
  := PolynomialRing(Integers(),15);
BBB := ZeroMatrix(R,4,4);

while true do
  s := Gets(f);
  if IsEof(s) then break; end if;
  if s in {""," ","with(linalg):","BBB := matrix(4,4):"}
    or s[1] eq "#" then continue; end if;
  ss := Split(s,"[,]");
  i,j := Explode([StringToInteger(ss[r]): r in [2,3]]);
  s1 := Sprintf("BBB[%o,%o] :=",i,j);
  assert s in {s1,s1 cat " "};
  s := Gets(f); repeat s cat:= Gets(f); until s[#s] eq ":";
  BBB[i,j] := eval Prune(s);
end while;

BiquadraticForms := func<f,x,y|Evaluate(BBB,Eltseq(f) cat x cat y)>;

end if;

//////////////////////////////////////////////////////////

QQ := Rationals();
MC := MonomialCoefficient;
MD := MonomialsOfDegree;
Deriv := Derivative;

// Creating the generic genus 2 curve in Magma

K<f0,f1,f2,f3,f4,f5,f6> := FunctionField(QQ,7);
P<x> := PolynomialRing(K);
f := P![f0,f1,f2,f3,f4,f5,f6];
C := HyperellipticCurve(f);
J := Jacobian(C);
Kum := KummerSurface(J);
L<t> := quo<Parent(f)|f>;
R4L := PolynomialRing(L,4);

print "Section 2.1 : The Kummer surface and its dual";

R4<a,b,c,d> := PolynomialRing(K,4);
P<x> := PolynomialRing(R4);
res := Resultant(a*x^2 - b*x + c,f);
assert Evaluate(res,[1,2*x,x^2,0]) eq f^2;
P2 := b^2 - 4*a*c;
P3 := 2*(2*f0*a^3 + f1*a^2*b + 2*f2*a^2*c + f3*a*b*c + 2*f4*a*c^2
  + f5*b*c^2 + 2*f6*c^3);
assert Evaluate(P2,[1,2*x,x^2,0]) eq 0;  
assert Evaluate(P3,[1,2*x,x^2,0]) eq 4*f;
P4 := ExactQuotient(P3^2 - 16*res,4*P2);
assert P3^2 - 4*P2*P4 eq 16*res;
KumEqn := P2*d^2 - P3*d + P4;
R4<x1,x2,x3,x4> := R4;
assert KumEqn eq R4!DefiningPolynomial(Kum);
// [CF,page 19]
assert KumEqn eq (x2^2 - 4*x1*x3)*x4^2 - 2*(2*f0*x1^3 + f1*x1^2*x2 +
    2*f2*x1^2*x3 + f3*x1*x2*x3 + 2*f4*x1*x3^2 + f5*x2*x3^2
    + 2*f6*x3^3)*x4 + (f1^2 - 4*f0*f2)*x1^4 - 4*f0*f3*x1^3*x2
    - 2*f1*f3*x1^3*x3 - 4*f0*f4*x1^2*x2^2 + 4*(f0*f5 - f1*f4)*x1^2*x2*x3
    + (f3^2 - 4*f0*f6 + 2*f1*f5 - 4*f2*f4)*x1^2*x3^2
    - 4*f0*f5*x1*x2^3 + 4*(2*f0*f6 - f1*f5)*x1*x2^2*x3
    + 4*(f1*f6 - f2*f5)*x1*x2*x3^2 - 2*f3*f5*x1*x3^3 - 4*f0*f6*x2^4
    - 4*f1*f6*x2^3*x3 - 4*f2*f6*x2^2*x3^2 - 4*f3*f6*x2*x3^3
    + (f5^2 - 4*f4*f6)*x3^4;
// The dual Kummer [CF,page 33]
KumDualMat := Matrix(4,4,[
  [ 2*f0*x4, f1*x4, x1, x2 ],
  [ f1*x4, 2*f2*x4 - 2*x1, f3*x4 - x2, x3 ],
  [ x1, f3*x4 - x2, 2*f4*x4 - 2*x3, f5*x4 ],
  [ x2, x3, f5*x4, 2*f6*x4 ]]);
KumDualEqn := Determinant(KumDualMat);
dd := [Deriv(KumEqn,i): i in [1..4]];
assert IsDivisibleBy(Evaluate(KumDualEqn,dd),KumEqn);
dd := [Deriv(KumDualEqn,i): i in [1..4]];
assert IsDivisibleBy(Evaluate(KumEqn,dd),KumDualEqn);

// A linear isomorphism K -> Kdual given by a skew symmetric matrix

// [CF, pages 38 and 184].
h3 := 2*f6*t^3 + f5*t^2;
h4 := 2*f6*t^4 + 2*f5*t^3 + 2*f4*t^2 + f3*t;
h5 := 2*f6*t^5 + 2*f5*t^4 + 2*f4*t^3 + 2*f3*t^2 + 2*f2*t + f1;
A := Matrix(4,4,[
    [   0, h5, h4,t^2 ],
    [ -h5,  0, h3, -t ],
    [ -h4,-h3,  0,  1 ],
    [-t^2,  t, -1,  0 ]]);
star := func<A|Matrix(BaseRing(A),4,4,[
  [ 0, A[4,3], A[2,4], A[3,2] ],
  [ A[3,4], 0, A[4,1], A[1,3] ],
  [ A[4,2], A[1,4], 0, A[2,1] ],
  [ A[2,3], A[3,1], A[1,2], 0 ]])>;
df := Evaluate(Deriv(f),t);  
assert Pfaffian(A) eq df;
assert (R4L!KumDualEqn)^A eq df^2*(R4L!KumEqn);
assert (R4L!KumEqn)^star(A) eq df^2*(R4L!KumDualEqn);

PP<xx> := PolynomialRing(L);
ff := ExactQuotient(PP!f,xx-t);
LL<tt> := quo<PP|ff>;
A1 := Evaluate(A,t);
A2 := Evaluate(A,tt);
assert star(A1)*A2 eq -star(A2)*A1;

// A linear isomorphism K -> Kdual given by a symmetric matrix

K1<r0,r1,r2,s0,s1,s2,f6> := FunctionField(QQ,7);
R41<x1,x2,x3,x4> := PolynomialRing(K1,4);
P1<x> := PolynomialRing(K1);
r := x^3 + r2*x^2 + r1*x + r0;
s := x^3 + s2*x^2 + s1*x + s0;
f := f6*r*s;
cc := Coefficients(f);
myeval := func<F|&+[Evaluate(Coefficients(F)[i],cc)
  *(R41!Monomials(F)[i]) : i in [1..#Terms(F)]]>;
KumEqn1 := myeval(KumEqn);
KumDualEqn1 := myeval(KumDualEqn);
// Some formulae recorded in Section 3.5
la := [ f6*(r0*s2 + r2*s0), f6*(r0 + s0), f6*(r1 + s1), 1 ];
AA := f6*Matrix(K1,3,3,[
  [ r2 - s2, -r1 + s1, r0 - s0 ],
  [ -r1 + s1, r0 + r1*s2 - r2*s1 - s0, -r0*s2 + r2*s0 ],
  [ r0 - s0, -r0*s2 + r2*s0, r0*s1 - r1*s0 ]]);
BB := Matrix(K1,4,4,[la[i]*la[j] : i,j in [1..4]]);
BB +:= DiagonalJoin(Adjoint(AA),ZeroMatrix(K1,1,1));
assert KumDualEqn1^BB eq Determinant(BB)*KumEqn1;  
assert Determinant(BB) eq f6^6*Resultant(r,s)^2;
assert Evaluate(BB,[s0,s1,s2,r0,r1,r2,f6]) eq BB;
assert IsSymmetric(BB);
// Returning to the end of Section 2.1
K2<t1,t2,t3,s0,s1,s2,f6> := FunctionField(QQ,7);
P2<x> := PolynomialRing(K2);
r := (x - t1)*(x - t2)*(x - t3);
s := x^3 + s2*x^2 + s1*x + s0;
f := f6*r*s;
myeval := func<e|P1![Evaluate(c,Coefficients(f)) : c in Eltseq(e)]>;
A0 := Matrix(4,4,[myeval(A[i,j]): i,j in [1..4]]);
A1 := Evaluate(A0,t1);
A2 := Evaluate(A0,t2);
A3 := Evaluate(A0,t3);
r0,r1,r2 := Explode(Coefficients(r));
B := Evaluate(BB,[r0,r1,r2,s0,s1,s2,f6]);
assert A1*star(A2)*A3/((t1-t2)*(t2-t3)*(t3-t1)) eq -B;
// The identity claimed at the end of Section 2.1 now
// follows by symmetry, swapping the cubic factors r and s.

print "Section 2.2 : The desingularised Kummer";

K<f0,f1,f2,f3,f4,f5,f6> := K;
P<x> := PolynomialRing(K);
f := P![f0,f1,f2,f3,f4,f5,f6];
R6<u0,u1,u2,u3,u4,u5> := PolynomialRing(K,6);
mons := MD(R6,2);
R6L := PolynomialRing(L,6);
bb := [1,t,t^2,h3,h4,h5];
uu := &+[R6L.i*bb[i] : i in [1..6]];
LHS := uu^2;
QQQ := [&+[EltseqPad(MC(LHS,R6L!mon))[j]*mon : mon in mons]: j in [1..6]];
assert LHS eq &+[R6L!QQQ[i]*t^(i-1): i in [1..6]];
mat := Matrix(6,6,[EltseqPad(b): b in bb])^(-1);
QQQ := [&+[mat[j,i]*QQQ[j]: j in [1..6]]: i in [1..6]];
assert LHS eq &+[R6L!QQQ[i]*bb[i]: i in [1..6]];
G := QQQ[6]/2;
H := QQQ[5]/2;
S := QQQ[4]/2;
assert G eq u0*u5 + u1*u4 + u2*u3;
assert H eq u0*u4 + u1*u3 - f0*u5^2 - f1*u4*u5 - f2*u4^2 - f3*u3*u4
     - f4*u3^2 + 1/(4*f6)*(u2 - f5*u3)^2;
assert S eq (u0*u3 - 2*f0*u4*u5 - f1*(u3*u5 + u4^2) - 2*f2*u3*u4
     - f3*u3^2 + 1/(2*f6)*(u1 - f3*u4 - 2*f4*u3)*(u2 - f5*u3)
     - 1/(4*f6^2)*f5*(u2 - f5*u3)^2);
GG := 2*SymmetricMatrix(G);
HH := 2*SymmetricMatrix(H);
SS := 2*SymmetricMatrix(S);
assert G eq (1/2)*&+[GG[i,j]*R6.i*R6.j : i,j in [1..6]];
assert H eq (1/2)*&+[HH[i,j]*R6.i*R6.j : i,j in [1..6]];
assert S eq (1/2)*&+[SS[i,j]*R6.i*R6.j : i,j in [1..6]];
assert SS eq HH*GG^(-1)*HH;
assert Determinant(x*GG - HH) eq -(1/f6)*f;
assert Rank(t*GG - HH) eq 5;
assert Vector(Reverse(bb))*(t*GG - HH) eq 0;

Lambda := Matrix(R4,4,6,[
    [   0,   0,  x4,   0,  x3,  x2 ],
    [   0, -x4,   0,  x3,   0, -x1 ],
    [  x4,   0,   0, -x2, -x1,   0 ],
    [ -x3,  x2, -x1,   0,   0,   0 ] ])
    where x1,x2,x3,x4 is Explode([R4.i : i in [1..4]]);
assert Lambda*ChangeRing(GG,R4)*Transpose(Lambda) eq 0;
B := Lambda*ChangeRing(HH,R4)*Transpose(Lambda);
adjB := Adjoint(B);
assert -2*f6*adjB eq KumEqn*Matrix(R4,4,4,[R4.i*R4.j : i,j in [1..4]]);

ASM := func<u|Matrix(4,4,[
  [    0,   u[1],  u[2],  u[4] ],
  [ -u[1],     0,  u[3], -u[5] ],
  [ -u[2], -u[3],     0,  u[6] ],
  [ -u[4],  u[5], -u[6],    0] ])>;
  
Z := ASM([R6.i : i in [1..6]]);
W := star(ASM([Derivative(H,i): i in [1..6]]));
Y := star(ASM([Derivative(S,i): i in [1..6]])); // as in Prop 3.24
P<x> := PolynomialRing(R6);
assert Pfaffian(Z + x*W) eq G - 2*x*H + x^2*S;

// Some maps between the Kummer and desingularised Kummer

DSK := Scheme(Proj(R6),[G,H,S]);
M := Z*star(W);
assert Minors(M,2) subset Ideal(DSK);
assert forall{i : i in [1..4] |
  Evaluate(KumEqn,Eltseq(M[i])) in Ideal(DSK)};
assert forall{i : i in [1..4]|
  Evaluate(KumDualEqn,Eltseq(Transpose(M)[i])) in Ideal(DSK)};
assert Eltseq(M*Z) subset Ideal(DSK);
assert Eltseq(M*W) subset Ideal(DSK);

wedge := func<M|Matrix(BaseRing(M),6,6,
  [M[r[1],s[1]]*M[r[2],s[2]] - M[r[1],s[2]]*M[r[2],s[1]] : r,s in ii])
  where ii is [[1,2],[1,3],[2,3],[1,4],[4,2],[3,4]]>;

Kum := Scheme(Proj(R4),KumEqn);
wedgeB := wedge(B);
assert Transpose(wedgeB) eq wedgeB;
assert Minors(wedgeB,2) subset Ideal(Kum);
for i in [1..6] do
  assert forall{Q : Q in [G,H,S] |
    Evaluate(Q,Eltseq(wedgeB[i])) in Ideal(Kum)};
end for;

print "Section 2.4 : Models for 2-coverings";

toqf := func<q|&+[q[i,j]*R6.i*R6.j : i,j in [1..6]]>;  
mats := [GG*TT^r : r in [0..5]] where TT is GG^(-1)*HH;
Qlist := [(1/f6)*&+[Coefficient(f,i)*mats[i-j]: i in [j+1..6]]: j in [0..5]];
QQlist := [toqf(q): q in Qlist];
Q0,Q1,Q2,Q3,Q4,Q5 := Explode(QQlist);
assert G eq Q5/2;
assert H eq (f6*Q4 - f5*Q5)/(2*f6);
assert S eq (f6^2*Q3 - f5*f6*Q4 + (f5^2 - f4*f6)*Q5)/(2*f6^2);

print "Section 2.6 : Twisted Kummer surfaces";

function GetCovariants(H)
  HH := 2*SymmetricMatrix(H);
  ff := -f6*Parent(f)!Determinant(x*GG - HH);
  ff0,ff1,ff2,ff3,ff4,ff5 := Explode(Eltseq(ff));
  assert Coefficient(ff,6) eq f6;
  mats := [GG*TT^r : r in [0..5]] where TT is GG^(-1)*HH;
  Qlist := [(1/f6)*&+[Coefficient(ff,i)*mats[i-j]: i in [j+1..6]]: j in [0..5]];
  B := Lambda*ChangeRing(HH,R4)*Transpose(Lambda);
  wedgeB := wedge(B);
  qq := [&+[Qlist[m,i,j]*wedgeB[i,j] : i,j in [1..6]] : m in [1..6]];
  Q0H,Q1H,Q2H,Q3H,Q4H,Q5H := Explode(qq);
  MM := [Lambda*ChangeRing(m,R4)*Transpose(Lambda) : m in mats];
  EE := [ExactQuotient(Adjoint(MM[r+1])[4,4],R4.4^2): r in [1..3]];
  E1,E2,E3 := Explode(EE);
  F0 := (1/(2*f6))*E1;
  F1 := Q2H - 2*ff4*F0;
  F2 := -Q1H + ff3*F0;  assert F2 eq -E2 - ff3*F0;
  F3 := Q0H;
  F4 := f6*E3 - (ff2*Q2H - ff3*Q1H + ff4*Q0H) - (ff1*ff5 - 4*ff2*ff4 + 2*ff3^2)*F0;
  assert Q3H eq 4*ff5*F0;
  assert Q4H eq 6*f6*F0;
  assert Q5H eq 0;
  return [F0,F1,F2,F3,F4];
end function;

F0,F1,F2,F3,F4 := Explode(GetCovariants(H));

// Checking the covariance

lambda := Random([10..100]);
P := ChangeRing(RandomSLnZ(4,2,10)*DiagonalMatrix([2,3,5,7]),K);
LHS := GetCovariants(lambda*H^wedge(P));
RHS := [F^(Transpose(P^(-1))) : F in [F0,F1,F2,F3,F4]];
assert LHS eq [lambda^d[i]*Determinant(P)^(d[i]+1)*RHS[i] : i in [1..5]]
  where d is [3,5,6,7,9];
  
// Checking agreement with the biquadratic forms
// (used in the proof of Proposition 3.19)

if have_biquadratic_forms then
  R4<x1,x2,x3,x4> := BaseRing(Lambda);
  BF := BiquadraticForms(f,[x1,x2,x3,x4],[x1,x2,x3,x4]);
  DQ := [2*KumEqn,2*BF[1,4],2*BF[2,4],2*BF[3,4],BF[4,4]];
  assert [F0,F1,F2,F3,F4] eq [-1/(8*f6^2)*p : p in DQ];
end if;

print "Section 3.5 : A formula for the untwisted (2,2,2)-form";

R<x1,x2,x3,x4,y1,y2,y3,y4,z1,z2,z3,z4> := PolynomialRing(K,12);
x := [x1,x2,x3,x4];
y := [y1,y2,y3,y4];
z := [z1,z2,z3,z4];

if have_biquadratic_forms then
  BF := BiquadraticForms(f,x,y);
  Phi := &+[BF[i,j]*z[i]*z[j] : i,j in [1..4]];
  assert Evaluate(Phi,x cat x cat [z1,z2,z3,0])
    eq 2*(z2^2 - z1*z3)*Evaluate(KumEqn,x);
end if;

K1<r0,r1,r2,s0,s1,s2,f6> := K1;
P1<x> := PolynomialRing(K1);
r := x^3 + r2*x^2 + r1*x + r0;
s := x^3 + s2*x^2 + s1*x + s0;
f := f6*r*s;
R<x1,x2,x3,x4,y1,y2,y3,y4,z1,z2,z3,z4> := PolynomialRing(K1,12);
x := [x1,x2,x3,x4];
y := [y1,y2,y3,y4];
z := [z1,z2,z3,z4];

if have_biquadratic_forms then
  BF := BiquadraticForms(f,x,y);
  Phi := &+[BF[i,j]*z[i]*z[j] : i,j in [1..4]];
end if;

Bxy := &+[BB[i,j]*x[i]*y[j] : i,j in [1..4]];

// The computer algebra proof of Lemma 3.15

if have_biquadratic_forms then
  assert Evaluate(Phi,x cat y cat la) eq Bxy^2;
  b := func<i,j|(i eq j select 1 else 2)*BB[i,j]>;
  for i,j in [1..4] do
    for k,l in [1..4] do
      c := func<m,n|MC(BF[m,n],x[i]*x[j]*y[k]*y[l])>;
      assert b(i,j)*b(k,l) eq &+[c(m,n)*b(m,n) : m,n in [1..4] | m le n];
    end for;
  end for;
end if;

R4<x1,x2,x3,x4> := PolynomialRing(K1,4);
x := [x1,x2,x3,x4];
xx := x cat x cat [0,0,0,0];
myeval := func<F|&+[Evaluate(Coefficients(F)[i],Coefficients(f))
  *(R4!Monomials(F)[i]) : i in [1..#Terms(F)]]>;
FF := [myeval(F): F in [F0,F1,F2,F3,F4]];

// Checking the first part of Proposition 3.17

Q := Evaluate(Bxy,xx);
if have_biquadratic_forms then 
  P := 2*(la[2]^2 - la[1]*la[3])*Evaluate(KumEqn1,x)
      + 2*&+[la[i]*Evaluate(BF[i,4],xx) : i in [1..3]]
      + Evaluate(BF[4,4],xx);
  assert Q eq &+[b(i,j)*R4.i*R4.j : i,j in [1..4] | i le j];
  assert P eq Q^2;
end if;

print "Section 3.6 : A formula for the twisted (2,2,2)-form";

// Proposition 3.19 with eps = 0

P0 := (la[2]^2 - la[1]*la[3])*FF[1] + &+[la[i]*FF[i+1] : i in [1..4]];
alpha0 := -1/(8*f6^2);
Q0 := Q;
assert P0 eq alpha0*Q0^2;

// The computer algebra proof of Proposition 3.24

mons := MD(R4,2);
cc := [MC(Q,mon): mon in mons];
PP := alpha0*Matrix(K1,10,10,[cc[i]*cc[j] : i,j in [1..10]]);
assert P0 eq &+[PP[i,j]*mons[i]*mons[j] : i,j in [1..10]];

A := M + Transpose(M) where M is star(W)*Z*star(Y);
R61<u0,u1,u2,u3,u4,u5> := PolynomialRing(K1,6);
cc := Coefficients(f);
myeval := func<F|&+[Evaluate(Coefficients(F)[i],cc)
  *(R61!Monomials(F)[i]) : i in [1..#Terms(F)]]>;
assert mons eq {@ R4.i*R4.j : i,j in [1..4] | i le j @};
AA := [myeval(A[i,j]) : i,j in [1..4] | i le j];
QQlist := [myeval(Q) : Q in QQlist];
Jmat := Matrix(6,6,[Deriv(Q,j): j in [1..6],Q in QQlist]);

PX<X> := PolynomialRing(R61);
xi123 := Resultant(Evaluate(r,X),PX!QQlist);
xi456 := Resultant(Evaluate(s,X),PX!QQlist);
m := (1/2^6)*Determinant(Jmat);
LHS := -f6*(xi123 + xi456 + 2*m);

print "Checking Proposition 3.24 (takes a few seconds)";

time RHS := &+[PP[i,j]*AA[i]*AA[j] : i,j in [1..10]];
assert LHS eq RHS;

/////////////////////////////////////////////////////////

print "Section 4 : Examples";

load "g2ctp_examples.m";
assert #examples eq 380;

R<u0,u1,u2,u3,u4,u5> := PolynomialRing(QQ,6);
mons := MD(R,2);

print "Example 4.5 : y^2 = -3*x^6 + 3*x - 15";

assert exists(e){e : e in examples |
  assigned e`notes and e`notes eq "Example 4.5"};

f := -3*x^6 + 3*x - 15;
assert e`f eq f;
C := HyperellipticCurve(f);
J := Jacobian(C);
K := KummerSurface(J);
pp := {0,2,3,5,7,11} join Set(BadPrimes(C));
defp := [p : p in pp | IsDeficient(C,p)];
assert e`deficient_places eq defp;
assert defp eq [0,3];
assert C eq MinimalWeierstrassModel(C);
assert Discriminant(C) eq -2^8*3^10*5^6*7*31*43;

L<t> := NumberField(x^6 - x + 5);
sel_basis := [<Evaluate(s[1],t),s[2]>: s in e`selmer_basis];
assert sel_basis eq [
    <1, -1>,
    <t^5 - 3*t^4 - 2*t^3 + 5*t^2 + 4*t - 9, 1>,
    <t^5 - 2*t^4 + 2*t^3 - t^2 + 1, 1>
];

G := u0*u5 + u1*u4 + u2*u3;
H1 := u0*u1 - 2*u0*u2 - u1*u2 + u1*u3 - 2*u1*u5 - 2*u2*u5
      - 2*u3*u4 - 2*u4*u5 + 2*u5^2;
H2 := u0*u2 - 2*u0*u3 - 2*u1^2 - u1*u2 + u2^2 - u2*u4 + 3*u2*u5
      + 2*u3^2 + 2*u3*u5 - 4*u4*u5;
H3 := -2*u0*u3 + u1*u2 + u1*u4 - 2*u1*u5 - u2*u3 + 2*u2*u4
      - u3*u4 + 4*u4*u5 + 2*u5^2;

models := [(1/m[1])*&+[m[2,j]*mons[j] : j in [1..#mons]]: m in e`models];
assert [H1/2,H2/2,H3/2] eq [models[i] : i in [2,4,6]];

// Checking these models correspond to the Selmer group elements as claimed

function GetSelmerElement(H,f,L)
  f6 := Coefficient(f,6);
  GG := 2*SymmetricMatrix(G);
  HH := 2*SymmetricMatrix(H);
  x := Parent(f).1;
  assert Determinant(x*GG - HH) eq (-1/f6)*f;
  t := L.1;
  df := Evaluate(Derivative(f),t);
  A := ASM(Eltseq(KernelMatrix(t*GG - HH)));
  xi := f6*Pfaffian(A)/df;
  N := Matrix(6,6,[EltseqPad(A[i,j]) : i,j in [1..4] | i gt j]);
  m := 1/8*Determinant(N);
  assert Norm(xi) eq m^2;
  return <xi,m>;
end function;

c,eps,eta := Explode(sel_basis);
sel := [eps,eta,<eps[1]*eta[1],eps[2]*eta[2]>];
sel_check := [GetSelmerElement(H/2,f,L) : H in [H1,H2,H3]];
for i in [1..3] do
  r := [-1,-1,1][i];
  flag,nu := IsSquare(sel_check[i,1]/(r*sel[i,1]));
  assert flag;
  assert sel_check[i] eq <r*nu^2*sel[i,1],r^3*Norm(nu)*sel[i,2]>;
end for;

// Creating the degree 10 etale algebra

h10 := x^10 - 45*x^8 + 675*x^6 + 2*x^5 - 3375*x^4 - 45*x^3 + 200*x + 1;
L10<u> := NumberField(h10);
PL<X> := PolynomialRing(L10);
L20<v> := NumberField(X^2 + u*X + 5);
PP := PolynomialRing(L20);
cubicfactors := [h[1] : h in Factorization(PP!f)];

function GetLambda(f,L10,cubicfactors)
  r0,r1,r2 := Explode(Coefficients(cubicfactors[1]));
  s0,s1,s2 := Explode(Coefficients(cubicfactors[2]));
  f6 := Coefficient(f,6);
  la1 := f6*(r0*s2 + r2*s0);
  la2 := f6*(r0 + s0);
  la3 := f6*(r1 + s1);
  return [L10 | la2^2 - la1*la3, la1, la2, la3, 1];
end function;

la := GetLambda(f,L10,cubicfactors);

// Computing the twisted Kummer surfaces

R4<x1,x2,x3,x4> := PolynomialRing(QQ,4);
RR := PolynomialRing(L10,4);

function TwistedKummerSurface(H,f,la,R4,RR)
  R<u0,u1,u2,u3,u4,u5> := Parent(H);
  G := u0*u5 + u1*u4 + u2*u3;
  GG := 2*SymmetricMatrix(G);
  HH := 2*SymmetricMatrix(H);
  x := Parent(f).1;
  f0,f1,f2,f3,f4,f5,f6 := Explode(Eltseq(f));
  assert Determinant(x*GG - HH) eq (-1/f6)*f;
  Lambda := Matrix(R4,4,6,[
      [   0,   0,  x4,   0,  x3,  x2 ],
      [   0, -x4,   0,  x3,   0, -x1 ],
      [  x4,   0,   0, -x2, -x1,   0 ],
      [ -x3,  x2, -x1,   0,   0,   0 ] ])
      where x1,x2,x3,x4 is Explode([R4.i : i in [1..4]]);
  M := Lambda*ChangeRing(HH,R4)*Transpose(Lambda);
  adjM := Adjoint(M);
  F0 := ExactQuotient(adjM[4,4],R4.4^2);
  assert adjM eq F0*Matrix(R4,4,4,[R4.i*R4.j : i,j in [1..4]]);
  MM := wedge(M);
  mats := [GG*TT^r : r in [0..5]] where TT is GG^(-1)*HH;
  Qlist := [(1/f6)*&+[Coefficient(f,i)*mats[i-j]
                     : i in [j+1..6]] : j in [0..5]];
  Q0H,Q1H,Q2H
    := Explode([&+[Qlist[m,i,j]*MM[i,j] : i,j in [1..6]] : m in [1..3]]);
  M3 := Lambda*ChangeRing(mats[4],R4)*Transpose(Lambda);
  E3 := ExactQuotient(Adjoint(M3)[4,4],R4.4^2);
  F0 := F0/(2*f6);
  FF := [ F0, Q2H - 2*f4*F0, -Q1H + f3*F0, Q0H,
          f6*E3 - (f2*Q2H - f3*Q1H + f4*Q0H)
          - (f1*f5 - 4*f2*f4 + 2*f3^2)*F0 ];
  P := &+[la[j]*(RR!FF[j]) : j in [1..5]];
  alpha := MC(P,RR.1^4);
  Q := SquareRoot(P/alpha);
  assert P eq alpha*Q^2;
  return F0,-f6*MM,alpha,Q,[FF[i] : i in [2..5]];
end function;

function IsScalarMultiple(F1,F2);
  la := QQ!(F1/F2);
  return la ne 0 and F1 eq la*F2;
end function;

F_eps := 2*x1^3*x2 + 4*x1^3*x3 + 4*x1^3*x4 - 18*x1^2*x2^2 +
  22*x1^2*x2*x3 + 2*x1^2*x2*x4 - 8*x1^2*x3^2 - 4*x1^2*x3*x4 -
  2*x1^2*x4^2 + 6*x1*x2^3 + 6*x1*x2^2*x3 + 7*x1*x2^2*x4 - 6*x1*x2*x3^2
  - 24*x1*x2*x3*x4 - 6*x1*x2*x4^2 + 4*x1*x3^3 + 6*x1*x4^3 - x2^4 +
  3*x2^3*x3 + 3*x2^3*x4 - 3*x2^2*x3*x4 - 5*x2^2*x4^2 + 2*x2*x3^3 -
  2*x2*x3^2*x4 + 2*x2*x4^3 - 2*x3^2*x4^2 + 2*x3*x4^3 + x4^4;
  
// old equation from Jiali's thesis, page 169
G_eps := 24389*x1^4 + 95186*x1^3*x2 + 83106*x1^3*x3 - 107648*x1^3*x4 +
  226470*x1^2*x2^2 + 259910*x1^2*x2*x3 - 347912*x1^2*x2*x4 +
  35670*x1^2*x3^2 + 281908*x1^2*x3*x4 + 216612*x1^2*x4^2 -
  269094*x1*x2^3 + 54858*x1*x2^2*x3 + 70288*x1*x2^2*x4 +
  159068*x1*x2*x3^2 - 561944*x1*x2*x3*x4 + 516*x1*x2*x4^2 +
  47716*x1*x3^3 + 648048*x1*x3^2*x4 - 304804*x1*x3*x4^2 -
  772320*x1*x4^3 + 104621*x2^4 + 102774*x2^3*x3 - 229260*x2^3*x4 -
  32734*x2^2*x3^2 + 674440*x2^2*x3*x4 + 246364*x2^2*x4^2 +
  108444*x2*x3^3 + 1162620*x2*x3^2*x4 - 878172*x2*x3*x4^2 -
  1837912*x2*x4^3 - 212544*x3^4 - 537980*x3^3*x4 + 2226484*x3^2*x4^2 +
  2609168*x3*x4^3 - 3199328*x4^4;

cob_eps := Matrix(QQ,4,4,[
     -106, 30, 45, -61,
     0, -202, 28, -232,
     68, 53, 118, -549,
     29, -89, 256, 120 ]);
assert Determinant(cob_eps) eq 2*5^2*7^2*31^2*43^2;
assert F_eps^cob_eps eq -5*7*31*43*G_eps;

KumEqn,N_eps,alpha_eps,Q_eps
  := TwistedKummerSurface(H1/2,f,la,R4,RR);
assert IsScalarMultiple(KumEqn,F_eps);

F_eta := 2*x1^4 + 3*x1^3*x2 + 7*x1^3*x3 - 4*x1^3*x4 - 13*x1^2*x2^2 -
    10*x1^2*x2*x3 + 3*x1^2*x2*x4 - 3*x1^2*x3^2 + 3*x1^2*x3*x4 +
    x1^2*x4^2 + 18*x1*x2^3 + 24*x1*x2^2*x3 - 2*x1*x2^2*x4 +
    14*x1*x2*x3^2 + 12*x1*x2*x3*x4 - 15*x1*x2*x4^2 + 6*x1*x3^2*x4 -
    3*x1*x3*x4^2 - 2*x1*x4^3 - 4*x2^4 - 32*x2^3*x3 + 24*x2^3*x4 -
    38*x2^2*x3*x4 + 37*x2^2*x4^2 - 8*x2*x3^3 + 8*x2*x3^2*x4 -
    6*x2*x3*x4^2 + 9*x2*x4^3 - 2*x3^3*x4 + 3*x3^2*x4^2 + x3*x4^3 -
    x4^4;

// old equation from Jiali's thesis, page 169
G_eta := 18*x1^4 - 44*x1^3*x2 - 4*x1^3*x3 - 192*x1^3*x4 +
  128*x1^2*x2^2 - 60*x1^2*x2*x3 + 60*x1^2*x2*x4 - 472*x1^2*x3^2 +
  48*x1^2*x3*x4 + 4*x1^2*x4^2 - 50*x1*x2^3 + 1008*x1*x2^2*x3 -
  1316*x1*x2^2*x4 + 214*x1*x2*x3^2 + 5032*x1*x2*x3*x4 -
  1060*x1*x2*x4^2 + 1492*x1*x3^3 + 732*x1*x3^2*x4 + 948*x1*x3*x4^2 +
  748*x1*x4^3 + 300*x2^4 - 486*x2^3*x3 + 1277*x2^3*x4 + 1364*x2^2*x3^2
  + 7457*x2^2*x3*x4 - 4467*x2^2*x4^2 + 1622*x2*x3^3 - 6665*x2*x3^2*x4
  + 11222*x2*x3*x4^2 - 1132*x2*x4^3 + 6280*x3^4 + 25707*x3^3*x4 +
  13719*x3^2*x4^2 + 416*x3*x4^3 - 846*x4^4;

cob_eta := Matrix(QQ,4,4,[
     -6, 12, 4, 17,
      1, 4, 10, 32,
     -7, -17, -17, -18,
     -6, -20, 14, -35 ]);
assert Determinant(cob_eta) eq 2*7^2*43^2;
assert F_eta^cob_eta eq 2*7*43*G_eta;

KumEqn,N_eta,alpha_eta,Q_eta
  := TwistedKummerSurface(H2/2,f,la,R4,RR);
assert IsScalarMultiple(KumEqn,F_eta);

// A Q-point on K_eps with inverse image in J_eta defined over Q(sqrt(-3)).

pt_eta := [QQ|10,-24,-1,3]; 
assert Evaluate(G_eta,pt_eta) eq 0;
pt_eta := Eltseq((-1/301)*Vector(pt_eta)*Transpose(cob_eta));
assert pt_eta eq [QQ|1,0,-1,-1];
assert Evaluate(F_eta,pt_eta) eq 0;
assert Evaluate(N_eta[3,3],pt_eta) eq -3*3^2;

// Equation for the twisted Kummer surface K_(eps+eta)

F_sum := 4*x1^4 - 24*x1^3*x2 - 4*x1^3*x3 - 8*x1^3*x4 + 8*x1^2*x2^2 -
  10*x1^2*x2*x3 + 6*x1^2*x2*x4 - 9*x1^2*x3^2 - 2*x1^2*x3*x4 -
  x1^2*x4^2 - 2*x1*x2^3 + 16*x1*x2^2*x3 + 8*x1*x2^2*x4 + 12*x1*x2*x3^2
  + 24*x1*x2*x3*x4 - 2*x1*x3^3 + 2*x1*x3*x4^2 + 4*x2^3*x4 +
  2*x2^2*x3^2 - 6*x2^2*x3*x4 - 4*x2^2*x4^2 + 9*x2*x3^3 + 3*x2*x3^2*x4
  + 3*x2*x3*x4^2 + x2*x4^3 + 4*x3^3*x4;

KumEqn,N_sum,alpha_sum,Q_sum,covmap
  := TwistedKummerSurface(H3/2,f,la,R4,RR);
assert IsScalarMultiple(KumEqn,F_sum);
mat := SymmetricMatrix(Q_sum)^(-1);
Q_sum_dual := &+[mat[i,j]*RR.i*RR.j : i,j in [1..4]];

// A Q-point on K_(eps + eta) that lifts to a Q-point on J_(eps+eta).

pt_sum := [QQ|1,-2,-2,0];
assert Evaluate(F_sum,pt_sum) eq 0;
assert Evaluate(N_sum[1,1],pt_sum) eq 6^2;
Ksum := Scheme(Proj(R4),F_sum);
K0 := Scheme(Proj(R4),DefiningPolynomial(K));
pi := map<Ksum->K0|covmap>; // the 2-covering map
assert pi(Ksum!pt_sum) eq K0![ 124, 238, 199, 3607 ];
assert e`generators eq [[ 124, 238, 199, 3607 ]];

// Computing the quadratic form g on K_eps needed to compute
// CTP(eps,eta).

mu := SquareRoot(6*alpha_eps*alpha_eta/alpha_sum);
psi0 := mu*Evaluate(Q_eta,pt_eta)*Evaluate(Q_sum_dual,[1,0,0,0]);
psi1 := mu*Evaluate(Q_eta,pt_eta)*Evaluate(Q_sum_dual,[30,27,-22,-8]);
g0 := &+[Trace(psi0*MC(Q_eps,RR!m))*m: m in MD(R4,2)];
g1 := &+[Trace(psi1*MC(Q_eps,RR!m))*m: m in MD(R4,2)];

g := 12*x1*x2 - 2*x2^2 + 6*x2*x3 + 3*x2*x4;

// old equation from Jiali's thesis, page 170
gg := 2223864*x1^2 + 14731410*x1*x2 + 24847815*x1*x3 - 24788337*x1*x4
  + 70375177*x2^2 + 74632289*x2*x3 - 70720951*x2*x4 - 15633788*x3^2
  + 80664164*x3*x4 + 58358461*x4^2;

assert IsScalarMultiple(g,g0);
assert IsScalarMultiple(gg,g1^cob_eps);

// Some local points on K_eps that lift to local points on J_eps

local_table := [
<  2, [3,4,1,2^2], -2, 1 >,
<  3, [1,-1,0,-3^2],1, 0 >,
<  5, [0,1,1,1],    2, 0 >,
<  7, [0,1,0,1],    1, 0 >,
< 31, [0,1,0,1],    1, 0 >,
< 43, [0,1,0,1],    1, 0 >,
<  0, [0,1,1,1],    1, 0 > ];

for dd in local_table do
  p,pt,gg := Explode(dd);
  Qp := p eq 0 select RealField() else pAdicField(p,50);
  IsDefinitelySquare := func<x|IsSquare(x) and
    (p eq 0 select (Abs(x) gt 0.01) else (Valuation(x) lt 10))>;
  if p in [2,3] then
    R<t> := PolynomialRing(Qp);
    poly := Evaluate(F_eps,[pt[1],pt[2],pt[3],pt[4]+p^3*t]);
    rts := [r[1] : r in Roots(poly) | Valuation(r[1]) ge 0];
    assert #rts eq 1;
    pt := [pt[1],pt[2],pt[3],pt[4]+p^3*rts[1]];
    assert Valuation(Evaluate(F_eps,pt)) gt 40;
  else
    assert Evaluate(F_eps,pt) eq 0;
  end if;
  assert IsDefinitelySquare(Qp!Evaluate(N_eps[1,1],pt));
  assert IsDefinitelySquare(Qp!Evaluate(g,pt)*gg);
end for;

assert e`ctp eq [[0,1,1],[1,1,1],[1,1,1]];

print "Example 4.6 : LMFDB label = 49471.a.49471.1";

assert exists(e){e : e in examples |
  assigned e`notes and e`notes eq "Example 4.6"};
assert e`label eq "49471.a.49471.1";
assert e`f eq -3*x^6 - 4*x^5 - 10*x^4 - 51*x^2 + 80*x - 28;
assert e`f eq (-3*x^3 + 5*x^2 - 13*x + 7)*(x^3 + 3*x^2 + 4*x - 4);
assert e`c eq [0,0];
assert e`ctp eq [[0,1],[1,0]];

print "Example 4.7 : Logan and van Luijk";

assert exists(e){e : e in examples |
  assigned e`notes and e`notes eq "Example 4.7"};
f := -6*(x^2 + 1)*(x^2 - 2*x - 1)*(x^2 + x - 1);
assert e`f eq f;
assert e`torsion eq [2,2];
L<t> := quo<P|e`f>;
LL,iso := AbsoluteAlgebra(L);
sel := [<Evaluate(s[1],t),s[2]>: s in e`selmer_basis];
assert sel eq [
    <1, -1>,
    <t^4 - t^3 - t^2 - 2*t - 2, 18>,
    <5*t^3 - 14*t^2 + 1, 900>,
    <t^4 + t^3 + 5*t^2 - 3, 270>
];
models := [(1/m[1])*&+[m[2,i]*mons[i] : i in [1..#mons]] : m in e`models];
sel_check := [GetSelmerElement(models[i],f,L) : i in [1,2,4,8]];
for i in [1..4] do
  r := [-1,2,-2,-3][i];
  ss := sel_check[i,1]/(r*sel[i,1]);
  nu := <Sqrt(s): s in iso(ss)> @@ iso;
  assert sel_check[i] eq <r*nu^2*sel[i,1],r^3*Norm(nu)*sel[i,2]>;
end for;
assert e`c eq [1,0,0,0];
assert e`ctp eq [
    [ 0, 1, 0, 0 ],
    [ 1, 1, 0, 0 ],
    [ 0, 0, 0, 0 ],
    [ 0, 0, 0, 0 ]
];

function KummerEquation(H)
  HH := 2*SymmetricMatrix(H);
  Lambda := Matrix(R4,4,6,[
      [   0,   0,  x4,   0,  x3,  x2 ],
      [   0, -x4,   0,  x3,   0, -x1 ],
      [  x4,   0,   0, -x2, -x1,   0 ],
      [ -x3,  x2, -x1,   0,   0,   0 ] ])
      where x1,x2,x3,x4 is Explode([R4.i : i in [1..4]]);
  M := Lambda*ChangeRing(HH,R4)*Transpose(Lambda);
  return ExactQuotient(Adjoint(M)[4,4],R4.4^2);
end function;

pts := [[ 0, -3, -7, 6 ], [], [], [ -1, -1, -5, 10 ], [ 1, 1, 1, 0 ],
[ -1, -1, 2, 1 ], [ 2, 0, -3, 5 ], [ 0, 1, 1, 2 ], [ -2, -5, 1, 10 ],
[ 2, 6, -1, 2 ], [ 1, 3, 3, 9 ], [ 6, -6, -7, 10 ], [ 0, 1, -1, 3 ],
[ 0, 0, 1, 2 ], [ -1, 1, 0, 1 ]];
assert forall{ i : i in [1] cat [4..15] |
  Evaluate(KummerEquation(models[i]),pts[i]) eq 0};

print "Example 4.8 : CTP on S^2(J/Q) has rank 3";

assert exists(e){e : e in examples |
  assigned e`notes and e`notes eq "Example 4.8"};
f := 3*x^6 + 10*x^5 - 16*x^4 + 18*x^3 + 23*x^2 - 54*x - 17;
C := HyperellipticCurve(f);
J := Jacobian(C);
K := KummerSurface(J);
assert e`f eq f;
assert #GaloisGroup(f) eq 720;
L<t> := NumberField(f);
sel := [<Evaluate(s[1],t),s[2]>: s in e`selmer_basis];
assert sel eq [
    <1, -1>,
    <3*t^2 - 8*t + 10, 2041>,
    <2*t^2 - 4*t + 15, 16657/3>,
    <6*t^3 + 14*t^2 - 16*t - 31, 37503>,
    <2*t^4 + 9*t^3 - 3*t^2 - 5*t + 1, 2925>
];
models := [(1/m[1])*&+[m[2,i]*mons[i] : i in [1..#mons]] : m in e`models];
sel_check := [GetSelmerElement(models[i],f,L) : i in [1,2,4,8,16]];
for i in [1..5] do
  r := [6,-6,6,-6,3][i];
  flag,nu := IsSquare(sel_check[i,1]/(r*sel[i,1]));
  assert flag;
  assert sel_check[i] eq <r*nu^2*sel[i,1],r^3*Norm(nu)*sel[i,2]>;
end for;
assert e`c eq [ 1, 0, 0, 0, 0 ];
assert e`ctp eq 
[
    [ 1, 0, 0, 0, 1 ],
    [ 0, 0, 1, 1, 0 ],
    [ 0, 1, 0, 0, 1 ],
    [ 0, 1, 0, 0, 1 ],
    [ 1, 0, 1, 1, 1 ]
];
assert Rank(Matrix(GF(2),5,5,e`ctp)) eq 3;
assert e`generators eq [[11, -98, 78, -2217],[44, 72, 124, -245]];
gens := &join[Points(J,K!P): P in e`generators];
assert #ReducedBasis(gens) eq 2;

print "Example 4.9 : A rank 1 example of Bruin and Stoll";

assert exists(e){e : e in examples |
  assigned e`notes and e`notes eq "Example 4.9"};
f := -x^6 + 2*x^5 + 3*x^4 + 2*x^3 - x - 3;
assert e`f eq f;
C := HyperellipticCurve(f);
J := Jacobian(C);
K := KummerSurface(J);
L<t> := NumberField(e`f);
sel_basis := [<Evaluate(s[1],t),s[2]>: s in e`selmer_basis];
assert sel_basis eq [
    <1, -1>,
    <t^2 + t + 1, 4>,
    <t^3 - 4*t^2 + 3*t - 1,8>
];
H1 := u0*u2 - u0*u4 + 2*u1*u3 - 2*u1*u5 + 2*u2^2 + 2*u2*u3
      + 4*u3^2 - 10*u3*u5 - 2*u4*u5;
H2 := 2*u0^2 + 2*u0*u1 + 2*u0*u4 + 4*u1*u5 + 2*u2^2 + 2*u2*u3
      + 4*u2*u5 - u3*u4 + 3*u3*u5;
H3 := u0*u4 + 2*u1*u2 - 2*u1*u3 + 4*u1*u4 - 2*u2*u3 + 8*u3*u5
      - u4^2 - 6*u4*u5 - 2*u5^2;
models := [(1/m[1])*&+[m[2,j]*mons[j] : j in [1..#mons]]: m in e`models];
assert [H1/2,H2/2,H3/2] eq [models[i] : i in [2,4,6]];
c,eps,eta := Explode(sel_basis);
sel := [eps,eta,<eps[1]*eta[1],eps[2]*eta[2]>];
sel_check := [GetSelmerElement(H/2,f,L) : H in [H1,H2,H3]];
for i in [1..3] do
  r := [1,-1,1][i];
  flag,nu := IsSquare(sel_check[i,1]/(r*sel[i,1]));
  assert flag;
  assert sel_check[i] eq <r*nu^2*sel[i,1],r^3*Norm(nu)*sel[i,2]>;
end for;
assert e`c eq [ 1, 0, 0 ];
assert e`ctp eq 
[
    [ 0, 0, 0 ],
    [ 0, 0, 1 ],
    [ 0, 1, 0 ]
];
assert e`generators eq [[9536,-5312,5008,53113]];
gens := &join[Points(J,K!P): P in e`generators];
assert #ReducedBasis(gens) eq 1;

print "Examples from an experiment of Bruin and Stoll";

bs_data := [
    <2, 0, -3*x^6 + x^5 + 3*x^4 - x^3 + 3*x^2 + 3*x - 1, "2^8*5*257*292661", "15.999999999543">,
    <2, 0, 2*x^6 - 3*x^5 - 3*x^4 - 3*x^3 - x^2 + x - 1, "2^14*43*97*647", "16.000000000268">,
    <2, 0, -x^6 + 3*x^5 + 2*x^4 - x^2 + 2*x - 2, "2^10*29*373*4139", "15.99999999620">,
    <2, 0, -x^6 + 3*x^5 + 3*x^4 - 3*x^3 - 2*x^2 + x - 2, "2^8*5569*33353", "15.9999999877">,
    <2, 0, -3*x^6 + 3*x^5 - x^4 + 2*x^3 + x^2 + 2*x + 3, "2^8*3*7*8753*28081", "15.999981">,
    <2, 0, -3*x^6 - x^5 + 2*x^4 + 3*x^3 + 2*x^2 + 2*x - 2, "2^10*3*43*557*5209", "15.9999856">,
    <2, 0, -3*x^6 - x^5 + 2*x^4 + 3*x^3 + 3*x - 1, "2^12*3*389*39107", "15.999999569">,
    <2, 0, -3*x^6 - 2*x^5 - x^4 + 3*x^3 + 3*x^2 + 2*x - 3, "2^8*339913073", "15.9999999999999807">,
    <2, 0, -3*x^6 - 3*x^5 - x^4 + 2*x^3 - 3*x^2 - 2*x + 3, "2^8*3*2041535471", "15.999582">,
    <2, 0, -3*x^6 + 3*x^5 + 2*x^3 + 3*x^2 + 2*x - 2, "2^10*3^3*43235921", "15.999229">,
    <2, 0, -3*x^6 - 3*x^5 - 2*x^4 - 2*x^3 + 3, "2^8*3^4*7*5069011", "15.999868">,
    <2, 0, -3*x^6 + 3*x^3 - 2*x^2 + 3*x + 2, "2^8*3^3*191*866581", "15.9999832">,
    <2, 0, -3*x^6 - 3*x^5 + 3*x^4 + 2*x^2 + x - 2, "2^11*3^3*61*22777", "15.999999831">,
    <2, 0, -2*x^6 + 3*x^5 + 3*x^4 - 3*x^3 - 3*x - 2, "2^8*3^6*67*1627", "16.0000000000542">,
    <2, 0, -3*x^6 - x^5 + 3*x^4 - 3*x^3 + 2*x^2 - 2*x - 2, "2^12*3*127*628189", "15.999521">,
    <2, 0, -3*x^6 - 3*x^5 + x^4 - 2*x^3 + x^2 - x - 2, "2^8*3*5*13*919*6997", "15.9999744">,
    <2, 0, 3*x^6 - 2*x^4 - 2*x^3 + 3*x - 3, "2^8*3^4*997*36017", "15.999813">,
    <2, 0, -3*x^6 - x^5 + 3*x^4 - 2*x^3 - x^2 + 3, "2^8*3*7*157*673*2053", "15.999469">,
    <2, 0, -3*x^6 + 3*x^5 + x^4 - 3*x^3 - 3*x^2 - 2*x + 2, "2^11*3*59*1481*1759", "15.999750">,
    <2, 0, -3*x^6 - 3*x^5 + 2*x^3 + x^2 - x + 3, "2^8*3^4*53*61*17053", "15.9997289">,
    <2, 0, 2*x^6 - 3*x^5 - 2*x^4 - 3*x^3 - 3*x^2 - 3*x - 3, "2^8*3^3*47*2026021", "15.9999288">,
    <2, 0, -x^6 - 3*x^5 + 2*x^4 + 3*x^3 - 3*x^2 - 3*x - 2, "2^8*149743897", "15.99999999468">,
    <2, 0, -3*x^6 - x^5 + 3*x^4 - x^3 + x^2 - 2*x - 3, "2^11*466805681", "15.99999155">,
    <2, 0, 3*x^6 + 3*x^5 - 3*x^4 + 3*x^3 - 2*x^2 + x - 3, "2^8*3^3*579859243", "15.999088">,
    <2, 0, 3*x^6 - 2*x^5 + x^4 + 3*x^3 + x^2 - x - 3, "2^11*6983*114001", "15.999107">,
    <2, 0, -3*x^6 - x^5 + x^4 - 3*x^3 - x^2 + x + 2, "2^12*7*7388099", "15.99999780">,
    <2, 0, 3*x^6 + 2*x^5 - x^4 + 3*x^3 + x - 3, "2^8*7^2*743*208003", "15.999794">,
    <2, 0, -3*x^6 - 3*x^5 + x^4 - 3*x^3 - x - 3, "2^8*3^5*43*385153", "15.9999694">,
    <2, 0, -3*x^6 - x^5 + 2*x^4 + 2*x^2 - 3*x - 3, "2^10*3*577*633877", "15.999663">,
    <2, 0, -x^6 - 2*x^5 + 3*x^4 - 3*x^3 + 3*x^2 - x - 3, "2^13*919*26813", "15.99999999999738">,
    <2, 0, 2*x^6 + 3*x^5 - x^4 + 2*x^3 + x^2 + x - 3, "2^8*73*1973*14549", "15.99999738">,
    <2, 0, -3*x^6 - x^5 + 2*x^4 - 2*x^3 - x^2 - 3*x - 2, "2^12*197*283*1307", "15.9999809">,
    <2, 0, 3*x^6 + 2*x^5 + x^4 - 2*x^3 - 3*x^2 + x - 3, "2^8*11*53*11425459", "15.999234">,
    <2, 0, -3*x^6 - 3*x^5 + 2*x^4 + 2*x^2 - 2, "2^12*3*12688303", "15.999999253">,
    <2, 0, -3*x^6 - x^5 - 3*x^3 + 3*x^2 - x - 2, "2^8*3*83*719*8039", "16.00000401">,
    <2, 0, -3*x^6 + 3*x^5 + 3*x^4 + 2*x^3 + x^2 + 3*x - 3, "2^12*3^5*7052371", "15.9893">,
    <3, 1, -3*x^6 + 2*x^5 - x^4 + 3*x^3 + 2*x^2 + 3*x - 3, "2^8*3*2886818791", "3.999999116">,
    <3, 1, -2*x^6 + 2*x^5 - 3*x^3 + 3*x^2 - 3*x - 3, "2^12*3^4*17*37057", "4.0000000700">,
    <3, 1, -x^6 - 3*x^5 + 2*x^4 - x^3 + x^2 + x - 3, "2^8*23^2*449*2633", "4.00000000636">,
    <3, 1, -x^6 + 2*x^5 + 3*x^4 + 2*x^3 - x - 3, "2^8*256881397", "4.000000000267">,
    <3, 1, -3*x^6 - x^5 + x^4 - x^3 + 3*x^2 - 3*x - 3, "2^8*3^4*211*647*829", "4.0000204">,
    <3, 1, -3*x^6 - 3*x^5 + x^4 + 3*x^3 + 3*x^2 - x + 3, "2^8*3^5*67*585337", "16.0000523">,
    <3, 1, 2*x^6 - 3*x^5 - 2*x^4 - 3*x^3 + 3*x^2 + x - 3, "2^8*4033156073", "15.99999328">,
    <3, 1, 3*x^6 - x^5 - 2*x^4 - 3*x^3 + x^2 + x - 3, "2^8*17*339748817", "15.9999702">,
    <3, 1, -3*x^6 + x^5 - x^4 - 2*x^3 + 2*x^2 - 2*x - 2, "2^14*7*468719", "16.000000000498">,
    <3, 1, 2*x^6 - 2*x^5 - 3*x^4 - 2*x^3 + x - 3, "2^10*107*6203297", "16.00000467">,
    <4, 2, 3*x^6 + 3*x^5 + x^4 - 3*x^3 - 3*x^2 + x - 3, "2^8*3^4*13*17*89*6229", "16.0000009986">
];
assert #bs_data eq 47;

for ctr in [1..#bs_data] do
  dimS2,rank,f,disc,nsha := Explode(bs_data[ctr]);
  C := HyperellipticCurve(f);
  Cmin := MinimalWeierstrassModel(C);
  assert Abs(Discriminant(Cmin)) eq (eval disc);
  label0 := Sprintf("Bruin Stoll #%o",ctr);
  assert exists(e){e : e in examples |
    assigned e`label and e`label eq label0 };
  assert e`f eq f;
  assert e`rank eq rank;
  assert #e`models eq 2^dimS2 - 1;
  assert e`discriminant eq (eval disc);
  assert e`analytic_order_III eq Round(eval nsha);
  J := Jacobian(C);
  K := KummerSurface(J);
  ptsJ := &join[Points(J,K!P): P in e`generators];
  assert #ReducedBasis(ptsJ) eq rank;
  tors := #[x : x in e`torsion | IsEven(x)];
  ctp := Matrix(GF(2),dimS2,dimS2,e`ctp);
  rankbound := dimS2 - tors - Rank(ctp);
  if ctr in [37..41] then       // the 5 easier cases
    assert rank eq rankbound;
    printf "v";
    continue;
  end if;
  assert rank eq rankbound - 2;
  if ctr in [2,21,23,33] then   // the 4 unresolved cases
    printf "x";
    continue;                 
  end if;
  // The remaining cases are solved by combining the
  // methods of visibility and computing the CTP.
  label1 := label0 cat " over Q(sqrt(d))";
  assert exists(ee){e : e in examples |
    assigned e`label and e`label eq label1 };
  assert ee`f eq f;
  d := ee`d;
  assert d in { -7, -3, -2, -1, 2, 3, 5 };
  C1 := HyperellipticCurve(d*f); // quadratic twist by d
  J1 := Jacobian(C1);
  K1 := KummerSurface(J1);
  ptsJ := &join[Points(J,K!P): P in ee`generators];
  ptsJ1 := &join[Points(J1,K1![P[1],P[2],P[3],d*P[4]])
                                      : P in ee`generators];
  ptsJ := ReducedBasis(ptsJ);
  ptsJ1 := ReducedBasis(ptsJ1);
  assert rank eq #ptsJ;
  assert ee`rank eq #ptsJ + #ptsJ1;
  tors_k := #[x : x in ee`torsion | IsEven(x)];
  dimS2_k := Valuation(#ee`models + 1,2);
  assert #ee`models eq 2^dimS2_k - 1;
  assert ee`deficient_places eq [];
  assert ee`rank eq dimS2_k - tors_k - 2;
// Since the number of deficient places is even, and
// we only need to improve the rank bound for J(k) by 2,
// it suffices to show that the Cassels-Tate pairing on
// S^2(J/k) is non-zero. The field "ctp_hint" lists a
// pair of elements eps,eta with CTP(eps,eta) != 0
// together with a k-point on K_eta.
  assert assigned ee`ctp_hint;
  printf ".";
end for;
print "";

print "Example 4.11 : A rank 2 example of Bruin and Stoll";

assert exists(e){e : e in examples |
  assigned e`notes and e`notes eq "Example 4.11"};
assert e`label eq "Bruin Stoll #47";
f :=  3*x^6 + 3*x^5 + x^4 - 3*x^3 - 3*x^2 + x - 3;
f0,f1,f2,f3,f4,f5,f6 := Explode(Eltseq(f));
assert e`f eq f;
assert #GaloisGroup(f) eq 720;
assert e`deficient_places eq [];

L<t> := NumberField(f);
sel := [<Evaluate(s[1],t),s[2]>: s in e`selmer_basis];
assert sel eq [
    <1, -1>,
    <t^2 + t, 1>,
    <3*t^4 - 3*t^2 + 1, 169/3>,
    <3*t^5 + 3*t^4 + t^3 + 3*t^2 + 1, 9>
];
models := [(1/m[1])*&+[m[2,i]*mons[i] : i in [1..#mons]] : m in e`models];
sel_check := [GetSelmerElement(models[i],f,L) : i in [1,2,4,8]];
for i in [1..4] do
  r := [3,-1,-39,-3][i];
  flag,nu := IsSquare(sel_check[i,1]/(r*sel[i,1]));
  assert flag;
  assert sel_check[i] eq <r*nu^2*sel[i,1],r^3*Norm(nu)*sel[i,2]>;
end for;
assert e`c eq [1,0,0,0];
assert Matrix(e`ctp) eq 0;

// We have 2 points of infinite order on the Jacobian

C := HyperellipticCurve(f);
J := Jacobian(C);
K := KummerSurface(J);
ptsK := [[ 2, -1, -4, -18 ],[ 2, 1, 1, 9 ]];
ptsJ := &join[Points(J,K!P) : P in ptsK];
assert #ReducedBasis(ptsJ) eq 2;

// We have 2 points of infinite order on the quadratic twist by -3

C1 := HyperellipticCurve(-3*f);
J1 := Jacobian(C1);
K1 := KummerSurface(J1);
ptsK1 := [[ 1, -1, 0, 3 ],[ 1, -1, 0, 39 ]];
ptsJ1 := &join[Points(J1,K1!P) : P in ptsK1];
assert #ReducedBasis(ptsJ1) eq 2;

assert MinimalWeierstrassModel(C) eq C;
assert Discriminant(C) eq 2^8*3^4*13*17*89*6229;

assert exists(ee){e : e in examples |
  assigned e`label and e`label eq "Bruin Stoll #47 over Q(sqrt(d))"};
assert ee`f eq f;
assert ee`d eq -3;

k<z> := CyclotomicField(3);
s := 2*z + 1;
assert s^2 eq -3;
R<u0,u1,u2,u3,u4,u5> := PolynomialRing(k,6);
mons := MD(R,2);
Ok := RingOfIntegers(k);
Pk<x> := PolynomialRing(k);
L<t> := NumberField(Pk!(f/f6));
sel_basis := [
    <1, -1>,
    <t^2 + t, 1>,
    <3*t^4 - 3*t^2 + 1, 169/3>,
    <3*t^5 + 3*t^4 + t^3 + 3*t^2 + 1, 9>,
    <3*(1 + z)*t^4 - 10*t^2 - 8*z*t - 5 - 2*z, -1543 - 2462*z>,
    <3*(2 + z)*t^3 - 2*(2 + z)*t, -171>
];
ll := 4*(1 - z);
H1 := (2 + z)*u0^2 - 2*(1 - z)*u0*u4 - 2*(1 - z)*u0*u5 + 2*u1^2
   - 4*u1*u3 + 5*(1 + 2*z)*u2^2 + 6*(3 + 2*z)*u2*u4
   + 4*(7 + 8*z)*u2*u5 - 2*u3^2 + 8*u3*u4 + 2*u4^2 + 18*u4*u5
   + (29 + 16*z)*u5^2;
H2 := 2*u0*u2 + 2*(1 - z)*u0*u3 - z*u1^2 - 2*(1 - z)*u1*u4
   - 4*u2^2 + 4*u2*u4 + 8*u2*u5 - 4*(1 - z)*u3*u4 - 8*(1 - z)*u3*u5
   - u4^2 + 8*(1 + 3*z)*u4*u5 - 16*u5^2;
H3 := 4*u0^2 + 8*u0*u1 + 4*u0*u2 - 4*z*u0*u3 - 8*z*u0*u4
   + (3 - z)*u1^2 + 4*(1 + z)*u1*u2 - 2*(1 - z)*u1*u4 + 2*z*u2^2
   + 2*(1 + 2*z)*u2*u5 - 2*(1 - 2*z)*u3^2 - 4*u3*u4 + 2*(2 + z)*u3*u5
   - (1 - 3*z)*u4^2;
models := [<Evaluate(m[1],s),[Evaluate(c,s): c in m[2]]>: m in ee`models];
models := [(1/m[1])*&+[m[2,j]*mons[j] : j in [1..#mons]] : m in models];
assert [H1/ll,H2/ll,H3/ll] eq [models[i] : i in [16,32,48]];

_,_,_,_,eps,eta := Explode(sel_basis);
sel := [eps,eta,<eps[1]*eta[1],eps[2]*eta[2]>];
sel_check := [GetSelmerElement(H/ll,Pk!f,L) : H in [H1,H2,H3]];
for i in [1..3] do
  r := [-1,z,1-z][i];
  flag,nu := IsSquare(sel_check[i,1]/(r*sel[i,1]));
  assert flag;
  assert sel_check[i] eq <r*nu^2*sel[i,1],r^3*Norm(nu)*sel[i,2]>;
end for;

// Creating the degree 10 etale algebra

h10 := 729*x^10 + 729*x^9 + 6075*x^8 + 2646*x^7 + 11502*x^6
   - 5481*x^5 - 15525*x^4 - 24363*x^3 - 48600*x^2 - 14023*x - 6408;
L10<u> := NumberField(h10);
PL<X> := PolynomialRing(L10);
L20<v> := NumberField(X^2 + u*X - 1);
PP := PolynomialRing(L20);
cubicfactors := [h[1] : h in Factorization(PP!f)];
la := GetLambda(f,L10,cubicfactors);

// Computing the twisted Kummer surfaces

R4<x1,x2,x3,x4> := PolynomialRing(k,4);
RR := PolynomialRing(L10,4);
F_eps,N_eps,alpha_eps,Q_eps := TwistedKummerSurface(H1/ll,Pk!f,la,R4,RR);
F_eta,N_eta,alpha_eta,Q_eta := TwistedKummerSurface(H2/ll,Pk!f,la,R4,RR);
F_sum,N_sum,alpha_sum,Q_sum := TwistedKummerSurface(H3/ll,Pk!f,la,R4,RR);

pt_eta := [Evaluate(w,s): w in ee`ctp_hint[3]];
assert pt_eta eq [ z, 1, 2*z + 2, -4*z - 2 ];
assert Evaluate(F_eta,pt_eta) eq 0;
N := Evaluate(N_eta,pt_eta);
assert N[1,1] ne 0;
a := 7 + 4*z;
assert Norm(a) eq 37;
assert forall{i : i in [1..6] | IsSquare(N[i,i]*a)};

mat := SymmetricMatrix(Q_sum)^(-1);
Q_sum_dual := &+[mat[i,j]*RR.i*RR.j : i,j in [1..4]];

mu := SquareRoot((4+2*z)*alpha_eps*alpha_eta/alpha_sum);
psi := mu*Evaluate(Q_eta,pt_eta)*Evaluate(Q_sum_dual,[1,0,0,0]);
g := (3*z/2)*&+[Trace(psi*MC(Q_eps,RR!m))*m: m in MD(R4,2)];

assert g eq -(233 + 446*z)*x1^2 - (276 - 308*z)*x1*x2
   + (178 - 316*z)*x1*x3 + (118 + 260*z)*x1*x4 + (228 - 196*z)*x2^2
   - (4 + 188*z)*x2*x3 + (84 - 300*z)*x2*x4 + (227 + 34*z)*x3^2
   - (6 - 36*z)*x3*x4 - (17 + 82*z)*x4^2;
assert ideal<Ok|Coefficients(g)> eq 1*Ok;

pushout := 4*N_eps[1,1];
assert ideal<Ok|&cat[Coefficients(pushout): i,j in [1..6]]> eq 1*Ok;
KumEqn := 72*F_eps;
assert ideal<Ok|Coefficients(KumEqn)> eq 1*Ok;
mons := MD(R4,4);

S0 := [ 2, 3, 5, 7, 11, 13, 17, 19, 37, 89, 6229 ];
S := &cat[[pp[1] : pp in Decomposition(Ok,p)]: p in S0];

primes := [ -z + 1, 5, -z + 2, -z - 3, 11, -z + 3, -z - 4, 17,
  -3*z + 2, 2*z - 3, -4*z + 3, 3*z - 4, 89, -20*z + 67, -20*z - 87 ];
	      
localpts := [[ 0, 1, 1, 1], [ 1, 4, 1, 4 ], [ 0, 0, 1, 1 ],
  [ 2, 4, 1, 0 ], [ 6, 9, 10, 1 ], [ 0, 2, 1, 1 ], [ 0, 5, 0, 1 ],
  [ 5, 6, 0, 1 ], [ 4, 0, 0, 1 ], [ 6, 7, 0, 1 ], [ 4, 0, 0, 1 ],
  [ 2, 1, 0, 1 ], [ 12*z + 88, 84*z + 155, 45*z + 80, 1 ],
  [ 555 , 3865, 2978 , 1 ], [ 162, 4825, 2653, 1 ]];

assert forall{ p : p in S |
  exists{pi : pi in [2] cat primes | p eq pi*Ok }};

// Checking that the primes other than (2) make no contribution

for ctr in [1..#primes] do
  p := primes[ctr]*Ok;
  mypt := localpts[ctr];
  Fp,resmap := ResidueClassField(p);
  Rp := PolynomialRing(Fp,4);
  KumEqn_p := &+[resmap(MC(KumEqn,mon))*Rp!mon : mon in mons];      
  Xp := Scheme(Proj(Rp),KumEqn_p);
  assert not IsSingular(Xp![resmap(x): x in mypt]);
  alpha := resmap(Evaluate(pushout,mypt));
  beta := resmap(Evaluate(g,mypt));
  assert alpha ne 0;
  assert beta ne 0;
  assert IsSquare(alpha);
  assert Valuation(a,p) eq 0 or IsSquare(beta);
end for;

// Computing the contribution from the prime (2)

p := Decomposition(Ok,2)[1,1];
_,resmap := ResidueClassField(p);
PP<X> := PolynomialRing(k);
subst := [ 1, 0, 1, 2^2 + (1 + z)*2^3 + 2^5*X];
poly := (1/2^7)*Evaluate(KumEqn,subst);
diffr := Eltseq(poly - (1 + z)*(X + 1));
assert forall{c : c in diffr | Valuation(c,p) ge 1};
pt := [Evaluate(c,0): c in subst];
assert Valuation(Evaluate(pushout,pt) - (2 + 5*z)^2,p) eq 4;
assert Valuation(Evaluate(g,pt) - 2^2*(-1 + 2*z),p) eq 5;
assert HilbertSymbol(a,-1 + 2*z,p) eq -1;

print "Section 4.4 : Examples from the LMFDB";

examples_LMFDB := [];
// load "examples_LMFDB.m"; // large file - available on request 
have_examples_LMFDB := false;

if have_examples_LMFDB then

  assert #examples_LMFDB eq 4208;

  ee := [e : e in examples_LMFDB | IsEven(e`analytic_order_III)];
  assert #ee eq 4161;

  table1 := ZeroMatrix(Integers(),5,5);  
  table2 := ZeroMatrix(Integers(),5,5);
  alt_tally := [0 : i in [1..4]];
  badlist := [];

  for e in ee do
    dimS2 := Valuation(#e`models + 1,2);
    assert #e`models eq 2^dimS2 - 1;
    tors := #[x : x in e`torsion | IsEven(x)];
    ctp := Matrix(GF(2),dimS2,dimS2,e`ctp);
    lowerbound := #e`generators;
    upperbound := dimS2 - tors - Rank(ctp);
    assert lowerbound le upperbound;
    if lowerbound eq upperbound then
      r := lowerbound;
      s := Rank(ctp);
      t := #e`deficient_places;
      assert r in [0..3];
      assert s in [1..4];
      assert t in [0..3];
      for i in [r+1,5] do
        for j in [s,5] do
          table1[i,j] +:= 1;
        end for;
      end for;
      for i in [t+1,5] do
        for j in [s,5] do
          table2[i,j] +:= 1;
        end for;
      end for;
      if forall{i : i in [1..dimS2] | ctp[i,i] eq 0} then
        alt_tally[s] +:= 1;
      end if;
    else
      Append(~badlist,e`label);
    end if;
  end for;

  assert table1 eq Matrix(5,5,[
    [ 1125, 1387, 38, 9, 2559 ],
    [ 1004, 406, 7, 2, 1419 ],
    [ 106, 3, 0, 0, 109 ],
    [ 1, 0, 0, 0, 1 ],
    [ 2236, 1796, 45, 11, 4088 ]
  ]);

  assert table2 eq Matrix(5,5,[
    [ 0, 1782, 0, 10, 1792 ],
    [ 2232, 0, 45, 0, 2277 ],
    [ 0, 14, 0, 1, 15 ],
    [ 4, 0, 0, 0, 4 ],
    [ 2236, 1796, 45, 11, 4088 ]
  ]);

  assert alt_tally eq [ 0, 486, 0, 3 ];
end if;

// The LMFDB labels of the genus 2 Jacobians whose
// Tate-Shafarevich group contains an element of order 4

badlist1 := [
"10800.c.691200.1", "12909.b.12909.1", "13108.a.26216.1",
"15680.b.250880.1", "16281.a.48843.1", "36356.b.72712.1",
"37375.b.37375.1", "38267.a.38267.1", "65563.d.65563.1",
"65563.d.65563.2", "72000.b.72000.1", "102016.b.102016.1",
"106015.b.742105.1", "108737.a.108737.1", "111989.a.111989.2",
"114240.a.114240.1", "114240.d.114240.1", "121077.a.121077.1",
"143039.a.143039.1", "149688.a.299376.1", "150729.a.150729.1",
"154541.a.154541.1", "171204.a.684816.1", "177660.a.355320.1",
"187200.a.748800.1", "190320.a.190320.1", "206320.a.206320.1",
"217488.a.217488.1", "220191.a.220191.1", "225306.a.675918.1",
"249939.a.249939.1", "270438.a.270438.1", "274688.a.274688.1",
"276083.a.276083.2", "293712.a.293712.1", "300429.a.300429.1",
"305408.b.305408.1", "323375.a.323375.1", "373030.a.746060.1",
"417152.a.417152.1", "434048.a.434048.1", "438837.b.438837.1",
"439280.a.439280.1", "483552.a.483552.1", "494451.a.494451.1",
"523925.a.523925.1", "530822.a.530822.1", "540800.a.540800.1",
"540800.b.540800.1", "549250.a.549250.1", "611103.b.611103.1",
"616496.a.616496.1", "616842.a.616842.1", "624978.a.624978.1",
"680646.a.680646.1", "681797.a.681797.1", "700368.a.700368.1",
"709566.a.709566.1", "711917.a.711917.1", "723520.b.723520.1",
"735488.d.735488.1", "738129.a.738129.1", "789616.a.789616.1",
"795818.a.795818.1", "858148.a.858148.1", "860433.a.860433.1",
"869042.a.869042.1", "876096.a.876096.1", "881669.a.881669.1",
"913071.a.913071.1", "918528.b.918528.1", "919360.a.919360.1",
"919360.b.919360.1" ];

if not assigned badlist then badlist := badlist1; end if;
assert badlist eq badlist1;
assert #badlist eq 73;

for ctr in [1..#badlist] do
  assert exists(e){e : e in examples |
    assigned e`label and e`label eq badlist[ctr]};
  assert e`notes in {"listA","listB","listC","listD"};
end for;

print "";

listA := [e : e in examples | assigned e`notes and e`notes eq "listA"];
assert #listA eq 17;

listB := [e : e in examples | assigned e`notes and e`notes eq "listB"];
assert #listB eq 30;

listC := [e : e in examples | assigned e`notes and e`notes eq "listC"];
assert #listC eq 15;

listD := [e : e in examples | assigned e`notes and e`notes eq "listD"];
assert #listD eq 11;

// The Jacobians in list A are each isogenous to a product
// of elliptic curves. The following table lists the Cremona
// references of the elliptic curves

listA_data := [
    <"10800.c.691200.1", { "120a5", "90b2" }>,
    <"15680.b.250880.1", { "14a5", "1120o2" }>,
    <"72000.b.72000.1", { "480h2", "150a2" }>,
    <"114240.a.114240.1", { "102b5", "1120l3" }>,
    <"114240.d.114240.1", { "1120o2", "102b5" }>,
    <"177660.a.355320.1", { "1974g2", "90b2" }>,
    <"187200.a.748800.1", { "480h2", "390f2" }>,
    <"190320.a.190320.1", { "2379b2", "80a1" }>,
    <"439280.a.439280.1", { "17a3", "25840e2" }>,
    <"483552.a.483552.1", { "48a1", "10074r2" }>,
    <"540800.a.540800.1", { "130b3", "4160r2" }>,
    <"540800.b.540800.1", { "130b3", "4160t2" }>,
    <"549250.a.549250.1", { "4225m2", "130b3" }>,
    <"723520.b.723520.1", { "1120o2", "646c2" }>,
    <"735488.d.735488.1", { "1664g2", "442d2" }>,
    <"919360.a.919360.1", { "2080f2", "442d2" }>,
    <"919360.b.919360.1", { "442d2", "2080e3" }>
];
assert #listA_data eq 17;

printf "Checking List A (%o curves)\n\n",#listA;

CR := CremonaReference;
for example in listA do
  assert exists(dd){dd : dd in listA_data | dd[1] eq example`label};
  print example`label,dd[2];
  C := HyperellipticCurve(example`f);
  J := Jacobian(C);
  _,EE,_ := TwoPowerIsogenies(J);
  assert exists{E : E in EE | { CR(E[i]) : i in [1..2] } eq dd[2]};
  assert example`rank eq &+[Rank(EllipticCurve(c)): c in dd[2]];
  assert example`rank in {0,1};
end for;

print "";

for example in listB cat listC cat listD do
  ex0 := example;
  dimS2 := Valuation(#example`models + 1,2);
  tors := #[x : x in example`torsion | IsEven(x)];
  assert Matrix(example`ctp) eq 0;
  assert #example`generators eq 0;
  assert dimS2 - tors eq 2;
  assert #example`deficient_places eq 0;
  assert example`analytic_order_III eq
    (example`label eq "108737.a.108737.1" select 64 else 16);
end for;

function IsTwoPowerIsogenous(C1,C2);
  CC := [Curve(J): J in TwoPowerIsogenies(Jacobian(C1))];
  return exists{C : C in CC | IsIsomorphic(C,C2)};
end function;

// The genus 2 curves in list B are each isogenous to a genus 2
// curve whose Jacobian has no elements of order 2 in III.
// The following table lists a label for the isogenous curve
// and the absolute value of its minimal discriminant.
// A label of the form "xxx-n" indicates the nth curve we
// found isogenous to the curve with LMFDB label "xxx", but
// beyond the current range of the LMFDB.

listB_data := [
  <"12909.b.12909.1",   "12909.b.12909.1-1",   68102859862198881329287767489773568>,
  <"13108.a.26216.1",   "13108.a.26216.1-1",   859045888>,
  <"37375.b.37375.1",   "37375.b.37375.1-1",   82112875>,
  <"16281.a.48843.1",   "16281.a.48843.1-1",   2884130307>,
  <"36356.b.72712.1",   "36356.b.72712.1-1",   1056271518208>,
  <"102016.b.102016.1", "102016.b.102016.1-2", 655707974204558409728>,
  <"150729.a.150729.1", "150729.a.150729.1-1", 993574951171875>,
  <"206320.a.206320.1", "206320.a.206320.1-1", 25185546875000000>,
  <"217488.a.217488.1", "217488.a.217488.1-1", 12482860342464>,
  <"249939.a.249939.1", "249939.a.249939.1-1", 155105323063164533935546875>,
  <"293712.a.293712.1", "293712.a.293712.1-1", 3244885257933029376>,
  <"149688.a.299376.1", "149688.a.299376.1-1", 11090084544>,
  <"323375.a.323375.1", "323375.a.323375.1-1", 559490781077921875>,
  <"417152.a.417152.1", "417152.a.417152.1-1", 13669236736>,
  <"434048.a.434048.1", "434048.a.434048.1-2", 517910562457811563577344>,
  <"494451.a.494451.1", "494451.a.494451.1-1", 4450059>,
  <"611103.b.611103.1", "611103.b.611103.1-1", 2329127540139057730949864226816>,
  <"616496.a.616496.1", "616496.a.616496.1-1", 872501594348155367601344>,
  <"616842.a.616842.1", "616842.a.616842.1-1", 23602689311184>,
  <"624978.a.624978.1", "624978.a.624978.1-1", 12665928095616410320896>,
  <"225306.a.675918.1", "225306.a.675918.1-1", 3344308651903942656>,
  <"680646.a.680646.1", "680646.a.680646.1-1", 2893785527088>,
  <"171204.a.684816.1", "171204.a.684816.1-1", 310211260710912>,
  <"700368.a.700368.1", "700368.a.700368.1-1", 77455097856>,
  <"709566.a.709566.1", "709566.a.709566.1-1", 12471332016>,
  <"373030.a.746060.1", "373030.a.746060.1-1", 660891566667395840>,
  <"789616.a.789616.1", "789616.a.789616.1-1", 771109375000000>,
  <"860433.a.860433.1", "860433.a.860433.1-1", 23231691>,
  <"869042.a.869042.1", "869042.a.869042.1-1", 6952336>,
  <"918528.b.918528.1", "918528.b.918528.1-1", 55793830330368>
];
assert #listB_data eq 30;

printf "Checking List B (%o curves)\n\n",#listB;

for example in listB do
  print example`label;
  assert example`torsion eq [2];
  assert exists(dd){dd : dd in listB_data | dd[1] eq example`label};
  assert exists(e){e : e in examples |
    assigned e`label and e`label eq dd[2]};
  assert dd eq <example`label,e`label,e`discriminant>;
  C1 := HyperellipticCurve(example`f); // curve in list B
  C2 := HyperellipticCurve(e`f);       // isogenous curve 
  assert IsTwoPowerIsogenous(C1,C2);  
  dimS2 := Valuation(#e`models+1,2);
  tors := #[x : x in e`torsion | IsEven(x)];
  assert dimS2 eq tors; // => rank = 0 
end for;

print "";

// The genus 2 curves in list C are each isogenous to a genus 2
// curve whose Jacobian has no elements of order 4 in III.
// The following table lists a label for the isogenous curve
// and the absolute value of its minimal discriminant.

listC_data := [
  <"38267.a.38267.1",   "38267.a.38267.1-1",   10807731072518427>,
  <"108737.a.108737.1", "108737.a.108737.1-1", 745827083>,
  <"111989.a.111989.2", "111989.a.111989.1",   111989>,
  <"121077.a.121077.1", "121077.a.121077.1-2", 4260504627893541996078957>,
  <"143039.a.143039.1", "143039.a.143039.1-1", 1398174630603888566063857664>,
  <"154541.a.154541.1", "154541.a.154541.1-1", 14677508837158203125>,
  <"220191.a.220191.1", "220191.a.220191.1-1", 5945157>,
  <"274688.a.274688.1", "274688.a.274688.1-1", 4500488192>,
  <"276083.a.276083.2", "276083.a.276083.1",   276083>,
  <"305408.b.305408.1", "305408.b.305408.1-1", 20495583936512>,
  <"523925.a.523925.1", "523925.a.523925.1-1", 449200196875>,
  <"530822.a.530822.1", "530822.a.530822.1-1", 2474149609686209548336>,
  <"738129.a.738129.1", "738129.a.738129.1-1", 5628674645995969323>,
  <"795818.a.795818.1", "795818.a.795818.1-1", 3383442509904>,
  <"858148.a.858148.1", "858148.a.858148.1-1", 1676070312500000> ];
assert #listC_data eq 15;

printf "Checking List C (%o curves)\n\n",#listC;

for example in listC do
  print example`label;
  assert example`torsion in {[2],[2,2],[4]};
  assert exists(dd){dd : dd in listC_data | dd[1] eq example`label};
  assert exists(e){e : e in examples |
    assigned e`label and e`label eq dd[2]};
  assert dd eq <example`label,e`label,e`discriminant>;
  C1 := HyperellipticCurve(example`f);  // curve in list C
  C2 := HyperellipticCurve(e`f);        // isogenous curve
  assert IsTwoPowerIsogenous(C1,C2);  
  dimS2 := Valuation(#e`models+1,2);
  tors := #[x : x in e`torsion | IsEven(x)];
  ctp := Matrix(GF(2),dimS2,dimS2,e`ctp);
  assert Rank(ctp) eq 2;
  assert dimS2 eq tors + Rank(ctp); // => rank = 0 
end for;

print "";

// For the curves in list D we combine visibility with computing
// the Cassels-Tate pairing over Q(sqrt(d)), where d is as recorded
// in the following table. We ignore the first curve since it is
// isogenous to the second.

listD_data := [
    <"65563.d.65563.1", 0>,
    <"65563.d.65563.2", -7>,
    <"106015.b.742105.1", -3>,
    <"270438.a.270438.1", -3>,
    <"300429.a.300429.1", -3>,
    <"438837.b.438837.1", -3>,
    <"681797.a.681797.1", -3>,
    <"711917.a.711917.1", -3>,
    <"876096.a.876096.1", -3>,
    <"881669.a.881669.1", 5>,
    <"913071.a.913071.1", -3>
];
assert #listD_data eq 11;

printf "Checking List D (%o curves)\n\n",#listD;

for example in listD do
  print example`label;
  f := example`f;
  tors := #[x : x in example`torsion | IsEven(x)];
  assert tors in [0,1,2];
  assert exists(d){dd[2] : dd in listD_data | dd[1] eq example`label};
  if d eq 0 then continue; end if;
  label1 := example`label cat " over Q(sqrt(d))";
  assert exists(e){e : e in examples |
    assigned e`label and e`label eq label1};
  assert e`f eq f;
  assert e`d eq d;
  C1 := HyperellipticCurve(d*f);
  J1 := Jacobian(C1);
  K1 := KummerSurface(J1);
  ptsJ1 := &join[Points(J1,K1![P[1],P[2],P[3],d*P[4]]): P in e`generators];
  ptsJ1 := ReducedBasis(ptsJ1);
  assert e`rank eq #ptsJ1;
  tors := #[x : x in e`torsion | IsEven(x)];
  dimS2 := Valuation(#e`models + 1,2);
  assert e`deficient_places eq [];
  assert dimS2 eq tors + #ptsJ1 + 2;
// Since the number of deficient places is even, and
// we only need to improve the rank bound for J(k) by 2,
// it suffices to show that the Cassels-Tate pairing on
// S^2(J/k) is non-zero. The field "ctp_hint" lists a
// pair of elements eps,eta with CTP(eps,eta) != 0
// together with a k-point on K_eta.
  assert assigned e`ctp_hint;
end for;

print "";

// Remark 4.12 : The previously unresolved cases

// The LMFDB labels of the genus 2 Jacobians whose ranks were
// previously only known conditionally.

// This list is taken from
// https://www.lmfdb.org/api/g2c_curves/?mw_rank_proved=0

unproved := [
"49471.a.49471.1", "57986.a.57986.1", "65563.d.65563.1",
"65563.d.65563.2", "82748.a.165496.1", "89776.a.179552.1",
"94297.a.660079.1", "106015.b.742105.1", "108003.a.756021.1",
"108737.a.108737.1", "111989.a.111989.2", "121077.a.121077.1",
"127715.a.127715.1", "131165.a.131165.1", "138877.d.138877.1",
"143039.a.143039.1", "154541.a.154541.1", "173144.a.692576.1",
"201746.a.201746.1", "220191.a.220191.1", "238948.a.477896.1",
"251229.b.753687.1", "270438.a.270438.1", "272538.a.545076.1",
"274688.a.274688.1", "276083.a.276083.1", "276083.a.276083.2",
"280859.a.280859.1", "300429.a.300429.1", "305408.b.305408.1",
"308683.a.308683.1", "312131.b.312131.1", "331917.a.331917.1",
"341893.a.341893.1", "359613.a.359613.1", "371664.a.371664.1",
"384110.a.384110.1", "407771.a.407771.1", "411077.a.411077.1",
"423483.b.423483.1", "425698.a.425698.1", "438837.b.438837.1",
"467207.a.467207.1", "475659.a.475659.1", "483755.a.483755.1",
"530822.a.530822.1", "566692.a.566692.1", "615371.a.615371.1",
"681797.a.681797.1", "696091.a.696091.1", "705651.b.705651.1",
"711917.a.711917.1", "714058.a.714058.1", "738129.a.738129.1",
"739723.a.739723.1", "769511.a.769511.1", "776185.a.776185.1",
"788819.a.788819.1", "795818.a.795818.1", "798795.a.798795.1",
"808981.a.808981.1", "851919.a.851919.1", "858148.a.858148.1",
"876096.a.876096.1", "880171.a.880171.1", "881669.a.881669.1",
"913071.a.913071.1", "958976.a.958976.1", "978429.a.978429.1" ];
assert #unproved eq 69;

assert #[e : e in listA | e`label in unproved] eq 0;
assert #[e : e in listB | e`label in unproved] eq 0;
assert #[e : e in listC | e`label in unproved] eq 13;
assert #[e : e in listD | e`label in unproved] eq 11;

assert {e`label : e in listC | e`label notin unproved}
  eq {"38267.a.38267.1","523925.a.523925.1"};
 
labelsC := [e`label : e in listC | e`label in unproved];
labelsD := [e`label : e in listD | e`label in unproved];
others := [ label : label in unproved | label notin (labelsC cat labelsD) ];
assert #others eq 45;
ee := [e : e in examples | assigned e`label and e`label in others];
assert #ee eq 45;
assert ee[1]`notes eq "Example 4.6";

for e in ee do
  assert e`deficient_places eq [];
  tors := #{x : x in e`torsion | IsEven(x)};
  assert tors in [0,1];
  assert e`rank eq (e`label eq "776185.a.776185.1" select 1 else 0);
  assert #e`generators eq e`rank;
  assert e`analytic_order_III eq 4;
  dimS2 := Valuation(#e`models + 1,2);
  assert #e`models eq 2^dimS2 - 1;
  assert dimS2 eq tors + e`rank + 2;
  assert Vector(GF(2),e`c) eq 0;
  ctp := Matrix(GF(2),dimS2,dimS2,e`ctp);
  assert Rank(ctp) eq 2;
end for;

