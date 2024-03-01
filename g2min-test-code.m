
////////////////////////////////////////////////////////
//                                                    //
// A Magma file accompanying the article              //
//                                                    //
// MINIMISATION OF 2-COVERINGS OF GENUS 2 JACOBIANS   // 
// by TOM FISHER AND MENGZHEN LIU                     //
//                                                    //
// Version: September 2023                            //
//                                                    //
////////////////////////////////////////////////////////

// This file checks Example 1.3 and then runs the code in
// "g2minimisation.m" on the examples in "g2min-test-data.m".

Attach("g2minimisation.m");
SetVerbose("Minimisation",1);
SetVerbose("Reduction",0);
SetColumns(150);

MC := MonomialCoefficient;
MD := MonomialsOfDegree;
P<x> := PolynomialRing(Rationals());
R<z12,z13,z23,z14,z24,z34> := PolynomialRing(Rationals(),6);
mons := MD(R,2);

function IsModel(f,model)
  la,H := Explode(model);
  R := Parent(H);
  u0,u1,u2,u3,u4,u5 := Explode([R.i : i in [1..6]]);
  G := u0*u5 - u1*u4 + u2*u3; // the pfaffian
  P := Parent(f);
  M := la*P.1*(2*SymmetricMatrix(G)) - (2*SymmetricMatrix(H));
  f6 := Coefficient(f,6);
  return Determinant(M) eq la^6*(-1/f6)*f;
end function;

wedge := func<M|Matrix(BaseRing(M),6,6,
    [M[r[1],s[1]]*M[r[2],s[2]] - M[r[1],s[2]]*M[r[2],s[1]] : r,s in ii])
    where ii is [[1,2],[1,3],[2,3],[1,4],[2,4],[3,4]]>;
    
apply := func<model,tr|
  <tr[1]*model[1],tr[1]/Determinant(tr[2])*model[2]^wedge(tr[2])>>;

// Example 1.3

f := -28*x^6 + 84*x^5 - 323*x^4 + 506*x^3 - 471*x^2 + 232*x - 60;

model1 := <42336, 25128*z12^2 + 24480*z12*z13 + 14031*z12*z23 +
    15408*z12*z14 + 13959*z12*z24 + 25407*z12*z34 + 2232*z13^2 -
    16407*z13*z23 + 4464*z13*z14 - 22815*z13*z24 + 1161*z13*z34 +
    2329*z23^2 + 15282*z23*z14 + 7687*z23*z24 - 19547*z23*z34 -
    2304*z14^2 - 17838*z14*z24 - 22590*z14*z34 - 134*z24^2 +
    41978*z24*z34 - 99584*z34^2>;

model2 := <14, z12*z23 + 2*z12*z14 - z12*z24 + 8*z12*z34 - 7*z13^2 -
    13*z13*z23 - 12*z13*z14 - 15*z13*z24 - 20*z13*z34 - 5*z23^2 -
    2*z23*z14 - 25*z23*z24 - 59*z23*z34 - 4*z14^2 - 14*z14*z24 -
    18*z14*z34 + 17*z24^2 - 37*z24*z34 - 11*z34^2>;

assert IsModel(f,model1);
assert IsModel(f,model2);

c := 1/3024;
PP := Matrix(Rationals(),4,4,[
    2, -19, 2, 5,
    4, 4, -31, 38,
    2, 2, 37, 40,
    -7, -7, -14, 7 ]);

assert model2 eq apply(model1,<c,PP>);

/////////////////////////////////////////////////////////////

// g2minimisation.m uses the sign conventions in [FY] rather
// than [FL]. We therefore need the following variants of
// "IsModel" and "wedge".

function IsModel(f,model)
  la,H := Explode(model);
  R := Parent(H);
  u0,u1,u2,u3,u4,u5 := Explode([R.i : i in [1..6]]);
  G := u0*u5 + u1*u4 + u2*u3; // all 1's on the antidiagonal
  P := Parent(f);
  M := la*P.1*(2*SymmetricMatrix(G)) - (2*SymmetricMatrix(H));
  f6 := Coefficient(f,6);
  return Determinant(M) eq la^6*(-1/f6)*f;
end function;

wedge := func<M|Matrix(BaseRing(M),6,6,
    [M[r[1],s[1]]*M[r[2],s[2]] - M[r[1],s[2]]*M[r[2],s[1]] : r,s in ii])
    where ii is [[1,2],[1,3],[2,3],[1,4],[4,2],[3,4]]>;
    
apply := func<model,tr|
  <tr[1]*model[1],tr[1]/Determinant(tr[2])*model[2]^wedge(tr[2])>>;

// Loading in the test examples

load "g2min-test-data.m";
assert #examples_Q eq 200;
assert #examples_nf eq 5;

// Checking the test examples

print "\nExamples over Q\n";

for ctr in [1..#examples_Q] do
  printf "%o/%o\n",ctr,#examples_Q;
  f,la,la_min,coeffs := Explode(examples_Q[ctr]);
  printf "C : y^2 = %o over Q\n",f;
  print "We minimise";
  print <la,coeffs>;
  model := <la,&+[coeffs[i]*mons[i] : i in [1..#mons]]>;
  assert IsModel(f,model);
  model1,tr1 := ReduceG2Model(f,model);
  assert model1 eq apply(model,tr1);
  model2,tr2 := MinimiseG2Model(f,model1);
  assert model2 eq apply(model1,tr2);
  model3,tr3 := ReduceG2Model(f,model2);
  assert model3 eq apply(model2,tr3);
  tr := <tr1[i]*tr2[i]*tr3[i] : i in [1,2]>;
  tr[2] /:= RationalGCD(Eltseq(tr[2]));
  assert model3 eq apply(model,tr);
  assert IsModel(f,model3);
  print "Applying the transformation",tr;
  model := <model3[1],[MC(model3[2],mon): mon in mons]>;
  print "gives";
  print model;
  assert model[1] eq la_min;
  print "";
end for;

print "\nExamples over small quadratic fields\n";

for ctr in [1..#examples_nf] do
  printf "%o/%o\n",ctr,#examples_nf;
  d,f,la,la_min,coeffs := Explode(examples_nf[ctr]);
  K<a> := QuadraticField(d);
  PK := PolynomialRing(K);
  printf "C : y^2 = %o over Q(sqrt(%o))\n",f,d;
  OK := RingOfIntegers(K);
  R := PolynomialRing(K,6);
  mons := MD(R,2);
  la := Evaluate(P!la,a);
  la_min := Evaluate(P!la_min,a);
  coeffs := [Evaluate(P!c,a): c in coeffs];
  print "We minimise";
  print <la,coeffs>;
  model := <la,&+[coeffs[i]*mons[i] : i in [1..#mons]]>;
  assert IsModel(PK!f,model);
  SetVerbose("Minimisation",1);
  model1,tr1 := MinimiseG2Model(PK!f,model);
  assert model1 eq apply(model,tr1);
  assert IsModel(PK!f,model1);
  print "to get";
  print <model1[1],[MC(model1[2],mon): mon in mons]>;
  assert ideal<OK|model1[1]> eq ideal<OK|la_min>;
  print "Minimising and reducing gives";
  U,Umap := UnitGroup(OK);
  if d gt 0 then 
    units := [Umap(U![a,b]): a in [0..1],b in [-500..500]];
  else
    units := [Umap(u): u in U];
  end if;
  smallelts := [a+n : n in [-3..3]];
  SetVerbose("Minimisation",0);
  model2,tr2 := MinRedOverQuadFld(PK!f,model,units,smallelts);
  assert model2 eq apply(model,tr2);
  assert IsModel(PK!f,model2);
  print <model2[1],[MC(model2[2],mon): mon in mons]>;  
  assert ideal<OK|model2[1]> eq ideal<OK|la_min>;
  print "";
end for;
