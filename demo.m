
Attach("g2minimisation.m");
Attach("genus2ctp.m");

SetClassGroupBounds("GRH");
SetDebugOnError(true);

SetVerbose("TwoDescent",0);
SetVerbose("CasselsTatePairing",0);
SetVerbose("Minimisation",0);
SetVerbose("PointSearch",0);

QQ := Rationals();
P<x> := PolynomialRing(QQ);

////////////////////////////////
// Example 4.8 from the paper //
////////////////////////////////

f := 3*x^6 + 10*x^5 - 16*x^4 + 18*x^3 + 23*x^2 - 54*x - 17;
C := HyperellipticCurve(f);
J := Jacobian(C);
assert #TorsionSubgroup(J) eq 1;

printf "J = Jac( y^2 = %o )\n",f;

print "--------------------------";
print "Carrying out the 2-descent";
print "--------------------------";

time S2,S2map := TwoDescentGenus2(J);
print "After a 2-descent we have";
dimS2 := #Generators(S2);
print "rank J(Q) <=",dimS2;
assert dimS2 eq 5;

print "----------------------------------";
print "Computing the Cassels-Tate pairing";
print "----------------------------------";

time ctp := CasselsTatePairingGenus2(J,S2map);
print "The Cassels-Tate pairing on S^2(J/Q) is given by";
print ctp;
print "After computing the Cassels-Tate pairing we have";
print "rank J(Q) <=",dimS2 - Rank(ctp);
assert Rank(ctp) eq 3;

print "----------------------------------------------------";
print "Checking agreement with a previously computed answer";
print "----------------------------------------------------";

models0 := [
<6,[0,0,0,0,6,0,0,6,0,0,0,43,-10,-98,-47,1,10,-2,13,152,52]>,
<6,[-3,-6,0,6,0,-18,-3,0,6,0,-9,-2,8,-4,-2,4,-8,2,0,0,-9]>,
<6,[0,0,0,0,-3,-3,-3,6,6,-9,-15,4,2,2,4,-5,8,10,-14,4,-5]>,
<6,[2,4,-4,4,-10,-2,5,-10,1,-7,-8,5,-1,7,-4,2,-1,-8,2,2,2]>,
<6,[0,3,0,-3,0,-3,1,1,6,2,-5,-5,-9,-2,-1,-12,18,-9,-5,10,-2]>,
<6,[0,0,3,-3,-6,-6,1,3,-5,-4,-4,0,0,3,-12,10,13,22,10,32,-5]>,
<6,[0,0,-3,3,-6,-3,1,-5,3,-4,1,10,-3,13,2,3,-3,-15,10,19,-17]>,
<6,[1,-3,5,5,6,-3,6,-3,-9,-9,6,7,2,-3,3,1,9,-3,9,3,0]>,
<6,[-1,0,-2,-3,-1,-3,0,-4,-7,-1,-13,-1,-6,-10,-12,0,0,-6,-13,-18,-21]>,
<6,[3,0,0,-6,-6,-12,-4,-2,6,2,-6,2,0,-4,-6,0,0,6,2,0,15]>,
<6,[-3,2,2,-4,-5,-15,-3,2,-4,5,3,3,0,5,-3,-3,2,0,-1,-3,-18]>,
<6,[-1,-2,-1,1,-2,0,-5,-3,-5,-6,-12,3,-4,-7,-15,-1,1,-15,-9,-12,-3]>,
<6,[-1,1,-3,-3,-2,1,0,-5,-5,-3,-7,-1,-8,-19,-2,-1,-7,-2,-17,-15,-8]>,
<6,[-1,0,2,8,-1,4,0,0,12,0,0,-4,-14,4,-4,-7,13,2,5,11,-7]>,
<6,[-1,0,-1,3,-5,2,-4,-6,4,-16,-4,-3,4,2,0,3,8,0,-11,0,-4]>,
<6,[1,2,2,2,2,-2,-2,-4,-4,-10,10,1,2,-10,4,-8,2,4,-11,16,7]>,
<6,[-1,1,-1,1,-2,2,-1,5,-2,1,-1,17,-13,-7,-5,2,7,-1,-4,-34,-10]>,
<6,[-1,4,-2,2,-4,-4,1,-1,0,-10,-12,-3,4,5,6,0,-8,8,11,16,4]>,
<6,[0,-1,0,-4,4,4,1,-4,-4,-4,-4,-1,-10,-12,-2,-11,-16,-10,-4,-12,12]>,
<6,[1,-7,1,-3,0,5,1,-5,0,0,-1,4,-15,6,-2,6,-6,3,-3,0,-5]>,
<6,[-1,0,2,-2,-8,0,2,4,-6,-6,0,0,-4,-14,-8,-1,10,0,7,20,-1]>,
<6,[1,-2,0,-1,-2,2,-5,0,-2,-10,-8,0,-2,-12,-4,4,-9,-2,-8,-4,5]>,
<6,[-1,1,-1,1,-5,5,2,3,-1,-17,0,-4,2,0,-9,-1,2,7,11,9,7]>,
<6,[-5,-2,-6,-4,-2,0,1,3,4,-1,3,-3,-9,0,-9,-2,7,-15,4,3,0]>,
<6,[3,6,0,-3,-9,-9,5,-2,2,0,-4,-4,-1,-3,-7,-1,3,4,0,15,2]>,
<6,[-1,2,4,2,10,-2,-1,-1,1,-7,14,5,-1,-2,1,-1,-7,-7,-4,19,-7]>,
<6,[-1,3,1,5,6,-9,3,-3,-6,0,6,-4,-1,0,9,1,-10,10,-3,18,-3]>,
<6,[6,5,3,-1,-2,-10,-3,3,2,1,0,-2,-1,-1,4,0,1,-12,-3,2,13]>,
<6,[0,6,0,-3,9,-6,-7,0,8,-4,2,3,0,6,-6,2,4,-8,-1,10,-4]>,
<6,[0,-1,0,2,8,-3,2,3,-3,-9,5,-1,2,2,-7,-3,12,-15,12,-39,-1]>,
<6,[1,2,-3,1,9,-4,-5,-6,-8,-6,8,0,0,3,0,1,-3,4,-9,12,1]>
];

ctp0 := Matrix(GF(2),dimS2,dimS2,[
[ 1, 0, 0, 0, 1 ],
[ 0, 0, 1, 1, 0 ],
[ 0, 1, 0, 0, 1 ],
[ 0, 1, 0, 0, 1 ],
[ 1, 0, 1, 1, 1 ]]);

S2elts := [ x : x in S2 | x ne S2!0 ];
S2map0 := map<S2->models0|x :-> models0[Position(S2elts,x)]>;
sel := TwoSelmerElementsGenus2(J,S2map);
sel0 := TwoSelmerElementsGenus2(J,S2map0);
flag,iota := IsSameSubgroup(J,sel,sel0);
assert flag;
assert forall{g : g in S2 | g eq S2!0 or
  IsEquivalent(J,S2map(g),S2map0(iota(g)))};
B := Matrix(GF(2),dimS2,dimS2,[Eltseq(iota(S2.i)): i in [1..dimS2]]);
assert ctp eq B*ctp0*Transpose(B);

print "Answers agree";
print "";
print "=======================================================";
print "";

/*

load "lmfdb_g2c_curves_xxx.m";
curves := make_data();
CC := [SimplifiedModel(x`curve) : x in curves];
ff := [Evaluate(-Equation(C),[x,0,1]): C in CC];
rr := [x`analytic_rank : x in curves];

for ctr in [1..#ff] do
  f := ff[ctr];
  assert Degree(f) in [5,6];
  if Degree(f) eq 5 then
    assert exists(j){j : j in [0..5] | Evaluate(f,j) ne 0};
    f := P!(x^6*Evaluate(f,1/x+j));
    assert Degree(f) eq 6;
  end if;
  C := HyperellipticCurve(f);
  J := Jacobian(C);
  tors := TorsionSubgroup(J);
  dimtors := #[x : x in InvariantFactors(tors) | IsEven(x)];
  printf "J = Jac( y^2 = %o )\n",f;
  time S2,S2map := TwoDescentGenus2(J);
  dimS2 := #Generators(S2);
  print "After a 2-descent we have";
  print "rank J(Q) <=",dimS2 - dimtors;
  time ctp := CasselsTatePairingGenus2(J,S2map);
  print "The Cassels-Tate pairing on S^2(J/Q) is given by";
  print ctp;
  print "After computing the Cassels-Tate pairing we have";
  print "rank J(Q) <=",dimS2 - dimtors - Rank(ctp);
  assert rr[ctr] le dimS2 - dimtors - Rank(ctp);
end for;

*/

load "~/public_html/papers/g2ctp_examples.m";
assert #examples eq 332 + 48;

print "";
print "Some examples over Q";

// nn := [1..332];
nn := Sort([Random([1..332]): i in [1..3]]);

for ctr in nn do
  printf "\nExample %o/%o\n",ctr,#examples;
  example := examples[ctr];
  f := example`f;
  C := HyperellipticCurve(f);
  J := Jacobian(C);
  printf "J = Jac( y^2 = %o )\n",f;
  models := example`models;
  dimS2 := Valuation(#models + 1,2);
  assert #models eq 2^dimS2 - 1;
  S2 := AbelianGroup([2 : i in [1..dimS2]]);
  S2elts := [ x : x in S2 | x ne S2!0 ];
  S2map := map<S2->models|x :-> models[Position(S2elts,x)]>;
  print "Carrying out the 2-descent";
  time S2_check,S2map_check := TwoDescentGenus2(J);
  sel := TwoSelmerElementsGenus2(J,S2map);
  sel_check := TwoSelmerElementsGenus2(J,S2map_check);
  flag,iota := IsSameSubgroup(J,sel,sel_check);
  assert flag;
  assert forall{g : g in S2 | g eq S2!0 or
    IsEquivalent(J,S2map(g),S2map_check(iota(g)))};
  print "Computing the Cassels-Tate pairing";
  time ctp,c := CasselsTatePairingGenus2(J,S2map); 
  print ctp;
  assert ctp eq Matrix(GF(2),dimS2,dimS2,example`ctp);
  assert c eq S2!example`c;
end for;

print "";
print "Some examples over small quadratic fields";

// nn := [332+1..332+48];
nn := Sort([332 + Random([1..48]): i in [1..3]]);

for ctr in nn do
  printf "\nExample %o/%o\n",ctr,#examples;
  example := examples[ctr];
  f := example`f;
  C := HyperellipticCurve(f);
  J := Jacobian(C);
  printf "J = Jac( y^2 = %o )\n",f;
  printf "We work over k = Q(t) where t = sqrt(%o)\n",example`d;
  k<t> := QuadraticField(example`d);
  tok := func<m|<Evaluate(P!m[1],t),[Evaluate(w,t): w in m[2]]>>;
  models := [tok(m): m in example`models];
  Jk := BaseChange(J,k);
  dimS2 := Valuation(#models + 1,2);
  assert #models eq 2^dimS2 - 1;
  S2 := AbelianGroup([2 : i in [1..dimS2]]);
  S2elts := [ x : x in S2 | x ne S2!0 ];
  S2map := map<S2->models|x :-> models[Position(S2elts,x)]>;
  print "Carrying out the 2-descent";
  time S2_check,sel_check,c := TwoSelmerGroupTrue(Jk:checking := true);
  print "Checking agreement with a previously computed answer";
  sel := TwoSelmerElementsGenus2(Jk,S2map);
  flag,iota := IsSameSubgroup(Jk,sel,sel_check);
  assert flag;
  assert iota(S2!example`c) eq c;
  gg := [Random(S2elts): i in [1..3]];
  time assert forall{g : g in gg | g eq S2!0 or
    IsEqualInSelmer(Jk,sel(g),sel_check(iota(g)))};
  print "Computing the Cassels-Tate pairing";
  eps,eta,pt_eta := Explode(example`ctp_hint);
  pt_eta := [Evaluate(P!w,t): w in pt_eta];
  time ctp := CasselsTatePairingGenus2(Jk,S2map:hint := <S2!eps,S2!eta,pt_eta>);
  print "ctp =",ctp;
  assert ctp eq 1;
  assert example`deficient_places eq [];
  dimtors := #[x : x in example`torsion | IsEven(x)];
  rkbd := dimS2 - dimtors - 2;
  assert example`rank eq rkbd;
end for;

/*

Magma V2.27-8     Thu Feb 29 2024 on chromium [Seed = 985641882]
Type ? for help.  Type <Ctrl>-D to quit.
> load "demo.m";
Loading "demo.m"
J = Jac( y^2 = 3*x^6 + 10*x^5 - 16*x^4 + 18*x^3 + 23*x^2 - 54*x - 17 )
--------------------------
Carrying out the 2-descent
--------------------------
Time: 10.510
After a 2-descent we have
rank J(Q) <= 5
----------------------------------
Computing the Cassels-Tate pairing
----------------------------------
Time: 8.770
The Cassels-Tate pairing on S^2(J/Q) is given by
[1 0 1 1 1]
[0 0 1 1 1]
[1 1 1 1 1]
[1 1 1 1 1]
[1 1 1 1 1]
After computing the Cassels-Tate pairing we have
rank J(Q) <= 2
----------------------------------------------------
Checking agreement with a previously computed answer
----------------------------------------------------
Answers agree

=======================================================

Loading "/homes/taf1000/public_html/papers/g2ctp_examples.m"

Some examples over Q

Example 213/380
J = Jac( y^2 = -x^6 - 3*x^5 + 2*x^4 + 3*x^3 - 3*x^2 - 3*x - 2 )
Carrying out the 2-descent
Time: 0.390
Computing the Cassels-Tate pairing
Time: 0.770
[0 0]
[0 0]

Example 267/380
J = Jac( y^2 = -3*x^6 + 3*x^5 - x^4 + 2*x^3 + x^2 + 2*x + 3 )
Carrying out the 2-descent
Time: 0.400
Computing the Cassels-Tate pairing
Time: 0.850
[0 0]
[0 0]

Example 275/380
J = Jac( y^2 = -3*x^6 + 2*x^5 - x^4 + 3*x^3 + 2*x^2 + 3*x - 3 )
Carrying out the 2-descent
Time: 0.830
Computing the Cassels-Tate pairing
Time: 1.970
[0 0 0]
[0 0 1]
[0 1 0]

Some examples over small quadratic fields

Example 353/380
J = Jac( y^2 = -3*x^6 + 3*x^3 - 2*x^2 + 3*x + 2 )
We work over k = Q(t) where t = sqrt(-3)
Carrying out the 2-descent
Time: 1.840
Checking agreement with a previously computed answer
Time: 1.230
Computing the Cassels-Tate pairing
Time: 3.750
ctp = 1

Example 360/380
J = Jac( y^2 = -3*x^6 + 3*x^5 + x^4 - 3*x^3 - 3*x^2 - 2*x + 2 )
We work over k = Q(t) where t = sqrt(-3)
Carrying out the 2-descent
Time: 2.080
Checking agreement with a previously computed answer
Time: 1.260
Computing the Cassels-Tate pairing
Time: 5.330
ctp = 1

Example 370/380
J = Jac( y^2 = 2*x^6 + 3*x^5 - x^4 + 2*x^3 + x^2 + x - 3 )
We work over k = Q(t) where t = sqrt(-1)
Carrying out the 2-descent
Time: 3.170
Checking agreement with a previously computed answer
Time: 1.480
Computing the Cassels-Tate pairing
Time: 6.170
ctp = 1

*/
