Attach("g2minimisation.m");
Attach("genus2ctp.m");

Q := Rationals();
P<x> := PolynomialRing(Q);
function SameSquareClass(a,b,LL,iso)
    rational_component := [i : i in [1..NumberOfComponents(LL)] |
        Degree(LL[i]) eq 1][1];
    r := iso(a/b);
    scalar := Q!r[rational_component];
    return forall{i : i in [1..NumberOfComponents(LL)] |
        IsSquare(r[i]/scalar)};
end function;
for twist in [1,3] do
f0 := twist*(x^5 - x);
f := P!(x^6*Evaluate(f0,2 + 1/x));
C := HyperellipticCurve(f);
J := Jacobian(C);

S0,m0,c0 := TwoSelmerGroupTrue(J:checking := true);
S1,m1,c1 := TwoSelmerGroupTrue(J:checking := true,
    SelmerAl := "TwoSelmerGroupNew");
assert #S0 eq #S1 and c0 eq S0!0 and c1 eq S1!0;
L := Parent(m0(S0!0)[1]);
LL,iso := AbsoluteAlgebra(L);

for g in S0 do
    assert #[h : h in S1 | SameSquareClass(m0(g)[1],m1(h)[1],LL,iso)] eq 1;
end for;

if twist eq 1 then
S,models,c := TwoDescentGenus2(J:SelmerAl := "TwoSelmerGroupNew");
assert #S eq #S1 and c eq S!0;
R := PolynomialRing(Q,6);
G := R.1*R.6 + R.2*R.5 + R.3*R.4;
mons := MonomialsOfDegree(R,2);
for g in S do
    if g ne S!0 then
        la,coeffs := Explode(models(g));
        H := &+[coeffs[i]*mons[i] : i in [1..#mons]];
        pencil := la*x*Matrix(P,2*SymmetricMatrix(G))
            - Matrix(P,2*SymmetricMatrix(H));
        assert Determinant(pencil) eq -la^6/Coefficient(f,6)*f;
    end if;
end for;
end if;
end for;
print "PASS: both algorithms agree on both twists and all New models validate";
