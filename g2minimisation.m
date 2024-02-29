
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

// This is a package file implementing the main algorithm
// of the paper (for minimisation) and the method of
// [FY, Remark 4.3] (for reduction). This code should
// work for models defined over the rationals, and to some
// extent for models defined over small quadratic fields.

star := func<A|Matrix(BaseRing(A),4,4,[
  [   0,    A[4,3], A[2,4], A[3,2] ],
  [ A[3,4],    0,   A[4,1], A[1,3] ],
  [ A[4,2], A[1,4],    0,   A[2,1] ],
  [ A[2,3], A[3,1], A[1,2],    0   ]])>;

// pf = true  : conventions as in [FL]
// pf = false : conventions as in [FY]

FixedQuadraticForm := func<R:pf := true|
  pf select R.1*R.6 - R.2*R.5 + R.3*R.4   // the pfaffian
       else R.1*R.6 + R.2*R.5 + R.3*R.4>; // all 1's on the antidiagonal
ASM := func<x:pf := true|Matrix(Universe(Eltseq(x)),4,4,[
  [      0,    x[1],    x[2],     x[4] ],
  [  -x[1],       0,    x[3],   e*x[5] ],
  [  -x[2],   -x[3],       0,     x[6] ],
  [  -x[4], -e*x[5],   -x[6],        0 ]])
    where e is pf select 1 else -1>;
wedge := func<M:pf := true|Matrix(BaseRing(M),6,6,
    [M[r[1],s[1]]*M[r[2],s[2]] - M[r[1],s[2]]*M[r[2],s[1]] : r,s in ii])
    where ii is pf select [[1,2],[1,3],[2,3],[1,4],[2,4],[3,4]]
                     else [[1,2],[1,3],[2,3],[1,4],[4,2],[3,4]]>;

MC := MonomialCoefficient;
apply := func<H,P|(1/Determinant(P))*H^wedge(P)>;
linearfactors := func<f|[g[1] : g in Factorization(f) | Degree(g[1]) eq 1]>;
redn := func<F,resmap:R := PolynomialRing(Codomain(resmap),Rank(Parent(F)))|
  &+[resmap(Coefficients(F)[i])*R!(Monomials(F)[i]) : i in [1..#Terms(F)]]>;

function IsModel(f,model,pf)
  P := Parent(f);
  f6 := Coefficient(f,6);
  la,H := Explode(model);
  R := Parent(H);
  G := FixedQuadraticForm(R:pf:=pf);
  M := la*P.1*(2*SymmetricMatrix(G)) - (2*SymmetricMatrix(H));
  return Determinant(M) eq -la^6*(1/f6)*f;
end function; 

// Determines whether the subspace W <= k^6 spanned by the rows of
// mat is isotropic for G

function IsIsotropic(mat)
  k := BaseRing(mat);
  Rp := PolynomialRing(k,6);
  G := FixedQuadraticForm(Rp);
  m := Nrows(mat);
  Sp := PolynomialRing(k,m);
  subst := [&+[mat[i,j]*Sp.i : i in [1..m]]: j in [1..6]];
  return Evaluate(G,subst) eq 0;
end function;

// Finds (if possible) a 3-dimensional subspace W <= k^6 that is
// isotropic for both G and H1

function Remark3pt2(H,resmap,pi)
  R := Parent(H);
  G := FixedQuadraticForm(R);
  H1 := (1/pi)*Evaluate(H,[R.1,R.2,R.3,R.4,R.5,0]);
  k := Codomain(resmap);
  RR<x1,x2,y1,y2> := PolynomialRing(k,4);
  SS<T> := PolynomialRing(RR);
  subst := [T,x1*y1,x1*y2,x2*y1,x2*y2,0];
  assert Evaluate(G,subst) eq 0;
  H1modp := redn(H1,resmap);
  F := GCD(Coefficients(Evaluate(H1modp,subst)));
  if F eq 0 then
    l := x1;
  else
    ll := linearfactors(F);
    if #ll eq 0 then return false,_; end if;
    l := ll[1];
  end if;
  c := [MC(l,RR.i): i in [1..4]];
  R3<x,y,z> := PolynomialRing(k,3);
  subst := [c[3],c[4]] eq [0,0]
    select [x,c[2]*y,c[2]*z,-c[1]*y,-c[1]*z,0]
    else   [x,c[4]*y,-c[3]*y,c[4]*z,-c[3]*z,0];	  
  assert Evaluate(G,subst) eq 0;
  assert Evaluate(H1modp,subst) eq 0;
  W := Matrix(k,3,6,[MC(s,R3.i): s in subst, i in [1..3]]);
  assert Rank(W) eq 3;  
  return true,W;
end function;

// Finds all codimension 1 subspaces of W that are isotropic for G,
// where W <= k^6 is the space spanned by the rows of mat.

function CodimensionOneSubspaces(mat)
  k := BaseRing(mat);
  G := FixedQuadraticForm(PolynomialRing(k,6));
  m := Nrows(mat);
  Rm := PolynomialRing(k,m);
  subst := [&+[mat[i,j]*Rm.i : i in [1..m]]: j in [1..6]];
  WW := [];
  for h in linearfactors(Evaluate(G,subst)) do
    mat1 := Matrix(m,1,[MC(h,Rm.j): j in [1..m]]);
    Append(~WW,KernelMatrix(mat1)*mat);
  end for;
  return WW;
end function;

// The rank and kernel of the quadratic form H (defined over
// a finite field). Some care is needed in characteristic 2.

function RankAndKernel(H)
  k := BaseRing(Parent(H));
  HH := Matrix(k,6,6,[Derivative(Derivative(H,i),j): i,j in [1..6]]);
  rank := Rank(HH);
  kernel := KernelMatrix(HH);
  if Characteristic(k) eq 2 and Nrows(kernel) gt 0 then
    m := Nrows(kernel);
    R := PolynomialRing(k,m);
    subst := [&+[kernel[i,j]*R.i : i in [1..m]]: j in [1..6]];
    H0 := Evaluate(H,subst);
    if H0 ne 0 then
      c := [Sqrt(MC(H0,R.j^2)): j in [1..m]];
      assert H0 eq (&+[c[i]*R.i : i in [1..m]])^2;
      rank +:= 1; 
      kernel := KernelMatrix(Matrix(k,m,1,c))*kernel;
    end if;
  end if;
  return rank,kernel;
end function;

// An integral change of coordinates suggested by the
// the subspace W <= k^6 spanned by the rows of mat

function ChangeOfCoordinates(resmap,mat)
  A := HorizontalJoin([star(ASM(mat[i])): i in [1..Nrows(mat)]]);
  kermat := KernelMatrix(A);
  OK := Domain(resmap);
  m := Nrows(kermat);
  n := Ncols(kermat);
  liftedmat := Matrix(OK,m,n,
    [kermat[i,j] @@ resmap : j in [1..n],i in [1..m]]);
  _,_,S := SmithForm(liftedmat);
  return Transpose(S)^(-1),4 - Nrows(kermat);
end function;

// Apply Operation 1, 2 or 3 to the quadratic form H using
// the uniformiser pi.

function Operation(m,H,pi)
  k := BaseRing(Parent(H));
  assert m in [1..3];
  dd := [i + m le 4 select 1 else pi : i in [1..4]];
  P := DiagonalMatrix(k,4,dd);
  H1 := apply(H,P);
  case m :
  when 1 :
    assert H1 eq (1/pi)*H^DiagonalMatrix(k,[1,1,1,pi,pi,pi]);
  when 2 :
    assert H1 eq H^DiagonalMatrix(k,[1/pi,1,1,1,1,pi]);
  when 3 :
    assert H1 eq (1/pi)*H^DiagonalMatrix(k,[1,1,pi,1,pi,pi]);
  end case;
  return H1,P;
end function;

function TryOperation(H,resmap,pi,mat)
  S,m := ChangeOfCoordinates(resmap,mat);
  if m in [0,4] then return []; end if;
  S := ChangeRing(S,BaseRing(Parent(H)));
  H1,P := Operation(m,apply(H,S),pi);
  if forall{c : c in Coefficients(H1) | IsIntegral(c)} then
    return [S*P];
  end if;
  return [];
end function;

function Algorithm2pt3(H,resmap,pi,mat)
  ans := TryOperation(H,resmap,pi,mat);
  if Nrows(mat) in [2,3] then
    T := Matrix(BaseRing(Parent(H)),6,6,
      [<1,6,1>,<2,5,-1>,<3,4,1>,<4,3,1>,<5,2,-1>,<6,1,1>]);
    ans1 := TryOperation(H^T,resmap,pi,mat*resmap(T));
    ans cat:= [Transpose(P)^(-1): P in ans1];
  end if;
  return ans;
end function;

function Algorithm2pt4(H,resmap,pi)
  H0 := H;
  K := BaseRing(Parent(H));
  P := IdentityMatrix(K,4);
  T := Matrix(K,6,6,
    [<1,6,1>,<2,5,-1>,<3,4,1>,<4,3,1>,<5,2,-1>,<6,1,1>]);
  k := Codomain(resmap);
  Rp := PolynomialRing(k,6);
  stepctr := 0;
  while true do 
    stepctr +:= 1;
    assert H eq apply(H0,P);
    assert forall{c : c in Coefficients(H) | IsIntegral(c)};
    
    // Step 1
    Hmodp := redn(H,resmap:R := Rp);
    rk,kerH := RankAndKernel(Hmodp); 
    assert rk in {0..6};
    assert Nrows(kerH) + rk eq 6;
    vprintf Minimisation,2 : "\nrank(Hbar) = ";
    vprintf Minimisation,1 : "%o",rk;
    if rk eq 0 then return true,P; end if;
    if stepctr ge 5 then return false,_; end if; 
    
    // Step 2
    if rk eq 1 then
      ff := linearfactors(Hmodp);
      assert #ff eq 1; 
      mat := Matrix(k,1,6,[MC(ff[1],Rp.j): j in [1..6]]);
      if IsIsotropic(mat) then
        mat := mat*ChangeRing(T,k);
	P1 := ChangeOfCoordinates(resmap,mat);
	P1 := ChangeRing(P1,K);
        H1 := apply(H,P1); 
        flag,mat := Remark3pt2(H1,resmap,pi);
        if flag then
	  vprintf Minimisation,2 : "\nStep 2";
          PP := Algorithm2pt3(H1,resmap,pi,mat); 
          assert #PP eq 1;
	  return true,P*P1*PP[1];
        end if;	
      end if;
    end if;

    // Step 3
    if rk eq 2 then
      Wlist := CodimensionOneSubspaces(kerH);
      Plist := &cat[Algorithm2pt3(H,resmap,pi,mat): mat in Wlist];
      if exists(P1){P1:P1 in Plist|redn(apply(H,P1),resmap:R:=Rp) eq 0} then
        vprintf Minimisation,2 : "\nStep 3";
        return true,P*P1;
      end if;
    end if;

    // Step 4
    Plist := [];
    if rk in [1,2] then
      for l in linearfactors(Hmodp) do
	mat := Matrix(k,1,6,[MC(l,Rp.j): j in [1..6]]);
        if IsIsotropic(mat) then
	  mat := mat*ChangeRing(T,k);
	  Plist cat:= TryOperation(H,resmap,pi,mat); 
        end if;
      end for;
      if #Plist ne 0 then vprintf Minimisation,2 : "\nStep 4"; end if;
    end if;

    // Step 5
    if rk in [2..5] and #Plist eq 0 then
      Wlist := [kerH];
      if not IsIsotropic(kerH) then
        Wlist := rk eq 5 select [] else CodimensionOneSubspaces(kerH);
      end if;
      Plist := &cat[Algorithm2pt3(H,resmap,pi,mat) : mat in Wlist];
      if #Plist ne 0 then vprintf Minimisation,2 : "\nStep 5"; end if;
    end if;

    // Steps 4 and 5
    if #Plist gt 0 then
      ranks := [RankAndKernel(redn(apply(H,P),resmap:R:=Rp)) : P in Plist];
      rkmin,j := Minimum(ranks);
      vprintf Minimisation,2 : "\nMinimum(%o) = %o",ranks,rkmin;
      P1 := Plist[j];
      H := apply(H,P1);
      P := P*P1;
      continue; // go to Step 1
    end if;

    // Step 6
    break;   
  end while;
  
  return false,_,_,stepctr;
end function;

function MinimiseAtp(model,p)
  la,H := Explode(model);
  H0 := H;
  K := BaseRing(Parent(H));
  tr := <K!1,IdentityMatrix(K,4)>;
  if K cmpeq Rationals() then
    k,resmap := ResidueClassField(p*Integers());    
    pi := p;
  else 
    k,resmap := ResidueClassField(p);
    flag,pi := IsPrincipal(p);
    error if not flag, "Prime is not principal";
  end if;
  while true do
    assert H eq tr[1]/Determinant(tr[2])*H0^wedge(tr[2]);
    assert forall{c : c in Coefficients(H) | IsIntegral(c)};
    flag,P := Algorithm2pt4(H,resmap,pi);
    if not flag then break; end if;
    H := apply(H,P);    
    la := (1/pi)*la;
    H := (1/pi)*H;
    tr := <(1/pi)*tr[1],tr[2]*P>;
    vprintf Minimisation,2 : "\n/**** Dividing out ****";
    vprintf Minimisation,1 : "/";
  end while;
  vprintf Minimisation,2 : "\n--> Minimal at p = %o\n",pi;
  return <la,H>,tr;
end function;

intrinsic MinimiseG2Model(f::RngUPolElt,model::Tup) -> Tup,Tup
{Minimises a model for a 2-covering of a genus 2 Jacobian}
  R := Parent(model[2]);
  K := BaseRing(R);
  D := DiagonalMatrix(K,[1,1,1,1,-1,1]);
  assert IsModel(f,model,false);
  model1 := <model[1],model[2]^D>;
  assert IsModel(f,model1,true);
  oldmodel := model;
  oldmodel1 := model1;
  assert forall{c : c in Coefficients(f) | IsIntegral(c)};
  f6 := Coefficient(f,6);
  if K cmpeq Rationals() then
    pp := PrimeDivisors(Integers()!(2*f6*model1[1]));
  else
    OK := RingOfIntegers(K);
    pp := [p[1] : p in Factorization(2*model1[1]*f6*OK)];  
  end if;
  tr := <K!1,IdentityMatrix(K,4)>;
  for p in pp do
    if K cmpeq Rationals() then
      vprintf Minimisation,1 : "p = %o : ",p;
    else
      vprintf Minimisation,1 : "Np = %o : ",Norm(p);    
    end if;
    model1,tr1 := MinimiseAtp(model1,p);
    tr := <tr[1]*tr1[1],tr[2]*tr1[2]>;
    vprint Minimisation,1 : "";
  end for;
  assert model1[2] eq tr[1]/Determinant(tr[2])*oldmodel1[2]^wedge(tr[2]);
  model := <model1[1],model1[2]^D>;
  assert model[1] eq tr[1]*oldmodel[1];
  assert model[2] eq tr[1]/Determinant(tr[2])*oldmodel[2]^wedge(tr[2]:pf := false);
  return model,tr;
end intrinsic;

// end of MINIMISATION code

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

// start of REDUCTION code

function ReductionCovariant(emb,phi,tt,tol)
  function MyEval(h,t)
    hh := EltseqPad(h);
    return &+[emb(hh[i])*t^(i-1): i in [1..6]];
  end function;
  phi1 := star(phi);
  M1 := [Matrix(4,4,[MyEval(phi1[r,s],t): r,s in [1..4]]): t in tt];
  M2 := [Matrix(4,4,[MyEval(phi[r,s],t): r,s in [1..4]]): t in tt];
  UU := [M1[i]*M2[j] : i,j in [1..6] | i lt j];	 
  if not exists{U : U in UU | Abs(Determinant(U)) lt 10^(-tol)} then
    kk := [1/Sqrt(Abs(Determinant(U))) : U in UU]; 
    redcov := 1 + &+[kk[i]*Transpose(Conjugate(UU[i]))*UU[i] : i in [1..#UU]];
    return true,redcov;
  end if;
  return false,_;
end function;

function RationalRedCov(phi,f,prec)
  repeat
    vprint Reduction,1 : "prec =",prec;
    R := RealField(prec);
    C := ComplexField(prec);
    tt := [r[1] : r in Roots(f,C)];
    emb := hom<Rationals()->C|>;
    flag,M := ReductionCovariant(emb,phi,tt,prec/5);
    prec *:= 2;
  until flag;
  M := Matrix(R,4,4,[Re(M[i,j]): i,j in [1..4]]);
  return M + Transpose(M);
end function;  

function QuadFldRedCov(phi,f,d,bb,prec)
  repeat
    vprint Reduction,1 : "prec =",prec;
    R := RealField(prec);
    C := ComplexField(prec);
    tt := [r[1] : r in Roots(f,C)];
    if d lt 0 then 
      aC := Sqrt(C!d);
      embs := [func<x|EltseqPad(x)[1] + EltseqPad(x)[2]*aC>];
    else
      aR := Sqrt(R!d);
      embs := [func<x|EltseqPad(x)[1] + e*EltseqPad(x)[2]*aR>: e in [1,-1]];
    end if;
    M := ZeroMatrix(C,8,8);
    for emb in embs do
      flag,U := ReductionCovariant(emb,phi,tt,prec/5);
      if not flag then break; end if;
      P := Matrix(C,8,4,[emb(bb[i,j]): j in [1..4],i in [1..8]]);
      M +:= Conjugate(P)*U*Transpose(P);
    end for;
    prec *:= 2;
  until flag;
  M := Matrix(R,8,8,[Re(M[i,j]): i,j in [1..8]]);
  return M + Transpose(M);    
end function;

intrinsic ReduceG2Model(f::RngUPolElt,model::Tup:prec := 500) -> Tup,Tup
{Reduces a model for a 2-covering of a genus 2 Jacobian defined over the rationals}
  L := quo<Parent(f)|f/Coefficient(f,6)>;
  assert IsModel(f,model,false); 
  la,H := Explode(model);
  R := Parent(H);
  G := FixedQuadraticForm(R:pf:=false);
  GG := 2*SymmetricMatrix(G);
  HH := 2*SymmetricMatrix(H);
  km := KernelMatrix(la*L.1*GG - HH);
  assert Nrows(km) eq 1;
  A := star(ASM(Eltseq(km):pf:=false));
  redcov := RationalRedCov(A,f,prec);
  vprint Reduction,1 : "Calling LLL";
  _,T := LLLGram(redcov);
  T[1] *:= Determinant(T);
  assert Determinant(T) eq 1;
  T := ChangeRing(Transpose(T),Rationals());
  return <la,H^wedge(T:pf:=false)>,<Rationals()!1,T>;  
end intrinsic;

intrinsic PseudoReduceG2Model(f::RngUPolElt,model::Tup:prec:=500) -> Tup,Tup
{(Almost) reduces a model for a 2-covering of a genus 2 Jacobian defined over a quadratic field}
  la,H := Explode(model);
  R := Parent(H);
  K<a> := BaseRing(R);
  P<x> := PolynomialRing(K);
  L := quo<P|f/Coefficient(f,6)>;
  G := FixedQuadraticForm(R:pf:=false);
  GG := 2*SymmetricMatrix(G);
  HH := 2*SymmetricMatrix(H);
  km := KernelMatrix(la*L.1*GG - HH);
  assert Nrows(km) eq 1;
  A := star(ASM(Eltseq(km):pf:=false));
  d := Integers()!(a^2);
  assert Abs(d) lt 20; // only tested on small quadratic fields 
  bb := Matrix(8,4,[[i eq j select b else 0 : j in [1..4]]
    : b in [1,a], i in [1..4]]);
  M := QuadFldRedCov(A,f,d,bb,prec);
  vprint Reduction,1 : "Calling LLL";
  _,T := LLLGram(M);
  E := ChangeRing(T,K)*bb;
  // It remains to pick 4 rows out of 8
  SS := SetToSequence(Subsets({1..8},4));
  sc := func<x|&+x>; //  + Random([-2..2])>;
  Sort(~SS,func<x,y|sc(x)-sc(y)>);
  dd := [];
  for S0 in SS do
    S := Sort(SetToSequence(S0));
    T := Matrix(K,4,4,[E[i] : i in S]);
    score := Abs(Norm(Determinant(T)));
    if score ne 0 then Append(~dd,<score,T>); end if;
    if #dd gt 10 then break; end if;
  end for;
  Sort(~dd,func<x,y|x[1]-y[1]>);
  T := Random([dd[i,2] : i in [1..Minimum(#dd,3)]]);
  T := ChangeRing(Transpose(T),K);
  det := Determinant(T); // might not be a unit (=> undoes minimisation)
  return <det*la,H^wedge(T:pf:=false)>,<det,T>;  
end intrinsic;

intrinsic MinRedOverQuadFld(f::RngUPolElt,model::Tup,units::SeqEnum,smallelts::SeqEnum) -> Tup,Tup
{Attempts to minimise and reduce a model for a 2-covering of a genus 2 Jacobian defined over a quadratic field}
  assert IsModel(f,model,false);
  ctr := 0;
  R := Parent(model[2]);
  K := BaseRing(R);
  tr := <K!1,IdentityMatrix(K,4)>;
  mons := MonomialsOfDegree(R,2);
  repeat // We alternately apply minimisation and reduction
    m1,tr1 := MinimiseG2Model(f,model);
    m2,tr2 := PseudoReduceG2Model(f,m1);
    trnew := <tr1[1]*tr2[1],tr1[2]*tr2[2]>;
    for jj in [1] cat smallelts do
      if exists(u){u : u in units | IsCoercible(Integers(),m2[1]/u/jj)} then
        m2 := <(1/u)*m2[1],(1/u)*m2[2]>;
	trnew[1] *:= (1/u);
        if Integers()!(m2[1]/jj) lt 0 then
          m2 := <-m2[1],-m2[2]>;
	  trnew[1] *:= -1;
        end if; 
      end if;
    end for;
    if #Sprint(m2) lt #Sprint(model) or Abs(Norm(m2[1])) lt Abs(Norm(model[1])) then
      model := m2;
      tr := <tr[1]*trnew[1],tr[2]*trnew[2]>;
      ctr := 0;
    else
      ctr +:= 1;
    end if;
  until ctr gt 3;
  return model,tr;
end intrinsic;
