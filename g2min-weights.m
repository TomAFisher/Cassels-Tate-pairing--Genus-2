
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

// We check some of the claims about "weights" in
// Sections 4 and 5 of the article.

// Definition 4.1

ii := [[1,2],[1,3],[2,3],[1,4],[2,4],[3,4]];
function Dominates(w,ww)
  nn := func<w,i,j,k,l|
    Maximum(1 + w[1] + w[2] + w[3] + w[4]
              - w[i] - w[j] - w[k] - w[l],0)>;
  return forall{[i,j] : i,j in ii |
      nn(w,i[1],i[2],j[1],j[2]) ge nn(ww,i[1],i[2],j[1],j[2])};
end function;

// Lemma 4.2 asserts that every weight w = (0, a, b, c) with
// 0 <= a <= b <= c dominates one of the following 12 weights

ww := [
    [ 0, 0, 0, 0 ],
    [ 0, 0, 0, 1 ],
    [ 0, 0, 1, 1 ],
    [ 0, 1, 1, 2 ],
    [ 0, 0, 1, 2 ],
    [ 0, 1, 1, 3 ],
    [ 0, 1, 2, 3 ],
    [ 0, 1, 2, 4 ],
    [ 0, 1, 1, 1 ],
    [ 0, 1, 2, 2 ],
    [ 0, 2, 2, 3 ],
    [ 0, 2, 3, 4 ]
];

// We check that this list of weights is minimal, i.e. no weight
// dominates any other weight.

assert forall{[w0,w1] : w0,w1 in ww | (w0 eq w1) or (not Dominates(w0,w1)) };

// We check that there are no weights with small entries that
// falsify Lemma 4.2.

max := 10;
for w0 in [[0,a,a+b,a+b+c] : a,b,c in [0..max]] do
  assert exists{w1 : w1 in ww | Dominates(w0,w1)};
end for;

printf "\nProof of Lemma 4.2\n\n";

K<a,b,c> := PolynomialRing(Rationals(),3);
w := [0,a,b,c];
XX := Matrix(6,6,[1 + w[1] + w[2] + w[3] + w[4]
  - w[i[1]] - w[i[2]] - w[j[1]] - w[j[2]] : i,j in ii]);
ww := [[w[2],w[3],w[4]]: w in ww];

assert XX eq Matrix(6,6,[
  [ 1+b+c-a, 1+c,     1+c-a,   1+b,     1+b-a,   1       ],
  [ 1+c,     1+a+c-b, 1+c-b,   1+a,     1,       1+a-b   ],
  [ 1+c-a,   1+c-b,   1+c-a-b, 1,       1-a ,    1-b     ],
  [ 1+b,     1+a,     1,       1+a+b-c, 1+b-c,   1+a-c   ],
  [ 1+b-a,   1,       1-a,     1+b-c,   1+b-a-c, 1-c     ], 
  [ 1,       1+a-b ,  1-b,     1+a-c,   1-c,     1+a-b-c ]]);

for i1,i2,i3 in ["eq","lt"] do // the 8 cases
  print [i1,i2,i3];
  nn0 := []; // a list of things we know are >= 0
  nn0 cat:= (i1 eq "lt" select [a - 1] else [a, -a]);
  nn0 cat:= (i2 eq "lt" select [b - a - 1] else [b - a, a - b]);
  nn0 cat:= (i3 eq "lt" select [c - b - 1] else [c - b, b - c]);
  extra := [[]];
  if [i1,i3] eq ["lt","lt"] then
    extra := [[c - a - b - 1],[a + b - c, c - a - b],[a + b - c - 1]];
  end if;
  for nn1 in extra do
    nn := nn0 cat nn1;
    ww1 := [w : w in ww | forall{n : n in nn | Evaluate(n,w) ge 0}];
    assert #ww1 eq 1;
    ans := ww1[1];
    printf "  %o ",[0] cat ans;
    for r,s in [1..6] do
      elt := XX[r,s];
      elt0 := Evaluate(elt,ans);
      if elt0 gt 0 then
        // looking for an identity to prove that elt >= elt0
        assert exists{uu : uu in CartesianProduct(<[0..2] : n in [1..#nn]>) |
          elt eq &+[uu[i]*nn[i] : i in [1..#nn]] + elt0};
      end if;
      printf ".";
    end for;
    print "";
  end for;
end for;

printf "\nThe table in Section 5\n\n";

for i in [1..8] do
  w := ww[i];
  printf "Case %o: %o\n",i,[0] cat w;
  X := Evaluate(XX,w);
  print Matrix(6,6,[Maximum(X[r,s],0): r,s in [1..6]]);
  print "";
end for;

/*

> load "g2min-weights.m";    
Loading "g2min-weights.m"

Proof of Lemma 4.2

[ eq, eq, eq ]
  [ 0, 0, 0, 0 ] ....................................
[ eq, eq, lt ]
  [ 0, 0, 0, 1 ] ....................................
[ eq, lt, eq ]
  [ 0, 0, 1, 1 ] ....................................
[ eq, lt, lt ]
  [ 0, 0, 1, 2 ] ....................................
[ lt, eq, eq ]
  [ 0, 1, 1, 1 ] ....................................
[ lt, eq, lt ]
  [ 0, 1, 1, 3 ] ....................................
  [ 0, 1, 1, 2 ] ....................................
  [ 0, 2, 2, 3 ] ....................................
[ lt, lt, eq ]
  [ 0, 1, 2, 2 ] ....................................
[ lt, lt, lt ]
  [ 0, 1, 2, 4 ] ....................................
  [ 0, 1, 2, 3 ] ....................................
  [ 0, 2, 3, 4 ] ....................................

The table in Section 5

Case 1: [ 0, 0, 0, 0 ]
[1 1 1 1 1 1]
[1 1 1 1 1 1]
[1 1 1 1 1 1]
[1 1 1 1 1 1]
[1 1 1 1 1 1]
[1 1 1 1 1 1]

Case 2: [ 0, 0, 0, 1 ]
[2 2 2 1 1 1]
[2 2 2 1 1 1]
[2 2 2 1 1 1]
[1 1 1 0 0 0]
[1 1 1 0 0 0]
[1 1 1 0 0 0]

Case 3: [ 0, 0, 1, 1 ]
[3 2 2 2 2 1]
[2 1 1 1 1 0]
[2 1 1 1 1 0]
[2 1 1 1 1 0]
[2 1 1 1 1 0]
[1 0 0 0 0 0]

Case 4: [ 0, 1, 1, 2 ]
[3 3 2 2 1 1]
[3 3 2 2 1 1]
[2 2 1 1 0 0]
[2 2 1 1 0 0]
[1 1 0 0 0 0]
[1 1 0 0 0 0]

Case 5: [ 0, 0, 1, 2 ]
[4 3 3 2 2 1]
[3 2 2 1 1 0]
[3 2 2 1 1 0]
[2 1 1 0 0 0]
[2 1 1 0 0 0]
[1 0 0 0 0 0]

Case 6: [ 0, 1, 1, 3 ]
[4 4 3 2 1 1]
[4 4 3 2 1 1]
[3 3 2 1 0 0]
[2 2 1 0 0 0]
[1 1 0 0 0 0]
[1 1 0 0 0 0]

Case 7: [ 0, 1, 2, 3 ]
[5 4 3 3 2 1]
[4 3 2 2 1 0]
[3 2 1 1 0 0]
[3 2 1 1 0 0]
[2 1 0 0 0 0]
[1 0 0 0 0 0]

Case 8: [ 0, 1, 2, 4 ]
[6 5 4 3 2 1]
[5 4 3 2 1 0]
[4 3 2 1 0 0]
[3 2 1 0 0 0]
[2 1 0 0 0 0]
[1 0 0 0 0 0]

*/
