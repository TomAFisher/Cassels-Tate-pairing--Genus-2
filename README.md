# Cassels-Tate-pairing---Genus-2
MAGMA code for computing the Cassels-Tate pairing on the 2-Selmer group of a genus 2 Jacobian

This MAGMA code accompanies the papers

[1] T.A. Fisher and J. Yan, Computing the Cassels-Tate pairing on the 2-Selmer group of a genus 2 Jacobian

https://www.dpmms.cam.ac.uk/~taf1000/papers/genus2ctp.html

and 

[2] T.A. Fisher and M. Liu, Minimisation of 2-coverings of genus 2 Jacobians

https://www.dpmms.cam.ac.uk/~taf1000/papers/g2minimise.html

Attaching the files "g2minimisation.m" and "genus2ctp.m" will make available the intrinsics "TwoDescentGenus2" and "CasselsTatePairingGenus2". See the example at the top of "demo.m" for how to use these.

`TwoDescentGenus2(J : SelmerAl := "TwoSelmerGroupNew")` selects Magma's
alternative 2-Selmer algorithm. The default remains `"TwoSelmerGroupData"`.
The alternative is supported over Q when the reduced working model has
degree 5; the coordinate transport and norm checks are retained. This
option is also available on `TwoSelmerGroupTrue`.
Run `magma selmer-algorithm-test.m` to compare both algorithms on two
quadratic twists and check the covering-model determinant identities.

The files "g2ctp_examples.m" and "examples_LMFDB.m" contain examples that have been computed using this code.

The file "g2ctp_check_paper.m" gives further details of the formulae and examples in [1].

The file "g2min-weights.m" checks some of the claims about "weights" in [2]. The main algorithm in [2] is implemented in "g2minimisation.m". The latter can be tested on the examples in "g2-min-test-data.m" using "g2-min-test-code.m".
