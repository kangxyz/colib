module

import Colib.AlgebraicGeometry.ProjectiveLine.AffineBassPositiveExactness

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules.PerfectMayerVietoris (perfectK)

local notation "R" => CommRingCat.of ℤ

example :
    (affineBassRestrictionPair R 1).range = (affineBassLaurentDifference R 1).ker ∧
    (affineBassLaurentDifference R 1).range = (affineBassLaurentConnecting R 0).ker ∧
    (affineBassLaurentConnecting R 0).range = (affineBassRestrictionPair R 0).ker :=
  affineBassPositiveExactSequence R 0

example (x : perfectK (Spec (.of (LaurentPolynomial ℤ))) 1) :
    affineBassLaurentConnecting R 0 x =
      AlgebraicGeometry.Scheme.Modules.PerfectMayerVietoris.connectingHom
        (negativeChart (Spec R)).ι (positiveChart (Spec R)) (standardChart_cover (Spec R))
        0 (affineBassOverlapEquiv R 1 x) :=
  affineBassLaurentConnecting_square R 0 x
