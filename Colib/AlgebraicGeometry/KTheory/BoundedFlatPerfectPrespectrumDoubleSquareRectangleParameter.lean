/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareScalarPaths
public import Colib.Topology.Path.Homotopy.ThreeRoutes

/-!
# The scalar rectangle in the merged double-square simplex

The original three typed comparison homotopies give the rectangle with its
literal source and target path words.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ScalarRectangleParameter.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareScalarPaths

/-- The source runs along the reversed first restriction and the second restriction, then
along the reversed middle chart and the last restriction. The target runs along the reversed
source chart, the reversed source total, and the target total and chart, in the original
association. -/
def rectangleParameter :
    ((firstRestriction.symm.trans secondRestriction).trans
      (middleChart.symm.trans lastRestriction)).Homotopy
    (sourceChart.symm.trans ((sourceTotal.symm.trans targetTotal).trans targetChart)) :=
  Path.Homotopy.threeRoutes firstComparison middleComparison lastComparison

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareScalarPaths
