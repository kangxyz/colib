/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientLaurentUnitSquares
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareRectangleFaces
public import Colib.AlgebraicGeometry.Scheme.CoefficientLaurentProjection

/-!
# The original scalar paths for Bass coefficient comparison

Reverse the path time of the original rectangle and keep its constituent
paths. The resulting scalar comparison evaluates to the actual scheme-level
comparison specialized along two coefficient squares.

Adapted from `BassRectangleSpecialization.lean` and `BassScalarComparison.lean`
under `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareScalarPaths

/-- The outer square traverses the target total backwards, then the source total forwards. -/
def outerSquarePath := targetTotal.symm.trans sourceTotal

/-- The original chart source reverses the concatenation of the two restriction routes. -/
def originalComparisonSource :=
  ((firstRestriction.symm.trans secondRestriction).trans
    (middleChart.symm.trans lastRestriction)).symm

/-- The target chart word retains the reversed target chart, outer square, and source chart. -/
def originalComparisonTarget :=
  (targetChart.symm.trans outerSquarePath).trans sourceChart

/-- Reverse only the path parameter and identify the endpoint paths by their exact words. -/
def originalComparisonParameter :
    originalComparisonSource.Homotopy originalComparisonTarget :=
  rectangleParameter.symm₂.cast rfl (by
    simp only [Path.trans_symm, Path.symm_symm]
    rfl)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareScalarPaths

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectBassScalarComparison

open BoundedFlatPerfectDoubleSquareScalarPaths SimplexParameters

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {M N : Under R ⥤ Under R} (α : M ⟶ N)
variable {a b c : Under R} (g : a ⟶ b) (h : b ⟶ c)

/-- The actual merged common simplex from the two adjacent coefficient squares. -/
def simplex :=
  BoundedFlatPerfectDoubleSquareMergedSimplex.simplex
    (coefficientMap P (M.map g)) (coefficientMap P (M.map h))
    (coefficientMap P (N.map g)) (coefficientMap P (N.map h))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (coefficientMap_naturality_of_natTrans P α g).symm
    (coefficientMap_naturality_of_natTrans P α h).symm

/-- The literal original scalar rectangle lifts the corresponding actual native rectangle. -/
theorem rectangle_nativeLift :
    HomotopyLift (simplex P α g h) rectangleParameter
      (BoundedFlatPerfectDoubleSquareTrack.originalComparison
        (coefficientMap P (M.map g)) (coefficientMap P (M.map h))
        (coefficientMap P (N.map g)) (coefficientMap P (N.map h))
        (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
        (coefficientMap_naturality_of_natTrans P α g).symm
        (coefficientMap_naturality_of_natTrans P α h).symm) :=
  original_rectangle_nativeLift
    (coefficientMap P (M.map g)) (coefficientMap P (M.map h))
    (coefficientMap P (N.map g)) (coefficientMap P (N.map h))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (coefficientMap_naturality_of_natTrans P α g).symm
    (coefficientMap_naturality_of_natTrans P α h).symm

/-- The exact comparison lift with the original reversed path coordinate. -/
theorem comparisonParameter_nativeLift :
    HomotopyLift (simplex P α g h) originalComparisonParameter
      (BoundedFlatPerfectDoubleSquareTrack.originalComparison
        (coefficientMap P (M.map g)) (coefficientMap P (M.map h))
        (coefficientMap P (N.map g)) (coefficientMap P (N.map h))
        (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
        (coefficientMap_naturality_of_natTrans P α g).symm
        (coefficientMap_naturality_of_natTrans P α h).symm).symmPath := by
  intro n r s x
  exact (HomotopyLift.symmPath _ (rectangle_nativeLift P α g h)) n r s x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectBassScalarComparison
