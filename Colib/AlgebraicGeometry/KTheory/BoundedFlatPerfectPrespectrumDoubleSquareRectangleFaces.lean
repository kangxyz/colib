/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareOriginalRectangle

/-! Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/DoubleSquareRectangleFaces.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
/-! Whole original square faces and the actual three-side quotient parameter. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Convexity Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareScalarPaths

open SimplexParameters

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- The source face is the entire first original exported geometric square route. -/
theorem rectangle_source_original :
    PathLift (BoundedFlatPerfectDoubleSquareMergedSimplex.simplex p q p' q' a b c hp hq)
      ((firstRestriction.symm.trans secondRestriction).trans
        (middleChart.symm.trans lastRestriction))
      (BoundedFlatPerfectDoubleSquareTrack.originalLeft p q p' q' a b c hp hq) :=
  HomotopyLift.source _ (original_rectangle_nativeLift p q p' q' a b c hp hq)

/-- The target face is the entire outer original geometric square route. -/
theorem rectangle_target_original :
    PathLift (BoundedFlatPerfectDoubleSquareMergedSimplex.simplex p q p' q' a b c hp hq)
      (sourceChart.symm.trans ((sourceTotal.symm.trans targetTotal).trans targetChart))
      (BoundedFlatPerfectDoubleSquareTrack.originalRight p q p' q' a b c hp hq) :=
  HomotopyLift.target _ (original_rectangle_nativeLift p q p' q' a b c hp hq)

/-- Explicit scalar family on the same three-side square quotient used for native Bass squares. -/
def rectangleCollapsed :
    C(unitInterval × unitInterval, StdSimplex ℝ (Fin 18)) :=
  collapsed rectangleParameter

/-- The quotient parameter recovers the literal rectangle before collapse. -/
theorem rectangleCollapsed_collapse (z : unitInterval × unitInterval) :
    rectangleCollapsed (ThreeSideSquare.collapse z) = rectangleParameter z :=
  collapsed_collapse rectangleParameter z

/-- Every collapsed parameter on the quotient has the original native rectangle value. -/
theorem rectangleCollapsed_original (n : ℕ) (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (BoundedFlatPerfectTripleSimplex.structureOn A)).space n) :
    prespectrumSimplexFamily
      (BoundedFlatPerfectDoubleSquareMergedSimplex.simplex p q p' q' a b c hp hq) n
      (rectangleCollapsed (ThreeSideSquare.collapse z), x) =
      (BoundedFlatPerfectDoubleSquareTrack.originalComparison p q p' q' a b c hp hq).level n
        (z.1, (z.2, x)) := by
  rw [rectangleCollapsed_collapse]
  exact original_rectangle_nativeLift p q p' q' a b c hp hq n z.1 z.2 x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareScalarPaths
