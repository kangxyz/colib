/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitUnitRows
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleSimplex
public import Colib.KTheory.Waldhausen.Iterated.SimplexLiftOperations
public import Colib.Topology.Path.Homotopy.ThreeRoutes

/-! The literal six triangles, four paths, route comparison and quotient clocks of the
original split-unit square. Adapted from `OriginalUnitSquareSimplex.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No native square evaluation is asserted. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Convexity Topology CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex
open BoundedFlatPerfectSplitTripleSimplex (triangleFace)

/-- The scalar triangle for the split first right-unit comparison. -/
def rightFirstParameter :=
  triangle (k := 7) (triangleFace 0 1 2 (by decide) (by decide))
/-- The scalar triangle for the split second right-unit comparison. -/
def rightSecondParameter :=
  triangle (k := 7) (triangleFace 2 3 7 (by decide) (by decide))
/-- The scalar triangle for the two unsplit right-unit comparisons. -/
def normalizedRightParameter :=
  triangle (k := 7) (triangleFace 0 2 7 (by decide) (by decide))
/-- The scalar triangle for the split first left-unit comparison. -/
def leftFirstParameter :=
  triangle (k := 7) (triangleFace 0 4 5 (by decide) (by decide))
/-- The scalar triangle for the split second left-unit comparison. -/
def leftSecondParameter :=
  triangle (k := 7) (triangleFace 5 6 7 (by decide) (by decide))
/-- The scalar triangle for the two unsplit left-unit comparisons. -/
def normalizedLeftParameter :=
  triangle (k := 7) (triangleFace 0 5 7 (by decide) (by decide))

/-- The two-edge parameter path for the first right-unit comparison. -/
def rightCompositionPath : Path (StdSimplex.single 0 : StdSimplex ℝ (Fin 8))
    (StdSimplex.single 2) := (edge 0 1).trans (edge 1 2)
/-- The two-edge parameter path for the second right-unit comparison. -/
def rightUnitPath : Path (StdSimplex.single 2 : StdSimplex ℝ (Fin 8))
    (StdSimplex.single 7) := (edge 2 3).trans (edge 3 7)
/-- The two-edge parameter path for the first left-unit comparison. -/
def leftCompositionPath : Path (StdSimplex.single 0 : StdSimplex ℝ (Fin 8))
    (StdSimplex.single 5) := (edge 0 4).trans (edge 4 5)
/-- The two-edge parameter path for the second left-unit comparison. -/
def leftUnitPath : Path (StdSimplex.single 5 : StdSimplex ℝ (Fin 8))
    (StdSimplex.single 7) := (edge 5 6).trans (edge 6 7)

/-- Original right-to-left unit-route comparison, with its unchanged association and speeds. -/
def routesParameter : (rightCompositionPath.trans rightUnitPath).Homotopy
    (leftCompositionPath.trans leftUnitPath) :=
  (rightFirstParameter.hcomp rightSecondParameter).symm.trans
    ((normalizedRightParameter.symm.trans normalizedLeftParameter).trans
      (leftFirstParameter.hcomp leftSecondParameter))

/-- Rotation and constant-half contraction are the actual native operations, before collapse. -/
def rotatedParameter :=
  (Path.Homotopy.rotate routesParameter).trans
    ((Path.Homotopy.transRefl rightUnitPath).symm.hcomp
      (Path.Homotopy.refl leftUnitPath.symm))

/-- The square parameter uses the same three-side quotient as the original unit square. -/
def squareParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 8)) :=
  collapsed rotatedParameter

theorem square_collapse (z : unitInterval × unitInterval) :
    squareParameter (ThreeSideSquare.collapse z) = rotatedParameter z :=
  collapsed_collapse rotatedParameter z

/-- Exact original lower scalar path. -/
theorem square_zero (t : unitInterval) :
    squareParameter (0, t) = (rightCompositionPath.symm.trans leftCompositionPath) t := by
  have h := square_collapse (0, t)
  rw [ThreeSideSquare.collapse_zero] at h
  exact h.trans (rotatedParameter.apply_zero t)

/-- Exact scalar left boundary, with the original first-quarter time. -/
theorem square_left (r : unitInterval) :
    squareParameter (r, 0) =
      ((rightUnitPath.trans (Path.refl (StdSimplex.single 7))).trans leftUnitPath.symm)
        (ThreeSideSquare.leftTime r) := by
  have h := square_collapse (1, ThreeSideSquare.leftTime r)
  rw [ThreeSideSquare.collapse_leftTime] at h
  exact h.trans (rotatedParameter.apply_one _)

/-- Exact scalar top boundary, retaining the original constant half before quotienting. -/
theorem square_top (t : unitInterval) :
    squareParameter (1, t) =
      ((rightUnitPath.trans (Path.refl (StdSimplex.single 7))).trans leftUnitPath.symm)
        (ThreeSideSquare.topTime t) := by
  have h := square_collapse (1, ThreeSideSquare.topTime t)
  rw [ThreeSideSquare.collapse_topTime] at h
  exact h.trans (rotatedParameter.apply_one _)

/-- Exact scalar right boundary, with the original reversed final-half time. -/
theorem square_right (r : unitInterval) :
    squareParameter (r, 1) =
      ((rightUnitPath.trans (Path.refl (StdSimplex.single 7))).trans leftUnitPath.symm)
        (ThreeSideSquare.rightTime r) := by
  have h := square_collapse (1, ThreeSideSquare.rightTime r)
  rw [ThreeSideSquare.collapse_rightTime] at h
  exact h.trans (rotatedParameter.apply_one _)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex
