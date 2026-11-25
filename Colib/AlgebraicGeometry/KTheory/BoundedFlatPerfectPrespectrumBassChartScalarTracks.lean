/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientTransformationComposition
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBassScalarBoundaryParameters

/-!
# Native evaluations of the original Bass scalar chart tracks

The actual coefficient rectangle and its original boundary, including the
terminal pause, are evaluated in the same merged simplex at every level.

Adapted from `BassBoundaryTracks.lean`, `BassBoundarySpecialization.lean` and
`BassMovingSquarePause.lean` in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectBassScalarComparison

open BoundedFlatPerfectDoubleSquareScalarPaths SimplexParameters

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {M N : Under R ⥤ Under R} (α : M ⟶ N)
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Original rectangle endpoints are transported only in type, with the same two-time map. -/
theorem original_nativeLift :
    HomotopyLift (simplex P α u v) originalComparisonParameter
      (BoundedFlatCoefficientTransformationComposition.comparison P α u v) := by
  intro n r s x
  exact comparisonParameter_nativeLift P α u v n r s x

/-- The target coefficient composition retains its exact original time. -/
theorem targetComposition_path :
    PathLift (simplex P α u v) targetChart
      (BoundedFlatCoefficientTransformationComposition.targetComposition P α u v) := by
  let S := simplex P α u v
  change PathLift S targetChart
    (BoundedFlatCoefficientTransformationComposition.targetComposition P α u v)
  have h := HomotopyLift.target S (original_nativeLift P α u v)
  have h' := PathLift.trans_left S h
  intro n t x
  have hv := (PathLift.trans_left S h') n (unitInterval.symm t) x
  change prespectrumSimplexFamily S n
      (targetChart (unitInterval.symm (unitInterval.symm t)), x) =
    (BoundedFlatCoefficientTransformationComposition.targetComposition P α u v).level n
      (unitInterval.symm (unitInterval.symm t), x) at hv
  rw [unitInterval.symm_symm] at hv
  exact hv

/-- The original source composition retains its exact original time. -/
theorem sourceComposition_path :
    PathLift (simplex P α u v) sourceChart
      (BoundedFlatCoefficientTransformationComposition.sourceComposition P α u v) := by
  let S := simplex P α u v
  have h := HomotopyLift.target S (original_nativeLift P α u v)
  exact PathLift.trans_right S h

/-- The direct outer coefficient square retains its exact original time. -/
theorem outerSquare_path :
    PathLift (simplex P α u v) outerSquarePath
      (BoundedFlatCoefficientTransformationComposition.square P α (u ≫ v)) := by
  let S := simplex P α u v
  have h := HomotopyLift.target S (original_nativeLift P α u v)
  exact PathLift.trans_right S (PathLift.trans_left S h)

/-- Both successive coefficient squares are one exact scalar route. -/
theorem compositeSquare_path :
    PathLift (simplex P α u v) originalComparisonSource
      (BoundedFlatCoefficientTransformationComposition.compositeSquare P α u v) :=
  HomotopyLift.source _ (original_nativeLift P α u v)

/-- The literal native moving-square boundary is evaluated from one scalar simplex surface. -/
theorem boundary_nativeLift :
    HomotopyLift (simplex P α u v)
      BoundedFlatPerfectDoubleSquareScalarPaths.coefficientBoundaryParameter
      (BoundedFlatCoefficientTransformationComposition.boundary P α u v) := by
  let S := simplex P α u v
  have h := HomotopyLift.boundaryOfComparison S
    (targetComposition_path P α u v)
    (outerSquare_path P α u v)
    (sourceComposition_path P α u v)
    (original_nativeLift P α u v)
  exact h

/-- The original moving square, not just its four edges, is the scalar collapsed surface. -/
theorem movingSquare_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum
      (RingedSpace.boundedAboveFlatPerfectWaldhausen
        (space (op P, M.obj a)).toRingedSpace)).space n) :
    prespectrumSimplexFamily (simplex P α u v) n
      (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s), x) =
      (BoundedFlatCoefficientTransformationComposition.movingSquare P α u v).level n
        (r, (s, x)) :=
  HomotopyLift.toSquare _ (boundary_nativeLift P α u v) n r s x

/-- The actual native `pauseRight` chart square keeps its whole scalar parameter and collapse. -/
theorem pausedSquare_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum
      (RingedSpace.boundedAboveFlatPerfectWaldhausen
        (space (op P, M.obj a)).toRingedSpace)).space n) :
    prespectrumSimplexFamily (simplex P α u v) n
      (BoundedFlatPerfectDoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s), x) =
      ((BoundedFlatCoefficientTransformationComposition.movingSquare P α u v).pauseRight).level n
        (r, (s, x)) :=
  HomotopyLift.pauseRight_square _ (boundary_nativeLift P α u v)
    (targetComposition_path P α u v)
    (compositeSquare_path P α u v)
    (sourceComposition_path P α u v) n r s x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectBassScalarComparison
